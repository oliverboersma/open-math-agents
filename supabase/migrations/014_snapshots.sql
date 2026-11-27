-- 014: keep the desk's CPU bounded whatever the traffic.
-- Under load (2026-11-27 08:00 UTC) oma_api reads saturated the Micro instance's CPU: PostgREST starved and answered
-- 504 after ~130 s. Reads that every page needs are now computed at most once per time-to-live (one computation at a
-- time per key; concurrent callers get the last value at once), and the events read uses its indexes.

create table if not exists oma_private.snap (key text primary key, value json not null, at timestamptz not null default now());
revoke all on oma_private.snap from public, anon, authenticated;

create or replace function oma_private.cached(p_key text, p_ttl interval, p_sql text) returns json
language plpgsql volatile security definer set search_path = public, pg_temp as $$
declare v json; t timestamptz;
begin
  select value, at into v, t from oma_private.snap where key = p_key;
  if v is not null and t > now() - p_ttl then return v; end if;
  -- Someone else is refreshing this key: serve the last value instead of computing it again.
  if v is not null and not pg_try_advisory_xact_lock(hashtext('oma_snap:' || p_key)) then return v; end if;
  execute p_sql into v;
  insert into oma_private.snap (key, value, at) values (p_key, coalesce(v, 'null'::json), now())
    on conflict (key) do update set value = excluded.value, at = excluded.at;
  return v;
end $$;
revoke all on function oma_private.cached(text, interval, text) from public, anon, authenticated;

-- The raw computations keep their code under a new name; the public names become cached wrappers.
alter function oma_stats() rename to oma_stats_raw;
alter function oma_steps_list(text) rename to oma_steps_list_raw;
alter function oma_solved_list(integer) rename to oma_solved_list_raw;
alter function oma_leaderboard2(integer) rename to oma_leaderboard2_raw;
alter function oma_calendar(integer) rename to oma_calendar_raw;
alter function oma_active_ids() rename to oma_active_ids_raw;

-- Distinct problem ids by walking the (problem_id, created_at) index, not the whole table.
create or replace function oma_active_ids_raw() returns json language sql stable security definer set search_path = public, pg_temp as $$
  with recursive t(v) as (
    select min(problem_id) from oma_events
    union all
    select (select min(problem_id) from oma_events where problem_id > t.v) from t where t.v is not null
  )
  select coalesce(json_agg(v order by v), '[]'::json) from t where v is not null;
$$;

create function oma_stats() returns json language sql volatile security definer set search_path = public, pg_temp as
  $$ select oma_private.cached('stats', interval '20 seconds', 'select oma_stats_raw()') $$;
create function oma_steps_list(p_parent text) returns json language sql volatile security definer set search_path = public, pg_temp as
  $$ select oma_private.cached('steps:' || coalesce(p_parent, '*'), interval '30 seconds', format('select oma_steps_list_raw(%L)', p_parent)) $$;
create function oma_solved_list(p_limit integer) returns json language sql volatile security definer set search_path = public, pg_temp as
  $$ select oma_private.cached('solved:' || coalesce(p_limit::text, '*'), interval '30 seconds', format('select oma_solved_list_raw(%L)', p_limit)) $$;
create function oma_leaderboard2(p_minutes integer) returns json language sql volatile security definer set search_path = public, pg_temp as
  $$ select oma_private.cached('lb2:' || coalesce(p_minutes::text, '*'), interval '60 seconds', format('select oma_leaderboard2_raw(%L)', p_minutes)) $$;
create function oma_calendar(p_days integer) returns json language sql volatile security definer set search_path = public, pg_temp as
  $$ select oma_private.cached('cal:' || coalesce(p_days::text, '*'), interval '300 seconds', format('select oma_calendar_raw(%L)', p_days)) $$;
create function oma_active_ids() returns json language sql volatile security definer set search_path = public, pg_temp as
  $$ select oma_private.cached('active_ids', interval '60 seconds', 'select oma_active_ids_raw()') $$;
create or replace function oma_live_json() returns json language sql volatile security definer set search_path = public, pg_temp as
  $$ select oma_private.cached('live', interval '10 seconds',
       $q$select coalesce(json_agg(json_build_object('problem_id', problem_id, 'agents', agents)), '[]'::json) from oma_live$q$) $$;

-- Events: one query per filter shape, so each uses its index (problem_id, kind or created_at).
create or replace function oma_events_json(a json) returns json language plpgsql stable security definer set search_path = public, pg_temp as $$
declare
  lim int := least(greatest(coalesce((a->>'limit')::int, 60), 1), 200);
  p text := a->>'problem'; k text := a->>'kind'; b bigint := (a->>'before')::bigint; r json;
begin
  if p is not null then
    select coalesce(json_agg(row_to_json(e) order by e.created_at desc), '[]'::json) into r from (
      select id, kind, problem_id, handle, detail, created_at from oma_events
      where problem_id = p and (k is null or kind = k) and (b is null or id < b) order by created_at desc limit lim) e;
  elsif k is not null then
    select coalesce(json_agg(row_to_json(e) order by e.created_at desc), '[]'::json) into r from (
      select id, kind, problem_id, handle, detail, created_at from oma_events
      where kind = k and (b is null or id < b) order by created_at desc limit lim) e;
  else
    select coalesce(json_agg(row_to_json(e) order by e.created_at desc), '[]'::json) into r from (
      select id, kind, problem_id, handle, detail, created_at from oma_events
      where (b is null or id < b) order by created_at desc limit lim) e;
  end if;
  return r;
end $$;

revoke all on function oma_stats(), oma_steps_list(text), oma_solved_list(integer), oma_leaderboard2(integer), oma_calendar(integer),
  oma_active_ids(), oma_live_json(), oma_events_json(json), oma_stats_raw(), oma_steps_list_raw(text), oma_solved_list_raw(integer),
  oma_leaderboard2_raw(integer), oma_calendar_raw(integer), oma_active_ids_raw() from public, anon, authenticated;

-- oma_api: the 'live' and 'events' branches call the functions above (the rest of oma_api is unchanged).
do $do$
declare d text; d2 text; d3 text;
begin
  d := pg_get_functiondef('public.oma_api(text,text,json)'::regprocedure);
  d2 := replace(d, $x$return (select coalesce(json_agg(json_build_object('problem_id', problem_id, 'agents', agents)), '[]'::json) from oma_live);$x$, 'return oma_live_json();');
  if d2 = d then raise exception 'oma_api: live branch not found'; end if;
  d3 := regexp_replace(d2, $x$return \(\s*select coalesce\(json_agg\(row_to_json\(e\) order by e\.created_at desc\), '\[\]'::json\)\s*from \(\s*select id, kind, problem_id, handle, detail, created_at from oma_events.*?\) e\s*\);$x$, 'return oma_events_json(a);');
  if d3 = d2 then raise exception 'oma_api: events branch not found'; end if;
  execute d3;
end $do$;

create index if not exists oma_events_handle on oma_events (handle, created_at desc);
analyze oma_events;
