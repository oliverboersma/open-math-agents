-- 016: agents on the same problem work as a team.
-- Each new lease on a problem gets the first free role (lead, checker, scout, splitter, then helper), the claim and
-- every heartbeat return the team (who holds the problem now, with which role) and the notes posted since the agent
-- last looked, and an agent may post up to 12 notes per lease (PLAN / TAKING / DONE / DEAD END).

alter table oma_leases add column if not exists role text;

create or replace function oma_team(p_problem text, p_except uuid) returns json
language sql stable security definer set search_path = public, pg_temp as $$
  select coalesce(json_agg(json_build_object('handle', handle, 'role', coalesce(role, 'helper'), 'agent', agent,
                                             'since', created_at, 'last_beat', beat_at) order by created_at), '[]'::json)
  from oma_leases
  where problem_id = p_problem and status = 'active' and beat_at > now() - interval '15 minutes'
    and (p_except is null or id <> p_except);
$$;

create or replace function oma_notes_since(p_problem text, p_since bigint, p_limit int) returns json
language sql stable security definer set search_path = public, pg_temp as $$
  select coalesce(json_agg(json_build_object('id', id, 'handle', handle, 'at', created_at, 'note', detail) order by id), '[]'::json)
  from (select id, handle, created_at, detail from oma_events
        where problem_id = p_problem and kind = 'note' and id > coalesce(p_since, 0)
        order by id desc limit least(greatest(coalesce(p_limit, 12), 1), 30)) n;
$$;

create or replace function oma_claim2(p_problem text, p_handle text, p_agent text, p_ip_hash text, p_points integer) returns json
language plpgsql volatile security definer set search_path = public, pg_temp as $$
declare r json; v_lease uuid; v_role text;
begin
  r := oma_claim(p_problem, p_handle, p_agent, p_ip_hash);
  if r->>'lease' is null then return r; end if;
  v_lease := (r->>'lease')::uuid;
  update oma_leases set points = coalesce(p_points, 0) where id = v_lease and points = 0;
  select role into v_role from oma_leases where id = v_lease;
  if v_role is null then
    select t.x into v_role from unnest(array['lead', 'checker', 'scout', 'splitter']) with ordinality as t(x, o)
     where t.x not in (select coalesce(role, '') from oma_leases
                        where problem_id = p_problem and status = 'active' and beat_at > now() - interval '15 minutes' and id <> v_lease)
     order by t.o limit 1;
    v_role := coalesce(v_role, 'helper');
    update oma_leases set role = v_role where id = v_lease;
  end if;
  return json_build_object('lease', v_lease, 'role', v_role, 'team', oma_team(p_problem, v_lease),
                           'notes', oma_notes_since(p_problem, 0, 12),
                           'last_note', (select max(id) from oma_events where problem_id = p_problem and kind = 'note'));
end $$;

create or replace function oma_beat2(p_lease uuid, p_since bigint) returns json
language plpgsql volatile security definer set search_path = public, pg_temp as $$
declare r json; v_row oma_leases;
begin
  r := oma_beat(p_lease);
  if (r->>'ok') is null then return r; end if;
  select * into v_row from oma_leases where id = p_lease;
  return json_build_object('ok', true, 'role', coalesce(v_row.role, 'helper'), 'team', oma_team(v_row.problem_id, p_lease),
                           'notes', oma_notes_since(v_row.problem_id, p_since, 12),
                           'last_note', (select max(id) from oma_events where problem_id = v_row.problem_id and kind = 'note'));
end $$;

create or replace function oma_note(p_lease uuid, p_note text) returns json
language plpgsql volatile security definer set search_path = public, pg_temp as $$
declare v_row oma_leases; v_n int; v_id bigint;
begin
  if p_note is null or length(btrim(p_note)) < 20 then return json_build_object('error', 'note_too_short'); end if;
  select * into v_row from oma_leases where id = p_lease and (status = 'active' or ended_at > now() - interval '2 hours');
  if not found then return json_build_object('error', 'unknown_or_old_lease'); end if;
  select count(*) into v_n from oma_events where kind = 'note' and problem_id = v_row.problem_id and handle = v_row.handle and created_at >= v_row.created_at;
  if v_n >= 12 then return json_build_object('error', 'too_many_notes', 'limit', 12); end if;
  insert into oma_events (kind, problem_id, handle, detail) values ('note', v_row.problem_id, v_row.handle, left(p_note, 4000)) returning id into v_id;
  return json_build_object('ok', true, 'problem', v_row.problem_id, 'id', v_id);
end $$;

revoke all on function oma_team(text, uuid), oma_notes_since(text, bigint, int), oma_claim2(text, text, text, text, integer),
  oma_beat2(uuid, bigint), oma_note(uuid, text) from public, anon, authenticated;

-- oma_api: a 'beat2' branch next to 'beat' (the rest unchanged).
do $do$
declare d text; d2 text;
begin
  d := pg_get_functiondef('public.oma_api(text,text,json)'::regprocedure);
  if position($x$when 'beat2' then$x$ in d) > 0 then return; end if;
  d2 := replace(d, $x$    when 'beat' then$x$, $x$    when 'beat2' then
      return oma_beat2((a->>'lease')::uuid, (a->>'since')::bigint);
    when 'beat' then$x$);
  if d2 = d then raise exception 'oma_api: beat branch not found'; end if;
  execute d2;
end $do$;
