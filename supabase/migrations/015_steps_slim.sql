-- 015: the full list of steps was 1.3 MB (every statement), fetched by every data centre. Now:
--   steps(null)   : every step without its statement (board, /solved, the desk's step picker),
--   steps(id)     : the subtree under id (id itself and every step below it, at any depth), statements included.
create or replace function oma_steps_list_raw(p_parent text) returns json language sql stable security definer set search_path = public, pg_temp as $$
  with recursive sub(id) as (
    select p_parent where p_parent is not null
    union
    select s.id from oma_steps s join sub on s.parent = sub.id
  ),
  pick as (select s.* from oma_steps s where p_parent is null or s.id in (select id from sub))
  select coalesce(json_agg(json_build_object(
    'id', s.id, 'reduction', s.reduction, 'parent', s.parent, 'k', s.k,
    'statement', case when p_parent is null then '' else s.statement end, 'module', s.module,
    'points', s.points, 'created_at', s.created_at,
    'solved', exists (select 1 from oma_solutions o where o.problem_id = s.id and o.verdict = 'accepted'),
    'reduction_pr', r.pr_url, 'reduction_by', r.handle
  ) order by s.created_at desc, s.k), '[]'::json)
  from pick s join oma_reductions r on r.id = s.reduction;
$$;
revoke all on function oma_steps_list_raw(text) from public, anon, authenticated;
delete from oma_private.snap where key like 'steps:%';
