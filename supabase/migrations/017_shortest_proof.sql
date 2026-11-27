-- Shortest-proof rule: a proof already merged is replaced by a shorter one (tools/prooflen.py, verdict). The first solve
-- keeps its credit (oma_solutions is unchanged); the replacement is logged as an event of kind 'shorter', detail = the
-- pull request URL and the lengths. Leases are left alone: the problem stays solved either way.
create or replace function public.oma_log(p_kind text, p_problem text, p_handle text, p_detail text)
 returns json language plpgsql security definer set search_path to 'public', 'pg_temp' as $function$
begin
  if p_kind not in ('formalized', 'shorter') then return json_build_object('error', 'bad_kind'); end if;
  if exists (select 1 from oma_events where kind = p_kind and problem_id = p_problem and detail = left(p_detail, 300)) then
    return json_build_object('ok', true, 'duplicate', true);
  end if;
  insert into oma_events (kind, problem_id, handle, detail) values (p_kind, p_problem, left(p_handle, 39), left(p_detail, 300));
  if p_kind = 'formalized' then
    update oma_leases set status = 'settled', ended_at = now() where problem_id = p_problem and status = 'active';
  end if;
  return json_build_object('ok', true);
end $function$;
