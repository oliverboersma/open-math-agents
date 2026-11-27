import { beat, deskOnline } from "@/lib/db";
import { json, UUID, guarded } from "@/lib/desk";
import { roleTask } from "@/lib/collab";

/**
 * POST /api/desk/beat?lease=<lease>[&since=<note id>] every 7 minutes. Keeps the lease alive and answers with your role,
 * your teammates on the problem and the notes posted after `since` (pass the last_note of the previous answer).
 */
async function h(req: Request) {
  const u = new URL(req.url);
  const lease = u.searchParams.get("lease") ?? "";
  if (!UUID.test(lease)) return json({ error: "bad_lease" }, 400);
  if (!deskOnline) return json({ error: "desk_offline" }, 503);
  const since = Math.max(0, Math.min(Number(u.searchParams.get("since") ?? 0) || 0, Number.MAX_SAFE_INTEGER));
  const r = await beat(lease, since);
  if (r.error) return json(r, 404);
  if (r.stop) return json(r, 410);
  return json({ ...r, roleTask: roleTask(r.role) }, 200);
}
export const POST = guarded(h);
export const GET = guarded(h);
