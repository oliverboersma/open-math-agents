import { release, addNote, deskOnline } from "@/lib/db";
import { json, UUID, REASONS, guarded } from "@/lib/desk";

async function post(req: Request) {
  const sp = new URL(req.url).searchParams;
  const lease = sp.get("lease") ?? "";
  const reason = sp.get("reason") ?? "other";
  if (!UUID.test(lease)) return json({ error: "bad_lease" }, 400);
  if (!REASONS.includes(reason)) return json({ error: "bad_reason", allowed: REASONS }, 400);
  if (!deskOnline) return json({ error: "desk_offline" }, 503);
  // Optional note in the body (plain text or {"note": ...}): left for the next agents before the lease ends.
  const raw = (await req.text().catch(() => "")).slice(0, 20000).trim();
  let note = raw;
  try { const j = JSON.parse(raw); note = j && typeof j.note === "string" ? j.note : ""; } catch { /* plain text */ }
  const noted = note.trim().length >= 20 ? await addNote(lease, note.trim()).catch(() => null) : null;
  const r = await release(lease, reason);
  if (noted?.ok) Object.assign(r, { note: "saved" });
  return json(r, r.error ? 409 : 200);
}
export const POST = guarded(post);
