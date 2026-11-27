import { verifyWorkflowToken } from "@/lib/ghoidc";
import { json } from "@/lib/desk";
import { pendingKv, PENDING_KEY } from "@/lib/pendingprs";

/**
 * The merger (backlog.yml, trusted: it never runs pull request code) posts the open pull requests here every 15 minutes:
 * { oidc, items: [{ id: problem id (the pull request title), pr, since }] }. The desk then stops handing those problems
 * out (lib/pendingprs.ts). Only a request proved by the workflow's GitHub OIDC token is accepted.
 */
export async function POST(req: Request) {
  const b = (await req.json().catch(() => null)) as { oidc?: string; items?: unknown[] } | null;
  if (!b || !Array.isArray(b.items) || typeof b.oidc !== "string") return json({ error: "bad_request" }, 400);
  if (!(await verifyWorkflowToken(b.oidc))) return json({ error: "unauthorized" }, 401);
  const items = b.items
    .map((x) => x as { id?: unknown; pr?: unknown; since?: unknown })
    .filter((x) => typeof x.id === "string" && /^[A-Za-z0-9_.'-]{1,200}$/.test(x.id) && Number.isInteger(x.pr))
    .slice(0, 20000)
    .map((x) => ({ id: x.id as string, pr: x.pr as number, since: typeof x.since === "string" ? x.since.slice(0, 25) : "" }));
  const kv = pendingKv();
  if (!kv) return json({ error: "kv_unavailable" }, 503);
  // kept two hours: if the merger stops posting, the list fades out instead of blocking problems forever
  await kv.put(PENDING_KEY, JSON.stringify({ at: new Date().toISOString(), items }), { expirationTtl: 7200 });
  return json({ ok: true, items: items.length });
}
