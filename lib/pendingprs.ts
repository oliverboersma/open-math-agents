/**
 * Problems with a proof (or a statement) waiting for its verdict: an open pull request, or a lease released as
 * "submitted" in the last hours. The desk stops handing them out, so no agent spends an hour on a problem someone
 * already sent a proof for. Two sources:
 *  - the merger (backlog.yml) lists the open pull requests every 15 minutes and posts their titles (problem ids) to
 *    /api/pending with its OIDC token; they are kept in Workers KV;
 *  - the desk's own "submit" events (tools/oma.sh submit), which cover the minutes before the next list.
 */
import { env as cfEnv } from "cloudflare:workers";
import { getEvents } from "@/lib/db";

export type Pending = { pr?: number; since: string };
type KV = { get(k: string, o: { type: "json"; cacheTtl?: number }): Promise<unknown>; put(k: string, v: string, o?: { expirationTtl?: number }): Promise<void> };
export const PENDING_KEY = "pending:v1";
/** A submission without a pull request in the merger's list is trusted this long. */
const SUBMIT_HOURS = 6;

export function pendingKv(): KV | null {
  try {
    return ((cfEnv as unknown as { DESK_KV?: KV }).DESK_KV) ?? null;
  } catch {
    return null;
  }
}

let mem: { at: number; map: Map<string, Pending> } | null = null;

/** Problem id -> the pending pull request (cached 30 seconds per isolate). */
export async function getPending(): Promise<Map<string, Pending>> {
  if (mem && Date.now() - mem.at < 30_000) return mem.map;
  const map = new Map<string, Pending>();
  try {
    const list = (await pendingKv()?.get(PENDING_KEY, { type: "json", cacheTtl: 60 })) as { items?: { id: string; pr: number; since: string }[] } | null;
    for (const x of list?.items ?? []) if (x && typeof x.id === "string") map.set(x.id, { pr: x.pr, since: x.since });
  } catch { /* KV unavailable: the events below still count */ }
  try {
    const cutoff = Date.now() - SUBMIT_HOURS * 3600_000;
    for (const e of await getEvents(500, undefined, "submit")) {
      if (Date.parse(e.created_at) >= cutoff && !map.has(e.problem_id)) map.set(e.problem_id, { since: e.created_at });
    }
  } catch { /* events unavailable */ }
  mem = { at: Date.now(), map };
  return map;
}

/** The answer the desk gives when an agent asks for a problem that already has a proof waiting. */
export function pendingError(id: string, p: Pending, repo: string) {
  return {
    error: "proof_pending",
    problem: id,
    pr: p.pr ? `https://github.com/${repo}/pull/${p.pr}` : null,
    since: p.since,
    hint: "Someone already sent a proof of this problem; it is waiting for its verdict. Take another problem " +
      "(call the desk without problem=), or add force=1 to work on it anyway: if that proof is accepted, yours is turned away.",
  };
}
