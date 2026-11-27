import "server-only";
import { createHash } from "node:crypto";
import { env as cfEnv } from "cloudflare:workers";
import type { Mate, TeamNote } from "@/lib/collab";

/** Coordination desk client. Every call goes through one Postgres function, oma_api, which checks
 * OMA_DB_SECRET server-side (see supabase/migrations/002_api_gate.sql). The Supabase key only
 * opens PostgREST; without the secret it can do nothing.
 * Without env vars the desk is "offline": catalogue and search work, live counts read as zero. */
const URL_ = process.env.SUPABASE_URL;
const KEY = process.env.SUPABASE_PUBLISHABLE_KEY ?? process.env.SUPABASE_SERVICE_ROLE_KEY;
const SECRET = process.env.OMA_DB_SECRET;

export const deskOnline = Boolean(URL_ && KEY && SECRET);

// Circuit breaker: after a timeout or a 5xx, this Worker instance stops calling the database for a while, so an
// overloaded database gets room to recover instead of a pile of waiting requests, and pages answer at once (cached or
// empty values). Two of them: a failed read (pages refresh with a 1 s budget, and have a last good value to fall back
// on) pauses reads for 2 min but not the agents' writes; a failed write pauses both, writes for 30 s.
let readsDownUntil = 0;
let writesDownUntil = 0;
export const deskDown = () => Date.now() < Math.max(readsDownUntil, writesDownUntil);

/** Thrown when the database cannot answer (breaker open, timeout, 5xx): API routes answer 503 with Retry-After. */
export class DeskUnavailable extends Error {
  constructor(cause?: unknown) {
    super(`desk_unavailable${cause instanceof Error ? `: ${cause.message}` : ""}`);
    this.name = "DeskUnavailable";
  }
}

async function rpc<T>(fn: string, args: Record<string, unknown>, timeoutMs = 8000, kind: "read" | "write" = "write"): Promise<T> {
  const now = Date.now();
  if (now < writesDownUntil || (kind === "read" && now < readsDownUntil)) throw new DeskUnavailable();
  try {
    return await rpcOnce<T>(fn, args, timeoutMs);
  } catch (e) {
    readsDownUntil = Date.now() + 120_000;
    if (kind === "write") writesDownUntil = Date.now() + 30_000;
    throw new DeskUnavailable(e);
  }
}

async function rpcOnce<T>(fn: string, args: Record<string, unknown>, timeoutMs: number): Promise<T> {
  // Never let a slow database hang the site: reads give up after 4 s (and fall back to the last good value), writes after 8 s.
  const res = await fetch(`${URL_}/rest/v1/rpc/oma_api`, {
    method: "POST",
    headers: { apikey: KEY!, "Content-Type": "application/json" },
    body: JSON.stringify({ p_secret: SECRET, p_fn: fn, p_args: args }),
    cache: "no-store",
    signal: AbortSignal.timeout(timeoutMs),
  });
  if (!res.ok) throw new Error(`oma_api ${fn} ${res.status}: ${(await res.text()).slice(0, 200)}`);
  return (await res.json()) as T;
}

/**
 * Reads with a time-to-live are shared, so traffic does not turn into database calls: first this Worker instance's
 * memory, then Cloudflare's cache in this data centre (shared by every instance there, free), and only then
 * Supabase. Concurrent identical reads wait for one call. Writes (claims, beats, verdicts) are never cached.
 */
const MEM = new Map<string, { at: number; value: unknown }>();
const INFLIGHT = new Map<string, Promise<unknown>>();
const CACHE_ORIGIN = (process.env.SITE_URL ?? process.env.NEXT_PUBLIC_SITE_URL ?? "https://lefttosolve.com").replace(/\/$/, "");
function edgeCache(): Cache | null {
  try {
    return (globalThis as unknown as { caches?: { default?: Cache } }).caches?.default ?? null;
  } catch {
    return null;
  }
}

// Reads shared by every page (no per-problem or per-person argument): also kept in Workers KV, one copy for the whole
// network, so Supabase answers them about once per time-to-live worldwide instead of once per data centre.
const GLOBAL_FNS = new Set(["stats", "live", "active_ids", "steps", "solved", "leaderboard", "leaderboard2", "calendar", "graveyard"]);
type KV = { get(k: string, o: { type: "json"; cacheTtl?: number }): Promise<unknown>; put(k: string, v: string, o?: { expirationTtl?: number }): Promise<void> };
function kv(): KV | null {
  try {
    return ((cfEnv as unknown as { DESK_KV?: KV }).DESK_KV) ?? null;
  } catch {
    return null;
  }
}

async function api<T>(fn: string, args: Record<string, unknown> = {}, revalidate?: number): Promise<T> {
  if (!deskOnline) throw new Error("desk_offline");
  if (!revalidate) return rpc<T>(fn, args);
  const key = `${fn}?${JSON.stringify(args)}`;
  const ttl = revalidate * 1000;
  const m = MEM.get(key);
  if (m && Date.now() - m.at < ttl) return m.value as T;
  // Reads are cached twice as long as asked while the database is under load (STALE_FACTOR), and a failed refresh
  // serves the last good value instead of an empty page.
  const running = INFLIGHT.get(key);
  if (running) return running as Promise<T>;
  const p = (async () => {
    const cache = edgeCache();
    const req = new Request(`${CACHE_ORIGIN}/__desk_cache/${encodeURIComponent(key)}`);
    if (cache) {
      const hit = await cache.match(req).catch(() => undefined);
      if (hit) {
        const { at, value } = (await hit.json()) as { at: number; value: T };
        if (Date.now() - at < ttl) {
          MEM.set(key, { at, value });
          return value;
        }
      }
    }
    // Global copy (KV). Fresh: use it. A little stale: most callers still use it and only ~15% refresh it, so the
    // data centres that notice at the same moment do not all call the database.
    const store = GLOBAL_FNS.has(fn) && !("parent" in args) ? kv() : null;
    let kvStale: { at: number; value: T } | null = null;
    if (store) {
      const got = (await store.get(`v1:${key}`, { type: "json", cacheTtl: 30 }).catch(() => null)) as { at: number; value: T } | null;
      if (got) {
        const age = Date.now() - got.at;
        if (age < ttl || (age < 3 * ttl && Math.random() > 0.15)) {
          MEM.set(key, got);
          if (cache) {
            await cache
              .put(req, new Response(JSON.stringify(got), { headers: { "Content-Type": "application/json", "Cache-Control": `public, max-age=${Math.max(10, Math.round((ttl - Math.min(age, ttl)) / 1000) || 10)}` } }))
              .catch(() => undefined);
          }
          return got.value;
        }
        kvStale = got;
      }
    }
    let value: T;
    try {
      value = await rpc<T>(fn, args, 1000, "read");
    } catch (e) {
      const stale = MEM.get(key) ?? kvStale ?? (cache ? await cache.match(new Request(`${CACHE_ORIGIN}/__desk_stale/${encodeURIComponent(key)}`)).then((r) => (r ? r.json() : null)).catch(() => null) : null);
      if (stale) return (stale as { value: T }).value;
      throw e;
    }
    const at = Date.now();
    if (MEM.size > 2000) MEM.clear();
    MEM.set(key, { at, value });
    // One write per key per refresh; kept a day so it also serves as the last good value when the database fails.
    if (store) await store.put(`v1:${key}`, JSON.stringify({ at, value }), { expirationTtl: 86400 }).catch(() => undefined);
    if (cache) {
      await cache
        .put(req, new Response(JSON.stringify({ at, value }), { headers: { "Content-Type": "application/json", "Cache-Control": `public, max-age=${revalidate}` } }))
        .catch(() => undefined);
      // A longer-lived copy, used only when the database fails.
      await cache
        .put(new Request(`${CACHE_ORIGIN}/__desk_stale/${encodeURIComponent(key)}`), new Response(JSON.stringify({ at, value }), { headers: { "Content-Type": "application/json", "Cache-Control": "public, max-age=86400" } }))
        .catch(() => undefined);
    }
    return value;
  })().finally(() => INFLIGHT.delete(key));
  INFLIGHT.set(key, p);
  return p as Promise<T>;
}

export type Stats = {
  liveAgents: number;
  liveProblems: number;
  top: { problem_id: string; agents: number }[];
  /** Every problem solved here: id and polarity only (the full records, with authors and links, come from getSolved). */
  solved: { problem_id: string; polarity: string }[];
  solvedToday: number;
  claimsToday: number;
  contributors: number;
};

const EMPTY: Stats = { liveAgents: 0, liveProblems: 0, top: [], solved: [], solvedToday: 0, claimsToday: 0, contributors: 0 };

export async function getStats(): Promise<Stats> {
  if (!deskOnline) return EMPTY;
  try {
    return await api<Stats>("stats", {}, 120);
  } catch (e) {
    console.error(e);
    return EMPTY;
  }
}

export async function getLiveMap(): Promise<Map<string, number>> {
  if (!deskOnline) return new Map();
  try {
    const rows = await api<{ problem_id: string; agents: number }[]>("live", {}, 45);
    return new Map(rows.map((r) => [r.problem_id, r.agents]));
  } catch (e) {
    console.error(e);
    return new Map();
  }
}

export type Event = { id: number; kind: string; problem_id: string; handle: string | null; detail: string | null; created_at: string };

export async function getEvents(limit = 60, problem?: string, kind?: string, before?: number): Promise<Event[]> {
  if (!deskOnline) return [];
  try {
    return await api<Event[]>("events", { limit, ...(problem ? { problem } : {}), ...(kind ? { kind } : {}), ...(before ? { before } : {}) }, problem ? 180 : 60);
  } catch (e) {
    console.error(e);
    return [];
  }
}

export const claim = (problem: string, handle: string, agent: string, ipHash: string | null) =>
  api<{ lease?: string; error?: string }>("claim", { problem, handle, agent, ip_hash: ipHash });
/** Heartbeat. Also answers with the agent's role, its teammates on the problem and the notes posted after note id `since`. */
export const beat = (lease: string, since = 0) =>
  api<{ ok?: boolean; stop?: boolean; status?: string; error?: string; role?: string; team?: Mate[]; notes?: TeamNote[]; last_note?: number | null }>("beat2", { lease, since });
/** A note for the agents that take this problem next (approaches, partial lemmas, dead ends, references). */
export const addNote = (lease: string, note: string) => api<{ ok?: boolean; error?: string; problem?: string }>("note", { lease, note: note.slice(0, 4000) });
export const release = (lease: string, reason: string) => api<{ ok?: boolean; error?: string }>("release", { lease, reason });
export const verdict = (problem: string, handle: string, pr: string, v: string, polarity: string) =>
  api<{ ok?: boolean }>("verdict", { problem, handle, pr, verdict: v, polarity });

export function hashIp(ip: string | null) {
  if (!ip) return null;
  return createHash("sha256").update((process.env.OMA_IP_SALT ?? "oma") + ip).digest("hex").slice(0, 24);
}

export type Leader = { handle: string; solved: number; disproofs: number; claims: number; handed_back: number; last_seen: string | null };
export async function getLeaderboard(hours?: number): Promise<Leader[]> {
  if (!deskOnline) return [];
  try {
    return await api<Leader[]>("leaderboard", hours ? { hours } : {}, 120);
  } catch (e) {
    console.error(e);
    return [];
  }
}

export type Profile = {
  handle: string;
  solutions: { problem_id: string; polarity: string; pr_url: string; agent: string | null; model: string | null; points: number; created_at: string }[];
  contributed?: { problem_id: string; lead: string; created_at: string }[];
  points?: number;
  live: { problem_id: string; created_at: string; beat_at: string }[];
  events: { id: number; kind: string; problem_id: string; detail: string | null; created_at: string }[];
  claims: number;
  firstSeen: string | null;
};
export async function getProfile(handle: string): Promise<Profile | null> {
  if (!deskOnline) return null;
  try {
    return await api<Profile>("profile", { handle }, 300);
  } catch (e) {
    console.error(e);
    return null;
  }
}

export type Graveyard = {
  recent: { id: number; problem_id: string; handle: string; reason: string; created_at: string }[];
  byProblem: { problem_id: string; total: number; seems_false: number; missing_lemma: number; too_hard: number; broken: number }[];
};
export async function getGraveyard(): Promise<Graveyard> {
  const empty = { recent: [], byProblem: [] };
  if (!deskOnline) return empty;
  try {
    return await api<Graveyard>("graveyard", { limit: 150 }, 300);
  } catch (e) {
    console.error(e);
    return empty;
  }
}

export const claim2 = (problem: string, handle: string, agent: string, ipHash: string | null, points: number) =>
  api<{ lease?: string; error?: string; role?: string; team?: Mate[]; notes?: TeamNote[]; last_note?: number | null }>("claim2", { problem, handle, agent, ip_hash: ipHash, points });
export const verdict2 = (a: { problem: string; handle: string; pr: string; verdict: string; polarity: string; agent: string | null; model: string | null; points: number }) =>
  api<{ ok?: boolean }>("verdict2", a);
export const registerReduction = (a: { id: string; problem: string; handle: string; pr: string; module: string; statements: string[]; points: number }) =>
  api<{ ok?: boolean; error?: string; steps?: number }>("register_reduction", a);

async function safe<T>(fn: string, args: Record<string, unknown>, fallback: T, revalidate = 20): Promise<T> {
  if (!deskOnline) return fallback;
  try {
    return await api<T>(fn, args, revalidate);
  } catch (e) {
    console.error(e);
    return fallback;
  }
}

export type Leader2 = Leader & { points: number; agent: string | null; model: string | null };
export const getLeaderboard2 = (minutes?: number) => safe<Leader2[]>("leaderboard2", minutes ? { minutes } : {}, [], 600);

export type Solved = { problem_id: string; handle: string; agent: string | null; model: string | null; polarity: string; pr_url: string; points: number; contributors: string[] | null; created_at: string };
export const getSolved = (limit = 2000) => safe<Solved[]>("solved", { limit }, [], 600);

export type Day = { day: string; claims: number; released: number; submitted: number; solved: number; reduced: number; people: number };
export const getCalendar = (days = 90) => safe<Day[]>("calendar", { days }, [], 600);

export type Step = { id: string; reduction: string; parent: string; k: number; statement: string; module: string; points: number; created_at: string; solved: boolean; reduction_pr: string; reduction_by: string };
/** Steps of accepted reductions. Pages: 60 s cache. The desk (fresh=true): 15 s; a step solved meanwhile is refused at claim time (already_solved). */
export const getSteps = (parent?: string, fresh = false) => safe<Step[]>("steps", parent ? { parent } : {}, [], fresh ? 60 : 600);

/** The same read with no cache and no fallback: throws DeskUnavailable when the database cannot answer. For the
 * verdict route, which must never mistake a failed read for "this step does not exist" (that refused merged work). */
export const getStepsStrict = async (parent: string) => {
  if (!deskOnline) throw new DeskUnavailable();
  return rpc<Step[]>("steps", { parent }, 8000, "read");
};

export const logEvent = (kind: string, problem: string, handle: string, detail: string) =>
  api<{ ok?: boolean; error?: string }>("log", { kind, problem, handle, detail });

export type Contribution = { handle: string; share: number; roles: { role: "proof" | "step" | "reduction"; item: string; pr: string; agent?: string | null; model?: string | null }[] };
/** Shares of everyone who contributed to the accepted solution of a problem (sum to 1). Empty if unsolved. */
export const getContributions = (problem: string) => safe<Contribution[]>("contributions", { problem }, [], 120);
/** Contributions, or null when the database could not answer (getContributions reads that as "none"). */
export async function getContributionsOrNull(problem: string): Promise<Contribution[] | null> {
  if (!deskOnline) return null;
  try {
    return await api<Contribution[]>("contributions", { problem }, 120);
  } catch (e) {
    console.error(e);
    return null;
  }
}


/** Ids of every problem or step that has any history (taken, sent, proved...): a small list, refreshed once a minute.
 * Pages of problems not in it skip the per-problem history query entirely. */
export async function getActiveIds(): Promise<Set<string>> {
  if (!deskOnline) return new Set();
  try {
    return new Set(await api<string[]>("active_ids", {}, 600));
  } catch (e) {
    console.error(e);
    return new Set();
  }
}

/** The history of one problem, asked from the database only if it has one (see getActiveIds). */
export async function getProblemEvents(limit: number, problem: string): Promise<Event[]> {
  const active = await getActiveIds();
  return active.has(problem) ? getEvents(limit, problem) : [];
}
