/**
 * Supporters: people who gave money to keep the site running. They get a "Supporter" badge on their profile and on the
 * leaderboard. Sources: content/supporters.json (by hand) and Workers KV, filled by the Ko-fi and GitHub Sponsors
 * webhooks (app/api/kofi, app/api/github-sponsors). Only a GitHub handle, a date and the channel are kept: no amount,
 * no name, no email.
 */
import { env as cfEnv } from "cloudflare:workers";
import manual from "@/content/supporters.json";

export type Supporter = { handle: string; since: string; via: "Ko-fi" | "GitHub Sponsors" | "by hand"; monthly?: boolean };
type KV = { get(k: string, o: { type: "json"; cacheTtl?: number }): Promise<unknown>; put(k: string, v: string): Promise<void> };
const KEY = "supporters:v1";
export const HANDLE_RE = /^[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})$/;

function kv(): KV | null {
  try {
    return ((cfEnv as unknown as { DESK_KV?: KV }).DESK_KV) ?? null;
  } catch {
    return null;
  }
}

/** A secret set on the Worker (dashboard or API), read from the binding or from process.env. */
export function workerSecret(name: string): string {
  try {
    const v = (cfEnv as unknown as Record<string, unknown>)[name];
    if (typeof v === "string" && v) return v;
  } catch { /* not on Workers */ }
  return process.env[name] ?? "";
}

let mem: { at: number; map: Map<string, Supporter> } | null = null;

async function stored(): Promise<Supporter[]> {
  try {
    return ((await kv()?.get(KEY, { type: "json", cacheTtl: 60 })) as Supporter[] | null) ?? [];
  } catch {
    return [];
  }
}

/** Every supporter, keyed by lower-case handle (cached a minute per isolate). */
export async function getSupporters(): Promise<Map<string, Supporter>> {
  if (mem && Date.now() - mem.at < 60_000) return mem.map;
  const map = new Map<string, Supporter>();
  const hand = ((manual as { supporters?: Supporter[] }).supporters ?? []).map((s) => ({ ...s, via: s.via ?? "by hand" }));
  for (const s of [...hand, ...(await stored())]) {
    if (!s?.handle || !HANDLE_RE.test(s.handle)) continue;
    const k = s.handle.toLowerCase(), prev = map.get(k);
    if (!prev || s.since < prev.since) map.set(k, { ...s, monthly: Boolean(s.monthly || prev?.monthly) });
    else if (s.monthly) prev.monthly = true;
  }
  mem = { at: Date.now(), map };
  return map;
}

/** Adds (or refreshes) a supporter in KV. */
export async function addSupporter(s: Supporter): Promise<boolean> {
  const store = kv();
  if (!store || !HANDLE_RE.test(s.handle)) return false;
  const list = await stored();
  const i = list.findIndex((x) => x.handle.toLowerCase() === s.handle.toLowerCase());
  if (i >= 0) list[i] = { ...list[i], monthly: Boolean(list[i].monthly || s.monthly) };
  else list.push(s);
  await store.put(KEY, JSON.stringify(list));
  mem = null;
  return true;
}

/** The GitHub handle a donor wrote in a Ko-fi message: "@handle", "github: handle" or "gh handle". */
export function handleFromMessage(msg: string): string | null {
  const m = msg.match(/\b(?:github|gh)(?:\s+(?:handle|username|user|name|account|login|is))*\s*[:=]?\s*@?([A-Za-z0-9](?:[A-Za-z0-9-]{0,38}))\b/i) ?? msg.match(/(?:^|\s)@([A-Za-z0-9](?:[A-Za-z0-9-]{0,38}))\b/);
  return m ? m[1] : null;
}

/** The canonical spelling of a GitHub login, or null if there is no such user. */
export async function githubLogin(handle: string): Promise<string | null> {
  if (!HANDLE_RE.test(handle)) return null;
  const r = await fetch(`https://api.github.com/users/${encodeURIComponent(handle)}`, { headers: { "User-Agent": "left-to-solve", Accept: "application/vnd.github+json" } }).catch(() => null);
  if (!r || !r.ok) return null;
  const j = (await r.json().catch(() => null)) as { login?: string; type?: string } | null;
  return j?.login && j.type !== "Organization" ? j.login : j?.login ?? null;
}

export function safeEqual(a: string, b: string): boolean {
  if (!a || !b || a.length !== b.length) return false;
  let d = 0;
  for (let i = 0; i < a.length; i++) d |= a.charCodeAt(i) ^ b.charCodeAt(i);
  return d === 0;
}
