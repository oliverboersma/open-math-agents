import "server-only";
import { REPO } from "@/lib/site";

/**
 * Verifies a GitHub Actions OIDC token: proof that a request comes from this repository's trusted verdict workflow
 * on main (it never runs pull request code). With it the site can take the pull request data the workflow read with
 * its own token, instead of asking the GitHub API anonymously (60 requests an hour, shared by every Cloudflare IP).
 */
const ISS = "https://token.actions.githubusercontent.com";
export const OIDC_AUDIENCE = "lefttosolve.com";
// The two trusted workflows that merge and credit (neither ever runs pull request code).
const WORKFLOWS = new Set(["verdict.yml", "backlog.yml"].map((w) => `${REPO}/.github/workflows/${w}@refs/heads/main`));

const unb64u = (s: string) => Uint8Array.from(atob(s.replace(/-/g, "+").replace(/_/g, "/") + "===".slice((s.length + 3) % 4)), (c) => c.charCodeAt(0));
const keys = new Map<string, CryptoKey>();
let fetchedAt = 0;

async function key(kid: string): Promise<CryptoKey | null> {
  if (keys.has(kid)) return keys.get(kid)!;
  if (Date.now() - fetchedAt < 60_000) return null; // unknown kid: refetch at most once a minute
  fetchedAt = Date.now();
  const res = await fetch(`${ISS}/.well-known/jwks`, { cache: "no-store" });
  if (!res.ok) return null;
  const { keys: list } = (await res.json()) as { keys: (JsonWebKey & { kid: string })[] };
  for (const k of list) {
    if (k.kty !== "RSA") continue;
    keys.set(k.kid, await crypto.subtle.importKey("jwk", { kty: "RSA", n: k.n, e: k.e, alg: "RS256", ext: true }, { name: "RSASSA-PKCS1-v1_5", hash: "SHA-256" }, false, ["verify"]));
  }
  return keys.get(kid) ?? null;
}

/** The token's claims if it is a valid token of the verdict workflow on main; null otherwise. */
export async function verifyWorkflowToken(jwt: unknown): Promise<Record<string, unknown> | null> {
  if (typeof jwt !== "string" || jwt.length > 8000) return null;
  const parts = jwt.split(".");
  if (parts.length !== 3) return null;
  try {
    const header = JSON.parse(new TextDecoder().decode(unb64u(parts[0])));
    if (header.alg !== "RS256" || typeof header.kid !== "string") return null;
    const k = await key(header.kid);
    if (!k) return null;
    const ok = await crypto.subtle.verify("RSASSA-PKCS1-v1_5", k, unb64u(parts[2]), new TextEncoder().encode(`${parts[0]}.${parts[1]}`));
    if (!ok) return null;
    const c = JSON.parse(new TextDecoder().decode(unb64u(parts[1])));
    const now = Date.now() / 1000;
    const aud = Array.isArray(c.aud) ? c.aud : [c.aud];
    if (c.iss !== ISS || !aud.includes(OIDC_AUDIENCE) || !(c.exp > now) || (c.nbf && c.nbf > now + 60)) return null;
    if (c.repository !== REPO || !WORKFLOWS.has(c.workflow_ref) || c.ref !== "refs/heads/main") return null;
    return c;
  } catch {
    return null;
  }
}
