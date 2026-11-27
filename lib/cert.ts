import "server-only";
import keyInfo from "@/public/certificate-key.json";
import { getProblem, KIND_LABEL } from "@/lib/catalog";
import { getContributions, getContributionsOrNull, getSolved, type Contribution, type Solved } from "@/lib/db";
import { SITE } from "@/lib/site";

/**
 * Contribution certificates. Each one is a JSON object signed with the site's Ed25519 key: anyone can check it with
 * the public key at /certificate-key.json, and changing a single character (a name, a percentage) breaks the
 * signature. The facts behind it are public too: the merged pull requests on GitHub and the Lean check.
 */
export type Certificate = {
  type: "left-to-solve/contribution-certificate";
  version: 1;
  issuer: string;
  keyId: string;
  problem: { id: string; title: string; kind: string; url: string };
  result: "proof" | "disproof";
  firstSolution: boolean;
  solvedAt: string;
  holder: { handle: string; github: string; sharePercent: number; roles: { role: string; item: string; pr: string; agent: string | null; model: string | null }[] };
  contributors: { handle: string; sharePercent: number }[];
  checkedBy: string;
};
export type Signed = { certificate: Certificate; id: string; signature: string; algorithm: "Ed25519"; publicKey: string; verify: string };

/** Canonical JSON: keys sorted at every level, no whitespace. This exact string is what gets signed. */
export function canonical(v: unknown): string {
  if (v === null || typeof v !== "object") return JSON.stringify(v);
  if (Array.isArray(v)) return `[${v.map(canonical).join(",")}]`;
  return `{${Object.keys(v as Record<string, unknown>).sort().map((k) => `${JSON.stringify(k)}:${canonical((v as Record<string, unknown>)[k])}`).join(",")}}`;
}

const b64u = (b: ArrayBuffer | Uint8Array) => btoa(String.fromCharCode(...new Uint8Array(b instanceof Uint8Array ? b : new Uint8Array(b)))).replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/, "");
const unb64u = (s: string) => Uint8Array.from(atob(s.replace(/-/g, "+").replace(/_/g, "/") + "===".slice((s.length + 3) % 4)), (c) => c.charCodeAt(0));
const pct = (x: number) => Math.round(x * 10000) / 100;

let signKey: CryptoKey | null = null;
async function signingKey() {
  if (signKey) return signKey;
  const raw = process.env.CERT_SIGNING_KEY;
  if (!raw) throw new Error("CERT_SIGNING_KEY missing");
  signKey = await crypto.subtle.importKey("pkcs8", Uint8Array.from(atob(raw), (c) => c.charCodeAt(0)), { name: "Ed25519" }, false, ["sign"]);
  return signKey;
}
let verifyKey: CryptoKey | null = null;
async function publicKey() {
  if (!verifyKey) verifyKey = await crypto.subtle.importKey("raw", unb64u(keyInfo.publicKey), { name: "Ed25519" }, false, ["verify"]);
  return verifyKey;
}

export async function certificateId(cert: Certificate) {
  const h = new Uint8Array(await crypto.subtle.digest("SHA-256", new TextEncoder().encode(canonical(cert))));
  return Array.from(h.slice(0, 8), (b) => b.toString(16).padStart(2, "0")).join("").toUpperCase().match(/.{4}/g)!.join("-");
}

/** Everyone credited on a solved problem, with shares; null when the problem is not solved here. */
export async function contributorsOf(problemId: string): Promise<Contribution[] | null> {
  const list = await getContributions(problemId);
  return list.length ? list : null;
}

/** Thrown by certificateFor when the shares cannot be read now (database down): the solution itself is known. */
export class CertificateUnavailable extends Error {
  constructor(public solution: Solved) {
    super("certificate_unavailable");
  }
}

/** The signed certificate of one contributor, or null if this person did not contribute to a solution of it.
 * Throws CertificateUnavailable when the problem is solved and credits this person, but the shares cannot be read. */
export async function certificateFor(problemId: string, handle: string): Promise<Signed | null> {
  const [contribRead, solved] = await Promise.all([getContributionsOrNull(problemId), getSolved()]);
  const sol = solved.find((s) => s.problem_id === problemId);
  const credited = sol && [sol.handle, ...(sol.contributors ?? [])].some((h) => h.toLowerCase() === handle.toLowerCase());
  if (contribRead === null && sol && credited) throw new CertificateUnavailable(sol);
  const contrib = contribRead?.length ? contribRead : null;
  const me = contrib?.find((c) => c.handle.toLowerCase() === handle.toLowerCase());
  if (!contrib || !me || !sol) return null;
  const p = getProblem(problemId);
  const certificate: Certificate = {
    type: "left-to-solve/contribution-certificate",
    version: 1,
    issuer: SITE.replace(/^https?:\/\//, ""),
    keyId: keyInfo.keyId,
    problem: { id: problemId, title: p?.title ?? problemId, kind: p ? KIND_LABEL[p.kind] : "step of a reduction", url: `${SITE}/p/${encodeURIComponent(problemId)}` },
    result: sol.polarity === "disproof" ? "disproof" : "proof",
    firstSolution: p?.kind === "open",
    solvedAt: sol.created_at,
    holder: {
      handle: me.handle, github: `https://github.com/${me.handle}`, sharePercent: pct(me.share),
      roles: me.roles.map((r) => ({ role: r.role, item: r.item, pr: r.pr.replace(/#closed$/, ""), agent: r.agent ?? null, model: r.model ?? null })),
    },
    contributors: contrib.map((c) => ({ handle: c.handle, sharePercent: pct(c.share) })),
    checkedBy: "Lean 4 kernel (Left to Solve checker; axioms limited to propext, Classical.choice, Quot.sound)",
  };
  const sig = await crypto.subtle.sign({ name: "Ed25519" }, await signingKey(), new TextEncoder().encode(canonical(certificate)));
  return { certificate, id: await certificateId(certificate), signature: b64u(sig), algorithm: "Ed25519", publicKey: keyInfo.publicKey, verify: `${SITE}/verify` };
}

/** Checks a certificate against the published public key. */
export async function verifySigned(s: { certificate: unknown; signature: string }): Promise<boolean> {
  try {
    return await crypto.subtle.verify({ name: "Ed25519" }, await publicKey(), unb64u(s.signature), new TextEncoder().encode(canonical(s.certificate)));
  } catch {
    return false;
  }
}

export const ROLE_LABEL: Record<string, string> = {
  proof: "Proved the theorem",
  step: "Proved a step of a reduction",
  reduction: "Split the problem into steps that, together, prove it",
};
