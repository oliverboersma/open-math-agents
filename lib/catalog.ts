import "server-only";
import PLACEHOLDERS from "@/data/placeholders.json";
import THIRD_PARTY from "@/content/prizes.json";
import cardsRaw from "@/data/gen/cards.json";
import overridesRaw from "@/data/status_overrides.json";
import { catalogSearch, problemDetail, problemDetails, excerpts } from "@/lib/d1";

/** open/known/warmup: has a Lean statement, provable now. unformalized: open, but nobody has stated it in Lean yet. */
export type Kind = "open" | "known" | "warmup" | "unformalized";

/**
 * What every list, filter and sort needs: kept in memory for all ~24k problems (about 10 MB of heap).
 * Full statements, Lean sources and references live in D1 (see FullProblem / getFull), because a Cloudflare Worker
 * has 128 MB of memory and the whole catalogue plus a search index did not fit.
 */
export type Problem = {
  id: string;
  title: string;
  source: string;
  kind: Kind;
  fields: string[];
  tags: string[];
  difficulty: number;
  /** How well known the problem is, 0-100: the default order, most famous first. */
  fame: number;
  prize: string | null;
  forumPosts: number;
  erdos: number | null;
  decl: string;
  /** Where the details live in D1: 0 the core tables, 1 the packed MathOverflow tables. */
  shard: number;
  /** A solution has been announced but is not verified (or is disputed). */
  claim?: { summary: string; date: string; sources: string[] };
  /** Editorial note (e.g. why a related result does not settle this one). */
  note?: { summary: string; sources: string[] };
};

/** A problem with everything the catalogue knows about it, read from D1. */
export type FullProblem = Problem & {
  statement: string;
  lean: string;
  module: string;
  file: string;
  line: number;
  category: string;
  ref: string | null;
  erdosState: string | null;
  license?: string;
  authors?: string[];
  area?: string;
  alsoIn?: string[];
  formalizedHere?: boolean;
};

export type Override = { id: string; status: "solved" | "claimed" | "open"; title?: string; summary: string; date: string; sources: string[] };
const OVERRIDES = (overridesRaw as unknown as { reviewed: string; entries: Override[] }).entries;
export const STATUS_REVIEWED = (overridesRaw as unknown as { reviewed: string }).reviewed;
const OV = new Map(OVERRIDES.map((o) => [o.id, o]));

type CardRow = [string, string, number, number, string[], string[], number, number, string | null, number, number | null, string, number];
const cards = cardsRaw as unknown as {
  meta: { upstream: string; upstreamCommit: string; license: string; counts: Record<"open" | "known" | "warmup", number>; total: number; extra: unknown; extra2: unknown; extra3: unknown; moBuckets: number };
  sources: string[]; kinds: Kind[]; rows: CardRow[];
};

// Identical field lists share one array (46k problems, a few hundred distinct lists): saves several MB of heap.
const FIELD_LISTS = new Map<string, string[]>();
const NO_TAGS: string[] = [];
const ALL: Problem[] = cards.rows.map(([id, title, si, ki, fields, , difficulty, fame, prize, forumPosts, erdos, decl, shard]) => {
  const key = fields.join("|");
  let f = FIELD_LISTS.get(key);
  if (!f) { f = fields; FIELD_LISTS.set(key, f); }
  return { id, title, source: cards.sources[si], kind: cards.kinds[ki], fields: f, tags: NO_TAGS, difficulty, fame, prize, forumPosts, erdos, decl, shard };
});
export const MO_BUCKETS = cards.meta.moBuckets;
// The parsed rows are not needed any more: let them be garbage-collected (only ALL is used from here on).
(cards as { rows: CardRow[] | null }).rows = null;

/** Problems settled recently (verified), removed from the open list and shown on /status. */
export const SETTLED: (Override & { problem?: Problem })[] = OVERRIDES.filter((o) => o.status === "solved").map((o) => ({ ...o, problem: ALL.find((p) => p.id === o.id) }));
/** Problems with an announced but unverified solution: kept, flagged, ranked lower. */
export const CLAIMED: Override[] = OVERRIDES.filter((o) => o.status === "claimed");

export const PROBLEMS: Problem[] = ALL.filter((p) => OV.get(p.id)?.status !== "solved").map((p) => {
  const o = OV.get(p.id);
  if (!o) return p;
  if (o.status === "claimed") return { ...p, fame: Math.max(1, p.fame - 30), claim: { summary: o.summary, date: o.date, sources: o.sources } };
  return { ...p, title: o.title ?? p.title, note: { summary: o.summary, sources: o.sources } };
});
const count = (k: Kind) => PROBLEMS.filter((p) => p.kind === k).length;
export const META = {
  upstream: cards.meta.upstream,
  upstreamCommit: cards.meta.upstreamCommit,
  license: cards.meta.license,
  counts: { open: count("open"), known: count("known"), warmup: count("warmup"), unformalized: count("unformalized") } as Record<Kind, number>,
  total: PROBLEMS.length,
  extra: cards.meta.extra,
  extra2: cards.meta.extra2,
  extra3: cards.meta.extra3,
};
/** Every open problem, stated in Lean or not. */
export const OPEN_TOTAL = META.counts.open + META.counts.unformalized;
const BY_ID = new Map(PROBLEMS.map((p) => [p.id, p]));

export const KIND_LABEL: Record<Kind, string> = {
  open: "Open problem: find a proof",
  known: "Known result: formalize the existing proof",
  warmup: "Warm-up exercise",
  unformalized: "Open, needs a Lean statement first",
};

/** What the person (or agent) is asked to do, in one sentence, by kind. Shown at the top of every problem page. */
export const TASK: Record<Kind | "step", { title: string; text: string }> = {
  open: { title: "Your task: find a proof (or a disproof)", text: "Nobody has proved this yet. A proof accepted by Lean here is a new result, once its formal statement has been checked against the original problem." },
  known: { title: "Your task: formalize an existing proof", text: "This result is already proved in the mathematical literature (see the references). What is missing is a machine-checked proof in Lean: useful formalization work, not a new discovery." },
  warmup: { title: "Your task: a warm-up exercise", text: "A textbook result, to check that your Lean setup and the submission pipeline work. It earns few points." },
  unformalized: { title: "Your task: write the Lean statement first", text: "This open problem has no formal statement yet, so no proof can be checked. Writing a faithful Lean statement is the first step, and it is credited." },
  step: { title: "Your task: prove this step", text: "One hypothesis of a reduction of a bigger problem: proving it brings the parent problem closer." },
};

export const isProvable = (p: Problem) => p.kind !== "unformalized";

export function getProblem(id: string) {
  return BY_ID.get(id);
}

/** The problem with its statement, Lean source and references (one D1 read). */
export async function getFull(id: string): Promise<FullProblem | undefined> {
  const p = BY_ID.get(id);
  if (!p) return undefined;
  const d = await problemDetail(p, MO_BUCKETS).catch(() => problemDetail(p, MO_BUCKETS)).catch((e) => {
    // D1 failed twice: the page still renders from the in-memory card (title, kind, source) instead of a 500.
    console.error("getFull", id, e);
    return null;
  });
  return {
    statement: "", lean: "", module: "", file: "", line: 0, category: p.kind === "unformalized" ? "unformalized" : "", ref: null, erdosState: null,
    ...(d as Partial<FullProblem>), ...p,
  };
}

/** Full data for several problems at once (one or two D1 queries instead of one per problem). */
export async function getFullMany(ids: string[]): Promise<FullProblem[]> {
  const ps = ids.map((id) => BY_ID.get(id)).filter((p): p is Problem => Boolean(p));
  const d = await problemDetails(ps, MO_BUCKETS).catch(() => problemDetails(ps, MO_BUCKETS)).catch((e) => {
    console.error("getFullMany", e);
    return new Map<string, Record<string, unknown>>();
  });
  return ps.map((p) => ({
    statement: "", lean: "", module: "", file: "", line: 0, category: p.kind === "unformalized" ? "unformalized" : "", ref: null, erdosState: null,
    ...(d.get(p.id) as Partial<FullProblem>), ...p,
  }));
}

export const SOURCES = Array.from(new Set(PROBLEMS.map((p) => p.source))).sort();
export const FIELDS = Array.from(new Set(PROBLEMS.flatMap((p) => p.fields))).sort();

export type Query = {
  q?: string;
  kind?: string;
  source?: string;
  field?: string;
  sort?: "relevance" | "famous" | "hardest" | "easiest" | "prize" | "active";
  limit?: number;
  offset?: number;
  live?: Map<string, number>;
  solved?: Set<string>;
  hideSolved?: boolean;
};

/** Clay Millennium Prize problems in the catalogue: $1,000,000 each from the Clay Mathematics Institute, under its rules. */
export const CLAY: Record<string, string> = {
  "ComplexityTheory.P_ne_NP": "P vs NP",
  "NavierStokes.navier_stokes_existence_and_smoothness_R3": "Navier–Stokes existence and smoothness",
  "NavierStokes.navier_stokes_existence_and_smoothness_periodic": "Navier–Stokes existence and smoothness",
  "WeierstrassCurve.Affine.Rat.weakBSD": "Birch and Swinnerton-Dyer conjecture",
  "WeierstrassCurve.Affine.Rat.strongBSD": "Birch and Swinnerton-Dyer conjecture",
  "wp-birch-and-swinnerton-dyer-conjecture": "Birch and Swinnerton-Dyer conjecture",
  "wp-hodge-conjecture": "Hodge conjecture",
  "wpc-yang-mills-existence-and-mass-gap": "Yang–Mills existence and mass gap",
};
export const CLAY_RULES = "https://www.claymath.org/millennium-problems/rules/";

export type Prize = { usd: number; label: string; by: string; claim: string; url: string };
/** Cash prize attached to a problem by a third party (never paid by this site). */
export function prizeOf(p: Problem): Prize | null {
  // A prize is a target only while the problem is open.
  if (!(p.kind === "open" || p.kind === "unformalized")) return null;
  if (CLAY[p.id]) return { usd: 1_000_000, label: "$1,000,000", by: "the Clay Mathematics Institute (Millennium Prize)", claim: "Clay awards it under its rules: a solution published in a refereed venue and accepted by the community two years later", url: CLAY_RULES };
  const tp = (THIRD_PARTY.prizes as Record<string, Prize>)[p.id];
  if (tp) return tp;
  if (!p.prize) return null;
  const m = p.prize.replace(/,/g, "").match(/[$£](\d+)/);
  const usd = m ? Number(m[1]) : 0;
  const url = p.erdos ? `https://www.erdosproblems.com/${p.erdos}` : "https://www.erdosproblems.com/prizes";
  // Upstream, every variant of an Erdős problem carries the problem's prize. The prize is for the main problem: a
  // variant (special case) does not win it by itself, so it is shown as such and not counted in totals.
  if (/\.variants?\./.test(p.id)) {
    return { usd: 0, label: `${p.prize} (main problem)`, by: `Paul Erdős (Erdős prize for Erdős Problem #${p.erdos ?? "?"} as a whole)`, claim: "This variant is a special case: solving it does not by itself win the prize, which is attached to the main problem", url };
  }
  return { usd, label: p.prize, by: "Paul Erdős (Erdős prize)", claim: "erdosproblems.com records each prize and who honours it today", url };
}
export function prizeValue(p: Problem) {
  return prizeOf(p)?.usd ?? 0;
}
/** Open problems with a cash prize, biggest first (variants of one Erdős problem counted once in the totals). */
export function prizeBoard() {
  const list = PROBLEMS.filter((p) => (p.kind === "open" || p.kind === "unformalized") && prizeValue(p) > 0).sort((a, b) => prizeValue(b) - prizeValue(a) || b.fame - a.fame);
  const clay = new Set(list.filter((p) => CLAY[p.id]).map((p) => CLAY[p.id]));
  const erdos = new Map<number, number>();
  for (const p of list) if (p.erdos && !CLAY[p.id]) erdos.set(p.erdos, Math.max(erdos.get(p.erdos) ?? 0, prizeValue(p)));
  return { list, clayCount: clay.size, erdosCount: erdos.size, erdosTotal: Array.from(erdos.values()).reduce((a, b) => a + b, 0), erdosMax: Math.max(0, ...erdos.values()) };
}

/** Search and filter. Text queries go to the D1 full-text index (titles weigh most); filters and sorts run in memory. */
export async function search(query: Query) {
  let list: Problem[];
  const q = query.q?.trim();
  const erdos = q?.match(/^erd(?:o|ő|oe)s\s*#?\s*(\d+)$/i);
  if (erdos) {
    list = PROBLEMS.filter((p) => p.erdos === Number(erdos[1]));
  } else if (q) {
    // BM25 order from D1, then lifted by fame and by an exact title match, so "collatz" puts the Collatz
    // conjecture above forum questions that mention it ten times.
    const hits = (await catalogSearch(q)).map((id) => BY_ID.get(id)!).filter(Boolean);
    const words = q.toLowerCase().normalize("NFKD").replace(/[\u0300-\u036f]/g, "").match(/[\p{L}\p{N}]+/gu) ?? [];
    const plainTitle = (t: string) => t.toLowerCase().normalize("NFKD").replace(/[\u0300-\u036f]/g, "");
    const score = new Map(hits.map((p, i) => {
      const t = plainTitle(p.title);
      const inTitle = words.length > 0 && words.every((w) => t.includes(w));
      return [p.id, 0.5 * (1 - i / hits.length) + 0.35 * (p.fame / 100) + (inTitle ? 0.4 : 0)];
    }));
    list = hits;
    if ((query.sort ?? "relevance") === "relevance") list = [...hits].sort((a, b) => score.get(b.id)! - score.get(a.id)!);
  } else {
    list = PROBLEMS.slice();
  }
  if (query.kind && query.kind !== "all") list = list.filter((p) => p.kind === query.kind);
  if (query.source && query.source !== "all") list = list.filter((p) => p.source === query.source);
  if (query.field && query.field !== "all") list = list.filter((p) => p.fields.includes(query.field!));
  if (query.hideSolved && query.solved) list = list.filter((p) => !query.solved!.has(p.id));
  const sort = query.sort ?? (q ? "relevance" : "famous");
  if (sort === "famous") list.sort((a, b) => b.fame - a.fame || b.difficulty - a.difficulty || a.id.localeCompare(b.id));
  if (sort === "hardest") list.sort((a, b) => b.difficulty - a.difficulty || a.id.localeCompare(b.id));
  if (sort === "easiest") list.sort((a, b) => a.difficulty - b.difficulty || a.id.localeCompare(b.id));
  if (sort === "prize") list.sort((a, b) => prizeValue(b) - prizeValue(a) || b.difficulty - a.difficulty);
  if (sort === "active" && query.live) {
    const live = query.live;
    list.sort((a, b) => (live.get(b.id) ?? 0) - (live.get(a.id) ?? 0) || b.difficulty - a.difficulty);
  }
  const total = list.length;
  const offset = Math.max(0, query.offset ?? 0);
  const limit = Math.min(200, Math.max(1, query.limit ?? 30));
  return { total, items: list.slice(offset, offset + limit) };
}

const TEX: Record<string, string> = {
  mathbb: "", mathbf: "", mathrm: "", mathcal: "", operatorname: "", text: "", textrm: "", mathfrak: "",
  le: "≤", leq: "≤", ge: "≥", geq: "≥", ne: "≠", neq: "≠", in: "∈", notin: "∉", subset: "⊂", subseteq: "⊆",
  cup: "∪", cap: "∩", infty: "∞", to: "→", rightarrow: "→", mapsto: "↦", times: "×", cdot: "·", cdots: "…", ldots: "…", dots: "…",
  sum: "∑", prod: "∏", int: "∫", sqrt: "√", log: "log", exp: "exp", lim: "lim", liminf: "liminf", limsup: "limsup", sim: "∼",
  approx: "≈", ll: "≪", gg: "≫", forall: "∀", exists: "∃", neg: "¬", land: "∧", lor: "∨", mid: "|", lvert: "|", rvert: "|", vert: "|",
  alpha: "α", beta: "β", gamma: "γ", delta: "δ", epsilon: "ε", varepsilon: "ε", zeta: "ζ", eta: "η", theta: "θ", lambda: "λ",
  mu: "μ", nu: "ν", pi: "π", rho: "ρ", sigma: "σ", tau: "τ", phi: "φ", varphi: "φ", chi: "χ", psi: "ψ", omega: "ω",
  Gamma: "Γ", Delta: "Δ", Lambda: "Λ", Sigma: "Σ", Phi: "Φ", Omega: "Ω", left: "", right: "", lfloor: "⌊", rfloor: "⌋",
  lceil: "⌈", rceil: "⌉", binom: "binom", frac: "", pmod: "mod", bmod: "mod", equiv: "≡", setminus: "∖", emptyset: "∅",
};
const BB: Record<string, string> = { N: "ℕ", Z: "ℤ", Q: "ℚ", R: "ℝ", C: "ℂ", P: "ℙ", F: "𝔽" };

/** Rough TeX → Unicode for one-line excerpts (the problem page renders real KaTeX). */
export function texPlain(s: string) {
  return s
    .replace(/\\mathbb\s*\{?([A-Z])\}?/g, (_, c) => BB[c] ?? c)
    .replace(/\\frac\s*\{([^{}]*)\}\s*\{([^{}]*)\}/g, "($1)/($2)")
    .replace(/\\([A-Za-z]+)/g, (m, w) => (w in TEX ? TEX[w] : w))
    .replace(/\\[,;!: ]/g, " ")
    .replace(/[{}$*`]/g, "")
    .replace(/\s+/g, " ")
    .trim();
}

/** Compact card shape sent to the browser. The excerpt comes from D1 (see withExcerpts). */
export function toCard(p: Problem, excerpt = "") {
  return {
    claimed: Boolean(p.claim),
    id: p.id,
    title: p.title,
    source: p.source,
    kind: p.kind,
    fields: p.fields,
    difficulty: p.difficulty,
    prize: p.prize,
    excerpt,
  };
}
export type Card = ReturnType<typeof toCard>;

/** Cards for the rows a page shows, with their excerpt (one or two D1 queries for the whole page). */
export async function withExcerpts(ps: Problem[]): Promise<Card[]> {
  const ex = await excerpts(ps, MO_BUCKETS);
  return ps.map((p) => toCard(p, texPlain(ex.get(p.id) ?? "").slice(0, 200)));
}

/** The Lean skeleton an agent fills in. `type_of%` pins the exact upstream statement. */
/** Problems that ask for a value: their statement depends on a placeholder defined as `sorry` upstream. */
export const answerPlaceholder = (id: string): string | null => (PLACEHOLDERS as Record<string, string[]>)[id]?.[0] ?? null;

export function skeleton(p: FullProblem, polarity: "proof" | "disproof" = "proof", handle = "<your GitHub handle>") {
  const ph = answerPlaceholder(p.id);
  if (ph) {
    // The upstream statement contains `${ph}`, defined as `sorry`: supply the value and prove the statement with it.
    return [
      `import ${p.module}`,
      ``,
      `-- Problem: ${p.title} (it asks for a value)`,
      `-- Upstream: formal-conjectures ${p.file}:${p.line} (declaration ${p.decl}; placeholder ${ph} := sorry)`,
      `-- Credit: @${handle} (the owner of the agent is credited as the solver)`,
      `-- Give the value explicitly as OMA.answer (same type as the placeholder; not built from ${p.decl.split(".")[0]}.…,`,
      `-- no choice / infimum / supremum of the quantity asked for), then prove the statement with the placeholder`,
      `-- replaced by it: start with \`intro h; rw [h]\`. No sorry, no axiom, no native_decide. A person checks the answer.`,
      ``,
      `noncomputable def OMA.answer := sorry -- write its type (copy the placeholder's) and the explicit value`,
      ``,
      `theorem OMA.solution : ${ph} = OMA.answer → type_of% @${p.decl} := by`,
      `  intro h`,
      `  rw [h]`,
      `  sorry`,
      ``,
    ].join("\n");
  }
  const target = polarity === "proof" ? `type_of% @${p.decl}` : `¬ (type_of% @${p.decl})`;
  return [
    `import ${p.module}`,
    ``,
    `-- Problem: ${p.title}`,
    `-- Upstream: formal-conjectures ${p.file}:${p.line} (declaration ${p.decl})`,
    `-- Credit: @${handle} (the owner of the agent is credited as the solver)`,
    `-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.`,
    ``,
    `theorem OMA.${polarity === "proof" ? "solution" : "disproof"} : ${target} := by`,
    `  sorry`,
    ``,
  ].join("\n");
}

/** Skeleton of a reduction: 2 to 4 smaller statements that together imply the target. */
export function reductionSkeleton(p: FullProblem, n = 1, handle = "<your GitHub handle>") {
  const ns = "OMA.R_" + `${p.id}.R${n}`.replace(/[^A-Za-z0-9]/g, "_");
  return [
    `import ${p.module}`,
    ``,
    `-- Reduction ${p.id}.R${n} of ${p.title}`,
    `-- Credit: @${handle}`,
    `-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.`,
    ``,
    `namespace ${ns}`,
    ``,
    `def H1 : Prop := sorry -- a smaller statement`,
    ``,
    `def H2 : Prop := sorry -- another one`,
    ``,
    `theorem main : H1 → H2 → type_of% @${p.decl} := by`,
    `  sorry`,
    ``,
    `end ${ns}`,
    ``,
  ].join("\n");
}

/** Skeleton of a Lean statement for a problem that has none. Reviewed by a person before it is merged. */
export function statementSkeleton(p: FullProblem, handle = "<your GitHub handle>") {
  const ns = "OMA.S_" + p.id.replace(/[^A-Za-z0-9]/g, "_");
  return [
    `import Mathlib`,
    ``,
    `/-!`,
    `# ${p.title}`,
    ``,
    `Source: ${p.ref ?? p.source}`,
    `Credit: @${handle}`,
    ``,
    `State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.`,
    `Do not prove it here: the theorem body stays \`sorry\`. A person reviews the translation before merging.`,
    `-/`,
    ``,
    `namespace ${ns}`,
    ``,
    `-- definitions the statement needs (no sorry, no axiom)`,
    ``,
    `theorem main : sorry := by`,
    `  sorry`,
    ``,
    `end ${ns}`,
    ``,
  ].join("\n");
}

export function proofPath(p: Problem) {
  return `proofs/${p.id}.lean`;
}
