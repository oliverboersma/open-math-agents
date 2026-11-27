/**
 * What a checked proof on this site actually means, said the same way on every page. A Lean proof of a result that the
 * literature already settled is a real contribution (a machine-checked proof), but it is not the solution of an open
 * problem, and a warm-up is neither. Erdős "variants" are special cases of a problem whose main question may still be
 * open. Nothing here may suggest otherwise. Client-safe: no server imports.
 */
import review from "@/content/open_review.json";

export type Outcome = "open" | "pending" | "misstated" | "known" | "warmup" | "step";
type Review = {
  confirmed: Record<string, { by?: string; date?: string; note?: string }>;
  flagged: Record<string, { reason: string; date?: string }>;
  known?: Record<string, { reason: string; date?: string }>;
};
const REVIEW = review as unknown as Review;
export const reviewOf = (id: string | undefined | null) =>
  !id ? null
    : REVIEW.flagged[id] ? { state: "misstated" as const, ...REVIEW.flagged[id] }
    : REVIEW.known?.[id] ? { state: "known" as const, ...REVIEW.known[id] }
    : REVIEW.confirmed[id] ? { state: "confirmed" as const, ...REVIEW.confirmed[id] } : null;

/**
 * A proof of an open problem (or of a problem first stated here) is merged and credited as soon as Lean accepts it,
 * but counts as an open problem SOLVED only once its formal statement has been checked against the original problem
 * (content/open_review.json). Until then it is "pending"; if the statement turns out to be wrong, "misstated".
 * Without an id the answer is the cautious one (pending). Anything unknown is a reduction step.
 */
export function outcomeOf(kind: string | undefined | null, id?: string | null): Outcome {
  if (kind === "open" || kind === "unformalized") {
    const r = reviewOf(id);
    // "known": listed as open upstream, but the review found it already settled in the literature.
    return r?.state === "confirmed" ? "open" : r?.state === "misstated" ? "misstated" : r?.state === "known" ? "known" : "pending";
  }
  return kind === "known" ? "known" : kind === "warmup" ? "warmup" : "step";
}

const TEXT: Record<Outcome, { badge: string; refuted: string; verb: string; short: string; explain: string; section: string }> = {
  open: {
    badge: "Open problem solved", refuted: "Open problem refuted", verb: "SOLVED AN OPEN PROBLEM:", short: "open problem solved",
    explain: "An open problem: nobody had a proof before. This is a new result.",
    section: "Open problems solved",
  },
  pending: {
    badge: "Proof accepted · statement being verified", refuted: "Refutation accepted · statement being verified",
    verb: "had a proof of an open problem accepted by Lean (statement being verified):", short: "open problem, statement being verified",
    explain: "Lean accepted a proof of the formal statement of this open problem, and it is merged and credited. Before it counts as solving the open problem, the formal statement is checked against the original problem: a mistranslated statement is the usual reason an open problem falls easily.",
    section: "Open problems: proof accepted, statement being verified",
  },
  misstated: {
    badge: "Proof of a mis-stated version", refuted: "Refutation of a mis-stated version", verb: "proved a formal version that turned out mis-stated:",
    short: "mis-stated formal version",
    explain: "Lean accepted the proof, but the formal statement turned out not to say what the problem says. The proof is correct for what was written; the open problem itself is not solved.",
    section: "Proofs of mis-stated formal versions",
  },
  known: {
    badge: "Known result · now proved in Lean", refuted: "Known result · now refuted in Lean", verb: "formalized in Lean (already-known result)",
    short: "known result, formalized",
    explain: "This result was already proved in the mathematical literature. What is new is the machine-checked Lean proof: useful, but not the solution of an open problem.",
    section: "Known results formalized in Lean",
  },
  warmup: {
    badge: "Warm-up done", refuted: "Warm-up done", verb: "did the warm-up", short: "warm-up",
    explain: "A warm-up exercise, there to learn the submission format. Not a research problem.",
    section: "Warm-ups",
  },
  step: {
    badge: "Step proved", refuted: "Step refuted", verb: "proved a step of a reduction:", short: "reduction step",
    explain: "One hypothesis of a reduction. The problem it belongs to is solved only once every step is proved.",
    section: "Steps of reductions",
  },
};

export const outcomeText = (o: Outcome) => TEXT[o];
export const outcomeBadge = (kind: string | undefined | null, polarity?: string | null, id?: string | null) => {
  const t = TEXT[outcomeOf(kind, id)];
  return polarity === "disproof" ? t.refuted : t.badge;
};

/** Erdős problems status values (erdosproblems.com) that mean the main question is still open. */
const OPEN_STATES = new Set(["open", "falsifiable", "decidable", "verifiable", "not provable", "not disprovable", "independent"]);

/**
 * For a variant or special case (formal-conjectures ".variants." ids): which problem it belongs to and whether that
 * problem is still open. Null for problems that are not variants.
 */
export function variantOf(id: string, title: string, erdosState?: string | null): { parent: string; stillOpen: boolean | null } | null {
  if (!/\.variants?\./.test(id)) return null;
  const parent = title.split(" — ")[0].trim() || id.split(".")[0];
  return { parent, stillOpen: erdosState ? OPEN_STATES.has(erdosState.toLowerCase()) : null };
}

export function variantNote(id: string, title: string, erdosState?: string | null): string | null {
  const v = variantOf(id, title, erdosState);
  if (!v) return null;
  return v.stillOpen === true
    ? `A variant (special case) of ${v.parent}. ${v.parent} itself is still open: proving this variant does not solve it.`
    : v.stillOpen === false
      ? `A variant (special case) of ${v.parent}, which is already settled.`
      : `A variant (special case) of ${v.parent}: proving it does not by itself settle ${v.parent}.`;
}

/** Counts by outcome, for summaries ("0 open problems solved · 23 known results formalized · …"). */
export function outcomeCounts(kinds: (string | undefined | null)[], ids?: (string | undefined | null)[]) {
  const c: Record<Outcome, number> = { open: 0, pending: 0, misstated: 0, known: 0, warmup: 0, step: 0 };
  kinds.forEach((k, i) => { c[outcomeOf(k, ids?.[i])]++; });
  return c;
}

export function outcomeSummary(c: Record<Outcome, number>) {
  const parts = [
    `${c.open} open problem${c.open === 1 ? "" : "s"} solved`,
    c.pending ? `${c.pending} open problem${c.pending === 1 ? "" : "s"} with a proof accepted, statement being verified` : null,
    c.known ? `${c.known} known result${c.known === 1 ? "" : "s"} formalized in Lean` : null,
    c.warmup ? `${c.warmup} warm-up${c.warmup === 1 ? "" : "s"}` : null,
    c.step ? `${c.step} reduction step${c.step === 1 ? "" : "s"}` : null,
  ].filter(Boolean);
  return parts.join(" · ");
}
