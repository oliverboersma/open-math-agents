import "server-only";
import { getProblem } from "@/lib/catalog";
import { getSteps, type Step } from "@/lib/db";
import { cachedJSON } from "@/lib/edgecache";
import { pointsFor } from "@/lib/points";
import { REPO, REPO_URL } from "@/lib/site";
import { parseStep, reductionHypotheses, reductionModule } from "@/lib/steps";

/**
 * A step of a reduction, found even when the database cannot say: its subtree read (statements included), else the
 * shared list of every step (no statements, kept in KV with long-lived stale copies), else the merged reduction file
 * itself on GitHub, which is the source of truth (a merged reduction whose registration failed has no database row).
 * Returns null only when the reduction file is known not to exist or has no such hypothesis.
 */
export type StepFound = { step: Step; subtree: Step[]; source: "db" | "list" | "file" };

type RedFile = { ok: true; src: string } | { ok: false; missing: boolean };

const MISSING = "reduction_file_missing";

/** The merged reduction file on main: cached an hour when found; a 404 or an error is not cached (asked again next time). */
export async function reductionFile(reductionId: string): Promise<RedFile> {
  try {
    const src = await cachedJSON<string>(`redfile?${reductionId}`, 3600, async () => {
      const res = await fetch(`https://raw.githubusercontent.com/${REPO}/main/reductions/${encodeURIComponent(reductionId)}.lean`, {
        signal: AbortSignal.timeout(4000),
      });
      if (res.status === 404) throw new Error(MISSING);
      if (!res.ok) throw new Error(`github raw ${res.status}`);
      return res.text();
    });
    return { ok: true, src };
  } catch (e) {
    const missing = e instanceof Error && e.message === MISSING;
    if (!missing) console.error("reductionFile", reductionId, e);
    return { ok: false, missing };
  }
}

/** The catalogue problem at the top of a chain of steps (X.R1.H2.R1.H1 → X), if there is one. */
export function rootProblem(id: string) {
  let top = id;
  while (!getProblem(top) && parseStep(top)) top = parseStep(top)!.parent;
  return getProblem(top);
}

/** Points of a target (problem or step), as the verdict route freezes them into a reduction's steps. */
function pointsOf(target: string, list: Step[]): number {
  const p = getProblem(target);
  if (p) return pointsFor(p.difficulty, p.kind);
  const s = list.find((x) => x.id === target);
  if (s) return s.points;
  const up = parseStep(target);
  return up ? pointsOf(up.parent, list) : 1;
}

export async function findStep(id: string): Promise<StepFound | null> {
  const st = parseStep(id);
  if (!st || !rootProblem(id)) return null;
  const subtree = await getSteps(id);
  const own = subtree.find((s) => s.id === id);
  if (own) return { step: own, subtree, source: "db" };

  // Every step, without statements (one shared read, kept in KV): the subtree below id comes from it too.
  const all = await getSteps();
  const listed = all.find((s) => s.id === id);
  const below = new Set([id]);
  const tree: Step[] = [];
  for (const s of [...all].sort((a, b) => a.id.length - b.id.length)) if (below.has(s.parent)) { below.add(s.id); tree.push(s); }

  const file = await reductionFile(st.reduction);
  const statement = file.ok ? reductionHypotheses(file.src)[st.k - 1] : undefined;
  if (listed) return { step: { ...listed, statement: listed.statement || statement || "" }, subtree: [listed, ...tree], source: "list" };
  if (file.ok && statement === undefined) return null; // the reduction exists but has no such hypothesis
  if (!file.ok && file.missing) return null;
  // The merged file is the record (or GitHub could not be asked: show what the id alone says rather than a 404).
  const step: Step = {
    id, reduction: st.reduction, parent: st.parent, k: st.k, statement: statement ?? "", module: reductionModule(st.reduction),
    points: pointsOf(st.parent, all), created_at: "", solved: false,
    reduction_pr: `${REPO_URL}/blob/main/reductions/${encodeURIComponent(st.reduction)}.lean`, reduction_by: "",
  };
  return { step, subtree: [step, ...tree], source: "file" };
}
