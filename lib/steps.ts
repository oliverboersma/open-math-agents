/** Reductions and steps share naming rules with tools/lint.py: keep them identical. */
export const STEP_RE = /^(.+)\.R(\d{1,2})\.H([1-4])$/;
export const REDUCTION_FILE_RE = /^reductions\/(.+)\.R(\d{1,2})\.lean$/;

const san = (id: string) => "R_" + id.replace(/[^A-Za-z0-9]/g, "_");
/** Lean module a step imports: the merged reduction file, compiled by the checker under OMAReductions/. */
export function reductionModule(reductionId: string) {
  return "OMAReductions." + san(reductionId);
}
/** Namespace a reduction declares its hypotheses in: unique per reduction, so reductions of steps never clash. */
export function reductionNamespace(reductionId: string) {
  return "OMA." + san(reductionId);
}

export function parseStep(id: string) {
  const m = id.match(STEP_RE);
  return m ? { parent: m[1], n: Number(m[2]), k: Number(m[3]), reduction: `${m[1]}.R${m[2]}` } : null;
}

/** Hypotheses of a reduction file: `def H1 : Prop := <statement>` … up to the next declaration. */
export function reductionHypotheses(src: string): string[] {
  const out: string[] = [];
  // A hypothesis ends at the next declaration, attribute or doc comment (`\b` applies to the keywords only: after
  // "/--" it never matched, so a doc comment of the next declaration ended up in the statement).
  const re = /^def\s+H([1-4])\s*:\s*Prop\s*:=\s*([\s\S]*?)(?=^\s*(?:(?:def|theorem|lemma|end|namespace|open|section|variable)\b|@\[|\/--)|(?![\s\S]))/gm;
  let m: RegExpExecArray | null;
  while ((m = re.exec(src))) out[Number(m[1]) - 1] = m[2].trim();
  return out.filter((x) => x !== undefined);
}

export function stepSkeleton(step: { id: string; reduction: string; module: string; k: number; statement: string }, handle = "<handle>") {
  return [
    `import ${step.module}`,
    ``,
    `-- Step ${step.id}: hypothesis H${step.k} of reduction ${step.id.replace(/\.H\d$/, "")}`,
    `-- Credit: @${handle}`,
    `-- H${step.k} := ${step.statement.replace(/\n/g, " ")}`,
    ``,
    `theorem OMA.solution : ${reductionNamespace(step.reduction)}.H${step.k} := by`,
    `  sorry`,
    ``,
  ].join("\n");
}
