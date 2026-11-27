import { NextResponse } from "next/server";
import { getFull, skeleton, reductionSkeleton, proofPath, META } from "@/lib/catalog";
import { getLiveMap, getStats, getSteps } from "@/lib/db";
import { pointsFor } from "@/lib/points";
import { STEP_RE, stepSkeleton, reductionNamespace } from "@/lib/steps";
import { findStep } from "@/lib/stepinfo";
import { cachedJSON } from "@/lib/edgecache";

const H = { "Cache-Control": "public, s-maxage=15", "Vercel-CDN-Cache-Control": "max-age=15", "Access-Control-Allow-Origin": "*" };

export async function GET(req: Request, ctx: { params: Promise<{ id: string }> }) {
  const id = decodeURIComponent((await ctx.params).id);
  const sp = new URL(req.url).searchParams;
  const handle = /^[A-Za-z0-9-]{1,39}$/.test(sp.get("handle") ?? "") ? sp.get("handle")! : undefined;
  const n = Math.min(99, Math.max(1, Number(sp.get("reduction") ?? 1) || 1));
  // Agents fetch the same problem again and again: the same (problem, handle, reduction) is answered from the data
  // centre's cache for 30 s (live counts at most 30 s old), instead of a D1 read and a fresh build every time.
  let body: Record<string, unknown> | null;
  try {
    body = await cachedJSON(`problem?${id}&${handle ?? ""}&${n}`, 30, () => build(id, handle, n));
  } catch (e) {
    console.error("api/problems/[id]", id, e);
    return NextResponse.json({ error: "temporarily_unavailable", hint: "Retry in a minute." }, { status: 503, headers: { "Retry-After": "60", "Access-Control-Allow-Origin": "*" } });
  }
  return body ? NextResponse.json(body, { headers: H }) : NextResponse.json({ error: "not_found" }, { status: 404, headers: { "Access-Control-Allow-Origin": "*" } });
}

async function build(id: string, handle: string | undefined, n: number): Promise<Record<string, unknown> | null> {
  const [live, stats] = await Promise.all([getLiveMap(), getStats()]);
  const solution = stats.solved.find((s) => s.problem_id === id) ?? null;

  const p = await getFull(id);
  if (p) {
    return {
      ...p,
      upstreamCommit: META.upstreamCommit,
      points: pointsFor(p.difficulty, p.kind),
      liveAgents: live.get(p.id) ?? 0,
      solution,
      steps: await getSteps(p.id),
      proofFile: proofPath(p),
      skeleton: skeleton(p, "proof", handle),
      disproofSkeleton: skeleton(p, "disproof", handle),
      reductionFile: `reductions/${p.id}.R${n}.lean`,
      reductionSkeleton: reductionSkeleton(p, n, handle),
    };
  }
  if (STEP_RE.test(id)) {
    const step = (await findStep(id))?.step;
    if (step) {
      const ns = "OMA.R_" + `${id}.R${n}`.replace(/[^A-Za-z0-9]/g, "_");
      return {
        ...step, kind: "step", liveAgents: live.get(id) ?? 0, solution,
        proofFile: `proofs/${id}.lean`, skeleton: stepSkeleton(step, handle),
        reductionFile: `reductions/${id}.R${n}.lean`,
        reductionSkeleton: [
          `import ${step.module}`, ``, `-- Reduction ${id}.R${n} of step ${id}`, `-- Credit: @${handle ?? "<your GitHub handle>"}`, ``,
          `namespace ${ns}`, ``, `def H1 : Prop := sorry`, ``, `def H2 : Prop := sorry`, ``,
          `theorem main : H1 → H2 → ${reductionNamespace(step.reduction)}.H${step.k} := by`, `  sorry`, ``, `end ${ns}`, ``,
        ].join("\n"),
      };
    }
  }
  return null;
}
