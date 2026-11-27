import { timingSafeEqual } from "node:crypto";
import { verdict2, registerReduction, deskOnline, getStepsStrict, logEvent } from "@/lib/db";
import { getProblem } from "@/lib/catalog";
import { json, guarded } from "@/lib/desk";
import { pointsFor } from "@/lib/points";
import { REDUCTION_FILE_RE, STEP_RE, parseStep, reductionHypotheses, reductionModule } from "@/lib/steps";
import { reductionFile } from "@/lib/stepinfo";
import { REPO } from "@/lib/site";
import { verifyWorkflowToken } from "@/lib/ghoidc";

const GH = "https://api.github.com";
const ghHeaders: Record<string, string> = {
  Accept: "application/vnd.github+json",
  "User-Agent": "open-math-agents",
  ...(process.env.GITHUB_TOKEN ? { Authorization: `Bearer ${process.env.GITHUB_TOKEN}` } : {}),
};

/** "Agent: claude-code" / "Model: claude-opus-5-5" lines in the pull request body. Free text, shown as credit. */
function creditLine(body: string, key: string) {
  const m = body.match(new RegExp(`^\\s*${key}\\s*:\\s*(.+)$`, "im"));
  return m ? m[1].replace(/[<>`*_\[\]]/g, "").trim().slice(0, 80) || null : null;
}

/**
 * A step the database does not know. If the reduction that defines it is merged, the step exists and only its
 * registration is missing (an earlier credit call failed): answer an error the credit tools retry and keep for a
 * later replay, instead of a final "unknown" that would drop merged work.
 */
async function missingStep(id: string, final: "unknown_target" | "unknown_step") {
  const st = parseStep(id);
  const file = st ? await reductionFile(st.reduction) : null;
  if (file && (file.ok || !file.missing)) {
    return { error: "step_not_registered_yet", id, reduction: st!.reduction, hint: "Register the reduction that defines this step (replay its pull request), then retry." };
  }
  return final === "unknown_target" ? { error: final, target: id } : { error: final, id };
}

/**
 * Records a merged contribution. The pull request data (merged into main? which single file? who authored it?) is
 * trusted only from the verdict workflow, proved by its GitHub OIDC token; any other caller sends just a PR number
 * and the site asks GitHub itself.
 * The PR author (the owner of the agent) is credited as the solver; the agent and model they declared in the
 * PR body are recorded next to it.
 */
async function post(req: Request) {
  if (!deskOnline) return json({ error: "desk_offline" }, 503);
  const b = await req.json().catch(() => null);
  if (!b) return json({ error: "bad_request" }, 400);

  // Optional trusted path for maintainers (manual corrections).
  const secret = process.env.OMA_VERDICT_SECRET ?? "";
  const got = req.headers.get("x-oma-secret") ?? "";
  const maintainer = Boolean(secret && got && got.length === secret.length && timingSafeEqual(Buffer.from(got), Buffer.from(secret)));
  // A maintainer replaying a merged pull request (after an outage) sends the same payload as the verdict workflow and
  // goes through the same checks below, reductions and statements included.
  if (maintainer && !Array.isArray(b.files)) {
    if (typeof b.problem !== "string" || !/^https:\/\/github\.com\//.test(b.pr ?? "") || !["accepted", "rejected", "fault"].includes(b.verdict)) {
      return json({ error: "bad_request" }, 400);
    }
    const p = getProblem(b.problem);
    return json(await verdict2({
      problem: b.problem, handle: String(b.handle).slice(0, 39), pr: b.pr, verdict: b.verdict,
      polarity: b.polarity === "disproof" ? "disproof" : "proof", agent: b.agent ?? null, model: b.model ?? null,
      points: p ? pointsFor(p.difficulty, p.kind) : Number(b.points ?? 1),
    }));
  }

  const n = Number(b.pr);
  if (!Number.isInteger(n) || n <= 0) return json({ error: "bad_request", hint: "body {\"pr\": <pull request number>}" }, 400);

  // The pull request as GitHub describes it: sent by the verdict workflow with an OIDC token proving where it comes
  // from (the workflow read it with its own token), or else asked from the GitHub API here.
  type PR = { merged: boolean; base: string; handle: string; body: string; mergeSha: string; url: string; files: { filename: string; status: string }[] };
  let pr: PR;
  if (((maintainer && Array.isArray(b.files)) || (b.oidc && (await verifyWorkflowToken(b.oidc)))) && Array.isArray(b.files) && b.pr === n) {
    pr = {
      merged: b.merged === true, base: String(b.base), handle: String(b.handle ?? "unknown"), body: String(b.body ?? ""),
      mergeSha: String(b.mergeSha ?? ""), url: String(b.url ?? ""),
      files: b.files.map((f: { filename?: unknown; status?: unknown }) => ({ filename: String(f.filename), status: String(f.status) })),
    };
    if (!/^[0-9a-f]{40}$/.test(pr.mergeSha) || pr.url !== `https://github.com/${REPO}/pull/${n}`) return json({ error: "bad_request" }, 400);
  } else {
    const prRes = await fetch(`${GH}/repos/${REPO}/pulls/${n}`, { headers: ghHeaders, cache: "no-store" });
    if (prRes.status === 404) return json({ error: "no_such_pr" }, 404);
    if (!prRes.ok) return json({ error: "github", status: prRes.status }, 502);
    const g = await prRes.json();
    const filesRes = await fetch(`${GH}/repos/${REPO}/pulls/${n}/files`, { headers: ghHeaders, cache: "no-store" });
    if (!filesRes.ok) return json({ error: "github", status: filesRes.status }, 502);
    pr = { merged: !!g.merged, base: g.base?.ref, handle: String(g.user?.login ?? "unknown"), body: String(g.body ?? ""), mergeSha: g.merge_commit_sha, url: g.html_url, files: await filesRes.json() };
  }
  if (!pr.merged || pr.base !== "main") return json({ error: "not_merged" }, 409);
  const files = pr.files;
  // A new file, or (shortest-proof rule) a shorter version of a proof already merged: the verdict workflow merged it
  // only after checking it is at least 5% shorter (tools/prooflen.py).
  const replacing = files.length === 1 && files[0].status === "modified" && /^proofs\/[^/]+\.lean$/.test(files[0].filename);
  if (files.length !== 1 || (files[0].status !== "added" && !replacing)) return json({ error: "not_a_single_new_file" }, 409);
  const path = files[0].filename;

  const raw = await fetch(`https://raw.githubusercontent.com/${REPO}/${pr.mergeSha}/${path}`, { cache: "no-store" });
  const src = raw.ok ? await raw.text() : "";
  const handle = pr.handle.slice(0, 39);
  const body = pr.body;
  const agent = creditLine(body, "Agent");
  const model = creditLine(body, "Model");

  // A reduction: register its hypotheses as new steps.
  const red = path.match(REDUCTION_FILE_RE);
  if (red) {
    const target = red[1];
    const id = `${target}.R${red[2]}`;
    const parentProblem = getProblem(target);
    const parentStep = parentProblem ? null : (await getStepsStrict(target)).find((s) => s.id === target);
    if (!parentProblem && !parentStep) return json(await missingStep(target, "unknown_target"), 409);
    const statements = reductionHypotheses(src);
    if (statements.length < 2 || statements.length > 4) return json({ error: "bad_reduction", found: statements.length }, 409);
    const points = parentProblem ? pointsFor(parentProblem.difficulty, parentProblem.kind) : parentStep!.points;
    return json(await registerReduction({ id, problem: target, handle, pr: pr.url, module: reductionModule(id), statements, points }));
  }

  // A Lean statement for a problem that had none: merged only after human review. Logged and credited;
  // the problem becomes provable at the next build (scripts/build_statements.mjs).
  const stm = path.match(/^statements\/([^/]+)\.lean$/);
  if (stm) {
    const sp = getProblem(stm[1]);
    if (!sp) return json({ error: "unknown_problem", id: stm[1] }, 409);
    return json(await logEvent("formalized", sp.id, handle, pr.url));
  }

  const m = path.match(/^proofs\/([^/]+)\.lean$/);
  if (!m) return json({ error: "not_a_proof" }, 409);
  const id = m[1];
  // The first solve keeps its credit; the shorter proof is recorded as the problem's shortest proof.
  if (replacing) return json(await logEvent("shorter", id, handle, pr.url));
  const polarity = /\btheorem\s+OMA\.disproof\b/.test(src) ? "disproof" : "proof";
  const p = getProblem(id);
  let points: number;
  if (p && p.kind === "unformalized") return json({ error: "not_formalized_yet", id }, 409);
  if (p) points = pointsFor(p.difficulty, p.kind);
  else if (STEP_RE.test(id)) {
    const step = (await getStepsStrict(id)).find((s) => s.id === id);
    if (!step) return json(await missingStep(id, "unknown_step"), 409);
    points = step.points;
  } else return json({ error: "unknown_problem", id }, 409);

  return json(await verdict2({ problem: id, handle, pr: pr.url, verdict: "accepted", polarity, agent, model, points }));
}
export const POST = guarded(post);
