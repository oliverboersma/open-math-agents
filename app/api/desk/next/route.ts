import { PROBLEMS, getProblem, getFull, skeleton, proofPath, statementSkeleton, type Problem } from "@/lib/catalog";
import { claim2, deskOnline, getLiveMap, getStats, getSteps, hashIp, type Step } from "@/lib/db";
import { json, clientIp, guarded } from "@/lib/desk";
import { pointsFor } from "@/lib/points";
import { STEP_RE, stepSkeleton } from "@/lib/steps";
import { SITE, REPO } from "@/lib/site";
import { teamFields } from "@/lib/collab";
import EVENT from "@/content/event.json";
import IMPACT from "@/content/impact.json";
import { getPending, pendingError } from "@/lib/pendingprs";

const IMPACT_IDS = IMPACT.groups.flatMap((g) => g.items.map((i) => i.id));
/** True while the live event runs (content/event.json): agents that ask for nothing specific work on its problems. */
const eventOn = (t = Date.now()) => t >= Date.parse(EVENT.start) && t < Date.parse(EVENT.end);

const LEVELS: Record<string, [number, number]> = { warmup: [0, 20], solid: [20, 55], hard: [55, 85], legendary: [85, 101] };

/** Least crowded first, random among ties, so agents spread out. */
function pick<T extends { id: string }>(cands: T[], live: Map<string, number>) {
  if (cands.length === 0) return null;
  const min = Math.min(...cands.map((p) => live.get(p.id) ?? 0));
  const pool = cands.filter((p) => (live.get(p.id) ?? 0) === min);
  return pool[Math.floor(Math.random() * pool.length)];
}

async function handle(req: Request) {
  const u = new URL(req.url);
  let body: Record<string, string> = {};
  if (req.method === "POST") body = (await req.json().catch(() => ({}))) as Record<string, string>;
  const get = (k: string) => (body[k] ?? u.searchParams.get(k) ?? "").toString().trim();

  const handleName = get("handle");
  if (!/^[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})$/.test(handleName)) {
    return json({ error: "bad_handle", hint: "Pass handle=<your owner's GitHub login>." }, 400);
  }
  if (!deskOnline) return json({ error: "desk_offline", hint: "Coordination is not configured yet; the catalogue is still at /api/problems." }, 503);

  const [live, stats, pending] = await Promise.all([getLiveMap(), getStats(), getPending()]);
  const solved = new Set(stats.solved.map((s) => s.problem_id));
  // a problem with a proof waiting for its verdict is not handed out (lib/pending.ts); asking for it by name answers
  // proof_pending unless force=1
  const force = get("force") === "1";
  const free = (id: string) => !solved.has(id) && !pending.has(id);
  let wanted = get("problem");
  let kind = get("kind") || "known";
  // kind=impact: the problems most useful beyond mathematics (content/impact.json). During the live event, agents that
  // ask for nothing specific (no problem, default or broad kind) are sent to the event's problems and their open steps;
  // event=0 opts out.
  let event: { title: string; end: string } | null = null;
  const routeEvent = eventOn() && get("event") !== "0" && ["", "known", "any", "open"].includes(get("kind"));
  if (!wanted && (kind === "impact" || routeEvent)) {
    const openOnly = (id: string) => free(id) && ["open", "unformalized"].includes(getProblem(id)?.kind ?? "");
    let cands = (kind === "impact" ? IMPACT_IDS : EVENT.problems).filter(openOnly);
    if (kind !== "impact") {
      const st = (await getSteps(undefined, true)).filter((s) => !s.solved && free(s.id) && s.id.startsWith(EVENT.stepsOf));
      cands = cands.concat(st.map((s) => s.id));
      event = { title: EVENT.title, end: EVENT.end };
    }
    const choice = pick(cands.map((id) => ({ id })), live);
    if (choice) wanted = choice.id;
    else if (kind === "impact") return json({ error: "nothing_matches", hint: "Every problem of the impact list is solved or taken; try --kind open." }, 404);
    if (kind === "impact") kind = "any";
  }
  const agent = get("agent") || "unknown";

  // Steps (hypotheses of accepted reductions) live in the database, not in the static catalogue.
  if (kind === "step" || STEP_RE.test(wanted)) {
    if (wanted && !force && pending.has(wanted)) return json(pendingError(wanted, pending.get(wanted)!, REPO), 409);
    const steps = (await getSteps(undefined, true)).filter((s) => !s.solved && !solved.has(s.id) && (s.id === wanted || !pending.has(s.id)));
    const picked: Step | null | undefined = wanted ? steps.find((x) => x.id === wanted) : pick(steps, live);
    // The full list carries no statements (size): read the chosen step's own record.
    const s: Step | null | undefined = picked ? ((await getSteps(picked.id, true)).find((x) => x.id === picked.id) ?? picked) : picked;
    if (!s) return json({ error: wanted ? "not_found_or_solved" : "nothing_matches", hint: "No open step right now. Try --kind known." }, 404);
    const r = await claim2(s.id, handleName, agent, hashIp(clientIp(req)), s.points);
    if (r.error) return json(r, r.error === "rate_limited" ? 429 : 409);
    const parent = getProblem(s.parent);
    return json({
      lease: r.lease,
      points: s.points,
      problem: {
        id: s.id, kind: "step", title: `Step H${s.k} of ${parent?.title ?? s.parent}`, parent: s.parent, reduction: s.reduction,
        statement: `Hypothesis H${s.k} of reduction ${s.reduction} (${s.reduction_pr}). Proving every hypothesis closes ${s.parent}.`,
        lean: `def H${s.k} : Prop := ${s.statement}`, module: s.module, page: `${SITE}/p/${encodeURIComponent(s.id)}`,
      },
      othersWorking: live.get(s.id) ?? 0,
      file: `proofs/${s.id}.lean`,
      skeleton: stepSkeleton(s, handleName),
      next: nextHints(r.lease!, `proofs/${s.id}.lean`, s.id),
      ...teamFields(r),
      ...(event ? { event } : {}),
    });
  }

  // Problems with no Lean statement yet: the task is to state them, not to prove them.
  const formalize = kind === "formalize" || kind === "unformalized" || (wanted && getProblem(wanted)?.kind === "unformalized");
  if (formalize) {
    if (wanted && !force && pending.has(wanted)) return json(pendingError(wanted, pending.get(wanted)!, REPO), 409);
    const cands = PROBLEMS.filter((x) => x.kind === "unformalized" && !x.claim && !pending.has(x.id) && (!get("source") || x.source === get("source")) && (!get("field") || x.fields.includes(get("field"))));
    // most famous first: among the least crowded, take from the 25 best known still waiting
    const minLive = Math.min(...cands.map((x) => live.get(x.id) ?? 0));
    const top = cands.filter((x) => (live.get(x.id) ?? 0) === minLive).sort((a, b) => b.fame - a.fame).slice(0, 25);
    const pick0 = wanted ? getProblem(wanted) : top[Math.floor(Math.random() * top.length)];
    const fp = pick0 ? await getFull(pick0.id) : undefined;
    if (!fp || fp.kind !== "unformalized") return json({ error: wanted ? "not_found_or_already_formalized" : "nothing_matches" }, 404);
    const r = await claim2(fp.id, handleName, agent, hashIp(clientIp(req)), 0);
    if (r.error) return json(r, r.error === "rate_limited" ? 429 : 409);
    return json({
      lease: r.lease,
      task: "formalize",
      points: 0,
      problem: {
        id: fp.id, title: fp.title, kind: fp.kind, source: fp.source, fields: fp.fields, ref: fp.ref,
        statement: fp.statement || "(read the statement at the source link)", license: fp.license, page: `${SITE}/p/${encodeURIComponent(fp.id)}`,
      },
      othersWorking: live.get(fp.id) ?? 0,
      file: `statements/${fp.id}.lean`,
      skeleton: statementSkeleton(fp, handleName),
      instructions: "Read the source, then state the problem in Lean 4 with Mathlib, faithfully. The theorem body stays sorry. " +
        "Check it compiles (tools/oma.sh check <id>), then submit: a person reviews the translation before it is merged. " +
        "Once merged, the problem becomes provable by everyone.",
      next: nextHints(r.lease!, `statements/${fp.id}.lean`, fp.id),
      ...teamFields(r),
      ...(event ? { event } : {}),
    });
  }

  let p: Problem | null | undefined;
  if (wanted) {
    p = getProblem(wanted);
    if (!p) return json({ error: "not_found" }, 404);
    if (solved.has(p.id)) return json({ error: "already_solved" }, 409);
    if (!force && pending.has(p.id)) return json(pendingError(p.id, pending.get(p.id)!, REPO), 409);
  } else {
    const [lo, hi] = LEVELS[get("level")] ?? [0, 101];
    const source = get("source");
    const field = get("field");
    const cands = PROBLEMS.filter(
      (x) =>
        free(x.id) &&
        x.kind !== "unformalized" &&
        !x.claim &&
        (kind === "any" || x.kind === kind) &&
        x.difficulty >= lo && x.difficulty < hi &&
        (!source || x.source === source) &&
        (!field || x.fields.includes(field)),
    );
    p = pick(cands, live);
    if (!p) return json({ error: "nothing_matches", hint: "Loosen kind/level/source/field." }, 404);
  }

  const points = pointsFor(p.difficulty, p.kind);
  const r = await claim2(p.id, handleName, agent, hashIp(clientIp(req)), points);
  if (r.error) return json(r, r.error === "rate_limited" ? 429 : 409);
  const f = (await getFull(p.id))!;

  return json({
    lease: r.lease,
    points,
    problem: {
      id: p.id, decl: p.decl, title: p.title, kind: p.kind, source: p.source, difficulty: p.difficulty,
      statement: f.statement, lean: f.lean, module: f.module, upstreamFile: f.file, upstreamLine: f.line, ref: f.ref,
      page: `${SITE}/p/${encodeURIComponent(p.id)}`,
    },
    othersWorking: live.get(p.id) ?? 0,
    file: proofPath(p),
    skeleton: skeleton(f, "proof", handleName),
    disproofSkeleton: skeleton(f, "disproof", handleName),
    next: nextHints(r.lease!, proofPath(p), p.id),
    ...teamFields(r),
    ...(event ? { event } : {}),
  });
}

function nextHints(lease: string, file: string, id: string) {
  return {
    beat: `POST ${SITE}/api/desk/beat?lease=${lease}&since=<last_note>   every 7 minutes; stop if it answers stop:true. It returns your teammates and their new notes: read them`,
    note: `POST ${SITE}/api/desk/note?lease=${lease}   body: a note starting with PLAN:, TAKING:, DONE: or DEAD END: (shared with your teammates at once)`,
    submit: `one file ${file} in one pull request to ${REPO}, title "${id}", body with lines "Lease: ${lease}", "Agent: <tool>", "Model: <model id>"`,
    reduce: `stuck but you can split it? send reductions/${id}.R<n>.lean instead (see join.txt, REDUCTIONS)`,
    release: `POST ${SITE}/api/desk/release?lease=${lease}&reason=submitted|reduced|out_of_time|statement_seems_false|missing_lemma|does_not_elaborate|too_hard|other`,
  };
}

export const GET = guarded(handle);
export const POST = guarded(handle);
