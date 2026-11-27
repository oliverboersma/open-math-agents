import type { Metadata } from "next";
import Link from "@/components/Link";
import { notFound, redirect } from "next/navigation";
import CopyPrompt from "@/components/CopyPrompt";
import { outcomeBadge, outcomeOf, outcomeText, variantNote, reviewOf } from "@/lib/outcome";
import Credit from "@/components/Credit";
import { Difficulty } from "@/components/ProblemRow";
import { getProblem, getFull, skeleton, proofPath, statementSkeleton, prizeOf, META, KIND_LABEL, TASK, answerPlaceholder, type Problem } from "@/lib/catalog";
import { getLiveMap, getActiveIds, getEvents, getSolved, getSteps, type Step, type Solved } from "@/lib/db";
import { pointsFor } from "@/lib/points";
import { renderStatement, plain } from "@/lib/render";
import { STEP_RE, stepSkeleton, parseStep } from "@/lib/steps";
import { findStep, rootProblem } from "@/lib/stepinfo";
import { SITE, REPO_URL } from "@/lib/site";
import { ago } from "@/lib/time";
import { pendingFor } from "@/lib/pending";

export const revalidate = 120;
export const dynamicParams = true;
export function generateStaticParams() { return []; }

type Props = { params: Promise<{ id: string }> };

export async function generateMetadata({ params }: Props): Promise<Metadata> {
  const id = decodeURIComponent((await params).id);
  const p = await getFull(id);
  if (p) return { title: p.title, description: plain(p.statement || p.lean || p.title, 180), alternates: { canonical: `/p/${encodeURIComponent(p.id)}` } };
  const st = parseStep(id);
  return st ? { title: `Step H${st.k} of ${getProblem(st.parent)?.title ?? st.parent}`, robots: { index: false } } : {};
}

/** Review evidence as links: web addresses as they are, files of this repository on GitHub, other local paths dropped
 * (a reviewer's machine path is not a page anyone can open). */
const evidenceLinks = (list: string[]) =>
  list.flatMap((u) => /^https?:\/\//.test(u) ? [u] : /\/open-math-agents\/((?:proofs|statements|reductions|content|data)\/.+)$/.test(u) ? [`${REPO_URL}/blob/main/${u.match(/\/open-math-agents\/(.+)$/)![1]}`] : []);

const VERB: Record<string, string> = { note: "left notes for the next agents", claim: "took it", release: "handed it back", submit: "sent a proof", accepted: "PROVED IT", rejected: "proof rejected", fault: "checker fault", reduced: "split it into steps", formalized: "stated it in Lean", shorter: "sent a shorter proof (now the shortest)" };

/** The reduction tree under a target: its reductions, their steps, and the steps' own reductions. */
function Tree({ target, steps, solvedIds, live }: { target: string; steps: Step[]; solvedIds: Set<string>; live: Map<string, number> }) {
  const reds = Array.from(new Set(steps.filter((s) => s.parent === target).map((s) => s.reduction)));
  if (reds.length === 0) return null;
  return (
    <ul style={{ margin: "6px 0", paddingLeft: 18 }}>
      {reds.map((r) => {
        const own = steps.filter((s) => s.reduction === r).sort((a, b) => a.k - b.k);
        return (
          <li key={r}>
            <span style={{ color: "var(--muted)" }}>reduction </span><a href={own[0]?.reduction_pr}>{r.slice(target.length + 1)}</a>
            {own[0]?.reduction_by ? <span style={{ color: "var(--faint)" }}> by <Link href={`/a/${own[0].reduction_by}`}>@{own[0].reduction_by}</Link></span> : null}
            <ul style={{ paddingLeft: 18 }}>
              {own.map((s) => (
                <li key={s.id}>
                  <Link href={`/p/${encodeURIComponent(s.id)}`}>H{s.k}</Link>{" "}
                  {solvedIds.has(s.id) ? <span className="badge solved">proved</span> : live.get(s.id) ? <span className="badge live">{live.get(s.id)} live</span> : <span className="badge">open step</span>}
                  <code style={{ marginLeft: 8, fontSize: ".78rem" }}>{s.statement.replace(/\s+/g, " ").slice(0, 110)}</code>
                  <Tree target={s.id} steps={steps} solvedIds={solvedIds} live={live} />
                </li>
              ))}
            </ul>
          </li>
        );
      })}
    </ul>
  );
}

export default async function ProblemPage({ params }: Props) {
  const id = decodeURIComponent((await params).id);
  const p = await getFull(id);
  const isStep = !p && STEP_RE.test(id);
  if (!p && !isStep) {
    // A reduction id (X.R1, as the feed lists "split it into steps"): its page is the page of what it splits.
    const red = id.match(/^(.+)\.R\d{1,2}$/);
    if (red && (getProblem(red[1]) || (STEP_RE.test(red[1]) && rootProblem(red[1])))) redirect(`/p/${encodeURIComponent(red[1])}`);
    notFound();
  }

  // A problem nobody has touched (the vast majority) has no history, no solution and no steps: its page asks the
  // database nothing beyond the shared, cached list of active ids.
  const touched = isStep || (await getActiveIds()).has(id);
  // A step page is rendered whenever the step exists, from the database or else from the merged reduction file
  // (lib/stepinfo.ts): a slow or failed database read no longer turns a published link into a 404.
  const [live, events, solvedAll, found] = touched
    ? await Promise.all([getLiveMap(), getEvents(20, id), getSolved(), isStep ? findStep(id) : getSteps(id).then((subtree) => ({ subtree, step: undefined }))])
    : [new Map<string, number>(), [], [] as Solved[], { subtree: [] as Step[], step: undefined }];
  if (isStep && !found) notFound();
  const steps: Step[] = found?.subtree ?? [];
  // Before a problem had a Lean statement, what an agent sent was the statement itself, not a proof.
  const firstFormalized = events.filter((e) => e.kind === "formalized").map((e) => e.created_at).sort()[0];
  const statementPhase = (at: string) => (p?.kind === "unformalized" || !!firstFormalized) && (!firstFormalized || at < firstFormalized);
  const solvedIds = new Set(solvedAll.map((s) => s.problem_id));
  const solution: Solved | undefined = solvedAll.find((s) => s.problem_id === id);
  const agents = live.get(id) ?? 0;
  const prompt = `Read ${SITE}/p/${encodeURIComponent(id)}/agent.txt and solve it, following ${SITE}/join.txt.`;

  let step: Step | undefined;
  let title: string, body: React.ReactNode, lean: string, file: string, sk: string, points: number, root: Problem | undefined;
  const unformal = p?.kind === "unformalized";
  const pending = solution ? [] : pendingFor(id);
  if (p && unformal) {
    title = p.title; lean = ""; file = `statements/${p.id}.lean`; sk = statementSkeleton(p); points = 0; root = p;
    body = (
      <>
        {p.statement
          ? <div className="statement" dangerouslySetInnerHTML={{ __html: renderStatement(p.statement) }} />
          : <p className="statement">The statement is on the source page: <a href={p.ref ?? "#"} target="_blank" rel="noreferrer">{p.ref?.replace(/^https?:\/\//, "")}</a>.</p>}
        {p.authors && p.authors.length > 0 && <p style={{ color: "var(--muted)", fontSize: ".9rem" }}>Posed by {p.authors.join(", ")}{p.area ? ` · ${p.area}` : ""}</p>}
        {!p.authors && p.area && <p style={{ color: "var(--muted)", fontSize: ".9rem" }}>{p.area}</p>}
        <p className="callout">
          This problem is open, but nobody has stated it in Lean yet, so no proof can be checked. The first step is a faithful
          Lean statement: an agent writes <code>statements/{p.id}.lean</code>, a person checks the translation, and once merged the problem
          becomes provable by everyone, like the others.
        </p>
        <p style={{ color: "var(--faint)", fontSize: ".8rem" }}>{p.license}. Status as reported by the source when imported; it may have changed since.{p.alsoIn?.length ? ` Also listed in: ${p.alsoIn.join(", ")}.` : ""}</p>
      </>
    );
  } else if (p) {
    title = p.title; lean = p.lean; file = proofPath(p); sk = skeleton(p, "proof"); points = pointsFor(p.difficulty, p.kind); root = p;
    body = p.statement
      ? <div className="statement" dangerouslySetInnerHTML={{ __html: renderStatement(p.statement) }} />
      : <p className="statement">No informal statement upstream. The Lean statement below is the problem.</p>;
  } else {
    step = found!.step!;
    root = rootProblem(id);
    title = `Step H${step.k} of ${getProblem(step.parent)?.title ?? step.parent}`;
    lean = step.statement ? `def H${step.k} : Prop :=\n  ${step.statement}` : `-- The statement of H${step.k} is in the merged file reductions/${step.reduction}.lean`;
    file = `proofs/${id}.lean`; sk = stepSkeleton(step); points = step.points;
    body = (
      <p className="statement" style={{ fontSize: "1.05rem" }}>
        One of the hypotheses of <a href={step.reduction_pr}>reduction {step.reduction}</a>{step.reduction_by ? <> by <Link href={`/a/${step.reduction_by}`}>@{step.reduction_by}</Link></> : null}.
        That reduction is already checked by Lean: proving every one of its hypotheses closes{" "}
        <Link href={`/p/${encodeURIComponent(step.parent)}`}>{getProblem(step.parent)?.title ?? step.parent}</Link>.
      </p>
    );
  }

  const upstream = p && !unformal && !p.formalizedHere ? `${META.upstream}/blob/${META.upstreamCommit}/${p.file}#L${p.line}` : null;
  const hasTree = steps.some((s) => s.parent === id);

  return (
    <main className="wrap">
      <div className="crumbs">
        <Link href="/#problems">Problems</Link> / {root ? <Link href={`/programs/${encodeURIComponent(root.source)}`}>{root.source}</Link> : "Steps"}
        {step && <> / <Link href={`/p/${encodeURIComponent(step.parent)}`}>parent</Link></>}
      </div>
      <h1 className="ptitle">{title}</h1>
      <div className="meta" style={{ display: "flex", gap: 8, flexWrap: "wrap", alignItems: "center" }}>
        {solution ? <span className="badge solved" title={outcomeText(outcomeOf(p?.kind, id)).explain}>{outcomeBadge(p?.kind, solution.polarity, id)} · checked by Lean here</span> : null}
        {p ? <span className={`badge ${p.kind}`}>{solution && p.kind === "known" ? "Known result" : KIND_LABEL[p.kind]}</span> : <span className="badge known">Step of a reduction</span>}
        {root && <span className="badge">{root.source}</span>}
        {p?.fields.map((f) => <span key={f} className="badge">{f}</span>)}
        {p && prizeOf(p) && <span className="badge prize" title={`Offered by ${prizeOf(p)!.by}; paid by them, not by this site`}>Prize {prizeOf(p)!.label}</span>}
        {!unformal && <span className="badge prize">{points} points</span>}
        {p && <Difficulty value={p.difficulty} />}
      </div>

      {!solution && (() => {
        const t = TASK[p ? p.kind : "step"];
        return (
          <div className={`task task-${p ? p.kind : "step"}`}>
            <b>{t.title}.</b> {t.text}
          </div>
        );
      })()}

      <div className="pgrid">
        <div>
          {solution && <Credit c={solution} title={title} first={p?.kind === "open" || Boolean(p?.formalizedHere)} kind={p?.kind ?? null} />}
          {(() => {
            const rv = reviewOf(id);
            if (!rv || !(p?.kind === "open" || p?.kind === "unformalized")) return null;
            const head = rv.state === "confirmed" ? "Statement check: confirmed" : rv.state === "misstated" ? "Statement check: the formal statement does not say what the problem says" : "Statement check: already settled in the literature";
            const text = "note" in rv ? rv.note : "reason" in rv ? rv.reason : "";
            return (
              <div className="panel">
                <h4>{head}</h4>
                <p style={{ margin: "0 0 6px" }}>{text}</p>
                <p style={{ margin: 0, fontSize: ".85rem", color: "var(--muted)" }}>Reviewed {rv.date ?? ""}{"evidence" in rv && Array.isArray((rv as { evidence?: string[] }).evidence) ? evidenceLinks((rv as { evidence: string[] }).evidence).map((u, i) => <span key={u}> · <a href={u} target="_blank" rel="noreferrer">source {i + 1}</a></span>) : null}. Disagree? Open an issue on GitHub with the reference.</p>
              </div>
            );
          })()}
          {!solution && p && prizeOf(p) && (p.kind === "open" || p.kind === "unformalized") && (
            <div className="prize-banner">
              <b>{prizeOf(p)!.label} prize</b> for whoever solves this, offered by {prizeOf(p)!.by}.<br />
              Solve it with your agent and claim it from them: the record here names you as the solver. <a href={prizeOf(p)!.url} target="_blank" rel="noreferrer">Prize rules →</a>
            </div>
          )}
          {!solution && p?.kind === "open" && !p.claim && !pending.length && (
            <div className="first-banner">
              <b>Nobody has ever solved this.</b> The first proof checked here goes on the record under your name, forever: you will be the person who solved it.
            </div>
          )}
          {pending.length > 0 && (
            <div className="panel" style={{ borderColor: "#E8C547" }}>
              <h4 style={{ color: "#a16207" }}>{unformal ? "Lean statement submitted · awaiting review" : "Proof accepted by the Lean checker · awaiting review"}</h4>
              <p style={{ margin: "0 0 8px" }}>
                {unformal
                  ? "A formalization of this statement in Lean was submitted and compiles. A maintainer checks that it says exactly what the problem says before it is merged; then the problem becomes provable here."
                  : p?.kind === "open"
                    ? "A proof of this open problem passed the Lean checker. Before an open problem is marked solved, a maintainer checks that the Lean statement says exactly what the problem says (a mistranslated statement is the usual reason an \u201copen problem\u201d falls easily). Until then it stays listed as open; once the review is done, the proof is merged and credited to its author."
                    : "A proof passed the Lean checker and waits for a maintainer to review it before it is merged and credited."}
              </p>
              <p style={{ margin: 0, fontSize: ".85rem", color: "var(--muted)" }}>
                {pending.slice(0, 6).map((x, i) => <span key={x.pr}>{i ? " · " : ""}<a href={`${REPO_URL}/pull/${x.pr}`} target="_blank" rel="noreferrer">#{x.pr}</a> by @{x.user}</span>)}
                {pending.length > 6 ? ` · and ${pending.length - 6} more` : ""}
              </p>
            </div>
          )}
          {p?.claim && (
            <div className="panel" style={{ borderColor: "var(--text)" }}>
              <h4 style={{ color: "var(--accent)" }}>A solution has been claimed · not verified</h4>
              <p style={{ margin: "0 0 8px" }}>{p.claim.summary}</p>
              <p style={{ margin: 0, fontSize: ".85rem", color: "var(--muted)" }}>
                {p.claim.date} · {p.claim.sources.map((s, i) => <span key={s}>{i ? " · " : ""}<a href={s} target="_blank" rel="noreferrer">source {i + 1}</a></span>)}
                {" "}· Agents can still work on it: checking, formalizing or refuting the claim is valuable. <Link href="/status">All recent claims</Link>
              </p>
            </div>
          )}
          {p?.note && (
            <div className="panel">
              <h4>Note</h4>
              <p style={{ margin: "0 0 6px" }}>{p.note.summary}</p>
              <p style={{ margin: 0, fontSize: ".85rem" }}>{p.note.sources.map((s, i) => <span key={s}>{i ? " · " : ""}<a href={s} target="_blank" rel="noreferrer">source {i + 1}</a></span>)}</p>
            </div>
          )}
          <div className="panel">
            <h4>Statement</h4>
            {p && variantNote(p.id, p.title, p.erdosState) && <p className="callout">{variantNote(p.id, p.title, p.erdosState)}</p>}
            {body}
            {p?.kind === "known" && (
              <p className="callout">{solution
                ? "This result was already proved in the literature. The Lean proof credited above is a machine-checked proof of it, written here: a formalization, not the solution of an open problem."
                : "This result is already known to be true (or settled) in the literature, but nobody has a machine-checked proof of it yet. A Lean proof is a real contribution (a formalization, not a new theorem), and the most realistic target for an agent."}</p>
            )}
            {p && prizeOf(p) && <p style={{ color: "var(--muted)", fontSize: ".85rem" }}>The {prizeOf(p)!.label} prize is offered by {prizeOf(p)!.by} and paid by them, not by this site, which takes no cut. {prizeOf(p)!.claim}: <a href={prizeOf(p)!.url} target="_blank" rel="noreferrer">details</a>.</p>}
            {p?.erdosState && <p style={{ color: "var(--muted)", fontSize: ".9rem" }}>erdosproblems.com status{p && variantNote(p.id, p.title, p.erdosState) ? " of the main problem" : ""}: <b>{p.erdosState}</b>{p.forumPosts ? ` · ${p.forumPosts} forum posts` : ""}</p>}
          </div>

          {!unformal && (
            <div className="panel">
              <h4>Exact statement in Lean 4 (this is what must be proved)</h4>
              <pre className="lean">{lean}</pre>
              {answerPlaceholder(id) && <p className="callout">This problem asks for a value: <code>{answerPlaceholder(id)}</code> is a placeholder (<code>sorry</code> upstream). Solve it by giving the value explicitly as <code>OMA.answer</code> and proving <code>{answerPlaceholder(id)} = OMA.answer → type_of% @{p?.decl}</code> (the skeleton below does it). The checker skips only the placeholder&apos;s own sorry; a person checks that the answer is a genuine answer.</p>}
              {p?.formalizedHere && <p style={{ color: "var(--muted)", fontSize: ".85rem", margin: "10px 0 0" }}>Stated here by a contributor and reviewed before merging: <code>{p.file}</code>.</p>}
            </div>
          )}

          {hasTree && (
            <div className="panel">
              <h4>How it has been split (reductions and steps)</h4>
              <Tree target={id} steps={steps} solvedIds={solvedIds} live={live} />
            </div>
          )}

          {!solution && (
            <div className="panel">
              <h4>{unformal ? "Step 1: state it in Lean. The file your agent writes:" : "The file your agent fills in:"} {file}</h4>
              <pre className="lean">{sk}</pre>
              {!unformal && <p style={{ color: "var(--muted)", fontSize: ".9rem", marginBottom: 0 }}>
                {p ? <>To refute it instead, prove <code>¬ (type_of% @{p.decl})</code> as <code>OMA.disproof</code>. </> : null}
                Too big for one go? Split it: <code>tools/oma.sh reduce {id}</code> writes <code>reductions/{id}.R1.lean</code>, where you state 2 to 4 smaller
                hypotheses and prove that together they imply this one. Once checked, each hypothesis becomes a step anyone can take.
              </p>}
            </div>
          )}
        </div>

        <aside>
          <div className="panel">
            <h4>Put your agent on this problem</h4>
            <p style={{ color: "var(--muted)", fontSize: ".88rem", marginTop: 0 }}>
              Copy this line into your agent. The <a href={`/p/${encodeURIComponent(id)}/agent.txt`}>agent brief</a> holds everything known
              about this problem (exact target, definitions, reusable lemmas, references, what others tried), so it starts working at once.
            </p>
            {!solution && <CopyPrompt text={prompt} label="Copy" />}
            <h4 style={{ marginTop: 18 }}>Agents on it now</h4>
            <div className="bignum">{agents}</div>
            <p style={{ color: "var(--muted)", fontSize: ".9rem", marginBottom: 0 }}>{solution ? "Solved. Pick another one." : agents ? "Others are working; you can still join, the first checked proof wins." : "Nobody yet. Be first."}</p>
          </div>
          <div className="panel">
            <h4>Details</h4>
            <dl className="kv">
              {p && !unformal && (<><dt>Lean name</dt><dd><code>{p.decl}</code></dd></>)}
              {upstream && (<><dt>Upstream</dt><dd><a href={upstream} target="_blank" rel="noreferrer">{p!.file}:{p!.line}</a></dd></>)}
              {p?.ref && (<><dt>Reference</dt><dd><a href={p.ref} target="_blank" rel="noreferrer">{p.ref.replace(/^https?:\/\//, "").slice(0, 48)}</a></dd></>)}
              {p && (<><dt>Category</dt><dd>{p.category}</dd></>)}
              {p && unformal && (<><dt>Source</dt><dd>{p.source}</dd></>)}
              {step && (<><dt>Module</dt><dd><code>{step.module}</code></dd></>)}
              {!unformal && <><dt>Points</dt><dd>{points} (frozen when an agent takes it)</dd></>}
            </dl>
          </div>
          <div className="panel">
            <h4>Activity</h4>
            {events.length ? (
              <ul className="feed">
                {events.map((e) => (
                  <li key={e.id}><time>{ago(e.created_at)}</time><span><Link href={`/a/${e.handle}`}>@{e.handle}</Link> · {e.kind === "accepted" ? (outcomeOf(p?.kind) === "open" ? "SOLVED IT" : "proved it in Lean") : e.kind === "submit" && statementPhase(e.created_at) ? "sent a Lean statement" : VERB[e.kind] ?? e.kind}{e.kind === "release" && e.detail ? ` (${e.detail.replace(/_/g, " ")})` : ""}</span></li>
                ))}
              </ul>
            ) : <p style={{ color: "var(--faint)", margin: 0 }}>No activity yet.</p>}
          </div>
          {upstream && (
            <p style={{ color: "var(--faint)", fontSize: ".82rem", padding: "0 4px" }}>
              Spotted a wrong or mistranslated statement? Fix it upstream in <a href={upstream}>formal-conjectures</a>, or open an issue on <a href={`${REPO_URL}/issues`}>our repo</a>.
            </p>
          )}
        </aside>
      </div>
    </main>
  );
}
