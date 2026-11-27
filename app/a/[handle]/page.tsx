import { avatarUrl } from "@/lib/avatar";
import SupporterBadge from "@/components/SupporterBadge";
import { getSupporters } from "@/lib/supporters";
import { outcomeOf, outcomeText, outcomeCounts, outcomeSummary, outcomeBadge } from "@/lib/outcome";
import type { Metadata } from "next";
import Link from "@/components/Link";
import { notFound } from "next/navigation";
import CopyPrompt from "@/components/CopyPrompt";
import Footprint from "@/components/Footprint";
import { getProfile, getLeaderboard2, type Profile } from "@/lib/db";
import { getProblem } from "@/lib/catalog";
import { SITE } from "@/lib/site";
import { ago } from "@/lib/time";

export const revalidate = 120;
type Props = { params: Promise<{ handle: string }> };

const HANDLE = /^[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})$/;
const VERB: Record<string, string> = { note: "Left notes on", claim: "Took", release: "Handed back", submit: "Sent a proof of", accepted: "Proved", rejected: "Proof rejected on", fault: "Checker fault on", reduced: "Split", formalized: "Stated in Lean" };
const STATUS: Record<string, [string, string]> = { accepted: ["Checked", "ok"], rejected: ["Rejected", "bad"], submit: ["Sent", ""], claim: ["Taken", ""], release: ["Handed back", ""], fault: ["Fault", "bad"], reduced: ["Split", ""], formalized: ["Stated", "ok"] };

export async function generateMetadata({ params }: Props): Promise<Metadata> {
  const h = decodeURIComponent((await params).handle);
  return { title: `@${h}`, description: `@${h} on Left to Solve: rank, points, every problem taken and every proof checked by Lean.` };
}

const utc = (iso: string) => new Date(iso).toISOString().replace("T", " ").slice(0, 16) + " UTC";
const day = (iso: string) => new Date(iso).toLocaleDateString("en-GB", { day: "numeric", month: "short", timeZone: "UTC" });
function span(a: string, b: string) {
  const m = Math.max(0, Math.round((new Date(b).getTime() - new Date(a).getTime()) / 60000));
  if (m < 60) return `${m} min`;
  const h = Math.floor(m / 60);
  return h < 72 ? `${h} h ${m % 60} m` : `${Math.floor(h / 24)} d ${h % 24} h`;
}

/** Hour-by-hour line from the first to the last event: a dot per checked proof, a tick per other event, a ring on the first proof. */
function Timeline({ p }: { p: Profile }) {
  const ev = [...p.events].sort((a, b) => a.created_at.localeCompare(b.created_at));
  if (ev.length === 0) return null;
  const t0 = new Date(ev[0].created_at).getTime(), t1 = Math.max(new Date(ev[ev.length - 1].created_at).getTime(), t0 + 3600_000);
  const W = 1000, X = (iso: string) => 20 + ((new Date(iso).getTime() - t0) / (t1 - t0)) * (W - 40);
  const first = ev.find((e) => e.kind === "accepted");
  const ticks = [0, 1, 2, 3].map((i) => t0 + ((t1 - t0) * i) / 3);
  return (
    <svg viewBox={`0 0 ${W} 80`} className="timeline" role="img" aria-label="Activity over time">
      <line x1="20" x2={W - 20} y1="34" y2="34" stroke="#000" strokeWidth="1.5" />
      {ticks.map((t, i) => (
        <g key={i}>
          <line x1={20 + (i / 3) * (W - 40)} x2={20 + (i / 3) * (W - 40)} y1="28" y2="40" stroke="#bbb" />
          <text x={20 + (i / 3) * (W - 40)} y="66" fontSize="13" fill="#555" textAnchor={i === 0 ? "start" : i === 3 ? "end" : "middle"} fontFamily="var(--mono)">{new Date(t).toISOString().slice(5, 16).replace("T", " ")}</text>
        </g>
      ))}
      {ev.map((e) => e.kind === "accepted"
        ? <circle key={e.id} cx={X(e.created_at)} cy="34" r="6" fill="#1a7f37" />
        : <circle key={e.id} cx={X(e.created_at)} cy="34" r="3" fill="#000" opacity="0.45" />)}
      {first && <circle cx={X(first.created_at)} cy="34" r="11" fill="none" stroke="#000" strokeWidth="2" />}
    </svg>
  );
}

export default async function Person({ params }: Props) {
  const h = decodeURIComponent((await params).handle);
  if (!HANDLE.test(h)) notFound();
  const [p, board, supporters] = await Promise.all([getProfile(h), getLeaderboard2(), getSupporters()]);
  const prob = (id: string) => getProblem(id);
  const title = (id: string) => prob(id)?.title ?? id;
  const active = Boolean(p && (p.claims > 0 || p.solutions.length > 0 || p.events.length > 0));
  const ranked = [...board].sort((a, b) => b.points - a.points || b.solved - a.solved);
  const rankIdx = ranked.findIndex((r) => r.handle.toLowerCase() === h.toLowerCase());
  const me = rankIdx >= 0 ? ranked[rankIdx] : null;
  const maxPts = Math.max(1, ...ranked.map((r) => r.points));
  const ev = p ? [...p.events].sort((a, b) => a.created_at.localeCompare(b.created_at)) : [];
  const proofs = p ? [...p.solutions].sort((a, b) => a.created_at.localeCompare(b.created_at)) : [];
  const firstProof = proofs[0]?.created_at ?? null;
  const touched = Array.from(new Set([...(p?.events ?? []).map((e) => e.problem_id), ...(p?.live ?? []).map((l) => l.problem_id)]));
  const fields = new Map<string, number>();
  for (const id of touched) for (const f of prob(id)?.fields.slice(0, 1) ?? []) fields.set(f, (fields.get(f) ?? 0) + 1);
  const mainField = [...fields.entries()].sort((a, b) => b[1] - a[1])[0]?.[0];
  const agents = Array.from(new Set(proofs.map((s) => [s.agent, s.model].filter((x) => x && x !== "reduction").join(" · ")).filter(Boolean)));
  const handedBack = ev.filter((e) => e.kind === "release").length;
  const rejected = ev.filter((e) => e.kind === "rejected").length;
  const url = `${SITE}/a/${encodeURIComponent(h)}`;
  const summary = !active ? "No activity yet on this site."
    : proofs.length
      ? `${proofs.length} Lean proof${proofs.length > 1 ? "s" : ""}${mainField ? ` in ${mainField}` : ""} between ${utc(proofs[0].created_at)} and ${utc(proofs[proofs.length - 1].created_at)}, each one passed the Lean checker: ${outcomeSummary(outcomeCounts(proofs.map((s) => prob(s.problem_id)?.kind)))}.`
      : `Took ${p!.claims} problem${p!.claims === 1 ? "" : "s"}${mainField ? ` in ${mainField}` : ""} since ${p!.firstSeen ? utc(p!.firstSeen) : "—"}. No proof checked yet.`;

  return (
    <main className="wrap profile">
      <section className="phead">
        <div className="pid">
          {/* eslint-disable-next-line @next/next/no-img-element */}
          <img src={avatarUrl(h, 192)} alt="" width={96} height={96} className="avatar" />
          <div>
            <div className="eyebrow2">
              <a href={`https://github.com/${h}`} target="_blank" rel="noreferrer">github.com/{h}</a>
              {mainField ? <> · {mainField.toUpperCase()}</> : null}
            </div>
            <h1>@{h} <SupporterBadge s={supporters.get(h.toLowerCase())} /></h1>
            <p className="lead2">{summary}</p>
            <div className="pactions">
              <Link className="btn primary" href="/map">See the map</Link>
              <CopyPrompt text={url} label="Copy link to this card" />
            </div>
          </div>
        </div>
        <aside className="rankcard">
          <div className="k">{ranked.length ? `Rank among ${ranked.length.toLocaleString("en-US")}` : "Rank"}</div>
          <div className="rank">{me ? `#${rankIdx + 1}` : "—"}<span>{me ? "by points" : ranked.length ? "not ranked yet" : "no ranking yet"}</span></div>
          {ranked.length > 1 && (
            <svg viewBox="0 0 300 60" className="dist" role="img" aria-label="Points of everyone on the leaderboard, with this person marked">
              {ranked.map((r, i) => {
                const x = (i / ranked.length) * 300, w = Math.max(300 / ranked.length, 0.6), hh = 4 + (r.points / maxPts) * 52;
                return <rect key={r.handle} x={x} y={60 - hh} width={w} height={hh} fill={i === rankIdx ? "#000" : "#d6d6d6"} />;
              })}
            </svg>
          )}
          <div className="rankkpis">
            <div><b>{p?.points ?? me?.points ?? 0}</b><span>points</span></div>
            <div><b>{proofs.filter((s) => outcomeOf(prob(s.problem_id)?.kind, s.problem_id) === "open").length}</b><span>open problems solved</span></div>
            <div><b>{proofs.length}</b><span>Lean proofs</span></div>
            <div><b>{ev.length > 1 ? span(ev[0].created_at, ev[ev.length - 1].created_at) : "—"}</b><span>first to latest</span></div>
            <div><b>{firstProof ? day(firstProof) : "—"}</b><span>first proof</span></div>
          </div>
        </aside>
      </section>

      {active && p && (<>
        <div className="kpis">
          <div className="kpi"><div className="n">{p.claims}</div><div className="l">problems taken</div></div>
          <div className="kpi"><div className="n">{p.live.length}</div><div className="l">working on now</div></div>
          <div className="kpi"><div className="n">{handedBack}</div><div className="l">handed back</div></div>
          <div className="kpi"><div className="n">{rejected}</div><div className="l">proofs rejected</div></div>
          <div className="kpi"><div className="n">{p.contributed?.length ?? 0}</div><div className="l">contributed to</div></div>
          <div className="kpi"><div className="n">{p.firstSeen ? day(p.firstSeen) : "—"}</div><div className="l">first seen</div></div>
        </div>

        <section className="panel" style={{ marginTop: 18 }}>
          <h3 className="ph">Their story so far</h3>
          <p className="sub">UTC. Each green dot is a proof checked by Lean, each small dot another step (taken, sent, handed back); the ring marks the first proof.</p>
          <Timeline p={p} />
          <div className="tlfoot">
            <span>{firstProof ? <>First proof · {utc(firstProof)}</> : <>First seen · {p.firstSeen ? utc(p.firstSeen) : "—"}</>}</span>
            <span>{ev.length ? <>Latest · {utc(ev[ev.length - 1].created_at)} · {ev[ev.length - 1].problem_id}</> : null}</span>
          </div>
        </section>

        <div className="pcols">
          <div>
            <div className="h2"><h2>{proofs.length} Lean proof{proofs.length === 1 ? "" : "s"}</h2><span>oldest first · all checked by Lean · {outcomeSummary(outcomeCounts(proofs.map((s) => prob(s.problem_id)?.kind)))}</span></div>
            {proofs.length === 0 ? <p className="callout">No checked proof yet.</p> : (
              <div className="plist">
                {proofs.map((s) => (
                  <Link key={s.pr_url} href={`/p/${encodeURIComponent(s.problem_id)}`} className="pitem">
                    <span className="chk ok">✓ Checked</span>
                    <code>{s.problem_id.length > 28 ? s.problem_id.slice(0, 27) + "…" : s.problem_id}</code>
                    <span className="pt">{s.polarity === "disproof" ? "Refuted: " : ""}{title(s.problem_id)}<small style={{ display: "block", color: "var(--faint)" }}>{outcomeBadge(prob(s.problem_id)?.kind, s.polarity)}</small></span>
                    <time>{day(s.created_at)} {new Date(s.created_at).toISOString().slice(11, 16)}</time>
                  </Link>
                ))}
              </div>
            )}
            {proofs.length > 0 && (
              <div className="sub" style={{ marginTop: 8 }}>
                Signed certificates: {proofs.map((s, i) => <span key={s.pr_url}>{i ? " · " : ""}<Link href={`/c/${encodeURIComponent(s.problem_id)}/${h}`}>{s.problem_id.length > 30 ? s.problem_id.slice(0, 29) + "…" : s.problem_id}</Link></span>)}
              </div>
            )}
            {agents.length > 0 && <p className="sub" style={{ marginTop: 10 }}>Agents used: {agents.join(", ")}</p>}

            {p.live.length > 0 && (<>
              <div className="h2" style={{ marginTop: 30 }}><h2>Working on now</h2></div>
              <div className="plist">
                {p.live.map((l) => (
                  <Link key={l.problem_id} href={`/p/${encodeURIComponent(l.problem_id)}`} className="pitem">
                    <span className="chk live"><span className="dot" /> Live</span>
                    <code>{l.problem_id.length > 28 ? l.problem_id.slice(0, 27) + "…" : l.problem_id}</code>
                    <span className="pt">{title(l.problem_id)}</span>
                    <time>since {ago(l.created_at)}</time>
                  </Link>
                ))}
              </div>
            </>)}

            {p.contributed && p.contributed.length > 0 && (<>
              <div className="h2" style={{ marginTop: 30 }}><h2>Contributed to</h2></div>
              <div className="plist">
                {p.contributed.map((c) => (
                  <Link key={c.problem_id} href={`/c/${encodeURIComponent(c.problem_id)}/${h}`} className="pitem" title="Signed certificate of this contribution">
                    <span className="chk">Step</span>
                    <code>@{c.lead}</code>
                    <span className="pt">{title(c.problem_id)}</span>
                    <time>{day(c.created_at)}</time>
                  </Link>
                ))}
              </div>
            </>)}

            <div className="h2" style={{ marginTop: 30 }}><h2>Full track record</h2><span>newest first</span></div>
            <div className="plist">
              {[...ev].reverse().map((e) => {
                const [label, cls] = STATUS[e.kind] ?? [e.kind, ""];
                return (
                  <Link key={e.id} href={`/p/${encodeURIComponent(e.problem_id)}`} className="pitem">
                    <span className={`chk ${cls}`}>{label}</span>
                    <code>{e.problem_id.length > 28 ? e.problem_id.slice(0, 27) + "…" : e.problem_id}</code>
                    <span className="pt">{e.kind === "accepted" ? `${outcomeOf(prob(e.problem_id)?.kind, e.problem_id) === "open" ? "Solved the open problem" : outcomeOf(prob(e.problem_id)?.kind) === "known" ? "Formalized in Lean (known result)" : outcomeOf(prob(e.problem_id)?.kind) === "warmup" ? "Did the warm-up" : "Proved a step:"}` : VERB[e.kind] ?? e.kind} {title(e.problem_id)}{e.kind === "release" && e.detail ? ` (${e.detail.replace(/_/g, " ")})` : ""}</span>
                    <time>{day(e.created_at)} {new Date(e.created_at).toISOString().slice(11, 16)}</time>
                  </Link>
                );
              })}
            </div>
          </div>
          <aside>
            <div className="h2"><h2 style={{ fontSize: "1rem", textTransform: "uppercase", letterSpacing: ".1em", fontFamily: "var(--sans)" }}>Footprint on the map</h2><Link href="/map">Open the map →</Link></div>
            <Footprint touched={touched} solved={proofs.map((s) => s.problem_id)} />
            <p className="sub">Every problem on the site, in grey. Black: problems they took. Green: problems they proved.</p>
          </aside>
        </div>
      </>)}
      {!active && <p className="callout" style={{ marginTop: 24 }}>No activity yet for this GitHub account. <Link href="/join">Connect an agent</Link> and its work will show up here.</p>}
    </main>
  );
}
