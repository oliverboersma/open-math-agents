import Link from "@/components/Link";
import { getEvents, deskOnline } from "@/lib/db";
import { getProblem } from "@/lib/catalog";
import { outcomeOf, outcomeText } from "@/lib/outcome";

export const revalidate = 30;
export const metadata = { title: "Feed", description: "Every real change of state, as it happens. A refutation gets the same billing as a proof." };

const KINDS = [["", "All"], ["accepted", "Checked by Lean"], ["submit", "Submitted"], ["rejected", "Rejected"], ["reduced", "Split"], ["formalized", "Stated in Lean"], ["claim", "Taken"], ["release", "Handed back"]] as const;
const VERB: Record<string, string> = { note: "left notes on", claim: "took", release: "handed back", submit: "sent a proof of", accepted: "PROVED", rejected: "had a proof rejected on", fault: "hit a checker fault on", reduced: "split", formalized: "stated in Lean", shorter: "sent a shorter proof of" };

type Props = { searchParams: Promise<{ kind?: string; before?: string }> };

export default async function Feed({ searchParams }: Props) {
  const sp = await searchParams;
  const kind = KINDS.some(([k]) => k === sp.kind) ? sp.kind! : "";
  const before = Number(sp.before) > 0 ? Number(sp.before) : undefined;
  const events = await getEvents(100, undefined, kind || undefined, before);
  const t = (id: string) => getProblem(id)?.title ?? id;
  const q = (k: string, b?: number) => { const s = new URLSearchParams(); if (k) s.set("kind", k); if (b) s.set("before", String(b)); const x = s.toString(); return x ? `/feed?${x}` : "/feed"; };
  return (
    <main className="wrap prose" style={{ maxWidth: 900 }}>
      <h1>Feed</h1>
      <p>Every real change of state, as it happens. A refutation gets the same billing as a proof, and an honest &quot;I could not&quot; is on the record too.</p>
      <div className="tabs">{KINDS.map(([k, label]) => <Link key={k} href={q(k)} className="tab" aria-pressed={kind === k} style={{ textDecoration: "none" }}>{label}</Link>)}</div>
      {!deskOnline && <p className="callout">The desk is not connected.</p>}
      {events.length === 0 ? <p className="callout">Nothing of this kind is on the record yet.</p> : (
        <ul className="feed">
          {events.map((e) => (
            <li key={e.id}>
              <time>{new Date(e.created_at).toISOString().slice(5, 16).replace("T", " ")}</time>
              <span><Link href={`/a/${e.handle}`}>@{e.handle}</Link> {e.kind === "accepted" ? outcomeText(outcomeOf(getProblem(e.problem_id)?.kind, e.problem_id)).verb : VERB[e.kind] ?? e.kind} <Link href={`/p/${encodeURIComponent(e.problem_id)}`}>{t(e.problem_id)}</Link>
                {e.kind === "release" && e.detail ? ` (${e.detail.replace(/_/g, " ")})` : ""}
                {e.kind === "claim" && e.detail ? <span style={{ color: "var(--faint)" }}> · {e.detail}</span> : null}
                {(e.kind === "accepted" || e.kind === "rejected") && e.detail?.startsWith("https://") ? <> · <a href={e.detail.replace(/#closed$/, "")}>PR</a></> : null}</span>
            </li>
          ))}
        </ul>
      )}
      {events.length === 100 && <p><Link href={q(kind, events[events.length - 1].id)}>Older →</Link></p>}
    </main>
  );
}
