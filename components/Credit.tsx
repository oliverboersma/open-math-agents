import { avatarUrl } from "@/lib/avatar";
import Link from "@/components/Link";
import { SITE } from "@/lib/site";
import { outcomeBadge, outcomeOf, outcomeText } from "@/lib/outcome";

export type CreditData = {
  problem_id: string; handle: string; agent: string | null; model: string | null; polarity: string;
  pr_url: string; points: number; contributors: string[] | null; created_at: string;
};

export function citation(c: CreditData, title: string, kind: string | null = null) {
  const o = outcomeOf(kind, c.problem_id);
  const tool = [c.agent && c.agent !== "reduction" ? c.agent : null, c.model].filter(Boolean).join(", ");
  const others = (c.contributors ?? []).filter((h) => h !== c.handle);
  return `@${c.handle}${tool ? ` (AI agent: ${tool})` : ""}${others.length ? `, with ${others.map((h) => "@" + h).join(", ")}` : ""}. ` +
    `${o === "known" ? "Lean formalization of the known result" : o === "warmup" ? "Warm-up" : c.polarity === "disproof" ? "Refutation of" : o === "open" ? "Solution of the open problem" : o === "pending" ? "Lean-accepted proof (statement being verified) of the open problem" : o === "misstated" ? "Proof of a mis-stated formal version of" : "Proof of"} "${title}", checked by the Lean 4 kernel. ` +
    `Left to Solve, ${c.created_at.slice(0, 10)}. ${c.pr_url.replace(/#closed$/, "")} · ${SITE}/p/${encodeURIComponent(c.problem_id)}`;
}

export default function Credit({ c, title, first: firstAsked = false, kind = null }: { c: CreditData; title: string; first?: boolean; kind?: string | null }) {
  // "Solved for the first time" only once the formal statement is confirmed to be the open problem.
  const first = firstAsked && outcomeOf(kind, c.problem_id) === "open";
  const others = (c.contributors ?? []).filter((h) => h !== c.handle);
  return (
    <div className="panel" style={{ borderColor: "var(--ok)" }}>
      <h4 style={{ color: "var(--warmup)" }}>{first ? (c.polarity === "disproof" ? "Refuted for the first time" : "Solved for the first time") : outcomeBadge(kind, c.polarity, c.problem_id)} · credited to the owner of the agent</h4>
      {!first && <p style={{ margin: "0 0 12px", color: "var(--muted)", fontSize: ".9rem" }}>{outcomeText(outcomeOf(kind, c.problem_id)).explain}</p>}
      {first && <p style={{ margin: "0 0 12px", fontWeight: 600 }}>An open problem nobody had solved before. On the record, @{c.handle} is the person who solved it.</p>}
      <div className="credit">
        {/* eslint-disable-next-line @next/next/no-img-element */}
        <img src={avatarUrl(c.handle, 88)} alt="" width={44} height={44} />
        <div>
          <div style={{ fontWeight: 650, fontSize: "1.05rem" }}><Link href={`/a/${c.handle}`}>@{c.handle}</Link></div>
          <div style={{ color: "var(--muted)", fontSize: ".9rem" }}>
            {c.agent === "reduction" ? "closed through a reduction into steps" : <>agent <b>{c.agent ?? "not declared"}</b>{c.model ? <> · model <b>{c.model}</b></> : null}</>}
            {" "}· {c.points} points · {c.created_at.slice(0, 10)} · <a href={c.pr_url.replace(/#closed$/, "")}>pull request</a>
          </div>
          {others.length > 0 && (
            <div style={{ color: "var(--muted)", fontSize: ".9rem", marginTop: 4 }}>
              with {others.map((h, i) => <span key={h}>{i ? ", " : ""}<Link href={`/a/${h}`}>@{h}</Link></span>)}
            </div>
          )}
        </div>
      </div>
      <p style={{ margin: "12px 0 0", fontSize: ".9rem" }}>
        <b>Signed certificates:</b>{" "}
        {[c.handle, ...others].map((h, i) => <span key={h}>{i ? " · " : ""}<Link href={`/c/${encodeURIComponent(c.problem_id)}/${h}`}>@{h}</Link></span>)}
        {" "}<span style={{ color: "var(--faint)" }}>(share of each contributor, verifiable at <Link href="/verify">/verify</Link>)</span>
      </p>
      <p style={{ color: "var(--faint)", fontSize: ".82rem", margin: "12px 0 6px" }}>Cite this result:</p>
      <div className="cite">{citation(c, title, kind)}</div>
    </div>
  );
}
