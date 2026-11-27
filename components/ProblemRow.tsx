import Link from "@/components/Link";

export type RowData = {
  id: string; title: string; source: string; kind: "open" | "known" | "warmup" | "unformalized"; fields: string[];
  difficulty: number; prize: string | null; excerpt: string; liveAgents?: number; solved?: boolean; claimed?: boolean;
};

const KIND = { open: "Open: find a proof", known: "Known: formalize the proof", warmup: "Warm-up", unformalized: "Open · needs a Lean statement" } as const;

export function Difficulty({ value }: { value: number }) {
  return (
    <span className="diff" title="Heuristic difficulty, 1–100. See the join page for how it is computed.">
      <span className="dl">difficulty</span>
      <i><b style={{ width: `${value}%` }} /></i>
      <b className="dv">{value}<small>/100</small></b>
    </span>
  );
}

export default function ProblemRow({ p }: { p: RowData }) {
  return (
    <Link className="row" href={`/p/${encodeURIComponent(p.id)}`}>
      <div>
        <h3>{p.title}</h3>
        <p>{p.excerpt}</p>
        <div className="meta">
          <span className={`badge ${p.kind}`}>{p.solved && p.kind === "known" ? "Known result" : KIND[p.kind]}</span>
          <span className="badge">{p.source}</span>
          {p.fields.slice(0, 2).map((f) => <span key={f} className="badge">{f}</span>)}
          {p.prize && <span className="badge prize" title="Erdős prize, offered by a third party; not paid by this site">Erdős prize {p.prize}</span>}
        </div>
      </div>
      <div className="side">
        {p.solved ? <span className="badge solved" title="Checked by Lean on this site">{p.kind === "open" || p.kind === "unformalized" ? "Solved" : p.kind === "known" ? "Formalized in Lean" : "Warm-up done"}</span> : null}
        {p.claimed ? <span className="badge prize" title="A solution has been announced but is not verified">Claimed solved</span> : null}
        {p.liveAgents ? <span className="badge live"><span className="dot" /> {p.liveAgents} live</span> : null}
        <Difficulty value={p.difficulty} />
      </div>
    </Link>
  );
}
