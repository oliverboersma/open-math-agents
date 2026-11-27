"use client";
import { useEffect, useRef, useState } from "react";
import ProblemRow, { type RowData } from "./ProblemRow";

type Props = { sources: string[]; fields: string[]; initial: { total: number; items: RowData[] }; counts: Record<string, number>; initialSource?: string; initialKind?: string };

const KINDS = [
  ["open", "Open problems: find a proof"],
  ["unformalized", "Open, not yet in Lean"],
  ["known", "Known results: formalize the proof"],
  ["warmup", "Warm-ups"],
  ["all", "Everything"],
] as const;

export default function Search({ sources, fields, initial, counts, initialSource, initialKind }: Props) {
  const [q, setQ] = useState("");
  const [kind, setKind] = useState(initialKind ?? "open");
  const [source, setSource] = useState(initialSource ?? "all");
  const [field, setField] = useState("all");
  const [sort, setSort] = useState("default");
  const [data, setData] = useState(initial);
  const [loading, setLoading] = useState(false);
  const first = useRef(true);

  function params(offset: number) {
    const sp = new URLSearchParams({ kind, source, field, limit: "30", offset: String(offset) });
    if (q.trim()) sp.set("q", q.trim());
    if (sort !== "default") sp.set("sort", sort);
    return sp.toString();
  }

  useEffect(() => {
    if (first.current) { first.current = false; return; }
    const ctl = new AbortController();
    const t = setTimeout(async () => {
      setLoading(true);
      try {
        const r = await fetch(`/api/problems?${params(0)}`, { signal: ctl.signal });
        const j = await r.json();
        setData({ total: j.total, items: j.items });
      } catch {}
      setLoading(false);
    }, 180);
    return () => { clearTimeout(t); ctl.abort(); };
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [q, kind, source, field, sort]);

  async function more() {
    setLoading(true);
    const r = await fetch(`/api/problems?${params(data.items.length)}`);
    const j = await r.json();
    setData((d) => ({ total: j.total, items: [...d.items, ...j.items] }));
    setLoading(false);
  }

  return (
    <div>
      <div className="searchbar">
        <input className="input q" type="search" placeholder="Search: twin primes, Erdős 3, Sidon sets, Collatz, Ramsey, Hadamard…"
          value={q} onChange={(e) => setQ(e.target.value)} aria-label="Search problems" />
        <select className="select" value={source} onChange={(e) => setSource(e.target.value)} aria-label="Source">
          <option value="all">All sources</option>
          {sources.map((s) => <option key={s} value={s}>{s}</option>)}
        </select>
        <select className="select" value={field} onChange={(e) => setField(e.target.value)} aria-label="Field">
          <option value="all">All fields</option>
          {fields.map((s) => <option key={s} value={s}>{s}</option>)}
        </select>
        <select className="select" value={sort} onChange={(e) => setSort(e.target.value)} aria-label="Sort">
          <option value="default">{q ? "Most relevant" : "Most famous first"}</option>
          <option value="famous">Most famous first</option>
          <option value="active">Most agents now</option>
          <option value="easiest">Easiest first</option>
          <option value="hardest">Hardest first</option>
          <option value="prize">Biggest prize</option>
        </select>
      </div>
      <div className="tabs" role="group" aria-label="Kind">
        {KINDS.map(([k, label]) => (
          <button key={k} className="tab" aria-pressed={kind === k} onClick={() => setKind(k)}>
            {label}{k !== "all" && counts[k] ? ` · ${counts[k].toLocaleString("en-US")}` : ""}
          </button>
        ))}
      </div>
      <div className="count">{loading ? "Searching…" : `${data.total.toLocaleString("en-US")} results`}</div>
      <div className="results">
        {data.items.map((p) => <ProblemRow key={p.id} p={p} />)}
        {data.items.length === 0 && !loading && <div className="row"><div><h3>Nothing matches.</h3><p>Try fewer words or another filter.</p></div></div>}
      </div>
      {data.items.length < data.total && (
        <button className="btn more" onClick={more} disabled={loading}>{loading ? "Loading…" : "Show 30 more"}</button>
      )}
    </div>
  );
}
