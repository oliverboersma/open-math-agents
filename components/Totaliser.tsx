// Progress against the goal: every problem of the catalogue settled in Lean. One bar, three parts (solved, someone on
// it now, nobody yet), and the next milestone. Numbers come from the same live stats as the rest of the home page.
const fmt = (n: number) => n.toLocaleString("en-US");
const MILESTONES = [100, 250, 500, 1000, 2500, 5000, 10000, 25000, 50000];

export default function Totaliser({ total, solved, inProgress, openSolved }: { total: number; solved: number; inProgress: number; openSolved: number }) {
  const busy = Math.min(inProgress, Math.max(0, total - solved));
  const untouched = Math.max(0, total - solved - busy);
  const pct = (n: number) => (total ? (100 * n) / total : 0);
  const next = MILESTONES.find((m) => m > solved) ?? total;
  const prev = [...MILESTONES].reverse().find((m) => m <= solved) ?? 0;
  const toNext = Math.max(0, next - solved);
  const stepPct = next > prev ? Math.round((100 * (solved - prev)) / (next - prev)) : 100;
  return (
    <section className="wrap totaliser" aria-label="Progress against the goal">
      <div className="tot-card">
      <div className="tot-head">
        <h2>Progress: {fmt(solved)} of {fmt(total)} problems settled in Lean</h2>
        <span className="tot-pct">{pct(solved) < 1 ? pct(solved).toFixed(2) : pct(solved).toFixed(1)}%</span>
      </div>
      <div className="tot-bar" role="img" aria-label={`${fmt(solved)} solved, ${fmt(busy)} in progress, ${fmt(untouched)} untouched`}>
        <span className="tot-solved" style={{ width: `${pct(solved)}%` }} />
        <span className="tot-busy" style={{ width: `${pct(busy)}%` }} />
      </div>
      <div className="tot-legend">
        <span><i className="tot-solved" /> {fmt(solved)} solved</span>
        <span><i className="tot-busy" /> {fmt(busy)} in progress now</span>
        <span><i className="tot-rest" /> {fmt(untouched)} untouched</span>
        <span className="tot-open">{fmt(openSolved)} of them open problems solved (statement checked)</span>
      </div>
      <div className="tot-next">
        Next milestone: <b>{fmt(next)}</b> solved, {fmt(toNext)} to go
        <span className="tot-mini" aria-hidden="true"><span style={{ width: `${stepPct}%` }} /></span>
      </div>
      </div>
    </section>
  );
}
