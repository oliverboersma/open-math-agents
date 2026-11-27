import { avatarUrl } from "@/lib/avatar";
import type { Metadata } from "next";
import Link from "@/components/Link";
import { notFound } from "next/navigation";
import PrintButton from "@/components/PrintButton";
import { certificateFor, CertificateUnavailable, ROLE_LABEL } from "@/lib/cert";
import { getProblem } from "@/lib/catalog";

export const revalidate = 600;
type Props = { params: Promise<{ id: string; handle: string }> };

export async function generateMetadata({ params }: Props): Promise<Metadata> {
  const { id, handle } = await params;
  return { title: `Certificate · @${decodeURIComponent(handle)} · ${decodeURIComponent(id)}`, robots: { index: false } };
}

const long = (iso: string) => new Date(iso).toLocaleDateString("en-GB", { day: "numeric", month: "long", year: "numeric", timeZone: "UTC" });

export default async function CertificatePage({ params }: Props) {
  const { id: rawId, handle: rawHandle } = await params;
  const id = decodeURIComponent(rawId), handle = decodeURIComponent(rawHandle);
  if (!/^[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})$/.test(handle)) notFound();
  let s: Awaited<ReturnType<typeof certificateFor>>;
  try {
    s = await certificateFor(id, handle);
  } catch (e) {
    if (!(e instanceof CertificateUnavailable)) throw e;
    // The database cannot give the shares right now: the solution is known, so say so instead of a 404.
    const sol = e.solution;
    return (
      <main className="wrap certpage">
        <article className="cert">
          <div className="cert-kind">Certificate of contribution</div>
          <p className="cert-lead">@{handle} is credited on the Lean-checked {sol.polarity === "disproof" ? "refutation" : "proof"} of</p>
          <h1 className="cert-title">{getProblem(id)?.title ?? id}</h1>
          <p className="cert-sub">checked by the Lean 4 kernel on {long(sol.created_at)} · <a href={sol.pr_url.replace(/#closed$/, "")}>pull request</a></p>
          <p className="callout">The signed certificate (with each contributor&apos;s share) cannot be produced right now because the coordination
            database is not answering. Reload this page in a few minutes.</p>
        </article>
        <div className="cert-actions"><Link className="btn" href={`/p/${encodeURIComponent(id)}`}>Problem page</Link></div>
      </main>
    );
  }
  if (!s) notFound();
  const c = s.certificate;
  const json = `/api/certificate?problem=${encodeURIComponent(id)}&handle=${encodeURIComponent(c.holder.handle)}`;
  return (
    <main className="wrap certpage">
      <article className="cert">
        <div className="cert-top">
          {/* eslint-disable-next-line @next/next/no-img-element */}
          <img src="/logo-mark.png" alt="" width={44} height={44} />
          <span>Left to Solve</span>
        </div>
        <div className="cert-kind">Certificate of contribution</div>
        <p className="cert-lead">This certifies that</p>
        <div className="cert-name">
          {/* eslint-disable-next-line @next/next/no-img-element */}
          <img src={avatarUrl(c.holder.handle, 120)} alt="" width={60} height={60} />
          @{c.holder.handle}
        </div>
        <p className="cert-lead">contributed <b className="cert-pct">{c.holder.sharePercent}%</b> of the {c.firstSolution ? "first ever solution" : "machine-checked Lean proof"} of</p>
        <h1 className="cert-title">{c.problem.title}</h1>
        <p className="cert-sub">{c.firstSolution ? "Open problem" : c.problem.kind === "Warm-up" ? "Warm-up exercise" : c.problem.kind.startsWith("Known") ? "Known result (already proved in the literature), formalized in Lean" : c.problem.kind} · {c.result === "disproof" ? "refuted" : "proved"} on {long(c.solvedAt)} · checked by the Lean 4 kernel</p>
        <ul className="cert-roles">
          {c.holder.roles.map((r, i) => <li key={i}>{ROLE_LABEL[r.role] ?? r.role}: <code>{r.item}</code>{r.agent && r.agent !== "reduction" ? ` · agent ${r.agent}${r.model ? ` (${r.model})` : ""}` : ""} · <a href={r.pr}>pull request</a></li>)}
        </ul>
        {c.contributors.length > 1 && (
          <table className="t cert-table">
            <thead><tr><th>Contributor</th><th className="n">Share</th></tr></thead>
            <tbody>{c.contributors.map((x) => <tr key={x.handle}><td><Link href={`/c/${encodeURIComponent(id)}/${x.handle}`}>@{x.handle}</Link></td><td className="n">{x.sharePercent}%</td></tr>)}</tbody>
          </table>
        )}
        <div className="cert-seal">
          <div><span>Certificate</span><b>{s.id}</b></div>
          <div><span>Signature (Ed25519)</span><code>{s.signature}</code></div>
          <div><span>Verify</span><a href="/verify">lefttosolve.com/verify</a> · public key <a href="/certificate-key.json">{c.keyId}</a></div>
        </div>
      </article>
      <div className="cert-actions">
        <PrintButton />
        <a className="btn" href={json + "&download=1"}>Download the signed certificate (JSON)</a>
        <Link className="btn" href={`/p/${encodeURIComponent(id)}`}>Problem page</Link>
      </div>
      <p className="sub" style={{ maxWidth: 760 }}>
        Shares: a direct proof is 100%; a problem closed through a reduction is split by the points of its steps, the reduction&apos;s author counting
        as one average step, and a step closed through its own reduction is split again the same way. The certificate is signed by Left to Solve: changing
        any character breaks the signature, which anyone can check at /verify or offline with the public key.
      </p>
    </main>
  );
}
