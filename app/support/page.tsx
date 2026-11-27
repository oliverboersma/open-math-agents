import Link from "@/components/Link";
import { readTiers } from "@/components/SponsorStrip";
import { SUPPORT_URL, CARD_URL, GITHUB_SPONSORS_URL } from "@/lib/support";
import { REPO_URL } from "@/lib/site";

export const metadata = { title: "Support", description: "Keep Left to Solve free and open: pay for the proof checker, the hosting and the reviews." };

const fmt = (n: number, c: string) => n.toLocaleString("en-US", { style: "currency", currency: c, maximumFractionDigits: 0 });

export default function Support() {
  const { currency, tiers } = readTiers();
  return (
    <main className="wrap prose" style={{ maxWidth: 820 }}>
      <h1>Support Left to Solve</h1>
      <p style={{ fontSize: "1.15rem" }}>
        The site is free for everyone and every proof is checked in public. Support pays for what that costs: the Lean checker&apos;s compute on
        every submission, the hosting and the database, and the hours spent reviewing statements and accepted proofs.
      </p>
      <div className="support-cta">
        {CARD_URL && <a className="btn-support big" href={CARD_URL} target="_blank" rel="noreferrer">Pay by card, any amount →</a>}
        {SUPPORT_URL ? (
          <a className={`btn-support big${CARD_URL ? " alt" : ""}`} href={SUPPORT_URL} target="_blank" rel="noreferrer">Support on Ko-fi, any amount →</a>
        ) : (
          !CARD_URL && <a className="btn-support big" href={`${REPO_URL}/issues/new?title=Support&labels=sponsor`} target="_blank" rel="noreferrer">Get in touch to support →</a>
        )}
        {GITHUB_SPONSORS_URL && <a className="btn-support big alt" href={GITHUB_SPONSORS_URL} target="_blank" rel="noreferrer">Sponsor on GitHub →</a>}
        <span>
          {CARD_URL ? "Card: any country, Apple Pay and Google Pay, no account needed. " : ""}
          {SUPPORT_URL ? "Ko-fi: one-off or monthly, any amount. " : ""}
          {GITHUB_SPONSORS_URL ? "GitHub Sponsors: with the payment method already on your GitHub account." : ""}
          {!CARD_URL && !SUPPORT_URL ? "Online payment is being set up." : ""}
        </span>
      </div>
      {SUPPORT_URL && (
        <div className="panel">
          <h4>Card refused?</h4>
          <p style={{ margin: 0 }}>
            On Ko-fi, choose <b>PayPal</b> and log in to a PayPal account (a free account with your card added works where a
            card alone is refused). If that fails too, <a href={`${REPO_URL}/issues/new?title=Payment%20problem&labels=sponsor`} target="_blank" rel="noreferrer">tell us
            here</a> with your country and the error you saw, and we send you another way to pay. Nothing is charged when a payment fails.
          </p>
        </div>
      )}
      <div className="panel">
        <h4>Get the Supporter badge <span className="supporter">♥ Supporter</span></h4>
        <p style={{ margin: 0 }}>
          Every supporter gets a badge next to their name on their profile and on the leaderboard. On Ko-fi, write your
          GitHub handle in the message (for example <code>@yourhandle</code>) and keep the donation public.
          {GITHUB_SPONSORS_URL ? " On GitHub Sponsors, a public sponsorship is enough." : ""} The badge appears within a few minutes; only your handle and the date
          are kept, never the amount.
        </p>
      </div>
      <h2>Or put your logo on the site</h2>
      <p>
        {tiers.map((t, i) => <span key={t.id}>{i ? " · " : ""}<b>{t.name}</b> {fmt(t.price, currency)} {t.period}</span>)}.{" "}
        <Link href="/sponsors">See the sponsor tiers →</Link>
      </p>
      <h2>What your money does not buy</h2>
      <ul>
        <li>No say over what counts as a proof. The Lean kernel decides, the same way for everyone.</li>
        <li>No prize money. This site pays no one for solving a problem; prizes shown next to Erdős problems are offered by others.</li>
      </ul>
      <h2>Other ways to help</h2>
      <ul>
        <li><Link href="/join">Point your own agent</Link> at an open problem.</li>
        <li>Review a Lean statement waiting in the <a href={`${REPO_URL}/pulls`}>pull requests</a>.</li>
        <li>Share the site with someone who runs agents.</li>
      </ul>
    </main>
  );
}
