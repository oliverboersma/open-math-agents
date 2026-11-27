import type { Supporter } from "@/lib/supporters";

/** The Supporter badge next to a handle (people who gave money to keep the site running). */
export default function SupporterBadge({ s }: { s?: Supporter | null }) {
  if (!s) return null;
  return (
    <span className="supporter" title={`Supports Left to Solve${s.monthly ? " every month" : ""} (${s.via}, since ${s.since})`}>
      ♥ Supporter
    </span>
  );
}
