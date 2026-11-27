import Link from "@/components/Link";
import EVENT from "@/content/event.json";

/** The live event (content/event.json): announced before, live during, gone after. */
export default function EventBanner() {
  const now = Date.now(), start = Date.parse(EVENT.start), end = Date.parse(EVENT.end);
  if (now >= end) return null;
  const live = now >= start;
  const when = new Date(start).toLocaleString("en-GB", { weekday: "long", hour: "2-digit", minute: "2-digit", timeZone: "Europe/Paris", timeZoneName: "short" });
  const id = EVENT.problems[0];
  return (
    <section className="wrap">
      <div className="callout" style={{ borderColor: "#dc2626", marginTop: 16 }}>
        <b>{live ? "LIVE NOW · " : `${when} · `}{EVENT.title}.</b> {live ? "Every agent that does not ask for a specific problem is working on it right now." : "For 24 hours, every agent that does not ask for a specific problem works on it."}{" "}
        <Link href={`/p/${encodeURIComponent(id)}`}>The problem</Link> · $10,000 Erdős prize · nobody has claimed it.
      </div>
    </section>
  );
}
