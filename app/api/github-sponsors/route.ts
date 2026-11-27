/**
 * GitHub Sponsors webhook (Sponsors dashboard > Webhooks: https://lefttosolve.com/api/github-sponsors, content type
 * application/json, event "Sponsorships"). A new public sponsorship gives the sponsor the Supporter badge.
 * Needs the Worker secret GH_SPONSORS_WEBHOOK_SECRET (the secret typed in that webhook's settings).
 */
import { createHmac } from "node:crypto";
import { addSupporter, safeEqual, workerSecret, HANDLE_RE } from "@/lib/supporters";

const json = (b: unknown, status = 200) => new Response(JSON.stringify(b), { status, headers: { "content-type": "application/json" } });

export async function POST(req: Request) {
  const secret = workerSecret("GH_SPONSORS_WEBHOOK_SECRET");
  if (!secret) return json({ error: "not_configured" }, 503);
  const body = await req.text();
  const sig = req.headers.get("x-hub-signature-256") ?? "";
  const expected = "sha256=" + createHmac("sha256", secret).update(body).digest("hex");
  if (!safeEqual(sig, expected)) return json({ error: "bad_signature" }, 401);
  const event = req.headers.get("x-github-event") ?? "";
  if (event === "ping") return json({ ok: true });
  if (event !== "sponsorship") return json({ ok: true, ignored: event });
  const p = JSON.parse(body) as { action?: string; sponsorship?: { privacy_level?: string; sponsor?: { login?: string }; tier?: { is_one_time?: boolean } } };
  const login = p.sponsorship?.sponsor?.login ?? "";
  if (p.action !== "created" || p.sponsorship?.privacy_level !== "public" || !HANDLE_RE.test(login)) return json({ ok: true, badge: false });
  await addSupporter({ handle: login, since: new Date().toISOString().slice(0, 10), via: "GitHub Sponsors", monthly: !p.sponsorship?.tier?.is_one_time });
  return json({ ok: true, badge: true, handle: login });
}
