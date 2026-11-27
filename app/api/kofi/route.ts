/**
 * Ko-fi webhook (Ko-fi > Settings > API > Webhooks: https://lefttosolve.com/api/kofi). Ko-fi posts a form with one field,
 * `data`, holding JSON with the account's verification token. A public donation whose message names a GitHub handle
 * ("@handle" or "github: handle") gives that person the Supporter badge. Nothing else is stored.
 * Needs the Worker secret KOFI_VERIFICATION_TOKEN (the token shown on that Ko-fi page).
 */
import { addSupporter, githubLogin, handleFromMessage, safeEqual, workerSecret } from "@/lib/supporters";

const json = (b: unknown, status = 200) => new Response(JSON.stringify(b), { status, headers: { "content-type": "application/json" } });

export async function POST(req: Request) {
  const token = workerSecret("KOFI_VERIFICATION_TOKEN");
  if (!token) return json({ error: "not_configured" }, 503);
  const form = await req.formData().catch(() => null);
  let d: Record<string, unknown>;
  try {
    d = JSON.parse(String(form?.get("data") ?? ""));
  } catch {
    return json({ error: "bad_payload" }, 400);
  }
  if (!safeEqual(String(d.verification_token ?? ""), token)) return json({ error: "bad_token" }, 401);
  if (d.is_public === false) return json({ ok: true, badge: false, reason: "private donation" });
  const h = handleFromMessage(String(d.message ?? ""));
  const login = h ? await githubLogin(h) : null;
  if (!login) return json({ ok: true, badge: false, reason: "no GitHub handle in the message" });
  await addSupporter({ handle: login, since: new Date().toISOString().slice(0, 10), via: "Ko-fi", monthly: Boolean(d.is_subscription_payment) });
  return json({ ok: true, badge: true, handle: login });
}
