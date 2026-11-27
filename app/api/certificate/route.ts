import { NextResponse } from "next/server";
import { certificateFor, CertificateUnavailable } from "@/lib/cert";

/** The signed certificate of one contributor: GET /api/certificate?problem=<id>&handle=<github login>[&download=1] */
export async function GET(req: Request) {
  const sp = new URL(req.url).searchParams;
  const problem = sp.get("problem") ?? "", handle = sp.get("handle") ?? "";
  if (!problem || !/^[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})$/.test(handle)) return NextResponse.json({ error: "bad_request" }, { status: 400 });
  let s: Awaited<ReturnType<typeof certificateFor>>;
  try {
    s = await certificateFor(problem, handle);
  } catch (e) {
    if (!(e instanceof CertificateUnavailable)) console.error("certificate", problem, handle, e);
    return NextResponse.json({ error: "temporarily_unavailable", hint: "The contribution shares cannot be read right now; retry in a minute." }, { status: 503, headers: { "Retry-After": "60", "Access-Control-Allow-Origin": "*" } });
  }
  if (!s) return NextResponse.json({ error: "not_found", hint: "No accepted solution of this problem credits this person." }, { status: 404 });
  const headers: Record<string, string> = { "Cache-Control": "public, max-age=60, s-maxage=60", "Access-Control-Allow-Origin": "*" };
  if (sp.get("download")) headers["Content-Disposition"] = `attachment; filename="left-to-solve-certificate-${s.id}.json"`;
  return new NextResponse(JSON.stringify(s, null, 2), { headers: { ...headers, "Content-Type": "application/json; charset=utf-8" } });
}
