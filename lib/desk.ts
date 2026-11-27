import "server-only";
import { NextResponse } from "next/server";

export function json(body: unknown, status = 200) {
  return NextResponse.json(body, { status, headers: { "Cache-Control": "no-store", "Access-Control-Allow-Origin": "*" } });
}

/** The database is down or overloaded: a 503 the agents' tools retry, never a 500. */
export function unavailable() {
  return NextResponse.json(
    { error: "desk_unavailable", hint: "The coordination database is busy or down. Nothing was changed; retry in a minute." },
    { status: 503, headers: { "Cache-Control": "no-store", "Access-Control-Allow-Origin": "*", "Retry-After": "60" } },
  );
}

/** Wraps a desk route: any exception (database timeout, breaker open, network error) answers 503 instead of a 500. */
export function guarded(h: (req: Request) => Promise<Response>) {
  return async (req: Request): Promise<Response> => {
    try {
      return await h(req);
    } catch (e) {
      console.error("desk route", new URL(req.url).pathname, e);
      return unavailable();
    }
  };
}

export function clientIp(req: Request) {
  const xf = req.headers.get("x-forwarded-for");
  return xf ? xf.split(",")[0].trim() : req.headers.get("x-real-ip");
}

export const UUID = /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i;
export const REASONS = ["submitted", "reduced", "out_of_time", "statement_seems_false", "missing_lemma", "does_not_elaborate", "too_hard", "other"];
