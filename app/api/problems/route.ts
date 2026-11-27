import { NextRequest, NextResponse } from "next/server";
import { META, search, withExcerpts, getFullMany } from "@/lib/catalog";
import { getLiveMap, getStats } from "@/lib/db";
import { cachedJSON } from "@/lib/edgecache";

export async function GET(req: NextRequest) {
  const sp = new URLSearchParams([...req.nextUrl.searchParams].sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0)));
  // The same query is answered from the cache for 30 s (agents repeat the same searches): no scan, no D1 read.
  let body: Awaited<ReturnType<typeof compute>>;
  try {
    body = await cachedJSON(`problems?${sp}`, 30, () => compute(sp));
  } catch (e) {
    console.error("api/problems", String(sp), e);
    return NextResponse.json({ error: "temporarily_unavailable", hint: "Retry in a minute." }, { status: 503, headers: { "Retry-After": "60", "Access-Control-Allow-Origin": "*" } });
  }
  return NextResponse.json(body, {
    headers: {
      // max-age: the same search repeated by the same visitor within a minute is answered by the browser.
      "Cache-Control": "public, max-age=60",
      "Access-Control-Allow-Origin": "*",
    },
  });
}

async function compute(sp: URLSearchParams) {
  const sort = (sp.get("sort") ?? undefined) as "relevance" | "famous" | "hardest" | "easiest" | "prize" | "active" | undefined;
  const [live, stats] = await Promise.all([getLiveMap(), getStats()]);
  const solved = new Set(stats.solved.map((s) => s.problem_id));
  const { total, items } = await search({
    q: sp.get("q") ?? undefined,
    kind: sp.get("kind") ?? sp.get("status") ?? undefined,
    source: sp.get("source") ?? undefined,
    field: sp.get("field") ?? undefined,
    sort,
    limit: Number(sp.get("limit") ?? 30),
    offset: Number(sp.get("offset") ?? 0),
    live,
    solved,
    hideSolved: sp.get("unsolved") === "1",
  });
  const full = sp.get("full") === "1";
  const details = full ? new Map((await getFullMany(items.map((p) => p.id))).map((f) => [f.id, f])) : null;
  const cards = details ? null : new Map((await withExcerpts(items)).map((c) => [c.id, c]));
  return {
    total,
    upstream: { repo: META.upstream, commit: META.upstreamCommit },
    items: items.map((p) => ({
      ...(details ? details.get(p.id) ?? p : cards!.get(p.id)),
      liveAgents: live.get(p.id) ?? 0,
      solved: solved.has(p.id),
    })),
  };
}
