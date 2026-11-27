/**
 * Worker entry: vinext's handler, plus a page cache in the Cache API of each data centre (free, not billed; unlike
 * Workers Cache, which bills every request). Only plain GET page requests are cached (no API, no RSC navigation
 * request, no authorization), only when vinext marks the page cacheable (s-maxage), for at most that long.
 * A cached page costs about a millisecond of CPU instead of a full render.
 */
import handler from "vinext/server/fetch-handler";
export * from "vinext/server/fetch-handler";

type ExecutionContext = { waitUntil(p: Promise<unknown>): void; passThroughOnException?(): void };
type Handler = { fetch(req: Request, env: unknown, ctx: ExecutionContext): Promise<Response> };
const inner = handler as unknown as Handler;
const SKIP = /^\/(api|_next|__|cdn-cgi)(\/|$)/;
const ORIGIN = "https://lefttosolve.com";
const NO_CACHE_HEADERS = ["rsc", "next-router-state-tree", "next-router-prefetch", "next-router-segment-prefetch", "next-url", "next-action",
  "x-vinext-interception-context", "x-vinext-interception-id", "x-vinext-mounted-slots", "x-vinext-rsc-render-mode",
  "x-vinext-rsc-state-fingerprint", "authorization", "x-oma-secret"];

// The revalidate of each ISR route (app/**/page.tsx): vinext marks a page's first render in an isolate no-store, but
// it is the same page; storing it at once saves every other isolate of the data centre a render.
const ROUTE_TTL: [RegExp, number][] = [
  [/^\/$/, 60], [/^\/solved$/, 60], [/^\/live$/, 30], [/^\/feed$/, 30], [/^\/board$/, 120],
  [/^\/p\/[^/]+\/agent\.txt$/, 300], [/^\/p\/[^/]+$/, 120], [/^\/a\/[^/]+$/, 120],
  [/^\/(contributors|graveyard|prizes|programs)(\/[^/]+)?$/, 300], [/^\/(calendar|c\/[^/]+\/[^/]+)$/, 600],
];
const routeTtl = (path: string) => ROUTE_TTL.find(([re]) => re.test(path))?.[1] ?? 0;

// Crawlers (search engines, AI crawlers, SEO tools) read the same pages over and over and do not need live counts to
// the minute: they get their own copy of each page, kept 6 hours. People always get the normal copy (at most a minute
// or two old), so nothing changes for them; the crawlers stop costing a full render per visit.
const CRAWLER = /(?<!cu)bot\b|bot\/|crawler|spider|slurp|bytespider|petalbot|facebookexternalhit|ia_archiver|semrush|ahrefs|gptbot|claudebot|perplexity|ccbot|amazonbot|applebot|elevenlabs/i;
const CRAWLER_TTL = 6 * 3600;

function eligible(req: Request, url: URL): boolean {
  if (req.method !== "GET" || SKIP.test(url.pathname) || url.searchParams.has("_rsc")) return false;
  const h = req.headers;
  // Every header vinext varies its response on (its Vary list), plus actions and credentials: a request carrying any
  // of them is rendered for itself and never stored, so nobody can plant a variant in the shared copy.
  for (const k of NO_CACHE_HEADERS) if (h.has(k)) return false;
  return true;
}

function secure(res: Response): Response {
  const type = res.headers.get("content-type") ?? "";
  if (!type.startsWith("text/html")) return res;
  const r = new Response(res.body, res);
  // No framing by other sites (clickjacking) and no full URLs leaked to other sites in Referer.
  r.headers.set("x-frame-options", "SAMEORIGIN");
  r.headers.set("content-security-policy", "frame-ancestors 'self'");
  r.headers.set("referrer-policy", "strict-origin-when-cross-origin");
  return r;
}

export default {
  async fetch(req: Request, env: unknown, ctx: ExecutionContext): Promise<Response> {
    return secure(await route(req, env, ctx));
  },
};

async function route(req: Request, env: unknown, ctx: ExecutionContext): Promise<Response> {
  {
    const url = new URL(req.url);
    const cache = (globalThis as unknown as { caches?: { default?: Cache } }).caches?.default;
    if (!cache || !eligible(req, url)) return inner.fetch(req, env, ctx);
    const bot = CRAWLER.test(req.headers.get("user-agent") ?? "");
    const key = new Request(`${ORIGIN}/${bot ? "__html_bot" : "__html"}${url.pathname}${url.search}`);
    const hit = await cache.match(key).catch(() => undefined);
    if (hit) {
      const r = new Response(hit.body, hit);
      r.headers.set("cache-control", "public, max-age=0, must-revalidate");
      r.headers.set("x-page-cache", "HIT");
      return r;
    }
    const res = await inner.fetch(req, env, ctx);
    const m = /s-maxage=(\d+)/.exec(res.headers.get("cache-control") ?? "")
      ?? (res.headers.get("x-vinext-cache") === "MISS" && routeTtl(url.pathname) ? [ "", String(routeTtl(url.pathname)) ] : null);
    const type = res.headers.get("content-type") ?? "";
    const vary = (res.headers.get("vary") ?? "").toLowerCase().split(",").map((v) => v.trim()).filter(Boolean);
    const variant = vary.includes("*") || vary.some((v) => v !== "accept-encoding" && req.headers.has(v));
    if (res.status === 200 && m && !variant && !res.headers.has("set-cookie") && /^text\/(html|plain)/.test(type)) {
      const ttl = bot ? CRAWLER_TTL : Math.min(Number(m[1]), 600);
      if (ttl > 0) {
        const copy = new Response(res.clone().body, res);
        copy.headers.set("cache-control", `public, max-age=${ttl}`);
        copy.headers.delete("vary");
        copy.headers.delete("x-page-cache");
        ctx.waitUntil(cache.put(key, copy).catch(() => undefined));
      }
    }
    return res;
  }
}
