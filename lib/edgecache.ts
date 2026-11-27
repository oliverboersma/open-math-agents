/**
 * Caches a computed JSON value for `ttl` seconds: in this isolate's memory, then in the data centre's Cache API
 * (shared by every isolate there; not billed, unlike Workers Cache). Identical concurrent computations run once.
 * For public, read-only values only.
 */
const MEM = new Map<string, { at: number; value: unknown }>();
const INFLIGHT = new Map<string, Promise<unknown>>();
const ORIGIN = (process.env.SITE_URL ?? process.env.NEXT_PUBLIC_SITE_URL ?? "https://lefttosolve.com").replace(/\/$/, "");

function edgeCache(): Cache | null {
  try {
    return (globalThis as unknown as { caches?: { default?: Cache } }).caches?.default ?? null;
  } catch {
    return null;
  }
}

export async function cachedJSON<T>(key: string, ttl: number, compute: () => Promise<T>): Promise<T> {
  const m = MEM.get(key);
  if (m && Date.now() - m.at < ttl * 1000) return m.value as T;
  const running = INFLIGHT.get(key);
  if (running) return running as Promise<T>;
  const p = (async () => {
    const cache = edgeCache();
    const req = new Request(`${ORIGIN}/__json_cache/${encodeURIComponent(key)}`);
    if (cache) {
      const hit = await cache.match(req).catch(() => undefined);
      if (hit) {
        const got = (await hit.json().catch(() => null)) as { at: number; value: T } | null;
        if (got && Date.now() - got.at < ttl * 1000) {
          MEM.set(key, got);
          return got.value;
        }
      }
    }
    const value = await compute();
    const at = Date.now();
    if (MEM.size > 500) MEM.clear();
    MEM.set(key, { at, value });
    if (cache) {
      await cache
        .put(req, new Response(JSON.stringify({ at, value }), { headers: { "Content-Type": "application/json", "Cache-Control": `public, max-age=${ttl}` } }))
        .catch(() => undefined);
    }
    return value;
  })().finally(() => INFLIGHT.delete(key));
  INFLIGHT.set(key, p);
  return p as Promise<T>;
}
