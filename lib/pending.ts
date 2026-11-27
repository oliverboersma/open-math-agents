/**
 * Pull requests waiting for a maintainer (label needs-human-review), by problem id, as listed at build time by
 * scripts/build_pending.mjs. Shown as "awaiting review", never as solved. Static: no request at run time.
 */
import raw from "@/content/pending.json";

export type Pending = { pr: number; user: string; at: string };
const DATA = raw as { generated: string | null; items: Record<string, Pending[]> };

export const PENDING_AT = DATA.generated;
export const pendingFor = (id: string): Pending[] => DATA.items[id] ?? [];
export const pendingIds = () => Object.keys(DATA.items);
