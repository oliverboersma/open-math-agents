import { bindings, defineConfig, defineWorker } from "cf/config";

export default defineConfig({
  worker: defineWorker({
    name: "open-math-agents",
    entrypoint: "./worker/entry.ts",
    compatibilityDate: "2026-11-10",
    // Custom domains (zones on this account). Kept here so a forced deploy never drops them. shipfastwith.me is the old
    // address: a redirect rule on its zone sends every request to lefttosolve.com before it reaches the Worker.
    domains: ["lefttosolve.com", "www.lefttosolve.com", "shipfastwith.me", "www.shipfastwith.me"],
    // Keep open-math-agents.openmathagents.workers.dev too (turned off by default once domains are set).
    workersDev: true,
    assets: {
      htmlHandling: "none",
      notFoundHandling: "none",
      // Static files skip the Worker (free, unlimited): build assets and the map layout.
      runWorkerFirst: ["/*", "!/_next/static/*", "!/*/_next/static/*", "!/map-data.json", "!/favicon.ico", "!/icon-*", "!/apple-touch-icon.png", "!/apple-touch-icon-precomposed.png", "!/logo-mark.png", "!/og.jpg", "!/certificate-key.json", "!/sponsor-logos/*"],
    },
    env: {
      ASSETS: bindings.assets(),
      // Public settings (also read at build time: NEXT_PUBLIC_* are inlined into the pages).
      NEXT_PUBLIC_SITE_URL: bindings.text("https://lefttosolve.com"),
      NEXT_PUBLIC_SUPPORT_URL: bindings.text("https://ko-fi.com/guillaumebaud"),
      NEXT_PUBLIC_SPONSOR_URL: bindings.text("https://ko-fi.com/guillaumebaud"),
      SUPABASE_URL: bindings.text("https://fcuptmutkcstnaxmqsmg.supabase.co"),
      // Set with the secrets API, never in this file.
      SUPABASE_PUBLISHABLE_KEY: bindings.secret(),
      OMA_DB_SECRET: bindings.secret(),
      OMA_IP_SALT: bindings.secret(),
      OMA_VERDICT_SECRET: bindings.secret(),
      // Ed25519 private key (PKCS#8, base64) that signs contribution certificates; public key: public/certificate-key.json
      CERT_SIGNING_KEY: bindings.secret(),
      // Full statements, Lean sources, the full-text index and the pinned upstream Lean files (data/gen/catalog.sql).
      CATALOG: bindings.d1({ id: "740a3c15-d8dd-460c-bcdd-938e38df77b7", name: "oma-catalog" }),
      // Global copy of the desk's shared reads (lib/db.ts): Supabase answers each about once per TTL worldwide.
      DESK_KV: bindings.kv({ id: "90a53a15263c48389984466206d94e6c" }),
    },
  }),
});
