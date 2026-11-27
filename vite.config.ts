import { defineConfig } from "vite";
import vinext from "vinext";
import { cloudflare } from "@cloudflare/vite-plugin";

export default defineConfig({
  plugins: [
    // No Workers Cache adapter: with Workers Cache on, every request (static files and the internal render call included)
    // is billed. Pages are cached by worker/entry.ts in the Cache API instead, which is not billed.
    vinext(),
    cloudflare({
      viteEnvironment: {
        name: "rsc",
        childEnvironments: ["ssr"],
      },
    }),
  ],
});
