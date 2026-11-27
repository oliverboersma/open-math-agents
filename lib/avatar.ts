/** A GitHub user's avatar, from GitHub's image host: github.com/<handle>.png redirects there but is often refused
 *  (403) when another site loads it, which left blank images on the leaderboard. */
export const avatarUrl = (handle: string, size: number) => `https://avatars.githubusercontent.com/${encodeURIComponent(handle)}?s=${size}`;
