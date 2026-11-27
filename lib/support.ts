/** Where the Support button sends people: the Ko-fi page (NEXT_PUBLIC_SUPPORT_URL), else the sponsor link, else
 *  nothing (the page explains how to help otherwise). */
export const SUPPORT_URL: string | null = process.env.NEXT_PUBLIC_SUPPORT_URL || process.env.NEXT_PUBLIC_SPONSOR_URL || null;
/** A direct card checkout (a Stripe Payment Link where the customer chooses the amount), shown first when set: it takes
 *  cards from any country, Apple Pay and Google Pay, with no account on any other site. */
export const CARD_URL: string | null = process.env.NEXT_PUBLIC_CARD_URL || null;
/** GitHub Sponsors profile of the maintainer. Shown only once set: a profile that is not live yet is a dead end. */
export const GITHUB_SPONSORS_URL: string | null = process.env.NEXT_PUBLIC_GITHUB_SPONSORS_URL || null;
