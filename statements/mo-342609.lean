import Mathlib

/-!
# Two conjectures on the sum of divisors and the Euler totient, inspired by an equation of Iannucci

Source: https://mathoverflow.net/questions/342609 (2019).
Credit: @prasledi

The statement is the Conjecture of the post, both parts, as a conjunction.
First part: if N is an odd positive integer and a positive integer n satisfies equation (2),
phi n + sigma (((N + 1) / 2) * n) = N * n + phi (2 * (N + 1) * n), then n is even.
Second part: if positive integers R and n satisfy equation (3),
phi n + sigma (R * n) = (2 * R - 1) * n + phi (4 * R * n), then n is even.
Here phi is Nat.totient and sigma is the sum of divisors. Since N is odd the division by 2 is exact,
and since R is positive the subtraction 2 * R - 1 is the usual one. The Claim that precedes the
conjecture in the post is not part of this statement.
-/

namespace OMA.S_mo_342609

open ArithmeticFunction

theorem main :
    (∀ N n : ℕ, 0 < N → 2 ∣ N + 1 → 0 < n →
      Nat.totient n + sigma 1 ((N + 1) / 2 * n) = N * n + Nat.totient (2 * (N + 1) * n) →
      Even n) ∧
    (∀ R n : ℕ, 1 ≤ R → 1 ≤ n →
      Nat.totient n + sigma 1 (R * n) = (2 * R - 1) * n + Nat.totient (4 * R * n) →
      Even n) := by
  sorry

end OMA.S_mo_342609
