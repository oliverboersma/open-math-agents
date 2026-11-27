import Mathlib

/-!
# OEIS A327836: the least k with n^k = 1 mod (n+1)^(n+1) is at most 2*(n+1)^n

Source: https://oeis.org/A327836 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A327836 (Matthias Baur, Sep 27 2019), offset 1: Least k > 0 such that n^k == 1 (mod
(n+1)^(n+1)). Comment: Conjecture: a(n) <= 2*(n+1)^n.

Formalization notes:
* a(n) is the infimum of the k > 0 with n^k congruent to 1 modulo (n+1)^(n+1); the statement is for
  every n >= 1 (offset 1).
* Controls from the entry: the definition gives a(1..4) = 1, 18, 64, 1250.
-/

namespace OMA.S_oeis_a327836

/-- The exponents allowed in the definition. -/
def Good (n k : ℕ) : Prop := 0 < k ∧ n ^ k ≡ 1 [MOD (n + 1) ^ (n + 1)]

/-- A327836(n): the least k > 0 with n^k = 1 mod (n+1)^(n+1). -/
noncomputable def a (n : ℕ) : ℕ := sInf {k | Good n k}

/-- Baur's conjecture: a(n) <= 2*(n+1)^n for every n >= 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n ≤ 2 * (n + 1) ^ n := by
  sorry

end OMA.S_oeis_a327836
