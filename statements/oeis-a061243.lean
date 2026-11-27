import Mathlib

/-!
# A061243: a(n) = n+r where r is the smallest number such that n divides (n+1)(n+2)(n+3)...(n+r).

Source: https://oeis.org/A061243
Credit: @max-otc

Offset 1: a(1) = 2, a(2) = 4, a(3) = 6, ..., so r ranges over positive integers (r = 1 for n = 1).
A002034 (Kempner numbers): the smallest positive integer m such that n divides m! (A002034(1) = 1).
Statement (the conjecture in the entry; Dean Hickerson notes it is easy to prove): a(n) = n + A002034(n)
for every n ≥ 1.
-/

namespace OMA.S_oeis_a061243

/-- A061243: a(n) = n + r, with r the least positive integer such that n ∣ (n+1)(n+2)...(n+r). -/
noncomputable def a (n : ℕ) : ℕ := n + sInf {r : ℕ | 0 < r ∧ n ∣ ∏ i ∈ Finset.Icc 1 r, (n + i)}

/-- A002034 (Kempner numbers): the least positive integer m such that n ∣ m!. -/
noncomputable def kempner (n : ℕ) : ℕ := sInf {m : ℕ | 0 < m ∧ n ∣ m.factorial}

/-- The conjecture of A061243: a(n) = n + A002034(n). -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = n + kempner n := by
  sorry

end OMA.S_oeis_a061243
