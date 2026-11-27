import Mathlib

/-!
# OEIS A189202

For n ≥ 2, a(n) is the least positive m for which the sum of the binary
digits of m(n−1) and the sum of the base-n digits of 2m(n−1) divided
by n−1 are both even. When there is no such m, a(n) is set to zero.
Vladimir Shevelev conjectured that the zero case never arises.

Source: https://oeis.org/A189202
-/

namespace OMA.S_oeis_a189202

def ds (b x : ℕ) := (Nat.digits b x).sum

def admissible (n m : ℕ) : Prop := 0 < m ∧ Even (ds 2 (m*(n-1))) ∧
  Even (ds n (2*m*(n-1))/(n-1))

noncomputable def term (n : ℕ) : ℕ := by
  classical
  exact if h : ∃ m, admissible n m then Nat.find h else 0

theorem main : ∀ n : ℕ, 2 ≤ n → 0 < term n := by
  sorry

end OMA.S_oeis_a189202
