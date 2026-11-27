import Mathlib

/-!
# Infinitely many common terms of A003325 and A052276

A003325 consists of sums of two positive cubes. A052276 consists of the
nonnegative values of a nonnegative cube plus or minus three. The comment
shared by both entries conjectures that their intersection is infinite.

Sources: https://oeis.org/A003325 and https://oeis.org/A052276
Credit: @justusklocke-cloud
-/

namespace OMA.S_oeis_a003325

/-- Common membership in A003325 and A052276. The second equality keeps
the minus-three case free of truncated natural-number subtraction. -/
def IsCommonTerm (n : ℕ) : Prop :=
  (∃ a b : ℕ, 0 < a ∧ 0 < b ∧ n = a ^ 3 + b ^ 3) ∧
    ∃ c : ℕ, n = c ^ 3 + 3 ∨ n + 3 = c ^ 3

theorem main : {n : ℕ | IsCommonTerm n}.Infinite := by
  sorry

end OMA.S_oeis_a003325
