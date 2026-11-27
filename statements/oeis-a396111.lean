import Mathlib

/-!
# A396111: a(n) = n^4 mod (2*n + 1)

Source: https://oeis.org/A396111
Credit: @AkiRA-COM-FP

Formalizes both OEIS A396111 conjectures (offset 0): the sequence `a(n) = n^4 mod (2*n + 1)`
attains every nonnegative integer `k` at least once, and attains every `k` only finitely
many times.
-/

namespace OMA.S_oeis_a396111

/-- The OEIS sequence A396111: `a(n) = n^4 mod (2*n + 1)`. -/
def a (n : ℕ) : ℕ :=
  n ^ 4 % (2 * n + 1)

/-- Every `k : ℕ` occurs in `a(n)`, and occurs only finitely many times. -/
theorem main :
    (∀ k : ℕ, ∃ n : ℕ, a n = k) ∧ (∀ k : ℕ, Set.Finite {n : ℕ | a n = k}) := by
  sorry

end OMA.S_oeis_a396111
