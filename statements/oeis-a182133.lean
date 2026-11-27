import Mathlib

/-!
# A182133: Carmichael numbers of the form (30*n + 13)*(90*n + 37)*(150*n + 61)

Source: https://oeis.org/A182133
Credit: @AkiRA-COM-FP

Formalizes the OEIS A182133 conjecture: if `30*n + 13`, `90*n + 37`, and `150*n + 61`
are all prime, then `C = (30*n + 13)*(90*n + 37)*(150*n + 61)` is a Carmichael number.
-/

namespace OMA.S_oeis_a182133

/-- A natural number `N > 1` is a Carmichael number if it is composite and satisfies
`a^N ≡ a [MOD N]` for every `a : ℕ`. -/
def IsCarmichael (N : ℕ) : Prop :=
  1 < N ∧ ¬ N.Prime ∧ ∀ a : ℕ, a ^ N ≡ a [MOD N]

/-- If `30*n + 13`, `90*n + 37`, and `150*n + 61` are all prime, then their product
is a Carmichael number. -/
theorem main :
    ∀ n : ℕ,
      (30 * n + 13).Prime → (90 * n + 37).Prime → (150 * n + 61).Prime →
      IsCarmichael ((30 * n + 13) * (90 * n + 37) * (150 * n + 61)) := by
  sorry

end OMA.S_oeis_a182133
