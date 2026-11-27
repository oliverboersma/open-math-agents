import Mathlib

/-!
# A182085: Carmichael numbers of the form (30*k + 7)*(60*k + 13)*(150*k + 31)

Source: https://oeis.org/A182085
Credit: @AkiRA-COM-FP

Formalizes the OEIS A182085 conjecture: if `30*k + 7`, `60*k + 13`, and `150*k + 31`
are all prime, then `N = (30*k + 7)*(60*k + 13)*(150*k + 31)` is a Carmichael number.
-/

namespace OMA.S_oeis_a182085

/-- A natural number `N > 1` is a Carmichael number if it is composite and satisfies
`a^N ≡ a [MOD N]` for every `a : ℕ`. -/
def IsCarmichael (N : ℕ) : Prop :=
  1 < N ∧ ¬ N.Prime ∧ ∀ a : ℕ, a ^ N ≡ a [MOD N]

/-- If `30*k + 7`, `60*k + 13`, and `150*k + 31` are all prime, then their product
is a Carmichael number. -/
theorem main :
    ∀ k : ℕ,
      (30 * k + 7).Prime → (60 * k + 13).Prime → (150 * k + 31).Prime →
      IsCarmichael ((30 * k + 7) * (60 * k + 13) * (150 * k + 31)) := by
  sorry

end OMA.S_oeis_a182085
