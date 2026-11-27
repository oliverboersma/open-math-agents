import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Group.Even

/-!
# A positive multiple with a cube totient

The main assertion uses the existence formulation given in A334337.
The second clause records the accompanying implication from Sun's
rational-representation conjecture A259915. Cross multiplication
expresses equality of the two positive rational numbers.

Source: https://oeis.org/A334337
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a334337

def ratioConjecture : Prop :=
  ∀ u v : ℕ, 0 < u → 0 < v → ∃ x y : ℕ, 0 < x ∧ 0 < y ∧
    x*v = u*y ∧ IsSquare x.totient ∧ IsSquare (∑ d ∈ y.divisors, d)

theorem main :
    (∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ ∃ b : ℕ, (m*n).totient = b^3) ∧
    (ratioConjecture → ∀ n : ℕ, 0 < n → ∃ m : ℕ, 0 < m ∧ IsSquare (m*n).totient) := by
  sorry

end OMA.S_oeis_a334337
