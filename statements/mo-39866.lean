import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Ideal.IsPrincipal

/-!
# Noetherian local rings with principal maximal ideal

Source: https://mathoverflow.net/questions/39866
Credit: @eliayousf

The question asks whether a commutative Noetherian local ring with
principal maximal ideal is a principal ideal ring. No domain hypothesis
is imposed. The use of commutative rings follows the stated scope of the
source question.
-/

namespace OMA.S_mo_39866

universe u

theorem main : ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
    (IsLocalRing.maximalIdeal R).IsPrincipal → IsPrincipalIdealRing R := by
  sorry

end OMA.S_mo_39866
