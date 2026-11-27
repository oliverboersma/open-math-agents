import FormalConjectures.GreensOpenProblems.«97»
import Mathlib

-- Credit: @marcusbuffett. The complete-mapping normalization was also noted by @MechaNuggan.
namespace OMA.R_Green97_green_97_variants_eberhard_manners_mrazovic_R1
open Green97 Filter Asymptotics
open scoped Nat

/-- The cyclic-group transversal estimate in the complete-mapping normalization. -/
def H1 : Prop :=
  (fun n : ℕ ↦ (Nat.card {σ : Equiv.Perm (ZMod n) //
    Function.Bijective fun x ↦ x + σ x} : ℝ)) ~[atTop ⊓ principal {n : ℕ | Odd n}]
      fun n ↦ Real.exp (-(1 / 2)) * (n.factorial : ℝ)^2 / (n : ℝ)^(n-1)

/-- For each complete mapping there is a free choice of the first bijection labeling its rows. -/
def H2 : Prop :=
  ∀ n : ℕ, 0 < n → numAdditiveTriples n = n.factorial *
    Nat.card {σ : Equiv.Perm (ZMod n) // Function.Bijective fun x ↦ x + σ x}

theorem main : H1 → H2 → type_of% @Green97.green_97.variants.eberhard_manners_mrazovic := by
  intro asym count
  let l := atTop ⊓ principal {n : ℕ | Odd n}
  let F := fun n : ℕ ↦ (n.factorial : ℝ)
  have refl : F ~[l] F := IsEquivalent.refl
  have prod := refl.mul asym
  refine (prod.congr_left ?_).congr_right ?_
  · have ev : ∀ᶠ n : ℕ in l, 1 ≤ n := (eventually_ge_atTop 1).filter_mono inf_le_left
    filter_upwards [ev] with n hn
    simp only [Pi.mul_apply,F,count n hn,Nat.cast_mul]
  · apply Filter.Eventually.of_forall
    intro n
    simp only [Pi.mul_apply,F]
    ring

end OMA.R_Green97_green_97_variants_eberhard_manners_mrazovic_R1
