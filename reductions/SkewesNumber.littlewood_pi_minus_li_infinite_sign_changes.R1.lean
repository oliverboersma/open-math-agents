import FormalConjectures.Wikipedia.SkewesNumber
import Mathlib

-- Credit: @marcusbuffett
namespace OMA.R_SkewesNumber_littlewood_pi_minus_li_infinite_sign_changes_R1
open Real

/-- Littlewood's two-sided real-variable oscillation estimate, weakened to fixed amplitude. -/
def H1 : Prop :=
  ∀ X : ℝ, (∃ x ≥ X, logIntegral x + 1 < (Nat.primeCounting ⌊x⌋₊ : ℝ)) ∧
    (∃ x ≥ X, (Nat.primeCounting ⌊x⌋₊ : ℝ) + 1 < logIntegral x)

/-- The change in the logarithmic integral on rounding down is nonnegative and at most one. -/
def H2 : Prop :=
  ∀ x : ℝ, 3 ≤ x → 0 ≤ logIntegral x - logIntegral (⌊x⌋₊ : ℝ) ∧
    logIntegral x - logIntegral (⌊x⌋₊ : ℝ) ≤ 1

theorem main : H1 → H2 → type_of% @SkewesNumber.littlewood_pi_minus_li_infinite_sign_changes := by
  intro osc hround
  have floorbound (n : ℕ) (x : ℝ) (hx : ((n+3 : ℕ) : ℝ) ≤ x) :
      n+3 ≤ ⌊x⌋₊ := Nat.le_floor hx
  constructor
  · apply Set.infinite_iff_exists_gt.mpr
    intro n
    obtain ⟨x,hx,h⟩ := (osc ((n+3 : ℕ) : ℝ)).1
    have hf := floorbound n x hx
    push_cast at hx
    have hd := (hround x (by linarith [(Nat.cast_nonneg n : 0 ≤ (n:ℝ))])).1
    exact ⟨⌊x⌋₊,⟨by omega,by linarith⟩,by omega⟩
  · apply Set.infinite_iff_exists_gt.mpr
    intro n
    obtain ⟨x,hx,h⟩ := (osc ((n+3 : ℕ) : ℝ)).2
    have hf := floorbound n x hx
    push_cast at hx
    have hd := (hround x (by linarith [(Nat.cast_nonneg n : 0 ≤ (n:ℝ))])).2
    exact ⟨⌊x⌋₊,⟨by omega,by linarith⟩,by omega⟩

end OMA.R_SkewesNumber_littlewood_pi_minus_li_infinite_sign_changes_R1
