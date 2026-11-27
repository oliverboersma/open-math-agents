import OMAReductions.R_CramerConjecture_cramer_conjecture_variants_baker_harman_pintz_R1
import Mathlib

-- Credit: @marcusbuffett
namespace OMA.R_CramerConjecture_cramer_conjecture_variants_baker_harman_pintz_R1_H1_R1
open Real Filter ArithmeticFunction Finset

/-- The Baker–Harman–Pintz short-interval lower bound on the central interval. -/
def H1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ a : ℕ in atTop,
    let h := ⌈2 * (a : ℝ)^(0.525 : ℝ)⌉₊
    c * h ≤ ∑ k ∈ Ico (a+h-h/2) (a+h+h/2), (Λ k : ℝ)

/-- A second difference of the integrated Chebyshev sum dominates the central mass. -/
def H2 : Prop :=
  let F (n : ℕ) := ∑ k ∈ range n, (Λ k : ℝ) * ((n : ℝ) - k)
  ∀ a h : ℕ, (h : ℝ)/2 * (∑ k ∈ Ico (a+h-h/2) (a+h+h/2), (Λ k : ℝ)) ≤
    F (a+2*h) - 2*F (a+h) + F a

theorem main : H1 → H2 → OMA.R_CramerConjecture_cramer_conjecture_variants_baker_harman_pintz_R1.H1 := by
  rintro ⟨c,hc,hm⟩ tent
  refine ⟨c/2, by positivity, ?_⟩
  filter_upwards [hm] with a ha
  let h := ⌈2 * (a : ℝ)^(0.525 : ℝ)⌉₊
  refine le_trans ?_ (tent a h)
  change c * (h : ℝ) ≤ ∑ k ∈ Ico (a+h-h/2) (a+h+h/2), (Λ k : ℝ) at ha
  change c/2 * (h : ℝ)^2 ≤ _
  nlinarith only [mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg (α := ℝ) h)]

end OMA.R_CramerConjecture_cramer_conjecture_variants_baker_harman_pintz_R1_H1_R1
