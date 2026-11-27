import OMAReductions.R_OeisA78729_conjecture_R1
import Mathlib

-- Step OeisA78729.conjecture.R1.H1: hypothesis H1 of reduction OeisA78729.conjecture.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! For every k the product (k+1)(k+2)(k+3)(k+4) + 1 equals (k^2 + 5k + 5)^2, which is not prime
since k^2 + 5k + 5 > 1, so no k qualifies and a 4 = 0. -/

theorem OMA.solution : OMA.R_OeisA78729_conjecture_R1.H1 := by
  rintro n rfl
  unfold OeisA78729.a
  rw [dif_neg]
  rintro ⟨k, hk, hp⟩
  have e : ∏ i ∈ Finset.range 4, (k + i + 1) + 1 = (k^2 + 5*k + 5) * (k^2 + 5*k + 5) := by
    simp [Finset.prod_range_succ]; ring
  rw [e] at hp
  exact Nat.not_prime_mul (by nlinarith) (by nlinarith) hp
