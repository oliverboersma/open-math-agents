import OMAReductions.R_ButsonHadamardMatrix_butson_hadamard_fourth_roots_conjecture_R1
import Mathlib

-- Step ButsonHadamardMatrix.butson_hadamard_fourth_roots_conjecture.R1.H1: hypothesis H1 of reduction ButsonHadamardMatrix.butson_hadamard_fourth_roots_conjecture.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! The two-circulant (complementary pair) construction. With `A = circulant a` and
`B = circulant b`, the hypothesis says exactly `A * Aᴴ + B * Bᴴ = 2m • 1` (every entry has
modulus one, and the off-diagonal entries are the given periodic correlations after the
substitution `j ↦ -j`). Circulant matrices commute and are normal, so the block matrix
`[[A, B], [-Bᴴ, Aᴴ]]`, reindexed to `Fin (2m)`, is a Butson Hadamard matrix of order four. -/


namespace P4Butson

open Matrix ButsonHadamardMatrix

theorem mul_star_of_pow_four {z : ℂ} (hz : z ^ 4 = 1) : z * star z = 1 := by
  have h1 : Complex.normSq z ^ 4 = 1 := by
    rw [← map_pow, hz, map_one]
  have h2 : Complex.normSq z = 1 :=
    (pow_eq_one_iff_of_nonneg (Complex.normSq_nonneg z) (by norm_num)).mp h1
  rw [Complex.star_def, Complex.mul_conj, h2, Complex.ofReal_one]

theorem pow_four_star {z : ℂ} (hz : z ^ 4 = 1) : (star z) ^ 4 = 1 := by
  rw [← star_pow, hz, star_one]

theorem pow_four_neg_star {z : ℂ} (hz : z ^ 4 = 1) : (-star z) ^ 4 = 1 := by
  rw [neg_pow, pow_four_star hz]; norm_num

theorem key (m : ℕ) [NeZero m] (a b : Fin m → ℂ) (hab : ∀ j, a j ^ 4 = 1 ∧ b j ^ 4 = 1)
    (hsum : ∀ i k : Fin m, i ≠ k →
      (∑ j : Fin m, (a (j+i)*star (a (j+k)) + b (j+i)*star (b (j+k)))) = 0) :
    circulant a * (circulant a)ᴴ + circulant b * (circulant b)ᴴ = ((2 * m : ℕ) : ℂ) • 1 := by
  ext i k
  simp only [Matrix.add_apply, mul_apply, conjTranspose_apply, circulant_apply, Matrix.smul_apply,
    one_apply, smul_eq_mul]
  rw [← Finset.sum_add_distrib]
  have hre : (∑ j : Fin m, (a (i - j) * star (a (k - j)) + b (i - j) * star (b (k - j)))) =
      ∑ j : Fin m, (a (j + i) * star (a (j + k)) + b (j + i) * star (b (j + k))) := by
    refine Fintype.sum_equiv (Equiv.neg (Fin m)) _ _ (fun j => ?_)
    simp only [Equiv.neg_apply, sub_eq_add_neg, add_comm]
  rw [hre]
  by_cases hik : i = k
  · subst hik
    rw [if_pos rfl, mul_one]
    have : ∀ j : Fin m, a (j + i) * star (a (j + i)) + b (j + i) * star (b (j + i)) = 2 := by
      intro j
      rw [mul_star_of_pow_four (hab _).1, mul_star_of_pow_four (hab _).2]; norm_num
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  · rw [if_neg hik, mul_zero]
    exact hsum i k hik

end P4Butson

open Matrix P4Butson in
theorem OMA.solution : OMA.R_ButsonHadamardMatrix_butson_hadamard_fourth_roots_conjecture_R1.H1 := by
  intro m hm a b hab hsum
  have : NeZero m := ⟨by omega⟩
  have hk := key m a b hab hsum
  set A := circulant a with hA
  set B := circulant b with hB
  let N : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℂ := fromBlocks A B (-Bᴴ) Aᴴ
  let e : Fin (2 * m) ≃ Fin m ⊕ Fin m := (finCongr (two_mul m)).trans finSumFinEquiv.symm
  refine ⟨N.submatrix e e, by norm_num, ?_, ?_⟩
  · intro i j
    simp only [submatrix_apply, N]
    generalize e i = x
    generalize e j = y
    rcases x with x | x <;> rcases y with y | y
    · simp only [fromBlocks_apply₁₁, hA, circulant_apply]
      exact (hab _).1
    · simp only [fromBlocks_apply₁₂, hB, circulant_apply]
      exact (hab _).2
    · simp only [fromBlocks_apply₂₁, hB]
      exact pow_four_neg_star (hab _).2
    · simp only [fromBlocks_apply₂₂, conjTranspose_apply, hA, circulant_apply]
      exact pow_four_star (hab _).1
  · have hAB : A * B = B * A := circulant_mul_comm a b
    have hAA : Aᴴ * A = A * Aᴴ := by
      rw [hA, conjTranspose_circulant]; exact circulant_mul_comm _ _
    have hBB : Bᴴ * B = B * Bᴴ := by
      rw [hB, conjTranspose_circulant]; exact circulant_mul_comm _ _
    rw [conjTranspose_submatrix, submatrix_mul_equiv]
    have hN : N * Nᴴ = fromBlocks (((2 * m : ℕ) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)) 0 0
        (((2 * m : ℕ) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)) := by
      simp only [N, fromBlocks_conjTranspose, fromBlocks_multiply, conjTranspose_neg,
        conjTranspose_conjTranspose]
      congr 1
      · rw [Matrix.mul_neg, hAB, neg_add_cancel]
      · rw [Matrix.neg_mul, ← conjTranspose_mul, ← conjTranspose_mul, hAB, neg_add_cancel]
      · rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg, hAA, hBB, add_comm]; exact hk
    have h1 : fromBlocks (((2 * m : ℕ) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)) 0 0
        (((2 * m : ℕ) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)) =
        ((2 * m : ℕ) : ℂ) • (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℂ) := by
      rw [← fromBlocks_one, fromBlocks_smul, smul_zero]
    rw [hN, h1]
    ext i j
    simp [Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq]

