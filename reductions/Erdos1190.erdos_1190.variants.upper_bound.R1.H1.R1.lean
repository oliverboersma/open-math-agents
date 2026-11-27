import OMAReductions.R_Erdos1190_erdos_1190_variants_upper_bound_R1

/-! The regularity conditions follow the pruning argument of de la Bretèche, Ford and
Vandehey and the presentation of Pawan Sasanka Ammanamanchi and collaborators in
Erdos/P202/Proof.lean, Shashi456/erdos-formalizations, commit 286f856. -/

namespace OMA.R_Erdos1190_erdos_1190_variants_upper_bound_R1_H1_R1
open Real Finset Filter

/-- A system above the critical size has a large subfamily with a fixed number
of prime factors, controlled factorization exponents and distinct radicals. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 → ∀ᶠ N : ℕ in atTop, ∀ (S : Finset ℕ) (a : ℕ → ℤ),
    (∀ n ∈ S, 0 < n ∧ n ≤ N) →
    (∀ n ∈ S, ∀ j ∈ S, n ≠ j →
      ¬ ∃ x : ℤ, x ≡ a n [ZMOD n] ∧ x ≡ a j [ZMOD j]) →
    N * scaleL N ^ (-1 : ℝ) ≤ (S.card : ℝ) →
    ∃ (T : Finset ℕ) (K : ℕ), T ⊆ S ∧
      (S.card : ℝ) * scaleL N ^ (-ε) ≤ (T.card : ℝ) ∧
      1 ≤ K ∧ (K : ℝ) ≤ 3 * sqrt (log N / log (log N)) ∧
      (∀ q ∈ T, N * scaleL N ^ (-2 : ℝ) ≤ (q : ℝ) ∧
        ((∏ p ∈ q.primeFactors, q.factorization p : ℕ) : ℝ) ≤ exp (sqrt (log N)) ∧
        q.primeFactors.card = K) ∧
      (∀ q ∈ T, ∀ r ∈ T, (∏ p ∈ q.primeFactors, p) = (∏ p ∈ r.primeFactors, p) → q = r)

/-- Counting bound restricted to the regular families produced by pruning. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ (T : Finset ℕ) (a : ℕ → ℤ) (K : ℕ),
    (∀ n ∈ T, 0 < n ∧ n ≤ N) →
    (∀ n ∈ T, ∀ j ∈ T, n ≠ j →
      ¬ ∃ x : ℤ, x ≡ a n [ZMOD n] ∧ x ≡ a j [ZMOD j]) →
    (1 ≤ K ∧ (K : ℝ) ≤ 3 * sqrt (log N / log (log N)) ∧
      (∀ q ∈ T, N * scaleL N ^ (-2 : ℝ) ≤ (q : ℝ) ∧
        ((∏ p ∈ q.primeFactors, q.factorization p : ℕ) : ℝ) ≤ exp (sqrt (log N)) ∧
        q.primeFactors.card = K) ∧
      (∀ q ∈ T, ∀ r ∈ T, (∏ p ∈ q.primeFactors, p) = (∏ p ∈ r.primeFactors, p) → q = r)) →
    (T.card : ℝ) ≤ N * scaleL N ^ (-(sqrt 3 / 2) + ε)

theorem main : H1 → H2 → OMA.R_Erdos1190_erdos_1190_variants_upper_bound_R1.H1 := by
  intro prune count δ hδ
  let ε := min (δ / 2) (1 / 4)
  have he : 0 < ε := lt_min (by positivity) (by norm_num)
  have heδ : ε + ε ≤ δ := by
    have := min_le_left (δ / 2) (1 / 4 : ℝ)
    dsimp [ε]
    linarith
  filter_upwards [prune ε he (min_le_right _ _), count ε he] with N hp hc S a hr hd
  have hb : 1 ≤ scaleL N := Real.one_le_exp (Real.sqrt_nonneg _)
  have hb' : 0 < scaleL N := lt_of_lt_of_le zero_lt_one hb
  have hN : (0 : ℝ) ≤ N := by positivity
  by_cases hbig : N * scaleL N ^ (-1 : ℝ) ≤ (S.card : ℝ)
  · obtain ⟨T, K, ht, hl, hg⟩ := hp S a hr hd hbig
    have hT := hc T a K (fun n hn => hr n (ht hn))
      (fun n hn j hj => hd n (ht hn) j (ht hj)) hg
    calc
      (S.card : ℝ) = ((S.card : ℝ) * scaleL N ^ (-ε)) * scaleL N ^ ε := by
        rw [mul_assoc, ← Real.rpow_add hb', neg_add_cancel, Real.rpow_zero, mul_one]
      _ ≤ (N * scaleL N ^ (-(sqrt 3 / 2) + ε)) * scaleL N ^ ε :=
        mul_le_mul_of_nonneg_right (hl.trans hT) (Real.rpow_nonneg hb'.le _)
      _ ≤ _ := by
        rw [mul_assoc, ← Real.rpow_add hb']
        apply mul_le_mul_of_nonneg_left _ hN
        exact Real.rpow_le_rpow_of_exponent_le hb (by linarith)
  · apply (not_le.mp hbig).le.trans
    apply mul_le_mul_of_nonneg_left _ hN
    apply Real.rpow_le_rpow_of_exponent_le hb
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
      sq_nonneg (Real.sqrt 3 - 2)]

end OMA.R_Erdos1190_erdos_1190_variants_upper_bound_R1_H1_R1
