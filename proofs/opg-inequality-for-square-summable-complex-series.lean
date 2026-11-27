import OMAStatements.S_opg_inequality_for_square_summable_complex_series

private def dyadicToNat (p : ℕ × ℕ) : ℕ :=
  2 ^ p.1 * (2 * p.2 + 1) - 1

private def natToDyadic (n : ℕ) : ℕ × ℕ :=
  ((n + 1).factorization 2, ordCompl[2] (n + 1) / 2)

private lemma dyadic_left_inv (p : ℕ × ℕ) : natToDyadic (dyadicToNat p) = p := by
  rcases p with ⟨k, l⟩
  have hm_pos : 0 < 2 ^ k * (2 * l + 1) := by positivity
  have hsub : dyadicToNat (k, l) + 1 = 2 ^ k * (2 * l + 1) := by
    dsimp [dyadicToNat]
    omega
  have hodd : ¬ 2 ∣ 2 * l + 1 := by omega
  have hfact_odd : (2 * l + 1).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hodd
  have hfact_pow : (2 ^ k).factorization 2 = k :=
    Nat.factorization_pow_self Nat.prime_two
  have hfact : (2 ^ k * (2 * l + 1)).factorization 2 = k := by
    rw [Nat.factorization_mul (by positivity) (by omega), Finsupp.coe_add, Pi.add_apply,
      hfact_pow, hfact_odd, add_zero]
  dsimp [natToDyadic]
  rw [hsub, hfact, Nat.mul_div_right _ (by positivity)]
  ext
  · rfl
  · dsimp; omega

private lemma dyadic_right_inv (n : ℕ) : dyadicToNat (natToDyadic n) = n := by
  have hmul := Nat.ordProj_mul_ordCompl_eq_self (n + 1) 2
  have hndvd : ¬ 2 ∣ ordCompl[2] (n + 1) :=
    Nat.not_dvd_ordCompl Nat.prime_two (Nat.succ_ne_zero n)
  have hodd : 2 * (ordCompl[2] (n + 1) / 2) + 1 = ordCompl[2] (n + 1) := by omega
  dsimp [dyadicToNat, natToDyadic]
  rw [hodd, hmul]
  omega

private def dyadicEquiv : ℕ × ℕ ≃ ℕ where
  toFun := dyadicToNat
  invFun := natToDyadic
  left_inv := dyadic_left_inv
  right_inv := dyadic_right_inv

private lemma dyadicEquiv_add_one (k l : ℕ) :
    dyadicEquiv (k, l) + 1 = 2 ^ k * (2 * l + 1) := by
  change 2 ^ k * (2 * l + 1) - 1 + 1 = 2 ^ k * (2 * l + 1)
  have : 0 < 2 ^ k * (2 * l + 1) := by positivity
  omega

private lemma hasSum_inv_succ_sq :
    HasSum (fun l : ℕ => (((l : ℝ) + 1)⁻¹) ^ 2) (Real.pi ^ 2 / 6) := by
  have h := hasSum_zeta_two
  rw [← hasSum_nat_add_iff' 1] at h
  simp only [Finset.sum_range_one, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, div_zero, sub_zero] at h
  refine h.congr_fun fun l => ?_
  push_cast
  rw [inv_pow, one_div]

private lemma tsum_mul_sq_le {u v : ℕ → ℝ} (hu0 : ∀ l, 0 ≤ u l) (hv0 : ∀ l, 0 ≤ v l)
    (hu : Summable (fun l => u l ^ 2)) (hv : Summable (fun l => v l ^ 2)) :
    (∑' l, u l * v l) ^ 2 ≤ (∑' l, u l ^ 2) * (∑' l, v l ^ 2) := by
  have huv : Summable (fun l => u l * v l) := by
    refine Summable.of_nonneg_of_le (fun l => mul_nonneg (hu0 l) (hv0 l)) (fun l => ?_)
      ((hu.add hv).div_const 2)
    nlinarith [sq_nonneg (u l - v l)]
  have hfin : ∀ s : Finset ℕ,
      (∑ l ∈ s, u l * v l) ^ 2 ≤ (∑' l, u l ^ 2) * (∑' l, v l ^ 2) := by
    intro s
    calc (∑ l ∈ s, u l * v l) ^ 2
        ≤ (∑ l ∈ s, u l ^ 2) * (∑ l ∈ s, v l ^ 2) := Finset.sum_mul_sq_le_sq_mul_sq s u v
      _ ≤ (∑' l, u l ^ 2) * (∑' l, v l ^ 2) :=
          mul_le_mul (hu.sum_le_tsum s fun l _ => sq_nonneg (u l))
            (hv.sum_le_tsum s fun l _ => sq_nonneg (v l))
            (Finset.sum_nonneg fun l _ => sq_nonneg (v l))
            (tsum_nonneg fun l => sq_nonneg (u l))
  exact le_of_tendsto (huv.hasSum.tendsto_sum_nat.pow 2)
    (Filter.Eventually.of_forall fun n => hfin (Finset.range n))

theorem OMA.solution :
    type_of% @OMA.S_opg_inequality_for_square_summable_complex_series.main := by
  intro a ha
  have hg : Summable (fun p : ℕ × ℕ => ‖a (2 ^ p.1 * (2 * p.2 + 1))‖ ^ 2) := by
    have ha' : Summable ((fun n : ℕ => ‖a (n + 1)‖ ^ 2) ∘ dyadicEquiv) :=
      (Equiv.summable_iff dyadicEquiv (f := fun n : ℕ => ‖a (n + 1)‖ ^ 2)).2 ha
    refine ha'.congr fun p => ?_
    change ‖a (dyadicEquiv p + 1)‖ ^ 2 = ‖a (2 ^ p.1 * (2 * p.2 + 1))‖ ^ 2
    rw [dyadicEquiv_add_one p.1 p.2]
  have hg_split :=
    (summable_prod_of_nonneg (f := fun p : ℕ × ℕ => ‖a (2 ^ p.1 * (2 * p.2 + 1))‖ ^ 2)
      (fun p => sq_nonneg _)).1 hg
  have hg_k : ∀ k : ℕ, Summable (fun l : ℕ => ‖a (2 ^ k * (2 * l + 1))‖ ^ 2) := hg_split.1
  have hg_outer : Summable (fun k : ℕ => ∑' l : ℕ, ‖a (2 ^ k * (2 * l + 1))‖ ^ 2) := hg_split.2
  have hg_eq :
      ∑' k : ℕ, ∑' l : ℕ, ‖a (2 ^ k * (2 * l + 1))‖ ^ 2 = ∑' n : ℕ, ‖a (n + 1)‖ ^ 2 := by
    rw [← hg.tsum_prod' hg_k]
    calc ∑' p : ℕ × ℕ, ‖a (2 ^ p.1 * (2 * p.2 + 1))‖ ^ 2
        = ∑' p : ℕ × ℕ, ‖a (dyadicEquiv p + 1)‖ ^ 2 := by
            refine tsum_congr fun p => ?_
            rw [dyadicEquiv_add_one p.1 p.2]
      _ = ∑' n : ℕ, ‖a (n + 1)‖ ^ 2 :=
          Equiv.tsum_eq dyadicEquiv (fun n : ℕ => ‖a (n + 1)‖ ^ 2)
  have hu_sum : Summable (fun l : ℕ => (((l : ℝ) + 1)⁻¹) ^ 2) :=
    hasSum_inv_succ_sq.summable
  have hu_tsum : ∑' l : ℕ, (((l : ℝ) + 1)⁻¹) ^ 2 = Real.pi ^ 2 / 6 :=
    hasSum_inv_succ_sq.tsum_eq
  have h_term : ∀ k : ℕ,
      ‖∑' l : ℕ, (((l : ℂ) + 1)⁻¹) * a (2 ^ k * (2 * l + 1))‖ ^ 2 ≤
        (Real.pi ^ 2 / 6) * (∑' l : ℕ, ‖a (2 ^ k * (2 * l + 1))‖ ^ 2) := by
    intro k
    let u : ℕ → ℝ := fun l => ((l : ℝ) + 1)⁻¹
    let v : ℕ → ℝ := fun l => ‖a (2 ^ k * (2 * l + 1))‖
    have hu0 : ∀ l, 0 ≤ u l := fun l => by dsimp [u]; positivity
    have hv0 : ∀ l, 0 ≤ v l := fun l => norm_nonneg _
    have hnorm : ∀ l : ℕ, ‖(((l : ℂ) + 1)⁻¹) * a (2 ^ k * (2 * l + 1))‖ = u l * v l := by
      intro l
      rw [norm_mul, norm_inv]
      have hcast : ((l : ℂ) + 1) = (((l : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [hcast, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have huv : Summable (fun l : ℕ => u l * v l) := by
      refine Summable.of_nonneg_of_le (fun l => mul_nonneg (hu0 l) (hv0 l)) (fun l => ?_)
        ((hu_sum.add (hg_k k)).div_const 2)
      nlinarith [sq_nonneg (u l - v l)]
    have hcsum : Summable (fun l : ℕ => ‖(((l : ℂ) + 1)⁻¹) * a (2 ^ k * (2 * l + 1))‖) :=
      huv.congr fun l => (hnorm l).symm
    have h1 : ‖∑' l : ℕ, (((l : ℂ) + 1)⁻¹) * a (2 ^ k * (2 * l + 1))‖ ^ 2 ≤
        (∑' l : ℕ, u l * v l) ^ 2 := by
      have hle := norm_tsum_le_tsum_norm hcsum
      simp_rw [hnorm] at hle
      exact pow_le_pow_left₀ (norm_nonneg _) hle 2
    have h2 : (∑' l : ℕ, u l * v l) ^ 2 ≤ (Real.pi ^ 2 / 6) * ∑' l : ℕ, v l ^ 2 := by
      rw [← hu_tsum]
      exact tsum_mul_sq_le hu0 hv0 hu_sum (hg_k k)
    exact h1.trans h2
  have h_lhs_sum : Summable
      (fun k : ℕ => ‖∑' l : ℕ, (((l : ℂ) + 1)⁻¹) * a (2 ^ k * (2 * l + 1))‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun k => sq_nonneg _) h_term (hg_outer.mul_left (Real.pi ^ 2 / 6))
  have h_sum_le :
      ∑' k : ℕ, ‖∑' l : ℕ, (((l : ℂ) + 1)⁻¹) * a (2 ^ k * (2 * l + 1))‖ ^ 2 ≤
        (Real.pi ^ 2 / 6) * (∑' n : ℕ, ‖a (n + 1)‖ ^ 2) := by
    calc ∑' k : ℕ, ‖∑' l : ℕ, (((l : ℂ) + 1)⁻¹) * a (2 ^ k * (2 * l + 1))‖ ^ 2
        ≤ ∑' k : ℕ, (Real.pi ^ 2 / 6) * (∑' l : ℕ, ‖a (2 ^ k * (2 * l + 1))‖ ^ 2) :=
          h_lhs_sum.tsum_le_tsum h_term (hg_outer.mul_left (Real.pi ^ 2 / 6))
      _ = (Real.pi ^ 2 / 6) * ∑' k : ℕ, ∑' l : ℕ, ‖a (2 ^ k * (2 * l + 1))‖ ^ 2 := tsum_mul_left
      _ = (Real.pi ^ 2 / 6) * (∑' n : ℕ, ‖a (n + 1)‖ ^ 2) := by rw [hg_eq]
  have h_mul := mul_le_mul_of_nonneg_left h_sum_le (by positivity : 0 ≤ 6 / Real.pi ^ 2)
  refine h_mul.trans_eq ?_
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp [hpi]
