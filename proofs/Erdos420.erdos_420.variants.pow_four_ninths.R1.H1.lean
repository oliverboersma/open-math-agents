import OMAReductions.R_Erdos420_erdos_420_variants_pow_four_ninths_R1

-- Step Erdos420.erdos_420.variants.pow_four_ninths.R1.H1: hypothesis H1 of reduction Erdos420.erdos_420.variants.pow_four_ninths.R1

/-!
Let `h = ⌊n ^ (4/9)⌋`. The product `(n + 1) ⋯ (n + h)` equals `choose (n + h) h * h !`. For a
prime `p ≤ h` the exponent of `p` in the binomial coefficient is at most `log_p (n + h)`, so the
primes up to `h` contribute at most `log (h !) + π(h) log (n + h)` to the double sum. Now
`log (h !) ≤ h log h ≤ (4/9) h log n`, and by Chebyshev `π(h) log (n + h) = O(h)`.
-/

open Finset Real

namespace OMA

theorem prod_eq (n h : ℕ) : ∏ i ∈ range h, (n + i + 1) = (n + h).choose h * h.factorial := by
  have hM : n.factorial * ∏ i ∈ range h, (n + i + 1) = (n + h).factorial := by
    induction h with
    | zero => simp
    | succ k ih =>
      rw [Finset.prod_range_succ, ← mul_assoc, ih, ← add_assoc, Nat.factorial_succ]
      ring
  have h1 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left h n)
  rw [Nat.add_sub_cancel] at h1
  apply Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos n)
  rw [hM, ← h1]
  ring

theorem core (n h : ℕ) :
    ∑ i ∈ range h, ∑ p ∈ (range (h + 1)).filter Nat.Prime,
        ((n + i + 1).factorization p : ℝ) * Real.log p ≤
      Real.log (h.factorial : ℝ) +
        (((range (h + 1)).filter Nat.Prime).card : ℝ) * Real.log ((n + h : ℕ) : ℝ) := by
  rw [Finset.sum_comm]
  have hfac : ∀ p : ℕ, ∑ i ∈ range h, ((n + i + 1).factorization p : ℝ) * Real.log p =
      (((n + h).choose h).factorization p : ℝ) * Real.log p +
        ((h.factorial).factorization p : ℝ) * Real.log p := by
    intro p
    have h1 : (∏ i ∈ range h, (n + i + 1)).factorization p =
        ∑ i ∈ range h, (n + i + 1).factorization p := by
      rw [Nat.factorization_prod (fun i _ => by omega)]
      exact Finsupp.finset_sum_apply _ _ _
    have h2 : ((n + h).choose h * h.factorial).factorization p =
        ((n + h).choose h).factorization p + (h.factorial).factorization p := by
      rw [Nat.factorization_mul (Nat.choose_pos (Nat.le_add_left h n)).ne'
        (Nat.factorial_ne_zero h)]
      rfl
    rw [← Finset.sum_mul, ← Nat.cast_sum, ← h1, OMA.prod_eq, h2]
    push_cast
    ring
  simp only [hfac]
  rw [Finset.sum_add_distrib, add_comm]
  apply add_le_add
  · -- the factorial part
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
    refine (Finset.sum_subset ?_ ?_).ge
    · intro p hp
      rw [Nat.support_factorization] at hp
      have hp' := Nat.mem_primeFactors.1 hp
      have hle : p ≤ h := (Nat.Prime.dvd_factorial hp'.1).1 hp'.2.1
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hp'.1⟩
    · intro p _ hnot
      have h0 : (h.factorial).factorization p = 0 := by
        by_contra hne
        exact hnot (Finsupp.mem_support_iff.2 hne)
      rw [h0]
      simp
  · -- the binomial part
    have hb : ∀ p ∈ (range (h + 1)).filter Nat.Prime,
        (((n + h).choose h).factorization p : ℝ) * Real.log p ≤ Real.log ((n + h : ℕ) : ℝ) := by
      intro p hp
      have hpp : p.Prime := (Finset.mem_filter.1 hp).2
      have hppos : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
      have h1 : (((n + h).choose h).factorization p : ℝ) ≤ (Nat.log p (n + h) : ℝ) := by
        exact_mod_cast Nat.factorization_choose_le_log
      have hnh : n + h ≠ 0 := by
        have := Finset.mem_range.1 (Finset.mem_filter.1 hp).1
        have := hpp.two_le
        omega
      have h2 : ((p : ℝ) ^ Nat.log p (n + h)) ≤ ((n + h : ℕ) : ℝ) := by
        exact_mod_cast Nat.pow_log_le_self p hnh
      have h3 := Real.log_le_log (pow_pos hppos _) h2
      rw [Real.log_pow] at h3
      exact (mul_le_mul_of_nonneg_right h1 hlogp).trans h3
    calc ∑ p ∈ (range (h + 1)).filter Nat.Prime,
          (((n + h).choose h).factorization p : ℝ) * Real.log p
        ≤ ∑ _p ∈ (range (h + 1)).filter Nat.Prime, Real.log ((n + h : ℕ) : ℝ) :=
          Finset.sum_le_sum hb
      _ = (((range (h + 1)).filter Nat.Prime).card : ℝ) * Real.log ((n + h : ℕ) : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]

end OMA

theorem OMA.solution : OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1.H1 := by
  unfold OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1.H1
  intro η hη
  have hY : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ ((4 : ℝ) / 9)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hX : Filter.Tendsto (fun n : ℕ => ((⌊(n : ℝ) ^ ((4 : ℝ) / 9)⌋₊ : ℕ) : ℝ))
      Filter.atTop Filter.atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_nat_floor_atTop.comp hY)
  have hpi : ∀ᶠ n : ℕ in Filter.atTop,
      (Nat.primeCounting ⌊((⌊(n : ℝ) ^ ((4 : ℝ) / 9)⌋₊ : ℕ) : ℝ)⌋₊ : ℝ) ≤
        (Real.log 4 + 1) * ((⌊(n : ℝ) ^ ((4 : ℝ) / 9)⌋₊ : ℕ) : ℝ) /
          Real.log ((⌊(n : ℝ) ^ ((4 : ℝ) / 9)⌋₊ : ℕ) : ℝ) :=
    hX.eventually (Chebyshev.eventually_primeCounting_le one_pos)
  have hlogn : ∀ᶠ n : ℕ in Filter.atTop, max (15 / η) (9 * Real.log 2) ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop _
  filter_upwards [hpi, hlogn, hY.eventually_ge_atTop 2, Filter.eventually_ge_atTop 2]
    with n hpi hlogn hy2 hn2
  intro h
  have hdef : h = ⌊(n : ℝ) ^ ((4 : ℝ) / 9)⌋₊ := rfl
  rw [← hdef, Nat.floor_natCast] at hpi
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hnpos : (0 : ℝ) < n := by linarith
  have hy0 : (0 : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 9) := by linarith
  have hhle : (h : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 9) := by rw [hdef]; exact Nat.floor_le hy0
  have hhgt : (n : ℝ) ^ ((4 : ℝ) / 9) < (h : ℝ) + 1 := by rw [hdef]; exact Nat.lt_floor_add_one _
  clear_value h
  have hL1 : 15 / η ≤ Real.log (n : ℝ) := (le_max_left _ _).trans hlogn
  have hL2 : 9 * Real.log 2 ≤ Real.log (n : ℝ) := (le_max_right _ _).trans hlogn
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogn_pos : 0 < Real.log (n : ℝ) := by linarith
  have hlogy : Real.log ((n : ℝ) ^ ((4 : ℝ) / 9)) = 4 / 9 * Real.log (n : ℝ) :=
    Real.log_rpow hnpos _
  have hh1 : (1 : ℝ) ≤ h := by linarith
  have hhpos : (0 : ℝ) < h := by linarith
  -- `log h ≤ (4/9) log n` and `log h ≥ (1/3) log n`
  have hlogh_le : Real.log (h : ℝ) ≤ 4 / 9 * Real.log (n : ℝ) := by
    rw [← hlogy]
    exact Real.log_le_log hhpos hhle
  have hlogh_ge : 1 / 3 * Real.log (n : ℝ) ≤ Real.log (h : ℝ) := by
    have h1 : (n : ℝ) ^ ((4 : ℝ) / 9) ≤ 2 * (h : ℝ) := by linarith
    have h2 := Real.log_le_log (by linarith : (0 : ℝ) < (n : ℝ) ^ ((4 : ℝ) / 9)) h1
    rw [hlogy, Real.log_mul (by norm_num) hhpos.ne'] at h2
    linarith
  have hlogh_pos : 0 < Real.log (h : ℝ) := by linarith
  -- `h ≤ n`
  have hyn : (n : ℝ) ^ ((4 : ℝ) / 9) ≤ n := by
    calc (n : ℝ) ^ ((4 : ℝ) / 9) ≤ (n : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = n := Real.rpow_one _
  have hlognh : Real.log ((n + h : ℕ) : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    have h1 : ((n + h : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by push_cast; linarith
    have h2 := Real.log_le_log (by push_cast; linarith : (0 : ℝ) < ((n + h : ℕ) : ℝ)) h1
    rw [Real.log_mul (by norm_num) hnpos.ne'] at h2
    linarith
  -- restrict the inner sums to the primes up to `h`
  have hinner : ∀ i ∈ range h,
      ∑ p ∈ (n + i + 1).primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 9)),
        ((n + i + 1).factorization p : ℝ) * Real.log p =
      ∑ p ∈ (range (h + 1)).filter Nat.Prime, ((n + i + 1).factorization p : ℝ) * Real.log p := by
    intro i _
    apply Finset.sum_subset
    · intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
      have hpp := (Nat.mem_primeFactors.1 hp1).1
      have hph : p ≤ h := by
        have : (p : ℝ) < (h : ℝ) + 1 := lt_of_le_of_lt hp2 hhgt
        have : p < h + 1 := by exact_mod_cast this
        omega
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hpp⟩
    · intro p hp hnot
      obtain ⟨hp1, hpp⟩ := Finset.mem_filter.1 hp
      have hph : p ≤ h := by have := Finset.mem_range.1 hp1; omega
      have hpy : (p : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 9) := by
        have : (p : ℝ) ≤ h := by exact_mod_cast hph
        linarith
      have hnp : p ∉ (n + i + 1).primeFactors := fun hmem =>
        hnot (Finset.mem_filter.2 ⟨hmem, hpy⟩)
      have h0 : (n + i + 1).factorization p = 0 := by
        by_contra hne
        apply hnp
        rw [← Nat.support_factorization]
        exact Finsupp.mem_support_iff.2 hne
      rw [h0]
      simp
  rw [Finset.sum_congr rfl hinner]
  refine (OMA.core n h).trans ?_
  -- the factorial term
  have hfact : Real.log (h.factorial : ℝ) ≤ 4 / 9 * (h : ℝ) * Real.log (n : ℝ) := by
    have h1 : (h.factorial : ℝ) ≤ (h : ℝ) ^ h := by exact_mod_cast Nat.factorial_le_pow h
    have h2 := Real.log_le_log (by exact_mod_cast Nat.factorial_pos h) h1
    rw [Real.log_pow] at h2
    have h3 : (h : ℝ) * Real.log (h : ℝ) ≤ (h : ℝ) * (4 / 9 * Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogh_le hhpos.le
    linarith
  -- the prime counting term
  have hcard : ((range (h + 1)).filter Nat.Prime).card = Nat.primeCounting h := by
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have hlog4 : Real.log 4 + 1 ≤ 5 / 2 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    have := Real.log_two_lt_d9
    linarith
  have hpi2 : (Nat.primeCounting h : ℝ) * Real.log ((n + h : ℕ) : ℝ) ≤ 15 * (h : ℝ) := by
    have h1 : (Nat.primeCounting h : ℝ) ≤ 5 / 2 * (h : ℝ) / (1 / 3 * Real.log (n : ℝ)) := by
      refine hpi.trans ?_
      rw [div_le_div_iff₀ hlogh_pos (by linarith)]
      have ha : (Real.log 4 + 1) * (h : ℝ) ≤ 5 / 2 * (h : ℝ) :=
        mul_le_mul_of_nonneg_right hlog4 hhpos.le
      have hb : 0 ≤ (Real.log 4 + 1) * (h : ℝ) := by
        have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
        positivity
      calc (Real.log 4 + 1) * (h : ℝ) * (1 / 3 * Real.log (n : ℝ))
          ≤ (Real.log 4 + 1) * (h : ℝ) * Real.log (h : ℝ) :=
            mul_le_mul_of_nonneg_left hlogh_ge hb
        _ ≤ 5 / 2 * (h : ℝ) * Real.log (h : ℝ) :=
            mul_le_mul_of_nonneg_right ha hlogh_pos.le
    have h2 : 5 / 2 * (h : ℝ) / (1 / 3 * Real.log (n : ℝ)) * (2 * Real.log (n : ℝ)) =
        15 * (h : ℝ) := by
      field_simp
      ring
    have hpc0 : (0 : ℝ) ≤ Nat.primeCounting h := Nat.cast_nonneg _
    calc (Nat.primeCounting h : ℝ) * Real.log ((n + h : ℕ) : ℝ)
        ≤ (Nat.primeCounting h : ℝ) * (2 * Real.log (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hlognh hpc0
      _ ≤ 5 / 2 * (h : ℝ) / (1 / 3 * Real.log (n : ℝ)) * (2 * Real.log (n : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 (by linarith)
      _ = 15 * (h : ℝ) := h2
  have h15 : 15 * (h : ℝ) ≤ η * (h : ℝ) * Real.log (n : ℝ) := by
    have h1 : 15 ≤ η * Real.log (n : ℝ) := by
      have := mul_le_mul_of_nonneg_left hL1 hη.le
      rwa [mul_div_cancel₀ _ hη.ne'] at this
    nlinarith
  rw [hcard]
  have hsplit : (4 / 9 + η) * (h : ℝ) * Real.log (n : ℝ) =
      4 / 9 * (h : ℝ) * Real.log (n : ℝ) + η * (h : ℝ) * Real.log (n : ℝ) := by ring
  rw [hsplit]
  linarith
