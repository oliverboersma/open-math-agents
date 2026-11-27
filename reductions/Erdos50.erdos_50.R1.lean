import FormalConjectures.ErdosProblems.«50»

-- Reduction Erdos50.erdos_50.R1 of Erdős Problem 50 — erdos 50
-- Credit: @mucoucah
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- Proved here: no positive derivative at x = 0, at x = 1, and at every totient ratio
-- x = phi(d)/d < 1 (dilation n -> d n plus a wheel lower bound for the tail near 1).
-- Remaining: interior points that are not totient ratios, split into irrational (H1) and
-- rational (H2) points.

open Filter Set Topology
open scoped BigOperators

namespace OMA.R_Erdos50_erdos_50_R1

namespace Erdos50Proof

private lemma phi_product (n : ℕ) :
    (n.totient : ℝ) = n * ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors n)
  push_cast at h
  exact h

private lemma prime_factor_estimate {p : ℕ} (hp : p.Prime) :
    1 ≤ (1 + 6 / (p : ℝ)) * (1 - (p : ℝ)⁻¹) ^ 2 := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  let u : ℝ := (p : ℝ)⁻¹
  have hu : 0 ≤ u := by positivity
  have hu' : u ≤ 1 / 2 := by
    simpa [u, one_div] using (one_div_le_one_div_of_le (by norm_num) hp')
  have hpoly : 0 ≤ u * (1 - 2 * u) * (4 - 3 * u) :=
    mul_nonneg (mul_nonneg hu (by linarith)) (by linarith)
  have h : 1 ≤ (1 + 6 * u) * (1 - u) ^ 2 := by nlinarith only [hpoly]
  simpa [u, div_eq_mul_inv] using h

private lemma phi_weight_bound {n : ℕ} (hn : n ≠ 0) :
    1 ≤ (∏ p ∈ n.primeFactors, (1 + 6 / (p : ℝ))) *
      ((n.totient : ℝ) / n) ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [phi_product, mul_div_cancel_left₀ _ hn', ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  simpa using (Finset.prod_le_prod (f := fun _ : ℕ => (1 : ℝ))
    (fun _ _ => zero_le_one)
    (fun p hp => prime_factor_estimate (Nat.mem_primeFactors.mp hp).1))

private lemma prime_subset_dvd (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p)
    {n : ℕ} (hn : n ≠ 0) :
    (∏ p ∈ s, p) ∣ n ↔ ∀ p ∈ s, p ∣ n := by
  refine ⟨fun h p hp => (Finset.dvd_prod_of_mem id hp).trans h, fun h => ?_⟩
  exact (Finset.prod_dvd_prod_of_subset s n.primeFactors id
    (fun p hp => Nat.mem_primeFactors.mpr ⟨hs p hp, h p hp, hn⟩)).trans
    (Nat.prod_primeFactors_dvd n)

private lemma finite_prime_average (N : ℕ) :
    (∑ n ∈ (Finset.range (N + 1)).filter (fun n => n ≠ 0),
      ∏ p ∈ n.primeFactors, (1 + 6 / (p : ℝ))) ≤
      (N : ℝ) * Real.exp (∑' p : ℕ, 6 / (p : ℝ) ^ 2) := by
  classical
  let P := (Finset.range (N + 1)).filter Nat.Prime
  let S := (Finset.range (N + 1)).filter (fun n => n ≠ 0)
  let w (p : ℕ) : ℝ := 6 / (p : ℝ)
  have hfactor (n : ℕ) (hn : n ∈ S) :
      n.primeFactors = P.filter (fun p => p ∣ n) := by
    obtain ⟨hnN, hn0⟩ := Finset.mem_filter.mp hn
    ext p
    simp only [Nat.mem_primeFactors, P, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hp, hd, _⟩
      exact ⟨⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hd).trans_lt
        (Finset.mem_range.mp hnN), hp⟩, hd⟩
    · rintro ⟨⟨_, hp⟩, hd⟩
      exact ⟨hp, hd, hn0⟩
  have hexpand (n : ℕ) (hn : n ∈ S) :
      (∏ p ∈ n.primeFactors, (1 + w p)) =
        ∑ s ∈ P.powerset, if (∏ p ∈ s, p) ∣ n then ∏ p ∈ s, w p else 0 := by
    rw [hfactor n hn, Finset.prod_filter]
    have hterm (p : ℕ) : (if p ∣ n then 1 + w p else 1) =
        (if p ∣ n then w p else 0) + 1 := by split_ifs <;> simp [add_comm]
    simp_rw [hterm]
    rw [Finset.prod_add_one]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [Finset.prod_ite_zero]
    simp only [prime_subset_dvd s
      (fun p hp => (Finset.mem_filter.mp (Finset.mem_powerset.mp hs hp)).2)
      (Finset.mem_filter.mp hn).2]
  have hcount (s : Finset ℕ) :
      (∑ n ∈ S, if (∏ p ∈ s, p) ∣ n then ∏ p ∈ s, w p else 0) =
        ((N / ∏ p ∈ s, p : ℕ) : ℝ) * ∏ p ∈ s, w p := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Finset.filter_filter,
      Nat.card_multiples']
  change (∑ n ∈ S, ∏ p ∈ n.primeFactors, (1 + w p)) ≤ _
  calc
    _ = ∑ s ∈ P.powerset, ((N / ∏ p ∈ s, p : ℕ) : ℝ) * ∏ p ∈ s, w p := by
      rw [Finset.sum_congr rfl hexpand, Finset.sum_comm]
      exact Finset.sum_congr rfl fun s _ => hcount s
    _ ≤ ∑ s ∈ P.powerset, (N : ℝ) * ∏ p ∈ s, (6 / (p : ℝ) ^ 2) := by
      refine Finset.sum_le_sum fun s _ => ?_
      calc
        _ ≤ ((N : ℝ) / (∏ p ∈ s, p : ℕ)) * ∏ p ∈ s, w p :=
          mul_le_mul_of_nonneg_right Nat.cast_div_le (Finset.prod_nonneg fun p _ => by
            dsimp [w]
            positivity)
        _ = _ := by
          rw [Nat.cast_prod, div_mul_eq_mul_div, mul_div_assoc, ← Finset.prod_div_distrib]
          refine congrArg ((N : ℝ) * ·) (Finset.prod_congr rfl fun p _ => ?_)
          simp [w, div_div, pow_two]
    _ = (N : ℝ) * ∏ p ∈ P, (6 / (p : ℝ) ^ 2 + 1) := by
      rw [Finset.prod_add_one, Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
      calc
        _ ≤ ∏ p ∈ P, Real.exp (6 / (p : ℝ) ^ 2) :=
          Finset.prod_le_prod (fun _ _ => by positivity) (fun _ _ => Real.add_one_le_exp _)
        _ = Real.exp (∑ p ∈ P, 6 / (p : ℝ) ^ 2) := (Real.exp_sum _ _).symm
        _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          have hsum : Summable (fun p : ℕ => 1 / (p : ℝ) ^ 2) :=
            Real.summable_one_div_nat_pow.mpr (by decide)
          have hsum' : Summable (fun p : ℕ => 6 / (p : ℝ) ^ 2) := by
            simpa [div_eq_mul_inv, mul_assoc] using hsum.mul_left (6 : ℝ)
          exact hsum'.sum_le_tsum P (fun _ _ => by positivity)

private lemma quadratic_density_bound {f : ℝ → ℝ} (hf : Erdos50.IsDistributionOfPhiRatio f)
    {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    f c ≤ Real.exp (∑' p : ℕ, 6 / (p : ℝ) ^ 2) * c ^ 2 := by
  classical
  let K := Real.exp (∑' p : ℕ, 6 / (p : ℝ) ^ 2)
  let A : Set ℕ := {n | (n.totient : ℝ) < c * n}
  have hlim : A.HasDensity (f c) := hf c hc
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with b hb
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
  let B := (Finset.range (N + 1)).filter (fun n => n ∈ A)
  let S := (Finset.range (N + 1)).filter (fun n => n ≠ 0)
  let W (n : ℕ) := ∏ p ∈ n.primeFactors, (1 + 6 / (p : ℝ))
  have hsub : B ⊆ S := by
    intro n hn
    have ⟨hb, hA⟩ := Finset.mem_filter.mp hn
    refine Finset.mem_filter.mpr ⟨hb, ?_⟩
    rintro rfl
    simp [A] at hA
  have hW (n : ℕ) : 0 ≤ W n := Finset.prod_nonneg fun p _ => by positivity
  have hterm (n : ℕ) (hn : n ∈ B) : 1 ≤ c ^ 2 * W n := by
    have hn0 : n ≠ 0 := (Finset.mem_filter.mp (hsub hn)).2
    have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have hratio : (n.totient : ℝ) / n < c := (div_lt_iff₀ hnp).mpr
      (Finset.mem_filter.mp hn).2
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ (n.totient : ℝ) / n) hratio.le 2
    rw [mul_comm]
    exact (phi_weight_bound hn0).trans (mul_le_mul_of_nonneg_left hsq (hW n))
  have hcount : (B.card : ℝ) ≤ (K * c ^ 2) * (N + 1 : ℕ) := calc
    _ = ∑ _n ∈ B, (1 : ℝ) := by simp
    _ ≤ ∑ n ∈ B, c ^ 2 * W n := Finset.sum_le_sum hterm
    _ ≤ ∑ n ∈ S, c ^ 2 * W n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => mul_nonneg (sq_nonneg c) (hW n)
    _ ≤ c ^ 2 * ((N : ℝ) * K) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (finite_prime_average N) (sq_nonneg c)
    _ = (K * c ^ 2) * (N : ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ N) (by dsimp [K]; positivity)
  have hB : A ∩ Iio (N + 1) = (B : Set ℕ) := by
    ext n
    simp [B, and_comm]
  have hpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  simpa only [Set.partialDensity, Set.inter_univ, Set.univ_inter, hB, Set.ncard_coe_finset,
    Nat.ncard_Iio] using (div_le_iff₀ hpos).mpr hcount

private lemma derivative_at_zero_nonpos {f : ℝ → ℝ} (hf : Erdos50.IsDistributionOfPhiRatio f)
    {y : ℝ} (hd : HasDerivWithinAt f y (Icc 0 1) 0) : y ≤ 0 := by
  have hz : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have hf0 : f 0 = 0 :=
    le_antisymm (by simpa using quadratic_density_bound hf hz) (hf 0 hz).nonneg
  let K := Real.exp (∑' p : ℕ, 6 / (p : ℝ) ^ 2)
  have hs : Tendsto (slope f 0) (𝓝[Ioo 0 1] 0) (𝓝 y) :=
    (hasDerivWithinAt_iff_tendsto_slope.mp hd).mono_left (nhdsWithin_mono 0 (by
      intro z hz
      exact ⟨Ioo_subset_Icc_self hz, by simpa using hz.1.ne'⟩))
  have ht : Tendsto (fun z : ℝ => K * z) (𝓝[Ioo 0 1] 0) (𝓝 0) := by
    have hid :
        Tendsto id (𝓝[Ioo (0 : ℝ) 1] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using (tendsto_const_nhds (x := K)).mul hid
  have : (𝓝[Ioo (0 : ℝ) 1] 0).NeBot := by
    rw [nhdsWithin_Ioo_eq_nhdsGT zero_lt_one]
    exact nhdsGT_neBot _
  refine le_of_tendsto_of_tendsto hs ht ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [slope_def_field, hf0, sub_zero, sub_zero, div_le_iff₀ hz.1]
  simpa [K, pow_two, mul_assoc] using quadratic_density_bound hf (Ioo_subset_Icc_self hz)

private lemma avoidance_count (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    {N : ℕ} (hN : (∏ p ∈ P, p) ∣ N) :
    (((Finset.range (N + 1)).filter (fun n => n ≠ 0 ∧ ∀ p ∈ P, ¬p ∣ n)).card : ℝ) =
      (N : ℝ) * ∏ p ∈ P, (1 - (p : ℝ)⁻¹) := by
  classical
  let S := (Finset.range (N + 1)).filter (fun n => n ≠ 0)
  have hexpand (n : ℕ) (hn : n ∈ S) :
      (if ∀ p ∈ P, ¬p ∣ n then (1 : ℝ) else 0) =
        ∑ s ∈ P.powerset, (-1 : ℝ) ^ s.card * (if (∏ p ∈ s, p) ∣ n then 1 else 0) := by
    have hterm (p : ℕ) : (if ¬p ∣ n then (1 : ℝ) else 0) =
        1 - (if p ∣ n then 1 else 0) := by by_cases hp : p ∣ n <;> simp [hp]
    have heq : (if ∀ p ∈ P, ¬p ∣ n then (1 : ℝ) else 0) =
        ∏ p ∈ P, (if ¬p ∣ n then (1 : ℝ) else 0) := by
      symm
      simpa only [Finset.prod_const_one] using
        (Finset.prod_ite_zero (s := P) (p := fun p => ¬p ∣ n) (f := fun _ => (1 : ℝ)))
    rw [heq]
    simp only [hterm, Finset.prod_sub, Finset.prod_const_one, mul_one]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [Finset.prod_ite_zero, Finset.prod_const_one]
    simp only [prime_subset_dvd s (fun p hp => hP p (Finset.mem_powerset.mp hs hp))
      (Finset.mem_filter.mp hn).2]
  have hcount (s : Finset ℕ) (hs : s ∈ P.powerset) :
      (∑ n ∈ S, (-1 : ℝ) ^ s.card * (if (∏ p ∈ s, p) ∣ n then 1 else 0)) =
        (N : ℝ) * ((-1 : ℝ) ^ s.card * ∏ p ∈ s, (p : ℝ)⁻¹) := by
    have hd : (∏ p ∈ s, p) ∣ N :=
      (Finset.prod_dvd_prod_of_subset s P id (Finset.mem_powerset.mp hs)).trans hN
    rw [← Finset.mul_sum, Finset.sum_boole, Finset.filter_filter, Nat.card_multiples',
      Nat.cast_div_charZero hd, Nat.cast_prod, div_eq_mul_inv, ← Finset.prod_inv_distrib]
    ring
  rw [← Finset.filter_filter, ← Finset.sum_boole]
  change (∑ n ∈ S, _) = _
  rw [Finset.sum_congr rfl hexpand, Finset.sum_comm]
  simp only [Finset.prod_sub, Finset.prod_const_one, mul_one, Finset.mul_sum]
  exact Finset.sum_congr rfl hcount

private lemma totient_gap_le {n : ℕ} (hn : n ≠ 0) :
    1 - (n.totient : ℝ) / n ≤ ∑ p ∈ n.primeFactors, (p : ℝ)⁻¹ := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [phi_product, mul_div_cancel_left₀ _ hn']
  suffices ∀ s : Finset ℕ, 1 - ∏ p ∈ s, (1 - (p : ℝ)⁻¹) ≤ ∑ p ∈ s, (p : ℝ)⁻¹ by
    exact this _
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    have hle (q : ℕ) : (q : ℝ)⁻¹ ≤ 1 := by
      by_cases hq : q = 0
      · simp [hq]
      · have hq' : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero hq
        simpa [one_div] using (one_div_le_one_div_of_le (by norm_num) hq')
    have hprod : (∏ q ∈ s, (1 - (q : ℝ)⁻¹)) ≤ 1 :=
      Finset.prod_le_one (fun q _ => sub_nonneg.mpr (hle q)) (fun q _ => sub_le_self _ (by positivity))
    rw [Finset.prod_insert hp, Finset.sum_insert hp]
    have h := mul_le_mul_of_nonneg_left hprod (show 0 ≤ (p : ℝ)⁻¹ by positivity)
    nlinarith only [ih, h]

private lemma reciprocal_square_tail {m N : ℕ} (hm : m ≤ N) (hm0 : m ≠ 0) :
    (∑ p ∈ Finset.Ico (m + 1) (N + 1), (p : ℝ)⁻¹ ^ 2) ≤ (m : ℝ)⁻¹ := by
  let u (p : ℕ) := -((p - 1 : ℕ) : ℝ)⁻¹
  calc
    _ ≤ ∑ p ∈ Finset.Ico (m + 1) (N + 1), (u (p + 1) - u p) := by
      refine Finset.sum_le_sum fun p hp => ?_
      have h1 : 0 < p - 1 := by have := (Finset.mem_Ico.mp hp).1; omega
      have h1' : (0 : ℝ) < (p - 1 : ℕ) := by exact_mod_cast h1
      have h2 : (0 : ℝ) < p := by have := (Finset.mem_Ico.mp hp).1; exact_mod_cast (by omega : 0 < p)
      have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
      simp only [u, Nat.add_sub_cancel, hcast]
      rw [inv_pow, ← one_div]
      apply (div_le_iff₀ (sq_pos_of_pos h2)).mpr
      have hpos : 0 < (p : ℝ) - 1 := by linarith
      field_simp [hpos.ne', h2.ne']
      nlinarith
    _ = (m : ℝ)⁻¹ - (N : ℝ)⁻¹ := by
      rw [Finset.sum_Ico_sub (f := u) (Nat.succ_le_succ hm)]
      simp [u, sub_eq_add_neg, add_comm]
    _ ≤ _ := sub_le_self _ (by positivity)

private lemma finite_large_divisor_average {m N : ℕ} (hm : m ≤ N) (hm0 : m ≠ 0) :
    (∑ n ∈ (Finset.range (N + 1)).filter (fun n => n ≠ 0),
      ∑ p ∈ Finset.Ico (m + 1) (N + 1), if p ∣ n then (p : ℝ)⁻¹ else 0)
      ≤ (N : ℝ) * (m : ℝ)⁻¹ := by
  rw [Finset.sum_comm]
  calc
    _ = ∑ p ∈ Finset.Ico (m + 1) (N + 1), ((N / p : ℕ) : ℝ) * (p : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro p _
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Finset.filter_filter,
        Nat.card_multiples']
    _ ≤ ∑ p ∈ Finset.Ico (m + 1) (N + 1), (N : ℝ) * (p : ℝ)⁻¹ ^ 2 := by
      refine Finset.sum_le_sum fun p _ => ?_
      calc
        _ ≤ ((N : ℝ) / p) * (p : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right Nat.cast_div_le (by positivity)
        _ = _ := by ring
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (reciprocal_square_tail hm hm0) (by positivity)

private lemma mem_smallPrimes {m p : ℕ} : p ∈ ((Finset.range (m + 1)).filter Nat.Prime) ↔ p ≤ m ∧ p.Prime := by
  simp

private lemma one_sub_inv_nonneg (p : ℕ) : 0 ≤ 1 - (p : ℝ)⁻¹ := by
  by_cases hp : p = 0
  · simp [hp]
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast Nat.pos_of_ne_zero hp
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hp'
  simpa [one_div, sub_nonneg] using h

private lemma wheel_step (k : ℕ) :
    (6 * (k : ℝ) + 1) / (6 * k + 7) ≤
      ((1 - (6 * k + 5 : ℝ)⁻¹) * (1 - (6 * k + 7 : ℝ)⁻¹)) ^ 3 := by
  let a := 6 * (k : ℝ)
  have ha : 0 ≤ a := by positivity
  have hcube (t : ℝ) (ht : 1 ≤ t) : 1 - 3 * t⁻¹ ≤ (1 - t⁻¹) ^ 3 := by
    have htinv : t⁻¹ ≤ 1 := by
      simpa [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) ht
    have hp : 0 ≤ t⁻¹ ^ 2 * (3 - t⁻¹) := mul_nonneg (sq_nonneg _) (by linarith)
    nlinarith only [hp]
  have h1 : (a + 1) / (a + 4) ≤ (1 - (a + 5)⁻¹) ^ 3 := by
    calc
      _ = 1 - 3 * (a + 4)⁻¹ := by field_simp; ring
      _ ≤ 1 - 3 * (a + 5)⁻¹ := by
        have h : (a + 5)⁻¹ ≤ (a + 4)⁻¹ := by
          simpa [one_div] using one_div_le_one_div_of_le (by linarith : 0 < a + 4)
            (by linarith : a + 4 ≤ a + 5)
        linarith
      _ ≤ _ := hcube _ (by linarith)
  have h2 : (a + 4) / (a + 7) ≤ (1 - (a + 7)⁻¹) ^ 3 := by
    calc
      _ = 1 - 3 * (a + 7)⁻¹ := by field_simp; ring
      _ ≤ _ := hcube _ (by linarith)
  change (a + 1) / (a + 7) ≤ _
  rw [mul_pow]
  calc
    _ = ((a + 1) / (a + 4)) * ((a + 4) / (a + 7)) := by field_simp
    _ ≤ _ := mul_le_mul h1 h2 (by positivity) (le_trans (by positivity) h1)

private lemma wheel_product_bound (k : ℕ) :
    1 / (27 * (6 * (k : ℝ) + 1)) ≤
      (∏ p ∈ ((Finset.range ((6 * k + 3) + 1)).filter Nat.Prime), (1 - (p : ℝ)⁻¹)) ^ 3 := by
  induction k with
  | zero =>
    have h : ((Finset.range (3 + 1)).filter Nat.Prime) = {2, 3} := by decide
    norm_num [h, Finset.prod_insert, Finset.prod_singleton]
  | succ k ih =>
    let g (p : ℕ) : ℝ := 1 - (p : ℝ)⁻¹
    let P := ((Finset.range ((6*k+3) + 1)).filter Nat.Prime)
    let P' := ((Finset.range ((6*(k+1)+3) + 1)).filter Nat.Prime)
    have hsub : P ⊆ P' := by
      intro p hp
      have := mem_smallPrimes.mp hp
      exact mem_smallPrimes.mpr ⟨by omega, this.2⟩
    have hcand : P' \ P ⊆ ({6*k+5, 6*k+7} : Finset ℕ) := by
      intro p hp
      obtain ⟨hp', hp⟩ := Finset.mem_sdiff.mp hp
      obtain ⟨hhi, hprime⟩ := mem_smallPrimes.mp hp'
      have hlo : 6*k+3 < p := by
        by_contra! h
        exact hp (mem_smallPrimes.mpr ⟨h, hprime⟩)
      have hodd : p % 2 = 1 := by
        rcases hprime.eq_two_or_odd with rfl | hodd
        · omega
        · exact hodd
      have hnot3 : ¬3 ∣ p := by
        intro h
        rcases hprime.eq_one_or_self_of_dvd 3 h with hfalse | heq <;> omega
      have hmod : p % 3 ≠ 0 := fun h => hnot3 (Nat.dvd_iff_mod_eq_zero.mpr h)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have hg (p : ℕ) : 0 ≤ g p := one_sub_inv_nonneg p
    have hprod : ∏ p ∈ ({6*k+5, 6*k+7} : Finset ℕ), g p ≤ ∏ p ∈ P' \ P, g p :=
      Finset.prod_le_prod_of_subset_of_le_one hcand (fun p _ => hg p)
        (fun p _ _ => sub_le_self _ (by positivity))
    have heq : ∏ p ∈ ({6*k+5, 6*k+7} : Finset ℕ), g p = g (6*k+5) * g (6*k+7) := by
      rw [Finset.prod_insert (by simp), Finset.prod_singleton]
    rw [heq] at hprod
    have hpow : (6 * (k : ℝ) + 1) / (6 * k + 7) ≤
        (∏ p ∈ P' \ P, g p) ^ 3 := by
      apply le_trans (wheel_step k)
      have hpow' := pow_le_pow_left₀ (mul_nonneg (hg (6*k+5)) (hg (6*k+7))) hprod 3
      simpa [g, Nat.cast_add, Nat.cast_mul] using hpow'
    change 1 / (27 * (6 * ((k + 1 : ℕ) : ℝ) + 1)) ≤ (∏ p ∈ P', g p) ^ 3
    rw [← Finset.prod_sdiff hsub, mul_pow]
    have hpos : 0 ≤ (∏ p ∈ P' \ P, g p) ^ 3 := pow_nonneg (Finset.prod_nonneg fun p _ => hg p) _
    calc
      _ = ((6 * (k : ℝ) + 1) / (6 * k + 7)) * (1 / (27 * (6 * k + 1))) := by
        push_cast
        have ht : 0 < 6 * (k : ℝ) + 1 := by positivity
        have ht' : 0 < 6 * (k : ℝ) + 7 := by positivity
        field_simp
        ring
      _ ≤ _ := mul_le_mul hpow ih (by positivity) hpos

private lemma partialDensity_count (A : Set ℕ) [DecidablePred (· ∈ A)] (b : ℕ) :
    A.partialDensity Set.univ b =
      (((Finset.range b).filter (fun n => n ∈ A)).card : ℝ) / b := by
  classical
  have hs : A ∩ Set.Iio b = ((Finset.range b).filter (fun n => n ∈ A) : Set ℕ) := by
    ext n
    simp [and_comm]
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, hs,
    Set.ncard_coe_finset, Nat.ncard_Iio]

private lemma density_at_one {f : ℝ → ℝ} (hf : Erdos50.IsDistributionOfPhiRatio f) : f 1 = 1 := by
  classical
  let A : Set ℕ := {n | (n.totient : ℝ) < 1 * n}
  have hfin : Aᶜ.Finite := by
    refine (Set.finite_Iio 2).subset ?_
    intro n hn
    by_contra! h
    apply hn
    have hlt := Nat.totient_lt n (by simpa using h : 1 < n)
    simpa [A] using (show (n.totient : ℝ) < n by exact_mod_cast hlt)
  have ha : A.HasDensity (f 1) := hf 1 ⟨zero_le_one, le_rfl⟩
  have hb : Aᶜ.HasDensity 0 := Nat.hasDensity_zero_of_finite hfin
  unfold Set.HasDensity at ha hb
  refine tendsto_nhds_unique ha (Tendsto.congr' ?_ (by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hb))
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with b hb'
  rw [partialDensity_count, partialDensity_count]
  have h := Finset.card_filter_add_card_filter_not (s := Finset.range b) (p := fun n => n ∈ A)
  rw [Finset.card_range] at h
  have hpos : (b : ℝ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  simp only [Set.mem_compl_iff]
  apply (eq_div_iff hpos).mpr
  rw [sub_mul, one_mul, div_mul_cancel₀ _ hpos]
  have h' : (((Finset.range b).filter (fun n => n ∈ A)).card : ℝ) +
      (((Finset.range b).filter (fun n => n ∉ A)).card : ℝ) = b := by exact_mod_cast h
  linarith

private lemma density_near_one {f : ℝ → ℝ} (hf : Erdos50.IsDistributionOfPhiRatio f)
    {m : ℕ} (hm : m ≠ 0) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    (∏ p ∈ ((Finset.range (m + 1)).filter Nat.Prime), (1 - (p : ℝ)⁻¹)) - (m : ℝ)⁻¹ / h ≤ 1 - f (1 - h) := by
  classical
  let P := ((Finset.range (m + 1)).filter Nat.Prime)
  let Q := ∏ p ∈ P, p
  let D := ∏ p ∈ P, (1 - (p : ℝ)⁻¹)
  let E := (m : ℝ)⁻¹ / h
  let A : Set ℕ := {n | (n.totient : ℝ) < (1 - h) * n}
  have hQ : 0 < Q := Finset.prod_pos fun p hp => (mem_smallPrimes.mp hp).2.pos
  have hseq : Tendsto (fun k : ℕ => k * Q + 1) atTop atTop := by
    refine tendsto_atTop_mono' _ (.of_forall fun k => ?_) tendsto_id
    exact (Nat.le_mul_of_pos_right k hQ).trans (Nat.le_succ _)
  have hlim : A.HasDensity (f (1 - h)) := hf _ ⟨by linarith, by linarith⟩
  have hlim' : Tendsto (fun k : ℕ => A.partialDensity Set.univ (k * Q + 1))
      atTop (𝓝 (f (1 - h))) := hlim.comp hseq
  have hlim'' : Tendsto (fun k : ℕ => 1 - (D - E) + (D - E) / (k * Q + 1 : ℕ))
      atTop (𝓝 (1 - (D - E))) := by
    simpa using (tendsto_const_nhds (x := 1 - (D - E))).add
      ((tendsto_const_div_atTop_nhds_zero_nat (D - E)).comp hseq)
  suffices f (1 - h) ≤ 1 - (D - E) by
    change D - E ≤ 1 - f (1 - h)
    linarith
  refine le_of_tendsto_of_tendsto hlim' hlim'' ?_
  filter_upwards [hseq.eventually (eventually_ge_atTop (m + 1))] with k hk
  let N := k * Q
  have hmN : m ≤ N := Nat.le_of_succ_le_succ hk
  let R := Finset.range (N + 1)
  let B := R.filter (fun n => n ∈ A)
  let U := R.filter (fun n => n ≠ 0 ∧ ∀ p ∈ P, ¬p ∣ n)
  let S := R.filter (fun n => n ≠ 0)
  let W (n : ℕ) := ∑ p ∈ Finset.Ico (m + 1) (N + 1), if p ∣ n then (p : ℝ)⁻¹ else 0
  have hterm (n : ℕ) (hn : n ∈ B ∩ U) : h ≤ W n := by
    obtain ⟨hnB, hnU⟩ := Finset.mem_inter.mp hn
    obtain ⟨hnN, hn0, hnP⟩ := Finset.mem_filter.mp hnU
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have hnA : (n.totient : ℝ) / n < 1 - h :=
      (div_lt_iff₀ hnpos).mpr (Finset.mem_filter.mp hnB).2
    have hsub : n.primeFactors ⊆ Finset.Ico (m + 1) (N + 1) := by
      intro p hp
      obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
      have hgt : m < p := lt_of_not_ge fun h => hnP p (mem_smallPrimes.mpr ⟨h, hpp⟩) hpd
      exact Finset.mem_Ico.mpr ⟨hgt, (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpd).trans_lt
        (Finset.mem_range.mp hnN)⟩
    calc
      _ ≤ 1 - (n.totient : ℝ) / n := by linarith
      _ ≤ ∑ p ∈ n.primeFactors, (p : ℝ)⁻¹ := totient_gap_le hn0
      _ = ∑ p ∈ n.primeFactors, if p ∣ n then (p : ℝ)⁻¹ else 0 := by
        exact Finset.sum_congr rfl fun p hp => (if_pos (Nat.mem_primeFactors.mp hp).2.1).symm
      _ ≤ W n := Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => by split_ifs <;> positivity
  have hbad : ((B ∩ U).card : ℝ) ≤ (N : ℝ) * E := by
    rw [show (N : ℝ) * E = ((N : ℝ) * (m : ℝ)⁻¹) / h by simp [E, mul_div_assoc]]
    apply (le_div_iff₀ hh).mpr
    calc
      _ = ∑ _n ∈ B ∩ U, h := by simp
      _ ≤ ∑ n ∈ B ∩ U, W n := Finset.sum_le_sum hterm
      _ ≤ ∑ n ∈ S, W n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_inter.mp hn).2).1,
            (Finset.mem_filter.mp (Finset.mem_inter.mp hn).2).2.1⟩
        · intro n _ _
          exact Finset.sum_nonneg fun p _ => by split_ifs <;> positivity
      _ ≤ _ := finite_large_divisor_average hmN hm
  have hU : (U.card : ℝ) = (N : ℝ) * D :=
    avoidance_count P (fun p hp => (mem_smallPrimes.mp hp).2) (dvd_mul_left Q k)
  have hBU : (B ∪ U).card ≤ N + 1 := by
    simpa [R] using Finset.card_le_card
      (Finset.union_subset (Finset.filter_subset _ R) (Finset.filter_subset _ R) :
        B ∪ U ⊆ R)
  have hcount : (B.card : ℝ) + (N : ℝ) * D ≤ (N + 1 : ℕ) + (N : ℝ) * E := calc
    _ = (B.card : ℝ) + U.card := by rw [hU]
    _ = ((B ∪ U).card : ℝ) + (B ∩ U).card := by
      exact_mod_cast (Finset.card_union_add_card_inter B U).symm
    _ ≤ _ := add_le_add (by exact_mod_cast hBU) hbad
  rw [partialDensity_count]
  change (B.card : ℝ) / (N + 1 : ℕ) ≤ 1 - (D - E) + (D - E) / (N + 1 : ℕ)
  have hpos : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  apply (div_le_iff₀ hpos).mpr
  rw [add_mul, div_mul_cancel₀ _ hpos.ne']
  push_cast at hcount ⊢
  nlinarith only [hcount]

private lemma endpoint_growth_unbounded {f : ℝ → ℝ} (hf : Erdos50.IsDistributionOfPhiRatio f)
    {C δ : ℝ} (hδ : 0 < δ)
    (hbound : ∀ h : ℝ, 0 < h → h ≤ 1 → h < δ → 1 - f (1 - h) ≤ C * h) : False := by
  let M : ℝ := max 1 (C + 1)
  obtain ⟨j, hj⟩ := exists_nat_gt (max 1 (max δ⁻¹ (189 * M ^ 3)))
  have hj1 : (1 : ℝ) < j := (le_max_left _ _).trans_lt hj
  have hjδ : δ⁻¹ < j := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hj
  have hjM : 189 * M ^ 3 < j := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hj
  let h : ℝ := ((j : ℝ) + 1)⁻¹
  have hjp : 0 < (j : ℝ) + 1 := by linarith
  have hp : 0 < h := inv_pos.mpr hjp
  have hh1 : h ≤ 1 := by
    simpa [h, one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (by linarith : (1 : ℝ) ≤ (j : ℝ) + 1)
  have hhδ : h < δ := by
    have hδi : 0 < δ⁻¹ := inv_pos.mpr hδ
    have hi : ((j : ℝ) + 1)⁻¹ < (δ⁻¹)⁻¹ :=
      (inv_lt_inv₀ hjp hδi).mpr (by linarith)
    simpa [h] using hi
  have hgap := hbound h hp hh1 hhδ
  let m : ℕ := 6 * (j * j) + 3
  have hm : m ≠ 0 := by dsimp [m]; omega
  have htail := density_near_one hf hm hp hh1
  have hmsq : ((j : ℝ) + 1) ^ 2 ≤ (m : ℝ) := by
    dsimp [m]
    push_cast
    nlinarith only [sq_nonneg ((j : ℝ) - 1), sq_nonneg (j : ℝ)]
  have he : (m : ℝ)⁻¹ / h ≤ h := by
    apply (div_le_iff₀ hp).mpr
    rw [← pow_two, show h = ((j : ℝ) + 1)⁻¹ by rfl, inv_pow]
    exact inv_anti₀ (by positivity) hmsq
  let D := ∏ p ∈ ((Finset.range (m + 1)).filter Nat.Prime), (1 - (p : ℝ)⁻¹)
  have hD0 : 0 ≤ D := Finset.prod_nonneg fun p _ => one_sub_inv_nonneg p
  have hD : D ≤ M * h := by
    have hmul := mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) (C + 1)) hp.le
    change D - (m : ℝ)⁻¹ / h ≤ _ at htail
    linarith only [htail, hgap, he, hmul]
  have hpow : 1 / (27 * (6 * ((j * j : ℕ) : ℝ) + 1)) ≤ (M * h) ^ 3 :=
    (wheel_product_bound (j * j)).trans (pow_le_pow_left₀ hD0 hD 3)
  have hden : 27 * (6 * ((j * j : ℕ) : ℝ) + 1) ≤ 189 * ((j : ℝ) + 1) ^ 2 := by
    push_cast
    nlinarith only [hj1, sq_nonneg (j : ℝ)]
  have hlow : 1 / (189 * ((j : ℝ) + 1) ^ 2) ≤ (M * h) ^ 3 :=
    (one_div_le_one_div_of_le (by positivity) hden).trans hpow
  rw [show h = ((j : ℝ) + 1)⁻¹ by rfl, mul_pow, inv_pow, ← div_eq_mul_inv] at hlow
  have hden' : 0 < 189 * ((j : ℝ) + 1) ^ 2 := by positivity
  have hcross := (div_le_div_iff₀ hden' (pow_pos hjp 3)).mp hlow
  have hjlt : 189 * M ^ 3 < (j : ℝ) + 1 := by linarith
  have hcontra := mul_lt_mul_of_pos_right hjlt (pow_pos hjp 2)
  nlinarith only [hcross, hcontra]

private lemma no_derivative_at_one {f : ℝ → ℝ} (hf : Erdos50.IsDistributionOfPhiRatio f)
    {y : ℝ} (hd : HasDerivWithinAt f y (Icc 0 1) 1) : False := by
  have ht := hasDerivWithinAt_iff_tendsto_slope.mp hd
  obtain ⟨δ, hδ, hlim⟩ := Metric.tendsto_nhdsWithin_nhds.mp ht 1 zero_lt_one
  apply endpoint_growth_unbounded hf (C := y + 1) hδ
  intro h hp hh1 hhδ
  have hmem : 1 - h ∈ Icc (0 : ℝ) 1 \ {1} := by
    exact ⟨⟨by linarith, by linarith⟩, by
      simp
      linarith⟩
  have hdist : dist (1 - h) 1 < δ := by
    rw [Real.dist_eq, show 1 - h - 1 = -h by ring, abs_neg, abs_of_pos hp]
    exact hhδ
  have hsl := hlim hmem hdist
  rw [Real.dist_eq, slope_def_field, show 1 - h - 1 = -h by ring, div_neg, ← neg_div,
    neg_sub] at hsl
  apply (div_le_iff₀ hp).mp
  have htop := (abs_lt.mp hsl).2
  rw [density_at_one hf] at htop
  linarith


private lemma density_difference {A B : Set ℕ} {a b : ℝ} (hs : A ⊆ B)
    (ha : A.HasDensity a) (hb : B.HasDensity b) : (B \ A).HasDensity (b - a) := by
  classical
  unfold Set.HasDensity at ha hb ⊢
  refine (hb.sub ha).congr fun N => ?_
  simp only [partialDensity_count]
  have hsub : (Finset.range N).filter (fun n => n ∈ A) ⊆
      (Finset.range N).filter (fun n => n ∈ B) := by
    intro n hn
    obtain ⟨hN, hA⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hN, hs hA⟩
  have heq : (Finset.range N).filter (fun n => n ∈ B \ A) =
      ((Finset.range N).filter (fun n => n ∈ B)) \
        ((Finset.range N).filter (fun n => n ∈ A)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_sdiff, Set.mem_sdiff]
    tauto
  rw [heq, Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub), sub_div]

private lemma phi_ratio_mul_upper {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    ((d*n).totient : ℝ) / (d*n : ℕ) ≤ (d.totient : ℝ) / d := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hdn' : ((d*n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.mul_pos hd hn).ne'
  simp only [phi_product, mul_div_cancel_left₀ _ hd', mul_div_cancel_left₀ _ hdn']
  refine Finset.prod_le_prod_of_subset_of_le_one ?_ (fun p _ => one_sub_inv_nonneg p)
    (fun p _ _ => sub_le_self _ (by positivity))
  intro p hp
  obtain ⟨hp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
  exact Nat.mem_primeFactors.mpr ⟨hp, hpd.trans (dvd_mul_right d n), (Nat.mul_pos hd hn).ne'⟩

private lemma scaled_tail_le_increment {f : ℝ → ℝ} (hf : Erdos50.IsDistributionOfPhiRatio f)
    {d : ℕ} (hd : 0 < d) {r h : ℝ} (hr : r = (d.totient : ℝ) / d)
    (hh : 0 < h) (hh1 : h ≤ 1) (hupper : r + h ≤ 1) :
    (1 - f (1 - h)) / d ≤ f (r + h) - f (r * (1 - h)) := by
  classical
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r ≤ 1 := by linarith
  have hl0 : 0 ≤ r * (1 - h) := mul_nonneg hr0 (by linarith)
  have hlr : r * (1 - h) ≤ r := by nlinarith only [mul_nonneg hr0 hh.le]
  let A (t : ℝ) : Set ℕ := {n | (n.totient : ℝ) < t * n}
  have hmono {a b : ℝ} (hab : a ≤ b) : A a ⊆ A b :=
    fun n hn => lt_of_lt_of_le hn (mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg n))
  let S := A 1 \ A (1 - h)
  let T := A (r + h) \ A (r * (1 - h))
  have hS : S.HasDensity (1 - f (1 - h)) := by
    have hs : S.HasDensity (f 1 - f (1 - h)) := density_difference
      (hmono (show 1 - h ≤ 1 by linarith)) (hf (1 - h) ⟨by linarith, by linarith⟩)
      (hf 1 ⟨zero_le_one, le_rfl⟩)
    simpa only [density_at_one hf] using hs
  have hT : T.HasDensity (f (r + h) - f (r * (1 - h))) :=
    density_difference (hmono (by linarith)) (hf _ ⟨hl0, hlr.trans hr1⟩)
      (hf _ ⟨by linarith, hupper⟩)
  have hmaps : ∀ n ∈ S, d*n ∈ T := by
    intro n hn
    have hn0 : 0 < n := by
      by_contra! hn0
      have : n = 0 := by omega
      subst n
      have hb := hn.1
      simp [A] at hb
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hdn' : (0 : ℝ) < ((d*n : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hd hn0
    refine ⟨?_, ?_⟩
    · apply (div_lt_iff₀ hdn').mp
      exact (phi_ratio_mul_upper hd hn0).trans_lt (by rw [← hr]; linarith)
    · intro hbad
      have ht : 1 - h ≤ (n.totient : ℝ) / n :=
        (le_div_iff₀ hn').mpr (le_of_not_gt hn.2)
      have hl : r * (1 - h) ≤ ((d*n).totient : ℝ) / (d*n : ℕ) := calc
        _ ≤ r * ((n.totient : ℝ) / n) := mul_le_mul_of_nonneg_left ht hr0
        _ = ((d.totient * n.totient : ℕ) : ℝ) / (d*n : ℕ) := by
          rw [hr, Nat.cast_mul, Nat.cast_mul, div_mul_div_comm]
        _ ≤ _ := div_le_div_of_nonneg_right
          (by exact_mod_cast Nat.totient_super_multiplicative d n) hdn'.le
      exact (not_lt_of_ge hl) ((div_lt_iff₀ hdn').mpr hbad)
  have hseq : Tendsto (fun N : ℕ => d * N) atTop atTop := by
    refine tendsto_atTop_mono' _ (.of_forall fun N => ?_) tendsto_id
    simpa [mul_comm] using Nat.le_mul_of_pos_right N hd
  unfold Set.HasDensity at hS hT
  refine le_of_tendsto_of_tendsto' (hS.div_const (d : ℝ)) (hT.comp hseq) fun N => ?_
  change S.partialDensity univ N / (d : ℝ) ≤ T.partialDensity univ (d*N)
  rw [partialDensity_count, partialDensity_count, div_div, Nat.cast_mul, mul_comm (N : ℝ)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Nat.cast_le.mpr
  refine Finset.card_le_card_of_injOn (fun n => d*n) ?_ ?_
  · intro n hn
    obtain ⟨hnN, hnS⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (Nat.mul_lt_mul_of_pos_left (Finset.mem_range.mp hnN) hd), hmaps n hnS⟩
  · intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left hd hab

private lemma derivative_increment_bound {f : ℝ → ℝ} {r y : ℝ}
    (hd : HasDerivWithinAt f y (Icc 0 1) r) :
    ∃ δ > 0, ∀ z ∈ Icc (0 : ℝ) 1, |z-r| < δ → |f z - f r| ≤ (|y| + 1) * |z-r| := by
  obtain ⟨δ, hδ, hlim⟩ :=
    Metric.tendsto_nhdsWithin_nhds.mp (hasDerivWithinAt_iff_tendsto_slope.mp hd) 1 zero_lt_one
  refine ⟨δ, hδ, fun z hz hdist => ?_⟩
  by_cases heq : z = r
  · subst z
    simp
  have hmem : z ∈ Icc (0 : ℝ) 1 \ {r} := ⟨hz, by simpa using heq⟩
  have hs := hlim hmem (by simpa [Real.dist_eq] using hdist)
  rw [Real.dist_eq] at hs
  have hab : |slope f r z| ≤ |y| + 1 := by
    calc
      _ = |(slope f r z - y) + y| := by rw [sub_add_cancel]
      _ ≤ |slope f r z - y| + |y| := abs_add_le _ _
      _ ≤ _ := by linarith
  rw [slope_def_field, abs_div] at hab
  exact (div_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr heq))).mp hab

private lemma no_derivative_at_finite_ratio {f : ℝ → ℝ} (hf : Erdos50.IsDistributionOfPhiRatio f)
    {d : ℕ} (hd : 0 < d) {r y : ℝ} (hr : r = (d.totient : ℝ) / d) (hr1 : r < 1)
    (hder : HasDerivWithinAt f y (Icc 0 1) r) : False := by
  obtain ⟨δ, hδ, hinc⟩ := derivative_increment_bound hder
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  let C := |y| + 1
  apply endpoint_growth_unbounded hf (C := (d : ℝ) * (2 * C))
    (δ := min δ (1 - r)) (lt_min hδ (by linarith))
  intro h hh hh1 hsmall
  have hhδ : h < δ := hsmall.trans_le (min_le_left _ _)
  have hright : r + h ≤ 1 := by
    have := hsmall.trans_le (min_le_right _ _)
    linarith
  have hleft : r * (1 - h) ≤ r := by nlinarith only [mul_nonneg hr0 hh.le]
  have hleftdist : |r * (1 - h) - r| = r*h := by
    rw [abs_of_nonpos (sub_nonpos.mpr hleft)]
    ring
  have hrightdist : |r + h - r| = h := by
    rw [show r + h - r = h by ring, abs_of_pos hh]
  have hmul : r*h ≤ h := by nlinarith only [mul_nonneg (sub_nonneg.mpr hr1.le) hh.le]
  have hincr := hinc (r+h) ⟨by linarith, hright⟩ (by rwa [hrightdist])
  have hincl := hinc (r*(1-h)) ⟨mul_nonneg hr0 (by linarith), hleft.trans hr1.le⟩
    (by rw [hleftdist]; exact hmul.trans_lt hhδ)
  rw [hleftdist] at hincl
  rw [hrightdist] at hincr
  have ht : f (r+h) - f (r*(1-h)) ≤ 2*C*h := by
    have h1 := (abs_le.mp hincr).2
    have h2 := (abs_le.mp hincl).1
    dsimp [C]
    nlinarith only [h1, h2, mul_le_mul_of_nonneg_left hmul (by positivity : 0 ≤ |y| + 1)]
  have hgap := (scaled_tail_le_increment hf hd hr hh hh1 hright).trans ht
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have hf' := (div_le_iff₀ hdp).mp hgap
  linarith only [hf']

private lemma derivative_band_error {f : ℝ → ℝ} {x y : ℝ}
    (hd : HasDerivWithinAt f y (Icc 0 1) x) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      |u - x| < δ → |v - x| < δ →
      |f v - f u - y * (v - u)| ≤ ε * (|u - x| + |v - x|) := by
  obtain ⟨δ, hδ, hloc⟩ := Metric.mem_nhdsWithin_iff.mp (hd.isLittleO.def hε)
  have herror (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) (hzδ : |z - x| < δ) :
      |f z - f x - (z - x) * y| ≤ ε * |z - x| := by
    have hb : z ∈ Metric.ball x δ := by
      simpa only [Metric.mem_ball, Real.dist_eq] using hzδ
    have h := hloc ⟨hb, hz⟩
    change ‖f z - f x - (z - x) • y‖ ≤ ε * ‖z - x‖ at h
    simpa only [Real.norm_eq_abs, smul_eq_mul] using h
  refine ⟨δ, hδ, fun u hu v hv huδ hvδ => ?_⟩
  calc
    _ = |(f v - f x - (v - x) * y) - (f u - f x - (u - x) * y)| := by
      congr 1
      ring
    _ ≤ |f v - f x - (v - x) * y| + |f u - f x - (u - x) * y| :=
      abs_sub _ _
    _ ≤ _ := by
      rw [mul_add, add_comm (ε * |u - x|)]
      exact add_le_add (herror v hv hvδ) (herror u hu huδ)

private lemma nearby_ratio_bound {f : ℝ → ℝ} (hf : Erdos50.IsDistributionOfPhiRatio f)
    {x y : ℝ} (hd : HasDerivWithinAt f y (Icc 0 1) x) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ d : ℕ, 0 < d → ∀ r h : ℝ, r = (d.totient : ℝ) / d →
      0 < h → h ≤ 1 → r + h ≤ 1 → |r - x| + h < δ →
      (1 - f (1 - h)) / d ≤ y * ((1 + r) * h) + 2 * ε * (|r - x| + h) := by
  obtain ⟨δ, hδ, he⟩ := derivative_band_error hd hε
  refine ⟨δ, hδ, fun d hdpos r h hr hh hh1 hrh hnear => ?_⟩
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r ≤ 1 := by linarith
  have hrmul : 0 ≤ r * h := mul_nonneg hr0 hh.le
  have hsmall : r * h ≤ h := by nlinarith only [mul_nonneg (sub_nonneg.mpr hr1) hh.le]
  have hu : r * (1 - h) ∈ Icc (0 : ℝ) 1 := by
    exact ⟨mul_nonneg hr0 (by linarith), by nlinarith only [hr1, hrmul]⟩
  have hv : r + h ∈ Icc (0 : ℝ) 1 := ⟨by linarith, hrh⟩
  have hud : |r * (1 - h) - x| ≤ |r - x| + h := by
    rw [show r * (1 - h) - x = (r - x) - r * h by ring]
    calc
      _ ≤ |r - x| + |r * h| := abs_sub _ _
      _ ≤ _ := by rw [abs_of_nonneg hrmul]; linarith
  have hvd : |r + h - x| ≤ |r - x| + h := by
    rw [show r + h - x = (r - x) + h by ring]
    simpa [abs_of_pos hh] using abs_add_le (r - x) h
  have ha := he _ hu _ hv (hud.trans_lt hnear) (hvd.trans_lt hnear)
  have hbound := le_trans (le_abs_self _) ha
  have hwidth : r + h - r * (1 - h) = (1 + r) * h := by ring
  rw [hwidth] at hbound
  have hgap := scaled_tail_le_increment hf hdpos hr hh hh1 hrh
  nlinarith only [hgap, hbound, mul_le_mul_of_nonneg_left hud hε.le,
    mul_le_mul_of_nonneg_left hvd hε.le]

end Erdos50Proof

/-- Irrational interior points (all totient ratios are rational, so these are never ratios). -/
def H1 : Prop :=
  ∀ f : ℝ → ℝ, (∀ c ∈ Set.Icc (0 : ℝ) 1, {n : ℕ | (Nat.totient n : ℝ) < c * n}.HasDensity (f c)) →
    ∀ x ∈ Set.Ioo (0 : ℝ) 1, (¬∃ d : ℕ, 0 < d ∧ x = (d.totient : ℝ) / d) → Irrational x →
      ¬∃ y > 0, HasDerivWithinAt f y (Set.Icc 0 1) x

/-- Rational interior points that are not of the form phi(d)/d. -/
def H2 : Prop :=
  ∀ f : ℝ → ℝ, (∀ c ∈ Set.Icc (0 : ℝ) 1, {n : ℕ | (Nat.totient n : ℝ) < c * n}.HasDensity (f c)) →
    ∀ x ∈ Set.Ioo (0 : ℝ) 1, (¬∃ d : ℕ, 0 < d ∧ x = (d.totient : ℝ) / d) → ¬ Irrational x →
      ¬∃ y > 0, HasDerivWithinAt f y (Set.Icc 0 1) x

theorem main : H1 → H2 → type_of% @Erdos50.erdos_50 := by
  intro h1 h2 f hf
  rintro ⟨x, hx, y, hy, hd⟩
  by_cases hx0 : x = 0
  · subst x
    exact (not_lt_of_ge (Erdos50Proof.derivative_at_zero_nonpos hf hd)) hy
  · by_cases hx1 : x = 1
    · subst x
      exact Erdos50Proof.no_derivative_at_one hf hd
    · have hxI : x ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0),
        lt_of_le_of_ne hx.2 hx1⟩
      by_cases hratio : ∃ d : ℕ, 0 < d ∧ x = (d.totient : ℝ) / d
      · obtain ⟨d, hdpos, hxeq⟩ := hratio
        exact Erdos50Proof.no_derivative_at_finite_ratio hf hdpos hxeq hxI.2 hd
      · by_cases hirr : Irrational x
        · exact h1 f hf x hxI hratio hirr ⟨y, hy, hd⟩
        · exact h2 f hf x hxI hratio hirr ⟨y, hy, hd⟩

end OMA.R_Erdos50_erdos_50_R1
