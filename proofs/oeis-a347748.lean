import OMAStatements.S_oeis_a347748

-- Problem: A347748: Number of positive integers with n digits that are equal both to the product of two integers ending with 4 and to that of two integers ending with 6
-- Upstream: formal-conjectures statements/oeis-a347748.lean:0 (declaration OMA.S_oeis_a347748.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.Proof_oeis_a347748

open OMA.S_oeis_a347748
open Filter Topology ArithmeticFunction vonMangoldt

private lemma log_div_rpow_le (n : ℕ) (hn : 1 ≤ n) {x : ℝ} (hx : 1 < x) :
    Real.log (n : ℝ) / (n : ℝ) ^ x ≤ (1 / (n : ℝ)) / (x - 1) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hx_pos : 0 < x - 1 := sub_pos.mpr hx
  have hpow : (n : ℝ) ^ x = (n : ℝ) * (n : ℝ) ^ (x - 1) := by
    conv_lhs => rw [show x = 1 + (x - 1) by ring]
    rw [Real.rpow_add hn_pos, Real.rpow_one]
  have hexp : (x - 1) * Real.log (n : ℝ) ≤ (n : ℝ) ^ (x - 1) := by
    rw [Real.rpow_def_of_pos hn_pos]
    have h1 := Real.add_one_le_exp (Real.log (n : ℝ) * (x - 1))
    linarith
  rw [hpow, div_div, div_le_div_iff₀ (mul_pos hn_pos (Real.rpow_pos_of_pos hn_pos _))
    (mul_pos hn_pos hx_pos)]
  nlinarith

private lemma not_summable_prime_recip_mod10 {a : ZMod 10} (ha : IsUnit a) :
    ¬ Summable (fun n : ℕ => if n.Prime ∧ (n : ZMod 10) = a then (1 : ℝ) / n else 0) := by
  intro hsum
  let f : ℕ → ℝ := fun n => if n.Prime ∧ (n : ZMod 10) = a then (1 : ℝ) / n else 0
  have hf_nonneg : ∀ n, 0 ≤ f n := by
    intro n
    dsimp [f]
    split_ifs <;> positivity
  have htot_pos : (0 : ℝ) < ((10 : ℕ).totient : ℝ)⁻¹ := by
    have : 0 < (10 : ℕ).totient := Nat.totient_pos.mpr (by decide)
    positivity
  let ε : ℝ := ((10 : ℕ).totient : ℝ)⁻¹ / 2
  have hε_pos : 0 < ε := by positivity
  have htend : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, f n) atTop (𝓝 (∑' n, f n)) :=
    hsum.hasSum.tendsto_sum_nat
  have hev : ∀ᶠ N in atTop, ∑' n, f n - ε < ∑ n ∈ Finset.range N, f n :=
    (tendsto_order.mp htend).1 _ (by linarith)
  obtain ⟨N, hN⟩ := hev.exists
  have htail_sum : Summable (fun n : ℕ => if N ≤ n then f n else 0) :=
    hsum.of_nonneg_of_le
      (fun n => by
        by_cases h : N ≤ n
        · simpa [h] using hf_nonneg n
        · simp [h])
      (fun n => by
        by_cases h : N ≤ n
        · simp [h, f]
        · simpa [h, f] using hf_nonneg n)
  have htail_lt : ∑' n : ℕ, (if N ≤ n then f n else 0) < ε := by
    have hsplit : (∑ n ∈ Finset.range N, f n) + (∑' n : ℕ, (if N ≤ n then f n else 0)) =
        ∑' n, f n := by
      have h1 : (∑ n ∈ Finset.range N, f n) = ∑' n : ℕ, (if n < N then f n else 0) := by
        rw [tsum_eq_sum (s := Finset.range N)]
        · refine Finset.sum_congr rfl fun n hn => by simp [Finset.mem_range.mp hn]
        · intro n hn
          have : ¬ n < N := by simpa [Finset.mem_range] using hn
          simp [this]
      rw [h1, ← Summable.tsum_add]
      · refine tsum_congr fun n => ?_
        by_cases hlt : n < N
        · have hge : ¬ N ≤ n := by omega
          simp [hlt, hge]
        · have hge : N ≤ n := by omega
          simp [hlt, hge]
      · exact summable_of_ne_finset_zero (s := Finset.range N) fun n hn => by
          have : ¬ n < N := by simpa [Finset.mem_range] using hn
          simp [this]
      · exact htail_sum
    linarith
  have hnonprime : Summable (fun n : ℕ => (if n.Prime then 0 else residueClass a n) / n) :=
    summable_residueClass_non_primes_div (a := a)
  have hfin : Summable (fun n : ℕ => if n < N then residueClass a n else 0) :=
    summable_of_ne_finset_zero (s := Finset.range N) fun n hn => by
      have : ¬ n < N := by simpa [Finset.mem_range] using hn
      simp [this]
  obtain ⟨C, hC⟩ := LSeries_residueClass_lower_bound (a := a) ha
  let M : ℝ := ∑' n : ℕ, (if n < N then residueClass a n else 0)
  let Cnp : ℝ := ∑' n : ℕ, (if n.Prime then 0 else residueClass a n) / n
  have hbound : ∀ {x : ℝ}, x ∈ Set.Ioc 1 2 →
      ((10 : ℕ).totient : ℝ)⁻¹ / (x - 1) - C ≤ M + Cnp + ε / (x - 1) := by
    intro x hx
    have hx1 : 1 < x := hx.1
    have hx_pos : 0 < x - 1 := sub_pos.mpr hx1
    have hsum_x : Summable (fun n : ℕ => residueClass a n / (n : ℝ) ^ x) :=
      LSeries.summable_real_of_abscissaOfAbsConv_lt <|
        (abscissaOfAbsConv_residueClass_le_one a).trans_lt <| mod_cast hx1
    have htail_div : Summable (fun n : ℕ => (if N ≤ n then f n else 0) / (x - 1)) :=
      htail_sum.div_const (x - 1)
    have hpw : ∀ n : ℕ, residueClass a n / (n : ℝ) ^ x ≤
        (if n < N then residueClass a n else 0) +
        (if n.Prime then 0 else residueClass a n) / n +
        (if N ≤ n then f n else 0) / (x - 1) := by
      intro n
      have h1 : 0 ≤ (if n < N then residueClass a n else 0) := by
        split_ifs
        · exact residueClass_nonneg a n
        · exact le_rfl
      have h2 : 0 ≤ (if n.Prime then 0 else residueClass a n) / (n : ℝ) := by
        split_ifs
        · simp
        · exact div_nonneg (residueClass_nonneg a n) (Nat.cast_nonneg n)
      have h3 : 0 ≤ (if N ≤ n then f n else 0) / (x - 1) := by
        refine div_nonneg ?_ hx_pos.le
        split_ifs
        · exact hf_nonneg n
        · exact le_rfl
      rcases Nat.eq_zero_or_pos n with rfl | hn_pos
      · have h0 : residueClass a 0 / ((0 : ℕ) : ℝ) ^ x = 0 := by simp [residueClass_apply_zero]
        rw [h0]
        linarith
      · by_cases hp : n.Prime
        · by_cases hlt : n < N
          · have hge1 : (1 : ℝ) ≤ (n : ℝ) ^ x := by
              have h1n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
              exact Real.one_le_rpow h1n (by linarith)
            have hle : residueClass a n / (n : ℝ) ^ x ≤ residueClass a n :=
              div_le_self (residueClass_nonneg a n) hge1
            have h1eq : (if n < N then residueClass a n else 0) = residueClass a n := if_pos hlt
            linarith
          · have hge : N ≤ n := by omega
            by_cases hmod : (n : ZMod 10) = a
            · have hrc : residueClass a n = Real.log (n : ℝ) := by
                simp only [residueClass, Set.indicator_apply, Set.mem_ofPred_eq, hmod, ite_true,
                  vonMangoldt_apply_prime hp]
              have hfn : f n = (1 : ℝ) / n := by
                simp [f, hp, hmod]
              have hle := log_div_rpow_le n (by omega) hx1
              have h3eq : (if N ≤ n then f n else 0) / (x - 1) = (1 / (n : ℝ)) / (x - 1) := by
                rw [if_pos hge, hfn]
              have hle' : residueClass a n / (n : ℝ) ^ x ≤ (1 / (n : ℝ)) / (x - 1) := by
                rw [hrc]; exact hle
              linarith
            · have hrc : residueClass a n = 0 := by
                simp only [residueClass, Set.indicator_apply, Set.mem_ofPred_eq, hmod, ite_false]
              have h0 : residueClass a n / (n : ℝ) ^ x = 0 := by rw [hrc, zero_div]
              rw [h0]
              linarith
        · have hle : residueClass a n / (n : ℝ) ^ x ≤ residueClass a n / (n : ℝ) := by
            refine div_le_div_of_nonneg_left (residueClass_nonneg a n) (mod_cast hn_pos) ?_
            conv_lhs => rw [← Real.rpow_one (n : ℝ)]
            exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn_pos) hx1.le
          have h2eq : (if n.Prime then 0 else residueClass a n) / (n : ℝ) =
              residueClass a n / (n : ℝ) := by rw [if_neg hp]
          linarith
    have htsum_le :
        (∑' n : ℕ, residueClass a n / (n : ℝ) ^ x) ≤
          M + Cnp + (∑' n : ℕ, (if N ≤ n then f n else 0)) / (x - 1) := by
      have hadd := (hfin.add hnonprime).add htail_div
      have h1 := Summable.tsum_le_tsum hpw hsum_x hadd
      rw [Summable.tsum_add (hfin.add hnonprime) htail_div,
        Summable.tsum_add hfin hnonprime, tsum_div_const] at h1
      exact h1
    have hdiv_le : (∑' n : ℕ, (if N ≤ n then f n else 0)) / (x - 1) ≤ ε / (x - 1) :=
      div_le_div_of_nonneg_right htail_lt.le hx_pos.le
    linarith [hC hx]
  have hkey : ∀ {x : ℝ}, x ∈ Set.Ioc 1 2 → ε ≤ (M + Cnp + C) * (x - 1) := by
    intro x hx
    have hx_pos : 0 < x - 1 := sub_pos.mpr hx.1
    have hb := hbound hx
    have hdiff : ((10 : ℕ).totient : ℝ)⁻¹ / (x - 1) - ε / (x - 1) = ε / (x - 1) := by
      dsimp [ε]; ring
    have : ε / (x - 1) ≤ M + Cnp + C := by linarith
    exact (div_le_iff₀ hx_pos).mp this
  let K : ℝ := max (M + Cnp + C) 1
  have hK : 0 < K := by positivity
  let δ : ℝ := min (ε / (2 * K)) 1
  have hδ_pos : 0 < δ := by positivity
  have hδ_le1 : δ ≤ 1 := min_le_right _ _
  have hmem : 1 + δ ∈ Set.Ioc (1 : ℝ) 2 := ⟨by linarith, by linarith⟩
  have h1 := hkey hmem
  have h2 : (M + Cnp + C) * δ ≤ K * δ := mul_le_mul_of_nonneg_right (le_max_left _ _) hδ_pos.le
  have h3 : K * δ ≤ ε / 2 := by
    have hle : δ ≤ ε / (2 * K) := min_le_left _ _
    calc K * δ ≤ K * (ε / (2 * K)) := mul_le_mul_of_nonneg_left hle hK.le
      _ = ε / 2 := by field_simp [hK.ne']
  linarith

private lemma exists_finset_primes_prod_lt (r : ℕ) (hr : r.Coprime 10) (hrlt : r < 10)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ p % 10 = r) ∧
      ∏ p ∈ S, (1 - (1 : ℝ) / p) < ε := by
  have ha : IsUnit (r : ZMod 10) := (ZMod.isUnit_iff_coprime r 10).mpr hr
  let f : ℕ → ℝ := fun n => if n.Prime ∧ (n : ZMod 10) = (r : ZMod 10) then (1 : ℝ) / n else 0
  have hf_nonneg : ∀ n, 0 ≤ f n := fun n => by dsimp [f]; split_ifs <;> positivity
  have hns : ¬ Summable f := not_summable_prime_recip_mod10 ha
  have htend : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, f n) atTop atTop :=
    not_summable_iff_tendsto_nat_atTop_of_nonneg hf_nonneg |>.mp hns
  obtain ⟨N, hN⟩ := (tendsto_atTop.mp htend (|Real.log ε| + 1)).exists
  let S : Finset ℕ := (Finset.range N).filter (fun n => n.Prime ∧ n % 10 = r)
  have hmod_iff : ∀ n : ℕ, (n : ZMod 10) = (r : ZMod 10) ↔ n % 10 = r := by
    intro n
    rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq, Nat.mod_eq_of_lt hrlt]
  have hsum_eq : ∑ p ∈ S, (1 : ℝ) / p = ∑ n ∈ Finset.range N, f n := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    dsimp [f]
    simp [hmod_iff n]
  refine ⟨S, fun p hp => (Finset.mem_filter.mp hp).2, ?_⟩
  have hprod_le : ∏ p ∈ S, (1 - (1 : ℝ) / p) ≤ Real.exp (-∑ p ∈ S, (1 : ℝ) / p) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_le_prod ?_ ?_
    · intro p hp
      have hp2 : 2 ≤ p := ((Finset.mem_filter.mp hp).2.1).two_le
      have h1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (show 1 ≤ p by omega)
      have hdiv : (1 : ℝ) / p ≤ 1 := div_le_one_of_le₀ h1 (by linarith)
      linarith
    · intro p _
      have := Real.add_one_le_exp (-(1 / (p : ℝ)))
      linarith
  have hlt : -∑ p ∈ S, (1 : ℝ) / p < Real.log ε := by
    rw [hsum_eq]
    have habs : -Real.log ε ≤ |Real.log ε| := neg_le_abs _
    linarith
  calc ∏ p ∈ S, (1 - (1 : ℝ) / p) ≤ Real.exp (-∑ p ∈ S, (1 : ℝ) / p) := hprod_le
    _ < Real.exp (Real.log ε) := Real.exp_lt_exp.mpr hlt
    _ = ε := Real.exp_log hε

private lemma card_mod20_avoid_primes (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p.Coprime 20) :
    ((Finset.range (20 * ∏ p ∈ S, p)).filter
      (fun r => r % 20 = 16 ∧ ∀ p ∈ S, ¬ p ∣ r)).card = ∏ p ∈ S, (p - 1) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    decide
  | @insert p S hpS ih =>
    have hp_prime : p.Prime := (hS p (Finset.mem_insert_self p S)).1
    have hp_cop20 : p.Coprime 20 := (hS p (Finset.mem_insert_self p S)).2
    have hS' : ∀ q ∈ S, q.Prime ∧ q.Coprime 20 :=
      fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have hih := ih hS'
    set M := ∏ q ∈ S, q with hM_def
    have hprod_eq : ∏ q ∈ insert p S, q = p * M := Finset.prod_insert hpS
    have hprod_sub : ∏ q ∈ insert p S, (q - 1) = (p - 1) * ∏ q ∈ S, (q - 1) :=
      Finset.prod_insert hpS
    have hp_copM : p.Coprime M := by
      rw [hM_def]
      refine Nat.Coprime.prod_right fun q hq => ?_
      have hq_prime : q.Prime := (hS' q hq).1
      have hne : p ≠ q := fun h => hpS (h ▸ hq)
      exact (Nat.coprime_primes hp_prime hq_prime).mpr hne
    have hp_cop20M : p.Coprime (20 * M) := hp_cop20.mul_right hp_copM
    have hM_pos : 0 < M := Finset.prod_pos fun q hq => (hS' q hq).1.pos
    have h20M_pos : 0 < 20 * M := by positivity
    let A : Finset ℕ := (Finset.range (20 * M)).filter (fun r => r % 20 = 16 ∧ ∀ q ∈ S, ¬ q ∣ r)
    let B : Finset ℕ := (Finset.range (20 * (p * M))).filter
      (fun r => r % 20 = 16 ∧ ∀ q ∈ insert p S, ¬ q ∣ r)
    rw [hprod_eq, hprod_sub, ← hih]
    change B.card = (p - 1) * A.card
    have hB_eq : B = A.biUnion (fun r =>
        ((Finset.range p).filter (fun k => ¬ p ∣ (r + k * (20 * M)))).image
          (fun k => r + k * (20 * M))) := by
      ext x
      simp only [B, A, Finset.mem_filter, Finset.mem_range, Finset.mem_biUnion,
        Finset.mem_image, Finset.mem_insert]
      constructor
      · rintro ⟨hx_lt, hx16, hx_ndvd⟩
        refine ⟨x % (20 * M), ⟨Nat.mod_lt x h20M_pos, ?_, ?_⟩, x / (20 * M), ⟨?_, ?_⟩, ?_⟩
        · have h20dvd : 20 ∣ 20 * M := dvd_mul_right 20 M
          rw [Nat.mod_mod_of_dvd x h20dvd]
          exact hx16
        · intro q hq
          have hqdvd : q ∣ 20 * M := dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hq) 20
          intro hqmod
          have : q ∣ x := (Nat.dvd_mod_iff hqdvd).mp hqmod
          exact hx_ndvd q (Or.inr hq) this
        · rw [Nat.div_lt_iff_lt_mul h20M_pos]
          linarith
        · have hrec : x % (20 * M) + x / (20 * M) * (20 * M) = x := by
            rw [mul_comm (x / (20 * M)), Nat.mod_add_div]
          rw [hrec]
          exact hx_ndvd p (Or.inl rfl)
        · rw [mul_comm (x / (20 * M)), Nat.mod_add_div]
      · rintro ⟨r, ⟨hr_lt, hr16, hr_ndvd⟩, k, ⟨hk_lt, hk_ndvd⟩, rfl⟩
        refine ⟨?_, ?_, ?_⟩
        · have hk1 : k + 1 ≤ p := hk_lt
          calc r + k * (20 * M) < 20 * M + k * (20 * M) := by omega
            _ = (k + 1) * (20 * M) := by ring
            _ ≤ p * (20 * M) := Nat.mul_le_mul_right _ hk1
            _ = 20 * (p * M) := by ring
        · have : (r + k * (20 * M)) % 20 = r % 20 := by
            rw [show k * (20 * M) = 20 * (k * M) by ring, Nat.add_mul_mod_self_left]
          rw [this, hr16]
        · rintro q (rfl | hq)
          · exact hk_ndvd
          · have hqdvd : q ∣ 20 * M := dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hq) 20
            intro hdvd
            have : q ∣ r := by
              have hkm : q ∣ k * (20 * M) := dvd_mul_of_dvd_right hqdvd k
              exact (Nat.dvd_add_left hkm).mp hdvd
            exact hr_ndvd q hq this
    rw [hB_eq, Finset.card_biUnion]
    · have hconst : ∀ r ∈ A,
          (((Finset.range p).filter (fun k => ¬ p ∣ (r + k * (20 * M)))).image
            (fun k => r + k * (20 * M))).card = p - 1 := by
        intro r _
        rw [Finset.card_image_of_injective]
        · let g : ℕ → ℕ := fun k => (r + k * (20 * M)) % p
          have hginj : Set.InjOn g (Finset.range p : Set ℕ) := by
            intro k₁ hk₁ k₂ hk₂ heq
            have hk1' : k₁ < p := Finset.mem_range.mp hk₁
            have hk2' : k₂ < p := Finset.mem_range.mp hk₂
            have hmod : (r + k₁ * (20 * M)) ≡ (r + k₂ * (20 * M)) [MOD p] := heq
            have hmod2 : k₁ * (20 * M) ≡ k₂ * (20 * M) [MOD p] :=
              Nat.ModEq.add_left_cancel' r hmod
            have hmod3 : k₁ ≡ k₂ [MOD p] :=
              Nat.ModEq.cancel_right_of_coprime hp_cop20M hmod2
            rw [Nat.ModEq, Nat.mod_eq_of_lt hk1', Nat.mod_eq_of_lt hk2'] at hmod3
            exact hmod3
          have hgimg : (Finset.range p).image g = Finset.range p := by
            refine Finset.eq_of_subset_of_card_le ?_ ?_
            · intro y hy
              obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hy
              exact Finset.mem_range.mpr (Nat.mod_lt _ hp_prime.pos)
            · rw [Finset.card_image_of_injOn hginj]
          have hfilt_eq :
              ((Finset.range p).filter (fun k => ¬ p ∣ (r + k * (20 * M)))).image g =
                (Finset.range p).erase 0 := by
            ext y
            simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
            constructor
            · rintro ⟨k, ⟨hk, hndvd⟩, rfl⟩
              refine ⟨?_, Nat.mod_lt _ hp_prime.pos⟩
              intro h0
              exact hndvd (Nat.dvd_of_mod_eq_zero h0)
            · rintro ⟨hy0, hylt⟩
              have hymem : y ∈ (Finset.range p).image g := by
                rw [hgimg]; exact Finset.mem_range.mpr hylt
              obtain ⟨k, hk, hgk⟩ := Finset.mem_image.mp hymem
              refine ⟨k, ⟨Finset.mem_range.mp hk, ?_⟩, hgk⟩
              intro hdvd
              have : g k = 0 := Nat.mod_eq_zero_of_dvd hdvd
              omega
          have hcard_img :
              (((Finset.range p).filter (fun k => ¬ p ∣ (r + k * (20 * M)))).image g).card =
                ((Finset.range p).filter (fun k => ¬ p ∣ (r + k * (20 * M)))).card :=
            Finset.card_image_of_injOn (hginj.mono (by intro k hk; exact (Finset.mem_filter.mp hk).1))
          rw [← hcard_img, hfilt_eq, Finset.card_erase_of_mem (Finset.mem_range.mpr hp_prime.pos),
            Finset.card_range]
        · intro k₁ k₂ h
          exact Nat.eq_of_mul_eq_mul_right h20M_pos (Nat.add_left_cancel h)
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, mul_comm]
    · intro r₁ hr₁ r₂ hr₂ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro x hx₁ hx₂
      obtain ⟨k₁, _, rfl⟩ := Finset.mem_image.mp hx₁
      obtain ⟨k₂, _, heq⟩ := Finset.mem_image.mp hx₂
      have hr1_lt : r₁ < 20 * M := Finset.mem_range.mp (Finset.mem_filter.mp hr₁).1
      have hr2_lt : r₂ < 20 * M := Finset.mem_range.mp (Finset.mem_filter.mp hr₂).1
      have hmod1 : (r₁ + k₁ * (20 * M)) % (20 * M) = r₁ := by
        rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr1_lt]
      have hmod2 : (r₂ + k₂ * (20 * M)) % (20 * M) = r₂ := by
        rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr2_lt]
      rw [← heq] at hmod1
      exact hne (hmod1.symm.trans hmod2)

private lemma card_Ico_mod20_avoid_primes (a : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ p.Coprime 20) :
    ((Finset.Ico a (a + 20 * ∏ p ∈ S, p)).filter
      (fun m => m % 20 = 16 ∧ ∀ p ∈ S, ¬ p ∣ m)).card = ∏ p ∈ S, (p - 1) := by
  set M := ∏ p ∈ S, p
  have hM_pos : 0 < M := Finset.prod_pos fun p hp => (hS p hp).1.pos
  have h20M_pos : 0 < 20 * M := by positivity
  rw [← card_mod20_avoid_primes S hS]
  refine Finset.card_bij (fun m _ => m % (20 * M)) ?_ ?_ ?_
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range] at hm ⊢
    refine ⟨Nat.mod_lt m h20M_pos, ?_, ?_⟩
    · rw [Nat.mod_mod_of_dvd m (dvd_mul_right 20 M)]
      exact hm.2.1
    · intro p hp hpmod
      have hpdvd : p ∣ 20 * M := dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hp) 20
      exact hm.2.2 p hp ((Nat.dvd_mod_iff hpdvd).mp hpmod)
  · intro m₁ hm₁ m₂ hm₂ heq
    have h1 := Finset.mem_Ico.mp (Finset.mem_filter.mp hm₁).1
    have h2 := Finset.mem_Ico.mp (Finset.mem_filter.mp hm₂).1
    have hq1 : m₁ = 20 * M * (m₁ / (20 * M)) + m₁ % (20 * M) := (Nat.div_add_mod m₁ (20 * M)).symm
    have hq2 : m₂ = 20 * M * (m₂ / (20 * M)) + m₂ % (20 * M) := (Nat.div_add_mod m₂ (20 * M)).symm
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hqle : m₁ / (20 * M) + 1 ≤ m₂ / (20 * M) := by
        have hmono : m₁ / (20 * M) ≤ m₂ / (20 * M) := Nat.div_le_div_right hlt.le
        by_contra hnot
        have hqeq : m₁ / (20 * M) = m₂ / (20 * M) := by omega
        rw [hqeq, heq] at hq1
        exact hne (hq1.trans hq2.symm)
      have hdiff : m₁ + 20 * M ≤ m₂ := by nlinarith
      omega
    · have hqle : m₂ / (20 * M) + 1 ≤ m₁ / (20 * M) := by
        have hmono : m₂ / (20 * M) ≤ m₁ / (20 * M) := Nat.div_le_div_right hgt.le
        by_contra hnot
        have hqeq : m₂ / (20 * M) = m₁ / (20 * M) := by omega
        rw [hqeq, ← heq] at hq2
        exact hne (hq1.trans hq2.symm)
      have hdiff : m₂ + 20 * M ≤ m₁ := by nlinarith
      omega
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr
    let b := a % (20 * M)
    let m := if b ≤ r then a + (r - b) else a + (20 * M + r - b)
    have hb_lt : b < 20 * M := Nat.mod_lt a h20M_pos
    have hm_in : m ∈ Finset.Ico a (a + 20 * M) := by
      simp only [Finset.mem_Ico, m]
      split_ifs <;> omega
    have hm_mod : m % (20 * M) = r := by
      have ha_eq : a = (a / (20 * M)) * (20 * M) + b := by
        rw [mul_comm, Nat.div_add_mod]
      dsimp [m]
      split_ifs with hbr
      · have : a + (r - b) = r + (a / (20 * M)) * (20 * M) := by omega
        rw [this, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr.1]
      · have : a + (20 * M + r - b) = r + (a / (20 * M) + 1) * (20 * M) := by
          have : (a / (20 * M) + 1) * (20 * M) = (a / (20 * M)) * (20 * M) + 20 * M := by ring
          omega
        rw [this, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr.1]
    refine ⟨m, ?_, hm_mod⟩
    simp only [Finset.mem_filter]
    refine ⟨hm_in, ?_, ?_⟩
    · rw [← Nat.mod_mod_of_dvd m (dvd_mul_right 20 M), hm_mod]
      exact hr.2.1
    · intro p hp hdvd
      have hpdvd : p ∣ 20 * M := dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hp) 20
      have : p ∣ r := by rw [← hm_mod]; exact (Nat.dvd_mod_iff hpdvd).mpr hdvd
      exact hr.2.2 p hp this

private lemma card_Ico_mod20_sixteen (n : ℕ) (hn : 3 ≤ n) :
    ((Finset.Ico (10 ^ (n - 1)) (10 ^ n)).filter (fun m => m % 20 = 16)).card =
      45 * 10 ^ (n - 3) := by
  have hlen : 10 ^ n = 10 ^ (n - 1) + (45 * 10 ^ (n - 3)) * 20 := by
    have h1 : 10 ^ (n - 1) = 100 * 10 ^ (n - 3) := by
      conv_lhs => rw [show n - 1 = (n - 3) + 2 by omega]
      rw [pow_add]
      ring
    have h2 : 10 ^ n = 10 * 10 ^ (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega]
      rw [pow_succ']
    linarith
  let blocks : ℕ → Finset ℕ := fun j =>
    (Finset.Ico (10 ^ (n - 1) + j * 20) (10 ^ (n - 1) + (j + 1) * 20)).filter
      (fun m => m % 20 = 16)
  have heq :
      (Finset.Ico (10 ^ (n - 1)) (10 ^ n)).filter (fun m => m % 20 = 16) =
        (Finset.range (45 * 10 ^ (n - 3))).biUnion blocks := by
    ext m
    simp only [blocks, Finset.mem_filter, Finset.mem_Ico, Finset.mem_biUnion, Finset.mem_range]
    constructor
    · rintro ⟨⟨hlo, hhi⟩, h16⟩
      refine ⟨(m - 10 ^ (n - 1)) / 20, ?_, ⟨?_, ?_⟩, h16⟩
      · rw [Nat.div_lt_iff_lt_mul (by norm_num)]
        omega
      · omega
      · omega
    · rintro ⟨j, hj, ⟨hlo, hhi⟩, h16⟩
      refine ⟨⟨by omega, ?_⟩, h16⟩
      have : j + 1 ≤ 45 * 10 ^ (n - 3) := hj
      have : (j + 1) * 20 ≤ (45 * 10 ^ (n - 3)) * 20 := Nat.mul_le_mul_right 20 this
      omega
  rw [heq, Finset.card_biUnion]
  · have h1 : ∀ j ∈ Finset.range (45 * 10 ^ (n - 3)), (blocks j).card = 1 := by
      intro j _
      have hspec := card_Ico_mod20_avoid_primes (10 ^ (n - 1) + j * 20) ∅ (by simp)
      simp only [Finset.prod_empty, mul_one, Finset.notMem_empty, IsEmpty.forall_iff,
        implies_true, and_true] at hspec
      have hhi : 10 ^ (n - 1) + j * 20 + 20 = 10 ^ (n - 1) + (j + 1) * 20 := by ring
      rw [hhi] at hspec
      exact hspec
    rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_range]
  · intro i _ j _ hij
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro m hmi hmj
    have hi := Finset.mem_Ico.mp (Finset.mem_filter.mp hmi).1
    have hj := Finset.mem_Ico.mp (Finset.mem_filter.mp hmj).1
    rcases lt_or_gt_of_ne hij with hlt | hgt <;> omega

private lemma bad_count_le (n : ℕ) (hn : 3 ≤ n) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ p.Coprime 20) :
    (((Finset.Ico (10 ^ (n - 1)) (10 ^ n)).filter
      (fun m => m % 20 = 16 ∧ ∀ p ∈ S, ¬ p ∣ m)).card : ℝ) ≤
      (45 * (10 : ℝ) ^ (n - 3)) * (∏ p ∈ S, (1 - (1 : ℝ) / p)) + (∏ p ∈ S, (p : ℝ)) := by
  set M := ∏ p ∈ S, p
  have hM_pos : 0 < M := Finset.prod_pos fun p hp => (hS p hp).1.pos
  have h20M_pos : 0 < 20 * M := by positivity
  let K := (45 * 10 ^ (n - 3)) / M + 1
  have hcov :
      (Finset.Ico (10 ^ (n - 1)) (10 ^ n)).filter (fun m => m % 20 = 16 ∧ ∀ p ∈ S, ¬ p ∣ m) ⊆
        (Finset.range K).biUnion (fun j =>
          (Finset.Ico (10 ^ (n - 1) + j * (20 * M))
            (10 ^ (n - 1) + (j + 1) * (20 * M))).filter
            (fun m => m % 20 = 16 ∧ ∀ p ∈ S, ¬ p ∣ m)) := by
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_Ico] at hm
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter, Finset.mem_Ico]
    have hlen : 10 ^ n - 10 ^ (n - 1) = (45 * 10 ^ (n - 3)) * 20 := by
      have h1 : 10 ^ (n - 1) = 100 * 10 ^ (n - 3) := by
        conv_lhs => rw [show n - 1 = (n - 3) + 2 by omega]
        rw [pow_add]
        ring
      have h2 : 10 ^ n = 10 * 10 ^ (n - 1) := by
        conv_lhs => rw [show n = (n - 1) + 1 by omega]
        rw [pow_succ']
      omega
    have hKge : 10 ^ n ≤ 10 ^ (n - 1) + K * (20 * M) := by
      have hdiv : 45 * 10 ^ (n - 3) < K * M := by
        dsimp [K]
        have := Nat.lt_div_mul_add (a := 45 * 10 ^ (n - 3)) hM_pos
        linarith
      have : (45 * 10 ^ (n - 3)) * 20 < K * (20 * M) := by nlinarith
      omega
    set j := (m - 10 ^ (n - 1)) / (20 * M) with hj_def
    refine ⟨j, ?_, ⟨?_, ?_⟩, hm.2⟩
    · rw [hj_def, Nat.div_lt_iff_lt_mul h20M_pos]
      omega
    · have h1 := Nat.div_mul_le_self (m - 10 ^ (n - 1)) (20 * M)
      rw [← hj_def] at h1
      omega
    · have h1 := Nat.lt_div_mul_add (a := m - 10 ^ (n - 1)) h20M_pos
      rw [← hj_def] at h1
      have h2 : (j + 1) * (20 * M) = j * (20 * M) + 20 * M := by ring
      omega
  have hcard_nat :
      ((Finset.Ico (10 ^ (n - 1)) (10 ^ n)).filter
        (fun m => m % 20 = 16 ∧ ∀ p ∈ S, ¬ p ∣ m)).card ≤ K * ∏ p ∈ S, (p - 1) := by
    calc _ ≤ _ := Finset.card_le_card hcov
      _ ≤ ∑ j ∈ Finset.range K,
            ((Finset.Ico (10 ^ (n - 1) + j * (20 * M))
              (10 ^ (n - 1) + (j + 1) * (20 * M))).filter
              (fun m => m % 20 = 16 ∧ ∀ p ∈ S, ¬ p ∣ m)).card := Finset.card_biUnion_le
      _ = ∑ _j ∈ Finset.range K, ∏ p ∈ S, (p - 1) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have hhi : 10 ^ (n - 1) + (j + 1) * (20 * M) =
            10 ^ (n - 1) + j * (20 * M) + 20 * M := by ring
        rw [hhi]
        exact card_Ico_mod20_avoid_primes (10 ^ (n - 1) + j * (20 * M)) S hS
      _ = K * ∏ p ∈ S, (p - 1) := by
        rw [Finset.sum_const, smul_eq_mul, Finset.card_range]
  have hM_cast : (M : ℝ) = ∏ p ∈ S, (p : ℝ) := by simp [M]
  have hprod_rat :
      ((∏ p ∈ S, (p - 1) : ℕ) : ℝ) = (M : ℝ) * ∏ p ∈ S, (1 - (1 : ℝ) / p) := by
    rw [hM_cast, ← Finset.prod_mul_distrib, Nat.cast_prod]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp1 : 1 ≤ p := (hS p hp).1.one_le
    have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hS p hp).1.ne_zero
    rw [Nat.cast_sub hp1, Nat.cast_one]
    field_simp [hp0]
  have hprod_le_M : ((∏ p ∈ S, (p - 1) : ℕ) : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast Finset.prod_le_prod' fun p _ => Nat.sub_le p 1
  have hK_le : ((K : ℕ) : ℝ) ≤ (45 * (10 : ℝ) ^ (n - 3)) / (M : ℝ) + 1 := by
    dsimp [K]
    push_cast
    have h1 : (((45 * 10 ^ (n - 3)) / M : ℕ) : ℝ) ≤ (45 * (10 : ℝ) ^ (n - 3)) / (M : ℝ) := by
      have hM_pos' : (0 : ℝ) < M := by exact_mod_cast hM_pos
      rw [le_div_iff₀ hM_pos']
      exact_mod_cast Nat.div_mul_le_self (45 * 10 ^ (n - 3)) M
    linarith
  have hM_pos' : (0 : ℝ) < M := by exact_mod_cast hM_pos
  calc
    (((Finset.Ico (10 ^ (n - 1)) (10 ^ n)).filter
        (fun m => m % 20 = 16 ∧ ∀ p ∈ S, ¬ p ∣ m)).card : ℝ)
        ≤ (K : ℝ) * ((∏ p ∈ S, (p - 1) : ℕ) : ℝ) := by exact_mod_cast hcard_nat
    _ ≤ ((45 * (10 : ℝ) ^ (n - 3)) / (M : ℝ) + 1) * ((∏ p ∈ S, (p - 1) : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hK_le (Nat.cast_nonneg _)
    _ = (45 * (10 : ℝ) ^ (n - 3)) / (M : ℝ) * ((M : ℝ) * ∏ p ∈ S, (1 - (1 : ℝ) / p)) +
          ((∏ p ∈ S, (p - 1) : ℕ) : ℝ) := by
        rw [add_mul, one_mul, hprod_rat]
    _ = (45 * (10 : ℝ) ^ (n - 3)) * (∏ p ∈ S, (1 - (1 : ℝ) / p)) +
          ((∏ p ∈ S, (p - 1) : ℕ) : ℝ) := by
        field_simp [hM_pos'.ne']
    _ ≤ (45 * (10 : ℝ) ^ (n - 3)) * (∏ p ∈ S, (1 - (1 : ℝ) / p)) + (∏ p ∈ S, (p : ℝ)) := by
        rw [← hM_cast]; linarith

private lemma mod20_sixteen_of_hasPair4 {m : ℕ} (h : hasPairEndingIn m 4 = true) : m % 20 = 16 := by
  unfold hasPairEndingIn at h
  rw [decide_eq_true_eq] at h
  obtain ⟨a, ha⟩ := h
  rw [Finset.mem_filter, Nat.mem_divisors] at ha
  have hmul : a * (m / a) = m := Nat.mul_div_cancel' ha.1.1
  have hmod10 : m % 10 = 6 := by
    have : (a * (m / a)) % 10 = ((a % 10) * ((m / a) % 10)) % 10 := Nat.mul_mod _ _ _
    rw [hmul, ha.2.1, ha.2.2] at this
    exact this
  have hmod4 : m % 4 = 0 := by
    have ha2 : 2 ∣ a := by omega
    have hb2 : 2 ∣ (m / a) := by omega
    obtain ⟨u, hu⟩ := ha2
    obtain ⟨v, hv⟩ := hb2
    have : m = 4 * (u * v) := by rw [← hmul, hv, hu]; ring
    omega
  omega

private lemma hasPair4_of_dvd {m p : ℕ} (hm0 : m ≠ 0) (hm20 : m % 20 = 16)
    (hp7 : p % 10 = 7) (hdvd : p ∣ m) : hasPairEndingIn m 4 = true := by
  have h4m : 4 ∣ m := by omega
  have hcop : Nat.Coprime 4 p := by
    rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_rec]
    have : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases this with h | h <;> rw [h] <;> decide
  have h4pm : 4 * p ∣ m := hcop.mul_dvd_of_dvd_of_dvd h4m hdvd
  obtain ⟨k, rfl⟩ := h4pm
  unfold hasPairEndingIn
  rw [decide_eq_true_eq]
  have hdvd2p : 2 * p ∣ 4 * p * k := ⟨2 * k, by ring⟩
  refine ⟨2 * p, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdvd2p, hm0⟩, by omega, ?_⟩⟩
  have hquot : 4 * p * k / (2 * p) = 2 * k := by
    have h2p_pos : 0 < 2 * p := by omega
    rw [show 4 * p * k = (2 * p) * (2 * k) by ring, Nat.mul_div_right _ h2p_pos]
  rw [hquot]
  have hmod : ((2 * p) * (2 * k)) % 10 = (((2 * p) % 10) * ((2 * k) % 10)) % 10 := Nat.mul_mod _ _ _
  have hm10 : ((2 * p) * (2 * k)) % 10 = 6 := by
    rw [show (2 * p) * (2 * k) = 4 * p * k by ring]
    omega
  have h2p10 : (2 * p) % 10 = 4 := by omega
  rw [hm10, h2p10] at hmod
  omega

private lemma hasPair6_of_dvd {m q : ℕ} (hm0 : m ≠ 0) (hm20 : m % 20 = 16)
    (hq3 : q % 10 = 3) (hdvd : q ∣ m) : hasPairEndingIn m 6 = true := by
  have h4m : 4 ∣ m := by omega
  have hcop : Nat.Coprime 4 q := by
    rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_rec]
    have : q % 4 = 1 ∨ q % 4 = 3 := by omega
    rcases this with h | h <;> rw [h] <;> decide
  have h4qm : 4 * q ∣ m := hcop.mul_dvd_of_dvd_of_dvd h4m hdvd
  obtain ⟨k, rfl⟩ := h4qm
  unfold hasPairEndingIn
  rw [decide_eq_true_eq]
  have hdvd2q : 2 * q ∣ 4 * q * k := ⟨2 * k, by ring⟩
  refine ⟨2 * q, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdvd2q, hm0⟩, by omega, ?_⟩⟩
  have hquot : 4 * q * k / (2 * q) = 2 * k := by
    have h2q_pos : 0 < 2 * q := by omega
    rw [show 4 * q * k = (2 * q) * (2 * k) by ring, Nat.mul_div_right _ h2q_pos]
  rw [hquot]
  have hmod : ((2 * q) * (2 * k)) % 10 = (((2 * q) % 10) * ((2 * k) % 10)) % 10 := Nat.mul_mod _ _ _
  have hm10 : ((2 * q) * (2 * k)) % 10 = 6 := by
    rw [show (2 * q) * (2 * k) = 4 * q * k by ring]
    omega
  have h2q10 : (2 * q) % 10 = 6 := by omega
  rw [hm10, h2q10] at hmod
  omega

private lemma coprime_20_of_mod10_three_or_seven {p : ℕ} (h : p % 10 = 3 ∨ p % 10 = 7) :
    p.Coprime 20 := by
  rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, Nat.gcd_rec]
  have : p % 20 = 3 ∨ p % 20 = 13 ∨ p % 20 = 7 ∨ p % 20 = 17 := by omega
  rcases this with h1 | h1 | h1 | h1 <;> rw [h1] <;> decide

private lemma tendsto_scaled :
    Tendsto (fun n : ℕ => (term n : ℝ) / (45 * (10 : ℝ) ^ (n - 3))) atTop (𝓝 1) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨S3, hS3, hprod3⟩ := exists_finset_primes_prod_lt 3 (by decide) (by omega) (ε / 4) (by linarith)
  obtain ⟨S7, hS7, hprod7⟩ := exists_finset_primes_prod_lt 7 (by decide) (by omega) (ε / 4) (by linarith)
  have hS3' : ∀ p ∈ S3, p.Prime ∧ p.Coprime 20 := fun p hp =>
    ⟨(hS3 p hp).1, coprime_20_of_mod10_three_or_seven (Or.inl (hS3 p hp).2)⟩
  have hS7' : ∀ p ∈ S7, p.Prime ∧ p.Coprime 20 := fun p hp =>
    ⟨(hS7 p hp).1, coprime_20_of_mod10_three_or_seven (Or.inr (hS7 p hp).2)⟩
  let C : ℝ := (∏ p ∈ S3, (p : ℝ)) + (∏ p ∈ S7, (p : ℝ))
  have hC_nonneg : 0 ≤ C := by positivity
  have htend_pow : Tendsto (fun n : ℕ => (45 * (10 : ℝ) ^ (n - 3))) atTop atTop := by
    have h1 : Tendsto (fun k : ℕ => (10 : ℝ) ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    have h2 : Tendsto (fun n : ℕ => n - 3) atTop atTop :=
      tendsto_atTop_atTop.mpr fun b => ⟨b + 3, fun n hn => by omega⟩
    exact Tendsto.const_mul_atTop (by norm_num) (h1.comp h2)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (tendsto_atTop.mp htend_pow (2 * (C + 1) / ε))
  refine ⟨max N₀ 3, fun n hn => ?_⟩
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hn0 : N₀ ≤ n := le_trans (le_max_left _ _) hn
  let D : ℝ := 45 * (10 : ℝ) ^ (n - 3)
  have hD_pos : 0 < D := by positivity
  have hupper : (term n : ℝ) ≤ D := by
    have hsub :
        (Finset.Ico (10 ^ (n - 1)) (10 ^ n)).filter
          (fun m => hasPairEndingIn m 4 = true ∧ hasPairEndingIn m 6 = true) ⊆
        (Finset.Ico (10 ^ (n - 1)) (10 ^ n)).filter (fun m => m % 20 = 16) := by
      intro m hm
      rw [Finset.mem_filter] at hm ⊢
      exact ⟨hm.1, mod20_sixteen_of_hasPair4 hm.2.1⟩
    have hle := Finset.card_le_card hsub
    rw [card_Ico_mod20_sixteen n hn3] at hle
    dsimp [term, D]
    exact_mod_cast hle
  let All16 := (Finset.Ico (10 ^ (n - 1)) (10 ^ n)).filter (fun m => m % 20 = 16)
  let Good := (Finset.Ico (10 ^ (n - 1)) (10 ^ n)).filter
    (fun m => hasPairEndingIn m 4 = true ∧ hasPairEndingIn m 6 = true)
  let Bad3 := (Finset.Ico (10 ^ (n - 1)) (10 ^ n)).filter
    (fun m => m % 20 = 16 ∧ ∀ p ∈ S3, ¬ p ∣ m)
  let Bad7 := (Finset.Ico (10 ^ (n - 1)) (10 ^ n)).filter
    (fun m => m % 20 = 16 ∧ ∀ p ∈ S7, ¬ p ∣ m)
  have hcov : All16 ⊆ Good ∪ (Bad3 ∪ Bad7) := by
    intro m hm
    by_cases h3 : ∃ q ∈ S3, q ∣ m
    · by_cases h7 : ∃ p ∈ S7, p ∣ m
      · apply Finset.mem_union_left
        obtain ⟨q, hqS, hqm⟩ := h3
        obtain ⟨p, hpS, hpm⟩ := h7
        rw [Finset.mem_filter] at hm ⊢
        have hm0 : m ≠ 0 := by
          have := (Finset.mem_Ico.mp hm.1).1
          have : 0 < 10 ^ (n - 1) := by positivity
          omega
        exact ⟨hm.1, hasPair4_of_dvd hm0 hm.2 (hS7 p hpS).2 hpm,
          hasPair6_of_dvd hm0 hm.2 (hS3 q hqS).2 hqm⟩
      · apply Finset.mem_union_right
        apply Finset.mem_union_right
        rw [Finset.mem_filter] at hm ⊢
        push Not at h7
        exact ⟨hm.1, hm.2, h7⟩
    · apply Finset.mem_union_right
      apply Finset.mem_union_left
      rw [Finset.mem_filter] at hm ⊢
      push Not at h3
      exact ⟨hm.1, hm.2, h3⟩
  have hcard_ineq : All16.card ≤ Good.card + Bad3.card + Bad7.card := by
    calc All16.card ≤ (Good ∪ (Bad3 ∪ Bad7)).card := Finset.card_le_card hcov
      _ ≤ Good.card + (Bad3 ∪ Bad7).card := Finset.card_union_le _ _
      _ ≤ Good.card + (Bad3.card + Bad7.card) := Nat.add_le_add_left (Finset.card_union_le _ _) _
      _ = Good.card + Bad3.card + Bad7.card := by omega
  have hAll16_card : (All16.card : ℝ) = D := by
    dsimp [All16, D]
    exact_mod_cast card_Ico_mod20_sixteen n hn3
  have hBad3 := bad_count_le n hn3 S3 hS3'
  have hBad7 := bad_count_le n hn3 S7 hS7'
  have hD_big : 2 * (C + 1) / ε ≤ D := hN₀ n hn0
  have hC_lt : C < (ε / 2) * D := by
    have hmul : 2 * (C + 1) ≤ D * ε := (div_le_iff₀ hε).mp hD_big
    linarith
  have hterm_ge : D - ε * D < (term n : ℝ) := by
    have hcast : (All16.card : ℝ) ≤ (term n : ℝ) + (Bad3.card : ℝ) + (Bad7.card : ℝ) := by
      exact_mod_cast hcard_ineq
    have hp3 : D * (∏ p ∈ S3, (1 - (1 : ℝ) / p)) < D * (ε / 4) :=
      mul_lt_mul_of_pos_left hprod3 hD_pos
    have hp7 : D * (∏ p ∈ S7, (1 - (1 : ℝ) / p)) < D * (ε / 4) :=
      mul_lt_mul_of_pos_left hprod7 hD_pos
    linarith
  rw [Real.dist_eq, abs_lt]
  constructor
  · have : 1 - ε < (term n : ℝ) / D := by
      rw [lt_div_iff₀ hD_pos]
      linarith
    linarith
  · have : (term n : ℝ) / D ≤ 1 := (div_le_one hD_pos).mpr hupper
    linarith

private lemma main_proof :
    Filter.Tendsto (fun n : ℕ => (term n : ℝ) / (term (n - 1) : ℝ))
      Filter.atTop (nhds 10) := by
  let g : ℕ → ℝ := fun n => (term n : ℝ) / (45 * (10 : ℝ) ^ (n - 3))
  have hg : Tendsto g atTop (𝓝 1) := tendsto_scaled
  have hsub : Tendsto (fun n : ℕ => n - 1) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b + 1, fun n hn => by omega⟩
  have hg1 : Tendsto (fun n : ℕ => g (n - 1)) atTop (𝓝 1) := hg.comp hsub
  have hquot : Tendsto (fun n : ℕ => 10 * (g n / g (n - 1))) atTop (𝓝 10) := by
    have h := (hg.div hg1 (by norm_num)).const_mul 10
    simpa using h
  have hev_pos : ∀ᶠ n : ℕ in atTop, 0 < g (n - 1) :=
    (tendsto_order.mp hg1).1 0 (by norm_num)
  have hev_eq : (fun n : ℕ => 10 * (g n / g (n - 1))) =ᶠ[atTop]
      (fun n : ℕ => (term n : ℝ) / (term (n - 1) : ℝ)) := by
    filter_upwards [hev_pos, eventually_ge_atTop 4] with n hgn hn4
    have hD1 : (45 * (10 : ℝ) ^ (n - 3)) ≠ 0 := by positivity
    have hD0 : (45 * (10 : ℝ) ^ (n - 1 - 3)) ≠ 0 := by positivity
    have ht1 : (term (n - 1) : ℝ) ≠ 0 := by
      intro h0
      have : g (n - 1) = 0 := by simp [g, h0]
      linarith
    have hpow : (45 * (10 : ℝ) ^ (n - 3)) = 10 * (45 * (10 : ℝ) ^ (n - 1 - 3)) := by
      have : n - 3 = (n - 1 - 3) + 1 := by omega
      rw [this, pow_succ']
      ring
    dsimp [g]
    rw [hpow]
    field_simp [hD0, ht1]
  exact hquot.congr' hev_eq

end OMA.Proof_oeis_a347748

theorem OMA.solution : type_of% @OMA.S_oeis_a347748.main :=
  OMA.Proof_oeis_a347748.main_proof
