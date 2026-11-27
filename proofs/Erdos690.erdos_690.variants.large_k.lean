import FormalConjectures.ErdosProblems.«690»

/-!
# Proof of Erdos690.erdos_690.variants.large_k

We prove that for all `k ≥ 21`, the natural density `d_k(p)` of integers whose `k`-th smallest
prime factor is `p` is not unimodal on the primes.
-/

open Filter Real Finset BigOperators
open scoped Topology

namespace Erdos690Proof

/-- The `r`-th prime (`p_0 = 2, p_1 = 3, ...`). -/
noncomputable def pNth (r : ℕ) : ℕ := Nat.nth Nat.Prime r

lemma pNth_prime (r : ℕ) : (pNth r).Prime :=
  Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime r

lemma pNth_strictMono : StrictMono pNth :=
  Nat.nth_strictMono Nat.infinite_setOfPred_prime

lemma two_le_pNth (r : ℕ) : 2 ≤ pNth r := (pNth_prime r).two_le

lemma pNth_pos (r : ℕ) : 0 < pNth r := (pNth_prime r).pos

lemma pNth_sub_one_pos (r : ℕ) : (0 : ℝ) < (pNth r : ℝ) - 1 := by
  have h : 2 ≤ pNth r := two_le_pNth r
  have hR : (2 : ℝ) ≤ (pNth r : ℝ) := by exact_mod_cast h
  linarith

/-- `x_j = 1 / (p_j - 1)`. -/
noncomputable def xTerm (j : ℕ) : ℝ := 1 / ((pNth j : ℝ) - 1)

lemma xTerm_pos (j : ℕ) : 0 < xTerm j := by
  unfold xTerm
  exact one_div_pos.mpr (pNth_sub_one_pos j)

lemma xTerm_nonneg (j : ℕ) : 0 ≤ xTerm j := (xTerm_pos j).le

lemma xTerm_antitone : Antitone xTerm := by
  intro i j hij
  unfold xTerm
  apply one_div_le_one_div_of_le (pNth_sub_one_pos i)
  have hle : pNth i ≤ pNth j := pNth_strictMono.monotone hij
  have hR : (pNth i : ℝ) ≤ (pNth j : ℝ) := by exact_mod_cast hle
  linarith

/-- Elementary symmetric polynomial `E_m(r)` in `x_0, ..., x_{r-1}`. -/
noncomputable def elemSym (m r : ℕ) : ℝ :=
  ∑ S ∈ (Finset.range r).powersetCard m, ∏ j ∈ S, xTerm j

/-- Partial sum `S(r) = ∑_{j < r} x_j`. -/
noncomputable def sumX (r : ℕ) : ℝ := ∑ j ∈ Finset.range r, xTerm j

lemma elemSym_zero (r : ℕ) : elemSym 0 r = 1 := by
  simp [elemSym]

lemma elemSym_nonneg (m r : ℕ) : 0 ≤ elemSym m r := by
  unfold elemSym
  refine Finset.sum_nonneg fun S _ => Finset.prod_nonneg fun j _ => xTerm_nonneg j

lemma elemSym_pos {m r : ℕ} (hmr : m ≤ r) : 0 < elemSym m r := by
  unfold elemSym
  have hmem : Finset.range m ∈ (Finset.range r).powersetCard m := by
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.range_mono hmr, Finset.card_range m⟩
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun S _ => Finset.prod_nonneg fun j _ => xTerm_nonneg j) hmem)
  exact Finset.prod_pos fun j _ => xTerm_pos j

lemma elemSym_succ (m r : ℕ) :
    elemSym (m + 1) (r + 1) = elemSym (m + 1) r + xTerm r * elemSym m r := by
  unfold elemSym
  rw [Finset.range_add_one, Finset.powersetCard_succ_insert (Finset.notMem_range_self)]
  rw [Finset.sum_union]
  · congr 1
    rw [Finset.sum_image]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun S hS => ?_
      rw [Finset.mem_powersetCard] at hS
      have hr : r ∉ S := fun h => Finset.notMem_range_self (hS.1 h)
      rw [Finset.prod_insert hr]
    · intro S₁ hS₁ S₂ hS₂ hEq
      rw [Finset.mem_coe, Finset.mem_powersetCard] at hS₁ hS₂
      have hr₁ : r ∉ S₁ := fun h => Finset.notMem_range_self (hS₁.1 h)
      have hr₂ : r ∉ S₂ := fun h => Finset.notMem_range_self (hS₂.1 h)
      exact (Finset.insert_erase_invOn.2.injOn (by simp [hr₁]) (by simp [hr₂])) hEq
  · rw [Finset.disjoint_left]
    intro S hS₁ hS₂
    rw [Finset.mem_powersetCard] at hS₁
    rw [Finset.mem_image] at hS₂
    rcases hS₂ with ⟨T, _, rfl⟩
    exact Finset.notMem_range_self (hS₁.1 (Finset.mem_insert_self r T))

/-- Exact density `d_k(p_r)`. -/
noncomputable def densK (k r : ℕ) : ℝ :=
  (1 / (pNth r : ℝ)) * (∏ j ∈ Finset.range r, (1 - 1 / (pNth j : ℝ))) * elemSym (k - 1) r

lemma prod_one_sub_inv_pos (r : ℕ) :
    0 < ∏ j ∈ Finset.range r, (1 - 1 / (pNth j : ℝ)) := by
  refine Finset.prod_pos fun j _ => ?_
  have hp : (2 : ℝ) ≤ (pNth j : ℝ) := by exact_mod_cast two_le_pNth j
  have h1 : 1 / (pNth j : ℝ) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  linarith

lemma densK_diff (k r : ℕ) (hk : 2 ≤ k) :
    densK k (r + 1) - densK k r =
      ((∏ j ∈ Finset.range r, (1 - 1 / (pNth j : ℝ))) / ((pNth r : ℝ) * (pNth (r + 1) : ℝ))) *
        (elemSym (k - 2) r - ((pNth (r + 1) : ℝ) - (pNth r : ℝ) + 1) * elemSym (k - 1) r) := by
  have hk1 : k - 1 = (k - 2) + 1 := by omega
  unfold densK
  rw [Finset.prod_range_succ, hk1, elemSym_succ]
  have hp0 : (pNth r : ℝ) ≠ 0 := by exact_mod_cast (pNth_pos r).ne'
  have hp1 : (pNth (r + 1) : ℝ) ≠ 0 := by exact_mod_cast (pNth_pos (r + 1)).ne'
  have hp0sub : (pNth r : ℝ) - 1 ≠ 0 := (pNth_sub_one_pos r).ne'
  unfold xTerm
  field_simp
  ring

lemma not_unimodal_of_descent_ascent {k : ℕ} (hk : 2 ≤ k) {d : ℕ → ℝ}
    (hd : ∀ r, d (pNth r) = densK k r) {a b : ℕ} (hab : a < b) (ha : k - 1 ≤ a)
    (hdesc : elemSym (k - 2) a / elemSym (k - 1) a < (pNth (a + 1) : ℝ) - (pNth a : ℝ) + 1)
    (hasc : (pNth (b + 1) : ℝ) - (pNth b : ℝ) + 1 < elemSym (k - 2) b / elemSym (k - 1) b) :
    ¬ Erdos690.IsUnimodalOnPrimes d := by
  intro ⟨m, hm, hinc, hdec⟩
  have hEa : 0 < elemSym (k - 1) a := elemSym_pos ha
  have hEb : 0 < elemSym (k - 1) b := elemSym_pos (by omega)
  have hda : d (pNth (a + 1)) < d (pNth a) := by
    rw [hd (a + 1), hd a, ← sub_neg, densK_diff k a hk]
    refine mul_neg_of_pos_of_neg ?_ ?_
    · refine div_pos (prod_one_sub_inv_pos a) ?_
      exact mul_pos (by exact_mod_cast pNth_pos a) (by exact_mod_cast pNth_pos (a + 1))
    · rw [div_lt_iff₀ hEa] at hdesc
      linarith
  have hdb : d (pNth b) < d (pNth (b + 1)) := by
    rw [hd (b + 1), hd b, ← sub_pos, densK_diff k b hk]
    refine mul_pos ?_ ?_
    · refine div_pos (prod_one_sub_inv_pos b) ?_
      exact mul_pos (by exact_mod_cast pNth_pos b) (by exact_mod_cast pNth_pos (b + 1))
    · rw [lt_div_iff₀ hEb] at hasc
      linarith
  by_cases hm_le : m ≤ pNth a
  · have hmpb : m ≤ pNth b := hm_le.trans (pNth_strictMono.monotone hab.le)
    have hpb : pNth b ≤ pNth (b + 1) := pNth_strictMono.monotone (Nat.le_succ b)
    have := hdec (pNth b) (pNth (b + 1)) (pNth_prime b) (pNth_prime (b + 1)) hmpb hpb
    linarith
  · push Not at hm_le
    have ha1_le_m : pNth (a + 1) ≤ m := by
      have hm_idx : ∃ j, pNth j = m :=
        ⟨Nat.count Nat.Prime m, Nat.nth_count hm⟩
      rcases hm_idx with ⟨j, rfl⟩
      have haj : a < j := pNth_strictMono.lt_iff_lt.mp hm_le
      exact pNth_strictMono.monotone (by omega)
    have hpa : pNth a ≤ pNth (a + 1) := pNth_strictMono.monotone (Nat.le_succ a)
    have := hinc (pNth a) (pNth (a + 1)) (pNth_prime a) (pNth_prime (a + 1)) hpa ha1_le_m
    linarith

/-- Counting periodic sets for natural density. -/
lemma hasDensity_periodic {S : Set ℕ} {M : ℕ} (hM : 0 < M) (A : Finset ℕ)
    (hAM : A ⊆ Finset.range M) (h0 : 0 ∉ S)
    (hper : ∀ n, 0 < n → (n ∈ S ↔ n % M ∈ A)) :
    S.HasDensity ((A.card : ℝ) / (M : ℝ)) := by
  rw [Set.HasDensity]
  have hbound : ∀ N : ℕ, 0 < N →
      |S.partialDensity Set.univ N - (A.card : ℝ) / (M : ℝ)| ≤ ((M : ℝ) + 1) / (N : ℝ) := by
    intro N hN
    simp only [Set.partialDensity, Set.inter_univ]
    have hIio : (Set.univ ∩ Set.Iio N).ncard = N := by
      rw [Set.univ_inter]
      have hset : Set.Iio N = ↑(Finset.range N) := by
        ext n; simp
      rw [hset, Set.ncard_coe_finset, Finset.card_range]
    rw [hIio]
    set q := N / M
    have hqM : q * M ≤ N := Nat.div_mul_le_self N M
    have hNlt : N < (q + 1) * M := by
      rw [add_mul, one_mul]
      have h1 := Nat.div_add_mod N M
      have h2 := Nat.mod_lt N hM
      have h3 : q * M = M * (N / M) := mul_comm q M
      omega
    have hcount_block : ∀ m : ℕ,
        ((Finset.Ico (m * M) ((m + 1) * M)).filter (fun n => n % M ∈ A)).card = A.card := by
      intro m
      refine Finset.card_bij (fun n _ => n % M) ?_ ?_ ?_
      · intro n hn
        rw [Finset.mem_filter] at hn
        exact hn.2
      · intro n₁ hn₁ n₂ hn₂ heq
        rw [Finset.mem_filter, Finset.mem_Ico] at hn₁ hn₂
        have h1 : n₁ = m * M + n₁ % M := by
          have hd : n₁ / M = m := by
            apply Nat.div_eq_of_lt_le
            · exact hn₁.1.1
            · exact hn₁.1.2
          rw [← hd, Nat.div_add_mod']
        have h2 : n₂ = m * M + n₂ % M := by
          have hd : n₂ / M = m := by
            apply Nat.div_eq_of_lt_le
            · exact hn₂.1.1
            · exact hn₂.1.2
          rw [← hd, Nat.div_add_mod']
        omega
      · intro a ha
        refine ⟨m * M + a, ?_, ?_⟩
        · rw [Finset.mem_filter, Finset.mem_Ico]
          have haM : a < M := Finset.mem_range.mp (hAM ha)
          refine ⟨⟨Nat.le_add_right _ _, by rw [add_mul, one_mul]; omega⟩, ?_⟩
          rwa [mul_comm m M, Nat.mul_add_mod, Nat.mod_eq_of_lt haM]
        · have haM : a < M := Finset.mem_range.mp (hAM ha)
          rw [mul_comm m M, Nat.mul_add_mod, Nat.mod_eq_of_lt haM]
    have hcount_prefix :
        ((Finset.range (q * M)).filter (fun n => n % M ∈ A)).card = q * A.card := by
      clear hN hqM hNlt
      induction q with
      | zero => simp
      | succ q ih =>
        rw [add_mul, one_mul, Finset.range_eq_Ico]
        have hsplit : Finset.Ico 0 (q * M + M) = Finset.Ico 0 (q * M) ∪ Finset.Ico (q * M) ((q + 1) * M) := by
          ext x
          simp only [Finset.mem_Ico, Finset.mem_union]
          rw [add_mul, one_mul]
          omega
        rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint]
        · rw [← Finset.range_eq_Ico, ih, hcount_block, add_mul, one_mul]
        · rw [Finset.disjoint_left]
          intro x hx₁ hx₂
          rw [Finset.mem_filter, Finset.mem_Ico] at hx₁ hx₂
          omega
    have hS_eq : (S ∩ Set.Iio N).ncard =
        ((Finset.range N).filter (fun n => 0 < n ∧ n % M ∈ A)).card := by
      have hset : (S ∩ Set.Iio N) = ↑((Finset.range N).filter (fun n => 0 < n ∧ n % M ∈ A)) := by
        ext n
        simp only [Set.mem_inter_iff, Set.mem_Iio, Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨hnS, hn⟩
          have hn0 : 0 < n := Nat.pos_of_ne_zero (fun h => h0 (h ▸ hnS))
          exact ⟨hn, hn0, (hper n hn0).mp hnS⟩
        · rintro ⟨hn, hn0, hA⟩
          exact ⟨(hper n hn0).mpr hA, hn⟩
      rw [hset, Set.ncard_coe_finset]
    have hcard_le : ((Finset.range N).filter (fun n => 0 < n ∧ n % M ∈ A)).card ≤ q * A.card + M := by
      have hsub : (Finset.range N).filter (fun n => 0 < n ∧ n % M ∈ A) ⊆
          (Finset.range (q * M)).filter (fun n => n % M ∈ A) ∪ Finset.Ico (q * M) N := by
        intro n hn
        rw [Finset.mem_filter, Finset.mem_range] at hn
        rw [Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        by_cases h : n < q * M
        · left; exact ⟨h, hn.2.2⟩
        · right; exact ⟨by omega, hn.1⟩
      have hq_def : q * M = M * (N / M) := mul_comm q M
      have hrem_lt : N - q * M ≤ M := by
        have := Nat.div_add_mod N M
        have := Nat.mod_lt N hM
        omega
      calc ((Finset.range N).filter (fun n => 0 < n ∧ n % M ∈ A)).card
          ≤ ((Finset.range (q * M)).filter (fun n => n % M ∈ A) ∪ Finset.Ico (q * M) N).card :=
            Finset.card_le_card hsub
        _ ≤ ((Finset.range (q * M)).filter (fun n => n % M ∈ A)).card + (Finset.Ico (q * M) N).card :=
            Finset.card_union_le _ _
        _ = q * A.card + (N - q * M) := by rw [hcount_prefix, Nat.card_Ico]
        _ ≤ q * A.card + M := by omega
    have hcard_ge : q * A.card ≤ ((Finset.range N).filter (fun n => 0 < n ∧ n % M ∈ A)).card + 1 := by
      have hsub : (Finset.range (q * M)).filter (fun n => n % M ∈ A) ⊆
          (Finset.range N).filter (fun n => 0 < n ∧ n % M ∈ A) ∪ {0} := by
        intro n hn
        rw [Finset.mem_filter, Finset.mem_range] at hn
        rw [Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
        by_cases h0n : n = 0
        · right; exact h0n
        · left; exact ⟨by omega, Nat.pos_of_ne_zero h0n, hn.2⟩
      calc q * A.card = ((Finset.range (q * M)).filter (fun n => n % M ∈ A)).card := hcount_prefix.symm
        _ ≤ ((Finset.range N).filter (fun n => 0 < n ∧ n % M ∈ A) ∪ {0}).card :=
            Finset.card_le_card hsub
        _ ≤ ((Finset.range N).filter (fun n => 0 < n ∧ n % M ∈ A)).card + 1 :=
            Finset.card_union_le _ _
    rw [hS_eq]
    have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN
    have hM_pos : (0 : ℝ) < M := by exact_mod_cast hM
    have hAM_le : (A.card : ℝ) ≤ M := by exact_mod_cast (Finset.card_le_card hAM).trans_eq (Finset.card_range M)
    have hqM_R : (q : ℝ) * M ≤ N := by exact_mod_cast hqM
    have hNlt_R : (N : ℝ) < ((q : ℝ) + 1) * M := by exact_mod_cast hNlt
    have hle_R : (((Finset.range N).filter (fun n => 0 < n ∧ n % M ∈ A)).card : ℝ) ≤ (q : ℝ) * A.card + M := by
      exact_mod_cast hcard_le
    have hge_R : (q : ℝ) * A.card ≤ (((Finset.range N).filter (fun n => 0 < n ∧ n % M ∈ A)).card : ℝ) + 1 := by
      exact_mod_cast hcard_ge
    have hM0 : (M : ℝ) ≠ 0 := hM_pos.ne'
    have hN0 : (N : ℝ) ≠ 0 := hN_pos.ne'
    rw [abs_le]
    constructor
    · have h1 : (A.card : ℝ) / M - ((q : ℝ) * A.card - 1) / N =
          (A.card : ℝ) * (N - (q : ℝ) * M) / (M * N) + 1 / N := by
        field_simp; ring
      have h2 : (A.card : ℝ) * (N - (q : ℝ) * M) / (M * N) ≤ M * M / (M * N) := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul hAM_le (by linarith) (by linarith) (by positivity)
      have h3 : (M : ℝ) * M / (M * N) = M / N := by field_simp
      have h4 : (((Finset.range N).filter (fun n => 0 < n ∧ n % M ∈ A)).card : ℝ) / N ≥
          ((q : ℝ) * A.card - 1) / N := by
        exact div_le_div_of_nonneg_right (by linarith) hN_pos.le
      have h5 : (1 : ℝ) / N + M / N = (M + 1) / N := by ring
      linarith [h1, h2, h3, h4, h5]
    · have h1 : ((q : ℝ) * A.card + M) / N - (A.card : ℝ) / M =
          M / N - (A.card : ℝ) * (N - (q : ℝ) * M) / (M * N) := by
        field_simp; ring
      have h2 : 0 ≤ (A.card : ℝ) * (N - (q : ℝ) * M) / (M * N) := by
        refine div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (by positivity)
      have h3 : (((Finset.range N).filter (fun n => 0 < n ∧ n % M ∈ A)).card : ℝ) / N ≤
          ((q : ℝ) * A.card + M) / N := by
        exact div_le_div_of_nonneg_right (by linarith) hN_pos.le
      have h4 : (M : ℝ) / N ≤ (M + 1) / N := div_le_div_of_nonneg_right (by linarith) hN_pos.le
      linarith [h1, h2, h3, h4]
  have htend : Tendsto (fun N : ℕ => ((M : ℝ) + 1) / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ htend
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [Real.norm_eq_abs]
  exact hbound N hN

section
open Classical

/-- CRT residue counting for prime divisibility. -/
lemma crt_count (r : ℕ) (T : Finset ℕ) (hT : T ⊆ Finset.range r) :
    ((Finset.range (∏ j ∈ Finset.range r, pNth j)).filter
      (fun a => (∀ j ∈ T, pNth j ∣ a) ∧ (∀ j ∈ Finset.range r \ T, ¬ pNth j ∣ a))).card =
    ∏ j ∈ Finset.range r, (if j ∈ T then 1 else pNth j - 1) := by
  induction r generalizing T with
  | zero =>
    have hTe : T = ∅ := Finset.subset_empty.mp (by simpa using hT)
    subst hTe
    simp
  | succ r ih =>
    set M' := ∏ j ∈ Finset.range r, pNth j
    have hM'_pos : 0 < M' := Finset.prod_pos fun j _ => pNth_pos j
    have hcop : Nat.Coprime M' (pNth r) := by
      refine Nat.Coprime.prod_left fun j hj => ?_
      have hjr : j < r := Finset.mem_range.mp hj
      have hne : pNth j ≠ pNth r := (pNth_strictMono.lt_iff_lt.mpr hjr).ne
      exact (Nat.coprime_primes (pNth_prime j) (pNth_prime r)).mpr hne
    set T' := T ∩ Finset.range r
    have hT' : T' ⊆ Finset.range r := Finset.inter_subset_right
    have ih' := ih T' hT'
    have hM_eq : ∏ j ∈ Finset.range (r + 1), pNth j = M' * pNth r := Finset.prod_range_succ _ r
    rw [hM_eq, Finset.prod_range_succ]
    have hbij : ∀ a : ℕ,
        ((∀ j ∈ T, pNth j ∣ a) ∧ (∀ j ∈ Finset.range (r + 1) \ T, ¬ pNth j ∣ a)) ↔
        (((∀ j ∈ T', pNth j ∣ (a % M')) ∧ (∀ j ∈ Finset.range r \ T', ¬ pNth j ∣ (a % M'))) ∧
          (if r ∈ T then pNth r ∣ (a % pNth r) else ¬ pNth r ∣ (a % pNth r))) := by
      intro a
      have hdvd_lt : ∀ j ∈ Finset.range r, (pNth j ∣ a ↔ pNth j ∣ (a % M')) := by
        intro j hj
        have hjp : pNth j ∣ M' := Finset.dvd_prod_of_mem _ hj
        exact Nat.dvd_mod_iff hjp |>.symm
      have hdvd_r : pNth r ∣ a ↔ pNth r ∣ (a % pNth r) :=
        (Nat.dvd_mod_iff dvd_rfl).symm
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨⟨fun j hj => ?_, fun j hj => ?_⟩, ?_⟩
        · rw [Finset.mem_inter] at hj
          exact (hdvd_lt j hj.2).mp (h1 j hj.1)
        · rw [Finset.mem_sdiff] at hj
          have hjr : j ∈ Finset.range (r + 1) := Finset.range_mono (Nat.le_succ r) hj.1
          have hjT : j ∉ T := fun h => hj.2 (Finset.mem_inter.mpr ⟨h, hj.1⟩)
          exact mt (hdvd_lt j hj.1).mpr (h2 j (Finset.mem_sdiff.mpr ⟨hjr, hjT⟩))
        · split_ifs with hr
          · exact hdvd_r.mp (h1 r hr)
          · exact mt hdvd_r.mpr (h2 r (Finset.mem_sdiff.mpr ⟨Finset.mem_range_succ_iff.mpr le_rfl, hr⟩))
      · rintro ⟨⟨h1, h2⟩, hr⟩
        refine ⟨fun j hj => ?_, fun j hj => ?_⟩
        · have hj_range : j ∈ Finset.range (r + 1) := hT hj
          rw [Finset.mem_range_succ_iff] at hj_range
          rcases eq_or_lt_of_le hj_range with rfl | hjr
          · rw [if_pos hj] at hr
            exact hdvd_r.mpr hr
          · have hjr' : j ∈ Finset.range r := Finset.mem_range.mpr hjr
            exact (hdvd_lt j hjr').mpr (h1 j (Finset.mem_inter.mpr ⟨hj, hjr'⟩))
        · rw [Finset.mem_sdiff, Finset.mem_range_succ_iff] at hj
          rcases eq_or_lt_of_le hj.1 with rfl | hjr
          · rw [if_neg hj.2] at hr
            exact mt hdvd_r.mp hr
          · have hjr' : j ∈ Finset.range r := Finset.mem_range.mpr hjr
            have hjT' : j ∉ T' := fun h => hj.2 (Finset.mem_inter.mp h).1
            exact mt (hdvd_lt j hjr').mp (h2 j (Finset.mem_sdiff.mpr ⟨hjr', hjT'⟩))
    set S1 := (Finset.range M').filter (fun b => (∀ j ∈ T', pNth j ∣ b) ∧ (∀ j ∈ Finset.range r \ T', ¬ pNth j ∣ b))
    set S2 := (Finset.range (pNth r)).filter (fun c => if r ∈ T then pNth r ∣ c else ¬ pNth r ∣ c)
    have hS2_card : S2.card = if r ∈ T then 1 else pNth r - 1 := by
      by_cases hr : r ∈ T
      · have hS2_eq : S2 = {0} := by
          ext c
          simp only [S2, Finset.mem_filter, Finset.mem_range, if_pos hr, Finset.mem_singleton]
          constructor
          · rintro ⟨hc, hd⟩; exact Nat.eq_zero_of_dvd_of_lt hd hc
          · rintro rfl; exact ⟨pNth_pos r, dvd_zero _⟩
        rw [if_pos hr, hS2_eq, Finset.card_singleton]
      · have hS2_eq : S2 = Finset.Ico 1 (pNth r) := by
          ext c
          simp only [S2, Finset.mem_filter, Finset.mem_range, if_neg hr, Finset.mem_Ico]
          constructor
          · rintro ⟨hc, hnd⟩
            have hc0 : c ≠ 0 := fun h => hnd (h ▸ dvd_zero _)
            exact ⟨Nat.pos_of_ne_zero hc0, hc⟩
          · rintro ⟨hc1, hc2⟩
            exact ⟨hc2, Nat.not_dvd_of_pos_of_lt hc1 hc2⟩
        rw [if_neg hr, hS2_eq, Nat.card_Ico]
    have hcard_eq : ((Finset.range (M' * pNth r)).filter
        (fun a => (∀ j ∈ T, pNth j ∣ a) ∧ (∀ j ∈ Finset.range (r + 1) \ T, ¬ pNth j ∣ a))).card =
        (S1 ×ˢ S2).card := by
      haveI : NeZero M' := ⟨hM'_pos.ne'⟩
      haveI : NeZero (pNth r) := ⟨(pNth_pos r).ne'⟩
      haveI : NeZero (M' * pNth r) := ⟨(mul_pos hM'_pos (pNth_pos r)).ne'⟩
      have hcr := ZMod.chineseRemainder hcop
      convert Finset.card_bij (fun a _ => (a % M', a % pNth r)) ?_ ?_ ?_
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_range] at ha
        have hcond := (hbij a).mp ha.2
        rw [Finset.mem_product]
        exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt a hM'_pos), hcond.1⟩,
               Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt a (pNth_pos r)), hcond.2⟩⟩
      · intro a₁ ha₁ a₂ ha₂ heq
        simp only [Finset.mem_filter, Finset.mem_range] at ha₁ ha₂
        rw [Prod.mk.injEq] at heq
        have hZ : (a₁ : ZMod (M' * pNth r)) = (a₂ : ZMod (M' * pNth r)) := by
          apply hcr.injective
          simp only [map_natCast]
          ext1
          · simp only [Prod.fst_natCast]
            rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq, heq.1]
          · simp only [Prod.snd_natCast]
            rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq, heq.2]
        rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq, Nat.mod_eq_of_lt ha₁.1, Nat.mod_eq_of_lt ha₂.1] at hZ
        exact hZ
      · rintro ⟨b, c⟩ hbc
        rw [Finset.mem_product, Finset.mem_filter, Finset.mem_range, Finset.mem_filter, Finset.mem_range] at hbc
        set z := hcr.symm ((b : ZMod M'), (c : ZMod (pNth r)))
        set a := z.val
        have ha_lt : a < M' * pNth r := ZMod.val_lt z
        have haz : (a : ZMod (M' * pNth r)) = z := ZMod.natCast_zmod_val z
        have happly : hcr z = ((b : ZMod M'), (c : ZMod (pNth r))) := hcr.apply_symm_apply _
        rw [← haz, map_natCast] at happly
        have haM : a % M' = b := by
          have hz1 : (a : ZMod M') = (b : ZMod M') := congr_arg Prod.fst happly
          rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq, Nat.mod_eq_of_lt hbc.1.1] at hz1
          exact hz1
        have har : a % pNth r = c := by
          have hz2 : (a : ZMod (pNth r)) = (c : ZMod (pNth r)) := congr_arg Prod.snd happly
          rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq, Nat.mod_eq_of_lt hbc.2.1] at hz2
          exact hz2
        refine ⟨a, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_range]
          refine ⟨ha_lt, (hbij a).mpr ?_⟩
          rw [haM, har]
          exact ⟨hbc.1.2, hbc.2.2⟩
        · simp [haM, har]
    convert hcard_eq.trans _
    rw [Finset.card_product, ih', hS2_card]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    have hjT : j ∈ T' ↔ j ∈ T := ⟨fun h => (Finset.mem_inter.mp h).1, fun h => Finset.mem_inter.mpr ⟨h, hj⟩⟩
    simp only [hjT]

/-- Exact density of `kthPrimeFactorSet k (pNth r)`. -/
lemma kthPrimeFactorSet_hasDensity (k r : ℕ) (hk : 1 ≤ k) :
    (Erdos690.kthPrimeFactorSet k (pNth r)).HasDensity (densK k r) := by
  set M := ∏ j ∈ Finset.range (r + 1), pNth j
  have hM_pos : 0 < M := Finset.prod_pos fun j _ => pNth_pos j
  set A := (Finset.range M).filter (fun a =>
    pNth r ∣ a ∧ ((Finset.range r).filter (fun j => pNth j ∣ a)).card = k - 1)
  have hAM : A ⊆ Finset.range M := Finset.filter_subset _ _
  have h0 : 0 ∉ Erdos690.kthPrimeFactorSet k (pNth r) := by
    intro h
    exact lt_irrefl 0 h.1
  have hper : ∀ n, 0 < n → (n ∈ Erdos690.kthPrimeFactorSet k (pNth r) ↔ n % M ∈ A) := by
    intro n hn
    simp only [Erdos690.kthPrimeFactorSet, Set.mem_setOf_eq, A, Finset.mem_filter, Finset.mem_range]
    have hmod_lt : n % M < M := Nat.mod_lt n hM_pos
    have hdvd_r : pNth r ∣ n ↔ pNth r ∣ n % M :=
      (Nat.dvd_mod_iff (Finset.dvd_prod_of_mem _ (Finset.mem_range_succ_iff.mpr le_rfl))).symm
    have hfilter_eq : (n.primeFactors.filter (· < pNth r)).card =
        ((Finset.range r).filter (fun j => pNth j ∣ n % M)).card := by
      refine Finset.card_bij (fun q _ => Nat.count Nat.Prime q) ?_ ?_ ?_
      · intro q hq
        rw [Finset.mem_filter, Nat.mem_primeFactors] at hq
        rw [Finset.mem_filter, Finset.mem_range]
        have hj : pNth (Nat.count Nat.Prime q) = q := Nat.nth_count hq.1.1
        have hlt : Nat.count Nat.Prime q < r := by
          rw [← pNth_strictMono.lt_iff_lt, hj]
          exact hq.2
        have hd : pNth (Nat.count Nat.Prime q) ∣ n % M := by
          have hq_lt : Nat.count Nat.Prime q < r + 1 := by omega
          have hq_dvd_M : q ∣ M := by
            rw [← hj]
            exact Finset.dvd_prod_of_mem pNth (Finset.mem_range.mpr hq_lt)
          have hq_dvd : q ∣ n % M := (Nat.dvd_mod_iff hq_dvd_M).mpr hq.1.2.1
          rwa [hj]
        exact ⟨hlt, hd⟩
      · intro q₁ hq₁ q₂ hq₂ heq
        rw [Finset.mem_filter, Nat.mem_primeFactors] at hq₁ hq₂
        have h1 := Nat.nth_count hq₁.1.1
        have h2 := Nat.nth_count hq₂.1.1
        rw [← h1, ← h2, heq]
      · intro j hj
        rw [Finset.mem_filter, Finset.mem_range] at hj
        have hjr : j < r := hj.1
        have hjr1 : j < r + 1 := by omega
        refine ⟨pNth j, ?_, ?_⟩
        · rw [Finset.mem_filter, Nat.mem_primeFactors]
          have hjp : pNth j ∣ M := Finset.dvd_prod_of_mem pNth (Finset.mem_range.mpr hjr1)
          refine ⟨⟨pNth_prime j, (Nat.dvd_mod_iff hjp).mp hj.2, hn.ne'⟩, pNth_strictMono hjr⟩
        · exact Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime j
    constructor
    · rintro ⟨_, hpr, hcard⟩
      refine ⟨hmod_lt, hdvd_r.mp (Nat.dvd_of_mem_primeFactors hpr), ?_⟩
      rwa [← hfilter_eq]
    · rintro ⟨_, hpr, hcard⟩
      refine ⟨hn, ?_, ?_⟩
      · rw [Nat.mem_primeFactors]
        exact ⟨pNth_prime r, hdvd_r.mpr hpr, hn.ne'⟩
      · rwa [hfilter_eq]
  have hdens := hasDensity_periodic hM_pos A hAM h0 hper
  suffices hEq : (A.card : ℝ) / (M : ℝ) = densK k r by rwa [← hEq]
  have hA_part : A = ((Finset.range r).powersetCard (k - 1)).biUnion (fun S =>
      (Finset.range M).filter (fun a =>
        (∀ j ∈ insert r S, pNth j ∣ a) ∧ (∀ j ∈ Finset.range (r + 1) \ insert r S, ¬ pNth j ∣ a))) := by
    ext a
    simp only [A, Finset.mem_filter, Finset.mem_range, Finset.mem_biUnion, Finset.mem_powersetCard]
    constructor
    · rintro ⟨haM, har, hcard⟩
      refine ⟨(Finset.range r).filter (fun j => pNth j ∣ a), ⟨Finset.filter_subset _ _, hcard⟩, haM, ?_, ?_⟩
      · intro j hj
        rw [Finset.mem_insert, Finset.mem_filter] at hj
        rcases hj with rfl | hj
        · exact har
        · exact hj.2
      · intro j hj
        rw [Finset.mem_sdiff, Finset.mem_range_succ_iff, Finset.mem_insert, Finset.mem_filter] at hj
        push Not at hj
        have hjr : j < r := lt_of_le_of_ne hj.1 hj.2.1
        exact fun hd => hj.2.2 (Finset.mem_range.mpr hjr) hd
    · rintro ⟨S, ⟨hSr, hScard⟩, haM, h1, h2⟩
      refine ⟨haM, h1 r (Finset.mem_insert_self r S), ?_⟩
      have hfilter_eq : (Finset.range r).filter (fun j => pNth j ∣ a) = S := by
        ext j
        rw [Finset.mem_filter]
        constructor
        · rintro ⟨hjr, hjd⟩
          by_contra hjS
          have hj_sdiff : j ∈ Finset.range (r + 1) \ insert r S := by
            rw [Finset.mem_sdiff, Finset.mem_range_succ_iff, Finset.mem_insert]
            have := Finset.mem_range.mp hjr
            exact ⟨by omega, by rintro (rfl | h); omega; exact hjS h⟩
          exact h2 j hj_sdiff hjd
        · intro hjS
          exact ⟨hSr hjS, h1 j (Finset.mem_insert_of_mem hjS)⟩
      rw [hfilter_eq, hScard]
  have hdisj : Set.PairwiseDisjoint ↑((Finset.range r).powersetCard (k - 1)) (fun S =>
      (Finset.range M).filter (fun a =>
        (∀ j ∈ insert r S, pNth j ∣ a) ∧ (∀ j ∈ Finset.range (r + 1) \ insert r S, ¬ pNth j ∣ a))) := by
    intro S₁ hS₁ S₂ hS₂ hne
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hS₁ hS₂
    rw [Function.onFun, Finset.disjoint_left]
    intro a ha₁ ha₂
    simp only [Finset.mem_filter] at ha₁ ha₂
    apply hne
    ext j
    constructor
    · intro hj
      by_contra hj₂
      have hj_sdiff : j ∈ Finset.range (r + 1) \ insert r S₂ := by
        rw [Finset.mem_sdiff, Finset.mem_range_succ_iff, Finset.mem_insert]
        have := Finset.mem_range.mp (hS₁.1 hj)
        exact ⟨by omega, by rintro (rfl | h); omega; exact hj₂ h⟩
      exact ha₂.2.2 j hj_sdiff (ha₁.2.1 j (Finset.mem_insert_of_mem hj))
    · intro hj
      by_contra hj₁
      have hj_sdiff : j ∈ Finset.range (r + 1) \ insert r S₁ := by
        rw [Finset.mem_sdiff, Finset.mem_range_succ_iff, Finset.mem_insert]
        have := Finset.mem_range.mp (hS₂.1 hj)
        exact ⟨by omega, by rintro (rfl | h); omega; exact hj₁ h⟩
      exact ha₁.2.2 j hj_sdiff (ha₂.2.1 j (Finset.mem_insert_of_mem hj))
  have hA_card : A.card = ∑ S ∈ (Finset.range r).powersetCard (k - 1),
      ((Finset.range M).filter (fun a =>
        (∀ j ∈ insert r S, pNth j ∣ a) ∧ (∀ j ∈ Finset.range (r + 1) \ insert r S, ¬ pNth j ∣ a))).card := by
    rw [hA_part]
    convert Finset.card_biUnion hdisj
  rw [hA_card]
  push_cast
  have hterm : ∀ S ∈ (Finset.range r).powersetCard (k - 1),
      (((Finset.range M).filter (fun a =>
        (∀ j ∈ insert r S, pNth j ∣ a) ∧ (∀ j ∈ Finset.range (r + 1) \ insert r S, ¬ pNth j ∣ a))).card : ℝ) /
      (M : ℝ) = (1 / (pNth r : ℝ)) * (∏ j ∈ Finset.range r, (1 - 1 / (pNth j : ℝ))) * ∏ j ∈ S, xTerm j := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    have hT : insert r S ⊆ Finset.range (r + 1) := by
      intro j hj
      rw [Finset.mem_insert] at hj
      rw [Finset.mem_range_succ_iff]
      rcases hj with rfl | hj
      · exact le_rfl
      · exact (Finset.mem_range.mp (hS.1 hj)).le
    have hcnt : ((Finset.range M).filter (fun a =>
        (∀ j ∈ insert r S, pNth j ∣ a) ∧ (∀ j ∈ Finset.range (r + 1) \ insert r S, ¬ pNth j ∣ a))).card =
        ∏ j ∈ Finset.range (r + 1), (if j ∈ insert r S then 1 else pNth j - 1) := by
      convert crt_count (r + 1) (insert r S) hT
    rw [hcnt]
    have hM_R : (M : ℝ) = (pNth r : ℝ) * ∏ j ∈ Finset.range r, (pNth j : ℝ) := by
      simp only [M, Finset.prod_range_succ]
      push_cast
      ring
    have hprod_num : ((∏ j ∈ Finset.range (r + 1), (if j ∈ insert r S then 1 else pNth j - 1) : ℕ) : ℝ) =
        ∏ j ∈ Finset.range r, (if j ∈ S then 1 else (pNth j : ℝ) - 1) := by
      rw [Finset.prod_range_succ, if_pos (Finset.mem_insert_self r S), mul_one]
      push_cast
      refine Finset.prod_congr rfl fun j hj => ?_
      have hjne : j ≠ r := (Finset.mem_range.mp hj).ne
      have hj_ins : j ∈ insert r S ↔ j ∈ S := by
        rw [Finset.mem_insert]
        exact ⟨fun h => h.resolve_left hjne, fun h => Or.inr h⟩
      by_cases h1 : j ∈ insert r S <;> by_cases h2 : j ∈ S
      · simp [h1, h2]
      · exact absurd (hj_ins.mp h1) h2
      · exact absurd (hj_ins.mpr h2) h1
      · simp [h1, h2, Nat.cast_sub (Nat.one_le_of_lt (two_le_pNth j))]
    rw [hprod_num, hM_R]
    have hsplit : ∏ j ∈ Finset.range r, (if j ∈ S then (1 : ℝ) else (pNth j : ℝ) - 1) =
        (∏ j ∈ Finset.range r, ((pNth j : ℝ) - 1)) * ∏ j ∈ S, xTerm j := by
      have hS' : S ⊆ Finset.range r := hS.1
      have h1 : ∏ j ∈ range r, (if j ∈ S then (1 : ℝ) else (pNth j : ℝ) - 1) =
          ∏ j ∈ range r \ S, ((pNth j : ℝ) - 1) := by
        rw [← Finset.prod_sdiff hS']
        have hS1 : ∏ j ∈ S, (if j ∈ S then (1 : ℝ) else (pNth j : ℝ) - 1) = 1 :=
          Finset.prod_eq_one fun j hj => if_pos hj
        rw [hS1, mul_one]
        refine Finset.prod_congr rfl fun j hj => if_neg (Finset.mem_sdiff.mp hj).2
      rw [h1]
      have h2 : (∏ j ∈ range r \ S, ((pNth j : ℝ) - 1)) * (∏ j ∈ S, ((pNth j : ℝ) - 1)) *
          ∏ j ∈ S, xTerm j = ∏ j ∈ range r \ S, ((pNth j : ℝ) - 1) := by
        rw [mul_assoc, ← Finset.prod_mul_distrib]
        have hS_one : ∏ j ∈ S, (((pNth j : ℝ) - 1) * xTerm j) = 1 := by
          refine Finset.prod_eq_one fun j _ => ?_
          unfold xTerm
          exact mul_one_div_cancel (pNth_sub_one_pos j).ne'
        rw [hS_one, mul_one]
      rw [← h2]
      conv_rhs => rw [← Finset.prod_sdiff hS']
    rw [hsplit]
    have hp_ne : ∀ j ∈ Finset.range r, (pNth j : ℝ) ≠ 0 := fun j _ => by exact_mod_cast (pNth_pos j).ne'
    have hpr_ne : (pNth r : ℝ) ≠ 0 := by exact_mod_cast (pNth_pos r).ne'
    have hprod_ne : (∏ j ∈ Finset.range r, (pNth j : ℝ)) ≠ 0 := Finset.prod_ne_zero_iff.mpr hp_ne
    have hdiv_prod : (∏ j ∈ Finset.range r, ((pNth j : ℝ) - 1)) / (∏ j ∈ Finset.range r, (pNth j : ℝ)) =
        ∏ j ∈ Finset.range r, (1 - 1 / (pNth j : ℝ)) := by
      rw [← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun j hj => ?_
      have := hp_ne j hj
      field_simp
    calc (∏ j ∈ Finset.range r, ((pNth j : ℝ) - 1)) * (∏ j ∈ S, xTerm j) /
          ((pNth r : ℝ) * ∏ j ∈ Finset.range r, (pNth j : ℝ))
        = (1 / (pNth r : ℝ)) * ((∏ j ∈ Finset.range r, ((pNth j : ℝ) - 1)) /
            (∏ j ∈ Finset.range r, (pNth j : ℝ))) * (∏ j ∈ S, xTerm j) := by ring
      _ = (1 / (pNth r : ℝ)) * (∏ j ∈ Finset.range r, (1 - 1 / (pNth j : ℝ))) * ∏ j ∈ S, xTerm j := by
          rw [hdiv_prod]
  rw [Finset.sum_div]
  unfold densK elemSym
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl hterm

end

/-- Elementary lower bound on `R_k(r) = elemSym (k - 2) r / elemSym (k - 1) r`. -/
lemma R_lower_bound {k r s : ℕ} (hk : 2 ≤ k) (hs : s < k - 1) (hr : k - 1 ≤ r)
    (hS : sumX s < sumX r) :
    ((k - 1 - s : ℕ) : ℝ) / (sumX r - sumX s) ≤ elemSym (k - 2) r / elemSym (k - 1) r := by
  have hE1 : 0 < elemSym (k - 1) r := elemSym_pos hr
  have hSpos : 0 < sumX r - sumX s := by linarith
  rw [div_le_div_iff₀ hSpos hE1]
  have hcount : ∀ T ∈ (Finset.range r).powersetCard (k - 1),
      (k - 1 - s : ℕ) ≤ (T \ Finset.range s).card := by
    intro T hT
    rw [Finset.mem_powersetCard] at hT
    have h1 : (T ∩ Finset.range s).card ≤ s :=
      (Finset.card_le_card Finset.inter_subset_right).trans_eq (Finset.card_range s)
    have h2 : (T \ Finset.range s).card + (T ∩ Finset.range s).card = T.card :=
      Finset.card_sdiff_add_card_inter T (Finset.range s)
    omega
  have hstep1 : ((k - 1 - s : ℕ) : ℝ) * elemSym (k - 1) r ≤
      ∑ T ∈ (Finset.range r).powersetCard (k - 1),
        ((T \ Finset.range s).card : ℝ) * ∏ i ∈ T, xTerm i := by
    unfold elemSym
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun T hT => ?_
    refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun i _ => xTerm_nonneg i)
    exact_mod_cast hcount T hT
  have hstep2 : ∑ T ∈ (Finset.range r).powersetCard (k - 1),
        ((T \ Finset.range s).card : ℝ) * ∏ i ∈ T, xTerm i =
      ∑ j ∈ Finset.Ico s r, xTerm j *
        ∑ U ∈ ((Finset.range r).erase j).powersetCard (k - 2), ∏ i ∈ U, xTerm i := by
    have hswap : ∀ T ∈ (Finset.range r).powersetCard (k - 1),
        ((T \ Finset.range s).card : ℝ) * ∏ i ∈ T, xTerm i =
        ∑ j ∈ Finset.Ico s r, if j ∈ T then ∏ i ∈ T, xTerm i else 0 := by
      intro T hT
      rw [Finset.mem_powersetCard] at hT
      rw [← Finset.sum_filter]
      have hfilt : (Finset.Ico s r).filter (· ∈ T) = T \ Finset.range s := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_sdiff, Finset.mem_range]
        exact ⟨fun ⟨⟨h1, _⟩, h2⟩ => ⟨h2, by omega⟩, fun ⟨h1, h2⟩ => ⟨⟨by omega, Finset.mem_range.mp (hT.1 h1)⟩, h1⟩⟩
      rw [hfilt, Finset.sum_const, nsmul_eq_mul]
    rw [Finset.sum_congr rfl hswap, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_Ico] at hj
    have hfilt : ((Finset.range r).powersetCard (k - 1)).filter (j ∈ ·) =
        (((Finset.range r).erase j).powersetCard (k - 2)).image (insert j) := by
      ext T
      simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_image]
      constructor
      · rintro ⟨⟨hTr, hTc⟩, hjT⟩
        refine ⟨T.erase j, ⟨?_, ?_⟩, Finset.insert_erase hjT⟩
        · exact Finset.erase_subset_erase j hTr
        · rw [Finset.card_erase_of_mem hjT, hTc]; omega
      · rintro ⟨U, ⟨hUr, hUc⟩, rfl⟩
        have hjU : j ∉ U := fun h => (Finset.mem_erase.mp (hUr h)).1 rfl
        refine ⟨⟨Finset.insert_subset_iff.mpr ⟨Finset.mem_range.mpr hj.2, hUr.trans (Finset.erase_subset _ _)⟩, ?_⟩,
                Finset.mem_insert_self j U⟩
        rw [Finset.card_insert_of_notMem hjU, hUc]; omega
    rw [← Finset.sum_filter, hfilt, Finset.sum_image, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun U hU => ?_
      rw [Finset.mem_powersetCard] at hU
      have hjU : j ∉ U := fun h => (Finset.mem_erase.mp (hU.1 h)).1 rfl
      rw [Finset.prod_insert hjU]
    · intro U₁ hU₁ U₂ hU₂ heq
      rw [Finset.mem_coe, Finset.mem_powersetCard] at hU₁ hU₂
      have hj₁ : j ∉ U₁ := fun h => (Finset.mem_erase.mp (hU₁.1 h)).1 rfl
      have hj₂ : j ∉ U₂ := fun h => (Finset.mem_erase.mp (hU₂.1 h)).1 rfl
      exact (Finset.insert_erase_invOn.2.injOn (by simp [hj₁]) (by simp [hj₂])) heq
  have hstep3 : ∑ j ∈ Finset.Ico s r, xTerm j *
        ∑ U ∈ ((Finset.range r).erase j).powersetCard (k - 2), ∏ i ∈ U, xTerm i ≤
      (sumX r - sumX s) * elemSym (k - 2) r := by
    have hIco_sum : ∑ j ∈ Finset.Ico s r, xTerm j = sumX r - sumX s := by
      unfold sumX
      have hsl : s ≤ r := by omega
      rw [← Finset.sum_range_add_sum_Ico xTerm hsl]
      ring
    rw [← hIco_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    refine mul_le_mul_of_nonneg_left ?_ (xTerm_nonneg j)
    unfold elemSym
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun U _ _ => Finset.prod_nonneg fun i _ => xTerm_nonneg i)
    exact Finset.powersetCard_mono (Finset.erase_subset j (Finset.range r))
  linarith

/-- Sum of an antitone function on any `m`-subset is at most its sum on `range m`. -/
lemma sum_antitone_le_range {f : ℕ → ℝ} (hf : Antitone f) {U : Finset ℕ} {m : ℕ}
    (hU : U.card = m) :
    ∑ j ∈ U, f j ≤ ∑ j ∈ Finset.range m, f j := by
  have hcard : (U \ Finset.range m).card = (Finset.range m \ U).card := by
    have h1 := Finset.card_sdiff_add_card_inter U (Finset.range m)
    have h2 := Finset.card_sdiff_add_card_inter (Finset.range m) U
    rw [Finset.inter_comm] at h2
    rw [hU] at h1
    rw [Finset.card_range] at h2
    omega
  have hsplit1 : ∑ j ∈ U, f j = ∑ j ∈ U \ Finset.range m, f j + ∑ j ∈ U ∩ Finset.range m, f j := by
    have hUeq : U \ (U ∩ Finset.range m) = U \ Finset.range m := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
    rw [← Finset.sum_sdiff (Finset.inter_subset_left : U ∩ Finset.range m ⊆ U), hUeq]
  have hsplit2 : ∑ j ∈ Finset.range m, f j =
      ∑ j ∈ Finset.range m \ U, f j + ∑ j ∈ Finset.range m ∩ U, f j := by
    have hmeq : Finset.range m \ (Finset.range m ∩ U) = Finset.range m \ U := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
    have h2 := Finset.sum_sdiff (Finset.inter_subset_left : Finset.range m ∩ U ⊆ Finset.range m) (f := f)
    rw [hmeq] at h2
    exact h2.symm
  rw [hsplit1, hsplit2, Finset.inter_comm (Finset.range m) U]
  have hle1 : ∑ j ∈ U \ Finset.range m, f j ≤ ((U \ Finset.range m).card : ℝ) * f m := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [Finset.mem_sdiff, Finset.mem_range] at hj
    exact hf (by omega)
  have hle2 : ((Finset.range m \ U).card : ℝ) * f m ≤ ∑ j ∈ Finset.range m \ U, f j := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [Finset.mem_sdiff, Finset.mem_range] at hj
    exact hf hj.1.le
  rw [hcard] at hle1
  linarith

/-- Elementary upper bound on `R_k(r) = elemSym (k - 2) r / elemSym (k - 1) r`. -/
lemma R_upper_bound {k r : ℕ} (hk : 2 ≤ k) (hr : k - 1 ≤ r)
    (hS : sumX (k - 2) < sumX r) :
    elemSym (k - 2) r / elemSym (k - 1) r ≤ ((k - 1 : ℕ) : ℝ) / (sumX r - sumX (k - 2)) := by
  have hE1 : 0 < elemSym (k - 1) r := elemSym_pos hr
  have hSpos : 0 < sumX r - sumX (k - 2) := by linarith
  rw [div_le_div_iff₀ hE1 hSpos]
  have hdouble : ((k - 1 : ℕ) : ℝ) * elemSym (k - 1) r =
      ∑ U ∈ (Finset.range r).powersetCard (k - 2),
        (∏ i ∈ U, xTerm i) * (sumX r - ∑ j ∈ U, xTerm j) := by
    have h1 : ((k - 1 : ℕ) : ℝ) * elemSym (k - 1) r =
        ∑ T ∈ (Finset.range r).powersetCard (k - 1), ∑ _ ∈ T, ∏ i ∈ T, xTerm i := by
      unfold elemSym
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun T hT => ?_
      rw [Finset.mem_powersetCard] at hT
      rw [Finset.sum_const, nsmul_eq_mul, hT.2]
    have h2 : ∑ U ∈ (Finset.range r).powersetCard (k - 2),
          (∏ i ∈ U, xTerm i) * (sumX r - ∑ j ∈ U, xTerm j) =
        ∑ U ∈ (Finset.range r).powersetCard (k - 2),
          ∑ j ∈ Finset.range r \ U, xTerm j * ∏ i ∈ U, xTerm i := by
      refine Finset.sum_congr rfl fun U hU => ?_
      rw [Finset.mem_powersetCard] at hU
      have hdiff : sumX r - ∑ j ∈ U, xTerm j = ∑ j ∈ Finset.range r \ U, xTerm j := by
        unfold sumX
        rw [← Finset.sum_sdiff hU.1]
        ring
      rw [hdiff, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [h1, h2]
    have hLHS : ∑ T ∈ (Finset.range r).powersetCard (k - 1), ∑ _ ∈ T, ∏ i ∈ T, xTerm i =
        ∑ x ∈ ((Finset.range r).powersetCard (k - 1)).sigma (fun T => T), ∏ i ∈ x.fst, xTerm i :=
      (Finset.sum_sigma ((Finset.range r).powersetCard (k - 1)) (fun T => T)
        (fun x => ∏ i ∈ x.fst, xTerm i)).symm
    have hRHS : ∑ U ∈ (Finset.range r).powersetCard (k - 2), ∑ j ∈ Finset.range r \ U, xTerm j * ∏ i ∈ U, xTerm i =
        ∑ x ∈ ((Finset.range r).powersetCard (k - 2)).sigma (fun U => Finset.range r \ U),
          xTerm x.snd * ∏ i ∈ x.fst, xTerm i :=
      (Finset.sum_sigma ((Finset.range r).powersetCard (k - 2)) (fun U => Finset.range r \ U)
        (fun x => xTerm x.snd * ∏ i ∈ x.fst, xTerm i)).symm
    rw [hLHS, hRHS]
    refine Finset.sum_bij (fun ⟨T, j⟩ _ => ⟨T.erase j, j⟩) ?_ ?_ ?_ ?_
    · rintro ⟨T, j⟩ hTj
      rw [Finset.mem_sigma, Finset.mem_powersetCard] at hTj
      rw [Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_sdiff]
      refine ⟨⟨Finset.erase_subset _ _ |>.trans hTj.1.1, ?_⟩, hTj.1.1 hTj.2, Finset.notMem_erase j T⟩
      rw [Finset.card_erase_of_mem hTj.2, hTj.1.2]; omega
    · rintro ⟨T₁, j₁⟩ h₁ ⟨T₂, j₂⟩ h₂ heq
      rw [Finset.mem_sigma] at h₁ h₂
      simp only [Sigma.mk.inj_iff] at heq
      rcases heq with ⟨hT, hj⟩
      subst hj
      have h2' : insert j₁ (T₁.erase j₁) = insert j₁ (T₂.erase j₁) := congr_arg (insert j₁) hT
      rw [Finset.insert_erase h₁.2, Finset.insert_erase h₂.2] at h2'
      exact Sigma.ext h2' (heq_of_eq rfl)
    · rintro ⟨U, j⟩ hUj
      rw [Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_sdiff] at hUj
      refine ⟨⟨insert j U, j⟩, ?_, ?_⟩
      · rw [Finset.mem_sigma, Finset.mem_powersetCard]
        refine ⟨⟨Finset.insert_subset_iff.mpr ⟨hUj.2.1, hUj.1.1⟩, ?_⟩, Finset.mem_insert_self j U⟩
        rw [Finset.card_insert_of_notMem hUj.2.2, hUj.1.2]; omega
      · simp [Finset.erase_insert hUj.2.2]
    · rintro ⟨T, j⟩ hTj
      rw [Finset.mem_sigma] at hTj
      dsimp only
      rw [← Finset.prod_erase_mul T xTerm hTj.2]
      ring
  have hle : ∑ U ∈ (Finset.range r).powersetCard (k - 2),
        (∏ i ∈ U, xTerm i) * (sumX r - sumX (k - 2)) ≤
      ((k - 1 : ℕ) : ℝ) * elemSym (k - 1) r := by
    rw [hdouble]
    refine Finset.sum_le_sum fun U hU => ?_
    rw [Finset.mem_powersetCard] at hU
    refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun i _ => xTerm_nonneg i)
    have hsum_le : ∑ j ∈ U, xTerm j ≤ sumX (k - 2) :=
      sum_antitone_le_range xTerm_antitone hU.2
    linarith
  have hfac : ∑ U ∈ (Finset.range r).powersetCard (k - 2),
        (∏ i ∈ U, xTerm i) * (sumX r - sumX (k - 2)) =
      elemSym (k - 2) r * (sumX r - sumX (k - 2)) := by
    rw [← Finset.sum_mul]
    rfl
  linarith

/- ### Module 3: Chebyshev `(30 m)!` bounds -/

lemma log_factorial_lb (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * log (n : ℝ) - (n : ℝ) + 1 ≤ log (Nat.factorial n : ℝ) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases eq_or_lt_of_le hn with h1 | hn1
    · have : n = 0 := by omega
      subst this
      simp
    · have hn' : 1 ≤ n := by omega
      have ih' := ih hn'
      rw [Nat.factorial_succ, Nat.cast_mul, log_mul (by positivity) (by positivity)]
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn'
      have hlog : log (((n : ℝ) + 1) / (n : ℝ)) ≤ ((n : ℝ) + 1) / (n : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [log_div (by positivity) hn_pos.ne'] at hlog
      have hmul : (n : ℝ) * (log ((n : ℝ) + 1) - log (n : ℝ)) ≤ 1 := by
        calc (n : ℝ) * (log ((n : ℝ) + 1) - log (n : ℝ))
            ≤ (n : ℝ) * (((n : ℝ) + 1) / (n : ℝ) - 1) :=
              mul_le_mul_of_nonneg_left hlog hn_pos.le
          _ = 1 := by field_simp; ring
      push_cast
      linarith

lemma log_factorial_ub (n : ℕ) :
    log (Nat.factorial n : ℝ) ≤ ((n : ℝ) + 1) * log ((n : ℝ) + 1) - (n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, log_mul (by positivity) (by positivity)]
    have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hlog : 1 - ((n : ℝ) + 1) / ((n : ℝ) + 2) ≤ log (((n : ℝ) + 2) / ((n : ℝ) + 1)) := by
      have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < ((n : ℝ) + 2) / ((n : ℝ) + 1) by positivity)
      rwa [inv_div] at h
    rw [log_div (by positivity) hn1_pos.ne'] at hlog
    have hmul : 1 ≤ ((n : ℝ) + 2) * (log ((n : ℝ) + 2) - log ((n : ℝ) + 1)) := by
      calc (1 : ℝ) = ((n : ℝ) + 2) * (1 - ((n : ℝ) + 1) / ((n : ℝ) + 2)) := by
            field_simp; ring
        _ ≤ ((n : ℝ) + 2) * (log ((n : ℝ) + 2) - log ((n : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left hlog (by positivity)
    simp only [Nat.cast_add, Nat.cast_one] at hlog hmul ⊢
    ring_nf at ih hmul ⊢
    linarith

lemma f30_bounds (u : ℕ) :
    u / 2 + u / 3 + u / 5 ≤ u + u / 30 ∧ u + u / 30 ≤ u / 2 + u / 3 + u / 5 + 1 := by
  have h1 : u = 30 * (u / 30) + u % 30 := (Nat.div_add_mod u 30).symm
  have h2 : u % 30 < 30 := Nat.mod_lt u (by omega)
  omega

lemma f30_one_of_le_five {u : ℕ} (hu1 : 1 ≤ u) (hu5 : u ≤ 5) :
    u + u / 30 - (u / 2 + u / 3 + u / 5) = 1 := by
  omega

noncomputable def chebA : ℝ :=
  30 * log 30 - 15 * log 15 - 10 * log 10 - 6 * log 6

lemma chebA_bounds : 27.51 < chebA ∧ chebA < 27.655 := by
  have h30 : log 30 = log 2 + log 3 + log 5 := by
    rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num, log_mul (by norm_num) (by norm_num),
        log_mul (by norm_num) (by norm_num)]
  have h15 : log 15 = log 3 + log 5 := by
    rw [show (15 : ℝ) = 3 * 5 by norm_num, log_mul (by norm_num) (by norm_num)]
  have h10 : log 10 = log 2 + log 5 := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num, log_mul (by norm_num) (by norm_num)]
  have h6 : log 6 = log 2 + log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, log_mul (by norm_num) (by norm_num)]
  have hA : chebA = 14 * log 2 + 9 * log 3 + 5 * log 5 := by
    unfold chebA; rw [h30, h15, h10, h6]; ring
  have hlog2_lb : 0.693 < log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hlog2_ub : log 2 < 0.6932 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hexp_lb : (2.71828 : ℝ) < exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have hexp_ub : exp 1 < (2.72 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hlog3_lb : 1.09 < log 3 := by
    rw [lt_log_iff_exp_lt (by norm_num)]
    have hpow : (exp 1) ^ (109 : ℕ) < (3 : ℝ) ^ (100 : ℕ) := by
      calc (exp 1) ^ (109 : ℕ) < (2.72 : ℝ) ^ (109 : ℕ) := by gcongr
        _ < (3 : ℝ) ^ (100 : ℕ) := by norm_num
    have hexp_pow : (exp (1.09 : ℝ)) ^ (100 : ℕ) < (3 : ℝ) ^ (100 : ℕ) := by
      rw [← Real.exp_nat_mul]
      have h109 : (100 : ℕ) * (1.09 : ℝ) = (109 : ℕ) * (1 : ℝ) := by norm_num
      rw [h109, Real.exp_nat_mul]
      exact hpow
    exact lt_of_pow_lt_pow_left₀ 100 (by norm_num) hexp_pow
  have hlog3_ub : log 3 < 1.1 := by
    rw [log_lt_iff_lt_exp (by norm_num)]
    have hpow : (3 : ℝ) ^ (10 : ℕ) < (exp 1) ^ (11 : ℕ) := by
      calc (3 : ℝ) ^ (10 : ℕ) < (2.71828 : ℝ) ^ (11 : ℕ) := by norm_num
        _ < (exp 1) ^ (11 : ℕ) := by gcongr
    have hexp_pow : (3 : ℝ) ^ (10 : ℕ) < (exp (1.1 : ℝ)) ^ (10 : ℕ) := by
      rw [← Real.exp_nat_mul]
      have h11 : (10 : ℕ) * (1.1 : ℝ) = (11 : ℕ) * (1 : ℝ) := by norm_num
      rw [h11, Real.exp_nat_mul]
      exact hpow
    exact lt_of_pow_lt_pow_left₀ 10 (by positivity) hexp_pow
  have hlog5_lb : 1.6 < log 5 := by
    rw [lt_log_iff_exp_lt (by norm_num)]
    have hpow : (exp 1) ^ (16 : ℕ) < (5 : ℝ) ^ (10 : ℕ) := by
      calc (exp 1) ^ (16 : ℕ) < (2.72 : ℝ) ^ (16 : ℕ) := by gcongr
        _ < (5 : ℝ) ^ (10 : ℕ) := by norm_num
    have hexp_pow : (exp (1.6 : ℝ)) ^ (10 : ℕ) < (5 : ℝ) ^ (10 : ℕ) := by
      rw [← Real.exp_nat_mul]
      have h16 : (10 : ℕ) * (1.6 : ℝ) = (16 : ℕ) * (1 : ℝ) := by norm_num
      rw [h16, Real.exp_nat_mul]
      exact hpow
    exact lt_of_pow_lt_pow_left₀ 10 (by norm_num) hexp_pow
  have hlog5_ub : log 5 < 1.61 := by
    rw [log_lt_iff_lt_exp (by norm_num)]
    have hpow : (5 : ℝ) ^ (100 : ℕ) < (exp 1) ^ (161 : ℕ) := by
      calc (5 : ℝ) ^ (100 : ℕ) < (2.71828 : ℝ) ^ (161 : ℕ) := by norm_num
        _ < (exp 1) ^ (161 : ℕ) := by gcongr
    have hexp_pow : (5 : ℝ) ^ (100 : ℕ) < (exp (1.61 : ℝ)) ^ (100 : ℕ) := by
      rw [← Real.exp_nat_mul]
      have h161 : (100 : ℕ) * (1.61 : ℝ) = (161 : ℕ) * (1 : ℝ) := by norm_num
      rw [h161, Real.exp_nat_mul]
      exact hpow
    exact lt_of_pow_lt_pow_left₀ 100 (by positivity) hexp_pow
  rw [hA]
  constructor <;> linarith

noncomputable def chebLog (m : ℕ) : ℝ :=
  log (Nat.factorial (30 * m) : ℝ) + log (Nat.factorial m : ℝ) -
    log (Nat.factorial (15 * m) : ℝ) - log (Nat.factorial (10 * m) : ℝ) -
    log (Nat.factorial (6 * m) : ℝ)

lemma chebLog_bounds (m : ℕ) (hm : 1 ≤ m) :
    chebA * (m : ℝ) - 5 * log (30 * (m : ℝ) + 1) - 10 ≤ chebLog m ∧
    chebLog m ≤ chebA * (m : ℝ) + 5 * log (30 * (m : ℝ) + 1) + 10 := by
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
  have h30_lb := log_factorial_lb (30 * m) (by omega)
  have h1_lb := log_factorial_lb m hm
  have h15_lb := log_factorial_lb (15 * m) (by omega)
  have h10_lb := log_factorial_lb (10 * m) (by omega)
  have h6_lb := log_factorial_lb (6 * m) (by omega)
  have h30_ub := log_factorial_ub (30 * m)
  have h1_ub := log_factorial_ub m
  have h15_ub := log_factorial_ub (15 * m)
  have h10_ub := log_factorial_ub (10 * m)
  have h6_ub := log_factorial_ub (6 * m)
  have hlog_eq : (30 * (m : ℝ)) * log (30 * (m : ℝ)) + (m : ℝ) * log (m : ℝ) -
      (15 * (m : ℝ)) * log (15 * (m : ℝ)) - (10 * (m : ℝ)) * log (10 * (m : ℝ)) -
      (6 * (m : ℝ)) * log (6 * (m : ℝ)) = chebA * (m : ℝ) := by
    rw [log_mul (by norm_num) hm_pos.ne', log_mul (by norm_num) hm_pos.ne',
        log_mul (by norm_num) hm_pos.ne', log_mul (by norm_num) hm_pos.ne']
    unfold chebA
    ring
  have hdiff_le : ∀ c : ℝ, 1 ≤ c → c ≤ 30 →
      (c * (m : ℝ) + 1) * log (c * (m : ℝ) + 1) - c * (m : ℝ) * log (c * (m : ℝ)) ≤
        log (30 * (m : ℝ) + 1) + 1 := by
    intro c hc1 hc30
    have hcm_pos : 0 < c * (m : ℝ) := mul_pos (by linarith) hm_pos
    have h1 : c * (m : ℝ) * (log (c * (m : ℝ) + 1) - log (c * (m : ℝ))) ≤ 1 := by
      have hlog : log ((c * (m : ℝ) + 1) / (c * (m : ℝ))) ≤ (c * (m : ℝ) + 1) / (c * (m : ℝ)) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [log_div (by positivity) hcm_pos.ne'] at hlog
      calc c * (m : ℝ) * (log (c * (m : ℝ) + 1) - log (c * (m : ℝ)))
          ≤ c * (m : ℝ) * ((c * (m : ℝ) + 1) / (c * (m : ℝ)) - 1) :=
            mul_le_mul_of_nonneg_left hlog hcm_pos.le
        _ = 1 := by field_simp; ring
    have h2 : log (c * (m : ℝ) + 1) ≤ log (30 * (m : ℝ) + 1) :=
      Real.log_le_log (by positivity) (by nlinarith)
    linarith
  have hd30 := hdiff_le 30 (by norm_num) (by norm_num)
  have hd15 := hdiff_le 15 (by norm_num) (by norm_num)
  have hd10 := hdiff_le 10 (by norm_num) (by norm_num)
  have hd6 := hdiff_le 6 (by norm_num) (by norm_num)
  have hd1 := hdiff_le 1 (by norm_num) (by norm_num)
  rw [one_mul] at hd1
  have h0_le : 0 ≤ log (30 * (m : ℝ) + 1) := Real.log_nonneg (by linarith)
  push_cast at h30_lb h15_lb h10_lb h6_lb h30_ub h1_ub h15_ub h10_ub h6_ub
  unfold chebLog
  constructor <;> linarith

private lemma padicValNat_factorial_eq (p n b : ℕ) (hp : p.Prime) (hnb : Nat.log p n < b) :
    (Nat.factorial n).factorization p = ∑ j ∈ Finset.Ico 1 b, n / p ^ j := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Nat.factorization_def _ hp, padicValNat_factorial hnb]

lemma cheb_dvd_and_lcmUpto (m : ℕ) :
    (Nat.factorial (15 * m) * Nat.factorial (10 * m) * Nat.factorial (6 * m)) ∣
      (Nat.factorial (30 * m) * Nat.factorial m) ∧
    (Nat.factorial (30 * m) * Nat.factorial m) /
      (Nat.factorial (15 * m) * Nat.factorial (10 * m) * Nat.factorial (6 * m)) ∣
      Nat.lcmUpto (30 * m) := by
  set A := Nat.factorial (30 * m) * Nat.factorial m
  set B := Nat.factorial (15 * m) * Nat.factorial (10 * m) * Nat.factorial (6 * m)
  have hA0 : A ≠ 0 := by positivity
  have hB0 : B ≠ 0 := by positivity
  have hBA : B ∣ A := by
    rw [← Nat.factorization_prime_le_iff_dvd hB0 hA0]
    intro p hp
    have hlog1 : Nat.log p (30 * m) < Nat.log p (30 * m) + 1 := Nat.lt_succ_self _
    have hlog15 : Nat.log p (15 * m) < Nat.log p (30 * m) + 1 :=
      (Nat.log_mono_right (by omega)).trans_lt hlog1
    have hlog10 : Nat.log p (10 * m) < Nat.log p (30 * m) + 1 :=
      (Nat.log_mono_right (by omega)).trans_lt hlog1
    have hlog6 : Nat.log p (6 * m) < Nat.log p (30 * m) + 1 :=
      (Nat.log_mono_right (by omega)).trans_lt hlog1
    have hlogm : Nat.log p m < Nat.log p (30 * m) + 1 :=
      (Nat.log_mono_right (by omega)).trans_lt hlog1
    simp only [A, B, Nat.factorization_mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),
      Nat.factorization_mul (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
        (Nat.factorial_ne_zero _),
      Finsupp.coe_add, Pi.add_apply]
    rw [padicValNat_factorial_eq p (30 * m) _ hp hlog1,
        padicValNat_factorial_eq p m _ hp hlogm,
        padicValNat_factorial_eq p (15 * m) _ hp hlog15,
        padicValNat_factorial_eq p (10 * m) _ hp hlog10,
        padicValNat_factorial_eq p (6 * m) _ hp hlog6]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have h2 : 15 * m / p ^ j = (30 * m / p ^ j) / 2 := by
      rw [Nat.div_div_eq_div_mul, mul_comm (p ^ j) 2, ← Nat.div_div_eq_div_mul]
      congr 1; omega
    have h3 : 10 * m / p ^ j = (30 * m / p ^ j) / 3 := by
      rw [Nat.div_div_eq_div_mul, mul_comm (p ^ j) 3, ← Nat.div_div_eq_div_mul]
      congr 1; omega
    have h5 : 6 * m / p ^ j = (30 * m / p ^ j) / 5 := by
      rw [Nat.div_div_eq_div_mul, mul_comm (p ^ j) 5, ← Nat.div_div_eq_div_mul]
      congr 1; omega
    have h30 : m / p ^ j = (30 * m / p ^ j) / 30 := by
      rw [Nat.div_div_eq_div_mul, mul_comm (p ^ j) 30, ← Nat.div_div_eq_div_mul]
      congr 1; omega
    rw [h2, h3, h5, h30]
    exact (f30_bounds (30 * m / p ^ j)).1
  refine ⟨hBA, ?_⟩
  have hQ0 : A / B ≠ 0 := Nat.div_ne_zero_iff.mpr ⟨hB0, Nat.le_of_dvd (Nat.pos_of_ne_zero hA0) hBA⟩
  rw [← Nat.factorization_prime_le_iff_dvd hQ0 (Nat.lcmUpto_ne_zero (30 * m))]
  intro p hp
  rw [Nat.factorization_lcmUpto (30 * m) hp, Nat.factorization_div hBA, Finsupp.coe_tsub, Pi.sub_apply]
  have hlog1 : Nat.log p (30 * m) < Nat.log p (30 * m) + 1 := Nat.lt_succ_self _
  have hlog15 : Nat.log p (15 * m) < Nat.log p (30 * m) + 1 :=
    (Nat.log_mono_right (by omega)).trans_lt hlog1
  have hlog10 : Nat.log p (10 * m) < Nat.log p (30 * m) + 1 :=
    (Nat.log_mono_right (by omega)).trans_lt hlog1
  have hlog6 : Nat.log p (6 * m) < Nat.log p (30 * m) + 1 :=
    (Nat.log_mono_right (by omega)).trans_lt hlog1
  have hlogm : Nat.log p m < Nat.log p (30 * m) + 1 :=
    (Nat.log_mono_right (by omega)).trans_lt hlog1
  simp only [A, B, Nat.factorization_mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),
    Nat.factorization_mul (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
      (Nat.factorial_ne_zero _),
    Finsupp.coe_add, Pi.add_apply]
  rw [padicValNat_factorial_eq p (30 * m) _ hp hlog1,
      padicValNat_factorial_eq p m _ hp hlogm,
      padicValNat_factorial_eq p (15 * m) _ hp hlog15,
      padicValNat_factorial_eq p (10 * m) _ hp hlog10,
      padicValNat_factorial_eq p (6 * m) _ hp hlog6]
  have hsum_le : ∑ j ∈ Finset.Ico 1 (Nat.log p (30 * m) + 1), (30 * m / p ^ j + m / p ^ j) ≤
      (∑ j ∈ Finset.Ico 1 (Nat.log p (30 * m) + 1), (15 * m / p ^ j + 10 * m / p ^ j + 6 * m / p ^ j)) +
      Nat.log p (30 * m) := by
    have hcard : Nat.log p (30 * m) = ∑ _ ∈ Finset.Ico 1 (Nat.log p (30 * m) + 1), 1 := by
      simp [Nat.card_Ico]
    conv_rhs => arg 2; rw [hcard]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have h2 : 15 * m / p ^ j = (30 * m / p ^ j) / 2 := by
      rw [Nat.div_div_eq_div_mul, mul_comm (p ^ j) 2, ← Nat.div_div_eq_div_mul]; congr 1; omega
    have h3 : 10 * m / p ^ j = (30 * m / p ^ j) / 3 := by
      rw [Nat.div_div_eq_div_mul, mul_comm (p ^ j) 3, ← Nat.div_div_eq_div_mul]; congr 1; omega
    have h5 : 6 * m / p ^ j = (30 * m / p ^ j) / 5 := by
      rw [Nat.div_div_eq_div_mul, mul_comm (p ^ j) 5, ← Nat.div_div_eq_div_mul]; congr 1; omega
    have h30 : m / p ^ j = (30 * m / p ^ j) / 30 := by
      rw [Nat.div_div_eq_div_mul, mul_comm (p ^ j) 30, ← Nat.div_div_eq_div_mul]; congr 1; omega
    rw [h2, h3, h5, h30]
    exact (f30_bounds (30 * m / p ^ j)).2
  simp only [Finset.sum_add_distrib] at hsum_le
  omega

lemma chebLog_le_psi (m : ℕ) : chebLog m ≤ Chebyshev.psi (30 * m) := by
  have ⟨hBA, hQ⟩ := cheb_dvd_and_lcmUpto m
  set A := Nat.factorial (30 * m) * Nat.factorial m
  set B := Nat.factorial (15 * m) * Nat.factorial (10 * m) * Nat.factorial (6 * m)
  have hB0 : (B : ℝ) ≠ 0 := by positivity
  have hQ0 : 0 < A / B := Nat.div_pos (Nat.le_of_dvd (by positivity) hBA) (by positivity)
  have hcheb_eq : chebLog m = log ((A / B : ℕ) : ℝ) := by
    unfold chebLog
    rw [Nat.cast_div hBA hB0, log_div (by positivity) hB0]
    simp only [A, B, Nat.cast_mul]
    rw [log_mul (by positivity) (by positivity),
        log_mul (by positivity) (by positivity),
        log_mul (by positivity) (by positivity)]
    ring
  rw [hcheb_eq, show (30 * (m : ℝ)) = ((30 * m : ℕ) : ℝ) by push_cast; ring, Chebyshev.psi_eq_log_lcmUpto]
  exact Real.log_le_log (by exact_mod_cast hQ0) (by exact_mod_cast Nat.le_of_dvd (Nat.lcmUpto_pos _) hQ)

lemma lcmUpto_div_dvd_cheb (m : ℕ) :
    Nat.lcmUpto (5 * m) ∣ Nat.lcmUpto (30 * m) ∧
    Nat.lcmUpto (30 * m) / Nat.lcmUpto (5 * m) ∣
      (Nat.factorial (30 * m) * Nat.factorial m) /
        (Nat.factorial (15 * m) * Nat.factorial (10 * m) * Nat.factorial (6 * m)) := by
  have hdvd : Nat.lcmUpto (5 * m) ∣ Nat.lcmUpto (30 * m) := by
    rw [← Nat.factorization_prime_le_iff_dvd (Nat.lcmUpto_ne_zero _) (Nat.lcmUpto_ne_zero _)]
    intro p hp
    rw [Nat.factorization_lcmUpto (5 * m) hp, Nat.factorization_lcmUpto (30 * m) hp]
    exact Nat.log_mono_right (by omega)
  refine ⟨hdvd, ?_⟩
  have ⟨hBA, _⟩ := cheb_dvd_and_lcmUpto m
  set A := Nat.factorial (30 * m) * Nat.factorial m
  set B := Nat.factorial (15 * m) * Nat.factorial (10 * m) * Nat.factorial (6 * m)
  have hQ0 : A / B ≠ 0 := Nat.div_ne_zero_iff.mpr ⟨by positivity, Nat.le_of_dvd (by positivity) hBA⟩
  have hL0 : Nat.lcmUpto (30 * m) / Nat.lcmUpto (5 * m) ≠ 0 :=
    Nat.div_ne_zero_iff.mpr ⟨Nat.lcmUpto_ne_zero _, Nat.le_of_dvd (Nat.lcmUpto_pos _) hdvd⟩
  rw [← Nat.factorization_prime_le_iff_dvd hL0 hQ0]
  intro p hp
  rw [Nat.factorization_div hdvd, Nat.factorization_div hBA, Finsupp.coe_tsub, Finsupp.coe_tsub,
      Pi.sub_apply, Pi.sub_apply, Nat.factorization_lcmUpto (30 * m) hp,
      Nat.factorization_lcmUpto (5 * m) hp]
  have hlog1 : Nat.log p (30 * m) < Nat.log p (30 * m) + 1 := Nat.lt_succ_self _
  have hlog15 : Nat.log p (15 * m) < Nat.log p (30 * m) + 1 :=
    (Nat.log_mono_right (by omega)).trans_lt hlog1
  have hlog10 : Nat.log p (10 * m) < Nat.log p (30 * m) + 1 :=
    (Nat.log_mono_right (by omega)).trans_lt hlog1
  have hlog6 : Nat.log p (6 * m) < Nat.log p (30 * m) + 1 :=
    (Nat.log_mono_right (by omega)).trans_lt hlog1
  have hlogm : Nat.log p m < Nat.log p (30 * m) + 1 :=
    (Nat.log_mono_right (by omega)).trans_lt hlog1
  simp only [A, B, Nat.factorization_mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),
    Nat.factorization_mul (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
      (Nat.factorial_ne_zero _),
    Finsupp.coe_add, Pi.add_apply]
  rw [padicValNat_factorial_eq p (30 * m) _ hp hlog1,
      padicValNat_factorial_eq p m _ hp hlogm,
      padicValNat_factorial_eq p (15 * m) _ hp hlog15,
      padicValNat_factorial_eq p (10 * m) _ hp hlog10,
      padicValNat_factorial_eq p (6 * m) _ hp hlog6]
  have hlog5_le : Nat.log p (5 * m) ≤ Nat.log p (30 * m) := Nat.log_mono_right (by omega)
  have hsplit : Finset.Ico 1 (Nat.log p (30 * m) + 1) =
      Finset.Ico 1 (Nat.log p (5 * m) + 1) ∪ Finset.Ico (Nat.log p (5 * m) + 1) (Nat.log p (30 * m) + 1) := by
    ext j; simp only [Finset.mem_Ico, Finset.mem_union]; omega
  have hterm_ge : ∀ j ∈ Finset.Ico (Nat.log p (5 * m) + 1) (Nat.log p (30 * m) + 1),
      15 * m / p ^ j + 10 * m / p ^ j + 6 * m / p ^ j + 1 ≤ 30 * m / p ^ j + m / p ^ j := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    have hgt : 5 * m < p ^ j := by
      by_contra hle
      push Not at hle
      have : j ≤ Nat.log p (5 * m) := Nat.le_log_of_pow_le hp.one_lt hle
      omega
    have hle : p ^ j ≤ 30 * m := by
      by_cases hm0 : m = 0
      · subst hm0; simp at hj; omega
      · exact Nat.pow_le_of_le_log (by omega) (by omega)
    have hu1 : 1 ≤ 30 * m / p ^ j := Nat.div_pos hle (pow_pos hp.pos j)
    have hu5 : 30 * m / p ^ j ≤ 5 := by
      rw [Nat.div_le_iff_le_mul_add_pred (pow_pos hp.pos j)]
      omega
    have h2 : 15 * m / p ^ j = (30 * m / p ^ j) / 2 := by
      rw [Nat.div_div_eq_div_mul, mul_comm (p ^ j) 2, ← Nat.div_div_eq_div_mul]; congr 1; omega
    have h3 : 10 * m / p ^ j = (30 * m / p ^ j) / 3 := by
      rw [Nat.div_div_eq_div_mul, mul_comm (p ^ j) 3, ← Nat.div_div_eq_div_mul]; congr 1; omega
    have h5 : 6 * m / p ^ j = (30 * m / p ^ j) / 5 := by
      rw [Nat.div_div_eq_div_mul, mul_comm (p ^ j) 5, ← Nat.div_div_eq_div_mul]; congr 1; omega
    have h30 : m / p ^ j = (30 * m / p ^ j) / 30 := by
      rw [Nat.div_div_eq_div_mul, mul_comm (p ^ j) 30, ← Nat.div_div_eq_div_mul]; congr 1; omega
    rw [h2, h3, h5, h30]
    have h1 := f30_one_of_le_five hu1 hu5
    have h0 := (f30_bounds (30 * m / p ^ j)).1
    omega
  have hterm_nn : ∀ j ∈ Finset.Ico 1 (Nat.log p (30 * m) + 1),
      15 * m / p ^ j + 10 * m / p ^ j + 6 * m / p ^ j ≤ 30 * m / p ^ j + m / p ^ j := by
    intro j _
    have h2 : 15 * m / p ^ j = (30 * m / p ^ j) / 2 := by
      rw [Nat.div_div_eq_div_mul, mul_comm (p ^ j) 2, ← Nat.div_div_eq_div_mul]; congr 1; omega
    have h3 : 10 * m / p ^ j = (30 * m / p ^ j) / 3 := by
      rw [Nat.div_div_eq_div_mul, mul_comm (p ^ j) 3, ← Nat.div_div_eq_div_mul]; congr 1; omega
    have h5 : 6 * m / p ^ j = (30 * m / p ^ j) / 5 := by
      rw [Nat.div_div_eq_div_mul, mul_comm (p ^ j) 5, ← Nat.div_div_eq_div_mul]; congr 1; omega
    have h30 : m / p ^ j = (30 * m / p ^ j) / 30 := by
      rw [Nat.div_div_eq_div_mul, mul_comm (p ^ j) 30, ← Nat.div_div_eq_div_mul]; congr 1; omega
    rw [h2, h3, h5, h30]
    exact (f30_bounds (30 * m / p ^ j)).1
  have hsum_ge : (∑ j ∈ Finset.Ico 1 (Nat.log p (30 * m) + 1), (15 * m / p ^ j + 10 * m / p ^ j + 6 * m / p ^ j)) +
      (Nat.log p (30 * m) - Nat.log p (5 * m)) ≤
      ∑ j ∈ Finset.Ico 1 (Nat.log p (30 * m) + 1), (30 * m / p ^ j + m / p ^ j) := by
    have hcard : Nat.log p (30 * m) - Nat.log p (5 * m) =
        ∑ _ ∈ Finset.Ico (Nat.log p (5 * m) + 1) (Nat.log p (30 * m) + 1), 1 := by
      simp [Nat.card_Ico]
    rw [hsplit, Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive _ _ _),
        Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive _ _ _)]
    have hpart1 : ∑ j ∈ Finset.Ico 1 (Nat.log p (5 * m) + 1), (15 * m / p ^ j + 10 * m / p ^ j + 6 * m / p ^ j) ≤
        ∑ j ∈ Finset.Ico 1 (Nat.log p (5 * m) + 1), (30 * m / p ^ j + m / p ^ j) :=
      Finset.sum_le_sum fun j hj => hterm_nn j (Finset.Ico_subset_Ico_right (by omega) hj)
    have hpart2 : ∑ j ∈ Finset.Ico (Nat.log p (5 * m) + 1) (Nat.log p (30 * m) + 1),
          (15 * m / p ^ j + 10 * m / p ^ j + 6 * m / p ^ j) + (Nat.log p (30 * m) - Nat.log p (5 * m)) ≤
        ∑ j ∈ Finset.Ico (Nat.log p (5 * m) + 1) (Nat.log p (30 * m) + 1), (30 * m / p ^ j + m / p ^ j) := by
      conv_lhs => rw [hcard]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum hterm_ge
    omega
  simp only [Finset.sum_add_distrib] at hsum_ge
  omega

lemma psi_sub_psi_five_le_chebLog (m : ℕ) :
    Chebyshev.psi (30 * m) - Chebyshev.psi (5 * m) ≤ chebLog m := by
  have ⟨hdvd, hdiv⟩ := lcmUpto_div_dvd_cheb m
  have ⟨hBA, _⟩ := cheb_dvd_and_lcmUpto m
  set A := Nat.factorial (30 * m) * Nat.factorial m
  set B := Nat.factorial (15 * m) * Nat.factorial (10 * m) * Nat.factorial (6 * m)
  have hB0 : (B : ℝ) ≠ 0 := by positivity
  have hcheb_eq : chebLog m = log ((A / B : ℕ) : ℝ) := by
    unfold chebLog
    rw [Nat.cast_div hBA hB0, log_div (by positivity) hB0]
    simp only [A, B, Nat.cast_mul]
    rw [log_mul (by positivity) (by positivity),
        log_mul (by positivity) (by positivity),
        log_mul (by positivity) (by positivity)]
    ring
  have hL0 : (Nat.lcmUpto (5 * m) : ℝ) ≠ 0 := by exact_mod_cast Nat.lcmUpto_ne_zero _
  have hL_pos : 0 < Nat.lcmUpto (30 * m) / Nat.lcmUpto (5 * m) :=
    Nat.div_pos (Nat.le_of_dvd (Nat.lcmUpto_pos _) hdvd) (Nat.lcmUpto_pos _)
  rw [hcheb_eq, show (30 * (m : ℝ)) = ((30 * m : ℕ) : ℝ) by push_cast; ring,
      show (5 * (m : ℝ)) = ((5 * m : ℕ) : ℝ) by push_cast; ring,
      Chebyshev.psi_eq_log_lcmUpto, Chebyshev.psi_eq_log_lcmUpto,
      ← log_div (by exact_mod_cast Nat.lcmUpto_ne_zero _) hL0, ← Nat.cast_div hdvd hL0]
  exact Real.log_le_log (by exact_mod_cast hL_pos)
    (by exact_mod_cast Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd (by positivity) hBA) (by positivity)) hdiv)

lemma psi_ge_cheb {x : ℝ} (hx : 30 ≤ x) :
    0.917 * x - 5 * log (x + 1) - 40 ≤ Chebyshev.psi x := by
  set m := ⌊x / 30⌋₊
  have hm1 : 1 ≤ m := Nat.le_floor (by norm_num; linarith)
  have hm_le : (30 * m : ℝ) ≤ x := by
    have := Nat.floor_le (show 0 ≤ x / 30 by linarith)
    linarith
  have hx_lt : x < 30 * ((m : ℝ) + 1) := by
    have := Nat.lt_floor_add_one (x / 30)
    linarith
  have h1 := (chebLog_bounds m hm1).1
  have h2 := chebLog_le_psi m
  have h3 := Chebyshev.psi_mono hm_le
  have hA := chebA_bounds.1
  have hm_pos : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hlog : log (30 * (m : ℝ) + 1) ≤ log (x + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  have hmul : 27.51 * (m : ℝ) ≤ chebA * (m : ℝ) := by nlinarith
  have h27 : 0.917 * x - 27.51 ≤ 27.51 * (m : ℝ) := by linarith
  linarith

lemma psi_le_cheb_nat : ∀ n : ℕ,
    Chebyshev.psi n ≤ 1.107 * (n : ℝ) + 10 * (log ((n : ℝ) + 31)) ^ 2 + 450 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
  by_cases hn180 : n < 180
  · have h1 : Chebyshev.psi n ≤ Chebyshev.psi 180 := Chebyshev.psi_mono (by exact_mod_cast hn180.le)
    have h2 : Chebyshev.psi 180 ≤ Chebyshev.theta 180 + 2 * √180 * log 180 := by
      have := Chebyshev.psi_sub_theta_le (show (1 : ℝ) ≤ 180 by norm_num)
      linarith
    have h3 : Chebyshev.theta 180 ≤ log 4 * 180 :=
      Chebyshev.theta_le_log4_mul_x (by norm_num)
    have hlog4 : log 4 < 1.4 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      have hlog2 : log 2 < 0.7 := lt_trans Real.log_two_lt_d9 (by norm_num)
      norm_num; linarith
    have hlog180 : log 180 < 5.6 := by
      have h180 : (180 : ℝ) < (2 : ℝ) ^ (8 : ℕ) := by norm_num
      have hlog180 : log 180 < 8 * log 2 := by
        calc log 180 < log ((2 : ℝ) ^ (8 : ℕ)) := Real.log_lt_log (by norm_num) h180
          _ = 8 * log 2 := by rw [Real.log_pow]; norm_num
      have hlog2 : log 2 < 0.7 := lt_trans Real.log_two_lt_d9 (by norm_num)
      linarith
    have hsqrt : √180 < 14 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    have h5 : 0 ≤ 1.107 * (n : ℝ) + 10 * (log ((n : ℝ) + 31)) ^ 2 := by positivity
    have h23 : Chebyshev.theta 180 ≤ 1.4 * 180 := by linarith
    have h24 : 2 * √180 * log 180 ≤ 2 * 14 * 5.6 := by nlinarith [Real.sqrt_nonneg 180]
    linarith
  · push Not at hn180
    set m := n / 30 + 1
    have hm1 : 1 ≤ m := Nat.succ_le_succ (Nat.zero_le _)
    have hn_le : n ≤ 30 * m := by omega
    have h5m_lt : 5 * m < n := by omega
    have hstep1 : Chebyshev.psi n ≤ Chebyshev.psi (30 * m) :=
      Chebyshev.psi_mono (by exact_mod_cast hn_le)
    have hstep2 := psi_sub_psi_five_le_chebLog m
    have hstep3 := (chebLog_bounds m hm1).2
    have hA := chebA_bounds.2
    have hih := ih (5 * m) h5m_lt
    have hm_le_R : (30 * m : ℝ) ≤ (n : ℝ) + 30 := by exact_mod_cast (show 30 * m ≤ n + 30 by omega)
    have hlog1 : log (30 * (m : ℝ) + 1) ≤ log ((n : ℝ) + 31) :=
      Real.log_le_log (by positivity) (by linarith)
    have h5m30 : (5 * m : ℝ) + 31 ≤ ((n : ℝ) + 31) / 3 := by
      have : 3 * (5 * m + 31) ≤ n + 31 := by omega
      have hR : (3 : ℝ) * (5 * (m : ℝ) + 31) ≤ (n : ℝ) + 31 := by exact_mod_cast this
      linarith
    have hlog3_lb : 1.09 < log 3 := by
      rw [lt_log_iff_exp_lt (by norm_num)]
      have hexp_ub : exp 1 < (2.72 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
      have hpow : (exp 1) ^ (109 : ℕ) < (3 : ℝ) ^ (100 : ℕ) := by
        calc (exp 1) ^ (109 : ℕ) < (2.72 : ℝ) ^ (109 : ℕ) := by gcongr
          _ < (3 : ℝ) ^ (100 : ℕ) := by norm_num
      have hexp_pow : (exp (1.09 : ℝ)) ^ (100 : ℕ) < (3 : ℝ) ^ (100 : ℕ) := by
        rw [← Real.exp_nat_mul]
        have h109 : (100 : ℕ) * (1.09 : ℝ) = (109 : ℕ) * (1 : ℝ) := by norm_num
        rw [h109, Real.exp_nat_mul]
        exact hpow
      exact lt_of_pow_lt_pow_left₀ 100 (by norm_num) hexp_pow
    have hlog2 : log ((5 * m : ℝ) + 31) ≤ log ((n : ℝ) + 31) - 1.09 := by
      have hle : log ((5 * m : ℝ) + 31) ≤ log (((n : ℝ) + 31) / 3) :=
        Real.log_le_log (by positivity) h5m30
      rw [Real.log_div (by positivity) (by norm_num)] at hle
      linarith
    have hlog_nn : 0 ≤ log ((5 * m : ℝ) + 31) := Real.log_nonneg (by linarith)
    have hlog_n_lb : 4.85 < log ((n : ℝ) + 31) := by
      have hn210 : (2 : ℝ) ^ (7 : ℕ) < (n : ℝ) + 31 := by
        have : (180 : ℝ) ≤ n := by exact_mod_cast hn180
        linarith
      have hlog128 : 7 * log 2 < log ((n : ℝ) + 31) := by
        calc 7 * log 2 = log ((2 : ℝ) ^ (7 : ℕ)) := by rw [Real.log_pow]; norm_num
          _ < log ((n : ℝ) + 31) := Real.log_lt_log (by positivity) hn210
      have hlog2_lb : 0.693 < log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
      linarith
    have hlog_sq : (log ((5 * m : ℝ) + 31)) ^ 2 ≤
        (log ((n : ℝ) + 31)) ^ 2 - 2.18 * log ((n : ℝ) + 31) + 1.2 := by
      have hsq : (log ((5 * m : ℝ) + 31)) ^ 2 ≤ (log ((n : ℝ) + 31) - 1.09) ^ 2 := by
        nlinarith
      linarith
    have hmulA : chebA * (m : ℝ) ≤ 27.655 * (m : ℝ) := by
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith
    have hm_30 : 33.190 * (m : ℝ) ≤ 1.1064 * ((n : ℝ) + 30) := by
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith
    push_cast at hih hstep1 hstep2 hstep3 ⊢
    linarith

lemma psi_le_cheb {x : ℝ} (hx : 0 ≤ x) :
    Chebyshev.psi x ≤ 1.107 * x + 10 * (log (x + 31)) ^ 2 + 450 := by
  rw [Chebyshev.psi_eq_psi_coe_floor]
  have h1 := psi_le_cheb_nat ⌊x⌋₊
  have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have hlog : log ((⌊x⌋₊ : ℝ) + 31) ≤ log (x + 31) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog0 : 0 ≤ log ((⌊x⌋₊ : ℝ) + 31) := Real.log_nonneg (by linarith)
  have hsq : (log ((⌊x⌋₊ : ℝ) + 31)) ^ 2 ≤ (log (x + 31)) ^ 2 := by nlinarith
  linarith

/- ### Module 4: Bounds on `sumX` via Abel summation -/

lemma pNth_ge_add_two (j : ℕ) : j + 2 ≤ pNth j := by
  induction j with
  | zero => exact two_le_pNth 0
  | succ j ih =>
    have hlt : pNth j < pNth (j + 1) := pNth_strictMono (Nat.lt_succ_self j)
    omega

lemma sumX_sub_sumX_bounds {s r : ℕ} (hsr : s ≤ r) :
    ∑ j ∈ Finset.Ico s r, (1 : ℝ) / (pNth j : ℝ) ≤ sumX r - sumX s ∧
    sumX r - sumX s ≤ (∑ j ∈ Finset.Ico s r, (1 : ℝ) / (pNth j : ℝ)) + 1 / ((s : ℝ) + 1) := by
  have hdiff : sumX r - sumX s = ∑ j ∈ Finset.Ico s r, xTerm j := by
    unfold sumX
    rw [← Finset.sum_range_add_sum_Ico xTerm hsr]
    ring
  rw [hdiff]
  constructor
  · refine Finset.sum_le_sum fun j _ => ?_
    unfold xTerm
    apply one_div_le_one_div_of_le (pNth_sub_one_pos j)
    linarith
  · have hstep : ∑ j ∈ Finset.Ico s r, (xTerm j - 1 / (pNth j : ℝ)) ≤ 1 / ((s : ℝ) + 1) := by
      have hterm : ∀ j ∈ Finset.Ico s r,
          xTerm j - 1 / (pNth j : ℝ) ≤ 1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + 2) := by
        intro j _
        unfold xTerm
        have hp2 : (j : ℝ) + 2 ≤ (pNth j : ℝ) := by exact_mod_cast pNth_ge_add_two j
        have hp1 : (j : ℝ) + 1 ≤ (pNth j : ℝ) - 1 := by linarith
        have hpos1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
        have hpos2 : (0 : ℝ) < (pNth j : ℝ) - 1 := pNth_sub_one_pos j
        have hpos3 : (0 : ℝ) < (pNth j : ℝ) := by exact_mod_cast pNth_pos j
        have heq1 : 1 / ((pNth j : ℝ) - 1) - 1 / (pNth j : ℝ) =
            1 / (((pNth j : ℝ) - 1) * (pNth j : ℝ)) := by field_simp; ring
        have heq2 : 1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + 2) =
            1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by field_simp; ring
        rw [heq1, heq2]
        exact one_div_le_one_div_of_le (by positivity) (mul_le_mul hp1 hp2 (by positivity) (by linarith))
      have htele : ∑ j ∈ Finset.Ico s r, (1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + 2)) ≤ 1 / ((s : ℝ) + 1) := by
        have hsum : ∑ j ∈ Finset.Ico s r, (1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + 2)) =
            1 / ((s : ℝ) + 1) - 1 / ((r : ℝ) + 1) := by
          clear hterm hdiff
          induction r with
          | zero =>
            have hs0 : s = 0 := by omega
            subst hs0; simp
          | succ r ih =>
            rcases eq_or_lt_of_le hsr with rfl | hlt
            · simp
            · rw [Finset.sum_Ico_succ_top (by omega), ih (by omega)]
              push_cast
              ring
        rw [hsum]
        have hnonneg : (0 : ℝ) ≤ 1 / ((r : ℝ) + 1) := by positivity
        linarith
      exact (Finset.sum_le_sum hterm).trans htele
    rw [Finset.sum_sub_distrib] at hstep
    linarith

lemma theta_diff_eq (n : ℕ) (hn : 1 ≤ n) :
    Chebyshev.theta (n + 1 : ℕ) - Chebyshev.theta n =
      if (n + 1).Prime then log (n + 1 : ℕ) else 0 := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log]
  by_cases hp : (n + 1).Prime
  · have hset : Nat.primesLE (n + 1) = insert (n + 1) (Nat.primesLE n) := by
      ext p
      simp only [Nat.mem_primesLE, Finset.mem_insert]
      constructor
      · rintro ⟨hle, hp'⟩
        rcases eq_or_lt_of_le hle with rfl | hlt
        · left; rfl
        · right; exact ⟨by omega, hp'⟩
      · rintro (rfl | ⟨hle, hp'⟩)
        · exact ⟨le_rfl, hp⟩
        · exact ⟨by omega, hp'⟩
    have hnot : n + 1 ∉ Nat.primesLE n := by
      intro h
      rw [Nat.mem_primesLE] at h
      omega
    rw [hset, Finset.sum_insert hnot, if_pos hp]
    ring
  · have hset : Nat.primesLE (n + 1) = Nat.primesLE n := by
      ext p
      simp only [Nat.mem_primesLE]
      constructor
      · rintro ⟨hle, hp'⟩
        refine ⟨?_, hp'⟩
        by_contra hgt
        have : p = n + 1 := by omega
        subst this
        exact hp hp'
      · rintro ⟨hle, hp'⟩
        exact ⟨by omega, hp'⟩
    rw [hset, if_neg hp]
    ring

lemma sum_inv_primes_abel {M N : ℕ} (hM : 2 ≤ M) (hMN : M ≤ N) :
    ∑ p ∈ Nat.primesLE N \ Nat.primesLE M, (1 : ℝ) / (p : ℝ) =
      Chebyshev.theta N / ((N : ℝ) * log N) - Chebyshev.theta M / ((M : ℝ) * log M) +
      ∑ n ∈ Finset.Ico M N, Chebyshev.theta n *
        (1 / ((n : ℝ) * log n) - 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1))) := by
  have h1 : ∑ p ∈ Nat.primesLE N \ Nat.primesLE M, (1 : ℝ) / (p : ℝ) =
      ∑ n ∈ Finset.Ico M N, (Chebyshev.theta (n + 1 : ℕ) - Chebyshev.theta n) /
        (((n : ℝ) + 1) * log ((n : ℝ) + 1)) := by
    have hfilt : ∑ p ∈ Nat.primesLE N \ Nat.primesLE M, (1 : ℝ) / (p : ℝ) =
        ∑ n ∈ Finset.Ico M N, if (n + 1).Prime then (1 : ℝ) / ((n + 1 : ℕ) : ℝ) else 0 := by
      rw [← Finset.sum_filter]
      refine Finset.sum_bij (fun p _ => p - 1) ?_ ?_ ?_ ?_
      · intro p hp
        rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE] at hp
        rw [Finset.mem_filter, Finset.mem_Ico]
        push Not at hp
        have hp2 : 2 ≤ p := hp.1.2.two_le
        have hMlt : M < p := by
          by_contra hle
          exact hp.2 (by omega) hp.1.2
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        rw [Nat.sub_add_cancel (by omega)]
        exact hp.1.2
      · intro p₁ hp₁ p₂ hp₂ heq
        rw [Finset.mem_sdiff, Nat.mem_primesLE] at hp₁ hp₂
        have := hp₁.1.2.two_le
        have := hp₂.1.2.two_le
        omega
      · intro n hn
        rw [Finset.mem_filter, Finset.mem_Ico] at hn
        refine ⟨n + 1, ?_, by omega⟩
        rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE]
        push Not
        exact ⟨⟨by omega, hn.2⟩, fun h _ => by omega⟩
      · intro p hp
        rw [Finset.mem_sdiff, Nat.mem_primesLE] at hp
        have hp2 : 2 ≤ p := hp.1.2.two_le
        rw [Nat.sub_add_cancel (by omega)]
    rw [hfilt]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Ico] at hn
    rw [theta_diff_eq n (by omega)]
    split_ifs with hp
    · have hn1 : (1 : ℝ) < (n : ℝ) + 1 := by exact_mod_cast (by omega : 1 < n + 1)
      have hlog : log ((n : ℝ) + 1) ≠ 0 := (Real.log_pos hn1).ne'
      simp only [Nat.cast_add, Nat.cast_one]
      field_simp
    · simp
  rw [h1]
  clear h1
  induction N with
  | zero => omega
  | succ N ih =>
    rcases eq_or_lt_of_le hMN with rfl | hlt
    · simp
    · rw [Finset.sum_Ico_succ_top (by omega), Finset.sum_Ico_succ_top (by omega), ih (by omega)]
      simp only [Nat.cast_add, Nat.cast_one]
      ring

lemma log_log_succ_sub_le (n : ℕ) (hn : 2 ≤ n) :
    log (log ((n : ℝ) + 1)) - log (log n) ≤ 1 / ((n : ℝ) * log n) := by
  have hn_pos : (0 : ℝ) < n := by positivity
  have hlogn : 0 < log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hlogn1 : 0 < log ((n : ℝ) + 1) := Real.log_pos (by exact_mod_cast (by omega : 1 < n + 1))
  have h1 : log (log ((n : ℝ) + 1) / log n) ≤ log ((n : ℝ) + 1) / log n - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hlogn1 hlogn)
  rw [log_div hlogn1.ne' hlogn.ne'] at h1
  have h2 : log ((n : ℝ) + 1) - log n ≤ 1 / (n : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((n : ℝ) + 1) / n by positivity)
    rw [log_div (by positivity) hn_pos.ne'] at h
    have heq : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
    linarith
  have h3 : log ((n : ℝ) + 1) / log n - 1 = (log ((n : ℝ) + 1) - log n) / log n := by
    field_simp
  have h4 : (log ((n : ℝ) + 1) - log n) / log n ≤ (1 / (n : ℝ)) / log n :=
    div_le_div_of_nonneg_right h2 hlogn.le
  have h5 : (1 / (n : ℝ)) / log n = 1 / ((n : ℝ) * log n) := by field_simp
  linarith

lemma le_log_log_succ_sub (n : ℕ) (hn : 2 ≤ n) :
    1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1)) ≤ log (log ((n : ℝ) + 1)) - log (log n) := by
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlogn : 0 < log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hlogn1 : 0 < log ((n : ℝ) + 1) := Real.log_pos (by exact_mod_cast (by omega : 1 < n + 1))
  have h1 : 1 - log n / log ((n : ℝ) + 1) ≤ log (log ((n : ℝ) + 1) / log n) := by
    have h := Real.one_sub_inv_le_log_of_pos (div_pos hlogn1 hlogn)
    rwa [inv_div] at h
  rw [log_div hlogn1.ne' hlogn.ne'] at h1
  have h2 : 1 / ((n : ℝ) + 1) ≤ log ((n : ℝ) + 1) - log n := by
    have hn_pos : (0 : ℝ) < n := by positivity
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < ((n : ℝ) + 1) / n by positivity)
    rw [inv_div, log_div (by positivity) hn_pos.ne'] at h
    have heq : 1 - (n : ℝ) / ((n : ℝ) + 1) = 1 / ((n : ℝ) + 1) := by field_simp; ring
    linarith
  have h3 : 1 - log n / log ((n : ℝ) + 1) = (log ((n : ℝ) + 1) - log n) / log ((n : ℝ) + 1) := by
    field_simp
  have h4 : (1 / ((n : ℝ) + 1)) / log ((n : ℝ) + 1) ≤
      (log ((n : ℝ) + 1) - log n) / log ((n : ℝ) + 1) :=
    div_le_div_of_nonneg_right h2 hlogn1.le
  have h5 : (1 / ((n : ℝ) + 1)) / log ((n : ℝ) + 1) = 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1)) := by
    field_simp
  linarith

lemma sum_Ico_sub_eq (f : ℕ → ℝ) {M N : ℕ} (hMN : M ≤ N) :
    ∑ n ∈ Finset.Ico M N, (f (n + 1) - f n) = f N - f M := by
  induction N with
  | zero =>
    have hM0 : M = 0 := by omega
    subst hM0
    simp
  | succ N ih =>
    rcases eq_or_lt_of_le hMN with rfl | hlt
    · simp
    · rw [Finset.sum_Ico_succ_top (by omega), ih (by omega)]; ring

lemma sum_inv_primes_lb {M N : ℕ} {c : ℝ} (hc : 0 ≤ c) (hM : 3 ≤ M) (hMN : M ≤ N)
    (htheta : ∀ n ∈ Finset.Ico M N, c * (n : ℝ) ≤ Chebyshev.theta n) :
    c * (log (log N) - log (log M) - 1 / (M * log M)) - 1.4 / log M ≤
      ∑ p ∈ Nat.primesLE N \ Nat.primesLE M, (1 : ℝ) / (p : ℝ) := by
  rw [sum_inv_primes_abel (by omega) hMN]
  have hlogM : 0 < log M := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hlogN : 0 < log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hN0 : 0 ≤ Chebyshev.theta N / ((N : ℝ) * log N) :=
    div_nonneg (Chebyshev.theta_nonneg _) (mul_nonneg (Nat.cast_nonneg N) hlogN.le)
  have hM_ub : Chebyshev.theta M / ((M : ℝ) * log M) ≤ 1.4 / log M := by
    have ht : Chebyshev.theta M ≤ log 4 * M := Chebyshev.theta_le_log4_mul_x (by positivity)
    have hlog4 : log 4 < 1.4 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      have hlog2 : log 2 < 0.7 := lt_trans Real.log_two_lt_d9 (by norm_num)
      norm_num; linarith
    have hMpos : (0 : ℝ) < M := by positivity
    have ht14 : Chebyshev.theta M ≤ 1.4 * M := by nlinarith
    rw [div_le_div_iff₀ (by positivity) hlogM]
    exact mul_le_mul_of_nonneg_right ht14 hlogM.le |>.trans_eq (by ring)
  have hdiff_nn : ∀ n ∈ Finset.Ico M N,
      0 ≤ 1 / ((n : ℝ) * log n) - 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1)) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hlogn : 0 < log n := Real.log_pos hn1
    have hlogn1_pos : 0 < log ((n : ℝ) + 1) := Real.log_pos (by exact_mod_cast (by omega : 1 < n + 1))
    have hlogn1 : log n ≤ log ((n : ℝ) + 1) := Real.log_le_log (by linarith) (by linarith)
    rw [sub_nonneg]
    refine one_div_le_one_div_of_le (mul_pos (by linarith) hlogn) ?_
    exact mul_le_mul (by linarith) hlogn1 hlogn.le (by linarith)
  have hsum_ge : ∑ n ∈ Finset.Ico M N,
        c * (n : ℝ) * (1 / ((n : ℝ) * log n) - 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1))) ≤
      ∑ n ∈ Finset.Ico M N, Chebyshev.theta n *
        (1 / ((n : ℝ) * log n) - 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1))) := by
    refine Finset.sum_le_sum fun n hn => ?_
    exact mul_le_mul_of_nonneg_right (htheta n hn) (hdiff_nn n hn)
  have hid : ∀ n ∈ Finset.Ico M N,
      (n : ℝ) * (1 / ((n : ℝ) * log n) - 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1))) =
      (1 / log n - 1 / log ((n : ℝ) + 1)) + 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1)) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hlogn : log n ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
    have hlogn1 : log ((n : ℝ) + 1) ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < n + 1))).ne'
    field_simp
    ring
  have hterm_ge : ∀ n ∈ Finset.Ico M N,
      (log (log ((n : ℝ) + 1)) - log (log n)) -
        (1 / ((n : ℝ) * log n) - 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1))) ≤
      (n : ℝ) * (1 / ((n : ℝ) * log n) - 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1))) := by
    intro n hn
    rw [hid n hn]
    rw [Finset.mem_Ico] at hn
    have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hlogn : 0 < log n := Real.log_pos hn1
    have hlogn1 : log n ≤ log ((n : ℝ) + 1) := Real.log_le_log (by positivity) (by linarith)
    have h1 : 0 ≤ 1 / log n - 1 / log ((n : ℝ) + 1) := by
      rw [sub_nonneg]
      exact one_div_le_one_div_of_le hlogn hlogn1
    have h2 := log_log_succ_sub_le n (by omega)
    linarith
  have htele1 : ∑ n ∈ Finset.Ico M N, (log (log ((n : ℝ) + 1)) - log (log n)) =
      log (log N) - log (log M) := by
    have h := sum_Ico_sub_eq (fun n => log (log (n : ℝ))) hMN
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have htele2 : ∑ n ∈ Finset.Ico M N,
        (1 / ((n : ℝ) * log n) - 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1))) =
      1 / ((M : ℝ) * log M) - 1 / ((N : ℝ) * log N) := by
    have h := sum_Ico_sub_eq (fun n => -(1 / ((n : ℝ) * log n))) hMN
    simpa only [Nat.cast_add, Nat.cast_one, sub_neg_eq_add, neg_add_eq_sub, neg_sub] using h
  have hsum_lb : log (log N) - log (log M) - 1 / ((M : ℝ) * log M) ≤
      ∑ n ∈ Finset.Ico M N, (n : ℝ) *
        (1 / ((n : ℝ) * log n) - 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1))) := by
    have h1 := Finset.sum_le_sum hterm_ge
    rw [Finset.sum_sub_distrib, htele1, htele2] at h1
    have hN_nn : 0 ≤ 1 / ((N : ℝ) * log N) := by positivity
    linarith
  have hmul_lb : c * (log (log N) - log (log M) - 1 / ((M : ℝ) * log M)) ≤
      ∑ n ∈ Finset.Ico M N, c * (n : ℝ) *
        (1 / ((n : ℝ) * log n) - 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1))) := by
    have h2 : ∑ n ∈ Finset.Ico M N, c * (n : ℝ) *
          (1 / ((n : ℝ) * log n) - 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1))) =
        c * ∑ n ∈ Finset.Ico M N, (n : ℝ) *
          (1 / ((n : ℝ) * log n) - 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => by ring
    rw [h2]
    exact mul_le_mul_of_nonneg_left hsum_lb hc
  linarith

lemma sum_inv_primes_ub {M N : ℕ} {c : ℝ} (hc : 0 ≤ c) (hM : 3 ≤ M) (hMN : M ≤ N)
    (htheta : ∀ n ∈ Finset.Ico M (N + 1), Chebyshev.theta n ≤ c * (n : ℝ)) :
    ∑ p ∈ Nat.primesLE N \ Nat.primesLE M, (1 : ℝ) / (p : ℝ) ≤
      c * (log (log N) - log (log M) + 1 / log M) := by
  rw [sum_inv_primes_abel (by omega) hMN]
  have hlogM : 0 < log M := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hlogN : 0 < log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hM0 : 0 ≤ Chebyshev.theta M / ((M : ℝ) * log M) :=
    div_nonneg (Chebyshev.theta_nonneg _) (mul_nonneg (Nat.cast_nonneg M) hlogM.le)
  have hN_ub : Chebyshev.theta N / ((N : ℝ) * log N) ≤ c / log N := by
    have ht := htheta N (Finset.mem_Ico.mpr ⟨hMN, Nat.lt_succ_self N⟩)
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    calc Chebyshev.theta N / ((N : ℝ) * log N)
        ≤ (c * (N : ℝ)) / ((N : ℝ) * log N) :=
          div_le_div_of_nonneg_right ht (mul_nonneg hNpos.le hlogN.le)
      _ = c / log N := by field_simp [hNpos.ne', hlogN.ne']
  have hdiff_nn : ∀ n ∈ Finset.Ico M N,
      0 ≤ 1 / ((n : ℝ) * log n) - 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1)) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hlogn : 0 < log n := Real.log_pos hn1
    have hlogn1 : log n ≤ log ((n : ℝ) + 1) := Real.log_le_log (by linarith) (by linarith)
    rw [sub_nonneg]
    refine one_div_le_one_div_of_le (mul_pos (by linarith) hlogn) ?_
    exact mul_le_mul (by linarith) hlogn1 hlogn.le (by linarith)
  have hsum_le : ∑ n ∈ Finset.Ico M N, Chebyshev.theta n *
        (1 / ((n : ℝ) * log n) - 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1))) ≤
      ∑ n ∈ Finset.Ico M N,
        c * (n : ℝ) * (1 / ((n : ℝ) * log n) - 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1))) := by
    refine Finset.sum_le_sum fun n hn => ?_
    have hn' := Finset.mem_Ico.mp hn
    exact mul_le_mul_of_nonneg_right (htheta n (Finset.mem_Ico.mpr ⟨hn'.1, by omega⟩)) (hdiff_nn n hn)
  have hid : ∀ n ∈ Finset.Ico M N,
      (n : ℝ) * (1 / ((n : ℝ) * log n) - 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1))) =
      (1 / log n - 1 / log ((n : ℝ) + 1)) + 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1)) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hlogn : log n ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
    have hlogn1 : log ((n : ℝ) + 1) ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < n + 1))).ne'
    field_simp
    ring
  have hterm_le : ∀ n ∈ Finset.Ico M N,
      (n : ℝ) * (1 / ((n : ℝ) * log n) - 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1))) ≤
      (1 / log n - 1 / log ((n : ℝ) + 1)) + (log (log ((n : ℝ) + 1)) - log (log n)) := by
    intro n hn
    rw [hid n hn]
    rw [Finset.mem_Ico] at hn
    linarith [le_log_log_succ_sub n (by omega)]
  have htele1 : ∑ n ∈ Finset.Ico M N, (1 / log n - 1 / log ((n : ℝ) + 1)) =
      1 / log M - 1 / log N := by
    have h := sum_Ico_sub_eq (fun n => -(1 / log (n : ℝ))) hMN
    simpa only [Nat.cast_add, Nat.cast_one, sub_neg_eq_add, neg_add_eq_sub, neg_sub] using h
  have htele2 : ∑ n ∈ Finset.Ico M N, (log (log ((n : ℝ) + 1)) - log (log n)) =
      log (log N) - log (log M) := by
    have h := sum_Ico_sub_eq (fun n => log (log (n : ℝ))) hMN
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hsum_ub : ∑ n ∈ Finset.Ico M N, (n : ℝ) *
        (1 / ((n : ℝ) * log n) - 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1))) ≤
      1 / log M - 1 / log N + (log (log N) - log (log M)) := by
    have h1 := Finset.sum_le_sum hterm_le
    rw [Finset.sum_add_distrib, htele1, htele2] at h1
    exact h1
  have hmul_ub : ∑ n ∈ Finset.Ico M N, c * (n : ℝ) *
        (1 / ((n : ℝ) * log n) - 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1))) ≤
      c * (1 / log M - 1 / log N + (log (log N) - log (log M))) := by
    have h2 : ∑ n ∈ Finset.Ico M N, c * (n : ℝ) *
          (1 / ((n : ℝ) * log n) - 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1))) =
        c * ∑ n ∈ Finset.Ico M N, (n : ℝ) *
          (1 / ((n : ℝ) * log n) - 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => by ring
    rw [h2]
    exact mul_le_mul_of_nonneg_left hsum_ub hc
  have hring : c / log N + c * (1 / log M - 1 / log N + (log (log N) - log (log M))) =
      c * (log (log N) - log (log M) + 1 / log M) := by ring
  linarith

/- ### Module 4b: Pocklington primality and moderate-k (`21 ≤ k ≤ 1500`) -/

def fastModPowFuel (f a e m : ℕ) : ℕ :=
  match f with
  | 0 => 1 % m
  | f + 1 =>
    if e = 0 then 1 % m
    else
      let h := fastModPowFuel f a (e / 2) m
      let sq := (h * h) % m
      if e % 2 = 0 then sq else (sq * a) % m

lemma fastModPowFuel_eq (f a e m : ℕ) (he : e < 2 ^ f) :
    fastModPowFuel f a e m = (a ^ e) % m := by
  induction f generalizing e with
  | zero =>
    have he0 : e = 0 := by omega
    subst he0; simp [fastModPowFuel]
  | succ f ih =>
    unfold fastModPowFuel
    by_cases he0 : e = 0
    · subst he0; simp
    · simp only [he0, ↓reduceIte]
      have hlt : e / 2 < 2 ^ f := by
        rw [Nat.pow_succ] at he
        omega
      rw [ih (e / 2) hlt]
      have hsq : ((a ^ (e / 2) % m) * (a ^ (e / 2) % m)) % m = (a ^ (2 * (e / 2))) % m := by
        rw [← Nat.mul_mod, ← pow_add, show e / 2 + e / 2 = 2 * (e / 2) by omega]
      rw [hsq]
      by_cases he2 : e % 2 = 0
      · simp only [he2, ↓reduceIte]
        congr 2; omega
      · simp only [he2, ↓reduceIte]
        rw [Nat.mod_mul_mod, ← pow_succ, show 2 * (e / 2) + 1 = e by omega]

lemma pocklington_step (p q a : ℕ) (hp : 1 < p) (hq : q.Prime) (hqd : q ∣ p - 1)
    (hp_lt : p - 1 < 2 ^ 65)
    (hpow : fastModPowFuel 65 a (p - 1) p = 1)
    (hgcd : Nat.gcd (fastModPowFuel 65 a ((p - 1) / q) p - 1) p = 1) :
    ∀ r : ℕ, r.Prime → r ∣ p → q ∣ r - 1 := by
  intro r hr hrp
  haveI : Fact r.Prime := ⟨hr⟩
  have hpow' : (a ^ (p - 1)) % p = 1 := by rwa [← fastModPowFuel_eq 65 a (p - 1) p hp_lt]
  have hdiv_lt : (p - 1) / q < 2 ^ 65 := lt_of_le_of_lt (Nat.div_le_self _ _) hp_lt
  have hmod_pos : 1 ≤ fastModPowFuel 65 a ((p - 1) / q) p := by
    by_contra h0
    have hz : fastModPowFuel 65 a ((p - 1) / q) p = 0 := by omega
    rw [hz] at hgcd
    simp at hgcd
    omega
  have hgcd' : Nat.gcd (a ^ ((p - 1) / q) - 1) p = 1 := by
    have hmod_eq : fastModPowFuel 65 a ((p - 1) / q) p = (a ^ ((p - 1) / q)) % p :=
      fastModPowFuel_eq 65 _ _ _ hdiv_lt
    have hpos : 1 ≤ a ^ ((p - 1) / q) := by
      by_contra h0
      have hz : a ^ ((p - 1) / q) = 0 := by omega
      rw [hz, Nat.zero_mod] at hmod_eq
      omega
    have hsub : (a ^ ((p - 1) / q) - 1) % p = (fastModPowFuel 65 a ((p - 1) / q) p - 1) % p := by
      rw [hmod_eq]
      have hle : a ^ ((p - 1) / q) % p ≤ a ^ ((p - 1) / q) := Nat.mod_le _ _
      have h1 : (a ^ ((p - 1) / q) - 1) = (a ^ ((p - 1) / q) % p - 1) + p * (a ^ ((p - 1) / q) / p) := by
        have := Nat.div_add_mod (a ^ ((p - 1) / q)) p
        omega
      rw [h1, Nat.add_mul_mod_self_left]
    rw [Nat.gcd_comm _ p, Nat.gcd_rec p _, hsub, ← Nat.gcd_rec p _, Nat.gcd_comm p _, hgcd]
  have ha_mod : (a : ZMod r) ^ (p - 1) = 1 := by
    have h1 : a ^ (p - 1) = (a ^ (p - 1) / p) * p + a ^ (p - 1) % p := (Nat.div_add_mod' _ _).symm
    have h2 : ((a ^ (p - 1) : ℕ) : ZMod r) = ((1 : ℕ) : ZMod r) := by
      rw [h1, hpow']
      have hdvd : (p : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff p r).mpr hrp
      simp [hdvd]
    simpa using h2
  have ha_sub_ne : (a : ZMod r) ^ ((p - 1) / q) ≠ 1 := by
    intro heq
    have hpos : 1 ≤ a ^ ((p - 1) / q) := by
      by_contra h0
      have hzero : a ^ ((p - 1) / q) = 0 := by omega
      have hzero' : ((a ^ ((p - 1) / q) : ℕ) : ZMod r) = 0 := by rw [hzero, Nat.cast_zero]
      push_cast at hzero'
      rw [hzero'] at heq
      exact zero_ne_one heq
    have hdvd_r : r ∣ a ^ ((p - 1) / q) - 1 := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hpos, Nat.cast_pow, Nat.cast_one, heq, sub_self]
    have hdvd_gcd : r ∣ Nat.gcd (a ^ ((p - 1) / q) - 1) p := Nat.dvd_gcd hdvd_r hrp
    rw [hgcd'] at hdvd_gcd
    exact hr.not_dvd_one hdvd_gcd
  have hord_dvd : orderOf (a : ZMod r) ∣ p - 1 := orderOf_dvd_iff_pow_eq_one.mpr ha_mod
  have hord_ndvd : ¬ orderOf (a : ZMod r) ∣ (p - 1) / q := by
    intro hdvd
    exact ha_sub_ne (orderOf_dvd_iff_pow_eq_one.mp hdvd)
  have hq_dvd_ord : q ∣ orderOf (a : ZMod r) := by
    have hmul : q * ((p - 1) / q) = p - 1 := Nat.mul_div_cancel' hqd
    rw [← hmul] at hord_dvd
    by_contra hnq
    have hcop : Nat.Coprime q (orderOf (a : ZMod r)) := hq.coprime_iff_not_dvd.mpr hnq
    exact hord_ndvd (hcop.symm.dvd_of_dvd_mul_left hord_dvd)
  have ha_ne0 : (a : ZMod r) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at ha_mod
    exact zero_ne_one ha_mod
  have hflt : (a : ZMod r) ^ (r - 1) = 1 := ZMod.pow_card_sub_one_eq_one ha_ne0
  have hord_dvd_r : orderOf (a : ZMod r) ∣ r - 1 := orderOf_dvd_iff_pow_eq_one.mpr hflt
  exact hq_dvd_ord.trans hord_dvd_r

lemma pocklington_one (p q a : ℕ) (hp : 1 < p) (hq : q.Prime) (hqd : q ∣ p - 1)
    (hsq : p < q * q) (hp_lt : p - 1 < 2 ^ 65)
    (hpow : fastModPowFuel 65 a (p - 1) p = 1)
    (hgcd : Nat.gcd (fastModPowFuel 65 a ((p - 1) / q) p - 1) p = 1) : p.Prime := by
  by_contra hnp
  have hr_prime : p.minFac.Prime := Nat.minFac_prime (by omega)
  have hr_dvd : p.minFac ∣ p := Nat.minFac_dvd p
  have hr_sq : p.minFac * p.minFac ≤ p := by
    have := Nat.minFac_sq_le_self (by omega) hnp
    rwa [sq] at this
  have hqr : q ∣ p.minFac - 1 :=
    pocklington_step p q a hp hq hqd hp_lt hpow hgcd p.minFac hr_prime hr_dvd
  have hpos : 0 < p.minFac - 1 := by have := hr_prime.two_le; omega
  have hq_le : q ≤ p.minFac - 1 := Nat.le_of_dvd hpos hqr
  have hq_lt : q < p.minFac := by omega
  have hqq : q * q < p.minFac * p.minFac := Nat.mul_lt_mul'' hq_lt hq_lt
  omega

lemma pocklington_two (p q₁ q₂ a₁ a₂ : ℕ) (hp : 1 < p) (hq₁ : q₁.Prime) (hq₂ : q₂.Prime)
    (hne : q₁ ≠ q₂) (hqd₁ : q₁ ∣ p - 1) (hqd₂ : q₂ ∣ p - 1)
    (hsq : p < (q₁ * q₂) * (q₁ * q₂)) (hp_lt : p - 1 < 2 ^ 65)
    (hpow₁ : fastModPowFuel 65 a₁ (p - 1) p = 1)
    (hgcd₁ : Nat.gcd (fastModPowFuel 65 a₁ ((p - 1) / q₁) p - 1) p = 1)
    (hpow₂ : fastModPowFuel 65 a₂ (p - 1) p = 1)
    (hgcd₂ : Nat.gcd (fastModPowFuel 65 a₂ ((p - 1) / q₂) p - 1) p = 1) :
    p.Prime := by
  by_contra hnp
  have hr_prime : p.minFac.Prime := Nat.minFac_prime (by omega)
  have hr_dvd : p.minFac ∣ p := Nat.minFac_dvd p
  have hr_sq : p.minFac * p.minFac ≤ p := by
    have := Nat.minFac_sq_le_self (by omega) hnp
    rwa [sq] at this
  have hd₁ : q₁ ∣ p.minFac - 1 :=
    pocklington_step p q₁ a₁ hp hq₁ hqd₁ hp_lt hpow₁ hgcd₁ p.minFac hr_prime hr_dvd
  have hd₂ : q₂ ∣ p.minFac - 1 :=
    pocklington_step p q₂ a₂ hp hq₂ hqd₂ hp_lt hpow₂ hgcd₂ p.minFac hr_prime hr_dvd
  have hcop : Nat.Coprime q₁ q₂ := (Nat.coprime_primes hq₁ hq₂).mpr hne
  have hd12 : q₁ * q₂ ∣ p.minFac - 1 := hcop.mul_dvd_of_dvd_of_dvd hd₁ hd₂
  have hpos : 0 < p.minFac - 1 := by have := hr_prime.two_le; omega
  have hle : q₁ * q₂ ≤ p.minFac - 1 := Nat.le_of_dvd hpos hd12
  have hlt : q₁ * q₂ < p.minFac := by omega
  have hqq : (q₁ * q₂) * (q₁ * q₂) < p.minFac * p.minFac := Nat.mul_lt_mul'' hlt hlt
  omega

set_option maxRecDepth 4096 in
lemma prime_18361375334787046697 : Nat.Prime 18361375334787046697 := by
  have h13781 : Nat.Prime 13781 := by norm_num
  have h50548709 : Nat.Prime 50548709 :=
    pocklington_one 50548709 13781 2 (by decide) h13781 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h997 : Nat.Prime 997 := by norm_num
  have h67 : Nat.Prime 67 := by norm_num
  have h13626997 : Nat.Prime 13626997 :=
    pocklington_two 13626997 997 67 2 2 (by decide) h997 h67 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h2295171916848380837 : Nat.Prime 2295171916848380837 :=
    pocklington_two 2295171916848380837 50548709 13626997 2 2 (by decide) h50548709 h13626997
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact pocklington_one 18361375334787046697 2295171916848380837 2 (by decide)
    h2295171916848380837 (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 4096 in
lemma prime_18361375334787048247 : Nat.Prime 18361375334787048247 := by
  have h5939 : Nat.Prime 5939 := by norm_num
  have h1330337 : Nat.Prime 1330337 :=
    pocklington_one 1330337 5939 2 (by decide) h5939 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h150149815843 : Nat.Prime 150149815843 :=
    pocklington_one 150149815843 1330337 2 (by decide) h1330337 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h72862600534869239 : Nat.Prime 72862600534869239 :=
    pocklington_one 72862600534869239 150149815843 2 (by decide) h150149815843 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h1020076407488169347 : Nat.Prime 1020076407488169347 :=
    pocklington_one 1020076407488169347 72862600534869239 2 (by decide) h72862600534869239 (by decide) (by decide) (by decide) (by decide) (by decide)
  exact pocklington_one 18361375334787048247 1020076407488169347 2 (by decide)
    h1020076407488169347 (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 4096 in
lemma prime_18361375334787054929 : Nat.Prime 18361375334787054929 := by
  have h31337 : Nat.Prime 31337 := by norm_num
  have h81789571 : Nat.Prime 81789571 :=
    pocklington_one 81789571 31337 2 (by decide) h31337 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h817895711 : Nat.Prime 817895711 :=
    pocklington_one 817895711 81789571 2 (by decide) h81789571 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h17550406166639 : Nat.Prime 17550406166639 :=
    pocklington_one 17550406166639 817895711 2 (by decide) h817895711 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h1147585958424190933 : Nat.Prime 1147585958424190933 :=
    pocklington_one 1147585958424190933 17550406166639 2 (by decide) h17550406166639 (by decide) (by decide) (by decide) (by decide) (by decide)
  exact pocklington_one 18361375334787054929 1147585958424190933 2 (by decide)
    h1147585958424190933 (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 4096 in
lemma prime_18361375334787054931 : Nat.Prime 18361375334787054931 := by
  have h21911 : Nat.Prime 21911 := by norm_num
  have h15118591 : Nat.Prime 15118591 :=
    pocklington_one 15118591 21911 2 (by decide) h21911 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h21770771041 : Nat.Prime 21770771041 :=
    pocklington_one 21770771041 15118591 2 (by decide) h15118591 (by decide) (by decide) (by decide) (by decide) (by decide)
  exact pocklington_one 18361375334787054931 21770771041 2 (by decide)
    h21770771041 (by decide) (by decide) (by decide) (by decide) (by decide)

def witList1550 : List ℕ :=
  [19, 3, 127, 5, 3, 7, 53, 3, 5, 67, 3, 73, 7, 3, 11, 248903, 3, 43, 5, 3, 17, 1039, 3, 5, 41, 3, 7, 31, 3, 13, 923177, 3, 77153, 5, 3, 2423588549, 11, 3, 5, 23, 3, 252029, 13, 3, 109, 29, 3, 7, 5, 3, 47, 16811, 3, 5, 7, 3, 61687, 19, 3, 37, 43, 3, 23, 5, 3, 41, 2151691249, 3, 5, 11, 3, 17, 167, 3, 29, 7, 3, 30869, 5, 3, 11, 13, 3, 5, 73, 3, 389, 138797, 3, 7, 107, 3, 62231947, 5, 3, 19, 7, 3, 5, 75659, 3, 34057, 11, 3, 97, 17, 3, 13, 5, 3, 7, 8087, 3, 5, 19, 3, 379, 7, 3, 211, 13, 3, 17, 5, 3, 571, 137, 3, 5, 71, 3, 7, 29, 3, 1132601, 11, 3, 9817, 5, 3, 79, 743, 3, 5, 47, 3, 11, 41, 3, 223, 397, 3, 7, 5, 3, 281, 17, 3, 5, 7, 3, 29, 80309, 3, 457, 53, 3, 61, 5, 3, 37, 19, 3, 5, 10477367, 3, 10039, 23, 3, 11, 7, 3, 31, 5, 3, 13, 2040781, 3, 5, 43, 3, 47, 4993, 3, 7, 1768343, 3, 107, 5, 3, 23, 7, 3, 5, 241, 3, 342865651, 17, 3, 19, 67, 3, 11, 5, 3, 7, 16631, 3, 5, 29, 3, 449, 7, 3, 13, 32779, 3, 761, 5, 3, 73, 4271039, 3, 5, 11, 3, 7, 13, 3, 167, 515149, 3, 271, 5, 3, 11, 23, 3, 5, 21317, 3, 353, 1699, 3, 227, 1307, 3, 7, 5, 3, 199, 1949, 3, 5, 7, 3, 19, 11, 3, 23, 41, 3, 1097, 5, 3, 17, 13, 3, 5, 191, 3, 37, 530265059, 3, 81875083, 7, 3, 93463, 5, 3, 5417, 1051, 3, 5, 619, 3, 491, 5692007, 3, 7, 11, 3, 13, 5, 3, 29881, 7, 3, 5, 17, 3, 11, 607, 3, 103, 13, 3, 14175494029, 5, 3, 7, 59, 3, 5, 53, 3, 17, 7, 3, 1061, 211, 3, 47, 5, 3, 29, 89, 3, 5, 139, 3, 7, 19, 3, 11, 163, 3, 1005559123, 5, 3, 61, 5381, 3, 5, 13, 3, 21577, 401, 3, 122849, 17, 3, 7, 5, 3, 20681, 11, 3, 5, 7, 3, 109, 223, 3, 383, 151, 3, 11, 5, 3, 13, 257, 3, 5, 23, 3, 62140422737, 2377, 3, 9923791, 7, 3, 37, 5, 3, 97, 4391, 3, 5, 11, 3, 229, 751, 3, 7, 8053, 3, 23, 5, 3, 11, 7, 3, 5, 3581, 3, 1553, 103, 3, 13, 375259, 3, 29, 5, 3, 7, 47, 3, 5, 37, 3, 27847, 7, 3, 41, 367, 3, 19, 5, 3, 1187, 1103, 3, 5, 863, 3, 7, 43, 3, 73, 563, 3, 101749, 5, 3, 1489, 19, 3, 5, 199, 3, 31, 17, 3, 774583, 11, 3, 7, 5, 3, 191, 13, 3, 5, 7, 3, 11, 15497, 3, 17, 29, 3, 232207, 5, 3, 17851283, 179, 3, 5, 80683, 3, 1283, 31, 3, 19, 7, 3, 13, 5, 3, 173, 69046811, 3, 5, 929, 3, 113, 59197, 3, 7, 13, 3, 2050992091, 5, 3, 83, 7, 3, 5, 1303, 3, 82307, 23, 3, 16741, 115128217, 3, 148411, 5, 3, 7, 11, 3, 5, 247381, 3, 13, 7, 3, 701, 37, 3, 11, 5, 3, 23, 12423539, 3, 5, 13, 3, 7, 208511, 3, 31, 71, 3, 41, 5, 3, 443, 21061, 3, 5, 11, 3, 499, 29, 3, 757, 19, 3, 7, 5, 3, 11, 43, 3, 5, 7, 3, 17, 442837, 3, 101, 31, 3, 1360309, 5, 3, 36739, 23, 3, 5, 61, 3, 29, 11, 3, 240725279, 7, 3, 283, 5, 3, 239893, 10513, 3, 5, 1321, 3, 1627, 67, 3, 7, 17, 3, 139, 5, 3, 953, 7, 3, 5, 12277, 3, 71, 13, 3, 3023, 11, 3, 17, 5, 3, 7, 3975661931, 3, 5, 41, 3, 11, 7, 3, 1237, 3731909, 3, 31, 5, 3, 582719, 37, 3, 5, 29, 3, 7, 276821, 3, 697469711, 23, 3, 43, 5, 3, 19, 13, 3, 5, 12812347, 3, 163, 17383, 3, 11, 59, 3, 7, 5, 3, 41, 83, 3, 5, 7, 3, 97, 1009, 3, 2801, 883, 3, 13, 5, 3, 53, 11, 3, 5, 7549, 3, 523, 1031, 3, 38609, 7, 3, 11, 5, 3, 125687, 8263, 3, 5, 10181, 3, 61, 17, 3, 7, 17667239, 3, 19, 5, 3, 37, 7, 3, 5, 11, 3, 13, 107, 3, 17, 6203, 3, 157, 5, 3, 7, 19, 3, 5, 13, 3, 67, 7, 3, 3119, 3491029, 3, 23, 5, 3, 47, 139, 3, 5, 71387, 3, 7, 11, 3, 83, 11329, 3, 2683, 5, 3, 13, 31, 3, 5]

set_option maxRecDepth 4096 in
lemma witList1550_valid :
    (List.range 774).all (fun i =>
      let w := witList1550.getD i 2
      decide (1 < w ∧ w < 18361375334787046699 + 2 * i ∧ (18361375334787046699 + 2 * i) % w = 0)) = true := by
  decide

lemma gap_1836_no_prime (n : ℕ) (h1 : 18361375334787046697 < n)
    (h2 : n < 18361375334787048247) : ¬ n.Prime := by
  intro hp
  rcases hp.eq_two_or_odd with rfl | hodd
  · omega
  · set i := (n - 18361375334787046699) / 2
    have hi : i < 774 := by omega
    have hn_eq : n = 18361375334787046699 + 2 * i := by omega
    have hvalid := List.all_eq_true.mp witList1550_valid i (List.mem_range.mpr hi)
    simp only [decide_eq_true_eq] at hvalid
    set w := witList1550.getD i 2
    have hdvd : w ∣ n := Nat.dvd_of_mod_eq_zero (hn_eq ▸ hvalid.2.2)
    have hnot : ¬ (w = 1 ∨ w = n) := by omega
    exact hnot ((Nat.dvd_prime hp).mp hdvd)

lemma pNth_consecutive_of_no_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hgap : ∀ n, p < n → n < q → ¬ n.Prime) :
    pNth (Nat.count Nat.Prime p + 1) = q := by
  set a := Nat.count Nat.Prime p
  have hpa : pNth a = p := Nat.nth_count hp
  have hlt : p < pNth (a + 1) := by rw [← hpa]; exact pNth_strictMono (Nat.lt_succ_self a)
  have hle : pNth (a + 1) ≤ q := by
    have hcount_lt : a < Nat.count Nat.Prime q := by
      unfold pNth at hpa
      rw [← pNth_strictMono.lt_iff_lt]
      unfold pNth
      rw [hpa, Nat.nth_count hq]
      exact hpq
    calc pNth (a + 1) ≤ pNth (Nat.count Nat.Prime q) := pNth_strictMono.monotone (by omega)
      _ = q := Nat.nth_count hq
  by_contra hne
  exact hgap (pNth (a + 1)) hlt (lt_of_le_of_ne hle hne) (pNth_prime (a + 1))

lemma primesLE_eq_image_pNth (N : ℕ) :
    Nat.primesLE N = (Finset.range (Nat.primeCounting N)).image pNth := by
  ext p
  simp only [Nat.mem_primesLE, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨hpN, hp⟩
    refine ⟨Nat.count Nat.Prime p, ?_, Nat.nth_count hp⟩
    change Nat.count Nat.Prime p < Nat.count Nat.Prime (N + 1)
    have hlt : Nat.count Nat.Prime p < Nat.count Nat.Prime (p + 1) := by
      rw [Nat.count_succ, if_pos hp]
      omega
    exact hlt.trans_le (Nat.count_monotone Nat.Prime (by omega))
  · rintro ⟨j, hj, rfl⟩
    refine ⟨?_, pNth_prime j⟩
    change j < Nat.count Nat.Prime (N + 1) at hj
    have hlt : pNth j < N + 1 := Nat.nth_lt_of_lt_count hj
    omega

lemma sumX_primeCounting (N : ℕ) :
    sumX (Nat.primeCounting N) = ∑ p ∈ Nat.primesLE N, (1 : ℝ) / ((p : ℝ) - 1) := by
  unfold sumX
  rw [primesLE_eq_image_pNth, Finset.sum_image]
  · refine Finset.sum_congr rfl fun j _ => rfl
  · intro i _ j _ hij
    exact pNth_strictMono.injective hij

set_option maxRecDepth 16384 in
lemma primeCounting_97 : Nat.primeCounting 97 = 25 := by decide

set_option maxRecDepth 16384 in
lemma primesLE_97_eq : Nat.primesLE 97 =
    {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97} := by
  decide

lemma sumX_25_ub : sumX 25 ≤ 2.58 := by
  rw [← primeCounting_97, sumX_primeCounting, primesLE_97_eq]
  norm_num

lemma log_le_add_four_sqrt_sqrt {x M : ℝ} (hM : 0 < M) (hx : M ≤ x) :
    log x ≤ log M + 4 * √(√(x / M)) - 4 := by
  have hx0 : 0 < x := lt_of_lt_of_le hM hx
  have hy_pos : 0 < √(√(x / M)) := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (div_pos hx0 hM))
  have h1 : log (√(√(x / M))) ≤ √(√(x / M)) - 1 := Real.log_le_sub_one_of_pos hy_pos
  have hpow : (√(√(x / M))) ^ (4 : ℕ) = x / M := by
    have hsq1 : (√(√(x / M))) ^ (2 : ℕ) = √(x / M) :=
      Real.sq_sqrt (Real.sqrt_nonneg _)
    have hsq2 : (√(x / M)) ^ (2 : ℕ) = x / M :=
      Real.sq_sqrt (div_nonneg hx0.le hM.le)
    calc (√(√(x / M))) ^ (4 : ℕ) = ((√(√(x / M))) ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      _ = (√(x / M)) ^ (2 : ℕ) := by rw [hsq1]
      _ = x / M := hsq2
  have hlog_eq : log (x / M) = 4 * log (√(√(x / M))) := by
    conv_lhs => rw [← hpow, Real.log_pow]
    norm_num
  rw [Real.log_div hx0.ne' hM.ne'] at hlog_eq
  linarith

lemma theta_ge_080 {n : ℕ} (hn : 40000 ≤ n) :
    0.80 * (n : ℝ) ≤ Chebyshev.theta n := by
  have hnR : (40000 : ℝ) ≤ n := by exact_mod_cast hn
  have hpsi := psi_ge_cheb (show (30 : ℝ) ≤ n by linarith)
  have hsub := Chebyshev.psi_sub_theta_le (show (1 : ℝ) ≤ n by linarith)
  have hlog40k : log 40000 < 11 := by
    rw [log_lt_iff_lt_exp (by norm_num)]
    calc (40000 : ℝ) < (2.71828 : ℝ) ^ (11 : ℕ) := by norm_num
      _ < (exp 1) ^ (11 : ℕ) := by gcongr; exact lt_trans (by norm_num) Real.exp_one_gt_d9
      _ = exp 11 := by rw [← Real.exp_nat_mul]; norm_num
  have hlog_n : log n ≤ 7 + 4 * √(√((n : ℝ) / 40000)) := by
    have h := log_le_add_four_sqrt_sqrt (show (0 : ℝ) < 40000 by norm_num) hnR
    linarith
  have hsqrt_le : √(√((n : ℝ) / 40000)) ≤ √((n : ℝ) / 40000) := by
    have h1 : 1 ≤ (n : ℝ) / 40000 := by linarith
    have h2 : 1 ≤ √((n : ℝ) / 40000) := Real.one_le_sqrt.mpr h1
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hsqrt_div : √((n : ℝ) / 40000) = √n / 200 := by
    rw [Real.sqrt_div (by linarith), show √40000 = 200 by
      rw [show (40000 : ℝ) = 200 ^ (2 : ℕ) by norm_num, Real.sqrt_sq (by norm_num)]]
  have hsqrt_n : 200 ≤ √n := by
    rw [show (200 : ℝ) = √40000 by
      rw [show (40000 : ℝ) = 200 ^ (2 : ℕ) by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hnR
  have hsq_n : √n * √n = n := Real.mul_self_sqrt (by linarith)
  have h2sqrt : 2 * √n * log n ≤ 0.11 * n := by
    have h1 : 2 * √n * log n ≤ 2 * √n * (7 + 4 * (√n / 200)) := by
      refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    calc 2 * √n * log n ≤ 2 * √n * (7 + 4 * (√n / 200)) := h1
      _ = 14 * √n + 0.04 * (√n * √n) := by ring
      _ ≤ 14 * (√n * (√n / 200)) + 0.04 * n := by
          rw [hsq_n]
          have : 1 ≤ √n / 200 := by linarith
          nlinarith [Real.sqrt_nonneg n]
      _ = 0.07 * (√n * √n) + 0.04 * n := by ring
      _ = 0.11 * n := by rw [hsq_n]; ring
  have hlog_n1 : 5 * log ((n : ℝ) + 1) ≤ 0.005 * n := by
    have hn1_le : (n : ℝ) + 1 ≤ 2 * n := by linarith
    have hlog1 : log ((n : ℝ) + 1) ≤ log (2 * n) := Real.log_le_log (by linarith) hn1_le
    have hlog2 : log (2 * n) = log 2 + log n := Real.log_mul (by norm_num) (by linarith)
    have hlog2_ub : log 2 < 0.7 := lt_trans Real.log_two_lt_d9 (by norm_num)
    have h1 : log n ≤ 7 + 4 * (√n / 200) := by linarith
    have h2 : √n ≤ n / 200 := by
      calc √n = √n * 1 := by ring
        _ ≤ √n * (√n / 200) := by nlinarith [Real.sqrt_nonneg n]
        _ = (√n * √n) / 200 := by ring
        _ = n / 200 := by rw [hsq_n]
    linarith
  linarith

lemma theta_ge_090 {n : ℕ} (hn : 10000000 ≤ n) :
    0.90 * (n : ℝ) ≤ Chebyshev.theta n := by
  have hnR : (10000000 : ℝ) ≤ n := by exact_mod_cast hn
  have hpsi := psi_ge_cheb (show (30 : ℝ) ≤ n by linarith)
  have hsub := Chebyshev.psi_sub_theta_le (show (1 : ℝ) ≤ n by linarith)
  have hlog10m : log 10000000 < 17 := by
    rw [log_lt_iff_lt_exp (by norm_num)]
    calc (10000000 : ℝ) < (2.71828 : ℝ) ^ (17 : ℕ) := by norm_num
      _ < (exp 1) ^ (17 : ℕ) := by gcongr; exact lt_trans (by norm_num) Real.exp_one_gt_d9
      _ = exp 17 := by rw [← Real.exp_nat_mul]; norm_num
  have hlog_n : log n ≤ 13 + 4 * √(√((n : ℝ) / 10000000)) := by
    have h := log_le_add_four_sqrt_sqrt (show (0 : ℝ) < 10000000 by norm_num) hnR
    linarith
  have hsqrt_le : √(√((n : ℝ) / 10000000)) ≤ √((n : ℝ) / 10000000) := by
    have h1 : 1 ≤ (n : ℝ) / 10000000 := by linarith
    have h2 : 1 ≤ √((n : ℝ) / 10000000) := Real.one_le_sqrt.mpr h1
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hsqrt10m : (3000 : ℝ) ≤ √10000000 := by
    rw [Real.le_sqrt' (by norm_num)]
    norm_num
  have hsqrt_div : √((n : ℝ) / 10000000) ≤ √n / 3000 := by
    rw [Real.sqrt_div (by linarith)]
    exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by norm_num) hsqrt10m
  have hsqrt_n : 3000 ≤ √n := hsqrt10m.trans (Real.sqrt_le_sqrt hnR)
  have hsq_n : √n * √n = n := Real.mul_self_sqrt (by linarith)
  have h2sqrt : 2 * √n * log n ≤ 0.012 * n := by
    have h1 : 2 * √n * log n ≤ 2 * √n * (13 + 4 * (√n / 3000)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    calc 2 * √n * log n ≤ 2 * √n * (13 + 4 * (√n / 3000)) := h1
      _ = 26 * √n + (8 / 3000) * (√n * √n) := by ring
      _ ≤ 26 * ((√n * √n) / 3000) + (8 / 3000) * n := by
        have hsqrt_le : √n ≤ (√n * √n) / 3000 := by
          calc √n = √n * 1 := by ring
            _ ≤ √n * (√n / 3000) := mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)
            _ = (√n * √n) / 3000 := by ring
        linarith
      _ = (34 / 3000) * n := by rw [hsq_n]; ring
      _ ≤ 0.012 * n := by linarith
  have hlog_n1 : 5 * log ((n : ℝ) + 1) ≤ 0.001 * n := by
    have hn1_le : (n : ℝ) + 1 ≤ 2 * n := by linarith
    have hlog1 : log ((n : ℝ) + 1) ≤ log (2 * n) := Real.log_le_log (by linarith) hn1_le
    have hlog2 : log (2 * n) = log 2 + log n := Real.log_mul (by norm_num) (by linarith)
    have hlog2_ub : log 2 < 0.7 := lt_trans Real.log_two_lt_d9 (by norm_num)
    have h1 : log n ≤ 13 + 4 * (√n / 3000) := by linarith
    have h2 : √n ≤ n / 3000 := by
      calc √n = √n * 1 := by ring
        _ ≤ √n * (√n / 3000) := by nlinarith [Real.sqrt_nonneg n]
        _ = (√n * √n) / 3000 := by ring
        _ = n / 3000 := by rw [hsq_n]
    linarith
  linarith

lemma theta_le_1108 {n : ℕ} (hn : 10000000 ≤ n) :
    Chebyshev.theta n ≤ 1.108 * (n : ℝ) := by
  have hnR : (10000000 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 := Chebyshev.theta_le_psi (n : ℝ)
  have h2 := psi_le_cheb (show (0 : ℝ) ≤ n by positivity)
  have hlog10m : log 10000000 < 17 := by
    rw [log_lt_iff_lt_exp (by norm_num)]
    calc (10000000 : ℝ) < (2.71828 : ℝ) ^ (17 : ℕ) := by norm_num
      _ < (exp 1) ^ (17 : ℕ) := by gcongr; exact lt_trans (by norm_num) Real.exp_one_gt_d9
      _ = exp 17 := by rw [← Real.exp_nat_mul]; norm_num
  have hlog : log ((n : ℝ) + 31) ≤ 13 + 4 * √(√(((n : ℝ) + 31) / 10000000)) := by
    have h := log_le_add_four_sqrt_sqrt (x := (n : ℝ) + 31) (M := 10000000) (by norm_num) (by linarith)
    linarith
  have hsqrt_le : √(√(((n : ℝ) + 31) / 10000000)) ≤ √(((n : ℝ) + 31) / 10000000) := by
    have h1' : 1 ≤ ((n : ℝ) + 31) / 10000000 := by linarith
    have h2' : 1 ≤ √(((n : ℝ) + 31) / 10000000) := Real.one_le_sqrt.mpr h1'
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hsq_le : (√(((n : ℝ) + 31) / 10000000)) ^ (2 : ℕ) = ((n : ℝ) + 31) / 10000000 :=
    Real.sq_sqrt (by positivity)
  have hlog_nn : 0 ≤ log ((n : ℝ) + 31) := Real.log_nonneg (by linarith)
  have hsq : (log ((n : ℝ) + 31)) ^ 2 ≤ (13 + 4 * √(((n : ℝ) + 31) / 10000000)) ^ 2 := by
    nlinarith
  have hsq_ab : (13 + 4 * √(((n : ℝ) + 31) / 10000000)) ^ 2 ≤
      2 * 13 ^ 2 + 2 * (4 * √(((n : ℝ) + 31) / 10000000)) ^ 2 := by
    nlinarith [sq_nonneg (13 - 4 * √(((n : ℝ) + 31) / 10000000))]
  have h2sq : (4 * √(((n : ℝ) + 31) / 10000000)) ^ 2 = 16 * (((n : ℝ) + 31) / 10000000) := by
    calc (4 * √(((n : ℝ) + 31) / 10000000)) ^ 2
        = 16 * (√(((n : ℝ) + 31) / 10000000)) ^ (2 : ℕ) := by ring
      _ = 16 * (((n : ℝ) + 31) / 10000000) := by rw [hsq_le]
  linarith

lemma primeCounting_40000_ge_2000 : 2000 ≤ Nat.primeCounting 40000 := by
  have hth := theta_ge_080 (le_refl 40000)
  norm_num at hth
  have hle := Chebyshev.theta_le_pi_mul_log 40000
  have hlog40k : log 40000 < 11 := by
    rw [log_lt_iff_lt_exp (by norm_num)]
    calc (40000 : ℝ) < (2.71828 : ℝ) ^ (11 : ℕ) := by norm_num
      _ < (exp 1) ^ (11 : ℕ) := by gcongr; exact lt_trans (by norm_num) Real.exp_one_gt_d9
      _ = exp 11 := by rw [← Real.exp_nat_mul]; norm_num
  obtain ⟨pi40k, hpi_def⟩ : ∃ m : ℕ, m = Nat.primeCounting 40000 := ⟨_, rfl⟩
  rw [← hpi_def] at hle
  norm_num at hle
  have hpi_nonneg : 0 ≤ (pi40k : ℝ) := by exact_mod_cast Nat.zero_le pi40k
  have hmul : (32000 : ℝ) ≤ (pi40k : ℝ) * 11 := by
    have h1 : (pi40k : ℝ) * log 40000 ≤ (pi40k : ℝ) * 11 :=
      mul_le_mul_of_nonneg_left hlog40k.le hpi_nonneg
    linarith only [hth, hle, h1]
  by_contra hlt
  have hltR : (pi40k : ℝ) < 2000 := by exact_mod_cast (by omega : pi40k < 2000)
  linarith only [hmul, hltR]

lemma sumX_primeCounting_1836_ub : sumX (Nat.primeCounting 18361375334787054929) ≤ 6.5 := by
  obtain ⟨b, hb_def⟩ : ∃ b, b = Nat.primeCounting 18361375334787054929 := ⟨_, rfl⟩
  rw [← hb_def]
  have h25_lt_b : 25 ≤ b := by
    rw [← primeCounting_97, hb_def]
    exact Nat.monotone_primeCounting (by norm_num)
  have h1 := (sumX_sub_sumX_bounds h25_lt_b).2
  have h2 := sumX_25_ub
  have hsub : ∑ j ∈ Finset.Ico 25 b, (1 : ℝ) / (pNth j : ℝ) ≤
      ∑ p ∈ Nat.primesLE 18361375334787054929 \ Nat.primesLE 97, (1 : ℝ) / (p : ℝ) := by
    have himg : Finset.image pNth (Finset.Ico 25 b) ⊆
        (Finset.range b).image pNth \ (Finset.range 25).image pNth := by
      intro q hq
      rw [Finset.mem_image] at hq
      rcases hq with ⟨j, hj, rfl⟩
      rw [Finset.mem_Ico] at hj
      rw [Finset.mem_sdiff, Finset.mem_image, Finset.mem_image]
      refine ⟨⟨j, Finset.mem_range.mpr hj.2, rfl⟩, ?_⟩
      rintro ⟨i, hi, heq⟩
      rw [Finset.mem_range] at hi
      have := pNth_strictMono.injective heq
      omega
    have hsum1 : ∑ j ∈ Finset.Ico 25 b, (1 : ℝ) / (pNth j : ℝ) =
        ∑ q ∈ Finset.image pNth (Finset.Ico 25 b), (1 : ℝ) / (q : ℝ) := by
      rw [Finset.sum_image]
      intro i _ j _ hij
      exact pNth_strictMono.injective hij
    have hsum2 : ∑ q ∈ Finset.image pNth (Finset.Ico 25 b), (1 : ℝ) / (q : ℝ) ≤
        ∑ q ∈ (Finset.range b).image pNth \ (Finset.range 25).image pNth, (1 : ℝ) / (q : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => div_nonneg zero_le_one (Nat.cast_nonneg _))
    rw [primesLE_eq_image_pNth, primesLE_eq_image_pNth, primeCounting_97, ← hb_def]
    exact hsum1.trans_le hsum2
  have htheta_ub : ∀ n ∈ Finset.Ico (97 : ℕ) 18361375334787054930, Chebyshev.theta n ≤ 1.4 * (n : ℝ) := by
    intro n _
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    have hth := Chebyshev.theta_le_log4_mul_x hn0
    have hlog4 : log 4 < 1.4 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      have hlog2 : log 2 < 0.7 := lt_trans Real.log_two_lt_d9 (by norm_num)
      linarith only [hlog2]
    nlinarith only [hth, hlog4, hn0]
  have hub := sum_inv_primes_ub (M := 97) (N := 18361375334787054929) (c := 1.4)
    (by norm_num) (by norm_num) (by norm_num) htheta_ub
  have hlog_ub : log (log (18361375334787054929 : ℝ)) < 4 := by
    have h1' : (18361375334787054929 : ℝ) < (2.71828 : ℝ) ^ (45 : ℕ) := by
      calc (18361375334787054929 : ℝ) < ((2.71828 : ℝ) ^ (9 : ℕ)) ^ (5 : ℕ) := by norm_num
        _ = (2.71828 : ℝ) ^ (45 : ℕ) := by ring
    have h2' : log (18361375334787054929 : ℝ) < 45 := by
      rw [log_lt_iff_lt_exp (by norm_num)]
      calc (18361375334787054929 : ℝ) < (2.71828 : ℝ) ^ (45 : ℕ) := h1'
        _ < (exp 1) ^ (45 : ℕ) := by gcongr; exact lt_trans (by norm_num) Real.exp_one_gt_d9
        _ = exp 45 := by rw [← Real.exp_nat_mul]; norm_num
    have h3' : log 45 < 4 := by
      rw [log_lt_iff_lt_exp (by norm_num)]
      calc (45 : ℝ) < (2.71828 : ℝ) ^ (4 : ℕ) := by norm_num
        _ < (exp 1) ^ (4 : ℕ) := by gcongr; exact lt_trans (by norm_num) Real.exp_one_gt_d9
        _ = exp 4 := by rw [← Real.exp_nat_mul]; norm_num
    have hpos : 0 < log (18361375334787054929 : ℝ) := Real.log_pos (by norm_num)
    exact (Real.log_lt_log hpos h2').trans h3'
  have hlog97_lb : 4.5 < log 97 := by
    rw [lt_log_iff_exp_lt (by norm_num)]
    have hexp_ub : exp 1 < (2.72 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have hpow : (exp 1) ^ (9 : ℕ) < (97 : ℝ) ^ (2 : ℕ) := by
      calc (exp 1) ^ (9 : ℕ) < (2.72 : ℝ) ^ (9 : ℕ) := by gcongr
        _ < (97 : ℝ) ^ (2 : ℕ) := by norm_num
    have hexp_pow : (exp (4.5 : ℝ)) ^ (2 : ℕ) < (97 : ℝ) ^ (2 : ℕ) := by
      rw [← Real.exp_nat_mul]
      have h9 : (2 : ℕ) * (4.5 : ℝ) = (9 : ℕ) * (1 : ℝ) := by norm_num
      rw [h9, Real.exp_nat_mul]
      exact hpow
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hexp_pow
  have hloglog97_lb : 1.5 < log (log 97) := by
    have h15 : 1.5 < log 4.5 := by
      rw [lt_log_iff_exp_lt (by norm_num)]
      have hexp_ub : exp 1 < (2.72 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
      have hpow : (exp 1) ^ (3 : ℕ) < (4.5 : ℝ) ^ (2 : ℕ) := by
        calc (exp 1) ^ (3 : ℕ) < (2.72 : ℝ) ^ (3 : ℕ) := by gcongr
          _ < (4.5 : ℝ) ^ (2 : ℕ) := by norm_num
      have hexp_pow : (exp (1.5 : ℝ)) ^ (2 : ℕ) < (4.5 : ℝ) ^ (2 : ℕ) := by
        rw [← Real.exp_nat_mul]
        have h3 : (2 : ℕ) * (1.5 : ℝ) = (3 : ℕ) * (1 : ℝ) := by norm_num
        rw [h3, Real.exp_nat_mul]
        exact hpow
      exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hexp_pow
    exact h15.trans (Real.log_lt_log (by norm_num) hlog97_lb)
  have hinv97 : 1 / log 97 < 0.223 := by
    rw [div_lt_iff₀ (by linarith only [hlog97_lb])]
    linarith only [hlog97_lb]
  have hub' : ∑ x ∈ Nat.primesLE 18361375334787054929 \ Nat.primesLE 97, (1 : ℝ) / (x : ℝ) ≤ 3.813 := by
    have hmul : 1.4 * (log (log (18361375334787054929 : ℝ)) -
        log (log (97 : ℝ)) + 1 / log (97 : ℝ)) ≤ 1.4 * (4 - 1.5 + 0.223) := by
      linarith only [hlog_ub, hinv97, hloglog97_lb]
    norm_num at hub hmul
    norm_num
    linarith only [hub, hmul]
  calc sumX b = sumX 25 + (sumX b - sumX 25) := by ring
    _ ≤ 2.58 + (∑ j ∈ Finset.Ico 25 b, (1 : ℝ) / (pNth j : ℝ) + 1 / ((25 : ℝ) + 1)) := by
      linarith only [h1, h2]
    _ ≤ 2.58 + (3.813 + 1 / 26) := by
      have h12 : ∑ j ∈ Finset.Ico 25 b, (1 : ℝ) / (pNth j : ℝ) ≤ 3.813 := hsub.trans hub'
      linarith only [h12]
    _ ≤ 6.5 := by norm_num

lemma sumX_1836_sub_40k_gt :
    0.97 < sumX (Nat.count Nat.Prime 18361375334787046697) - sumX (Nat.primeCounting 40000) := by
  obtain ⟨a, ha_def⟩ : ∃ a, a = Nat.count Nat.Prime 18361375334787046697 := ⟨_, rfl⟩
  rw [← ha_def]
  have h40k_le_a : Nat.primeCounting 40000 ≤ a := by
    rw [ha_def]
    change Nat.count Nat.Prime (40000 + 1) ≤ Nat.count Nat.Prime 18361375334787046697
    exact Nat.count_monotone Nat.Prime (by norm_num)
  have h1 := (sumX_sub_sumX_bounds h40k_le_a).1
  have ha_eq : a = Nat.primeCounting 18361375334787046696 := ha_def
  have hsub : ∑ p ∈ Nat.primesLE 18361375334787046696 \ Nat.primesLE 40000, (1 : ℝ) / (p : ℝ) ≤
      ∑ j ∈ Finset.Ico (Nat.primeCounting 40000) a, (1 : ℝ) / (pNth j : ℝ) := by
    have himg : (Finset.range a).image pNth \ (Finset.range (Nat.primeCounting 40000)).image pNth ⊆
        Finset.image pNth (Finset.Ico (Nat.primeCounting 40000) a) := by
      intro q hq
      rw [Finset.mem_sdiff, Finset.mem_image, Finset.mem_image] at hq
      rcases hq.1 with ⟨j, hj, rfl⟩
      rw [Finset.mem_range] at hj
      rw [Finset.mem_image]
      refine ⟨j, Finset.mem_Ico.mpr ⟨?_, hj⟩, rfl⟩
      by_contra hlt
      exact hq.2 ⟨j, Finset.mem_range.mpr (by omega), rfl⟩
    have hsum1 : ∑ q ∈ (Finset.range a).image pNth \ (Finset.range (Nat.primeCounting 40000)).image pNth,
          (1 : ℝ) / (q : ℝ) ≤
        ∑ q ∈ Finset.image pNth (Finset.Ico (Nat.primeCounting 40000) a), (1 : ℝ) / (q : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => div_nonneg zero_le_one (Nat.cast_nonneg _))
    have hsum2 : ∑ q ∈ Finset.image pNth (Finset.Ico (Nat.primeCounting 40000) a), (1 : ℝ) / (q : ℝ) =
        ∑ j ∈ Finset.Ico (Nat.primeCounting 40000) a, (1 : ℝ) / (pNth j : ℝ) := by
      rw [Finset.sum_image]
      intro i _ j _ hij
      exact pNth_strictMono.injective hij
    rw [primesLE_eq_image_pNth, primesLE_eq_image_pNth, ← ha_eq]
    exact hsum1.trans_eq hsum2
  have hlb := sum_inv_primes_lb (M := 40000) (N := 18361375334787046696) (c := 0.80)
    (by norm_num) (by norm_num) (by norm_num)
    (fun n hn => theta_ge_080 (Finset.mem_Ico.mp hn).1)
  have hlog40k_lb : 10.5 < log 40000 := by
    rw [lt_log_iff_exp_lt (by norm_num)]
    have hexp_ub : exp 1 < (2.72 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have hpow : (exp 1) ^ (21 : ℕ) < (40000 : ℝ) ^ (2 : ℕ) := by
      calc (exp 1) ^ (21 : ℕ) < (2.72 : ℝ) ^ (21 : ℕ) := by gcongr
        _ < (40000 : ℝ) ^ (2 : ℕ) := by norm_num
    have hexp_pow : (exp (10.5 : ℝ)) ^ (2 : ℕ) < (40000 : ℝ) ^ (2 : ℕ) := by
      rw [← Real.exp_nat_mul]
      have h21 : (2 : ℕ) * (10.5 : ℝ) = (21 : ℕ) * (1 : ℝ) := by norm_num
      rw [h21, Real.exp_nat_mul]
      exact hpow
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hexp_pow
  have hlog40k_ub : log 40000 < 10.6 := by
    rw [log_lt_iff_lt_exp (by norm_num)]
    have hexp_lb : (2.71828 : ℝ) < exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
    have hpow : (40000 : ℝ) ^ (5 : ℕ) < (exp 1) ^ (53 : ℕ) := by
      calc (40000 : ℝ) ^ (5 : ℕ) < (2.71828 : ℝ) ^ (53 : ℕ) := by norm_num
        _ < (exp 1) ^ (53 : ℕ) := by gcongr
    have hexp_pow : (40000 : ℝ) ^ (5 : ℕ) < (exp (10.6 : ℝ)) ^ (5 : ℕ) := by
      rw [← Real.exp_nat_mul]
      have h53 : (5 : ℕ) * (10.6 : ℝ) = (53 : ℕ) * (1 : ℝ) := by norm_num
      rw [h53, Real.exp_nat_mul]
      exact hpow
    exact lt_of_pow_lt_pow_left₀ 5 (by positivity) hexp_pow
  have hloglog40k_ub : log (log 40000) < 2.364 := by
    have h237 : log 10.6 < 26 / 11 := by
      rw [log_lt_iff_lt_exp (by norm_num)]
      have hexp_lb : (2.71828 : ℝ) < exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
      have hpow : (10.6 : ℝ) ^ (11 : ℕ) < (exp 1) ^ (26 : ℕ) := by
        calc (10.6 : ℝ) ^ (11 : ℕ) < (2.71828 : ℝ) ^ (26 : ℕ) := by norm_num
          _ < (exp 1) ^ (26 : ℕ) := by gcongr
      have hexp_pow : (10.6 : ℝ) ^ (11 : ℕ) < (exp ((26 : ℝ) / 11)) ^ (11 : ℕ) := by
        rw [← Real.exp_nat_mul]
        have h26 : (11 : ℕ) * ((26 : ℝ) / 11) = (26 : ℕ) * (1 : ℝ) := by norm_num
        rw [h26, Real.exp_nat_mul]
        exact hpow
      exact lt_of_pow_lt_pow_left₀ 11 (by positivity) hexp_pow
    have h2364 : (26 : ℝ) / 11 < 2.364 := by norm_num
    exact (Real.log_lt_log (by linarith only [hlog40k_lb]) hlog40k_ub).trans (h237.trans h2364)
  have hlogN_lb : 44 < log (18361375334787046696 : ℝ) := by
    rw [lt_log_iff_exp_lt (by norm_num)]
    have hexp_ub : exp 1 < (2.72 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
    calc exp (44 : ℝ) = (exp 1) ^ (44 : ℕ) := by
          rw [← Real.exp_nat_mul]; norm_num
      _ < (2.72 : ℝ) ^ (44 : ℕ) := by gcongr
      _ = ((2.72 : ℝ) ^ (11 : ℕ)) ^ (4 : ℕ) := by ring
      _ < (18361375334787046696 : ℝ) := by norm_num
  have hloglogN_lb : 3.75 < log (log (18361375334787046696 : ℝ)) := by
    have h375 : 3.75 < log 44 := by
      rw [lt_log_iff_exp_lt (by norm_num)]
      have hexp_ub : exp 1 < (2.72 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
      have hpow : (exp 1) ^ (15 : ℕ) < (44 : ℝ) ^ (4 : ℕ) := by
        calc (exp 1) ^ (15 : ℕ) < (2.72 : ℝ) ^ (15 : ℕ) := by gcongr
          _ < (44 : ℝ) ^ (4 : ℕ) := by norm_num
      have hexp_pow : (exp (3.75 : ℝ)) ^ (4 : ℕ) < (44 : ℝ) ^ (4 : ℕ) := by
        rw [← Real.exp_nat_mul]
        have h15 : (4 : ℕ) * (3.75 : ℝ) = (15 : ℕ) * (1 : ℝ) := by norm_num
        rw [h15, Real.exp_nat_mul]
        exact hpow
      exact lt_of_pow_lt_pow_left₀ 4 (by norm_num) hexp_pow
    exact h375.trans (Real.log_lt_log (by norm_num) hlogN_lb)
  have hinv1 : 1 / ((40000 : ℝ) * log 40000) < 0.00001 := by
    rw [div_lt_iff₀ (by linarith only [hlog40k_lb])]
    linarith only [hlog40k_lb]
  have hinv2 : 1.4 / log 40000 < 0.134 := by
    rw [div_lt_iff₀ (by linarith only [hlog40k_lb])]
    linarith only [hlog40k_lb]
  linarith only [h1, hsub, hlb, hloglog40k_ub, hloglogN_lb, hinv1, hinv2]

lemma moderate_k_case {k : ℕ} (hk21 : 21 ≤ k) (hk1500 : k ≤ 1500) {d : ℕ → ℝ}
    (hd : ∀ r, d (pNth r) = densK k r) : ¬ Erdos690.IsUnimodalOnPrimes d := by
  obtain ⟨a, ha_def⟩ : ∃ a, a = Nat.count Nat.Prime 18361375334787046697 := ⟨_, rfl⟩
  obtain ⟨b, hb_def⟩ : ∃ b, b = Nat.count Nat.Prime 18361375334787054929 := ⟨_, rfl⟩
  have hpa : pNth a = 18361375334787046697 := ha_def ▸ Nat.nth_count prime_18361375334787046697
  have hpa1 : pNth (a + 1) = 18361375334787048247 :=
    ha_def ▸ pNth_consecutive_of_no_prime prime_18361375334787046697 prime_18361375334787048247
      (by norm_num) gap_1836_no_prime
  have hpb : pNth b = 18361375334787054929 := hb_def ▸ Nat.nth_count prime_18361375334787054929
  have hpb1 : pNth (b + 1) = 18361375334787054931 := by
    rw [hb_def]
    refine pNth_consecutive_of_no_prime prime_18361375334787054929 prime_18361375334787054931
      (by norm_num) ?_
    intro n hn1 hn2 hn_prime
    have hn_eq : n = 18361375334787054930 := by omega
    subst hn_eq
    rcases hn_prime.eq_two_or_odd with h2 | hodd <;> omega
  have hab : a < b := by
    rw [← pNth_strictMono.lt_iff_lt, hpa, hpb]
    norm_num
  have hk_le_40k : k - 1 ≤ Nat.primeCounting 40000 := by
    have h2k := primeCounting_40000_ge_2000
    omega
  have h40k_le_a : Nat.primeCounting 40000 ≤ a := by
    rw [ha_def]
    change Nat.count Nat.Prime (40000 + 1) ≤ Nat.count Nat.Prime 18361375334787046697
    exact Nat.count_monotone Nat.Prime (by norm_num)
  have ha_ge : k - 1 ≤ a := hk_le_40k.trans h40k_le_a
  have hSb_ub : sumX b ≤ 6.5 := by
    have hb_le : b ≤ Nat.primeCounting 18361375334787054929 := by
      rw [hb_def]
      change Nat.count Nat.Prime 18361375334787054929 ≤ Nat.count Nat.Prime (18361375334787054929 + 1)
      exact Nat.count_monotone Nat.Prime (Nat.le_succ _)
    have hmono : sumX b ≤ sumX (Nat.primeCounting 18361375334787054929) := by
      unfold sumX
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hb_le)
        (fun j _ _ => xTerm_nonneg j)
    exact hmono.trans sumX_primeCounting_1836_ub
  have hSa_diff : 0.97 < sumX a - sumX (k - 2) := by
    have hk2_le : k - 2 ≤ Nat.primeCounting 40000 := by omega
    have hmono : sumX (k - 2) ≤ sumX (Nat.primeCounting 40000) := by
      unfold sumX
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk2_le)
        (fun j _ _ => xTerm_nonneg j)
    have hgt := ha_def ▸ sumX_1836_sub_40k_gt
    linarith only [hmono, hgt]
  have hdesc : elemSym (k - 2) a / elemSym (k - 1) a < (pNth (a + 1) : ℝ) - (pNth a : ℝ) + 1 := by
    have hSpos : sumX (k - 2) < sumX a := by linarith only [hSa_diff]
    have hub := R_upper_bound (by omega) ha_ge hSpos
    have hgap : (pNth (a + 1) : ℝ) - (pNth a : ℝ) + 1 = 1551 := by
      rw [hpa, hpa1]; norm_num
    have hnum : ((k - 1 : ℕ) : ℝ) ≤ 1499 := by exact_mod_cast (by omega : k - 1 ≤ 1499)
    have hdiv : ((k - 1 : ℕ) : ℝ) / (sumX a - sumX (k - 2)) < 1551 := by
      rw [div_lt_iff₀ (by linarith only [hSa_diff])]
      nlinarith only [hSa_diff, hnum]
    linarith only [hub, hgap, hdiv]
  have hasc : (pNth (b + 1) : ℝ) - (pNth b : ℝ) + 1 < elemSym (k - 2) b / elemSym (k - 1) b := by
    have hSpos : sumX 0 < sumX b := by
      have hb0 : 0 < b := by omega
      have hx0 : 0 < xTerm 0 := xTerm_pos 0
      have hle : xTerm 0 ≤ sumX b :=
        Finset.single_le_sum (fun j _ => xTerm_nonneg j) (Finset.mem_range.mpr hb0)
      have hS0 : sumX 0 = 0 := by simp [sumX]
      linarith only [hx0, hle, hS0]
    have hlb := R_lower_bound (by omega) (by omega : 0 < k - 1) (ha_ge.trans hab.le) hSpos
    have hgap : (pNth (b + 1) : ℝ) - (pNth b : ℝ) + 1 = 3 := by
      rw [hpb, hpb1]; norm_num
    have hS0 : sumX 0 = 0 := by simp [sumX]
    rw [hS0, sub_zero, Nat.sub_zero] at hlb
    have hnum : (20 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 20 ≤ k - 1)
    have hSb_pos : 0 < sumX b := by linarith only [hSpos, hS0]
    have hdiv : 3 < ((k - 1 : ℕ) : ℝ) / sumX b := by
      rw [lt_div_iff₀ hSb_pos]
      nlinarith only [hSb_ub, hnum, hSb_pos]
    linarith only [hlb, hgap, hdiv]
  exact not_unimodal_of_descent_ascent (by omega) hd hab ha_ge hdesc hasc

/-! ### Module 5: Large k case (k > 1500) -/

def smallPrimes109 : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
   73, 79, 83, 89, 97, 101, 103, 107, 109]

def isCand12000 (n : ℕ) : Bool :=
  if n < 2 then false
  else if n ≤ 109 then smallPrimes109.contains n
  else smallPrimes109.all (fun p => n % p != 0)

lemma isCand12000_iff_prime {n : ℕ} (hn : n ≤ 12000) :
    isCand12000 n = true ↔ n.Prime := by
  constructor
  · intro h
    by_cases hn109 : n ≤ 109
    · have : ∀ m ≤ 109, isCand12000 m = true → m.Prime := by decide
      exact this n hn109 h
    · unfold isCand12000 at h
      have hn2 : ¬ n < 2 := by omega
      rw [if_neg hn2, if_neg hn109, List.all_eq_true] at h
      by_contra hnp
      have hmin_prime : n.minFac.Prime := Nat.minFac_prime (by omega)
      have hmin_dvd : n.minFac ∣ n := Nat.minFac_dvd n
      have hmin_sq : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
      have hmin_le : n.minFac ≤ 109 := by
        by_contra hgt
        have : 110 ≤ n.minFac := by omega
        have : 110 ^ 2 ≤ n.minFac ^ 2 := Nat.pow_le_pow_left this 2
        omega
      have hmem : n.minFac ∈ smallPrimes109 := by
        have : ∀ q ≤ 109, q.Prime → q ∈ smallPrimes109 := by decide
        exact this n.minFac hmin_le hmin_prime
      have hbad := h n.minFac hmem
      simp only [bne_iff_ne, ne_eq, decide_not, Bool.not_eq_true', decide_eq_false_iff_not,
        Decidable.not_not] at hbad
      exact hbad (Nat.mod_eq_zero_of_dvd hmin_dvd)
  · intro hp
    have h2 : 2 ≤ n := hp.two_le
    by_cases hn109 : n ≤ 109
    · have : ∀ m ≤ 109, m.Prime → isCand12000 m = true := by decide
      exact this n hn109 hp
    · unfold isCand12000
      rw [if_neg (by omega), if_neg hn109, List.all_eq_true]
      intro p hp_mem
      have hp_prime : p.Prime := by
        have : ∀ q ∈ smallPrimes109, q.Prime := by decide
        exact this p hp_mem
      have hp_le : p ≤ 109 := by
        have : ∀ q ∈ smallPrimes109, q ≤ 109 := by decide
        exact this p hp_mem
      simp only [bne_iff_ne, ne_eq, decide_not, Bool.not_eq_true', decide_eq_false_iff_not,
        Decidable.not_not]
      intro hmod
      have hdvd : p ∣ n := Nat.dvd_of_mod_eq_zero hmod
      rcases (Nat.dvd_prime hp).mp hdvd with rfl | rfl
      · exact Nat.not_prime_one hp_prime
      · omega

def blockCnt10 (j : ℕ) : ℕ :=
  ((List.range 10).filter (fun r => isCand12000 (10 * j + r))).length

def wtUb10 (j : ℕ) : ℕ :=
  if j ≤ 0 then 231 else if j ≤ 2 then 341 else if j ≤ 8 then 451
  else if j ≤ 14 then 502 else if j ≤ 20 then 535 else if j ≤ 29 then 571
  else if j ≤ 32 then 580 else if j ≤ 35 then 589 else if j ≤ 39 then 600
  else if j ≤ 44 then 611 else if j ≤ 54 then 631 else if j ≤ 64 then 648
  else if j ≤ 79 then 669 else if j ≤ 99 then 691 else if j ≤ 129 then 718
  else if j ≤ 169 then 744 else if j ≤ 219 then 770 else if j ≤ 299 then 801
  else if j ≤ 399 then 830 else if j ≤ 549 then 862 else if j ≤ 749 then 893
  else if j ≤ 999 then 922 else 940

def wtLb10 (j : ℕ) : ℕ :=
  if j ≤ 0 then 0 else if j ≤ 2 then 230 else if j ≤ 8 then 340
  else if j ≤ 14 then 449 else if j ≤ 20 then 501 else if j ≤ 29 then 534
  else if j ≤ 99 then 570 else if j ≤ 299 then 690 else if j ≤ 999 then 800
  else 921

def checkBlocks1200Loop (n accU accL : ℕ) : ℕ → Bool
  | 0 => true
  | m + 1 =>
    let j := n
    let okL := j < 20 || 74 * (10 * (j + 1)) ≤ accL
    let accU' := accU + blockCnt10 j * wtUb10 j
    let accL' := accL + blockCnt10 j * wtLb10 j
    let okU := j < 20 || accU' ≤ 105 * (10 * j)
    okL && okU && checkBlocks1200Loop (n + 1) accU' accL' m

set_option maxRecDepth 65536 in
lemma checkBlocks1200_ok : checkBlocks1200Loop 0 0 0 1200 = true := by
  decide

lemma checkBlocks1200_spec :
    ∀ m n accU accL, checkBlocks1200Loop n accU accL m = true →
      ∀ j, n ≤ j → j < n + m → 20 ≤ j →
        74 * (10 * (j + 1)) ≤ accL + ∑ i ∈ Finset.Ico n j, blockCnt10 i * wtLb10 i ∧
        accU + ∑ i ∈ Finset.Ico n (j + 1), blockCnt10 i * wtUb10 i ≤ 105 * (10 * j) := by
  intro m
  induction m with
  | zero =>
    intro n accU accL _ j hnj hj
    omega
  | succ m ih =>
    intro n accU accL hloop j hnj hj hm20
    unfold checkBlocks1200Loop at hloop
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hloop
    rcases hloop with ⟨⟨hokL, hokU⟩, hrest⟩
    by_cases hjn : j = n
    · subst hjn
      have h20 : ¬ j < 20 := by omega
      simp only [h20, false_or] at hokL hokU
      rw [Finset.Ico_self, Finset.sum_empty, add_zero]
      rw [Finset.sum_eq_sum_Ico_succ_bot (Nat.lt_succ_self j), Finset.Ico_self,
          Finset.sum_empty, add_zero]
      exact ⟨hokL, hokU⟩
    · have hlt : n + 1 ≤ j := by omega
      have hrec := ih (n + 1) (accU + blockCnt10 n * wtUb10 n)
        (accL + blockCnt10 n * wtLb10 n) hrest j hlt (by omega) hm20
      rw [Finset.sum_eq_sum_Ico_succ_bot (show n < j by omega)]
      rw [Finset.sum_eq_sum_Ico_succ_bot (show n < j + 1 by omega)]
      omega

lemma blocks1200_bounds {j : ℕ} (hj20 : 20 ≤ j) (hj1200 : j < 1200) :
    74 * (10 * (j + 1)) ≤ ∑ i ∈ Finset.range j, blockCnt10 i * wtLb10 i ∧
    ∑ i ∈ Finset.range (j + 1), blockCnt10 i * wtUb10 i ≤ 105 * (10 * j) := by
  have h := checkBlocks1200_spec 1200 0 0 0 checkBlocks1200_ok j (Nat.zero_le _) hj1200 hj20
  simpa [Nat.Ico_zero_eq_range] using h

lemma exp_div_100_gt_of_lt {B wt : ℕ} (hBpos : 0 < B)
    (hB : (B : ℝ) < (2.71828 : ℝ) ^ (wt / 100) * (1.10517 : ℝ) ^ ((wt % 100) / 10) *
      (1.01005 : ℝ) ^ (wt % 10)) :
    log (B : ℝ) < (wt : ℝ) / 100 := by
  rw [log_lt_iff_lt_exp (by exact_mod_cast hBpos)]
  have hexp1 : (2.71828 : ℝ) < exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have hexp10 : (1.10517 : ℝ) ≤ exp (0.1 : ℝ) := by
    have hsum := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.1 by norm_num) 5
    have hexp_eq : ∑ i ∈ Finset.range 5, (0.1 : ℝ) ^ i / (Nat.factorial i : ℝ) =
        1 + 0.1 + 0.1 ^ 2 / 2 + 0.1 ^ 3 / 6 + 0.1 ^ 4 / 24 := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
      have hf0 : ((Nat.factorial 0 : ℕ) : ℝ) = 1 := by norm_num
      have hf1 : ((Nat.factorial 1 : ℕ) : ℝ) = 1 := by norm_num
      have hf2 : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num
      have hf3 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by exact_mod_cast (by decide : Nat.factorial 3 = 6)
      have hf4 : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by exact_mod_cast (by decide : Nat.factorial 4 = 24)
      rw [hf0, hf1, hf2, hf3, hf4]
      ring
    rw [hexp_eq] at hsum
    norm_num at hsum
    linarith
  have hexp01 : (1.01005 : ℝ) ≤ exp (0.01 : ℝ) := by
    have hsum := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.01 by norm_num) 3
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty] at hsum
    have hf0 : ((Nat.factorial 0 : ℕ) : ℝ) = 1 := by norm_num
    have hf1 : ((Nat.factorial 1 : ℕ) : ℝ) = 1 := by norm_num
    have hf2 : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num
    rw [hf0, hf1, hf2] at hsum
    norm_num at hsum
    linarith
  have hwt : (wt : ℝ) / 100 = (wt / 100 : ℕ) * (1 : ℝ) + ((wt % 100) / 10 : ℕ) * (0.1 : ℝ) +
      (wt % 10 : ℕ) * (0.01 : ℝ) := by
    have h1 := Nat.div_add_mod wt 100
    have h2 := Nat.div_add_mod (wt % 100) 10
    have hmod10 : (wt % 100) % 10 = wt % 10 := Nat.mod_mod_of_dvd wt (by norm_num)
    have h12 : 100 * (wt / 100) + 10 * ((wt % 100) / 10) + wt % 10 = wt := by omega
    have hR : (100 : ℝ) * ((wt / 100 : ℕ) : ℝ) + 10 * (((wt % 100) / 10 : ℕ) : ℝ) +
        ((wt % 10 : ℕ) : ℝ) = (wt : ℝ) := by exact_mod_cast h12
    linarith
  calc (B : ℝ) < (2.71828 : ℝ) ^ (wt / 100) * (1.10517 : ℝ) ^ ((wt % 100) / 10) *
        (1.01005 : ℝ) ^ (wt % 10) := hB
    _ ≤ (exp 1) ^ (wt / 100) * (exp (0.1 : ℝ)) ^ ((wt % 100) / 10) *
        (exp (0.01 : ℝ)) ^ (wt % 10) := by gcongr
    _ = exp ((wt / 100 : ℕ) * (1 : ℝ)) * exp (((wt % 100) / 10 : ℕ) * (0.1 : ℝ)) *
        exp ((wt % 10 : ℕ) * (0.01 : ℝ)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    _ = exp ((wt : ℝ) / 100) := by rw [← Real.exp_add, ← Real.exp_add, hwt]

lemma exp_div_100_lt_of_gt {B wt : ℕ} (hBpos : 0 < B)
    (hB : (2.718282 : ℝ) ^ (wt / 100) * (1.105171 : ℝ) ^ ((wt % 100) / 10) *
      (1.010051 : ℝ) ^ (wt % 10) < (B : ℝ)) :
    (wt : ℝ) / 100 < log (B : ℝ) := by
  rw [lt_log_iff_exp_lt (by exact_mod_cast hBpos)]
  have hexp1 : exp 1 < (2.718282 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hexp10 : exp (0.1 : ℝ) < (1.105171 : ℝ) := by
    have h := Real.exp_bound (x := (0.1 : ℝ)) (by norm_num) (n := 5) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty] at h
    have hf0 : ((Nat.factorial 0 : ℕ) : ℝ) = 1 := by norm_num
    have hf1 : ((Nat.factorial 1 : ℕ) : ℝ) = 1 := by norm_num
    have hf2 : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num
    have hf3 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by exact_mod_cast (by decide : Nat.factorial 3 = 6)
    have hf4 : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by exact_mod_cast (by decide : Nat.factorial 4 = 24)
    have hf5 : ((Nat.factorial 5 : ℕ) : ℝ) = 120 := by exact_mod_cast (by decide : Nat.factorial 5 = 120)
    rw [hf0, hf1, hf2, hf3, hf4, hf5] at h
    norm_num at h
    have hle : |exp (0.1 : ℝ) - (1 + 0.1 + 0.1 ^ 2 / 2 + 0.1 ^ 3 / 6 + 0.1 ^ 4 / 24)| < 0.00000011 := by
      have : (0.1 : ℝ) ^ 5 * ((Nat.succ 5 : ℝ) / (120 * 5)) < 0.00000011 := by norm_num
      linarith
    have habs := abs_lt.mp hle
    linarith
  have hexp01 : exp (0.01 : ℝ) < (1.010051 : ℝ) := by
    have h := Real.exp_bound (x := (0.01 : ℝ)) (by norm_num) (n := 3) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty] at h
    have hf0 : ((Nat.factorial 0 : ℕ) : ℝ) = 1 := by norm_num
    have hf1 : ((Nat.factorial 1 : ℕ) : ℝ) = 1 := by norm_num
    have hf2 : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num
    have hf3 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by exact_mod_cast (by decide : Nat.factorial 3 = 6)
    rw [hf0, hf1, hf2, hf3] at h
    norm_num at h
    have hle : |exp (0.01 : ℝ) - (1 + 0.01 + 0.01 ^ 2 / 2)| < 0.0000005 := by
      have : (0.01 : ℝ) ^ 3 * ((Nat.succ 3 : ℝ) / (6 * 3)) < 0.0000005 := by norm_num
      linarith
    have habs := abs_lt.mp hle
    linarith
  have hwt : (wt : ℝ) / 100 = (wt / 100 : ℕ) * (1 : ℝ) + ((wt % 100) / 10 : ℕ) * (0.1 : ℝ) +
      (wt % 10 : ℕ) * (0.01 : ℝ) := by
    have h12 : 100 * (wt / 100) + 10 * ((wt % 100) / 10) + wt % 10 = wt := by omega
    have hR : (100 : ℝ) * ((wt / 100 : ℕ) : ℝ) + 10 * (((wt % 100) / 10 : ℕ) : ℝ) +
        ((wt % 10 : ℕ) : ℝ) = (wt : ℝ) := by exact_mod_cast h12
    linarith
  calc exp ((wt : ℝ) / 100)
      = exp ((wt / 100 : ℕ) * (1 : ℝ)) * exp (((wt % 100) / 10 : ℕ) * (0.1 : ℝ)) *
        exp ((wt % 10 : ℕ) * (0.01 : ℝ)) := by
        rw [hwt, Real.exp_add, Real.exp_add]
    _ = (exp 1) ^ (wt / 100) * (exp (0.1 : ℝ)) ^ ((wt % 100) / 10) *
        (exp (0.01 : ℝ)) ^ (wt % 10) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    _ ≤ (2.718282 : ℝ) ^ (wt / 100) * (1.105171 : ℝ) ^ ((wt % 100) / 10) *
        (1.010051 : ℝ) ^ (wt % 10) := by
        gcongr
    _ < (B : ℝ) := hB

set_option maxRecDepth 65536 in
lemma wtUb10_nat_ok :
    (List.range 1200).all (fun j =>
      let w := wtUb10 j
      10 * (j + 1) * 100000 ^ (w / 100 + (w % 100) / 10) * 100000 ^ (w % 10) <
        271828 ^ (w / 100) * 110517 ^ ((w % 100) / 10) * 101005 ^ (w % 10)) = true := by
  decide

lemma log_le_wtUb10 {j : ℕ} (hj : j < 1200) :
    log ((10 * (j + 1) : ℕ) : ℝ) ≤ (wtUb10 j : ℝ) / 100 := by
  have h := List.all_eq_true.mp wtUb10_nat_ok j (List.mem_range.mpr hj)
  simp only [decide_eq_true_eq] at h
  have hR : ((10 * (j + 1) : ℕ) : ℝ) <
      (2.71828 : ℝ) ^ (wtUb10 j / 100) * (1.10517 : ℝ) ^ ((wtUb10 j % 100) / 10) *
        (1.01005 : ℝ) ^ (wtUb10 j % 10) := by
    have hnat : ((10 * (j + 1) : ℕ) : ℝ) * (100000 : ℝ) ^ (wtUb10 j / 100 + (wtUb10 j % 100) / 10) *
        (100000 : ℝ) ^ (wtUb10 j % 10) <
        (271828 : ℝ) ^ (wtUb10 j / 100) * (110517 : ℝ) ^ ((wtUb10 j % 100) / 10) *
          (101005 : ℝ) ^ (wtUb10 j % 10) := by
      exact_mod_cast h
    have hpow : (100000 : ℝ) ^ (wtUb10 j / 100 + (wtUb10 j % 100) / 10) *
        (100000 : ℝ) ^ (wtUb10 j % 10) =
        (100000 : ℝ) ^ (wtUb10 j / 100) * (100000 : ℝ) ^ ((wtUb10 j % 100) / 10) *
          (100000 : ℝ) ^ (wtUb10 j % 10) := by
      rw [pow_add, mul_assoc]
    have hpos : (0 : ℝ) < (100000 : ℝ) ^ (wtUb10 j / 100) * (100000 : ℝ) ^ ((wtUb10 j % 100) / 10) *
        (100000 : ℝ) ^ (wtUb10 j % 10) := by positivity
    have hnat2 : ((10 * (j + 1) : ℕ) : ℝ) *
        ((100000 : ℝ) ^ (wtUb10 j / 100) * (100000 : ℝ) ^ ((wtUb10 j % 100) / 10) *
          (100000 : ℝ) ^ (wtUb10 j % 10)) <
        (271828 : ℝ) ^ (wtUb10 j / 100) * (110517 : ℝ) ^ ((wtUb10 j % 100) / 10) *
          (101005 : ℝ) ^ (wtUb10 j % 10) := by
      rw [← hpow]; linarith only [hnat]
    have hdiv : ((10 * (j + 1) : ℕ) : ℝ) <
        ((271828 : ℝ) ^ (wtUb10 j / 100) * (110517 : ℝ) ^ ((wtUb10 j % 100) / 10) *
          (101005 : ℝ) ^ (wtUb10 j % 10)) /
        ((100000 : ℝ) ^ (wtUb10 j / 100) * (100000 : ℝ) ^ ((wtUb10 j % 100) / 10) *
          (100000 : ℝ) ^ (wtUb10 j % 10)) := (lt_div_iff₀ hpos).mpr hnat2
    convert hdiv using 1
    have ha : (2.71828 : ℝ) = 271828 / 100000 := by norm_num
    have hb : (1.10517 : ℝ) = 110517 / 100000 := by norm_num
    have hc : (1.01005 : ℝ) = 101005 / 100000 := by norm_num
    rw [ha, hb, hc, div_pow, div_pow, div_pow]
    ring
  exact (exp_div_100_gt_of_lt (by omega) hR).le

set_option maxRecDepth 65536 in
lemma wtLb10_nat_ok :
    (List.range 1200).all (fun j =>
      j < 1 ||
      let w := wtLb10 j
      2718282 ^ (w / 100) * 1105171 ^ ((w % 100) / 10) * 1010051 ^ (w % 10) <
        10 * j * 1000000 ^ (w / 100 + (w % 100) / 10) * 1000000 ^ (w % 10)) = true := by
  decide

lemma wtLb10_le_log {j : ℕ} (hj1 : 1 ≤ j) (hj : j < 1200) :
    (wtLb10 j : ℝ) / 100 ≤ log ((10 * j : ℕ) : ℝ) := by
  have h := List.all_eq_true.mp wtLb10_nat_ok j (List.mem_range.mpr hj)
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with hlt | h
  · omega
  · have hR : (2.718282 : ℝ) ^ (wtLb10 j / 100) * (1.105171 : ℝ) ^ ((wtLb10 j % 100) / 10) *
        (1.010051 : ℝ) ^ (wtLb10 j % 10) < ((10 * j : ℕ) : ℝ) := by
      have hnat : (2718282 : ℝ) ^ (wtLb10 j / 100) * (1105171 : ℝ) ^ ((wtLb10 j % 100) / 10) *
          (1010051 : ℝ) ^ (wtLb10 j % 10) <
          ((10 * j : ℕ) : ℝ) * (1000000 : ℝ) ^ (wtLb10 j / 100 + (wtLb10 j % 100) / 10) *
            (1000000 : ℝ) ^ (wtLb10 j % 10) := by
        exact_mod_cast h
      have hpow : (1000000 : ℝ) ^ (wtLb10 j / 100 + (wtLb10 j % 100) / 10) *
          (1000000 : ℝ) ^ (wtLb10 j % 10) =
          (1000000 : ℝ) ^ (wtLb10 j / 100) * (1000000 : ℝ) ^ ((wtLb10 j % 100) / 10) *
            (1000000 : ℝ) ^ (wtLb10 j % 10) := by
        rw [pow_add, mul_assoc]
      have hpos : (0 : ℝ) < (1000000 : ℝ) ^ (wtLb10 j / 100) * (1000000 : ℝ) ^ ((wtLb10 j % 100) / 10) *
          (1000000 : ℝ) ^ (wtLb10 j % 10) := by positivity
      have hnat2 : (2718282 : ℝ) ^ (wtLb10 j / 100) * (1105171 : ℝ) ^ ((wtLb10 j % 100) / 10) *
          (1010051 : ℝ) ^ (wtLb10 j % 10) <
          ((10 * j : ℕ) : ℝ) * ((1000000 : ℝ) ^ (wtLb10 j / 100) *
            (1000000 : ℝ) ^ ((wtLb10 j % 100) / 10) * (1000000 : ℝ) ^ (wtLb10 j % 10)) := by
        rw [← hpow]; linarith only [hnat]
      have hdiv : ((2718282 : ℝ) ^ (wtLb10 j / 100) * (1105171 : ℝ) ^ ((wtLb10 j % 100) / 10) *
            (1010051 : ℝ) ^ (wtLb10 j % 10)) /
          ((1000000 : ℝ) ^ (wtLb10 j / 100) * (1000000 : ℝ) ^ ((wtLb10 j % 100) / 10) *
            (1000000 : ℝ) ^ (wtLb10 j % 10)) < ((10 * j : ℕ) : ℝ) := (div_lt_iff₀ hpos).mpr hnat2
      convert hdiv using 1
      have ha : (2.718282 : ℝ) = 2718282 / 1000000 := by norm_num
      have hb : (1.105171 : ℝ) = 1105171 / 1000000 := by norm_num
      have hc : (1.010051 : ℝ) = 1010051 / 1000000 := by norm_num
      rw [ha, hb, hc, div_pow, div_pow, div_pow]
      ring
    exact (exp_div_100_lt_of_gt (by omega) hR).le

lemma card_filter_range_eq_length_filter (n : ℕ) (P : ℕ → Bool) :
    ((Finset.range n).filter (fun r => P r = true)).card = ((List.range n).filter P).length := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.range_add_one, Finset.filter_insert, List.range_succ, List.filter_append, List.length_append]
    by_cases h : P n = true
    · rw [if_pos h, Finset.card_insert_of_notMem (by simp), ih]
      simp [h]
    · rw [if_neg h, ih]
      simp [Bool.eq_false_iff.mpr h]

lemma theta_nat_eq_sum_primesLE (N : ℕ) :
    Chebyshev.theta (N : ℝ) = ∑ p ∈ Nat.primesLE N, log (p : ℝ) := by
  unfold Chebyshev.theta
  have hfl : ⌊(N : ℝ)⌋₊ = N := Nat.floor_natCast N
  rw [hfl]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_primesLE]
  exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨h.2.pos, h.1⟩, h.2⟩⟩

lemma theta_105_and_070_small {y : ℕ} (hy1 : 200 ≤ y) (hy2 : y < 12000) :
    0.74 * (y : ℝ) ≤ Chebyshev.theta (y : ℝ) ∧ Chebyshev.theta (y : ℝ) ≤ 1.05 * (y : ℝ) := by
  set j := y / 10
  have hj20 : 20 ≤ j := by omega
  have hj1200 : j < 1200 := by omega
  have hblk := blocks1200_bounds hj20 hj1200
  have hfl_ub : Chebyshev.theta (y : ℝ) ≤ ∑ i ∈ Finset.range (j + 1), (blockCnt10 i : ℝ) * ((wtUb10 i : ℝ) / 100) := by
    rw [theta_nat_eq_sum_primesLE]
    have hsub : Nat.primesLE y ⊆ (Finset.range (j + 1)).biUnion
        (fun i => (Finset.range 10).image (fun r => 10 * i + r) |>.filter (fun n => isCand12000 n = true)) := by
      intro p hp
      rw [Nat.mem_primesLE] at hp
      rw [Finset.mem_biUnion]
      refine ⟨p / 10, Finset.mem_range.mpr (by omega), ?_⟩
      rw [Finset.mem_filter, Finset.mem_image]
      refine ⟨⟨p % 10, Finset.mem_range.mpr (Nat.mod_lt _ (by omega)), Nat.div_add_mod p 10⟩, ?_⟩
      exact (isCand12000_iff_prime (by omega)).mpr hp.2
    calc ∑ p ∈ Nat.primesLE y, log (p : ℝ)
        ≤ ∑ p ∈ (Finset.range (j + 1)).biUnion
            (fun i => (Finset.range 10).image (fun r => 10 * i + r) |>.filter (fun n => isCand12000 n = true)),
            log (p : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
          intro p hp _
          rw [Finset.mem_biUnion] at hp
          rcases hp with ⟨i, _, hp'⟩
          rw [Finset.mem_filter, Finset.mem_image] at hp'
          rcases hp'.1 with ⟨r, _, rfl⟩
          have hp2 : 2 ≤ 10 * i + r := by
            by_contra hlt
            have : isCand12000 (10 * i + r) = false := by
              unfold isCand12000; rw [if_pos (by omega)]
            rw [this] at hp'; exact absurd hp'.2 Bool.false_ne_true
          exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 10 * i + r))
      _ = ∑ i ∈ Finset.range (j + 1),
            ∑ p ∈ ((Finset.range 10).image (fun r => 10 * i + r)).filter (fun n => isCand12000 n = true),
            log (p : ℝ) := by
          rw [Finset.sum_biUnion]
          intro i1 _ i2 _ hne s hs1 hs2 p hp
          have hp1 := hs1 hp; have hp2 := hs2 hp
          rw [Finset.mem_filter, Finset.mem_image] at hp1 hp2
          rcases hp1.1 with ⟨r1, hr1, h1⟩; rcases hp2.1 with ⟨r2, hr2, h2⟩
          rw [Finset.mem_range] at hr1 hr2
          omega
      _ ≤ ∑ i ∈ Finset.range (j + 1), (blockCnt10 i : ℝ) * ((wtUb10 i : ℝ) / 100) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [Finset.mem_range] at hi
          have hlog_i := log_le_wtUb10 (by omega : i < 1200)
          have hcard : (((Finset.range 10).image (fun r => 10 * i + r)).filter (fun n => isCand12000 n = true)).card = blockCnt10 i := by
            unfold blockCnt10
            rw [Finset.filter_image, Finset.card_image_of_injective _ (fun a b hab => by omega)]
            exact card_filter_range_eq_length_filter 10 (fun r => isCand12000 (10 * i + r))
          calc ∑ p ∈ ((Finset.range 10).image (fun r => 10 * i + r)).filter (fun n => isCand12000 n = true), log (p : ℝ)
              ≤ ∑ _ ∈ ((Finset.range 10).image (fun r => 10 * i + r)).filter (fun n => isCand12000 n = true), ((wtUb10 i : ℝ) / 100) := by
                refine Finset.sum_le_sum fun p hp => ?_
                rw [Finset.mem_filter, Finset.mem_image] at hp
                rcases hp.1 with ⟨r, hr, rfl⟩
                rw [Finset.mem_range] at hr
                have hle : ((10 * i + r : ℕ) : ℝ) ≤ ((10 * (i + 1) : ℕ) : ℝ) := by exact_mod_cast (by omega : 10 * i + r ≤ 10 * (i + 1))
                have hpos : 0 < ((10 * i + r : ℕ) : ℝ) := by
                  have : 2 ≤ 10 * i + r := by
                    by_contra hlt
                    have : isCand12000 (10 * i + r) = false := by unfold isCand12000; rw [if_pos (by omega)]
                    rw [this] at hp; exact absurd hp.2 Bool.false_ne_true
                  exact_mod_cast (by omega : 0 < 10 * i + r)
                exact (Real.log_le_log hpos hle).trans hlog_i
            _ = (blockCnt10 i : ℝ) * ((wtUb10 i : ℝ) / 100) := by
                rw [Finset.sum_const, hcard, nsmul_eq_mul]
  have hub_final : Chebyshev.theta (y : ℝ) ≤ 1.05 * (y : ℝ) := by
    have hblkR : (∑ i ∈ Finset.range (j + 1), (blockCnt10 i : ℝ) * ((wtUb10 i : ℝ) / 100)) ≤ 1.05 * ((10 * j : ℕ) : ℝ) := by
      have h1 : (∑ i ∈ Finset.range (j + 1), blockCnt10 i * wtUb10 i : ℕ) ≤ 105 * (10 * j) := hblk.2
      have h1R : (∑ i ∈ Finset.range (j + 1), (blockCnt10 i : ℝ) * (wtUb10 i : ℝ)) ≤ 105 * ((10 * j : ℕ) : ℝ) := by
        exact_mod_cast h1
      have hdiv : (∑ i ∈ Finset.range (j + 1), (blockCnt10 i : ℝ) * ((wtUb10 i : ℝ) / 100)) =
          (∑ i ∈ Finset.range (j + 1), (blockCnt10 i : ℝ) * (wtUb10 i : ℝ)) / 100 := by
        rw [Finset.sum_div]; refine Finset.sum_congr rfl fun _ _ => by ring
      linarith
    have hjy : ((10 * j : ℕ) : ℝ) ≤ (y : ℝ) := by exact_mod_cast (by omega : 10 * j ≤ y)
    linarith
  have hfl_lb : ∑ i ∈ Finset.range j, (blockCnt10 i : ℝ) * ((wtLb10 i : ℝ) / 100) ≤ Chebyshev.theta (y : ℝ) := by
    rw [theta_nat_eq_sum_primesLE]
    have hsub : (Finset.range j).biUnion
        (fun i => (Finset.range 10).image (fun r => 10 * i + r) |>.filter (fun n => isCand12000 n = true)) ⊆
        Nat.primesLE y := by
      intro p hp
      rw [Finset.mem_biUnion] at hp
      rcases hp with ⟨i, hi, hp'⟩
      rw [Finset.mem_range] at hi
      rw [Finset.mem_filter, Finset.mem_image] at hp'
      rcases hp'.1 with ⟨r, hr, rfl⟩
      rw [Finset.mem_range] at hr
      rw [Nat.mem_primesLE]
      exact ⟨by omega, (isCand12000_iff_prime (by omega)).mp hp'.2⟩
    calc ∑ i ∈ Finset.range j, (blockCnt10 i : ℝ) * ((wtLb10 i : ℝ) / 100)
        ≤ ∑ i ∈ Finset.range j,
            ∑ p ∈ ((Finset.range 10).image (fun r => 10 * i + r)).filter (fun n => isCand12000 n = true),
            log (p : ℝ) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [Finset.mem_range] at hi
          by_cases hi0 : i = 0
          · subst hi0
            have hwt0 : wtLb10 0 = 0 := rfl
            rw [hwt0]
            simp only [Nat.cast_zero, zero_div, mul_zero]
            refine Finset.sum_nonneg fun p hp => ?_
            rw [Finset.mem_filter, Finset.mem_image] at hp
            rcases hp.1 with ⟨r, _, rfl⟩
            have hp2 : 2 ≤ 10 * 0 + r := by
              by_contra hlt
              have hfalse : isCand12000 (10 * 0 + r) = false := by unfold isCand12000; rw [if_pos (by omega)]
              simp only [Nat.mul_zero, zero_add] at hfalse
              simp only [zero_add] at hp
              rw [hfalse] at hp; exact absurd hp.2 Bool.false_ne_true
            exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 10 * 0 + r))
          · have hlog_i := wtLb10_le_log (by omega : 1 ≤ i) (by omega : i < 1200)
            have hcard : (((Finset.range 10).image (fun r => 10 * i + r)).filter (fun n => isCand12000 n = true)).card = blockCnt10 i := by
              unfold blockCnt10
              rw [Finset.filter_image, Finset.card_image_of_injective _ (fun a b hab => by omega)]
              exact card_filter_range_eq_length_filter 10 (fun r => isCand12000 (10 * i + r))
            calc (blockCnt10 i : ℝ) * ((wtLb10 i : ℝ) / 100)
                = ∑ _ ∈ ((Finset.range 10).image (fun r => 10 * i + r)).filter (fun n => isCand12000 n = true), ((wtLb10 i : ℝ) / 100) := by
                  rw [Finset.sum_const, hcard, nsmul_eq_mul]
              _ ≤ ∑ p ∈ ((Finset.range 10).image (fun r => 10 * i + r)).filter (fun n => isCand12000 n = true), log (p : ℝ) := by
                  refine Finset.sum_le_sum fun p hp => ?_
                  rw [Finset.mem_filter, Finset.mem_image] at hp
                  rcases hp.1 with ⟨r, _, rfl⟩
                  have hle : ((10 * i : ℕ) : ℝ) ≤ ((10 * i + r : ℕ) : ℝ) := by exact_mod_cast (by omega : 10 * i ≤ 10 * i + r)
                  exact hlog_i.trans (Real.log_le_log (by exact_mod_cast (by omega : 0 < 10 * i)) hle)
      _ = ∑ p ∈ (Finset.range j).biUnion
            (fun i => (Finset.range 10).image (fun r => 10 * i + r) |>.filter (fun n => isCand12000 n = true)),
            log (p : ℝ) := by
          rw [Finset.sum_biUnion]
          intro i1 _ i2 _ hne s hs1 hs2 p hp
          have hp1 := hs1 hp; have hp2 := hs2 hp
          rw [Finset.mem_filter, Finset.mem_image] at hp1 hp2
          rcases hp1.1 with ⟨r1, hr1, h1⟩; rcases hp2.1 with ⟨r2, hr2, h2⟩
          rw [Finset.mem_range] at hr1 hr2
          omega
      _ ≤ ∑ p ∈ Nat.primesLE y, log (p : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
          intro p hp _
          rw [Nat.mem_primesLE] at hp
          exact Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le)
  have hlb_final : 0.74 * (y : ℝ) ≤ Chebyshev.theta (y : ℝ) := by
    have hblkR : 0.74 * ((10 * (j + 1) : ℕ) : ℝ) ≤ ∑ i ∈ Finset.range j, (blockCnt10 i : ℝ) * ((wtLb10 i : ℝ) / 100) := by
      have h1 : 74 * (10 * (j + 1)) ≤ ∑ i ∈ Finset.range j, blockCnt10 i * wtLb10 i := hblk.1
      have h1R : 74 * ((10 * (j + 1) : ℕ) : ℝ) ≤ ∑ i ∈ Finset.range j, (blockCnt10 i : ℝ) * (wtLb10 i : ℝ) := by
        exact_mod_cast h1
      have hdiv : (∑ i ∈ Finset.range j, (blockCnt10 i : ℝ) * ((wtLb10 i : ℝ) / 100)) =
          (∑ i ∈ Finset.range j, (blockCnt10 i : ℝ) * (wtLb10 i : ℝ)) / 100 := by
        rw [Finset.sum_div]; refine Finset.sum_congr rfl fun _ _ => by ring
      linarith
    have hyj : (y : ℝ) ≤ ((10 * (j + 1) : ℕ) : ℝ) := by exact_mod_cast (by omega : y ≤ 10 * (j + 1))
    linarith
  exact ⟨hlb_final, hub_final⟩

lemma theta_ge_072_10k {n : ℕ} (hn : 10000 ≤ n) :
    0.72 * (n : ℝ) ≤ Chebyshev.theta n := by
  have hnR : (10000 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 := Chebyshev.psi_sub_theta_le (show (1 : ℝ) ≤ n by linarith)
  have h2 := psi_ge_cheb (show (30 : ℝ) ≤ n by linarith)
  have hlog10k : log 10000 < 9.3 := by
    rw [log_lt_iff_lt_exp (by norm_num)]
    have hexp_lb : (2.71828 : ℝ) < exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
    have hpow : (10000 : ℝ) ^ (10 : ℕ) < (exp 1) ^ (93 : ℕ) := by
      calc (10000 : ℝ) ^ (10 : ℕ) < (2.71828 : ℝ) ^ (93 : ℕ) := by norm_num
        _ < (exp 1) ^ (93 : ℕ) := by gcongr
    have hexp_pow : (10000 : ℝ) ^ (10 : ℕ) < (exp (9.3 : ℝ)) ^ (10 : ℕ) := by
      rw [← Real.exp_nat_mul]
      have h93 : (10 : ℕ) * (9.3 : ℝ) = (93 : ℕ) * (1 : ℝ) := by norm_num
      rw [h93, Real.exp_nat_mul]
      exact hpow
    exact lt_of_pow_lt_pow_left₀ 10 (by positivity) hexp_pow
  have hlog : log (n : ℝ) ≤ 5.3 + 4 * √(√((n : ℝ) / 10000)) := by
    have ht : 0 < (n : ℝ) / 10000 := by positivity
    have hq : 0 < √(√((n : ℝ) / 10000)) := by positivity
    have hpow4 : (√(√((n : ℝ) / 10000))) ^ (4 : ℕ) = (n : ℝ) / 10000 := by
      calc (√(√((n : ℝ) / 10000))) ^ (4 : ℕ)
          = ((√(√((n : ℝ) / 10000))) ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
        _ = (√((n : ℝ) / 10000)) ^ (2 : ℕ) := by rw [Real.sq_sqrt (by positivity)]
        _ = (n : ℝ) / 10000 := Real.sq_sqrt (by positivity)
    have hlog_div : log ((n : ℝ) / 10000) = 4 * log (√(√((n : ℝ) / 10000))) := by
      nth_rw 1 [← hpow4]
      rw [Real.log_pow]
      norm_num
    have hle1 : log (√(√((n : ℝ) / 10000))) ≤ √(√((n : ℝ) / 10000)) - 1 :=
      Real.log_le_sub_one_of_pos hq
    have hmul : log (n : ℝ) = log ((n : ℝ) / 10000) + log 10000 := by
      rw [← Real.log_mul (by positivity) (by norm_num), div_mul_cancel₀ _ (by norm_num)]
    linarith
  have hsqrt100 : 100 ≤ √n := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    linarith
  have hrt4 : √(√((n : ℝ) / 10000)) ≤ √n / 100 := by
    have h1' : 1 ≤ (n : ℝ) / 10000 := by linarith
    have h2' : 1 ≤ √((n : ℝ) / 10000) := Real.one_le_sqrt.mpr h1'
    have h3' : √(√((n : ℝ) / 10000)) ≤ √((n : ℝ) / 10000) := by
      rw [Real.sqrt_le_left (by positivity)]; nlinarith
    have h4' : √((n : ℝ) / 10000) = √n / 100 := by
      rw [Real.sqrt_div (by positivity), show (10000 : ℝ) = 100 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith
  have hsq_n : √n * √n = n := Real.mul_self_sqrt (by positivity)
  have h2sqrt : 2 * √n * log n ≤ 0.186 * n := by
    have h1' : 2 * √n * log n ≤ 2 * √n * (5.3 + 4 * (√n / 100)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hsqrt_le : √n ≤ (√n * √n) / 100 := by
      calc √n = √n * 1 := by ring
        _ ≤ √n * (√n / 100) := mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)
        _ = (√n * √n) / 100 := by ring
    calc 2 * √n * log n ≤ 2 * √n * (5.3 + 4 * (√n / 100)) := h1'
      _ = 10.6 * √n + (8 / 100) * (√n * √n) := by ring
      _ ≤ 10.6 * ((√n * √n) / 100) + (8 / 100) * n := by linarith
      _ = (18.6 / 100) * n := by rw [hsq_n]; ring
      _ = 0.186 * n := by norm_num
  have hlog_n1 : 5 * log ((n : ℝ) + 1) ≤ 0.005 * n := by
    have hn1_le : (n : ℝ) + 1 ≤ 2 * n := by linarith
    have hlog1' : log ((n : ℝ) + 1) ≤ log (2 * n) := Real.log_le_log (by linarith) hn1_le
    have hlog2' : log (2 * n) = log 2 + log n := Real.log_mul (by norm_num) (by linarith)
    have hlog2_ub : log 2 < 0.7 := lt_trans Real.log_two_lt_d9 (by norm_num)
    have hsqrt_le : √n ≤ n / 100 := by
      calc √n = √n * 1 := by ring
        _ ≤ √n * (√n / 100) := by nlinarith [Real.sqrt_nonneg n]
        _ = (√n * √n) / 100 := by ring
        _ = n / 100 := by rw [hsq_n]
    linarith
  linarith

lemma theta_le_126_10k {n : ℕ} (hn : 10000 ≤ n) :
    Chebyshev.theta n ≤ 1.26 * (n : ℝ) := by
  have hnR : (10000 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 := Chebyshev.theta_le_psi (n : ℝ)
  have h2 := psi_le_cheb (show (0 : ℝ) ≤ n by positivity)
  have hlog10k : log 10000 < 10 := by
    rw [log_lt_iff_lt_exp (by norm_num)]
    calc (10000 : ℝ) < (2.71828 : ℝ) ^ (10 : ℕ) := by norm_num
      _ < (exp 1) ^ (10 : ℕ) := by gcongr; exact lt_trans (by norm_num) Real.exp_one_gt_d9
      _ = exp 10 := by rw [← Real.exp_nat_mul]; norm_num
  have hlog : log ((n : ℝ) + 31) ≤ 6 + 4 * √(√(((n : ℝ) + 31) / 10000)) := by
    have h := log_le_add_four_sqrt_sqrt (x := (n : ℝ) + 31) (M := 10000) (by norm_num) (by linarith)
    linarith
  have hsqrt_le : √(√(((n : ℝ) + 31) / 10000)) ≤ √(((n : ℝ) + 31) / 10000) := by
    have h1' : 1 ≤ ((n : ℝ) + 31) / 10000 := by linarith
    have h2' : 1 ≤ √(((n : ℝ) + 31) / 10000) := Real.one_le_sqrt.mpr h1'
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hsq_le : (√(((n : ℝ) + 31) / 10000)) ^ (2 : ℕ) = ((n : ℝ) + 31) / 10000 :=
    Real.sq_sqrt (by positivity)
  have hlog_nn : 0 ≤ log ((n : ℝ) + 31) := Real.log_nonneg (by linarith)
  have hsq : (log ((n : ℝ) + 31)) ^ 2 ≤ (6 + 4 * √(((n : ℝ) + 31) / 10000)) ^ 2 := by
    nlinarith
  have hsq_ab : (6 + 4 * √(((n : ℝ) + 31) / 10000)) ^ 2 ≤
      2 * 6 ^ 2 + 2 * (4 * √(((n : ℝ) + 31) / 10000)) ^ 2 := by
    nlinarith [sq_nonneg (6 - 4 * √(((n : ℝ) + 31) / 10000))]
  have h2sq : (4 * √(((n : ℝ) + 31) / 10000)) ^ 2 = 16 * (((n : ℝ) + 31) / 10000) := by
    calc (4 * √(((n : ℝ) + 31) / 10000)) ^ 2
        = 16 * (√(((n : ℝ) + 31) / 10000)) ^ (2 : ℕ) := by ring
      _ = 16 * (((n : ℝ) + 31) / 10000) := by rw [hsq_le]
  linarith

lemma theta_ge_070 {y : ℕ} (hy : 200 ≤ y) :
    0.70 * (y : ℝ) ≤ Chebyshev.theta (y : ℝ) := by
  by_cases hy12 : y < 12000
  · linarith [(theta_105_and_070_small hy hy12).1]
  · exact (by linarith [theta_ge_072_10k (by omega : 10000 ≤ y)])

lemma theta_le_small_or_large {y : ℕ} (hy : 200 ≤ y) :
    (y < 12000 → Chebyshev.theta (y : ℝ) ≤ 1.05 * (y : ℝ)) ∧
    (10000 ≤ y → Chebyshev.theta (y : ℝ) ≤ 1.26 * (y : ℝ)) :=
  ⟨fun h => (theta_105_and_070_small hy h).2, fun h => theta_le_126_10k h⟩

lemma exists_prime_between_mul {y : ℕ} (hy : 200 ≤ y) :
    ∃ q, q.Prime ∧ y < q ∧ q ≤ 10 * y := by
  have h1 : 0.70 * ((10 * y : ℕ) : ℝ) ≤ Chebyshev.theta ((10 * y : ℕ) : ℝ) :=
    theta_ge_070 (by omega)
  have h2 : Chebyshev.theta (y : ℝ) ≤ 1.26 * (y : ℝ) := by
    by_cases hy12 : y < 12000
    · linarith [(theta_105_and_070_small hy hy12).2]
    · exact theta_le_126_10k (by omega)
  have hdiff : 0 < Chebyshev.theta ((10 * y : ℕ) : ℝ) - Chebyshev.theta (y : ℝ) := by
    have h10 : ((10 * y : ℕ) : ℝ) = 10 * (y : ℝ) := by push_cast; ring
    have hypos : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
    linarith
  rw [theta_nat_eq_sum_primesLE, theta_nat_eq_sum_primesLE] at hdiff
  have hsub : Nat.primesLE y ⊆ Nat.primesLE (10 * y) := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨by omega, hp.2⟩
  rw [← Finset.sum_sdiff hsub] at hdiff
  have hpos_sum : 0 < ∑ p ∈ Nat.primesLE (10 * y) \ Nat.primesLE y, log (p : ℝ) := by linarith
  have hne : (Nat.primesLE (10 * y) \ Nat.primesLE y).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Finset.sum_empty] at hpos_sum
    linarith
  rcases hne with ⟨q, hq⟩
  rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE] at hq
  refine ⟨q, hq.1.2, ?_, hq.1.1⟩
  by_contra hle
  exact hq.2 ⟨by omega, hq.1.2⟩

lemma exists_large_gap_below {y : ℕ} (hy : 200 ≤ y) :
    ∃ a N : ℕ, 10000000 ≤ N ∧ pNth a < N ∧ N < pNth (a + 1) ∧
      2 * (y : ℝ) + 2 ≤ (pNth (a + 1) : ℝ) - (pNth a : ℝ) ∧
      Chebyshev.theta (y : ℝ) ≤ log (N : ℝ) ∧
      log (N : ℝ) ≤ Chebyshev.theta (y : ℝ) + log ((1001 * y ^ 2 : ℕ) : ℝ) := by
  obtain ⟨q₁, hq1p, hq1_gt, hq1_le⟩ := exists_prime_between_mul hy
  obtain ⟨q₂, hq2p, hq2_gt, hq2_le⟩ := exists_prime_between_mul (by omega : 200 ≤ 10 * y)
  set P := ∏ p ∈ Nat.primesLE y, p
  have hP_pos : 0 < P := Finset.prod_pos fun p hp => (Nat.mem_primesLE.mp hp).2.pos
  have hP_ge_10m : 10000000 ≤ P := by
    have hsub : ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ) ⊆ Nat.primesLE y := by
      intro p hp
      rw [Nat.mem_primesLE]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨by omega, by decide⟩
    have hprod_le : ∏ p ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ), p ≤ P := by
      refine Finset.prod_le_prod_of_subset_of_one_le' hsub fun p hp _ => ?_
      exact (Nat.mem_primesLE.mp hp).2.one_lt.le
    have hval : ∏ p ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ), p = 6469693230 := by
      decide
    omega
  have hlogP : log (P : ℝ) = Chebyshev.theta (y : ℝ) := by
    rw [theta_nat_eq_sum_primesLE, Nat.cast_prod, Real.log_prod]
    intro p hp
    exact_mod_cast (Nat.mem_primesLE.mp hp).2.ne_zero
  have h100y_lt_P : 100 * y < P := by
    have hth : 0.70 * (y : ℝ) ≤ log (P : ℝ) := hlogP ▸ theta_ge_070 hy
    have hlog_100y : log ((100 * y : ℕ) : ℝ) < 0.70 * (y : ℝ) := by
      have hyR : (200 : ℝ) ≤ y := by exact_mod_cast hy
      have hlog100 : log 100 < 5 := by
        rw [log_lt_iff_lt_exp (by norm_num)]
        calc (100 : ℝ) < (2.71828 : ℝ) ^ (5 : ℕ) := by norm_num
          _ < (exp 1) ^ (5 : ℕ) := by gcongr; exact lt_trans (by norm_num) Real.exp_one_gt_d9
          _ = exp 5 := by rw [← Real.exp_nat_mul]; norm_num
      have hlogy : log (y : ℝ) ≤ (y : ℝ) / 10 + 1.5 := by
        have h1 := Real.log_le_sub_one_of_pos (show 0 < (y : ℝ) / 10 by positivity)
        have h2 : log (y : ℝ) = log ((y : ℝ) / 10) + log 10 := by
          rw [← Real.log_mul (by positivity) (by norm_num), div_mul_cancel₀ _ (by norm_num)]
        have hlog10 : log 10 < 2.5 := by
          rw [log_lt_iff_lt_exp (by norm_num)]
          have hexp_lb : (2.71828 : ℝ) < exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
          have hpow : (10 : ℝ) ^ (2 : ℕ) < (exp 1) ^ (5 : ℕ) := by
            calc (10 : ℝ) ^ (2 : ℕ) < (2.71828 : ℝ) ^ (5 : ℕ) := by norm_num
              _ < (exp 1) ^ (5 : ℕ) := by gcongr
          have hexp_pow : (10 : ℝ) ^ (2 : ℕ) < (exp (2.5 : ℝ)) ^ (2 : ℕ) := by
            rw [← Real.exp_nat_mul]
            have h5 : (2 : ℕ) * (2.5 : ℝ) = (5 : ℕ) * (1 : ℝ) := by norm_num
            rw [h5, Real.exp_nat_mul]
            exact hpow
          exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hexp_pow
        linarith
      have hmul : log ((100 * y : ℕ) : ℝ) = log 100 + log (y : ℝ) := by
        rw [Nat.cast_mul, Real.log_mul (by norm_num) (by positivity)]
        norm_num
      linarith
    have hltR : ((100 * y : ℕ) : ℝ) < (P : ℝ) := by
      have h100y_pos : (0 : ℝ) < ((100 * y : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
      have hP_posR : (0 : ℝ) < (P : ℝ) := Nat.cast_pos.mpr hP_pos
      rw [← Real.exp_log h100y_pos, ← Real.exp_log hP_posR]
      exact Real.exp_lt_exp.mpr (hlog_100y.trans_le hth)
    exact_mod_cast hltR
  have hcop_P : ∀ q, q.Prime → y < q → Nat.Coprime P q := by
    intro q hqp hqy
    rw [Nat.coprime_comm, hqp.coprime_iff_not_dvd]
    intro hdvd
    have hex : ∃ p ∈ Nat.primesLE y, q ∣ p := by
      have hmem : ∀ S : Finset ℕ, q ∣ ∏ p ∈ S, p → ∃ p ∈ S, q ∣ p := by
        intro S hS
        induction S using Finset.induction_on with
        | empty =>
          rw [Finset.prod_empty] at hS
          exact absurd (Nat.dvd_one.mp hS) hqp.ne_one
        | @insert a s ha ih =>
          rw [Finset.prod_insert ha] at hS
          rcases hqp.prime.dvd_mul.mp hS with hqa | hqs
          · exact ⟨a, Finset.mem_insert_self a s, hqa⟩
          · obtain ⟨p, hp, hqp_dvd⟩ := ih hqs
            exact ⟨p, Finset.mem_insert_of_mem hp, hqp_dvd⟩
      exact hmem (Nat.primesLE y) hdvd
    rcases hex with ⟨p, hp_mem, hqp_dvd⟩
    rw [Nat.mem_primesLE] at hp_mem
    rcases (Nat.dvd_prime hp_mem.2).mp hqp_dvd with h1 | rfl
    · exact hqp.ne_one h1
    · omega
  have hcop1 : Nat.Coprime P q₁ := hcop_P q₁ hq1p hq1_gt
  have hcop2 : Nat.Coprime P q₂ := hcop_P q₂ hq2p (by omega)
  have hcop12 : Nat.Coprime q₁ q₂ := by
    rw [hq1p.coprime_iff_not_dvd]
    intro hdvd
    rcases (Nat.dvd_prime hq2p).mp hdvd with h1 | rfl
    · exact hq1p.ne_one h1
    · omega
  obtain ⟨n₁, hn1_P, hn1_q1⟩ := Nat.chineseRemainder hcop1 0 (q₁ - 1)
  have hcop_Pq1_q2 : Nat.Coprime (P * q₁) q₂ := hcop2.mul_left hcop12
  obtain ⟨n₂, hn2_Pq1, hn2_q2⟩ := Nat.chineseRemainder hcop_Pq1_q2 n₁ 1
  set M := P * q₁ * q₂
  have hM_pos : 0 < M := mul_pos (mul_pos hP_pos hq1p.pos) hq2p.pos
  set r := n₂ % M
  set N := if r ≤ y then r + M else r
  have hN_gt_y : y < N := by
    dsimp [N]
    split_ifs with h
    · have hyP : y < P := by omega
      have hM_gt : y < M := by
        dsimp [M]
        exact hyP.trans_le ((Nat.le_mul_of_pos_right P hq1p.pos).trans (Nat.le_mul_of_pos_right _ hq2p.pos))
      omega
    · omega
  have hN_le : N ≤ M + y := by
    dsimp [N]
    split_ifs with h
    · omega
    · have := Nat.mod_lt n₂ hM_pos
      omega
  have hN_mod : N ≡ n₂ [MOD M] := by
    dsimp [N]
    split_ifs with h
    · rw [Nat.ModEq, Nat.add_mod_right, Nat.mod_mod]
    · exact Nat.mod_modEq n₂ M
  have hP_dvd_N : P ∣ N := by
    have h1 : N ≡ 0 [MOD P] := by
      have hm1 : N ≡ n₂ [MOD P] := hN_mod.of_dvd (dvd_mul_of_dvd_left (dvd_mul_right P q₁) q₂)
      have hm2 : n₂ ≡ n₁ [MOD P] := hn2_Pq1.of_dvd (dvd_mul_right P q₁)
      exact hm1.trans (hm2.trans hn1_P)
    exact Nat.dvd_of_mod_eq_zero (by simpa [Nat.ModEq] using h1)
  have hq1_dvd_N1 : q₁ ∣ N + 1 := by
    have h1 : N ≡ q₁ - 1 [MOD q₁] := by
      have hm1 : N ≡ n₂ [MOD q₁] := hN_mod.of_dvd (dvd_mul_of_dvd_left (dvd_mul_left q₁ P) q₂)
      have hm2 : n₂ ≡ n₁ [MOD q₁] := hn2_Pq1.of_dvd (dvd_mul_left q₁ P)
      exact hm1.trans (hm2.trans hn1_q1)
    have hq1_pos : 0 < q₁ := hq1p.pos
    have hmod : (N + 1) % q₁ = 0 := by
      rw [Nat.add_mod]
      have hNmod : N % q₁ = (q₁ - 1) % q₁ := h1
      rw [hNmod, ← Nat.add_mod]
      have : q₁ - 1 + 1 = q₁ := Nat.sub_add_cancel hq1_pos
      rw [this, Nat.mod_self]
    exact Nat.dvd_of_mod_eq_zero hmod
  have hq2_dvd_N1 : q₂ ∣ N - 1 := by
    have h1 : N ≡ 1 [MOD q₂] := (hN_mod.of_dvd (dvd_mul_left q₂ (P * q₁))).trans hn2_q2
    have hq2_1 : 1 < q₂ := hq2p.one_lt
    have hmod : (N - 1) % q₂ = 0 := by
      have hNmod : N % q₂ = 1 % q₂ := h1
      rw [Nat.mod_eq_of_lt hq2_1] at hNmod
      have hsub : N = N - 1 + 1 := (Nat.sub_add_cancel (by omega)).symm
      rw [hsub, Nat.add_mod] at hNmod
      have h1mod : 1 % q₂ = 1 := Nat.mod_eq_of_lt hq2_1
      rw [h1mod] at hNmod
      have h0 : (N - 1) % q₂ < q₂ := Nat.mod_lt _ hq2p.pos
      rcases Nat.lt_or_ge ((N - 1) % q₂ + 1) q₂ with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt] at hNmod; omega
      · have heq : (N - 1) % q₂ + 1 = q₂ := by omega
        rw [heq, Nat.mod_self] at hNmod; omega
    exact Nat.dvd_of_mod_eq_zero hmod
  have hP_le_N : P ≤ N := Nat.le_of_dvd (by omega) hP_dvd_N
  have hN_ge_10m : 10000000 ≤ N := hP_ge_10m.trans hP_le_N
  have hgap_comp : ∀ m, N - y ≤ m → m ≤ N + y → ¬ m.Prime := by
    intro m hm1 hm2 hm_prime
    by_cases hmN : m = N
    · subst hmN
      have h2dvd : 2 ∣ P := Finset.dvd_prod_of_mem _ (Nat.mem_primesLE.mpr ⟨by omega, Nat.prime_two⟩)
      rcases (Nat.dvd_prime hm_prime).mp (h2dvd.trans hP_dvd_N) with h1 | h2
      · omega
      · have : 2 < N := by omega
        omega
    · by_cases hmN1 : m = N + 1
      · subst hmN1
        rcases (Nat.dvd_prime hm_prime).mp hq1_dvd_N1 with h1 | h2
        · exact hq1p.ne_one h1
        · omega
      · by_cases hmN2 : m = N - 1
        · subst hmN2
          rcases (Nat.dvd_prime hm_prime).mp hq2_dvd_N1 with h1 | h2
          · exact hq2p.ne_one h1
          · have hq2_odd : q₂ % 2 = 1 := by
              rcases hq2p.eq_two_or_odd with rfl | hodd
              · omega
              · exact hodd
            have hq2_lt_100y : q₂ < 100 * y := by
              have h100 : q₂ ≤ 10 * (10 * y) := hq2_le
              omega
            have hq2_lt_P : q₂ + 1 < P := by omega
            omega
        · by_cases hlt : m < N
          · have hd_ge2 : 2 ≤ N - m := by omega
            have hd_le_y : N - m ≤ y := by omega
            set p := (N - m).minFac
            have hp_prime : p.Prime := Nat.minFac_prime (by omega)
            have hp_dvd_d : p ∣ N - m := Nat.minFac_dvd (N - m)
            have hp_le_y : p ≤ y := (Nat.minFac_le (by omega)).trans hd_le_y
            have hp_dvd_P : p ∣ P :=
              Finset.dvd_prod_of_mem _ (Nat.mem_primesLE.mpr ⟨hp_le_y, hp_prime⟩)
            have hp_dvd_N : p ∣ N := hp_dvd_P.trans hP_dvd_N
            have hm_eq : m = N - (N - m) := by omega
            have hp_dvd_m : p ∣ m := hm_eq ▸ Nat.dvd_sub hp_dvd_N hp_dvd_d
            rcases (Nat.dvd_prime hm_prime).mp hp_dvd_m with h1 | hpm
            · exact hp_prime.ne_one h1
            · omega
          · have hd_ge2 : 2 ≤ m - N := by omega
            have hd_le_y : m - N ≤ y := by omega
            set p := (m - N).minFac
            have hp_prime : p.Prime := Nat.minFac_prime (by omega)
            have hp_dvd_d : p ∣ m - N := Nat.minFac_dvd (m - N)
            have hp_le_y : p ≤ y := (Nat.minFac_le (by omega)).trans hd_le_y
            have hp_dvd_P : p ∣ P :=
              Finset.dvd_prod_of_mem _ (Nat.mem_primesLE.mpr ⟨hp_le_y, hp_prime⟩)
            have hp_dvd_N : p ∣ N := hp_dvd_P.trans hP_dvd_N
            have hm_eq : m = N + (m - N) := by omega
            have hp_dvd_m : p ∣ m := hm_eq ▸ Nat.dvd_add hp_dvd_N hp_dvd_d
            rcases (Nat.dvd_prime hm_prime).mp hp_dvd_m with h1 | hpm
            · exact hp_prime.ne_one h1
            · omega
  have h2_lt : 2 < N - y := by omega
  have hcount_pos : 0 < Nat.count Nat.Prime (N - y) := by
    have : Nat.count Nat.Prime 3 ≤ Nat.count Nat.Prime (N - y) :=
      Nat.count_monotone Nat.Prime (by omega)
    have h1 : Nat.count Nat.Prime 3 = 1 := by decide
    omega
  set a := Nat.count Nat.Prime (N - y) - 1
  have ha_lt : pNth a < N - y := by
    unfold pNth
    exact Nat.nth_lt_of_lt_count (by omega)
  have ha1_gt : N + y < pNth (a + 1) := by
    have hge : N - y ≤ pNth (a + 1) := by
      by_contra hlt
      push Not at hlt
      have hcnt : Nat.count Nat.Prime (pNth (a + 1) + 1) ≤ Nat.count Nat.Prime (N - y) :=
        Nat.count_monotone Nat.Prime hlt
      have hsucc : Nat.count Nat.Prime (pNth (a + 1) + 1) = a + 2 := by
        rw [Nat.count_succ, if_pos (pNth_prime (a + 1))]
        have hcnt_eq : Nat.count Nat.Prime (pNth (a + 1)) = a + 1 :=
          pNth_strictMono.injective (Nat.nth_count (pNth_prime (a + 1)))
        omega
      omega
    by_contra hle
    exact hgap_comp (pNth (a + 1)) hge (by omega) (pNth_prime (a + 1))
  have hgap_R : 2 * (y : ℝ) + 2 ≤ (pNth (a + 1) : ℝ) - (pNth a : ℝ) := by
    have : 2 * y + 2 ≤ pNth (a + 1) - pNth a := by omega
    have hle : pNth a ≤ pNth (a + 1) := (pNth_strictMono (Nat.lt_succ_self a)).le
    have : ((2 * y + 2 : ℕ) : ℝ) ≤ ((pNth (a + 1) - pNth a : ℕ) : ℝ) := by exact_mod_cast this
    rw [Nat.cast_sub hle] at this
    push_cast at this
    linarith
  have hlogN_lb : Chebyshev.theta (y : ℝ) ≤ log (N : ℝ) := by
    rw [← hlogP]
    exact Real.log_le_log (by exact_mod_cast hP_pos) (by exact_mod_cast hP_le_N)
  have hlogN_ub : log (N : ℝ) ≤ Chebyshev.theta (y : ℝ) + log ((1001 * y ^ 2 : ℕ) : ℝ) := by
    have hN_le_prod : N ≤ P * (1001 * y ^ 2) := by
      have hq12 : q₁ * q₂ ≤ 1000 * y ^ 2 := by nlinarith
      calc N ≤ P * q₁ * q₂ + y := hN_le
        _ = P * (q₁ * q₂) + y := by ring
        _ ≤ P * (1000 * y ^ 2) + P * y ^ 2 := by nlinarith
        _ = P * (1001 * y ^ 2) := by ring
    have h1 := Real.log_le_log (Nat.cast_pos.mpr (by omega : 0 < N))
      (Nat.cast_le (α := ℝ) |>.mpr hN_le_prod)
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hP_pos.ne') (by positivity), hlogP] at h1
    exact h1
  exact ⟨a, N, hN_ge_10m, by omega, by omega, hgap_R, hlogN_lb, hlogN_ub⟩

lemma exists_small_gap_in_Icc {N : ℕ} (hN : 10000000 ≤ N) :
    ∃ b : ℕ, N < pNth b ∧ pNth (b + 1) ≤ 100 * N ∧
      (pNth (b + 1) : ℝ) - (pNth b : ℝ) ≤ 1.116 * log ((100 * N : ℕ) : ℝ) := by
  have h1 := theta_ge_090 (by omega : 10000000 ≤ 100 * N)
  have h2 := theta_le_1108 hN
  have hdiff : 88.892 * (N : ℝ) ≤ Chebyshev.theta ((100 * N : ℕ) : ℝ) - Chebyshev.theta (N : ℝ) := by
    have h100 : ((100 * N : ℕ) : ℝ) = 100 * (N : ℝ) := by push_cast; ring
    rw [h100] at h1 ⊢
    linarith only [h1, h2]
  have hsub : Nat.primesLE N ⊆ Nat.primesLE (100 * N) := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hsum_eq : Chebyshev.theta ((100 * N : ℕ) : ℝ) - Chebyshev.theta (N : ℝ) =
      ∑ p ∈ Nat.primesLE (100 * N) \ Nat.primesLE N, log (p : ℝ) := by
    rw [theta_nat_eq_sum_primesLE, theta_nat_eq_sum_primesLE, ← Finset.sum_sdiff hsub]
    ring
  set m₁ := Nat.primeCounting N
  set m₂ := Nat.primeCounting (100 * N)
  have hm1_le : m₁ ≤ m₂ := Nat.monotone_primeCounting (by omega)
  have hcard_eq : (Nat.primesLE (100 * N) \ Nat.primesLE N).card = m₂ - m₁ := by
    rw [Finset.card_sdiff_of_subset hsub, primesLE_eq_image_pNth, primesLE_eq_image_pNth,
        Finset.card_image_of_injective _ pNth_strictMono.injective,
        Finset.card_image_of_injective _ pNth_strictMono.injective,
        Finset.card_range, Finset.card_range]
  have hlog_pos : 0 < log ((100 * N : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < 100 * N))
  have hsum_ub : ∑ p ∈ Nat.primesLE (100 * N) \ Nat.primesLE N, log (p : ℝ) ≤
      ((m₂ - m₁ : ℕ) : ℝ) * log ((100 * N : ℕ) : ℝ) := by
    calc ∑ p ∈ Nat.primesLE (100 * N) \ Nat.primesLE N, log (p : ℝ)
        ≤ ∑ _ ∈ Nat.primesLE (100 * N) \ Nat.primesLE N, log ((100 * N : ℕ) : ℝ) := by
          refine Finset.sum_le_sum fun p hp => ?_
          rw [Finset.mem_sdiff, Nat.mem_primesLE] at hp
          exact Real.log_le_log (by exact_mod_cast hp.1.2.pos) (by exact_mod_cast hp.1.1)
      _ = ((Nat.primesLE (100 * N) \ Nat.primesLE N).card : ℝ) * log ((100 * N : ℕ) : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((m₂ - m₁ : ℕ) : ℝ) * log ((100 * N : ℕ) : ℝ) := by rw [hcard_eq]
  have hcnt_lb : 88.892 * (N : ℝ) / log ((100 * N : ℕ) : ℝ) ≤ ((m₂ - m₁ : ℕ) : ℝ) := by
    rw [div_le_iff₀ hlog_pos]
    linarith
  have hcnt_ge_1000 : 1000 ≤ m₂ - m₁ := by
    have hlog_ub : log ((100 * N : ℕ) : ℝ) ≤ (N : ℝ) / 100 := by
      have hN_R : (10000000 : ℝ) ≤ N := by exact_mod_cast hN
      have h100N : ((100 * N : ℕ) : ℝ) = 100 * (N : ℝ) := by push_cast; ring
      have hlog_sq : log (100 * (N : ℝ)) = 2 * log (√(100 * (N : ℝ))) := by
        rw [← Real.sq_sqrt (show 0 ≤ 100 * (N : ℝ) by positivity), Real.log_pow]; norm_num
      have hle_sqrt : log (100 * (N : ℝ)) ≤ 2 * √(100 * (N : ℝ)) := by
        have := Real.log_le_sub_one_of_pos (show 0 < √(100 * (N : ℝ)) by positivity)
        linarith
      have hsqrt_le : 2 * √(100 * (N : ℝ)) ≤ (N : ℝ) / 100 := by
        have hsq : (2 * √(100 * (N : ℝ))) ^ 2 = 400 * (N : ℝ) := by
          calc (2 * √(100 * (N : ℝ))) ^ 2 = 4 * (√(100 * (N : ℝ))) ^ 2 := by ring
            _ = 4 * (100 * (N : ℝ)) := by rw [Real.sq_sqrt (by positivity)]
            _ = 400 * (N : ℝ) := by ring
        have hrhs : ((N : ℝ) / 100) ^ 2 = (N : ℝ) * (N : ℝ) / 10000 := by ring
        have hlt : 400 * (N : ℝ) ≤ ((N : ℝ) / 100) ^ 2 := by
          rw [hrhs, le_div_iff₀ (by norm_num)]
          nlinarith only [hN_R]
        nlinarith [Real.sqrt_nonneg (100 * (N : ℝ))]
      rw [h100N]; linarith
    have h1 : (8889 : ℝ) ≤ 88.892 * (N : ℝ) / log ((100 * N : ℕ) : ℝ) := by
      rw [le_div_iff₀ hlog_pos]
      linarith only [hlog_ub]
    have h2 : (1000 : ℝ) ≤ ((m₂ - m₁ : ℕ) : ℝ) := by linarith
    exact_mod_cast h2
  have hm2_gt : m₁ + 1 < m₂ := by omega
  have htele : ∑ j ∈ Finset.Ico m₁ (m₂ - 1), ((pNth (j + 1) : ℝ) - (pNth j : ℝ)) =
      (pNth (m₂ - 1) : ℝ) - (pNth m₁ : ℝ) := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hsub : m₂ - 1 - m₁ + m₁ = m₂ - 1 := by omega
    have hr := Finset.sum_range_sub (fun i => (pNth (m₁ + i) : ℝ)) (m₂ - 1 - m₁)
    have hcongr : ∑ x ∈ Finset.range (m₂ - 1 - m₁), ((pNth (m₁ + x + 1) : ℝ) - (pNth (m₁ + x) : ℝ)) =
        ∑ x ∈ Finset.range (m₂ - 1 - m₁), ((pNth (m₁ + (x + 1)) : ℝ) - (pNth (m₁ + x) : ℝ)) := by
      refine Finset.sum_congr rfl fun x _ => by ring_nf
    rw [hcongr, hr, Nat.add_zero, show m₁ + (m₂ - 1 - m₁) = m₂ - 1 by omega]
  have hm1_gt_N : N < pNth m₁ := by
    by_contra hle
    push Not at hle
    have h1 : Nat.count Nat.Prime (pNth m₁ + 1) ≤ Nat.count Nat.Prime (N + 1) :=
      Nat.count_monotone Nat.Prime (by omega)
    have h2 : Nat.count Nat.Prime (pNth m₁ + 1) = m₁ + 1 := by
      rw [Nat.count_succ, if_pos (pNth_prime m₁)]
      have hcnt_eq : Nat.count Nat.Prime (pNth m₁) = m₁ :=
        pNth_strictMono.injective (Nat.nth_count (pNth_prime m₁))
      omega
    have h3 : Nat.count Nat.Prime (N + 1) = m₁ := rfl
    omega
  have hm2_le_100N : pNth (m₂ - 1) ≤ 100 * N := by
    have hlt : pNth (m₂ - 1) < 100 * N + 1 := by
      unfold pNth
      exact Nat.nth_lt_of_lt_count (show m₂ - 1 < Nat.count Nat.Prime (100 * N + 1) by
        change m₂ - 1 < m₂; omega)
    omega
  have hsum_gap_le : ∑ j ∈ Finset.Ico m₁ (m₂ - 1), ((pNth (j + 1) : ℝ) - (pNth j : ℝ)) ≤
      99 * (N : ℝ) := by
    have h1 : (pNth (m₂ - 1) : ℝ) ≤ 100 * (N : ℝ) := by exact_mod_cast hm2_le_100N
    have h2 : (N : ℝ) ≤ (pNth m₁ : ℝ) := by exact_mod_cast hm1_gt_N.le
    linarith
  have hex_b : ∃ b ∈ Finset.Ico m₁ (m₂ - 1),
      ((m₂ - 1 - m₁ : ℕ) : ℝ) * ((pNth (b + 1) : ℝ) - (pNth b : ℝ)) ≤ 99 * (N : ℝ) := by
    by_contra hno
    push Not at hno
    have hlt : 99 * (N : ℝ) < ∑ j ∈ Finset.Ico m₁ (m₂ - 1), ((pNth (j + 1) : ℝ) - (pNth j : ℝ)) := by
      have hcard : (Finset.Ico m₁ (m₂ - 1)).card = m₂ - 1 - m₁ := Nat.card_Ico m₁ (m₂ - 1)
      have hpos_card : 0 < m₂ - 1 - m₁ := by omega
      have hsum_gt : ∑ _ ∈ Finset.Ico m₁ (m₂ - 1), (99 * (N : ℝ) / ((m₂ - 1 - m₁ : ℕ) : ℝ)) <
          ∑ j ∈ Finset.Ico m₁ (m₂ - 1), ((pNth (j + 1) : ℝ) - (pNth j : ℝ)) := by
        refine Finset.sum_lt_sum_of_nonempty (Finset.nonempty_Ico.mpr (by omega)) fun j hj => ?_
        rw [div_lt_iff₀ (by exact_mod_cast hpos_card)]
        linarith [hno j hj]
      have hconst : ∑ _ ∈ Finset.Ico m₁ (m₂ - 1), (99 * (N : ℝ) / ((m₂ - 1 - m₁ : ℕ) : ℝ)) = 99 * (N : ℝ) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_div_cancel₀ _ (by exact_mod_cast hpos_card.ne')]
      linarith
    linarith
  rcases hex_b with ⟨b, hb_mem, hb_gap⟩
  rw [Finset.mem_Ico] at hb_mem
  have hb_gt_N : N < pNth b := by
    calc N < pNth m₁ := hm1_gt_N
      _ ≤ pNth b := pNth_strictMono.monotone hb_mem.1
  have hb1_le_100N : pNth (b + 1) ≤ 100 * N := by
    calc pNth (b + 1) ≤ pNth (m₂ - 1) := pNth_strictMono.monotone (by omega)
      _ ≤ 100 * N := hm2_le_100N
  have hden_lb : 88.80 * (N : ℝ) / log ((100 * N : ℕ) : ℝ) ≤ ((m₂ - 1 - m₁ : ℕ) : ℝ) := by
    have h1 : ((m₂ - 1 - m₁ : ℕ) : ℝ) = ((m₂ - m₁ : ℕ) : ℝ) - 1 := by
      have : m₂ - 1 - m₁ + 1 = m₂ - m₁ := by omega
      have : ((m₂ - 1 - m₁ + 1 : ℕ) : ℝ) = ((m₂ - m₁ : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at this
      linarith
    have h2 : (1 : ℝ) ≤ 0.001 * ((m₂ - m₁ : ℕ) : ℝ) := by
      have : (1000 : ℝ) ≤ ((m₂ - m₁ : ℕ) : ℝ) := by exact_mod_cast hcnt_ge_1000
      linarith
    have h3 : 0.999 * ((m₂ - m₁ : ℕ) : ℝ) ≤ ((m₂ - 1 - m₁ : ℕ) : ℝ) := by linarith
    have h4 : 0.999 * (88.892 * (N : ℝ) / log ((100 * N : ℕ) : ℝ)) ≤ 0.999 * ((m₂ - m₁ : ℕ) : ℝ) := by
      linarith
    have h5 : 88.80 * ((N : ℝ) / log ((100 * N : ℕ) : ℝ)) ≤
        0.999 * (88.892 * ((N : ℝ) / log ((100 * N : ℕ) : ℝ))) := by
      have hpos : 0 ≤ (N : ℝ) / log ((100 * N : ℕ) : ℝ) := div_nonneg (Nat.cast_nonneg _) hlog_pos.le
      nlinarith only [hpos]
    have h4' : 0.999 * (88.892 * ((N : ℝ) / log ((100 * N : ℕ) : ℝ))) ≤ 0.999 * ((m₂ - m₁ : ℕ) : ℝ) := by
      simpa only [mul_div_assoc] using h4
    have h5' : 88.80 * (N : ℝ) / log ((100 * N : ℕ) : ℝ) =
        88.80 * ((N : ℝ) / log ((100 * N : ℕ) : ℝ)) := by ring
    linarith only [h3, h4', h5, h5']
  have hgap_ub : (pNth (b + 1) : ℝ) - (pNth b : ℝ) ≤ 1.116 * log ((100 * N : ℕ) : ℝ) := by
    have hgap_nn : 0 ≤ (pNth (b + 1) : ℝ) - (pNth b : ℝ) := by
      have : pNth b ≤ pNth (b + 1) := (pNth_strictMono (Nat.lt_succ_self b)).le
      have : (pNth b : ℝ) ≤ (pNth (b + 1) : ℝ) := by exact_mod_cast this
      linarith
    have hmul : (88.80 * (N : ℝ) / log ((100 * N : ℕ) : ℝ)) * ((pNth (b + 1) : ℝ) - (pNth b : ℝ)) ≤
        99 * (N : ℝ) := by
      exact (mul_le_mul_of_nonneg_right hden_lb hgap_nn).trans hb_gap
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hmul2 : 88.80 * ((pNth (b + 1) : ℝ) - (pNth b : ℝ)) ≤ 99 * log ((100 * N : ℕ) : ℝ) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hlog_pos] at hmul
      nlinarith
    linarith
  exact ⟨b, hb_gt_N, hb1_le_100N, hgap_ub⟩

lemma large_k_y_bounds {k : ℕ} (hk : 1500 < k) :
    let kR : ℝ := (k : ℝ)
    let y : ℕ := if k < 95000 then ⌊0.86 * kR / (0.90 * log kR - 2.5)⌋₊
                 else ⌊0.76 * kR / (0.90 * log kR - 2.5)⌋₊
    290 ≤ y ∧ (k < 110000 → y < 12000) ∧ (110000 ≤ k → 10000 ≤ y) ∧
    (0 : ℝ) < 0.90 * log kR - 2.5 ∧ 7.3 < log kR := by
  intro kR y
  have hk1501 : (1501 : ℝ) ≤ kR := by dsimp [kR]; exact_mod_cast (by omega : 1501 ≤ k)
  have hlog_lb : 7.3 < log kR := by
    have h1501 : 7.3 < log 1501 := by
      rw [lt_log_iff_exp_lt (by norm_num)]
      have hexp_ub : exp 1 < (2.72 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
      have hpow : (exp 1) ^ (73 : ℕ) < (1501 : ℝ) ^ (10 : ℕ) := by
        calc (exp 1) ^ (73 : ℕ) < (2.72 : ℝ) ^ (73 : ℕ) := by gcongr
          _ < (1501 : ℝ) ^ (10 : ℕ) := by norm_num
      have hexp_pow : (exp (7.3 : ℝ)) ^ (10 : ℕ) < (1501 : ℝ) ^ (10 : ℕ) := by
        rw [← Real.exp_nat_mul]
        have h73 : (10 : ℕ) * (7.3 : ℝ) = (73 : ℕ) * (1 : ℝ) := by norm_num
        rw [h73, Real.exp_nat_mul]
        exact hpow
      exact lt_of_pow_lt_pow_left₀ 10 (by positivity) hexp_pow
    exact h1501.trans_le (Real.log_le_log (by norm_num) hk1501)
  have hden_pos : (0 : ℝ) < 0.90 * log kR - 2.5 := by linarith
  have hlog_ub_1501 : log kR ≤ kR / 1501 + 6.32 := by
    have hlog1501 : log 1501 < 7.32 := by
      rw [log_lt_iff_lt_exp (by norm_num)]
      have hexp_lb : (2.71828 : ℝ) < exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
      have hpow : (1501 : ℝ) ^ (25 : ℕ) < (exp 1) ^ (183 : ℕ) := by
        calc (1501 : ℝ) ^ (25 : ℕ) < (2.71828 : ℝ) ^ (183 : ℕ) := by norm_num
          _ < (exp 1) ^ (183 : ℕ) := by gcongr
      have hexp_pow : (1501 : ℝ) ^ (25 : ℕ) < (exp (7.32 : ℝ)) ^ (25 : ℕ) := by
        rw [← Real.exp_nat_mul]
        have h183 : (25 : ℕ) * (7.32 : ℝ) = (183 : ℕ) * (1 : ℝ) := by norm_num
        rw [h183, Real.exp_nat_mul]
        exact hpow
      exact lt_of_pow_lt_pow_left₀ 25 (by positivity) hexp_pow
    have h1 := Real.log_le_sub_one_of_pos (show 0 < kR / 1501 by positivity)
    have h2 : log kR = log (kR / 1501) + log 1501 := by
      rw [← Real.log_mul (by positivity) (by norm_num), div_mul_cancel₀ _ (by norm_num)]
    linarith
  have hy_ge : 290 ≤ y := by
    dsimp [y]
    split_ifs with hlt
    · refine Nat.le_floor ?_
      rw [le_div_iff₀ hden_pos]
      linarith
    · refine Nat.le_floor ?_
      have hk95k : (95000 : ℝ) ≤ kR := by dsimp [kR]; exact_mod_cast (by omega : 95000 ≤ k)
      rw [le_div_iff₀ hden_pos]
      linarith
  have hy_lt : k < 110000 → y < 12000 := by
    intro hlt
    dsimp [y]
    split_ifs with h95
    · rw [Nat.floor_lt (div_nonneg (by positivity) hden_pos.le), div_lt_iff₀ hden_pos]
      by_cases hk20k : k < 20000
      · have : kR < 20000 := by dsimp [kR]; exact_mod_cast hk20k
        linarith
      · by_cases hk50k : k < 50000
        · have hk20kR : (20000 : ℝ) ≤ kR := by dsimp [kR]; exact_mod_cast (by omega : 20000 ≤ k)
          have hlog20k : 9.8 < log 20000 := by
            rw [lt_log_iff_exp_lt (by norm_num)]
            have hexp_ub : exp 1 < (2.72 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
            have hpow : (exp 1) ^ (49 : ℕ) < (20000 : ℝ) ^ (5 : ℕ) := by
              calc (exp 1) ^ (49 : ℕ) < (2.72 : ℝ) ^ (49 : ℕ) := by gcongr
                _ < (20000 : ℝ) ^ (5 : ℕ) := by norm_num
            have hexp_pow : (exp (9.8 : ℝ)) ^ (5 : ℕ) < (20000 : ℝ) ^ (5 : ℕ) := by
              rw [← Real.exp_nat_mul]
              have h49 : (5 : ℕ) * (9.8 : ℝ) = (49 : ℕ) * (1 : ℝ) := by norm_num
              rw [h49, Real.exp_nat_mul]; exact hpow
            exact lt_of_pow_lt_pow_left₀ 5 (by positivity) hexp_pow
          have hlogk : 9.8 < log kR := hlog20k.trans_le (Real.log_le_log (by norm_num) hk20kR)
          have : kR < 50000 := by dsimp [kR]; exact_mod_cast hk50k
          linarith
        · have hk50kR : (50000 : ℝ) ≤ kR := by dsimp [kR]; exact_mod_cast (by omega : 50000 ≤ k)
          have hlog50k : 10.8 < log 50000 := by
            rw [lt_log_iff_exp_lt (by norm_num)]
            have hexp_ub : exp 1 < (2.72 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
            have hpow : (exp 1) ^ (54 : ℕ) < (50000 : ℝ) ^ (5 : ℕ) := by
              calc (exp 1) ^ (54 : ℕ) < (2.72 : ℝ) ^ (54 : ℕ) := by gcongr
                _ < (50000 : ℝ) ^ (5 : ℕ) := by norm_num
            have hexp_pow : (exp (10.8 : ℝ)) ^ (5 : ℕ) < (50000 : ℝ) ^ (5 : ℕ) := by
              rw [← Real.exp_nat_mul]
              have h54 : (5 : ℕ) * (10.8 : ℝ) = (54 : ℕ) * (1 : ℝ) := by norm_num
              rw [h54, Real.exp_nat_mul]; exact hpow
            exact lt_of_pow_lt_pow_left₀ 5 (by positivity) hexp_pow
          have hlogk : 10.8 < log kR := hlog50k.trans_le (Real.log_le_log (by norm_num) hk50kR)
          have : kR < 95000 := by dsimp [kR]; exact_mod_cast h95
          linarith
    · rw [Nat.floor_lt (div_nonneg (by positivity) hden_pos.le), div_lt_iff₀ hden_pos]
      have hk95kR : (95000 : ℝ) ≤ kR := by dsimp [kR]; exact_mod_cast (by omega : 95000 ≤ k)
      have hlog95k : 10.8 < log 95000 := by
        have hlog50k : 10.8 < log 50000 := by
          rw [lt_log_iff_exp_lt (by norm_num)]
          have hexp_ub : exp 1 < (2.72 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
          have hpow : (exp 1) ^ (54 : ℕ) < (50000 : ℝ) ^ (5 : ℕ) := by
            calc (exp 1) ^ (54 : ℕ) < (2.72 : ℝ) ^ (54 : ℕ) := by gcongr
              _ < (50000 : ℝ) ^ (5 : ℕ) := by norm_num
          have hexp_pow : (exp (10.8 : ℝ)) ^ (5 : ℕ) < (50000 : ℝ) ^ (5 : ℕ) := by
            rw [← Real.exp_nat_mul]
            have h54 : (5 : ℕ) * (10.8 : ℝ) = (54 : ℕ) * (1 : ℝ) := by norm_num
            rw [h54, Real.exp_nat_mul]; exact hpow
          exact lt_of_pow_lt_pow_left₀ 5 (by positivity) hexp_pow
        exact hlog50k.trans_le (Real.log_le_log (by norm_num) (by norm_num))
      have hlogk : 10.8 < log kR := hlog95k.trans_le (Real.log_le_log (by norm_num) hk95kR)
      have : kR < 110000 := by dsimp [kR]; exact_mod_cast hlt
      linarith
  have hy_ge_10k : 110000 ≤ k → 10000 ≤ y := by
    intro hge
    dsimp [y]
    rw [if_neg (by omega : ¬ k < 95000)]
    refine Nat.le_floor ?_
    rw [le_div_iff₀ hden_pos]
    have hk110k : (110000 : ℝ) ≤ kR := by dsimp [kR]; exact_mod_cast hge
    have hlog_ub_110k : log kR ≤ kR / 110000 + 10.61 := by
      have hlog110k : log 110000 < 11.61 := by
        have h := exp_div_100_gt_of_lt (B := 110000) (wt := 1161) (by norm_num) (by norm_num)
        linarith only [h]
      have h1 := Real.log_le_sub_one_of_pos (show 0 < kR / 110000 by positivity)
      have h2 : log kR = log (kR / 110000) + log 110000 := by
        rw [← Real.log_mul (by positivity) (by norm_num), div_mul_cancel₀ _ (by norm_num)]
      linarith
    linarith
  exact ⟨hy_ge, hy_lt, hy_ge_10k, hden_pos, hlog_lb⟩

set_option maxRecDepth 32768 in
lemma primeCounting_290 : Nat.primeCounting 290 = 61 := by decide

lemma sum_inv_primes_97_290 :
    ∑ p ∈ Nat.primesLE 290 \ Nat.primesLE 97, (1 : ℝ) / (p : ℝ) ≤ 0.37 := by
  have hsub : Nat.primesLE 97 ⊆ Nat.primesLE 290 := by
    intro p hp; rw [Nat.mem_primesLE] at hp ⊢; exact ⟨by omega, hp.2⟩
  have hcard : (Nat.primesLE 290 \ Nat.primesLE 97).card = 36 := by
    rw [Finset.card_sdiff_of_subset hsub, primesLE_eq_image_pNth, primesLE_eq_image_pNth,
        Finset.card_image_of_injective _ pNth_strictMono.injective,
        Finset.card_image_of_injective _ pNth_strictMono.injective,
        Finset.card_range, Finset.card_range]
    rw [primeCounting_290, primeCounting_97]
  calc ∑ p ∈ Nat.primesLE 290 \ Nat.primesLE 97, (1 : ℝ) / (p : ℝ)
      ≤ ∑ _ ∈ Nat.primesLE 290 \ Nat.primesLE 97, (1 : ℝ) / 98 := by
        refine Finset.sum_le_sum fun p hp => ?_
        rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE] at hp
        have hgt97 : 97 < p := by
          by_contra hle
          push Not at hle
          exact hp.2 ⟨hle, hp.1.2⟩
        have h98 : (98 : ℝ) ≤ p := by exact_mod_cast (by omega : 98 ≤ p)
        exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) h98
    _ = ((Nat.primesLE 290 \ Nat.primesLE 97).card : ℝ) * ((1 : ℝ) / 98) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 0.37 := by rw [hcard]; norm_num

lemma large_k_M_bounds {k y a N : ℕ} (hk : 1500 < k) (hy200 : 200 ≤ y)
    (hN_ge_10m : 10000000 ≤ N) (hlog_k_lb : 7.3 < log (k : ℝ))
    (hy_lb : 2 * log (k : ℝ) + 2.4 < 0.70 * (y : ℝ))
    (ha_lt_N : pNth a < N) (hN_lt_a1 : N < pNth (a + 1))
    (hlogN_lb : Chebyshev.theta (y : ℝ) ≤ log (N : ℝ)) :
    let M := ⌊4 * (k : ℝ) * log (k : ℝ)⌋₊
    40000 ≤ M ∧ k - 1 ≤ Nat.primeCounting M ∧ Nat.primeCounting M ≤ a ∧
    log (M : ℝ) ≤ log 4 + log (k : ℝ) + log (log (k : ℝ)) ∧ 10.5 ≤ log (M : ℝ) := by
  intro M
  have hk1501 : (1501 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1501 ≤ k)
  have hM_ge_40k : 40000 ≤ M := by
    dsimp [M]
    refine Nat.le_floor ?_
    have h1 : 4 * (1501 : ℝ) * 7.3 ≤ 4 * (k : ℝ) * log (k : ℝ) := by nlinarith only [hk1501, hlog_k_lb]
    norm_num at h1 ⊢
    linarith only [h1]
  have hM_le_k2 : (M : ℝ) ≤ (k : ℝ) ^ 2 := by
    dsimp [M]
    have hfl := Nat.floor_le (show 0 ≤ 4 * (k : ℝ) * log (k : ℝ) by positivity)
    have hlog_le_k : 4 * log (k : ℝ) ≤ (k : ℝ) := by
      have h1 := Real.log_le_sub_one_of_pos (show 0 < √(k : ℝ) by positivity)
      have h2 : log (k : ℝ) = 2 * log (√(k : ℝ)) := by
        rw [← Real.sq_sqrt (by positivity : 0 ≤ (k : ℝ)), Real.log_pow]; norm_num
      have hrt : 8 ≤ √(k : ℝ) := by
        rw [Real.le_sqrt (by norm_num) (by positivity)]
        linarith only [hk1501]
      have hsq : √(k : ℝ) * √(k : ℝ) = (k : ℝ) := Real.mul_self_sqrt (by positivity)
      have h8rt : 8 * √(k : ℝ) ≤ (k : ℝ) := by nlinarith only [hrt, hsq]
      linarith only [h1, h2, h8rt]
    have h4 : 4 * (k : ℝ) * log (k : ℝ) ≤ (k : ℝ) * (k : ℝ) := by nlinarith only [hk1501, hlog_le_k]
    linarith only [hfl, h4]
  have hk_le_M : k - 1 ≤ Nat.primeCounting M := by
    have hth : 0.70 * (M : ℝ) ≤ Chebyshev.theta (M : ℝ) := theta_ge_070 (by omega)
    have hle := Chebyshev.theta_le_pi_mul_log M
    have hlogM_le : log (M : ℝ) ≤ 2 * log (k : ℝ) := by
      have h1 : log (M : ℝ) ≤ log ((k : ℝ) ^ 2) :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < M)) hM_le_k2
      rw [Real.log_pow] at h1; norm_num at h1; exact h1
    have hMR : 4 * (k : ℝ) * log (k : ℝ) - 1 < (M : ℝ) := Nat.sub_one_lt_floor _
    have hpi_ge : ((k - 1 : ℕ) : ℝ) ≤ (Nat.primeCounting M : ℝ) := by
      have hpi_nn : 0 ≤ (Nat.primeCounting M : ℝ) := Nat.cast_nonneg _
      have hmul1 : (Nat.primeCounting M : ℝ) * log (M : ℝ) ≤ (Nat.primeCounting M : ℝ) * (2 * log (k : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogM_le hpi_nn
      have h1 : 0.70 * (4 * (k : ℝ) * log (k : ℝ) - 1) ≤ (Nat.primeCounting M : ℝ) * (2 * log (k : ℝ)) := by
        linarith only [hth, hle, hmul1, hMR]
      have h2 : 2 * (k : ℝ) * log (k : ℝ) < 0.70 * (4 * (k : ℝ) * log (k : ℝ) - 1) := by
        nlinarith only [hk1501, hlog_k_lb]
      have h3 : (k : ℝ) < (Nat.primeCounting M : ℝ) := by
        by_contra hle_pi
        push Not at hle_pi
        have : (Nat.primeCounting M : ℝ) * (2 * log (k : ℝ)) ≤ (k : ℝ) * (2 * log (k : ℝ)) :=
          mul_le_mul_of_nonneg_right hle_pi (by linarith only [hlog_k_lb])
        linarith only [h1, h2, this]
      have hk1 : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.sub_le k 1
      linarith only [h3, hk1]
    exact_mod_cast hpi_ge
  have hlogN_ge_070y : 0.70 * (y : ℝ) ≤ log (N : ℝ) := (theta_ge_070 hy200).trans hlogN_lb
  have hM_le_a : Nat.primeCounting M ≤ a := by
    have hM_lt_N_10 : 10 * M < N := by
      have hlog10M : log ((10 * M : ℕ) : ℝ) < log (N : ℝ) := by
        have h1 : log (M : ℝ) ≤ 2 * log (k : ℝ) := by
          have h' := Real.log_le_log (by exact_mod_cast (by omega : 0 < M)) hM_le_k2
          rw [Real.log_pow] at h'; norm_num at h'; exact h'
        have h2 : log (10 : ℝ) < 2.4 := by
          have h := exp_div_100_gt_of_lt (B := 10) (wt := 240) (by norm_num) (by norm_num)
          norm_num at h; linarith
        have h3 : log ((10 * M : ℕ) : ℝ) = log 10 + log (M : ℝ) := by
          rw [Nat.cast_mul, Real.log_mul (by norm_num) (by positivity)]
          norm_num
        linarith only [h1, h2, h3, hy_lb, hlogN_ge_070y]
      have h10M_pos : (0 : ℝ) < ((10 * M : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 10 * M)
      have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
      have hltR : ((10 * M : ℕ) : ℝ) < (N : ℝ) := by
        rw [← Real.exp_log h10M_pos, ← Real.exp_log hN_pos]
        exact Real.exp_lt_exp.mpr hlog10M
      exact Nat.cast_lt.mp hltR
    have hdiff_pos : 0 < Chebyshev.theta ((N - 1 : ℕ) : ℝ) - Chebyshev.theta (M : ℝ) := by
      have h1 : 0.72 * ((N - 1 : ℕ) : ℝ) ≤ Chebyshev.theta ((N - 1 : ℕ) : ℝ) :=
        theta_ge_072_10k (by omega)
      have h2 : Chebyshev.theta (M : ℝ) ≤ 1.26 * (M : ℝ) := theta_le_126_10k (by omega)
      have h10 : (10 * M : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 10 * M ≤ N - 1)
      have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
      linarith only [h1, h2, h10, hMpos]
    rw [theta_nat_eq_sum_primesLE, theta_nat_eq_sum_primesLE] at hdiff_pos
    have hsub : Nat.primesLE M ⊆ Nat.primesLE (N - 1) := by
      intro p hp; rw [Nat.mem_primesLE] at hp ⊢; exact ⟨by omega, hp.2⟩
    rw [← Finset.sum_sdiff hsub] at hdiff_pos
    have hpos_sum : 0 < ∑ p ∈ Nat.primesLE (N - 1) \ Nat.primesLE M, log (p : ℝ) := by linarith only [hdiff_pos]
    have hne : (Nat.primesLE (N - 1) \ Nat.primesLE M).Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      rw [hemp, Finset.sum_empty] at hpos_sum
      linarith only [hpos_sum]
    rcases hne with ⟨q, hq⟩
    rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE] at hq
    have hq_gt_M : M < q := by by_contra hle; exact hq.2 ⟨by omega, hq.1.2⟩
    have hq_lt_a1 : q < pNth (a + 1) := by omega
    have hcnt1 : Nat.count Nat.Prime (M + 1) ≤ Nat.count Nat.Prime q :=
      Nat.count_monotone Nat.Prime hq_gt_M
    have hcnt2 : Nat.count Nat.Prime q < Nat.count Nat.Prime (pNth (a + 1)) := by
      have h1 : Nat.count Nat.Prime (q + 1) ≤ Nat.count Nat.Prime (pNth (a + 1)) :=
        Nat.count_monotone Nat.Prime hq_lt_a1
      have h2 : Nat.count Nat.Prime (q + 1) = Nat.count Nat.Prime q + 1 := by
        rw [Nat.count_succ, if_pos hq.1.2]
      omega
    have ha1_cnt : Nat.count Nat.Prime (pNth (a + 1)) = a + 1 :=
      pNth_strictMono.injective (Nat.nth_count (pNth_prime (a + 1)))
    change Nat.count Nat.Prime (M + 1) ≤ a
    omega
  have hlogM_le_exact : log (M : ℝ) ≤ log 4 + log (k : ℝ) + log (log (k : ℝ)) := by
    have hM_le : (M : ℝ) ≤ 4 * (k : ℝ) * log (k : ℝ) := Nat.floor_le (by positivity)
    have h1 : log (M : ℝ) ≤ log (4 * (k : ℝ) * log (k : ℝ)) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < M)) hM_le
    rw [Real.log_mul (by positivity) (by linarith only [hlog_k_lb]),
        Real.log_mul (by norm_num) (by linarith only [hk1501])] at h1
    linarith only [h1]
  have hlogM_ge_105 : 10.5 ≤ log (M : ℝ) := by
    have h40kR : (40000 : ℝ) ≤ M := by exact_mod_cast hM_ge_40k
    have h1 : 10.5 < log 40000 := by
      rw [lt_log_iff_exp_lt (by norm_num)]
      have hexp_ub : exp 1 < (2.72 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
      have hpow : (exp 1) ^ (21 : ℕ) < (40000 : ℝ) ^ (2 : ℕ) := by
        calc (exp 1) ^ (21 : ℕ) < (2.72 : ℝ) ^ (21 : ℕ) := by gcongr
          _ < (40000 : ℝ) ^ (2 : ℕ) := by norm_num
      have hexp_pow : (exp (10.5 : ℝ)) ^ (2 : ℕ) < (40000 : ℝ) ^ (2 : ℕ) := by
        rw [← Real.exp_nat_mul]
        have h21 : (2 : ℕ) * (10.5 : ℝ) = (21 : ℕ) * (1 : ℝ) := by norm_num
        rw [h21, Real.exp_nat_mul]; exact hpow
      exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hexp_pow
    exact h1.le.trans (Real.log_le_log (by norm_num) h40kR)
  exact ⟨hM_ge_40k, hk_le_M, hM_le_a, hlogM_le_exact, hlogM_ge_105⟩

lemma primeCounting_le_iff_pNth_gt {M j : ℕ} : Nat.primeCounting M ≤ j ↔ M < pNth j := by
  constructor
  · intro h
    by_contra hle; push Not at hle
    have h1 := Nat.count_monotone Nat.Prime (by omega : pNth j + 1 ≤ M + 1)
    have h2 : Nat.count Nat.Prime (pNth j + 1) = j + 1 := by
      rw [Nat.count_succ, if_pos (pNth_prime j), pNth_strictMono.injective (Nat.nth_count (pNth_prime j))]
    change Nat.count Nat.Prime (pNth j + 1) ≤ Nat.count Nat.Prime (M + 1) at h1
    change Nat.count Nat.Prime (M + 1) ≤ j at h
    omega
  · intro h
    change Nat.count Nat.Prime (M + 1) ≤ j
    rw [← pNth_strictMono.injective (Nat.nth_count (pNth_prime j))]
    exact Nat.count_monotone Nat.Prime (by omega)

lemma sum_abel_n_diff_le {A B : ℕ} (hA : 3 ≤ A) (hAB : A ≤ B) :
    ∑ n ∈ Finset.Ico A B, (n : ℝ) *
      (1 / ((n : ℝ) * log n) - 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1))) ≤
    (1 / log A - 1 / log B) + (log (log B) - log (log A)) := by
  have hterm_le : ∀ n ∈ Finset.Ico A B,
      (n : ℝ) * (1 / ((n : ℝ) * log n) - 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1))) ≤
      (1 / log n - 1 / log ((n : ℝ) + 1)) + (log (log ((n : ℝ) + 1)) - log (log n)) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hn0 : (n : ℝ) ≠ 0 := by linarith
    have hn1_ne : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hlogn : 0 < log n := Real.log_pos hn1
    have hlogn1 : 0 < log ((n : ℝ) + 1) := Real.log_pos (by linarith)
    have hid : (n : ℝ) * (1 / ((n : ℝ) * log n) - 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1))) =
        (1 / log n - 1 / log ((n : ℝ) + 1)) + 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1)) := by
      field_simp [hn0, hn1_ne, hlogn.ne', hlogn1.ne']
      ring
    rw [hid]
    have hll_step : (log ((n : ℝ) + 1) - log n) / log ((n : ℝ) + 1) ≤
        log (log ((n : ℝ) + 1)) - log (log n) := by
      have h1 : log (log n / log ((n : ℝ) + 1)) ≤ log n / log ((n : ℝ) + 1) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div hlogn.ne' hlogn1.ne'] at h1
      have h2 : log n / log ((n : ℝ) + 1) - 1 = -((log ((n : ℝ) + 1) - log n) / log ((n : ℝ) + 1)) := by
        field_simp [hlogn1.ne']; ring
      linarith only [h1, h2]
    have hlog_ge_1_div : 1 / ((n : ℝ) + 1) ≤ log ((n : ℝ) + 1) - log n := by
      have h1 : log ((n : ℝ) / ((n : ℝ) + 1)) ≤ (n : ℝ) / ((n : ℝ) + 1) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div hn0 hn1_ne] at h1
      have h2 : (n : ℝ) / ((n : ℝ) + 1) - 1 = -(1 / ((n : ℝ) + 1)) := by field_simp [hn1_ne]; ring
      linarith only [h1, h2]
    have hdiv_le : 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1)) ≤
        (log ((n : ℝ) + 1) - log n) / log ((n : ℝ) + 1) := by
      have h1 : 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1)) = (1 / ((n : ℝ) + 1)) / log ((n : ℝ) + 1) := by
        field_simp [hn1_ne, hlogn1.ne']
      rw [h1]
      exact div_le_div_of_nonneg_right hlog_ge_1_div hlogn1.le
    linarith
  calc ∑ n ∈ Finset.Ico A B, (n : ℝ) *
        (1 / ((n : ℝ) * log n) - 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1)))
      ≤ ∑ n ∈ Finset.Ico A B,
          ((1 / log n - 1 / log ((n : ℝ) + 1)) + (log (log ((n : ℝ) + 1)) - log (log n))) :=
        Finset.sum_le_sum hterm_le
    _ = (∑ n ∈ Finset.Ico A B, (1 / log n - 1 / log ((n : ℝ) + 1))) +
        (∑ n ∈ Finset.Ico A B, (log (log ((n : ℝ) + 1)) - log (log n))) := Finset.sum_add_distrib
    _ = (1 / log A - 1 / log B) + (log (log B) - log (log A)) := by
        have ht1 : ∑ n ∈ Finset.Ico A B, (1 / log (n : ℝ) - 1 / log ((n : ℝ) + 1)) =
            1 / log (A : ℝ) - 1 / log (B : ℝ) := by
          have h := Finset.sum_Ico_sub (fun n : ℕ => 1 / log (n : ℝ)) hAB
          simp only [Nat.cast_add, Nat.cast_one] at h
          have hneg : ∑ n ∈ Finset.Ico A B, (1 / log (n : ℝ) - 1 / log ((n : ℝ) + 1)) =
              - ∑ n ∈ Finset.Ico A B, (1 / log ((n : ℝ) + 1) - 1 / log (n : ℝ)) := by
            rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun _ _ => by ring
          linarith only [h, hneg]
        have ht2 := Finset.sum_Ico_sub (fun n : ℕ => log (log (n : ℝ))) hAB
        simp only [Nat.cast_add, Nat.cast_one] at ht2
        rw [ht1, ht2]

lemma large_k_D_lb {k a M N : ℕ} (hM40k : 40000 ≤ M) (hN10m : 10000000 ≤ N)
    (hkM : k - 1 ≤ Nat.primeCounting M) (hMa : Nat.primeCounting M ≤ a)
    (haN : pNth a < N) (hNa1 : N < pNth (a + 1)) (hlogM : 10.5 ≤ log (M : ℝ)) :
    (if M < 10000000 then 0.90 * log (log (N : ℝ)) - 0.80 * log (log (M : ℝ)) - 0.52
     else 0.90 * (log (log (N : ℝ)) - log (log (M : ℝ))) - 0.10) ≤ sumX a - sumX (k - 2) := by
  have hS_k2 : sumX (k - 2) ≤ sumX (Nat.primeCounting M) := by
    unfold sumX
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun _ _ _ => xTerm_nonneg _)
  have h1 : ∑ p ∈ Nat.primesLE N \ Nat.primesLE M, (1 : ℝ) / (p : ℝ) - 1 / 40000 ≤
      sumX a - sumX (Nat.primeCounting M) := by
    have hsub : Nat.primesLE N \ Nat.primesLE M ⊆
        (Finset.Ico (Nat.primeCounting M) (a + 1)).image pNth := by
      intro p hp
      rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE] at hp
      rcases hp with ⟨⟨hpN, hp_prime⟩, hpM⟩
      have hp_gt_M : M < p := by
        by_contra hle; push Not at hle; exact hpM ⟨hle, hp_prime⟩
      obtain ⟨j, hj_eq⟩ : ∃ j, pNth j = p := ⟨Nat.count Nat.Prime p, Nat.nth_count hp_prime⟩
      subst hj_eq
      refine Finset.mem_image.mpr ⟨j, Finset.mem_Ico.mpr ⟨?_, ?_⟩, rfl⟩
      · change Nat.count Nat.Prime (M + 1) ≤ j
        rw [← pNth_strictMono.injective (Nat.nth_count (pNth_prime j))]
        exact Nat.count_monotone Nat.Prime (by omega)
      · by_contra hge
        push Not at hge
        have : N < pNth j := hNa1.trans_le (pNth_strictMono.monotone (by omega))
        omega
    have hsum1 : ∑ p ∈ Nat.primesLE N \ Nat.primesLE M, (1 : ℝ) / (p : ℝ) ≤
        ∑ j ∈ Finset.Ico (Nat.primeCounting M) (a + 1), (1 : ℝ) / (pNth j : ℝ) := by
      calc ∑ p ∈ Nat.primesLE N \ Nat.primesLE M, (1 : ℝ) / (p : ℝ)
          ≤ ∑ p ∈ (Finset.Ico (Nat.primeCounting M) (a + 1)).image pNth, (1 : ℝ) / (p : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
        _ = ∑ j ∈ Finset.Ico (Nat.primeCounting M) (a + 1), (1 : ℝ) / (pNth j : ℝ) := by
            rw [Finset.sum_image]
            intro i _ j _ hij
            exact pNth_strictMono.injective hij
    have hsplit : ∑ j ∈ Finset.Ico (Nat.primeCounting M) (a + 1), (1 : ℝ) / (pNth j : ℝ) =
        (∑ j ∈ Finset.Ico (Nat.primeCounting M) a, (1 : ℝ) / (pNth j : ℝ)) + 1 / (pNth a : ℝ) := by
      rw [Finset.sum_Ico_succ_top hMa]
    have hle_sumX : ∑ j ∈ Finset.Ico (Nat.primeCounting M) a, (1 : ℝ) / (pNth j : ℝ) ≤
        sumX a - sumX (Nat.primeCounting M) := by
      have hsub_eq : sumX a - sumX (Nat.primeCounting M) =
          ∑ j ∈ Finset.Ico (Nat.primeCounting M) a, xTerm j := by
        unfold sumX
        rw [← Finset.sum_range_add_sum_Ico _ hMa]
        ring
      rw [hsub_eq]
      refine Finset.sum_le_sum fun j _ => ?_
      unfold xTerm
      have hp2 : (1 : ℝ) < (pNth j : ℝ) := by
        exact_mod_cast (Nat.nth_mem_of_infinite Nat.infinite_setOf_prime j).one_lt
      exact div_le_div_of_nonneg_left zero_le_one (by linarith) (by linarith)
    have hpa_ge : (40000 : ℝ) ≤ (pNth a : ℝ) := by
      have hpi : M < pNth (Nat.primeCounting M) := primeCounting_le_iff_pNth_gt.mp (le_refl _)
      have hpa : M < pNth a := hpi.trans_le (pNth_strictMono.monotone hMa)
      exact_mod_cast (by omega : 40000 ≤ pNth a)
    have hinv_a : 1 / (pNth a : ℝ) ≤ 1 / 40000 :=
      div_le_div_of_nonneg_left zero_le_one (by norm_num) hpa_ge
    linarith
  have hMN : M ≤ N := by
    have hpi : M < pNth (Nat.primeCounting M) := primeCounting_le_iff_pNth_gt.mp (le_refl _)
    exact (hpi.trans_le (pNth_strictMono.monotone hMa)).le.trans haN.le
  have hlog10m_lb : 16 ≤ log (10000000 : ℝ) := by
    rw [le_log_iff_exp_le (by norm_num)]
    calc exp 16 = (exp 1) ^ (16 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ (2.718282 : ℝ) ^ (16 : ℕ) := by gcongr; exact lt_trans Real.exp_one_lt_d9 (by norm_num) |>.le
      _ ≤ 10000000 := by norm_num
  have hlog10m_ub : log (10000000 : ℝ) < 16.5 := by
    rw [log_lt_iff_lt_exp (by norm_num)]
    calc (10000000 : ℝ) < (2.71828 : ℝ) ^ (16 : ℕ) * (1 + 0.5) := by norm_num
      _ < (exp 1) ^ (16 : ℕ) * exp (0.5 : ℝ) := by
          gcongr
          · exact lt_trans (by norm_num) Real.exp_one_gt_d9
          · linarith [Real.add_one_lt_exp (by norm_num : (0.5 : ℝ) ≠ 0)]
      _ = exp 16.5 := by rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have hsum_lb : (if M < 10000000 then 0.90 * log (log (N : ℝ)) - 0.80 * log (log (M : ℝ)) - 0.51
      else 0.90 * (log (log (N : ℝ)) - log (log (M : ℝ))) - 0.09) ≤
      ∑ p ∈ Nat.primesLE N \ Nat.primesLE M, (1 : ℝ) / (p : ℝ) := by
    by_cases hM10m : 10000000 ≤ M
    · rw [if_neg (by omega : ¬ M < 10000000)]
      have hlb := sum_inv_primes_lb (M := M) (N := N) (c := 0.90) (by norm_num) (by omega) hMN
        (fun n hn => theta_ge_090 (by have := (Finset.mem_Ico.mp hn).1; omega))
      have hMlog : 16 ≤ log (M : ℝ) := hlog10m_lb.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hM10m))
      have hMpos : (10000000 : ℝ) ≤ M := by exact_mod_cast hM10m
      have hM1 : 1 / ((M : ℝ) * log (M : ℝ)) ≤ 1 / (10000000 * 16) :=
        one_div_le_one_div_of_le (by norm_num) (mul_le_mul hMpos hMlog (by norm_num) (by positivity))
      have hM2 : 1.4 / log (M : ℝ) ≤ 1.4 / 16 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hMlog
      linarith only [hlb, hM1, hM2]
    · rw [if_pos (by omega : M < 10000000)]
      have hM_lt : M < 10000000 := by omega
      have hsub_eq : ∑ p ∈ Nat.primesLE N \ Nat.primesLE M, (1 : ℝ) / (p : ℝ) =
          (∑ p ∈ Nat.primesLE 10000000 \ Nat.primesLE M, (1 : ℝ) / (p : ℝ)) +
          (∑ p ∈ Nat.primesLE N \ Nat.primesLE 10000000, (1 : ℝ) / (p : ℝ)) := by
        have hdisj : Disjoint (Nat.primesLE 10000000 \ Nat.primesLE M) (Nat.primesLE N \ Nat.primesLE 10000000) := by
          rw [Finset.disjoint_left]; intro p hp1 hp2; rw [Finset.mem_sdiff] at hp1 hp2; exact hp2.2 hp1.1
        have hunion : Nat.primesLE N \ Nat.primesLE M =
            (Nat.primesLE 10000000 \ Nat.primesLE M) ∪ (Nat.primesLE N \ Nat.primesLE 10000000) := by
          ext p; simp only [Finset.mem_union, Finset.mem_sdiff, Nat.mem_primesLE]
          constructor
          · rintro ⟨⟨hpN, hp⟩, hpM⟩
            by_cases hp10m : p ≤ 10000000
            · exact Or.inl ⟨⟨hp10m, hp⟩, hpM⟩
            · exact Or.inr ⟨⟨hpN, hp⟩, fun h => hp10m h.1⟩
          · rintro (⟨⟨hp10m, hp⟩, hpM⟩ | ⟨⟨hpN, hp⟩, hp10m⟩)
            · exact ⟨⟨by omega, hp⟩, hpM⟩
            · exact ⟨⟨hpN, hp⟩, fun h => hp10m ⟨by omega, h.2⟩⟩
        rw [hunion, Finset.sum_union hdisj]
      have hlb1 := sum_inv_primes_lb (M := M) (N := 10000000) (c := 0.80) (by norm_num) (by omega) hM_lt.le
        (fun n hn => theta_ge_080 (by have := (Finset.mem_Ico.mp hn).1; omega))
      have hlb2 := sum_inv_primes_lb (M := 10000000) (N := N) (c := 0.90) (by norm_num) (by norm_num) hN10m
        (fun n hn => theta_ge_090 (Finset.mem_Ico.mp hn).1)
      have hll10m_ub : log (log (10000000 : ℝ)) ≤ 2.88 := by
        have h1 : log (log (10000000 : ℝ)) ≤ log 16.5 := Real.log_le_log (by linarith [hlog10m_lb]) hlog10m_ub.le
        have h2 : (16.5 : ℝ) < exp 2.88 := by
          have hexp88 : (1 + 0.88 + 0.88 ^ 2 / 2 : ℝ) ≤ exp 0.88 := by
            have h := Real.sum_le_exp_of_nonneg (x := (0.88 : ℝ)) (by norm_num) 3
            simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty] at h
            norm_num at h ⊢; linarith
          calc (16.5 : ℝ) < (2.71828 : ℝ) ^ (2 : ℕ) * (1 + 0.88 + 0.88 ^ 2 / 2) := by norm_num
            _ < (exp 1) ^ (2 : ℕ) * (1 + 0.88 + 0.88 ^ 2 / 2) := by
                gcongr; exact lt_trans (by norm_num) Real.exp_one_gt_d9
            _ ≤ (exp 1) ^ (2 : ℕ) * exp 0.88 := by
                gcongr
            _ = exp 2.88 := by rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
        exact h1.trans ((log_lt_iff_lt_exp (by norm_num)).mpr h2).le
      have hMpos : (40000 : ℝ) ≤ M := by exact_mod_cast hM40k
      have hM1 : 1 / ((M : ℝ) * log (M : ℝ)) ≤ 1 / (40000 * 10.5) :=
        one_div_le_one_div_of_le (by norm_num) (mul_le_mul hMpos hlogM (by norm_num) (by positivity))
      have hM2 : 1.4 / log (M : ℝ) ≤ 1.4 / 10.5 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hlogM
      have hN1 : 1 / ((10000000 : ℝ) * log (10000000 : ℝ)) ≤ 1 / (10000000 * 16) :=
        one_div_le_one_div_of_le (by norm_num) (mul_le_mul (by norm_num) hlog10m_lb (by norm_num) (by norm_num))
      have hN2 : 1.4 / log (10000000 : ℝ) ≤ 1.4 / 16 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hlog10m_lb
      linarith only [hsub_eq, hlb1, hlb2, hll10m_ub, hM1, hM2, hN1, hN2]
  split_ifs at hsum_lb ⊢
  · linarith only [hS_k2, h1, hsum_lb]
  · linarith only [hS_k2, h1, hsum_lb]

lemma large_k_Sb_sub_a_le {a b N : ℕ} (hN10m : 10000000 ≤ N) (hpa : 40000 ≤ pNth a)
    (haN : pNth a < N) (hNa1 : N < pNth (a + 1)) (hNb : N < pNth b)
    (hb1 : pNth (b + 1) ≤ 100 * N) (hlogN : 140 ≤ log (N : ℝ)) :
    sumX b - sumX a ≤ 0.045 := by
  have hab : a < b := by rw [← pNth_strictMono.lt_iff_lt]; exact haN.trans hNb
  have hsub_eq : sumX b - sumX a = ∑ j ∈ Finset.Ico a b, xTerm j := by
    unfold sumX; rw [← Finset.sum_range_add_sum_Ico _ hab.le]; ring
  rw [hsub_eq, Finset.sum_eq_sum_Ico_succ_bot hab]
  have hxa : xTerm a ≤ 1 / 39999 := by
    unfold xTerm
    have hpaR : (40000 : ℝ) ≤ (pNth a : ℝ) := by exact_mod_cast hpa
    exact div_le_div_of_nonneg_left zero_le_one (by norm_num) (by linarith)
  have hIco_le : ∑ j ∈ Finset.Ico (a + 1) b, xTerm j ≤
      1.000001 * ∑ p ∈ Nat.primesLE (100 * N) \ Nat.primesLE N, (1 : ℝ) / (p : ℝ) := by
    have hterm : ∀ j ∈ Finset.Ico (a + 1) b, xTerm j ≤ 1.000001 * ((1 : ℝ) / (pNth j : ℝ)) := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      have hj_gt : N < pNth j := hNa1.trans_le (pNth_strictMono.monotone hj.1)
      have hpR : (10000001 : ℝ) ≤ (pNth j : ℝ) := by exact_mod_cast (by omega : 10000001 ≤ pNth j)
      unfold xTerm
      rw [mul_one_div, div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith only [hpR]
    have hsum1 : ∑ j ∈ Finset.Ico (a + 1) b, xTerm j ≤
        1.000001 * ∑ j ∈ Finset.Ico (a + 1) b, (1 : ℝ) / (pNth j : ℝ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hterm
    have hsub : (Finset.Ico (a + 1) b).image pNth ⊆ Nat.primesLE (100 * N) \ Nat.primesLE N := by
      intro p hp
      rw [Finset.mem_image] at hp
      rcases hp with ⟨j, hj, rfl⟩
      rw [Finset.mem_Ico] at hj
      have hj_gt : N < pNth j := hNa1.trans_le (pNth_strictMono.monotone hj.1)
      have hj_lt : pNth j ≤ 100 * N :=
        (pNth_strictMono.monotone (by omega : j ≤ b + 1)).trans hb1
      rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE]
      exact ⟨⟨hj_lt, Nat.nth_mem_of_infinite Nat.infinite_setOf_prime j⟩, fun h => by omega⟩
    have hsum2 : ∑ j ∈ Finset.Ico (a + 1) b, (1 : ℝ) / (pNth j : ℝ) ≤
        ∑ p ∈ Nat.primesLE (100 * N) \ Nat.primesLE N, (1 : ℝ) / (p : ℝ) := by
      calc ∑ j ∈ Finset.Ico (a + 1) b, (1 : ℝ) / (pNth j : ℝ)
          = ∑ p ∈ (Finset.Ico (a + 1) b).image pNth, (1 : ℝ) / (p : ℝ) := by
            rw [Finset.sum_image]; intro i _ j _ hij; exact pNth_strictMono.injective hij
        _ ≤ ∑ p ∈ Nat.primesLE (100 * N) \ Nat.primesLE N, (1 : ℝ) / (p : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    linarith [mul_le_mul_of_nonneg_left hsum2 (by norm_num : (0 : ℝ) ≤ 1.000001)]
  have hub := sum_inv_primes_ub (M := N) (N := 100 * N) (c := 1.108) (by norm_num) (by omega) (by omega)
    (fun n hn => theta_le_1108 (by have := (Finset.mem_Ico.mp hn).1; omega))
  have hlog100 : log (100 : ℝ) ≤ 4.61 := by
    rw [log_le_iff_le_exp (by norm_num)]
    calc (100 : ℝ) ≤ (2.71828 : ℝ) ^ (4 : ℕ) * (1 + 0.61 + 0.61 ^ 2 / 2 + 0.61 ^ 3 / 6) := by norm_num
      _ ≤ (exp 1) ^ (4 : ℕ) * exp 0.61 := by
          gcongr
          · exact lt_trans (by norm_num) Real.exp_one_gt_d9 |>.le
          · have h := Real.sum_le_exp_of_nonneg (x := (0.61 : ℝ)) (by norm_num) 4
            simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty] at h
            have hf0 : ((Nat.factorial 0 : ℕ) : ℝ) = 1 := by norm_num
            have hf1 : ((Nat.factorial 1 : ℕ) : ℝ) = 1 := by norm_num
            have hf2 : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num
            have hf3 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by exact_mod_cast (by decide : Nat.factorial 3 = 6)
            rw [hf0, hf1, hf2, hf3] at h
            norm_num at h ⊢; linarith
      _ = exp 4.61 := by rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have hll_diff : log (log ((100 * N : ℕ) : ℝ)) - log (log (N : ℝ)) ≤ 4.61 / 140 := by
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hlogN_pos : 0 < log (N : ℝ) := by linarith
    have h1 : log ((100 * N : ℕ) : ℝ) = log 100 + log (N : ℝ) := by
      push_cast; rw [Real.log_mul (by norm_num) hNpos.ne']
    have h2 : log (log ((100 * N : ℕ) : ℝ)) - log (log (N : ℝ)) =
        log ((log 100 + log (N : ℝ)) / log (N : ℝ)) := by
      rw [h1, Real.log_div (by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 100)]) hlogN_pos.ne']
    have h3 : log ((log 100 + log (N : ℝ)) / log (N : ℝ)) ≤
        (log 100 + log (N : ℝ)) / log (N : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos (by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 100)]) hlogN_pos)
    have h4 : (log 100 + log (N : ℝ)) / log (N : ℝ) - 1 = log 100 / log (N : ℝ) := by
      field_simp [hlogN_pos.ne']; ring
    have h5 : log 100 / log (N : ℝ) ≤ 4.61 / 140 :=
      div_le_div₀ (by norm_num) hlog100 (by norm_num) hlogN
    linarith only [h2, h3, h4, h5]
  have hinv_N : 1 / log (N : ℝ) ≤ 1 / 140 :=
    div_le_div_of_nonneg_left zero_le_one (by norm_num) hlogN
  have h100_ub : 1.000001 * ∑ p ∈ Nat.primesLE (100 * N) \ Nat.primesLE N, (1 : ℝ) / (p : ℝ) ≤
      1.000001 * (1.108 * (4.61 / 140 + 1 / 140)) := by
    have h1 : 1.108 * (log (log ((100 * N : ℕ) : ℝ)) - log (log (N : ℝ)) + 1 / log (N : ℝ)) ≤
        1.108 * (4.61 / 140 + 1 / 140) := by linarith only [hll_diff, hinv_N]
    have hub' : ∑ p ∈ Nat.primesLE (100 * N) \ Nat.primesLE N, (1 : ℝ) / (p : ℝ) ≤
        1.108 * (log (log ((100 * N : ℕ) : ℝ)) - log (log (N : ℝ)) + 1 / log (N : ℝ)) := by
      exact hub
    exact mul_le_mul_of_nonneg_left (hub'.trans h1) (by norm_num)
  linarith only [hxa, hIco_le, h100_ub]

lemma large_k_Sk_sub_61_le {k M : ℕ} (hM40k : 40000 ≤ M) (hkM : k - 1 ≤ Nat.primeCounting M)
    (hk : 1500 < k) :
    sumX (k - 2) - sumX 61 ≤
      1.05 * (log (log 12000) - log (log 290)) + 1.26 * (log (log (M : ℝ)) - log (log 12000)) + 0.085 := by
  have hk2_le : k - 2 ≤ Nat.primeCounting M := by omega
  have hS_mono : sumX (k - 2) ≤ sumX (Nat.primeCounting M) := by
    unfold sumX
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk2_le) (fun _ _ _ => xTerm_nonneg _)
  have h61_le : 61 ≤ Nat.primeCounting M := by
    rw [← primeCounting_290]
    exact Nat.monotone_primeCounting (by omega)
  have hsub_eq : sumX (Nat.primeCounting M) - sumX 61 =
      ∑ j ∈ Finset.Ico 61 (Nat.primeCounting M), xTerm j := by
    unfold sumX; rw [← Finset.sum_range_add_sum_Ico _ h61_le]; ring
  have hsplit_x : ∑ j ∈ Finset.Ico 61 (Nat.primeCounting M), xTerm j ≤
      (∑ p ∈ Nat.primesLE M \ Nat.primesLE 290, (1 : ℝ) / (p : ℝ)) + 0.004 := by
    have hid : ∀ j ∈ Finset.Ico 61 (Nat.primeCounting M),
        xTerm j = 1 / (pNth j : ℝ) + 1 / ((pNth j : ℝ) * ((pNth j : ℝ) - 1)) := by
      intro j _
      have hp2 : (2 : ℝ) ≤ (pNth j : ℝ) := by
        exact_mod_cast (Nat.nth_mem_of_infinite Nat.infinite_setOf_prime j).two_le
      unfold xTerm
      field_simp [show (pNth j : ℝ) ≠ 0 by linarith, show (pNth j : ℝ) - 1 ≠ 0 by linarith]
      ring
    rw [Finset.sum_congr rfl hid, Finset.sum_add_distrib]
    have h1 : ∑ j ∈ Finset.Ico 61 (Nat.primeCounting M), (1 : ℝ) / (pNth j : ℝ) ≤
        ∑ p ∈ Nat.primesLE M \ Nat.primesLE 290, (1 : ℝ) / (p : ℝ) := by
      have hsub : (Finset.Ico 61 (Nat.primeCounting M)).image pNth ⊆ Nat.primesLE M \ Nat.primesLE 290 := by
        intro p hp
        rw [Finset.mem_image] at hp
        rcases hp with ⟨j, hj, rfl⟩
        rw [Finset.mem_Ico] at hj
        have hp_gt : 290 < pNth j :=
          primeCounting_le_iff_pNth_gt.mp (by rw [primeCounting_290]; exact hj.1)
        have hp_le : pNth j ≤ M := by
          by_contra hgt; push Not at hgt
          have := primeCounting_le_iff_pNth_gt.mpr hgt
          omega
        rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE]
        exact ⟨⟨hp_le, Nat.nth_mem_of_infinite Nat.infinite_setOf_prime j⟩, fun h => by omega⟩
      calc ∑ j ∈ Finset.Ico 61 (Nat.primeCounting M), (1 : ℝ) / (pNth j : ℝ)
          = ∑ p ∈ (Finset.Ico 61 (Nat.primeCounting M)).image pNth, (1 : ℝ) / (p : ℝ) := by
            rw [Finset.sum_image]; intro i _ j _ hij; exact pNth_strictMono.injective hij
        _ ≤ ∑ p ∈ Nat.primesLE M \ Nat.primesLE 290, (1 : ℝ) / (p : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    have h2 : ∑ j ∈ Finset.Ico 61 (Nat.primeCounting M),
          1 / ((pNth j : ℝ) * ((pNth j : ℝ) - 1)) ≤ 0.004 := by
      have hsub : (Finset.Ico 61 (Nat.primeCounting M)).image pNth ⊆ Finset.Ico 291 (M + 1) := by
        intro p hp
        rw [Finset.mem_image] at hp
        rcases hp with ⟨j, hj, rfl⟩
        rw [Finset.mem_Ico] at hj ⊢
        have hp_gt : 290 < pNth j :=
          primeCounting_le_iff_pNth_gt.mp (by rw [primeCounting_290]; exact hj.1)
        have hp_le : pNth j ≤ M := by
          by_contra hgt; push Not at hgt
          have := primeCounting_le_iff_pNth_gt.mpr hgt
          omega
        omega
      calc ∑ j ∈ Finset.Ico 61 (Nat.primeCounting M), 1 / ((pNth j : ℝ) * ((pNth j : ℝ) - 1))
          = ∑ p ∈ (Finset.Ico 61 (Nat.primeCounting M)).image pNth, 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
            rw [Finset.sum_image]; intro i _ j _ hij; exact pNth_strictMono.injective hij
        _ ≤ ∑ n ∈ Finset.Ico 291 (M + 1), 1 / ((n : ℝ) * ((n : ℝ) - 1)) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn _ => by
              rw [Finset.mem_Ico] at hn
              have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 ≤ n)
              exact one_div_nonneg.mpr (mul_nonneg (by linarith only [hn2]) (by linarith only [hn2])))
        _ = ∑ n ∈ Finset.Ico 291 (M + 1), (1 / ((n : ℝ) - 1) - 1 / (((n + 1 : ℕ) : ℝ) - 1)) := by
            refine Finset.sum_congr rfl fun n hn => ?_
            rw [Finset.mem_Ico] at hn
            have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 ≤ n)
            have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
            have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
            push_cast
            field_simp [hn_pos.ne', hn1_pos.ne']; ring
        _ = 1 / ((291 : ℝ) - 1) - 1 / (((M + 1 : ℕ) : ℝ) - 1) := by
            have h := Finset.sum_Ico_sub (fun n : ℕ => 1 / ((n : ℝ) - 1)) (by omega : 291 ≤ M + 1)
            have hneg : ∑ n ∈ Finset.Ico 291 (M + 1), (1 / ((n : ℝ) - 1) - 1 / (((n + 1 : ℕ) : ℝ) - 1)) =
                - ∑ n ∈ Finset.Ico 291 (M + 1), (1 / (((n + 1 : ℕ) : ℝ) - 1) - 1 / ((n : ℝ) - 1)) := by
              rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun _ _ => by ring
            linarith only [h, hneg]
        _ ≤ 0.004 := by
            have hM1 : (1 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 1 < M)
            have hMeq : (((M + 1 : ℕ) : ℝ) - 1) = (M : ℝ) := by push_cast; ring
            rw [hMeq]
            have hMpos : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
            linarith
    linarith
  have habel := sum_inv_primes_abel (M := 290) (N := M) (by omega) (by omega)
  have hM_ub : Chebyshev.theta (M : ℝ) / ((M : ℝ) * log (M : ℝ)) ≤ 1.26 / log (M : ℝ) := by
    have ht := theta_le_126_10k (by omega : 10000 ≤ M)
    have hMpos : (0 : ℝ) < M := by positivity
    have hlogM : 0 < log (M : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
    calc Chebyshev.theta (M : ℝ) / ((M : ℝ) * log (M : ℝ))
        ≤ (1.26 * (M : ℝ)) / ((M : ℝ) * log (M : ℝ)) :=
          div_le_div_of_nonneg_right ht (mul_nonneg hMpos.le hlogM.le)
      _ = 1.26 / log (M : ℝ) := by field_simp [hMpos.ne', hlogM.ne']
  have h290_lb : 0.74 / log (290 : ℝ) ≤ Chebyshev.theta (290 : ℝ) / ((290 : ℝ) * log (290 : ℝ)) := by
    have ht := (theta_105_and_070_small (y := 290) (by omega) (by omega)).1
    have hlog290 : 0 < log (290 : ℝ) := Real.log_pos (by norm_num)
    calc 0.74 / log (290 : ℝ)
        = (0.74 * (290 : ℝ)) / ((290 : ℝ) * log (290 : ℝ)) := by field_simp [hlog290.ne']
      _ ≤ Chebyshev.theta (290 : ℝ) / ((290 : ℝ) * log (290 : ℝ)) :=
          div_le_div_of_nonneg_right ht (by positivity)
  have hdiff_nn : ∀ n ∈ Finset.Ico 290 M,
      0 ≤ 1 / ((n : ℝ) * log n) - 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1)) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hlogn : 0 < log n := Real.log_pos hn1
    have hlogn1 : log n ≤ log ((n : ℝ) + 1) := Real.log_le_log (by linarith) (by linarith)
    rw [sub_nonneg]
    refine one_div_le_one_div_of_le (mul_pos (by linarith) hlogn) ?_
    exact mul_le_mul (by linarith) hlogn1 hlogn.le (by linarith)
  have hIco_split : ∑ n ∈ Finset.Ico (290 : ℕ) M, Chebyshev.theta n *
        (1 / ((n : ℝ) * log n) - 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1))) =
      (∑ n ∈ Finset.Ico (290 : ℕ) 12000, Chebyshev.theta n *
        (1 / ((n : ℝ) * log n) - 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1)))) +
      (∑ n ∈ Finset.Ico (12000 : ℕ) M, Chebyshev.theta n *
        (1 / ((n : ℝ) * log n) - 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1)))) := by
    rw [← Finset.sum_Ico_consecutive _ (by omega : (290 : ℕ) ≤ 12000) (by omega : (12000 : ℕ) ≤ M)]
  have hpart1 : ∑ n ∈ Finset.Ico (290 : ℕ) 12000, Chebyshev.theta n *
        (1 / ((n : ℝ) * log n) - 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1))) ≤
      1.05 * ((1 / log 290 - 1 / log 12000) + (log (log 12000) - log (log 290))) := by
    have h1 : ∑ n ∈ Finset.Ico (290 : ℕ) 12000, Chebyshev.theta n *
          (1 / ((n : ℝ) * log n) - 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1))) ≤
        1.05 * ∑ n ∈ Finset.Ico (290 : ℕ) 12000, (n : ℝ) *
          (1 / ((n : ℝ) * log n) - 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun n hn => ?_
      have hn' := Finset.mem_Ico.mp hn
      have ht := (theta_105_and_070_small (by omega : 200 ≤ n) hn'.2).2
      have hnn := hdiff_nn n (Finset.mem_Ico.mpr ⟨hn'.1, by omega⟩)
      nlinarith only [ht, hnn]
    exact h1.trans (mul_le_mul_of_nonneg_left (sum_abel_n_diff_le (by omega) (by omega)) (by norm_num))
  have hpart2 : ∑ n ∈ Finset.Ico (12000 : ℕ) M, Chebyshev.theta n *
        (1 / ((n : ℝ) * log n) - 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1))) ≤
      1.26 * ((1 / log 12000 - 1 / log (M : ℝ)) + (log (log (M : ℝ)) - log (log 12000))) := by
    have h1 : ∑ n ∈ Finset.Ico (12000 : ℕ) M, Chebyshev.theta n *
          (1 / ((n : ℝ) * log n) - 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1))) ≤
        1.26 * ∑ n ∈ Finset.Ico (12000 : ℕ) M, (n : ℝ) *
          (1 / ((n : ℝ) * log n) - 1 / (((n : ℝ) + 1) * log ((n : ℝ) + 1))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun n hn => ?_
      have hn' := Finset.mem_Ico.mp hn
      have ht := theta_le_126_10k (by omega : 10000 ≤ n)
      have hnn := hdiff_nn n (Finset.mem_Ico.mpr ⟨by omega, hn'.2⟩)
      nlinarith only [ht, hnn]
    exact h1.trans (mul_le_mul_of_nonneg_left (sum_abel_n_diff_le (by omega) (by omega)) (by norm_num))
  have hlog290 : 5.6 ≤ log (290 : ℝ) := by
    rw [le_log_iff_exp_le (by norm_num)]
    calc exp 5.6 = (exp 1) ^ (5 : ℕ) * exp 0.6 := by rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
      _ ≤ (2.718282 : ℝ) ^ (5 : ℕ) * (1.83 : ℝ) := by
          gcongr
          · exact lt_trans Real.exp_one_lt_d9 (by norm_num) |>.le
          · have := Real.exp_bound (x := (0.6 : ℝ)) (by norm_num) (n := 4) (by norm_num)
            simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty] at this
            have hf0 : ((Nat.factorial 0 : ℕ) : ℝ) = 1 := by norm_num
            have hf1 : ((Nat.factorial 1 : ℕ) : ℝ) = 1 := by norm_num
            have hf2 : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num
            have hf3 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by exact_mod_cast (by decide : Nat.factorial 3 = 6)
            rw [hf0, hf1, hf2, hf3] at this; norm_num at this
            have hle : |exp (0.6 : ℝ) - (1 + 0.6 + 0.6 ^ 2 / 2 + 0.6 ^ 3 / 6)| < 0.014 := by
              have : (0.6 : ℝ) ^ 4 * ((Nat.succ 4 : ℝ) / (24 * 4)) < 0.014 := by norm_num
              linarith
            linarith [(abs_lt.mp hle).2]
      _ ≤ 290 := by norm_num
  have hlog12k : 9.3 ≤ log (12000 : ℝ) := by
    rw [le_log_iff_exp_le (by norm_num)]
    calc exp 9.3 = (exp 1) ^ (9 : ℕ) * exp 0.3 := by rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
      _ ≤ (2.718282 : ℝ) ^ (9 : ℕ) * (1.36 : ℝ) := by
          gcongr
          · exact lt_trans Real.exp_one_lt_d9 (by norm_num) |>.le
          · have := Real.exp_bound (x := (0.3 : ℝ)) (by norm_num) (n := 3) (by norm_num)
            simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty] at this
            have hf0 : ((Nat.factorial 0 : ℕ) : ℝ) = 1 := by norm_num
            have hf1 : ((Nat.factorial 1 : ℕ) : ℝ) = 1 := by norm_num
            have hf2 : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num
            rw [hf0, hf1, hf2] at this; norm_num at this
            have hle : |exp (0.3 : ℝ) - (1 + 0.3 + 0.3 ^ 2 / 2)| < 0.015 := by
              have : (0.3 : ℝ) ^ 3 * ((Nat.succ 3 : ℝ) / (6 * 3)) < 0.015 := by norm_num
              linarith
            linarith [(abs_lt.mp hle).2]
      _ ≤ 12000 := by norm_num
  have hinv290 : 1 / log (290 : ℝ) ≤ 1 / 5.6 := div_le_div_of_nonneg_left zero_le_one (by norm_num) hlog290
  have hinv12k : 1 / log (12000 : ℝ) ≤ 1 / 9.3 := div_le_div_of_nonneg_left zero_le_one (by norm_num) hlog12k
  simp only [Nat.cast_ofNat] at habel
  ring_nf at hsplit_x habel hIco_split hM_ub h290_lb hpart1 hpart2 hinv290 hinv12k ⊢
  linarith only [hS_mono, hsub_eq, hsplit_x, habel, hM_ub, h290_lb, hIco_split, hpart1, hpart2, hinv290, hinv12k]

lemma exp_05_le : exp (0.5 : ℝ) ≤ 1.65 := by
  have h := Real.exp_bound (x := (0.5 : ℝ)) (by norm_num) (n := 4) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty] at h
  have hf0 : ((Nat.factorial 0 : ℕ) : ℝ) = 1 := by norm_num
  have hf1 : ((Nat.factorial 1 : ℕ) : ℝ) = 1 := by norm_num
  have hf2 : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num
  have hf3 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by exact_mod_cast (by decide : Nat.factorial 3 = 6)
  rw [hf0, hf1, hf2, hf3] at h; norm_num at h
  have hle : |exp (0.5 : ℝ) - (1 + 0.5 + 0.5 ^ 2 / 2 + 0.5 ^ 3 / 6)| < 0.004 := by
    have : (0.5 : ℝ) ^ 4 * ((Nat.succ 4 : ℝ) / (24 * 4)) < 0.004 := by norm_num
    linarith
  linarith [(abs_lt.mp hle).2]

noncomputable def goodGap (k y : ℕ) : Prop :=
  200 ≤ y ∧ 2 * log (k : ℝ) + 2.4 < 0.70 * (y : ℝ) ∧
  ∃ a N : ℕ, 10000000 ≤ N ∧ pNth a < N ∧ N < pNth (a + 1) ∧
    2 * (y : ℝ) + 2 ≤ (pNth (a + 1) : ℝ) - (pNth a : ℝ) ∧
    Chebyshev.theta (y : ℝ) ≤ log (N : ℝ) ∧
    log (N : ℝ) ≤ Chebyshev.theta (y : ℝ) + log ((1001 * y ^ 2 : ℕ) : ℝ) ∧
    k - 1 ≤ a ∧
    elemSym (k - 2) a / elemSym (k - 1) a < (pNth (a + 1) : ℝ) - (pNth a : ℝ) + 1

lemma large_k_exists_y_good {k : ℕ} (hk1500 : 1500 < k) : ∃ y, goodGap k y := by
  refine ⟨k, by omega, ?_, ?_⟩
  · have hkR : (1501 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1501 ≤ k)
    have hlogk : log (k : ℝ) ≤ (k : ℝ) / 100 + 8 := by
      have h1 : log ((k : ℝ) / 100) ≤ (k : ℝ) / 100 - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div (by positivity) (by norm_num)] at h1
      have hlog100 : log (100 : ℝ) < 5 := by
        rw [log_lt_iff_lt_exp (by norm_num)]
        calc (100 : ℝ) < (2.71828 : ℝ) ^ (5 : ℕ) := by norm_num
          _ < (exp 1) ^ (5 : ℕ) := by gcongr; exact lt_trans (by norm_num) Real.exp_one_gt_d9
          _ = exp 5 := by rw [← Real.exp_nat_mul]; norm_num
      linarith
    linarith
  · obtain ⟨a, N, hN10m, haN, hNa1, hgap, hlogN_lb, hlogN_ub⟩ := exists_large_gap_below (by omega : 200 ≤ k)
    have hlogk_lb : 7.3 < log (k : ℝ) := (large_k_y_bounds hk1500).2.2.2.2
    have hkR : (1501 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1501 ≤ k)
    have hlogk : log (k : ℝ) ≤ (k : ℝ) / 100 + 8 := by
      have h1 : log ((k : ℝ) / 100) ≤ (k : ℝ) / 100 - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div (by positivity) (by norm_num)] at h1
      have hlog100 : log (100 : ℝ) < 5 := by
        rw [log_lt_iff_lt_exp (by norm_num)]
        calc (100 : ℝ) < (2.71828 : ℝ) ^ (5 : ℕ) := by norm_num
          _ < (exp 1) ^ (5 : ℕ) := by gcongr; exact lt_trans (by norm_num) Real.exp_one_gt_d9
          _ = exp 5 := by rw [← Real.exp_nat_mul]; norm_num
      linarith
    have hy_lb : 2 * log (k : ℝ) + 2.4 < 0.70 * (k : ℝ) := by linarith
    obtain ⟨M, hM_def⟩ : ∃ M : ℕ, M = ⌊4 * (k : ℝ) * log (k : ℝ)⌋₊ := ⟨_, rfl⟩
    have hMb := large_k_M_bounds hk1500 (by omega : 200 ≤ k) hN10m hlogk_lb hy_lb haN hNa1 hlogN_lb
    have hM40k : 40000 ≤ M := hM_def ▸ hMb.1
    have hkM : k - 1 ≤ Nat.primeCounting M := hM_def ▸ hMb.2.1
    have hMa : Nat.primeCounting M ≤ a := hM_def ▸ hMb.2.2.1
    have hlogM_ub : log (M : ℝ) ≤ log 4 + log (k : ℝ) + log (log (k : ℝ)) := hM_def ▸ hMb.2.2.2.1
    have hlogM_lb : 10.5 ≤ log (M : ℝ) := hM_def ▸ hMb.2.2.2.2
    have hD_lb := large_k_D_lb hM40k hN10m hkM hMa haN hNa1 hlogM_lb
    have hlogN_ge : 0.72 * (k : ℝ) ≤ log (N : ℝ) := by
      have ht : 0.72 * (k : ℝ) ≤ Chebyshev.theta (k : ℝ) := by
        by_cases hk12 : k < 12000
        · linarith [(theta_105_and_070_small (by omega) hk12).1]
        · exact theta_ge_072_10k (by omega)
      linarith
    have hD_ge_1 : 1 < sumX a - sumX (k - 2) := by
      have hlogM_le2 : log (M : ℝ) ≤ 2.1 * log (k : ℝ) := by
        have hlog4 : log (4 : ℝ) < 1.4 := by
          have h2 : log (2 : ℝ) < 0.7 := lt_trans Real.log_two_lt_d9 (by norm_num)
          have h4 : log (4 : ℝ) = 2 * log (2 : ℝ) := by
            rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
          linarith only [h2, h4]
        have hll : log (log (k : ℝ)) ≤ log (k : ℝ) - 1 := Real.log_le_sub_one_of_pos (by linarith)
        linarith
      have hllM : log (log (M : ℝ)) ≤ log (2.1 * log (k : ℝ)) :=
        Real.log_le_log (by linarith) hlogM_le2
      have hllN : log (0.72 * (k : ℝ)) ≤ log (log (N : ℝ)) :=
        Real.log_le_log (by positivity) (by linarith)
      have hratio : 0.90 * log (0.72 * (k : ℝ)) - 0.90 * log (2.1 * log (k : ℝ)) - 0.52 > 1 := by
        have h1 : log (0.72 * (k : ℝ)) = log 0.72 + log (k : ℝ) :=
          Real.log_mul (by norm_num) (by positivity)
        have hlog072 : -0.35 ≤ log (0.72 : ℝ) := by
          rw [le_log_iff_exp_le (by norm_num)]
          have h := Real.exp_neg_one_lt_d9
          have h035 : exp (-0.35 : ℝ) ≤ 0.71 := by
            rw [Real.exp_neg, inv_le_comm₀ (by positivity) (by norm_num)]
            have h1' : (1 : ℝ) + 0.35 + 0.35 ^ 2 / 2 ≤ exp 0.35 := by
              have := Real.sum_le_exp_of_nonneg (x := (0.35 : ℝ)) (by norm_num) 3
              simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty] at this
              norm_num at this; linarith
            linarith
          linarith
        have h2 : log (2.1 * log (k : ℝ)) ≤ log 2.1 + log (k : ℝ) / 3 + 0.15 := by
          rw [Real.log_mul (by norm_num) (by linarith)]
          have hll : log (log (k : ℝ) / 3) ≤ log (k : ℝ) / 3 - 1 :=
            Real.log_le_sub_one_of_pos (by linarith)
          rw [Real.log_div (by linarith) (by norm_num)] at hll
          have hlog3 : log (3 : ℝ) < 1.15 := by
            have h := exp_div_100_gt_of_lt (B := 3) (wt := 115) (by norm_num) (by norm_num)
            norm_num at h; linarith only [h]
          linarith
        have hlog21 : log (2.1 : ℝ) < 0.8 := by
          have h1 := exp_div_100_gt_of_lt (B := 21) (wt := 310) (by norm_num) (by norm_num)
          have h2 : log (21 : ℝ) = log 2.1 + log 10 := by
            rw [show (21 : ℝ) = 2.1 * 10 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
          have h3 := exp_div_100_lt_of_gt (B := 10) (wt := 230) (by norm_num) (by norm_num)
          norm_num at h1 h3; linarith
        linarith
      have hllM_pos : 0 < log (log (M : ℝ)) := Real.log_pos (by linarith only [hlogM_lb])
      split_ifs at hD_lb <;> linarith only [hD_lb, hllM, hllN, hratio, hllM_pos]
    have hub := R_upper_bound (by omega) (hkM.trans hMa) (by linarith)
    have hnum : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : k - 1 ≤ k)
    have hdiv : ((k - 1 : ℕ) : ℝ) / (sumX a - sumX (k - 2)) < (k : ℝ) := by
      rw [div_lt_iff₀ (by linarith)]
      nlinarith only [hnum, hD_ge_1, hkR]
    refine ⟨a, N, hN10m, haN, hNa1, hgap, hlogN_lb, hlogN_ub, hkM.trans hMa, ?_⟩
    linarith only [hub, hdiv, hgap, hkR]

private lemma lk_log10_gt : (2.3 : ℝ) < log (10 : ℝ) := by
  have h := exp_div_100_lt_of_gt (B := 10) (wt := 230) (by norm_num) (by norm_num)
  norm_num at h; linarith only [h]

private lemma lk_log10_lt : log (10 : ℝ) < (2.31 : ℝ) := by
  have h := exp_div_100_gt_of_lt (B := 10) (wt := 231) (by norm_num) (by norm_num)
  norm_num at h; linarith only [h]

private lemma lk_log100_gt : (4.6 : ℝ) < log (100 : ℝ) := by
  have h := exp_div_100_lt_of_gt (B := 100) (wt := 460) (by norm_num) (by norm_num)
  norm_num at h; linarith only [h]

private lemma lk_log100_lt : log (100 : ℝ) < (4.61 : ℝ) := by
  have h := exp_div_100_gt_of_lt (B := 100) (wt := 461) (by norm_num) (by norm_num)
  norm_num at h; linarith only [h]

private lemma lk_log1000_gt : (6.9 : ℝ) < log (1000 : ℝ) := by
  have h := exp_div_100_lt_of_gt (B := 1000) (wt := 690) (by norm_num) (by norm_num)
  norm_num at h; linarith only [h]

private lemma lk_log1000_lt : log (1000 : ℝ) < (6.91 : ℝ) := by
  have h := exp_div_100_gt_of_lt (B := 1000) (wt := 691) (by norm_num) (by norm_num)
  norm_num at h; linarith only [h]

private lemma lk_log1001_le : log (1001 : ℝ) ≤ 6.91 := by
  have h := exp_div_100_gt_of_lt (B := 1001) (wt := 691) (by norm_num) (by norm_num)
  norm_num at h; linarith only [h]

private lemma lk_log200_le : log (200 : ℝ) ≤ 5.30 := by
  have h := exp_div_100_gt_of_lt (B := 200) (wt := 530) (by norm_num) (by norm_num)
  norm_num at h; linarith only [h]

private lemma lk_log201_le : log (201 : ℝ) ≤ 5.31 := by
  have h := exp_div_100_gt_of_lt (B := 201) (wt := 531) (by norm_num) (by norm_num)
  norm_num at h; linarith only [h]

private lemma lk_log2322_le : log (232.2 : ℝ) ≤ 5.46 := by
  have h := exp_div_100_gt_of_lt (B := 233) (wt := 546) (by norm_num) (by norm_num)
  norm_num at h
  exact (Real.log_le_log (by norm_num) (by norm_num : (232.2 : ℝ) ≤ 233)).trans (by linarith only [h])

private lemma lk_log10_le : log (10 : ℝ) ≤ 2.4 := by linarith only [lk_log10_lt]

private lemma lk_log5_le : log (5 : ℝ) ≤ 1.65 := by
  have h := exp_div_100_gt_of_lt (B := 5) (wt := 165) (by norm_num) (by norm_num)
  norm_num at h; linarith only [h]

private lemma lk_log1000_le : log (1000 : ℝ) ≤ 7 := by linarith only [lk_log1000_lt]

private lemma lk_log50000_lt : log (50000 : ℝ) < 12 := by
  have h := exp_div_100_gt_of_lt (B := 50000) (wt := 1200) (by norm_num) (by norm_num)
  norm_num at h; linarith only [h]

private lemma lk_exp045_ge : (1.56 : ℝ) ≤ exp 0.45 := by
  have h := exp_div_100_gt_of_lt (B := 156) (wt := 505) (by norm_num) (by norm_num)
  have h1 : log (1.56 : ℝ) = log 156 - log 100 := by
    rw [show (1.56 : ℝ) = 156 / 100 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  norm_num at h
  exact (log_le_iff_le_exp (by norm_num)).mp (by linarith only [h, h1, lk_log100_gt])

private lemma lk_exp057_ge : (1.75 : ℝ) ≤ exp 0.57 := by
  have h := exp_div_100_gt_of_lt (B := 175) (wt := 517) (by norm_num) (by norm_num)
  have h1 : log (1.75 : ℝ) = log 175 - log 100 := by
    rw [show (1.75 : ℝ) = 175 / 100 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  norm_num at h
  exact (log_le_iff_le_exp (by norm_num)).mp (by linarith only [h, h1, lk_log100_gt])

private lemma lk_ll290_ge : (1.73 : ℝ) ≤ log (log (290 : ℝ)) := by
  have h1 := exp_div_100_lt_of_gt (B := 290) (wt := 566) (by norm_num) (by norm_num)
  have h2 := exp_div_100_lt_of_gt (B := 5660) (wt := 864) (by norm_num) (by norm_num)
  have h3 : log (5.66 : ℝ) = log 5660 - log 1000 := by
    rw [show (5.66 : ℝ) = 5660 / 1000 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  norm_num at h1 h2
  have h566 : (5.66 : ℝ) ≤ log (290 : ℝ) := by linarith only [h1]
  have h173 : (1.73 : ℝ) ≤ log (5.66 : ℝ) := by linarith only [h2, h3, lk_log1000_lt]
  exact h173.trans (Real.log_le_log (by norm_num) h566)

private lemma lk_ll12k_ge : (2.23 : ℝ) ≤ log (log (12000 : ℝ)) := by
  have h1 := exp_div_100_lt_of_gt (B := 12000) (wt := 939) (by norm_num) (by norm_num)
  have h2 := exp_div_100_lt_of_gt (B := 939) (wt := 684) (by norm_num) (by norm_num)
  have h3 : log (9.39 : ℝ) = log 939 - log 100 := by
    rw [show (9.39 : ℝ) = 939 / 100 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  norm_num at h1 h2
  have h939 : (9.39 : ℝ) ≤ log (12000 : ℝ) := by linarith only [h1]
  have h223 : (2.23 : ℝ) ≤ log (9.39 : ℝ) := by linarith only [h2, h3, lk_log100_lt]
  exact h223.trans (Real.log_le_log (by norm_num) h939)

private lemma lk_ll12k_le : log (log (12000 : ℝ)) ≤ 2.25 := by
  have h1 := exp_div_100_gt_of_lt (B := 12000) (wt := 940) (by norm_num) (by norm_num)
  have h2 := exp_div_100_gt_of_lt (B := 940) (wt := 685) (by norm_num) (by norm_num)
  have h3 : log (9.40 : ℝ) = log 940 - log 100 := by
    rw [show (9.40 : ℝ) = 940 / 100 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  norm_num at h1 h2
  have h940 : log (12000 : ℝ) ≤ 9.40 := by linarith only [h1]
  have hpos : 0 < log (12000 : ℝ) := Real.log_pos (by norm_num)
  exact (Real.log_le_log hpos h940).trans (by linarith only [h2, h3, lk_log100_gt])

private lemma lk_log12000_le : log (12000 : ℝ) ≤ 9.40 := by
  have h := exp_div_100_gt_of_lt (B := 12000) (wt := 940) (by norm_num) (by norm_num)
  norm_num at h; linarith only [h]

private lemma lk_log15000_le : log (15000 : ℝ) ≤ 9.7 := by
  have h := exp_div_100_gt_of_lt (B := 15000) (wt := 970) (by norm_num) (by norm_num)
  norm_num at h; linarith only [h]

private lemma lk_log97_le : log (9.7 : ℝ) ≤ 2.28 := by
  have h := exp_div_100_gt_of_lt (B := 97) (wt := 458) (by norm_num) (by norm_num)
  have h1 : log (9.7 : ℝ) = log 97 - log 10 := by
    rw [show (9.7 : ℝ) = 97 / 10 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  norm_num at h; linarith only [h, h1, lk_log10_gt]

private lemma lk_log134_le : log (13.4 : ℝ) ≤ 2.60 := by
  have h := exp_div_100_gt_of_lt (B := 134) (wt := 490) (by norm_num) (by norm_num)
  have h1 : log (13.4 : ℝ) = log 134 - log 10 := by
    rw [show (13.4 : ℝ) = 134 / 10 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  norm_num at h; linarith only [h, h1, lk_log10_gt]

private lemma lk_log650_le : log (650 : ℝ) ≤ 6.5 := by
  have h := exp_div_100_gt_of_lt (B := 650) (wt := 650) (by norm_num) (by norm_num)
  norm_num at h; linarith only [h]

private lemma lk_log3000_le : log (3000 : ℝ) ≤ 8.1 := by
  have h := exp_div_100_gt_of_lt (B := 3000) (wt := 810) (by norm_num) (by norm_num)
  norm_num at h; linarith only [h]

private lemma lk_log81_le : log (8.1 : ℝ) ≤ 2.1 := by
  have h := exp_div_100_gt_of_lt (B := 81) (wt := 440) (by norm_num) (by norm_num)
  have h1 : log (8.1 : ℝ) = log 81 - log 10 := by
    rw [show (8.1 : ℝ) = 81 / 10 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  norm_num at h; linarith only [h, h1, lk_log10_gt]

private lemma lk_log116_le : log (11.6 : ℝ) ≤ 2.46 := by
  have h := exp_div_100_gt_of_lt (B := 116) (wt := 476) (by norm_num) (by norm_num)
  have h1 : log (11.6 : ℝ) = log 116 - log 10 := by
    rw [show (11.6 : ℝ) = 116 / 10 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  norm_num at h; linarith only [h, h1, lk_log10_gt]

private lemma lk_log15000_ge : (9.6 : ℝ) ≤ log (15000 : ℝ) := by
  have h := exp_div_100_lt_of_gt (B := 15000) (wt := 960) (by norm_num) (by norm_num)
  norm_num at h; linarith only [h]

private lemma lk_log110000_le : log (110000 : ℝ) ≤ 11.7 := by
  have h := exp_div_100_gt_of_lt (B := 110000) (wt := 1170) (by norm_num) (by norm_num)
  norm_num at h; linarith only [h]

private lemma lk_log117_le : log (11.7 : ℝ) ≤ 2.5 := by
  have h := exp_div_100_gt_of_lt (B := 117) (wt := 480) (by norm_num) (by norm_num)
  have h1 : log (11.7 : ℝ) = log 117 - log 10 := by
    rw [show (11.7 : ℝ) = 117 / 10 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  norm_num at h; linarith only [h, h1, lk_log10_gt]

private lemma lk_log16_le : log (16 : ℝ) ≤ 2.80 := by
  have h := exp_div_100_gt_of_lt (B := 16) (wt := 280) (by norm_num) (by norm_num)
  norm_num at h; linarith only [h]

private lemma lk_log110000_ge : (11.6 : ℝ) ≤ log (110000 : ℝ) := by
  have h := exp_div_100_lt_of_gt (B := 110000) (wt := 1160) (by norm_num) (by norm_num)
  norm_num at h; linarith only [h]

private lemma lk_log135_le : log (1.35 : ℝ) ≤ 0.31 := by
  have h := exp_div_100_gt_of_lt (B := 135) (wt := 491) (by norm_num) (by norm_num)
  have h1 : log (1.35 : ℝ) = log 135 - log 100 := by
    rw [show (1.35 : ℝ) = 135 / 100 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  norm_num at h; linarith only [h, h1, lk_log100_gt]

private lemma lk_log105_ge : (2.34 : ℝ) ≤ log (10.5 : ℝ) := by
  have h := exp_div_100_lt_of_gt (B := 105) (wt := 465) (by norm_num) (by norm_num)
  have h1 : log (10.5 : ℝ) = log 105 - log 10 := by
    rw [show (10.5 : ℝ) = 105 / 10 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  norm_num at h; linarith only [h, h1, lk_log10_lt]

private lemma large_k_y1_D_big_ge95k {k y a N M : ℕ}
    (hk95' : 95000 ≤ k) (hden_pos : 0 < 0.90 * log (k : ℝ) - 2.5)
    (hlogk_lb : 7.3 < log (k : ℝ))
    (hlogN_ge : 0.72 * (y : ℝ) ≤ log (N : ℝ))
    (hlogM_ub : log (M : ℝ) ≤ log 4 + log (k : ℝ) + log (log (k : ℝ)))
    (hlogM_lb : 10.5 ≤ log (M : ℝ))
    (hlogM_pos : 0 < log (M : ℝ))
    (hyR' : 0.76 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5) - 1 < (y : ℝ))
    {D : ℝ}
    (hD_lb : (if M < 10000000 then 0.90 * log (log (N : ℝ)) - 0.80 * log (log (M : ℝ)) - 0.52
              else 0.90 * (log (log (N : ℝ)) - log (log (M : ℝ))) - 0.10) ≤ D) :
    0.90 * log (k : ℝ) - 2.5 < 1.52 * D := by
  have h054 : 0.54 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5) ≤ log (N : ℝ) := by
    have h1 : 0.72 * (y : ℝ) ≥ 0.72 * (0.75 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5)) := by
      have hbig : (1 : ℝ) < 0.01 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5) := by
        have h95R : (95000 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk95'
        have hlog1000 : log (1000 : ℝ) < 6.91 := lk_log1000_lt
        have hlogk_ub : log (k : ℝ) ≤ (k : ℝ) / 1000 - 1 + log (1000 : ℝ) := by
          have h := Real.log_le_sub_one_of_pos (show 0 < (k : ℝ) / 1000 by positivity)
          rw [Real.log_div (by positivity) (by norm_num)] at h
          linarith only [h]
        rw [lt_div_iff₀ hden_pos]
        linarith only [h95R, hlog1000, hlogk_ub]
      have hsub : 0.75 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5) =
          0.76 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5) -
          0.01 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5) := by ring
      linarith only [hyR', hbig, hsub]
    have hmul54 : 0.54 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5) =
        0.72 * (0.75 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5)) := by ring
    linarith only [hlogN_ge, h1, hmul54]
  have hllN : log (0.54 * (k : ℝ)) - log (0.90 * log (k : ℝ) - 2.5) ≤ log (log (N : ℝ)) := by
    have h0 : log (0.54 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5)) ≤ log (log (N : ℝ)) :=
      Real.log_le_log (div_pos (by positivity) hden_pos) h054
    rwa [Real.log_div (by positivity) hden_pos.ne'] at h0
  have hlog10_gt : 2.3 < log (10 : ℝ) := lk_log10_gt
  have hlog100_gt : 4.6 < log (100 : ℝ) := lk_log100_gt
  have hlog054 : -0.62 ≤ log (0.54 : ℝ) := by
    have h1 := exp_div_100_lt_of_gt (B := 540) (wt := 629) (by norm_num) (by norm_num)
    have h3 : log (0.54 : ℝ) = log 540 - log 1000 := by
      rw [show (0.54 : ℝ) = 540 / 1000 by norm_num, Real.log_div (by norm_num) (by norm_num)]
    norm_num at h1; linarith only [h1, h3, lk_log1000_lt]
  have hk114 : 11.4 ≤ log (k : ℝ) := by
    have hk95R : (95000 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk95'
    have h1 := exp_div_100_lt_of_gt (B := 95000) (wt := 1140) (by norm_num) (by norm_num)
    norm_num at h1
    exact (by linarith only [h1] : (11.4 : ℝ) ≤ log (95000 : ℝ)).trans (Real.log_le_log (by norm_num) hk95R)
  have hlog4 : log (4 : ℝ) < 1.4 := by
    have h2 : log (2 : ℝ) < 0.7 := lt_trans Real.log_two_lt_d9 (by norm_num)
    have h4 : log (4 : ℝ) = 2 * log (2 : ℝ) := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
    linarith only [h2, h4]
  have hll_den : log (0.90 * log (k : ℝ) - 2.5) ≤ log (0.90 * log (k : ℝ)) :=
    Real.log_le_log hden_pos (sub_le_self _ (by norm_num))
  have hlog090 : log (0.90 : ℝ) ≤ -0.10 := by
    have h1 := exp_div_100_gt_of_lt (B := 9) (wt := 220) (by norm_num) (by norm_num)
    have h2 : log (0.90 : ℝ) = log 9 - log 10 := by
      rw [show (0.90 : ℝ) = 9 / 10 by norm_num, Real.log_div (by norm_num) (by norm_num)]
    norm_num at h1; linarith only [h1, h2, hlog10_gt]
  have hllM_14 : log (M : ℝ) ≤ 1.38 * log (k : ℝ) := by
    have hllk : log (log (k : ℝ)) ≤ log (k : ℝ) / 5 + 0.65 := by
      have h1 := Real.log_le_sub_one_of_pos (show 0 < log (k : ℝ) / 5 by linarith only [hlogk_lb])
      rw [Real.log_div (by linarith only [hlogk_lb]) (by norm_num)] at h1
      linarith only [h1, lk_log5_le]
    linarith only [hlogM_ub, hlog4, hllk, hk114]
  have hllM_le : log (log (M : ℝ)) ≤ log 1.38 + log (log (k : ℝ)) := by
    have h1 := Real.log_le_log hlogM_pos hllM_14
    rwa [Real.log_mul (by norm_num) (by linarith only [hlogk_lb])] at h1
  have hlog135 : log (1.38 : ℝ) ≤ 0.33 := by
    have h := exp_div_100_gt_of_lt (B := 138) (wt := 493) (by norm_num) (by norm_num)
    have h2 : log (1.38 : ℝ) = log 138 - log 100 := by
      rw [show (1.38 : ℝ) = 138 / 100 by norm_num, Real.log_div (by norm_num) (by norm_num)]
    norm_num at h; linarith only [h, h2, lk_log100_gt]
  have hllN' : 0.90 * (log (k : ℝ) - 0.62 - (-0.10 + log (log (k : ℝ)))) ≤ 0.90 * log (log (N : ℝ)) := by
    have h1 : log (0.54 * (k : ℝ)) = log 0.54 + log (k : ℝ) := Real.log_mul (by norm_num) (by positivity)
    have h2 : log (0.90 * log (k : ℝ)) = log 0.90 + log (log (k : ℝ)) := Real.log_mul (by norm_num) (by linarith only [hlogk_lb])
    linarith only [hllN, h1, hlog054, hll_den, h2, hlog090]
  by_cases hk14 : 14 ≤ log (k : ℝ)
  · have hllk_ub : log (log (k : ℝ)) ≤ 2.64 + (log (k : ℝ) - 14) / 14 := by
      have h1 := Real.log_le_sub_one_of_pos (show 0 < log (k : ℝ) / 14 by linarith only [hlogk_lb])
      rw [Real.log_div (by linarith only [hlogk_lb]) (by norm_num)] at h1
      have hlog14 : log (14 : ℝ) ≤ 2.64 := by
        have h := exp_div_100_gt_of_lt (B := 14) (wt := 264) (by norm_num) (by norm_num)
        norm_num at h; linarith only [h]
      linarith only [h1, hlog14]
    split_ifs at hD_lb
    · linarith only [hD_lb, hllN', hllM_le, hlog135, hllk_ub, hk14]
    · have hllM_pos : 0 < log (log (M : ℝ)) := Real.log_pos (by linarith only [hlogM_lb])
      linarith only [hD_lb, hllN', hllM_le, hlog135, hllk_ub, hk14, hllM_pos]
  · have hk_lt14 : log (k : ℝ) < 14 := by linarith only [hk14]
    have hden_lin : log (0.90 * log (k : ℝ) - 2.5) ≤ 2.08 + 0.1125 * log (k : ℝ) - 1.3125 := by
      have h1 : log ((0.90 * log (k : ℝ) - 2.5) / 8) ≤ (0.90 * log (k : ℝ) - 2.5) / 8 - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div hden_pos.ne' (by norm_num)] at h1
      have hlog8 : log (8 : ℝ) ≤ 2.08 := by
        have h := exp_div_100_gt_of_lt (B := 8) (wt := 208) (by norm_num) (by norm_num)
        norm_num at h; linarith only [h]
      have h8 : (0.90 * log (k : ℝ) - 2.5) / 8 - 1 = 0.1125 * log (k : ℝ) - 1.3125 := by ring
      linarith only [h1, hlog8, h8]
    have hllN_lin : 0.90 * (0.8875 * log (k : ℝ) - 1.3875) ≤ 0.90 * log (log (N : ℝ)) := by
      have h1 : log (0.54 * (k : ℝ)) = log 0.54 + log (k : ℝ) := Real.log_mul (by norm_num) (by positivity)
      linarith only [hllN, h1, hlog054, hden_lin]
    by_cases hk119 : log (k : ℝ) ≤ 11.9
    · have hllM119 : log (log (M : ℝ)) ≤ 2.77 := by
        have hlogM119 : log (M : ℝ) ≤ 15.8 := by
          have hllk : log (log (k : ℝ)) ≤ 2.48 := by
            have h3 := exp_div_100_gt_of_lt (B := 119) (wt := 478) (by norm_num) (by norm_num)
            have h4 : log (11.9 : ℝ) = log 119 - log 10 := by
              rw [show (11.9 : ℝ) = 119 / 10 by norm_num, Real.log_div (by norm_num) (by norm_num)]
            have h5 := Real.log_le_log (by linarith only [hlogk_lb]) hk119
            norm_num at h3; linarith only [h3, h4, h5, hlog10_gt]
          linarith only [hlogM_ub, hlog4, hk119, hllk]
        have h2 : log (15.8 : ℝ) ≤ 2.77 := by
          have h3 := exp_div_100_gt_of_lt (B := 158) (wt := 507) (by norm_num) (by norm_num)
          have h4 : log (15.8 : ℝ) = log 158 - log 10 := by
            rw [show (15.8 : ℝ) = 158 / 10 by norm_num, Real.log_div (by norm_num) (by norm_num)]
          norm_num at h3; linarith only [h3, h4, hlog10_gt]
        exact (Real.log_le_log hlogM_pos hlogM119).trans h2
      split_ifs at hD_lb <;> linarith only [hD_lb, hllN_lin, hllM119, hk114]
    · have hk119' : 11.9 < log (k : ℝ) := by linarith only [hk119]
      have hllM14 : log (log (M : ℝ)) ≤ 2.90 := by
        have hlogM14 : log (M : ℝ) ≤ 18.1 := by
          have hllk : log (log (k : ℝ)) ≤ 2.64 := by
            have h3 := exp_div_100_gt_of_lt (B := 14) (wt := 264) (by norm_num) (by norm_num)
            have h5 := Real.log_le_log (by linarith only [hlogk_lb]) hk_lt14.le
            norm_num at h3; linarith only [h3, h5]
          linarith only [hlogM_ub, hlog4, hk_lt14, hllk]
        have h2 : log (18.1 : ℝ) ≤ 2.90 := by
          have h3 := exp_div_100_gt_of_lt (B := 181) (wt := 520) (by norm_num) (by norm_num)
          have h4 : log (18.1 : ℝ) = log 181 - log 10 := by
            rw [show (18.1 : ℝ) = 181 / 10 by norm_num, Real.log_div (by norm_num) (by norm_num)]
          norm_num at h3; linarith only [h3, h4, hlog10_gt]
        exact (Real.log_le_log hlogM_pos hlogM14).trans h2
      split_ifs at hD_lb <;> linarith only [hD_lb, hllN_lin, hllM14, hk119']

lemma large_k_y1_good {k : ℕ} (hk1500 : 1500 < k) :
    goodGap k (if k < 95000 then ⌊0.86 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5)⌋₊
               else ⌊0.76 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5)⌋₊) := by
  obtain ⟨y, hy_def⟩ : ∃ y : ℕ,
      y = (if k < 95000 then ⌊0.86 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5)⌋₊
           else ⌊0.76 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5)⌋₊) := ⟨_, rfl⟩
  have hyb := large_k_y_bounds hk1500
  have hy290 : 290 ≤ y := hy_def ▸ hyb.1
  have hy_lt : k < 110000 → y < 12000 := hy_def ▸ hyb.2.1
  have hy_10k : 110000 ≤ k → 10000 ≤ y := hy_def ▸ hyb.2.2.1
  have hden_pos : 0 < 0.90 * log (k : ℝ) - 2.5 := hyb.2.2.2.1
  have hlogk_lb : 7.3 < log (k : ℝ) := hyb.2.2.2.2
  have hkR : (1501 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1501 ≤ k)
  have hy_lb : 2 * log (k : ℝ) + 2.4 < 0.70 * (y : ℝ) := by
    by_cases hk95 : k < 95000
    · have hy290R : (290 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy290
      have hklt : log (k : ℝ) < 11.5 := by
        have hk95k : (k : ℝ) < 95000 := by exact_mod_cast hk95
        have h1 := exp_div_100_gt_of_lt (B := 95000) (wt := 1150) (by norm_num) (by norm_num)
        norm_num at h1
        exact (Real.log_lt_log (by positivity) hk95k).trans (by linarith only [h1])
      linarith only [hy290R, hklt]
    · have hk95R : (95000 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 95000 ≤ k)
      have hyR : 0.76 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5) - 1 < (y : ℝ) := by
        rw [hy_def, if_neg hk95]; exact Nat.sub_one_lt_floor _
      have hmul : 0.532 * (k : ℝ) - 0.70 * (0.90 * log (k : ℝ) - 2.5) <
          0.70 * (y : ℝ) * (0.90 * log (k : ℝ) - 2.5) := by
        have := mul_lt_mul_of_pos_right hyR hden_pos
        rw [sub_mul, div_mul_cancel₀ _ hden_pos.ne'] at this
        linarith only [this]
      have hlog_sq : (log (k : ℝ)) ^ 2 < 0.06 * (k : ℝ) := by
        have h1 : log (k : ℝ) ≤ 4 * ((k : ℝ) ^ (1 / 4 : ℝ)) := by
          have h := Real.log_le_rpow_div (x := (k : ℝ)) (ε := (1 / 4 : ℝ)) (by positivity) (by norm_num)
          linarith
        have h3 : ((k : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = √(k : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
          norm_num; exact Real.sqrt_eq_rpow (k : ℝ) |>.symm
        have hsq_k : 16 * √(k : ℝ) < 0.06 * (k : ℝ) := by
          have h300 : (300 : ℝ) ≤ √(k : ℝ) := by
            rw [Real.le_sqrt (by norm_num) (by positivity)]
            linarith only [hk95R]
          nlinarith only [h300, Real.sq_sqrt (show 0 ≤ (k : ℝ) by positivity)]
        have hlog_nn : 0 ≤ log (k : ℝ) := by linarith only [hlogk_lb]
        nlinarith only [h1, h3, hsq_k, hlog_nn]
      have hquad : (2 * log (k : ℝ) + 2.4) * (0.90 * log (k : ℝ) - 2.5) <
          0.532 * (k : ℝ) - 0.70 * (0.90 * log (k : ℝ) - 2.5) := by
        nlinarith only [hlog_sq, hk95R, hlogk_lb]
      nlinarith only [hmul, hquad, hden_pos]
  obtain ⟨a, N, hN10m, haN, hNa1, hgap, hlogN_lb, hlogN_ub⟩ := exists_large_gap_below (by omega : 200 ≤ y)
  obtain ⟨M, hM_def⟩ : ∃ M : ℕ, M = ⌊4 * (k : ℝ) * log (k : ℝ)⌋₊ := ⟨_, rfl⟩
  have hMb := large_k_M_bounds hk1500 (by omega : 200 ≤ y) hN10m hlogk_lb hy_lb haN hNa1 hlogN_lb
  have hM40k : 40000 ≤ M := hM_def ▸ hMb.1
  have hkM : k - 1 ≤ Nat.primeCounting M := hM_def ▸ hMb.2.1
  have hMa : Nat.primeCounting M ≤ a := hM_def ▸ hMb.2.2.1
  have hlogM_ub : log (M : ℝ) ≤ log 4 + log (k : ℝ) + log (log (k : ℝ)) := hM_def ▸ hMb.2.2.2.1
  have hlogM_lb : 10.5 ≤ log (M : ℝ) := hM_def ▸ hMb.2.2.2.2
  have hD_lb := large_k_D_lb hM40k hN10m hkM hMa haN hNa1 hlogM_lb
  have hlogN_ge : 0.72 * (y : ℝ) ≤ log (N : ℝ) := by
    have ht : 0.72 * (y : ℝ) ≤ Chebyshev.theta (y : ℝ) := by
      by_cases hy12 : y < 12000
      · linarith [(theta_105_and_070_small (by omega) hy12).1]
      · exact theta_ge_072_10k (by omega)
    linarith
  have hlogM_pos : 0 < log (M : ℝ) := by linarith
  have hllM_ub : log (log (M : ℝ)) ≤ log (log 4 + log (k : ℝ) + log (log (k : ℝ))) :=
    Real.log_le_log hlogM_pos hlogM_ub
  have hD_pos : 0 < sumX a - sumX (k - 2) := by
    have hy074 : 2 * log (k : ℝ) + 2.4 < 0.72 * (y : ℝ) := by linarith
    have hlogN_gt : 2 * log (k : ℝ) + 2.4 < log (N : ℝ) := lt_of_lt_of_le hy074 hlogN_ge
    have hllN_gt : log (2 * log (k : ℝ) + 2.4) < log (log (N : ℝ)) :=
      Real.log_lt_log (by linarith) hlogN_gt
    have hlog4 : log (4 : ℝ) < 1.4 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      linarith [lt_trans Real.log_two_lt_d9 (by norm_num : (0.6931471808 : ℝ) < 0.7)]
    have hllk : log (log (k : ℝ)) ≤ log (k : ℝ) / 4 + 0.4 := by
      have h1 := Real.log_le_sub_one_of_pos (show 0 < log (k : ℝ) / 4 by linarith)
      rw [Real.log_div (by linarith) (by norm_num)] at h1
      have hlog4 : log (4 : ℝ) < 1.4 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
        linarith [lt_trans Real.log_two_lt_d9 (by norm_num : (0.6931471808 : ℝ) < 0.7)]
      linarith
    have hll_le : log (log 4 + log (k : ℝ) + log (log (k : ℝ))) ≤ log (2 * log (k : ℝ) + 2.4) - 0.35 := by
      have hlogsum_pos : 0 < log 4 + log (k : ℝ) + log (log (k : ℝ)) := by
        have : 0 < log (4 : ℝ) := Real.log_pos (by norm_num)
        have : 0 < log (log (k : ℝ)) := Real.log_pos (by linarith only [hlogk_lb])
        linarith only [‹0 < log (4 : ℝ)›, hlogk_lb, ‹0 < log (log (k : ℝ))›]
      have hexp35 : exp (0.35 : ℝ) ≤ 1.43 := by
        have h1 := exp_div_100_lt_of_gt (B := 143) (wt := 496) (by norm_num) (by norm_num)
        have h2 := exp_div_100_gt_of_lt (B := 100) (wt := 461) (by norm_num) (by norm_num)
        have h3 : log (1.43 : ℝ) = log 143 - log 100 := by
          rw [show (1.43 : ℝ) = 143 / 100 by norm_num, Real.log_div (by norm_num) (by norm_num)]
        have h35 : (0.35 : ℝ) ≤ log (1.43 : ℝ) := by norm_num at h1 h2; linarith only [h1, h2, h3]
        exact (Real.exp_le_exp.mpr h35).trans (le_of_eq (Real.exp_log (by norm_num)))
      have h1 : (log 4 + log (k : ℝ) + log (log (k : ℝ))) * exp 0.35 ≤ 2 * log (k : ℝ) + 2.4 := by
        have hsum_ub : log 4 + log (k : ℝ) + log (log (k : ℝ)) ≤ 1.25 * log (k : ℝ) + 1.8 := by
          linarith only [hlog4, hllk]
        have hmul : (log 4 + log (k : ℝ) + log (log (k : ℝ))) * exp 0.35 ≤ (1.25 * log (k : ℝ) + 1.8) * 1.43 :=
          mul_le_mul hsum_ub hexp35 (by positivity) (by linarith only [hlogk_lb])
        linarith only [hmul, hlogk_lb]
      have h2 := Real.log_le_log (mul_pos hlogsum_pos (by positivity)) h1
      rw [Real.log_mul hlogsum_pos.ne' (by positivity), Real.log_exp] at h2
      linarith only [h2]
    have hllN_pos : 0 < log (log (N : ℝ)) := by
      have : 1 < 2 * log (k : ℝ) + 2.4 := by linarith
      exact Real.log_pos (by linarith)
    have hllM_235 : 2.34 ≤ log (log (M : ℝ)) := by
      have h1 := exp_div_100_lt_of_gt (B := 105) (wt := 465) (by norm_num) (by norm_num)
      have h2 := exp_div_100_gt_of_lt (B := 10) (wt := 231) (by norm_num) (by norm_num)
      have h3 : log (10.5 : ℝ) = log 105 - log 10 := by
        rw [show (10.5 : ℝ) = 105 / 10 by norm_num, Real.log_div (by norm_num) (by norm_num)]
      have h4 : 2.34 < log (10.5 : ℝ) := by norm_num at h1 h2; linarith only [h1, h2, h3]
      exact (by linarith only [h4] : (2.34 : ℝ) ≤ log (10.5 : ℝ)).trans (Real.log_le_log (by norm_num) hlogM_lb)
    split_ifs at hD_lb
    · linarith only [hD_lb, hllM_ub, hll_le, hllN_gt, hllN_pos, hllM_235]
    · have hllM_pos : 0 < log (log (M : ℝ)) := Real.log_pos (by linarith only [hlogM_lb])
      linarith only [hD_lb, hllM_ub, hll_le, hllN_gt, hllN_pos, hllM_pos]
  have hub := R_upper_bound (by omega) (hkM.trans hMa) (sub_pos.mp hD_pos)
  have hnum : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : k - 1 ≤ k)
  obtain ⟨D, hD_def⟩ : ∃ D : ℝ, D = sumX a - sumX (k - 2) := ⟨_, rfl⟩
  rw [← hD_def] at hub hD_lb hD_pos
  have hdiv : (k : ℝ) / D < 2 * (y : ℝ) + 2 := by
    rw [div_lt_iff₀ hD_pos]
    by_cases hk95 : k < 95000
    · have hyR : 0.86 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5) < (y : ℝ) + 1 := by
        rw [hy_def, if_pos hk95]; exact Nat.lt_floor_add_one _
      have h2y : 1.72 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5) < 2 * (y : ℝ) + 2 := by
        have hmul : 1.72 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5) =
            2 * (0.86 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5)) := by ring
        linarith only [hyR, hmul]
      have hD_big : 0.90 * log (k : ℝ) - 2.5 < 1.72 * D := by
        have h074 : 0.74 * (y : ℝ) ≤ log (N : ℝ) := by
          have hy12 := hy_lt (by omega)
          linarith [(theta_105_and_070_small (by omega) hy12).1]
        have hklt : log (k : ℝ) < 11.5 := by
          have hk95k : (k : ℝ) < 95000 := by exact_mod_cast hk95
          have h1 := exp_div_100_gt_of_lt (B := 95000) (wt := 1150) (by norm_num) (by norm_num)
          norm_num at h1
          exact (Real.log_lt_log (by positivity) hk95k).trans (by linarith only [h1])
        have h063 : 0.63 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5) ≤ log (N : ℝ) := by
          have hyR' : 0.86 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5) - 1 < (y : ℝ) := by
            rw [hy_def, if_pos hk95]; exact Nat.sub_one_lt_floor _
          have h1 : 0.74 * (y : ℝ) ≥ 0.74 * (0.855 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5)) := by
            have hbig : 1 < 0.005 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5) := by
              have hlog1500 : log (1500 : ℝ) < 7.32 := by
                have h := exp_div_100_gt_of_lt (B := 1500) (wt := 732) (by norm_num) (by norm_num)
                norm_num at h; linarith only [h]
              have hlogk_ub : log (k : ℝ) ≤ (k : ℝ) / 1500 - 1 + log (1500 : ℝ) := by
                have h := Real.log_le_sub_one_of_pos (show 0 < (k : ℝ) / 1500 by positivity)
                rw [Real.log_div (by positivity) (by norm_num)] at h
                linarith only [h]
              rw [lt_div_iff₀ hden_pos]
              linarith only [hkR, hlog1500, hlogk_ub]
            have hsub : 0.855 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5) =
                0.86 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5) -
                0.005 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5) := by ring
            linarith only [hyR', hbig, hsub]
          have hmul63 : 0.63 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5) ≤
              0.74 * (0.855 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5)) := by
            have hpos : 0 ≤ (k : ℝ) / (0.90 * log (k : ℝ) - 2.5) := div_nonneg (by positivity) hden_pos.le
            have hring1 : 0.63 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5) =
                0.63 * ((k : ℝ) / (0.90 * log (k : ℝ) - 2.5)) := by ring
            have hring2 : 0.74 * (0.855 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5)) =
                0.6327 * ((k : ℝ) / (0.90 * log (k : ℝ) - 2.5)) := by ring
            linarith only [hpos, hring1, hring2]
          linarith only [h074, h1, hmul63]
        have hllN : log (0.63 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5)) ≤ log (log (N : ℝ)) :=
          Real.log_le_log (div_pos (by positivity) hden_pos) h063
        have hllN' : log (0.63 * (k : ℝ)) - log (0.90 * log (k : ℝ) - 2.5) ≤ log (log (N : ℝ)) := by
          rwa [Real.log_div (by positivity) hden_pos.ne'] at hllN
        have hlog063 : -0.47 ≤ log (0.63 : ℝ) := by
          have h1 := exp_div_100_lt_of_gt (B := 63) (wt := 414) (by norm_num) (by norm_num)
          have h2 := exp_div_100_gt_of_lt (B := 100) (wt := 461) (by norm_num) (by norm_num)
          have h3 : log (0.63 : ℝ) = log 63 - log 100 := by
            rw [show (0.63 : ℝ) = 63 / 100 by norm_num, Real.log_div (by norm_num) (by norm_num)]
          norm_num at h1 h2; linarith
        have hlog10_gt : 2.3 < log (10 : ℝ) := by
          have h := exp_div_100_lt_of_gt (B := 10) (wt := 230) (by norm_num) (by norm_num)
          norm_num at h; linarith only [h]
        have hlog100_gt : 4.6 < log (100 : ℝ) := by
          have h := exp_div_100_lt_of_gt (B := 100) (wt := 460) (by norm_num) (by norm_num)
          norm_num at h; linarith only [h]
        have hD_lb' : 0.90 * log (log (N : ℝ)) - 0.80 * log (log (M : ℝ)) - 0.52 ≤ D := by
          have hM_lt10m : M < 10000000 := by
            have hM_le_klogk : (M : ℝ) ≤ 4 * (k : ℝ) * log (k : ℝ) := by
              rw [hM_def]; exact Nat.floor_le (by positivity)
            have hk95R : (k : ℝ) ≤ 95000 := by exact_mod_cast hk95.le
            have hlt : (M : ℝ) < 10000000 := by nlinarith only [hM_le_klogk, hk95R, hklt]
            exact Nat.cast_lt.mp hlt
          rwa [if_pos hM_lt10m] at hD_lb
        have hden_lin : log (0.90 * log (k : ℝ) - 2.5) ≤ 1.41 + 0.222 * (log (k : ℝ) - 7.3) := by
          have h1 : log ((0.90 * log (k : ℝ) - 2.5) / 4.07) ≤ (0.90 * log (k : ℝ) - 2.5) / 4.07 - 1 :=
            Real.log_le_sub_one_of_pos (by positivity)
          rw [Real.log_div hden_pos.ne' (by norm_num)] at h1
          have hlog407 : log (4.07 : ℝ) ≤ 1.41 := by
            have h3 := exp_div_100_gt_of_lt (B := 407) (wt := 601) (by norm_num) (by norm_num)
            have h4 : log (4.07 : ℝ) = log 407 - log 100 := by
              rw [show (4.07 : ℝ) = 407 / 100 by norm_num, Real.log_div (by norm_num) (by norm_num)]
            norm_num at h3; linarith only [h3, h4, hlog100_gt]
          have h407 : (0.90 * log (k : ℝ) - 2.5) / 4.07 - 1 = (90 / 407 : ℝ) * (log (k : ℝ) - 7.3) := by ring
          linarith only [h1, h407, hlog407, hlogk_lb]
        have hllM_lin : log (log (M : ℝ)) ≤ 2.42 + 0.09 * (log (k : ℝ) - 7.3) := by
          have hlog4 : log (4 : ℝ) < 1.4 := by
            rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
            linarith [lt_trans Real.log_two_lt_d9 (by norm_num : (0.6931471808 : ℝ) < 0.7)]
          have hllk : log (log (k : ℝ)) < 2.5 := by
            have h1 := exp_div_100_gt_of_lt (B := 115) (wt := 480) (by norm_num) (by norm_num)
            have h2 : log (11.5 : ℝ) = log 115 - log 10 := by
              rw [show (11.5 : ℝ) = 115 / 10 by norm_num, Real.log_div (by norm_num) (by norm_num)]
            have h3 := Real.log_lt_log (by linarith only [hlogk_lb]) hklt
            norm_num at h1; linarith only [h1, h2, h3, hlog10_gt]
          have hM_le : log (M : ℝ) ≤ log (k : ℝ) + 3.9 := by linarith only [hlogM_ub, hlog4, hllk]
          have h1 : log ((log (M : ℝ)) / 11.2) ≤ (log (M : ℝ)) / 11.2 - 1 :=
            Real.log_le_sub_one_of_pos (by positivity)
          rw [Real.log_div hlogM_pos.ne' (by norm_num)] at h1
          have hlog112 : log (11.2 : ℝ) ≤ 2.42 := by
            have h3 := exp_div_100_gt_of_lt (B := 112) (wt := 472) (by norm_num) (by norm_num)
            have h4 : log (11.2 : ℝ) = log 112 - log 10 := by
              rw [show (11.2 : ℝ) = 112 / 10 by norm_num, Real.log_div (by norm_num) (by norm_num)]
            norm_num at h3; linarith only [h3, h4, hlog10_gt]
          have h1' : log (M : ℝ) / 11.2 - 1 ≤ (log (k : ℝ) + 3.9) / 11.2 - 1 :=
            sub_le_sub_right (div_le_div_of_nonneg_right hM_le (by norm_num)) 1
          have h112 : (log (k : ℝ) + 3.9) / 11.2 - 1 = (10 / 112 : ℝ) * (log (k : ℝ) - 7.3) := by ring
          linarith only [h1, h1', h112, hlog112, hlogk_lb]
        have hllN_final : 0.90 * (log (k : ℝ) - 0.47 - (1.41 + 0.222 * (log (k : ℝ) - 7.3))) ≤
            0.90 * log (log (N : ℝ)) := by
          have hmul := Real.log_mul (by norm_num : (0.63 : ℝ) ≠ 0) (by positivity : (k : ℝ) ≠ 0)
          linarith only [hllN', hmul, hlog063, hden_lin]
        linarith only [hD_lb', hllN_final, hllM_lin, hlogk_lb]
      have hmul : (k : ℝ) < D * (1.72 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5)) := by
        rw [mul_div_assoc', lt_div_iff₀ hden_pos]
        nlinarith only [hkR, hD_big]
      rw [mul_comm]
      exact lt_trans hmul (by gcongr)
    · have hk95' : 95000 ≤ k := by omega
      have hyR : 0.76 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5) < (y : ℝ) + 1 := by
        rw [hy_def, if_neg hk95]; exact Nat.lt_floor_add_one _
      have h2y : 1.52 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5) < 2 * (y : ℝ) + 2 := by
        have hmul : 1.52 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5) =
            2 * (0.76 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5)) := by ring
        linarith only [hyR, hmul]
      have hD_big : 0.90 * log (k : ℝ) - 2.5 < 1.52 * D := by
        have hyR' : 0.76 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5) - 1 < (y : ℝ) := by
          rw [hy_def, if_neg hk95]; exact Nat.sub_one_lt_floor _
        exact large_k_y1_D_big_ge95k (a := a) hk95' hden_pos hlogk_lb hlogN_ge hlogM_ub hlogM_lb hlogM_pos hyR' hD_lb
      have hmul : (k : ℝ) < D * (1.52 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5)) := by
        rw [mul_div_assoc', lt_div_iff₀ hden_pos]
        nlinarith only [hkR, hD_big]
      rw [mul_comm]
      exact lt_trans hmul (by gcongr)
  rw [← hy_def]
  refine ⟨by omega, by linarith, a, N, hN10m, haN, hNa1, hgap, hlogN_lb, hlogN_ub, hkM.trans hMa, ?_⟩
  have hnum1 : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : k - 1 ≤ k)
  have hdiv1 : ((k - 1 : ℕ) : ℝ) / D ≤ (k : ℝ) / D := div_le_div_of_nonneg_right hnum1 hD_pos.le
  linarith only [hub, hdiv1, hdiv, hgap]


private lemma large_k_D'_pos {k y0 a' N' M : ℕ}
    (hM40k : 40000 ≤ M) (hN'10m : 10000000 ≤ N') (hkM : k - 1 ≤ Nat.primeCounting M)
    (hMa' : Nat.primeCounting M ≤ a') (ha'N' : pNth a' < N') (hN'a1' : N' < pNth (a' + 1))
    (hlogk_lb : 7.3 < log (k : ℝ))
    (hy'_200 : 200 ≤ y0 - 1) (hy'_lb : 2 * log (k : ℝ) + 2.4 < 0.70 * ((y0 - 1 : ℕ) : ℝ))
    (hlogN'_lb : Chebyshev.theta ((y0 - 1 : ℕ) : ℝ) ≤ log (N' : ℝ))
    (hlogM_ub : log (M : ℝ) ≤ log 4 + log (k : ℝ) + log (log (k : ℝ)))
    (hlogM_lb : 10.5 ≤ log (M : ℝ)) :
    0 < sumX a' - sumX (k - 2) := by
  have hD'_lb := large_k_D_lb hM40k hN'10m hkM hMa' ha'N' hN'a1' hlogM_lb
  have hlogN'_gt : 2 * log (k : ℝ) + 2.4 < log (N' : ℝ) := by
    have ht : 0.70 * ((y0 - 1 : ℕ) : ℝ) ≤ Chebyshev.theta ((y0 - 1 : ℕ) : ℝ) := theta_ge_070 hy'_200
    linarith only [ht, hy'_lb, hlogN'_lb]
  have hllN' : log (2 * log (k : ℝ) + 2.4) < log (log (N' : ℝ)) :=
    Real.log_lt_log (by linarith only [hlogk_lb]) hlogN'_gt
  have hlog4 : log (4 : ℝ) < 1.4 := by
    have h2 : log (2 : ℝ) < 0.7 := lt_trans Real.log_two_lt_d9 (by norm_num)
    have h4 : log (4 : ℝ) = 2 * log (2 : ℝ) := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
    linarith only [h2, h4]
  have hllk : log (log (k : ℝ)) ≤ log (k : ℝ) / 4 + 0.4 := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < log (k : ℝ) / 4 by linarith only [hlogk_lb])
    rw [Real.log_div (by linarith only [hlogk_lb]) (by norm_num)] at h1
    linarith only [h1, hlog4]
  have hllM' : log (log (M : ℝ)) ≤ log (2 * log (k : ℝ) + 2.4) - 0.35 := by
    have hlogsum_pos : 0 < log 4 + log (k : ℝ) + log (log (k : ℝ)) := by
      have : 0 < log (4 : ℝ) := Real.log_pos (by norm_num)
      have : 0 < log (log (k : ℝ)) := Real.log_pos (by linarith only [hlogk_lb])
      linarith only [‹0 < log (4 : ℝ)›, hlogk_lb, ‹0 < log (log (k : ℝ))›]
    have hexp35 : exp (0.35 : ℝ) ≤ 1.43 := by
      have h1 := exp_div_100_lt_of_gt (B := 143) (wt := 496) (by norm_num) (by norm_num)
      have h2 := exp_div_100_gt_of_lt (B := 100) (wt := 461) (by norm_num) (by norm_num)
      have h3 : log (1.43 : ℝ) = log 143 - log 100 := by
        rw [show (1.43 : ℝ) = 143 / 100 by norm_num, Real.log_div (by norm_num) (by norm_num)]
      have h35 : (0.35 : ℝ) ≤ log (1.43 : ℝ) := by norm_num at h1 h2; linarith only [h1, h2, h3]
      exact (Real.exp_le_exp.mpr h35).trans (le_of_eq (Real.exp_log (by norm_num)))
    have h1 : (log 4 + log (k : ℝ) + log (log (k : ℝ))) * exp 0.35 ≤ 2 * log (k : ℝ) + 2.4 := by
      have hsum_ub : log 4 + log (k : ℝ) + log (log (k : ℝ)) ≤ 1.25 * log (k : ℝ) + 1.8 := by
        linarith only [hlog4, hllk]
      have hmul : (log 4 + log (k : ℝ) + log (log (k : ℝ))) * exp 0.35 ≤ (1.25 * log (k : ℝ) + 1.8) * 1.43 :=
        mul_le_mul hsum_ub hexp35 (by positivity) (by linarith only [hlogk_lb])
      linarith only [hmul, hlogk_lb]
    have h2 := Real.log_le_log (mul_pos hlogsum_pos (by positivity)) h1
    rw [Real.log_mul hlogsum_pos.ne' (by positivity), Real.log_exp] at h2
    have h3 := Real.log_le_log (by linarith only [hlogM_lb]) hlogM_ub
    linarith only [h2, h3]
  have hll_pos : 0 < log (log (N' : ℝ)) := by
    have : 1 < 2 * log (k : ℝ) + 2.4 := by linarith only [hlogk_lb]
    exact Real.log_pos (by linarith only [‹1 < 2 * log (k : ℝ) + 2.4›, hlogN'_gt])
  have hllM_234 : 2.34 ≤ log (log (M : ℝ)) :=
    lk_log105_ge.trans (Real.log_le_log (by norm_num) hlogM_lb)
  split_ifs at hD'_lb
  · linarith only [hD'_lb, hllN', hllM', hll_pos, hllM_234]
  · have hllM_pos : 0 < log (log (M : ℝ)) := Real.log_pos (by linarith only [hlogM_lb])
    linarith only [hD'_lb, hllN', hllM', hll_pos, hllM_pos]

private lemma lk_convex (α β γ δ L y U : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hδ : 0 < δ)
    (hL : 0 < L) (hLy : L ≤ y) (hyU : y ≤ U) :
    α * γ * y + β * δ / y ≤ max (α * γ * L + β * δ / L) (α * γ * U + β * δ / U) := by
  by_cases hcmp : y * U ≤ β * δ / (α * γ)
  · have hy_pos : 0 < y := by linarith only [hL, hLy]
    have h1 : y * L ≤ β * δ / (α * γ) := by nlinarith only [hcmp, hLy, hyU, hL, hy_pos]
    have h1' : (α * γ) * (y * L) ≤ β * δ := by
      nlinarith only [(le_div_iff₀ (mul_pos hα hγ)).mp h1]
    have h2 : α * γ ≤ β * δ / (y * L) := (le_div_iff₀ (mul_pos hy_pos hL)).mpr h1'
    have h3 : α * γ * (y - L) ≤ β * δ / (y * L) * (y - L) :=
      mul_le_mul_of_nonneg_right h2 (by linarith only [hLy])
    have h4 : β * δ / L - β * δ / y = β * δ / (y * L) * (y - L) := by
      field_simp [hL.ne', hy_pos.ne']
    have h5 : α * γ * y + β * δ / y ≤ α * γ * L + β * δ / L := by linarith only [h3, h4]
    exact h5.trans (le_max_left _ _)
  · push Not at hcmp
    have hy_pos : 0 < y := by linarith only [hL, hLy]
    have hU_pos : 0 < U := by linarith only [hy_pos, hyU]
    have h1' : β * δ < (α * γ) * (y * U) := by
      nlinarith only [(div_lt_iff₀ (mul_pos hα hγ)).mp hcmp]
    have h2 : β * δ / (y * U) < α * γ := (div_lt_iff₀ (mul_pos hy_pos hU_pos)).mpr h1'
    have h3 : α * γ * (U - y) ≥ β * δ / (y * U) * (U - y) :=
      mul_le_mul_of_nonneg_right h2.le (by linarith only [hyU])
    have h4 : β * δ / y - β * δ / U = β * δ / (y * U) * (U - y) := by
      field_simp [hy_pos.ne', hU_pos.ne']
    have h5 : α * γ * y + β * δ / y ≤ α * γ * U + β * δ / U := by linarith only [h3, h4]
    exact h5.trans (le_max_right _ _)

private lemma large_k_Sa_a' {a a' N N' M : ℕ}
    (hM40k : 40000 ≤ M) (hMa' : Nat.primeCounting M ≤ a')
    (hN'10m : 10000000 ≤ N') (haN : pNth a < N) (hN'a1' : N' < pNth (a' + 1)) :
    sumX a - sumX a' ≤
      (if a ≤ a' then (0 : ℝ)
       else 1.109 * (log (log (N : ℝ)) - log (log (N' : ℝ)) + 1 / log (N' : ℝ)) + 0.0001) := by
  split_ifs with haa'
  · have h1 : sumX a ≤ sumX a' := by
      unfold sumX
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono haa') (fun _ _ _ => xTerm_nonneg _)
    linarith only [h1]
  · have ha'a : a' < a := by omega
    have hsub_eq : sumX a - sumX a' = ∑ j ∈ Finset.Ico a' a, xTerm j := by
      unfold sumX; rw [← Finset.sum_range_add_sum_Ico _ ha'a.le]; ring
    rw [hsub_eq, Finset.sum_eq_sum_Ico_succ_bot ha'a]
    have hpa'_40k : 40000 ≤ pNth a' := by
      have hpi : M < pNth (Nat.primeCounting M) := primeCounting_le_iff_pNth_gt.mp (le_refl _)
      exact (by omega : 40000 ≤ M).trans (hpi.le.trans (pNth_strictMono.monotone hMa'))
    have hxa' : xTerm a' ≤ 1 / 39999 := by
      unfold xTerm
      have hpa'R : (40000 : ℝ) ≤ (pNth a' : ℝ) := by exact_mod_cast hpa'_40k
      exact div_le_div_of_nonneg_left zero_le_one (by norm_num) (by linarith)
    have hN'_le_N : N' ≤ N := by
      have h1 : N' < pNth (a' + 1) := hN'a1'
      have h2 : pNth (a' + 1) ≤ pNth a := pNth_strictMono.monotone (by omega : a' + 1 ≤ a)
      omega
    have hIco_le : ∑ j ∈ Finset.Ico (a' + 1) a, xTerm j ≤
        1.000001 * ∑ p ∈ Nat.primesLE N \ Nat.primesLE N', (1 : ℝ) / (p : ℝ) := by
      have hterm : ∀ j ∈ Finset.Ico (a' + 1) a, xTerm j ≤ 1.000001 * ((1 : ℝ) / (pNth j : ℝ)) := by
        intro j hj
        rw [Finset.mem_Ico] at hj
        have hj_gt : N' < pNth j := hN'a1'.trans_le (pNth_strictMono.monotone hj.1)
        have hpR : (10000001 : ℝ) ≤ (pNth j : ℝ) := by exact_mod_cast (by omega : 10000001 ≤ pNth j)
        unfold xTerm
        rw [mul_one_div, div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith only [hpR]
      have hsum1 : ∑ j ∈ Finset.Ico (a' + 1) a, xTerm j ≤
          1.000001 * ∑ j ∈ Finset.Ico (a' + 1) a, (1 : ℝ) / (pNth j : ℝ) := by
        rw [Finset.mul_sum]; exact Finset.sum_le_sum hterm
      have hsub : (Finset.Ico (a' + 1) a).image pNth ⊆ Nat.primesLE N \ Nat.primesLE N' := by
        intro p hp
        rw [Finset.mem_image] at hp; rcases hp with ⟨j, hj, rfl⟩
        rw [Finset.mem_Ico] at hj
        have hj_gt : N' < pNth j := hN'a1'.trans_le (pNth_strictMono.monotone hj.1)
        have hj_lt : pNth j ≤ N := (pNth_strictMono.monotone hj.2.le).trans haN.le
        rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE]
        exact ⟨⟨hj_lt, Nat.nth_mem_of_infinite Nat.infinite_setOf_prime j⟩, fun h => by omega⟩
      have hsum2 : ∑ j ∈ Finset.Ico (a' + 1) a, (1 : ℝ) / (pNth j : ℝ) ≤
          ∑ p ∈ Nat.primesLE N \ Nat.primesLE N', (1 : ℝ) / (p : ℝ) := by
        calc ∑ j ∈ Finset.Ico (a' + 1) a, (1 : ℝ) / (pNth j : ℝ)
            = ∑ p ∈ (Finset.Ico (a' + 1) a).image pNth, (1 : ℝ) / (p : ℝ) := by
              rw [Finset.sum_image]; intro i _ j _ hij; exact pNth_strictMono.injective hij
          _ ≤ ∑ p ∈ Nat.primesLE N \ Nat.primesLE N', (1 : ℝ) / (p : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      linarith [mul_le_mul_of_nonneg_left hsum2 (by norm_num : (0 : ℝ) ≤ 1.000001)]
    have hub := sum_inv_primes_ub (M := N') (N := N) (c := 1.108) (by norm_num) (by omega) hN'_le_N
      (fun n hn => theta_le_1108 (by have := (Finset.mem_Ico.mp hn).1; omega))
    have hsum_pos : 0 ≤ ∑ p ∈ Nat.primesLE N \ Nat.primesLE N', (1 : ℝ) / (p : ℝ) :=
      Finset.sum_nonneg (fun _ _ => by positivity)
    have h1109_ub : 1.000001 * ∑ p ∈ Nat.primesLE N \ Nat.primesLE N', (1 : ℝ) / (p : ℝ) ≤
        1.109 * (log (log (N : ℝ)) - log (log (N' : ℝ)) + 1 / log (N' : ℝ)) := by
      have h1 : 1.000001 * (1.108 * (log (log (N : ℝ)) - log (log (N' : ℝ)) + 1 / log (N' : ℝ))) ≤
          1.109 * (log (log (N : ℝ)) - log (log (N' : ℝ)) + 1 / log (N' : ℝ)) := by
        have hll_nn : 0 ≤ log (log (N : ℝ)) - log (log (N' : ℝ)) + 1 / log (N' : ℝ) := by
          have h1' : log (N' : ℝ) ≤ log (N : ℝ) :=
            Real.log_le_log (by exact_mod_cast (by omega : 0 < N')) (by exact_mod_cast hN'_le_N)
          have hlogN'_pos : 0 < log (N' : ℝ) := by
            have h10m : (10000000 : ℝ) ≤ (N' : ℝ) := by exact_mod_cast hN'10m
            have h16 : (16 : ℝ) ≤ log (10000000 : ℝ) := by
              have h := exp_div_100_lt_of_gt (B := 10000000) (wt := 1600) (by norm_num) (by norm_num)
              norm_num at h; linarith only [h]
            linarith [h16.trans (Real.log_le_log (by norm_num) h10m)]
          have h2' : log (log (N' : ℝ)) ≤ log (log (N : ℝ)) := Real.log_le_log hlogN'_pos h1'
          positivity
        nlinarith only [hll_nn]
      linarith [mul_le_mul_of_nonneg_left hub (by norm_num : (0 : ℝ) ≤ 1.000001), h1]
    linarith only [hxa', hIco_le, h1109_ub]

private lemma large_k_sa_ub {y0 a a' N N' : ℕ}
    (hy0_200 : 200 ≤ y0) (hy'_200 : 200 ≤ y0 - 1) (hy0_gt : 201 ≤ y0)
    (hlogN_ge_140 : 140 ≤ log (N : ℝ))
    (hlogN_ub : log (N : ℝ) ≤ Chebyshev.theta (y0 : ℝ) + log ((1001 * y0 ^ 2 : ℕ) : ℝ))
    (hlogN'_lb : Chebyshev.theta ((y0 - 1 : ℕ) : ℝ) ≤ log (N' : ℝ)) :
    (if a ≤ a' then (0 : ℝ)
     else 1.109 * (log (log (N : ℝ)) - log (log (N' : ℝ)) + 1 / log (N' : ℝ)) + 0.0001) ≤ 0.20 := by
  have hy0_R : (201 : ℝ) ≤ (y0 : ℝ) := by exact_mod_cast hy0_gt
  have hlog1001 : log (1001 : ℝ) ≤ 6.91 := lk_log1001_le
  have hlogN'_ge : 0.72 * ((y0 - 1 : ℕ) : ℝ) ≤ log (N' : ℝ) := by
    have ht : 0.72 * ((y0 - 1 : ℕ) : ℝ) ≤ Chebyshev.theta ((y0 - 1 : ℕ) : ℝ) := by
      by_cases hy12 : y0 - 1 < 12000
      · linarith [(theta_105_and_070_small hy'_200 hy12).1]
      · exact theta_ge_072_10k (by omega)
    linarith only [ht, hlogN'_lb]
  have hy'_R : (200 : ℝ) ≤ ((y0 - 1 : ℕ) : ℝ) := by exact_mod_cast hy'_200
  have hlogN'_144 : 144 ≤ log (N' : ℝ) := by linarith only [hlogN'_ge, hy'_R]
  have hinvN' : 1 / log (N' : ℝ) ≤ 1 / 144 :=
    div_le_div_of_nonneg_left zero_le_one (by norm_num) hlogN'_144
  split_ifs with haa'
  · norm_num
  · have hth_diff : Chebyshev.theta (y0 : ℝ) - Chebyshev.theta ((y0 - 1 : ℕ) : ℝ) ≤ log (y0 : ℝ) := by
      have h1 := theta_diff_eq (y0 - 1) (by omega)
      have hy_eq : ((y0 - 1 + 1 : ℕ) : ℝ) = (y0 : ℝ) := by exact_mod_cast (by omega : y0 - 1 + 1 = y0)
      rw [hy_eq] at h1
      rw [h1]
      split_ifs
      · exact le_refl _
      · exact Real.log_nonneg (by linarith only [hy0_R])
    have hlogN_diff : log (N : ℝ) - log (N' : ℝ) ≤ log 1001 + 3 * log (y0 : ℝ) := by
      have h2 : log ((1001 * y0 ^ 2 : ℕ) : ℝ) = log 1001 + 2 * log (y0 : ℝ) := by
        push_cast; rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; ring
      linarith only [hlogN_ub, hlogN'_lb, hth_diff, h2]
    have hlogy0_ub : log (y0 : ℝ) ≤ log 201 + (y0 : ℝ) / 201 - 1 := by
      have h := Real.log_le_sub_one_of_pos (show 0 < (y0 : ℝ) / 201 by positivity)
      rw [Real.log_div (by positivity) (by norm_num)] at h
      linarith only [h]
    have hdiff_y0 : log (N : ℝ) - log (N' : ℝ) ≤ 0.114 * (y0 : ℝ) := by
      linarith only [hlogN_diff, hlog1001, hlogy0_ub, lk_log201_le, hy0_R]
    have hN'_y0 : 0.716 * (y0 : ℝ) ≤ log (N' : ℝ) := by
      have hy_cast : ((y0 - 1 : ℕ) : ℝ) = (y0 : ℝ) - 1 := by exact_mod_cast Nat.cast_sub (by omega : 1 ≤ y0)
      linarith only [hlogN'_ge, hy_cast, hy0_R]
    have hll_diff : log (log (N : ℝ)) - log (log (N' : ℝ)) ≤ 0.16 := by
      have hNpos : 0 < log (N : ℝ) := by linarith only [hlogN_ge_140]
      have hN'pos : 0 < log (N' : ℝ) := by linarith only [hlogN'_144]
      rw [← Real.log_div hNpos.ne' hN'pos.ne']
      have h1 : log (log (N : ℝ) / log (N' : ℝ)) ≤ log (N : ℝ) / log (N' : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hNpos hN'pos)
      have h2 : log (N : ℝ) / log (N' : ℝ) - 1 ≤ 0.16 := by
        rw [sub_le_iff_le_add, div_le_iff₀ hN'pos]
        linarith only [hdiff_y0, hN'_y0]
      exact h1.trans h2
    linarith only [hll_diff, hinvN']

private lemma lk_logk_le_0001k {k : ℕ} (hk110 : 110000 ≤ k) :
    log (k : ℝ) ≤ 0.001 * (k : ℝ) := by
  have hk110R : (110000 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk110
  have h1 : log (k : ℝ) ≤ 4 * ((k : ℝ) ^ (1 / 4 : ℝ)) := by
    have h := Real.log_le_rpow_div (x := (k : ℝ)) (ε := (1 / 4 : ℝ)) (by positivity) (by norm_num)
    linarith only [h]
  have h2 : (18 : ℝ) ≤ (k : ℝ) ^ (1 / 4 : ℝ) := by
    have hk18 : (18 : ℝ) ^ (4 : ℕ) ≤ (k : ℝ) := by linarith only [hk110R]
    have hpow := Real.rpow_le_rpow (by positivity) hk18 (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rwa [← Real.rpow_natCast (18 : ℝ) 4, ← Real.rpow_mul (by norm_num),
         show ((4 : ℕ) : ℝ) * (1 / 4 : ℝ) = 1 by norm_num, Real.rpow_one] at hpow
  have h3 : (k : ℝ) ^ (1 / 4 : ℝ) * (k : ℝ) ^ (3 / 4 : ℝ) = (k : ℝ) := by
    rw [← Real.rpow_add (by positivity)]; norm_num
  have h4 : (18 : ℝ) ^ 3 ≤ (k : ℝ) ^ (3 / 4 : ℝ) := by
    have h5 : (18 : ℝ) ^ 3 = ((18 : ℝ)) ^ (3 : ℝ) := by norm_num
    rw [h5, show (3 / 4 : ℝ) = (1 / 4 : ℝ) * 3 by norm_num, Real.rpow_mul (by positivity)]
    exact Real.rpow_le_rpow (by norm_num) h2 (by norm_num)
  nlinarith only [h1, h3, h4, hk110R]

private lemma large_k_caseB_lt12k {k y0 y1 a a' N N' M b : ℕ}
    (hk1500 : 1500 < k) (hy0_gt : 201 ≤ y0) (hy0_le_y1 : y0 ≤ y1) (hy12 : y0 < 12000)
    (hy1_def : y1 = (if k < 95000 then ⌊0.86 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5)⌋₊
                     else ⌊0.76 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5)⌋₊))
    (hlogk_lb : 7.3 < log (k : ℝ)) (hden_pos : 0 < 0.90 * log (k : ℝ) - 2.5)
    (hlogM_ub : log (M : ℝ) ≤ log 4 + log (k : ℝ) + log (log (k : ℝ)))
    (hlogM_lb : 10.5 ≤ log (M : ℝ))
    (h100N_ub : log ((100 * N : ℕ) : ℝ) ≤
      (if y0 < 12000 then 1.05 * (y0 : ℝ) else 1.26 * (y0 : ℝ)) + log 100 + log 1001 + 2 * log (y0 : ℝ))
    (hS_nn : 0 ≤ sumX b - sumX 61)
    (hsum_b61 : sumX b - sumX 61 ≤ 0.045 +
      (if a ≤ a' then (0 : ℝ)
       else 1.109 * (log (log (N : ℝ)) - log (log (N' : ℝ)) + 1 / log (N' : ℝ)) + 0.0001) +
      ((k : ℝ) - 1) / (2 * (y0 : ℝ)) +
      (1.05 * (log (log 12000) - log (log 290)) + 1.26 * (log (log (M : ℝ)) - log (log 12000)) + 0.085))
    (hsa_ub : (if a ≤ a' then (0 : ℝ)
       else 1.109 * (log (log (N : ℝ)) - log (log (N' : ℝ)) + 1 / log (N' : ℝ)) + 0.0001) ≤ 0.20) :
    (1.116 * log ((100 * N : ℕ) : ℝ) + 1) * (sumX b - sumX 61) < (k : ℝ) - 62 := by
  have hkR : (1501 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1501 ≤ k)
  have hy0_R : (201 : ℝ) ≤ (y0 : ℝ) := by exact_mod_cast hy0_gt
  have hlog100 : log (100 : ℝ) ≤ 4.61 := lk_log100_lt.le
  have hlog1001 : log (1001 : ℝ) ≤ 6.91 := lk_log1001_le
  rw [if_pos hy12] at h100N_ub
  have hlog4 : log (4 : ℝ) < 1.4 := by
    have h2 : log (2 : ℝ) < 0.7 := lt_trans Real.log_two_lt_d9 (by norm_num)
    have h4 : log (4 : ℝ) = 2 * log (2 : ℝ) := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
    linarith only [h2, h4]
  have hU_ub : (y1 : ℝ) ≤ 0.86 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5) := by
    by_cases hk95 : k < 95000
    · have h1 : y1 ≤ ⌊0.86 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5)⌋₊ := by rw [hy1_def, if_pos hk95]
      exact (by exact_mod_cast h1 : (y1 : ℝ) ≤ _).trans (Nat.floor_le (by positivity))
    · have h1 : y1 ≤ ⌊0.76 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5)⌋₊ := by rw [hy1_def, if_neg hk95]
      have h2 := (by exact_mod_cast h1 : (y1 : ℝ) ≤ _).trans (Nat.floor_le (by positivity))
      exact h2.trans (div_le_div_of_nonneg_right (by linarith only [hkR]) hden_pos.le)
  have hA_ub : 0.045 + (if a ≤ a' then (0 : ℝ)
     else 1.109 * (log (log (N : ℝ)) - log (log (N' : ℝ)) + 1 / log (N' : ℝ)) + 0.0001) +
    (1.05 * (log (log 12000) - log (log 290)) + 1.26 * (log (log (M : ℝ)) - log (log 12000)) + 0.085) ≤
      1.26 * log (log (M : ℝ)) - 1.93 := by
    linarith only [hsa_ub, lk_ll290_ge, lk_ll12k_ge, lk_ll12k_le]
  have hA_pos : 0 < 1.26 * log (log (M : ℝ)) - 1.93 := by
    have h2 : 2.34 ≤ log (log (M : ℝ)) := lk_log105_ge.trans (Real.log_le_log (by norm_num) hlogM_lb)
    linarith only [h2]
  have hk_half_pos : 0 < ((k : ℝ) - 1) / 2 := by linarith only [hkR]
  by_cases hk3k : k < 3000
  · have hk3R : (k : ℝ) ≤ 3000 := by exact_mod_cast hk3k.le
    have hy1_650 : (y1 : ℝ) ≤ 650 := by
      have h2 : 4.07 ≤ 0.90 * log (k : ℝ) - 2.5 := by linarith only [hlogk_lb]
      have h3 : 0.86 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5) ≤ 0.86 * 3000 / 4.07 :=
        div_le_div₀ (by positivity) (by linarith only [hk3R]) (by norm_num) h2
      linarith only [hU_ub, h3]
    have hlogy0_65 : log (y0 : ℝ) ≤ 6.5 :=
      (Real.log_le_log (by positivity) ((by exact_mod_cast hy0_le_y1 : (y0 : ℝ) ≤ (y1 : ℝ)).trans hy1_650)).trans lk_log650_le
    have hβ_def : 1.116 * log ((100 * N : ℕ) : ℝ) + 1 ≤ 1.1718 * (y0 : ℝ) + 28.37 := by
      linarith only [h100N_ub, hlog100, hlog1001, hlogy0_65]
    have hconv := lk_convex 1.1718 28.37
      (1.26 * log (log (M : ℝ)) - 1.93) (((k : ℝ) - 1) / 2) 201 (y0 : ℝ) (y1 : ℝ)
      (by norm_num) (by norm_num) hA_pos hk_half_pos (by norm_num) hy0_R (by exact_mod_cast hy0_le_y1)
    have hprod_le : (1.116 * log ((100 * N : ℕ) : ℝ) + 1) * (sumX b - sumX 61) ≤
        1.1718 * (1.26 * log (log (M : ℝ)) - 1.93) * (y0 : ℝ) +
          28.37 * (((k : ℝ) - 1) / 2) / (y0 : ℝ) +
          (1.1718 * (((k : ℝ) - 1) / 2) + 28.37 * (1.26 * log (log (M : ℝ)) - 1.93)) := by
      have h1 : sumX b - sumX 61 ≤ (1.26 * log (log (M : ℝ)) - 1.93) + (((k : ℝ) - 1) / 2) / (y0 : ℝ) := by
        have hdiv_eq : ((k : ℝ) - 1) / (2 * (y0 : ℝ)) = (((k : ℝ) - 1) / 2) / (y0 : ℝ) := by ring
        linarith only [hsum_b61, hA_ub, hdiv_eq]
      have h2 := mul_le_mul hβ_def h1 hS_nn (by linarith only [hy0_R])
      have h3 : (1.1718 * (y0 : ℝ) + 28.37) * ((1.26 * log (log (M : ℝ)) - 1.93) + (((k : ℝ) - 1) / 2) / (y0 : ℝ)) =
          1.1718 * (1.26 * log (log (M : ℝ)) - 1.93) * (y0 : ℝ) +
            28.37 * (((k : ℝ) - 1) / 2) / (y0 : ℝ) +
            (1.1718 * (((k : ℝ) - 1) / 2) + 28.37 * (1.26 * log (log (M : ℝ)) - 1.93)) := by
        field_simp [(by linarith only [hy0_R] : (y0 : ℝ) ≠ 0)]; ring
      linarith only [h2, h3]
    have hlogk_81 : log (k : ℝ) ≤ 8.1 := (Real.log_le_log (by positivity) hk3R).trans lk_log3000_le
    have hlogM_116 : log (M : ℝ) ≤ 11.6 := by
      have hllk : log (log (k : ℝ)) ≤ 2.1 := (Real.log_le_log (by linarith only [hlogk_lb]) hlogk_81).trans lk_log81_le
      linarith only [hlogM_ub, hlog4, hlogk_81, hllk]
    have hllM_246 : log (log (M : ℝ)) ≤ 2.46 := (Real.log_le_log (by linarith only [hlogM_lb]) hlogM_116).trans lk_log116_le
    have hL_lt : 1.1718 * (1.26 * log (log (M : ℝ)) - 1.93) * 201 +
        28.37 * (((k : ℝ) - 1) / 2) / 201 +
        (1.1718 * (((k : ℝ) - 1) / 2) + 28.37 * (1.26 * log (log (M : ℝ)) - 1.93)) < (k : ℝ) - 62 := by
      linarith only [hllM_246, hkR]
    have hU_lt : 1.1718 * (1.26 * log (log (M : ℝ)) - 1.93) * (y1 : ℝ) +
        28.37 * (((k : ℝ) - 1) / 2) / (y1 : ℝ) +
        (1.1718 * (((k : ℝ) - 1) / 2) + 28.37 * (1.26 * log (log (M : ℝ)) - 1.93)) < (k : ℝ) - 62 := by
      have hy1_290 : (290 : ℝ) ≤ (y1 : ℝ) := by exact_mod_cast hy1_def ▸ (large_k_y_bounds hk1500).1
      have hdiv_y1 : 28.37 * (((k : ℝ) - 1) / 2) / (y1 : ℝ) ≤ 28.37 * (((k : ℝ) - 1) / 2) / 290 := by gcongr
      have hdiv_eq : 28.37 * (((k : ℝ) - 1) / 2) / 290 = (28.37 / 580) * ((k : ℝ) - 1) := by ring
      have hprod_y1 : 1.1718 * (1.26 * log (log (M : ℝ)) - 1.93) * (y1 : ℝ) ≤
          (1.1718 * 1.17 * 0.86 / 4.07) * (k : ℝ) := by
        have hA' : 1.26 * log (log (M : ℝ)) - 1.93 ≤ 1.17 := by linarith only [hllM_246]
        have h2 : 4.07 ≤ 0.90 * log (k : ℝ) - 2.5 := by linarith only [hlogk_lb]
        have h3 : (y1 : ℝ) ≤ 0.86 * (k : ℝ) / 4.07 :=
          hU_ub.trans (div_le_div_of_nonneg_left (by positivity) (by norm_num) h2)
        have h4 : 1.1718 * 1.17 * (0.86 * (k : ℝ) / 4.07) = (1.1718 * 1.17 * 0.86 / 4.07) * (k : ℝ) := by ring
        nlinarith only [hA', h3, hA_pos, h4]
      linarith only [hdiv_y1, hdiv_eq, hprod_y1, hllM_246, hkR]
    have hmax_lt : max (1.1718 * (1.26 * log (log (M : ℝ)) - 1.93) * 201 +
        28.37 * (((k : ℝ) - 1) / 2) / 201)
      (1.1718 * (1.26 * log (log (M : ℝ)) - 1.93) * (y1 : ℝ) +
        28.37 * (((k : ℝ) - 1) / 2) / (y1 : ℝ)) +
      (1.1718 * (((k : ℝ) - 1) / 2) + 28.37 * (1.26 * log (log (M : ℝ)) - 1.93)) < (k : ℝ) - 62 := by
      rw [← max_add_add_right]
      exact max_lt hL_lt hU_lt
    linarith only [hprod_le, hconv, hmax_lt]
  have hk3R : (3000 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 3000 ≤ k)
  have hlogy0_ub : log (y0 : ℝ) ≤ 9.40 :=
    (Real.log_le_log (by positivity) (by exact_mod_cast hy12.le)).trans lk_log12000_le
  have hβ_def : 1.116 * log ((100 * N : ℕ) : ℝ) + 1 ≤ 1.1718 * (y0 : ℝ) + 34.84 := by
    linarith only [h100N_ub, hlog100, hlog1001, hlogy0_ub]
  have hconv := lk_convex 1.1718 34.84
    (1.26 * log (log (M : ℝ)) - 1.93) (((k : ℝ) - 1) / 2) 201 (y0 : ℝ) (y1 : ℝ)
    (by norm_num) (by norm_num) hA_pos hk_half_pos (by norm_num) hy0_R (by exact_mod_cast hy0_le_y1)
  have hprod_le : (1.116 * log ((100 * N : ℕ) : ℝ) + 1) * (sumX b - sumX 61) ≤
      1.1718 * (1.26 * log (log (M : ℝ)) - 1.93) * (y0 : ℝ) +
        34.84 * (((k : ℝ) - 1) / 2) / (y0 : ℝ) +
        (1.1718 * (((k : ℝ) - 1) / 2) + 34.84 * (1.26 * log (log (M : ℝ)) - 1.93)) := by
    have h1 : sumX b - sumX 61 ≤ (1.26 * log (log (M : ℝ)) - 1.93) + (((k : ℝ) - 1) / 2) / (y0 : ℝ) := by
      have hdiv_eq : ((k : ℝ) - 1) / (2 * (y0 : ℝ)) = (((k : ℝ) - 1) / 2) / (y0 : ℝ) := by ring
      linarith only [hsum_b61, hA_ub, hdiv_eq]
    have h2 := mul_le_mul hβ_def h1 hS_nn (by linarith only [hy0_R])
    have h3 : (1.1718 * (y0 : ℝ) + 34.84) * ((1.26 * log (log (M : ℝ)) - 1.93) + (((k : ℝ) - 1) / 2) / (y0 : ℝ)) =
        1.1718 * (1.26 * log (log (M : ℝ)) - 1.93) * (y0 : ℝ) +
          34.84 * (((k : ℝ) - 1) / 2) / (y0 : ℝ) +
          (1.1718 * (((k : ℝ) - 1) / 2) + 34.84 * (1.26 * log (log (M : ℝ)) - 1.93)) := by
      field_simp [(by linarith only [hy0_R] : (y0 : ℝ) ≠ 0)]; ring
    linarith only [h2, h3]
  have hllM_le : log (log (M : ℝ)) ≤ 1.5 + log (log (k : ℝ)) := by
    have hlogM_le2 : log (M : ℝ) ≤ 2 * log (k : ℝ) := by
      have hllk : log (log (k : ℝ)) ≤ log (k : ℝ) / 2 - 0.3 := by
        have h1 := Real.log_le_sub_one_of_pos (show 0 < log (k : ℝ) / 2 by linarith only [hlogk_lb])
        rw [Real.log_div (by linarith only [hlogk_lb]) (by norm_num)] at h1
        have hlog2 : log (2 : ℝ) < 0.7 := lt_trans Real.log_two_lt_d9 (by norm_num)
        linarith only [h1, hlog2]
      linarith only [hlogM_ub, hlog4, hllk, hlogk_lb]
    have h1 := Real.log_le_log (by linarith only [hlogM_lb]) hlogM_le2
    rw [Real.log_mul (by norm_num) (by linarith only [hlogk_lb])] at h1
    have hlog2 : log (2 : ℝ) ≤ 1.5 := by linarith only [lt_trans Real.log_two_lt_d9 (by norm_num : (0.6931471808 : ℝ) < 0.7)]
    linarith only [h1, hlog2]
  have hllk_le : log (log (k : ℝ)) ≤ log (k : ℝ) / 3 + 0.15 := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < log (k : ℝ) / 3 by linarith only [hlogk_lb])
    rw [Real.log_div (by linarith only [hlogk_lb]) (by norm_num)] at h1
    have hlog3 : log (3 : ℝ) < 1.15 := by
      have h := exp_div_100_gt_of_lt (B := 3) (wt := 115) (by norm_num) (by norm_num)
      norm_num at h; linarith only [h]
    linarith only [h1, hlog3]
  have hL_lt : 1.1718 * (1.26 * log (log (M : ℝ)) - 1.93) * 201 +
      34.84 * (((k : ℝ) - 1) / 2) / 201 +
      (1.1718 * (((k : ℝ) - 1) / 2) + 34.84 * (1.26 * log (log (M : ℝ)) - 1.93)) < (k : ℝ) - 62 := by
    by_cases hk15k : k < 15000
    · have hk15R : (k : ℝ) ≤ 15000 := by exact_mod_cast hk15k.le
      have hlogk_97 : log (k : ℝ) ≤ 9.7 := (Real.log_le_log (by positivity) hk15R).trans lk_log15000_le
      have hlogM_134 : log (M : ℝ) ≤ 13.4 := by
        have hllk : log (log (k : ℝ)) ≤ 2.28 := (Real.log_le_log (by linarith only [hlogk_lb]) hlogk_97).trans lk_log97_le
        linarith only [hlogM_ub, hlog4, hlogk_97, hllk]
      have hllM_260 : log (log (M : ℝ)) ≤ 2.60 := (Real.log_le_log (by linarith only [hlogM_lb]) hlogM_134).trans lk_log134_le
      linarith only [hllM_260, hk3R]
    · have hk15R : (15000 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 15000 ≤ k)
      have hlogk_lin : log (k : ℝ) ≤ 0.0022 * (k : ℝ) := by
        have h1 : log (k : ℝ) ≤ 6 * ((k : ℝ) ^ (1 / 6 : ℝ)) := by
          have h := Real.log_le_rpow_div (x := (k : ℝ)) (ε := (1 / 6 : ℝ)) (by positivity) (by norm_num)
          linarith only [h]
        have h2 : (4.9 : ℝ) ≤ (k : ℝ) ^ (1 / 6 : ℝ) := by
          refine (Real.rpow_le_rpow_iff (by norm_num) (by positivity) (by norm_num : (0 : ℝ) < 6)).mp ?_
          rw [← Real.rpow_mul (by positivity)]; norm_num; linarith only [hk15R]
        have h3 : (k : ℝ) ^ (1 / 6 : ℝ) * (k : ℝ) ^ (5 / 6 : ℝ) = (k : ℝ) := by
          rw [← Real.rpow_add (by positivity)]; norm_num
        have h4 : (4.9 : ℝ) ^ 5 ≤ (k : ℝ) ^ (5 / 6 : ℝ) := by
          have h5 : (4.9 : ℝ) ^ 5 = ((4.9 : ℝ)) ^ (5 : ℝ) := by norm_num
          rw [h5, show (5 / 6 : ℝ) = (1 / 6 : ℝ) * 5 by norm_num, Real.rpow_mul (by positivity)]
          exact Real.rpow_le_rpow (by norm_num) h2 (by norm_num)
        nlinarith only [h1, h3, h4, hk15R]
      linarith only [hllM_le, hllk_le, hlogk_lin, hk15R]
  have hU_lt : 1.1718 * (1.26 * log (log (M : ℝ)) - 1.93) * (y1 : ℝ) +
      34.84 * (((k : ℝ) - 1) / 2) / (y1 : ℝ) +
      (1.1718 * (((k : ℝ) - 1) / 2) + 34.84 * (1.26 * log (log (M : ℝ)) - 1.93)) < (k : ℝ) - 62 := by
    have hy1_290 : (290 : ℝ) ≤ (y1 : ℝ) := by exact_mod_cast hy1_def ▸ (large_k_y_bounds hk1500).1
    have hdiv_y1 : 34.84 * (((k : ℝ) - 1) / 2) / (y1 : ℝ) ≤ 34.84 * (((k : ℝ) - 1) / 2) / 290 := by gcongr
    have hdiv_eq : 34.84 * (((k : ℝ) - 1) / 2) / 290 = (34.84 / 580) * ((k : ℝ) - 1) := by ring
    by_cases hk110 : k < 110000
    · by_cases hk15k : k < 15000
      · have hk15R : (k : ℝ) ≤ 15000 := by exact_mod_cast hk15k.le
        have hlogk_97 : log (k : ℝ) ≤ 9.7 := (Real.log_le_log (by positivity) hk15R).trans lk_log15000_le
        have hlogM_134 : log (M : ℝ) ≤ 13.4 := by
          have hllk : log (log (k : ℝ)) ≤ 2.28 := (Real.log_le_log (by linarith only [hlogk_lb]) hlogk_97).trans lk_log97_le
          linarith only [hlogM_ub, hlog4, hlogk_97, hllk]
        have hllM_260 : log (log (M : ℝ)) ≤ 2.60 := (Real.log_le_log (by linarith only [hlogM_lb]) hlogM_134).trans lk_log134_le
        have hlogk_80 : 8.0 ≤ log (k : ℝ) := by
          have h1 := exp_div_100_lt_of_gt (B := 3000) (wt := 800) (by norm_num) (by norm_num)
          norm_num at h1
          exact (by linarith only [h1] : (8.0 : ℝ) ≤ log (3000 : ℝ)).trans (Real.log_le_log (by norm_num) hk3R)
        have hden_47 : 4.70 ≤ 0.90 * log (k : ℝ) - 2.5 := by linarith only [hlogk_80]
        have hprod_y1 : 1.1718 * (1.26 * log (log (M : ℝ)) - 1.93) * (y1 : ℝ) ≤
            (1.1718 * 1.35 * 0.86 / 4.70) * (k : ℝ) := by
          have hA' : 1.26 * log (log (M : ℝ)) - 1.93 ≤ 1.35 := by linarith only [hllM_260]
          have h3 : (y1 : ℝ) ≤ 0.86 * (k : ℝ) / 4.70 :=
            hU_ub.trans (div_le_div_of_nonneg_left (by positivity) (by norm_num) hden_47)
          have h4 : 1.1718 * 1.35 * (0.86 * (k : ℝ) / 4.70) = (1.1718 * 1.35 * 0.86 / 4.70) * (k : ℝ) := by ring
          nlinarith only [hA', h3, hA_pos, h4]
        linarith only [hdiv_y1, hdiv_eq, hprod_y1, hllM_260, hk3R]
      · have hk15R : (15000 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 15000 ≤ k)
        have hlogk_96 : 9.6 ≤ log (k : ℝ) := lk_log15000_ge.trans (Real.log_le_log (by norm_num) hk15R)
        have hden_61 : 6.14 ≤ 0.90 * log (k : ℝ) - 2.5 := by linarith only [hlogk_96]
        have hlogk_117 : log (k : ℝ) ≤ 11.7 := by
          have hk110R : (k : ℝ) ≤ 110000 := by exact_mod_cast hk110.le
          exact (Real.log_le_log (by positivity) hk110R).trans lk_log110000_le
        have hlogM_16 : log (M : ℝ) ≤ 16 := by
          have hllk : log (log (k : ℝ)) ≤ 2.5 := (Real.log_le_log (by linarith only [hlogk_lb]) hlogk_117).trans lk_log117_le
          linarith only [hlogM_ub, hlog4, hlogk_117, hllk]
        have hllM_28 : log (log (M : ℝ)) ≤ 2.80 := (Real.log_le_log (by linarith only [hlogM_lb]) hlogM_16).trans lk_log16_le
        have hprod_y1 : 1.1718 * (1.26 * log (log (M : ℝ)) - 1.93) * (y1 : ℝ) ≤
            (1.1718 * 1.60 * 0.86 / 6.14) * (k : ℝ) := by
          have hA' : 1.26 * log (log (M : ℝ)) - 1.93 ≤ 1.60 := by linarith only [hllM_28]
          have h3 : (y1 : ℝ) ≤ 0.86 * (k : ℝ) / 6.14 :=
            hU_ub.trans (div_le_div_of_nonneg_left (by positivity) (by norm_num) hden_61)
          have h4 : 1.1718 * 1.60 * (0.86 * (k : ℝ) / 6.14) = (1.1718 * 1.60 * 0.86 / 6.14) * (k : ℝ) := by ring
          nlinarith only [hA', h3, hA_pos, h4]
        linarith only [hdiv_y1, hdiv_eq, hprod_y1, hllM_28, hk15R]
    · have hk110R : (110000 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 110000 ≤ k)
      have hlogk_116 : 11.6 ≤ log (k : ℝ) := lk_log110000_ge.trans (Real.log_le_log (by norm_num) hk110R)
      have hy1_76 : (y1 : ℝ) ≤ 0.76 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5) := by
        have h1 : y1 ≤ ⌊0.76 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5)⌋₊ := by rw [hy1_def, if_neg (by omega : ¬ k < 95000)]
        exact (by exact_mod_cast h1 : (y1 : ℝ) ≤ _).trans (Nat.floor_le (by positivity))
      have hllM_lin : log (log (M : ℝ)) ≤ 1.79 + 0.087 * log (k : ℝ) := by
        have hllk : log (log (k : ℝ)) ≤ log (k : ℝ) / 5 + 0.65 := by
          have h1 := Real.log_le_sub_one_of_pos (show 0 < log (k : ℝ) / 5 by linarith only [hlogk_116])
          rw [Real.log_div (by linarith only [hlogk_116]) (by norm_num)] at h1
          linarith only [h1, lk_log5_le]
        have hM138 : log (M : ℝ) ≤ 1.38 * log (k : ℝ) := by linarith only [hlogM_ub, hlog4, hllk, hlogk_116]
        have h1 := Real.log_le_log (by linarith only [hlogM_lb]) hM138
        rw [Real.log_mul (by norm_num) (by linarith only [hlogk_116])] at h1
        have hlog138 : log (1.38 : ℝ) ≤ 0.33 := by
          have h := exp_div_100_gt_of_lt (B := 138) (wt := 493) (by norm_num) (by norm_num)
          have h2 : log (1.38 : ℝ) = log 138 - log 100 := by
            rw [show (1.38 : ℝ) = 138 / 100 by norm_num, Real.log_div (by norm_num) (by norm_num)]
          norm_num at h; linarith only [h, h2, lk_log100_gt]
        have hllk2 : log (log (k : ℝ)) ≤ 1.46 + 0.087 * log (k : ℝ) := by
          have h2 := Real.log_le_sub_one_of_pos (div_pos (by linarith only [hlogk_116]) (by norm_num : (0 : ℝ) < 11.6))
          rw [Real.log_div (by linarith only [hlogk_116]) (by norm_num)] at h2
          have hdiv116 : log (k : ℝ) / 11.6 ≤ 0.087 * log (k : ℝ) := by
            rw [div_le_iff₀ (by norm_num)]; linarith only [hlogk_116]
          linarith only [h2, lk_log116_le, hdiv116]
        linarith only [h1, hlog138, hllk2]
      have hprod_y1 : 1.1718 * (1.26 * log (log (M : ℝ)) - 1.93) * (y1 : ℝ) ≤ 0.22 * (k : ℝ) := by
        have h1 : 1.26 * log (log (M : ℝ)) - 1.93 ≤ 0.24 * (0.90 * log (k : ℝ) - 2.5) := by
          linarith only [hllM_lin, hlogk_116]
        have h2 : (1.26 * log (log (M : ℝ)) - 1.93) * (y1 : ℝ) ≤ 0.24 * 0.76 * (k : ℝ) := by
          have h3 := mul_le_mul_of_nonneg_left hy1_76 hA_pos.le
          have h4 : (1.26 * log (log (M : ℝ)) - 1.93) * (0.76 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5)) ≤
              0.24 * 0.76 * (k : ℝ) := by
            rw [mul_div_assoc', div_le_iff₀ hden_pos]
            nlinarith only [h1, hk110R]
          linarith only [h3, h4]
        linarith only [h2]
      have hlogk_lin : log (k : ℝ) ≤ 0.001 * (k : ℝ) := lk_logk_le_0001k (by omega)
      linarith only [hdiv_y1, hdiv_eq, hprod_y1, hllM_lin, hlogk_lin, hk110R]
  have hmax_lt : max (1.1718 * (1.26 * log (log (M : ℝ)) - 1.93) * 201 +
      34.84 * (((k : ℝ) - 1) / 2) / 201)
    (1.1718 * (1.26 * log (log (M : ℝ)) - 1.93) * (y1 : ℝ) +
      34.84 * (((k : ℝ) - 1) / 2) / (y1 : ℝ)) +
    (1.1718 * (((k : ℝ) - 1) / 2) + 34.84 * (1.26 * log (log (M : ℝ)) - 1.93)) < (k : ℝ) - 62 := by
    rw [← max_add_add_right]
    exact max_lt hL_lt hU_lt
  linarith only [hprod_le, hconv, hmax_lt]

private lemma large_k_caseB_ge12k {k y0 y1 a a' N N' M b : ℕ}
    (hk1500 : 1500 < k) (hy12_ge : 12000 ≤ y0) (hy0_le_y1 : y0 ≤ y1)
    (hy1_def : y1 = (if k < 95000 then ⌊0.86 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5)⌋₊
                     else ⌊0.76 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5)⌋₊))
    (hden_pos : 0 < 0.90 * log (k : ℝ) - 2.5)
    (hlogM_ub : log (M : ℝ) ≤ log 4 + log (k : ℝ) + log (log (k : ℝ)))
    (hlogM_lb : 10.5 ≤ log (M : ℝ))
    (h100N_ub : log ((100 * N : ℕ) : ℝ) ≤
      (if y0 < 12000 then 1.05 * (y0 : ℝ) else 1.26 * (y0 : ℝ)) + log 100 + log 1001 + 2 * log (y0 : ℝ))
    (hS_nn : 0 ≤ sumX b - sumX 61)
    (hsum_b61 : sumX b - sumX 61 ≤ 0.045 +
      (if a ≤ a' then (0 : ℝ)
       else 1.109 * (log (log (N : ℝ)) - log (log (N' : ℝ)) + 1 / log (N' : ℝ)) + 0.0001) +
      ((k : ℝ) - 1) / (2 * (y0 : ℝ)) +
      (1.05 * (log (log 12000) - log (log 290)) + 1.26 * (log (log (M : ℝ)) - log (log 12000)) + 0.085))
    (hsa_ub : (if a ≤ a' then (0 : ℝ)
       else 1.109 * (log (log (N : ℝ)) - log (log (N' : ℝ)) + 1 / log (N' : ℝ)) + 0.0001) ≤ 0.20) :
    (1.116 * log ((100 * N : ℕ) : ℝ) + 1) * (sumX b - sumX 61) < (k : ℝ) - 62 := by
  have hlog100 : log (100 : ℝ) ≤ 4.61 := lk_log100_lt.le
  have hlog1001 : log (1001 : ℝ) ≤ 6.91 := lk_log1001_le
  have hy1_12k : 12000 ≤ y1 := hy12_ge.trans hy0_le_y1
  have hk110 : 110000 ≤ k := by
    by_contra hlt; push Not at hlt
    have := hy1_def ▸ (large_k_y_bounds hk1500).2.1 hlt
    omega
  have hk110R : (110000 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk110
  have hlogk_116 : 11.6 ≤ log (k : ℝ) :=
    lk_log110000_ge.trans (Real.log_le_log (by norm_num) hk110R)
  have hy1_76 : (y1 : ℝ) ≤ 0.76 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5) := by
    have h1 : y1 ≤ ⌊0.76 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5)⌋₊ := by
      rw [hy1_def, if_neg (by omega : ¬ k < 95000)]
    exact (by exact_mod_cast h1 : (y1 : ℝ) ≤ _).trans (Nat.floor_le (by positivity))
  have hy0_R12 : (12000 : ℝ) ≤ (y0 : ℝ) := by exact_mod_cast hy12_ge
  have hlogy0_lin : log (y0 : ℝ) ≤ 8.40 + (y0 : ℝ) / 12000 := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < (y0 : ℝ) / 12000 by positivity)
    rw [Real.log_div (by positivity) (by norm_num)] at h1
    linarith only [h1, lk_log12000_le]
  rw [if_neg (by omega : ¬ y0 < 12000)] at h100N_ub
  have hβ_def : 1.116 * log ((100 * N : ℕ) : ℝ) + 1 ≤
      1.40635 * (y0 : ℝ) + 32.61 := by
    linarith only [h100N_ub, hlog100, hlog1001, hlogy0_lin]
  have hA_ub : 0.045 + (if a ≤ a' then (0 : ℝ)
     else 1.109 * (log (log (N : ℝ)) - log (log (N' : ℝ)) + 1 / log (N' : ℝ)) + 0.0001) +
    (1.05 * (log (log 12000) - log (log 290)) + 1.26 * (log (log (M : ℝ)) - log (log 12000)) + 0.085) ≤
      1.26 * log (log (M : ℝ)) - 1.93 := by
    linarith only [hsa_ub, lk_ll290_ge, lk_ll12k_ge, lk_ll12k_le]
  have hA_pos : 0 < 1.26 * log (log (M : ℝ)) - 1.93 := by
    have h2 : 2.34 ≤ log (log (M : ℝ)) := lk_log105_ge.trans (Real.log_le_log (by norm_num) hlogM_lb)
    linarith only [h2]
  have hllM_le : log (log (M : ℝ)) ≤ 0.33 + log (log (k : ℝ)) := by
    have hlog4 : log (4 : ℝ) < 1.4 := by
      have h2 : log (2 : ℝ) < 0.7 := lt_trans Real.log_two_lt_d9 (by norm_num)
      have h4 : log (4 : ℝ) = 2 * log (2 : ℝ) := by
        rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
      linarith only [h2, h4]
    have hllk : log (log (k : ℝ)) ≤ log (k : ℝ) / 5 + 0.65 := by
      have h1 := Real.log_le_sub_one_of_pos (show 0 < log (k : ℝ) / 5 by linarith only [hlogk_116])
      rw [Real.log_div (by linarith only [hlogk_116]) (by norm_num)] at h1
      linarith only [h1, lk_log5_le]
    have hM138 : log (M : ℝ) ≤ 1.38 * log (k : ℝ) := by linarith only [hlogM_ub, hlog4, hllk, hlogk_116]
    have h1 := Real.log_le_log (by linarith only [hlogM_lb]) hM138
    rw [Real.log_mul (by norm_num) (by linarith only [hlogk_116])] at h1
    have hlog138 : log (1.38 : ℝ) ≤ 0.33 := by
      have h := exp_div_100_gt_of_lt (B := 138) (wt := 493) (by norm_num) (by norm_num)
      have h2 : log (1.38 : ℝ) = log 138 - log 100 := by
        rw [show (1.38 : ℝ) = 138 / 100 by norm_num, Real.log_div (by norm_num) (by norm_num)]
      norm_num at h; linarith only [h, h2, lk_log100_gt]
    linarith only [h1, hlog138]
  have hllk_le : log (log (k : ℝ)) ≤ 1.46 + 0.087 * log (k : ℝ) := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos (by linarith only [hlogk_116]) (by norm_num : (0 : ℝ) < 11.6))
    rw [Real.log_div (by linarith only [hlogk_116]) (by norm_num)] at h1
    have hdiv116 : log (k : ℝ) / 11.6 ≤ 0.087 * log (k : ℝ) := by
      rw [div_le_iff₀ (by norm_num)]; linarith only [hlogk_116]
    linarith only [h1, lk_log116_le, hdiv116]
  have hprod_le : (1.116 * log ((100 * N : ℕ) : ℝ) + 1) * (sumX b - sumX 61) ≤
      1.40635 * (1.26 * log (log (M : ℝ)) - 1.93) * (y0 : ℝ) +
        32.61 * (((k : ℝ) - 1) / 2) / (y0 : ℝ) +
        (1.40635 * (((k : ℝ) - 1) / 2) + 32.61 * (1.26 * log (log (M : ℝ)) - 1.93)) := by
    have h1 : sumX b - sumX 61 ≤ (1.26 * log (log (M : ℝ)) - 1.93) + (((k : ℝ) - 1) / 2) / (y0 : ℝ) := by
      have hdiv_eq : ((k : ℝ) - 1) / (2 * (y0 : ℝ)) = (((k : ℝ) - 1) / 2) / (y0 : ℝ) := by ring
      linarith only [hsum_b61, hA_ub, hdiv_eq]
    have h2 := mul_le_mul hβ_def h1 hS_nn (by linarith only [hy0_R12])
    have h3 : (1.40635 * (y0 : ℝ) + 32.61) *
        ((1.26 * log (log (M : ℝ)) - 1.93) + (((k : ℝ) - 1) / 2) / (y0 : ℝ)) =
        1.40635 * (1.26 * log (log (M : ℝ)) - 1.93) * (y0 : ℝ) +
          32.61 * (((k : ℝ) - 1) / 2) / (y0 : ℝ) +
          (1.40635 * (((k : ℝ) - 1) / 2) + 32.61 * (1.26 * log (log (M : ℝ)) - 1.93)) := by
      field_simp [(by linarith only [hy0_R12] : (y0 : ℝ) ≠ 0)]; ring
    linarith only [h2, h3]
  have hdiv_y0 : 32.61 * (((k : ℝ) - 1) / 2) / (y0 : ℝ) ≤ (32.61 / 24000) * ((k : ℝ) - 1) := by
    have h1 : 32.61 * (((k : ℝ) - 1) / 2) / (y0 : ℝ) ≤ 32.61 * (((k : ℝ) - 1) / 2) / 12000 :=
      div_le_div_of_nonneg_left (by linarith only [hk110R]) (by norm_num) hy0_R12
    have h2 : 32.61 * (((k : ℝ) - 1) / 2) / 12000 = (32.61 / 24000) * ((k : ℝ) - 1) := by ring
    linarith only [h1, h2]
  have hprod_y0 : 1.40635 * (1.26 * log (log (M : ℝ)) - 1.93) * (y0 : ℝ) ≤
      1.40635 * 0.24 * 0.76 * (k : ℝ) := by
    have h1 : 1.26 * log (log (M : ℝ)) - 1.93 ≤ 0.24 * (0.90 * log (k : ℝ) - 2.5) := by
      linarith only [hllM_le, hllk_le, hlogk_116]
    have h2 : (y0 : ℝ) ≤ 0.76 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5) :=
      (by exact_mod_cast hy0_le_y1 : (y0 : ℝ) ≤ (y1 : ℝ)).trans hy1_76
    have h3 := mul_le_mul_of_nonneg_left h2 hA_pos.le
    have h4 : (1.26 * log (log (M : ℝ)) - 1.93) * (0.76 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5)) ≤
        0.24 * 0.76 * (k : ℝ) := by
      rw [mul_div_assoc', div_le_iff₀ hden_pos]
      nlinarith only [h1, hk110R]
    linarith only [h3, h4]
  have hlogk_lin : log (k : ℝ) ≤ 0.001 * (k : ℝ) := lk_logk_le_0001k hk110
  linarith only [hprod_le, hdiv_y0, hprod_y0, hllM_le, hllk_le, hlogk_lin, hk110R]

lemma large_k_case {k : ℕ} (hk1500 : 1500 < k) {d : ℕ → ℝ}
    (hd : ∀ r, d (pNth r) = densK k r) : ¬ Erdos690.IsUnimodalOnPrimes d := by
  classical
  obtain ⟨y0, hy0_def⟩ : ∃ y0 : ℕ, y0 = Nat.find (large_k_exists_y_good hk1500) := ⟨_, rfl⟩
  have hspec : goodGap k y0 := hy0_def ▸ Nat.find_spec (large_k_exists_y_good hk1500)
  rcases hspec with ⟨hy0_200, hy0_lb, a, N, hN10m, haN, hNa1, hgap_a, hlogN_lb, hlogN_ub, hk_le_a, hdesc⟩
  obtain ⟨b, hb_gt_N, hb1_le_100N, hgap_b⟩ := exists_small_gap_in_Icc hN10m
  have hab : a < b := by
    rw [← pNth_strictMono.lt_iff_lt]
    exact haN.trans hb_gt_N
  obtain ⟨y1, hy1_def⟩ : ∃ y1 : ℕ,
      y1 = (if k < 95000 then ⌊0.86 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5)⌋₊
            else ⌊0.76 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5)⌋₊) := ⟨_, rfl⟩
  have hy1_good : goodGap k y1 := hy1_def ▸ large_k_y1_good hk1500
  have hy0_le_y1 : y0 ≤ y1 := by
    rw [hy0_def]
    exact Nat.find_min' (large_k_exists_y_good hk1500) hy1_good
  have hy1_ub : y1 ≤ (if k < 95000 then ⌊0.86 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5)⌋₊
                      else ⌊0.76 * (k : ℝ) / (0.90 * log (k : ℝ) - 2.5)⌋₊) := hy1_def.le
  have hlogk_lb : 7.3 < log (k : ℝ) := (large_k_y_bounds hk1500).2.2.2.2
  have hden_pos : 0 < 0.90 * log (k : ℝ) - 2.5 := (large_k_y_bounds hk1500).2.2.2.1
  have hkR : (1501 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1501 ≤ k)
  obtain ⟨M, hM_def⟩ : ∃ M : ℕ, M = ⌊4 * (k : ℝ) * log (k : ℝ)⌋₊ := ⟨_, rfl⟩
  have hlogN_ge_140 : 140 ≤ log (N : ℝ) := by
    have ht : 0.70 * (y0 : ℝ) ≤ Chebyshev.theta (y0 : ℝ) := theta_ge_070 hy0_200
    have hyR : (200 : ℝ) ≤ (y0 : ℝ) := by exact_mod_cast hy0_200
    linarith only [ht, hlogN_lb, hyR]
  have hasc : (pNth (b + 1) : ℝ) - (pNth b : ℝ) + 1 < elemSym (k - 2) b / elemSym (k - 1) b := by
    have h61_lt : 61 < k - 1 := by omega
    have hSpos : sumX 61 < sumX b := by
      have h61_le_a : 61 < a := by omega
      have hx61 : 0 < xTerm 61 := xTerm_pos 61
      have hsum_le : sumX 61 + xTerm 61 ≤ sumX b := by
        unfold sumX
        rw [← Finset.sum_range_succ]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega : 62 ≤ b))
          (fun _ _ _ => xTerm_nonneg _)
      linarith only [hx61, hsum_le]
    have hlb := R_lower_bound (by omega) h61_lt (hk_le_a.trans hab.le) hSpos
    have hmul_goal : (1.116 * log ((100 * N : ℕ) : ℝ) + 1) * (sumX b - sumX 61) < ((k - 62 : ℕ) : ℝ) := by
      have h100N_ub : log ((100 * N : ℕ) : ℝ) ≤
          (if y0 < 12000 then 1.05 * (y0 : ℝ) else 1.26 * (y0 : ℝ)) +
            log 100 + log 1001 + 2 * log (y0 : ℝ) := by
        have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
        have hypos : (0 : ℝ) < (y0 : ℝ) := by exact_mod_cast (by omega : 0 < y0)
        have h1 : log ((100 * N : ℕ) : ℝ) = log 100 + log (N : ℝ) := by
          push_cast; rw [Real.log_mul (by norm_num) hNpos.ne']
        have h2 : log ((1001 * y0 ^ 2 : ℕ) : ℝ) = log 1001 + 2 * log (y0 : ℝ) := by
          push_cast
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
          ring
        have hth : Chebyshev.theta (y0 : ℝ) ≤
            (if y0 < 12000 then 1.05 * (y0 : ℝ) else 1.26 * (y0 : ℝ)) := by
          split_ifs with hy12
          · exact (theta_105_and_070_small hy0_200 hy12).2
          · exact theta_le_126_10k (by omega : 10000 ≤ y0)
        linarith only [h1, h2, hth, hlogN_ub]
      have hlog100 : log (100 : ℝ) ≤ 4.61 := lk_log100_lt.le
      have hlog1001 : log (1001 : ℝ) ≤ 6.91 := lk_log1001_le
      by_cases hcaseA : y0 = 200 ∨ 0.70 * ((y0 - 1 : ℕ) : ℝ) ≤ 2 * log (k : ℝ) + 2.4
      · -- Case A: y0 = 200 or y0 <= 2.86 * log k + 4.5
        have hb_le_pi : b ≤ Nat.primeCounting (100 * N) := by
          have h1 : pNth b ≤ 100 * N := (pNth_strictMono.monotone (Nat.le_succ b)).trans hb1_le_100N
          by_contra hgt; push Not at hgt
          have h2 := primeCounting_le_iff_pNth_gt.mp (by omega : Nat.primeCounting (100 * N) ≤ b)
          omega
        have hSb_mono : sumX b - sumX 61 ≤ sumX (Nat.primeCounting (100 * N)) - sumX 61 := by
          have h1 : sumX b ≤ sumX (Nat.primeCounting (100 * N)) := by
            unfold sumX
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hb_le_pi)
              (fun _ _ _ => xTerm_nonneg _)
          linarith only [h1]
        have hpi_ge : 2000 ≤ Nat.primeCounting (100 * N) := by
          have h1 := primeCounting_40000_ge_2000
          have h2 : Nat.primeCounting 40000 ≤ Nat.primeCounting (100 * N) :=
            Nat.monotone_primeCounting (by omega)
          omega
        have hSk_100N := large_k_Sk_sub_61_le (k := Nat.primeCounting (100 * N) + 1) (M := 100 * N)
          (by omega) (by omega) (by omega)
        have hSk_step : sumX (Nat.primeCounting (100 * N)) ≤
            sumX (Nat.primeCounting (100 * N) - 1) + 0.02 := by
          have hpi_eq : Nat.primeCounting (100 * N) = (Nat.primeCounting (100 * N) - 1) + 1 := by omega
          have hx_ub : xTerm (Nat.primeCounting (100 * N) - 1) ≤ 0.02 := by
            unfold xTerm
            have hp_ge : (63 : ℝ) ≤ (pNth (Nat.primeCounting (100 * N) - 1) : ℝ) := by
              have h1 : 61 + 2 ≤ pNth 61 := by
                have := pNth_ge_add_two 61; omega
              have h2 : pNth 61 ≤ pNth (Nat.primeCounting (100 * N) - 1) :=
                pNth_strictMono.monotone (by omega)
              exact_mod_cast h1.trans h2
            rw [div_le_iff₀ (by linarith)]
            linarith
          have hsum_eq : sumX (Nat.primeCounting (100 * N)) =
              sumX (Nat.primeCounting (100 * N) - 1) + xTerm (Nat.primeCounting (100 * N) - 1) := by
            conv_lhs => rw [hpi_eq]
            unfold sumX; rw [Finset.sum_range_succ]
          linarith only [hsum_eq, hx_ub]
        have hSk_eq : (Nat.primeCounting (100 * N) + 1 - 2 : ℕ) = Nat.primeCounting (100 * N) - 1 := by omega
        rw [hSk_eq] at hSk_100N
        have hSk_100N' : sumX (Nat.primeCounting (100 * N)) - sumX 61 ≤
            1.26 * log (log ((100 * N : ℕ) : ℝ)) - 1.44 := by
          have hll290 : 1.73 ≤ log (log (290 : ℝ)) := lk_ll290_ge
          have hll12k : 2.23 ≤ log (log (12000 : ℝ)) := lk_ll12k_ge
          linarith only [hSk_100N, hSk_step, hll290, hll12k]
        by_cases hy0_200_eq : y0 = 200
        · subst hy0_200_eq
          have hy200_lt : (200 : ℕ) < 12000 := by omega
          rw [if_pos hy200_lt] at h100N_ub
          have hlog200 : log (200 : ℝ) ≤ 5.30 := lk_log200_le
          have h100N_233 : log ((100 * N : ℕ) : ℝ) ≤ 232.2 := by linarith only [h100N_ub, hlog100, hlog1001, hlog200]
          have hll233 : log (log ((100 * N : ℕ) : ℝ)) ≤ 5.46 := by
            have hpos : 0 < log ((100 * N : ℕ) : ℝ) := by linarith only [hlogN_ge_140, Real.log_le_log (by positivity) (show (N : ℝ) ≤ ((100 * N : ℕ) : ℝ) by exact_mod_cast (by omega : N ≤ 100 * N))]
            exact (Real.log_le_log hpos h100N_233).trans lk_log2322_le
          have hkm62 : (1439 : ℝ) ≤ ((k - 62 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1439 ≤ k - 62)
          have hS_pos : 0 ≤ sumX b - sumX 61 := by linarith only [hSpos]
          nlinarith only [h100N_233, hSb_mono, hSk_100N', hll233, hkm62, hS_pos]
        · -- y0 > 200 and 0.70 * (y0 - 1) <= 2 * log k + 2.4
          have hy0_gt : 201 ≤ y0 := by omega
          have hy0_small : 0.70 * ((y0 - 1 : ℕ) : ℝ) ≤ 2 * log (k : ℝ) + 2.4 := hcaseA.resolve_left hy0_200_eq
          have hy0_ub : (y0 : ℝ) ≤ 2.86 * log (k : ℝ) + 4.5 := by
            have h1 : ((y0 - 1 : ℕ) : ℝ) = (y0 : ℝ) - 1 := by exact_mod_cast Nat.cast_sub (by omega : 1 ≤ y0)
            linarith only [hy0_small, h1, hlogk_lb]
          have hk_huge : 68 ≤ log (k : ℝ) := by
            have : (201 : ℝ) ≤ (y0 : ℝ) := by exact_mod_cast hy0_gt
            linarith only [this, hy0_ub]
          have h100N_ub' : log ((100 * N : ℕ) : ℝ) ≤ 4.2 * log (k : ℝ) := by
            have hy_le : (if y0 < 12000 then 1.05 * (y0 : ℝ) else 1.26 * (y0 : ℝ)) ≤ 1.26 * (y0 : ℝ) := by
              split_ifs <;> linarith only [show (0 : ℝ) ≤ (y0 : ℝ) by positivity]
            have hlogy0 : log (y0 : ℝ) ≤ log (3 * log (k : ℝ)) :=
              Real.log_le_log (by positivity) (by linarith only [hy0_ub, hk_huge])
            have hllk : log (3 * log (k : ℝ)) ≤ 2 + log (log (k : ℝ)) := by
              rw [Real.log_mul (by norm_num) (by linarith)]
              have hlog3 : log (3 : ℝ) ≤ 2 := by
                have h := exp_div_100_gt_of_lt (B := 3) (wt := 200) (by norm_num) (by norm_num)
                norm_num at h; linarith only [h]
              linarith
            have hllk2 : log (log (k : ℝ)) ≤ log (k : ℝ) / 10 + 1.4 := by
              have h1 := Real.log_le_sub_one_of_pos (show 0 < log (k : ℝ) / 10 by linarith)
              rw [Real.log_div (by linarith) (by norm_num)] at h1
              have hlog10 : log (10 : ℝ) ≤ 2.4 := lk_log10_le
              linarith only [h1, hlog10]
            linarith only [h100N_ub, hy_le, hy0_ub, hlog100, hlog1001, hlogy0, hllk, hllk2, hk_huge]
          have hll_ub : log (log ((100 * N : ℕ) : ℝ)) ≤ 1.5 + log (log (k : ℝ)) := by
            have hpos : 0 < log ((100 * N : ℕ) : ℝ) := by
              have hle : (N : ℝ) ≤ ((100 * N : ℕ) : ℝ) := by exact_mod_cast (by omega : N ≤ 100 * N)
              linarith only [hlogN_ge_140, Real.log_le_log (by positivity) hle]
            have h1 := Real.log_le_log hpos h100N_ub'
            rw [Real.log_mul (by norm_num) (by linarith)] at h1
            have hlog42 : log (4.2 : ℝ) ≤ 1.5 := by
              have h := exp_div_100_gt_of_lt (B := 42) (wt := 380) (by norm_num) (by norm_num)
              have h2 : log (4.2 : ℝ) = log 42 - log 10 := by
                rw [show (4.2 : ℝ) = 42 / 10 by norm_num, Real.log_div (by norm_num) (by norm_num)]
              norm_num at h; linarith only [h, h2, lk_log10_gt]
            linarith only [h1, hlog42]
          have hk_exp72 : (log (k : ℝ)) ^ 3 < (k : ℝ) := by
            have h1 : log (k : ℝ) ≤ 6 * ((k : ℝ) ^ (1 / 6 : ℝ)) := by
              have h := Real.log_le_rpow_div (x := (k : ℝ)) (ε := (1 / 6 : ℝ)) (by positivity) (by norm_num)
              linarith
            have h2 : (6 * ((k : ℝ) ^ (1 / 6 : ℝ))) ^ (3 : ℕ) = 216 * √(k : ℝ) := by
              calc (6 * ((k : ℝ) ^ (1 / 6 : ℝ))) ^ (3 : ℕ)
                  = 216 * (((k : ℝ) ^ (1 / 6 : ℝ)) ^ (3 : ℕ)) := by ring
                _ = 216 * (((k : ℝ) ^ (1 / 6 : ℝ)) ^ (3 : ℝ)) := by
                    rw [← Real.rpow_natCast ((k : ℝ) ^ (1 / 6 : ℝ)) 3]; norm_num
                _ = 216 * ((k : ℝ) ^ ((1 / 6 : ℝ) * 3)) := by
                    rw [← Real.rpow_mul (by positivity)]
                _ = 216 * √(k : ℝ) := by norm_num; rw [← Real.sqrt_eq_rpow]
            have h3 : 216 * √(k : ℝ) < (k : ℝ) := by
              have h216 : (216 : ℝ) < √(k : ℝ) := by
                rw [Real.lt_sqrt (by norm_num)]
                have h1' : (50000 : ℝ) < (k : ℝ) := by
                  have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
                  have hlt : log (50000 : ℝ) < log (k : ℝ) := lt_of_lt_of_le lk_log50000_lt (by linarith only [hk_huge])
                  exact (Real.log_lt_log_iff (by norm_num) hk_pos).mp hlt
                linarith
              nlinarith only [h216, Real.sq_sqrt (show 0 ≤ (k : ℝ) by positivity)]
            have hlog_nn : 0 ≤ log (k : ℝ) := by linarith
            have hpow3 : (log (k : ℝ)) ^ 3 ≤ (6 * ((k : ℝ) ^ (1 / 6 : ℝ))) ^ 3 :=
              pow_le_pow_left₀ hlog_nn h1 3
            linarith
          have hllk_le : log (log (k : ℝ)) ≤ log (k : ℝ) :=
            (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
          have hprod_le : (1.116 * log ((100 * N : ℕ) : ℝ) + 1) * (sumX b - sumX 61) ≤
              (4.7 * log (k : ℝ) + 1) * (1.26 * log (k : ℝ) + 1) := by
            have hS_nn : 0 ≤ sumX b - sumX 61 := by linarith only [hSpos]
            have hL_nn : 0 ≤ 1.116 * log ((100 * N : ℕ) : ℝ) + 1 := by
              have hle : (N : ℝ) ≤ ((100 * N : ℕ) : ℝ) := by exact_mod_cast (by omega : N ≤ 100 * N)
              linarith only [hlogN_ge_140, Real.log_le_log (by positivity) hle]
            exact mul_le_mul (by linarith only [h100N_ub', hk_huge])
              (by linarith only [hSb_mono, hSk_100N', hll_ub, hllk_le]) hS_nn (by linarith only [hk_huge])
          have hkm62_eq : ((k - 62 : ℕ) : ℝ) = (k : ℝ) - 62 := by exact_mod_cast Nat.cast_sub (by omega : 62 ≤ k)
          rw [hkm62_eq]
          nlinarith only [hprod_le, hk_exp72, hk_huge]
      · -- Case B: 201 <= y0 and 2 * log k + 2.4 < 0.70 * (y0 - 1)
        push Not at hcaseA
        have hy0_gt : 201 ≤ y0 := by omega
        have hy'_200 : 200 ≤ y0 - 1 := by omega
        have hy'_lb : 2 * log (k : ℝ) + 2.4 < 0.70 * ((y0 - 1 : ℕ) : ℝ) := hcaseA.2
        have hnot : ¬ goodGap k (y0 - 1) := by
          rw [hy0_def]
          exact Nat.find_min (large_k_exists_y_good hk1500) (by omega)
        obtain ⟨a', N', hN'10m, ha'N', hN'a1', hgap_a', hlogN'_lb, hlogN'_ub⟩ := exists_large_gap_below hy'_200
        have hMb := large_k_M_bounds hk1500 hy0_200 hN10m hlogk_lb hy0_lb haN hNa1 hlogN_lb
        have hM40k : 40000 ≤ M := hM_def ▸ hMb.1
        have hkM : k - 1 ≤ Nat.primeCounting M := hM_def ▸ hMb.2.1
        have hMa : Nat.primeCounting M ≤ a := hM_def ▸ hMb.2.2.1
        have hlogM_ub : log (M : ℝ) ≤ log 4 + log (k : ℝ) + log (log (k : ℝ)) := hM_def ▸ hMb.2.2.2.1
        have hlogM_lb : 10.5 ≤ log (M : ℝ) := hM_def ▸ hMb.2.2.2.2
        have hMb' := large_k_M_bounds hk1500 hy'_200 hN'10m hlogk_lb hy'_lb ha'N' hN'a1' hlogN'_lb
        have hMa' : Nat.primeCounting M ≤ a' := hM_def ▸ hMb'.2.2.1
        have hk_le_a' : k - 1 ≤ a' := hkM.trans hMa'
        have hR_ge : (pNth (a' + 1) : ℝ) - (pNth a' : ℝ) + 1 ≤ elemSym (k - 2) a' / elemSym (k - 1) a' := by
          by_contra hlt
          push Not at hlt
          exact hnot ⟨hy'_200, hy'_lb, a', N', hN'10m, ha'N', hN'a1', hgap_a', hlogN'_lb, hlogN'_ub, hk_le_a', hlt⟩
        have hD'_pos : 0 < sumX a' - sumX (k - 2) :=
          large_k_D'_pos hM40k hN'10m hkM hMa' ha'N' hN'a1' hlogk_lb hy'_200 hy'_lb hlogN'_lb hlogM_ub hlogM_lb
        have hub' := R_upper_bound (by omega) hk_le_a' (sub_pos.mp hD'_pos)
        have h2y0 : 2 * (y0 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) / (sumX a' - sumX (k - 2)) := by
          have hy_cast : ((y0 - 1 : ℕ) : ℝ) = (y0 : ℝ) - 1 := by exact_mod_cast Nat.cast_sub (by omega : 1 ≤ y0)
          linarith only [hgap_a', hR_ge, hub', hy_cast]
        have hD'_ub : sumX a' - sumX (k - 2) ≤ ((k - 1 : ℕ) : ℝ) / (2 * (y0 : ℝ)) := by
          rw [le_div_iff₀ (by positivity)]
          have h1 := (le_div_iff₀ hD'_pos).mp h2y0
          linarith only [h1]
        have hpa_40k : 40000 ≤ pNth a := by
          have hpi : M < pNth (Nat.primeCounting M) := primeCounting_le_iff_pNth_gt.mp (le_refl _)
          exact (by omega : 40000 ≤ M).trans (hpi.le.trans (pNth_strictMono.monotone hMa))
        have hSb_a := large_k_Sb_sub_a_le hN10m hpa_40k haN hNa1 hb_gt_N hb1_le_100N hlogN_ge_140
        have hSk_61 := large_k_Sk_sub_61_le hM40k hkM hk1500
        have hSa_a' := large_k_Sa_a' hM40k hMa' hN'10m haN hN'a1'
        -- Combine: sumX b - sumX 61 <= 0.045 + sa_diff + (k - 1)/(2*y0) + s_k_61
        have hconvex := lk_convex
        have hy0_R : (201 : ℝ) ≤ (y0 : ℝ) := by exact_mod_cast hy0_gt
        have hsum_b61 : sumX b - sumX 61 ≤ 0.045 +
            (if a ≤ a' then (0 : ℝ)
             else 1.109 * (log (log (N : ℝ)) - log (log (N' : ℝ)) + 1 / log (N' : ℝ)) + 0.0001) +
            ((k - 1 : ℕ) : ℝ) / (2 * (y0 : ℝ)) +
            (1.05 * (log (log 12000) - log (log 290)) + 1.26 * (log (log (M : ℝ)) - log (log 12000)) + 0.085) := by
          linarith only [hSb_a, hSa_a', hD'_ub, hSk_61]
        -- Bound sa_diff cleanly:
        have hsa_ub := large_k_sa_ub (a := a) (a' := a') hy0_200 hy'_200 hy0_gt hlogN_ge_140 hlogN_ub hlogN'_lb
        -- Now finish Case B via hconvex!
        have hk62_eq : ((k - 62 : ℕ) : ℝ) = (k : ℝ) - 62 := by exact_mod_cast Nat.cast_sub (by omega : 62 ≤ k)
        have hkm1_eq : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by exact_mod_cast Nat.cast_sub (by omega : 1 ≤ k)
        rw [hk62_eq]
        rw [hkm1_eq] at hsum_b61
        have hS_nn : 0 ≤ sumX b - sumX 61 := by linarith only [hSpos]
        have hL_nn : 0 ≤ 1.116 * log ((100 * N : ℕ) : ℝ) + 1 := by
          have hle : (N : ℝ) ≤ ((100 * N : ℕ) : ℝ) := by exact_mod_cast (by omega : N ≤ 100 * N)
          linarith only [hlogN_ge_140, Real.log_le_log (by positivity) hle]
        by_cases hy12 : y0 < 12000
        · exact large_k_caseB_lt12k hk1500 hy0_gt hy0_le_y1 hy12 hy1_def hlogk_lb hden_pos hlogM_ub hlogM_lb h100N_ub hS_nn hsum_b61 hsa_ub
        · exact large_k_caseB_ge12k hk1500 (by omega) hy0_le_y1 hy1_def hden_pos hlogM_ub hlogM_lb h100N_ub hS_nn hsum_b61 hsa_ub
    have hS_pos : 0 < sumX b - sumX 61 := by linarith only [hSpos]
    have hdiv : ((k - 62 : ℕ) : ℝ) / (sumX b - sumX 61) > 1.116 * log ((100 * N : ℕ) : ℝ) + 1 := by
      rw [gt_iff_lt, lt_div_iff₀ hS_pos]
      exact hmul_goal
    have hsub_eq : k - 1 - 61 = k - 62 := by omega
    rw [hsub_eq] at hlb
    linarith only [hlb, hdiv, hgap_b]
  exact not_unimodal_of_descent_ascent (by omega) hd hab hk_le_a hdesc hasc


end Erdos690Proof

theorem OMA.solution : type_of% @Erdos690.erdos_690.variants.large_k := by
  intro ⟨k, hk, h⟩
  let d : ℕ → ℝ := fun p => if p.Prime then Erdos690Proof.densK k (Nat.count Nat.Prime p) else 0
  have hd_dens : ∀ p, p.Prime → (Erdos690.kthPrimeFactorSet k p).HasDensity (d p) := by
    intro p hp
    have hdp : d p = Erdos690Proof.densK k (Nat.count Nat.Prime p) := if_pos hp
    rw [hdp]
    have hnth : Erdos690Proof.pNth (Nat.count Nat.Prime p) = p := Nat.nth_count hp
    nth_rw 1 [← hnth]
    exact Erdos690Proof.kthPrimeFactorSet_hasDensity k (Nat.count Nat.Prime p) (by omega)
  have hunim := h d hd_dens
  have hd_eq : ∀ r, d (Erdos690Proof.pNth r) = Erdos690Proof.densK k r := by
    intro r
    dsimp [d]
    rw [if_pos (Erdos690Proof.pNth_prime r)]
    congr 1
    exact Erdos690Proof.pNth_strictMono.injective (Nat.nth_count (Erdos690Proof.pNth_prime r))
  by_cases hk1500 : k ≤ 1500
  · exact Erdos690Proof.moderate_k_case hk hk1500 hd_eq hunim
  · exact Erdos690Proof.large_k_case (by omega) hd_eq hunim
