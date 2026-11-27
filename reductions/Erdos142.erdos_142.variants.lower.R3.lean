import FormalConjectures.ErdosProblems.«142»

-- Reduction Erdos142.erdos_142.variants.lower.R3 of Erdős Problem 142 — lower
-- Credit: @mucoucah
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos142_erdos_142_variants_lower_R3

open Asymptotics Erdos142 Filter
open scoped Topology

lemma apFree_iff {A : Set ℕ} {k : ℕ} (hk : 1 < k) :
    A.IsAPOfLengthFree k ↔ ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A := by
  have hk' : (1 : ℕ∞) < (k : ℕ∞) := by exact_mod_cast hk
  constructor
  · rintro hA ⟨a, d, hd, hterms⟩
    let f (i : ℕ) := a + i * d
    let T := (Finset.range k).image f
    have hf : Function.Injective f := fun i j hij =>
      Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel hij)
    have hT : ((T : Finset ℕ) : Set ℕ) = {a + n • d | (n : ℕ) (_ : n < (k : ℕ∞))} := by
      ext x
      simp [T, f]
    have hcard : T.card = k := by simp [T, Finset.card_image_of_injective _ hf]
    have hsub : (T : Set ℕ) ⊆ A := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact hterms i (Finset.mem_range.mp hi)
    exact hk'.not_ge (hA _ hsub ⟨a, d, by simp [hcard], hT⟩)
  · intro hno T hsub hT
    obtain ⟨a, d, hcard, hterms⟩ := hT
    have hmem (i : ℕ) (hi : i < k) : a + i * d ∈ T := by
      rw [hterms]
      exact ⟨i, by exact_mod_cast hi, by simp⟩
    have hd : 0 < d := by
      by_contra! h
      have he : d = 0 := Nat.eq_zero_of_le_zero h
      have hs : T = {a} := by
        apply Set.Subset.antisymm
        · rw [hterms, he]
          rintro _ ⟨i, -, rfl⟩
          simp
        · apply Set.singleton_subset_iff.mpr
          simpa using hmem 0 (by omega)
      rw [hs] at hcard
      exact hk'.ne (by simpa using hcard)
    exact (hno ⟨a, d, hd, fun i hi => hsub (hmem i hi)⟩).elim

lemma exists_maximizer {k : ℕ} (hk : 1 < k) (N : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧ (S : Set ℕ).IsAPOfLengthFree k ∧
      r k N = S.card := by
  let C : Set ℕ := {m | ∃ S : Finset ℕ, ∃ _ : S ⊆ Finset.Icc 1 N,
    ∃ _ : (S : Set ℕ).IsAPOfLengthFree k, S.card = m}
  have hz : 0 ∈ C := by
    refine ⟨∅, Finset.empty_subset _, (apFree_iff hk).mpr ?_, rfl⟩
    rintro ⟨a, d, -, h⟩
    simpa using h 0 (by omega)
  have hb : BddAbove C := by
    refine ⟨N, ?_⟩
    rintro _ ⟨S, hS, -, rfl⟩
    simpa using Finset.card_le_card hS
  obtain ⟨S, hS, hf, he⟩ := Nat.sSup_mem ⟨0, hz⟩ hb
  exact ⟨S, hS, hf, he.symm⟩

lemma card_le_r {k N : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 N)
    (hf : (S : Set ℕ).IsAPOfLengthFree k) : S.card ≤ r k N := by
  unfold r Set.IsAPOfLengthFree.maxCard
  refine le_csSup ?_ ⟨S, hS, hf, rfl⟩
  refine ⟨N, ?_⟩
  rintro _ ⟨U, hU, -, rfl⟩
  simpa using Finset.card_le_card hU

lemma r_mono {k : ℕ} (hk : 1 < k) : Monotone (r k) := by
  intro M N hMN
  obtain ⟨S, hS, hf, hcard⟩ := exists_maximizer hk M
  rw [hcard]
  exact card_le_r (hS.trans (Finset.Icc_subset_Icc_right hMN)) hf

lemma r_add_le {k : ℕ} (hk : 1 < k) (M N : ℕ) :
    r k (M + N) ≤ r k M + r k N := by
  obtain ⟨S, hS, hf, hcard⟩ := exists_maximizer hk (M + N)
  let L := S.filter (· ≤ M)
  let R := S.filter (fun x => ¬ x ≤ M)
  let U := (Finset.Icc 1 N).filter (fun x => M + x ∈ S)
  have hL : L.card ≤ r k M := by
    apply card_le_r
    · intro x hx
      obtain ⟨hxS, hxM⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (hS hxS)).1, hxM⟩
    · exact fun T hT hAP => hf T (hT.trans (Finset.filter_subset _ _)) hAP
  have hU : U.card ≤ r k N := by
    apply card_le_r (Finset.filter_subset _ _)
    rw [apFree_iff hk] at hf ⊢
    rintro ⟨a, d, hd, h⟩
    refine hf ⟨M + a, d, hd, fun i hi => ?_⟩
    change M + a + i * d ∈ S
    simpa only [add_assoc] using (Finset.mem_filter.mp (h i hi)).2
  have hR : R.card ≤ U.card := by
    apply Finset.card_le_card_of_injOn (fun x => x - M)
    · intro x hx
      obtain ⟨hxS, hxM⟩ := Finset.mem_filter.mp hx
      have hxN := (Finset.mem_Icc.mp (hS hxS)).2
      change x - M ∈ U
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
        by rwa [show M + (x - M) = x by omega]⟩
    · intro x hx y hy he
      have hxM := (Finset.mem_filter.mp hx).2
      have hyM := (Finset.mem_filter.mp hy).2
      change x - M = y - M at he
      omega
  calc
    r k (M + N) = L.card + R.card := hcard.trans
      (Finset.card_filter_add_card_filter_not (s := S) (· ≤ M)).symm
    _ ≤ r k M + r k N := Nat.add_le_add hL (hR.trans hU)

lemma r_mul_le {k : ℕ} (hk : 1 < k) (N q : ℕ) : r k (q * N) ≤ q * r k N := by
  induction q with
  | zero =>
    simp only [zero_mul]
    obtain ⟨S, hS, -, hcard⟩ := exists_maximizer hk 0
    rw [hcard]
    simpa using Finset.card_le_card hS
  | succ q ih =>
    rw [Nat.succ_mul, Nat.succ_mul]
    exact (r_add_le hk (q * N) N).trans (Nat.add_le_add_right ih _)

lemma blockDensity_antitone {k : ℕ} (hk : 1 < k) : Antitone (fun j : ℕ => (r k (4 ^ j) : ℝ) / (4 : ℝ) ^ j) := by
  intro i j hij
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hij
  have hb : (r k (4 ^ (i + t)) : ℝ) ≤ (4 : ℝ) ^ t * r k (4 ^ i) := by
    exact_mod_cast (show r k (4 ^ (i + t)) ≤ 4 ^ t * r k (4 ^ i) by
      rw [pow_add, mul_comm]
      exact r_mul_le hk _ _)
  beta_reduce
  have hp : (0 : ℝ) < 4 ^ t := by positivity
  calc
    _ ≤ ((4 : ℝ) ^ t * r k (4 ^ i)) / 4 ^ (i + t) :=
      div_le_div_of_nonneg_right hb (by positivity)
    _ = _ := by rw [pow_add]; field_simp

lemma littleO_of_blockDensity {k : ℕ} (hk : 1 < k)
    (h : ∀ δ : ℝ, 0 < δ → ∀ᶠ j : ℕ in atTop, (j : ℝ) * ((r k (4 ^ j) : ℝ) / (4 : ℝ) ^ j) ≤ δ) :
    (fun N => (r k N : ℝ)) =o[atTop] (fun N : ℕ => N / (N : ℝ).log) := by
  rw [isLittleO_iff]
  intro ε hε
  have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
  let C := 8 * Real.log 4
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (h (ε / C) (div_pos hε hC))
  filter_upwards [eventually_ge_atTop (4 ^ max J 1)] with N hN
  let j := Nat.log 4 N
  have hj : max J 1 ≤ j := Nat.le_log_of_pow_le (by decide) hN
  have hj1 : 1 ≤ j := (le_max_right _ _).trans hj
  have hN4 : 4 ≤ N := by
    have hp : 4 ^ 1 ≤ (4 : ℕ) ^ max J 1 :=
      pow_le_pow_right₀ (by decide) (le_max_right _ _)
    simpa using hp.trans hN
  have hlN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hfloor : 4 ^ j ≤ N := Nat.pow_log_le_self 4 (by omega)
  have hceil : N < 4 ^ (j + 1) := Nat.lt_pow_succ_log_self (by decide) _
  have hr : (r k N : ℝ) ≤ 4 * r k (4 ^ j) := by
    exact_mod_cast ((r_mono hk hceil.le).trans (by
      rw [pow_succ, mul_comm]
      exact r_mul_le hk _ _))
  have hlogN : Real.log (N : ℝ) ≤ 2 * (j : ℝ) * Real.log 4 := by
    have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hc : (N : ℝ) ≤ (4 : ℝ) ^ (j + 1) := by exact_mod_cast hceil.le
    have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
    calc
      _ ≤ Real.log ((4 : ℝ) ^ (j + 1)) := Real.log_le_log hpos hc
      _ ≤ _ := by
        rw [Real.log_pow, Nat.cast_add, Nat.cast_one]
        exact mul_le_mul_of_nonneg_right (by linarith) hlog.le
  have hd := hJ j ((le_max_left _ _).trans hj)
  rw [← mul_div_assoc, div_le_iff₀ (by positivity)] at hd
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
    ← mul_div_assoc, le_div_iff₀ hlN]
  calc
    _ ≤ (4 * (r k (4 ^ j) : ℝ)) * (2 * (j : ℝ) * Real.log 4) := by gcongr
    _ = C * ((j : ℝ) * r k (4 ^ j)) := by dsimp [C]; ring
    _ ≤ C * (ε / C * (4 : ℝ) ^ j) := mul_le_mul_of_nonneg_left hd hC.le
    _ = ε * (4 : ℝ) ^ j := by field_simp
    _ ≤ ε * N := mul_le_mul_of_nonneg_left (by exact_mod_cast hfloor) hε.le

lemma mem_shiftBlock_bounds {j x : ℕ} {B : Finset ℕ} (hB : B ⊆ Finset.Icc 1 (4 ^ j))
    (hx : x ∈ B.map (addLeftEmbedding (4 * 4 ^ j))) : 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j := by
  obtain ⟨b, hb, he⟩ := Finset.mem_map.mp hx
  change 4 * 4 ^ j + b = x at he
  obtain ⟨h₁, h₂⟩ := Finset.mem_Icc.mp (hB hb)
  omega

lemma pow_four_gap {i j : ℕ} (hij : i < j) : 4 * 4 ^ i ≤ 4 ^ j := by
  rw [mul_comm, ← pow_succ]
  exact pow_le_pow_right₀ (by decide) hij

lemma blockIndex_le {i j x y : ℕ} (hxy : x ≤ y) (hx : 4 * 4 ^ i < x)
    (hy : y ≤ 5 * 4 ^ j) : i ≤ j := by
  by_contra! h
  have hp := pow_four_gap h
  omega

lemma block_indices_of_midpoint {i j l x y z : ℕ} (hxy : x ≤ y) (hyz : y ≤ z)
    (hmid : x + z = 2 * y)
    (hx : 4 * 4 ^ i < x ∧ x ≤ 5 * 4 ^ i)
    (hy : 4 * 4 ^ j < y ∧ y ≤ 5 * 4 ^ j)
    (hz : 4 * 4 ^ l < z ∧ z ≤ 5 * 4 ^ l) : i = j ∧ j = l := by
  have hij := blockIndex_le hxy hx.1 hy.2
  have hjl := blockIndex_le hyz hy.1 hz.2
  have he : j = l := by
    by_contra hn
    have hp := pow_four_gap (lt_of_le_of_ne hjl hn)
    omega
  subst l
  refine ⟨?_, rfl⟩
  by_contra hn
  have hp := pow_four_gap (lt_of_le_of_ne hij hn)
  omega

lemma shifted_blocks_free {k : ℕ} (hk : 3 ≤ k) (I : Finset ℕ) (B : ℕ → Finset ℕ)
    (hB : ∀ j, B j ⊆ Finset.Icc 1 (4 ^ j))
    (hf : ∀ j, (B j : Set ℕ).IsAPOfLengthFree k) :
    (I.biUnion (fun j => (B j).map (addLeftEmbedding (4 * 4 ^ j))) : Set ℕ).IsAPOfLengthFree k := by
  have hk' : 1 < k := by omega
  rw [apFree_iff hk']
  rintro ⟨a, d, hd, h⟩
  have hm (i : ℕ) (hi : i < k) : ∃ j, a + i * d ∈ (B j).map (addLeftEmbedding (4 * 4 ^ j)) := by
    obtain ⟨j, -, hji⟩ := Finset.mem_biUnion.mp (h i hi)
    exact ⟨j, hji⟩
  choose! J hJ using hm
  have hb (i : ℕ) (hi : i < k) :=
    mem_shiftBlock_bounds (hB (J i)) (hJ i hi)
  have htrip (i : ℕ) (hi : i + 2 < k) : J i = J (i + 1) ∧ J (i + 1) = J (i + 2) := by
    apply block_indices_of_midpoint (x := a + i * d)
      (y := a + (i + 1) * d) (z := a + (i + 2) * d)
    · simp only [Nat.add_mul, one_mul]; omega
    · simp only [Nat.add_mul, one_mul, two_mul]; omega
    · simp only [Nat.add_mul, one_mul, two_mul]; omega
    · exact hb i (by omega)
    · exact hb (i + 1) (by omega)
    · exact hb (i + 2) hi
  have hsame (i : ℕ) (hi : i < k) : J i = J 0 := by
    induction i with
    | zero => rfl
    | succ i ih =>
      have hi' : i < k := by omega
      apply Eq.trans _ (ih hi')
      by_cases ht : i + 2 < k
      · exact (htrip i ht).1.symm
      · have hprev := (htrip (i - 1) (by omega)).2.symm
        rwa [show i - 1 + 2 = i + 1 by omega, show i - 1 + 1 = i by omega] at hprev
  have ha : 4 * 4 ^ J 0 ≤ a := by simpa using (hb 0 (by omega)).1.le
  apply (apFree_iff hk').mp (hf (J 0))
  refine ⟨a - 4 * 4 ^ J 0, d, hd, fun i hi => ?_⟩
  have hm' := hJ i hi
  rw [hsame i hi] at hm'
  obtain ⟨b, hb', he⟩ := Finset.mem_map.mp hm'
  change 4 * 4 ^ J 0 + b = a + i * d at he
  rwa [show a - 4 * 4 ^ J 0 + i * d = b by omega]

lemma shiftBlocks_pairwiseDisjoint (I : Finset ℕ) (B : ℕ → Finset ℕ)
    (hB : ∀ j, B j ⊆ Finset.Icc 1 (4 ^ j)) :
    Set.PairwiseDisjoint (I : Set ℕ) (fun j => (B j).map (addLeftEmbedding (4 * 4 ^ j))) := by
  intro i _ j _ hne
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  have hi := mem_shiftBlock_bounds (hB i) hxi
  have hj := mem_shiftBlock_bounds (hB j) hxj
  exact hne (le_antisymm (blockIndex_le le_rfl hi.1 hj.2)
    (blockIndex_le le_rfl hj.1 hi.2))

lemma shiftBlock_reciprocal_lower {j : ℕ} {B : Finset ℕ}
    (hB : B ⊆ Finset.Icc 1 (4 ^ j)) :
    (B.card : ℝ) / (5 * 4 ^ j) ≤ ∑ x ∈ B.map (addLeftEmbedding (4 * 4 ^ j)), (x : ℝ)⁻¹ := by
  calc
    _ = ∑ _x ∈ B.map (addLeftEmbedding (4 * 4 ^ j)), (5 * (4 : ℝ) ^ j)⁻¹ := by
      simp [div_eq_mul_inv]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro x hx
      have hb := mem_shiftBlock_bounds hB hx
      apply inv_anti₀ (by exact_mod_cast (show 0 < x by omega))
      exact_mod_cast hb.2

lemma weighted_blockDensity_of_window {k : ℕ} (hk : 3 ≤ k)
    (hw : (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ S : Finset ℕ, (∀ x ∈ S, ∃ j ∈ Finset.Ico n (2 * n), 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j) → (S : Set ℕ).IsAPOfLengthFree k → (∑ x ∈ S, (x : ℝ)⁻¹) ≤ ε)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ j : ℕ in atTop, (j : ℝ) * ((r k (4 ^ j) : ℝ) / (4 : ℝ) ^ j) ≤ δ := by
  have hk' : 1 < k := by omega
  choose B hB hf hcard using fun t : ℕ => exists_maximizer hk' (4 ^ t)
  intro δ hδ
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hw (δ / 15) (by positivity))
  filter_upwards [eventually_ge_atTop (2 * max M 1)] with j hj
  let n := j / 2
  have hn : max M 1 ≤ n := by dsimp [n]; omega
  have hnj : 2 * n ≤ j := by dsimp [n]; omega
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hfactor : (j : ℝ) ≤ 3 * (n : ℝ) := by
    exact_mod_cast (show j ≤ 3 * n by dsimp [n] at *; omega)
  let I := Finset.Ico n (2 * n)
  let S := I.biUnion (fun t => (B t).map (addLeftEmbedding (4 * 4 ^ t)))
  have hS : ∀ x ∈ S, ∃ t ∈ I, 4 * 4 ^ t < x ∧ x ≤ 5 * 4 ^ t := by
    intro x hx
    obtain ⟨t, ht, hxt⟩ := Finset.mem_biUnion.mp hx
    exact ⟨t, ht, mem_shiftBlock_bounds (hB t) hxt⟩
  have hmass := hM n ((le_max_left _ _).trans hn) S hS (shifted_blocks_free hk I B hB hf)
  have hcardI : I.card = n := by
    dsimp [I]
    rw [Nat.card_Ico]
    omega
  have hlower : (n : ℝ) * (((r k (4 ^ j) : ℝ) / (4 : ℝ) ^ j) / 5) ≤ ∑ x ∈ S, (x : ℝ)⁻¹ := by
    calc
      _ = ∑ _t ∈ I, ((r k (4 ^ j) : ℝ) / (4 : ℝ) ^ j) / 5 := by simp [hcardI]
      _ ≤ ∑ t ∈ I, ∑ x ∈ (B t).map (addLeftEmbedding (4 * 4 ^ t)), (x : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro t ht
        have htj : t ≤ j := ((Finset.mem_Ico.mp ht).2.le).trans hnj
        calc
          _ ≤ ((r k (4 ^ t) : ℝ) / (4 : ℝ) ^ t) / 5 :=
            div_le_div_of_nonneg_right (blockDensity_antitone hk' htj) (by norm_num)
          _ = (B t).card / (5 * (4 : ℝ) ^ t) := by
            simp only [hcard, div_div, mul_comm (5 : ℝ)]
          _ ≤ _ := shiftBlock_reciprocal_lower (hB t)
      _ = _ := (Finset.sum_biUnion (shiftBlocks_pairwiseDisjoint I B hB)).symm
  have hc : 0 ≤ ((r k (4 ^ j) : ℝ) / (4 : ℝ) ^ j) := by positivity
  have hm := mul_le_mul_of_nonneg_right hfactor hc
  have hle := hlower.trans hmass
  linarith only [hm, hle]

lemma littleO_of_window {k : ℕ} (hk : 3 ≤ k) (hw : (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ S : Finset ℕ, (∀ x ∈ S, ∃ j ∈ Finset.Ico n (2 * n), 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j) → (S : Set ℕ).IsAPOfLengthFree k → (∑ x ∈ S, (x : ℝ)⁻¹) ≤ ε)) :
    (fun N => (r k N : ℝ)) =o[atTop] (fun N : ℕ => N / (N : ℝ).log) := by
  exact littleO_of_blockDensity (by omega) (weighted_blockDensity_of_window hk hw)

lemma r_two_le_one (N : ℕ) : r 2 N ≤ 1 := by
  unfold r Set.IsAPOfLengthFree.maxCard
  apply csSup_le
  · refine ⟨0, ∅, by simp, ?_, Finset.card_empty⟩
    intro T hT hAP
    have he : T = ∅ := Set.eq_empty_of_subset_empty (by simpa using hT)
    subst T
    exact (Set.not_isAPOfLength_empty (by decide) hAP).elim
  · rintro m ⟨S, -, hfree, rfl⟩
    by_contra! hc
    obtain ⟨a, ha, b, hb, hne⟩ := Finset.one_lt_card.mp hc
    have noPair {x y : ℕ} (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) : False := by
      have hs : ({x, y} : Set ℕ) ⊆ (S : Set ℕ) :=
        Set.insert_subset_iff.mpr ⟨hx, Set.singleton_subset_iff.mpr hy⟩
      exact (by decide : ¬ (2 : ℕ∞) ≤ 1) (hfree _ hs (Nat.isAPOfLength_pair hxy))
    exact (lt_or_gt_of_ne hne).elim (noPair ha hb) (noPair hb ha)

lemma two_littleO :
    (fun N => (r 2 N : ℝ)) =o[atTop] (fun N : ℕ => N / (N : ℝ).log) := by
  have hlog :
      Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hc : (fun _ : ℕ => (1 : ℝ)) =o[atTop] (fun N : ℕ => N / (N : ℝ).log) := by
    apply isLittleO_of_tendsto'
    · filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
      have hp : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      exact fun h => (div_pos (zero_lt_one.trans hp) (Real.log_pos hp)).ne' h |>.elim
    · simpa only [one_div, inv_div] using hlog
  apply IsBigO.trans_isLittleO _ hc
  apply IsBigO.of_bound 1
  exact Eventually.of_forall fun N => by simpa using (show (r 2 N : ℝ) ≤ 1 by
    exact_mod_cast r_two_le_one N)


/-- Reciprocal mass of 3-AP-free sets on windows of geometric blocks tends to zero. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ S : Finset ℕ,
    (∀ x ∈ S, ∃ j ∈ Finset.Ico n (2 * n), 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j) →
    (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < 3, a + i * d ∈ S) →
    (∑ x ∈ S, (x : ℝ)⁻¹) ≤ ε

/-- The same window decay for every progression length at least four. -/
def H2 : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ S : Finset ℕ,
    (∀ x ∈ S, ∃ j ∈ Finset.Ico n (2 * n), 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j) →
    (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
    (∑ x ∈ S, (x : ℝ)⁻¹) ≤ ε

theorem main : H1 → H2 → type_of% @Erdos142.erdos_142.variants.lower := by
  intro h1 h2 k hk
  rcases eq_or_lt_of_le (show 2 ≤ k by omega) with rfl | hk'
  · exact two_littleO
  have hw : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ S : Finset ℕ,
      (∀ x ∈ S, ∃ j ∈ Finset.Ico n (2 * n), 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j) →
      (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
      (∑ x ∈ S, (x : ℝ)⁻¹) ≤ ε := by
    rcases eq_or_lt_of_le (show 3 ≤ k by omega) with rfl | hk4
    · exact h1
    · exact h2 k (by omega)
  apply littleO_of_window (by omega)
  intro ε hε
  filter_upwards [hw ε hε] with n hn S hS hf
  exact hn S hS ((apFree_iff (by omega)).mp hf)

end OMA.R_Erdos142_erdos_142_variants_lower_R3
