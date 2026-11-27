import OMAReductions.R_Erdos687_erdos_687_parts_iii_R1_H2_R1

-- Step Erdos687.erdos_687.parts.iii.R1.H2.R1.H1: hypothesis H1 of reduction Erdos687.erdos_687.parts.iii.R1.H2.R1
-- Credit: @santiemanuel

/-!
# Upper Fundamental Lemma of the Shifted Sieve via Brun's Combinatorial Sieve

We prove `OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1.H1`: for every `δ > 0`, there exists
`s₀ ≥ 2` such that for every `s ≥ s₀`, all sufficiently large `z`, every `y ≥ z ^ s`, and every
choice of residue classes `a : ℕ → ℕ`, at most `(1 + δ / s ^ 3) * y * ∏_{p ≤ z} (1 - 1 / p)`
integers in `[1, y]` avoid every congruence `a p (mod p)` for primes `p ≤ z`.

The proof implements **Brun's combinatorial upper sieve**:
1. Partition the primes `p ≤ z` into doubly-exponential blocks `P_i = (cut i, cut (i - 1)]`
   with `cut i = min z (2 ^ (L / 2 ^ i))`, where `L = Nat.log 2 z + 1`.
2. Truncate inclusion-exclusion to subsets `D` satisfying `|D ∩ (P_1 ∪ ⋯ ∪ P_i)| ≤ 2 * b_i`
   with `b_i = b + K * i` and `b = (s - 16 * K - 4) / 8`. Induction on the number of blocks
   yields the pointwise upper bound (`brun_pointwise_upper`).
3. Apply the Chinese remainder theorem to count each progression in `[1, y]` within `± 1`
   (`crt_count_sub_div_le_one`), and bound the number of retained divisors via summation by parts
   (`brun_prod_le`).
4. Factor out the Euler-product tail on the first violated block and apply Rankin's trick
   together with `OMA.R_Erdos687_erdos_687_parts_iii_R1.sum_prime_inv_Ioc_le` to bound the
   truncation error exponentially in `b` uniformly for all `s ≥ s₀`.
-/

open Filter Finset Real

private lemma alternating_choose_sum {n : ℕ} (hn : 1 ≤ n) (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), (-1 : ℝ) ^ j * (n.choose j : ℝ) =
      (-1 : ℝ) ^ m * ((n - 1).choose m : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have hpas : n.choose (m + 1) = (n - 1).choose m + (n - 1).choose (m + 1) := by
      have h := Nat.choose_succ_succ (n - 1) m
      rw [Nat.succ_eq_add_one, Nat.sub_add_cancel hn] at h
      exact h
    have hpas_r : (n.choose (m + 1) : ℝ) = ((n - 1).choose m : ℝ) + ((n - 1).choose (m + 1) : ℝ) := by
      exact_mod_cast hpas
    rw [hpas_r, pow_succ (-1 : ℝ) m]
    ring

private lemma alternating_powerset_eq (B : Finset ℕ) (M : ℕ) :
    ∑ D ∈ B.powerset.filter (fun D => D.card ≤ M), (-1 : ℝ) ^ D.card =
      ∑ j ∈ Finset.range (M + 1), (-1 : ℝ) ^ j * (B.card.choose j : ℝ) := by
  have hpart : B.powerset.filter (fun D => D.card ≤ M) =
      (Finset.range (M + 1)).biUnion (fun j => B.powersetCard j) := by
    ext D
    simp only [mem_filter, mem_powerset, mem_biUnion, mem_range, mem_powersetCard]
    constructor
    · rintro ⟨hDB, hcard⟩
      exact ⟨D.card, by omega, hDB, rfl⟩
    · rintro ⟨j, hj, hDB, rfl⟩
      exact ⟨hDB, by omega⟩
  have hpw : (Finset.range (M + 1) : Set ℕ).PairwiseDisjoint (fun j => B.powersetCard j) := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro D hDi hDj
    have hi := (mem_powersetCard.mp hDi).2
    have hj := (mem_powersetCard.mp hDj).2
    exact hij (hi.symm.trans hj)
  rw [hpart, Finset.sum_biUnion hpw]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hconst : ∑ D ∈ B.powersetCard j, (-1 : ℝ) ^ D.card =
      ∑ _D ∈ B.powersetCard j, (-1 : ℝ) ^ j :=
    Finset.sum_congr rfl fun D hD => by rw [(mem_powersetCard.mp hD).2]
  rw [hconst, Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard, mul_comm]

private lemma icc_succ_eq_insert {a b : ℕ} (h : a ≤ b + 1) :
    Icc a (b + 1) = insert (b + 1) (Icc a b) := by
  ext x
  simp only [mem_Icc, mem_insert]
  omega

private def brunPredIco (Q : ℕ → Finset ℕ) (b : ℕ → ℕ) (i : ℕ) (D : Finset ℕ) : Prop :=
  ∀ j ∈ Ico 1 i, (D ∩ Q j).card ≤ 2 * b j

private instance instDecidableBrunPredIco (Q : ℕ → Finset ℕ) (b : ℕ → ℕ) (i : ℕ) :
    DecidablePred (brunPredIco Q b i) :=
  fun _ => Finset.decidableDforallFinset

private def brunPred (Q : ℕ → Finset ℕ) (b : ℕ → ℕ) (r : ℕ) (D : Finset ℕ) : Prop :=
  ∀ i ∈ Icc 1 r, (D ∩ Q i).card ≤ 2 * b i

private instance instDecidableBrunPred (Q : ℕ → Finset ℕ) (b : ℕ → ℕ) (r : ℕ) :
    DecidablePred (brunPred Q b r) :=
  fun _ => Finset.decidableDforallFinset

/-- Brun's combinatorial upper bound: for pairwise disjoint blocks `P 1, ..., P r` and
nondecreasing depths `b 1 ≤ b 2 ≤ ...`, restricting inclusion-exclusion to sets with
`|D ∩ (P 1 ∪ ⋯ ∪ P i)| ≤ 2 * b i` yields a pointwise upper bound on `1_{B = ∅}`. -/
private lemma brun_pointwise_upper (P : ℕ → Finset ℕ) (b : ℕ → ℕ)
    (hb_mono : ∀ i, 1 ≤ i → b i ≤ b (i + 1))
    (hdisj : ∀ i j, 1 ≤ i → 1 ≤ j → i ≠ j → Disjoint (P i) (P j)) :
    ∀ (r : ℕ) (B : Finset ℕ), B ⊆ (Icc 1 r).biUnion P →
      (if B = ∅ then (1 : ℝ) else 0) ≤
        ∑ D ∈ B.powerset.filter (brunPred (fun k => (Icc 1 k).biUnion P) b r),
          (-1 : ℝ) ^ D.card := by
  intro r
  induction r with
  | zero =>
    intro B hB
    have hBe : B = ∅ := by
      rw [Finset.Icc_eq_empty_of_lt (by norm_num : 0 < 1), Finset.biUnion_empty] at hB
      exact Finset.subset_empty.mp hB
    subst hBe
    have hfilt : (∅ : Finset ℕ).powerset.filter (brunPred (fun k => (Icc 1 k).biUnion P) b 0) = {∅} := by
      ext D
      simp [brunPred]
    rw [hfilt]
    simp
  | succ r ih =>
    intro B hB
    let Q : ℕ → Finset ℕ := fun k => (Icc 1 k).biUnion P
    have hQsucc : Q (r + 1) = Q r ∪ P (r + 1) := by
      dsimp [Q]
      rw [icc_succ_eq_insert (by omega : 1 ≤ r + 1), Finset.biUnion_insert,
        Finset.union_comm]
    have hQdisj : Disjoint (Q r) (P (r + 1)) := by
      rw [Finset.disjoint_left]
      intro x hxQ hxP
      rw [mem_biUnion] at hxQ
      obtain ⟨j, hj, hxj⟩ := hxQ
      have hj_mem := mem_Icc.mp hj
      exact Finset.disjoint_left.mp (hdisj j (r + 1) hj_mem.1 (by omega) (by omega)) hxj hxP
    let B' := B ∩ Q r
    let B₁ := B ∩ P (r + 1)
    have hB_union : B = B' ∪ B₁ := by
      ext x
      simp only [B', B₁, mem_union, mem_inter]
      constructor
      · intro hxB
        have hxQ := hB hxB
        change x ∈ Q (r + 1) at hxQ
        rw [hQsucc, mem_union] at hxQ
        rcases hxQ with h | h
        · exact Or.inl ⟨hxB, h⟩
        · exact Or.inr ⟨hxB, h⟩
      · rintro (⟨hxB, _⟩ | ⟨hxB, _⟩) <;> exact hxB
    by_cases hB₁_empty : B₁ = ∅
    · have hBeq : B = B' := by rw [hB_union, hB₁_empty, Finset.union_empty]
      have hB_sub : B ⊆ Q r := by
        rw [hBeq]
        exact Finset.inter_subset_right
      have hfilt_eq :
          B.powerset.filter (brunPred Q b (r + 1)) =
          B.powerset.filter (brunPred Q b r) := by
        ext D
        simp only [mem_filter, mem_powerset, brunPred]
        constructor
        · rintro ⟨hDB, hall⟩
          exact ⟨hDB, fun i hi => hall i (mem_Icc.mpr ⟨(mem_Icc.mp hi).1, (mem_Icc.mp hi).2.trans (Nat.le_succ r)⟩)⟩
        · rintro ⟨hDB, hall⟩
          refine ⟨hDB, fun i hi => ?_⟩
          have hi' := mem_Icc.mp hi
          by_cases hir : i ≤ r
          · exact hall i (mem_Icc.mpr ⟨hi'.1, hir⟩)
          · have hieq : i = r + 1 := by omega
            subst hieq
            have hDsub : D ⊆ Q r := hDB.trans hB_sub
            have hDQ : D ∩ Q (r + 1) = D := by
              rw [hQsucc]
              exact Finset.inter_eq_left.mpr (hDsub.trans Finset.subset_union_left)
            rw [hDQ]
            by_cases hr0 : r = 0
            · subst hr0
              have hDe : D = ∅ := by
                dsimp [Q] at hDsub
                rw [Finset.Icc_eq_empty_of_lt (by norm_num : 0 < 1), Finset.biUnion_empty] at hDsub
                exact Finset.subset_empty.mp hDsub
              subst hDe
              simp only [Finset.card_empty]
              exact Nat.zero_le _
            · have hr1 : 1 ≤ r := by omega
              have hDr := hall r (mem_Icc.mpr ⟨hr1, le_rfl⟩)
              rw [Finset.inter_eq_left.mpr hDsub] at hDr
              have hbm := hb_mono r hr1
              omega
      change _ ≤ ∑ D ∈ B.powerset.filter (brunPred Q b (r + 1)),
          (-1 : ℝ) ^ D.card
      rw [hfilt_eq]
      exact ih B hB_sub
    · have hB₁_ne : B₁.Nonempty := Finset.nonempty_iff_ne_empty.mpr hB₁_empty
      have hB_ne : B ≠ ∅ := by
        intro h
        obtain ⟨x, hx⟩ := hB₁_ne
        simp [B₁, h] at hx
      rw [if_neg hB_ne]
      let M := 2 * b (r + 1)
      have hM_even : (-1 : ℝ) ^ M = 1 := by
        dsimp [M]
        rw [pow_mul]
        norm_num
      let F_prev := B'.powerset.filter (brunPred Q b r)
      let F_full := B.powerset.filter (brunPred Q b (r + 1))
      let S_sig := F_prev.sigma fun D' => B₁.powerset.filter (fun D₁ => D₁.card ≤ M - D'.card)
      have hD'_le_M : ∀ D' ∈ F_prev, D'.card ≤ M := by
        intro D' hD'
        have hD'sub : D' ⊆ Q r := (mem_powerset.mp (mem_filter.mp hD').1).trans Finset.inter_subset_right
        by_cases hr0 : r = 0
        · subst hr0
          dsimp [Q] at hD'sub
          rw [Finset.Icc_eq_empty_of_lt (by norm_num : 0 < 1), Finset.biUnion_empty] at hD'sub
          rw [Finset.subset_empty.mp hD'sub]
          simp [M]
        · have hr1 : 1 ≤ r := by omega
          have h := (mem_filter.mp hD').2 r (mem_Icc.mpr ⟨hr1, le_rfl⟩)
          rw [Finset.inter_eq_left.mpr hD'sub] at h
          have hbm := hb_mono r hr1
          dsimp [M]
          omega
      have hbij : ∑ D ∈ F_full, (-1 : ℝ) ^ D.card =
          ∑ x ∈ S_sig, (-1 : ℝ) ^ (x.1 ∪ x.2).card := by
        refine (Finset.sum_nbij (fun x => x.1 ∪ x.2) ?_ ?_ ?_ ?_).symm
        · intro x hx
          rw [mem_sigma] at hx
          obtain ⟨hD', hD₁⟩ := hx
          have hD'p := mem_filter.mp hD'
          have hD₁p := mem_filter.mp hD₁
          have hD'B' : x.1 ⊆ B' := mem_powerset.mp hD'p.1
          have hD₁B₁ : x.2 ⊆ B₁ := mem_powerset.mp hD₁p.1
          have hdisj_x : Disjoint x.1 x.2 :=
            Disjoint.mono (hD'B'.trans Finset.inter_subset_right)
              (hD₁B₁.trans Finset.inter_subset_right) hQdisj
          refine mem_filter.mpr ⟨mem_powerset.mpr ?_, fun i hi => ?_⟩
          · rw [hB_union]
            exact Finset.union_subset_union hD'B' hD₁B₁
          · have hi' := mem_Icc.mp hi
            by_cases hir : i ≤ r
            · have hQi_sub : Q i ⊆ Q r :=
                Finset.biUnion_subset_biUnion_of_subset_left P
                  (Finset.Icc_subset_Icc_right hir)
              have hdisj_2 : Disjoint x.2 (Q i) :=
                (Disjoint.mono (hD₁B₁.trans Finset.inter_subset_right) hQi_sub hQdisj.symm)
              have hinter : (x.1 ∪ x.2) ∩ Q i = x.1 ∩ Q i := by
                rw [Finset.union_inter_distrib_right, Finset.disjoint_iff_inter_eq_empty.mp hdisj_2,
                  Finset.union_empty]
              rw [hinter]
              exact hD'p.2 i (mem_Icc.mpr ⟨hi'.1, hir⟩)
            · have hieq : i = r + 1 := by omega
              subst hieq
              have hsub_Q : x.1 ∪ x.2 ⊆ Q (r + 1) := by
                rw [hQsucc]
                exact Finset.union_subset_union (hD'B'.trans Finset.inter_subset_right)
                  (hD₁B₁.trans Finset.inter_subset_right)
              rw [Finset.inter_eq_left.mpr hsub_Q, Finset.card_union_of_disjoint hdisj_x]
              have h1 := hD'_le_M x.1 hD'
              have h2 : x.2.card ≤ M - x.1.card := hD₁p.2
              change x.1.card + x.2.card ≤ M
              omega
        · intro x hx y hy hxy
          rw [mem_coe, mem_sigma] at hx hy
          have hx1 : x.1 ⊆ Q r := (mem_powerset.mp (mem_filter.mp hx.1).1).trans Finset.inter_subset_right
          have hx2 : x.2 ⊆ P (r + 1) := (mem_powerset.mp (mem_filter.mp hx.2).1).trans Finset.inter_subset_right
          have hy1 : y.1 ⊆ Q r := (mem_powerset.mp (mem_filter.mp hy.1).1).trans Finset.inter_subset_right
          have hy2 : y.2 ⊆ P (r + 1) := (mem_powerset.mp (mem_filter.mp hy.2).1).trans Finset.inter_subset_right
          have heq1 : x.1 = y.1 := by
            have := congrArg (· ∩ Q r) hxy
            simpa only [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hx1,
              Finset.inter_eq_left.mpr hy1,
              Finset.disjoint_iff_inter_eq_empty.mp (Disjoint.mono_left hx2 hQdisj.symm),
              Finset.disjoint_iff_inter_eq_empty.mp (Disjoint.mono_left hy2 hQdisj.symm),
              Finset.union_empty] using this
          have heq2 : x.2 = y.2 := by
            have := congrArg (· ∩ P (r + 1)) hxy
            simpa only [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hx2,
              Finset.inter_eq_left.mpr hy2,
              Finset.disjoint_iff_inter_eq_empty.mp (Disjoint.mono_left hx1 hQdisj),
              Finset.disjoint_iff_inter_eq_empty.mp (Disjoint.mono_left hy1 hQdisj),
              Finset.empty_union] using this
          exact Sigma.ext heq1 (heq_of_eq heq2)
        · intro D hD
          rw [mem_coe] at hD
          have hDp := mem_filter.mp hD
          have hDB : D ⊆ B := mem_powerset.mp hDp.1
          let D' := D ∩ Q r
          let D₁ := D ∩ P (r + 1)
          have hD_eq : D' ∪ D₁ = D := by
            ext z
            simp only [D', D₁, mem_union, mem_inter]
            constructor
            · rintro (⟨hz, _⟩ | ⟨hz, _⟩) <;> exact hz
            · intro hz
              have hzQ : z ∈ Q (r + 1) := hB (hDB hz)
              rw [hQsucc, mem_union] at hzQ
              rcases hzQ with h | h
              · exact Or.inl ⟨hz, h⟩
              · exact Or.inr ⟨hz, h⟩
          have hD'mem : D' ∈ F_prev := by
            refine mem_filter.mpr ⟨mem_powerset.mpr (Finset.inter_subset_inter_right hDB), fun i hi => ?_⟩
            have hi' := mem_Icc.mp hi
            have hQi_sub : Q i ⊆ Q r :=
              Finset.biUnion_subset_biUnion_of_subset_left P (Finset.Icc_subset_Icc_right hi'.2)
            have hinter : D' ∩ Q i = D ∩ Q i := by
              dsimp [D']
              rw [Finset.inter_assoc, Finset.inter_eq_right.mpr hQi_sub]
            rw [hinter]
            exact hDp.2 i (mem_Icc.mpr ⟨hi'.1, hi'.2.trans (Nat.le_succ r)⟩)
          have hD₁mem : D₁ ∈ B₁.powerset.filter (fun E => E.card ≤ M - D'.card) := by
            refine mem_filter.mpr ⟨mem_powerset.mpr (Finset.inter_subset_inter_right hDB), ?_⟩
            have hdisj_D : Disjoint D' D₁ :=
              Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right hQdisj
            have htot := hDp.2 (r + 1) (mem_Icc.mpr ⟨by omega, le_rfl⟩)
            have hDQ : D ∩ Q (r + 1) = D := Finset.inter_eq_left.mpr (hDB.trans hB)
            rw [hDQ, ← hD_eq, Finset.card_union_of_disjoint hdisj_D] at htot
            change D₁.card ≤ M - D'.card
            dsimp [M]
            omega
          exact ⟨⟨D', D₁⟩, mem_coe.mpr (mem_sigma.mpr ⟨hD'mem, hD₁mem⟩), hD_eq⟩
        · intro _ _
          rfl
      change 0 ≤ ∑ D ∈ F_full, (-1 : ℝ) ^ D.card
      rw [hbij, Finset.sum_sigma]
      refine Finset.sum_nonneg fun D' hD' => ?_
      have hD'sub : D' ⊆ Q r := (mem_powerset.mp (mem_filter.mp hD').1).trans Finset.inter_subset_right
      have hfactor : ∑ D₁ ∈ B₁.powerset.filter (fun E => E.card ≤ M - D'.card),
          (-1 : ℝ) ^ (D' ∪ D₁).card =
          (-1 : ℝ) ^ D'.card *
            ∑ D₁ ∈ B₁.powerset.filter (fun E => E.card ≤ M - D'.card), (-1 : ℝ) ^ D₁.card := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun D₁ hD₁ => ?_
        have hD₁sub : D₁ ⊆ P (r + 1) :=
          (mem_powerset.mp (mem_filter.mp hD₁).1).trans Finset.inter_subset_right
        have hdisj_D : Disjoint D' D₁ := Disjoint.mono hD'sub hD₁sub hQdisj
        rw [Finset.card_union_of_disjoint hdisj_D, pow_add]
      rw [hfactor, alternating_powerset_eq,
        alternating_choose_sum (Finset.card_pos.mpr hB₁_ne), ← mul_assoc, ← pow_add,
        Nat.add_sub_of_le (hD'_le_M D' hD'), hM_even]
      have hnn : (0 : ℝ) ≤ ((B₁.card - 1).choose (M - D'.card) : ℝ) := Nat.cast_nonneg _
      linarith

/-- Counting elements of `[1, y]` in a fixed residue class modulo `d > 0` has error at most `1`. -/
private lemma count_modEq_Icc_error {d : ℕ} (hd : 0 < d) (k y : ℕ) :
    |(((Icc 1 y).filter fun m => m ≡ k [MOD d]).card : ℝ) - (y : ℝ) / (d : ℝ)| ≤ 1 := by
  let r := k % d
  let r' := if r = 0 then d else r
  have hr_lt : r < d := Nat.mod_lt k hd
  have hr'1 : 1 ≤ r' := by
    dsimp [r', r]
    split_ifs <;> omega
  have hr'd : r' ≤ d := by
    dsimp [r', r]
    split_ifs <;> omega
  have hr'mod : r' % d = r := by
    dsimp [r', r]
    split_ifs with h
    · rw [Nat.mod_self, h]
    · exact Nat.mod_eq_of_lt hr_lt
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  by_cases hyr : y < r'
  · have hemp : ((Icc 1 y).filter fun m => m ≡ k [MOD d]) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro m hm
      rw [mem_filter, mem_Icc] at hm
      have hmod : m % d = r := hm.2
      have hm_lt : m < d := by omega
      have hmr : m = r := by rwa [Nat.mod_eq_of_lt hm_lt] at hmod
      dsimp [r'] at hyr
      split_ifs at hyr with h0
      · omega
      · omega
    rw [hemp, Finset.card_empty, Nat.cast_zero, zero_sub, abs_neg,
      abs_of_nonneg (by positivity)]
    rw [div_le_one hd_pos]
    exact_mod_cast (show y ≤ d by omega)
  · push Not at hyr
    let q := (y - r') / d
    have hcard : ((Icc 1 y).filter fun m => m ≡ k [MOD d]).card = q + 1 := by
      have himg : ((Icc 1 y).filter fun m => m ≡ k [MOD d]) =
          (Finset.range (q + 1)).image (fun j => j * d + r') := by
        ext m
        simp only [mem_filter, mem_Icc, mem_image, mem_range]
        constructor
        · rintro ⟨⟨hm1, hmy⟩, hmod⟩
          have hmd : m % d = r := hmod
          have hmr' : r' ≤ m := by
            by_contra hlt
            push Not at hlt
            have hm_lt_d : m < d := by omega
            have := Nat.mod_eq_of_lt hm_lt_d
            dsimp [r'] at hlt
            split_ifs at hlt with h0 <;> omega
          have hdvd : d ∣ m - r' := by
            have h1 : m ≡ r' [MOD d] := hmod.trans (Nat.ModEq.symm (by
              change r' % d = k % d
              exact hr'mod))
            exact (Nat.modEq_iff_dvd' hmr').mp h1.symm
          obtain ⟨j, hj⟩ := hdvd
          have hmeq : j * d + r' = m := by
            rw [Nat.mul_comm]
            omega
          refine ⟨j, ?_, hmeq⟩
          have hj_le : j ≤ q := by
            dsimp [q]
            exact (Nat.le_div_iff_mul_le hd).mpr (by omega)
          omega
        · rintro ⟨j, hj, rfl⟩
          have hj_le : j ≤ q := by omega
          have hmul : j * d ≤ y - r' := by
            have hqmul : q * d ≤ y - r' := Nat.div_mul_le_self (y - r') d
            exact (Nat.mul_le_mul_right d hj_le).trans hqmul
          refine ⟨⟨by omega, by omega⟩, ?_⟩
          change (j * d + r') % d = k % d
          rw [Nat.mul_add_mod_self_right, hr'mod]
      rw [himg, Finset.card_image_of_injective _ (fun j₁ j₂ h => by
        have := Nat.add_right_cancel h
        exact Nat.eq_of_mul_eq_mul_right hd this), Finset.card_range]
    rw [hcard, abs_le]
    have hlo_nat : q * d ≤ y := (Nat.div_mul_le_self (y - r') d).trans (Nat.sub_le y r')
    have hhi_nat : y < (q + 2) * d := by
      have hlt : y - r' < (q + 1) * d := by
        dsimp [q]
        rw [Nat.add_mul, Nat.one_mul]
        have hdm : ((y - r') / d) * d + (y - r') % d = y - r' := by
          rw [Nat.mul_comm]
          exact Nat.div_add_mod (y - r') d
        have := Nat.mod_lt (y - r') hd
        omega
      rw [show q + 2 = (q + 1) + 1 by omega, Nat.add_mul, Nat.one_mul]
      omega
    have hlo : (q : ℝ) ≤ (y : ℝ) / (d : ℝ) := by
      rw [le_div_iff₀ hd_pos]
      exact_mod_cast hlo_nat
    have hhi : (y : ℝ) / (d : ℝ) ≤ (q : ℝ) + 2 := by
      rw [div_le_iff₀ hd_pos]
      have : (y : ℝ) < ((q + 2 : ℕ) : ℝ) * (d : ℝ) := by exact_mod_cast hhi_nat
      push_cast at this
      linarith
    push_cast
    constructor <;> linarith

private lemma finset_prod_dvd_of_nat_coprime {D : Finset ℕ} {n : ℕ}
    (hcop : Set.Pairwise (D : Set ℕ) (Function.onFun Nat.Coprime id))
    (hdvd : ∀ p ∈ D, p ∣ n) : (∏ p ∈ D, p) ∣ n := by
  induction D using Finset.cons_induction with
  | empty => simp
  | cons a s has ih =>
    rw [Finset.prod_cons]
    have hcop_s : Set.Pairwise (s : Set ℕ) (Function.onFun Nat.Coprime id) :=
      hcop.mono fun x hx => Finset.mem_coe.mpr (Finset.mem_cons_of_mem (Finset.mem_coe.mp hx))
    have hs_dvd : (∏ p ∈ s, p) ∣ n := ih hcop_s (fun p hp => hdvd p (Finset.mem_cons_of_mem hp))
    have ha_dvd : a ∣ n := hdvd a (Finset.mem_cons_self a s)
    have ha_cop : Nat.Coprime a (∏ p ∈ s, p) :=
      Nat.Coprime.prod_right fun p hp =>
        hcop (Finset.mem_coe.mpr (Finset.mem_cons_self a s))
          (Finset.mem_coe.mpr (Finset.mem_cons_of_mem hp))
          (fun heq => has (heq ▸ hp))
    exact ha_cop.mul_dvd_of_dvd_of_dvd ha_dvd hs_dvd

/-- Chinese remainder theorem count of simultaneous residue hits in `[1, y]`. -/
private lemma crt_count_sub_div_le_one {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime)
    (a : ℕ → ℕ) (y : ℕ) :
    |(((Icc 1 y).filter fun m => ∀ p ∈ D, m ≡ a p [MOD p]).card : ℝ) -
      (y : ℝ) * (∏ p ∈ D, (p : ℝ)⁻¹)| ≤ 1 := by
  let d := ∏ p ∈ D, p
  have hd_pos : 0 < d := Finset.prod_pos fun p hp => (hD p hp).pos
  have hs : ∀ p ∈ D, id p ≠ 0 := fun p hp => (hD p hp).ne_zero
  have pp : Set.Pairwise (D : Set ℕ) (Function.onFun Nat.Coprime id) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (hD p hp) (hD q hq)).2 hpq
  let k := Nat.chineseRemainderOfFinset a id D hs pp
  have hfilt : ((Icc 1 y).filter fun m => ∀ p ∈ D, m ≡ a p [MOD p]) =
      ((Icc 1 y).filter fun m => m ≡ (k : ℕ) [MOD d]) := by
    ext m
    simp only [mem_filter]
    refine and_congr_right fun _ => ?_
    constructor
    · intro hm
      have hmk : ∀ p ∈ D, m ≡ (k : ℕ) [MOD p] := fun p hp => (hm p hp).trans (k.2 p hp).symm
      rcases le_total (k : ℕ) m with hle | hle
      · apply Nat.ModEq.symm
        apply (Nat.modEq_iff_dvd' hle).mpr
        refine finset_prod_dvd_of_nat_coprime pp fun p hp => ?_
        exact (Nat.modEq_iff_dvd' hle).mp (hmk p hp).symm
      · apply (Nat.modEq_iff_dvd' hle).mpr
        refine finset_prod_dvd_of_nat_coprime pp fun p hp => ?_
        exact (Nat.modEq_iff_dvd' hle).mp (hmk p hp)
    · intro hmd p hp
      have hpd : p ∣ d := Finset.dvd_prod_of_mem id hp
      exact (hmd.of_dvd hpd).trans (k.2 p hp)
  have hprod : (y : ℝ) * (∏ p ∈ D, (p : ℝ)⁻¹) = (y : ℝ) / (d : ℝ) := by
    rw [div_eq_mul_inv]
    congr 1
    dsimp [d]
    rw [Nat.cast_prod, Finset.prod_inv_distrib]
  rw [hfilt, hprod]
  exact count_modEq_Icc_error hd_pos k y

private lemma eulerProd_eq_powerset_sum (S : Finset ℕ) :
    ∏ p ∈ S, (1 - (p : ℝ)⁻¹) =
      ∑ D ∈ S.powerset, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹) := by
  have h1 : ∏ p ∈ S, (1 - (p : ℝ)⁻¹) = ∏ p ∈ S, (-(p : ℝ)⁻¹ + 1) :=
    Finset.prod_congr rfl fun _ _ => by ring
  rw [h1, Finset.prod_add]
  refine Finset.sum_congr rfl fun D _ => ?_
  rw [Finset.prod_const_one, mul_one, Finset.prod_neg]

private lemma eulerProd_pos_finset (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    0 < ∏ p ∈ S, (1 - (p : ℝ)⁻¹) := by
  apply Finset.prod_pos
  intro p hp
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hS p hp).two_le
  have hinv : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp2
  linarith

private lemma eulerProd_ge_inv {z : ℕ} (hz : 1 ≤ z) :
    (z : ℝ)⁻¹ ≤ ∏ p ∈ (range (z + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹) := by
  have htele : ∏ n ∈ Icc 2 z, (1 - (n : ℝ)⁻¹) = (z : ℝ)⁻¹ := by
    induction z, hz using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      rw [Finset.prod_Icc_succ_top (by omega : 2 ≤ m + 1), ih]
      have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
      have hm1_ne : ((m + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show m + 1 ≠ 0 by omega)
      push_cast
      field_simp
      ring
  rw [← htele]
  have hsub : (range (z + 1)).filter Nat.Prime ⊆ Icc 2 z := by
    intro p hp
    rw [mem_filter, mem_range] at hp
    exact mem_Icc.mpr ⟨hp.2.two_le, by omega⟩
  rw [← Finset.prod_sdiff hsub]
  have hle1 : ∏ n ∈ Icc 2 z \ (range (z + 1)).filter Nat.Prime, (1 - (n : ℝ)⁻¹) ≤ 1 := by
    apply Finset.prod_le_one
    · intro n hn
      have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (mem_Icc.mp (mem_sdiff.mp hn).1).1
      have hinv : (n : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hn2
      linarith
    · intro n hn
      have hn0 : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
      linarith
  have hpos : 0 ≤ ∏ p ∈ (range (z + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹) :=
    (eulerProd_pos_finset _ fun _ hp => (mem_filter.mp hp).2).le
  calc
    (∏ n ∈ Icc 2 z \ (range (z + 1)).filter Nat.Prime, (1 - (n : ℝ)⁻¹)) *
        (∏ p ∈ (range (z + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹))
        ≤ 1 * (∏ p ∈ (range (z + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)) :=
      mul_le_mul_of_nonneg_right hle1 hpos
    _ = _ := one_mul _

private lemma one_sub_inv_inv_le_exp_two {p : ℕ} (hp : 2 ≤ p) :
    (1 - (p : ℝ)⁻¹)⁻¹ ≤ Real.exp (2 * (p : ℝ)⁻¹) := by
  set u : ℝ := (p : ℝ)⁻¹
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hu_pos : 0 < u := inv_pos.mpr hp_pos
  have hu_le : u ≤ 1 / 2 := by
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    simpa [u, one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hp2
  have h1u_pos : 0 < 1 - u := by linarith
  have hquad : 1 ≤ (1 - u) * (1 + 2 * u) := by nlinarith
  have hexp : 1 + 2 * u ≤ Real.exp (2 * u) := by linarith [Real.add_one_le_exp (2 * u)]
  have hmul : 1 ≤ (1 - u) * Real.exp (2 * u) :=
    hquad.trans (mul_le_mul_of_nonneg_left hexp h1u_pos.le)
  rw [inv_eq_one_div, div_le_iff₀ h1u_pos]
  linarith

/-- Rankin's trick bound on the tail of reciprocal products over subsets of size `≥ m`. -/
private lemma brun_tail_bound (Q : Finset ℕ) (m : ℕ) :
    ∑ D ∈ Q.powerset.filter (fun D => m ≤ D.card), (∏ p ∈ D, (p : ℝ)⁻¹) ≤
      Real.exp (-(m : ℝ) + Real.exp 1 * ∑ p ∈ Q, (p : ℝ)⁻¹) := by
  have h1 : ∑ D ∈ Q.powerset.filter (fun D => m ≤ D.card), (∏ p ∈ D, (p : ℝ)⁻¹) ≤
      Real.exp (-(m : ℝ)) *
        ∑ D ∈ Q.powerset, (∏ p ∈ D, (Real.exp 1 * (p : ℝ)⁻¹)) := by
    rw [Finset.mul_sum]
    calc
      ∑ D ∈ Q.powerset.filter (fun D => m ≤ D.card), (∏ p ∈ D, (p : ℝ)⁻¹)
          ≤ ∑ D ∈ Q.powerset.filter (fun D => m ≤ D.card),
              Real.exp (-(m : ℝ)) * (∏ p ∈ D, (Real.exp 1 * (p : ℝ)⁻¹)) := by
        refine Finset.sum_le_sum fun D hD => ?_
        have hmD : (m : ℝ) ≤ (D.card : ℝ) := by exact_mod_cast (mem_filter.mp hD).2
        rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_nat_mul, mul_one,
          ← mul_assoc, ← Real.exp_add]
        have hexp_ge1 : (1 : ℝ) ≤ Real.exp (-(m : ℝ) + (D.card : ℝ)) :=
          Real.one_le_exp (by linarith)
        have hprod_nn : 0 ≤ ∏ p ∈ D, (p : ℝ)⁻¹ := Finset.prod_nonneg fun _ _ => by positivity
        calc
          ∏ p ∈ D, (p : ℝ)⁻¹ = 1 * ∏ p ∈ D, (p : ℝ)⁻¹ := (one_mul _).symm
          _ ≤ Real.exp (-(m : ℝ) + (D.card : ℝ)) * ∏ p ∈ D, (p : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_right hexp_ge1 hprod_nn
      _ ≤ ∑ D ∈ Q.powerset, Real.exp (-(m : ℝ)) * (∏ p ∈ D, (Real.exp 1 * (p : ℝ)⁻¹)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => ?_
        positivity
  have h2 : ∑ D ∈ Q.powerset, (∏ p ∈ D, (Real.exp 1 * (p : ℝ)⁻¹)) =
      ∏ p ∈ Q, (1 + Real.exp 1 * (p : ℝ)⁻¹) := by
    have hadd := Finset.prod_add (fun p : ℕ => Real.exp 1 * (p : ℝ)⁻¹) (fun _ => (1 : ℝ)) Q
    have hcomm : ∏ p ∈ Q, (1 + Real.exp 1 * (p : ℝ)⁻¹) =
        ∏ p ∈ Q, (Real.exp 1 * (p : ℝ)⁻¹ + 1) :=
      Finset.prod_congr rfl fun _ _ => add_comm _ _
    rw [hcomm, hadd]
    refine Finset.sum_congr rfl fun D _ => ?_
    rw [Finset.prod_const_one, mul_one]
  have h3 : ∏ p ∈ Q, (1 + Real.exp 1 * (p : ℝ)⁻¹) ≤
      Real.exp (Real.exp 1 * ∑ p ∈ Q, (p : ℝ)⁻¹) := by
    rw [Finset.mul_sum, Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p _; positivity
    · intro p _; linarith [Real.add_one_le_exp (Real.exp 1 * (p : ℝ)⁻¹)]
  calc
    ∑ D ∈ Q.powerset.filter (fun D => m ≤ D.card), (∏ p ∈ D, (p : ℝ)⁻¹)
        ≤ Real.exp (-(m : ℝ)) * Real.exp (Real.exp 1 * ∑ p ∈ Q, (p : ℝ)⁻¹) :=
      h1.trans (mul_le_mul_of_nonneg_left (h2.le.trans h3) (by positivity))
    _ = Real.exp (-(m : ℝ) + Real.exp 1 * ∑ p ∈ Q, (p : ℝ)⁻¹) := (Real.exp_add _ _).symm

/-- Distinct finite sets of primes have distinct products. -/
private lemma prime_finset_prod_injOn (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Set.InjOn (fun D : Finset ℕ => ∏ p ∈ D, p) (P.powerset : Set (Finset ℕ)) := by
  intro D₁ hD₁ D₂ hD₂ heq
  have hD₁p : ∀ p ∈ D₁, p.Prime := fun p hp => hP p (mem_powerset.mp (mem_coe.mp hD₁) hp)
  have hD₂p : ∀ p ∈ D₂, p.Prime := fun p hp => hP p (mem_powerset.mp (mem_coe.mp hD₂) hp)
  dsimp only at heq
  ext p
  constructor
  · intro hp
    have hdvd : p ∣ ∏ q ∈ D₂, q := by
      rw [← heq]
      exact Finset.dvd_prod_of_mem id hp
    obtain ⟨q, hq, hpq⟩ := ((hD₁p p hp).prime.dvd_finsetProd_iff id).mp hdvd
    have hpeq : p = q := ((hD₂p q hq).eq_one_or_self_of_dvd p hpq).resolve_left (hD₁p p hp).ne_one
    rwa [hpeq]
  · intro hp
    have hdvd : p ∣ ∏ q ∈ D₁, q := by
      rw [heq]
      exact Finset.dvd_prod_of_mem id hp
    obtain ⟨q, hq, hpq⟩ := ((hD₂p p hp).prime.dvd_finsetProd_iff id).mp hdvd
    have hpeq : p = q := ((hD₁p q hq).eq_one_or_self_of_dvd p hpq).resolve_left (hD₂p p hp).ne_one
    rwa [hpeq]

/-- Summation by parts bound for Brun's dyadic block exponents. -/
private lemma brun_dyadic_weight_bound (b K : ℕ) :
    ∀ r : ℕ, 1 ≤ r →
      ((2 * b + 2 * K * r : ℝ) / (2 : ℝ) ^ (r - 1)) +
        ∑ i ∈ Icc 1 (r - 1), ((2 * b + 2 * K * i : ℝ) / (2 : ℝ) ^ i) =
      (2 * b + 4 * K : ℝ) - (2 * K : ℝ) / (2 : ℝ) ^ (r - 1) := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base =>
    simp
    ring
  | succ m hm ih =>
    have hm1 : 1 ≤ m := hm
    have hsub : m + 1 - 1 = m := by omega
    rw [hsub]
    have hIcc : Icc 1 m = insert m (Icc 1 (m - 1)) := by
      ext i
      simp only [mem_Icc, mem_insert]
      omega
    have hnotmem : m ∉ Icc 1 (m - 1) := by
      simp only [mem_Icc]
      omega
    rw [hIcc, Finset.sum_insert hnotmem]
    have hpow : (2 : ℝ) ^ m = 2 * (2 : ℝ) ^ (m - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hm1]
    have hsum_eq : ∑ i ∈ Icc 1 (m - 1), ((2 * b + 2 * K * i : ℝ) / (2 : ℝ) ^ i) =
        (2 * b + 4 * K : ℝ) - (2 * K : ℝ) / (2 : ℝ) ^ (m - 1) -
          ((2 * b + 2 * K * m : ℝ) / (2 : ℝ) ^ (m - 1)) := by
      linarith
    rw [hsum_eq, hpow]
    have h2m : (2 : ℝ) ^ (m - 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

private lemma geom_half_sum_le_one (r : ℕ) :
    ∑ i ∈ Icc 1 r, ((1 / 2 : ℝ) ^ i) ≤ 1 := by
  have heq : ∀ n : ℕ, ∑ i ∈ Icc 1 n, ((1 / 2 : ℝ) ^ i) = 1 - (1 / 2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), ih, pow_succ]
      ring
  rw [heq r]
  have hnn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ r := by positivity
  linarith

private lemma pow_four_div_le_exp {x : ℝ} (hx : 0 ≤ x) :
    x ^ 4 / 256 ≤ Real.exp x := by
  have h1 : x / 4 ≤ 1 + x / 4 := by linarith
  have h2 : 1 + x / 4 ≤ Real.exp (x / 4) := by linarith [Real.add_one_le_exp (x / 4)]
  have h3 : (x / 4) ^ 4 ≤ (Real.exp (x / 4)) ^ 4 :=
    pow_le_pow_left₀ (by positivity) (h1.trans h2) 4
  rw [← Real.exp_nat_mul] at h3
  have hexp : (4 : ℕ) * (x / 4) = x := by push_cast; ring
  rw [hexp] at h3
  have hpow : (x / 4) ^ 4 = x ^ 4 / 256 := by ring
  rwa [hpow] at h3

/-- Reciprocal prime sum over `(cut, z]` for Brun's doubly-exponential cutoff `cut i`. -/
private lemma brun_block_recip_sum_le {z i : ℕ} (hz : 16 ≤ z) (hi : 1 ≤ i) :
    let L := Nat.log 2 z + 1
    let c := min z (2 ^ (L / 2 ^ i))
    ∑ q ∈ (Ioc c z).filter Nat.Prime, (q : ℝ)⁻¹ ≤ 18 + 2 * (i : ℝ) := by
  intro L c
  have hlog2_le1 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hL_ge5 : 5 ≤ L := by
    dsimp [L]
    have := Nat.le_log_of_pow_le (by norm_num : 1 < 2) (by omega : 2 ^ 4 ≤ z)
    omega
  have hc_eq : c = 2 ^ (L / 2 ^ i) := by
    dsimp [c]
    apply min_eq_right
    have hdiv : L / 2 ^ i ≤ L - 1 := by
      have h2i : 2 ≤ 2 ^ i := by
        calc 2 = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi
      have hq : L / 2 ^ i ≤ L / 2 := Nat.div_le_div_left h2i (by norm_num)
      omega
    have h1 : 2 ^ (L / 2 ^ i) ≤ 2 ^ (L - 1) := Nat.pow_le_pow_right (by norm_num) hdiv
    have h2 : 2 ^ (L - 1) ≤ z := by
      have hsub : L - 1 = Nat.log 2 z := Nat.add_sub_cancel _ 1
      rw [hsub]
      exact Nat.pow_log_le_self 2 (by omega)
    exact h1.trans h2
  have hc_le_z : c ≤ z := min_le_left _ _
  by_cases hc10 : 10 ≤ c
  · have hbase := OMA.R_Erdos687_erdos_687_parts_iii_R1.sum_prime_inv_Ioc_le hc10 hc_le_z
    have hlogc : Nat.log 2 c = L / 2 ^ i := by
      rw [hc_eq, Nat.log_pow (by norm_num : 1 < 2)]
    have hlogc_ge3 : 3 ≤ Nat.log 2 c :=
      Nat.le_log_of_pow_le (by norm_num : 1 < 2) (by omega : 2 ^ 3 ≤ c)
    have hratio : (Nat.log 2 z : ℝ) / (Nat.log 2 c : ℝ) ≤ (2 : ℝ) ^ (i + 1) := by
      have hlogc_pos : (0 : ℝ) < (Nat.log 2 c : ℝ) := by exact_mod_cast (show 0 < Nat.log 2 c by omega)
      rw [div_le_iff₀ hlogc_pos]
      have hnat : Nat.log 2 z ≤ 2 ^ (i + 1) * Nat.log 2 c := by
        rw [hlogc, pow_succ, Nat.mul_assoc]
        have hdm := Nat.div_add_mod L (2 ^ i)
        have hmod := Nat.mod_lt L (Nat.two_pow_pos i)
        have hq1 : 1 ≤ L / 2 ^ i := by omega
        have hL_le : L ≤ 2 ^ i * (L / 2 ^ i + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
          omega
        have h2q : L / 2 ^ i + 1 ≤ 2 * (L / 2 ^ i) := by omega
        have h1 : L ≤ 2 ^ i * (2 * (L / 2 ^ i)) := hL_le.trans (Nat.mul_le_mul_left _ h2q)
        exact (Nat.le_succ (Nat.log 2 z)).trans h1
      exact_mod_cast hnat
    have hlogz_pos : (0 : ℝ) < (Nat.log 2 z : ℝ) := by exact_mod_cast (show 0 < Nat.log 2 z by omega)
    have hlogc_pos : (0 : ℝ) < (Nat.log 2 c : ℝ) := by exact_mod_cast (show 0 < Nat.log 2 c by omega)
    have hlog_mono : Real.log ((Nat.log 2 z : ℝ) / (Nat.log 2 c : ℝ)) ≤
        Real.log ((2 : ℝ) ^ (i + 1)) :=
      Real.log_le_log (div_pos hlogz_pos hlogc_pos) hratio
    rw [Real.log_pow] at hlog_mono
    have hlog_le : ((i + 1 : ℕ) : ℝ) * Real.log 2 ≤ (i : ℝ) + 1 := by
      push_cast
      nlinarith
    linarith
  · push Not at hc10
    have hdiv_le3 : L / 2 ^ i ≤ 3 := by
      by_contra hgt
      push Not at hgt
      have hpow : 2 ^ 4 ≤ 2 ^ (L / 2 ^ i) := Nat.pow_le_pow_right (by norm_num) hgt
      rw [← hc_eq] at hpow
      omega
    have hL_lt : L < 2 ^ (i + 2) := by
      have hdm := Nat.div_add_mod L (2 ^ i)
      have hmod := Nat.mod_lt L (Nat.two_pow_pos i)
      have hmul : 2 ^ i * (L / 2 ^ i) ≤ 2 ^ i * 3 := Nat.mul_le_mul_left _ hdiv_le3
      have hpow : 2 ^ (i + 2) = 2 ^ i * 4 := by rw [pow_add]; norm_num
      omega
    have hsplit : (Ioc c z).filter Nat.Prime ⊆
        (range 11).filter Nat.Prime ∪ (Ioc 10 z).filter Nat.Prime := by
      intro q hq
      rw [mem_filter, mem_Ioc] at hq
      rw [mem_union, mem_filter, mem_filter, mem_range, mem_Ioc]
      by_cases hq10 : q ≤ 10
      · exact Or.inl ⟨by omega, hq.2⟩
      · exact Or.inr ⟨⟨by omega, hq.1.2⟩, hq.2⟩
    have hdisj_sp : Disjoint ((range 11).filter Nat.Prime) ((Ioc 10 z).filter Nat.Prime) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      have h1 := mem_range.mp (mem_filter.mp hp1).1
      have h2 := (mem_Ioc.mp (mem_filter.mp hp2).1).1
      omega
    have hsum_split : ∑ q ∈ (Ioc c z).filter Nat.Prime, (q : ℝ)⁻¹ ≤
        ∑ q ∈ (range 11).filter Nat.Prime, (q : ℝ)⁻¹ +
          ∑ q ∈ (Ioc 10 z).filter Nat.Prime, (q : ℝ)⁻¹ := by
      calc
        ∑ q ∈ (Ioc c z).filter Nat.Prime, (q : ℝ)⁻¹
            ≤ ∑ q ∈ (range 11).filter Nat.Prime ∪ (Ioc 10 z).filter Nat.Prime, (q : ℝ)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsplit (fun _ _ _ => by positivity)
        _ = _ := Finset.sum_union hdisj_sp
    have hsmall : ∑ q ∈ (range 11).filter Nat.Prime, (q : ℝ)⁻¹ ≤ 10 := by
      calc
        ∑ q ∈ (range 11).filter Nat.Prime, (q : ℝ)⁻¹
            ≤ ∑ _q ∈ (range 11).filter Nat.Prime, (1 : ℝ) := by
          refine Finset.sum_le_sum fun q hq => ?_
          have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (mem_filter.mp hq).2.one_le
          exact inv_le_one_of_one_le₀ hq1
        _ = (((range 11).filter Nat.Prime).card : ℝ) := by simp
        _ ≤ 10 := by
          have hcard : ((range 11).filter Nat.Prime).card ≤ 10 := by decide
          exact_mod_cast hcard
    have hbig := OMA.R_Erdos687_erdos_687_parts_iii_R1.sum_prime_inv_Ioc_le
      (show 10 ≤ 10 by norm_num) (by omega : 10 ≤ z)
    have hlog10 : Nat.log 2 10 = 3 := by decide
    have hratio : (Nat.log 2 z : ℝ) / (Nat.log 2 10 : ℝ) ≤ (2 : ℝ) ^ (i + 2) := by
      rw [hlog10]
      have h1 : (Nat.log 2 z : ℝ) ≤ (2 : ℝ) ^ (i + 2) := by
        have : Nat.log 2 z ≤ 2 ^ (i + 2) := by dsimp [L] at hL_lt; omega
        exact_mod_cast this
      have h2 : (Nat.log 2 z : ℝ) / (3 : ℝ) ≤ (Nat.log 2 z : ℝ) :=
        div_le_self (Nat.cast_nonneg _) (by norm_num)
      exact h2.trans h1
    have hlogz_pos : (0 : ℝ) < (Nat.log 2 z : ℝ) := by exact_mod_cast (show 0 < Nat.log 2 z by omega)
    have hlog10_pos : (0 : ℝ) < (Nat.log 2 10 : ℝ) := by rw [hlog10]; norm_num
    have hlog_mono : Real.log ((Nat.log 2 z : ℝ) / (Nat.log 2 10 : ℝ)) ≤
        Real.log ((2 : ℝ) ^ (i + 2)) :=
      Real.log_le_log (div_pos hlogz_pos hlog10_pos) hratio
    rw [Real.log_pow] at hlog_mono
    have hlog_le : ((i + 2 : ℕ) : ℝ) * Real.log 2 ≤ (i : ℝ) + 2 := by
      push_cast
      nlinarith
    linarith

/-- Product bound for every divisor set `D` retained in Brun's combinatorial sieve. -/
private lemma brun_prod_le {z b K : ℕ} (hz : 16 ≤ z) (_hb : 1 ≤ b)
    (D : Finset ℕ) (hD_sub : D ⊆ (range (z + 1)).filter Nat.Prime)
    (hD_brun :
      let L := Nat.log 2 z + 1
      let r := Nat.log 2 L + 1
      let cut : ℕ → ℕ := fun i => if i = 0 then z else min z (2 ^ (L / 2 ^ i))
      ∀ i ∈ Icc 1 r, (D ∩ (Ioc (cut i) z).filter Nat.Prime).card ≤ 2 * (b + K * i)) :
    ∏ p ∈ D, p ≤ z ^ (4 * b + 8 * K) := by
  let L := Nat.log 2 z + 1
  let r := Nat.log 2 L + 1
  let cut : ℕ → ℕ := fun i => if i = 0 then z else min z (2 ^ (L / 2 ^ i))
  let P : ℕ → Finset ℕ := fun i => (Ioc (cut i) (cut (i - 1))).filter Nat.Prime
  have hL_ge5 : 5 ≤ L := by
    dsimp [L]
    have := Nat.le_log_of_pow_le (by norm_num : 1 < 2) (by omega : 2 ^ 4 ≤ z)
    omega
  have hr_ge1 : 1 ≤ r := by dsimp [r]; omega
  have hcut_anti : Antitone cut := by
    intro i j hij
    by_cases hi0 : i = 0
    · subst hi0
      dsimp only [cut]
      rw [if_pos rfl]
      split_ifs
      · exact le_rfl
      · exact min_le_left z _
    · have hj0 : j ≠ 0 := by omega
      dsimp only [cut]
      rw [if_neg hi0, if_neg hj0]
      apply min_le_min_left z
      exact Nat.pow_le_pow_right (by norm_num)
        (Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) hij) (Nat.two_pow_pos i))
  have hcut_r : cut r = 1 := by
    dsimp [cut, r]
    have hlt : L < 2 ^ (Nat.log 2 L + 1) := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) L
    rw [Nat.div_eq_of_lt hlt, pow_zero]
    exact min_eq_right (by omega)
  have hcut_le_pow : ∀ i : ℕ, cut i ≤ 2 ^ (L / 2 ^ i) := by
    intro i
    dsimp [cut]
    split_ifs with h0
    · subst h0
      rw [pow_zero, Nat.div_one]
      exact le_of_lt (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) z)
    · exact min_le_right _ _
  have hP_disj : (Icc 1 r : Set ℕ).PairwiseDisjoint P := by
    intro i hi j hj hij
    rw [Function.onFun, Finset.disjoint_left]
    intro p hpi hpj
    have h1 := mem_Ioc.mp (mem_filter.mp hpi).1
    have h2 := mem_Ioc.mp (mem_filter.mp hpj).1
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have : cut (j - 1) ≤ cut i := hcut_anti (by omega)
      omega
    · have : cut (i - 1) ≤ cut j := hcut_anti (by omega)
      omega
  have hP_union : ∀ k ≤ r, (Icc 1 k).biUnion P = (Ioc (cut k) z).filter Nat.Prime := by
    intro k hk
    induction k with
    | zero =>
      simp [cut]
    | succ m hm =>
      rw [icc_succ_eq_insert (by omega : 1 ≤ m + 1), Finset.biUnion_insert,
        hm (by omega)]
      ext p
      simp only [P, mem_union, mem_filter, mem_Ioc, Nat.add_sub_cancel]
      have hm1 : cut (m + 1) ≤ cut m := hcut_anti (Nat.le_succ m)
      have hm2 : cut m ≤ z := hcut_anti (Nat.zero_le m)
      constructor
      · rintro (⟨⟨h1, h2⟩, hp⟩ | ⟨⟨h1, h2⟩, hp⟩)
        · exact ⟨⟨h1, h2.trans hm2⟩, hp⟩
        · exact ⟨⟨lt_of_le_of_lt hm1 h1, h2⟩, hp⟩
      · rintro ⟨⟨h1, h2⟩, hp⟩
        by_cases hpm : p ≤ cut m
        · exact Or.inl ⟨⟨h1, hpm⟩, hp⟩
        · exact Or.inr ⟨⟨by omega, h2⟩, hp⟩
  have hD_part : D = (Icc 1 r).biUnion (fun i => D ∩ P i) := by
    have hfull : (range (z + 1)).filter Nat.Prime = (Icc 1 r).biUnion P := by
      rw [hP_union r le_rfl, hcut_r]
      ext p
      simp only [mem_filter, mem_range, mem_Ioc]
      constructor
      · rintro ⟨hpz, hpp⟩
        exact ⟨⟨hpp.one_lt, by omega⟩, hpp⟩
      · rintro ⟨⟨_, hpz⟩, hpp⟩
        exact ⟨by omega, hpp⟩
    rw [← Finset.inter_biUnion, ← hfull, Finset.inter_eq_left.mpr hD_sub]
  have hDP_disj : (Icc 1 r : Set ℕ).PairwiseDisjoint (fun i => D ∩ P i) := by
    intro i hi j hj hij
    rw [Function.onFun]
    exact Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right (hP_disj hi hj hij)
  have hprod_bound : ∏ p ∈ D, p ≤ 2 ^ (∑ i ∈ Icc 1 r, (D ∩ P i).card * (L / 2 ^ (i - 1))) := by
    conv_lhs => rw [hD_part]
    rw [Finset.prod_biUnion hDP_disj, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod' fun i _ => ?_
    calc
      ∏ p ∈ D ∩ P i, p ≤ ∏ _p ∈ D ∩ P i, 2 ^ (L / 2 ^ (i - 1)) := by
        refine Finset.prod_le_prod' fun p hp => ?_
        have hp_le : p ≤ cut (i - 1) := (mem_Ioc.mp (mem_filter.mp (mem_inter.mp hp).2).1).2
        exact hp_le.trans (hcut_le_pow (i - 1))
      _ = (2 ^ (L / 2 ^ (i - 1))) ^ (D ∩ P i).card := Finset.prod_const _
      _ = 2 ^ ((D ∩ P i).card * (L / 2 ^ (i - 1))) := by rw [← pow_mul, Nat.mul_comm]
  -- Bound the natural-number exponent via summation by parts in `ℝ`.
  let N : ℕ → ℝ := fun k => ((D ∩ (Ioc (cut k) z).filter Nat.Prime).card : ℝ)
  have hN0 : N 0 = 0 := by simp [N, cut]
  have hN_step : ∀ i ∈ Icc 1 r, ((D ∩ P i).card : ℝ) = N i - N (i - 1) := by
    intro i hi
    have hi' := mem_Icc.mp hi
    have hdisj_i : Disjoint (D ∩ (Ioc (cut (i - 1)) z).filter Nat.Prime) (D ∩ P i) := by
      rw [← hP_union (i - 1) (by omega), Finset.disjoint_left]
      intro p hp1 hp2
      have h1 := (mem_inter.mp hp1).2
      have h2 := (mem_inter.mp hp2).2
      rw [mem_biUnion] at h1
      obtain ⟨j, hj, hpj⟩ := h1
      have hj' := mem_Icc.mp hj
      exact Finset.disjoint_left.mp
        (hP_disj (mem_coe.mpr (mem_Icc.mpr ⟨hj'.1, by omega⟩)) (mem_coe.mpr hi) (by omega)) hpj h2
    have hunion_i : D ∩ (Ioc (cut i) z).filter Nat.Prime =
        (D ∩ (Ioc (cut (i - 1)) z).filter Nat.Prime) ∪ (D ∩ P i) := by
      rw [← hP_union i hi'.2, ← hP_union (i - 1) (by omega)]
      have hIcc : Icc 1 i = insert i (Icc 1 (i - 1)) := by
        ext j
        simp only [mem_Icc, mem_insert]
        omega
      rw [hIcc, Finset.biUnion_insert, Finset.inter_union_distrib_left, Finset.union_comm]
    have hcard_add : (D ∩ (Ioc (cut i) z).filter Nat.Prime).card =
        (D ∩ (Ioc (cut (i - 1)) z).filter Nat.Prime).card + (D ∩ P i).card := by
      rw [hunion_i, Finset.card_union_of_disjoint hdisj_i]
    have hcard_r : N i = N (i - 1) + ((D ∩ P i).card : ℝ) := by
      dsimp [N]
      exact_mod_cast hcard_add
    linarith
  have hN_le : ∀ i ∈ Icc 1 r, N i ≤ (2 * b + 2 * K * i : ℝ) := by
    intro i hi
    have hle : (D ∩ (Ioc (cut i) z).filter Nat.Prime).card ≤ 2 * (b + K * i) := hD_brun i hi
    have hle_r : N i ≤ ((2 * (b + K * i) : ℕ) : ℝ) := by
      dsimp [N]
      exact_mod_cast hle
    push_cast at hle_r
    linarith
  have hexp_real : ((∑ i ∈ Icc 1 r, (D ∩ P i).card * (L / 2 ^ (i - 1)) : ℕ) : ℝ) ≤
      ((2 * b + 4 * K) * L : ℝ) := by
    push_cast
    have h1 : ∑ i ∈ Icc 1 r, ((D ∩ P i).card : ℝ) * ((L / 2 ^ (i - 1) : ℕ) : ℝ) ≤
        ∑ i ∈ Icc 1 r, (N i - N (i - 1)) * ((L : ℝ) / (2 : ℝ) ^ (i - 1)) := by
      refine Finset.sum_le_sum fun i hi => ?_
      rw [hN_step i hi]
      have hnn : 0 ≤ N i - N (i - 1) := by rw [← hN_step i hi]; exact Nat.cast_nonneg _
      have hdiv : ((L / 2 ^ (i - 1) : ℕ) : ℝ) ≤ (L : ℝ) / (2 : ℝ) ^ (i - 1) := by
        rw [le_div_iff₀ (by positivity)]
        exact_mod_cast Nat.div_mul_le_self L (2 ^ (i - 1))
      exact mul_le_mul_of_nonneg_left hdiv hnn
    have hsbp : ∑ i ∈ Icc 1 r, (N i - N (i - 1)) * ((L : ℝ) / (2 : ℝ) ^ (i - 1)) =
        (L : ℝ) * (N r / (2 : ℝ) ^ (r - 1) + ∑ i ∈ Icc 1 (r - 1), N i / (2 : ℝ) ^ i) := by
      have htele : ∀ n : ℕ, 1 ≤ n →
          ∑ i ∈ Icc 1 n, (N i - N (i - 1)) * ((L : ℝ) / (2 : ℝ) ^ (i - 1)) =
          (L : ℝ) * (N n / (2 : ℝ) ^ (n - 1) + ∑ i ∈ Icc 1 (n - 1), N i / (2 : ℝ) ^ i) := by
        intro n hn
        induction n, hn using Nat.le_induction with
        | base => simp [hN0]; ring
        | succ m hm ih =>
          rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), ih]
          have hsub : m + 1 - 1 = m := by omega
          rw [hsub]
          have hIcc : Icc 1 m = insert m (Icc 1 (m - 1)) := by
            ext i; simp only [mem_Icc, mem_insert]; omega
          have hnotmem : m ∉ Icc 1 (m - 1) := by simp only [mem_Icc]; omega
          rw [hIcc, Finset.sum_insert hnotmem]
          have hpow : (2 : ℝ) ^ m = 2 * (2 : ℝ) ^ (m - 1) := by
            rw [← pow_succ', Nat.sub_add_cancel hm]
          rw [hpow]
          have h2m : (2 : ℝ) ^ (m - 1) ≠ 0 := by positivity
          field_simp
          ring
      exact htele r hr_ge1
    have h2 : N r / (2 : ℝ) ^ (r - 1) + ∑ i ∈ Icc 1 (r - 1), N i / (2 : ℝ) ^ i ≤
        (2 * b + 4 * K : ℝ) := by
      have hterm1 : N r / (2 : ℝ) ^ (r - 1) ≤ (2 * b + 2 * K * r : ℝ) / (2 : ℝ) ^ (r - 1) :=
        div_le_div_of_nonneg_right (hN_le r (mem_Icc.mpr ⟨hr_ge1, le_rfl⟩)) (by positivity)
      have hterm2 : ∑ i ∈ Icc 1 (r - 1), N i / (2 : ℝ) ^ i ≤
          ∑ i ∈ Icc 1 (r - 1), (2 * b + 2 * K * i : ℝ) / (2 : ℝ) ^ i := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' := mem_Icc.mp hi
        exact div_le_div_of_nonneg_right (hN_le i (mem_Icc.mpr ⟨hi'.1, by omega⟩)) (by positivity)
      have hident := brun_dyadic_weight_bound b K r hr_ge1
      have hKnn : (0 : ℝ) ≤ (2 * K : ℝ) / (2 : ℝ) ^ (r - 1) := by positivity
      linarith
    calc
      ∑ i ∈ Icc 1 r, ((D ∩ P i).card : ℝ) * ((L / 2 ^ (i - 1) : ℕ) : ℝ)
          ≤ (L : ℝ) * (N r / (2 : ℝ) ^ (r - 1) + ∑ i ∈ Icc 1 (r - 1), N i / (2 : ℝ) ^ i) :=
        h1.trans_eq hsbp
      _ ≤ (L : ℝ) * (2 * b + 4 * K : ℝ) := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg L)
      _ = ((2 * b + 4 * K) * L : ℝ) := by ring
  have hexp_nat : ∑ i ∈ Icc 1 r, (D ∩ P i).card * (L / 2 ^ (i - 1)) ≤ (2 * b + 4 * K) * L := by
    exact_mod_cast hexp_real
  have h2L_le : 2 ^ L ≤ z ^ 2 := by
    have h1 : 2 ^ (Nat.log 2 z) ≤ z := Nat.pow_log_le_self 2 (by omega)
    dsimp [L]
    rw [pow_succ, sq]
    nlinarith
  calc
    ∏ p ∈ D, p ≤ 2 ^ (∑ i ∈ Icc 1 r, (D ∩ P i).card * (L / 2 ^ (i - 1))) := hprod_bound
    _ ≤ 2 ^ ((2 * b + 4 * K) * L) := Nat.pow_le_pow_right (by norm_num) hexp_nat
    _ = (2 ^ L) ^ (2 * b + 4 * K) := by rw [Nat.mul_comm, pow_mul]
    _ ≤ (z ^ 2) ^ (2 * b + 4 * K) := Nat.pow_le_pow_left h2L_le _
    _ = z ^ (4 * b + 8 * K) := by rw [← pow_mul]; congr 1; ring

theorem OMA.solution : OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1.H1 := by
  intro δ hδ
  obtain ⟨K₀, hK₀⟩ := exists_nat_ge (2 + Real.exp 1)
  let K : ℕ := K₀ + 1
  let A : ℝ := 18 * (K₀ : ℝ)
  let C₁ : ℝ := (20 + 16 * (K : ℝ)) ^ 3
  have hC₁_pos : 0 < C₁ := by dsimp [C₁]; positivity
  obtain ⟨b₀, hb₀⟩ := exists_nat_ge (32 * Real.exp A * C₁ / δ)
  let b_min : ℕ := max 1 (b₀ + 1)
  have hb_min1 : 1 ≤ b_min := le_max_left _ _
  have hb_min0 : b₀ + 1 ≤ b_min := le_max_right _ _
  let s₀ : ℕ := 8 * b_min + 16 * K + 4
  refine ⟨s₀, by dsimp [s₀]; omega, fun s hs_ge => ?_⟩
  let b : ℕ := (s - 16 * K - 4) / 8
  have hb_ge_min : b_min ≤ b := by
    dsimp [b]
    exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 8)).mpr (by dsimp [s₀] at hs_ge; omega)
  have hb1 : 1 ≤ b := hb_min1.trans hb_ge_min
  have hbb₀ : b₀ + 1 ≤ b := hb_min0.trans hb_ge_min
  have hs_lo : 8 * b + 16 * K + 4 ≤ s := by
    have hmul : b * 8 ≤ s - 16 * K - 4 := Nat.div_mul_le_self (s - 16 * K - 4) 8
    dsimp [s₀] at hs_ge
    omega
  have hs_hi : s ≤ 8 * b + 16 * K + 11 := by
    have hdm : b * 8 + (s - 16 * K - 4) % 8 = s - 16 * K - 4 := by
      dsimp [b]
      rw [Nat.mul_comm]
      exact Nat.div_add_mod (s - 16 * K - 4) 8
    have hlt : (s - 16 * K - 4) % 8 < 8 := Nat.mod_lt _ (by norm_num)
    dsimp [s₀] at hs_ge
    omega
  obtain ⟨Z₁, hZ₁⟩ := exists_nat_ge (2 * (s : ℝ) ^ 3 / δ)
  rw [eventually_atTop]
  refine ⟨max 16 (Z₁ + 1), fun z hz y hzy a => ?_⟩
  have hz16 : 16 ≤ z := le_trans (le_max_left _ _) hz
  have hzZ₁ : Z₁ + 1 ≤ z := le_trans (le_max_right _ _) hz
  let P_all := (range (z + 1)).filter Nat.Prime
  let L := Nat.log 2 z + 1
  let r := Nat.log 2 L + 1
  let cut : ℕ → ℕ := fun i => if i = 0 then z else min z (2 ^ (L / 2 ^ i))
  let P : ℕ → Finset ℕ := fun i => (Ioc (cut i) (cut (i - 1))).filter Nat.Prime
  let Q : ℕ → Finset ℕ := fun i => (Ioc (cut i) z).filter Nat.Prime
  let bf : ℕ → ℕ := fun i => b + K * i
  have hr_ge1 : 1 ≤ r := by dsimp [r]; omega
  have hcut_anti : Antitone cut := by
    intro i j hij
    by_cases hi0 : i = 0
    · subst hi0
      dsimp only [cut]
      rw [if_pos rfl]
      split_ifs
      · exact le_rfl
      · exact min_le_left z _
    · have hj0 : j ≠ 0 := by omega
      dsimp only [cut]
      rw [if_neg hi0, if_neg hj0]
      apply min_le_min_left z
      exact Nat.pow_le_pow_right (by norm_num)
        (Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) hij) (Nat.two_pow_pos i))
  have hcut_r : cut r = 1 := by
    dsimp [cut, r]
    have hlt : L < 2 ^ (Nat.log 2 L + 1) := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) L
    rw [Nat.div_eq_of_lt hlt, pow_zero]
    exact min_eq_right (by omega)
  have hP_disj : ∀ i j, 1 ≤ i → 1 ≤ j → i ≠ j → Disjoint (P i) (P j) := by
    intro i j hi hj hij
    rw [Finset.disjoint_left]
    intro p hpi hpj
    have h1 := mem_Ioc.mp (mem_filter.mp hpi).1
    have h2 := mem_Ioc.mp (mem_filter.mp hpj).1
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have : cut (j - 1) ≤ cut i := hcut_anti (by omega)
      omega
    · have : cut (i - 1) ≤ cut j := hcut_anti (by omega)
      omega
  have hQ_eq : ∀ k ≤ r, (Icc 1 k).biUnion P = Q k := by
    intro k hk
    induction k with
    | zero => simp [Q, cut]
    | succ m hm =>
      rw [icc_succ_eq_insert (by omega : 1 ≤ m + 1), Finset.biUnion_insert,
        hm (by omega)]
      ext p
      simp only [P, Q, mem_union, mem_filter, mem_Ioc, Nat.add_sub_cancel]
      have hm1 : cut (m + 1) ≤ cut m := hcut_anti (Nat.le_succ m)
      have hm2 : cut m ≤ z := hcut_anti (Nat.zero_le m)
      constructor
      · rintro (⟨⟨h1, h2⟩, hp⟩ | ⟨⟨h1, h2⟩, hp⟩)
        · exact ⟨⟨h1, h2.trans hm2⟩, hp⟩
        · exact ⟨⟨lt_of_le_of_lt hm1 h1, h2⟩, hp⟩
      · rintro ⟨⟨h1, h2⟩, hp⟩
        by_cases hpm : p ≤ cut m
        · exact Or.inl ⟨⟨h1, hpm⟩, hp⟩
        · exact Or.inr ⟨⟨by omega, h2⟩, hp⟩
  have hP_all_eq : P_all = (Icc 1 r).biUnion P := by
    rw [hQ_eq r le_rfl]
    dsimp [P_all, Q]
    rw [hcut_r]
    ext p
    simp only [mem_filter, mem_range, mem_Ioc]
    constructor
    · rintro ⟨hpz, hpp⟩; exact ⟨⟨hpp.one_lt, by omega⟩, hpp⟩
    · rintro ⟨⟨_, hpz⟩, hpp⟩; exact ⟨by omega, hpp⟩
  -- Define Brun's retained divisor family `D_brun ⊆ P_all.powerset`.
  let D_brun := P_all.powerset.filter (brunPred Q bf r)
  -- Step 1: Pointwise Brun upper bound summed over `m ∈ Icc 1 y`.
  have hstep1 :
      (((Icc 1 y).filter fun m => ∀ p ≤ z, p.Prime → ¬ (m ≡ a p [MOD p])).card : ℝ) ≤
      ∑ D ∈ D_brun, (-1 : ℝ) ^ D.card *
        (((Icc 1 y).filter fun m => ∀ p ∈ D, m ≡ a p [MOD p]).card : ℝ) := by
    let B : ℕ → Finset ℕ := fun m => P_all.filter (fun p => m ≡ a p [MOD p])
    have hsurv : (((Icc 1 y).filter fun m => ∀ p ≤ z, p.Prime → ¬ (m ≡ a p [MOD p])).card : ℝ) =
        ∑ m ∈ Icc 1 y, (if B m = ∅ then (1 : ℝ) else 0) := by
      rw [Finset.sum_boole]
      congr 2
      ext m
      simp only [B, P_all, mem_filter, Finset.eq_empty_iff_forall_notMem, mem_range]
      refine and_congr_right fun _ => ?_
      constructor
      · intro h p ⟨⟨hpz, hpp⟩, hmod⟩
        exact h p (by omega) hpp hmod
      · intro h p hpz hpp hmod
        exact h p ⟨⟨by omega, hpp⟩, hmod⟩
    rw [hsurv]
    have hpt : ∀ m ∈ Icc 1 y,
        (if B m = ∅ then (1 : ℝ) else 0) ≤
          ∑ D ∈ D_brun, (if ∀ p ∈ D, m ≡ a p [MOD p] then (-1 : ℝ) ^ D.card else 0) := by
      intro m _
      have hBm_sub : B m ⊆ (Icc 1 r).biUnion P := by
        rw [← hP_all_eq]
        exact Finset.filter_subset _ _
      have hfilt_eq : D_brun.filter (fun D => ∀ p ∈ D, m ≡ a p [MOD p]) =
          (B m).powerset.filter (brunPred (fun k => (Icc 1 k).biUnion P) bf r) := by
        ext D
        simp only [D_brun, B, brunPred, mem_filter, mem_powerset]
        constructor
        · rintro ⟨⟨hDP, hDb⟩, hDm⟩
          refine ⟨fun p hp => mem_filter.mpr ⟨hDP hp, hDm p hp⟩, fun i hi => ?_⟩
          rw [hQ_eq i (mem_Icc.mp hi).2]
          exact hDb i hi
        · rintro ⟨hDB, hDb⟩
          refine ⟨⟨fun p hp => (mem_filter.mp (hDB hp)).1, fun i hi => ?_⟩,
            fun p hp => (mem_filter.mp (hDB hp)).2⟩
          rw [← hQ_eq i (mem_Icc.mp hi).2]
          exact hDb i hi
      rw [← Finset.sum_filter, hfilt_eq]
      exact brun_pointwise_upper P bf
        (fun i _ => by dsimp [bf]; rw [Nat.mul_succ]; omega) hP_disj r (B m) hBm_sub
    have hswap :
        ∑ D ∈ D_brun, (-1 : ℝ) ^ D.card *
          (((Icc 1 y).filter fun m => ∀ p ∈ D, m ≡ a p [MOD p]).card : ℝ) =
        ∑ m ∈ Icc 1 y, ∑ D ∈ D_brun,
          if ∀ p ∈ D, m ≡ a p [MOD p] then (-1 : ℝ) ^ D.card else 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun D _ => ?_
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul,
        mul_comm]
    rw [hswap]
    exact Finset.sum_le_sum hpt
  -- Step 2: Apply CRT approximation to every retained divisor `D ∈ D_brun`.
  have hstep2 :
      ∑ D ∈ D_brun, (-1 : ℝ) ^ D.card *
        (((Icc 1 y).filter fun m => ∀ p ∈ D, m ≡ a p [MOD p]).card : ℝ) ≤
      (y : ℝ) * (∑ D ∈ D_brun, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹)) +
        (D_brun.card : ℝ) := by
    have hdiff : ∀ D ∈ D_brun,
        (-1 : ℝ) ^ D.card *
          (((Icc 1 y).filter fun m => ∀ p ∈ D, m ≡ a p [MOD p]).card : ℝ) ≤
        (y : ℝ) * ((-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹)) + 1 := by
      intro D hD
      have hDp : ∀ p ∈ D, p.Prime := fun p hp =>
        (mem_filter.mp (mem_powerset.mp (mem_filter.mp hD).1 hp)).2
      have hcrt := crt_count_sub_div_le_one hDp a y
      have hmul_abs :
          |(-1 : ℝ) ^ D.card *
            ((((Icc 1 y).filter fun m => ∀ p ∈ D, m ≡ a p [MOD p]).card : ℝ) -
              (y : ℝ) * (∏ p ∈ D, (p : ℝ)⁻¹))| ≤ 1 := by
        rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
        exact hcrt
      have hhi := (abs_le.mp hmul_abs).2
      linarith
    have hsum := Finset.sum_le_sum hdiff
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
    exact hsum
  -- Step 3: Bound the truncation tail `|V(z) - ∑_{D ∈ D_brun} (-1)^|D| w(D)|`.
  let V : ℕ → ℝ := fun u => ∏ p ∈ (range (u + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)
  have hVz_pos : 0 < V z := eulerProd_pos_finset _ fun _ hp => (mem_filter.mp hp).2
  have htrunc :
      |V z - ∑ D ∈ D_brun, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹)| ≤
        Real.exp (A - 2 * (b : ℝ)) * V z := by
    have hsub_D : D_brun ⊆ P_all.powerset := Finset.filter_subset _ _
    -- Partition `P_all.powerset \ D_brun` by the first violated block `i ∈ Icc 1 r`.
    let Bad : ℕ → Finset (Finset ℕ) := fun i =>
      P_all.powerset.filter fun D =>
        brunPredIco Q bf i D ∧ 2 * bf i + 1 ≤ (D ∩ Q i).card
    have hBad_pw : (Icc 1 r : Set ℕ).PairwiseDisjoint Bad := by
      intro i hi j hj hij
      rw [Function.onFun, Finset.disjoint_left]
      intro D hDi hDj
      have h1 := (mem_filter.mp hDi).2
      have h2 := (mem_filter.mp hDj).2
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · have := h2.1 i (mem_Ico.mpr ⟨(mem_Icc.mp hi).1, hlt⟩)
        omega
      · have := h1.1 j (mem_Ico.mpr ⟨(mem_Icc.mp hj).1, hgt⟩)
        omega
    have hBad_eq : P_all.powerset \ D_brun = (Icc 1 r).biUnion Bad := by
      ext D
      simp only [Finset.mem_sdiff, mem_biUnion, D_brun, Bad, mem_filter]
      simp only [brunPred, brunPredIco]
      constructor
      · rintro ⟨hDP, hnot⟩
        let S := (Icc 1 r).filter fun i => 2 * bf i + 1 ≤ (D ∩ Q i).card
        have hS_ne : S.Nonempty := by
          by_contra hnone
          rw [Finset.not_nonempty_iff_eq_empty, Finset.eq_empty_iff_forall_notMem] at hnone
          refine hnot ⟨hDP, fun i hi => ?_⟩
          have hni := hnone i
          simp only [S, mem_filter, hi, true_and, not_le] at hni
          omega
        let i := S.min' hS_ne
        have hi_mem : i ∈ S := Finset.min'_mem S hS_ne
        have hi_p := mem_filter.mp hi_mem
        refine ⟨i, hi_p.1, hDP, fun j hj => ?_, hi_p.2⟩
        have hj' := mem_Ico.mp hj
        have hj_not : j ∉ S := fun hjS =>
          (not_le_of_gt hj'.2) (Finset.min'_le S j hjS)
        have hj_icc : j ∈ Icc 1 r := mem_Icc.mpr ⟨hj'.1, hj'.2.le.trans (mem_Icc.mp hi_p.1).2⟩
        simp only [S, mem_filter, hj_icc, true_and, not_le] at hj_not
        omega
      · rintro ⟨i, hi, hDP, _, hviol⟩
        refine ⟨hDP, fun h => ?_⟩
        have hle := h.2 i hi
        omega
    have hdiff_eq : V z - ∑ D ∈ D_brun, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹) =
        ∑ i ∈ Icc 1 r, ∑ D ∈ Bad i, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹) := by
      rw [show V z = ∑ D ∈ P_all.powerset, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹) from
        eulerProd_eq_powerset_sum P_all, ← Finset.sum_sdiff hsub_D, add_sub_cancel_right,
        hBad_eq, Finset.sum_biUnion hBad_pw]
    rw [hdiff_eq]
    have hterm_i : ∀ i ∈ Icc 1 r,
        |∑ D ∈ Bad i, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹)| ≤
          Real.exp (A - 2 * (b : ℝ)) * ((1 / 2 : ℝ) ^ i) * V z := by
      intro i hi
      have hi' := mem_Icc.mp hi
      let P_lo := (range (cut i + 1)).filter Nat.Prime
      have hQ_sub : Q i ⊆ P_all := by
        intro p hp
        rw [mem_filter, mem_Ioc] at hp
        exact mem_filter.mpr ⟨mem_range.mpr (by omega), hp.2⟩
      have hPlo_sub : P_lo ⊆ P_all := by
        intro p hp
        rw [mem_filter, mem_range] at hp
        have hcz : cut i ≤ z := hcut_anti (Nat.zero_le i)
        exact mem_filter.mpr ⟨mem_range.mpr (by omega), hp.2⟩
      have hQP_disj : Disjoint (Q i) P_lo := by
        rw [Finset.disjoint_left]
        intro p hpQ hpL
        have h1 := (mem_Ioc.mp (mem_filter.mp hpQ).1).1
        have h2 := mem_range.mp (mem_filter.mp hpL).1
        omega
      have hQP_union : Q i ∪ P_lo = P_all := by
        ext p
        simp only [Q, P_lo, P_all, mem_union, mem_filter, mem_Ioc, mem_range]
        have hcz : cut i ≤ z := hcut_anti (Nat.zero_le i)
        constructor
        · rintro (⟨⟨_, h2⟩, hp⟩ | ⟨h1, hp⟩) <;> exact ⟨by omega, hp⟩
        · rintro ⟨h1, hp⟩
          by_cases hpc : p ≤ cut i
          · exact Or.inr ⟨by omega, hp⟩
          · exact Or.inl ⟨⟨by omega, by omega⟩, hp⟩
      let A_i := (Q i).powerset.filter fun D₁ =>
        brunPredIco Q bf i D₁ ∧ 2 * bf i + 1 ≤ D₁.card
      -- Factor `Bad i` as `A_i ×ˢ P_lo.powerset`.
      have hfac : ∑ D ∈ Bad i, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹) =
          (∑ D₁ ∈ A_i, (-1 : ℝ) ^ D₁.card * (∏ p ∈ D₁, (p : ℝ)⁻¹)) * V (cut i) := by
        rw [show V (cut i) = ∑ D₂ ∈ P_lo.powerset, (-1 : ℝ) ^ D₂.card * (∏ p ∈ D₂, (p : ℝ)⁻¹) from
          eulerProd_eq_powerset_sum P_lo, Finset.sum_mul_sum, ← Finset.sum_product']
        refine (Finset.sum_nbij (fun x : Finset ℕ × Finset ℕ => x.1 ∪ x.2) ?_ ?_ ?_ ?_).symm
        · intro x hx
          rw [mem_product] at hx
          obtain ⟨hD₁, hD₂⟩ := hx
          have hD₁p := mem_filter.mp hD₁
          have hD₁Q : x.1 ⊆ Q i := mem_powerset.mp hD₁p.1
          have hD₂L : x.2 ⊆ P_lo := mem_powerset.mp hD₂
          refine mem_filter.mpr ⟨mem_powerset.mpr ?_, fun j hj => ?_, ?_⟩
          · rw [← hQP_union]
            exact Finset.union_subset_union hD₁Q hD₂L
          · have hj' := mem_Ico.mp hj
            have hQj_sub : Q j ⊆ Q i := by
              intro p hp
              rw [mem_filter, mem_Ioc] at hp ⊢
              have : cut i ≤ cut j := hcut_anti hj'.2.le
              exact ⟨⟨lt_of_le_of_lt this hp.1.1, hp.1.2⟩, hp.2⟩
            have hdisj2 : Disjoint x.2 (Q j) := Disjoint.mono hD₂L hQj_sub hQP_disj.symm
            rw [Finset.union_inter_distrib_right,
              Finset.disjoint_iff_inter_eq_empty.mp hdisj2, Finset.union_empty]
            exact hD₁p.2.1 j hj
          · have hdisj2 : Disjoint x.2 (Q i) := Disjoint.mono_left hD₂L hQP_disj.symm
            rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hD₁Q,
              Finset.disjoint_iff_inter_eq_empty.mp hdisj2, Finset.union_empty]
            exact hD₁p.2.2
        · intro x hx y hy hxy
          rw [mem_coe, mem_product] at hx hy
          have hx1 : x.1 ⊆ Q i := mem_powerset.mp (mem_filter.mp hx.1).1
          have hx2 : x.2 ⊆ P_lo := mem_powerset.mp hx.2
          have hy1 : y.1 ⊆ Q i := mem_powerset.mp (mem_filter.mp hy.1).1
          have hy2 : y.2 ⊆ P_lo := mem_powerset.mp hy.2
          have heq1 : x.1 = y.1 := by
            have := congrArg (· ∩ Q i) hxy
            simpa only [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hx1,
              Finset.inter_eq_left.mpr hy1,
              Finset.disjoint_iff_inter_eq_empty.mp (Disjoint.mono_left hx2 hQP_disj.symm),
              Finset.disjoint_iff_inter_eq_empty.mp (Disjoint.mono_left hy2 hQP_disj.symm),
              Finset.union_empty] using this
          have heq2 : x.2 = y.2 := by
            have := congrArg (· ∩ P_lo) hxy
            simpa only [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hx2,
              Finset.inter_eq_left.mpr hy2,
              Finset.disjoint_iff_inter_eq_empty.mp (Disjoint.mono_left hx1 hQP_disj),
              Finset.disjoint_iff_inter_eq_empty.mp (Disjoint.mono_left hy1 hQP_disj),
              Finset.empty_union] using this
          exact Prod.ext heq1 heq2
        · intro D hD
          rw [mem_coe] at hD
          have hDp := mem_filter.mp hD
          have hDP : D ⊆ P_all := mem_powerset.mp hDp.1
          let D₁ := D ∩ Q i
          let D₂ := D ∩ P_lo
          have hDeq : D₁ ∪ D₂ = D := by
            rw [← Finset.inter_union_distrib_left, hQP_union, Finset.inter_eq_left.mpr hDP]
          have hD₁mem : D₁ ∈ A_i := by
            refine mem_filter.mpr ⟨mem_powerset.mpr Finset.inter_subset_right, fun j hj => ?_, hDp.2.2⟩
            have hj' := mem_Ico.mp hj
            have hQj_sub : Q j ⊆ Q i := by
              intro p hp
              rw [mem_filter, mem_Ioc] at hp ⊢
              have : cut i ≤ cut j := hcut_anti hj'.2.le
              exact ⟨⟨lt_of_le_of_lt this hp.1.1, hp.1.2⟩, hp.2⟩
            dsimp [D₁]
            rw [Finset.inter_assoc, Finset.inter_eq_right.mpr hQj_sub]
            exact hDp.2.1 j hj
          have hD₂mem : D₂ ∈ P_lo.powerset := mem_powerset.mpr Finset.inter_subset_right
          exact ⟨(D₁, D₂), mem_coe.mpr (mem_product.mpr ⟨hD₁mem, hD₂mem⟩), hDeq⟩
        · intro x hx
          rw [mem_product] at hx
          have hx1 : x.1 ⊆ Q i := mem_powerset.mp (mem_filter.mp hx.1).1
          have hx2 : x.2 ⊆ P_lo := mem_powerset.mp hx.2
          have hdisj : Disjoint x.1 x.2 := Disjoint.mono hx1 hx2 hQP_disj
          rw [Finset.card_union_of_disjoint hdisj, pow_add, Finset.prod_union hdisj]
          ring
      rw [hfac, abs_mul, abs_of_pos (eulerProd_pos_finset _ fun _ hp => (mem_filter.mp hp).2)]
      have hAi_le : |∑ D₁ ∈ A_i, (-1 : ℝ) ^ D₁.card * (∏ p ∈ D₁, (p : ℝ)⁻¹)| ≤
          ∑ D₁ ∈ (Q i).powerset.filter (fun D₁ => 2 * bf i ≤ D₁.card),
            (∏ p ∈ D₁, (p : ℝ)⁻¹) := by
        calc
          |∑ D₁ ∈ A_i, (-1 : ℝ) ^ D₁.card * (∏ p ∈ D₁, (p : ℝ)⁻¹)|
              ≤ ∑ D₁ ∈ A_i, |(-1 : ℝ) ^ D₁.card * (∏ p ∈ D₁, (p : ℝ)⁻¹)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ = ∑ D₁ ∈ A_i, (∏ p ∈ D₁, (p : ℝ)⁻¹) := by
            refine Finset.sum_congr rfl fun D₁ _ => ?_
            rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
              abs_of_nonneg (Finset.prod_nonneg fun _ _ => by positivity)]
          _ ≤ ∑ D₁ ∈ (Q i).powerset.filter (fun D₁ => 2 * bf i ≤ D₁.card),
                (∏ p ∈ D₁, (p : ℝ)⁻¹) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ =>
              Finset.prod_nonneg fun _ _ => by positivity)
            intro D₁ hD₁
            have h := mem_filter.mp hD₁
            exact mem_filter.mpr ⟨h.1, by have := h.2.2; omega⟩
      -- Bound `V (cut i) ≤ Real.exp (2 * S_i) * V z`.
      let S_i := ∑ q ∈ Q i, (q : ℝ)⁻¹
      have hV_ratio : V (cut i) ≤ Real.exp (2 * S_i) * V z := by
        have hVsplit : V z = V (cut i) * ∏ q ∈ Q i, (1 - (q : ℝ)⁻¹) := by
          dsimp [V]
          rw [show (range (z + 1)).filter Nat.Prime = Q i ∪ P_lo from hQP_union.symm,
            Finset.prod_union hQP_disj, mul_comm]
        have hQprod_pos : 0 < ∏ q ∈ Q i, (1 - (q : ℝ)⁻¹) :=
          eulerProd_pos_finset _ fun _ hq => (mem_filter.mp hq).2
        have hQinv : (∏ q ∈ Q i, (1 - (q : ℝ)⁻¹))⁻¹ ≤ Real.exp (2 * S_i) := by
          rw [← Finset.prod_inv_distrib, Finset.mul_sum, Real.exp_sum]
          apply Finset.prod_le_prod
          · intro q hq
            have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (mem_filter.mp hq).2.two_le
            have hinv : (q : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hq2
            exact inv_nonneg.mpr (by linarith)
          · intro q hq
            exact one_sub_inv_inv_le_exp_two (mem_filter.mp hq).2.two_le
        rw [hVsplit]
        calc
          V (cut i) = V (cut i) * ((∏ q ∈ Q i, (1 - (q : ℝ)⁻¹))⁻¹ *
              (∏ q ∈ Q i, (1 - (q : ℝ)⁻¹))) := by
            rw [inv_mul_cancel₀ hQprod_pos.ne', mul_one]
          _ ≤ V (cut i) * (Real.exp (2 * S_i) * (∏ q ∈ Q i, (1 - (q : ℝ)⁻¹))) := by
            gcongr
            exact (eulerProd_pos_finset _ fun _ hp => (mem_filter.mp hp).2).le
          _ = Real.exp (2 * S_i) * (V (cut i) * ∏ q ∈ Q i, (1 - (q : ℝ)⁻¹)) := by ring
      have hS_i : S_i ≤ 18 + 2 * (i : ℝ) := by
        have hcut_eq : cut i = min z (2 ^ (L / 2 ^ i)) := if_neg (by omega)
        dsimp [S_i, Q]
        rw [hcut_eq]
        exact brun_block_recip_sum_le hz16 hi'.1
      have htail := brun_tail_bound (Q i) (2 * bf i)
      have hcomb_exp : -(2 * bf i : ℕ) + Real.exp 1 * S_i + 2 * S_i ≤
          A - 2 * (b : ℝ) - 2 * (i : ℝ) := by
        have hS_nn : 0 ≤ S_i := Finset.sum_nonneg fun _ _ => by positivity
        have h1 : (2 + Real.exp 1) * S_i ≤ (K₀ : ℝ) * (18 + 2 * (i : ℝ)) :=
          mul_le_mul hK₀ hS_i hS_nn (by positivity)
        have hbf_cast : ((2 * bf i : ℕ) : ℝ) = 2 * (b : ℝ) + 2 * ((K₀ : ℝ) + 1) * (i : ℝ) := by
          dsimp [bf, K]
          push_cast
          ring
        rw [hbf_cast]
        dsimp [A]
        linarith
      have hexp_half : Real.exp (-2 * (i : ℝ)) ≤ (1 / 2 : ℝ) ^ i := by
        have h2e : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
        have he_le : Real.exp (-2 : ℝ) ≤ 1 / 2 := by
          rw [Real.exp_neg, inv_eq_one_div]
          exact one_div_le_one_div_of_le (by norm_num) h2e
        have hpow : Real.exp (-2 * (i : ℝ)) = (Real.exp (-2 : ℝ)) ^ i := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
        rw [hpow]
        exact pow_le_pow_left₀ (by positivity) he_le i
      calc
        |∑ D₁ ∈ A_i, (-1 : ℝ) ^ D₁.card * (∏ p ∈ D₁, (p : ℝ)⁻¹)| * V (cut i)
            ≤ Real.exp (-(2 * bf i : ℕ) + Real.exp 1 * S_i) * (Real.exp (2 * S_i) * V z) := by
          exact mul_le_mul (hAi_le.trans htail) hV_ratio
            (eulerProd_pos_finset _ fun _ hp => (mem_filter.mp hp).2).le (by positivity)
        _ = Real.exp (-(2 * bf i : ℕ) + Real.exp 1 * S_i + 2 * S_i) * V z := by
          rw [← mul_assoc, ← Real.exp_add]
        _ ≤ Real.exp (A - 2 * (b : ℝ) - 2 * (i : ℝ)) * V z := by
          exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcomb_exp) hVz_pos.le
        _ = Real.exp (A - 2 * (b : ℝ)) * Real.exp (-2 * (i : ℝ)) * V z := by
          rw [← Real.exp_add]
          congr 2
          ring
        _ ≤ Real.exp (A - 2 * (b : ℝ)) * ((1 / 2 : ℝ) ^ i) * V z := by
          have h1 := mul_le_mul_of_nonneg_left hexp_half (by positivity : 0 ≤ Real.exp (A - 2 * (b : ℝ)))
          exact mul_le_mul_of_nonneg_right h1 hVz_pos.le
    calc
      |∑ i ∈ Icc 1 r, ∑ D ∈ Bad i, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹)|
          ≤ ∑ i ∈ Icc 1 r, |∑ D ∈ Bad i, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Icc 1 r, Real.exp (A - 2 * (b : ℝ)) * ((1 / 2 : ℝ) ^ i) * V z :=
        Finset.sum_le_sum hterm_i
      _ = Real.exp (A - 2 * (b : ℝ)) * (∑ i ∈ Icc 1 r, (1 / 2 : ℝ) ^ i) * V z := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ Real.exp (A - 2 * (b : ℝ)) * 1 * V z := by
        have h1 := mul_le_mul_of_nonneg_left (geom_half_sum_le_one r)
          (by positivity : 0 ≤ Real.exp (A - 2 * (b : ℝ)))
        exact mul_le_mul_of_nonneg_right h1 hVz_pos.le
      _ = Real.exp (A - 2 * (b : ℝ)) * V z := by rw [mul_one]
  -- Step 4: Bound `D_brun.card ≤ z ^ (4 * b + 8 * K)` using `brun_prod_le`.
  have hD_card : D_brun.card ≤ z ^ (4 * b + 8 * K) := by
    have hsub_D : D_brun ⊆ P_all.powerset := Finset.filter_subset _ _
    have hinj : Set.InjOn (fun D : Finset ℕ => ∏ p ∈ D, p) (D_brun : Set (Finset ℕ)) :=
      (prime_finset_prod_injOn P_all fun _ hp => (mem_filter.mp hp).2).mono
        (Finset.coe_subset.mpr hsub_D)
    have hmaps : Set.MapsTo (fun D : Finset ℕ => ∏ p ∈ D, p) (D_brun : Set (Finset ℕ))
        (Icc 1 (z ^ (4 * b + 8 * K)) : Set ℕ) := by
      intro D hD
      rw [mem_coe] at hD ⊢
      have hDp := mem_filter.mp hD
      have hDsub : D ⊆ P_all := mem_powerset.mp hDp.1
      have hpos : 1 ≤ ∏ p ∈ D, p :=
        Finset.prod_pos fun p hp => (mem_filter.mp (hDsub hp)).2.pos
      have hle : ∏ p ∈ D, p ≤ z ^ (4 * b + 8 * K) := brun_prod_le hz16 hb1 D hDsub hDp.2
      exact mem_Icc.mpr ⟨hpos, hle⟩
    have hle := Finset.card_le_card_of_injOn (fun D : Finset ℕ => ∏ p ∈ D, p) hmaps hinj
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hle
  -- Step 5: Verify both error terms are at most `(δ / (2 * s ^ 3)) * y * V z`.
  have herr_trunc : Real.exp (A - 2 * (b : ℝ)) ≤ δ / (2 * (s : ℝ) ^ 3) := by
    have hs_le : (s : ℝ) ≤ (20 + 16 * (K : ℝ)) * (b : ℝ) := by
      have hb1_r : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb1
      have hs_hi_r : (s : ℝ) ≤ 8 * (b : ℝ) + 16 * (K : ℝ) + 11 := by exact_mod_cast hs_hi
      nlinarith
    have hs3_le : (s : ℝ) ^ 3 ≤ C₁ * (b : ℝ) ^ 3 := by
      dsimp [C₁]
      calc
        (s : ℝ) ^ 3 ≤ ((20 + 16 * (K : ℝ)) * (b : ℝ)) ^ 3 :=
          pow_le_pow_left₀ (Nat.cast_nonneg s) hs_le 3
        _ = (20 + 16 * (K : ℝ)) ^ 3 * (b : ℝ) ^ 3 := mul_pow _ _ 3
    have hb_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
    have hexp_ge : (2 * (b : ℝ)) ^ 4 / 256 ≤ Real.exp (2 * (b : ℝ)) :=
      pow_four_div_le_exp (by positivity)
    have h1 : Real.exp (A - 2 * (b : ℝ)) ≤ 16 * Real.exp A / (b : ℝ) ^ 4 := by
      rw [Real.exp_sub, div_le_div_iff₀ (by positivity) (by positivity)]
      have : 16 * Real.exp A * ((2 * (b : ℝ)) ^ 4 / 256) = Real.exp A * (b : ℝ) ^ 4 := by ring
      nlinarith [mul_le_mul_of_nonneg_left hexp_ge (by positivity : 0 ≤ 16 * Real.exp A)]
    have hb_ge : 32 * Real.exp A * C₁ / δ ≤ (b : ℝ) := by
      have h1' : (b₀ : ℝ) ≤ (b : ℝ) := by exact_mod_cast (show b₀ ≤ b by omega)
      exact hb₀.trans h1'
    have h2 : 16 * Real.exp A / (b : ℝ) ^ 4 ≤ δ / (2 * (s : ℝ) ^ 3) := by
      have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (show 0 < s by omega)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hkey : 32 * Real.exp A * C₁ ≤ δ * (b : ℝ) := by
        rw [mul_comm δ]
        exact (div_le_iff₀ hδ).mp hb_ge
      have hkey2 : 32 * Real.exp A * (C₁ * (b : ℝ) ^ 3) ≤ δ * (b : ℝ) ^ 4 := by
        calc
          32 * Real.exp A * (C₁ * (b : ℝ) ^ 3) = (32 * Real.exp A * C₁) * (b : ℝ) ^ 3 := by ring
          _ ≤ (δ * (b : ℝ)) * (b : ℝ) ^ 3 := mul_le_mul_of_nonneg_right hkey (by positivity)
          _ = δ * (b : ℝ) ^ 4 := by ring
      have hkey3 : 32 * Real.exp A * (s : ℝ) ^ 3 ≤ 32 * Real.exp A * (C₁ * (b : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left hs3_le (by positivity)
      linarith
    exact h1.trans h2
  have herr_crt : (D_brun.card : ℝ) ≤ (δ / (2 * (s : ℝ) ^ 3)) * ((y : ℝ) * V z) := by
    have hz_pos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast (show 0 < z by omega)
    have hVz_ge : (z : ℝ)⁻¹ ≤ V z := eulerProd_ge_inv (by omega)
    have hD_le_z : (D_brun.card : ℝ) ≤ (z : ℝ)⁻¹ * ((y : ℝ) * V z) := by
      have hpow_nat : z ^ (4 * b + 8 * K) * z ^ 2 ≤ z ^ s := by
        rw [← pow_add]
        exact Nat.pow_le_pow_right (by omega) (by omega)
      have hpow_y : ((z ^ (4 * b + 8 * K) : ℕ) : ℝ) * ((z : ℝ) ^ 2) ≤ (y : ℝ) := by
        exact_mod_cast hpow_nat.trans hzy
      have hcard_r : (D_brun.card : ℝ) ≤ ((z ^ (4 * b + 8 * K) : ℕ) : ℝ) := by
        exact_mod_cast hD_card
      have hcard_y : (D_brun.card : ℝ) ≤ (z : ℝ)⁻¹ * ((y : ℝ) * (z : ℝ)⁻¹) := by
        have h1 : (D_brun.card : ℝ) * (z : ℝ) ^ 2 ≤ (y : ℝ) :=
          (mul_le_mul_of_nonneg_right hcard_r (by positivity)).trans hpow_y
        have h2 : (D_brun.card : ℝ) ≤ (y : ℝ) / (z : ℝ) ^ 2 :=
          (le_div_iff₀ (by positivity)).mpr h1
        have h3 : (y : ℝ) / (z : ℝ) ^ 2 = (z : ℝ)⁻¹ * ((y : ℝ) * (z : ℝ)⁻¹) := by
          field_simp
        rwa [h3] at h2
      have h4 : (z : ℝ)⁻¹ * ((y : ℝ) * (z : ℝ)⁻¹) ≤ (z : ℝ)⁻¹ * ((y : ℝ) * V z) := by
        gcongr
      exact hcard_y.trans h4
    have hz_ge : 2 * (s : ℝ) ^ 3 / δ ≤ (z : ℝ) := by
      have h1 : (Z₁ : ℝ) ≤ (z : ℝ) := by exact_mod_cast (show Z₁ ≤ z by omega)
      exact hZ₁.trans h1
    have hinv_le : (z : ℝ)⁻¹ ≤ δ / (2 * (s : ℝ) ^ 3) := by
      have hs_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (show 0 < s by omega)
      have hs3_pos : (0 : ℝ) < 2 * (s : ℝ) ^ 3 := by positivity
      rw [inv_eq_one_div, div_le_div_iff₀ hz_pos hs3_pos, one_mul, mul_comm δ]
      exact (div_le_iff₀ hδ).mp hz_ge
    exact hD_le_z.trans (mul_le_mul_of_nonneg_right hinv_le (by positivity))
  -- Final assembly.
  have hmain_hi :
      ∑ D ∈ D_brun, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹) ≤
        (1 + δ / (2 * (s : ℝ) ^ 3)) * V z := by
    have h1 := (abs_le.mp htrunc).1
    have h2 : Real.exp (A - 2 * (b : ℝ)) * V z ≤ (δ / (2 * (s : ℝ) ^ 3)) * V z :=
      mul_le_mul_of_nonneg_right herr_trunc hVz_pos.le
    linarith
  have hmain_mul :
      (y : ℝ) * (∑ D ∈ D_brun, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹)) ≤
        (1 + δ / (2 * (s : ℝ) ^ 3)) * ((y : ℝ) * V z) := by
    have h := mul_le_mul_of_nonneg_left hmain_hi (Nat.cast_nonneg y)
    linarith
  have hcomb :
      (y : ℝ) * (∑ D ∈ D_brun, (-1 : ℝ) ^ D.card * (∏ p ∈ D, (p : ℝ)⁻¹)) + (D_brun.card : ℝ) ≤
        (1 + δ / (s : ℝ) ^ 3) * (y : ℝ) * V z := by
    have hs_eq : (1 + δ / (s : ℝ) ^ 3) * (y : ℝ) * V z =
        (1 + δ / (2 * (s : ℝ) ^ 3)) * ((y : ℝ) * V z) +
          (δ / (2 * (s : ℝ) ^ 3)) * ((y : ℝ) * V z) := by
      ring
    rw [hs_eq]
    linarith
  exact (hstep1.trans hstep2).trans hcomb
