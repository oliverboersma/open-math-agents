import FormalConjectures.ErdosProblems.«1191»

/-!
# Nearby-scale block packing plus an additive label code for Erdős problem 1191(ii)

H1 asks, at every finite horizon, for dense Sidon sets in the dyadic blocks whose
positive differences avoid those of blocks at nearby scales j/3 < i < j. Collisions
with distant scales are removed by pruning short differences, at the cost of one log
power. H2 asks for an additive code that remembers the pair of dyadic labels of a sum,
with polynomial loss in the label. The code makes the union of pruned blocks Sidon, and
a compactness argument on Boolean sequences passes from finite witnesses to an infinite
set with the required liminf.
-/

-- Credit: @mucoucah

namespace OMA.R_Erdos1191_erdos_1191_parts_ii_R2

open Filter Set
open scoped Topology

/-- A squared lower bound at the dyadic cutoffs suffices for the liminf. -/
lemma density_from_dyadic_counts (A : Set ℕ) (d J : ℕ)
    (h : ∀ j ≥ J, 2 ^ j ≤ (A ∩ Icc 1 (2 ^ j)).ncard ^ 2 * (j + 1) ^ (2 * (d + 1))) :
    ∃ c > (0 : ℝ), 0 < liminf (fun x : ℕ ↦ ENNReal.ofReal
      ((A ∩ Icc 1 x).ncard / (x : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ c)) atTop := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let c : ℕ := 2 * (d + 1)
  refine ⟨(c : ℝ), by dsimp [c]; positivity, ?_⟩
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ x : ℕ in atTop, 2 / Real.log 2 ≤ Real.log (x : ℝ) :=
    hlog.eventually_ge_atTop _
  have hpoint : ∀ᶠ x : ℕ in atTop,
      (1 / 2 : ℝ) ≤ (A ∩ Icc 1 x).ncard / (x : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (c : ℝ) := by
    filter_upwards [hlarge, eventually_ge_atTop (2 ^ max J 1 : ℕ)] with x hx hxpow
    let j := Nat.log 2 x
    have hj : max J 1 ≤ j := Nat.le_log_of_pow_le (by decide) hxpow
    have hJ : J ≤ j := (le_max_left _ _).trans hj
    have hj1 : 1 ≤ j := (le_max_right _ _).trans hj
    have hx0 : 0 < x := (pow_pos (by decide) _ : 0 < 2 ^ max J 1).trans_le hxpow
    have hlo : 2 ^ j ≤ x := Nat.pow_log_le_self 2 hx0.ne'
    have hhi : x ≤ 2 * 2 ^ j := by
      simpa only [pow_succ, mul_comm] using (Nat.lt_pow_succ_log_self (by decide : 1 < 2) x).le
    have hcount : (A ∩ Icc 1 (2 ^ j)).ncard ≤ (A ∩ Icc 1 x).ncard :=
      Set.ncard_le_ncard (inter_subset_inter_right _ (Icc_subset_Icc_right hlo))
        ((finite_Icc 1 x).subset inter_subset_right)
    have hjlog : (j : ℝ) * Real.log 2 ≤ Real.log (x : ℝ) := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) (by exact_mod_cast hlo)
    have hlog0 : 0 ≤ Real.log (x : ℝ) := Real.log_natCast_nonneg x
    have hlogsq : 2 ≤ Real.log (x : ℝ) * Real.log 2 := (div_le_iff₀ hlog2).1 hx
    have hjreal : 1 ≤ (j : ℝ) := by exact_mod_cast hj1
    have hjbase : (j : ℝ) + 1 ≤ Real.log (x : ℝ) ^ 2 := by
      calc
        _ ≤ (j : ℝ) * 2 := by linarith
        _ ≤ (j : ℝ) * (Real.log (x : ℝ) * Real.log 2) :=
          mul_le_mul_of_nonneg_left hlogsq (Nat.cast_nonneg j)
        _ = Real.log (x : ℝ) * ((j : ℝ) * Real.log 2) := by ring
        _ ≤ _ := by simpa only [pow_two] using mul_le_mul_of_nonneg_left hjlog hlog0
    let m : ℝ := (A ∩ Icc 1 (2 ^ j)).ncard
    have hroot : Real.sqrt ((2 : ℝ) ^ j) ≤ m * ((j : ℝ) + 1) ^ (d + 1) := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity, ?_⟩
      rw [mul_pow, ← pow_mul, mul_comm (d + 1) 2]
      dsimp [m]
      exact_mod_cast h j hJ
    have hscale : Real.sqrt (x : ℝ) ≤ 2 * Real.sqrt ((2 : ℝ) ^ j) := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity, ?_⟩
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      apply le_trans (show (x : ℝ) ≤ 2 * (2 : ℝ) ^ j by exact_mod_cast hhi)
      nlinarith [show 0 ≤ (2 : ℝ) ^ j by positivity]
    have hweighted : m * ((j : ℝ) + 1) ^ (d + 1) ≤
        (A ∩ Icc 1 x).ncard * Real.log (x : ℝ) ^ (c : ℝ) := by
      rw [Real.rpow_natCast, show c = 2 * (d + 1) from rfl, pow_mul]
      apply mul_le_mul (by dsimp [m]; exact_mod_cast hcount)
        (pow_le_pow_left₀ (by positivity) hjbase _) (by positivity) (Nat.cast_nonneg _)
    rw [← Real.sqrt_eq_rpow, div_mul_eq_mul_div₀]
    apply (le_div_iff₀ (Real.sqrt_pos.2 (by exact_mod_cast hx0))).2
    linarith [hscale, hroot, hweighted]
  exact (ENNReal.ofReal_pos.mpr (by norm_num : (0 : ℝ) < 1 / 2)).trans_le
    (le_liminf_of_le (h := hpoint.mono fun _ hx ↦ ENNReal.ofReal_le_ofReal hx))

/-- A property of finitely many coordinates of a Boolean sequence is closed. -/
lemma closed_prefix_condition (n : ℕ) (P : (ℕ → Bool) → Prop)
    (hP : ∀ f g, (∀ i ≤ n, f i = g i) → P f → P g) : IsClosed {f | P f} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro f hf
  have hagree : ∀ᶠ g in 𝓝 f, ∀ i ∈ Finset.range (n + 1), g i = f i := by
    refine (eventually_all_finset _).mpr fun i _ ↦ ?_
    have hopen : IsOpen ((fun g : ℕ → Bool ↦ g i) ⁻¹' {f i}) :=
      (isOpen_discrete _).preimage (continuous_apply i)
    exact hopen.mem_nhds (by simp)
  exact hagree.mono fun g hg hPg ↦ hf (hP g f
    (fun i hi ↦ hg i (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))) hPg)

/-- Compatible finite prefix constraints have a common Boolean solution. -/
lemma compact_prefix_conditions (P : ℕ → (ℕ → Bool) → Prop)
    (hloc : ∀ n f g, (∀ i ≤ n, f i = g i) → P n f → P n g)
    (hfin : ∀ N, ∃ f, ∀ n ≤ N, P n f) : ∃ f, ∀ n, P n f := by
  classical
  let C (n : ℕ) : Set (ℕ → Bool) := {f | P n f}
  have hnonempty := (isCompact_univ : IsCompact (univ : Set (ℕ → Bool))).inter_iInter_nonempty C
    (fun n ↦ closed_prefix_condition n (P n) (hloc n)) ?_
  · obtain ⟨f, _, hf⟩ := hnonempty
    exact ⟨f, mem_iInter.mp hf⟩
  · intro u
    obtain ⟨N, hN⟩ := (u.finite_toSet.bddAbove : BddAbove (u : Set ℕ))
    obtain ⟨f, hf⟩ := hfin N
    exact ⟨f, mem_univ _, mem_iInter₂.mpr fun n hn ↦ hf n (hN hn)⟩

lemma infinite_of_dyadic_counts (A : Set ℕ) (d J : ℕ)
    (h : ∀ j ≥ J, 2 ^ j ≤ (A ∩ Icc 1 (2 ^ j)).ncard ^ 2 * (j + 1) ^ (2 * (d + 1))) :
    A.Infinite := by
  intro hfin
  let M : ℝ := (A.ncard : ℝ) ^ 2
  let k : ℕ := 2 * (d + 1)
  have hM : 0 ≤ M := sq_nonneg _
  have hdecay : Tendsto (fun j : ℕ ↦ (2 * M) * (((j + 1 : ℕ) : ℝ) ^ k / 2 ^ (j + 1)))
      atTop (𝓝 (0 : ℝ)) := by
    have hbase := tendsto_pow_const_div_const_pow_of_one_lt k (by norm_num : (1 : ℝ) < 2)
    simpa only [Function.comp_apply, mul_zero] using
      (hbase.comp (tendsto_add_atTop_nat 1)).const_mul (2 * M)
  obtain ⟨j, hj, hsmall⟩ := ((eventually_ge_atTop J).and
    (hdecay.eventually_lt_const (by norm_num : (0 : ℝ) < 1))).exists
  have hcount : ((A ∩ Icc 1 (2 ^ j)).ncard : ℝ) ≤ A.ncard := by
    exact_mod_cast (Set.ncard_le_ncard inter_subset_left hfin)
  have hcast : (2 : ℝ) ^ j ≤ ((A ∩ Icc 1 (2 ^ j)).ncard : ℝ) ^ 2 * ((j : ℝ) + 1) ^ k := by
    exact_mod_cast h j hj
  have hlower : (2 : ℝ) ^ j ≤ M * ((j : ℝ) + 1) ^ k :=
    hcast.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hcount 2) (by positivity))
  rw [Nat.cast_add, Nat.cast_one, pow_succ, ← mul_div_assoc] at hsmall
  have hnum := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ j * 2)).mp hsmall
  linarith

lemma sidon_of_finite_dyadic_witnesses (d J : ℕ) (h : ∀ N : ℕ, ∃ S : Set ℕ, S ⊆ Icc 1 (2 ^ N) ∧ IsSidon S ∧
      ∀ j, J ≤ j → j ≤ N → 2 ^ j ≤ (S ∩ Icc 1 (2 ^ j)).ncard ^ 2 * (j + 1) ^ (2 * (d + 1))) :
    ∃ A : Set ℕ, IsSidon A ∧
      ∀ j ≥ J, 2 ^ j ≤ (A ∩ Icc 1 (2 ^ j)).ncard ^ 2 * (j + 1) ^ (2 * (d + 1)) := by
  classical
  let cut (f : ℕ → Bool) (n : ℕ) : Set ℕ := {a | f a = true} ∩ Icc 1 n
  let P (n : ℕ) (f : ℕ → Bool) : Prop := IsSidon (cut f n) ∧
    ∀ j, J ≤ j → 2 ^ j ≤ n →
      2 ^ j ≤ (cut f n ∩ Icc 1 (2 ^ j)).ncard ^ 2 * (j + 1) ^ (2 * (d + 1))
  obtain ⟨f, hf⟩ : ∃ f, ∀ n, P n f := by
    apply compact_prefix_conditions P
    · intro n f g hagree hf
      have hcut : cut f n = cut g n := by
        ext a
        constructor
        · rintro ⟨ha, hn⟩
          exact ⟨(hagree a hn.2).symm.trans (show f a = true from ha), hn⟩
        · rintro ⟨ha, hn⟩
          exact ⟨(hagree a hn.2).trans (show g a = true from ha), hn⟩
      simpa only [P, hcut] using hf
    · intro N
      obtain ⟨S, _, hSidon, hcount⟩ := h N
      let f : ℕ → Bool := fun a ↦ decide (a ∈ S)
      refine ⟨f, fun n hn ↦ ?_⟩
      have hcut : cut f n = S ∩ Icc 1 n := by
        ext a
        simp [cut, f]
      dsimp only [P]
      rw [hcut]
      refine ⟨?_, fun j hJ hj ↦ ?_⟩
      · intro a ha b hb c hc e he hsum
        exact hSidon a ha.1 b hb.1 c hc.1 e he.1 hsum
      · rw [inter_assoc, inter_eq_right.mpr (Icc_subset_Icc_right hj)]
        have hle : (2 : ℕ) ^ j ≤ 2 ^ N := hj.trans (hn.trans N.lt_two_pow_self.le)
        exact hcount j hJ ((pow_le_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mp hle)
  let A := {a | f a = true} ∩ Ici 1
  have hcut (n : ℕ) : A ∩ Icc 1 n = cut f n := by
    dsimp only [A, cut]
    rw [inter_assoc, inter_eq_right.mpr Icc_subset_Ici_self]
  refine ⟨A, ?_, fun j hj ↦ ?_⟩
  · intro a ha b hb c hc e he hsum
    let n := a + b + c + e
    have hm (x : ℕ) (hx : x ∈ A) (hn : x ≤ n) : x ∈ cut f n := by
      rw [← hcut]
      exact ⟨hx, hx.2, hn⟩
    exact (hf n).1 a (hm a ha (by dsimp [n]; omega)) b (hm b hb (by dsimp [n]; omega))
      c (hm c hc (by dsimp [n]; omega)) e (hm e he (by dsimp [n]; omega)) hsum
  · have hcount := (hf (2 ^ j)).2 j hj le_rfl
    simpa only [← hcut, inter_assoc, inter_self] using hcount

lemma sidon_positive_difference_unique (S : Finset ℕ) (hS : IsSidon (S : Set ℕ))
    {a b u v : ℕ} (ha : a ∈ S) (hb : b ∈ S) (hu : u ∈ S) (hv : v ∈ S)
    (hba : b < a) (hvu : v < u) (heq : a - b = u - v) : a = u ∧ b = v := by
  have hadd : a + v = u + b := by omega
  rcases hS a ha u hu v hv b hb hadd with h | h
  · exact ⟨h.1, h.2.symm⟩
  · omega

/-- Removing one endpoint for each short positive difference costs at most t points. -/
lemma prune_short_differences (S : Finset ℕ) (hS : IsSidon (S : Set ℕ)) (t : ℕ) :
    ∃ T ⊆ S, S.card ≤ T.card + t ∧ ∀ a ∈ T, ∀ b ∈ T, b < a → t ≤ a - b := by
  let bad := (S.product S).filter fun p ↦ p.2 < p.1 ∧ p.1 - p.2 < t
  let drop := bad.image Prod.fst
  have hbad : bad.card ≤ t := by
    rw [← Finset.card_range t]
    apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ ↦ p.1 - p.2)
    · intro p hp
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2.2
    · intro p hp q hq heq
      obtain ⟨hab, hp₁, _⟩ := Finset.mem_filter.mp hp
      obtain ⟨huv, hq₁, _⟩ := Finset.mem_filter.mp hq
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
      obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
      obtain ⟨h₁, h₂⟩ := sidon_positive_difference_unique S hS ha hb hu hv hp₁ hq₁ heq
      exact Prod.ext h₁ h₂
  have hsubset : drop ⊆ S := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  have hdrop : drop.card ≤ t := Finset.card_image_le.trans hbad
  refine ⟨S \ drop, Finset.sdiff_subset, ?_, ?_⟩
  · rw [Finset.card_sdiff_of_subset hsubset]
    omega
  · intro a ha b hb hba
    by_contra! hlt
    obtain ⟨haS, haD⟩ := Finset.mem_sdiff.mp ha
    have hbS := (Finset.mem_sdiff.mp hb).1
    have hp : (a, b) ∈ bad := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨haS, hbS⟩, hba, hlt⟩
    exact haD (Finset.mem_image.mpr ⟨(a, b), hp, rfl⟩)

/-- Interactions between dyadic scales with i ≤ j/3 can be removed at low cost. -/
lemma prune_distant_dyadic_collisions
    (B : ℕ → Finset ℕ) (hpos : ∀ j, B j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1)))
    (hSidon : ∀ j, IsSidon (B j : Set ℕ))
    (hneighbors : ∀ i j, j / 3 < i → i < j →
      ∀ a ∈ B i, ∀ b ∈ B i, ∀ u ∈ B j, ∀ v ∈ B j,
        b < a → v < u → a - b ≠ u - v) :
    ∃ C : ℕ → Finset ℕ, (∀ j, C j ⊆ B j ∧ (B j).card ≤ (C j).card + 2 ^ (j / 3)) ∧
      ∀ i j, i < j → ∀ a ∈ C i, ∀ b ∈ C i, ∀ u ∈ C j, ∀ v ∈ C j,
        b < a → v < u → a - b ≠ u - v := by
  choose C hsub hcount hsep using fun j ↦
    prune_short_differences (B j) (hSidon j) (2 ^ (j / 3))
  refine ⟨C, fun j ↦ ⟨hsub j, hcount j⟩, ?_⟩
  intro i j hij a ha b hb u hu v hv hba hvu
  by_cases hnear : j / 3 < i
  · exact hneighbors i j hnear hij a (hsub i ha) b (hsub i hb)
      u (hsub j hu) v (hsub j hv) hba hvu
  · have hcap : (2 : ℕ) ^ i ≤ 2 ^ (j / 3) :=
      pow_le_pow_right₀ (by decide) (le_of_not_gt hnear)
    have htop := (Finset.mem_Ico.mp (hpos i (hsub i ha))).2
    have hbot := (Finset.mem_Ico.mp (hpos i (hsub i hb))).1
    rw [pow_succ] at htop
    have hgap : a - b < (2 : ℕ) ^ i := by omega
    exact ((hgap.trans_le hcap).trans_le (hsep j u hu v hv hvu)).ne

/-- The squared deletion budget times any fixed polynomial is negligible. -/
lemma eventually_dyadic_pruning_budget (k : ℕ) :
    ∀ᶠ j : ℕ in atTop, 4 * (2 ^ (j / 3)) ^ 2 * (j + 1) ^ k ≤ 2 ^ j := by
  have hdecay := (tendsto_pow_const_div_const_pow_of_one_lt k (by norm_num : (1 : ℝ) < 2)).comp
    (tendsto_add_atTop_nat 1)
  have hlim : Tendsto (fun n : ℕ ↦ (8 * 3 ^ k : ℝ) *
      (((n + 1 : ℕ) : ℝ) ^ k / 2 ^ (n + 1))) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_apply, mul_zero] using hdecay.const_mul (8 * 3 ^ k : ℝ)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1))
  refine (eventually_ge_atTop (3 * N)).mono fun j hj ↦ ?_
  let n := j / 3
  have hn : N ≤ n := by dsimp [n]; omega
  have hpoly : 4 * 3 ^ k * (n + 1) ^ k ≤ (2 : ℕ) ^ n := by
    have hsmall := hN n hn
    rw [Nat.cast_add, Nat.cast_one, pow_succ, ← mul_div_assoc] at hsmall
    have hnum := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ n * 2)).mp hsmall
    have hcast : (4 : ℝ) * 3 ^ k * ((n : ℝ) + 1) ^ k ≤ 2 ^ n := by linarith
    exact_mod_cast hcast
  have hbound : j + 1 ≤ 3 * (n + 1) := by dsimp [n]; omega
  calc
    _ ≤ 4 * (2 ^ n) ^ 2 * (3 * (n + 1)) ^ k :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbound _)
    _ = (2 ^ n) ^ 2 * (4 * 3 ^ k * (n + 1) ^ k) := by rw [mul_pow]; ring
    _ ≤ (2 ^ n) ^ 2 * 2 ^ n := Nat.mul_le_mul_left _ hpoly
    _ = 2 ^ (n * 2 + n) := by rw [pow_add, pow_mul]
    _ ≤ 2 ^ j := pow_le_pow_right₀ (by decide) (by dsimp [n]; omega)

/-- After pruning, one extra power of the dyadic index absorbs the loss. -/
lemma eventually_dyadic_pruning_preserves_count (d : ℕ) :
    ∀ᶠ j : ℕ in atTop, ∀ M m : ℕ,
      2 ^ j ≤ M ^ 2 * (j + 1) ^ (2 * (d + 1)) →
      M ≤ m + 2 ^ (j / 3) →
      2 ^ j ≤ m ^ 2 * (j + 1) ^ (2 * (d + 2)) := by
  filter_upwards [eventually_dyadic_pruning_budget (2 * (d + 1)), eventually_ge_atTop (1 : ℕ)]
    with j hbudget hj M m hM hm
  let q : ℝ := (j : ℝ) + 1
  let t : ℝ := (2 : ℝ) ^ (j / 3)
  let x : ℝ := (2 : ℝ) ^ j
  have hq : 2 ≤ q := by
    have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
    dsimp [q]
    linarith
  have hq0 : 0 ≤ q := by linarith
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hm' : (M : ℝ) ≤ (m : ℝ) + t := by dsimp [t]; exact_mod_cast hm
  have hroot : Real.sqrt x ≤ (M : ℝ) * q ^ (d + 1) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, ← pow_mul, mul_comm (d + 1) 2]
    dsimp [x, q]
    exact_mod_cast hM
  have hhalf : 2 * t * q ^ (d + 1) ≤ Real.sqrt x := by
    apply (Real.le_sqrt (by positivity) hx).mpr
    rw [mul_pow, mul_pow, ← pow_mul q, mul_comm (d + 1) 2]
    norm_num only
    dsimp [t, x, q]
    exact_mod_cast hbudget
  have hremaining : Real.sqrt x ≤ 2 * (m : ℝ) * q ^ (d + 1) := by
    have hmul := mul_le_mul_of_nonneg_right hm' (pow_nonneg hq0 (d + 1))
    linarith only [hroot, hhalf, hmul]
  have hweighted : Real.sqrt x ≤ (m : ℝ) * q ^ (d + 2) := by
    apply hremaining.trans
    calc
      _ = ((m : ℝ) * q ^ (d + 1)) * 2 := by ring
      _ ≤ ((m : ℝ) * q ^ (d + 1)) * q := mul_le_mul_of_nonneg_left hq (by positivity)
      _ = _ := by rw [mul_assoc, ← pow_succ]
  have hfinal := (Real.sqrt_le_iff.mp hweighted).2
  rw [mul_pow, ← pow_mul, mul_comm (d + 2) 2] at hfinal
  dsimp [x, q] at hfinal
  exact_mod_cast hfinal


/-- Four points from two blocks with equal sums are trivial, given cross-block
difference disjointness and Sidon blocks. -/
lemma two_block_core (C : ℕ → Finset ℕ) (hS : ∀ j, IsSidon (C j : Set ℕ))
    (hcross : ∀ i j, i < j → ∀ a ∈ C i, ∀ b ∈ C i, ∀ u ∈ C j, ∀ v ∈ C j,
      b < a → v < u → a - b ≠ u - v)
    {p r a b u v : ℕ} (ha : a ∈ C p) (hb : b ∈ C r) (hu : u ∈ C p) (hv : v ∈ C r)
    (hs : a + b = u + v) : (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
  rcases lt_trichotomy p r with hpr | rfl | hpr
  · left
    rcases lt_trichotomy a u with h | h | h
    · exact (hcross p r hpr u hu a ha b hb v hv h (by omega) (by omega)).elim
    · exact ⟨h, by omega⟩
    · exact (hcross p r hpr a ha u hu v hv b hb h (by omega) (by omega)).elim
  · exact hS p a ha u hu b hb v hv hs
  · left
    rcases lt_trichotomy b v with h | h | h
    · exact (hcross r p hpr v hv b hb a ha u hu h (by omega) (by omega)).elim
    · exact ⟨by omega, h⟩
    · exact (hcross r p hpr b hb v hv u hu a ha h (by omega) (by omega)).elim

/-- Encoding a cross-disjoint block family by a label-preserving additive code gives a Sidon set. -/
lemma coded_union_sidon (C : ℕ → Finset ℕ) (hpos : ∀ j, C j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1)))
    (hS : ∀ j, IsSidon (C j : Set ℕ))
    (hcross : ∀ i j, i < j → ∀ a ∈ C i, ∀ b ∈ C i, ∀ u ∈ C j, ∀ v ∈ C j,
      b < a → v < u → a - b ≠ u - v)
    (E : ℕ → ℕ)
    (hsum : ∀ a b u v, E a + E b = E u + E v →
      a + b = u + v ∧
        ((Nat.log 2 a = Nat.log 2 u ∧ Nat.log 2 b = Nat.log 2 v) ∨
         (Nat.log 2 a = Nat.log 2 v ∧ Nat.log 2 b = Nat.log 2 u)))
    (I : Finset ℕ) : IsSidon ((I.biUnion fun j ↦ (C j).image E : Finset ℕ) : Set ℕ) := by
  have hlog : ∀ j a, a ∈ C j → Nat.log 2 a = j := fun j a ha ↦
    Nat.log_eq_of_pow_le_of_lt_pow (Finset.mem_Ico.mp (hpos j ha)).1
      (Finset.mem_Ico.mp (hpos j ha)).2
  have hmem : ∀ x, x ∈ ((I.biUnion fun j ↦ (C j).image E : Finset ℕ) : Set ℕ) →
      ∃ a, a ∈ C (Nat.log 2 a) ∧ E a = x := by
    intro x hx
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hx)
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hj
    exact ⟨a, by rw [hlog j a ha]; exact ha, rfl⟩
  intro x hx y hy z hz w hw hxz
  obtain ⟨a, ha, rfl⟩ := hmem x hx
  obtain ⟨u, hu, rfl⟩ := hmem y hy
  obtain ⟨b, hb, rfl⟩ := hmem z hz
  obtain ⟨v, hv, rfl⟩ := hmem w hw
  obtain ⟨hs, hl | hl⟩ := hsum a b u v hxz
  · rw [← hl.1] at hu
    rw [← hl.2] at hv
    rcases two_block_core C hS hcross ha hb hu hv hs with h | h
    · exact Or.inl ⟨by rw [h.1], by rw [h.2]⟩
    · exact Or.inr ⟨by rw [h.1], by rw [h.2]⟩
  · rw [← hl.1] at hv
    rw [← hl.2] at hu
    rcases two_block_core C hS hcross ha hb hv hu (by omega) with h | h
    · exact Or.inr ⟨by rw [h.1], by rw [h.2]⟩
    · exact Or.inl ⟨by rw [h.1], by rw [h.2]⟩

/-- A logarithmic shift is eventually dominated. -/
lemma eventually_log_shift (c c' : ℕ) :
    ∃ K, ∀ k ≥ K, c' + c * (Nat.log 2 (k + 2) + 1) ≤ k := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 2)
  let Q : ℝ := c' + 2 * c + 3
  have hQ : 0 < Q := by positivity
  obtain ⟨L0, hL0⟩ := eventually_atTop.mp
    ((h.eventually_lt_const (inv_pos.mpr hQ)).and (eventually_ge_atTop 1))
  refine ⟨c' + c * (L0 + 1) + 2, fun k hk ↦ ?_⟩
  by_cases hL : L0 ≤ Nat.log 2 (k + 2)
  · obtain ⟨hlt, hL1⟩ := hL0 _ hL
    set L := Nat.log 2 (k + 2)
    have hpow : 2 ^ L ≤ k + 2 := Nat.pow_log_le_self 2 (by omega)
    have hreal : Q * (L : ℝ) < 2 ^ L := by
      rw [pow_one, div_lt_iff₀ (by positivity)] at hlt
      have := mul_lt_mul_of_pos_left hlt hQ
      rwa [← mul_assoc, mul_inv_cancel₀ hQ.ne', one_mul] at this
    have hL1' : (1 : ℝ) ≤ L := by exact_mod_cast hL1
    have hnat : c' + c * (L + 1) + 2 < 2 ^ L := by
      have : ((c' + c * (L + 1) + 2 : ℕ) : ℝ) < 2 ^ L := by
        push_cast
        refine lt_of_le_of_lt ?_ hreal
        dsimp [Q]
        nlinarith [show (0 : ℝ) ≤ c by positivity, show (0 : ℝ) ≤ c' by positivity]
      exact_mod_cast this
    omega
  · have : c * (Nat.log 2 (k + 2) + 1) ≤ c * (L0 + 1) := Nat.mul_le_mul_left _ (by omega)
    omega

/-- Finite Sidon witnesses from pruned dense blocks and a polylogarithmic additive code. -/
lemma coded_finite_witness (d J : ℕ)
    (hB : ∀ N : ℕ, ∃ B : ℕ → Finset ℕ,
      (∀ j, B j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1))) ∧
      (∀ j, ∀ a ∈ B j, ∀ b ∈ B j, ∀ u ∈ B j, ∀ v ∈ B j,
        a + b = u + v → (a = u ∧ b = v) ∨ (a = v ∧ b = u)) ∧
      (∀ j, J ≤ j → j ≤ N → 2 ^ j ≤ (B j).card ^ 2 * (j + 1) ^ (2 * (d + 1))) ∧
      ∀ i j, j / 3 < i → i < j → ∀ a ∈ B i, ∀ b ∈ B i, ∀ u ∈ B j, ∀ v ∈ B j,
        b < a → v < u → a - b ≠ u - v)
    (E : ℕ → ℕ) (e : ℕ)
    (hsum : ∀ a b u v, E a + E b = E u + E v →
      a + b = u + v ∧
        ((Nat.log 2 a = Nat.log 2 u ∧ Nat.log 2 b = Nat.log 2 v) ∨
         (Nat.log 2 a = Nat.log 2 v ∧ Nat.log 2 b = Nat.log 2 u)))
    (hsize : ∀ j, ∀ a ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), 1 ≤ E a ∧ E a ≤ 2 ^ j * (j + 2) ^ e) :
    ∃ D J₀ : ℕ, ∀ N : ℕ, ∃ S : Set ℕ, S ⊆ Icc 1 (2 ^ N) ∧ IsSidon S ∧
      ∀ j, J₀ ≤ j → j ≤ N → 2 ^ j ≤ (S ∩ Icc 1 (2 ^ j)).ncard ^ 2 * (j + 1) ^ (2 * (D + 1)) := by
  classical
  obtain ⟨J₁, hJ₁⟩ := eventually_atTop.mp (eventually_dyadic_pruning_preserves_count d)
  obtain ⟨K, hK⟩ := eventually_log_shift e (max J J₁)
  have hEinj : Function.Injective E := by
    intro a b hab
    have h := (hsum a a b b (by rw [hab])).1
    omega
  refine ⟨d + 2 + 3 * e, max K 1, fun N ↦ ?_⟩
  obtain ⟨B, hpos, hBS, hcounts, hnear⟩ := hB N
  have hSid : ∀ j, IsSidon (B j : Set ℕ) := fun j a ha u hu b hb v hv h ↦
    hBS j a ha b hb u hu v hv h
  obtain ⟨C, hC, hcross⟩ := prune_distant_dyadic_collisions B hpos hSid hnear
  have hCpos : ∀ j, C j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1)) := fun j ↦ (hC j).1.trans (hpos j)
  have hCS : ∀ j, IsSidon (C j : Set ℕ) := fun j a ha u hu b hb v hv h ↦
    hSid j a ((hC j).1 ha) u ((hC j).1 hu) b ((hC j).1 hb) v ((hC j).1 hv) h
  let I := (Finset.range (N + 1)).filter (fun j ↦ 2 ^ j * (j + 2) ^ e ≤ 2 ^ N)
  let T : Finset ℕ := I.biUnion fun j ↦ (C j).image E
  refine ⟨(T : Set ℕ), ?_, coded_union_sidon C hCpos hCS hcross E hsum I, ?_⟩
  · intro x hx
    obtain ⟨j, hj, hjx⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hx)
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hjx
    have h1 := hsize j a (hCpos j ha)
    exact ⟨h1.1, h1.2.trans (Finset.mem_filter.mp hj).2⟩
  · intro k hk hkN
    let t := e * (Nat.log 2 (k + 2) + 1)
    have hkt := hK k ((le_max_left _ _).trans hk)
    have hk1 : 1 ≤ k := (le_max_right _ _).trans hk
    let j := k - t
    have hjk : j + t = k := by dsimp [j]; omega
    have hJj : J ≤ j := by dsimp [j]; have := le_max_left J J₁; omega
    have hJ₁j : J₁ ≤ j := by dsimp [j]; have := le_max_right J J₁; omega
    have hjN : j ≤ N := by dsimp [j]; omega
    have hlogk : k + 2 < 2 ^ (Nat.log 2 (k + 2) + 1) := Nat.lt_pow_succ_log_self (by decide) _
    have hlogk' : 2 ^ Nat.log 2 (k + 2) ≤ k + 2 := Nat.pow_log_le_self 2 (by omega)
    have ht1 : (k + 2) ^ e ≤ 2 ^ t := by
      rw [show t = (Nat.log 2 (k + 2) + 1) * e by dsimp [t]; ring, pow_mul]
      exact Nat.pow_le_pow_left hlogk.le _
    have ht2 : 2 ^ t ≤ (k + 1) ^ (3 * e) := by
      rw [show t = (Nat.log 2 (k + 2) + 1) * e by dsimp [t]; ring, pow_mul, pow_mul]
      apply Nat.pow_le_pow_left
      rw [pow_succ]
      have h3 : 2 * (k + 2) ≤ (k + 1) ^ 3 := by
        have h2 : 2 ≤ k + 1 := by omega
        have h4 : 2 * 2 * (k + 1) ≤ (k + 1) ^ 3 := by
          rw [pow_succ, pow_two]
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul h2 h2)
        omega
      omega
    have hjk2 : 2 ^ j * (j + 2) ^ e ≤ 2 ^ k := by
      rw [← hjk, pow_add]
      exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by omega) _).trans ht1)
    have hjI : j ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
      hjk2.trans (pow_le_pow_right₀ (by decide) hkN)⟩
    have hsub : (((C j).image E : Finset ℕ) : Set ℕ) ⊆ (T : Set ℕ) ∩ Icc 1 (2 ^ k) := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      have h1 := hsize j a (hCpos j ha)
      exact ⟨Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨j, hjI, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩),
        h1.1, h1.2.trans hjk2⟩
    have hcard : (C j).card ≤ ((T : Set ℕ) ∩ Icc 1 (2 ^ k)).ncard := by
      have := Set.ncard_le_ncard hsub ((finite_Icc 1 (2 ^ k)).subset inter_subset_right)
      rwa [Set.ncard_coe_finset, Finset.card_image_of_injective _ hEinj] at this
    have hcount := hJ₁ j hJ₁j _ _ (hcounts j hJj hjN) (hC j).2
    calc
      2 ^ k = 2 ^ j * 2 ^ t := by rw [← pow_add, hjk]
      _ ≤ ((C j).card ^ 2 * (j + 1) ^ (2 * (d + 2))) * (k + 1) ^ (3 * e) :=
        Nat.mul_le_mul hcount ht2
      _ ≤ (((T : Set ℕ) ∩ Icc 1 (2 ^ k)).ncard ^ 2 * (k + 1) ^ (2 * (d + 2))) *
          (k + 1) ^ (3 * e) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.pow_le_pow_left hcard _)
          (Nat.pow_le_pow_left (by omega) _))
      _ = ((T : Set ℕ) ∩ Icc 1 (2 ^ k)).ncard ^ 2 * (k + 1) ^ (2 * (d + 2) + 3 * e) := by
        rw [pow_add]; ring
      _ ≤ _ := Nat.mul_le_mul_left _ (pow_le_pow_right₀ (by omega) (by omega))

/-- Dense Sidon blocks in all dyadic intervals whose positive differences avoid those of
blocks at nearby scales (j/3 < i < j), with a fixed polylogarithmic loss. -/
def H1 : Prop :=
  ∃ d J : ℕ, ∀ N : ℕ, ∃ B : ℕ → Finset ℕ,
    (∀ j, B j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1))) ∧
    (∀ j, ∀ a ∈ B j, ∀ b ∈ B j, ∀ u ∈ B j, ∀ v ∈ B j,
      a + b = u + v → (a = u ∧ b = v) ∨ (a = v ∧ b = u)) ∧
    (∀ j, J ≤ j → j ≤ N → 2 ^ j ≤ (B j).card ^ 2 * (j + 1) ^ (2 * (d + 1))) ∧
    ∀ i j, j / 3 < i → i < j → ∀ a ∈ B i, ∀ b ∈ B i, ∀ u ∈ B j, ∀ v ∈ B j,
      b < a → v < u → a - b ≠ u - v

/-- An integer code whose pair sums determine the original sum and the unordered pair of
dyadic labels, moving each dyadic block up by at most a polynomial in the label. -/
def H2 : Prop :=
  ∃ (E : ℕ → ℕ) (e : ℕ),
    (∀ a b u v, E a + E b = E u + E v →
      a + b = u + v ∧
        ((Nat.log 2 a = Nat.log 2 u ∧ Nat.log 2 b = Nat.log 2 v) ∨
         (Nat.log 2 a = Nat.log 2 v ∧ Nat.log 2 b = Nat.log 2 u))) ∧
    ∀ j, ∀ a ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), 1 ≤ E a ∧ E a ≤ 2 ^ j * (j + 2) ^ e

theorem main : H1 → H2 → type_of% @Erdos1191.erdos_1191.parts.ii := by
  intro h1 h2
  obtain ⟨d, J, hB⟩ := h1
  obtain ⟨E, e, hsum, hsize⟩ := h2
  obtain ⟨D, J₀, hfin⟩ := coded_finite_witness d J hB E e hsum hsize
  obtain ⟨A, hSidon, hcount⟩ := sidon_of_finite_dyadic_witnesses D J₀ hfin
  exact ⟨A, infinite_of_dyadic_counts A D J₀ hcount, hSidon,
    density_from_dyadic_counts A D J₀ hcount⟩

end OMA.R_Erdos1191_erdos_1191_parts_ii_R2
