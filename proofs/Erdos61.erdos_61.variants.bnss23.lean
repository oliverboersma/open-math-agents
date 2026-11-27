import FormalConjectures.ErdosProblems.«61»

/-!
Bucić, Nguyen, Scott and Seymour, Induced subgraph density I,
International Mathematics Research Notices 2024, DOI 10.1093/imrn/rnae065.

The counting and blockade construction follow Sections 3 and 4. Iterating
the largest clique and independent set product transfers the blockade bound
directly to the stated logarithmic improvement.
-/

open Finset Filter SimpleGraph
open scoped BigOperators

namespace OMA.BNSS

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def Independent (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b

noncomputable def stability (G : SimpleGraph V) (S : Finset V) : ℕ := by
  classical
  exact (S.powerset.filter (Independent G)).sup Finset.card

theorem le_stability {V : Type*} {G : SimpleGraph V} {S T : Finset V}
    (h : T ⊆ S) (hi : Independent G T) :
    T.card ≤ stability G S := by
  classical
  unfold stability
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr h, hi⟩)

theorem stability_attained {V : Type*} (G : SimpleGraph V) (S : Finset V) :
    ∃ T ⊆ S, Independent G T ∧ T.card = stability G S := by
  classical
  have he : (S.powerset.filter (Independent G)).Nonempty :=
    ⟨∅, by simp [Independent]⟩
  obtain ⟨T, hT, hc⟩ := Finset.exists_mem_eq_sup _ he Finset.card
  exact ⟨T, Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1,
    (Finset.mem_filter.mp hT).2, hc.symm⟩

theorem stability_mono {S T : Finset V} (h : S ⊆ T) :
    stability G S ≤ stability G T := by
  obtain ⟨U, hU, hi, hc⟩ := stability_attained G S
  rw [← hc]
  exact le_stability (hU.trans h) hi

theorem stability_pos {S : Finset V} (h : S.Nonempty) : 0 < stability G S := by
  obtain ⟨v, hv⟩ := h
  have hb : ({v} : Finset V).card ≤ stability G S :=
    le_stability (singleton_subset_iff.mpr hv) (by simp [Independent])
  rw [Finset.card_singleton] at hb
  omega

noncomputable def capacity (G : SimpleGraph V) (S : Finset V) : ℕ :=
  stability G S * stability Gᶜ S

@[simp] theorem capacity_compl {V : Type*} (G : SimpleGraph V) (S : Finset V) :
    capacity Gᶜ S = capacity G S := by
  simp [capacity, mul_comm]

theorem capacity_pos {S : Finset V} (h : S.Nonempty) : 0 < capacity G S :=
  Nat.mul_pos (stability_pos h) (stability_pos h)

noncomputable def neighbours (G : SimpleGraph V) (A : Finset V) (b : V) : Finset V := by
  classical
  exact A.filter (G.Adj b)

theorem mem_neighbours {V : Type*} {G : SimpleGraph V} {A : Finset V} {u v : V} :
    u ∈ neighbours G A v ↔ u ∈ A ∧ G.Adj v u := by
  classical
  simp [neighbours]

def SparseTo (G : SimpleGraph V) (x : ℝ) (B A : Finset V) : Prop :=
  ∀ b ∈ B, ((neighbours G A b).card : ℝ) ≤ x * A.card

def SparseBlocks (G : SimpleGraph V) (x : ℝ) (S : Finset V) (w : ℝ)
    (blocks : List (Finset V)) : Prop :=
  (∀ A ∈ blocks, A ⊆ S ∧ w ≤ (A.card : ℝ)) ∧
    blocks.Pairwise (fun A B ↦ Disjoint A B ∧ SparseTo G x B A)

theorem clear_neighbourhood {base A U : Finset V} {x : ℝ} (hx : 0 ≤ x)
    (hUb : U ⊆ base) (hUs : Independent G U)
    (hsp : SparseTo G x U A) (hbase : base.Nonempty)
    (hsmall : x * capacity G base ≤ 1 / 2) :
    ∃ C ⊆ A, ((A.card : ℝ) / 2 ≤ C.card) ∧
      ∀ v ∈ C, ∀ u ∈ U, ¬ G.Adj v u := by
  classical
  let D := U.biUnion (neighbours G A)
  have hDA : D ⊆ A := by
    intro v hv
    obtain ⟨u, hu, hv'⟩ := Finset.mem_biUnion.mp hv
    exact (mem_neighbours.mp hv').1
  let C := A \ D
  have hU : (U.card : ℝ) ≤ capacity G base := by
    have hu := le_stability hUb hUs
    have hp : 1 ≤ stability Gᶜ base := stability_pos hbase
    exact_mod_cast hu.trans (by simpa [capacity] using Nat.mul_le_mul_left (stability G base) hp)
  have hD : (D.card : ℝ) ≤ U.card * (x * A.card) := by
    have h := Finset.card_biUnion_le (s := U) (t := neighbours G A)
    calc
      (D.card : ℝ) ≤ ∑ b ∈ U, ((neighbours G A b).card : ℝ) := by exact_mod_cast h
      _ ≤ ∑ _b ∈ U, (x * A.card) := Finset.sum_le_sum hsp
      _ = _ := by simp
  refine ⟨C, Finset.sdiff_subset, ?_, ?_⟩
  · have hcount : (C.card : ℝ) + D.card = A.card := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hDA
    have hbound : (U.card : ℝ) * x ≤ 1 / 2 :=
      (mul_comm (U.card : ℝ) x).le.trans ((mul_le_mul_of_nonneg_left hU hx).trans hsmall)
    nlinarith [mul_le_mul_of_nonneg_right hbound (Nat.cast_nonneg (α := ℝ) A.card)]
  · intro v hv u hu hadj
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_biUnion.mpr
      ⟨u, hu, mem_neighbours.mpr ⟨(Finset.mem_sdiff.mp hv).1, hadj.symm⟩⟩)

/-- Process the blocks from the last to the first. Previously chosen independent vertices
remove at most half of the next block. The ambient clique number bounds each internal
clique number, so the products for the surviving blocks add. -/
theorem sparse_gain {base S : Finset V} {x w : ℝ} {blocks : List (Finset V)}
    {m : ℕ} (hx : 0 ≤ x) (hS : S ⊆ base) (hbase : base.Nonempty)
    (hsmall : x * capacity G base ≤ 1 / 2) (hb : SparseBlocks G x S w blocks)
    (hrec : ∀ C ⊆ S, w / 2 ≤ (C.card : ℝ) → m ≤ capacity G C) :
    blocks.length * m ≤ capacity G S := by
  classical
  have core : ∃ U ⊆ S, Independent G U ∧
      (∀ u ∈ U, ∃ B ∈ blocks, u ∈ B) ∧
      blocks.length * m ≤ U.card * stability Gᶜ S := by
    induction blocks with
    | nil => exact ⟨∅, empty_subset _, by simp [Independent], by simp, by simp⟩
    | cons A tail ih =>
      obtain ⟨hparts, hpair⟩ := hb
      have ht : SparseBlocks G x S w tail :=
        ⟨fun B hB ↦ hparts B (List.mem_cons_of_mem _ hB), (List.pairwise_cons.mp hpair).2⟩
      obtain ⟨U, hUS, hUi, hUtail, hUm⟩ := ih ht
      have hAU : Disjoint A U := by
        apply Finset.disjoint_left.mpr
        intro u hu huU
        obtain ⟨B, hB, huB⟩ := hUtail u huU
        exact Finset.disjoint_left.mp ((List.pairwise_cons.mp hpair).1 _ hB).1 hu huB
      have hsp : SparseTo G x U A := by
        intro u hu
        obtain ⟨B, hB, huB⟩ := hUtail u hu
        exact ((List.pairwise_cons.mp hpair).1 _ hB).2 u huB
      have hA := hparts A (List.mem_cons_self)
      obtain ⟨C, hCA, hCcard, hcross⟩ :=
        clear_neighbourhood hx (hUS.trans hS) hUi hsp hbase hsmall
      have hCS := hCA.trans hA.1
      have hre := hrec C hCS (by linarith [hA.2])
      obtain ⟨I, hIC, hIi, hIc⟩ := stability_attained G C
      have hIA := hIC.trans hCA
      have hIUS : I ∪ U ⊆ S := Finset.union_subset (hIC.trans hCS) hUS
      have hIU : Disjoint I U := hAU.mono_left hIA
      have hIiU : Independent G (I ∪ U) := by
        intro a ha b hb'
        rcases Finset.mem_union.mp ha with ha | ha <;>
          rcases Finset.mem_union.mp hb' with hb' | hb'
        · exact hIi a ha b hb'
        · exact hcross a (hIC ha) b hb'
        · exact fun h ↦ hcross b (hIC hb') a ha h.symm
        · exact hUi a ha b hb'
      have hmI : m ≤ I.card * stability Gᶜ S :=
        hre.trans (by
          rw [capacity, ← hIc]
          exact Nat.mul_le_mul_left _ (stability_mono hCS))
      refine ⟨I ∪ U, hIUS, hIiU, ?_, ?_⟩
      · intro u hu
        rcases Finset.mem_union.mp hu with hu | hu
        · exact ⟨A, List.mem_cons_self, hIA hu⟩
        · obtain ⟨B, hB, huB⟩ := hUtail u hu
          exact ⟨B, List.mem_cons_of_mem _ hB, huB⟩
      · rw [Finset.card_union_of_disjoint hIU, Nat.add_mul, List.length_cons, Nat.add_mul]
        simpa [Nat.add_comm] using Nat.add_le_add hmI hUm
  obtain ⟨U, hU, hi, _, hcard⟩ := core
  exact hcard.trans (Nat.mul_le_mul_right _ (le_stability hU hi))

theorem harm_pos {V : Type*} {S : Finset V} (hS : (1 : ℝ) ≤ S.card) : S.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  rintro rfl
  norm_num at hS

/-- A block decomposition into at least k pieces multiplies the homogeneous-set product
by k at each level. Complementing the graph preserves the product. -/
theorem block_iterate {base : Finset V} {x y : ℝ} {k : ℕ} (hbase : base.Nonempty)
    (hx : 0 ≤ x) (hy : 0 < y) (hy1 : y ≤ 1)
    (hsmall : x * capacity G base ≤ 1 / 2)
    (hsplit : ∀ S ⊆ base, 1 ≤ y * S.card →
      (∃ blocks, k ≤ blocks.length ∧ SparseBlocks G x S (2 * y * S.card) blocks) ∨
      (∃ blocks, k ≤ blocks.length ∧ SparseBlocks Gᶜ x S (2 * y * S.card) blocks)) :
    ∀ t (S : Finset V), S ⊆ base → 1 ≤ y ^ t * S.card → k ^ t ≤ capacity G S := by
  intro t
  induction t with
  | zero =>
    intro S _ hsize
    rw [pow_zero]
    exact capacity_pos (G := G) (harm_pos (by simpa using hsize))
  | succ t ih =>
    intro S hS hsize
    have hytn : 0 ≤ y ^ t := by positivity
    have hyt : y ^ t ≤ 1 := pow_le_one₀ hy.le hy1
    have hyS : 1 ≤ y * S.card := by
      rw [pow_succ', mul_assoc, mul_left_comm] at hsize
      exact hsize.trans (by
        nlinarith [mul_le_mul_of_nonneg_right hyt (show 0 ≤ y * (S.card : ℝ) by positivity)])
    have hrec (C : Finset V) (hCS : C ⊆ S)
        (hc : (2 * y * S.card) / 2 ≤ (C.card : ℝ)) :
        k ^ t ≤ capacity G C := by
      apply ih C (hCS.trans hS)
      rw [pow_succ, mul_assoc] at hsize
      exact hsize.trans (mul_le_mul_of_nonneg_left (by linarith) hytn)
    rw [pow_succ']
    rcases hsplit S hS hyS with ⟨B, hBk, hB⟩ | ⟨B, hBk, hB⟩
    · exact (Nat.mul_le_mul_right _ hBk).trans (sparse_gain hx hS hbase hsmall hB hrec)
    · have hg := sparse_gain hx hS hbase (G := Gᶜ)
        (by simpa only [capacity_compl] using hsmall) hB
        (fun C hC hsize ↦ by simpa only [capacity_compl] using hrec C hC hsize)
      simpa only [capacity_compl] using (Nat.mul_le_mul_right _ hBk).trans hg

theorem stability_le_indepNum [Finite V] (G : SimpleGraph V) (S : Finset V) :
    stability G S ≤ G.indepNum := by
  obtain ⟨T, _, hi, hc⟩ := stability_attained G S
  rw [← hc]
  apply SimpleGraph.IsIndepSet.card_le_indepNum
  intro a ha b hb _
  exact hi a ha b hb

def Avoids {W : Type*} (H : SimpleGraph W) (G : SimpleGraph V) (S : Finset V) : Prop :=
  ¬ ∃ f : W ↪ V, H = G.comap f ∧ ∀ w, f w ∈ S

def HasBlockadeBound {W : Type*} (H : SimpleGraph W) (D : ℕ) (x₀ : ℝ) : Prop :=
  ∀ {V : Type} [DecidableEq V] (G : SimpleGraph V) (S : Finset V) (x : ℝ) (k : ℕ),
    0 < x → x ≤ x₀ → (k : ℝ) ≤ Real.log x⁻¹ / 2 → Avoids H G S →
    1 ≤ x ^ D * S.card →
    (∃ blocks, k ≤ blocks.length ∧ SparseBlocks G x S (2 * x ^ D * S.card) blocks) ∨
    (∃ blocks, k ≤ blocks.length ∧ SparseBlocks Gᶜ x S (2 * x ^ D * S.card) blocks)

open Real
open scoped Topology

/-- Balance the available recursion depth against the logarithmic number of blocks. -/
theorem loglog_parameters {D : ℕ} (hD : 0 < D) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ n : ℕ in atTop,
      ∃ x : ℝ, ∃ k t : ℕ, 0 < x ∧ x ≤ x₀ ∧ x ≤ 1 ∧
        (k : ℝ) ≤ log x⁻¹ / 2 ∧ 1 ≤ (x ^ D) ^ t * n ∧
        exp (a * sqrt (log n * log (log n))) ≤ (k : ℝ) ^ t ∧
        x * exp (a * sqrt (log n * log (log n))) ≤ 1 / 2 := by
  let a : ℝ := 1 / (8 * D)
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨a, ha, ?_⟩
  have hLtop : Tendsto (fun n : ℕ ↦ log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogtop : Tendsto (fun n : ℕ ↦ log (log (n : ℝ))) atTop atTop :=
    tendsto_log_atTop.comp hLtop
  let threshold : ℝ := max 4 (max (log 2) (-log x₀))
  filter_upwards [hlogtop.eventually_ge_atTop (max 1 (-4 * log a)),
    hLtop.eventually_ge_atTop ((threshold / a)^2 + 1)] with n hLLbase hLbase
  let L : ℝ := log (n : ℝ)
  let R : ℝ := a * sqrt (L * log L)
  let x : ℝ := exp (-2 * R)
  let k : ℕ := ⌊R⌋₊
  let t : ℕ := ⌈2 * R / log R⌉₊
  have hL : 0 < L := by dsimp [L]; nlinarith [sq_nonneg (threshold / a)]
  have hLL : 1 ≤ log L := le_trans (le_max_left _ _) hLLbase
  have hlogA : -4 * log a ≤ log L := le_trans (le_max_right _ _) hLLbase
  have hLLL : 0 ≤ log (log L) := log_nonneg hLL
  have hLP : 0 < L * log L := mul_pos hL (by linarith)
  have hth : 4 ≤ threshold := le_max_left _ _
  have hthr : 0 ≤ threshold / a := div_nonneg (by linarith) ha.le
  have hsr : threshold / a ≤ sqrt (L * log L) := by
    rw [← sq_le_sq₀ hthr (sqrt_nonneg _), sq_sqrt hLP.le]
    have hmul : L ≤ L * log L := by simpa using mul_le_mul_of_nonneg_left hLL hL.le
    exact (show (threshold/a)^2 ≤ L by dsimp [L]; linarith).trans hmul
  have hRth : threshold ≤ R := by
    dsimp [R]
    rw [mul_comm]
    exact (div_le_iff₀ ha).mp hsr
  have hR4 : 4 ≤ R := hth.trans hRth
  have hR : 0 < R := by linarith
  have hlogR : 0 < log R := log_pos (by linarith)
  have hlogRlow : log L / 4 ≤ log R := by
    dsimp [R]
    rw [log_mul ha.ne' (sqrt_pos.2 hLP).ne', log_sqrt hLP.le,
      log_mul hL.ne' (show log L ≠ 0 by linarith)]
    linarith
  have hfold : (k : ℝ) ≤ R := Nat.floor_le hR.le
  have hkhalf : R / 2 ≤ (k : ℝ) := by
    have h := Nat.lt_floor_add_one R
    change R < (k : ℝ) + 1 at h
    linarith
  have hkpos : 0 < (k : ℝ) := by linarith
  have hlogs : log R / 2 ≤ log (k : ℝ) := by
    rw [← log_sqrt hR.le]
    apply log_le_log (sqrt_pos.2 hR)
    rw [← sq_le_sq₀ (sqrt_nonneg _) hkpos.le, sq_sqrt hR.le]
    nlinarith [mul_nonneg (show 0 ≤ R / 2 - 2 by linarith)
      (show 0 ≤ R / 2 by positivity), mul_nonneg
      (show 0 ≤ (k : ℝ) - R / 2 by linarith)
      (show 0 ≤ (k : ℝ) + R / 2 by positivity)]
  have htLower : 2 * R ≤ (t : ℝ) * log R :=
    (div_le_iff₀ hlogR).mp (Nat.le_ceil (2 * R / log R))
  have htUpper : (t : ℝ) * log R ≤ 3 * R := by
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ 2 * R / log R by positivity)
    change (t : ℝ) < 2 * R / log R + 1 at hceil
    have hlt : (t : ℝ) < (2 * R + log R) / log R := by
      rwa [add_div, div_self hlogR.ne']
    have hh := (lt_div_iff₀ hlogR).mp hlt
    linarith [log_le_sub_one_of_pos hR]
  have hrate : 2 * D * (t : ℝ) * R ≤ L := by
    have hsq : R ^ 2 = a ^ 2 * (L * log L) := by
      dsimp [R]
      rw [mul_pow, sq_sqrt hLP.le]
    have ht0 : 0 ≤ (t : ℝ) := by positivity
    have hmain : (t : ℝ) * log L ≤ 12 * R := by
      nlinarith [mul_le_mul_of_nonneg_left hlogRlow ht0]
    have haD : 24 * (D : ℝ) * a ^ 2 ≤ 1 := by
      have hge : (1 : ℝ) ≤ D := by exact_mod_cast hD
      dsimp [a]
      field_simp
      nlinarith [mul_nonneg hDr.le (show 0 ≤ (D : ℝ) - 1 by linarith)]
    apply (mul_le_mul_iff_of_pos_right (show 0 < log L by linarith)).mp
    have hcoef : 0 ≤ 2 * (D : ℝ) * R := by positivity
    have hlast := mul_le_mul_of_nonneg_right haD hLP.le
    nlinarith only [mul_le_mul_of_nonneg_left hmain hcoef, hlast,
      congrArg (fun z : ℝ ↦ 24 * D * z) hsq]
  have hn : 0 < (n : ℝ) := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [L] at hL
    · exact_mod_cast hpos
  have hxpos : 0 < x := exp_pos _
  have hxone : x ≤ 1 := by
    dsimp [x]
    rw [exp_le_one_iff]
    linarith
  have htrim : 1 ≤ (x ^ D) ^ t * n := by
    dsimp [x]
    rw [← exp_nat_mul, ← exp_nat_mul, ← exp_log hn, ← exp_add, ← exp_zero,
      exp_le_exp]
    dsimp [L] at hrate
    nlinarith only [hrate]
  have hkpower : exp R ≤ (k : ℝ)^t := by
    calc
      exp R ≤ exp ((t : ℝ) * log k) := by
        rw [exp_le_exp]
        nlinarith only [htLower, mul_le_mul_of_nonneg_left hlogs (Nat.cast_nonneg (α := ℝ) t)]
      _ = _ := by rw [exp_nat_mul, exp_log hkpos]
  refine ⟨x, k, t, hxpos, ?_, hxone, ?_, htrim, hkpower, ?_⟩
  · have htx : -log x₀ ≤ threshold := (le_max_right (log 2) _).trans (le_max_right _ _)
    rw [← exp_log hx₀, show x = exp (-2 * R) by rfl, exp_le_exp]
    linarith [htx.trans hRth]
  · dsimp [x]
    rw [log_inv, log_exp]
    linarith
  · have ht2 : log 2 ≤ threshold := (le_max_left (log 2) _).trans (le_max_right _ _)
    change exp (-2 * R) * exp R ≤ 1 / 2
    rw [← exp_add, show -2 * R + R = -R by ring, one_div, ← exp_log (by norm_num : 0 < (2 : ℝ)),
      ← exp_neg, exp_le_exp]
    linarith [ht2.trans hRth]

theorem from_blockade {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    {D : ℕ} (hD : 0 < D) {x₀ : ℝ} (hx₀ : 0 < x₀) (h : HasBlockadeBound H D x₀) :
    ∃ c > (0 : ℝ), Erdos61.IsErdosHajnalLowerBound H
      (fun n : ℕ ↦ exp (c * sqrt (log n * log (log n)))) := by
  classical
  obtain ⟨a, ha, haParam⟩ := loglog_parameters hD hx₀
  refine ⟨a / 2, by positivity, ?_⟩
  filter_upwards [haParam] with n hn
  obtain ⟨x, k, t, hx, hxt, hx1, hk, hsize, hpow, hsmall⟩ := hn
  intro G hAvoid
  let S : Finset (Fin n) := univ
  have hcard : S.card = n := by simp [S]
  have hsizeS : 1 ≤ (x^D)^t * S.card := by simpa [hcard] using hsize
  have hbase : S.Nonempty := harm_pos (hsizeS.trans (by
    simpa using mul_le_mul_of_nonneg_right
      (pow_le_one₀ (pow_nonneg hx.le D) (pow_le_one₀ hx.le hx1)) (show 0 ≤ (S.card : ℝ) by positivity)))
  let R := a * sqrt (log (n : ℝ) * log (log n))
  have hcap : exp R ≤ capacity G S := by
    by_contra! hbad
    have hsplit (T : Finset (Fin n)) (_ : T ⊆ S) (hsz : 1 ≤ x^D * T.card) :=
      h G T x k hx hxt hk (fun ⟨f, hf, _⟩ ↦ hAvoid ⟨f,hf⟩) hsz
    have hnat := block_iterate hbase hx.le (pow_pos hx D) (pow_le_one₀ hx.le hx1)
      ((mul_le_mul_of_nonneg_left hbad.le hx.le).trans hsmall) hsplit t S Subset.rfl hsizeS
    have hreal : (k : ℝ)^t ≤ capacity G S := by exact_mod_cast hnat
    exact (not_lt_of_ge (hpow.trans hreal)) hbad
  have hcap' : exp R ≤ (G.indepNum : ℝ) * G.cliqueNum :=
    hcap.trans (by
      norm_cast
      simpa only [capacity, SimpleGraph.indepNum_compl] using
        Nat.mul_le_mul (stability_le_indepNum G S) (stability_le_indepNum Gᶜ S))
  by_contra! hbad
  have htarget : exp (R / 2) * exp (R / 2) = exp R := by rw [← exp_add]; ring_nf
  obtain ⟨ha', hb'⟩ := hbad
  have ha'' : (G.indepNum : ℝ) < exp (R / 2) := by simpa [R, div_mul_eq_mul_div] using ha'
  have hb'' : (G.cliqueNum : ℝ) < exp (R / 2) := by simpa [R, div_mul_eq_mul_div] using hb'
  rw [← htarget] at hcap'
  apply not_lt_of_ge hcap'
  calc
    (G.indepNum : ℝ) * G.cliqueNum ≤ exp (R / 2) * G.cliqueNum :=
      mul_le_mul_of_nonneg_right ha''.le (by positivity)
    _ < _ := mul_lt_mul_of_pos_left hb'' (exp_pos _)

end OMA.BNSS

namespace OMA.BNSS

open Finset SimpleGraph Filter Real
open scoped BigOperators

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem neighbours_mono (G : SimpleGraph V) {A B : Finset V} (h : A ⊆ B) (v : V) :
    neighbours G A v ⊆ neighbours G B v := by
  intro u hu
  obtain ⟨huA, ha⟩ := mem_neighbours.mp hu
  exact mem_neighbours.mpr ⟨h huA, ha⟩

theorem sparseTo_subset_left {V : Type*} {G : SimpleGraph V} {x : ℝ} {A B C : Finset V}
    (hc : C ⊆ B) (h : SparseTo G x B A) : SparseTo G x C A :=
  fun _ hv ↦ h _ (hc hv)

open scoped Classical in
theorem adj_indicator_sum {V : Type*} (G : SimpleGraph V) (A : Finset V) (v : V) :
    ((neighbours G A v).card : ℝ) =
      ∑ a ∈ A, (if G.Adj v a then 1 else 0 : ℝ) := by
  classical
  rw [Finset.sum_boole]
  rfl

noncomputable def crossEdges (G : SimpleGraph V) (A B : Finset V) : ℝ :=
  ∑ b ∈ B, ((neighbours G A b).card : ℝ)

theorem crossEdges_symm (G : SimpleGraph V) (A B : Finset V) :
    crossEdges G A B = crossEdges G B A := by
  classical
  simp only [crossEdges, adj_indicator_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [G.adj_comm]

theorem crossEdges_le {V : Type*} {G : SimpleGraph V} {x : ℝ} {A B : Finset V}
    (h : SparseTo G x B A) :
    crossEdges G A B ≤ x * A.card * B.card := by
  unfold crossEdges
  refine (Finset.sum_le_sum h).trans_eq ?_
  simp [mul_comm]

theorem markov_half {Q : Finset V} (f : V → ℝ) (hf : ∀ v ∈ Q, 0 ≤ f v)
    {q : ℝ} (hq : 0 ≤ q) (h : ∑ v ∈ Q, f v ≤ q * Q.card) :
    ∃ T ⊆ Q, ((Q.card : ℝ) / 2 ≤ T.card) ∧ ∀ v ∈ T, f v ≤ 2 * q := by
  classical
  let T := Q.filter (fun v ↦ f v ≤ 2 * q)
  let U := Q \ T
  have hT : T ⊆ Q := filter_subset _ _
  have hc : (U.card : ℝ) + T.card = Q.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hT
  have hstrict : ∀ v ∈ U, 2 * q < f v := by
    intro v hv
    have hv' := Finset.mem_sdiff.mp hv
    exact lt_of_not_ge fun hle ↦ hv'.2 (mem_filter.mpr ⟨hv'.1, hle⟩)
  refine ⟨T, hT, ?_, fun v hv ↦ (mem_filter.mp hv).2⟩
  by_contra! hbad
  have hUne : U.Nonempty := Finset.card_pos.mp (by
    have hUpos : (0 : ℝ) < (U.card : ℝ) := by
      linarith [Nat.cast_nonneg (α := ℝ) T.card]
    exact_mod_cast hUpos)
  have hs : (∑ v ∈ U, 2 * q) < ∑ v ∈ U, f v :=
    Finset.sum_lt_sum_of_nonempty hUne hstrict
  have hsub : ∑ v ∈ U, f v ≤ ∑ v ∈ Q, f v :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun v hv _ ↦ hf v hv)
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  nlinarith only [h, hs, hsub, mul_nonneg hq (show 0 ≤ (U.card : ℝ) - T.card by linarith),
    congrArg (fun a : ℝ ↦ q * a) hc]

theorem sparse_half {x : ℝ} {A B : Finset V} (hx : 0 ≤ x)
    (h : crossEdges G A B ≤ x * A.card * B.card) :
    ∃ C ⊆ B, ((B.card : ℝ) / 2 ≤ C.card) ∧ SparseTo G (2*x) C A := by
  obtain ⟨C, hCB, hcard, hC⟩ := markov_half
    (fun v ↦ ((neighbours G A v).card : ℝ)) (fun _ _ ↦ Nat.cast_nonneg _)
    (mul_nonneg hx (Nat.cast_nonneg _)) h
  exact ⟨C, hCB, hcard, fun v hv ↦ by simpa only [mul_assoc] using hC v hv⟩

end OMA.BNSS

namespace OMA.BNSS

open Finset SimpleGraph Filter Real
open scoped BigOperators

variable {V W : Type*} [DecidableEq V] [Fintype W] [DecidableEq W]

def Embeds (H : SimpleGraph W) (G : SimpleGraph V) (f : W → V) : Prop :=
  Function.Injective f ∧ ∀ a b, H.Adj a b ↔ G.Adj (f a) (f b)

noncomputable def copiesInParts (H : SimpleGraph W) (G : SimpleGraph V)
    (parts : W → Finset V) : Finset (W → V) := by
  classical
  exact (Fintype.piFinset parts).filter (Embeds H G)

noncomputable def copies (H : SimpleGraph W) (G : SimpleGraph V) (S : Finset V) : Finset (W → V) :=
  copiesInParts H G (fun _ ↦ S)

theorem mem_copiesInParts {V : Type*} {H : SimpleGraph W} {G : SimpleGraph V}
    {parts : W → Finset V} {f : W → V} :
    f ∈ copiesInParts H G parts ↔ Embeds H G f ∧ ∀ a, f a ∈ parts a := by
  classical
  rw [copiesInParts, Finset.mem_filter, Fintype.mem_piFinset]
  exact and_comm

theorem mem_copies {H : SimpleGraph W} {G : SimpleGraph V} {S : Finset V} {f : W → V} :
    f ∈ copies H G S ↔ Embeds H G f ∧ ∀ a, f a ∈ S :=
  mem_copiesInParts

theorem copies_mono (H : SimpleGraph W) (G : SimpleGraph V) {A B : Finset V}
    (h : A ⊆ B) : copies H G A ⊆ copies H G B := by
  intro f hf
  obtain ⟨hh, hp⟩ := mem_copies.mp hf
  exact mem_copies.mpr ⟨hh, fun a ↦ h (hp a)⟩

theorem copies_empty_of_avoids {H : SimpleGraph W} {G : SimpleGraph V} {A : Finset V}
    (h : Avoids H G A) : copies H G A = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro f hf
  obtain ⟨⟨hi, he⟩, hm⟩ := mem_copies.mp hf
  apply h
  refine ⟨⟨f, hi⟩, ?_, hm⟩
  ext a b
  exact he a b

theorem copiesInParts_subset {H : SimpleGraph W} {G : SimpleGraph V}
    {S : Finset V} {parts : W → Finset V} (hp : ∀ w, parts w ⊆ S) :
    copiesInParts H G parts ⊆ copies H G S := by
  intro f hf
  obtain ⟨he, hf⟩ := mem_copiesInParts.mp hf
  exact mem_copies.mpr ⟨he, fun a ↦ hp a (hf a)⟩

theorem embeds_compl {V W : Type*} {H : SimpleGraph W} {G : SimpleGraph V} {f : W → V} :
    Embeds Hᶜ Gᶜ f ↔ Embeds H G f := by
  have aux (J : SimpleGraph W) (K : SimpleGraph V) :
      Embeds J K f → Embeds Jᶜ Kᶜ f := by
    rintro ⟨hi, ha⟩
    refine ⟨hi, fun a b ↦ ?_⟩
    simp only [SimpleGraph.compl_adj, hi.ne_iff]
    exact and_congr_right fun _ ↦ not_congr (ha a b)
  exact ⟨fun h ↦ by simpa only [compl_compl] using aux Hᶜ Gᶜ h, aux H G⟩

theorem copies_compl (H : SimpleGraph W) (G : SimpleGraph V) (A : Finset V) :
    copies Hᶜ Gᶜ A = copies H G A := by
  ext f
  simp only [mem_copies, embeds_compl]

end OMA.BNSS

namespace OMA.BNSS

open Finset Filter SimpleGraph Real
open scoped BigOperators

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def polarity (G : SimpleGraph V) (b : Bool) : SimpleGraph V :=
  if b then Gᶜ else G

def Restricted (G : SimpleGraph V) (x : ℝ) (S : Finset V) (w : ℝ)
    (B : List (Bool × Finset V)) : Prop :=
  (∀ A ∈ B, A.2 ⊆ S ∧ w ≤ (A.2.card : ℝ)) ∧
    B.Pairwise (fun A C ↦ Disjoint A.2 C.2 ∧ SparseTo (polarity G A.1) x C.2 A.2)

theorem restricted_mono {V : Type*} {G : SimpleGraph V} {S S' : Finset V} {x w w' : ℝ}
    {B : List (Bool × Finset V)}
    (h : Restricted G x S w B) (hs : S ⊆ S') (hw : w' ≤ w) :
    Restricted G x S' w' B :=
  ⟨fun A ha ↦ ⟨(h.1 A ha).1.trans hs, hw.trans (h.1 A ha).2⟩, h.2⟩

theorem restricted_cons {x w : ℝ} {Y A D : Finset V} {sign : Bool}
    {B : List (Bool × Finset V)}
    (hA : A ⊆ Y) (hD : D ⊆ Y) (hwidth : w ≤ A.card)
    (hdis : Disjoint A D) (hs : SparseTo (polarity G sign) x D A)
    (hB : Restricted G x D w B) :
    Restricted G x Y w ((sign, A) :: B) := by
  constructor
  · intro P hP
    rcases List.mem_cons.mp hP with rfl | hP
    · exact ⟨hA, hwidth⟩
    · exact ⟨(hB.1 _ hP).1.trans hD, (hB.1 _ hP).2⟩
  · apply List.pairwise_cons.mpr
    exact ⟨fun P hp ↦ ⟨hdis.mono_right (hB.1 _ hp).1,
      sparseTo_subset_left (hB.1 _ hp).1 hs⟩, hB.2⟩

theorem sparse_of_sign {V : Type*} {G : SimpleGraph V} {x w : ℝ} {S : Finset V}
    {B : List (Bool × Finset V)}
    (hB : Restricted G x S w B) (b : Bool) :
    SparseBlocks (polarity G b) x S w (B.filter (fun P ↦ P.1 == b) |>.map Prod.snd) := by
  constructor
  · intro A hA
    obtain ⟨P, hp, rfl⟩ := List.mem_map.mp hA
    exact hB.1 P (List.mem_of_mem_filter hp)
  · rw [List.pairwise_map]
    apply List.pairwise_filter.mpr
    apply hB.2.imp
    intro A C hAc hAsign hCsign
    have ha : A.1 = b := by simpa using hAsign
    simpa only [ha] using hAc

theorem color_pigeonhole {x w : ℝ} {S : Finset V} {B : List (Bool × Finset V)}
    {k : ℕ} (hn : 2*k ≤ B.length) (hB : Restricted G x S w B) :
    (∃ blocks, k ≤ blocks.length ∧ SparseBlocks G x S w blocks) ∨
    (∃ blocks, k ≤ blocks.length ∧ SparseBlocks Gᶜ x S w blocks) := by
  let B₀ := (B.filter (fun P ↦ P.1 == false)).map Prod.snd
  let B₁ := (B.filter (fun P ↦ P.1 == true)).map Prod.snd
  have hcard : B₀.length + B₁.length = B.length := by
    have he : (fun P : Bool × Finset V ↦ !(P.1 == false)) = (fun P ↦ P.1 == true) := by
      funext P
      cases P.1 <;> rfl
    simpa only [B₀, B₁, List.length_map, ← he] using
      (B.length_eq_length_filter_add (fun P ↦ P.1 == false)).symm
  by_cases h₀ : k ≤ B₀.length
  · have hs : SparseBlocks G x S w B₀ := sparse_of_sign hB false
    exact Or.inl ⟨B₀, h₀, hs⟩
  · have h₁ : k ≤ B₁.length := by omega
    have hs : SparseBlocks Gᶜ x S w B₁ := sparse_of_sign hB true
    exact Or.inr ⟨B₁, h₁, hs⟩

theorem restricted_iterate {x w p : ℝ} (hp : 0 ≤ p)
    {S : Finset V} (m : ℕ)
    (step : ∀ j < m, ∀ Y ⊆ S, p^j * S.card ≤ (Y.card : ℝ) →
      (∃ B, m ≤ B.length ∧ Restricted G x Y w B) ∨
      (∃ (sign : Bool) (A D : Finset V),
        A ⊆ Y ∧ D ⊆ Y ∧ Disjoint A D ∧ w ≤ A.card ∧
        p * Y.card ≤ (D.card : ℝ) ∧ SparseTo (polarity G sign) x D A)) :
    ∃ B, m ≤ B.length ∧ Restricted G x S w B := by
  have inner : ∀ r j : ℕ, r + j = m →
      ∀ Y ⊆ S, p^j * S.card ≤ (Y.card : ℝ) →
        ∃ B, r ≤ B.length ∧ Restricted G x Y w B := by
    intro r
    induction r with
    | zero =>
      intro j _ Y _ _
      exact ⟨[], by simp, by simp [Restricted]⟩
    | succ r ih =>
      intro j hj Y hY hcard
      cases step j (by omega) Y hY hcard with
      | inl h =>
        obtain ⟨B, hb, hb'⟩ := h
        exact ⟨B, (show r + 1 ≤ m by omega).trans hb, hb'⟩
      | inr h =>
        obtain ⟨sign, A, D, hA, hD, hdis, hw, hDS, hsp⟩ := h
        have hDb : p^(j+1) * S.card ≤ (D.card : ℝ) := by
          rw [pow_succ', mul_assoc]
          exact (mul_le_mul_of_nonneg_left hcard hp).trans hDS
        obtain ⟨B, hlength, hB⟩ := ih (j+1) (by omega) D (hD.trans hY) hDb
        exact ⟨(sign, A) :: B, by simp; omega, restricted_cons hA hD hw hdis hsp hB⟩
  exact inner m 0 (by simp) S Subset.rfl (by simp)

end OMA.BNSS

namespace OMA.BNSS

open Finset Filter SimpleGraph Real
open scoped BigOperators

variable {V I : Type*} [DecidableEq V]

theorem edge_cut_nonneg {V : Type*} (G : SimpleGraph V) (A B : Finset V) :
    0 ≤ crossEdges G A B :=
  Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _

theorem heavy_fibre {S : Finset I} {mass cost : I → ℝ} {w q : ℝ}
    (hc : ∀ i ∈ S, 0 ≤ cost i) (hq : 0 ≤ q) (hw : 0 ≤ w)
    (hsize : 2 * w * S.card ≤ ∑ i ∈ S, mass i)
    (hcost : ∑ i ∈ S, cost i < q * ∑ i ∈ S, mass i) :
    ∃ i ∈ S, w ≤ mass i ∧ cost i ≤ 2 * q * mass i := by
  classical
  let H := S.filter (fun i ↦ w ≤ mass i)
  let L := S \ H
  have hHS : H ⊆ S := filter_subset _ _
  have hLS : L ⊆ S := sdiff_subset
  have hsplit : (∑ i ∈ H, mass i) + ∑ i ∈ L, mass i = ∑ i ∈ S, mass i := by
    rw [add_comm]
    exact Finset.sum_sdiff hHS
  have hL : ∑ i ∈ L, mass i ≤ w * S.card := by
    have hupper (i : I) (hi : i ∈ L) : mass i ≤ w := by
      have h' := Finset.mem_sdiff.mp hi
      exact le_of_lt (lt_of_not_ge fun hw ↦ h'.2 (mem_filter.mpr ⟨h'.1, hw⟩))
    calc
      ∑ i ∈ L, mass i ≤ ∑ _i ∈ L, w := sum_le_sum hupper
      _ ≤ _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [mul_comm w]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hLS) hw
  have hH : (∑ i ∈ S, mass i) / 2 ≤ ∑ i ∈ H, mass i := by linarith
  have hHcost : ∑ i ∈ H, cost i ≤ ∑ i ∈ S, cost i :=
    Finset.sum_le_sum_of_subset_of_nonneg hHS (fun i hi _ ↦ hc i hi)
  by_contra! hnone
  have hcost' : ∑ i ∈ H, (2 * q * mass i) ≤ ∑ i ∈ H, cost i := by
    apply Finset.sum_le_sum
    intro i hi
    have h' := mem_filter.mp hi
    exact (hnone i h'.1 h'.2).le
  rw [← Finset.mul_sum] at hcost'
  have hm' := mul_le_mul_of_nonneg_left hH (show 0 ≤ 2 * q by positivity)
  nlinarith only [hcost', hm', hHcost, hcost]

end OMA.BNSS

namespace OMA.BNSS

open Finset Filter SimpleGraph Real
open scoped BigOperators

def FewCopiesBlockade {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    (d e : ℕ) (x₀ : ℝ) : Prop :=
  ∀ {V : Type} [DecidableEq V] (G : SimpleGraph V) (S : Finset V) (x : ℝ) (m : ℕ),
    0 < x → x ≤ x₀ → (m : ℝ) ≤ log x⁻¹ → 1 ≤ x^d * S.card →
    ((copies H G S).card : ℝ) < x^e * (S.card : ℝ) ^ Fintype.card W →
    ∃ B, m ≤ B.length ∧ Restricted G x S (x^d * S.card) B

def Trichotomy {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    (g : W) (a b c : ℕ) (x₀ : ℝ) : Prop :=
  ∀ {V : Type} [DecidableEq V] (G : SimpleGraph V) (Y : Finset V) (x : ℝ),
    2 ≤ Y.card → 0 < x → x ≤ x₀ →
    (∃ A ⊆ Y, x^b * Y.card ≤ (A.card : ℝ) ∧
      ((copies (H.induce ({v | v ≠ g} : Set W)) G A).card : ℝ) <
        x^a * (A.card : ℝ) ^ (Fintype.card W - 1)) ∨
    x^c * (Y.card : ℝ) ^ Fintype.card W ≤ (copies H G Y).card ∨
    (∃ (sign : Bool) (A B : Finset V), A ⊆ Y ∧ B ⊆ Y ∧ Disjoint A B ∧
      x^b * Y.card ≤ (A.card : ℝ) ∧ (Y.card : ℝ) / (2 * Fintype.card W) ≤ B.card ∧
        SparseTo (polarity G sign) x B A)

theorem reciprocal_pow_ge {x : ℝ} {K j : ℕ} (hx : 0 < x) (hx1 : x ≤ 1)
    (hK : 1 ≤ K) (hj : (j : ℝ) ≤ log x⁻¹) :
    x ^ K ≤ ((K : ℝ)⁻¹) ^ j := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hk : (0 : ℝ) < K := by linarith
  have hlogK : 0 ≤ log (K : ℝ) := log_nonneg hKr
  have hxlog : log x ≤ 0 := log_nonpos hx.le hx1
  have hcalc : (j : ℝ) * log (K : ℝ) ≤ -log x * K := by
    rw [log_inv] at hj
    exact (mul_le_mul_of_nonneg_right hj hlogK).trans
      (mul_le_mul_of_nonneg_left (by linarith [log_le_sub_one_of_pos hk]) (neg_nonneg.mpr hxlog))
  rw [← exp_log hx, ← exp_log (inv_pos.mpr hk), ← exp_nat_mul,
    ← exp_nat_mul, exp_le_exp, log_inv]
  nlinarith only [hcalc]

theorem card_delete {W : Type*} [Fintype W] [DecidableEq W] (g : W) :
    Fintype.card ({v | v ≠ g} : Set W) = Fintype.card W - 1 := by
  classical
  simpa [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ g)]
    using Fintype.card_subtype (fun v ↦ v ≠ g)

/-- At each step either continue inside the large block, or apply the induction
hypothesis for the smaller forbidden graph to a subset with few copies. -/
theorem few_from_trichotomy {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (g : W) {d a b c : ℕ} (hd : 0 < d)
    {y₀ z₀ : ℝ} (hy₀ : 0 < y₀) (hz₀ : 0 < z₀)
    (hsmall : FewCopiesBlockade (H.induce ({v | v ≠ g} : Set W)) d a y₀)
    (htri : Trichotomy H g a b c z₀) :
    ∃ d' e : ℕ, 0 < d' ∧ 0 < e ∧ ∃ x₀ : ℝ, 0 < x₀ ∧ x₀ ≤ 1/2 ∧
      FewCopiesBlockade H d' e x₀ := by
  classical
  let h := Fintype.card W
  have hh : 0 < h := Fintype.card_pos_iff.mpr ⟨g⟩
  let K := 2 * h
  let d' := K + b + d
  let e := c + K * h
  let x₀ := min (1/2) (min y₀ z₀)
  have Hx : 0 < x₀ ∧ x₀ ≤ 1/2 := ⟨lt_min (by norm_num) (lt_min hy₀ hz₀), min_le_left _ _⟩
  have hKnat : 1 ≤ K := by dsimp [K]; omega
  refine ⟨d', e, by dsimp [d']; omega, by dsimp [e]; positivity, x₀, Hx.1, Hx.2, ?_⟩
  intro V _ G S x m hx hx' hm hsize hfew
  have hxhalf : x ≤ 1/2 := hx'.trans Hx.2
  have hxone : x ≤ 1 := hxhalf.trans (by norm_num)
  let p : ℝ := (K : ℝ)⁻¹
  have hp : 0 ≤ p := inv_nonneg.mpr (by positivity)
  apply restricted_iterate (G := G) hp m
  intro j hj Y hYS hY
  have hj' : (j : ℝ) ≤ log x⁻¹ := (by exact_mod_cast hj.le : (j : ℝ) ≤ m).trans hm
  have hy : x^K * S.card ≤ (Y.card : ℝ) := by
    exact (mul_le_mul_of_nonneg_right (reciprocal_pow_ge hx hxone hKnat hj')
      (Nat.cast_nonneg _)).trans hY
  have hYtwo : 2 ≤ Y.card := by
    have hpow : x^d' ≤ x^K * x := by
      rw [← pow_succ]
      exact pow_le_pow_of_le_one hx.le hxone (by dsimp [d']; omega)
    have ht : (1 : ℝ) ≤ x * Y.card := by
      have hS : x^d' * S.card ≤ (x^K * x) * S.card :=
        mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _)
      have hY' := mul_le_mul_of_nonneg_left hy hx.le
      nlinarith only [hsize, hS, hY']
    have hY' : (2 : ℝ) ≤ Y.card := by
      nlinarith only [ht, mul_le_mul_of_nonneg_right hxhalf (Nat.cast_nonneg (α := ℝ) Y.card)]
    exact_mod_cast hY'
  have hcopy : ((copies H G Y).card : ℝ) <
      x^c * (Y.card : ℝ) ^ h := by
    have hM : ((copies H G Y).card : ℝ) ≤ (copies H G S).card := by
      exact_mod_cast Finset.card_le_card (copies_mono H G hYS)
    apply (hM.trans_lt hfew).trans_le
    change x^e * (S.card : ℝ)^h ≤ x^c * (Y.card : ℝ)^h
    dsimp [e]
    rw [pow_add, pow_mul, mul_assoc, ← mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hy _) (by positivity)
  have hwidth {A : Finset V} (hA : x^b * Y.card ≤ (A.card : ℝ)) :
      x^d' * S.card ≤ x^d * A.card := by
    have hm := hA.trans' (mul_le_mul_of_nonneg_left hy (pow_nonneg hx.le b))
    have := mul_le_mul_of_nonneg_left hm (pow_nonneg hx.le d)
    simpa only [d', pow_add, mul_assoc, mul_left_comm, mul_comm] using this
  rcases htri G Y x hYtwo hx (hx'.trans ((min_le_right _ _).trans (min_le_right _ _))) with
    ⟨A, hAY, hA, hACount⟩ | hmany | ⟨sign, A, B, hAY, hBY, hAB, hA, hB, hsp⟩
  · have hA' := hwidth hA
    rw [← card_delete g] at hACount
    obtain ⟨Bs, hm', hBs⟩ := hsmall G A x m hx
      (hx'.trans ((min_le_right _ _).trans (min_le_left _ _))) hm (hsize.trans hA') hACount
    exact Or.inl ⟨Bs, hm', restricted_mono hBs hAY hA'⟩
  · exact False.elim (not_le_of_gt hcopy hmany)
  · refine Or.inr ⟨sign, A, B, hAY, hBY, hAB, (hwidth hA).trans ?_, ?_, hsp⟩
    · simpa using mul_le_mul_of_nonneg_right (pow_le_one₀ hx.le hxone)
        (show 0 ≤ (A.card : ℝ) by positivity)
    · simpa only [p, K, Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv, mul_comm] using hB

theorem blockade_of_few {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) {d e : ℕ} {x₀ : ℝ} (hx₀ : x₀ ≤ 1 / 2)
    (hfew : FewCopiesBlockade H d e x₀) :
    HasBlockadeBound H (d + 1) x₀ := by
  intro V _ G S x k hx hxc hk hAvoid hsize
  have hxhalf := hxc.trans hx₀
  have hwidth : 2 * x^(d+1) * S.card ≤ x^d * S.card := by
    rw [pow_succ]
    nlinarith only [mul_le_mul_of_nonneg_right hxhalf (show 0 ≤ x^d * (S.card : ℝ) by positivity)]
  have hsize' : 1 ≤ x^d * S.card := by linarith
  have hn : 0 < (S.card : ℝ) := by
    by_contra! h
    linarith [mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hx.le d) h]
  have hc : ((copies H G S).card : ℝ) < x^e * (S.card : ℝ) ^ Fintype.card W := by
    rw [copies_empty_of_avoids hAvoid, Finset.card_empty, Nat.cast_zero]
    positivity
  have hm : ((2*k : ℕ) : ℝ) ≤ log x⁻¹ := by push_cast; linarith
  obtain ⟨B, hh, hB⟩ := hfew G S x (2*k) hx hxc hm hsize' hc
  exact color_pigeonhole hh (restricted_mono hB Subset.rfl hwidth)

end OMA.BNSS

namespace OMA.BNSS

open Finset SimpleGraph Filter Real
open scoped BigOperators

variable {V W : Type*} [DecidableEq V] [Fintype W] [DecidableEq W]

def toggle (H : SimpleGraph W) (g : W) (D : Finset W) : SimpleGraph W where
  Adj a b := H.Adj a b ∧ (a = g → b ∈ D) ∧ (b = g → a ∈ D)
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun a h ↦ H.loopless.irrefl a h.1⟩

theorem toggle_full {W : Type*} (H : SimpleGraph W) (g : W) (D : Finset W)
    (hD : ∀ a, H.Adj g a → a ∈ D) : toggle H g D = H := by
  ext a b
  change (H.Adj a b ∧ (a = g → b ∈ D) ∧ (b = g → a ∈ D)) ↔ _
  refine ⟨And.left, fun h ↦ ⟨h, ?_, ?_⟩⟩
  · rintro rfl
    exact hD _ h
  · rintro rfl
    exact hD _ h.symm

theorem toggle_none {W : Type*} (H : SimpleGraph W) (g a : W) : ¬ (toggle H g ∅).Adj g a :=
  fun h ↦ Finset.notMem_empty _ (h.2.1 rfl)

noncomputable def special (H : SimpleGraph W) (G : SimpleGraph V) (g : W)
    (A B : Finset V) : Finset (W → V) :=
  copiesInParts H G (Function.update (fun _ ↦ B) g A)

theorem mem_special {H : SimpleGraph W} {G : SimpleGraph V} {g : W}
    {A B : Finset V} {f : W → V} :
    f ∈ special H G g A B ↔ Embeds H G f ∧ f g ∈ A ∧ ∀ b ≠ g, f b ∈ B := by
  rw [special, mem_copiesInParts]
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨h, by simpa using h' g, fun b hb ↦ by simpa [Function.update_of_ne hb] using h' b⟩
  · rintro ⟨h, hA, hB⟩
    refine ⟨h, fun b ↦ ?_⟩
    by_cases hb : b = g
    · subst b
      simpa using hA
    · simpa [Function.update_of_ne hb] using hB b hb

theorem special_subset {H : SimpleGraph W} {G : SimpleGraph V} {g : W}
    {A B S : Finset V} (hA : A ⊆ S) (hB : B ⊆ S) :
    special H G g A B ⊆ copies H G S := by
  intro f hf
  obtain ⟨he, ha, hb⟩ := mem_special.mp hf
  refine mem_copies.mpr ⟨he, fun w ↦ ?_⟩
  by_cases hw : w = g
  · simpa [hw] using hA ha
  · exact hB (hb w hw)

def extendOne (g : W) (a : V) (f : ({v | v ≠ g} : Set W) → V) (w : W) : V :=
  if h : w = g then a else f ⟨w, h⟩

theorem extendOne_at {V W : Type*} [DecidableEq W]
    (g : W) (a : V) (f : ({v | v ≠ g} : Set W) → V) :
    extendOne g a f g = a := by simp [extendOne]

theorem extendOne_away {V W : Type*} [DecidableEq W]
    (g : W) (a : V) (f : ({v | v ≠ g} : Set W) → V)
    (w : ({v | v ≠ g} : Set W)) :
    extendOne g a f w = f w := by
  simp [extendOne, show w.val ≠ g from w.2]

noncomputable def nonneighbours (G : SimpleGraph V) (B : Finset V) (a : V) : Finset V := by
  classical
  exact B.filter (fun b ↦ ¬ G.Adj a b)

theorem mem_nonneighbours {V : Type*} {G : SimpleGraph V} {B : Finset V} {a b : V} :
    b ∈ nonneighbours G B a ↔ b ∈ B ∧ ¬ G.Adj a b := by
  classical
  simp [nonneighbours]

theorem extendOne_isolated {H : SimpleGraph W} {G : SimpleGraph V} {g : W}
    {A B : Finset V} {a : V} (ha : a ∈ A) (hAB : Disjoint A B)
    {f : ({v | v ≠ g} : Set W) → V}
    (hf : f ∈ copies (H.induce ({v | v ≠ g} : Set W)) G (nonneighbours G B a)) :
    extendOne g a f ∈ special (toggle H g ∅) G g A B := by
  obtain ⟨⟨hi, he⟩, hfm⟩ := mem_copies.mp hf
  have hv := fun w ↦ mem_nonneighbours.mp (hfm w)
  apply mem_special.mpr
  refine ⟨⟨?_, ?_⟩, by simpa [extendOne_at] using ha,
    fun w hw ↦ by simpa [extendOne, hw] using (hv ⟨w, hw⟩).1⟩
  · intro p q hpq
    by_cases hp : p = g <;> by_cases hq : q = g
    · exact hp.trans hq.symm
    · exfalso
      have heq : a = f ⟨q, hq⟩ := by simpa [extendOne, hp, hq] using hpq
      exact Finset.disjoint_left.mp hAB ha (heq.symm ▸ (hv ⟨q, hq⟩).1)
    · exfalso
      have heq : f ⟨p, hp⟩ = a := by simpa [extendOne, hp, hq] using hpq
      exact Finset.disjoint_left.mp hAB ha (heq ▸ (hv ⟨p, hp⟩).1)
    · have heq : f ⟨p, hp⟩ = f ⟨q, hq⟩ := by simpa [extendOne, hp, hq] using hpq
      exact congrArg Subtype.val (hi heq)
  · intro p q
    by_cases hp : p = g <;> by_cases hq : q = g
    · subst p
      subst q
      simp
    · subst p
      simp [toggle_none, extendOne, hq, (hv ⟨q, hq⟩).2]
    · subst q
      have hna : ¬ G.Adj (f ⟨p, hp⟩) a := fun h ↦ (hv ⟨p, hp⟩).2 h.symm
      simp [extendOne, hp, hna, (toggle H g ∅).adj_comm p g, toggle_none]
    · simpa [toggle, extendOne, hp, hq] using he ⟨p, hp⟩ ⟨q, hq⟩

theorem special_zero_lower {H : SimpleGraph W} {G : SimpleGraph V}
    {g : W} {A B : Finset V} (hAB : Disjoint A B) :
    ∑ a ∈ A, (copies (H.induce ({v | v ≠ g} : Set W)) G (nonneighbours G B a)).card ≤
      (special (toggle H g ∅) G g A B).card := by
  classical
  let possible (a : V) := copies (H.induce ({v | v ≠ g} : Set W)) G (nonneighbours G B a)
  rw [← Finset.card_sigma]
  apply Finset.card_le_card_of_injOn (fun p : Sigma (fun _ : V ↦ ({v | v ≠ g} : Set W) → V) ↦
    extendOne g p.1 p.2)
  · intro p hp
    obtain ⟨hpa, hpf⟩ := Finset.mem_sigma.mp hp
    exact extendOne_isolated hpa hAB hpf
  · intro p hp q hq eq
    obtain ⟨a, f⟩ := p
    obtain ⟨b, u⟩ := q
    have hab := congrFun eq g
    simp only [extendOne_at] at hab
    subst b
    congr 1
    funext z
    simpa only [extendOne_away] using congrFun eq z.val

theorem first_small_step {W : Type*} [DecidableEq W]
    {T : Finset W} {f : Finset W → ℝ} {x : ℝ} {n c : ℕ} {r : ℝ}
    (h0 : x ^ n * r ≤ f ∅) (hT : f T < x ^ (n + c * T.card) * r) :
    ∃ D ⊆ T, ∃ w ∈ T, w ∉ D ∧ x ^ (n + c * D.card) * r ≤ f D ∧
      f (insert w D) < x ^ (n + c * (D.card + 1)) * r := by
  induction T using Finset.induction_on with
  | empty => exact False.elim (not_lt_of_ge (by simpa using h0) hT)
  | @insert w T hw ih =>
    by_cases hlow : f T < x ^ (n + c * T.card) * r
    · obtain ⟨D, hD, u, hu, huD, hDlo, hDhi⟩ := ih hlow
      exact ⟨D, hD.trans (Finset.subset_insert _ _), u, Finset.mem_insert_of_mem hu,
        huD, hDlo, hDhi⟩
    · exact ⟨T, Finset.subset_insert _ _, w, Finset.mem_insert_self _ _, hw,
        le_of_not_gt hlow, by simpa [Finset.card_insert_of_notMem hw] using hT⟩

end OMA.BNSS

namespace OMA.BNSS

open Finset SimpleGraph Filter Real
open scoped BigOperators

variable {V W : Type*} [DecidableEq V] [Fintype W] [DecidableEq W]

abbrev Others (g h : W) := ({w | w ≠ g ∧ w ≠ h} : Set W)

def extendTwo (g h : W) (p : V × V) (ψ : Others g h → V) (w : W) : V :=
  if hg : w = g then p.1 else if hh : w = h then p.2 else ψ ⟨w, hg, hh⟩

theorem extendTwo_at_left {V W : Type*} [DecidableEq W]
    (g h : W) (p : V × V) (ψ : Others g h → V) :
    extendTwo g h p ψ g = p.1 := by simp [extendTwo]

theorem extendTwo_at_right {V W : Type*} [DecidableEq W]
    {g h : W} (hgh : g ≠ h) (p : V × V) (ψ : Others g h → V) :
    extendTwo g h p ψ h = p.2 := by simp [extendTwo, hgh.symm]

theorem extendTwo_away {V W : Type*} [DecidableEq W]
    (g h : W) (p : V × V) (ψ : Others g h → V) (w : Others g h) :
    extendTwo g h p ψ w = ψ w := by
  simp [extendTwo, show w.val ≠ g from w.2.1, show w.val ≠ h from w.2.2]

def Compatible (H : SimpleGraph W) (G : SimpleGraph V) {g h : W}
    (ψ : Others g h → V) (w : W) (v : V) : Prop :=
  ∀ i : Others g h, v ≠ ψ i ∧ (H.Adj w i ↔ G.Adj v (ψ i))

noncomputable def candidates (H : SimpleGraph W) (G : SimpleGraph V) {g h : W}
    (ψ : Others g h → V) (w : W) (S : Finset V) : Finset V := by
  classical
  exact S.filter (Compatible H G ψ w)

theorem mem_candidates {V W : Type*} {H : SimpleGraph W} {G : SimpleGraph V} {g h : W}
    {ψ : Others g h → V} {w : W} {S : Finset V} {v : V} :
    v ∈ candidates H G ψ w S ↔ v ∈ S ∧ Compatible H G ψ w v := by
  classical
  simp [candidates]

theorem embeds_extendTwo {H : SimpleGraph W} {G : SimpleGraph V} {g h : W}
    (hgh : g ≠ h) {p : V × V} {ψ : Others g h → V}
    (hψ : Embeds (H.induce (Others g h)) G ψ)
    (hneq : p.1 ≠ p.2) (ha : Compatible H G ψ g p.1)
    (hb : Compatible H G ψ h p.2) (hab : H.Adj g h ↔ G.Adj p.1 p.2) :
    Embeds H G (extendTwo g h p ψ) := by
  have hnull : ∀ w : W, ¬ (w = g ∧ w = h) := fun w ⟨u,v⟩ ↦ hgh (u.symm.trans v)
  let f := extendTwo g h p ψ
  have f_g : f g = p.1 := extendTwo_at_left ..
  have f_h : f h = p.2 := extendTwo_at_right hgh ..
  have f_w (w : W) (hg : w ≠ g) (hh : w ≠ h) : f w = ψ ⟨w, hg, hh⟩ :=
    extendTwo_away g h p ψ ⟨w, hg, hh⟩
  have casesW (w : W) : w = g ∨ w = h ∨ w ≠ g ∧ w ≠ h := by tauto
  constructor
  · intro u v heq
    rcases casesW u with rfl | rfl | ⟨hug,huh⟩ <;>
      rcases casesW v with rfl | rfl | ⟨hvg,hvh⟩
    · rfl
    · exact False.elim (hneq (f_g.symm.trans (heq.trans f_h)))
    · exact False.elim ((ha ⟨v,hvg,hvh⟩).1 (f_g.symm.trans (heq.trans (f_w v hvg hvh))))
    · exact False.elim (hneq (f_g.symm.trans (heq.symm.trans f_h)))
    · rfl
    · exact False.elim ((hb ⟨v,hvg,hvh⟩).1 (f_h.symm.trans (heq.trans (f_w v hvg hvh))))
    · exact False.elim ((ha ⟨u,hug,huh⟩).1 (f_g.symm.trans (heq.symm.trans (f_w u hug huh))))
    · exact False.elim ((hb ⟨u,hug,huh⟩).1 (f_h.symm.trans (heq.symm.trans (f_w u hug huh))))
    · exact congrArg Subtype.val (hψ.1 ((f_w u hug huh).symm.trans (heq.trans (f_w v hvg hvh))))
  · intro u v
    change H.Adj u v ↔ G.Adj (f u) (f v)
    rcases casesW u with hu | hu | ⟨hug,huh⟩ <;>
      rcases casesW v with hv | hv | ⟨hvg,hvh⟩
    · rw [hu,hv]
      simp
    · rw [hu,hv,f_g,f_h]
      exact hab
    · rw [hu,f_g,f_w v hvg hvh]
      exact (ha ⟨v,hvg,hvh⟩).2
    · rw [hu,hv,f_h,f_g,H.adj_comm h g,G.adj_comm p.2 p.1]
      exact hab
    · rw [hu,hv]
      simp
    · rw [hu,f_h,f_w v hvg hvh]
      exact (hb ⟨v,hvg,hvh⟩).2
    · rw [hv,H.adj_comm u g,G.adj_comm (f u) (f g),f_g,f_w u hug huh]
      exact (ha ⟨u,hug,huh⟩).2
    · rw [hv,H.adj_comm u h,G.adj_comm (f u) (f h),f_h,f_w u hug huh]
      exact (hb ⟨u,hug,huh⟩).2
    · rw [f_w u hug huh, f_w v hvg hvh]
      exact hψ.2 ⟨u,hug,huh⟩ ⟨v,hvg,hvh⟩

noncomputable def pairsFor (H : SimpleGraph W) (G : SimpleGraph V) (g h : W)
    (ψ : Others g h → V) (A B : Finset V) : Finset (V × V) := by
  classical
  exact ((candidates H G ψ g A) ×ˢ (candidates H G ψ h B)).filter
    (fun p ↦ H.Adj g h ↔ G.Adj p.1 p.2)

theorem mem_pairsFor {H : SimpleGraph W} {G : SimpleGraph V} {g h : W}
    {ψ : Others g h → V} {A B : Finset V} {p : V × V} :
    p ∈ pairsFor H G g h ψ A B ↔
      (p.1 ∈ A ∧ Compatible H G ψ g p.1) ∧
      (p.2 ∈ B ∧ Compatible H G ψ h p.2) ∧ (H.Adj g h ↔ G.Adj p.1 p.2) := by
  classical
  simp only [pairsFor, Finset.mem_filter, Finset.mem_product, mem_candidates, and_assoc]

theorem special_fibre_card {H : SimpleGraph W} {G : SimpleGraph V} {g h : W}
    {A B : Finset V} (hgh : g ≠ h) (hAB : Disjoint A B) :
    (special H G g A B).card =
      ∑ ψ ∈ copies (H.induce (Others g h)) G B, (pairsFor H G g h ψ A B).card := by
  classical
  rw [← Finset.card_sigma]
  apply Finset.card_bij (fun f _ ↦ ⟨fun i : Others g h ↦ f i, (f g, f h)⟩)
  · intro f hf
    obtain ⟨⟨hi, he⟩, hg, hh⟩ := mem_special.mp hf
    have hp (w : W) (hw : w = g ∨ w = h) : Compatible H G (fun i : Others g h ↦ f i) w (f w) := by
      intro i
      refine ⟨?_, he w i⟩
      rcases hw with rfl | rfl
      · exact fun e ↦ i.2.1 (hi e).symm
      · exact fun e ↦ i.2.2 (hi e).symm
    apply mem_sigma.mpr
    exact ⟨mem_copies.mpr ⟨⟨fun _ _ e ↦ Subtype.ext (hi e), fun i j ↦ he i j⟩,
      fun i ↦ hh i i.2.1⟩, mem_pairsFor.mpr
        ⟨⟨hg, hp g (Or.inl rfl)⟩, ⟨hh h hgh.symm, hp h (Or.inr rfl)⟩, he g h⟩⟩
  · intro f hf f' hf' he
    funext w
    by_cases hwg : w = g
    · subst w
      exact congrArg (fun p : Sigma (fun _ : Others g h → V ↦ V × V) ↦ p.2.1) he
    · by_cases hwh : w = h
      · subst w
        exact congrArg (fun p : Sigma (fun _ : Others g h → V ↦ V × V) ↦ p.2.2) he
      · exact congrFun (congrArg Sigma.fst he) ⟨w, hwg, hwh⟩
  · intro z hz
    obtain ⟨ψ, p⟩ := z
    obtain ⟨hψ, hp⟩ := Finset.mem_sigma.mp hz
    obtain ⟨hemb, hψB⟩ := mem_copies.mp hψ
    obtain ⟨⟨ha,hpa⟩, ⟨hb,hpb⟩, hr⟩ := mem_pairsFor.mp hp
    have hn : p.1 ≠ p.2 := fun e ↦ Finset.disjoint_left.mp hAB ha (e.symm ▸ hb)
    use extendTwo g h p ψ
    refine ⟨mem_special.mpr ⟨embeds_extendTwo hgh hemb hn hpa hpb hr,
      by simpa only [extendTwo_at_left] using ha, ?_⟩, ?_⟩
    · intro w hw
      by_cases hwh : w = h
      · subst w
        simpa only [extendTwo_at_right hgh] using hb
      · simpa only [extendTwo_away g h p ψ ⟨w,hw,hwh⟩] using hψB ⟨w,hw,hwh⟩
    · congr 1
      · funext i
        exact extendTwo_away g h p ψ i
      · exact Prod.ext (extendTwo_at_left ..) (extendTwo_at_right hgh ..)

end OMA.BNSS

namespace OMA.BNSS

open Finset Filter SimpleGraph Real
open scoped BigOperators

variable {V W : Type*} [DecidableEq V] [Fintype W] [DecidableEq W]

theorem card_copies_le {V : Type*} (H : SimpleGraph W) (G : SimpleGraph V) (S : Finset V) :
    (copies H G S).card ≤ S.card ^ Fintype.card W := by
  classical
  unfold copies copiesInParts
  exact (Finset.card_filter_le _ _).trans_eq (by rw [Fintype.card_piFinset]; simp)

theorem card_others {g h : W} (hgh : g ≠ h) :
    Fintype.card (Others g h) = Fintype.card W - 2 := by
  classical
  have hh : h ∈ (univ : Finset W).erase g := Finset.mem_erase.mpr ⟨hgh.symm, mem_univ _⟩
  have he : (univ.filter (fun w : W ↦ w ≠ g ∧ w ≠ h)) = (univ.erase g).erase h := by
    ext w
    simp only [mem_filter, mem_univ, true_and, mem_erase, and_true]
    exact and_comm
  change Fintype.card {w : W // w ≠ g ∧ w ≠ h} = _
  rw [Fintype.card_subtype, he, Finset.card_erase_of_mem hh,
    Finset.card_erase_of_mem (mem_univ g), Finset.card_univ]
  omega

open scoped Classical in
theorem cut_as_card (G : SimpleGraph V) (A B : Finset V) :
    crossEdges G B A = (((A ×ˢ B).filter fun p ↦ G.Adj p.1 p.2).card : ℝ) := by
  classical
  unfold crossEdges
  norm_cast
  rw [← Finset.card_sigma]
  apply Finset.card_bij (fun p _ ↦ (p.1,p.2))
  · intro p hp
    obtain ⟨ha, hb⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hb, he⟩ := mem_neighbours.mp hb
    exact mem_filter.mpr ⟨mem_product.mpr ⟨ha, hb⟩, he⟩
  · intro a ha b hb e
    cases a
    cases b
    simpa using e
  · rintro ⟨a,b⟩ hp
    obtain ⟨hq, hp⟩ := mem_filter.mp hp
    obtain ⟨ha,hb⟩ := mem_product.mp hq
    exact ⟨⟨a,b⟩, mem_sigma.mpr ⟨ha, mem_neighbours.mpr ⟨hb,hp⟩⟩, rfl⟩

theorem toggle_others {W : Type*} (H : SimpleGraph W) (g h : W) (D : Finset W) :
    (toggle H g D).induce (Others g h) = H.induce (Others g h) := by
  ext u v
  exact ⟨And.left, fun e ↦ ⟨e, fun hg ↦ False.elim (u.2.1 hg),
    fun hg ↦ False.elim (v.2.1 hg)⟩⟩

theorem candidates_toggle_insert (H : SimpleGraph W) (G : SimpleGraph V)
    (g h w : W) (D : Finset W) (S : Finset V) (ψ : Others g h → V) :
    candidates (toggle H g (insert h D)) G ψ w S =
      candidates (toggle H g D) G ψ w S := by
  classical
  ext v
  simp only [mem_candidates]
  refine and_congr_right (fun _ ↦ forall_congr' fun i ↦ ?_)
  apply and_congr_right
  intro _
  have hrel : (toggle H g (insert h D)).Adj w i ↔ (toggle H g D).Adj w i := by
    have hg : i.val ≠ g := i.2.1
    have hh : i.val ≠ h := i.2.2
    simp [toggle, Finset.mem_insert, hg, hh]
  exact iff_congr hrel Iff.rfl

theorem low_and_high_fibres {H : SimpleGraph W} {G : SimpleGraph V} {g h : W}
    {D : Finset W} {A B : Finset V} (hh : H.Adj g h) (hnot : h ∉ D)
    (hAB : Disjoint A B) :
    let Ψ := copies (H.induce (Others g h)) G B
    let U := fun ψ ↦ candidates (toggle H g D) G ψ g A
    let V' := fun ψ ↦ candidates (toggle H g D) G ψ h B
    let area := fun ψ ↦ ((U ψ).card : ℝ) * (V' ψ).card
    let edges := fun ψ ↦ crossEdges G (V' ψ) (U ψ)
    (((special (toggle H g D) G g A B).card : ℝ) = ∑ ψ ∈ Ψ, (area ψ - edges ψ)) ∧
    (((special (toggle H g (insert h D)) G g A B).card : ℝ) = ∑ ψ ∈ Ψ, edges ψ) := by
  classical
  intro Ψ U V' area edges
  have hgh := hh.ne
  have hlo : ¬ (toggle H g D).Adj g h := fun e ↦ hnot (e.2.1 rfl)
  have hhi : (toggle H g (insert h D)).Adj g h :=
    ⟨hh, fun _ ↦ mem_insert_self _ _, fun r ↦ False.elim (hgh r.symm)⟩
  constructor
  · rw [special_fibre_card hgh hAB, toggle_others, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro ψ hψ
    have hpair :
        pairsFor (toggle H g D) G g h ψ A B =
          ((U ψ) ×ˢ (V' ψ)).filter (fun p ↦ ¬ G.Adj p.1 p.2) := by
      ext p
      simp [pairsFor, U, V', hlo]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := ((U ψ) ×ˢ (V' ψ))) (p := fun p ↦ G.Adj p.1 p.2)
    have hsplit' : ((((U ψ) ×ˢ (V' ψ)).filter fun p ↦ G.Adj p.1 p.2).card : ℝ) +
        ((((U ψ) ×ˢ (V' ψ)).filter fun p ↦ ¬ G.Adj p.1 p.2).card : ℝ) =
          ((U ψ).card : ℝ) * (V' ψ).card := by
      rw [← Nat.cast_add, ← Nat.cast_mul, hsplit, Finset.card_product]
    rw [hpair]
    dsimp [area, edges]
    rw [cut_as_card]
    linarith
  · rw [special_fibre_card hgh hAB, toggle_others, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro ψ hψ
    dsimp [edges]
    rw [cut_as_card]
    apply congrArg (fun A : Finset (V × V) ↦ (A.card : ℝ))
    unfold pairsFor
    rw [candidates_toggle_insert H G g h g D A ψ, candidates_toggle_insert H G g h h D B ψ]
    ext p
    simp [U, V', hhi]

theorem local_split_of_step {H : SimpleGraph W} {G : SimpleGraph V} {g h : W} {D : Finset W}
    {A B : Finset V} (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : Disjoint A B) (hh : H.Adj g h) (hnot : h ∉ D)
    {u q : ℝ} (hu : 0 ≤ u) (hq : 0 ≤ q)
    (hlow : 2 * u * A.card * (B.card : ℝ)^(Fintype.card W - 1) ≤
      (special (toggle H g D) G g A B).card)
    (hhigh : ((special (toggle H g (insert h D)) G g A B).card : ℝ) <
      q * (special (toggle H g D) G g A B).card) :
    ∃ A' ⊆ A, ∃ B' ⊆ B, u * A.card ≤ (A'.card : ℝ) ∧ u * B.card ≤ (B'.card : ℝ) ∧
      crossEdges G A' B' ≤ 2 * q * A'.card * B'.card := by
  classical
  obtain ⟨he, he'⟩ := low_and_high_fibres (D := D) hh hnot hAB
  let Ψ := copies (H.induce (Others g h)) G B
  let U := fun ψ : Others g h → V ↦ candidates (toggle H g D) G ψ g A
  let Z := fun ψ : Others g h → V ↦ candidates (toggle H g D) G ψ h B
  let mass := fun ψ ↦ ((U ψ).card : ℝ) * (Z ψ).card - crossEdges G (Z ψ) (U ψ)
  let cost := fun ψ ↦ crossEdges G (Z ψ) (U ψ)
  have hw : 0 ≤ u * A.card * B.card := by positivity
  have hP : Ψ.card ≤ B.card ^ (Fintype.card W - 2) := by
    rw [← card_others hh.ne]
    exact card_copies_le _ _ _
  have hPW : 2 ≤ Fintype.card W :=
    Fintype.one_lt_card_iff.mpr ⟨g,h,hh.ne⟩
  have hsum : 2 * (u * A.card * B.card) * Ψ.card ≤ ∑ ψ ∈ Ψ, mass ψ := by
    change ((special (toggle H g D) G g A B).card : ℝ) = ∑ ψ ∈ Ψ, mass ψ at he
    rw [← he]
    have h' := mul_le_mul_of_nonneg_left
      (show ((Ψ.card : ℝ)) ≤ (B.card : ℝ) ^ (Fintype.card W - 2) by exact_mod_cast hP)
      (show 0 ≤ 2 * (u * (A.card : ℝ) * B.card) by positivity)
    have hh' : Fintype.card W - 1 = Fintype.card W - 2 + 1 := by omega
    rw [hh', pow_succ] at hlow
    nlinarith only [h', hlow]
  have hstrict : ∑ ψ ∈ Ψ, cost ψ < q * ∑ ψ ∈ Ψ, mass ψ := by
    exact he' ▸ he ▸ hhigh
  obtain ⟨ψ, _, hweight, hcost⟩ := heavy_fibre
    (fun ψ _ ↦ edge_cut_nonneg _ _ _) hq hw hsum hstrict
  have hU : U ψ ⊆ A := Finset.filter_subset _ _
  have hZ : Z ψ ⊆ B := Finset.filter_subset _ _
  have harea : u * A.card * B.card ≤ ((U ψ).card : ℝ) * (Z ψ).card :=
    hweight.trans (sub_le_self _ (edge_cut_nonneg _ _ _))
  have hAnc : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hBnc : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  refine ⟨U ψ, hU, Z ψ, hZ, ?_, ?_, ?_⟩
  · apply (mul_le_mul_iff_of_pos_right hBnc).mp
    exact harea.trans (mul_le_mul_of_nonneg_left
      (by exact_mod_cast Finset.card_le_card hZ) (Nat.cast_nonneg _))
  · apply (mul_le_mul_iff_of_pos_left hAnc).mp
    have hn := mul_le_mul_of_nonneg_right
      (show ((U ψ).card : ℝ) ≤ A.card by exact_mod_cast Finset.card_le_card hU)
      (show 0 ≤ ((Z ψ).card : ℝ) by positivity)
    linarith only [harea, hn, show (A.card : ℝ) * (u * B.card) = u * A.card * B.card by ring]
  · rw [crossEdges_symm]
    have hm : mass ψ ≤ ((U ψ).card : ℝ) * (Z ψ).card :=
      sub_le_self _ (edge_cut_nonneg _ _ _)
    exact hcost.trans (by
      have h := mul_le_mul_of_nonneg_left hm (show 0 ≤ 2*q by positivity)
      linarith only [h, show 2*q*((U ψ).card : ℝ)*(Z ψ).card =
        (2*q)*(((U ψ).card : ℝ)*(Z ψ).card) by ring])

end OMA.BNSS

namespace OMA.BNSS

open Finset SimpleGraph Filter Real
open scoped BigOperators

variable {V W : Type*} [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Restore the missing edges at the distinguished pattern vertex one by one.
If the number of copies drops at a step, group the copies by their assignments
away from the two endpoints. A large group with few restored edges yields a sparse cut. -/
theorem local_pair {H : SimpleGraph W} {G : SimpleGraph V} (g : W)
    {A B : Finset V} (hA : A.Nonempty) (hB : B.Nonempty) (hAB : Disjoint A B)
    {x : ℝ} (hx : 0 < x) (hx2 : x ≤ 1/2) (a c : ℕ)
    (hh : ∀ v ∈ A, x * B.card ≤ ((nonneighbours G B v).card : ℝ)) :
    let E := a + (c+1) * Fintype.card W
    (∃ B' ⊆ B, x * B.card ≤ (B'.card : ℝ) ∧
      ((copies (H.induce ({v | v ≠ g} : Set W)) G B').card : ℝ) <
        x^a * (B'.card : ℝ)^(Fintype.card W - 1)) ∨
    x^E * A.card * (B.card : ℝ)^(Fintype.card W - 1) ≤ (special H G g A B).card ∨
    (∃ A' ⊆ A, ∃ B' ⊆ B, x^E * A.card ≤ (A'.card : ℝ) ∧
      x^E * B.card ≤ (B'.card : ℝ) ∧ crossEdges G A' B' ≤ 2 * x^c * A'.card * B'.card) := by
  classical
  intro E
  let k := Fintype.card W
  have hk : 1 ≤ k := Fintype.card_pos_iff.mpr ⟨g⟩
  have hx1 : x ≤ 1 := hx2.trans (by norm_num)
  by_cases hl : ∃ B' ⊆ B, x * B.card ≤ (B'.card : ℝ) ∧
      ((copies (H.induce ({v | v ≠ g} : Set W)) G B').card : ℝ) <
        x^a * (B'.card : ℝ)^(k - 1)
  · exact Or.inl hl
  refine Or.inr ?_
  by_cases hi : x^E * A.card * (B.card : ℝ)^(k-1) ≤ (special H G g A B).card
  · exact Or.inl hi
  refine Or.inr ?_
  let f := fun D : Finset W ↦ ((special (toggle H g D) G g A B).card : ℝ)
  let T := univ.filter (H.Adj g)
  let r := (A.card : ℝ) * (B.card : ℝ)^(k-1)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hT : T.card ≤ k-1 := by
    have h : T ⊆ univ.erase g := by
      intro v hv
      exact mem_erase.mpr ⟨(mem_filter.mp hv).2.ne.symm, mem_univ _⟩
    exact (Finset.card_le_card h).trans_eq (by simp [k])
  have h0 : x^(a+(k-1)) * r ≤ f ∅ := by
    have hpoint (v : V) (hv : v ∈ A) :
        x^(a+(k-1)) * (B.card : ℝ)^(k-1) ≤
          (copies (H.induce ({v | v ≠ g} : Set W)) G (nonneighbours G B v)).card := by
      have hh' := hh v hv
      let C := nonneighbours G B v
      have hC : C ⊆ B := Finset.filter_subset _ _
      have hf := le_of_not_gt (fun hlt ↦ hl ⟨C, hC, hh', hlt⟩)
      rw [pow_add, mul_assoc, ← mul_pow]
      exact (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hh' _) (by positivity)).trans hf
    have hsum := Finset.sum_le_sum hpoint
    have hcount : (∑ v ∈ A, ((copies (H.induce ({v | v ≠ g} : Set W)) G
        (nonneighbours G B v)).card : ℝ)) ≤ f ∅ := by
      dsimp [f]
      exact_mod_cast special_zero_lower (H := H) (G := G) (g := g) hAB
    exact (by
      simpa only [Finset.sum_const, nsmul_eq_mul, r, mul_comm, mul_left_comm, mul_assoc]
        using hsum : x^(a+(k-1)) * r ≤ _).trans hcount
  have hTfull : f T < x^(a+(k-1) + c*T.card) * r := by
    have hEq : toggle H g T = H := toggle_full H g T
      (fun w hw ↦ mem_filter.mpr ⟨mem_univ _, hw⟩)
    dsimp [f]
    rw [hEq]
    have hn : a+(k-1) + c*T.card ≤ E := by
      change a+(k-1) + c*T.card ≤ a+(c+1)*k
      rw [Nat.add_mul]
      have h1 := Nat.mul_le_mul_left c (show T.card ≤ k by omega)
      omega
    have hp := mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hx.le hx1 hn) hr
    have hh : ((special H G g A B).card : ℝ) < x^E * r := by
      simpa only [r, mul_assoc] using lt_of_not_ge hi
    exact hh.trans_le hp
  obtain ⟨D, hDT, w, hwT, hnot, hlo, hhi⟩ := first_small_step h0 hTfull
  have hwH : H.Adj g w := (mem_filter.mp hwT).2
  have hRat : f (insert w D) < x^c * f D := by
    refine hhi.trans_le ?_
    rw [Nat.mul_succ, ← Nat.add_assoc, pow_add]
    nlinarith only [mul_le_mul_of_nonneg_left hlo (show 0 ≤ x^c by positivity)]
  have hN : a + (k-1) + c * D.card + 1 ≤ E := by
    change a + (k-1) + c * D.card + 1 ≤ a+(c+1)*k
    rw [Nat.add_mul]
    have hDC := (Finset.card_le_card hDT).trans hT
    have h1 := Nat.mul_le_mul_left c (show D.card ≤ k by omega)
    omega
  have hfac : 2 * x^E ≤ x^(a+(k-1)+c*D.card) := by
    have hpow := pow_le_pow_of_le_one hx.le hx1 hN
    rw [pow_succ] at hpow
    nlinarith only [hpow, mul_le_mul_of_nonneg_left hx2
      (show 0 ≤ x^(a+(k-1)+c*D.card) by positivity)]
  have hlo' : 2 * x^E * A.card * (B.card : ℝ)^(k-1) ≤ f D := by
    rw [mul_assoc]
    exact (mul_le_mul_of_nonneg_right hfac hr).trans hlo
  exact local_split_of_step hA hB hAB hwH hnot (pow_nonneg hx.le _) (pow_nonneg hx.le _) hlo' hRat

end OMA.BNSS

namespace OMA.BNSS

open Finset SimpleGraph Filter Real
open scoped BigOperators

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem trim_average (f : V → ℝ) (q : ℝ) (m : ℕ) (S : Finset V)
    (hm : m ≤ S.card) (hsum : ∑ u ∈ S, f u ≤ q * S.card) :
    ∃ T ⊆ S, T.card = m ∧ ∑ u ∈ T, f u ≤ q * T.card := by
  classical
  revert hm hsum
  refine Finset.strongInductionOn S ?_
  intro S ih hm hsum
  by_cases hSame : m = S.card
  · exact ⟨S, Subset.rfl, hSame.symm, hsum⟩
  · by_cases hEvery : ∀ u ∈ S, f u ≤ q
    · obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq hm
      refine ⟨T, hT, hTc, ?_⟩
      calc
        ∑ u ∈ T, f u ≤ ∑ _u ∈ T, q := sum_le_sum fun u hu ↦ hEvery u (hT hu)
        _ = _ := by simp [mul_comm]
    · push Not at hEvery
      obtain ⟨u, hu, hqu⟩ := hEvery
      have hd : (S.erase u).card + 1 = S.card := Finset.card_erase_add_one hu
      have hc : (S.erase u).card < S.card := by omega
      have hsum' : ∑ j ∈ S.erase u, f j ≤ q * (S.erase u).card := by
        have hadd : (∑ j ∈ S.erase u, f j) + f u = ∑ j ∈ S, f j :=
          Finset.sum_erase_add _ _ hu
        have hrd : ((S.erase u).card : ℝ) + 1 = S.card := by exact_mod_cast hd
        nlinarith only [hsum, hqu, hadd, congrArg (fun z : ℝ ↦ q * z) hrd]
      obtain ⟨T, hT, hTc, hTf⟩ := ih (S.erase u) (Finset.erase_ssubset hu) (by omega) hsum'
      exact ⟨T, hT.trans (Finset.erase_subset _ _), hTc, hTf⟩

theorem trim_cross_edges {q : ℝ} {A B : Finset V} {m : ℕ} (hm : m ≤ A.card)
    (h : crossEdges G A B ≤ q * A.card * B.card) :
    ∃ C ⊆ A, C.card = m ∧ crossEdges G C B ≤ q * C.card * B.card := by
  have h' : ∑ a ∈ A, ((neighbours G B a).card : ℝ) ≤ (q * B.card) * A.card := by
    rw [← crossEdges, crossEdges_symm]
    convert h using 1 <;> ring
  obtain ⟨C, hCA, hc, hz⟩ := trim_average
    (fun a ↦ ((neighbours G B a).card : ℝ)) (q * B.card) m A hm h'
  refine ⟨C, hCA, hc, ?_⟩
  rw [crossEdges_symm]
  simpa only [crossEdges, mul_right_comm] using hz

end OMA.BNSS

namespace OMA.BNSS

open Finset SimpleGraph Filter Real
open scoped BigOperators

universe u v

variable {V : Type v} [DecidableEq V] {W : Type u} [Fintype W] [DecidableEq W]

noncomputable def goodFor (H : SimpleGraph W) (G : SimpleGraph V) (g w : W)
    (a : V) (S : Finset V) : Finset V := by
  classical
  exact S.filter fun b ↦ H.Adj g w ↔ G.Adj a b

theorem mem_goodFor {V : Type v} {W : Type u} {H : SimpleGraph W} {G : SimpleGraph V} {g w : W}
    {a b : V} {S : Finset V} :
    b ∈ goodFor H G g w a S ↔ b ∈ S ∧ (H.Adj g w ↔ G.Adj a b) := by
  classical
  simp [goodFor]

theorem goodFor_subset (H : SimpleGraph W) (G : SimpleGraph V) (g w : W)
    (a : V) (S : Finset V) : goodFor H G g w a S ⊆ S :=
  fun _ hz ↦ (mem_goodFor.mp hz).1

open scoped Classical in
theorem goodFor_removes {H : SimpleGraph W} {G : SimpleGraph V} {g w : W}
    {a : V} {S : Finset V} {q : ℝ} (hne : ∀ b ∈ S, a ≠ b)
    (h : ((neighbours (polarity G (decide (H.Adj g w))) S a).card : ℝ) ≤ q) :
    (S.card : ℝ) - q ≤ (goodFor H G g w a S).card := by
  classical
  have e : S \ goodFor H G g w a S = neighbours (polarity G (decide (H.Adj g w))) S a := by
    ext b
    rw [Finset.mem_sdiff, mem_goodFor, mem_neighbours]
    constructor <;> intro hb
    · refine ⟨hb.1, ?_⟩
      have hn := hne b hb.1
      have hnot : ¬ (H.Adj g w ↔ G.Adj a b) := fun he ↦ hb.2 ⟨hb.1, he⟩
      by_cases hg : H.Adj g w
      · simpa [polarity, hg, SimpleGraph.compl_adj, hn] using hnot
      · simpa [polarity, hg] using hnot
    · refine ⟨hb.1, fun hc ↦ ?_⟩
      have hn := hne b hb.1
      by_cases hg : H.Adj g w
      · have hnon : ¬ G.Adj a b := by simpa [polarity, hg, SimpleGraph.compl_adj, hn] using hb.2
        exact hnon (hc.2.mp hg)
      · have hadj : G.Adj a b := by simpa [polarity, hg] using hb.2
        exact hg (hc.2.mpr hadj)
  have hcard : (((S \ goodFor H G g w a S).card : ℕ) : ℝ) +
      (goodFor H G g w a S).card = S.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card (goodFor_subset H G g w a S)
  rw [e] at hcard
  linarith

theorem restrict_embedding {H : SimpleGraph W} {G : SimpleGraph V} {g : W}
    {P : W → Finset V} {a : V} (ha : a ∈ P g)
    (hdis : ∀ w ≠ g, Disjoint (P g) (P w))
    {f : ({w | w ≠ g} : Set W) → V}
    (hf : f ∈ copiesInParts (H.induce ({w | w ≠ g} : Set W)) G
      (fun w ↦ goodFor H G g w a (P w))) :
    extendOne g a f ∈ copiesInParts H G P := by
  obtain ⟨⟨hi, he⟩, hfm⟩ := mem_copiesInParts.mp hf
  have hv := fun w ↦ mem_goodFor.mp (hfm w)
  apply mem_copiesInParts.mpr
  refine ⟨⟨?_, ?_⟩, fun w ↦ ?_⟩
  · intro p q hpq
    by_cases hp : p = g <;> by_cases hq : q = g
    · exact hp.trans hq.symm
    · exfalso
      have heq : a = f ⟨q, hq⟩ := by simpa [extendOne, hp, hq] using hpq
      exact Finset.disjoint_left.mp (hdis q hq) ha (heq.symm ▸ (hv ⟨q, hq⟩).1)
    · exfalso
      have heq : f ⟨p, hp⟩ = a := by simpa [extendOne, hp, hq] using hpq
      exact Finset.disjoint_left.mp (hdis p hp) ha (heq ▸ (hv ⟨p, hp⟩).1)
    · have heq : f ⟨p, hp⟩ = f ⟨q, hq⟩ := by simpa [extendOne, hp, hq] using hpq
      exact congrArg Subtype.val (hi heq)
  · intro p q
    by_cases hp : p = g <;> by_cases hq : q = g
    · subst p
      subst q
      simp
    · subst p
      simpa [extendOne, hq] using (hv ⟨q,hq⟩).2
    · subst q
      simpa [extendOne, hp, H.adj_comm p g, G.adj_comm (f ⟨p,hp⟩) a]
        using (hv ⟨p,hp⟩).2
    · simpa [extendOne, hp, hq] using he ⟨p, hp⟩ ⟨q, hq⟩
  · by_cases hw : w = g
    · subst w
      simpa [extendOne] using ha
    · simpa [extendOne, hw] using (hv ⟨w,hw⟩).1

theorem copies_count_sum {H : SimpleGraph W} {G : SimpleGraph V} {g : W}
    {P : W → Finset V} (hdis : ∀ w ≠ g, Disjoint (P g) (P w)) :
    ∑ a ∈ P g, (copiesInParts (H.induce ({w | w ≠ g} : Set W)) G
      (fun w ↦ goodFor H G g w a (P w))).card ≤ (copiesInParts H G P).card := by
  classical
  rw [← Finset.card_sigma]
  apply Finset.card_le_card_of_injOn (fun p : Sigma (fun _ : V ↦ ({v | v ≠ g} : Set W) → V) ↦
    extendOne g p.1 p.2)
  · intro p hp
    obtain ⟨hpa, hpf⟩ := Finset.mem_sigma.mp hp
    exact restrict_embedding hpa hdis hpf
  · intro p hp q hq eq
    obtain ⟨a, f⟩ := p
    obtain ⟨b, u⟩ := q
    have hab := congrFun eq g
    simp only [extendOne_at] at hab
    subst b
    congr 1
    funext z
    simpa only [extendOne_away] using congrFun eq z.val

set_option maxHeartbeats 1000000 in
open scoped Classical in
theorem copies_of_part_bounds {V : Type v} [DecidableEq V] (G : SimpleGraph V)
    {q t : ℝ} (hq : 0 ≤ q) (ht : 0 ≤ t) :
    ∀ n : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W], Fintype.card W = n →
    ∀ (H : SimpleGraph W) (P : W → Finset V),
      (∀ w, t + (n-1 : ℕ) * q ≤ (P w).card) →
      (∀ w z, w ≠ z → Disjoint (P w) (P z)) →
      (∀ w z, w ≠ z → ∀ a ∈ P w,
        ((neighbours (polarity G (decide (H.Adj w z))) (P z) a).card : ℝ) ≤ q) →
      t^n ≤ (copiesInParts H G P).card := by
  intro n
  induction n with
  | zero =>
    intro W _ _ hn H P hsize hdis hbad
    have : IsEmpty W := Fintype.card_eq_zero_iff.mp hn
    let f : W → V := fun w ↦ isEmptyElim w
    have hf : f ∈ copiesInParts H G P := by
      apply mem_copiesInParts.mpr
      exact ⟨⟨fun w ↦ isEmptyElim w, fun w ↦ isEmptyElim w⟩, fun w ↦ isEmptyElim w⟩
    rw [pow_zero, ← Nat.cast_one, Nat.cast_le]
    exact Finset.card_pos.mpr ⟨f,hf⟩
  | succ n ih =>
    intro W _ _ hn H P hsize hdis hbad
    have hW : Nonempty W := Fintype.card_pos_iff.mp (by omega)
    let g := Classical.choice hW
    let W' := ({w | w ≠ g} : Set W)
    have hcardW : Fintype.card W' = n := by rw [card_delete, hn]; omega
    have hsum : (∑ a ∈ P g, (copiesInParts (H.induce W') G
      (fun w ↦ goodFor H G g w a (P w))).card : ℕ) ≤ (copiesInParts H G P).card :=
      copies_count_sum (fun w hw ↦ hdis g w hw.symm)
    have hlower (a : V) (ha : a ∈ P g) : t^n ≤ (copiesInParts (H.induce W') G
        (fun w ↦ goodFor H G g w a (P w))).card := by
      apply ih W' hcardW (H.induce W') (fun w ↦ goodFor H G g w a (P w))
      · intro w
        have hwg : (w.val : W) ≠ g := w.2
        have hb := hbad g w hwg.symm a ha
        have hd : ∀ b ∈ P w, a ≠ b := by
          intro b hb e
          subst b
          exact Finset.disjoint_left.mp (hdis g w hwg.symm) ha hb
        have ht0 := goodFor_removes hd hb
        have hle := hsize w
        cases n with
        | zero =>
          letI : IsEmpty W' := Fintype.card_eq_zero_iff.mp hcardW
          exact isEmptyElim w
        | succ n => push_cast at hle ⊢; nlinarith only [hq, ht0, hle]
      · intro w z hn
        have hn' : w.val ≠ z.val := fun e ↦ hn (Subtype.ext e)
        exact (hdis w z hn').mono (goodFor_subset ..) (goodFor_subset ..)
      · intro w z hn b hb
        have hn' : w.val ≠ z.val := fun e ↦ hn (Subtype.ext e)
        have hb' := hbad w z hn' b (mem_goodFor.mp hb).1
        refine le_trans ?_ hb'
        exact_mod_cast Finset.card_le_card (neighbours_mono _ (goodFor_subset ..) b)
    have h' : ∑ _a ∈ P g, t^n ≤ ∑ a ∈ P g, ((copiesInParts (H.induce W') G
      (fun w ↦ goodFor H G g w a (P w))).card : ℝ) := Finset.sum_le_sum hlower
    have h'' : (∑ a ∈ P g, ((copiesInParts (H.induce W') G
      (fun w ↦ goodFor H G g w a (P w))).card : ℝ)) ≤ (copiesInParts H G P).card := by
      exact_mod_cast hsum
    have hg := hsize g
    simp only [Finset.sum_const, nsmul_eq_mul] at h'
    rw [pow_succ, mul_comm (t^n) t]
    have hgle : t ≤ (P g).card :=
      (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hq)).trans hg
    exact (mul_le_mul_of_nonneg_right hgle
      (pow_nonneg ht n)).trans (by linarith only [h', h''])

end OMA.BNSS

namespace OMA.BNSS

open Finset SimpleGraph Filter Real
open scoped BigOperators Classical

variable {V W : Type*} [DecidableEq V] [Fintype W] [DecidableEq W]

/-- A partial blowup whose equal-sized parts have at most q incorrectly coloured
neighbours per vertex in each other part. The bound q is absolute. -/
def ApproxParts (H : SimpleGraph W) (G : SimpleGraph V) (S : Finset V)
    (J : Finset W) (P : W → Finset V) (t : ℕ) (q : ℝ) : Prop :=
  (∀ j ∈ J, P j ⊆ S ∧ (P j).card = t) ∧
  (∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (P i) (P j)) ∧
  (∀ i ∈ J, ∀ j ∈ J, i ≠ j → ∀ a ∈ P i,
    ((neighbours (polarity G (decide (H.Adj i j))) (P j) a).card : ℝ) ≤ q)

theorem max_approx_parts {V W : Type*} [Fintype W]
    (H : SimpleGraph W) (G : SimpleGraph V) (S : Finset V)
    (t : ℕ → ℕ) (q : ℝ) :
    ∃ J P, ApproxParts H G S J P (t J.card) q ∧
      ∀ J' P', ApproxParts H G S J' P' (t J'.card) q → J'.card ≤ J.card := by
  classical
  let valid := (univ : Finset (Finset W)).filter (fun J ↦
    ∃ P, ApproxParts H G S J P (t J.card) q)
  have hne : valid.Nonempty := ⟨∅, mem_filter.mpr ⟨mem_univ _, fun _ ↦ ∅, by simp [ApproxParts]⟩⟩
  obtain ⟨J, hJ, hMax⟩ := Finset.exists_max_image valid Finset.card hne
  obtain ⟨P, hP⟩ := (Finset.mem_filter.mp hJ).2
  exact ⟨J, P, hP, fun J' P' h' ↦ hMax J' (mem_filter.mpr ⟨mem_univ _, ⟨P', h'⟩⟩)⟩

theorem goodFor_eq_neighbours {H : SimpleGraph W} {G : SimpleGraph V} {g w : W}
    {S : Finset V} {a : V} (hn : a ∉ S) :
    goodFor H G g w a S = neighbours (polarity G (!(decide (H.Adj g w)))) S a := by
  classical
  ext b
  rw [mem_goodFor, mem_neighbours]
  apply and_congr_right
  intro hb
  have hne : a ≠ b := fun h ↦ hn (h.symm ▸ hb)
  by_cases h : H.Adj g w <;> simp [h, polarity, SimpleGraph.compl_adj, hne]

theorem select_compatible_pool {H : SimpleGraph W} {G : SimpleGraph V} {S : Finset V}
    {J : Finset W} {P : W → Finset V} {t : ℕ} {q x : ℝ}
    (hP : ApproxParts H G S J P t q) (hJac : J.card < Fintype.card W) (w : W)
    (hwidth : (J.card : ℝ) * t ≤ (S.card : ℝ) / (2*Fintype.card W)) :
    (∃ j ∈ J, ∃ B ⊆ S, Disjoint (P j) B ∧
      (S.card : ℝ) / (2*Fintype.card W) ≤ B.card ∧
      SparseTo (polarity G (!(decide (H.Adj w j)))) x B (P j)) ∨
    (∃ Z ⊆ S, (S.card : ℝ) / 2 ≤ Z.card ∧
      (∀ j ∈ J, Disjoint (P j) Z) ∧
      ∀ j ∈ J, ∀ a ∈ Z, x * (P j).card ≤ ((goodFor H G w j a (P j)).card : ℝ)) := by
  classical
  let L := J.biUnion P
  let M := fun j ↦ (S \ L).filter (fun a ↦ ((goodFor H G w j a (P j)).card : ℝ) ≤ x * (P j).card)
  let K : ℝ := 2 * Fintype.card W
  have hK : 0 < K := by
    have hp : 0 < Fintype.card W := by omega
    have hp' : (0 : ℝ) < Fintype.card W := by exact_mod_cast hp
    dsimp [K]
    positivity
  have hMS (j : W) : M j ⊆ S := (Finset.filter_subset _ _).trans sdiff_subset
  have hMdis (j : W) (hj : j ∈ J) : Disjoint (P j) (M j) := by
    apply Finset.disjoint_left.mpr
    intro a ha hMa
    have h := (mem_sdiff.mp (mem_filter.mp hMa).1).2
    exact h (Finset.mem_biUnion.mpr ⟨j, hj, ha⟩)
  by_cases one : ∃ j ∈ J, (S.card : ℝ)/K ≤ (M j).card
  · obtain ⟨j,hj,hMj⟩ := one
    refine Or.inl ⟨j,hj,M j,hMS j,hMdis j hj,hMj, ?_⟩
    intro a ha
    have hn : a ∉ P j := fun he ↦ Finset.disjoint_left.mp (hMdis j hj) he ha
    rw [← goodFor_eq_neighbours hn]
    exact (mem_filter.mp ha).2
  apply Or.inr
  push Not at one
  let Z := S \ (L ∪ J.biUnion M)
  have hLsize : (L.card : ℝ) ≤ (J.card : ℝ) * t := by
    have hi := Finset.card_biUnion_le (s := J) (t := P)
    have hsum : ∑ j ∈ J, (P j).card = J.card * t := by
      calc
        _ = ∑ _j ∈ J, t := Finset.sum_congr rfl fun j hj ↦ (hP.1 j hj).2
        _ = _ := by simp
    exact_mod_cast hi.trans_eq hsum
  have hMsize : ((J.biUnion M).card : ℝ) ≤ J.card * ((S.card : ℝ) / K) := by
    calc
      ((J.biUnion M).card : ℝ) ≤ ∑ j ∈ J, ((M j).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ J, (S.card : ℝ) / K := Finset.sum_le_sum fun j hj ↦ (one j hj).le
      _ = _ := by simp
  have hZsize : (S.card : ℝ) / 2 ≤ Z.card := by
    have hs := Finset.card_le_card_sdiff_add_card (s := S) (t := L ∪ J.biUnion M)
    have hs' : (S.card : ℝ) ≤ Z.card + (L ∪ J.biUnion M).card := by exact_mod_cast hs
    have hcnt : ((L ∪ J.biUnion M).card : ℝ) ≤ L.card + (J.biUnion M).card := by
      exact_mod_cast Finset.card_union_le _ _
    have hJR : (J.card : ℝ) + 1 ≤ Fintype.card W := by exact_mod_cast hJac
    have hhalf : (J.card : ℝ) * ((S.card : ℝ) / K) + (S.card : ℝ) / K ≤ (S.card : ℝ) / 2 := by
      calc
        _ = ((J.card : ℝ) + 1) * ((S.card : ℝ) / K) := by ring
        _ ≤ (Fintype.card W : ℝ) * ((S.card : ℝ) / K) :=
          mul_le_mul_of_nonneg_right hJR (by positivity)
        _ = _ := by
          have hw : (Fintype.card W : ℝ) ≠ 0 := by
            intro eq
            dsimp only [K] at hK
            rw [eq,mul_zero] at hK
            exact (lt_irrefl _ hK)
          dsimp [K]
          field_simp
    change (J.card : ℝ) * t ≤ (S.card : ℝ) / K at hwidth
    linarith only [hs',hcnt,hhalf,hwidth,hLsize,hMsize]
  refine ⟨Z,Finset.sdiff_subset,hZsize, ?_, ?_⟩
  · intro j hj
    apply Finset.disjoint_left.mpr
    intro a ha haZ
    exact (mem_sdiff.mp haZ).2 (mem_union.mpr (Or.inl (mem_biUnion.mpr ⟨j,hj,ha⟩)))
  · intro j hj a ha
    have hna : a ∉ M j := fun hc ↦
      (mem_sdiff.mp ha).2 (mem_union.mpr (Or.inr (mem_biUnion.mpr ⟨j,hj,hc⟩)))
    have hSnu : a ∈ S \ L := mem_sdiff.mpr ⟨(mem_sdiff.mp ha).1,
      fun hl ↦ (mem_sdiff.mp ha).2 (mem_union.mpr (Or.inl hl))⟩
    exact le_of_lt (lt_of_not_ge fun hh ↦ hna (mem_filter.mpr ⟨hSnu,hh⟩))

end OMA.BNSS

namespace OMA.BNSS

open Finset SimpleGraph Filter Real
open scoped BigOperators Classical

variable {V W : Type*} [DecidableEq V] [Fintype W] [DecidableEq W]

theorem symmetric_trim {G : SimpleGraph V} {B C : Finset V} {t : ℕ} {q : ℝ}
    (hq : 0 ≤ q) (hb : B.card = t) (hc : C.card = 2*t)
    (h : ∀ b ∈ B, ((neighbours G C b).card : ℝ) ≤ q) :
    ∃ C' ⊆ C, C'.card = t ∧
      (∀ b ∈ B, ((neighbours G C' b).card : ℝ) ≤ q) ∧
      (∀ c ∈ C', ((neighbours G B c).card : ℝ) ≤ q) := by
  have hedges : crossEdges G C B ≤ (q / 2) * C.card := by
    unfold crossEdges
    refine (Finset.sum_le_sum h).trans_eq ?_
    rw [Finset.sum_const, nsmul_eq_mul, hb, hc, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [crossEdges_symm] at hedges
  obtain ⟨D, hD, hDc, hDq⟩ := markov_half _ (fun _ _ ↦ Nat.cast_nonneg _) (by positivity) hedges
  have ht : t ≤ D.card := by
    have h' : (C.card : ℝ) = 2*t := by exact_mod_cast hc
    have hh : (t : ℝ) ≤ D.card := by linarith only [h',hDc]
    exact_mod_cast hh
  obtain ⟨C', hC'D, hC'⟩ := Finset.exists_subset_card_eq ht
  have hC'C := hC'D.trans hD
  refine ⟨C', hC'C, hC', ?_, ?_⟩
  · intro b hb'
    have hMono : ((neighbours G C' b).card : ℝ) ≤ (neighbours G C b).card := by
      exact_mod_cast Finset.card_le_card (neighbours_mono G hC'C b)
    exact hMono.trans (h b hb')
  · intro v hv
    have h' := hDq v (hC'D hv)
    linarith

theorem extend_approx_parts {V W : Type*} [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V} {S : Finset V}
    {J : Finset W} {P C : W → Finset V} {t t' : ℕ} {q : ℝ} (hq : 0 ≤ q)
    (hP : ApproxParts H G S J P t q) {w : W} (hw : w ∉ J)
    {B : Finset V} (hBS : B ⊆ S) (hB : B.card = t')
    (hdis : ∀ j ∈ J, Disjoint (P j) B)
    (hC : ∀ j ∈ J, C j ⊆ P j ∧ (C j).card = 2*t' ∧
      ∀ b ∈ B, ((neighbours (polarity G (decide (H.Adj w j))) (C j) b).card : ℝ) ≤ q) :
    ∃ P', ApproxParts H G S (insert w J) P' t' q := by
  classical
  have hs (j : W) (hj : j ∈ J) :
      ∃ A ⊆ P j, A.card = t' ∧
      (∀ b ∈ B, ((neighbours (polarity G (decide (H.Adj w j))) A b).card : ℝ) ≤ q) ∧
      (∀ a ∈ A, ((neighbours (polarity G (decide (H.Adj j w))) B a).card : ℝ) ≤ q) := by
    obtain ⟨hCjP, hc, hq1⟩ := hC j hj
    obtain ⟨A, hA, hAc, hAB, hBA⟩ := symmetric_trim hq hB hc hq1
    exact ⟨A, hA.trans hCjP, hAc, hAB, by simpa only [H.adj_comm j w] using hBA⟩
  let P₀ := fun j ↦ if hj : j ∈ J then Classical.choose (hs j hj) else ∅
  have hP₀ (j : W) (hj : j ∈ J) :
      P₀ j ⊆ P j ∧ (P₀ j).card = t' ∧
      (∀ b ∈ B, ((neighbours (polarity G (decide (H.Adj w j))) (P₀ j) b).card : ℝ) ≤ q) ∧
      (∀ a ∈ P₀ j, ((neighbours (polarity G (decide (H.Adj j w))) B a).card : ℝ) ≤ q) := by
    simpa only [P₀, dif_pos hj] using Classical.choose_spec (hs j hj)
  let P' := Function.update P₀ w B
  have hw' : P' w = B := by simp [P']
  have hj' (j : W) (hj : j ∈ J) : P' j = P₀ j := by
    simp [P', Function.update_of_ne (show j ≠ w from fun e ↦ hw (e ▸ hj))]
  refine ⟨P', ?_, ?_, ?_⟩
  · intro j hj
    rcases Finset.mem_insert.mp hj with hjw | hj
    · rw [hjw,hw']
      exact ⟨hBS,hB⟩
    · rw [hj' j hj]
      exact ⟨(hP₀ j hj).1.trans (hP.1 j hj).1, (hP₀ j hj).2.1⟩
  · intro i hi j hj hn
    rcases Finset.mem_insert.mp hi with hiw | hi <;> rcases Finset.mem_insert.mp hj with hjw | hj
    · exact False.elim (hn (hiw.trans hjw.symm))
    · rw [hiw,hw', hj' j hj]
      exact ((hdis j hj).mono_left (hP₀ j hj).1).symm
    · rw [hjw,hw', hj' i hi]
      exact (hdis i hi).mono_left (hP₀ i hi).1
    · rw [hj' i hi, hj' j hj]
      exact (hP.2.1 i hi j hj hn).mono (hP₀ i hi).1 (hP₀ j hj).1
  · intro i hi j hj hn a ha
    rcases Finset.mem_insert.mp hi with hiw | hi <;> rcases Finset.mem_insert.mp hj with hjw | hj
    · exact False.elim (hn (hiw.trans hjw.symm))
    · rw [hiw,hw'] at ha
      rw [hiw]
      rw [hj' j hj]
      exact (hP₀ j hj).2.2.1 a ha
    · rw [hj' i hi] at ha
      rw [hjw,hw']
      exact (hP₀ i hi).2.2.2 a ha
    · rw [hj' i hi] at ha
      rw [hj' j hj]
      have hMono : ((neighbours (polarity G (decide (H.Adj i j))) (P₀ j) a).card : ℝ) ≤
          (neighbours (polarity G (decide (H.Adj i j))) (P j) a).card := by
        exact_mod_cast Finset.card_le_card (neighbours_mono _ (hP₀ j hj).1 a)
      exact hMono.trans (hP.2.2 i hi j hj hn a ((hP₀ i hi).1 ha))

theorem parallel_shrink {V W : Type*} {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (J : Finset W) (Z : Finset V)
    (Good : W → Finset V → Finset V → Prop)
    (hmono : ∀ j C Y Y', Y' ⊆ Y → Good j C Y → Good j C Y')
    (hstep : ∀ j ∈ J, ∀ Y ⊆ Z, r^J.card*Z.card ≤ (Y.card : ℝ) →
      ∃ C, ∃ Y' ⊆ Y, r*Y.card ≤ (Y'.card : ℝ) ∧ Good j C Y') :
    ∃ C : W → Finset V, ∃ Y ⊆ Z, r^J.card*Z.card ≤ (Y.card : ℝ) ∧
      ∀ j ∈ J, Good j (C j) Y := by
  classical
  have aux : ∀ J' ⊆ J, ∀ Y ⊆ Z, r^(J.card-J'.card)*Z.card ≤ (Y.card : ℝ) →
      ∃ C : W → Finset V, ∃ Y' ⊆ Y, r^J.card*Z.card ≤ (Y'.card : ℝ) ∧
        ∀ j ∈ J', Good j (C j) Y' := by
    intro J'
    induction J' using Finset.induction_on with
    | empty =>
      intro _ Y _ hY
      exact ⟨fun _ ↦ ∅, Y, Subset.rfl, by simpa using hY, by simp⟩
    | @insert j J' hj ih =>
      intro hJ Y hY hYsize
      have hsub : J' ⊆ J := (Finset.subset_insert _ _).trans hJ
      have hin : j ∈ J := hJ (Finset.mem_insert_self _ _)
      have hsmall : r^J.card*Z.card ≤ (Y.card : ℝ) :=
        (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hr hr1 (Nat.sub_le ..))
          (Nat.cast_nonneg _)).trans hYsize
      obtain ⟨Cj,X,hXY,hX,hXj⟩ := hstep j hin Y hY hsmall
      have hJc : J'.card < J.card := by
        have hi' := Finset.card_le_card hJ
        rw [Finset.card_insert_of_notMem hj] at hi'
        exact hi'
      have ht : J.card-J'.card = (J.card-(insert j J').card)+1 := by
        rw [Finset.card_insert_of_notMem hj]
        omega
      have hXsize : r^(J.card-J'.card)*Z.card ≤ (X.card : ℝ) := by
        rw [ht,pow_succ',mul_assoc]
        exact (mul_le_mul_of_nonneg_left hYsize hr).trans hX
      obtain ⟨C,Y',hY'X,hY's,hY'good⟩ := ih hsub X (hXY.trans hY) hXsize
      refine ⟨Function.update C j Cj,Y',hY'X.trans hXY,hY's, fun w hw ↦ ?_⟩
      rcases Finset.mem_insert.mp hw with rfl | hw
      · simpa using hmono _ _ X Y' hY'X hXj
      · have hn : w ≠ j := fun e ↦ hj (e ▸ hw)
        simpa [Function.update_of_ne hn] using hY'good w hw
  exact aux J Subset.rfl Z Subset.rfl (by simp)

end OMA.BNSS

namespace OMA.BNSS

open Finset SimpleGraph Filter Real
open scoped BigOperators Classical

def scaleExponent (a h : ℕ) : ℕ → ℕ
  | 0 => 0
  | s + 1 => a + 2*h + 1 + (h+1)*scaleExponent a h s

theorem scale_mono (a h : ℕ) : Monotone (scaleExponent a h) := by
  apply monotone_nat_of_le_succ
  intro s
  simp only [scaleExponent, Nat.add_mul, Nat.one_mul]
  omega

theorem scale_step_lt (a h s : ℕ) : scaleExponent a h s < scaleExponent a h (s+1) := by
  simp only [scaleExponent, Nat.add_mul, Nat.one_mul]
  omega

theorem one_le_scale {a h s : ℕ} (hs : 0 < s) : 1 ≤ scaleExponent a h s := by
  cases s with
  | zero => omega
  | succ s =>
    simp only [scaleExponent]
    omega

theorem scale_room {a h k : ℕ} (hh : 0 < h) (hk : k < h) :
    k * (scaleExponent a h (h-k) - scaleExponent a h (h-(k+1))) +
      scaleExponent a h (h-(k+1)) + 1 ≤ scaleExponent a h h := by
  let r := scaleExponent a h (h-k)
  let r' := scaleExponent a h (h-(k+1))
  have hr : r' ≤ r := scale_mono a h (by omega)
  change k*(r-r')+r'+1 ≤ scaleExponent a h h
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · have hlt : r' < scaleExponent a h h := by
      have hx : h - (0+1) + 1 = h := by omega
      simpa only [hx] using scale_step_lt a h (h-(0+1))
    omega
  · have hroom := scale_mono a h (show h-k+1 ≤ h by omega)
    have hright : (h+1)*r+1 ≤ scaleExponent a h (h-k+1) := by
      change (h+1)*r+1 ≤ a+2*h+1+(h+1)*r
      omega
    have hn : k*(r-r')+r' ≤ (h+1)*r := by
      have ha := Nat.mul_le_mul_right r (show k ≤ h by omega)
      have hb := Nat.mul_le_mul_left k (show r-r' ≤ r by omega)
      rw [Nat.add_mul, Nat.one_mul]
      omega
    exact (Nat.add_le_add_right hn 1).trans (hright.trans hroom)

theorem scale_gap {a h k : ℕ} (hk : k < h) :
    scaleExponent a h (h-k) =
      scaleExponent a h (h-(k+1)) + (a + (scaleExponent a h (h-(k+1))+2)*h) + 1 := by
  nth_rw 1 [show h-k = h-(k+1)+1 by omega]
  simp only [scaleExponent, Nat.add_mul, Nat.one_mul]
  ring

theorem reciprocal_width {z : ℕ} (hz : 0 < z) (T r : ℕ) :
    ((z : ℝ)⁻¹)^r * ((z^r*T : ℕ) : ℝ) = (T : ℝ) := by
  have hz' : (z : ℝ) ≠ 0 := by exact_mod_cast hz.ne'
  push_cast
  rw [← mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero r hz'), one_mul]

theorem small_graph_split {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (hS : 2 ≤ S.card) {x : ℝ} (hx : 0 ≤ x) {h : ℕ} (hh : 2 ≤ h) :
    ∃ (sign : Bool) (A B : Finset V), A ⊆ S ∧ B ⊆ S ∧ Disjoint A B ∧ (1 : ℝ) ≤ A.card ∧
      (S.card : ℝ) / (2*h) ≤ B.card ∧ SparseTo (polarity G sign) x B A := by
  classical
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  let T := S.erase a
  let A : Finset V := {a}
  let B₀ := T.filter fun b ↦ ¬ G.Adj b a
  let B₁ := T.filter fun b ↦ G.Adj b a
  have htc : T.card + 1 = S.card := Finset.card_erase_add_one ha
  have hsum : B₀.card + B₁.card = T.card := by
    rw [add_comm]
    exact Finset.card_filter_add_card_filter_not _
  have htruth : (S.card : ℝ)/(2*h) ≤ (T.card : ℝ)/2 := by
    have htr : (T.card : ℝ) + 1 = S.card := by exact_mod_cast htc
    have hS' : (2 : ℝ) ≤ S.card := by exact_mod_cast hS
    have hhr : (2 : ℝ) ≤ h := by exact_mod_cast hh
    have hh' : (0 : ℝ) < 2*h := by positivity
    apply (div_le_iff₀ hh').mpr
    nlinarith only [hS',htr,mul_le_mul_of_nonneg_right hhr (Nat.cast_nonneg (α := ℝ) T.card)]
  have good {b : Bool} {B : Finset V} (hb : B ⊆ T) (hc : (T.card : ℝ)/2 ≤ B.card)
      (hB : ∀ v ∈ B, ¬ (polarity G b).Adj v a) :
      ∃ (sign : Bool) (A B : Finset V), A ⊆ S ∧ B ⊆ S ∧ Disjoint A B ∧ (1 : ℝ) ≤ A.card ∧
        (S.card : ℝ) / (2*h) ≤ B.card ∧ SparseTo (polarity G sign) x B A := by
    refine ⟨b,A,B,singleton_subset_iff.mpr ha,hb.trans (erase_subset _ _),?_,
      by simp [A],htruth.trans hc,?_⟩
    · change Disjoint ({a} : Finset V) B
      rw [Finset.disjoint_singleton_left]
      exact fun hc ↦ (Finset.mem_erase.mp (hb hc)).1 rfl
    · intro v hv
      have hn : neighbours (polarity G b) A v = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro w hw
        obtain ⟨hwa, hwv⟩ := mem_neighbours.mp hw
        simp only [A, Finset.mem_singleton] at hwa
        exact hB v hv (hwa ▸ hwv)
      simpa [hn, A] using hx
  by_cases h₀ : (T.card : ℝ)/2 ≤ B₀.card
  · apply good (b := false) (filter_subset _ _) h₀
    exact fun v hv ↦ (mem_filter.mp hv).2
  · have h' : (B₀.card : ℝ) + B₁.card = T.card := by exact_mod_cast hsum
    have h₁ : (T.card : ℝ)/2 ≤ B₁.card := by linarith
    apply good (b := true) (filter_subset _ _) h₁
    intro v hv hbad
    exact hbad.2 (mem_filter.mp hv).2

end OMA.BNSS

namespace OMA.BNSS

open Finset SimpleGraph Filter Real
open scoped BigOperators Classical

variable {V W : Type*} [DecidableEq V] [Fintype W] [DecidableEq W]

theorem copies_polarity (H : SimpleGraph W) (G : SimpleGraph V) (b : Bool) (S : Finset V) :
    copies (polarity H b) (polarity G b) S = copies H G S := by
  cases b <;> simp [polarity, copies_compl]

theorem copies_drop_polarity (H : SimpleGraph W) (G : SimpleGraph V) (b : Bool) (g : W)
    (S : Finset V) :
    copies ((polarity H b).induce ({v | v ≠ g} : Set W)) (polarity G b) S =
      copies (H.induce ({v | v ≠ g} : Set W)) G S := by
  cases b with
  | false => rfl
  | true =>
    have eq : Hᶜ.induce ({v | v ≠ g} : Set W) = (H.induce ({v | v ≠ g} : Set W))ᶜ := by
      ext a b
      simp [SimpleGraph.compl_adj, Subtype.ext_iff]
    change copies (Hᶜ.induce _) Gᶜ S = _
    rw [eq, copies_compl]

theorem goodFor_eq_nonneighbours {H : SimpleGraph W} {G : SimpleGraph V} {w j : W}
    {A : Finset V} {v : V} (h : v ∉ A) :
    goodFor H G w j v A = nonneighbours (polarity G (decide (H.Adj w j))) A v := by
  classical
  ext a
  rw [mem_goodFor, mem_nonneighbours]
  apply and_congr_right
  intro ha
  have hne : v ≠ a := fun e ↦ h (e.symm ▸ ha)
  by_cases hpair : H.Adj w j <;> simp [hpair, polarity, SimpleGraph.compl_adj, hne]

set_option maxHeartbeats 2000000 in
/-- A maximal partial blowup either supplies the required sparse pair or can
be made larger. The reciprocal integer parameter keeps the widths integral. -/
theorem trichotomy_integer (H : SimpleGraph W) (g : W) (a : ℕ)
    (hh : 2 ≤ Fintype.card W) :
    let h := Fintype.card W
    let R := scaleExponent a h h
    let β := R + 3
    let γ := 2*R + β*h
    ∀ {V : Type} [DecidableEq V] (G : SimpleGraph V) (S : Finset V) (z : ℕ),
      8*h ≤ z → 2 ≤ S.card →
      let x := ((z : ℝ)⁻¹)
      (∃ A ⊆ S, x^β * S.card ≤ (A.card : ℝ) ∧
        ((copies (H.induce ({v | v ≠ g} : Set W)) G A).card : ℝ) <
          x^a * (A.card : ℝ) ^ (h - 1)) ∨
      x^γ * (S.card : ℝ)^h ≤ (copies H G S).card ∨
      (∃ (sign : Bool) (A B : Finset V), A ⊆ S ∧ B ⊆ S ∧ Disjoint A B ∧
        x^β * S.card ≤ (A.card : ℝ) ∧ (S.card : ℝ) / (2*h) ≤ B.card ∧
          SparseTo (polarity G sign) x B A) := by
  classical
  intro h R β γ V _ G S z hz hS x
  have hhr : (2 : ℝ) ≤ h := by exact_mod_cast hh
  have hhp : 0 < (h : ℝ) := by linarith
  have hzr : (8 : ℝ) * h ≤ z := by exact_mod_cast hz
  have hzp : 0 < (z : ℝ) := by linarith
  have hx : 0 < x := inv_pos.mpr hzp
  have hx8 : x ≤ (8*(h:ℝ))⁻¹ := inv_anti₀ (by positivity) hzr
  have hx8' : x * (8*(h:ℝ)) ≤ 1 := by
    rw [← one_div] at hx8
    exact (le_div_iff₀ (by positivity)).mp hx8
  have hx2 : x ≤ 1/2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    nlinarith only [hx8', mul_le_mul_of_nonneg_left hhr hx.le]
  have hx1 : x ≤ 1 := by linarith
  have hN : 0 < (S.card : ℝ) := by exact_mod_cast (show 0 < S.card by omega)
  by_cases small : x^β * (S.card : ℝ) ≤ 1
  · obtain ⟨b,A,B,hA,hB,hAB,hAc,hBc,hsp⟩ := small_graph_split G S hS hx.le hh
    exact Or.inr (Or.inr ⟨b,A,B,hA,hB,hAB,small.trans hAc,hBc,hsp⟩)
  by_cases lower : ∃ A ⊆ S, x^β * S.card ≤ (A.card : ℝ) ∧
      ((copies (H.induce ({v | v ≠ g} : Set W)) G A).card : ℝ) <
        x^a * (A.card : ℝ)^(h-1)
  · exact Or.inl lower
  apply Or.inr
  by_cases many : x^γ * (S.card : ℝ)^h ≤ (copies H G S).card
  · exact Or.inl many
  apply Or.inr
  let T : ℕ := ⌈x^β * S.card⌉₊
  let r := fun k ↦ scaleExponent a h (h-k)
  let t := fun k ↦ z ^ r k * T
  let q : ℝ := T / h
  have hTlo : x^β * S.card ≤ (T : ℝ) := Nat.le_ceil _
  have hTpos : 0 < (T : ℝ) := (show 0 < x^β * (S.card : ℝ) by positivity).trans_le hTlo
  have hThi : (T : ℝ) ≤ x^(R+2) * S.card := by
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ x^β * (S.card : ℝ) by positivity)
    change (T : ℝ) < x^β * S.card + 1 at hceil
    have hr : x^β = x^(R+2)*x := by dsimp [β]; rw [← pow_succ]
    nlinarith only [hceil, lt_of_not_ge small,
      mul_le_mul_of_nonneg_right hx2 (show 0 ≤ x^(R+2)*(S.card : ℝ) by positivity),
      congrArg (fun v : ℝ ↦ v*S.card) hr]
  have hrt (k : ℕ) : x^r k * (t k : ℝ) = T :=
    reciprocal_width (by exact_mod_cast hzp) T (r k)
  have hrr (k : ℕ) : r k ≤ R := scale_mono a h (Nat.sub_le ..)
  have htr (k : ℕ) : x^β * S.card ≤ (t k : ℝ) := by
    have hh' := mul_le_mul_of_nonneg_right (pow_le_one₀ hx.le hx1 : x^r k ≤ 1)
      (Nat.cast_nonneg (α := ℝ) (t k))
    nlinarith only [hTlo, hrt k, hh']
  obtain ⟨J,P,hP,hmax⟩ := max_approx_parts H G S t q
  let k := J.card
  have hkh : k ≤ h := by simpa [h,k] using Finset.card_le_univ J
  have hproper : k < h := by
    by_contra! heq
    have keq : k = h := by omega
    have he : J = univ := J.eq_univ_of_card (by simpa [h,k] using keq)
    have htk : t k = T := by simp [t,r,keq,scaleExponent]
    have hq0 : 0 ≤ q := by dsimp [q]; positivity
    have hstr := copies_of_part_bounds G (t := q) (q := q) hq0 hq0 h W rfl H P
    have hb : ∀ w : W, q + ((h-1 : ℕ) : ℝ)*q ≤ (P w).card := by
      intro w
      have hm := (hP.1 w (by simp [he])).2
      change (P w).card = t k at hm
      rw [hm,htk]
      have hn : ((h-1 : ℕ) : ℝ) + 1 = h := by
        exact_mod_cast (show h-1+1=h by omega)
      have hq : q * h = (T : ℝ) := by dsimp [q]; field_simp
      nlinarith only [congrArg (fun v : ℝ ↦ v*q) hn,hq]
    have hcov : q^h ≤ (copiesInParts H G P).card :=
      hstr hb (fun u v huv ↦ hP.2.1 u (by simp [he]) v (by simp [he]) huv)
        (fun u v huv ↦ hP.2.2 u (by simp [he]) v (by simp [he]) huv)
    have hcard : ((copiesInParts H G P).card : ℝ) ≤ (copies H G S).card := by
      exact_mod_cast Finset.card_le_card (copiesInParts_subset (fun w ↦ (hP.1 w (by simp [he])).1))
    have hdq : x^(β+1) * S.card ≤ q := by
      dsimp [q]
      apply (le_div_iff₀ hhp).mpr
      have hxH : x*(h:ℝ) ≤ 1 := by linarith only [hx8', show 0 ≤ x*(h:ℝ) by positivity]
      rw [pow_succ]
      nlinarith only [hTlo, mul_le_mul_of_nonneg_right hxH
        (show 0 ≤ x^β * (S.card : ℝ) by positivity)]
    have hγ : (β+1)*h ≤ γ := by
      have hR : h ≤ R := by
        have hge := scale_mono a h (show 1 ≤ h by omega)
        simp only [scaleExponent] at hge
        omega
      dsimp [γ]
      rw [Nat.add_mul, one_mul]
      omega
    apply many
    refine (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hx.le hx1 hγ) (by positivity)).trans ?_
    rw [pow_mul, ← mul_pow]
    exact (pow_le_pow_left₀ (by positivity) hdq _).trans (hcov.trans hcard)
  have hPwidth : (J.card : ℝ) * (t J.card : ℝ) ≤ (S.card : ℝ)/(2*h) := by
    have ht2 : (t k : ℝ) ≤ x^2 * S.card := by
      apply (mul_le_mul_iff_of_pos_left (pow_pos hx (r k))).mp
      rw [hrt, ← mul_assoc, ← pow_add]
      exact hThi.trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one hx.le hx1 (Nat.add_le_add_right (hrr k) 2)) (Nat.cast_nonneg _))
    have hk' : (k : ℝ) ≤ h := by exact_mod_cast hkh
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2*h)).mpr
    have hg : x*(h:ℝ) ≤ 1/8 := by linarith only [hx8']
    have hgg : x^2*(h:ℝ)^2 ≤ (1/8:ℝ)^2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hg _
    have ha := mul_le_mul_of_nonneg_left ht2 (show 0 ≤ (k : ℝ) by positivity)
    have hb := mul_le_mul_of_nonneg_right hk' (show 0 ≤ x^2*(S.card : ℝ) by positivity)
    change (k : ℝ) * t k * (2*h) ≤ S.card
    have hc := mul_le_mul_of_nonneg_right (ha.trans hb) (show 0 ≤ (2*(h:ℝ)) by positivity)
    nlinarith only [hc, mul_le_mul_of_nonneg_right hgg hN.le, hN.le]
  obtain ⟨w, hw⟩ : ∃ w, w ∉ J := by
    by_contra! he
    have hJu : J = univ := Finset.eq_univ_of_forall he
    have hh' : k = h := by simp [k,h,hJu]
    omega
  rcases select_compatible_pool hP hproper w hPwidth with
    ⟨j,hj,B,hBS,hAB,hBc,hsp⟩ | ⟨Z,hZS,hZsize,hZj,hgood⟩
  · exact ⟨_,P j,B,(hP.1 j hj).1,hBS,hAB,by simpa [(hP.1 j hj).2] using htr k,hBc,hsp⟩
  exfalso
  let r₀ := r k
  let r₁ := r (k+1)
  let E := a+(r₁+2)*h
  let s := x^(E+1)
  have hgap : r₀ = r₁+E+1 := scale_gap hproper
  have hroom : k*(E+1)+r₁+1 ≤ R := by
    have hr := scale_room (a := a) (h := h) (k := k) (by omega) hproper
    change k*(r₀-r₁)+r₁+1 ≤ R at hr
    rwa [hgap, show r₁+E+1-r₁ = E+1 by omega] at hr
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hs1 : s ≤ 1 := pow_le_one₀ hx.le hx1
  have hZbound : x^(k*(E+1)+1)*S.card ≤ s^k*Z.card := by
    have heq : x^(k*(E+1)+1) = s^k*x := by
      rw [pow_succ, Nat.mul_comm k (E+1), pow_mul]
    rw [heq, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_right hx2 hN.le).trans (by linarith only [hZsize])) (by positivity)
  have htX : (t (k+1) : ℝ) ≤ s^k * Z.card := by
    apply (mul_le_mul_iff_of_pos_left (pow_pos hx r₁)).mp
    rw [show r₁ = r (k+1) by rfl, hrt]
    have hxexp : R+2 ≥ r₁+(k*(E+1)+1) := by omega
    refine hThi.trans ((mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hx.le hx1 hxexp) hN.le).trans ?_)
    rw [pow_add,mul_assoc]
    exact mul_le_mul_of_nonneg_left hZbound (by positivity)
  let Good := fun j (C Y : Finset V) ↦ C ⊆ P j ∧ C.card = 2*t (k+1) ∧
    ∀ y ∈ Y, ((neighbours (polarity G (decide (H.Adj w j))) C y).card : ℝ) ≤ q
  have hthin : ∀ j ∈ J, ∀ Y ⊆ Z, s^J.card*Z.card ≤ (Y.card : ℝ) →
      ∃ C, ∃ Y' ⊆ Y, s*Y.card ≤ (Y'.card : ℝ) ∧ Good j C Y' := by
    intro j hj Y hYZ hYsize
    let b := decide (H.Adj w j)
    let K := polarity H b
    let L := polarity G b
    have hPj := hP.1 j hj
    have hPjc : (P j).card = t k := hPj.2
    have hPjpos : 0 < (P j).card := by
      have h : (0 : ℝ) < (P j).card := by
        rw [hPjc]
        exact (show 0 < x^β * (S.card : ℝ) by positivity).trans_le (htr k)
      exact_mod_cast h
    have hbY : x^R*S.card ≤ (Y.card : ℝ) :=
      ((mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hx.le hx1
        (show k*(E+1)+1 ≤ R by omega)) hN.le).trans hZbound).trans hYsize
    have hYpos : 0 < Y.card := by
      exact_mod_cast ((show 0 < x^R * (S.card : ℝ) by positivity).trans_le hbY)
    have hdis : Disjoint Y (P j) := ((hZj j hj).mono_right hYZ).symm
    have hun : ∀ v ∈ Y, x * (P j).card ≤ ((nonneighbours L (P j) v).card : ℝ) := by
      intro v hv
      rw [← goodFor_eq_nonneighbours (H := H) (w := w) (j := j)
        (fun hc ↦ Finset.disjoint_left.mp hdis hv hc)]
      exact hgood j hj v (hYZ hv)
    rcases local_pair (H := K) (G := L) g (Finset.card_pos.mp hYpos) (Finset.card_pos.mp hPjpos)
        hdis hx hx2 a (r₁+1) hun with
      ⟨A,hA,hAc,hFew⟩ | hMany | ⟨D,hDY,A,hAP,hDc,hAc,hcut⟩
    · apply False.elim
      apply lower
      refine ⟨A,hA.trans hPj.1,?_,?_⟩
      · have hr₂ : 1 ≤ r₀ := one_le_scale (Nat.sub_pos_of_lt hproper)
        have hf : (T : ℝ) ≤ x * (P j).card := by
          rw [hPjc, ← hrt k]
          exact mul_le_mul_of_nonneg_right (by
            simpa using pow_le_pow_of_le_one hx.le hx1 hr₂) (Nat.cast_nonneg _)
        exact (hTlo.trans hf).trans hAc
      · simpa [K,L,copies_drop_polarity] using hFew
    · apply False.elim
      apply many
      have he : E ≤ R := by have h := hrr k; omega
      have hc : x^E * (Y.card : ℝ) * (P j).card^(h-1) ≤ (copies H G S).card := by
        have hp := special_subset (H := K) (G := L) (g := g) (hYZ.trans hZS) hPj.1
        have hh' : ((special K L g Y (P j)).card : ℝ) ≤ (copies K L S).card := by
          exact_mod_cast Finset.card_le_card hp
        dsimp only [K,L] at hh'
        rw [copies_polarity] at hh'
        exact hMany.trans hh'
      have hdiv : x^R * (x^R * S.card) * (x^β * S.card)^(h-1) ≤
          x^E * (Y.card : ℝ) * (P j).card^(h-1) := by
        have hex : x^R ≤ x^E := pow_le_pow_of_le_one hx.le hx1 he
        have hthird : x^β * S.card ≤ ((P j).card : ℝ) := by simpa only [hPjc] using htr k
        exact mul_le_mul
          (mul_le_mul hex hbY (by positivity) (by positivity))
          (pow_le_pow_left₀ (by positivity) hthird _) (by positivity) (by positivity)
      have hh1 : h = (h-1)+1 := by omega
      have ha : 2*R+β*(h-1) ≤ γ := by
        apply Nat.add_le_add_left
        exact Nat.mul_le_mul_left _ (Nat.sub_le ..)
      have hgoal := mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hx.le hx1 ha)
        (pow_nonneg hN.le h)
      refine hgoal.trans ?_
      have hexact : x^(2*R+β*(h-1)) * (S.card : ℝ)^h =
          x^R * (x^R * S.card) * (x^β * S.card)^(h-1) := by
        rw [pow_add, show x^(2*R) = x^R*x^R by rw [two_mul,pow_add],
          show x^(β*(h-1)) = (x^β)^(h-1) by rw [pow_mul], mul_pow,
          show (S.card : ℝ)^h = (S.card : ℝ)^(h-1) * S.card by rw [← pow_succ,← hh1]]
        ring
      rw [hexact]
      exact hdiv.trans hc
    · have hAmin : 2*t (k+1) ≤ A.card := by
        have heq : x^E*(P j).card*x = (t (k+1) : ℝ) := by
          rw [hPjc]
          have ha1 := hrt k
          have ha2 := hrt (k+1)
          change x^r₀*(t k : ℝ) = T at ha1
          change x^r₁*(t (k+1) : ℝ) = T at ha2
          apply mul_left_cancel₀ (pow_pos hx r₁).ne'
          rw [hgap, pow_succ,pow_add] at ha1
          nlinarith only [ha1,ha2]
        have ht : (2 : ℝ)*(t (k+1) : ℝ) ≤ A.card := by
          nlinarith only [hAc,heq,mul_le_mul_of_nonneg_right hx2
            (show 0 ≤ x^E*(P j).card by positivity)]
        exact_mod_cast ht
      have hcut' : crossEdges L A D ≤ 2*x^(r₁+1)*A.card*D.card := by
        rw [crossEdges_symm L A D]
        exact hcut.trans_eq (by ring)
      obtain ⟨C,hCA,hCc,hEdges⟩ := trim_cross_edges hAmin hcut'
      have hQ : 0 ≤ 2*x^(r₁+1) := by positivity
      obtain ⟨D',hD'D,hD'c,hD's⟩ := sparse_half hQ hEdges
      have hshrink : s*(Y.card : ℝ) ≤ D'.card := by
        dsimp [s]
        rw [pow_succ]
        nlinarith only [hDc,hD'c, mul_le_mul_of_nonneg_right hx2
          (show 0 ≤ x^E * (Y.card : ℝ) by positivity)]
      refine ⟨C,D',hD'D.trans hDY,hshrink,hCA.trans hAP,hCc,?_⟩
      intro y hy
      have hed := hD's y hy
      change ((neighbours L C y).card : ℝ) ≤ q
      refine hed.trans ?_
      rw [hCc,Nat.cast_mul,Nat.cast_ofNat,pow_succ]
      have htx := hrt (k+1)
      have hxh : 8*x*(h:ℝ) ≤ 1 := by linarith only [hx8']
      dsimp [q]
      apply (le_div_iff₀ hhp).mpr
      nlinarith only [mul_le_mul_of_nonneg_right hxh hTpos.le,
        congrArg (fun z : ℝ ↦ 8*x*h*z) htx]
  obtain ⟨C, Y, hYZ, hYsize, hGood⟩ := parallel_shrink hs0 hs1 J Z Good
    (fun j C Y Y' hh h ↦ ⟨h.1,h.2.1,fun a ha ↦ h.2.2 a (hh ha)⟩) hthin
  obtain ⟨B,hBY,hBc⟩ := Finset.exists_subset_card_eq (by exact_mod_cast htX.trans hYsize)
  obtain ⟨P', hP'⟩ := extend_approx_parts (q := q) (by dsimp [q]; positivity) hP hw
    (hBY.trans (hYZ.trans hZS)) hBc (fun j hj ↦ (hZj j hj).mono_right (hBY.trans hYZ))
    (fun j hj ↦ ⟨(hGood j hj).1,(hGood j hj).2.1,fun b hb ↦ (hGood j hj).2.2 b (hBY hb)⟩)
  have ht' : (insert w J).card = k+1 := Finset.card_insert_of_notMem hw
  have hn := hmax (insert w J) P' (by simpa only [ht'] using hP')
  omega

end OMA.BNSS

namespace OMA.BNSS

open Finset SimpleGraph Filter Real
open scoped BigOperators Classical

universe u

theorem trichotomy_general {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (g : W) (a : ℕ) (hh : 2 ≤ Fintype.card W) :
    ∃ b c : ℕ, ∃ x₀ : ℝ, 0 < x₀ ∧ Trichotomy H g a b c x₀ := by
  classical
  let h := Fintype.card W
  let R := scaleExponent a h h
  let β := R+3
  let γ := 2*R+β*h
  let x₀ : ℝ := (8*(h:ℝ))⁻¹
  have hhr : (2 : ℝ) ≤ h := by exact_mod_cast hh
  have hhp : (0 : ℝ) < h := by linarith
  refine ⟨2*β,2*γ,x₀,inv_pos.mpr (by positivity),?_⟩
  intro V _ G S x hS hx hxx
  let z : ℕ := ⌈x⁻¹⌉₊
  let y : ℝ := (z:ℝ)⁻¹
  have hz : (x:ℝ)⁻¹ ≤ (z:ℝ) := Nat.le_ceil _
  have hzpos : 0 < (z:ℝ) := (inv_pos.mpr hx).trans_le hz
  have hze : 8*h ≤ z := by
    have hle := inv_anti₀ hx hxx
    change x₀⁻¹ ≤ x⁻¹ at hle
    have h' : (8 : ℝ)*h ≤ (z : ℝ) := by simpa [x₀] using hle.trans hz
    exact_mod_cast h'
  have hxsmall : x ≤ 1/2 := by
    change x ≤ (8*(h:ℝ))⁻¹ at hxx
    exact hxx.trans (by
      rw [← one_div]
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith only [hhr])
  have hyy : y ≤ x := by
    simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hx) hz
  have hyge : x^2 ≤ y := by
    have hceil := Nat.ceil_lt_add_one (inv_nonneg.mpr hx.le)
    change (z:ℝ) < x⁻¹ + 1 at hceil
    have h' := mul_le_mul_of_nonneg_left hceil.le (show 0 ≤ x^2 by positivity)
    have hxx' : x^2*x⁻¹ = x := by field_simp
    have hxs : x^2 ≤ x := by nlinarith only [hxsmall,mul_le_mul_of_nonneg_left hxsmall hx.le]
    rw [show y=(z:ℝ)⁻¹ by rfl, ← one_div]
    apply (le_div_iff₀ hzpos).mpr
    nlinarith only [h',hxx',hxs,hxsmall]
  have hp (r : ℕ) : x^(2*r) ≤ y^r := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) hyge _
  rcases trichotomy_integer H g a hh G S z hze hS with
    ⟨A,hA,hAc,hCf⟩ | hc | ⟨sign,A,B,hA,hB,hAB,hAc,hBc,hs⟩
  · refine Or.inl ⟨A,hA,?_,?_⟩
    · exact (mul_le_mul_of_nonneg_right (hp β) (Nat.cast_nonneg _)).trans hAc
    · exact hCf.trans_le (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (inv_nonneg.mpr hzpos.le) hyy _) (by positivity))
  · exact Or.inr (Or.inl ((mul_le_mul_of_nonneg_right (hp γ) (by positivity)).trans hc))
  · refine Or.inr (Or.inr ⟨sign,A,B,hA,hB,hAB,?_,hBc,?_⟩)
    · exact (mul_le_mul_of_nonneg_right (hp β) (Nat.cast_nonneg _)).trans hAc
    · exact fun v hv ↦ (hs v hv).trans (mul_le_mul_of_nonneg_right hyy (Nat.cast_nonneg _))

theorem copies_small_pattern {W V : Type*} [Fintype W] [DecidableEq W] [DecidableEq V]
    (H : SimpleGraph W) (G : SimpleGraph V) (S : Finset V) (hW : Fintype.card W ≤ 1) :
    (copies H G S).card = S.card ^ Fintype.card W := by
  classical
  have : Subsingleton W := Fintype.card_le_one_iff_subsingleton.mp hW
  unfold copies copiesInParts
  rw [Finset.filter_true_of_mem]
  · rw [Fintype.card_piFinset]; simp
  · intro f hf
    refine ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun a b ↦ ?_⟩
    rw [Subsingleton.elim b a]
    simp

theorem few_all :
    ∀ n : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W],
    Fintype.card W = n → ∀ H : SimpleGraph W,
      ∃ d e : ℕ, 0 < d ∧ 0 < e ∧ ∃ x₀ : ℝ, 0 < x₀ ∧ x₀ ≤ 1/2 ∧
        FewCopiesBlockade H d e x₀ := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W _ _ hW H
    by_cases hn : n ≤ 1
    · refine ⟨1,1,by omega,by omega,1/2,by norm_num,le_rfl,?_⟩
      intro V _ G S x m hx hxx hm hsize hcopy
      rw [copies_small_pattern H G S (hW.trans_le hn), Nat.cast_pow, pow_one] at hcopy
      have hle : x * (S.card : ℝ)^Fintype.card W ≤ (S.card : ℝ)^Fintype.card W := by
        exact mul_le_of_le_one_left (by positivity) (by linarith)
      exact False.elim (not_lt_of_ge hle hcopy)
    · have hh : 2 ≤ Fintype.card W := by omega
      have he : Nonempty W := Fintype.card_pos_iff.mp (by omega)
      let g := Classical.choice he
      let W' := ({w | w ≠ g} : Set W)
      have hW' : Fintype.card W' = n-1 := by rw [card_delete, hW]
      obtain ⟨d,a,hd,ha,y₀,hy₀,hy₀',hs⟩ := ih (n-1) (by omega) W' hW' (H.induce W')
      obtain ⟨b,c,z₀,hz₀,htri⟩ := trichotomy_general H g a hh
      exact few_from_trichotomy H g hd hy₀ hz₀ hs htri

end OMA.BNSS

theorem OMA.solution : type_of% @Erdos61.erdos_61.variants.bnss23 := by
  intro W _ _ H
  obtain ⟨d,e,hd,he,x₀,hx₀,hx₀',hfew⟩ := OMA.BNSS.few_all (Fintype.card W) W rfl H
  exact OMA.BNSS.from_blockade H (Nat.succ_pos d) hx₀ (OMA.BNSS.blockade_of_few H hx₀' hfew)
