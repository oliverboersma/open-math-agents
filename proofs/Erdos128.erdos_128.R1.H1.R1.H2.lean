import OMAReductions.R_Erdos128_erdos_128_R1_H1_R1
import Mathlib.Algebra.Order.Chebyshev

namespace OMA.SparseHalvesLowDegree

open Finset OMA.R_Erdos128_erdos_128_R1

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private def degreeIn (S : Finset V) (v : V) : ℕ := (S.filter (G.Adj v)).card
private noncomputable def edges (S : Finset V) : ℕ := (G.induce (S : Set V)).edgeSet.ncard

private lemma degreeIn_mono {S T : Finset V} (h : S ⊆ T) (v : V) :
    degreeIn G S v ≤ degreeIn G T v :=
  card_le_card (fun x hx => mem_filter.mpr ⟨h (mem_filter.mp hx).1, (mem_filter.mp hx).2⟩)

private lemma degreeIn_union {S T : Finset V} (h : Disjoint S T) (v : V) :
    degreeIn G (S ∪ T) v = degreeIn G S v + degreeIn G T v := by
  unfold degreeIn
  rw [filter_union, card_union_of_disjoint]
  exact h.mono (filter_subset _ _) (filter_subset _ _)

private lemma degreeIn_zero {S : Finset V} {v : V} (h : ∀ w ∈ S, ¬ G.Adj v w) :
    degreeIn G S v = 0 := by
  rw [degreeIn, card_eq_zero]
  apply eq_empty_iff_forall_notMem.mpr
  intro w hw
  exact h w (mem_filter.mp hw).1 (mem_filter.mp hw).2

private lemma twice_edges (S : Finset V) :
    2 * edges G S = ∑ v ∈ S, degreeIn G S v :=
  two_mul_induce G S

private lemma degreeIn_sum_swap (S T : Finset V) :
    ∑ v ∈ S, degreeIn G T v = ∑ w ∈ T, degreeIn G S w := by
  unfold degreeIn
  simp only [card_filter]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun w _ =>
    Finset.sum_congr rfl fun v _ => if_congr (G.adj_comm v w) rfl rfl

private lemma edges_union {S T : Finset V} (h : Disjoint S T) :
    edges G (S ∪ T) = edges G S + edges G T + ∑ v ∈ T, degreeIn G S v := by
  have he := twice_edges G (S ∪ T)
  rw [sum_union h] at he
  simp_rw [degreeIn_union G h, sum_add_distrib] at he
  rw [← twice_edges G S, ← twice_edges G T, degreeIn_sum_swap G S T] at he
  omega

private lemma independent_neighborhood (hcf : G.CliqueFree 3) {v x y : V}
    (hx : G.Adj v x) (hy : G.Adj v y) : ¬ G.Adj x y := by
  intro hxy
  exact hcf {v, x, y} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hx, hy, hxy⟩)

private lemma edges_zero {S : Finset V} (h : ∀ v ∈ S, ∀ w ∈ S, ¬ G.Adj v w) :
    edges G S = 0 := by
  have hs := twice_edges G S
  rw [Finset.sum_eq_zero (fun v hv => degreeIn_zero G (h v hv))] at hs
  omega

private lemma degreeIn_sum_bound (S T : Finset V) (k : ℕ)
    (h : ∀ v ∈ S, degreeIn G T v ≤ k) :
    ∑ v ∈ S, degreeIn G T v ≤ S.card * k := by
  simpa only [sum_const, smul_eq_mul] using
    (Finset.sum_le_sum h : (∑ v ∈ S, degreeIn G T v) ≤ ∑ _v ∈ S, k)


-- The exact averaging lemmas are adapted from the merged Erdős 128 sparse-case reduction by ashnewmanjones.
private lemma sum_sum_erase (S : Finset V) (c : V → ℕ) :
    ∑ v ∈ S, ∑ u ∈ S.erase v, c u + ∑ u ∈ S, c u = S.card * ∑ u ∈ S, c u := by
  calc ∑ v ∈ S, ∑ u ∈ S.erase v, c u + ∑ u ∈ S, c u
      = ∑ v ∈ S, (∑ u ∈ S.erase v, c u + c v) := by rw [Finset.sum_add_distrib]
    _ = ∑ _v ∈ S, ∑ u ∈ S, c u := Finset.sum_congr rfl fun v hv => Finset.sum_erase_add S c hv
    _ = S.card * ∑ u ∈ S, c u := by rw [Finset.sum_const, smul_eq_mul]

-- One deletion step of the weighted potential 2 y m' a + y (y-1) D.
private lemma avg_step (Z Y : Finset V) (y m : ℕ) (hY : Y.card = m + 2) :
    ∃ v ∈ Y, (m + 2) * (2 * y * m * ∑ u ∈ Y.erase v, (Z.filter (G.Adj u)).card +
        y * (y - 1) * ∑ u ∈ Y.erase v, ((Y.erase v).filter (G.Adj u)).card) ≤
      m * (2 * y * (m + 1) * ∑ u ∈ Y, (Z.filter (G.Adj u)).card +
        y * (y - 1) * ∑ u ∈ Y, (Y.filter (G.Adj u)).card) := by
  have hne : Y.Nonempty := by rw [← Finset.card_pos, hY]; omega
  apply Finset.exists_le_of_sum_le hne
  have ha := sum_sum_erase Y (fun u => (Z.filter (G.Adj u)).card)
  have hD := deg_sum_erase_total G Y
  rw [hY] at ha hD
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_const, hY, smul_eq_mul]
  generalize ∑ v ∈ Y, ∑ u ∈ Y.erase v, (Z.filter (G.Adj u)).card = A at ha ⊢
  generalize ∑ u ∈ Y, (Z.filter (G.Adj u)).card = a at ha ⊢
  generalize ∑ v ∈ Y, ∑ u ∈ Y.erase v, ((Y.erase v).filter (G.Adj u)).card = B at hD ⊢
  generalize ∑ u ∈ Y, (Y.filter (G.Adj u)).card = D at hD ⊢
  have hA : A = (m + 1) * a := by nlinarith
  have hB : B = m * D := by nlinarith
  subst hA hB
  apply le_of_eq
  ring

-- Repeated deletion keeps the potential below its proportional share.
private lemma avg_descend (X Z : Finset V) (y : ℕ) (hy : 1 ≤ y) : ∀ d, d + y ≤ X.card →
    ∃ Y ⊆ X, Y.card = X.card - d ∧
      (2 * y * (X.card - d - 1) * ∑ u ∈ Y, (Z.filter (G.Adj u)).card +
        y * (y - 1) * ∑ u ∈ Y, (Y.filter (G.Adj u)).card) * (X.card * (X.card - 1)) ≤
      (X.card - d) * (X.card - d - 1) * (2 * y * (X.card - 1) * ∑ u ∈ X, (Z.filter (G.Adj u)).card +
        y * (y - 1) * ∑ u ∈ X, (X.filter (G.Adj u)).card) := by
  intro d
  induction d with
  | zero =>
    intro _
    refine ⟨X, subset_refl _, by simp, ?_⟩
    simp only [Nat.sub_zero]
    exact le_of_eq (by ring)
  | succ d ih =>
    intro hd
    obtain ⟨Y, hYX, hY, hb⟩ := ih (by omega)
    obtain ⟨m, hm⟩ : ∃ m, X.card - d = m + 2 := ⟨X.card - d - 2, by omega⟩
    obtain ⟨v, hv, hstep⟩ := avg_step G Z Y y m (by rw [hY, hm])
    refine ⟨Y.erase v, (Finset.erase_subset v Y).trans hYX, by
      rw [Finset.card_erase_of_mem hv, hY]; omega, ?_⟩
    have e1 : X.card - d - 1 = m + 1 := by omega
    have e2 : X.card - (d + 1) = m + 1 := by omega
    have e3 : X.card - (d + 1) - 1 = m := by omega
    rw [e1, hm] at hb
    rw [e3, e2]
    generalize (2 * y * m * ∑ u ∈ Y.erase v, (Z.filter (G.Adj u)).card +
        y * (y - 1) * ∑ u ∈ Y.erase v, ((Y.erase v).filter (G.Adj u)).card) = P at hstep ⊢
    generalize (2 * y * (m + 1) * ∑ u ∈ Y, (Z.filter (G.Adj u)).card +
        y * (y - 1) * ∑ u ∈ Y, (Y.filter (G.Adj u)).card) = Q at hstep hb
    generalize (X.card * (X.card - 1)) = N at hb ⊢
    generalize (2 * y * (X.card - 1) * ∑ u ∈ X, (Z.filter (G.Adj u)).card +
        y * (y - 1) * ∑ u ∈ X, (X.filter (G.Adj u)).card) = C at hb ⊢
    have h1 : (m + 2) * (P * N) ≤ (m + 2) * ((m + 1) * m * C) := by
      calc (m + 2) * (P * N) = ((m + 2) * P) * N := by ring
        _ ≤ (m * Q) * N := Nat.mul_le_mul_right _ hstep
        _ = m * (Q * N) := by ring
        _ ≤ m * ((m + 2) * (m + 1) * C) := Nat.mul_le_mul_left _ hb
        _ = (m + 2) * ((m + 1) * m * C) := by ring
    exact Nat.le_of_mul_le_mul_left h1 (by omega)

-- Averaging fact (ii) of Keevash and Sudakov, with exact weights: for 1 ≤ y ≤ |X| some
-- y-subset Y of X has 2 e(Y, Z) + 2 e(Y) ≤ (2 y (x-1) e(X, Z) + y (y-1) 2 e(X)) / (x (x-1)).
private lemma avg_two (X Z : Finset V) (y : ℕ) (hy : 1 ≤ y) (hyx : y ≤ X.card) :
    ∃ Y ⊆ X, Y.card = y ∧
      (2 * ∑ u ∈ Y, (Z.filter (G.Adj u)).card + ∑ u ∈ Y, (Y.filter (G.Adj u)).card) *
          (X.card * (X.card - 1)) ≤
        2 * y * (X.card - 1) * ∑ u ∈ X, (Z.filter (G.Adj u)).card +
          y * (y - 1) * ∑ u ∈ X, (X.filter (G.Adj u)).card := by
  rcases Nat.lt_or_ge y 2 with hy2 | hy2
  · -- y = 1: a single vertex with few neighbours in Z
    have hy1 : y = 1 := by omega
    subst hy1
    have hne : X.Nonempty := by rw [← Finset.card_pos]; omega
    obtain ⟨u, hu, hle⟩ := Finset.exists_le_of_sum_le hne
      (f := fun u => X.card * (Z.filter (G.Adj u)).card)
      (g := fun _ => ∑ w ∈ X, (Z.filter (G.Adj w)).card) (by rw [← Finset.mul_sum, Finset.sum_const, smul_eq_mul])
    refine ⟨{u}, Finset.singleton_subset_iff.mpr hu, by simp, ?_⟩
    simp only [Finset.sum_singleton, Nat.sub_self, mul_zero, zero_mul, add_zero]
    have h0 : (({u} : Finset V).filter (G.Adj u)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro w hw; rw [Finset.mem_singleton] at hw; subst hw; exact G.loopless.irrefl _
    rw [h0, add_zero]
    calc 2 * (Z.filter (G.Adj u)).card * (X.card * (X.card - 1))
        = 2 * (X.card - 1) * (X.card * (Z.filter (G.Adj u)).card) := by ring
      _ ≤ 2 * (X.card - 1) * ∑ w ∈ X, (Z.filter (G.Adj w)).card := Nat.mul_le_mul_left _ hle
      _ = 2 * 1 * (X.card - 1) * ∑ w ∈ X, (Z.filter (G.Adj w)).card := by ring
  · obtain ⟨Y, hYX, hY, hb⟩ := avg_descend G X Z y hy (X.card - y) (by omega)
    have e1 : X.card - (X.card - y) = y := by omega
    rw [e1] at hY hb
    refine ⟨Y, hYX, hY, ?_⟩
    have hyy : 0 < y * (y - 1) := Nat.mul_pos (by omega) (by omega)
    apply Nat.le_of_mul_le_mul_left _ hyy
    calc y * (y - 1) * ((2 * ∑ u ∈ Y, (Z.filter (G.Adj u)).card +
          ∑ u ∈ Y, (Y.filter (G.Adj u)).card) * (X.card * (X.card - 1)))
        = (2 * y * (y - 1) * ∑ u ∈ Y, (Z.filter (G.Adj u)).card +
          y * (y - 1) * ∑ u ∈ Y, (Y.filter (G.Adj u)).card) * (X.card * (X.card - 1)) := by ring
      _ ≤ _ := hb

-- Degree sum of a union with an independent set.


private lemma edges_univ :
    edges G (univ : Finset V) = G.edgeSet.ncard := by
  have h := twice_edges G (univ : Finset V)
  change 2 * edges G univ = (∑ x ∈ (univ : Finset V), ((univ : Finset V).filter (G.Adj x)).card) at h
  rw [deg_sum_univ] at h
  omega

private def cross (X Z : Finset V) : ℕ := ∑ x ∈ X, degreeIn G Z x

private lemma cross_mono_left {X Y : Finset V} (h : X ⊆ Y) (Z : Finset V) :
    cross G X Z ≤ cross G Y Z :=
  sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => Nat.zero_le _)

private lemma edges_mono {X Y : Finset V} (h : X ⊆ Y) : edges G X ≤ edges G Y := by
  have htot : ∑ x ∈ X, degreeIn G X x ≤ ∑ x ∈ Y, degreeIn G Y x :=
    (sum_le_sum fun x _ => degreeIn_mono G h x).trans
      (sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => Nat.zero_le _))
  rw [← twice_edges G X, ← twice_edges G Y] at htot
  omega

private lemma sum_neighborhood_score (U : Finset V) :
    ∑ x ∈ U, (∑ y ∈ U.filter (G.Adj x), degreeIn G U y) =
    ∑ y ∈ U, degreeIn G U y ^ 2 := by
  simp_rw [sum_filter]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun y _ => ?_
  simp_rw [G.adj_comm _ y]
  rw [← sum_filter, sum_const, smul_eq_mul, sq]
  rfl

private lemma average_extension {Z X : Finset V} (hd : Disjoint Z X) (hx : 0 < X.card)
    (k : ℕ) (hk : k ≤ X.card) :
    ∃ Y ⊆ X, Y.card = k ∧
      (edges G (Z ∪ Y) : ℝ) ≤ edges G Z +
        ((k : ℝ) / X.card) * cross G X Z + ((k : ℝ) / X.card) ^ 2 * edges G X := by
  by_cases hk0 : k = 0
  · subst k
    exact ⟨∅, empty_subset _, rfl, by simp⟩
  by_cases heq : k = X.card
  · subst k
    refine ⟨X, Subset.rfl, rfl, ?_⟩
    rw [edges_union G hd, Nat.cast_add, Nat.cast_add, div_self (by positivity : (X.card : ℝ) ≠ 0)]
    unfold cross
    ring_nf
    exact le_rfl
  have hkpos : 1 ≤ k := by omega
  have hx2 : 2 ≤ X.card := by omega
  obtain ⟨Y, hYX, hY, h⟩ := avg_two G X Z k hkpos hk
  refine ⟨Y, hYX, hY, ?_⟩
  change (2 * cross G Y Z + ∑ u ∈ Y, degreeIn G Y u) * (X.card * (X.card - 1)) ≤
    2 * k * (X.card - 1) * cross G X Z +
      k * (k - 1) * ∑ u ∈ X, degreeIn G X u at h
  rw [← twice_edges G X, ← twice_edges G Y] at h
  have h' : (2 * (cross G Y Z : ℝ) + 2 * edges G Y) *
      ((X.card : ℝ) * ((X.card : ℝ) - 1)) ≤
      2 * (k : ℝ) * ((X.card : ℝ) - 1) * cross G X Z +
        (k : ℝ) * ((k : ℝ) - 1) * (2 * edges G X) := by
    have hcast := (Nat.cast_le (α := ℝ)).2 h
    push_cast [Nat.cast_sub hx, Nat.cast_sub hkpos] at hcast
    exact hcast
  have hxR : 0 < (X.card : ℝ) := by exact_mod_cast hx
  have hx1 : 0 < (X.card : ℝ) - 1 := by
    have : (2:ℝ) ≤ X.card := by exact_mod_cast hx2
    linarith
  have hkR : (k : ℝ) ≤ X.card := by exact_mod_cast hk
  have hcoef : ((k : ℝ) - 1) / ((X.card : ℝ) - 1) ≤ (k : ℝ) / X.card := by
    apply (div_le_div_iff₀ hx1 hxR).2
    nlinarith
  have hnonneg : 0 ≤ (k : ℝ) / X.card := by positivity
  have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef hnonneg)
    (Nat.cast_nonneg (α := ℝ) (edges G X))
  have hb : (cross G Y Z : ℝ) + edges G Y ≤ (k : ℝ) / X.card * cross G X Z +
      ((k : ℝ) / X.card) * (((k : ℝ) - 1) / ((X.card : ℝ) - 1)) * edges G X := by
    apply (mul_le_mul_iff_right₀ (mul_pos hxR hx1)).mp
    field_simp [ne_of_gt hxR, ne_of_gt hx1]
    nlinarith
  rw [edges_union G (hd.mono_right hYX)]
  change (↑(edges G Z + edges G Y + cross G Y Z) : ℝ) ≤ _
  push_cast
  rw [pow_two]
  linarith

private lemma average_linear {Z X : Finset V} (hd : Disjoint Z X) (hx : 0 < X.card)
    (k : ℕ) (hk : k ≤ X.card) :
    ∃ Y ⊆ X, Y.card = k ∧
      (edges G (Z ∪ Y) : ℝ) ≤ edges G Z +
        ((k : ℝ) / X.card) * (edges G (Z ∪ X) - (edges G Z : ℝ)) := by
  obtain ⟨Y, hYX, hY, h⟩ := average_extension G hd hx k hk
  refine ⟨Y, hYX, hY, h.trans ?_⟩
  have hxR : 0 < (X.card : ℝ) := by exact_mod_cast hx
  let q : ℝ := (k : ℝ) / X.card
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := (div_le_one hxR).2 (by exact_mod_cast hk)
  have hq2 : q ^ 2 ≤ q := by nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq1)]
  have hProd := mul_le_mul_of_nonneg_right hq2 (Nat.cast_nonneg (α := ℝ) (edges G X))
  rw [edges_union G hd]
  change ↑(edges G Z) + q * ↑(cross G X Z) + q ^ 2 * ↑(edges G X) ≤
    ↑(edges G Z) + q * (↑(edges G Z + edges G X + cross G X Z) - ↑(edges G Z))
  push_cast
  nlinarith

end OMA.SparseHalvesLowDegree


open Finset OMA.SparseHalvesLowDegree OMA.R_Erdos128_erdos_128_R1

-- Keevash and Sudakov, Sparse halves in triangle-free graphs, Theorem 1.1, Case 2.
-- Using a weak inequality in the neighborhood average includes the regular case directly.
set_option maxHeartbeats 2500000 in
theorem OMA.solution : OMA.R_Erdos128_erdos_128_R1_H1_R1.H2 := by
  classical
  intro V _ G hcf hdiv hdense hmax
  obtain ⟨m, hm⟩ := hdiv
  let U : Finset V := univ
  have hU : U.card = 10 * m := by simpa [U] using hm
  have finish (S : Finset V) (hS : S.card = 5 * m)
      (he : (edges G S : ℝ) ≤ 2 * (m : ℝ) ^ 2) :
      ∃ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V ∧
        50 * (G.induce V').edgeSet.ncard ≤ Fintype.card V ^ 2 := by
    refine ⟨(S : Set V), ?_, ?_⟩
    · rw [Set.ncard_coe_finset, hS, hm]
      omega
    · change 50 * edges G S ≤ Fintype.card V ^ 2
      rw [← Nat.cast_le (α := ℝ), hm]
      push_cast
      nlinarith
  by_cases hm0 : m = 0
  · apply finish ∅ (by simp [hm0])
    rw [edges_zero G (by simp), hm0]
    norm_num
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have hun : U.Nonempty := card_pos.mp (by omega)
  have hdeg (v : V) : degreeIn G U v = (G.neighborSet v).ncard := by
    unfold degreeIn U
    rw [← G.neighborFinset_eq_filter]
    simpa only [Set.ncard_coe_finset] using
      congrArg (fun s : Set V => s.ncard) (G.coe_neighborFinset v)
  have hmax' (x : V) : 27 * degreeIn G U x < 110 * m := by
    have h := hmax x
    rw [hm, ← hdeg] at h
    omega
  have htotal := deg_sum_univ G
  change ∑ x ∈ U, degreeIn G U x = 2 * G.edgeSet.ncard at htotal
  have he : 20 * m ^ 2 ≤ G.edgeSet.ncard := by
    rw [hm] at hdense
    nlinarith
  let score (x : V) : ℕ := cross G (U.filter (G.Adj x)) U
  obtain ⟨v, _, hv⟩ := U.exists_max_image score hun
  have hsumScore : ∑ x ∈ U, score x = ∑ x ∈ U, degreeIn G U x ^ 2 :=
    sum_neighborhood_score G U
  have hscore :
      (2 * G.edgeSet.ncard) ^ 2 ≤ (10 * m) ^ 2 * score v := by
    have hsq := sq_sum_le_card_mul_sum_sq (s := U) (f := degreeIn G U)
    rw [htotal, ← hsumScore] at hsq
    have hsum : ∑ x ∈ U, score x ≤ U.card * score v := by
      simpa only [sum_const, smul_eq_mul] using
        (sum_le_sum hv : (∑ x ∈ U, score x) ≤ ∑ _x ∈ U, score v)
    have h := hsq.trans (Nat.mul_le_mul_left U.card hsum)
    rw [hU] at h
    simpa only [pow_two, mul_assoc] using h
  have hscoresmall : 16 * m ^ 2 ≤ score v := by
    have h1 : 40 * m ^ 2 ≤ 2 * G.edgeSet.ncard := by omega
    apply Nat.le_of_mul_le_mul_left (c := (10 * m) ^ 2) _ (by positivity)
    calc
      (10 * m) ^ 2 * (16 * m ^ 2) = (40 * m ^ 2) ^ 2 := by ring
      _ ≤ (2 * G.edgeSet.ncard) ^ 2 := Nat.pow_le_pow_left h1 2
      _ ≤ _ := hscore
  let A := U.filter (G.Adj v)
  let O := U \ A
  have hA : A.card = degreeIn G U v := rfl
  have hAlimit : 27 * A.card < 110 * m := by rw [hA]; exact hmax' v
  have hAind (x) (hx : x ∈ A) (y) (hy : y ∈ A) : ¬ G.Adj x y :=
    independent_neighborhood G hcf (mem_filter.mp hx).2 (mem_filter.mp hy).2
  have heA := edges_zero G hAind
  have hAU : A ⊆ U := filter_subset _ _
  have hAO : Disjoint A O := disjoint_sdiff
  have hcover : A ∪ O = U := union_sdiff_of_subset hAU
  have hO : O.card = 10 * m - A.card := by rw [card_sdiff_of_subset hAU, hU]
  have hScoreEq : G.edgeSet.ncard = edges G O + score v := by
    have h := edges_union G hAO
    rw [hcover, heA, zero_add] at h
    change edges G U = edges G O + cross G O A at h
    rw [show edges G U = G.edgeSet.ncard from edges_univ G] at h
    rw [h]
    congr 1
    unfold cross score
    rw [degreeIn_sum_swap G O A]
    refine sum_congr rfl fun x hx => ?_
    rw [← hcover, degreeIn_union G hAO, degreeIn_zero G (hAind x hx), zero_add]
  have hOE : (edges G O : ℝ) ≤ 4 * (m : ℝ) ^ 2 := by
    have heR : 20 * (m : ℝ) ^ 2 ≤ G.edgeSet.ncard := by exact_mod_cast he
    have hscoreR : (2 * (G.edgeSet.ncard : ℝ)) ^ 2 ≤ (10 * (m : ℝ)) ^ 2 * score v := by
      exact_mod_cast hscore
    have heqR : (G.edgeSet.ncard : ℝ) = edges G O + score v := by exact_mod_cast hScoreEq
    let e : ℝ := G.edgeSet.ncard
    have hprod : 0 ≤ (e - 20 * (m : ℝ) ^ 2) * (4 * e - 20 * (m : ℝ) ^ 2) :=
      mul_nonneg (sub_nonneg.mpr heR) (by dsimp [e]; linarith)
    apply (mul_le_mul_iff_right₀ (show 0 < (10 * (m : ℝ)) ^ 2 by positivity)).mp
    dsimp [e] at hprod
    rw [heqR] at hscoreR hprod
    nlinarith only [hprod, hscoreR]
  have hApos : A.Nonempty := by
    rw [← card_pos]
    by_contra hn
    have hz : A = ∅ := card_eq_zero.mp (by omega)
    have hh := hscoresmall
    change 16 * m ^ 2 ≤ cross G A U at hh
    simp [hz, cross] at hh
    omega
  obtain ⟨w, hwA, hw⟩ := A.exists_max_image (degreeIn G U) hApos
  have hwdeg : 8 * m - A.card ≤ degreeIn G U w := by
    have hsum := degreeIn_sum_bound G A U (degreeIn G U w) hw
    change score v ≤ _ at hsum
    have hgeom : A.card * degreeIn G U w < 16 * m ^ 2 ∨
        8 * m - A.card ≤ degreeIn G U w := by
      by_cases hb : 8 * m - A.card ≤ degreeIn G U w
      · exact Or.inr hb
      left
      have ha : 0 < A.card := card_pos.mpr hApos
      have haR : 0 < (A.card : ℝ) := by exact_mod_cast ha
      have hh : degreeIn G U w + A.card < 8 * m := by omega
      have hhR : (degreeIn G U w : ℝ) + A.card < 8 * m := by exact_mod_cast hh
      have hmul := mul_lt_mul_of_pos_left hhR haR
      have hineq : (A.card : ℝ) * degreeIn G U w < 16 * (m : ℝ) ^ 2 := by
        nlinarith only [hmul, sq_nonneg ((A.card : ℝ) - 4 * m)]
      exact_mod_cast hineq
    exact hgeom.resolve_left (fun hb => (hscoresmall.trans hsum).not_gt hb)
  obtain ⟨B, hBsub, hB⟩ := exists_subset_card_eq
    (s := U.filter (G.Adj w)) (show 8 * m - A.card ≤ (U.filter (G.Adj w)).card from hwdeg)
  have hBO : B ⊆ O := by
    intro x hx
    obtain ⟨hxU, hwx⟩ := mem_filter.mp (hBsub hx)
    exact mem_sdiff.mpr ⟨hxU, fun hxA => hAind w hwA x hxA hwx⟩
  have hBind (x) (hx : x ∈ B) (y) (hy : y ∈ B) : ¬ G.Adj x y :=
    independent_neighborhood G hcf (mem_filter.mp (hBsub hx)).2 (mem_filter.mp (hBsub hy)).2
  have heB := edges_zero G hBind
  let C := O \ B
  have hC : C.card = 2 * m := by
    rw [card_sdiff_of_subset hBO, hO, hB]
    omega
  have hBC : Disjoint B C := disjoint_sdiff
  have hBCcover : B ∪ C = O := union_sdiff_of_subset hBO
  have hCO : C ⊆ O := sdiff_subset
  by_contra hbad
  have hno (S : Finset V) (hS : S.card = 5 * m) : 2 * (m : ℝ) ^ 2 < edges G S :=
    lt_of_not_ge fun he => hbad (finish S hS he)
  have hBsmall : B.card < 5 * m := by
    by_contra hh
    obtain ⟨S, hSB, hS⟩ := exists_subset_card_eq (show 5 * m ≤ B.card by omega)
    have h := hno S hS
    rw [edges_zero G (fun x hx y hy => hBind x (hSB hx) y (hSB hy)), Nat.cast_zero] at h
    nlinarith
  have hAlow : 4 * m < A.card := by
    by_contra hh
    let k := 5 * m - B.card
    have hk : k ≤ m := by dsimp [k]; omega
    obtain ⟨X, hXC, hX, hE⟩ := average_linear G hBC (by omega : 0 < C.card) k (by omega)
    have hsz : (B ∪ X).card = 5 * m := by
      rw [card_union_of_disjoint (hBC.mono_right hXC), hX]
      dsimp [k]
      omega
    have h := hno (B ∪ X) hsz
    rw [heB, hBCcover, hC] at hE
    push_cast at hE
    norm_num at hE
    have hkR : (k : ℝ) ≤ m := by exact_mod_cast hk
    have hratio : (k : ℝ) / (2 * m) ≤ 1 / 2 := by
      apply (div_le_iff₀ (by positivity)).2
      linarith
    have hb1 : (k : ℝ) / (2 * m) * (edges G O : ℝ) ≤ (1 / 2 : ℝ) * edges G O :=
      mul_le_mul_of_nonneg_right hratio (by positivity)
    linarith only [hE, h, hb1, hOE]
  let s := A.card - 4 * m
  have hs : 0 < s := by dsimp [s]; omega
  have hAs : A.card = 4 * m + s := by dsimp [s]; omega
  have hBs : B.card = 4 * m - s := by omega
  have hsl : 27 * s < 2 * m := by omega
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
  have hslR : 27 * (s : ℝ) < 2 * m := by exact_mod_cast hsl
  have hs_m : s ≤ m := by omega
  have hsizeA (X : Finset V) (hXO : X ⊆ O) (hX : X.card = m - s) :
      (A ∪ X).card = 5 * m := by
    rw [card_union_of_disjoint (hAO.mono_right hXO), hX]
    omega


  let K := C.filter (fun x => 2 * m - s ≤ degreeIn G A x)
  have hKC : K ⊆ C := filter_subset _ _
  have hKdegree (x : V) (hx : x ∈ K) : degreeIn G O x ≤ m - s := by
    have hxA := (mem_filter.mp hx).2
    by_contra hneg
    have hex : m - s ≤ (O.filter (G.Adj x)).card := by
      change m - s ≤ degreeIn G O x
      omega
    obtain ⟨X, hXsub, hX⟩ := exists_subset_card_eq hex
    have hXO : X ⊆ O := hXsub.trans (filter_subset _ _)
    have hXadj (y) (hy : y ∈ X) := (mem_filter.mp (hXsub hy)).2
    have hXind : edges G X = 0 :=
      edges_zero G fun y hy z hz => independent_neighborhood G hcf (hXadj y hy) (hXadj z hz)
    have hcross (y) (hy : y ∈ X) : degreeIn G A y ≤ 2 * m + 2 * s := by
      have hsub : A.filter (G.Adj y) ⊆ A \ A.filter (G.Adj x) := by
        intro z hz
        obtain ⟨hzA, hyz⟩ := mem_filter.mp hz
        refine mem_sdiff.mpr ⟨hzA, fun hzx => ?_⟩
        exact independent_neighborhood G hcf (hXadj y hy) (mem_filter.mp hzx).2 hyz
      have hh := card_le_card hsub
      rw [card_sdiff_of_subset (filter_subset _ _)] at hh
      change degreeIn G A y ≤ A.card - degreeIn G A x at hh
      omega
    have hsum := degreeIn_sum_bound G X A (2 * m + 2 * s) hcross
    rw [hX] at hsum
    have hE := hno (A ∪ X) (hsizeA X hXO hX)
    rw [edges_union G (hAO.mono_right hXO), heA, hXind, zero_add, zero_add] at hE
    have hsumR : (∑ y ∈ X, degreeIn G A y : ℕ) ≤ (m - s) * (2 * m + 2 * s) := hsum
    have hsumC := (Nat.cast_le (α := ℝ)).mpr hsumR
    push_cast [Nat.cast_sub hs_m] at hsumC
    push_cast at hE
    nlinarith only [hE, hsumC, sq_nonneg (s : ℝ)]
  -- The number of edges inside C is at most 9 m s.
  have hbeta : (edges G C : ℝ) ≤ 9 * (m : ℝ) * (s : ℝ) := by
    have hk : m + s ≤ C.card := by omega
    obtain ⟨Y, hYC, hY, hYE⟩ := average_extension G hBC (by omega : 0 < C.card) (m + s) hk
    have hsz : (B ∪ Y).card = 5 * m := by
      rw [card_union_of_disjoint (hBC.mono_right hYC), hY, hBs]
      omega
    have hL := hno (B ∪ Y) hsz
    have hBCe : edges G O = edges G C + cross G C B := by
      simpa only [hBCcover, heB, zero_add, cross] using edges_union G hBC
    have hBCr : (edges G O : ℝ) = edges G C + cross G C B := by exact_mod_cast hBCe
    let q : ℝ := ((m : ℝ) + s) / (2 * m)
    rw [heB, hC] at hYE
    push_cast at hYE
    change (edges G (B ∪ Y) : ℝ) ≤ 0 + q * cross G C B + q ^ 2 * edges G C at hYE
    have hq0 : 0 ≤ q := by dsimp [q]; positivity
    have hqlo : 1 / 3 ≤ q := by
      dsimp [q]
      apply (le_div_iff₀ (by positivity)).2
      linarith
    have hqhi : q ≤ 2 / 3 := by
      dsimp [q]
      apply (div_le_iff₀ (by positivity)).2
      linarith
    have hcoef : (2 / 9 : ℝ) ≤ q - q ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hqlo) (sub_nonneg.mpr hqhi)]
    have h1 := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg (α := ℝ) (edges G C))
    have h2 := mul_le_mul_of_nonneg_left hOE hq0
    have hqE : q * (4 * (m : ℝ) ^ 2) = 2 * m ^ 2 + 2 * m * s := by
      dsimp [q]
      field_simp [ne_of_gt hmR]
      <;> ring
    rw [hqE, hBCr] at h2
    nlinarith only [hL, hYE, h1, h2]
  -- If K were large, include a controlled sample from K and fill up from the rest of C.
  have hKsmall : K.card < 4 * s := by
    by_contra hneg
    obtain ⟨I, hIK, hI⟩ := exists_subset_card_eq (show 4 * s ≤ K.card by omega)
    have hIC := hIK.trans hKC
    have hIO := hIC.trans hCO
    have hBI := hBC.mono_right hIC
    let Z := B ∪ I
    let X := C \ I
    have hZX : Disjoint Z X := by
      apply Finset.disjoint_left.mpr
      intro z hz hzx
      rcases mem_union.mp hz with hb | hi
      · exact Finset.disjoint_left.mp hBC hb (mem_sdiff.mp hzx).1
      · exact (mem_sdiff.mp hzx).2 hi
    have hZXcover : Z ∪ X = O := by
      change (B ∪ I) ∪ (C \ I) = O
      rw [union_assoc, union_sdiff_of_subset hIC, hBCcover]
    have hZ : Z.card = B.card + I.card := card_union_of_disjoint hBI
    have hX : X.card = 2 * m - 4 * s := by rw [card_sdiff_of_subset hIC, hC, hI]
    have hsum := degreeIn_sum_bound G I O (m - s) fun x hx => hKdegree x (hIK hx)
    have hsumZ : ∑ x ∈ I, degreeIn G Z x ≤ I.card * (m - s) := by
      have hZO : Z ⊆ O := union_subset hBO hIO
      exact (sum_le_sum fun x _ => degreeIn_mono G hZO x).trans hsum
    have hEa : edges G Z ≤ (4 * s) * (m - s) := by
      change ∑ x ∈ I, degreeIn G (B ∪ I) x ≤ I.card * (m - s) at hsumZ
      simp_rw [degreeIn_union G hBI] at hsumZ
      rw [sum_add_distrib, ← twice_edges G I, hI] at hsumZ
      change edges G (B ∪ I) ≤ _
      rw [edges_union G hBI, heB, zero_add]
      omega
    have hEaR := (Nat.cast_le (α := ℝ)).mpr hEa
    push_cast [Nat.cast_sub hs_m] at hEaR
    let k := m - 3 * s
    have hk : k ≤ X.card := by dsimp [k]; omega
    obtain ⟨Y, hYX, hY, hYedges⟩ := average_linear G hZX (by omega : 0 < X.card) k hk
    have hsz : (Z ∪ Y).card = 5 * m := by
      rw [card_union_of_disjoint (hZX.mono_right hYX), hY, hZ, hBs, hI]
      dsimp [k]
      omega
    have hpos1 : (3 * s : ℕ) ≤ m := by omega
    have hpos2 : (4 * s : ℕ) ≤ 2 * m := by omega
    let t : ℝ := ((m : ℝ) - 3 * s) / (2 * m - 4 * s)
    let r : ℝ := ((m : ℝ) - s) / (2 * m)
    have ht0 : 0 ≤ t := by
      dsimp [t]
      exact div_nonneg (by linarith) (by linarith)
    have htr : t ≤ r := by
      dsimp [t, r]
      apply (div_le_div_iff₀ (by linarith) (by positivity)).2
      nlinarith [sq_nonneg (s : ℝ)]
    have hr1 : r ≤ 1 := by
      dsimp [r]
      exact (div_le_one (by positivity)).mpr (by linarith)
    have hZO : Z ⊆ O := union_subset hBO hIO
    have hEa4 : (edges G Z : ℝ) ≤ 4 * (m : ℝ) ^ 2 :=
      (show (edges G Z : ℝ) ≤ edges G O by exact_mod_cast edges_mono G hZO).trans hOE
    have hcalc := calc
      (edges G (Z ∪ Y) : ℝ) ≤ edges G Z + t * (edges G O - (edges G Z : ℝ)) := by
        rw [hZXcover, hX] at hYedges
        dsimp [k] at hYedges
        push_cast [Nat.cast_sub hpos1, Nat.cast_sub hpos2] at hYedges
        exact hYedges
      _ ≤ edges G Z + t * (4 * (m : ℝ) ^ 2 - (edges G Z : ℝ)) := by
        gcongr
      _ ≤ edges G Z + r * (4 * (m : ℝ) ^ 2 - (edges G Z : ℝ)) := by
        gcongr
      _ = r * (4 * (m : ℝ) ^ 2) + (1 - r) * edges G Z := by ring
      _ ≤ r * (4 * (m : ℝ) ^ 2) + (1 - r) * (4 * s * ((m : ℝ) - s)) :=
        by gcongr
      _ = 2 * (m : ℝ) ^ 2 - 2 * (s : ℝ) ^ 3 / m := by
        dsimp [r]
        field_simp [ne_of_gt hmR]
        <;> ring
      _ ≤ 2 * (m : ℝ) ^ 2 := sub_le_self _ (by positivity)
    exact (hno (Z ∪ Y) hsz).not_ge hcalc
  let L := C \ K
  have hLC : L ⊆ C := sdiff_subset
  have hLO : L ⊆ O := hLC.trans hCO
  have hLs : L.card = 2 * m - K.card := by rw [card_sdiff_of_subset hKC, hC]
  have hLbig : 2 * m - 4 * s ≤ L.card := by omega
  have hLspos : 0 < L.card := by omega
  have hsmall (x : V) (hx : x ∈ L) : degreeIn G A x ≤ 2 * m - s := by
    obtain ⟨hxC, hxK⟩ := mem_sdiff.mp hx
    exact le_of_not_ge fun h => hxK (mem_filter.mpr ⟨hxC, h⟩)
  have hsubcoef : m - s ≤ L.card := by omega
  obtain ⟨J, hJL, hJ, hJedge⟩ :=
    average_extension G (hAO.mono_right hLO) hLspos (m - s) hsubcoef
  have hJsize := hsizeA J (hJL.trans hLO) hJ
  have hlc := degreeIn_sum_bound G L A (2 * m - s) hsmall
  change cross G L A ≤ _ at hlc
  have hlcr := (Nat.cast_le (α := ℝ)).mpr hlc
  push_cast [Nat.cast_sub (show s ≤ 2 * m by omega)] at hlcr
  have hLpos : 0 < (L.card : ℝ) := by exact_mod_cast hLspos
  have hLbigR : 2 * (m : ℝ) - 4 * s ≤ (L.card : ℝ) := by
    have hcast := (Nat.cast_le (α := ℝ)).mpr hLbig
    push_cast [Nat.cast_sub (show 4 * s ≤ 2 * m by omega)] at hcast
    exact hcast
  let q : ℝ := ((m : ℝ) - s) / L.card
  have hq0 : 0 ≤ q := by dsimp [q]; exact div_nonneg (by linarith) hLpos.le
  have hq6 : q ≤ 6 / 11 := by
    dsimp [q]
    apply (div_le_iff₀ hLpos).2
    linarith only [hLbigR, hslR, hsR, hmR]
  have hq3 : q ^ 2 ≤ 3 / 10 := by
    have h := mul_nonneg hq0 (sub_nonneg.mpr hq6)
    nlinarith only [h, hq6]
  have hCross := mul_le_mul_of_nonneg_left hlcr hq0
  have hprod : q * (L.card * (2 * (m : ℝ) - s)) =
      ((m : ℝ) - s) * (2 * (m : ℝ) - s) := by
    rw [← mul_assoc]
    rw [show q * (L.card : ℝ) = (m : ℝ) - s from div_mul_cancel₀ _ hLpos.ne']
  rw [hprod] at hCross
  have heLC : (edges G L : ℝ) ≤ edges G C := by exact_mod_cast edges_mono G hLC
  have htail := calc
    q ^ 2 * (edges G L : ℝ) ≤ (3 / 10 : ℝ) * edges G L :=
      mul_le_mul_of_nonneg_right hq3 (by positivity)
    _ ≤ (3 / 10 : ℝ) * edges G C := by gcongr
    _ ≤ (3 / 10 : ℝ) * (9 * (m : ℝ) * s) := by gcongr
  rw [heA] at hJedge
  push_cast [Nat.cast_sub hs_m] at hJedge
  change (edges G (A ∪ J) : ℝ) ≤ 0 + q * cross G L A + q ^ 2 * edges G L at hJedge
  have hcontr := hno (A ∪ J) hJsize
  nlinarith only [hcontr, hJedge, hCross, htail,
    mul_nonneg hsR.le (show 0 ≤ (m : ℝ) / 10 - s by linarith)]

