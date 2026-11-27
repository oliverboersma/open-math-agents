import OMAReductions.R_Erdos128_erdos_128_R1_H1_R1

-- Step Erdos128.erdos_128.R1.H1.R1.H1: hypothesis H1 of reduction Erdos128.erdos_128.R1.H1.R1
-- Credit: @ashnewmanjones
-- Proof: Keevash and Sudakov, Sparse halves in triangle-free graphs, JCTB 96 (2006), Theorem 1.1, Case 1,
-- done in exact integers with n = 10m and maximum degree s = 4m + t, 27t ≥ 2m.


namespace OMA.E128C1

open Finset OMA.R_Erdos128_erdos_128_R1

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

-- Mantel's theorem in degree-sum form: 2 D(Z) ≤ |Z|^2 for triangle-free G.
lemma mantel_D (hcf : G.CliqueFree 3) (Z : Finset V) :
    2 * ∑ u ∈ Z, (Z.filter (G.Adj u)).card ≤ Z.card ^ 2 := by
  classical
  rw [← two_mul_induce G Z]
  have hcf' : (G.induce (Z : Set V)).CliqueFree (2 + 1) :=
    hcf.comap (SimpleGraph.Embedding.induce (Z : Set V)).isContained
  have h := SimpleGraph.CliqueFree.card_edgeFinset_le hcf'
  simp only at h
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  have hk : Fintype.card (Z : Set V) = Z.card := by simp
  rw [hk] at h
  have hmod : Z.card % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hc : (Z.card % 2).choose 2 = 0 := Nat.choose_eq_zero_of_lt hmod
  rw [hc, add_zero] at h
  have : 4 * ((Z.card ^ 2 - (Z.card % 2) ^ 2) * (2 - 1) / (2 * 2)) ≤ Z.card ^ 2 := by
    have := Nat.mul_div_le ((Z.card ^ 2 - (Z.card % 2) ^ 2) * (2 - 1)) (2 * 2)
    simp only [Nat.reduceMul, Nat.add_one_sub_one, mul_one] at this ⊢
    omega
  omega

lemma nbhd_indep' (hcf : G.CliqueFree 3) (v : V) :
    ∀ u ∈ (univ : Finset V).filter (G.Adj v), ∀ w ∈ (univ : Finset V).filter (G.Adj v),
      ¬ G.Adj u w := by
  intro u hu w hw huw
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hw
  exact hcf {v, u, w} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hu, hw, huw⟩)

lemma D_zero (S : Finset V) (hS : ∀ u ∈ S, ∀ w ∈ S, ¬ G.Adj u w) :
    ∑ u ∈ S, (S.filter (G.Adj u)).card = 0 := by
  apply Finset.sum_eq_zero
  intro u hu
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro w hw; exact hS u hu w hw

lemma D_union' (I Y : Finset V) (hdisj : Disjoint I Y) (hI : ∀ u ∈ I, ∀ w ∈ I, ¬ G.Adj u w) :
    ∑ u ∈ I ∪ Y, ((I ∪ Y).filter (G.Adj u)).card =
      ∑ u ∈ Y, (Y.filter (G.Adj u)).card + 2 * ∑ u ∈ Y, (I.filter (G.Adj u)).card := by
  have hsplit : ∀ u, ((I ∪ Y).filter (G.Adj u)).card =
      (I.filter (G.Adj u)).card + (Y.filter (G.Adj u)).card := by
    intro u
    rw [Finset.filter_union, Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter hdisj)]
  simp_rw [hsplit]
  rw [Finset.sum_union hdisj, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hII : ∑ u ∈ I, (I.filter (G.Adj u)).card = 0 := D_zero G I hI
  have hswap : ∑ u ∈ I, (Y.filter (G.Adj u)).card = ∑ u ∈ Y, (I.filter (G.Adj u)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => ?_
    simp only [G.adj_comm]
  rw [hII, hswap]
  ring

-- degree splits along A and its complement
lemma deg_split (A : Finset V) (x : V) :
    ((univ : Finset V).filter (G.Adj x)).card =
      (A.filter (G.Adj x)).card + (((univ : Finset V) \ A).filter (G.Adj x)).card := by
  rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter Finset.disjoint_sdiff),
    ← Finset.filter_union, Finset.union_sdiff_of_subset (Finset.subset_univ _)]

end OMA.E128C1

set_option maxHeartbeats 4000000 in
open Finset OMA.R_Erdos128_erdos_128_R1 OMA.E128C1 in
theorem OMA.solution : OMA.R_Erdos128_erdos_128_R1_H1_R1.H1 := by
  intro V _ G hcf hdiv hdense hbig
  classical
  obtain ⟨m, hm⟩ := hdiv
  by_contra hno
  push Not at hno
  -- every set of 5m vertices spans more than 2m² edges (degree sum > 4m²)
  have hsp : ∀ S : Finset V, S.card = 5 * m → 4 * m ^ 2 < ∑ u ∈ S, (S.filter (G.Adj u)).card := by
    intro S hS
    have h1 := hno (S : Set V) (by rw [Set.ncard_coe_finset, hS, hm]; omega)
    have h2 := two_mul_induce G S
    rw [hm] at h1
    nlinarith
  obtain ⟨v0, hv0⟩ := hbig
  obtain ⟨v, -, hvmax⟩ := Finset.exists_max_image (univ : Finset V)
    (fun v => ((univ : Finset V).filter (G.Adj v)).card) ⟨v0, Finset.mem_univ _⟩
  set A := (univ : Finset V).filter (G.Adj v) with hAdef
  set s := A.card with hsdef
  have hdeg : ∀ x, ((univ : Finset V).filter (G.Adj x)).card ≤ s := fun x => hvmax x (Finset.mem_univ _)
  have hs27 : 110 * m ≤ 27 * s := by
    have e : (G.neighborSet v0).ncard = ((univ : Finset V).filter (G.Adj v0)).card := by
      rw [← Set.ncard_coe_finset]; congr 1; ext w; simp [SimpleGraph.mem_neighborSet]
    have := hdeg v0
    rw [hm] at hv0
    omega
  have hm0 : 0 < m := by
    have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v0⟩
    omega
  have hAind := nbhd_indep' G hcf v
  have hAsub : A ⊆ univ := Finset.subset_univ _
  have hvA : v ∉ A := by simp [hAdef]
  -- s < 5m (else A contains an independent half)
  have hs5 : s < 5 * m := by
    by_contra h
    push Not at h
    obtain ⟨S, hSA, hS⟩ := Finset.exists_subset_card_eq h
    have := hsp S hS
    rw [D_zero G S (fun u hu w hw => hAind u (hSA hu) w (hSA hw))] at this
    omega
  -- observation (O)
  have hO : ∀ x, x ∉ A → 6 * m ≤ s + (A.filter (G.Adj x)).card →
      (((univ : Finset V) \ A).filter (G.Adj x)).card < 5 * m - s := by
    intro x _ hx
    by_contra h
    push Not at h
    obtain ⟨Y, hYN, hY⟩ := Finset.exists_subset_card_eq h
    have hdisj : Disjoint A Y :=
      Finset.disjoint_of_subset_right (hYN.trans (Finset.filter_subset _ _)) Finset.disjoint_sdiff
    have hScard : (A ∪ Y).card = 5 * m := by rw [Finset.card_union_of_disjoint hdisj, hY]; omega
    have hD := D_union' G A Y hdisj hAind
    have hY0 : ∑ u ∈ Y, (Y.filter (G.Adj u)).card = 0 := D_zero G Y (fun u hu w hw huw => by
      have hu' := (Finset.mem_filter.mp (hYN hu)).2
      have hw' := (Finset.mem_filter.mp (hYN hw)).2
      exact hcf {x, u, w} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hu', hw', huw⟩))
    have hyA : ∀ y ∈ Y, (A.filter (G.Adj y)).card ≤ 2 * s - 6 * m := by
      intro y hy
      have hxy := (Finset.mem_filter.mp (hYN hy)).2
      have hsub : A.filter (G.Adj y) ⊆ A \ A.filter (G.Adj x) := by
        intro a ha
        obtain ⟨haA, hya⟩ := Finset.mem_filter.mp ha
        refine Finset.mem_sdiff.mpr ⟨haA, fun hxa' => ?_⟩
        have hxa := (Finset.mem_filter.mp hxa').2
        exact hcf {x, y, a} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy, hxa, hya⟩)
      have := Finset.card_le_card hsub
      rw [Finset.card_sdiff_of_subset (Finset.filter_subset _ _)] at this
      omega
    have hsum : ∑ u ∈ Y, (A.filter (G.Adj u)).card ≤ (5 * m - s) * (2 * s - 6 * m) := by
      calc _ ≤ ∑ _u ∈ Y, (2 * s - 6 * m) := Finset.sum_le_sum hyA
        _ = _ := by rw [Finset.sum_const, hY, smul_eq_mul]
    have h3 := hsp (A ∪ Y) hScard
    rw [hD, hY0] at h3
    have key : (5 * m - s) * (2 * s - 6 * m) ≤ 2 * m ^ 2 := by
      obtain ⟨p, hp⟩ : ∃ p, 5 * m = s + p := ⟨5 * m - s, by omega⟩
      obtain ⟨q, hq⟩ : ∃ q, 2 * s = 6 * m + q := ⟨2 * s - 6 * m, by omega⟩
      rw [show 5 * m - s = p by omega, show 2 * s - 6 * m = q by omega]
      nlinarith
    omega
  -- B and C
  set B := ((univ : Finset V) \ A).filter (fun x => 6 * m ≤ s + (A.filter (G.Adj x)).card) with hBdef
  set C := ((univ : Finset V) \ A).filter (fun x => ¬ 6 * m ≤ s + (A.filter (G.Adj x)).card) with hCdef
  have hBC : B.card + C.card = 10 * m - s := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_sdiff_of_subset hAsub,
      Finset.card_univ, hm]
  have hBA : Disjoint A B := Finset.disjoint_of_subset_right (Finset.filter_subset _ _) Finset.disjoint_sdiff
  have hCA : Disjoint A C := Finset.disjoint_of_subset_right (Finset.filter_subset _ _) Finset.disjoint_sdiff
  -- |C| < 5m - s
  have hC : C.card < 5 * m - s := by
    by_contra h
    push Not at h
    obtain ⟨X, hXC, hX⟩ := Finset.exists_subset_card_eq h
    have hdisj : Disjoint A X := Finset.disjoint_of_subset_right hXC hCA
    have hScard : (A ∪ X).card = 5 * m := by rw [Finset.card_union_of_disjoint hdisj, hX]; omega
    have hD := D_union' G A X hdisj hAind
    have hman := mantel_D G hcf X
    have hxA : ∀ x ∈ X, (A.filter (G.Adj x)).card ≤ 6 * m - s - 1 := by
      intro x hx
      have := (Finset.mem_filter.mp (hXC hx)).2
      omega
    have hsum : ∑ u ∈ X, (A.filter (G.Adj u)).card ≤ (5 * m - s) * (6 * m - s - 1) := by
      calc _ ≤ ∑ _u ∈ X, (6 * m - s - 1) := Finset.sum_le_sum hxA
        _ = _ := by rw [Finset.sum_const, hX, smul_eq_mul]
    have h3 := hsp (A ∪ X) hScard
    rw [hD] at h3
    rw [hX] at hman
    obtain ⟨t, ht⟩ : ∃ t, s = 4 * m + t := ⟨s - 4 * m, by omega⟩
    obtain ⟨p, hp⟩ : ∃ p, m = t + p := ⟨m - t, by omega⟩
    rw [show 5 * m - s = p by omega, show 6 * m - s - 1 = p + m - 1 by omega] at hsum
    rw [show 5 * m - s = p by omega] at hman
    have h27 : 2 * m ≤ 27 * t := by omega
    -- 2·D(A ∪ X) ≤ p² + 4 p (p + m - 1) ≤ 8 m²
    have hq : p ^ 2 + 4 * (p * (p + m - 1)) ≤ 8 * m ^ 2 := by
      have hpm : p ≤ m := by omega
      have e1 : p * (p + m - 1) ≤ p * (p + m) := Nat.mul_le_mul_left _ (by omega)
      have hcore : p ^ 2 + 4 * (p * (p + m)) ≤ 8 * m ^ 2 := by
        rw [hp] at h27 ⊢
        nlinarith [mul_nonneg (Nat.zero_le t) (Nat.zero_le p), h27]
      omega
    nlinarith
  have hB5 : 5 * m ≤ B.card := by omega
  -- t < m/5
  have h21 : 5 * s + 5 < 21 * m := by
    obtain ⟨Y, hYB, hY⟩ := Finset.exists_subset_card_eq hB5
    have hyY : ∀ y ∈ Y, (Y.filter (G.Adj y)).card ≤ 5 * m - s - 1 := by
      intro y hy
      have hyB := Finset.mem_filter.mp (hYB hy)
      have hyA : y ∉ A := (Finset.mem_sdiff.mp hyB.1).2
      have := hO y hyA hyB.2
      have hsub : Y.filter (G.Adj y) ⊆ ((univ : Finset V) \ A).filter (G.Adj y) := by
        intro w hw
        rw [Finset.mem_filter] at hw ⊢
        exact ⟨(Finset.mem_filter.mp (hYB hw.1)).1, hw.2⟩
      have := Finset.card_le_card hsub
      omega
    have hsum : ∑ u ∈ Y, (Y.filter (G.Adj u)).card ≤ 5 * m * (5 * m - s - 1) := by
      calc _ ≤ ∑ _u ∈ Y, (5 * m - s - 1) := Finset.sum_le_sum hyY
        _ = _ := by rw [Finset.sum_const, hY, smul_eq_mul]
    have h3 := hsp Y hY
    have : 4 * m < 5 * (5 * m - s - 1) := by
      have h4 : m * (4 * m) < m * (5 * (5 * m - s - 1)) := by nlinarith
      exact Nat.lt_of_mul_lt_mul_left h4
    omega
  -- D' : vertices of B with few neighbours in A
  set D := B.filter (fun x => (A.filter (G.Adj x)).card ≤ 2 * s - 6 * m) with hDdef
  have hDdeg : ∀ x ∈ D, ((univ : Finset V).filter (G.Adj x)).card ≤ s - m - 1 := by
    intro x hx
    have hxD := Finset.mem_filter.mp hx
    have hxB := Finset.mem_filter.mp hxD.1
    have := hO x (Finset.mem_sdiff.mp hxB.1).2 hxB.2
    rw [deg_split G A x]
    omega
  have hDcard : D.card ≤ 10 * (s - 4 * m) := by
    have hsumdeg := deg_sum_univ G
    have hE : 20 * m ^ 2 ≤ G.edgeSet.ncard := by rw [hm] at hdense; nlinarith
    have hsplit := Finset.sum_filter_add_sum_filter_not (univ : Finset V) (fun x => x ∈ D)
      (fun x => ((univ : Finset V).filter (G.Adj x)).card)
    have h1 : ∑ x ∈ (univ : Finset V).filter (fun x => x ∈ D), ((univ : Finset V).filter (G.Adj x)).card ≤
        D.card * (s - m - 1) := by
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
      calc _ ≤ ∑ _x ∈ D, (s - m - 1) := Finset.sum_le_sum hDdeg
        _ = _ := by rw [Finset.sum_const, smul_eq_mul]
    have h2 : ∑ x ∈ (univ : Finset V).filter (fun x => x ∉ D), ((univ : Finset V).filter (G.Adj x)).card ≤
        (10 * m - D.card) * s := by
      calc _ ≤ ∑ _x ∈ (univ : Finset V).filter (fun x => x ∉ D), s := Finset.sum_le_sum fun x _ => hdeg x
        _ = ((univ : Finset V).filter (fun x => x ∉ D)).card * s := by rw [Finset.sum_const, smul_eq_mul]
        _ = (10 * m - D.card) * s := by
          rw [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter,
            Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hm]
    have hDle : D.card ≤ 10 * m := by
      have := Finset.card_le_univ D; rw [hm] at this; exact this
    obtain ⟨t, ht⟩ : ∃ t, s = 4 * m + t := ⟨s - 4 * m, by omega⟩
    obtain ⟨d, hd⟩ : ∃ d, 10 * m = D.card + d := ⟨10 * m - D.card, by omega⟩
    rw [ht, show 4 * m + t - m - 1 = 3 * m + t - 1 by omega] at h1
    rw [ht, show 10 * m - D.card = d by omega] at h2
    rw [ht, show 4 * m + t - 4 * m = t by omega]
    have h3 : 40 * m ^ 2 ≤ D.card * (3 * m + t - 1) + d * (4 * m + t) := by
      rw [← hsplit] at hsumdeg; omega
    have h4 : D.card * (3 * m + t - 1) ≤ D.card * (3 * m + t) := Nat.mul_le_mul_left _ (by omega)
    have h5 : D.card * (m + 1) ≤ 10 * m * t := by
      have hw : D.card * (3 * m + t - 1) + D.card * (m + 1) ≤ D.card * (4 * m + t) := by
        rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
      have e : D.card * (4 * m + t) + d * (4 * m + t) = 40 * m ^ 2 + 10 * m * t := by
        rw [← Nat.add_mul, ← hd]; ring
      linarith
    have h6 : D.card * (m + 1) ≤ 10 * t * (m + 1) := by
      calc D.card * (m + 1) ≤ 10 * m * t := h5
        _ ≤ 10 * t * (m + 1) := by nlinarith
    exact Nat.le_of_mul_le_mul_right h6 (by omega)
  -- edges inside B lie inside D
  have hBedge : ∀ x ∈ B, x ∉ D → ∀ y ∈ B, ¬ G.Adj x y := by
    intro x hx hxD y hy hxy
    have hxA : 2 * s - 6 * m < (A.filter (G.Adj x)).card := by
      by_contra h; push Not at h; exact hxD (Finset.mem_filter.mpr ⟨hx, h⟩)
    have hyA := (Finset.mem_filter.mp hy).2
    have hne : ((A.filter (G.Adj x)) ∩ (A.filter (G.Adj y))).Nonempty :=
      Finset.inter_nonempty_of_card_lt_card_add_card (Finset.filter_subset _ _)
        (Finset.filter_subset _ _) (by omega)
    obtain ⟨a, ha⟩ := hne
    obtain ⟨hax, hay⟩ := Finset.mem_inter.mp ha
    exact hcf {x, y, a} (SimpleGraph.is3Clique_triple_iff.mpr
      ⟨hxy, (Finset.mem_filter.mp hax).2, (Finset.mem_filter.mp hay).2⟩)
  -- final contradiction
  obtain ⟨Y, hYB, hY⟩ := Finset.exists_subset_card_eq hB5
  have hYD : ∑ u ∈ Y, (Y.filter (G.Adj u)).card = ∑ u ∈ Y ∩ D, ((Y ∩ D).filter (G.Adj u)).card := by
    rw [← Finset.sum_filter_add_sum_filter_not Y (fun u => u ∈ D)]
    have z : ∑ u ∈ Y.filter (fun u => u ∉ D), (Y.filter (G.Adj u)).card = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      rw [Finset.mem_filter] at hu
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro w hw
      exact hBedge u (hYB hu.1) hu.2 w (hYB hw)
    rw [z, add_zero, Finset.filter_mem_eq_inter]
    refine Finset.sum_congr rfl fun u hu => ?_
    congr 1
    ext w
    simp only [Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨hw, hadj⟩
      refine ⟨⟨hw, ?_⟩, hadj⟩
      by_contra hwD
      exact hBedge w (hYB hw) hwD u (hYB (Finset.mem_inter.mp hu).1) hadj.symm
    · rintro ⟨⟨hw, _⟩, hadj⟩; exact ⟨hw, hadj⟩
  have hman := mantel_D G hcf (Y ∩ D)
  have hYDc : (Y ∩ D).card ≤ D.card := Finset.card_le_card Finset.inter_subset_right
  have h3 := hsp Y hY
  rw [hYD] at h3
  have hsq : (Y ∩ D).card ^ 2 ≤ (10 * (s - 4 * m)) ^ 2 := Nat.pow_le_pow_left (hYDc.trans hDcard) 2
  have ht5 : 5 * (s - 4 * m) < m := by omega
  have : (10 * (s - 4 * m)) ^ 2 < 4 * m ^ 2 := by nlinarith
  omega
