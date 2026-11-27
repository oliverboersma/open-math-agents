import OMAStatements.S_mo_148821
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

section ProofMo148821

/-! ## Part 1: Double-counting (`certified → guaranteed`) -/

private def endpointSum {n : ℕ} (φ : Fin n → ℤ) (e : Sym2 (Fin n)) : ℤ :=
  ∑ v ∈ Finset.univ.filter (fun v => v ∈ e), φ v

private lemma sum_endpointSum {n : ℕ} (E : OMA.S_mo_148821.Edges n) (φ : Fin n → ℤ) :
    ∑ e ∈ E, endpointSum φ e = ∑ v : Fin n, (OMA.S_mo_148821.degreeAt E v : ℤ) * φ v := by
  unfold endpointSum OMA.S_mo_148821.degreeAt
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

private lemma exists_endpoints_of_mem_edgeSet {n : ℕ} {G : SimpleGraph (Fin n)}
    {e : Sym2 (Fin n)} (he : e ∈ G.edgeSet) :
    ∃ u w : Fin n, u ≠ w ∧ e = Sym2.mk u w ∧
      ∀ φ : Fin n → ℤ, endpointSum φ e = φ u + φ w := by
  induction e using Sym2.ind with
  | _ u w =>
    have hadj : G.Adj u w := G.mem_edgeSet.mp he
    have hne : u ≠ w := G.ne_of_adj hadj
    refine ⟨u, w, hne, rfl, fun φ => ?_⟩
    unfold endpointSum
    have hfilt : Finset.univ.filter (fun v : Fin n => v ∈ Sym2.mk u w) = {u, w} := by
      ext v
      simp [Sym2.mem_iff]
    rw [hfilt, Finset.sum_pair hne]

private lemma mem_lbl_iff {b n : ℕ} (R : Fin b → OMA.S_mo_148821.Edges n) (v : Fin n) (i : Fin b) :
    i ∈ (Finset.univ.filter (fun j : Fin b => 0 < OMA.S_mo_148821.degreeAt (R j) v)) ↔
      ∃ f ∈ R i, v ∈ f := by
  simp [OMA.S_mo_148821.degreeAt, Finset.card_pos, Finset.Nonempty]

private lemma degreeAt_Ri_cast {b n : ℕ} {G : SimpleGraph (Fin n)}
    {R : Fin b → OMA.S_mo_148821.Edges n} (hR : ∀ i, OMA.S_mo_148821.feasible G 1 (R i))
    (v : Fin n) (i : Fin b) :
    (OMA.S_mo_148821.degreeAt (R i) v : ℤ) =
      if i ∈ Finset.univ.filter (fun j : Fin b => 0 < OMA.S_mo_148821.degreeAt (R j) v)
      then 1 else 0 := by
  have hle : OMA.S_mo_148821.degreeAt (R i) v ≤ 1 := (hR i).2 v
  split_ifs with hmem
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    omega
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt, Nat.le_zero] at hmem
    simp [hmem]

private theorem certified_imp_guaranteed {b p q : ℕ} (hcert : OMA.S_mo_148821.certified b p q) :
    OMA.S_mo_148821.guaranteed b p q := by
  rcases hcert with ⟨L, h, a, hL, hvtx, hx, hyz⟩
  intro n G R O hlegal hfeasO
  rcases hlegal with ⟨hR_feas, hR_disj, hR_max⟩
  rcases hfeasO with ⟨hO_sub, hO_deg⟩
  let lbl : Fin n → OMA.S_mo_148821.Label b :=
    fun v => Finset.univ.filter (fun j : Fin b => 0 < OMA.S_mo_148821.degreeAt (R j) v)
  let φh : Fin n → ℤ := fun v => (h (lbl v) : ℤ)
  have hpwd : (↑(Finset.univ : Finset (Fin b)) : Set (Fin b)).PairwiseDisjoint R := by
    intro i _ j _ hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hR_disj i j hlt
    · exact (hR_disj j i hgt).symm
  have hpwd_inter :
      (↑(Finset.univ : Finset (Fin b)) : Set (Fin b)).PairwiseDisjoint (fun i => R i ∩ O) := by
    intro i hi j hj hij
    exact (hpwd hi hj hij).mono Finset.inter_subset_left Finset.inter_subset_left
  let O_out : OMA.S_mo_148821.Edges n := O.filter (fun e => ∀ i : Fin b, e ∉ R i)
  let O_in_all : OMA.S_mo_148821.Edges n := Finset.univ.biUnion (fun i => R i ∩ O)
  have hO_disj : Disjoint O_out O_in_all := by
    rw [Finset.disjoint_left]
    intro e he_out he_in
    simp only [O_out, Finset.mem_filter] at he_out
    simp only [O_in_all, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_inter] at he_in
    rcases he_in with ⟨i, hi, _⟩
    exact he_out.2 i hi
  have hO_union : O_out ∪ O_in_all = O := by
    ext e
    simp only [O_out, O_in_all, Finset.mem_union, Finset.mem_filter, Finset.mem_biUnion,
      Finset.mem_univ, true_and, Finset.mem_inter]
    constructor
    · rintro (⟨heO, _⟩ | ⟨i, _, heO⟩) <;> exact heO
    · intro heO
      by_cases hex : ∃ i : Fin b, e ∈ R i
      · rcases hex with ⟨i, hi⟩
        exact Or.inr ⟨i, hi, heO⟩
      · exact Or.inl ⟨heO, fun i hi => hex ⟨i, hi⟩⟩
  have hO_card : (O.card : ℤ) = (O_out.card : ℤ) + ∑ i : Fin b, ((R i ∩ O).card : ℤ) := by
    conv_lhs => rw [← hO_union]
    rw [Finset.card_union_of_disjoint hO_disj, Finset.card_biUnion hpwd_inter]
    push_cast
    rfl
  have hO_sum_h : ∑ e ∈ O, endpointSum φh e =
      (∑ e ∈ O_out, endpointSum φh e) + ∑ i : Fin b, ∑ e ∈ R i ∩ O, endpointSum φh e := by
    conv_lhs => rw [← hO_union]
    rw [Finset.sum_union hO_disj, Finset.sum_biUnion hpwd_inter]
  have h_edge_out : ∀ e ∈ O_out, (L : ℤ) * (p : ℤ) ≤ endpointSum φh e := by
    intro e he
    simp only [O_out, Finset.mem_filter] at he
    rcases exists_endpoints_of_mem_edgeSet (hO_sub e he.1) with ⟨u, w, _, rfl, hend⟩
    rw [hend]
    have hcov : ∀ i : Fin b, i ∈ lbl u ∨ i ∈ lbl w := by
      intro i
      rcases hR_max i (Sym2.mk u w) (hO_sub _ he.1) (fun j _ => he.2 j) with ⟨f, hfR, v, hve, hvf⟩
      rcases Sym2.mem_iff.mp hve with hvu | hvw
      · subst hvu
        exact Or.inl ((mem_lbl_iff R v i).mpr ⟨f, hfR, hvf⟩)
      · subst hvw
        exact Or.inr ((mem_lbl_iff R v i).mpr ⟨f, hfR, hvf⟩)
    dsimp [φh]
    exact_mod_cast hx (lbl u) (lbl w) hcov
  have h_sum_out : (L : ℤ) * (p : ℤ) * (O_out.card : ℤ) ≤ ∑ e ∈ O_out, endpointSum φh e := by
    calc (L : ℤ) * (p : ℤ) * (O_out.card : ℤ)
        = ∑ _e ∈ O_out, (L : ℤ) * (p : ℤ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ ∑ e ∈ O_out, endpointSum φh e := Finset.sum_le_sum h_edge_out
  have h_edge_Ri : ∀ (i : Fin b) (e : Sym2 (Fin n)), e ∈ R i →
      endpointSum (fun v => a (lbl v) i) e ≤ (L : ℤ) * (q : ℤ) ∧
      (L : ℤ) * (p : ℤ) + endpointSum (fun v => a (lbl v) i) e ≤
        (L : ℤ) * (q : ℤ) + endpointSum φh e := by
    intro i e heRi
    have heG : e ∈ G.edgeSet := (hR_feas i).1 e heRi
    rcases exists_endpoints_of_mem_edgeSet heG with ⟨u, w, _, rfl, hend⟩
    rw [hend, hend]
    have hu : i ∈ lbl u := (mem_lbl_iff R u i).mpr ⟨Sym2.mk u w, heRi, Sym2.mem_mk_left u w⟩
    have hw : i ∈ lbl w := (mem_lbl_iff R w i).mpr ⟨Sym2.mk u w, heRi, Sym2.mem_mk_right u w⟩
    have hjcov : ∀ j, j < i → j ∈ lbl u ∨ j ∈ lbl w := by
      intro j hj
      have hnot : ∀ k, k ≤ j → Sym2.mk u w ∉ R k := by
        intro k hk
        exact Finset.disjoint_right.mp (hR_disj k i (lt_of_le_of_lt hk hj)) heRi
      rcases hR_max j (Sym2.mk u w) heG hnot with ⟨f, hfR, v, hve, hvf⟩
      rcases Sym2.mem_iff.mp hve with hvu | hvw
      · subst hvu
        exact Or.inl ((mem_lbl_iff R v j).mpr ⟨f, hfR, hvf⟩)
      · subst hvw
        exact Or.inr ((mem_lbl_iff R v j).mpr ⟨f, hfR, hvf⟩)
    have hboth := hyz (lbl u) (lbl w) i hu hw hjcov
    exact ⟨hboth.1, by linarith [hboth.2]⟩
  have h_round : ∀ i : Fin b,
      (L : ℤ) * (p : ℤ) * ((R i ∩ O).card : ℤ) + ∑ e ∈ R i, endpointSum (fun v => a (lbl v) i) e ≤
      (L : ℤ) * (q : ℤ) * ((R i).card : ℤ) + ∑ e ∈ R i ∩ O, endpointSum φh e := by
    intro i
    have h1 : ∑ e ∈ R i ∩ O, ((L : ℤ) * (p : ℤ) + endpointSum (fun v => a (lbl v) i) e) ≤
        ∑ e ∈ R i ∩ O, ((L : ℤ) * (q : ℤ) + endpointSum φh e) :=
      Finset.sum_le_sum fun e he => (h_edge_Ri i e (Finset.mem_inter.mp he).1).2
    have h2 : ∑ e ∈ R i \ O, endpointSum (fun v => a (lbl v) i) e ≤
        ∑ _e ∈ R i \ O, (L : ℤ) * (q : ℤ) :=
      Finset.sum_le_sum fun e he => (h_edge_Ri i e (Finset.mem_sdiff.mp he).1).1
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
      nsmul_eq_mul, nsmul_eq_mul] at h1
    rw [Finset.sum_const, nsmul_eq_mul] at h2
    have hdisj_part : Disjoint (R i ∩ O) (R i \ O) := by
      rw [Finset.disjoint_left]
      intro e he1 he2
      exact (Finset.mem_sdiff.mp he2).2 (Finset.mem_inter.mp he1).2
    have hunion_part : (R i ∩ O) ∪ (R i \ O) = R i := by
      ext e
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      tauto
    have hsum_part : ∑ e ∈ R i, endpointSum (fun v => a (lbl v) i) e =
        (∑ e ∈ R i ∩ O, endpointSum (fun v => a (lbl v) i) e) +
        (∑ e ∈ R i \ O, endpointSum (fun v => a (lbl v) i) e) := by
      conv_lhs => rw [← hunion_part]
      exact Finset.sum_union hdisj_part
    have hcard_part : ((R i).card : ℤ) = ((R i ∩ O).card : ℤ) + ((R i \ O).card : ℤ) := by
      conv_lhs => rw [← hunion_part]
      rw [Finset.card_union_of_disjoint hdisj_part]
      push_cast
      rfl
    have hmul_p : (L : ℤ) * (p : ℤ) * ((R i ∩ O).card : ℤ) =
        ((R i ∩ O).card : ℤ) * ((L : ℤ) * (p : ℤ)) := by ring
    have hmul_q : (L : ℤ) * (q : ℤ) * ((R i).card : ℤ) =
        ((R i ∩ O).card : ℤ) * ((L : ℤ) * (q : ℤ)) +
        ((R i \ O).card : ℤ) * ((L : ℤ) * (q : ℤ)) := by
      rw [hcard_part]
      ring
    linarith
  have h_sum_rounds := Finset.sum_le_sum (s := Finset.univ) (fun i _ => h_round i)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h_sum_rounds
  have h_sum_a : ∑ i : Fin b, ∑ e ∈ R i, endpointSum (fun v => a (lbl v) i) e =
      ∑ v : Fin n, ∑ i ∈ lbl v, a (lbl v) i := by
    simp_rw [sum_endpointSum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp_rw [degreeAt_Ri_cast hR_feas v]
    simp [lbl, Finset.sum_filter]
  have h_sum_O_ub : ∑ e ∈ O, endpointSum φh e ≤ ∑ v : Fin n, ∑ i ∈ lbl v, a (lbl v) i := by
    rw [sum_endpointSum]
    refine Finset.sum_le_sum fun v _ => ?_
    have hdeg_le : (OMA.S_mo_148821.degreeAt O v : ℤ) ≤ (b : ℤ) := by exact_mod_cast hO_deg v
    have hh_nonneg : (0 : ℤ) ≤ φh v := Nat.cast_nonneg _
    exact le_trans (mul_le_mul_of_nonneg_right hdeg_le hh_nonneg) (hvtx (lbl v))
  have h_main_int : (L : ℤ) * ((p * O.card : ℕ) : ℤ) ≤
      (L : ℤ) * ((q * ∑ i : Fin b, (R i).card : ℕ) : ℤ) := by
    push_cast
    have h_lhs : (L : ℤ) * ((p : ℤ) * (O.card : ℤ)) =
        (L : ℤ) * (p : ℤ) * (O_out.card : ℤ) +
        (L : ℤ) * (p : ℤ) * ∑ i : Fin b, ((R i ∩ O).card : ℤ) := by
      rw [hO_card]
      ring
    have h_rhs : (L : ℤ) * ((q : ℤ) * ∑ i : Fin b, ((R i).card : ℤ)) =
        (L : ℤ) * (q : ℤ) * ∑ i : Fin b, ((R i).card : ℤ) := by ring
    linarith [hO_sum_h, h_sum_out, h_sum_rounds, h_sum_a, h_sum_O_ub]
  have hL_pos : (0 : ℤ) < (L : ℤ) := by exact_mod_cast hL
  have h_cancel : ((p * O.card : ℕ) : ℤ) ≤ ((q * ∑ i : Fin b, (R i).card : ℕ) : ℤ) :=
    le_of_mul_le_mul_left h_main_int hL_pos
  exact_mod_cast h_cancel

/-! ## Part 2: Rational Farkas Lemma via Fourier-Motzkin Elimination -/

private def rowTriEquiv {R : Type} (v : R → ℚ) :
    {r : R // v r = 0} ⊕ ({r : R // 0 < v r} ⊕ {r : R // v r < 0}) ≃ R where
  toFun
    | Sum.inl z => z.1
    | Sum.inr (Sum.inl p) => p.1
    | Sum.inr (Sum.inr n) => n.1
  invFun r :=
    if hz : v r = 0 then Sum.inl ⟨r, hz⟩
    else if hp : 0 < v r then Sum.inr (Sum.inl ⟨r, hp⟩)
    else Sum.inr (Sum.inr ⟨r, lt_of_le_of_ne (le_of_not_gt hp) hz⟩)
  left_inv x := by
    rcases x with ⟨r, hz⟩ | (⟨r, hp⟩ | ⟨r, hn⟩)
    · simp [hz]
    · have hne : v r ≠ 0 := ne_of_gt hp
      simp [hne, hp]
    · have hne : v r ≠ 0 := ne_of_lt hn
      have hnp : ¬ 0 < v r := not_lt_of_gt hn
      simp [hne, hnp]
  right_inv r := by
    by_cases hz : v r = 0
    · simp [hz]
    · by_cases hp : 0 < v r
      · simp [hz, hp]
      · simp [hz, hp]

private theorem rat_farkas : ∀ (d : ℕ) {R : Type} [Fintype R] [DecidableEq R]
    (A : R → Fin d → ℚ) (c : R → ℚ),
    (∃ x : Fin d → ℚ, ∀ r, ∑ j, A r j * x j ≤ c r) ∨
    (∃ y : R → ℚ, (∀ r, 0 ≤ y r) ∧ (∀ j, ∑ r, y r * A r j = 0) ∧ ∑ r, y r * c r < 0) := by
  intro d
  induction d with
  | zero =>
    intro R _ _ A c
    by_cases hc : ∀ r : R, 0 ≤ c r
    · refine Or.inl ⟨fun j => Fin.elim0 j, fun r => ?_⟩
      simp [hc r]
    · have hex : ∃ r0 : R, c r0 < 0 := by
        rcases Classical.not_forall.mp hc with ⟨r0, hr0⟩
        exact ⟨r0, lt_of_not_ge hr0⟩
      rcases hex with ⟨r0, hr0⟩
      refine Or.inr ⟨fun r => if r = r0 then 1 else 0, ?_, ?_, ?_⟩
      · intro r
        dsimp
        split_ifs <;> norm_num
      · intro j
        exact Fin.elim0 j
      · simp [hr0]
  | succ d ih =>
    intro R _ _ A c
    let last : Fin (d + 1) := Fin.last d
    let Z := {r : R // A r last = 0}
    let P := {r : R // 0 < A r last}
    let N := {r : R // A r last < 0}
    let R' := Z ⊕ (P × N)
    let A' : R' → Fin d → ℚ := fun idx j =>
      match idx with
      | Sum.inl z => A z.1 j.castSucc
      | Sum.inr (p, n) => (-A n.1 last) * A p.1 j.castSucc + A p.1 last * A n.1 j.castSucc
    let c' : R' → ℚ := fun idx =>
      match idx with
      | Sum.inl z => c z.1
      | Sum.inr (p, n) => (-A n.1 last) * c p.1 + A p.1 last * c n.1
    rcases ih A' c' with ⟨x', hx'⟩ | ⟨y', hy'_nonneg, hy'_zero, hy'_neg⟩
    · refine Or.inl ?_
      let s : R → ℚ := fun r => ∑ j : Fin d, A r j.castSucc * x' j
      let LB : N → ℚ := fun n => (s n.1 - c n.1) / (-A n.1 last)
      let UB : P → ℚ := fun p => (c p.1 - s p.1) / A p.1 last
      have h_lb_ub : ∀ (p : P) (n : N), LB n ≤ UB p := by
        intro p n
        have hpn := hx' (Sum.inr (p, n))
        have hsum_pn : ∑ j : Fin d, A' (Sum.inr (p, n)) j * x' j =
            (-A n.1 last) * s p.1 + A p.1 last * s n.1 := by
          simp only [A', s, Finset.mul_sum]
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => by ring
        rw [hsum_pn] at hpn
        have hap : 0 < A p.1 last := p.2
        have han : 0 < -A n.1 last := neg_pos.mpr n.2
        have hprod : 0 < A p.1 last * (-A n.1 last) := mul_pos hap han
        have hmul_lb : A p.1 last * (-A n.1 last) * LB n = A p.1 last * (s n.1 - c n.1) := by
          dsimp [LB]
          rw [mul_assoc, mul_div_cancel₀ _ (ne_of_gt han)]
        have hmul_ub : A p.1 last * (-A n.1 last) * UB p = (-A n.1 last) * (c p.1 - s p.1) := by
          dsimp [UB]
          rw [mul_comm (A p.1 last) (-A n.1 last), mul_assoc, mul_div_cancel₀ _ (ne_of_gt hap)]
        have hmul_le : A p.1 last * (-A n.1 last) * LB n ≤ A p.1 last * (-A n.1 last) * UB p := by
          rw [hmul_lb, hmul_ub]
          dsimp [c'] at hpn
          linarith
        exact le_of_mul_le_mul_left hmul_le hprod
      have hex_last : ∃ x_last : ℚ, (∀ n : N, LB n ≤ x_last) ∧ (∀ p : P, x_last ≤ UB p) := by
        by_cases hN : (Finset.univ : Finset N).Nonempty
        · refine ⟨(Finset.univ : Finset N).sup' hN LB, ?_, ?_⟩
          · intro n
            exact Finset.le_sup' LB (Finset.mem_univ n)
          · intro p
            exact Finset.sup'_le hN LB fun n _ => h_lb_ub p n
        · by_cases hP : (Finset.univ : Finset P).Nonempty
          · refine ⟨(Finset.univ : Finset P).inf' hP UB, ?_, ?_⟩
            · intro n
              exact False.elim (hN ⟨n, Finset.mem_univ n⟩)
            · intro p
              exact Finset.inf'_le UB (Finset.mem_univ p)
          · refine ⟨0, ?_, ?_⟩
            · intro n
              exact False.elim (hN ⟨n, Finset.mem_univ n⟩)
            · intro p
              exact False.elim (hP ⟨p, Finset.mem_univ p⟩)
      rcases hex_last with ⟨x_last, hLB, hUB⟩
      refine ⟨Fin.snoc x' x_last, fun r => ?_⟩
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      change s r + A r last * x_last ≤ c r
      rcases lt_trichotomy (A r last) 0 with hn | hz | hp
      · have h1 := hLB ⟨r, hn⟩
        have han : 0 < -A r last := neg_pos.mpr hn
        have h2 : (-A r last) * LB ⟨r, hn⟩ ≤ (-A r last) * x_last :=
          mul_le_mul_of_nonneg_left h1 (le_of_lt han)
        dsimp [LB] at h2
        rw [mul_div_cancel₀ _ (ne_of_gt han)] at h2
        linarith
      · have h1 := hx' (Sum.inl ⟨r, hz⟩)
        dsimp [A', c'] at h1
        change s r ≤ c r at h1
        rw [hz]
        linarith
      · have h1 := hUB ⟨r, hp⟩
        have h2 : A r last * x_last ≤ A r last * UB ⟨r, hp⟩ :=
          mul_le_mul_of_nonneg_left h1 (le_of_lt hp)
        dsimp [UB] at h2
        rw [mul_div_cancel₀ _ (ne_of_gt hp)] at h2
        linarith
    · refine Or.inr ?_
      let eR := rowTriEquiv (fun r => A r last)
      let y : R → ℚ := fun r =>
        match eR.symm r with
        | Sum.inl z => y' (Sum.inl z)
        | Sum.inr (Sum.inl p) => ∑ n : N, y' (Sum.inr (p, n)) * (-A n.1 last)
        | Sum.inr (Sum.inr n) => ∑ p : P, y' (Sum.inr (p, n)) * A p.1 last
      have hy_nonneg : ∀ r : R, 0 ≤ y r := by
        intro r
        dsimp [y]
        rcases eR.symm r with z | (p | n)
        · exact hy'_nonneg (Sum.inl z)
        · exact Finset.sum_nonneg fun n _ =>
            mul_nonneg (hy'_nonneg (Sum.inr (p, n))) (le_of_lt (neg_pos.mpr n.2))
        · exact Finset.sum_nonneg fun p _ =>
            mul_nonneg (hy'_nonneg (Sum.inr (p, n))) (le_of_lt p.2)
      have h_sum_φ : ∀ φ : R → ℚ,
          ∑ r : R, y r * φ r =
            (∑ z : Z, y' (Sum.inl z) * φ z.1) +
            ∑ p : P, ∑ n : N,
              y' (Sum.inr (p, n)) * ((-A n.1 last) * φ p.1 + A p.1 last * φ n.1) := by
        intro φ
        rw [← eR.sum_comp, Fintype.sum_sum_type, Fintype.sum_sum_type]
        have hz_sum : ∑ z : Z, y (eR (Sum.inl z)) * φ (eR (Sum.inl z)) =
            ∑ z : Z, y' (Sum.inl z) * φ z.1 := by
          refine Finset.sum_congr rfl fun z _ => ?_
          simp only [y, Equiv.symm_apply_apply]
          rfl
        have hp_sum : ∑ p : P, y (eR (Sum.inr (Sum.inl p))) * φ (eR (Sum.inr (Sum.inl p))) =
            ∑ p : P, ∑ n : N, y' (Sum.inr (p, n)) * (-A n.1 last) * φ p.1 := by
          refine Finset.sum_congr rfl fun p _ => ?_
          simp only [y, Equiv.symm_apply_apply]
          dsimp [eR, rowTriEquiv]
          rw [Finset.sum_mul]
        have hn_sum : ∑ n : N, y (eR (Sum.inr (Sum.inr n))) * φ (eR (Sum.inr (Sum.inr n))) =
            ∑ p : P, ∑ n : N, y' (Sum.inr (p, n)) * A p.1 last * φ n.1 := by
          rw [← Finset.sum_comm]
          refine Finset.sum_congr rfl fun n _ => ?_
          simp only [y, Equiv.symm_apply_apply]
          dsimp [eR, rowTriEquiv]
          rw [Finset.sum_mul]
        rw [hz_sum, hp_sum, hn_sum]
        congr 1
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun n _ => by ring
      refine ⟨y, hy_nonneg, ?_, ?_⟩
      · intro j
        refine Fin.lastCases ?_ ?_ j
        · rw [h_sum_φ (fun r => A r last)]
          have hz0 : ∑ z : Z, y' (Sum.inl z) * A z.1 last = 0 := by
            refine Finset.sum_eq_zero fun z _ => ?_
            rw [z.2, mul_zero]
          have hpn0 : ∑ p : P, ∑ n : N,
              y' (Sum.inr (p, n)) * ((-A n.1 last) * A p.1 last + A p.1 last * A n.1 last) = 0 := by
            refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun n _ => by ring
          rw [hz0, hpn0, add_zero]
        · intro i
          rw [h_sum_φ (fun r => A r i.castSucc)]
          have h_eq := hy'_zero i
          rw [Fintype.sum_sum_type, Fintype.sum_prod_type] at h_eq
          exact h_eq
      · rw [h_sum_φ c]
        rw [Fintype.sum_sum_type, Fintype.sum_prod_type] at hy'_neg
        exact hy'_neg

private theorem rat_farkas_fintype {R V : Type} [Fintype R] [DecidableEq R] [Fintype V] [DecidableEq V]
    (A : R → V → ℚ) (c : R → ℚ) :
    (∃ x : V → ℚ, ∀ r, ∑ v, A r v * x v ≤ c r) ∨
    (∃ y : R → ℚ, (∀ r, 0 ≤ y r) ∧ (∀ v, ∑ r, y r * A r v = 0) ∧ ∑ r, y r * c r < 0) := by
  let eV : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  rcases rat_farkas (Fintype.card V) (fun r j => A r (eV.symm j)) c with ⟨x', hx'⟩ | ⟨y, hy0, hyA, hyc⟩
  · refine Or.inl ⟨fun v => x' (eV v), fun r => ?_⟩
    have hsum : ∑ v : V, A r v * x' (eV v) = ∑ j : Fin (Fintype.card V), A r (eV.symm j) * x' j := by
      rw [← eV.symm.sum_comp]
      simp
    rw [hsum]
    exact hx' r
  · refine Or.inr ⟨y, hy0, fun v => ?_, hyc⟩
    have hv := hyA (eV v)
    simp only [Equiv.symm_apply_apply] at hv
    exact hv

/-! ## Part 3a: LP Formulation and Dual Integer Weights -/

private abbrev ValidX (b : ℕ) :=
  {st : OMA.S_mo_148821.Label b × OMA.S_mo_148821.Label b //
    ∀ i : Fin b, i ∈ st.1 ∨ i ∈ st.2}

private abbrev ValidYZ (b : ℕ) :=
  {sti : OMA.S_mo_148821.Label b × OMA.S_mo_148821.Label b × Fin b //
    sti.2.2 ∈ sti.1 ∧ sti.2.2 ∈ sti.2.1 ∧
    ∀ j : Fin b, j < sti.2.2 → j ∈ sti.1 ∨ j ∈ sti.2.1}

private structure DualWeights (b p q : ℕ) where
  N : OMA.S_mo_148821.Label b → ℕ
  X : ValidX b → ℕ
  Y : ValidYZ b → ℕ
  Z : ValidYZ b → ℕ
  eq_Ri : ∀ (s : OMA.S_mo_148821.Label b) (i : Fin b), i ∈ s →
    (∑ e : ValidYZ b, if e.1.1 = s ∧ e.1.2.2 = i then Y e + Z e else 0) +
    (∑ e : ValidYZ b, if e.1.2.1 = s ∧ e.1.2.2 = i then Y e + Z e else 0) = N s
  le_O : ∀ (s : OMA.S_mo_148821.Label b),
    (∑ e : ValidX b, if e.1.1 = s then X e else 0) +
    (∑ e : ValidX b, if e.1.2 = s then X e else 0) +
    (∑ e : ValidYZ b, if e.1.1 = s then Y e else 0) +
    (∑ e : ValidYZ b, if e.1.2.1 = s then Y e else 0) ≤ b * N s
  strict_obj :
    q * ((∑ e : ValidYZ b, Y e) + (∑ e : ValidYZ b, Z e)) <
    p * ((∑ e : ValidX b, X e) + (∑ e : ValidYZ b, Y e))

private lemma exists_int_of_den_dvd {r : ℚ} {L : ℕ} (hdvd : r.den ∣ L) :
    ∃ z : ℤ, (z : ℚ) = (L : ℚ) * r := by
  rcases hdvd with ⟨k, rfl⟩
  refine ⟨(k : ℤ) * r.num, ?_⟩
  have hden_ne : (r.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr r.den_nz
  have hmul : r * (r.den : ℚ) = (r.num : ℚ) := by
    calc r * (r.den : ℚ)
        = ((r.num : ℚ) / (r.den : ℚ)) * (r.den : ℚ) := by rw [Rat.num_div_den]
      _ = (r.num : ℚ) := div_mul_cancel₀ _ hden_ne
  push_cast
  rw [← hmul]
  ring

private lemma exists_nat_of_nonneg_of_den_dvd {r : ℚ} {L : ℕ} (hr : 0 ≤ r) (hdvd : r.den ∣ L) :
    ∃ m : ℕ, (m : ℚ) = (L : ℚ) * r := by
  rcases exists_int_of_den_dvd hdvd with ⟨z, hz⟩
  have hz_q : (0 : ℚ) ≤ (z : ℚ) := by
    rw [hz]
    exact mul_nonneg (Nat.cast_nonneg L) hr
  have hz0 : 0 ≤ z := by exact_mod_cast hz_q
  refine ⟨z.toNat, ?_⟩
  have hcast : ((z.toNat : ℤ) : ℚ) = (z : ℚ) := by rw [Int.toNat_of_nonneg hz0]
  exact_mod_cast hcast.trans hz

private abbrev LPVar (b : ℕ) :=
  OMA.S_mo_148821.Label b ⊕ (OMA.S_mo_148821.Label b × Fin b)

private abbrev LPCon (b : ℕ) :=
  OMA.S_mo_148821.Label b ⊕
  (OMA.S_mo_148821.Label b ⊕
    (ValidX b ⊕ (ValidYZ b ⊕ ValidYZ b)))

private def lpMatrix (b : ℕ) : LPCon b → LPVar b → ℚ
  | Sum.inl s, Sum.inl s' => if s' = s then -1 else 0
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr (Sum.inl s), Sum.inl s' => if s' = s then (b : ℚ) else 0
  | Sum.inr (Sum.inl s), Sum.inr (s', i') => if s' = s ∧ i' ∈ s then -1 else 0
  | Sum.inr (Sum.inr (Sum.inl e)), Sum.inl s' =>
      (if e.1.1 = s' then -1 else 0) + (if e.1.2 = s' then -1 else 0)
  | Sum.inr (Sum.inr (Sum.inl _)), Sum.inr _ => 0
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl e))), Sum.inl s' =>
      (if e.1.1 = s' then -1 else 0) + (if e.1.2.1 = s' then -1 else 0)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl e))), Sum.inr (s', i') =>
      (if e.1.1 = s' ∧ e.1.2.2 = i' then 1 else 0) +
      (if e.1.2.1 = s' ∧ e.1.2.2 = i' then 1 else 0)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))), Sum.inl _ => 0
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr e))), Sum.inr (s', i') =>
      (if e.1.1 = s' ∧ e.1.2.2 = i' then 1 else 0) +
      (if e.1.2.1 = s' ∧ e.1.2.2 = i' then 1 else 0)

private def lpRhs (b p q : ℕ) : LPCon b → ℚ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr (Sum.inl _)) => -(p : ℚ)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => (q : ℚ) - (p : ℚ)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => (q : ℚ)

private lemma lp_primal_to_certified {b p q : ℕ}
    (x : LPVar b → ℚ) (hx : ∀ r : LPCon b, ∑ v : LPVar b, lpMatrix b r v * x v ≤ lpRhs b p q r) :
    OMA.S_mo_148821.certified b p q := by
  have hx_nh : ∀ s : OMA.S_mo_148821.Label b, 0 ≤ x (Sum.inl s) := by
    intro s
    have hrow := hx (Sum.inl s)
    rw [Fintype.sum_sum_type] at hrow
    simp only [lpMatrix, lpRhs, ite_mul, neg_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_const_zero, add_zero] at hrow
    linarith
  let L : ℕ := ∏ v : LPVar b, (x v).den
  have hL : 0 < L := Finset.prod_pos fun v _ => (x v).den_pos
  have hdvd : ∀ v : LPVar b, (x v).den ∣ L :=
    fun v => Finset.dvd_prod_of_mem (fun u => (x u).den) (Finset.mem_univ v)
  have hex_h : ∀ s : OMA.S_mo_148821.Label b, ∃ m : ℕ, (m : ℚ) = (L : ℚ) * x (Sum.inl s) :=
    fun s => exists_nat_of_nonneg_of_den_dvd (hx_nh s) (hdvd (Sum.inl s))
  have hex_a : ∀ (s : OMA.S_mo_148821.Label b) (i : Fin b),
      ∃ z : ℤ, (z : ℚ) = (L : ℚ) * x (Sum.inr (s, i)) :=
    fun s i => exists_int_of_den_dvd (hdvd (Sum.inr (s, i)))
  choose h hh using hex_h
  choose a ha using hex_a
  have hL_nonneg : (0 : ℚ) ≤ (L : ℚ) := Nat.cast_nonneg L
  refine ⟨L, h, a, hL, ?_, ?_, ?_⟩
  · intro s
    have hrow := hx (Sum.inr (Sum.inl s))
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type] at hrow
    have h1 : ∑ s' : OMA.S_mo_148821.Label b, lpMatrix b (Sum.inr (Sum.inl s)) (Sum.inl s') * x (Sum.inl s') =
        (b : ℚ) * x (Sum.inl s) := by
      simp [lpMatrix, ite_mul]
    have h2 : ∑ s' : OMA.S_mo_148821.Label b, ∑ i' : Fin b,
        lpMatrix b (Sum.inr (Sum.inl s)) (Sum.inr (s', i')) * x (Sum.inr (s', i')) =
        - ∑ i' ∈ s, x (Sum.inr (s, i')) := by
      have hinner : ∀ s' : OMA.S_mo_148821.Label b,
          ∑ i' : Fin b, lpMatrix b (Sum.inr (Sum.inl s)) (Sum.inr (s', i')) * x (Sum.inr (s', i')) =
          if s' = s then - ∑ i' ∈ s, x (Sum.inr (s', i')) else 0 := by
        intro s'
        by_cases hs : s' = s
        · subst hs
          simp [lpMatrix, Finset.sum_neg_distrib]
        · simp [lpMatrix, hs]
      simp_rw [hinner]
      simp
    rw [h1, h2] at hrow
    dsimp [lpRhs] at hrow
    have hmul := mul_le_mul_of_nonneg_left hrow hL_nonneg
    have hq_ineq : ((b : ℤ) * (h s : ℤ) : ℚ) ≤ (∑ i ∈ s, a s i : ℚ) := by
      push_cast
      simp_rw [hh, ha, ← Finset.mul_sum]
      linarith
    exact_mod_cast hq_ineq
  · intro s t hcov
    let e : ValidX b := ⟨(s, t), hcov⟩
    have hrow := hx (Sum.inr (Sum.inr (Sum.inl e)))
    rw [Fintype.sum_sum_type] at hrow
    have h1 : ∑ s' : OMA.S_mo_148821.Label b,
        lpMatrix b (Sum.inr (Sum.inr (Sum.inl e))) (Sum.inl s') * x (Sum.inl s') =
        - x (Sum.inl s) - x (Sum.inl t) := by
      simp only [lpMatrix, e, add_mul, Finset.sum_add_distrib, ite_mul, neg_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      ring
    have h2 : ∑ p' : OMA.S_mo_148821.Label b × Fin b,
        lpMatrix b (Sum.inr (Sum.inr (Sum.inl e))) (Sum.inr p') * x (Sum.inr p') = 0 := by
      simp [lpMatrix]
    rw [h1, h2] at hrow
    dsimp [lpRhs] at hrow
    have hmul := mul_le_mul_of_nonneg_left hrow hL_nonneg
    have hq_ineq : ((L * p : ℕ) : ℚ) ≤ ((h s + h t : ℕ) : ℚ) := by
      push_cast
      rw [hh, hh]
      linarith
    exact_mod_cast hq_ineq
  · intro s t i his hit hjcov
    let e : ValidYZ b := ⟨(s, t, i), his, hit, hjcov⟩
    have h_pair_a : ∀ r_a : LPVar b → ℚ,
        (∀ s' i', r_a (Sum.inr (s', i')) =
          (if s = s' ∧ i = i' then 1 else 0) + (if t = s' ∧ i = i' then 1 else 0)) →
        ∑ p' : OMA.S_mo_148821.Label b × Fin b, r_a (Sum.inr p') * x (Sum.inr p') =
        x (Sum.inr (s, i)) + x (Sum.inr (t, i)) := by
      intro r_a hra
      rw [Fintype.sum_prod_type]
      simp_rw [hra, add_mul, Finset.sum_add_distrib]
      have hsingle : ∀ u : OMA.S_mo_148821.Label b,
          ∑ s' : OMA.S_mo_148821.Label b, ∑ i' : Fin b,
            (if u = s' ∧ i = i' then (1 : ℚ) else 0) * x (Sum.inr (s', i')) =
          x (Sum.inr (u, i)) := by
        intro u
        have hin : ∀ s' : OMA.S_mo_148821.Label b,
            ∑ i' : Fin b, (if u = s' ∧ i = i' then (1 : ℚ) else 0) * x (Sum.inr (s', i')) =
            if u = s' then x (Sum.inr (s', i)) else 0 := by
          intro s'
          by_cases hu : u = s'
          · subst hu
            simp
          · simp [hu]
        simp_rw [hin]
        simp
      rw [hsingle s, hsingle t]
    constructor
    · have hrow := hx (Sum.inr (Sum.inr (Sum.inr (Sum.inr e))))
      rw [Fintype.sum_sum_type] at hrow
      have h1 : ∑ s' : OMA.S_mo_148821.Label b,
          lpMatrix b (Sum.inr (Sum.inr (Sum.inr (Sum.inr e)))) (Sum.inl s') * x (Sum.inl s') = 0 := by
        simp [lpMatrix]
      have h2 := h_pair_a (lpMatrix b (Sum.inr (Sum.inr (Sum.inr (Sum.inr e)))))
        (fun s' i' => rfl)
      rw [h1, h2] at hrow
      dsimp [lpRhs] at hrow
      have hmul := mul_le_mul_of_nonneg_left hrow hL_nonneg
      have hq_ineq : ((a s i + a t i : ℤ) : ℚ) ≤ (((L : ℤ) * (q : ℤ) : ℤ) : ℚ) := by
        push_cast
        rw [ha, ha]
        linarith
      exact_mod_cast hq_ineq
    · have hrow := hx (Sum.inr (Sum.inr (Sum.inr (Sum.inl e))))
      rw [Fintype.sum_sum_type] at hrow
      have h1 : ∑ s' : OMA.S_mo_148821.Label b,
          lpMatrix b (Sum.inr (Sum.inr (Sum.inr (Sum.inl e)))) (Sum.inl s') * x (Sum.inl s') =
          - x (Sum.inl s) - x (Sum.inl t) := by
        simp only [lpMatrix, e, add_mul, Finset.sum_add_distrib, ite_mul, neg_mul, one_mul, zero_mul,
          Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
        ring
      have h2 := h_pair_a (lpMatrix b (Sum.inr (Sum.inr (Sum.inr (Sum.inl e)))))
        (fun s' i' => rfl)
      rw [h1, h2] at hrow
      dsimp [lpRhs] at hrow
      have hmul := mul_le_mul_of_nonneg_left hrow hL_nonneg
      have hq_ineq : (((L : ℤ) * (p : ℤ) + a s i + a t i : ℤ) : ℚ) ≤
          (((L : ℤ) * (q : ℤ) + h s + h t : ℤ) : ℚ) := by
        push_cast
        rw [ha, ha, hh, hh]
        linarith
      exact_mod_cast hq_ineq

private lemma lp_dual_to_weights {b p q : ℕ}
    (y : LPCon b → ℚ) (hy0 : ∀ r, 0 ≤ y r)
    (hyA : ∀ v : LPVar b, ∑ r : LPCon b, y r * lpMatrix b r v = 0)
    (hyc : ∑ r : LPCon b, y r * lpRhs b p q r < 0) :
    Nonempty (DualWeights b p q) := by
  let D : ℕ := ∏ r : LPCon b, (y r).den
  have hD : 0 < D := Finset.prod_pos fun r _ => (y r).den_pos
  have hdvd : ∀ r : LPCon b, (y r).den ∣ D :=
    fun r => Finset.dvd_prod_of_mem (fun u => (y u).den) (Finset.mem_univ r)
  have hex_W : ∀ r : LPCon b, ∃ m : ℕ, (m : ℚ) = (D : ℚ) * y r :=
    fun r => exists_nat_of_nonneg_of_den_dvd (hy0 r) (hdvd r)
  choose W hW using hex_W
  have hWA : ∀ v : LPVar b, ∑ r : LPCon b, (W r : ℚ) * lpMatrix b r v = 0 := by
    intro v
    simp_rw [hW, mul_assoc, ← Finset.mul_sum, hyA v, mul_zero]
  have hWc : ∑ r : LPCon b, (W r : ℚ) * lpRhs b p q r < 0 := by
    simp_rw [hW, mul_assoc, ← Finset.mul_sum]
    have hD_pos : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hD
    exact mul_neg_of_pos_of_neg hD_pos hyc
  let N_nh : OMA.S_mo_148821.Label b → ℕ := fun s => W (Sum.inl s)
  let N : OMA.S_mo_148821.Label b → ℕ := fun s => W (Sum.inr (Sum.inl s))
  let X : ValidX b → ℕ := fun e => W (Sum.inr (Sum.inr (Sum.inl e)))
  let Y : ValidYZ b → ℕ := fun e => W (Sum.inr (Sum.inr (Sum.inr (Sum.inl e))))
  let Z : ValidYZ b → ℕ := fun e => W (Sum.inr (Sum.inr (Sum.inr (Sum.inr e))))
  refine ⟨⟨N, X, Y, Z, ?_, ?_, ?_⟩⟩
  · intro s i his
    have hcol := hWA (Sum.inr (s, i))
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type] at hcol
    have hc1 : ∑ s' : OMA.S_mo_148821.Label b, (W (Sum.inl s') : ℚ) * lpMatrix b (Sum.inl s') (Sum.inr (s, i)) = 0 := by
      simp [lpMatrix]
    have hc2 : ∑ s' : OMA.S_mo_148821.Label b,
        (W (Sum.inr (Sum.inl s')) : ℚ) * lpMatrix b (Sum.inr (Sum.inl s')) (Sum.inr (s, i)) = -(N s : ℚ) := by
      have hin : ∀ s' : OMA.S_mo_148821.Label b,
          (W (Sum.inr (Sum.inl s')) : ℚ) * lpMatrix b (Sum.inr (Sum.inl s')) (Sum.inr (s, i)) =
          if s = s' then -(N s' : ℚ) else 0 := by
        intro s'
        by_cases hs : s = s'
        · subst hs
          simp [lpMatrix, his, N]
        · simp [lpMatrix, hs]
      simp_rw [hin]
      simp
    have hc3 : ∑ e : ValidX b,
        (W (Sum.inr (Sum.inr (Sum.inl e))) : ℚ) * lpMatrix b (Sum.inr (Sum.inr (Sum.inl e))) (Sum.inr (s, i)) = 0 := by
      simp [lpMatrix]
    have hc4 : ∑ e : ValidYZ b,
        (W (Sum.inr (Sum.inr (Sum.inr (Sum.inl e)))) : ℚ) *
          lpMatrix b (Sum.inr (Sum.inr (Sum.inr (Sum.inl e)))) (Sum.inr (s, i)) =
        (∑ e : ValidYZ b, if e.1.1 = s ∧ e.1.2.2 = i then (Y e : ℚ) else 0) +
        (∑ e : ValidYZ b, if e.1.2.1 = s ∧ e.1.2.2 = i then (Y e : ℚ) else 0) := by
      simp only [lpMatrix, Y, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
    have hc5 : ∑ e : ValidYZ b,
        (W (Sum.inr (Sum.inr (Sum.inr (Sum.inr e)))) : ℚ) *
          lpMatrix b (Sum.inr (Sum.inr (Sum.inr (Sum.inr e)))) (Sum.inr (s, i)) =
        (∑ e : ValidYZ b, if e.1.1 = s ∧ e.1.2.2 = i then (Z e : ℚ) else 0) +
        (∑ e : ValidYZ b, if e.1.2.1 = s ∧ e.1.2.2 = i then (Z e : ℚ) else 0) := by
      simp only [lpMatrix, Z, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
    rw [hc1, hc2, hc3, hc4, hc5] at hcol
    have hq_eq : (((∑ e : ValidYZ b, if e.1.1 = s ∧ e.1.2.2 = i then Y e + Z e else 0) +
        (∑ e : ValidYZ b, if e.1.2.1 = s ∧ e.1.2.2 = i then Y e + Z e else 0) : ℕ) : ℚ) =
        (N s : ℚ) := by
      have hcast1 : ((∑ e : ValidYZ b, if e.1.1 = s ∧ e.1.2.2 = i then Y e + Z e else 0 : ℕ) : ℚ) =
          (∑ e : ValidYZ b, if e.1.1 = s ∧ e.1.2.2 = i then (Y e : ℚ) else 0) +
          (∑ e : ValidYZ b, if e.1.1 = s ∧ e.1.2.2 = i then (Z e : ℚ) else 0) := by
        rw [Nat.cast_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun e _ => ?_
        split_ifs <;> simp
      have hcast2 : ((∑ e : ValidYZ b, if e.1.2.1 = s ∧ e.1.2.2 = i then Y e + Z e else 0 : ℕ) : ℚ) =
          (∑ e : ValidYZ b, if e.1.2.1 = s ∧ e.1.2.2 = i then (Y e : ℚ) else 0) +
          (∑ e : ValidYZ b, if e.1.2.1 = s ∧ e.1.2.2 = i then (Z e : ℚ) else 0) := by
        rw [Nat.cast_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun e _ => ?_
        split_ifs <;> simp
      rw [Nat.cast_add, hcast1, hcast2]
      linarith
    exact_mod_cast hq_eq
  · intro s
    have hcol := hWA (Sum.inl s)
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type] at hcol
    have hc1 : ∑ s' : OMA.S_mo_148821.Label b,
        (W (Sum.inl s') : ℚ) * lpMatrix b (Sum.inl s') (Sum.inl s) = -(N_nh s : ℚ) := by
      simp [lpMatrix, N_nh, mul_ite]
    have hc2 : ∑ s' : OMA.S_mo_148821.Label b,
        (W (Sum.inr (Sum.inl s')) : ℚ) * lpMatrix b (Sum.inr (Sum.inl s')) (Sum.inl s) =
        (b : ℚ) * (N s : ℚ) := by
      simp [lpMatrix, N, mul_comm]
    have h_ite_neg : ∀ (P : Prop) [Decidable P] (v : ℚ), (if P then -v else 0) = -(if P then v else 0) := by
      intro P _ v
      split_ifs <;> ring
    have hc3 : ∑ e : ValidX b,
        (W (Sum.inr (Sum.inr (Sum.inl e))) : ℚ) * lpMatrix b (Sum.inr (Sum.inr (Sum.inl e))) (Sum.inl s) =
        - (∑ e : ValidX b, if e.1.1 = s then (X e : ℚ) else 0) -
        (∑ e : ValidX b, if e.1.2 = s then (X e : ℚ) else 0) := by
      simp only [lpMatrix, X, mul_add, Finset.sum_add_distrib, mul_ite, mul_neg, mul_one, mul_zero,
        h_ite_neg, Finset.sum_neg_distrib]
      ring
    have hc4 : ∑ e : ValidYZ b,
        (W (Sum.inr (Sum.inr (Sum.inr (Sum.inl e)))) : ℚ) *
          lpMatrix b (Sum.inr (Sum.inr (Sum.inr (Sum.inl e)))) (Sum.inl s) =
        - (∑ e : ValidYZ b, if e.1.1 = s then (Y e : ℚ) else 0) -
        (∑ e : ValidYZ b, if e.1.2.1 = s then (Y e : ℚ) else 0) := by
      simp only [lpMatrix, Y, mul_add, Finset.sum_add_distrib, mul_ite, mul_neg, mul_one, mul_zero,
        h_ite_neg, Finset.sum_neg_distrib]
      ring
    have hc5 : ∑ e : ValidYZ b,
        (W (Sum.inr (Sum.inr (Sum.inr (Sum.inr e)))) : ℚ) *
          lpMatrix b (Sum.inr (Sum.inr (Sum.inr (Sum.inr e)))) (Sum.inl s) = 0 := by
      simp [lpMatrix]
    rw [hc1, hc2, hc3, hc4, hc5] at hcol
    have hnh_nonneg : (0 : ℚ) ≤ (N_nh s : ℚ) := Nat.cast_nonneg _
    have hq_le : (((∑ e : ValidX b, if e.1.1 = s then X e else 0) +
        (∑ e : ValidX b, if e.1.2 = s then X e else 0) +
        (∑ e : ValidYZ b, if e.1.1 = s then Y e else 0) +
        (∑ e : ValidYZ b, if e.1.2.1 = s then Y e else 0) : ℕ) : ℚ) ≤ ((b * N s : ℕ) : ℚ) := by
      push_cast
      linarith
    exact_mod_cast hq_le
  · rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type] at hWc
    simp only [lpRhs, mul_zero, Finset.sum_const_zero, zero_add] at hWc
    change (∑ e : ValidX b, (X e : ℚ) * -(p : ℚ)) +
      ((∑ e : ValidYZ b, (Y e : ℚ) * ((q : ℚ) - (p : ℚ))) +
       (∑ e : ValidYZ b, (Z e : ℚ) * (q : ℚ))) < 0 at hWc
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul] at hWc
    have hq_lt : ((q * ((∑ e : ValidYZ b, Y e) + (∑ e : ValidYZ b, Z e)) : ℕ) : ℚ) <
        ((p * ((∑ e : ValidX b, X e) + (∑ e : ValidYZ b, Y e)) : ℕ) : ℚ) := by
      push_cast
      linarith
    exact_mod_cast hq_lt

private theorem certified_or_dualWeights (b p q : ℕ) :
    OMA.S_mo_148821.certified b p q ∨ Nonempty (DualWeights b p q) := by
  classical
  rcases rat_farkas_fintype (lpMatrix b) (lpRhs b p q) with ⟨x, hx⟩ | ⟨y, hy0, hyA, hyc⟩
  · exact Or.inl (lp_primal_to_certified x hx)
  · exact Or.inr (lp_dual_to_weights y hy0 hyA hyc)

/-! ## Part 3b: Cyclic Blowup Realization (`DualWeights → ¬ guaranteed`) -/

private def shiftVal (M k a : ℕ) : ℕ :=
  if a + k < M then a + k else a + k - M

private def unshiftVal (M k a : ℕ) : ℕ :=
  if k ≤ a then a - k else a + M - k

private lemma shiftVal_lt {M k a : ℕ} (ha : a < M) (hk : k < M) : shiftVal M k a < M := by
  dsimp [shiftVal]
  split_ifs <;> omega

private lemma unshiftVal_lt {M k a : ℕ} (_ha : a < M) (_hk1 : 1 ≤ k) : unshiftVal M k a < M := by
  dsimp [unshiftVal]
  split_ifs <;> omega

private lemma shiftVal_ne {M k a : ℕ} (_ha : a < M) (hk1 : 1 ≤ k) (hk : k < M) :
    shiftVal M k a ≠ a := by
  dsimp [shiftVal]
  split_ifs <;> omega

private lemma unshiftVal_shiftVal {M k a : ℕ} (ha : a < M) (hk : k < M) :
    unshiftVal M k (shiftVal M k a) = a := by
  dsimp [shiftVal, unshiftVal]
  split_ifs <;> omega

private lemma shiftVal_unshiftVal {M k a : ℕ} (ha : a < M) (hk : k < M) :
    shiftVal M k (unshiftVal M k a) = a := by
  dsimp [shiftVal, unshiftVal]
  split_ifs <;> omega

private lemma shiftVal_inj_step {M k1 k2 a : ℕ} (_ha : a < M) (hk1 : k1 < M) (hk2 : k2 < M)
    (heq : shiftVal M k1 a = shiftVal M k2 a) : k1 = k2 := by
  dsimp [shiftVal] at heq
  split_ifs at heq <;> omega

private lemma shiftVal_no_two_cycle {M k1 k2 a1 a2 : ℕ} (ha1 : a1 < M) (_ha2 : a2 < M)
    (hk1 : 1 ≤ k1) (hk2 : 1 ≤ k2) (hsum : k1 + k2 < M)
    (h1 : a1 = shiftVal M k2 a2) (h2 : a2 = shiftVal M k1 a1) : False := by
  dsimp [shiftVal] at h1 h2
  split_ifs at h1 h2 <;> omega

private lemma card_tok_bool_pred {E : Type} [Fintype E] (f : E → ℕ)
    (P0 P1 : E → Prop) [DecidablePred P0] [DecidablePred P1] :
    Fintype.card {x : (Σ e : E, Fin (f e)) × Bool // if x.2 = true then P1 x.1.1 else P0 x.1.1} =
      (∑ e : E, if P0 e then f e else 0) + (∑ e : E, if P1 e then f e else 0) := by
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter,
    Fintype.sum_prod_type_right, Fintype.sum_bool, add_comm]
  congr 1
  · rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases h : P0 e <;> simp [h]
  · rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases h : P1 e <;> simp [h]

private lemma sigma_snd_eq_of_eq {A : Type} {B : A → Type} {a : A}
    {p1 p2 : Σ x : A, B x} (h1 : p1.1 = a) (h2 : p2.1 = a)
    (hcast : h1 ▸ p1.2 = h2 ▸ p2.2) : p1 = p2 := by
  rcases p1 with ⟨a1, b1⟩
  rcases p2 with ⟨a2, b2⟩
  dsimp at h1 h2 hcast
  subst h1
  subst h2
  exact congrArg (Sigma.mk _) hcast

namespace Realize

variable {b p q : ℕ} (w : DualWeights b p q)

private abbrev TokX := Σ e : ValidX b, Fin (w.X e)
private abbrev TokY := Σ e : ValidYZ b, Fin (w.Y e)
private abbrev TokZ := Σ e : ValidYZ b, Fin (w.Z e)
private abbrev TokYZ := TokY w ⊕ TokZ w
private abbrev AllTok := TokX w ⊕ TokYZ w
private abbrev BaseV := Σ s : OMA.S_mo_148821.Label b, Fin (w.N s)

private def xLabel (τ : TokX w) (side : Bool) : OMA.S_mo_148821.Label b :=
  match side with
  | false => τ.1.1.1
  | true => τ.1.1.2

private def yzLabel (τ : TokYZ w) (side : Bool) : OMA.S_mo_148821.Label b :=
  match τ, side with
  | Sum.inl τy, false => τy.1.1.1
  | Sum.inl τy, true => τy.1.1.2.1
  | Sum.inr τz, false => τz.1.1.1
  | Sum.inr τz, true => τz.1.1.2.1

private def yzRound (τ : TokYZ w) : Fin b :=
  match τ with
  | Sum.inl τy => τy.1.1.2.2
  | Sum.inr τz => τz.1.1.2.2

private lemma yzRound_mem_yzLabel (τ : TokYZ w) (side : Bool) :
    yzRound w τ ∈ yzLabel w τ side := by
  rcases τ with ⟨e, _⟩ | ⟨e, _⟩ <;> cases side
  · exact e.2.1
  · exact e.2.2.1
  · exact e.2.1
  · exact e.2.2.1

private lemma card_he_yz (s : OMA.S_mo_148821.Label b) (i : Fin b) (hi : i ∈ s) :
    Fintype.card {he : TokYZ w × Bool // yzLabel w he.1 he.2 = s ∧ yzRound w he.1 = i} =
      Fintype.card (Fin (w.N s)) := by
  rw [Fintype.card_fin, Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter,
    Fintype.sum_prod_type_right, Fintype.sum_bool, add_comm,
    Fintype.sum_sum_type, Fintype.sum_sum_type]
  have hy0 : ∑ τ : TokY w, (if yzLabel w (Sum.inl τ) false = s ∧ yzRound w (Sum.inl τ) = i then 1 else 0) =
      ∑ e : ValidYZ b, if e.1.1 = s ∧ e.1.2.2 = i then w.Y e else 0 := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases h : e.1.1 = s ∧ e.1.2.2 = i <;> simp [yzLabel, yzRound, h]
  have hz0 : ∑ τ : TokZ w, (if yzLabel w (Sum.inr τ) false = s ∧ yzRound w (Sum.inr τ) = i then 1 else 0) =
      ∑ e : ValidYZ b, if e.1.1 = s ∧ e.1.2.2 = i then w.Z e else 0 := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases h : e.1.1 = s ∧ e.1.2.2 = i <;> simp [yzLabel, yzRound, h]
  have hy1 : ∑ τ : TokY w, (if yzLabel w (Sum.inl τ) true = s ∧ yzRound w (Sum.inl τ) = i then 1 else 0) =
      ∑ e : ValidYZ b, if e.1.2.1 = s ∧ e.1.2.2 = i then w.Y e else 0 := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases h : e.1.2.1 = s ∧ e.1.2.2 = i <;> simp [yzLabel, yzRound, h]
  have hz1 : ∑ τ : TokZ w, (if yzLabel w (Sum.inr τ) true = s ∧ yzRound w (Sum.inr τ) = i then 1 else 0) =
      ∑ e : ValidYZ b, if e.1.2.1 = s ∧ e.1.2.2 = i then w.Z e else 0 := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases h : e.1.2.1 = s ∧ e.1.2.2 = i <;> simp [yzLabel, yzRound, h]
  rw [hy0, hz0, hy1, hz1, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have hm0 : (∑ e : ValidYZ b, ((if e.1.1 = s ∧ e.1.2.2 = i then w.Y e else 0) +
      (if e.1.1 = s ∧ e.1.2.2 = i then w.Z e else 0))) =
      ∑ e : ValidYZ b, if e.1.1 = s ∧ e.1.2.2 = i then w.Y e + w.Z e else 0 :=
    Finset.sum_congr rfl fun e _ => by split_ifs <;> omega
  have hm1 : (∑ e : ValidYZ b, ((if e.1.2.1 = s ∧ e.1.2.2 = i then w.Y e else 0) +
      (if e.1.2.1 = s ∧ e.1.2.2 = i then w.Z e else 0))) =
      ∑ e : ValidYZ b, if e.1.2.1 = s ∧ e.1.2.2 = i then w.Y e + w.Z e else 0 :=
    Finset.sum_congr rfl fun e _ => by split_ifs <;> omega
  rw [hm0, hm1]
  exact w.eq_Ri s i hi

private noncomputable def bijYZ (s : OMA.S_mo_148821.Label b) (i : Fin b) (hi : i ∈ s) :
    {he : TokYZ w × Bool // yzLabel w he.1 he.2 = s ∧ yzRound w he.1 = i} ≃ Fin (w.N s) :=
  Fintype.equivOfCardEq (card_he_yz w s i hi)

private noncomputable def endYZ (he : TokYZ w × Bool) : BaseV w :=
  ⟨yzLabel w he.1 he.2,
    bijYZ w (yzLabel w he.1 he.2) (yzRound w he.1) (yzRound_mem_yzLabel w he.1 he.2)
      ⟨he, rfl, rfl⟩⟩

private lemma endYZ_fst (he : TokYZ w × Bool) : (endYZ w he).1 = yzLabel w he.1 he.2 := rfl

private lemma endYZ_eq_iff (he : TokYZ w × Bool) (s : OMA.S_mo_148821.Label b) (i : Fin b)
    (hs : yzLabel w he.1 he.2 = s) (hr : yzRound w he.1 = i)
    (hi : i ∈ s) (k : Fin (w.N s)) :
    endYZ w he = ⟨s, k⟩ ↔ bijYZ w s i hi ⟨he, hs, hr⟩ = k := by
  subst hs
  subst hr
  simp [endYZ]

private lemma endYZ_round_unique {he1 he2 : TokYZ w × Bool}
    (hend : endYZ w he1 = endYZ w he2) (hr : yzRound w he1.1 = yzRound w he2.1) :
    he1 = he2 := by
  rcases h1 : endYZ w he1 with ⟨s, k⟩
  have hs1 : yzLabel w he1.1 he1.2 = s := congrArg Sigma.fst h1
  have h2 : endYZ w he2 = ⟨s, k⟩ := hend.symm.trans h1
  have hs2 : yzLabel w he2.1 he2.2 = s := congrArg Sigma.fst h2
  let i := yzRound w he1.1
  have hi : i ∈ s := hs1 ▸ yzRound_mem_yzLabel w he1.1 he1.2
  have hb1 : bijYZ w s i hi ⟨he1, hs1, rfl⟩ = k :=
    (endYZ_eq_iff w he1 s i hs1 rfl hi k).mp h1
  have hb2 : bijYZ w s i hi ⟨he2, hs2, hr.symm⟩ = k :=
    (endYZ_eq_iff w he2 s i hs2 hr.symm hi k).mp h2
  have hsub := (bijYZ w s i hi).injective (hb1.trans hb2.symm)
  exact congrArg Subtype.val hsub

private noncomputable def degY (u : BaseV w) : ℕ :=
  Fintype.card {hy : TokY w × Bool // endYZ w (Sum.inl hy.1, hy.2) = u}

private lemma degY_le_b (u : BaseV w) : degY w u ≤ b := by
  unfold degY
  have hinj : Function.Injective
      (fun hy : {hy : TokY w × Bool // endYZ w (Sum.inl hy.1, hy.2) = u} =>
        yzRound w (Sum.inl hy.1.1)) := by
    intro hy1 hy2 hr
    have heq := endYZ_round_unique w (hy1.2.trans hy2.2.symm) hr
    have hpair := Prod.mk.inj heq
    have htok := Sum.inl.inj hpair.1
    exact Subtype.ext (Prod.ext htok hpair.2)
  calc Fintype.card {hy : TokY w × Bool // endYZ w (Sum.inl hy.1, hy.2) = u}
      ≤ Fintype.card (Fin b) := Fintype.card_le_of_injective _ hinj
    _ = b := Fintype.card_fin b

private lemma sum_degY_at (s : OMA.S_mo_148821.Label b) :
    ∑ k : Fin (w.N s), degY w ⟨s, k⟩ =
      (∑ e : ValidYZ b, if e.1.1 = s then w.Y e else 0) +
      (∑ e : ValidYZ b, if e.1.2.1 = s then w.Y e else 0) := by
  have hsum : ∑ k : Fin (w.N s), degY w ⟨s, k⟩ =
      Fintype.card {hy : TokY w × Bool // yzLabel w (Sum.inl hy.1) hy.2 = s} := by
    unfold degY
    simp_rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun hy _ => ?_
    by_cases hs : yzLabel w (Sum.inl hy.1) hy.2 = s
    · rw [if_pos hs]
      rcases hu : endYZ w (Sum.inl hy.1, hy.2) with ⟨s', k'⟩
      have hs' : s' = s := (congrArg Sigma.fst hu).symm.trans hs
      subst hs'
      simp
    · rw [if_neg hs]
      refine Finset.sum_eq_zero fun k _ => if_neg ?_
      intro hk
      exact hs (congrArg Sigma.fst hk)
  rw [hsum]
  have hcond : ∀ hy : TokY w × Bool,
      (yzLabel w (Sum.inl hy.1) hy.2 = s) ↔
        (if hy.2 = true then hy.1.1.1.2.1 = s else hy.1.1.1.1 = s) := by
    rintro ⟨⟨e, m⟩, false | true⟩ <;> simp [yzLabel]
  simp_rw [hcond]
  exact card_tok_bool_pred w.Y (fun e => e.1.1 = s) (fun e => e.1.2.1 = s)

private lemma card_he_x_le_cap (s : OMA.S_mo_148821.Label b) :
    Fintype.card {hx : TokX w × Bool // xLabel w hx.1 hx.2 = s} ≤
      Fintype.card (Σ k : Fin (w.N s), Fin (b - degY w ⟨s, k⟩)) := by
  have hcardX : Fintype.card {hx : TokX w × Bool // xLabel w hx.1 hx.2 = s} =
      (∑ e : ValidX b, if e.1.1 = s then w.X e else 0) +
      (∑ e : ValidX b, if e.1.2 = s then w.X e else 0) := by
    have hcond : ∀ hx : TokX w × Bool,
        (xLabel w hx.1 hx.2 = s) ↔ (if hx.2 = true then hx.1.1.1.2 = s else hx.1.1.1.1 = s) := by
      rintro ⟨⟨e, m⟩, false | true⟩ <;> simp [xLabel]
    simp_rw [hcond]
    exact card_tok_bool_pred w.X (fun e => e.1.1 = s) (fun e => e.1.2 = s)
  have hcardCap : Fintype.card (Σ k : Fin (w.N s), Fin (b - degY w ⟨s, k⟩)) =
      ∑ k : Fin (w.N s), (b - degY w ⟨s, k⟩) := by
    simp
  have hsum_add : (∑ k : Fin (w.N s), (b - degY w ⟨s, k⟩)) + ∑ k : Fin (w.N s), degY w ⟨s, k⟩ =
      b * w.N s := by
    rw [← Finset.sum_add_distrib]
    calc ∑ k : Fin (w.N s), (b - degY w ⟨s, k⟩ + degY w ⟨s, k⟩)
        = ∑ _k : Fin (w.N s), b :=
          Finset.sum_congr rfl fun k _ => Nat.sub_add_cancel (degY_le_b w ⟨s, k⟩)
      _ = b * w.N s := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]
  have hle := w.le_O s
  rw [hcardX, hcardCap]
  have hdegY := sum_degY_at w s
  omega

private noncomputable def embX (s : OMA.S_mo_148821.Label b) :
    {hx : TokX w × Bool // xLabel w hx.1 hx.2 = s} ↪
      (Σ k : Fin (w.N s), Fin (b - degY w ⟨s, k⟩)) :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (card_he_x_le_cap w s))

private noncomputable def endX (hx : TokX w × Bool) : BaseV w :=
  ⟨xLabel w hx.1 hx.2, (embX w (xLabel w hx.1 hx.2) ⟨hx, rfl⟩).1⟩

private lemma endX_fst (hx : TokX w × Bool) : (endX w hx).1 = xLabel w hx.1 hx.2 := rfl

private lemma endX_eq_iff (hx : TokX w × Bool) (s : OMA.S_mo_148821.Label b)
    (hs : xLabel w hx.1 hx.2 = s) (k : Fin (w.N s)) :
    endX w hx = ⟨s, k⟩ ↔ (embX w s ⟨hx, hs⟩).1 = k := by
  subst hs
  simp [endX]

private noncomputable def degX (u : BaseV w) : ℕ :=
  Fintype.card {hx : TokX w × Bool // endX w hx = u}

private lemma degX_le_sub (u : BaseV w) : degX w u ≤ b - degY w u := by
  rcases u with ⟨s, k⟩
  unfold degX
  let toSlot : {hx : TokX w × Bool // endX w hx = ⟨s, k⟩} → Fin (b - degY w ⟨s, k⟩) :=
    fun hx =>
      have hs : xLabel w hx.1.1 hx.1.2 = s := congrArg Sigma.fst hx.2
      have hk : (embX w s ⟨hx.1, hs⟩).1 = k := (endX_eq_iff w hx.1 s hs k).mp hx.2
      hk ▸ (embX w s ⟨hx.1, hs⟩).2
  have hinj : Function.Injective toSlot := by
    intro hx1 hx2 hslot
    have hs1 : xLabel w hx1.1.1 hx1.1.2 = s := congrArg Sigma.fst hx1.2
    have hs2 : xLabel w hx2.1.1 hx2.1.2 = s := congrArg Sigma.fst hx2.2
    have hk1 : (embX w s ⟨hx1.1, hs1⟩).1 = k := (endX_eq_iff w hx1.1 s hs1 k).mp hx1.2
    have hk2 : (embX w s ⟨hx2.1, hs2⟩).1 = k := (endX_eq_iff w hx2.1 s hs2 k).mp hx2.2
    have hemb : embX w s ⟨hx1.1, hs1⟩ = embX w s ⟨hx2.1, hs2⟩ :=
      sigma_snd_eq_of_eq hk1 hk2 hslot
    have hsub := (embX w s).injective hemb
    have hval : hx1.1 = hx2.1 :=
      congrArg (Subtype.val : {hx : TokX w × Bool // xLabel w hx.1 hx.2 = s} → TokX w × Bool) hsub
    exact Subtype.ext hval
  calc Fintype.card {hx : TokX w × Bool // endX w hx = ⟨s, k⟩}
      ≤ Fintype.card (Fin (b - degY w ⟨s, k⟩)) := Fintype.card_le_of_injective toSlot hinj
    _ = b - degY w ⟨s, k⟩ := Fintype.card_fin _

private noncomputable def endTok (τ : AllTok w) (side : Bool) : BaseV w :=
  match τ with
  | Sum.inl τx => endX w (τx, side)
  | Sum.inr τyz => endYZ w (τyz, side)

private noncomputable def numTok : ℕ := Fintype.card (AllTok w)
private noncomputable def idxTok : AllTok w ≃ Fin (numTok w) := Fintype.equivFin (AllTok w)
private noncomputable def modM : ℕ := 2 * numTok w + 3

private lemma modM_pos : 0 < modM w := by
  unfold modM
  omega

private noncomputable def stepTok (τ : AllTok w) : ℕ := (idxTok w τ).1 + 1

private lemma stepTok_ge_one (τ : AllTok w) : 1 ≤ stepTok w τ := by
  unfold stepTok
  omega

private lemma stepTok_lt_modM (τ : AllTok w) : stepTok w τ < modM w := by
  unfold stepTok modM
  have h := (idxTok w τ).2
  omega

private lemma stepTok_add_lt_modM (τ1 τ2 : AllTok w) :
    stepTok w τ1 + stepTok w τ2 < modM w := by
  unfold stepTok modM
  have h1 := (idxTok w τ1).2
  have h2 := (idxTok w τ2).2
  omega

private noncomputable def shiftFin (τ : AllTok w) (m : Fin (modM w)) : Fin (modM w) :=
  ⟨shiftVal (modM w) (stepTok w τ) m.1, shiftVal_lt m.2 (stepTok_lt_modM w τ)⟩

private noncomputable def unshiftFin (τ : AllTok w) (m : Fin (modM w)) : Fin (modM w) :=
  ⟨unshiftVal (modM w) (stepTok w τ) m.1, unshiftVal_lt m.2 (stepTok_ge_one w τ)⟩

private lemma shiftFin_ne (τ : AllTok w) (m : Fin (modM w)) : shiftFin w τ m ≠ m := by
  intro h
  exact shiftVal_ne m.2 (stepTok_ge_one w τ) (stepTok_lt_modM w τ) (congrArg Fin.val h)

private lemma unshiftFin_shiftFin (τ : AllTok w) (m : Fin (modM w)) :
    unshiftFin w τ (shiftFin w τ m) = m :=
  Fin.ext (unshiftVal_shiftVal m.2 (stepTok_lt_modM w τ))

private lemma shiftFin_unshiftFin (τ : AllTok w) (m : Fin (modM w)) :
    shiftFin w τ (unshiftFin w τ m) = m :=
  Fin.ext (shiftVal_unshiftVal m.2 (stepTok_lt_modM w τ))

private noncomputable def nV : ℕ := Fintype.card (BaseV w × Fin (modM w))
private noncomputable def eV : BaseV w × Fin (modM w) ≃ Fin (nV w) :=
  Fintype.equivFin (BaseV w × Fin (modM w))

private noncomputable def wEnd (τ : AllTok w) (m : Fin (modM w)) (side : Bool) : Fin (nV w) :=
  match side with
  | false => eV w (endTok w τ false, m)
  | true => eV w (endTok w τ true, shiftFin w τ m)

private noncomputable def edgeOf (p : AllTok w × Fin (modM w)) : Sym2 (Fin (nV w)) :=
  Sym2.mk (wEnd w p.1 p.2 false) (wEnd w p.1 p.2 true)

private lemma wEnd_false_ne_true (τ : AllTok w) (m : Fin (modM w)) :
    wEnd w τ m false ≠ wEnd w τ m true := by
  intro h
  have hpair := (eV w).injective h
  exact shiftFin_ne w τ m (Prod.mk.inj hpair).2.symm

private lemma edgeOf_not_isDiag (p : AllTok w × Fin (modM w)) : ¬ (edgeOf w p).IsDiag := by
  rw [edgeOf, Sym2.mk_isDiag_iff]
  exact wEnd_false_ne_true w p.1 p.2

private lemma edgeOf_injective : Function.Injective (edgeOf w) := by
  rintro ⟨τ1, m1⟩ ⟨τ2, m2⟩ heq
  rw [edgeOf, edgeOf, Sym2.eq_iff] at heq
  rcases heq with ⟨h00, h11⟩ | ⟨h01, h10⟩
  · have hm : m1 = m2 := (Prod.mk.inj ((eV w).injective h00)).2
    subst hm
    have hsh : shiftFin w τ1 m1 = shiftFin w τ2 m1 := (Prod.mk.inj ((eV w).injective h11)).2
    have hstep : stepTok w τ1 = stepTok w τ2 :=
      shiftVal_inj_step m1.2 (stepTok_lt_modM w τ1) (stepTok_lt_modM w τ2) (congrArg Fin.val hsh)
    have hidx : idxTok w τ1 = idxTok w τ2 := by
      ext
      unfold stepTok at hstep
      omega
    exact Prod.ext ((idxTok w).injective hidx) rfl
  · have hm1 : m1 = shiftFin w τ2 m2 := (Prod.mk.inj ((eV w).injective h01)).2
    have hm2 : shiftFin w τ1 m1 = m2 := (Prod.mk.inj ((eV w).injective h10)).2
    exfalso
    exact shiftVal_no_two_cycle m1.2 m2.2 (stepTok_ge_one w τ1) (stepTok_ge_one w τ2)
      (stepTok_add_lt_modM w τ1 τ2) (congrArg Fin.val hm1) (congrArg Fin.val hm2.symm)

private noncomputable def mkEdges {S : Type} [Fintype S] (ι : S → AllTok w) :
    OMA.S_mo_148821.Edges (nV w) :=
  Finset.univ.image (fun q : S × Fin (modM w) => edgeOf w (ι q.1, q.2))

private lemma card_mkEdges {S : Type} [Fintype S] {ι : S → AllTok w}
    (hι : Function.Injective ι) :
    (mkEdges w ι).card = Fintype.card S * modM w := by
  unfold mkEdges
  have hinj : Function.Injective (fun q : S × Fin (modM w) => edgeOf w (ι q.1, q.2)) := by
    intro q1 q2 heq
    have hp := Prod.mk.inj (edgeOf_injective w heq)
    exact Prod.ext (hι hp.1) hp.2
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]

private lemma degreeAt_mkEdges {S : Type} [Fintype S] {ι : S → AllTok w}
    (hι : Function.Injective ι) (u : BaseV w) (m0 : Fin (modM w)) :
    OMA.S_mo_148821.degreeAt (mkEdges w ι) (eV w (u, m0)) =
      Fintype.card {he : S × Bool // endTok w (ι he.1) he.2 = u} := by
  unfold OMA.S_mo_148821.degreeAt mkEdges
  have hinj : Function.Injective (fun q : S × Fin (modM w) => edgeOf w (ι q.1, q.2)) := by
    intro q1 q2 heq
    have hp := Prod.mk.inj (edgeOf_injective w heq)
    exact Prod.ext (hι hp.1) hp.2
  rw [Finset.filter_image, Finset.card_image_of_injective _ hinj, ← Fintype.card_subtype]
  refine Fintype.card_congr ?_
  refine
    { toFun := fun q =>
        if h0 : eV w (u, m0) = wEnd w (ι q.1.1) q.1.2 false then
          ⟨(q.1.1, false), (Prod.mk.inj ((eV w).injective h0)).1.symm⟩
        else
          ⟨(q.1.1, true), by
            have hmem := Sym2.mem_iff.mp q.2
            rcases hmem with hleft | hright
            · exact False.elim (h0 hleft)
            · exact (Prod.mk.inj ((eV w).injective hright)).1.symm⟩
      invFun := fun he =>
        match he with
        | ⟨(s_tok, false), hu⟩ =>
          ⟨(s_tok, m0), by
            rw [edgeOf, Sym2.mem_iff]
            exact Or.inl (by simp [wEnd, hu])⟩
        | ⟨(s_tok, true), hu⟩ =>
          ⟨(s_tok, unshiftFin w (ι s_tok) m0), by
            rw [edgeOf, Sym2.mem_iff]
            exact Or.inr (by simp [wEnd, hu, shiftFin_unshiftFin])⟩
      left_inv := fun q => by
        rcases q with ⟨⟨s_tok, m⟩, hmem⟩
        by_cases h0 : eV w (u, m0) = wEnd w (ι s_tok) m false
        · simp only [dif_pos h0]
          have hm : m0 = m := (Prod.mk.inj ((eV w).injective h0)).2
          subst hm
          rfl
        · simp only [dif_neg h0]
          rcases Sym2.mem_iff.mp hmem with hleft | hright
          · exact False.elim (h0 hleft)
          · have hm : m0 = shiftFin w (ι s_tok) m := (Prod.mk.inj ((eV w).injective hright)).2
            subst hm
            simp [unshiftFin_shiftFin]
      right_inv := fun he => by
        rcases he with ⟨⟨s_tok, false | true⟩, hu⟩
        · have h0 : eV w (u, m0) = wEnd w (ι s_tok) m0 false := by simp [wEnd, hu]
          simp [dif_pos h0]
        · have hnot0 : eV w (u, m0) ≠ wEnd w (ι s_tok) (unshiftFin w (ι s_tok) m0) false := by
            intro h0
            have hm : m0 = unshiftFin w (ι s_tok) m0 := (Prod.mk.inj ((eV w).injective h0)).2
            have hsh := congrArg (shiftFin w (ι s_tok)) hm
            rw [shiftFin_unshiftFin] at hsh
            exact shiftFin_ne w (ι s_tok) m0 hsh
          simp [dif_neg hnot0] }

private noncomputable def allEdges : OMA.S_mo_148821.Edges (nV w) :=
  mkEdges w id

private noncomputable def blowupGraph : SimpleGraph (Fin (nV w)) :=
  SimpleGraph.fromEdgeSet (↑(allEdges w) : Set (Sym2 (Fin (nV w))))

private lemma mem_blowupGraph_edgeSet (e : Sym2 (Fin (nV w))) :
    e ∈ (blowupGraph w).edgeSet ↔ e ∈ allEdges w := by
  unfold blowupGraph
  rw [SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff, Finset.mem_coe]
  constructor
  · exact fun h => h.1
  · intro he
    refine ⟨he, ?_⟩
    unfold allEdges mkEdges at he
    rcases Finset.mem_image.mp he with ⟨p, _, rfl⟩
    exact edgeOf_not_isDiag w p

private lemma mkEdges_sub_edgeSet {S : Type} [Fintype S] (ι : S → AllTok w) :
    ∀ e ∈ mkEdges w ι, e ∈ (blowupGraph w).edgeSet := by
  intro e he
  rw [mem_blowupGraph_edgeSet]
  rcases Finset.mem_image.mp he with ⟨q, _, rfl⟩
  exact Finset.mem_image.mpr ⟨(ι q.1, q.2), Finset.mem_univ _, rfl⟩

private noncomputable def roundEdges (i : Fin b) : OMA.S_mo_148821.Edges (nV w) :=
  mkEdges w (fun τ : {τ : TokYZ w // yzRound w τ = i} => Sum.inr τ.1)

private noncomputable def optEdges : OMA.S_mo_148821.Edges (nV w) :=
  mkEdges w (fun τ : TokX w ⊕ TokY w =>
    match τ with
    | Sum.inl τx => Sum.inl τx
    | Sum.inr τy => Sum.inr (Sum.inl τy))

private lemma inj_round (i : Fin b) :
    Function.Injective (fun τ : {τ : TokYZ w // yzRound w τ = i} => (Sum.inr τ.1 : AllTok w)) := by
  intro τ1 τ2 h
  exact Subtype.ext (Sum.inr.inj h)

private lemma inj_opt :
    Function.Injective (fun τ : TokX w ⊕ TokY w =>
      (match τ with
      | Sum.inl τx => Sum.inl τx
      | Sum.inr τy => Sum.inr (Sum.inl τy) : AllTok w)) := by
  rintro (τ1 | τ1) (τ2 | τ2) h
  · exact congrArg Sum.inl (Sum.inl.inj h)
  · cases h
  · cases h
  · exact congrArg Sum.inr (Sum.inl.inj (Sum.inr.inj h))

private lemma degreeAt_roundEdges_eq (i : Fin b) (u : BaseV w) (m0 : Fin (modM w)) :
    OMA.S_mo_148821.degreeAt (roundEdges w i) (eV w (u, m0)) =
      if i ∈ u.1 then 1 else 0 := by
  unfold roundEdges
  rw [degreeAt_mkEdges w (inj_round w i) u m0]
  rcases u with ⟨s, k⟩
  by_cases hi : i ∈ s
  · rw [if_pos hi]
    rcases het : (bijYZ w s i hi).symm k with ⟨⟨τ0, side0⟩, hs0, hr0⟩
    have hdef_end : endTok w (Sum.inr τ0) side0 = ⟨s, k⟩ := by
      dsimp [endTok]
      have happ : bijYZ w s i hi ⟨(τ0, side0), hs0, hr0⟩ = k := by
        rw [← het, Equiv.apply_symm_apply]
      exact (endYZ_eq_iff w (τ0, side0) s i hs0 hr0 hi k).mpr happ
    have huniq : ∀ x : {he : {τ : TokYZ w // yzRound w τ = i} × Bool //
        endTok w (Sum.inr he.1.1) he.2 = ⟨s, k⟩},
        x = ⟨(⟨τ0, hr0⟩, side0), hdef_end⟩ := by
      rintro ⟨⟨⟨τ, hr⟩, side⟩, hend⟩
      dsimp [endTok] at hend
      have hs : yzLabel w τ side = s := congrArg Sigma.fst hend
      have hb : bijYZ w s i hi ⟨(τ, side), hs, hr⟩ = k :=
        (endYZ_eq_iff w (τ, side) s i hs hr hi k).mp hend
      have hsymm : (⟨(τ, side), hs, hr⟩ : {he : TokYZ w × Bool // yzLabel w he.1 he.2 = s ∧ yzRound w he.1 = i}) =
          ⟨(τ0, side0), hs0, hr0⟩ := by
        rw [← het, ← hb, Equiv.symm_apply_apply]
      have hval : (τ, side) = (τ0, side0) := congrArg Subtype.val hsymm
      rcases Prod.mk.inj hval with ⟨rfl, rfl⟩
      rfl
    have : Unique {he : {τ : TokYZ w // yzRound w τ = i} × Bool //
        endTok w (Sum.inr he.1.1) he.2 = ⟨s, k⟩} :=
      { default := ⟨(⟨τ0, hr0⟩, side0), hdef_end⟩
        uniq := huniq }
    exact Fintype.card_unique
  · rw [if_neg hi, Fintype.card_eq_zero_iff]
    refine ⟨fun x => ?_⟩
    rcases x with ⟨⟨⟨τ, hr⟩, side⟩, hend⟩
    dsimp [endTok] at hend
    have hs : yzLabel w τ side = s := congrArg Sigma.fst hend
    have hmem : i ∈ s := hr ▸ hs ▸ yzRound_mem_yzLabel w τ side
    exact hi hmem

private lemma legalRounds_blowup :
    OMA.S_mo_148821.legalRounds (blowupGraph w) (roundEdges w) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    refine ⟨mkEdges_sub_edgeSet w _, fun v => ?_⟩
    rcases (eV w).surjective v with ⟨⟨u, m0⟩, rfl⟩
    rw [degreeAt_roundEdges_eq]
    split_ifs <;> omega
  · intro i j hij
    rw [Finset.disjoint_left]
    intro e hei hej
    rcases Finset.mem_image.mp hei with ⟨⟨τ1, m1⟩, _, rfl⟩
    rcases Finset.mem_image.mp hej with ⟨⟨τ2, m2⟩, _, heq⟩
    have hp := Prod.mk.inj (edgeOf_injective w heq.symm)
    have hτ : τ1.1 = τ2.1 := Sum.inr.inj hp.1
    have hij_eq : i = j := τ1.2.symm.trans ((congrArg (yzRound w) hτ).trans τ2.2)
    exact (ne_of_lt hij) hij_eq
  · intro i e heG hnot
    rw [mem_blowupGraph_edgeSet] at heG
    rcases Finset.mem_image.mp heG with ⟨⟨τ, m⟩, _, rfl⟩
    have hcov : i ∈ (endTok w τ false).1 ∨ i ∈ (endTok w τ true).1 := by
      rcases τ with ⟨ex, _⟩ | τyz
      · dsimp [endTok]
        rw [endX_fst, endX_fst]
        exact ex.2 i
      · dsimp [endTok]
        rw [endYZ_fst, endYZ_fst]
        let i0 := yzRound w τyz
        have he_i0 : edgeOf w (Sum.inr τyz, m) ∈ roundEdges w i0 := by
          unfold roundEdges mkEdges
          exact Finset.mem_image.mpr ⟨(⟨τyz, rfl⟩, m), Finset.mem_univ _, rfl⟩
        have hlt : i < i0 := by
          by_contra hge
          exact hnot i0 (le_of_not_gt hge) he_i0
        rcases τyz with ⟨ey, _⟩ | ⟨ez, _⟩
        · exact ey.2.2.2 i hlt
        · exact ez.2.2.2 i hlt
    rcases hcov with h0 | h1
    · let v0 := wEnd w τ m false
      have hv0_eq : v0 = eV w (endTok w τ false, m) := rfl
      have hdeg : 0 < OMA.S_mo_148821.degreeAt (roundEdges w i) v0 := by
        rw [hv0_eq, degreeAt_roundEdges_eq, if_pos h0]
        omega
      rcases Finset.card_pos.mp hdeg with ⟨f, hf⟩
      rw [Finset.mem_filter] at hf
      refine ⟨f, hf.1, v0, ?_, hf.2⟩
      rw [edgeOf, Sym2.mem_iff]
      exact Or.inl rfl
    · let v1 := wEnd w τ m true
      have hv1_eq : v1 = eV w (endTok w τ true, shiftFin w τ m) := rfl
      have hdeg : 0 < OMA.S_mo_148821.degreeAt (roundEdges w i) v1 := by
        rw [hv1_eq, degreeAt_roundEdges_eq, if_pos h1]
        omega
      rcases Finset.card_pos.mp hdeg with ⟨f, hf⟩
      rw [Finset.mem_filter] at hf
      refine ⟨f, hf.1, v1, ?_, hf.2⟩
      rw [edgeOf, Sym2.mem_iff]
      exact Or.inr rfl

private lemma feasible_optEdges :
    OMA.S_mo_148821.feasible (blowupGraph w) b (optEdges w) := by
  refine ⟨mkEdges_sub_edgeSet w _, fun v => ?_⟩
  rcases (eV w).surjective v with ⟨⟨u, m0⟩, rfl⟩
  unfold optEdges
  rw [degreeAt_mkEdges w (inj_opt w) u m0]
  have hcard : Fintype.card {he : (TokX w ⊕ TokY w) × Bool //
      endTok w (match he.1 with | Sum.inl τx => Sum.inl τx | Sum.inr τy => Sum.inr (Sum.inl τy)) he.2 = u} =
      degX w u + degY w u := by
    unfold degX degY
    rw [← Fintype.card_sum]
    refine Fintype.card_congr ?_
    refine
      { toFun := fun x =>
          match x with
          | ⟨(Sum.inl τx, side), hu⟩ => Sum.inl ⟨(τx, side), hu⟩
          | ⟨(Sum.inr τy, side), hu⟩ => Sum.inr ⟨(τy, side), hu⟩
        invFun := fun y =>
          match y with
          | Sum.inl ⟨(τx, side), hu⟩ => ⟨(Sum.inl τx, side), hu⟩
          | Sum.inr ⟨(τy, side), hu⟩ => ⟨(Sum.inr τy, side), hu⟩
        left_inv := by rintro ⟨⟨_ | _, _⟩, _⟩ <;> rfl
        right_inv := by rintro (⟨⟨_, _⟩, _⟩ | ⟨⟨_, _⟩, _⟩) <;> rfl }
  rw [hcard]
  have h1 := degX_le_sub w u
  have h2 := degY_le_b w u
  omega

private lemma sum_card_roundEdges :
    ∑ i : Fin b, (roundEdges w i).card =
      ((∑ e : ValidYZ b, w.Y e) + (∑ e : ValidYZ b, w.Z e)) * modM w := by
  simp_rw [roundEdges, card_mkEdges w (inj_round w _)]
  rw [← Finset.sum_mul]
  congr 1
  have hpart : ∑ i : Fin b, Fintype.card {τ : TokYZ w // yzRound w τ = i} =
      Fintype.card (TokYZ w) := by
    simp_rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  rw [hpart, Fintype.card_sum, Fintype.card_sigma, Fintype.card_sigma]
  simp

private lemma card_optEdges :
    (optEdges w).card =
      ((∑ e : ValidX b, w.X e) + (∑ e : ValidYZ b, w.Y e)) * modM w := by
  rw [optEdges, card_mkEdges w (inj_opt w), Fintype.card_sum, Fintype.card_sigma, Fintype.card_sigma]
  simp

private theorem not_guaranteed_of_dualWeights (w : DualWeights b p q) :
    ¬ OMA.S_mo_148821.guaranteed b p q := by
  intro hguar
  have hineq := hguar (nV w) (blowupGraph w) (roundEdges w) (optEdges w)
    (legalRounds_blowup w) (feasible_optEdges w)
  rw [card_optEdges, sum_card_roundEdges, ← mul_assoc, ← mul_assoc] at hineq
  have hle := Nat.le_of_mul_le_mul_right hineq (modM_pos w)
  exact Nat.not_lt.mpr hle w.strict_obj

end Realize

end ProofMo148821

theorem OMA.solution : type_of% @OMA.S_mo_148821.main := by
  intro b p q _ _
  constructor
  · intro hguar
    rcases certified_or_dualWeights b p q with hcert | ⟨⟨N, X, Y, Z, heq, hle, hlt⟩⟩
    · exact hcert
    · exact False.elim (Realize.not_guaranteed_of_dualWeights ⟨N, X, Y, Z, heq, hle, hlt⟩ hguar)
  · exact certified_imp_guaranteed
