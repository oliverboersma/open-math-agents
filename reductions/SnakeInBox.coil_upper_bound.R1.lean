import FormalConjectures.Wikipedia.SnakeInTheBox
import Mathlib

-- Credit: @marcusbuffett
/- The walk-to-vertex-set correspondence and boundary edge count are adapted
from @skhakim, SnakeInBox.coil_small_dimensions.R1. -/
namespace OMA.R_SnakeInBox_coil_upper_bound_R1
open SimpleGraph SnakeInBox symmDiff Finset
open scoped Classical

private lemma hypercube_adj_iff (n : ℕ) (a b : Finset (Fin n)) :
    (Hypercube n).Adj a b ↔ (a ∆ b).card = 1 := by
  simp only [Hypercube, fromRel_adj]
  rw [symmDiff_comm b a]
  constructor
  · exact fun h => h.2.elim id id
  · intro h
    refine ⟨?_, Or.inl h⟩
    rintro rfl
    simp at h

private lemma hypercube_deg (n : ℕ) (a : Finset (Fin n)) :
    (Finset.univ.filter (fun b => (Hypercube n).Adj a b)).card = n := by
  have hbij : (Finset.univ.filter (fun b => (Hypercube n).Adj a b)) =
      Finset.univ.image (fun i : Fin n => a ∆ {i}) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, hypercube_adj_iff,
      Finset.card_eq_one]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, by rw [← hi, symmDiff_symmDiff_cancel_left]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, by simp⟩
  rw [hbij, Finset.card_image_of_injective]
  · simp
  · intro i j hij
    have h1 : ({i} : Finset (Fin n)) = {j} := by
      have := congrArg (a ∆ ·) hij
      simpa using this
    exact Finset.singleton_injective h1

private lemma walk_toSubgraph_adj_iff {V : Type*} {G : SimpleGraph V} {u v : V}
    (P : G.Walk u v) (a b : V) : P.toSubgraph.Adj a b ↔ s(a, b) ∈ P.edges := by
  induction P with
  | nil => simp
  | cons h Q ih =>
    change (G.subgraphOfAdj h ⊔ Q.toSubgraph).Adj a b ↔ s(a, b) ∈ (Walk.cons h Q).edges
    simp only [Subgraph.sup_adj, subgraphOfAdj_adj, Walk.edges_cons, List.mem_cons, ih, eq_comm]

private lemma coil_finset_props {n k : ℕ} {S : Subgraph (Hypercube n)}
    (h : IsCoilInGraphOfLength (Hypercube n) S k) :
    ∃ C : Finset (Finset (Fin n)), C.card = k ∧
      ∀ v ∈ C, (C.filter (fun w => (Hypercube n).Adj v w)).card = 2 := by
  obtain ⟨hInd, u, P, hCyc, rfl, rfl⟩ := h
  refine ⟨P.support.toFinset, ?_, ?_⟩
  · have htail : P.support.toFinset = P.support.tail.toFinset := by
      ext x
      simp only [List.mem_toFinset]
      cases P with
      | nil => exact (hCyc.ne_nil rfl).elim
      | @cons a b c hab Q =>
        simp only [Walk.support_cons, List.tail_cons, List.mem_cons]
        constructor
        · rintro (rfl | hx)
          · exact Q.end_mem_support
          · exact hx
        · exact Or.inr
    rw [htail, List.toFinset_card_of_nodup hCyc.support_nodup, List.length_tail, Walk.length_support]
    omega
  · intro v hv
    rw [List.mem_toFinset] at hv
    let Q := P.rotate v hv
    have hQCyc : Q.IsCycle := hCyc.rotate hv
    have hQedges : ∀ e, e ∈ Q.edges ↔ e ∈ P.edges := fun e => (P.rotate_edges v hv).perm.mem_iff
    have hQlen : 3 ≤ Q.length := hQCyc.three_le_length
    cases hQ : Q with
    | nil => exact (hQCyc.ne_nil hQ).elim
    | @cons _ w₁ _ hw₁ R =>
      have hmem_iff : ∀ w, w ∈ P.support.toFinset.filter (fun w => (Hypercube n).Adj v w) ↔
          s(v, w) ∈ Q.edges := by
        intro w
        simp only [Finset.mem_filter, List.mem_toFinset, hQedges]
        constructor
        · rintro ⟨hw, hadj⟩
          have hadj_sub : P.toSubgraph.Adj v w :=
            hInd (P.mem_verts_toSubgraph.mpr hv) (P.mem_verts_toSubgraph.mpr hw) hadj
          exact (walk_toSubgraph_adj_iff P v w).mp hadj_sub
        · intro he
          have hadj_sub : P.toSubgraph.Adj v w := (walk_toSubgraph_adj_iff P v w).mpr he
          exact ⟨(P.mem_verts_toSubgraph).mp hadj_sub.snd_mem, P.toSubgraph.adj_sub hadj_sub⟩
      -- Count edges of Q incident to v using Q = cons hw₁ R
      have hv_not_R_init : ∀ x ∈ R.support.dropLast, x ≠ v := by
        intro x hx hxv
        rw [hxv] at hx
        have hnodup := hQCyc.support_nodup
        rw [hQ, Walk.support_cons, List.tail_cons] at hnodup
        have hRsupp : R.support = R.support.dropLast ++ [v] := by
          have hne : R.support ≠ [] := Walk.support_ne_nil R
          conv_lhs => rw [← List.dropLast_append_getLast hne]
          congr 1
          simp [Walk.getLast_support]
        rw [hRsupp, List.nodup_append] at hnodup
        exact hnodup.2.2 v hx v (List.mem_singleton_self v) rfl
      -- Now look at R: since R is non-nil (length >= 2), reverse R to get the last edge!
      cases hRrev : R.reverse with
      | nil =>
        have : R.length = 0 := by
          have := congrArg Walk.length hRrev
          simpa using this
        rw [hQ] at hQlen
        simp [this] at hQlen
      | @cons _ w₂ _ hw₂ S =>
        have hR_eq : R = S.reverse.concat hw₂.symm := by
          rw [← Walk.reverse_reverse R, hRrev, Walk.reverse_cons, Walk.concat_eq_append]
        have hS_not_v : v ∉ S.reverse.support := by
          intro hvS
          have hsub : S.reverse.support = R.support.dropLast := by
            rw [hR_eq, Walk.support_concat]
            simp
          rw [hsub] at hvS
          exact hv_not_R_init v hvS rfl
        have hQ_edges_eq : Q.edges = s(v, w₁) :: (S.reverse.edges ++ [s(w₂, v)]) := by
          rw [hQ, Walk.edges_cons, hR_eq, Walk.edges_concat, List.concat_eq_append]
        have hset : P.support.toFinset.filter (fun w => (Hypercube n).Adj v w) = {w₁, w₂} := by
          ext w
          rw [hmem_iff, hQ_edges_eq]
          simp only [List.mem_cons, List.mem_append, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro (h1 | h2 | h3)
            · rw [Sym2.eq_iff] at h1
              rcases h1 with ⟨_, rfl⟩ | ⟨hvw, _⟩
              · exact Or.inl rfl
              · exact (hw₁.ne hvw).elim
            · exfalso
              exact hS_not_v (Walk.fst_mem_support_of_mem_edges S.reverse h2)
            · rcases h3 with h3 | h3
              · rw [Sym2.eq_iff] at h3
                rcases h3 with ⟨hvw, _⟩ | ⟨_, rfl⟩
                · exact (hw₂.ne hvw).elim
                · exact Or.inr rfl
              · exact (List.not_mem_nil h3).elim
          · rintro (rfl | rfl)
            · exact Or.inl rfl
            · exact Or.inr (Or.inr (Or.inl Sym2.eq_swap))
        rw [hset, Finset.card_pair]
        intro h12
        subst h12
        have hnodup := hQCyc.edges_nodup
        rw [hQ_edges_eq, List.nodup_cons] at hnodup
        exact hnodup.1 (List.mem_append_right _ (List.mem_singleton.mpr Sym2.eq_swap))


private lemma boundary {n : ℕ} (C : Finset (Finset (Fin n)))
    (hdeg : ∀ v ∈ C, (C.filter (fun w ↦ (Hypercube n).Adj v w)).card = 2) :
    C.card * (n-2) ≤ n*Cᶜ.card := by
  have h1 : ∑ v ∈ C, (Cᶜ.filter (fun w => (Hypercube n).Adj v w)).card = C.card * (n-2) := by
    have hpt : ∀ v ∈ C, (Cᶜ.filter (fun w => (Hypercube n).Adj v w)).card = n-2 := by
      intro v hv
      have htot := hypercube_deg n v
      have hin := hdeg v hv
      have hunion : (C.filter (fun w => (Hypercube n).Adj v w)) ∪
          (Cᶜ.filter (fun w => (Hypercube n).Adj v w)) =
          Finset.univ.filter (fun w => (Hypercube n).Adj v w) := by
        ext w; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_compl, Finset.mem_univ,
          true_and]; tauto
      have hdisj : Disjoint (C.filter (fun w => (Hypercube n).Adj v w))
          (Cᶜ.filter (fun w => (Hypercube n).Adj v w)) := by
        rw [Finset.disjoint_left]
        intro w hw1 hw2
        exact (Finset.mem_compl.mp (Finset.mem_filter.mp hw2).1) (Finset.mem_filter.mp hw1).1
      have hsum := Finset.card_union_of_disjoint hdisj
      rw [hunion, htot, hin] at hsum
      omega
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, smul_eq_mul]
  have h2 : ∑ v ∈ C, (Cᶜ.filter (fun w => (Hypercube n).Adj v w)).card ≤ n * Cᶜ.card := by
    calc ∑ v ∈ C, (Cᶜ.filter (fun w => (Hypercube n).Adj v w)).card
        = ∑ w ∈ Cᶜ, (C.filter (fun v => (Hypercube n).Adj w v)).card := by
          simp only [Finset.card_filter]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun v _ => ?_
          simp [adj_comm]
      _ ≤ ∑ w ∈ Cᶜ, n := by
          refine Finset.sum_le_sum fun w _ => ?_
          calc (C.filter (fun v => (Hypercube n).Adj w v)).card
              ≤ (Finset.univ.filter (fun v => (Hypercube n).Adj w v)).card :=
                Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
            _ = n := hypercube_deg n w
      _ = n * Cᶜ.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  exact h1 ▸ h2

private lemma tiny (n : ℕ) (hn : 2 ≤ n) (ht : n ≤ 4) :
    LongestCoilInTheBox n ≤ (if n = 2 then 4 else if n = 3 then 6 else 10) := by
  apply csSup_le'
  rintro k ⟨S,hS⟩
  obtain ⟨C,rfl,hd⟩ := coil_finset_props hS
  have he := boundary C hd
  have hc : C.card + Cᶜ.card = 2^n := by
    rw [Finset.card_add_card_compl, Fintype.card_finset, Fintype.card_fin]
  interval_cases n <;> norm_num only [Nat.reducePow] at hc <;> norm_num at he ⊢ <;> omega

/-- Huang's cube degree bound applied to a subset of maximum induced degree two. -/
def H1 : Prop :=
  ∀ n : ℕ, 5 ≤ n → ∀ C : Finset (Finset (Fin n)),
    (∀ v ∈ C, (C.filter (fun w ↦ (Hypercube n).Adj v w)).card ≤ 2) →
    C.card ≤ 2^(n-1)

/-- The high-dimensional regime of Zémor's estimate, where the correction in
the denominator is positive and the half-cube bound no longer suffices. -/
def H2 : Prop :=
  ∀ n : ℕ, 10584 < n → (LongestCoilInTheBox n : ℝ) ≤ 1 + (2:ℝ) ^ (n-1) * (6 * n) /
        (6 * n + 1 / (6 * Real.sqrt 6) * Real.sqrt n - 7)

theorem main : H1 → H2 → type_of% @SnakeInBox.coil_upper_bound := by
  intro huang zemor n hn
  by_cases hlarge : 10584 < n
  · exact zemor n hlarge
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  let d := 1 / (6 * Real.sqrt 6) * Real.sqrt n
  have d0 : 0 ≤ d := by positivity
  have den : 0 < 6 * (n:ℝ) + d - 7 := by linarith
  change (LongestCoilInTheBox n : ℝ) ≤ 1 + (2:ℝ)^(n-1) * (6*n) / (6*n+d-7)
  rw [add_comm (1:ℝ), ← sub_le_iff_le_add, le_div_iff₀ den]
  have root6 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 6)
  have rootn := Real.sq_sqrt (Nat.cast_nonneg n : 0 ≤ (n:ℝ))
  have hr6 := Real.sqrt_nonneg (6:ℝ)
  have hrn := Real.sqrt_nonneg (n:ℝ)
  by_cases hsmall : n ≤ 4
  · have hd : d ≤ 1 := by
      have hn4 : (n:ℝ) ≤ 4 := by exact_mod_cast hsmall
      dsimp [d]
      rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)]
      apply (sq_le_sq₀ hrn (by positivity)).mp
      nlinarith
    let B : ℕ := if n = 2 then 4 else if n = 3 then 6 else 10
    have hcnt : (LongestCoilInTheBox n : ℝ) ≤ (B : ℝ) := by exact_mod_cast tiny n hn hsmall
    have hb : 0 ≤ (B:ℝ)-1 := by dsimp [B]; split_ifs <;> norm_num
    calc
      _ ≤ ((B:ℝ)-1)*(6*n+d-7) := mul_le_mul_of_nonneg_right (by linarith) den.le
      _ ≤ ((B:ℝ)-1)*(6*n-6) := mul_le_mul_of_nonneg_left (by linarith) hb
      _ ≤ _ := by dsimp only [B]; interval_cases n <;> norm_num
  · have hmax : LongestCoilInTheBox n ≤ 2^(n-1) := by
      apply csSup_le'
      rintro k ⟨S,hS⟩
      obtain ⟨C,rfl,hd⟩ := coil_finset_props hS
      exact huang n (by omega) C (fun v hv ↦ (hd v hv).le)
    have hmaxR : (LongestCoilInTheBox n : ℝ) ≤ (2:ℝ)^(n-1) := by exact_mod_cast hmax
    have hd : d ≤ 7 := by
      have hN : (n:ℝ) ≤ 10584 := by exact_mod_cast (Nat.le_of_not_gt hlarge)
      dsimp [d]
      rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)]
      apply (sq_le_sq₀ hrn (by positivity)).mp
      nlinarith
    calc
      _ ≤ (2:ℝ)^(n-1)*(6*n+d-7) := mul_le_mul_of_nonneg_right (by linarith) den.le
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

end OMA.R_SnakeInBox_coil_upper_bound_R1