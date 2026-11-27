import FormalConjectures.Wikipedia.TotalColoringConjecture
import Mathlib

/-! Reduction of the total colouring conjecture for graphs of maximum degree at most 5 to
the Rosenfeld-Vijayaditya case (maximum degree 2 or 3) and Kostochka's theorem (maximum degree
4 or 5), handling the cases of maximum degree 0 and 1 directly by constructing explicit total
colourings with 2 and 3 colours respectively. -/

namespace OMA.R_TotalColoringConjecture_total_coloring_conjecture_variants_maxDegree_le_five_R1

open SimpleGraph

private lemma adj_false_of_maxDegree_eq_zero {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h0 : G.maxDegree = 0) {u v : V}
    (huv : G.Adj u v) : False := by
  have hdeg : G.degree u ≤ 0 := h0 ▸ G.degree_le_maxDegree u
  have hmem : v ∈ G.neighborFinset u := (G.mem_neighborFinset u v).2 huv
  have hpos : 0 < G.degree u := by
    rw [← G.card_neighborFinset_eq_degree]
    exact Finset.card_pos.2 ⟨v, hmem⟩
  omega

private lemma totalChromaticNumber_le_two_of_maxDegree_eq_zero {V : Type} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (h0 : G.maxDegree = 0) :
    G.totalChromaticNumber ≤ 2 := by
  refine Nat.sInf_le ⟨fun _ => (0 : Fin 2), ?_, ?_, ?_⟩
  · intro u v huv
    exact (adj_false_of_maxDegree_eq_zero G h0 huv).elim
  · intro e _ _ _
    rcases e with ⟨e, he⟩
    induction e using Sym2.ind with
    | _ u v =>
      exact (adj_false_of_maxDegree_eq_zero G h0 (G.mem_edgeSet.1 he)).elim
  · intro _ e _
    rcases e with ⟨e, he⟩
    induction e using Sym2.ind with
    | _ u v =>
      exact (adj_false_of_maxDegree_eq_zero G h0 (G.mem_edgeSet.1 he)).elim

private lemma adj_unique_of_maxDegree_le_one {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h1 : G.maxDegree ≤ 1) {u v w : V}
    (huv : G.Adj u v) (huw : G.Adj u w) : v = w := by
  have hdeg : (G.neighborFinset u).card ≤ 1 := by
    rw [G.card_neighborFinset_eq_degree]
    exact le_trans (G.degree_le_maxDegree u) h1
  exact Finset.card_le_one.1 hdeg v ((G.mem_neighborFinset u v).2 huv)
    w ((G.mem_neighborFinset u w).2 huw)

private lemma totalChromaticNumber_le_three_of_maxDegree_le_one {V : Type} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (h1 : G.maxDegree ≤ 1) :
    G.totalChromaticNumber ≤ 3 := by
  classical
  let e := Fintype.equivFin V
  let c : V ⊕ G.edgeSet → Fin 3 := fun x =>
    match x with
    | Sum.inl v => if ∃ w : V, G.Adj v w ∧ e v < e w then (0 : Fin 3) else (1 : Fin 3)
    | Sum.inr _ => (2 : Fin 3)
  refine Nat.sInf_le ⟨c, ?_, ?_, ?_⟩
  · intro u v huv
    simp only [c]
    have hne : e u ≠ e v := fun h => G.ne_of_adj huv (e.injective h)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hu : ∃ w : V, G.Adj u w ∧ e u < e w := ⟨v, huv, hlt⟩
      have hv : ¬ ∃ w : V, G.Adj v w ∧ e v < e w := by
        rintro ⟨w, hvw, hlt'⟩
        have hwu : w = u := adj_unique_of_maxDegree_le_one G h1 hvw huv.symm
        subst hwu
        exact lt_asymm hlt hlt'
      simp [hu, hv]
    · have hv : ∃ w : V, G.Adj v w ∧ e v < e w := ⟨u, huv.symm, hgt⟩
      have hu : ¬ ∃ w : V, G.Adj u w ∧ e u < e w := by
        rintro ⟨w, huw, hlt'⟩
        have hwv : w = v := adj_unique_of_maxDegree_le_one G h1 huw huv
        subst hwv
        exact lt_asymm hgt hlt'
      simp [hu, hv]
  · intro e1 e2 hne ⟨v, hv1, hv2⟩
    exfalso
    rcases e1 with ⟨s1, hs1⟩
    rcases e2 with ⟨s2, hs2⟩
    induction s1 using Sym2.ind with
    | _ u1 w1 =>
      induction s2 using Sym2.ind with
      | _ u2 w2 =>
        have hadj1 : G.Adj u1 w1 := G.mem_edgeSet.1 hs1
        have hadj2 : G.Adj u2 w2 := G.mem_edgeSet.1 hs2
        have h1' : v = u1 ∨ v = w1 := Sym2.mem_iff.1 hv1
        have h2' : v = u2 ∨ v = w2 := Sym2.mem_iff.1 hv2
        apply hne
        apply Subtype.ext
        rcases h1' with rfl | rfl <;> rcases h2' with rfl | rfl
        · have := adj_unique_of_maxDegree_le_one G h1 hadj1 hadj2
          subst this; rfl
        · have := adj_unique_of_maxDegree_le_one G h1 hadj1 hadj2.symm
          subst this; exact Sym2.eq_swap
        · have := adj_unique_of_maxDegree_le_one G h1 hadj1.symm hadj2
          subst this; exact Sym2.eq_swap
        · have := adj_unique_of_maxDegree_le_one G h1 hadj1.symm hadj2.symm
          subst this; rfl
  · intro v _ _
    simp only [c]
    split_ifs <;> decide

/-- Rosenfeld-Vijayaditya (1971): every finite simple graph of maximum degree 2 or 3 has
total chromatic number at most `Δ + 2`. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (G.maxDegree = 2 ∨ G.maxDegree = 3) → G.totalChromaticNumber ≤ G.maxDegree + 2

/-- Kostochka (1996): every finite simple graph of maximum degree 4 or 5 has
total chromatic number at most `Δ + 2`. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (G.maxDegree = 4 ∨ G.maxDegree = 5) → G.totalChromaticNumber ≤ G.maxDegree + 2

theorem main : H1 → H2 →
    type_of% @TotalColoringConjecture.total_coloring_conjecture.variants.maxDegree_le_five := by
  intro h1 h2 V _ _ G _ hΔ
  have hcases : G.maxDegree = 0 ∨ G.maxDegree = 1 ∨ (G.maxDegree = 2 ∨ G.maxDegree = 3) ∨
      (G.maxDegree = 4 ∨ G.maxDegree = 5) := by omega
  rcases hcases with h0 | h1' | h23 | h45
  · rw [h0]
    exact totalChromaticNumber_le_two_of_maxDegree_eq_zero G h0
  · rw [h1']
    exact totalChromaticNumber_le_three_of_maxDegree_le_one G (by omega)
  · exact h1 G h23
  · exact h2 G h45

end OMA.R_TotalColoringConjecture_total_coloring_conjecture_variants_maxDegree_le_five_R1
