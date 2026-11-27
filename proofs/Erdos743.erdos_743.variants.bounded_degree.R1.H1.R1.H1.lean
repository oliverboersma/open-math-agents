import OMAReductions.R_Erdos743_erdos_743_variants_bounded_degree_R1_H1_R1
import Mathlib

-- Step Erdos743.erdos_743.variants.bounded_degree.R1.H1.R1.H1: hypothesis H1 of reduction Erdos743.erdos_743.variants.bounded_degree.R1.H1.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Finset SimpleGraph
open scoped Classical

/-! The degrees of a tree on k vertices sum to 2k - 2 and are all positive. Vertices of degree two
contribute exactly twice their number, so the degrees in B sum to 2|B| - 2. Every vertex of B other
than a leaf has degree at least three, which gives |B| ≤ 2L - 2 and hence the two bounds. -/

theorem OMA.solution : OMA.R_Erdos743_erdos_743_variants_bounded_degree_R1_H1_R1.H1 := by
  intro k G hk hT L B
  have hnt : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
  have hpos : ∀ v, 0 < G.degree v := fun v => hT.connected.preconnected.degree_pos_of_nontrivial v
  have hsum : ∑ v, G.degree v + 2 = 2 * k := by
    rw [sum_degrees_eq_twice_card_edges]
    have := hT.card_edgeFinset
    rw [Fintype.card_fin] at this
    omega
  set C := univ.filter (fun v => ¬ G.degree v ≠ 2) with hC
  have h1 : ∑ v, G.degree v = ∑ v ∈ B, G.degree v + ∑ v ∈ C, G.degree v :=
    (sum_filter_add_sum_filter_not _ _ _).symm
  have h2 : ∑ v ∈ C, G.degree v = C.card * 2 := by
    apply sum_const_nat
    intro x hx
    simp only [hC, mem_filter, mem_univ, true_and, not_not] at hx
    exact hx
  have h3 : B.card + C.card = k := by
    rw [card_filter_add_card_filter_not, card_univ, Fintype.card_fin]
  set D := B.filter (fun v => ¬ G.degree v = 1) with hD
  have hBL : B.filter (fun v => G.degree v = 1) = univ.filter (fun v => G.degree v = 1) := by
    ext v; simp only [B, mem_filter, mem_univ, true_and]; omega
  have h4 : ∑ v ∈ B, G.degree v = L + ∑ v ∈ D, G.degree v := by
    rw [← sum_filter_add_sum_filter_not B (fun v => G.degree v = 1), hBL]
    congr 1
    rw [sum_const_nat (m := 1) (fun x hx => (mem_filter.mp hx).2)]
    simp [L]
  have h5 : D.card * 3 ≤ ∑ v ∈ D, G.degree v := by
    rw [← smul_eq_mul, ← sum_const]
    apply sum_le_sum
    intro v hv
    simp only [hD, B, mem_filter, mem_univ, true_and] at hv
    have := hpos v
    omega
  have h6 : B.card = L + D.card := by
    rw [← card_filter_add_card_filter_not (fun v => G.degree v = 1), hBL]
  omega
