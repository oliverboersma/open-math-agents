import OMAReductions.R_Erdos643_erdos_643_parts_ii_R1

namespace OMA.R_Erdos643_erdos_643_parts_ii_R1_H1_R1

/-- Combinatorial core: the forbidden repeated disjoint union forces the pair-shadow Hall
inequality in every subfamily of a uniform triple system. -/
def H1 : Prop := ∀ n : ℕ, ∀ H : Finset (Finset (Fin n)),
    (∀ e ∈ H, e.card = 3) → ¬ H.HasRepeatedDisjointUnion →
    ∀ F ⊆ H, F.card ≤
      (((Finset.univ : Finset (Fin n)).powersetCard 2).filter
        fun p => ∃ e ∈ F, p ⊆ e).card

/-- Finite matching/bookkeeping core: the pair-shadow Hall inequality yields the quadratic
edge bound. -/
def H2 : Prop := ∀ n : ℕ, ∀ H : Finset (Finset (Fin n)),
    (∀ e ∈ H, e.card = 3) →
    (∀ F ⊆ H, F.card ≤
      (((Finset.univ : Finset (Fin n)).powersetCard 2).filter
        fun p => ∃ e ∈ F, p ⊆ e).card) →
    H.card ≤ n.choose 2

open scoped Classical in

open scoped Classical in
private lemma mem_adm {n : ℕ} {P : Finset (Finset (Fin n)) → Prop}
    {H : Finset (Finset (Fin n))} :
    H ∈ (((Finset.univ : Finset (Fin n)).powersetCard 3).powerset.filter P) ↔
      H ⊆ (Finset.univ : Finset (Fin n)).powersetCard 3 ∧ P H := by
  rw [Finset.mem_filter, Finset.mem_powerset]

open scoped Classical in
private lemma extremal_le {n b : ℕ} {P : Finset (Finset (Fin n)) → Prop}
    (h : ∀ H : Finset (Finset (Fin n)),
      H ⊆ (Finset.univ : Finset (Fin n)).powersetCard 3 → P H → H.card ≤ b) :
    Hypergraph.extremalNumber n 3 P ≤ b := by
  unfold Hypergraph.extremalNumber
  exact Finset.sup_le fun H hH => h H (mem_adm.mp hH).1 (mem_adm.mp hH).2

theorem main : H1 → H2 → OMA.R_Erdos643_erdos_643_parts_ii_R1.H1 := by
  intro hhall hmatch n
  refine extremal_le fun H hsub hfree => ?_
  have huniform : ∀ e ∈ H, e.card = 3 := by
    intro e he
    exact Finset.mem_powersetCard.mp (hsub he) |>.2
  exact hmatch n H huniform (hhall n H huniform hfree)

end OMA.R_Erdos643_erdos_643_parts_ii_R1_H1_R1
