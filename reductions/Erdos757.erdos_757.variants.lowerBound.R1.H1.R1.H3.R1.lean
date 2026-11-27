import OMAReductions.R_Erdos757_erdos_757_variants_lowerBound_R1_H1_R1

/-! Delete vertices of degree at least four and pay for adding them to a transversal.
In maximum degree two, a dual matching covers two hyperedges per selected vertex.
The remaining case has maximum degree exactly three. -/

namespace OMA.R_Erdos757_erdos_757_variants_lowerBound_R1_H1_R1_H3_R1
open Finset
open scoped Classical

/-- A matching estimate on the dual subcubic graph. Each selected vertex represents
an edge of that graph, joining its two incident hyperedges. -/
def H1 : Prop :=
  ∀ (A : Finset ℝ) (E : Finset (Finset ℝ)), (∀ e ∈ E, e ⊆ A ∧ e.card = 3) →
    (∀ e ∈ E, ∀ f ∈ E, e ≠ f → (e ∩ f).card ≤ 1) →
    let L := fun v : ℝ => E.filter fun e => v ∈ e
    (∀ v ∈ A, (L v).card ≤ 2) → ∃ M ⊆ A,
      (∀ v ∈ M, (L v).card = 2) ∧ (M : Set ℝ).PairwiseDisjoint L ∧
      14*E.card ≤ 5*A.card + 17*M.card

/-- The remaining extremal case of the Henning–Yeo transversal theorem. -/
def H2 : Prop :=
  ∀ (A : Finset ℝ) (E : Finset (Finset ℝ)), (∀ e ∈ E, e ⊆ A ∧ e.card = 3) →
    (∀ e ∈ E, ∀ f ∈ E, e ≠ f → (e ∩ f).card ≤ 1) →
    (¬ ∃ f : Fin 7 ↪ ℝ, {f 0,f 1,f 2} ∈ E ∧ {f 0,f 3,f 4} ∈ E ∧
        {f 0,f 5,f 6} ∈ E ∧ {f 1,f 3,f 5} ∈ E ∧ {f 2,f 4,f 6} ∈ E) →
    (∀ v ∈ A, (E.filter fun e => v ∈ e).card ≤ 3) →
    (∃ v ∈ A, (E.filter fun e => v ∈ e).card = 3) →
    ∃ T ⊆ A, (∀ e ∈ E, (e ∩ T).Nonempty) ∧ 17*T.card ≤ 5*A.card+3*E.card

theorem main : H1 → H2 → OMA.R_Erdos757_erdos_757_variants_lowerBound_R1_H1_R1.H3 := by
  classical
  intro matching cubic A
  induction A using Finset.strongInductionOn
  rename_i A ih
  intro E uniform linear free
  let L (v : ℝ) := E.filter fun e => v ∈ e
  by_cases high : ∃ v ∈ A, 4 ≤ (L v).card
  · obtain ⟨v,hv,deg⟩ := high
    let F := E.filter fun e => v ∉ e
    have sub : F ⊆ E := filter_subset _ _
    have uniform' (e) (he : e ∈ F) : e ⊆ A.erase v ∧ e.card = 3 := by
      refine ⟨?_,(uniform e (sub he)).2⟩
      intro x hx
      refine mem_erase.mpr ⟨?_,(uniform e (sub he)).1 hx⟩
      rintro rfl
      exact (mem_filter.mp he).2 hx
    obtain ⟨T,hT,hit,bound⟩ := ih (A.erase v) (erase_ssubset hv) F uniform'
      (fun e he f hf h => linear e (sub he) f (sub hf) h)
      (fun ⟨f,h₁,h₂,h₃,h₄,h₅⟩ => free ⟨f,sub h₁,sub h₂,sub h₃,sub h₄,sub h₅⟩)
    refine ⟨insert v T,insert_subset hv (hT.trans (erase_subset _ _)),?_,?_⟩
    · intro e he
      by_cases h : v ∈ e
      · exact ⟨v,mem_inter.mpr ⟨h,mem_insert_self _ _⟩⟩
      · obtain ⟨x,hx⟩ := hit e (mem_filter.mpr ⟨he,h⟩)
        exact ⟨x,mem_inter.mpr ⟨(mem_inter.mp hx).1,mem_insert_of_mem (mem_inter.mp hx).2⟩⟩
    · have a := card_erase_add_one hv
      have b : (L v).card + F.card = E.card := card_filter_add_card_filter_not (s := E) (fun e => v ∈ e)
      have c := card_insert_le v T
      omega
  · have max3 (v) (hv : v ∈ A) : (L v).card ≤ 3 := by
      by_contra! h
      exact high ⟨v,hv,h⟩
    by_cases exists3 : ∃ v ∈ A, (L v).card = 3
    · exact cubic A E uniform linear free max3 exists3
    · have max2 (v) (hv : v ∈ A) : (L v).card ≤ 2 := by
        have := max3 v hv
        have ne : (L v).card ≠ 3 := fun h => exists3 ⟨v,hv,h⟩
        omega
      obtain ⟨M,hM,two,disj,lower⟩ := matching A E uniform linear max2
      let B := M.biUnion L
      have sub : B ⊆ E := by
        intro e he
        obtain ⟨v,hv,h⟩ := mem_biUnion.mp he
        exact (mem_filter.mp h).1
      have size : B.card = 2*M.card := by
        calc
          B.card = ∑ v ∈ M, (L v).card := card_biUnion disj
          _ = ∑ _v ∈ M, 2 := sum_congr rfl two
          _ = _ := by simp [Nat.mul_comm]
      let F := E \ B
      have rem : F.card + B.card = E.card := card_sdiff_add_card_eq_card sub
      let rep (e : Finset ℝ) := if h : e.Nonempty then h.choose else 0
      have repMem (e) (he : e ∈ E) : rep e ∈ e := by
        have h := card_pos.mp (show 0 < e.card by rw [(uniform e he).2]; decide)
        simpa [rep,h] using h.choose_spec
      let T := M ∪ F.image rep
      refine ⟨T,union_subset hM ?_,?_,?_⟩
      · intro x hx
        obtain ⟨e,he,rfl⟩ := mem_image.mp hx
        have h := (mem_sdiff.mp he).1
        exact (uniform e h).1 (repMem e h)
      · intro e he
        by_cases h : e ∈ B
        · obtain ⟨v,hv,hev⟩ := mem_biUnion.mp h
          exact ⟨v,mem_inter.mpr ⟨(mem_filter.mp hev).2,mem_union_left _ hv⟩⟩
        · exact ⟨rep e,mem_inter.mpr ⟨repMem e he,
            mem_union_right _ (mem_image_of_mem _ (mem_sdiff.mpr ⟨he,h⟩))⟩⟩
      · have ht : T.card ≤ M.card + (F.image rep).card := card_union_le _ _
        have hi : (F.image rep).card ≤ F.card := card_image_le
        omega

end OMA.R_Erdos757_erdos_757_variants_lowerBound_R1_H1_R1_H3_R1
