import FormalConjectures.ErdosProblems.«723»

-- Reduction Erdos723.erdos_723.variants.eq_12.R2: a projective plane of order 12 from nets.
-- Credit: @sntntHb
-- The final step (lemmas third_point and plane_of_blocks) is copied from the merged reduction
-- Erdos723.erdos_723.variants.eq_12.R1 by @ian139.

/-
A net of order 12 and degree k is a family of k functions on the 144 cells of a 12 by 12 grid,
any two of which determine a cell: (f i x, f j x) determines x for i ≠ j. Degree k + 2 nets are
exactly k mutually orthogonal Latin squares of order 12 (the extra two coordinates are row and
column). A net of degree 13 (eleven MOLS) is an affine plane of order 12; adding the 13 points at
infinity and the line at infinity gives the projective plane, which is what main does.

* H1, the open core: a net of order 12 and degree 11, that is, nine MOLS of order 12. The best
  known is five MOLS (Johnson, Dulmage and Mendelsohn 1961); McKay's five MOLS have no common
  transversal, so they do not extend even to six.
* H2, a known theorem: every net of order 12 and degree 11 (deficiency 2) completes to one of
  degree 13. This is the case n = 12, d = 2 of R. H. Bruck, Finite nets II, Pacific J. Math.
  13 (1963), Theorem 4.3, since 12 > p(1) = 4.
-/

namespace OMA.R_Erdos723_erdos_723_variants_eq_12_R2

open Configuration

/-- The open core: a net of order 12 and degree 11 (nine mutually orthogonal Latin squares). -/
def H1 : Prop :=
  ∃ f : Fin 11 → Fin 12 × Fin 12 → Fin 12,
    ∀ i j, i ≠ j → Function.Injective (fun x => (f i x, f j x))

/-- Bruck's completion theorem for deficiency two at order 12: every net of degree 11 completes
to a net of degree 13 (an affine plane). -/
def H2 : Prop :=
  ∀ f : Fin 11 → Fin 12 × Fin 12 → Fin 12,
    (∀ i j, i ≠ j → Function.Injective (fun x => (f i x, f j x))) →
    ∃ g : Fin 13 → Fin 12 × Fin 12 → Fin 12,
      ∀ i j, i ≠ j → Function.Injective (fun x => (g i x, g j x))

lemma third_point (s : Finset (Fin 157)) (hs : s.card = 13) (a b : Fin 157) :
    ∃ x ∈ s, x ≠ a ∧ x ≠ b := by
  classical
  by_contra hn
  have sub : s ⊆ {a, b} := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra! h
    exact hn ⟨x, hx, h⟩
  have hle := Finset.card_le_card sub
  have hpair : ({a, b} : Finset (Fin 157)).card ≤ 2 := by
    by_cases h : a = b <;> simp [h]
  omega

lemma plane_of_blocks (B : Fin 157 → Finset (Fin 157)) (size : ∀ i, (B i).card = 13)
    (meet : ∀ i j, i ≠ j → ∃! x, x ∈ B i ∧ x ∈ B j) :
    type_of% @Erdos723.erdos_723.variants.eq_12 := by
  classical
  letI : Membership (Fin 157) (Fin 157) := ⟨fun l p => p ∈ B l⟩
  have outside (i j : Fin 157) : ∃ p, p ∉ B i ∧ p ∉ B j := by
    by_contra hn
    have sub : Finset.univ ⊆ B i ∪ B j := by
      intro p _
      simp only [Finset.mem_union]
      by_contra! hh
      exact hn ⟨p, hh⟩
    have hle := Finset.card_le_card sub
    have hu := Finset.card_union_le (B i) (B j)
    simp only [Finset.card_univ, Fintype.card_fin] at hle
    rw [size, size] at hu
    omega
  have misses (p : Fin 157) : ∃ i, p ∉ B i := by
    by_contra! hall
    choose f hf using fun i => third_point (B i) (size i) p p
    have inj : Function.Injective f := by
      intro i j h
      by_contra hij
      exact (hf i).2.1 ((meet i j hij).unique ⟨(hf i).1, h ▸ (hf j).1⟩ ⟨hall i, hall j⟩)
    obtain ⟨i, hi⟩ := (Finite.surjective_of_injective inj) p
    exact (hf i).2.1 hi
  letI : HasPoints (Fin 157) (Fin 157) := {
    exists_point := fun l => (outside l l).imp fun _ h => h.1
    exists_line := misses
    eq_or_eq := by
      intro p q l m hpl hql hpm hqm
      by_cases h : l = m
      · exact Or.inr h
      · exact Or.inl ((meet l m h).unique ⟨hpl, hpm⟩ ⟨hql, hqm⟩)
    mkPoint := fun {l m} h => (meet l m h).choose
    mkPoint_ax := fun {l m} h => (meet l m h).choose_spec.1 }
  letI := HasPoints.hasLines (P := Fin 157) (L := Fin 157) rfl
  obtain ⟨p, hp, _⟩ := meet 0 1 (by decide)
  obtain ⟨l, hl⟩ := misses p
  have hl0 : l ≠ 0 := by rintro rfl; exact hl hp.1
  obtain ⟨z, hz, _⟩ := meet l 0 hl0
  obtain ⟨q, hq, hqz, hqp⟩ := third_point (B 0) (size 0) z p
  obtain ⟨u, hu⟩ := outside 0 1
  letI pp : ProjectivePlane (Fin 157) (Fin 157) :=
    { (inferInstance : HasPoints (Fin 157) (Fin 157)),
      (inferInstance : HasLines (Fin 157) (Fin 157)) with
      exists_config := ⟨u, p, q, l, 0, 1, hu.1, hu.2, hl, hp.1, hp.2,
        fun h => hqz ((meet l 0 hl0).unique ⟨h, hq⟩ hz), hq,
        fun h => hqp ((meet 0 1 (by decide)).unique ⟨hq, h⟩ hp)⟩ }
  refine ⟨Fin 157, Fin 157, inferInstance, inferInstance, inferInstance, pp, ?_⟩
  have hc := ProjectivePlane.pointCount_eq (Fin 157) (0 : Fin 157)
  have hk : pointCount (Fin 157) (0 : Fin 157) = 13 := by
    change Nat.card {p : Fin 157 // p ∈ B 0} = 13
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using size 0
  change ProjectivePlane.order (Fin 157) (Fin 157) = 12
  omega

lemma pair_bij (g : Fin 13 → Fin 12 × Fin 12 → Fin 12)
    (hg : ∀ i j, i ≠ j → Function.Injective (fun x => (g i x, g j x))) (i j : Fin 13)
    (hij : i ≠ j) : Function.Bijective (fun x => (g i x, g j x)) :=
  (Fintype.bijective_iff_injective_and_card _).2 ⟨hg i j hij, rfl⟩

lemma fiber_card (g : Fin 13 → Fin 12 × Fin 12 → Fin 12)
    (hg : ∀ i j, i ≠ j → Function.Injective (fun x => (g i x, g j x))) (i : Fin 13) (v : Fin 12) :
    (Finset.univ.filter (fun x => g i x = v)).card = 12 := by
  classical
  obtain ⟨j, hij⟩ : ∃ j, i ≠ j := ⟨if i = 0 then 1 else 0, by split_ifs with h <;> simp [h]⟩
  have hb := pair_bij g hg i j hij
  have key : (Finset.univ.filter (fun x => g i x = v)).card =
      (Finset.univ.filter (fun q : Fin 12 × Fin 12 => q.1 = v)).card := by
    apply Finset.card_nbij (fun x => (g i x, g j x))
    · intro x hx
      simpa using hx
    · intro x _ y _ h
      exact hb.1 h
    · intro q hq
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hq
      obtain ⟨x, hx⟩ := hb.2 q
      refine ⟨x, ?_, hx⟩
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      rw [← hq]
      exact congrArg Prod.fst hx
  have h12 : ∀ w : Fin 12,
      (Finset.univ.filter (fun q : Fin 12 × Fin 12 => q.1 = w)).card = 12 := by decide
  rw [key, h12]

theorem main : H1 → H2 → type_of% @Erdos723.erdos_723.variants.eq_12 := by
  classical
  intro h1 h2
  obtain ⟨f, hf⟩ := h1
  obtain ⟨g, hg⟩ := h2 f hf
  let blk : (Fin 13 × Fin 12) ⊕ Unit → Finset ((Fin 12 × Fin 12) ⊕ Fin 13) := fun l =>
    match l with
    | Sum.inl (i, v) => (Finset.univ.filter (fun x => g i x = v)).disjSum {i}
    | Sum.inr _ => (∅ : Finset (Fin 12 × Fin 12)).disjSum Finset.univ
  have mem_l (i : Fin 13) (v : Fin 12) (p : (Fin 12 × Fin 12) ⊕ Fin 13) :
      p ∈ blk (Sum.inl (i, v)) ↔ (∃ x, p = Sum.inl x ∧ g i x = v) ∨ p = Sum.inr i := by
    cases p <;> simp [blk]
  have mem_inf (u : Unit) (p : (Fin 12 × Fin 12) ⊕ Fin 13) :
      p ∈ blk (Sum.inr u) ↔ ∃ k, p = Sum.inr k := by
    cases p <;> simp [blk]
  have size0 (l : (Fin 13 × Fin 12) ⊕ Unit) : (blk l).card = 13 := by
    rcases l with ⟨i, v⟩ | u
    · simp only [blk, Finset.card_disjSum, Finset.card_singleton]
      rw [fiber_card g hg i v]
    · simp [blk]
  have meet0 (l m : (Fin 13 × Fin 12) ⊕ Unit) (hlm : l ≠ m) :
      ∃! p, p ∈ blk l ∧ p ∈ blk m := by
    rcases l with ⟨i, v⟩ | u <;> rcases m with ⟨j, w⟩ | u'
    · by_cases hij : i = j
      · subst hij
        have hvw : v ≠ w := fun h => hlm (by rw [h])
        refine ⟨Sum.inr i, ⟨(mem_l i v _).2 (Or.inr rfl), (mem_l i w _).2 (Or.inr rfl)⟩, ?_⟩
        rintro p ⟨hp1, hp2⟩
        rcases (mem_l i v p).1 hp1 with ⟨x, rfl, hx⟩ | h
        · rcases (mem_l i w _).1 hp2 with ⟨y, hy, hy'⟩ | h
          · cases hy; exact absurd (hx.symm.trans hy') hvw
          · cases h
        · exact h
      · obtain ⟨x, hx⟩ := (pair_bij g hg i j hij).2 (v, w)
        simp only [Prod.mk.injEq] at hx
        refine ⟨Sum.inl x, ⟨(mem_l i v _).2 (Or.inl ⟨x, rfl, hx.1⟩),
          (mem_l j w _).2 (Or.inl ⟨x, rfl, hx.2⟩)⟩, ?_⟩
        rintro p ⟨hp1, hp2⟩
        rcases (mem_l i v p).1 hp1 with ⟨y, rfl, hy⟩ | rfl
        · rcases (mem_l j w _).1 hp2 with ⟨z, hz, hz'⟩ | h
          · cases hz
            have := hg i j hij (show (g i y, g j y) = (g i x, g j x) by
              rw [hy, hz', hx.1, hx.2])
            rw [this]
          · cases h
        · rcases (mem_l j w _).1 hp2 with ⟨z, hz, _⟩ | h
          · cases hz
          · cases h; exact absurd rfl hij
    · refine ⟨Sum.inr i, ⟨(mem_l i v _).2 (Or.inr rfl), (mem_inf u' _).2 ⟨i, rfl⟩⟩, ?_⟩
      rintro p ⟨hp1, hp2⟩
      obtain ⟨k, rfl⟩ := (mem_inf u' p).1 hp2
      rcases (mem_l i v _).1 hp1 with ⟨x, hx, _⟩ | h
      · cases hx
      · exact h
    · refine ⟨Sum.inr j, ⟨(mem_inf u _).2 ⟨j, rfl⟩, (mem_l j w _).2 (Or.inr rfl)⟩, ?_⟩
      rintro p ⟨hp1, hp2⟩
      obtain ⟨k, rfl⟩ := (mem_inf u p).1 hp1
      rcases (mem_l j w _).1 hp2 with ⟨x, hx, _⟩ | h
      · cases hx
      · exact h
    · exact absurd rfl hlm
  have cP : Fintype.card ((Fin 12 × Fin 12) ⊕ Fin 13) = 157 := by simp
  have cL : Fintype.card ((Fin 13 × Fin 12) ⊕ Unit) = 157 := by simp
  let eP := Fintype.equivFinOfCardEq cP
  let eL := Fintype.equivFinOfCardEq cL
  apply plane_of_blocks (fun k => (blk (eL.symm k)).map eP.toEmbedding)
  · intro k
    rw [Finset.card_map]
    exact size0 _
  · intro a b hab
    have hne : eL.symm a ≠ eL.symm b := fun h => hab (eL.symm.injective h)
    obtain ⟨p, ⟨hp1, hp2⟩, hu⟩ := meet0 _ _ hne
    refine ⟨eP p, ?_, ?_⟩
    · simp only [Finset.mem_map_equiv, Equiv.symm_apply_apply]
      exact ⟨hp1, hp2⟩
    · rintro y ⟨hy1, hy2⟩
      rw [Finset.mem_map_equiv] at hy1 hy2
      rw [← hu _ ⟨hy1, hy2⟩, Equiv.apply_symm_apply]

end OMA.R_Erdos723_erdos_723_variants_eq_12_R2
