import FormalConjectures.Wikipedia.AlspachConjecture
import Mathlib

/-!
Bryant, Horsley and Pettersson, arXiv:1204.3709, Lemma 2 and Theorem 3.
Their even-order decompositions include a perfect matching among the pieces.
The hypotheses below allow the construction to choose that matching.
The proof transports the cycles to the complement of the prescribed matching.

The edge-indexing argument is adapted from E713MatchingIso.matching_iso in
Erdos713.erdos_713.parts.i.R1. The cycle transport generalizes moveCycle and
moveMem from AlspachConjecture.alspach_conjecture.R1.H1.
-/

namespace OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R2

open SimpleGraph AlspachConjecture
open scoped Classical

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

theorem iso_decomposition [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    [DecidableRel G.Adj] [DecidableRel H.Adj] (f : G ≃g H)
    {m : Multiset ℕ} {C : Multiset (Cycle G)}
    (hc : IsCycleDecomposition G C) (hl : lengths C = m) :
    ∃ D : Multiset (Cycle H), IsCycleDecomposition H D ∧ lengths D = m := by
  classical
  let move (c : Cycle G) : Cycle H :=
    ⟨f c.base, c.walk.map f.toHom, c.isCycle.map f.injective⟩
  have mem (c : Cycle G) (a b : V) :
      s(f a, f b) ∈ (move c).edges ↔ s(a, b) ∈ c.edges := by
    change s(f a, f b) ∈ (c.walk.map f.toHom).edges ↔ _
    rw [Walk.edges_map]
    change Sym2.map f s(a, b) ∈ List.map (Sym2.map f) c.edges ↔ s(a, b) ∈ c.edges
    exact List.mem_map_of_injective (Sym2.map.injective f.injective)
  refine ⟨C.map move, ?_, ?_⟩
  · intro e
    induction e using Sym2.ind with
    | h x y =>
      obtain ⟨a, rfl⟩ := f.surjective x
      obtain ⟨b, rfl⟩ := f.surjective y
      intro he
      have hxy : H.Adj (f a) (f b) := H.mem_edgeFinset.mp he
      have hab : s(a, b) ∈ G.edgeFinset := G.mem_edgeFinset.mpr (f.map_rel_iff.mp hxy)
      rw [Multiset.filter_map, Multiset.card_map]
      simpa [Function.comp_def, mem] using hc s(a, b) hab
  · have len (c : Cycle G) : (move c).length = c.length := Walk.length_map _ _
    simpa [lengths, Multiset.map_map, Function.comp_def, len] using hl

open Finset

theorem matching_iso {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (regular : ∀ v, G.degree v = 1)
    {k : ℕ} (hk : G.edgeFinset.card = k) :
    ∃ M : SimpleGraph (Fin k × Bool),
      (∀ x y, M.Adj x y ↔ x.1 = y.1 ∧ x.2 ≠ y.2) ∧ Nonempty (M ≃g G) := by
  let number : Fin k ≃ G.edgeFinset := (Finset.equivFinOfCardEq hk).symm
  let endpt (e : G.edgeFinset) : Bool ≃ e.val.toFinset :=
    finTwoEquiv.symm.trans (Finset.equivFinOfCardEq (G.card_toFinset_mem_edgeFinset e)).symm
  let f (p : Fin k × Bool) : V := (endpt (number p.1) p.2).val
  have incident (p : Fin k × Bool) : (number p.1).val ∈ G.incidenceFinset (f p) :=
    (G.mem_incidenceFinset _ _).mpr ⟨G.mem_edgeFinset.mp (number p.1).property,
      Sym2.mem_toFinset.mp (endpt (number p.1) p.2).property⟩
  have unique (x : V) : ∀ e ∈ G.incidenceFinset x, ∀ d ∈ G.incidenceFinset x, e = d := by
    apply card_le_one.mp
    rw [card_incidenceFinset_eq_degree,regular]
  have inj : Function.Injective f := by
    rintro ⟨i,a⟩ ⟨j,b⟩ eq
    have ie := incident (i,a)
    rw [eq] at ie
    have same : (number i).val = (number j).val := unique _ _ ie _ (incident (j,b))
    have ij := number.injective (Subtype.ext same)
    subst j
    have ab := (endpt (number i)).injective (Subtype.ext eq)
    exact congrArg (Prod.mk i) ab
  have surj : Function.Surjective f := by
    intro x
    obtain ⟨e,he⟩ := card_pos.mp (by rw [card_incidenceFinset_eq_degree,regular]; decide :
      0 < (G.incidenceFinset x).card)
    let E : G.edgeFinset := ⟨e,G.incidenceFinset_subset x he⟩
    obtain ⟨i,hi⟩ := number.surjective E
    have hx : x ∈ (number i).val.toFinset := by
      rw [hi]
      exact Sym2.mem_toFinset.mpr ((G.mem_incidenceFinset _ _).mp he).2
    exact ⟨(i,(endpt (number i)).symm ⟨x,hx⟩),congrArg Subtype.val ((endpt (number i)).apply_symm_apply _)⟩
  let e := Equiv.ofBijective f ⟨inj,surj⟩
  refine ⟨G.comap e,?_,⟨SimpleGraph.Iso.comap e G⟩⟩
  intro p q
  change G.Adj (f p) (f q) ↔ _
  constructor
  · intro h
    have edgep : s(f p,f q) ∈ G.incidenceFinset (f p) :=
      (G.mem_incidenceFinset _ _).mpr (G.mk'_mem_incidenceSet_left_iff.mpr h)
    have edgeq : s(f p,f q) ∈ G.incidenceFinset (f q) :=
      (G.mem_incidenceFinset _ _).mpr (G.mk'_mem_incidenceSet_right_iff.mpr h)
    have index : p.1 = q.1 := number.injective (Subtype.ext
      ((unique _ _ (incident p) _ edgep).trans (unique _ _ edgeq _ (incident q))))
    exact ⟨index,fun same => h.ne (congrArg f (Prod.ext index same))⟩
  · rintro ⟨index,different⟩
    have ne : f p ≠ f q := fun same => different (congrArg Prod.snd (inj same))
    have hi := (G.mem_incidenceFinset _ _).mp (incident p)
    have hj := (G.mem_incidenceFinset _ _).mp (incident q)
    rw [← index] at hj
    exact G.adj_of_mem_incidenceSet ne hi hj


theorem matchings_complements_iso {n : ℕ}
    (I J : (completeGraph (Fin n)).Subgraph) (hi : I.IsPerfectMatching)
    (hj : J.IsPerfectMatching) :
    Nonempty ((completeGraph (Fin n) \ I.spanningCoe) ≃g
      (completeGraph (Fin n) \ J.spanningCoe)) := by
  classical
  have regular (T : (completeGraph (Fin n)).Subgraph) (ht : T.IsPerfectMatching)
      (v : Fin n) : T.spanningCoe.degree v = 1 :=
    degree_eq_one_iff_existsUnique_adj.mpr (Subgraph.isPerfectMatching_iff.mp ht v)
  have card (T : (completeGraph (Fin n)).Subgraph) (ht : T.IsPerfectMatching) :
      T.spanningCoe.edgeFinset.card = n / 2 := by
    have h := T.spanningCoe.sum_degrees_eq_twice_card_edges
    simp only [regular T ht, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one] at h
    omega
  obtain ⟨A, ha, ⟨fa⟩⟩ := matching_iso I.spanningCoe (regular I hi) (card I hi)
  obtain ⟨B, hb, ⟨fb⟩⟩ := matching_iso J.spanningCoe (regular J hj) (card J hj)
  have hab : A = B := by ext u v; exact (ha u v).trans (hb u v).symm
  subst B
  let f : I.spanningCoe ≃g J.spanningCoe := fa.symm.trans fb
  exact ⟨{ toEquiv := f.toEquiv
           map_rel_iff' := fun {a b} =>
             and_congr f.injective.ne_iff (not_congr f.map_rel_iff) }⟩

/-- Finite verification for even positive orders up to 14 (Lemma 2). -/
def H1 : Prop :=
  ∀ (n : ℕ), Even n → 0 < n → n ≤ 14 → ∀ (m : Multiset ℕ),
    (∀ k ∈ m, 3 ≤ k ∧ k ≤ n) → m.sum = n.choose 2 - n / 2 →
      ∃ J : (completeGraph (Fin n)).Subgraph, J.IsPerfectMatching ∧
        ∃ C : Multiset (Cycle (completeGraph (Fin n) \ J.spanningCoe)),
          IsCycleDecomposition (completeGraph (Fin n) \ J.spanningCoe) C ∧ lengths C = m

/-- Theorem 3 extends existence for ancestor lists to every admissible list. -/
def H2 : Prop :=
  ∀ (n : ℕ), Even n → 15 ≤ n →
    let admissible := fun m : Multiset ℕ =>
      (∀ k ∈ m, 3 ≤ k ∧ k ≤ n) ∧ m.sum = n.choose 2 - n / 2
    let ancestor := fun m : Multiset ℕ =>
      (m.filter (fun k => 6 ≤ k ∧ k < n)).card ≤ 1 ∧
      (3 ≤ m.count 5 → 2 * m.count 4 + 6 ≤ n) ∧
      (2 ≤ m.count 5 → 3 * m.count 3 + 10 ≤ n) ∧
      (1 ≤ m.count 4 → 1 ≤ m.count 5 → 3 * m.count 3 + 9 ≤ n) ∧
      (1 ≤ m.count 4 → m.count (n - 2) = 0 ∧ m.count (n - 1) = 0) ∧
      (1 ≤ m.count 5 → m.count (n - 4) = 0 ∧ m.count (n - 3) = 0 ∧
        m.count (n - 2) = 0 ∧ m.count (n - 1) = 0)
    let realizes := fun m : Multiset ℕ =>
      ∃ J : (completeGraph (Fin n)).Subgraph, J.IsPerfectMatching ∧
        ∃ C : Multiset (Cycle (completeGraph (Fin n) \ J.spanningCoe)),
          IsCycleDecomposition (completeGraph (Fin n) \ J.spanningCoe) C ∧ lengths C = m
    (∀ m, admissible m → ancestor m → realizes m) →
      ∀ m, admissible m → realizes m

/-- Construct the ancestor-list decompositions at large even orders. -/
def H3 : Prop :=
  ∀ (n : ℕ), Even n → 15 ≤ n →
    let admissible := fun m : Multiset ℕ =>
      (∀ k ∈ m, 3 ≤ k ∧ k ≤ n) ∧ m.sum = n.choose 2 - n / 2
    let ancestor := fun m : Multiset ℕ =>
      (m.filter (fun k => 6 ≤ k ∧ k < n)).card ≤ 1 ∧
      (3 ≤ m.count 5 → 2 * m.count 4 + 6 ≤ n) ∧
      (2 ≤ m.count 5 → 3 * m.count 3 + 10 ≤ n) ∧
      (1 ≤ m.count 4 → 1 ≤ m.count 5 → 3 * m.count 3 + 9 ≤ n) ∧
      (1 ≤ m.count 4 → m.count (n - 2) = 0 ∧ m.count (n - 1) = 0) ∧
      (1 ≤ m.count 5 → m.count (n - 4) = 0 ∧ m.count (n - 3) = 0 ∧
        m.count (n - 2) = 0 ∧ m.count (n - 1) = 0)
    let realizes := fun m : Multiset ℕ =>
      ∃ J : (completeGraph (Fin n)).Subgraph, J.IsPerfectMatching ∧
        ∃ C : Multiset (Cycle (completeGraph (Fin n) \ J.spanningCoe)),
          IsCycleDecomposition (completeGraph (Fin n) \ J.spanningCoe) C ∧ lengths C = m
    ∀ m, admissible m → ancestor m → realizes m

theorem main : H1 → H2 → H3 → type_of% @AlspachConjecture.alspach_conjecture.variants.even := by
  intro small lift build n hn I hI m hm hsum
  by_cases hn0 : n = 0
  · subst n
    have hm0 : m = 0 := by
      rw [Multiset.eq_zero_iff_forall_notMem]
      intro k hk
      have := hm k hk
      omega
    subst m
    refine ⟨0, fun e he => ?_, Multiset.map_zero _⟩
    exfalso
    induction e using Sym2.ind with
    | _ u _ => exact u.elim0
  · have solve : ∃ J : (completeGraph (Fin n)).Subgraph, J.IsPerfectMatching ∧
        ∃ C : Multiset (Cycle (completeGraph (Fin n) \ J.spanningCoe)),
          IsCycleDecomposition (completeGraph (Fin n) \ J.spanningCoe) C ∧ lengths C = m := by
      by_cases hs : n ≤ 14
      · exact small n hn (Nat.pos_of_ne_zero hn0) hs m hm hsum
      · have hl : 15 ≤ n := by omega
        exact lift n hn hl (build n hn hl) m ⟨hm, hsum⟩
    obtain ⟨J, hJ, C, hc, hlen⟩ := solve
    obtain ⟨f⟩ := matchings_complements_iso J I hJ hI
    exact iso_decomposition f hc hlen

end OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R2
