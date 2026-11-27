import OMAReductions.R_LovaszPlummerConjecture_sheehan_conjecture_R1_H2_R1

/-! A two-step rotation of the marked rim reduces the even case to two
chord orbits. In the remaining case a specified edge has an absent translate.
The indexing lemma is adapted from open-math-agents PR 5313. -/
namespace OMA.R_LovaszPlummerConjecture_sheehan_conjecture_R1_H2_R1_H2_R1
open SimpleGraph Finset LovaszPlummerConjecture

private lemma cycle_indexing {V : Type} [Fintype V] [DecidableEq V] [NeZero (Fintype.card V)]
    (G : SimpleGraph V) (v : V) (c : G.Walk v v)
    (hc : LovaszPlummerConjecture.IsHamiltonianCycle G c) :
    3 ≤ Fintype.card V ∧
    ∃ (e : Fin (Fintype.card V) ≃ V),
      (∀ i : Fin (Fintype.card V), G.Adj (e i) (e (i + 1))) ∧
      (∀ x y : V, s(x, y) ∈ c.edges ↔
        ∃ i : Fin (Fintype.card V), s(x, y) = s(e i, e (i + 1))) := by
  have hcyc : c.IsCycle := hc.1
  have hham : ∀ w, w ∈ c.support := hc.2
  have h3 : 3 ≤ c.length := hcyc.three_le_length
  have hnodup : c.support.dropLast.Nodup := hcyc.nodup_dropLast_support
  have hlen_sup : c.support.length = c.length + 1 := Walk.length_support c
  have hlen_dl : c.support.dropLast.length = c.length := by
    rw [List.length_dropLast, hlen_sup]; omega
  have hmem_dl : ∀ w : V, w ∈ c.support.dropLast := by
    intro w
    have hw := hham w
    have hne : c.support ≠ [] := Walk.support_ne_nil c
    have hsplit : c.support = c.support.dropLast ++ [c.support.getLast hne] :=
      (List.dropLast_append_getLast hne).symm
    rw [hsplit, List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · exact hw
    · have hlast : c.support.getLast hne = v := Walk.getLast_support c
      have hpos : 0 < c.support.dropLast.length := by rw [hlen_dl]; omega
      have h0 : c.support.dropLast[0] = v := by
        rw [List.getElem_dropLast (by omega), ← List.head_eq_getElem_zero hne, Walk.head_support c]
      have hmem : v ∈ c.support.dropLast :=
        Eq.subst (motive := fun x => x ∈ c.support.dropLast) h0 (List.getElem_mem hpos)
      rw [hlast]
      exact hmem
  have hcard : c.length = Fintype.card V := by
    have h1 : c.support.dropLast.toFinset = Finset.univ := by
      ext w; simp [hmem_dl w]
    have h2 := congrArg Finset.card h1
    rw [List.toFinset_card_of_nodup hnodup, Finset.card_univ, hlen_dl] at h2
    exact h2
  have hn3 : 3 ≤ Fintype.card V := hcard ▸ h3
  have hbij : Function.Bijective (fun i : Fin (Fintype.card V) =>
      c.support.dropLast[i.val]'(by rw [hlen_dl, hcard]; exact i.isLt)) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun i j hij => ?_, by simp⟩
    exact Fin.ext (hnodup.getElem_inj_iff.mp hij)
  let e : Fin (Fintype.card V) ≃ V := Equiv.ofBijective _ hbij
  have he_def : ∀ i : Fin (Fintype.card V),
      e i = c.support.dropLast[i.val]'(by rw [hlen_dl, hcard]; exact i.isLt) :=
    fun _ => rfl
  have hgetVert_eq : ∀ i : ℕ, (hi : i < Fintype.card V) →
      c.getVert i = e ⟨i, hi⟩ := by
    intro i hi
    rw [he_def, Walk.getVert_eq_support_getElem c (by rw [hcard]; omega),
      List.getElem_dropLast]
  have hlast_eq : c.getVert (Fintype.card V) = e ⟨0, by omega⟩ := by
    calc
      c.getVert (Fintype.card V) = c.getVert c.length := by rw [hcard]
      _ = v := Walk.getVert_length c
      _ = c.support.head (Walk.support_ne_nil c) := (Walk.head_support c).symm
      _ = c.support[0]'(by rw [hlen_sup]; omega) := List.head_eq_getElem_zero _
      _ = c.support.dropLast[0]'(by rw [hlen_dl]; omega) := (List.getElem_dropLast _).symm
      _ = e ⟨0, by omega⟩ := (he_def ⟨0, by omega⟩).symm
  have hfin_last : ∀ i : Fin (Fintype.card V), i.val + 1 = Fintype.card V →
      i + 1 = ⟨0, by omega⟩ := fun i h => by
    ext
    simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < Fintype.card V), h]
  have hfin_lt : ∀ (i : Fin (Fintype.card V)) (hlt : i.val + 1 < Fintype.card V),
      i + 1 = ⟨i.val + 1, hlt⟩ := fun i hlt => by
    ext
    simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < Fintype.card V),
      Nat.mod_eq_of_lt hlt]
  have hadj : ∀ i : Fin (Fintype.card V), G.Adj (e i) (e (i + 1)) := by
    intro i
    have hi_len : i.val < c.length := by rw [hcard]; exact i.isLt
    have hadj_i := c.adj_getVert_succ hi_len
    rw [hgetVert_eq i.val i.isLt] at hadj_i
    by_cases hlast : i.val + 1 = Fintype.card V
    · have hi1 := hfin_last i hlast
      have hgv : c.getVert (i.val + 1) = e (i + 1) := by
        rw [hlast, hi1]; exact hlast_eq
      rwa [hgv] at hadj_i
    · have hi_lt : i.val + 1 < Fintype.card V := by omega
      have hi1 := hfin_lt i hi_lt
      have hgv : c.getVert (i.val + 1) = e (i + 1) := by
        rw [hi1]; exact hgetVert_eq (i.val + 1) hi_lt
      rwa [hgv] at hadj_i
  have hedges : ∀ x y : V, s(x, y) ∈ c.edges ↔
      ∃ i : Fin (Fintype.card V), s(x, y) = s(e i, e (i + 1)) := by
    intro x y
    rw [Walk.mk_mem_edges_iff_exists]
    constructor
    · rintro ⟨i, hi, hs⟩
      have hiV : i < Fintype.card V := hcard ▸ hi
      refine ⟨⟨i, hiV⟩, ?_⟩
      rw [← hs, hgetVert_eq i hiV]
      by_cases hlast : i + 1 = Fintype.card V
      · have hi1 := hfin_last ⟨i, hiV⟩ hlast
        rw [hlast, hi1, hlast_eq]
      · have hi_lt : i + 1 < Fintype.card V := by omega
        have hi1 := hfin_lt ⟨i, hiV⟩ hi_lt
        rw [hi1, hgetVert_eq (i + 1) hi_lt]
    · rintro ⟨i, hs⟩
      refine ⟨i.val, by rw [hcard]; exact i.isLt, ?_⟩
      rw [hs, hgetVert_eq i.val i.isLt]
      by_cases hlast : i.val + 1 = Fintype.card V
      · have hi1 := hfin_last i hlast
        rw [hlast, hi1, hlast_eq]
      · have hi_lt : i.val + 1 < Fintype.card V := by omega
        have hi1 := hfin_lt i hi_lt
        rw [hi1, hgetVert_eq (i.val + 1) hi_lt]
  exact ⟨hn3, e, hadj, hedges⟩

/-- Two-step rotation symmetry forces another cycle at minimum degree three. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (∀ u, 3 ≤ G.degree u) → ∀ (v : V) (c : G.Walk v v), IsHamiltonianCycle G c →
    ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ (e : Fin n ≃ V),
    (∀ x y, s(x,y) ∈ c.edges ↔ ∃ i : Fin n, s(x,y)=s(e i,e (i+1))) →
    (∀ i j, G.Adj (e i) (e j) → G.Adj (e (i+2)) (e (j+2))) →
    ∃ (w : V) (d : G.Walk w w), IsHamiltonianCycle G d ∧ d.edges.toFinset ≠ c.edges.toFinset

open scoped Classical in
/-- The unmatched, undominated residual with a specific broken two-step rotation. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (_four : ∀ u, G.degree u=4) (v : V) (c : G.Walk v v), IsHamiltonianCycle G c →
    (¬ ∃ (M : SimpleGraph V) (e : Sym2 V), M ≤ G ∧ e ∈ c.edges ∧
      (∀ u, M.degree u ≤ 1) ∧ (∀ u, M.degree u = 0 → u ∈ e) ∧
      (∀ f ∈ c.edges, f ∉ M.edgeSet)) →
    (¬ ∃ I : Finset V, I.Nonempty ∧
      (∀ x ∈ I, ∀ y ∈ I, s(x,y) ∉ c.edges) ∧
      (∀ u : V, u ∉ I → (∃ x ∈ I, s(u,x) ∈ c.edges) →
        ∃ w ∈ I, G.Adj u w ∧ s(u,w) ∉ c.edges)) →
    ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ (e : Fin n ≃ V),
    (∀ x y, s(x,y) ∈ c.edges ↔ ∃ i : Fin n, s(x,y)=s(e i,e (i+1))) →
    ∀ i j : Fin n, G.Adj (e i) (e j) → ¬G.Adj (e (i+2)) (e (j+2)) →
    ∃ (w : V) (d : G.Walk w w), IsHamiltonianCycle G d ∧ d.edges.toFinset ≠ c.edges.toFinset

theorem main : H1 → H2 → OMA.R_LovaszPlummerConjecture_sheehan_conjecture_R1_H2_R1.H2 := by
  intro periodic asymmetric V _ _ G _ four v c hc unmatched undominated
  letI : Nonempty V := ⟨v⟩
  letI : NeZero (Fintype.card V) := ⟨Nat.ne_of_gt Fintype.card_pos⟩
  obtain ⟨size,e,_,rim⟩ := cycle_indexing G v c hc
  by_cases rotates : ∀ i j : Fin (Fintype.card V),
      G.Adj (e i) (e j) → G.Adj (e (i+2)) (e (j+2))
  · exact periodic G (fun u => by rw [four u]; decide) v c hc (Fintype.card V) size e rim rotates
  · push_neg at rotates
    obtain ⟨i,j,edge,missing⟩ := rotates
    exact asymmetric G four v c hc unmatched undominated (Fintype.card V) size e rim i j edge missing

end OMA.R_LovaszPlummerConjecture_sheehan_conjecture_R1_H2_R1_H2_R1
