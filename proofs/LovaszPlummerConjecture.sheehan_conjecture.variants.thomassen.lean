import FormalConjectures.Wikipedia.LovaszPlummerConjecture

section R1Section
-- Reduction LovaszPlummerConjecture.sheehan_conjecture.variants.thomassen.R1 of Thomassen (1998): regular graphs of large degree.
-- Credit: @bradenchurch
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.SheehanR1

def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ), 300 ≤ r → (∀ v, G.degree v = r) →
    ∀ (v : V) (c : G.Walk v v), LovaszPlummerConjecture.IsHamiltonianCycle G c →
      ∃ I : Finset V,
        (∀ x ∈ I, ∀ y ∈ I, s(x, y) ∉ c.edges) ∧
        (∀ u : V, u ∉ I → ∃ w ∈ I, G.Adj u w ∧ s(u, w) ∉ c.edges)

def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (c : G.Walk v v), LovaszPlummerConjecture.IsHamiltonianCycle G c →
    ∀ I : Finset V,
      (∀ x ∈ I, ∀ y ∈ I, s(x, y) ∉ c.edges) →
      (∀ u : V, u ∉ I → ∃ w ∈ I, G.Adj u w ∧ s(u, w) ∉ c.edges) →
      ∃ (w : V) (c' : G.Walk w w), LovaszPlummerConjecture.IsHamiltonianCycle G c' ∧
        c'.edges.toFinset ≠ c.edges.toFinset

theorem main : H1 → H2 → type_of% @LovaszPlummerConjecture.sheehan_conjecture.variants.thomassen := by
  intro h1 h2 V _ _ G _ r hr hreg v c hc
  obtain ⟨I, hind, hdom⟩ := h1 G r hr hreg v c hc
  exact h2 G v c hc I hind hdom

end OMA.SheehanR1
end R1Section

section H1Section
/-
Thomassen's Local Lemma proof of hypothesis H1 for `LovaszPlummerConjecture.sheehan_conjecture`.
-/

-- Step LovaszPlummerConjecture.sheehan_conjecture.variants.thomassen.R1.H1: hypothesis H1 of reduction LovaszPlummerConjecture.sheehan_conjecture.variants.thomassen.R1
-- Credit: @luciusacarr (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace Helpers1

open SimpleGraph Finset

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

private def greedyPairs {n : ℕ} [NeZero n] (s : Finset (Fin n)) : Finset (Fin n) :=
  if hs : s.Nonempty then
    let x := s.min' hs
    have hsub : (s \ {x, x - 1, x + 1}).card < s.card := by
      refine Finset.card_lt_card ⟨Finset.sdiff_subset, ?_⟩
      intro h
      exact (Finset.mem_sdiff.mp (h (s.min'_mem hs))).2 (Finset.mem_insert_self _ _)
    insert x (greedyPairs (s \ {x, x - 1, x + 1}))
  else ∅
termination_by s.card

private lemma greedyPairs_subset {n : ℕ} [NeZero n] (s : Finset (Fin n)) :
    greedyPairs s ⊆ s := by
  unfold greedyPairs
  split_ifs with hs
  · have ih := greedyPairs_subset (s \ {s.min' hs, s.min' hs - 1, s.min' hs + 1})
    exact Finset.insert_subset_iff.mpr ⟨s.min'_mem hs, ih.trans Finset.sdiff_subset⟩
  · exact Finset.empty_subset _
termination_by s.card
decreasing_by
  refine Finset.card_lt_card ⟨Finset.sdiff_subset, ?_⟩
  intro h
  exact (Finset.mem_sdiff.mp (h (s.min'_mem hs))).2 (Finset.mem_insert_self _ _)

private lemma greedyPairs_indep {n : ℕ} [NeZero n] (s : Finset (Fin n)) :
    ∀ x ∈ greedyPairs s, ∀ y ∈ greedyPairs s, x ≠ y → y ≠ x - 1 ∧ y ≠ x + 1 := by
  unfold greedyPairs
  split_ifs with hs
  · set x₀ := s.min' hs
    set s' := s \ {x₀, x₀ - 1, x₀ + 1}
    have ih := greedyPairs_indep s'
    have hsub := greedyPairs_subset s'
    intro x hx y hy hne
    rw [Finset.mem_insert] at hx hy
    rcases hx with rfl | hx'
    · rcases hy with rfl | hy'
      · exact absurd rfl hne
      · have hmem := Finset.mem_sdiff.mp (hsub hy')
        have hnot := hmem.2
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
        exact ⟨hnot.2.1, hnot.2.2⟩
    · rcases hy with rfl | hy'
      · have hmem := Finset.mem_sdiff.mp (hsub hx')
        have hnot := hmem.2
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
        constructor
        · intro h; apply hnot.2.2; change x₀ = x - 1 at h; rw [h]; abel
        · intro h; apply hnot.2.1; change x₀ = x + 1 at h; rw [h]; abel
      · exact ih x hx' y hy' hne
  · intro x hx
    simp at hx
termination_by s.card
decreasing_by
  refine Finset.card_lt_card ⟨Finset.sdiff_subset, ?_⟩
  intro h
  exact (Finset.mem_sdiff.mp (h (s.min'_mem hs))).2 (Finset.mem_insert_self _ _)

private lemma greedyPairs_card {n : ℕ} [NeZero n] (s : Finset (Fin n)) :
    s.card ≤ 3 * (greedyPairs s).card := by
  unfold greedyPairs
  split_ifs with hs
  · set x₀ := s.min' hs
    set t : Finset (Fin n) := {x₀, x₀ - 1, x₀ + 1}
    set s' := s \ t
    have ih := greedyPairs_card s'
    have hx₀_not : x₀ ∉ greedyPairs s' := fun h =>
      (Finset.mem_sdiff.mp (greedyPairs_subset s' h)).2 (by simp [t])
    rw [Finset.card_insert_of_notMem hx₀_not]
    have ht_card : t.card ≤ 3 :=
      (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (Finset.card_le_two) 1)
    have hs_eq : s.card ≤ s'.card + t.card := by
      have : s ⊆ s' ∪ t := fun a ha => by
        by_cases hat : a ∈ t
        · exact Finset.mem_union_right _ hat
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ha, hat⟩)
      exact (Finset.card_le_card this).trans (Finset.card_union_le _ _)
    omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hs
    simp [hs]
termination_by s.card
decreasing_by
  refine Finset.card_lt_card ⟨Finset.sdiff_subset, ?_⟩
  intro h
  exact (Finset.mem_sdiff.mp (h (s.min'_mem hs))).2 (Finset.mem_insert_self _ _)

private lemma pow_four_thirds_ge (r : ℕ) (hr : 300 ≤ r) :
    3 ^ ((r - 2) / 3) * (4 * r ^ 2 + 1) ^ 2 ≤ 4 ^ ((r - 2) / 3) := by
  have hbase : ∀ k : ℕ, 300 ≤ k → k < 303 →
      3 ^ ((k - 2) / 3) * (4 * k ^ 2 + 1) ^ 2 ≤ 4 ^ ((k - 2) / 3) := by
    intro k hk1 hk2
    rcases (show k = 300 ∨ k = 301 ∨ k = 302 by omega) with rfl | rfl | rfl <;> norm_num
  have hstep : ∀ k : ℕ, 300 ≤ k →
      3 * (4 * (k + 3) ^ 2 + 1) ^ 2 ≤ 4 * (4 * k ^ 2 + 1) ^ 2 := by
    intro k hk
    nlinarith [hk]
  have hind : ∀ t : ℕ, ∀ k : ℕ, 300 ≤ k → k < 303 →
      3 ^ ((k + 3 * t - 2) / 3) * (4 * (k + 3 * t) ^ 2 + 1) ^ 2 ≤ 4 ^ ((k + 3 * t - 2) / 3) := by
    intro t
    induction t with
    | zero =>
      intro k hk1 hk2
      simpa using hbase k hk1 hk2
    | succ t ih =>
      intro k hk1 hk2
      have hk' := ih k hk1 hk2
      have heq1 : (k + 3 * (t + 1) - 2) / 3 = (k + 3 * t - 2) / 3 + 1 := by omega
      have heq2 : k + 3 * (t + 1) = (k + 3 * t) + 3 := by omega
      rw [heq1, heq2, pow_succ, pow_succ]
      have hst := hstep (k + 3 * t) (by omega)
      calc 3 ^ ((k + 3 * t - 2) / 3) * 3 * (4 * (k + 3 * t + 3) ^ 2 + 1) ^ 2
          = 3 ^ ((k + 3 * t - 2) / 3) * (3 * (4 * (k + 3 * t + 3) ^ 2 + 1) ^ 2) := by ring
        _ ≤ 3 ^ ((k + 3 * t - 2) / 3) * (4 * (4 * (k + 3 * t) ^ 2 + 1) ^ 2) := by gcongr
        _ = (3 ^ ((k + 3 * t - 2) / 3) * (4 * (k + 3 * t) ^ 2 + 1) ^ 2) * 4 := by ring
        _ ≤ 4 ^ ((k + 3 * t - 2) / 3) * 4 := by gcongr
  let t := (r - 300) / 3
  let k := 300 + (r - 300) % 3
  have hr_eq : r = k + 3 * t := by omega
  rw [hr_eq]
  exact hind t k (by omega) (by omega)

private lemma indep_split_product {n : ℕ}
    (U : Finset (Fin n)) (E F : Finset (Fin n → Bool))
    (hE : ∀ X Y : Fin n → Bool, (∀ u ∈ U, X u = Y u) → (X ∈ E ↔ Y ∈ E))
    (hF : ∀ X Y : Fin n → Bool, (∀ u ∉ U, X u = Y u) → (X ∈ F ↔ Y ∈ F)) :
    (E ∩ F).card * 2 ^ n = E.card * F.card := by
  classical
  let e : (Fin n → Bool) ≃ ((u : {x // x ∈ U}) → Bool) × ((u : {x // x ∉ U}) → Bool) :=
    { toFun := fun X => (fun u => X u.1, fun u => X u.1)
      invFun := fun ⟨X1, X2⟩ x => if hx : x ∈ U then X1 ⟨x, hx⟩ else X2 ⟨x, hx⟩
      left_inv := fun X => by
        ext x
        dsimp only
        split_ifs <;> rfl
      right_inv := fun ⟨X1, X2⟩ => by
        ext ⟨x, hx⟩
        · simp [dif_pos hx]
        · simp [dif_neg hx] }
  let E1 : Finset ((u : {x // x ∈ U}) → Bool) :=
    Finset.univ.filter fun X1 => e.symm (X1, fun _ => false) ∈ E
  let F2 : Finset ((u : {x // x ∉ U}) → Bool) :=
    Finset.univ.filter fun X2 => e.symm (fun _ => false, X2) ∈ F
  have hmemE : ∀ X, X ∈ E ↔ (e X).1 ∈ E1 := by
    intro X
    rw [mem_filter]
    refine ⟨fun h => ⟨mem_univ _, (hE X _ fun u hu => ?_).mp h⟩,
      fun h => (hE _ X fun u hu => ?_).mp h.2⟩
    · simp [e, dif_pos hu]
    · simp [e, dif_pos hu]
  have hmemF : ∀ X, X ∈ F ↔ (e X).2 ∈ F2 := by
    intro X
    rw [mem_filter]
    refine ⟨fun h => ⟨mem_univ _, (hF X _ fun u hu => ?_).mp h⟩,
      fun h => (hF _ X fun u hu => ?_).mp h.2⟩
    · simp [e, dif_neg hu]
    · simp [e, dif_neg hu]
  have hcE : E.card = E1.card * 2 ^ (Finset.univ \ U).card := by
    have : E.card = (E1 ×ˢ (Finset.univ : Finset ((u : {x // x ∉ U}) → Bool))).card := by
      refine Finset.card_bij (fun X _ => e X) ?_ ?_ ?_
      · intro X hX; rw [mem_product]; exact ⟨(hmemE X).mp hX, mem_univ _⟩
      · intro X₁ _ X₂ _ h; exact e.injective h
      · intro ⟨X1, X2⟩ hmem
        rw [mem_product] at hmem
        refine ⟨e.symm (X1, X2), ?_, e.apply_symm_apply _⟩
        rw [hmemE]; simpa using hmem.1
    rw [this, Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_bool]
    congr 2
    rw [← Finset.card_univ]
    refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
    · intro x _; exact mem_sdiff.mpr ⟨mem_univ _, x.2⟩
    · intro _ _ _ _ h; exact Subtype.ext h
    · intro y hy; exact ⟨⟨y, (mem_sdiff.mp hy).2⟩, mem_univ _, rfl⟩
  have hcF : F.card = 2 ^ U.card * F2.card := by
    have : F.card = ((Finset.univ : Finset ((u : {x // x ∈ U}) → Bool)) ×ˢ F2).card := by
      refine Finset.card_bij (fun X _ => e X) ?_ ?_ ?_
      · intro X hX; rw [mem_product]; exact ⟨mem_univ _, (hmemF X).mp hX⟩
      · intro X₁ _ X₂ _ h; exact e.injective h
      · intro ⟨X1, X2⟩ hmem
        rw [mem_product] at hmem
        refine ⟨e.symm (X1, X2), ?_, e.apply_symm_apply _⟩
        rw [hmemF]; simpa using hmem.2
    rw [this, Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
  have hcEF : (E ∩ F).card = E1.card * F2.card := by
    have : (E ∩ F).card = (E1 ×ˢ F2).card := by
      refine Finset.card_bij (fun X _ => e X) ?_ ?_ ?_
      · intro X hX; rw [mem_inter] at hX; rw [mem_product]; exact ⟨(hmemE X).mp hX.1, (hmemF X).mp hX.2⟩
      · intro X₁ _ X₂ _ h; exact e.injective h
      · intro ⟨X1, X2⟩ hmem
        rw [mem_product] at hmem
        refine ⟨e.symm (X1, X2), mem_inter.mpr ⟨?_, ?_⟩, e.apply_symm_apply _⟩
        · rw [hmemE]; simpa using hmem.1
        · rw [hmemF]; simpa using hmem.2
    rw [this, Finset.card_product]
  have hsum_card : U.card + (Finset.univ \ U).card = n := by
    have := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin n)) U
    simpa [Finset.inter_comm, add_comm] using this
  rw [hcEF, hcE, hcF]
  calc (E1.card * F2.card) * 2 ^ n
      = (E1.card * F2.card) * 2 ^ (U.card + (Finset.univ \ U).card) := by rw [hsum_card]
    _ = (E1.card * 2 ^ (Finset.univ \ U).card) * (2 ^ U.card * F2.card) := by
        rw [pow_add]; ring

private lemma finite_lll_nat {n D : ℕ} (hD : 1 ≤ D)
    (supp : Fin n → Finset (Fin n))
    (Bad : Fin n → Finset (Fin n → Bool))
    (hBad_dep : ∀ u (X Y : Fin n → Bool), (∀ x ∈ supp u, X x = Y x) → (X ∈ Bad u ↔ Y ∈ Bad u))
    (hdeg : ∀ u : Fin n,
      (Finset.univ.filter fun w : Fin n => ¬ Disjoint (supp w) (supp u)).card ≤ D)
    (hprob : ∀ u : Fin n, (Bad u).card * (D + 1) ^ 2 ≤ 2 ^ n) :
    (Finset.univ.filter fun X : Fin n → Bool => ∀ u : Fin n, X ∉ Bad u).Nonempty := by
  classical
  let Good (T : Finset (Fin n)) : Finset (Fin n → Bool) :=
    Finset.univ.filter fun X => ∀ w ∈ T, X ∉ Bad w
  have hclaim : ∀ m : ℕ, ∀ T : Finset (Fin n), T.card = m →
      0 < (Good T).card ∧
      ∀ u : Fin n, u ∉ T → (D + 1) * ((Good T) ∩ Bad u).card ≤ (Good T).card := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro T hm
      have ih' : ∀ T' : Finset (Fin n), T'.card < T.card →
          0 < (Good T').card ∧
          ∀ u : Fin n, u ∉ T' → (D + 1) * ((Good T') ∩ Bad u).card ≤ (Good T').card :=
        fun T' hlt => ih T'.card (hm ▸ hlt) T' rfl
      by_cases hT_empty : T = ∅
      · subst hT_empty
        have hG : Good ∅ = Finset.univ := by ext X; simp [Good]
        rw [hG, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
        refine ⟨pow_pos (by omega) n, fun u _ => ?_⟩
        rw [Finset.univ_inter]
        have hp := hprob u
        have hd1 : D + 1 ≤ (D + 1) ^ 2 := by nlinarith
        calc (D + 1) * (Bad u).card
            ≤ (D + 1) ^ 2 * (Bad u).card := Nat.mul_le_mul_right _ hd1
          _ = (Bad u).card * (D + 1) ^ 2 := mul_comm _ _
          _ ≤ 2 ^ n := hp
      · have step_ind : ∀ u : Fin n,
            (D + 1) * (Good T ∩ Bad u).card ≤ (Good T).card ∧ 0 < (Good T).card := by
          intro u
          let T1 := T.filter fun w => ¬ Disjoint (supp w) (supp u)
          let T2 := T \ T1
          have hT_split : T = T2 ∪ T1 := by
            ext w; simp [T2, T1]; tauto
          have hT2_card_le : T2.card ≤ T.card := Finset.card_le_card (Finset.sdiff_subset)
          have hGood_T_le_T2 : (Good T).card ≤ (Good T2).card := by
            refine Finset.card_le_card fun X hX => ?_
            rw [mem_filter] at hX ⊢
            exact ⟨mem_univ _, fun w hw => hX.2 w (Finset.sdiff_subset hw)⟩
          have hT1_card : T1.card ≤ D := by
            refine (Finset.card_le_card ?_).trans (hdeg u)
            intro w hw
            rw [mem_filter] at hw ⊢
            exact ⟨mem_univ _, hw.2⟩
          have hT2_good_Bad : (Good T2 ∩ Bad u).card * 2 ^ n = (Bad u).card * (Good T2).card := by
            rw [Finset.inter_comm]
            refine indep_split_product (supp u) (Bad u) (Good T2) (hBad_dep u) ?_
            intro X Y hXY
            simp only [Good, mem_filter, mem_univ, true_and]
            refine forall₂_congr fun w hw => ?_
            have hdisj : Disjoint (supp w) (supp u) := by
              have := (Finset.mem_sdiff.mp hw).2
              simpa [T1, Finset.mem_filter, Finset.mem_sdiff.mp hw |>.1] using this
            refine not_congr (hBad_dep w X Y fun x hx => ?_)
            exact hXY x (Finset.disjoint_left.mp hdisj hx)
          by_cases hT1_empty : T1 = ∅
          · have hTT2 : T = T2 := by rw [hT_split, hT1_empty, Finset.union_empty]
            rw [hTT2]
            have hT2_pos : 0 < (Good T2).card := by
              by_cases hu_empty : T2 = ∅
              · rw [hu_empty]
                have : Good ∅ = Finset.univ := by ext X; simp [Good]
                rw [this, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
                exact pow_pos (by omega) n
              · obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.mpr hu_empty
                have hlt : (T2.erase w).card < T.card := by
                  rw [hTT2]
                  exact Finset.card_erase_lt_of_mem hw
                have hprev := (ih' (T2.erase w) hlt).2 w (Finset.notMem_erase _ _)
                have hpos_er := (ih' (T2.erase w) hlt).1
                have heq_er : Good T2 = Good (T2.erase w) \ (Good (T2.erase w) ∩ Bad w) := by
                  ext X
                  simp only [Good, mem_sdiff, mem_filter, mem_univ, true_and, mem_inter]
                  constructor
                  · intro h
                    refine ⟨fun y hy => h y (Finset.erase_subset _ _ hy), fun ⟨_, hbad⟩ => h w hw hbad⟩
                  · rintro ⟨h1, h2⟩ y hy
                    by_cases hyw : y = w
                    · subst hyw; intro hb; exact h2 ⟨h1, hb⟩
                    · exact h1 y (Finset.mem_erase.mpr ⟨hyw, hy⟩)
                rw [heq_er, Finset.card_sdiff, Finset.inter_eq_left.mpr Finset.inter_subset_left]
                have hle : (D + 1) * (Good (T2.erase w) ∩ Bad w).card ≤ (Good (T2.erase w)).card := hprev
                have hdpos : 0 < D + 1 := by omega
                have : (Good (T2.erase w) ∩ Bad w).card < (Good (T2.erase w)).card := by
                  nlinarith [hD, hpos_er, hle]
                omega
            refine ⟨?_, hT2_pos⟩
            have h1 : (D + 1) * (Good T2 ∩ Bad u).card * 2 ^ n = (D + 1) * (Bad u).card * (Good T2).card := by
              calc (D + 1) * (Good T2 ∩ Bad u).card * 2 ^ n
                  = (D + 1) * ((Good T2 ∩ Bad u).card * 2 ^ n) := by ring
                _ = (D + 1) * ((Bad u).card * (Good T2).card) := by rw [hT2_good_Bad]
                _ = (D + 1) * (Bad u).card * (Good T2).card := by ring
            have h2 : (D + 1) * (Bad u).card * (Good T2).card ≤ 2 ^ n * (Good T2).card := by
              have hp := hprob u
              have hd1 : D + 1 ≤ (D + 1) ^ 2 := by nlinarith
              calc (D + 1) * (Bad u).card * (Good T2).card
                  ≤ (D + 1) ^ 2 * (Bad u).card * (Good T2).card := by gcongr
                _ = (Bad u).card * (D + 1) ^ 2 * (Good T2).card := by ring
                _ ≤ 2 ^ n * (Good T2).card := by gcongr
            rw [mul_comm (2 ^ n) _] at h2
            exact Nat.le_of_mul_le_mul_right (h1.trans_le h2) (pow_pos (by omega) n)
          · have hT1_ne : T1.Nonempty := Finset.nonempty_iff_ne_empty.mpr hT1_empty
            have hT2_lt : T2.card < T.card := by
              refine Finset.card_lt_card ⟨Finset.sdiff_subset, ?_⟩
              intro h
              obtain ⟨w, hw⟩ := hT1_ne
              have hwT : w ∈ T := (Finset.mem_filter.mp hw).1
              exact (Finset.mem_sdiff.mp (h hwT)).2 hw
            have hT2_pos : 0 < (Good T2).card := (ih' T2 hT2_lt).1
            have hdiff_bd : ∀ A : Finset (Fin n), A ⊆ T1 → T2.card + A.card ≤ T.card →
                (D + 1) * ((Good T2).card - (Good (T2 ∪ A)).card) ≤ A.card * (Good T2).card := by
              intro A hAT1 _
              induction A using Finset.induction_on with
              | empty => simp
              | @insert a A' ha ihA =>
                have haT1 : a ∈ T1 := hAT1 (mem_insert_self a A')
                have haT2 : a ∉ T2 := fun h => (Finset.mem_sdiff.mp h).2 haT1
                have ha_not : a ∉ T2 ∪ A' := fun h => by
                  rw [mem_union] at h; rcases h with h | h <;> contradiction
                have hlt' : (T2 ∪ A').card < T.card := by
                  have hsub : T2 ∪ A' ⊆ T \ {a} := by
                    intro w hw
                    rw [mem_sdiff, mem_singleton]
                    rw [mem_union] at hw
                    refine ⟨?_, fun h => ha_not (h ▸ (mem_union.mpr hw))⟩
                    rcases hw with hw | hw
                    · exact Finset.sdiff_subset hw
                    · exact (Finset.mem_filter.mp (hAT1 (mem_insert_of_mem hw))).1
                  have : (T \ {a}).card < T.card := by
                    refine Finset.card_lt_card ⟨Finset.sdiff_subset, ?_⟩
                    intro h
                    have haT : a ∈ T := (Finset.mem_filter.mp haT1).1
                    exact (Finset.mem_sdiff.mp (h haT)).2 (mem_singleton_self a)
                  exact (Finset.card_le_card hsub).trans_lt this
                have hstep_a := (ih' (T2 ∪ A') hlt').2 a ha_not
                have hle_T2 : (Good (T2 ∪ A')).card ≤ (Good T2).card := by
                  refine Finset.card_le_card fun X hX => ?_
                  rw [mem_filter] at hX ⊢
                  exact ⟨mem_univ _, fun w hw => hX.2 w (mem_union_left _ hw)⟩
                have hstep_le : (D + 1) * (Good (T2 ∪ A') ∩ Bad a).card ≤ (Good T2).card :=
                  hstep_a.trans hle_T2
                have hsplit_a : Good (T2 ∪ insert a A') =
                    Good (T2 ∪ A') \ (Good (T2 ∪ A') ∩ Bad a) := by
                  ext X
                  simp only [Good, mem_sdiff, mem_filter, mem_univ, true_and, mem_inter, mem_union, mem_insert]
                  constructor
                  · intro h
                    refine ⟨fun w hw => h w (by tauto), fun ⟨_, hb⟩ => h a (by tauto) hb⟩
                  · rintro ⟨h1, h2⟩ w (hw | rfl | hw)
                    · exact h1 w (Or.inl hw)
                    · intro hb; exact h2 ⟨h1, hb⟩
                    · exact h1 w (Or.inr hw)
                have hcard_a : (Good (T2 ∪ insert a A')).card =
                    (Good (T2 ∪ A')).card - (Good (T2 ∪ A') ∩ Bad a).card := by
                  rw [hsplit_a, Finset.card_sdiff, Finset.inter_eq_left.mpr Finset.inter_subset_left]
                have hsub_le : (Good (T2 ∪ insert a A')).card ≤ (Good (T2 ∪ A')).card := by
                  rw [hcard_a]; exact Nat.sub_le _ _
                have hle_T2' : (Good (T2 ∪ A')).card ≤ (Good T2).card := hle_T2
                have hih := ihA (Finset.Subset.trans (Finset.subset_insert _ _) hAT1) (by
                  have := Finset.card_le_card (Finset.subset_insert a A')
                  omega)
                rw [Finset.card_insert_of_notMem ha]
                have hint_le : (Good (T2 ∪ A') ∩ Bad a).card ≤ (Good (T2 ∪ A')).card :=
                  Finset.card_le_card Finset.inter_subset_left
                have heq_diff : (Good T2).card - (Good (T2 ∪ insert a A')).card =
                    ((Good T2).card - (Good (T2 ∪ A')).card) + (Good (T2 ∪ A') ∩ Bad a).card := by
                  omega
                rw [heq_diff, mul_add]
                calc (D + 1) * ((Good T2).card - (Good (T2 ∪ A')).card) +
                      (D + 1) * (Good (T2 ∪ A') ∩ Bad a).card
                    ≤ A'.card * (Good T2).card + (Good T2).card := by gcongr
                  _ = (A'.card + 1) * (Good T2).card := by ring
            have hT_bd := hdiff_bd T1 (Finset.Subset.refl _) (by
              have hs := Finset.card_sdiff_add_card_inter T T1
              have hinter : T ∩ T1 = T1 := Finset.inter_eq_right.mpr (Finset.filter_subset _ _)
              rw [hinter] at hs
              dsimp only [T2]
              omega)
            rw [← hT_split] at hT_bd
            have hT2_le_D1 : (Good T2).card ≤ (D + 1) * (Good T).card := by
              have h1 : (D + 1) * ((Good T2).card - (Good T).card) ≤ D * (Good T2).card :=
                hT_bd.trans (Nat.mul_le_mul_right _ hT1_card)
              have hdiff_eq : (Good T).card + ((Good T2).card - (Good T).card) = (Good T2).card :=
                Nat.add_sub_cancel' hGood_T_le_T2
              nlinarith [h1, hdiff_eq]
            have hT_pos : 0 < (Good T).card := by nlinarith [hT2_pos, hT2_le_D1]
            refine ⟨?_, hT_pos⟩
            have hsub_inter : (Good T ∩ Bad u).card ≤ (Good T2 ∩ Bad u).card := by
              refine Finset.card_le_card fun X hX => ?_
              rw [mem_inter] at hX ⊢
              refine ⟨?_, hX.2⟩
              rw [mem_filter] at hX ⊢
              exact ⟨mem_univ _, fun w hw => hX.1.2 w (Finset.sdiff_subset hw)⟩
            have hmul : (D + 1) * (Good T ∩ Bad u).card * 2 ^ n ≤ (Good T).card * 2 ^ n := by
              calc (D + 1) * (Good T ∩ Bad u).card * 2 ^ n
                  ≤ (D + 1) * (Good T2 ∩ Bad u).card * 2 ^ n := by gcongr
                _ = (D + 1) * ((Good T2 ∩ Bad u).card * 2 ^ n) := by ring
                _ = (D + 1) * (Bad u).card * (Good T2).card := by rw [hT2_good_Bad]; ring
                _ ≤ (D + 1) * (Bad u).card * ((D + 1) * (Good T).card) := by gcongr
                _ = (Bad u).card * (D + 1) ^ 2 * (Good T).card := by ring
                _ ≤ 2 ^ n * (Good T).card := by gcongr; exact hprob u
                _ = (Good T).card * 2 ^ n := by ring
            exact Nat.le_of_mul_le_mul_right hmul (pow_pos (by omega) n)
        obtain ⟨u₀, _⟩ := Finset.nonempty_iff_ne_empty.mpr hT_empty
        exact ⟨(step_ind u₀).2, fun u _ => (step_ind u).1⟩
  have hfinal := (hclaim (Fintype.card (Fin n)) Finset.univ rfl).1
  have : (Finset.univ.filter fun X : Fin n → Bool => ∀ u : Fin n, X ∉ Bad u) = Good Finset.univ := by
    ext X; simp [Good]
  rw [this]
  exact Finset.card_pos.mp hfinal

private lemma h1_main {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r)
    (v : V) (c : G.Walk v v) (hc : LovaszPlummerConjecture.IsHamiltonianCycle G c) :
    ∃ I : Finset V,
      (∀ x ∈ I, ∀ y ∈ I, s(x, y) ∉ c.edges) ∧
      (∀ u : V, u ∉ I → ∃ w ∈ I, G.Adj u w ∧ s(u, w) ∉ c.edges) := by
  classical
  have : Nonempty V := ⟨v⟩
  obtain ⟨hn3, e, hadj, hedges⟩ := cycle_indexing G v c hc
  let n := Fintype.card V
  have hr_lt : r < n := by
    have := G.degree_lt_card_verts v
    rw [hreg v] at this
    exact this
  have hn301 : 301 ≤ n := by omega
  have : NeZero n := ⟨by omega⟩
  let G' : SimpleGraph (Fin n) := SimpleGraph.comap e G
  have hG'_deg : ∀ u : Fin n, G'.degree u = r := by
    intro u
    rw [SimpleGraph.degree, SimpleGraph.neighborFinset_def]
    have hcard : (G'.neighborSet u).toFinset.card = (G.neighborSet (e u)).toFinset.card := by
      refine Finset.card_bij (fun w _ => e w) ?_ ?_ ?_
      · intro w hw; simpa [G'] using hw
      · intro w₁ _ w₂ _ h; exact e.injective h
      · intro y hy
        rw [Set.mem_toFinset, mem_neighborSet] at hy
        refine ⟨e.symm y, ?_, by simp⟩
        rw [Set.mem_toFinset, mem_neighborSet]
        simpa [G'] using hy
    rw [hcard]
    simpa [SimpleGraph.degree, SimpleGraph.neighborFinset_def] using hreg (e u)
  have hadj_next : ∀ u : Fin n, G'.Adj u (u + 1) := fun u => by
    simpa [G'] using hadj u
  have hadj_prev : ∀ u : Fin n, G'.Adj u (u - 1) := fun u => by
    have := (hadj (u - 1)).symm
    simpa [G'] using this
  have hprev_ne_next : ∀ u : Fin n, u - 1 ≠ u + 1 := by
    intro u h
    have h1 := congrArg (fun x => x - (u - 1)) h
    have htwo : (2 : Fin n) = (1 : Fin n) + 1 := by
      ext; simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < n),
        Nat.mod_eq_of_lt (by omega : 2 < n)]
    have h2 : u + 1 - (u - 1) = (2 : Fin n) := by rw [htwo]; abel
    rw [sub_self, h2] at h1
    have hv := congrArg Fin.val h1
    simp [Nat.mod_eq_of_lt (by omega : 2 < n)] at hv
  let greenNbrs (u : Fin n) : Finset (Fin n) :=
    ((G'.neighborFinset u).erase (u - 1)).erase (u + 1)
  have hgreen_card : ∀ u : Fin n, (greenNbrs u).card = r - 2 := by
    intro u
    have hmem1 : u - 1 ∈ G'.neighborFinset u := (mem_neighborFinset _ _ _).mpr (hadj_prev u)
    have hmem2 : u + 1 ∈ (G'.neighborFinset u).erase (u - 1) :=
      mem_erase.mpr ⟨(hprev_ne_next u).symm, (mem_neighborFinset _ _ _).mpr (hadj_next u)⟩
    dsimp only [greenNbrs]
    rw [card_erase_of_mem hmem2, card_erase_of_mem hmem1]
    change G'.degree u - 1 - 1 = r - 2
    rw [hG'_deg u, Nat.sub_sub]
  let m : ℕ := (r - 2) / 3
  have hm_ge : 99 ≤ m := by omega
  have hP_exists : ∀ u : Fin n, ∃ P : Finset (Fin n),
      P ⊆ greenNbrs u ∧ P.card = m ∧
      (∀ x ∈ P, ∀ y ∈ P, x ≠ y → y ≠ x - 1 ∧ y ≠ x + 1) := by
    intro u
    let pu := greedyPairs (greenNbrs u)
    have hcard_pu : m ≤ pu.card := by
      have h3 := greedyPairs_card (greenNbrs u)
      rw [hgreen_card u] at h3
      dsimp only [m, pu]
      omega
    obtain ⟨P, hP_sub, hP_card⟩ := Finset.exists_subset_card_eq hcard_pu
    refine ⟨P, hP_sub.trans (greedyPairs_subset _), hP_card, fun x hx y hy hne => ?_⟩
    exact greedyPairs_indep (greenNbrs u) x (hP_sub hx) y (hP_sub hy) hne
  let P : Fin n → Finset (Fin n) := fun u => Classical.choose (hP_exists u)
  have hP_sub : ∀ u, P u ⊆ greenNbrs u := fun u => (Classical.choose_spec (hP_exists u)).1
  have hP_card : ∀ u, (P u).card = m := fun u => (Classical.choose_spec (hP_exists u)).2.1
  have hP_ind : ∀ u, ∀ x ∈ P u, ∀ y ∈ P u, x ≠ y → y ≠ x - 1 ∧ y ≠ x + 1 :=
    fun u => (Classical.choose_spec (hP_exists u)).2.2
  let supp : Fin n → Finset (Fin n) := fun u => (P u).biUnion fun x => {x, x - 1}
  have hsupp_card : ∀ u, (supp u).card = 2 * m := by
    intro u
    have hpair_card : ∀ x : Fin n, ({x, x - 1} : Finset (Fin n)).card = 2 := by
      intro x
      have hne : x ≠ x - 1 := by
        intro h
        have hv := congrArg (fun a => a - (x - 1)) h
        have : x - (x - 1) = (1 : Fin n) := by abel
        rw [this, sub_self] at hv
        have hvv := congrArg Fin.val hv
        simp [Nat.mod_eq_of_lt (by omega : 1 < n)] at hvv
      exact Finset.card_pair hne
    dsimp only [supp]
    rw [Finset.card_biUnion]
    · rw [Finset.sum_congr rfl fun x _ => hpair_card x, Finset.sum_const, hP_card u, smul_eq_mul]
      omega
    · intro x hx y hy hne
      change Disjoint ({x, x - 1} : Finset (Fin n)) {y, y - 1}
      rw [Finset.disjoint_left]
      intro z hz₁ hz₂
      simp only [mem_insert, mem_singleton] at hz₁ hz₂
      have hind := hP_ind u x hx y hy hne
      rcases hz₁ with rfl | rfl <;> rcases hz₂ with h2 | h2
      · exact hne h2
      · exact hind.2 (by rw [h2]; abel)
      · exact hind.1 h2.symm
      · exact hne (by have := congrArg (· + 1) h2; simpa using this)
  let Bad : Fin n → Finset (Fin n → Bool) := fun u =>
    Finset.univ.filter fun X => ∀ x ∈ P u, ¬ (X x = true ∧ X (x - 1) = false)
  have hBad_dep : ∀ u (X Y : Fin n → Bool),
      (∀ z ∈ supp u, X z = Y z) → (X ∈ Bad u ↔ Y ∈ Bad u) := by
    intro u X Y hXY
    simp only [Bad, mem_filter, mem_univ, true_and]
    refine forall₂_congr fun x hx => ?_
    have hx1 : x ∈ supp u := mem_biUnion.mpr ⟨x, hx, by simp⟩
    have hx2 : x - 1 ∈ supp u := mem_biUnion.mpr ⟨x, hx, by simp⟩
    rw [hXY x hx1, hXY (x - 1) hx2]
  let D : ℕ := 4 * r ^ 2
  have hdeg : ∀ u : Fin n,
      (Finset.univ.filter fun w : Fin n => ¬ Disjoint (supp w) (supp u)).card ≤ D := by
    intro u
    let S := (supp u).biUnion fun z => greenNbrs z ∪ greenNbrs (z + 1)
    have hsub_S : (Finset.univ.filter fun w : Fin n => ¬ Disjoint (supp w) (supp u)) ⊆ S := by
      intro w hw
      rw [mem_filter] at hw
      rw [Finset.not_disjoint_iff] at hw
      obtain ⟨z, hzw, hzu⟩ := hw.2
      rw [mem_biUnion]
      refine ⟨z, hzu, ?_⟩
      dsimp only [supp] at hzw
      rw [mem_biUnion] at hzw
      obtain ⟨x, hxP, hzx⟩ := hzw
      have hxG : G'.Adj x w := ((mem_neighborFinset _ _ _).mp
        (mem_erase.mp (mem_erase.mp (hP_sub w hxP)).2).2).symm
      have hx_ne1 : x ≠ w - 1 := (mem_erase.mp (mem_erase.mp (hP_sub w hxP)).2).1
      have hx_ne2 : x ≠ w + 1 := (mem_erase.mp (hP_sub w hxP)).1
      have hw_gr : w ∈ greenNbrs x := by
        dsimp only [greenNbrs]
        rw [mem_erase, mem_erase, mem_neighborFinset]
        refine ⟨fun h => hx_ne1 (by rw [h]; abel),
          fun h => hx_ne2 (by rw [h]; abel), hxG⟩
      simp only [mem_insert, mem_singleton] at hzx
      rcases hzx with rfl | rfl
      · exact mem_union_left _ hw_gr
      · exact mem_union_right _ (by simpa using hw_gr)
    refine (Finset.card_le_card hsub_S).trans ?_
    calc S.card ≤ ∑ z ∈ supp u, (greenNbrs z ∪ greenNbrs (z + 1)).card := Finset.card_biUnion_le
      _ ≤ ∑ _z ∈ supp u, (2 * (r - 2)) := by
          refine Finset.sum_le_sum fun z _ => ?_
          exact (Finset.card_union_le _ _).trans (by rw [hgreen_card z, hgreen_card (z + 1)]; omega)
      _ = (supp u).card * (2 * (r - 2)) := by simp
      _ = (2 * m) * (2 * (r - 2)) := by rw [hsupp_card u]
      _ ≤ D := by
          have hm_le : m ≤ r := by omega
          have hrm2 : r - 2 ≤ r := by omega
          dsimp [D]
          nlinarith
  have hprob : ∀ u : Fin n, (Bad u).card * (D + 1) ^ 2 ≤ 2 ^ n := by
    intro u
    have hBad_card : (Bad u).card * 4 ^ m = 3 ^ m * 2 ^ n := by
      let pickX : {z // z ∈ supp u} → Fin n := fun p => (Finset.mem_biUnion.mp p.2).choose
      have hpick : ∀ p : {z // z ∈ supp u},
          pickX p ∈ P u ∧ (p.1 = pickX p ∨ p.1 = pickX p - 1) := by
        intro ⟨z, hz⟩
        have hspec := (Finset.mem_biUnion.mp hz).choose_spec
        refine ⟨hspec.1, ?_⟩
        dsimp only [pickX]
        simpa only [mem_insert, mem_singleton] using hspec.2
      let pairEquiv : {x // x ∈ P u} × Bool ≃ {z // z ∈ supp u} :=
        { toFun := fun ⟨⟨x, hx⟩, b⟩ =>
            if b then ⟨x, mem_biUnion.mpr ⟨x, hx, Finset.mem_insert_self _ _⟩⟩
            else ⟨x - 1, mem_biUnion.mpr ⟨x, hx, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩⟩
          invFun := fun p =>
            ⟨⟨pickX p, (hpick p).1⟩, decide (p.1 = pickX p)⟩
          left_inv := fun ⟨⟨x, hx⟩, b⟩ => by
            dsimp only
            cases b
            · simp only [Bool.false_eq_true, ↓reduceIte]
              have hzmem : x - 1 ∈ supp u :=
                mem_biUnion.mpr ⟨x, hx, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
              let p : {z // z ∈ supp u} := ⟨x - 1, hzmem⟩
              have hx'P : pickX p ∈ P u := (hpick p).1
              have hx'mem : x - 1 = pickX p ∨ x - 1 = pickX p - 1 := (hpick p).2
              have heq_x : pickX p = x := by
                by_contra hne
                have hind := hP_ind u x hx (pickX p) hx'P (Ne.symm hne)
                rcases hx'mem with h1 | h1
                · exact hind.1 h1.symm
                · exact hne (by have := congrArg (· + 1) h1; simpa using this.symm)
              have hne_sub : x - 1 ≠ x := by
                intro h
                have hv := congrArg (fun a => a - (x - 1)) h
                have : x - (x - 1) = (1 : Fin n) := by abel
                rw [sub_self, this] at hv
                have hvv := congrArg Fin.val hv
                simp [Nat.mod_eq_of_lt (by omega : 1 < n)] at hvv
              refine Prod.ext (Subtype.ext heq_x) ?_
              exact decide_eq_false (by change x - 1 ≠ pickX p; rw [heq_x]; exact hne_sub)
            · simp only [↓reduceIte]
              have hzmem : x ∈ supp u :=
                mem_biUnion.mpr ⟨x, hx, Finset.mem_insert_self _ _⟩
              let p : {z // z ∈ supp u} := ⟨x, hzmem⟩
              have hx'P : pickX p ∈ P u := (hpick p).1
              have hx'mem : x = pickX p ∨ x = pickX p - 1 := (hpick p).2
              have heq_x : pickX p = x := by
                by_contra hne
                have hind := hP_ind u x hx (pickX p) hx'P (Ne.symm hne)
                rcases hx'mem with h1 | h1
                · exact hne h1.symm
                · exact hind.2 (by rw [h1]; abel)
              refine Prod.ext (Subtype.ext heq_x) ?_
              exact decide_eq_true (by change x = pickX p; rw [heq_x])
          right_inv := fun p => by
            dsimp only
            by_cases hzx : p.1 = pickX p
            · rw [if_pos (decide_eq_true hzx)]
              exact Subtype.ext hzx.symm
            · rw [if_neg (by rw [decide_eq_false hzx]; decide)]
              exact Subtype.ext ((hpick p).2.resolve_left hzx).symm }
      let splitEquiv : (Fin n → Bool) ≃
          ({x // x ∈ P u} → Bool × Bool) × ({z // z ∉ supp u} → Bool) :=
        { toFun := fun X =>
            (fun ⟨x, _⟩ => (X x, X (x - 1)), fun ⟨z, _⟩ => X z)
          invFun := fun ⟨Y1, Y2⟩ z =>
            if hz : z ∈ supp u then
              let pb := pairEquiv.symm ⟨z, hz⟩
              if pb.2 then (Y1 pb.1).1 else (Y1 pb.1).2
            else Y2 ⟨z, hz⟩
          left_inv := fun X => by
            ext z
            by_cases hz : z ∈ supp u
            · simp only [dif_pos hz]
              rcases hpb : pairEquiv.symm ⟨z, hz⟩ with ⟨⟨x, hx⟩, b⟩
              have h1 : pairEquiv ⟨⟨x, hx⟩, b⟩ = ⟨z, hz⟩ := by
                rw [← hpb]; exact pairEquiv.apply_symm_apply _
              cases b
              · change X (x - 1) = X z
                exact congrArg X (congrArg Subtype.val h1)
              · change X x = X z
                exact congrArg X (congrArg Subtype.val h1)
            · simp [dif_neg hz]
          right_inv := fun ⟨Y1, Y2⟩ => by
            refine Prod.ext (funext fun x => Prod.ext ?_ ?_) (funext fun x => ?_)
            · have hx1 : x.1 ∈ supp u := mem_biUnion.mpr ⟨x.1, x.2, Finset.mem_insert_self _ _⟩
              have hp1 : pairEquiv.symm ⟨x.1, hx1⟩ = (x, true) := by
                apply pairEquiv.injective; rw [pairEquiv.apply_symm_apply]; rfl
              simp [dif_pos hx1, hp1]
            · have hx2 : x.1 - 1 ∈ supp u := mem_biUnion.mpr ⟨x.1, x.2, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
              have hp2 : pairEquiv.symm ⟨x.1 - 1, hx2⟩ = (x, false) := by
                apply pairEquiv.injective; rw [pairEquiv.apply_symm_apply]; rfl
              simp [dif_pos hx2, hp2]
            · simp [dif_neg x.2] }
      let goodPairs : Finset (Bool × Bool) := {(false, false), (false, true), (true, true)}
      have hgp_card : goodPairs.card = 3 := by decide
      let B1 : Finset ({x // x ∈ P u} → Bool × Bool) :=
        Finset.univ.filter fun Y1 => ∀ x, Y1 x ∈ goodPairs
      have hB1_card : B1.card = 3 ^ m := by
        have hbij_b1 : B1.card = Fintype.card ({x // x ∈ P u} → goodPairs) := by
          refine Finset.card_bij (fun Y1 hY1 x => ⟨Y1 x, (mem_filter.mp hY1).2 x⟩) ?_ ?_ ?_
          · intro _ _; exact mem_univ _
          · intro Y₁ _ Y₂ _ h
            ext x
            · exact congrArg (fun f => (f x).1.1) h
            · exact congrArg (fun f => (f x).1.2) h
          · intro f _
            exact ⟨fun x => (f x).1, mem_filter.mpr ⟨mem_univ _, fun x => (f x).2⟩, rfl⟩
        rw [hbij_b1, Fintype.card_fun, Fintype.card_coe, hgp_card, Fintype.card_coe, hP_card u]
      have hBad_bij : (Bad u).card = (B1 ×ˢ (Finset.univ : Finset ({z // z ∉ supp u} → Bool))).card := by
        refine Finset.card_bij (fun X _ => splitEquiv X) ?_ ?_ ?_
        · intro X hX
          rw [mem_filter] at hX
          rw [mem_product, mem_filter]
          refine ⟨⟨mem_univ _, fun ⟨x, hx⟩ => ?_⟩, mem_univ _⟩
          have hnot := hX.2 x hx
          change (X x, X (x - 1)) ∈ goodPairs
          rcases Bool.dichotomy (X x) with hx1 | hx1 <;>
            rcases Bool.dichotomy (X (x - 1)) with hx2 | hx2 <;> rw [hx1, hx2]
          · exact decide_eq_true_iff.mp (by decide : decide ((false, false) ∈ goodPairs) = true)
          · exact decide_eq_true_iff.mp (by decide : decide ((false, true) ∈ goodPairs) = true)
          · exact absurd ⟨hx1, hx2⟩ hnot
          · exact decide_eq_true_iff.mp (by decide : decide ((true, true) ∈ goodPairs) = true)
        · intro X₁ _ X₂ _ h; exact splitEquiv.injective h
        · intro ⟨Y1, Y2⟩ hmem
          rw [mem_product, mem_filter] at hmem
          refine ⟨splitEquiv.symm (Y1, Y2), mem_filter.mpr ⟨mem_univ _, fun x hx => ?_⟩,
            splitEquiv.apply_symm_apply _⟩
          have heq := congrArg (fun p => p.1 ⟨x, hx⟩) (splitEquiv.apply_symm_apply (Y1, Y2))
          change (splitEquiv.symm (Y1, Y2) x, splitEquiv.symm (Y1, Y2) (x - 1)) = Y1 ⟨x, hx⟩ at heq
          have hpair := hmem.1.2 ⟨x, hx⟩
          simp only [goodPairs, mem_insert, mem_singleton] at hpair
          intro hbad
          rcases hpair with h | h | h <;> rw [hbad.1, hbad.2] at heq <;> rw [h] at heq <;> cases heq
      rw [hBad_bij, Finset.card_product, hB1_card, Finset.card_univ, Fintype.card_fun, Fintype.card_bool]
      have hcompl : (Fintype.card {z // z ∉ supp u}) + (supp u).card = n := by
        rw [Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin]
        exact Nat.sub_add_cancel (Finset.card_le_univ _ |>.trans_eq (Fintype.card_fin n))
      calc 3 ^ m * 2 ^ Fintype.card {z // z ∉ supp u} * 4 ^ m
          = 3 ^ m * (2 ^ Fintype.card {z // z ∉ supp u} * (2 ^ 2) ^ m) := by norm_num; ring
        _ = 3 ^ m * 2 ^ (Fintype.card {z // z ∉ supp u} + 2 * m) := by
            rw [← pow_mul, ← pow_add]
        _ = 3 ^ m * 2 ^ n := by rw [← hsupp_card u, hcompl]
    have hpow : 3 ^ m * (D + 1) ^ 2 ≤ 4 ^ m := pow_four_thirds_ge r hr
    have hmul : (Bad u).card * (D + 1) ^ 2 * 4 ^ m ≤ 2 ^ n * 4 ^ m := by
      calc (Bad u).card * (D + 1) ^ 2 * 4 ^ m
          = ((Bad u).card * 4 ^ m) * (D + 1) ^ 2 := by ring
        _ = 3 ^ m * 2 ^ n * (D + 1) ^ 2 := by rw [hBad_card]
        _ = 2 ^ n * (3 ^ m * (D + 1) ^ 2) := by ring
        _ ≤ 2 ^ n * 4 ^ m := by gcongr
    exact Nat.le_of_mul_le_mul_right hmul (pow_pos (by omega) m)
  have hD : 1 ≤ D := by dsimp [D]; nlinarith [hr]
  obtain ⟨X, hX⟩ := finite_lll_nat hD supp Bad hBad_dep hdeg hprob
  rw [mem_filter] at hX
  let I' : Finset (Fin n) := Finset.univ.filter fun x => X x = true ∧ X (x - 1) = false
  refine ⟨I'.image e, ?_, ?_⟩
  · intro a ha b hb hc_ab
    rw [mem_image] at ha hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    rw [mem_filter] at hx hy
    rw [hedges] at hc_ab
    obtain ⟨i, hi⟩ := hc_ab
    rw [Sym2.eq_iff] at hi
    rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hxi : x = i := e.injective h1
      have hyi : y = i + 1 := e.injective h2
      have hsub : y - 1 = x := by rw [hxi, hyi]; abel
      rw [hsub] at hy
      exact Bool.noConfusion (hx.2.1.symm.trans hy.2.2)
    · have hxi : x = i + 1 := e.injective h1
      have hyi : y = i := e.injective h2
      have hsub : x - 1 = y := by rw [hxi, hyi]; abel
      rw [hsub] at hx
      exact Bool.noConfusion (hy.2.1.symm.trans hx.2.2)
  · intro u _
    let u' := e.symm u
    have hnotBad : X ∉ Bad u' := hX.2 u'
    simp only [Bad, mem_filter, mem_univ, true_and, not_forall, Classical.not_not] at hnotBad
    obtain ⟨w', hw'P, hw'X⟩ := hnotBad
    refine ⟨e w', mem_image.mpr ⟨w', mem_filter.mpr ⟨mem_univ _, hw'X⟩, rfl⟩, ?_, ?_⟩
    · have hw'gr := hP_sub u' hw'P
      have hadj' : G'.Adj u' w' := (mem_neighborFinset _ _ _).mp
        (mem_erase.mp (mem_erase.mp hw'gr).2).2
      simpa [G', u'] using hadj'
    · intro hce
      rw [hedges] at hce
      obtain ⟨i, hi⟩ := hce
      have hw'gr := hP_sub u' hw'P
      have hne1 : w' ≠ u' - 1 := (mem_erase.mp (mem_erase.mp hw'gr).2).1
      have hne2 : w' ≠ u' + 1 := (mem_erase.mp hw'gr).1
      rw [Sym2.eq_iff] at hi
      rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have h1' : u' = i := e.injective (by simpa [u'] using h1)
        have h2' : w' = i + 1 := e.injective h2
        exact hne2 (by rw [h1', h2'])
      · have h1' : u' = i + 1 := e.injective (by simpa [u'] using h1)
        have h2' : w' = i := e.injective h2
        exact hne1 (by rw [h1', h2']; abel)

end Helpers1

theorem h1_proof : OMA.SheehanR1.H1 :=
  fun G _ r hr hreg v c hc => Helpers1.h1_main G r hr hreg v c hc
end H1Section

section H2Section
/-
Thomassen's parity proof of hypothesis H2 for `LovaszPlummerConjecture.sheehan_conjecture`.
-/

-- Step LovaszPlummerConjecture.sheehan_conjecture.variants.thomassen.R1.H2: hypothesis H2 of reduction LovaszPlummerConjecture.sheehan_conjecture.variants.thomassen.R1
-- Credit: @luciusacarr (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace Helpers2

open SimpleGraph Finset

private def rotIdx (n k j : ℕ) : ℕ :=
  if j ≤ k then j else n + k - j

private lemma rotIdx_lt {n k j : ℕ} (_hk : k + 2 < n) (hj : j < n) : rotIdx n k j < n := by
  unfold rotIdx
  split_ifs <;> omega

private lemma rotIdx_invol {n k j : ℕ} (_hk : k + 2 < n) (hj : j < n) :
    rotIdx n k (rotIdx n k j) = j := by
  unfold rotIdx
  split_ifs <;> omega

private lemma rotIdx_eq_iff {n k j₁ j₂ : ℕ} (hk : k + 2 < n) (h1 : j₁ < n) (h2 : j₂ < n) :
    rotIdx n k j₁ = rotIdx n k j₂ ↔ j₁ = j₂ := by
  constructor
  · intro h
    have := congrArg (rotIdx n k) h
    rwa [rotIdx_invol hk h1, rotIdx_invol hk h2] at this
  · rintro rfl; rfl

private def rotFin {n : ℕ} (P : Fin n → Fin n) (k : ℕ) (hk : k + 2 < n) : Fin n → Fin n :=
  fun j => P ⟨rotIdx n k j.val, rotIdx_lt hk j.isLt⟩

private lemma rotFin_invol {n : ℕ} (P : Fin n → Fin n) (k : ℕ) (hk : k + 2 < n) :
    rotFin (rotFin P k hk) k hk = P := by
  ext ⟨j, hj⟩
  simp only [rotFin, rotIdx_invol hk hj]

private lemma rotFin_inj {n : ℕ} {P : Fin n → Fin n} (hP : Function.Injective P)
    {k : ℕ} (hk : k + 2 < n) : Function.Injective (rotFin P k hk) := by
  intro ⟨j₁, hj₁⟩ ⟨j₂, hj₂⟩ h
  have h1 := hP h
  simp only [Fin.mk.injEq, rotIdx_eq_iff hk hj₁ hj₂] at h1
  exact Fin.ext h1

private lemma walkOfChain_exists {V : Type*} (G : SimpleGraph V) (l : List V) (hl : l ≠ [])
    (hadj : ∀ i : ℕ, (hi : i + 1 < l.length) → G.Adj l[i] l[i + 1]) :
    ∃ p : G.Walk (l.head hl) (l.getLast hl),
      p.support = l ∧ p.length + 1 = l.length ∧
      ∀ e, e ∈ p.edges ↔ ∃ i : ℕ, ∃ (hi : i + 1 < l.length), e = s(l[i], l[i + 1]) := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a t ih =>
    cases t with
    | nil =>
      refine ⟨Walk.nil, by simp, by simp, ?_⟩
      intro e
      simp
    | cons b t' =>
      have ht_ne : b :: t' ≠ [] := List.cons_ne_nil _ _
      have hadj_t : ∀ i : ℕ, (hi : i + 1 < (b :: t').length) →
          G.Adj (b :: t')[i] (b :: t')[i + 1] := by
        intro i hi
        have h1 := hadj (i + 1) (by simp only [List.length_cons] at hi ⊢; omega)
        simpa only [List.getElem_cons_succ] using h1
      obtain ⟨q, hq_sup, hq_len, hq_edges⟩ := ih ht_ne hadj_t
      have hab : G.Adj a ((b :: t').head ht_ne) := hadj 0 (by simp)
      refine ⟨(Walk.cons hab q).copy (List.head_cons (a := a) (l := b :: t') (h := hl)).symm
          (List.getLast_cons ht_ne).symm, ?_, ?_, ?_⟩
      · simp only [Walk.support_copy, Walk.support_cons, hq_sup]
      · rw [Walk.length_copy, Walk.length_cons, hq_len]
        rfl
      · intro e
        simp only [Walk.edges_copy, Walk.edges_cons, List.mem_cons, hq_edges]
        constructor
        · rintro (rfl | ⟨i, hi, rfl⟩)
          · exact ⟨0, by simp, rfl⟩
          · exact ⟨i + 1, by simp only [List.length_cons] at hi ⊢; omega, by simp⟩
        · rintro ⟨i, hi, rfl⟩
          cases i with
          | zero => left; rfl
          | succ i' =>
            right
            exact ⟨i', by simp only [List.length_cons] at hi ⊢; omega, by simp⟩

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

private lemma h2_on_fin (n : ℕ) [NeZero n] (hn4 : 4 ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hc : ∀ i : Fin n, G.Adj i (i + 1))
    (I : Finset (Fin n)) (h0I : (0 : Fin n) ∈ I)
    (hI_ind : ∀ x ∈ I, ∀ y ∈ I, y ≠ x + 1 ∧ x ≠ y + 1)
    (hI_dom : ∀ u : Fin n, u ∉ I → ∃ w ∈ I, G.Adj u w ∧ w ≠ u + 1 ∧ u ≠ w + 1) :
    ∃ (p : Fin n → Fin n), Function.Injective p ∧
      p ⟨0, by omega⟩ = 0 ∧ p ⟨1, by omega⟩ = 1 ∧
      (∀ i : ℕ, (hi : i + 1 < n) → G.Adj (p ⟨i, by omega⟩) (p ⟨i + 1, hi⟩)) ∧
      G.Adj (p ⟨n - 1, by omega⟩) 0 ∧
      ∃ i : ℕ, ∃ (hi : i < n), p ⟨i, hi⟩ ≠ ⟨i, hi⟩ := by
  classical
  have h2ne0 : (2 : Fin n) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt (by omega : 2 < n)] at hv
  have hprev_ne_next : ∀ u : Fin n, u - 1 ≠ u + 1 := by
    intro u h
    apply h2ne0
    have h1 := congrArg (fun x => x - (u - 1)) h
    have h2 : u + 1 - (u - 1) = (2 : Fin n) := by
      have htwo : (2 : Fin n) = (1 : Fin n) + 1 := by
        ext; simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < n),
          Nat.mod_eq_of_lt (by omega : 2 < n)]
      rw [htwo]
      abel
    simpa [sub_self, h2] using h1.symm
  let B : Finset (Fin n) := Finset.univ.filter fun u => u ∉ I ∧ (u - 1 ∈ I ∨ u + 1 ∈ I)
  have hg_exists : ∀ u : Fin n, u ∈ B → ∃ w ∈ I, G.Adj u w ∧ w ≠ u + 1 ∧ u ≠ w + 1 := by
    intro u hu
    rw [mem_filter] at hu
    exact hI_dom u hu.2.1
  let g : Fin n → Fin n := fun u =>
    if hu : u ∈ B then Classical.choose (hg_exists u hu) else 0
  have hg_spec : ∀ u ∈ B, g u ∈ I ∧ G.Adj u (g u) ∧ g u ≠ u + 1 ∧ u ≠ g u + 1 := by
    intro u hu
    simp only [g, dif_pos hu]
    exact Classical.choose_spec (hg_exists u hu)
  let CAdj : Fin n → Fin n → Prop := fun u w => w = u + 1 ∨ u = w + 1
  let HAdj : Fin n → Fin n → Prop := fun u w =>
    CAdj u w ∨ (u ∈ B ∧ w = g u) ∨ (w ∈ B ∧ u = g w)
  have hH_symm : ∀ u w, HAdj u w → HAdj w u := by
    rintro u w (h | h | h)
    · exact Or.inl (Or.symm h)
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  have hH_irrefl : ∀ u, ¬ HAdj u u := by
    rintro u (⟨h | h⟩ | ⟨hu, hgu⟩ | ⟨hu, hgu⟩)
    · have : (1 : Fin n) = 0 := by
        have := congrArg (· - u) h
        simpa using this.symm
      have hv := congrArg Fin.val this
      simp [Nat.mod_eq_of_lt (by omega : 1 < n)] at hv
    · have : (1 : Fin n) = 0 := by
        have := congrArg (· - u) h
        simpa using this
      have hv := congrArg Fin.val this
      simp [Nat.mod_eq_of_lt (by omega : 1 < n)] at hv
    · have huB := (mem_filter.mp hu).2.1
      have hgI := (hg_spec u hu).1
      exact huB (hgu ▸ hgI)
    · have huB := (mem_filter.mp hu).2.1
      have hgI := (hg_spec u hu).1
      exact huB (hgu ▸ hgI)
  let H : SimpleGraph (Fin n) := ⟨HAdj, ⟨fun _ _ => hH_symm _ _⟩, ⟨hH_irrefl⟩⟩
  have hH_le_G : H ≤ G := by
    rintro u w (⟨rfl | rfl⟩ | ⟨hu, rfl⟩ | ⟨hw, rfl⟩)
    · exact hc u
    · exact (hc w).symm
    · exact (hg_spec u hu).2.1
    · exact (hg_spec w hw).2.1.symm
  have hH_ind : ∀ u w : Fin n, H.Adj u w → u ∉ I ∨ w ∉ I := by
    intro u w hadj
    by_contra h
    push Not at h
    rcases hadj with (⟨rfl | rfl⟩ | ⟨hu, _⟩ | ⟨hw, _⟩)
    · exact (hI_ind u h.1 (u + 1) h.2).1 rfl
    · exact (hI_ind (w + 1) h.1 w h.2).2 rfl
    · exact (mem_filter.mp hu).2.1 h.1
    · exact (mem_filter.mp hw).2.1 h.2
  have hH_nbr_B : ∀ u ∈ B, ∀ w : Fin n, H.Adj u w ↔ w = u - 1 ∨ w = u + 1 ∨ w = g u := by
    intro u hu w
    constructor
    · rintro (⟨rfl | rfl⟩ | ⟨_, rfl⟩ | ⟨hw, hgw⟩)
      · right; left; rfl
      · left; abel
      · right; right; rfl
      · exfalso
        exact (mem_filter.mp hu).2.1 (hgw ▸ (hg_spec w hw).1)
    · rintro (rfl | rfl | rfl)
      · left; right; abel
      · left; left; rfl
      · right; left; exact ⟨hu, rfl⟩
  have hH_nbr_nonB : ∀ u : Fin n, u ∉ I → u ∉ B → ∀ w : Fin n,
      H.Adj u w ↔ w = u - 1 ∨ w = u + 1 := by
    intro u huI huB w
    constructor
    · rintro (⟨rfl | rfl⟩ | ⟨hu, _⟩ | ⟨hw, hgw⟩)
      · right; rfl
      · left; abel
      · exact absurd hu huB
      · exact absurd (hgw ▸ (hg_spec w hw).1) huI
    · rintro (rfl | rfl)
      · left; right; abel
      · left; left; rfl
  let IsGood (P : Fin n → Fin n) : Prop :=
    Function.Injective P ∧
    P ⟨0, by omega⟩ = 0 ∧
    P ⟨1, by omega⟩ = 1 ∧
    (∀ i : ℕ, (hi : i + 1 < n) → H.Adj (P ⟨i, by omega⟩) (P ⟨i + 1, hi⟩)) ∧
    (∀ u : Fin n, u ∉ I → u + 1 ∉ I →
      ∃ i : ℕ, ∃ (hi : i + 1 < n),
        ((P ⟨i, by omega⟩ = u ∧ P ⟨i + 1, hi⟩ = u + 1) ∨
          (P ⟨i, by omega⟩ = u + 1 ∧ P ⟨i + 1, hi⟩ = u))) ∧
    P ⟨n - 1, by omega⟩ ∉ I
  let LVert := { P : Fin n → Fin n // IsGood P }
  have hgood_end_B : ∀ P : LVert, P.1 ⟨n - 1, by omega⟩ ∈ B := by
    intro ⟨P, hP⟩
    set z := P ⟨n - 1, by omega⟩
    have hzI : z ∉ I := hP.2.2.2.2.2
    by_contra hzB
    have hzm1 : z - 1 ∉ I := fun h => hzB (mem_filter.mpr ⟨mem_univ _, hzI, Or.inl h⟩)
    have hzp1 : z + 1 ∉ I := fun h => hzB (mem_filter.mpr ⟨mem_univ _, hzI, Or.inr h⟩)
    have hp1 := hP.2.2.2.2.1 z hzI hzp1
    have hzm1p1 : (z - 1) + 1 = z := by abel
    have hm1 := hP.2.2.2.2.1 (z - 1) hzm1 (by rwa [hzm1p1])
    rw [hzm1p1] at hm1
    have extract_prev : ∀ w : Fin n,
        (∃ i : ℕ, ∃ (hi : i + 1 < n),
          ((P ⟨i, by omega⟩ = z ∧ P ⟨i + 1, hi⟩ = w) ∨
            (P ⟨i, by omega⟩ = w ∧ P ⟨i + 1, hi⟩ = z))) →
        w = P ⟨n - 2, by omega⟩ := by
      intro w ⟨i, hi, hpair⟩
      rcases hpair with ⟨hi_z, _⟩ | ⟨hi_w, hi1_z⟩
      · have heq := hP.1 hi_z
        have hval := congrArg Fin.val heq
        simp at hval
        omega
      · have heq := hP.1 hi1_z
        have hval := congrArg Fin.val heq
        simp at hval
        have hi2 : i = n - 2 := by omega
        subst hi2
        exact hi_w.symm
    have hm1' : ∃ i : ℕ, ∃ (hi : i + 1 < n),
        (P ⟨i, by omega⟩ = z ∧ P ⟨i + 1, hi⟩ = z - 1) ∨
          (P ⟨i, by omega⟩ = z - 1 ∧ P ⟨i + 1, hi⟩ = z) :=
      let ⟨i, hi, hp⟩ := hm1; ⟨i, hi, hp.symm⟩
    exact hprev_ne_next z ((extract_prev (z - 1) hm1').trans (extract_prev (z + 1) hp1).symm)
  have hgood_nbr_I : ∀ P : LVert, ∀ w : Fin n,
      H.Adj (P.1 ⟨n - 1, by omega⟩) w → w ≠ P.1 ⟨n - 2, by omega⟩ → w ∈ I := by
    intro ⟨P, hP⟩ w hw hne
    set z := P ⟨n - 1, by omega⟩
    have hzB : z ∈ B := hgood_end_B ⟨P, hP⟩
    have hzI : z ∉ I := hP.2.2.2.2.2
    rw [hH_nbr_B z hzB] at hw
    rcases hw with rfl | rfl | rfl
    · by_contra hzmI
      have hzm1p1 : (z - 1) + 1 = z := by abel
      obtain ⟨i, hi, hpair⟩ := hP.2.2.2.2.1 (z - 1) hzmI (by rwa [hzm1p1])
      rw [hzm1p1] at hpair
      apply hne
      rcases hpair with ⟨hi_w, hi1_z⟩ | ⟨hi_z, _⟩
      · have hval := congrArg Fin.val (hP.1 hi1_z)
        simp at hval
        have : i = n - 2 := by omega
        subst this; exact hi_w.symm
      · have hval := congrArg Fin.val (hP.1 hi_z)
        simp at hval; omega
    · by_contra hzpI
      obtain ⟨i, hi, hpair⟩ := hP.2.2.2.2.1 z hzI hzpI
      apply hne
      rcases hpair with ⟨hi_z, hi1_w⟩ | ⟨hi_w, hi1_z⟩
      · have hval := congrArg Fin.val (hP.1 hi_z)
        simp at hval; omega
      · have hval := congrArg Fin.val (hP.1 hi1_z)
        simp at hval
        have : i = n - 2 := by omega
        subst this; exact hi_w.symm
    · exact (hg_spec z hzB).1
  let LAdj : LVert → LVert → Prop := fun P Q =>
    ∃ k : ℕ, ∃ hk : k + 2 < n, 1 ≤ k ∧
      H.Adj (P.1 ⟨n - 1, by omega⟩) (P.1 ⟨k, by omega⟩) ∧
      Q.1 = rotFin P.1 k hk
  have hL_symm : ∀ P Q, LAdj P Q → LAdj Q P := by
    rintro ⟨P, hP⟩ ⟨Q, hQ⟩ ⟨k, hk, hk1, hadj, hQ_eq⟩
    dsimp only at hadj hQ_eq
    refine ⟨k, hk, hk1, ?_, ?_⟩
    · have hQ_n1 : Q ⟨n - 1, by omega⟩ = P ⟨k + 1, by omega⟩ := by
        rw [hQ_eq]
        dsimp only [rotFin]
        have hidx : (⟨rotIdx n k (n - 1), rotIdx_lt hk (by omega : n - 1 < n)⟩ : Fin n) =
            ⟨k + 1, by omega⟩ := by
          ext; simp only [rotIdx, show ¬ (n - 1 ≤ k) by omega, ↓reduceIte]; omega
        rw [hidx]
      have hQ_k : Q ⟨k, by omega⟩ = P ⟨k, by omega⟩ := by
        rw [hQ_eq]
        dsimp only [rotFin]
        have hidx : (⟨rotIdx n k k, rotIdx_lt hk (by omega : k < n)⟩ : Fin n) =
            ⟨k, by omega⟩ := by
          ext; simp only [rotIdx, le_refl, ↓reduceIte]
        rw [hidx]
      change H.Adj (Q ⟨n - 1, by omega⟩) (Q ⟨k, by omega⟩)
      rw [hQ_n1, hQ_k]
      exact (hP.2.2.2.1 k (by omega)).symm
    · exact (rotFin_invol P k hk).symm.trans (congrArg (fun f => rotFin f k hk) hQ_eq.symm)
  have hL_irrefl : ∀ P, ¬ LAdj P P := by
    rintro ⟨P, hP⟩ ⟨k, hk, _, _, hP_eq⟩
    dsimp only at hP_eq
    have hv := congrArg (fun f => f ⟨k + 1, by omega⟩) hP_eq
    have hidx : (⟨rotIdx n k (k + 1), rotIdx_lt hk (by omega : k + 1 < n)⟩ : Fin n) =
        ⟨n - 1, by omega⟩ := by
      ext; simp only [rotIdx, show ¬ (k + 1 ≤ k) by omega, ↓reduceIte]; omega
    have hrot : rotFin P k hk ⟨k + 1, by omega⟩ = P ⟨n - 1, by omega⟩ := by
      dsimp only [rotFin]; rw [hidx]
    rw [hrot] at hv
    have hval := congrArg Fin.val (hP.1 hv)
    simp at hval
    omega
  let L : SimpleGraph LVert := ⟨LAdj, ⟨fun _ _ => hL_symm _ _⟩, ⟨hL_irrefl⟩⟩
  have hrot_good : ∀ (P : LVert) (k : ℕ) (hk : k + 2 < n), 1 ≤ k →
      H.Adj (P.1 ⟨n - 1, by omega⟩) (P.1 ⟨k, by omega⟩) →
      IsGood (rotFin P.1 k hk) := by
    intro ⟨P, hP⟩ k hk hk1 hadj
    dsimp only at hadj
    have hPkI : P ⟨k, by omega⟩ ∈ I := by
      apply hgood_nbr_I ⟨P, hP⟩ _ hadj
      intro heq
      have hval := congrArg Fin.val (hP.1 heq)
      simp at hval
      omega
    have hPk1_notI : P ⟨k + 1, by omega⟩ ∉ I := by
      rcases hH_ind _ _ (hP.2.2.2.1 k (by omega)) with h | h
      · exact absurd hPkI h
      · exact h
    refine ⟨rotFin_inj hP.1 hk, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only [rotFin]
      have hidx : (⟨rotIdx n k 0, rotIdx_lt hk (by omega : 0 < n)⟩ : Fin n) = ⟨0, by omega⟩ := by
        ext; simp [rotIdx]
      rw [hidx]; exact hP.2.1
    · dsimp only [rotFin]
      have hidx : (⟨rotIdx n k 1, rotIdx_lt hk (by omega : 1 < n)⟩ : Fin n) = ⟨1, by omega⟩ := by
        ext; simp [rotIdx, hk1]
      rw [hidx]; exact hP.2.2.1
    · intro i hi
      dsimp only [rotFin]
      by_cases hik : i + 1 ≤ k
      · have hidx1 : (⟨rotIdx n k i, rotIdx_lt hk (by omega : i < n)⟩ : Fin n) = ⟨i, by omega⟩ := by
          ext; simp [rotIdx, show i ≤ k by omega]
        have hidx2 : (⟨rotIdx n k (i + 1), rotIdx_lt hk hi⟩ : Fin n) = ⟨i + 1, hi⟩ := by
          ext; simp [rotIdx, hik]
        rw [hidx1, hidx2]
        exact hP.2.2.2.1 i hi
      · by_cases hik0 : i ≤ k
        · have hik_eq : i = k := by omega
          subst i
          have hidx1 : (⟨rotIdx n k k, rotIdx_lt hk (by omega : k < n)⟩ : Fin n) = ⟨k, by omega⟩ := by
            ext; simp [rotIdx]
          have hidx2 : (⟨rotIdx n k (k + 1), rotIdx_lt hk hi⟩ : Fin n) = ⟨n - 1, by omega⟩ := by
            ext; simp only [rotIdx, show ¬ (k + 1 ≤ k) by omega, ↓reduceIte]; omega
          rw [hidx1, hidx2]
          exact hadj.symm
        · have hidx1 : (⟨rotIdx n k i, rotIdx_lt hk (by omega : i < n)⟩ : Fin n) =
              ⟨n + k - i, by omega⟩ := by
            ext; simp [rotIdx, hik0]
          have hidx2 : (⟨rotIdx n k (i + 1), rotIdx_lt hk hi⟩ : Fin n) =
              ⟨n + k - (i + 1), by omega⟩ := by
            ext; simp [rotIdx, hik]
          rw [hidx1, hidx2]
          have hm_lt : n + k - (i + 1) + 1 < n := by omega
          have hchain := (hP.2.2.2.1 (n + k - (i + 1)) hm_lt).symm
          convert hchain using 2 <;> ext <;> dsimp <;> omega
    · intro u huI hu1I
      obtain ⟨i, hi, hpair⟩ := hP.2.2.2.2.1 u huI hu1I
      have hineq : i ≠ k := by
        rintro rfl
        rcases hpair with ⟨h1, _⟩ | ⟨h2, _⟩
        · exact huI (h1 ▸ hPkI)
        · exact hu1I (h2 ▸ hPkI)
      by_cases hik : i + 1 ≤ k
      · refine ⟨i, hi, ?_⟩
        dsimp only [rotFin]
        have hidx1 : (⟨rotIdx n k i, rotIdx_lt hk (by omega : i < n)⟩ : Fin n) = ⟨i, by omega⟩ := by
          ext; simp [rotIdx, show i ≤ k by omega]
        have hidx2 : (⟨rotIdx n k (i + 1), rotIdx_lt hk hi⟩ : Fin n) = ⟨i + 1, hi⟩ := by
          ext; simp [rotIdx, hik]
        rw [hidx1, hidx2]
        exact hpair
      · have ik_gt : k < i := by omega
        let j := n + k - 1 - i
        have hj_lt : j + 1 < n := by omega
        have hj_gt : ¬ (j ≤ k) := by omega
        have hj1_gt : ¬ (j + 1 ≤ k) := by omega
        refine ⟨j, hj_lt, ?_⟩
        have hidx1 : (⟨rotIdx n k j, rotIdx_lt hk (by omega : j < n)⟩ : Fin n) = ⟨i + 1, hi⟩ := by
          ext; simp only [rotIdx, hj_gt, ↓reduceIte, j]; omega
        have hidx2 : (⟨rotIdx n k (j + 1), rotIdx_lt hk hj_lt⟩ : Fin n) = ⟨i, by omega⟩ := by
          ext; simp only [rotIdx, hj1_gt, ↓reduceIte, j]; omega
        dsimp only [rotFin]
        rw [hidx1, hidx2]
        rcases hpair with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact Or.inr ⟨hb, ha⟩
        · exact Or.inl ⟨hb, ha⟩
    · dsimp only [rotFin]
      have hidx : (⟨rotIdx n k (n - 1), rotIdx_lt hk (by omega : n - 1 < n)⟩ : Fin n) =
          ⟨k + 1, by omega⟩ := by
        ext; simp only [rotIdx, show ¬ (n - 1 ≤ k) by omega, ↓reduceIte]; omega
      rw [hidx]
      exact hPk1_notI
  have hP0_good : IsGood (fun i : Fin n => i) := by
    refine ⟨Function.injective_id, rfl, by ext; simp [Nat.mod_eq_of_lt (by omega : 1 < n)],
      fun i hi => ?_, fun u _ _ => ?_, ?_⟩
    · left; left; ext
      simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < n), Nat.mod_eq_of_lt hi]
    · by_cases hu : u.val + 1 < n
      · refine ⟨u.val, hu, Or.inl ⟨rfl, ?_⟩⟩
        ext
        simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < n), Nat.mod_eq_of_lt hu]
      · exfalso
        have hu_lt := u.isLt
        have huv : u = ⟨n - 1, by omega⟩ := Fin.ext (by change u.val = n - 1; omega)
        have hu1 : u + 1 = 0 := by
          rw [huv]
          ext
          simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < n)]
          rw [Nat.sub_add_cancel (by omega : 1 ≤ n), Nat.mod_self]
        exact absurd h0I (hu1 ▸ ‹u + 1 ∉ I›)
    · intro hnm1
      have h0_eq : (0 : Fin n) = (⟨n - 1, by omega⟩ : Fin n) + 1 := by
        ext
        simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < n)]
        rw [Nat.sub_add_cancel (by omega : 1 ≤ n), Nat.mod_self]
      exact (hI_ind ⟨n - 1, by omega⟩ hnm1 0 h0I).1 h0_eq
  let P0 : LVert := ⟨fun i : Fin n => i, hP0_good⟩
  have hdeg_eq : ∀ P : LVert, L.degree P =
      (Finset.univ.filter fun k : Fin n =>
        1 ≤ k.val ∧ k.val < n - 2 ∧ H.Adj (P.1 ⟨n - 1, by omega⟩) (P.1 k)).card := by
    intro P
    rw [SimpleGraph.degree, SimpleGraph.neighborFinset_def]
    have hmap :
        (Finset.univ.filter fun k : Fin n =>
          1 ≤ k.val ∧ k.val < n - 2 ∧ H.Adj (P.1 ⟨n - 1, by omega⟩) (P.1 k)).card =
        (L.neighborSet P).toFinset.card := by
      have inj_lt : ∀ (a b : Fin n), 1 ≤ a.val → ∀ (hlt : a.val < b.val) (hb2 : b.val + 2 < n),
          rotFin P.1 a.val (lt_trans (Nat.add_lt_add_right hlt 2) hb2) ≠
            rotFin P.1 b.val hb2 := by
        intro a b _ hlt hb2 heq
        have ha2 : a.val + 2 < n := lt_trans (Nat.add_lt_add_right hlt 2) hb2
        have hv := congrArg (fun f => f ⟨a.val + 1, by omega⟩) heq
        have hidx1 : (⟨rotIdx n a.val (a.val + 1), rotIdx_lt ha2
            (by omega : a.val + 1 < n)⟩ : Fin n) = ⟨n - 1, by omega⟩ := by
          ext; simp only [rotIdx, show ¬ (a.val + 1 ≤ a.val) by omega, ↓reduceIte]; omega
        have hidx2 : (⟨rotIdx n b.val (a.val + 1), rotIdx_lt hb2
            (by omega : a.val + 1 < n)⟩ : Fin n) = ⟨a.val + 1, by omega⟩ := by
          ext; simp only [rotIdx, show a.val + 1 ≤ b.val by omega, ↓reduceIte]
        have h1 : rotFin P.1 a.val ha2 ⟨a.val + 1, by omega⟩ = P.1 ⟨n - 1, by omega⟩ := by
          dsimp only [rotFin]; rw [hidx1]
        have h2 : rotFin P.1 b.val hb2 ⟨a.val + 1, by omega⟩ = P.1 ⟨a.val + 1, by omega⟩ := by
          dsimp only [rotFin]; rw [hidx2]
        rw [h1, h2] at hv
        have hval := congrArg Fin.val (P.2.1 hv)
        simp at hval; omega
      refine Finset.card_bij
        (fun k hk =>
          have hkm := (mem_filter.mp hk).2
          have hk2 : k.val + 2 < n := by omega
          ⟨rotFin P.1 k.val hk2, hrot_good P k.val hk2 hkm.1 hkm.2.2⟩)
        ?_ ?_ ?_
      · intro k hk
        have hkm := (mem_filter.mp hk).2
        rw [Set.mem_toFinset, mem_neighborSet]
        exact ⟨k.val, by omega, hkm.1, hkm.2.2, rfl⟩
      · intro k₁ hk₁ k₂ hk₂ heq
        have hk1_mem := (mem_filter.mp hk₁).2
        have hk2_mem := (mem_filter.mp hk₂).2
        have hfun : rotFin P.1 k₁.val (by omega) = rotFin P.1 k₂.val (by omega) :=
          congrArg Subtype.val heq
        rcases lt_trichotomy k₁.val k₂.val with hlt | heqv | hgt
        · exact absurd hfun (inj_lt k₁ k₂ hk1_mem.1 hlt (by omega))
        · exact Fin.ext heqv
        · exact absurd hfun.symm (inj_lt k₂ k₁ hk2_mem.1 hgt (by omega))
      · rintro ⟨Q, hQ⟩ hmem
        rw [Set.mem_toFinset, mem_neighborSet] at hmem
        rcases hmem with ⟨k, hk, hk1, hadj, hQ_eq⟩
        refine ⟨⟨k, by omega⟩, mem_filter.mpr ⟨mem_univ _, hk1, by simp; omega, hadj⟩, ?_⟩
        exact Subtype.ext hQ_eq.symm
    exact hmap.symm.trans (by simp)
  have hdeg_char : ∀ P : LVert,
      (Odd (L.degree P) ↔ H.Adj (P.1 ⟨n - 1, by omega⟩) 0) := by
    intro P
    rw [hdeg_eq P]
    set z := P.1 ⟨n - 1, by omega⟩
    have hzB : z ∈ B := hgood_end_B P
    have hz_nbrs : H.neighborFinset z = {z - 1, z + 1, g z} := by
      ext w
      rw [mem_neighborFinset, hH_nbr_B z hzB]
      simp
    have hcard_z : (H.neighborFinset z).card = 3 := by
      rw [hz_nbrs]
      have h12 : z - 1 ≠ z + 1 := hprev_ne_next z
      have h13 : z - 1 ≠ g z := by
        intro h
        have hg := (hg_spec z hzB).2.2.2
        apply hg
        calc
          z = z - 1 + 1 := by abel
          _ = g z + 1 := by rw [h]
      have h23 : z + 1 ≠ g z := (hg_spec z hzB).2.2.1.symm
      rw [Finset.card_insert_of_notMem (by simp [h12, h13]),
        Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]
    have hP_bij : Function.Bijective P.1 := (Fintype.bijective_iff_injective_and_card _).mpr ⟨P.2.1, rfl⟩
    let S_idx : Finset (Fin n) := (Finset.univ.filter fun i : Fin n => H.Adj z (P.1 i))
    have hS_card : S_idx.card = 3 := by
      have : S_idx.card = (H.neighborFinset z).card := by
        refine Finset.card_bij (fun i _ => P.1 i) ?_ ?_ ?_
        · intro i hi; rw [mem_neighborFinset]; exact (mem_filter.mp hi).2
        · intro i₁ _ i₂ _ h; exact P.2.1 h
        · intro w hw
          rw [mem_neighborFinset] at hw
          obtain ⟨i, rfl⟩ := hP_bij.2 w
          exact ⟨i, mem_filter.mpr ⟨mem_univ _, hw⟩, rfl⟩
      rw [this, hcard_z]
    let nm2 : Fin n := ⟨n - 2, by omega⟩
    have hnm2_mem : nm2 ∈ S_idx := by
      rw [mem_filter]
      refine ⟨mem_univ _, ?_⟩
      have hnm1_eq : (⟨n - 2 + 1, by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ := by
        ext; simp; omega
      have hadj_nm2 := (P.2.2.2.2.1 (n - 2) (by omega)).symm
      rwa [hnm1_eq] at hadj_nm2
    have hS_sub : ∀ i ∈ S_idx, i = nm2 ∨ i = ⟨0, by omega⟩ ∨ (1 ≤ i.val ∧ i.val < n - 2) := by
      intro i hi
      by_cases h1 : i = nm2
      · left; exact h1
      · by_cases h0 : i = ⟨0, by omega⟩
        · right; left; exact h0
        · right; right
          have hne_last : i ≠ ⟨n - 1, by omega⟩ := by
            intro heq
            exact H.loopless.irrefl z (by simpa [z, heq] using (mem_filter.mp hi).2)
          have hiv0 : i.val ≠ 0 := fun h => h0 (Fin.ext h)
          have hiv2 : i.val ≠ n - 2 := fun h => h1 (Fin.ext h)
          have hiv1 : i.val ≠ n - 1 := fun h => hne_last (Fin.ext h)
          omega
    let K_idx : Finset (Fin n) := Finset.univ.filter fun i : Fin n =>
      1 ≤ i.val ∧ i.val < n - 2 ∧ H.Adj z (P.1 i)
    change Odd K_idx.card ↔ H.Adj z 0
    have hS_part : (S_idx.erase nm2).card = 2 := by
      rw [Finset.card_erase_of_mem hnm2_mem, hS_card]
    by_cases hadj0 : H.Adj z 0
    · have h0_mem : (⟨0, by omega⟩ : Fin n) ∈ S_idx.erase nm2 := by
        rw [mem_erase, mem_filter]
        refine ⟨?_, mem_univ _, by rw [P.2.2.1]; exact hadj0⟩
        intro heq
        have hval := congrArg Fin.val heq
        dsimp only [nm2] at hval
        omega
      have hK_eq_erase : K_idx = (S_idx.erase nm2).erase ⟨0, by omega⟩ := by
        ext i
        simp only [K_idx, S_idx, mem_filter, mem_erase, mem_univ, true_and]
        constructor
        · rintro ⟨h1, h2, hiH⟩
          refine ⟨fun h => by have hv : i.val = 0 := congrArg Fin.val h; omega,
            fun h => by have hv : i.val = n - 2 := congrArg Fin.val h; omega, hiH⟩
        · rintro ⟨h0, h2, hiH⟩
          have hiS : i ∈ S_idx := mem_filter.mpr ⟨mem_univ _, hiH⟩
          rcases hS_sub i hiS with rfl | rfl | hk
          · exact absurd rfl h2
          · exact absurd rfl h0
          · exact ⟨hk.1, hk.2, hiH⟩
      rw [hK_eq_erase, Finset.card_erase_of_mem h0_mem, hS_part]
      simp [hadj0]
    · have hK_eq_erase : K_idx = S_idx.erase nm2 := by
        ext i
        simp only [K_idx, S_idx, mem_filter, mem_erase, mem_univ, true_and]
        constructor
        · rintro ⟨_, h2, hiH⟩
          exact ⟨fun h => by have hv : i.val = n - 2 := congrArg Fin.val h; omega, hiH⟩
        · rintro ⟨h2, hiH⟩
          have hiS : i ∈ S_idx := mem_filter.mpr ⟨mem_univ _, hiH⟩
          rcases hS_sub i hiS with rfl | rfl | hk
          · exact absurd rfl h2
          · exfalso
            apply hadj0
            rwa [P.2.2.1] at hiH
          · exact ⟨hk.1, hk.2, hiH⟩
      rw [hK_eq_erase, hS_part]
      simp [hadj0]
  have hP0_odd : Odd (L.degree P0) := by
    rw [hdeg_char P0]
    refine Or.inl (Or.inl ?_)
    ext
    dsimp [P0]
    simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < n)]
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n), Nat.mod_self]
  obtain ⟨P1, hP1_ne, hP1_odd⟩ := L.exists_ne_odd_degree_of_exists_odd_degree P0 hP0_odd
  have hP1_closes : H.Adj (P1.1 ⟨n - 1, by omega⟩) 0 := (hdeg_char P1).mp hP1_odd
  have hP1_ne_fun : P1.1 ≠ fun i : Fin n => i := by
    intro heq
    exact hP1_ne (Subtype.ext heq)
  have hdiff : ∃ i : Fin n, P1.1 i ≠ i := by
    by_contra h
    push Not at h
    exact hP1_ne_fun (funext h)
  rcases hdiff with ⟨i_diff, hi_diff⟩
  refine ⟨P1.1, P1.2.1, P1.2.2.1, P1.2.2.2.1, ?_, ?_, i_diff.val, i_diff.isLt, hi_diff⟩
  · intro i hi
    exact hH_le_G (P1.2.2.2.2.1 i hi)
  · exact hH_le_G hP1_closes

private lemma h2_main {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) (c : G.Walk v v)
    (hc : LovaszPlummerConjecture.IsHamiltonianCycle G c) (I : Finset V)
    (hI_ind : ∀ x ∈ I, ∀ y ∈ I, s(x, y) ∉ c.edges)
    (hI_dom : ∀ u : V, u ∉ I → ∃ w ∈ I, G.Adj u w ∧ s(u, w) ∉ c.edges) :
    ∃ (w : V) (c' : G.Walk w w), LovaszPlummerConjecture.IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset := by
  have : Nonempty V := ⟨v⟩
  obtain ⟨hn3, e₀, hadj₀, hedges₀⟩ := cycle_indexing G v c hc
  let n := Fintype.card V
  have hI_ne : I.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    subst h
    obtain ⟨w, hw, _⟩ := hI_dom v (by simp)
    simp at hw
  obtain ⟨s₀, hs₀⟩ := hI_ne
  let i₀ : Fin n := e₀.symm s₀
  let rotEquiv : Fin n ≃ Fin n :=
    ⟨fun i => i + i₀, fun i => i - i₀, fun i => add_sub_cancel_right i i₀, fun i => sub_add_cancel i i₀⟩
  let e : Fin n ≃ V := rotEquiv.trans e₀
  have he0 : e ⟨0, by omega⟩ = s₀ := by
    simp [e, rotEquiv, i₀]
  have he_adj : ∀ i : Fin n, G.Adj (e i) (e (i + 1)) := by
    intro i
    dsimp only [e, Equiv.trans_apply, rotEquiv, Equiv.coe_fn_mk]
    have hadd : i + 1 + i₀ = (i + i₀) + 1 := by abel
    rw [hadd]
    exact hadj₀ (i + i₀)
  have he_edges : ∀ x y : V, s(x, y) ∈ c.edges ↔ ∃ i : Fin n, s(x, y) = s(e i, e (i + 1)) := by
    intro x y
    rw [hedges₀ x y]
    constructor
    · rintro ⟨j, hj⟩
      refine ⟨j - i₀, ?_⟩
      dsimp only [e, Equiv.trans_apply, rotEquiv, Equiv.coe_fn_mk]
      have h1 : j - i₀ + i₀ = j := sub_add_cancel j i₀
      have h2 : j - i₀ + 1 + i₀ = j + 1 := by abel
      rw [h1, h2, hj]
    · rintro ⟨i, hi⟩
      refine ⟨i + i₀, ?_⟩
      dsimp only [e, Equiv.trans_apply, rotEquiv, Equiv.coe_fn_mk] at hi
      have h2 : i + 1 + i₀ = i + i₀ + 1 := by abel
      rwa [h2] at hi
  let G' : SimpleGraph (Fin n) := SimpleGraph.comap e G
  let I' : Finset (Fin n) := Finset.univ.filter fun i => e i ∈ I
  have h0I' : (⟨0, by omega⟩ : Fin n) ∈ I' := by
    rw [mem_filter]
    exact ⟨mem_univ _, by rw [he0]; exact hs₀⟩
  have hI'_ind : ∀ x ∈ I', ∀ y ∈ I', y ≠ x + 1 ∧ x ≠ y + 1 := by
    intro x hx y hy
    rw [mem_filter] at hx hy
    constructor
    · rintro rfl
      exact hI_ind (e x) hx.2 (e (x + 1)) hy.2 ((he_edges _ _).mpr ⟨x, rfl⟩)
    · rintro rfl
      exact hI_ind (e (y + 1)) hx.2 (e y) hy.2 ((he_edges _ _).mpr ⟨y, Sym2.eq_swap⟩)
  have hn4 : 4 ≤ n := by
    by_contra h
    have hn_eq : n = 3 := by omega
    have h1nI' : (⟨1, by omega⟩ : Fin n) ∉ I' := by
      intro h1
      apply (hI'_ind ⟨0, by omega⟩ h0I' ⟨1, by omega⟩ h1).1
      ext
      simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
    have hu : e ⟨1, by omega⟩ ∉ I := fun h => h1nI' (mem_filter.mpr ⟨mem_univ _, h⟩)
    obtain ⟨w, hwI, _, hnotc⟩ := hI_dom (e ⟨1, by omega⟩) hu
    let j := e.symm w
    have hj_mem : j ∈ I' := mem_filter.mpr ⟨mem_univ _, by simpa [j] using hwI⟩
    have hj_ne0 : j ≠ ⟨0, by omega⟩ := by
      intro hj0
      apply hnotc
      rw [← show e j = w by simp [j], hj0]
      refine (he_edges _ _).mpr ⟨⟨0, by omega⟩, ?_⟩
      have h01 : (⟨0, by omega⟩ : Fin n) + 1 = ⟨1, by omega⟩ := by
        ext; simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
      rw [h01, Sym2.eq_swap]
    have hj_ne1 : j ≠ ⟨1, by omega⟩ := fun h => h1nI' (h ▸ hj_mem)
    have hj_eq2 : j = ⟨2, by omega⟩ := by
      ext
      have hjv : (e.symm w).val < n := (e.symm w).isLt
      have hj0 : (e.symm w).val ≠ 0 := fun h => hj_ne0 (Fin.ext h)
      have hj1 : (e.symm w).val ≠ 1 := fun h => hj_ne1 (Fin.ext h)
      change (e.symm w).val = 2
      omega
    apply hnotc
    rw [← show e j = w by simp [j], hj_eq2]
    refine (he_edges _ _).mpr ⟨⟨1, by omega⟩, ?_⟩
    have h12 : (⟨1, by omega⟩ : Fin n) + 1 = ⟨2, by omega⟩ := by
      ext; simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < n),
        Nat.mod_eq_of_lt (by omega : 2 < n)]
    rw [h12]
  have hI'_dom : ∀ u : Fin n, u ∉ I' → ∃ w ∈ I', G'.Adj u w ∧ w ≠ u + 1 ∧ u ≠ w + 1 := by
    intro u hu
    have huI : e u ∉ I := fun h => hu (mem_filter.mpr ⟨mem_univ _, h⟩)
    obtain ⟨w, hwI, hadj_w, hnotc⟩ := hI_dom (e u) huI
    refine ⟨e.symm w, mem_filter.mpr ⟨mem_univ _, by simpa using hwI⟩, ?_, ?_, ?_⟩
    · simpa [G'] using hadj_w
    · intro h
      apply hnotc
      have hwu : w = e (u + 1) := by rw [← h]; simp
      rw [hwu]
      exact (he_edges _ _).mpr ⟨u, rfl⟩
    · intro h
      apply hnotc
      have huw : e u = e (e.symm w + 1) := congrArg e h
      rw [huw]
      refine (he_edges _ _).mpr ⟨e.symm w, ?_⟩
      simp [Sym2.eq_swap]
  obtain ⟨p, hp_inj, hp0, hp1, hp_adj, hp_last, i_diff, hi_diff_lt, hi_diff⟩ :=
    h2_on_fin n hn4 G' (fun i => by simpa [G'] using he_adj i) I' h0I' hI'_ind hI'_dom
  let l : List V := List.ofFn fun i : Fin n => e (p i)
  have hl_ne : l ≠ [] := by
    intro h
    have := congrArg List.length h
    simp [l] at this
    omega
  have hl_len : l.length = n := by simp [l]
  have hl_nodup : l.Nodup := by
    rw [List.nodup_ofFn]
    exact e.injective.comp hp_inj
  have hl_adj : ∀ i : ℕ, (hi : i + 1 < l.length) → G.Adj l[i] l[i + 1] := by
    intro i hi
    rw [hl_len] at hi
    simp only [l, List.getElem_ofFn]
    exact hp_adj i hi
  obtain ⟨q, hq_sup, hq_len, hq_edges⟩ := walkOfChain_exists G l hl_ne hl_adj
  have hhead : l.head hl_ne = e ⟨0, by omega⟩ := by
    rw [List.head_eq_getElem_zero]
    simp only [l, List.getElem_ofFn, hp0]
    rfl
  have hlast : l.getLast hl_ne = e (p ⟨n - 1, by omega⟩) := by
    rw [List.getLast_eq_getElem]
    simp only [l, hl_len, List.getElem_ofFn]
  have hadj_close : G.Adj (l.head hl_ne) (l.getLast hl_ne) := by
    rw [hhead, hlast]
    exact hp_last.symm
  let c' : G.Walk (l.head hl_ne) (l.head hl_ne) := Walk.cons hadj_close q.reverse
  have hc'_edge_not : s(l.head hl_ne, l.getLast hl_ne) ∉ q.reverse.edges := by
    rw [Walk.edges_reverse, List.mem_reverse, hq_edges]
    rintro ⟨i, hi, heq⟩
    rw [hl_len] at hi
    simp only [l, List.getElem_ofFn] at heq
    rw [hhead, hlast] at heq
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hp1' : p ⟨0, by omega⟩ = p ⟨i, by omega⟩ := hp0.symm ▸ e.injective h1
      have hv1 := congrArg Fin.val (hp_inj hp1')
      simp only at hv1
      have hv2 := congrArg Fin.val (hp_inj (e.injective h2))
      simp only at hv2
      omega
    · have hp1' : p ⟨0, by omega⟩ = p ⟨i + 1, hi⟩ := hp0.symm ▸ e.injective h1
      have hv1 := congrArg Fin.val (hp_inj hp1')
      simp only at hv1
      have hv2 := congrArg Fin.val (hp_inj (e.injective h2))
      simp only at hv2
      omega
  have hc'_cyc : c'.IsCycle := by
    rw [Walk.cons_isCycle_iff]
    refine ⟨?_, hc'_edge_not⟩
    rw [Walk.isPath_def, Walk.support_reverse, hq_sup]
    exact List.nodup_reverse.mpr hl_nodup
  have hc'_ham : ∀ w : V, w ∈ c'.support := by
    intro w
    simp only [c', Walk.support_cons, List.mem_cons, Walk.support_reverse, List.mem_reverse, hq_sup]
    right
    have hp_bij : Function.Bijective p := (Fintype.bijective_iff_injective_and_card _).mpr ⟨hp_inj, rfl⟩
    obtain ⟨i, hi⟩ := (e.bijective.comp hp_bij).2 w
    rw [← hi]
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  refine ⟨l.head hl_ne, c', ⟨hc'_cyc, hc'_ham⟩, ?_⟩
  intro hfin
  have hedge_sub : ∀ i : ℕ, (hi : i + 1 < n) →
      ∃ j : Fin n, s(e (p ⟨i, by omega⟩), e (p ⟨i + 1, hi⟩)) = s(e j, e (j + 1)) := by
    intro i hi
    have hmem : s(e (p ⟨i, by omega⟩), e (p ⟨i + 1, hi⟩)) ∈ c'.edges.toFinset := by
      rw [List.mem_toFinset]
      simp only [c', Walk.edges_cons, List.mem_cons, Walk.edges_reverse, List.mem_reverse, hq_edges]
      right
      refine ⟨i, by rw [hl_len]; exact hi, ?_⟩
      simp [l]
    rw [hfin, List.mem_toFinset] at hmem
    exact (he_edges _ _).mp hmem
  have hp_eq_id : ∀ k : ℕ, (hk : k < n) → p ⟨k, hk⟩ = ⟨k, hk⟩ := by
    intro k hk
    induction k using Nat.strong_induction_on with
    | h k ih =>
      rcases eq_or_lt_of_le (Nat.zero_le k) with rfl | hk0
      · exact hp0
      · rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hk0)) with rfl | hk1
        · exact hp1.trans (by ext; simp [Nat.mod_eq_of_lt hk])
        · have hk_m1 : k - 1 < k := by omega
          have hk_m2 : k - 2 < k := by omega
          have hpm1 := ih (k - 1) hk_m1 (by omega)
          have hpm2 := ih (k - 2) hk_m2 (by omega)
          obtain ⟨j, hj⟩ := hedge_sub (k - 1) (by omega)
          rw [Sym2.eq_iff] at hj
          have hstep : p ⟨k, hk⟩ = p ⟨k - 1, by omega⟩ + 1 ∨
              p ⟨k - 1, by omega⟩ = p ⟨k, hk⟩ + 1 := by
            rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · left
              have ha := e.injective h1
              have hb := e.injective h2
              have hc : (⟨k - 1 + 1, by omega⟩ : Fin n) = ⟨k, hk⟩ := by ext; simp; omega
              rw [hc] at hb
              rw [ha, hb]
            · right
              have ha := e.injective h1
              have hb := e.injective h2
              have hc : (⟨k - 1 + 1, by omega⟩ : Fin n) = ⟨k, hk⟩ := by ext; simp; omega
              rw [hc] at hb
              rw [ha, hb]
          rw [hpm1] at hstep
          rcases hstep with hplus | hminus
          · have h1val : (1 : Fin n).val = 1 := Nat.mod_eq_of_lt (by omega : 1 < n)
            rw [hplus, Fin.ext_iff, Fin.val_add, h1val]
            change (k - 1 + 1) % n = k
            rw [Nat.sub_add_cancel (by omega : 1 ≤ k), Nat.mod_eq_of_lt hk]
          · exfalso
            have hkp : p ⟨k, hk⟩ = ⟨k - 2, by omega⟩ := by
              have h1 := congrArg (· - 1) hminus
              have h2 : p ⟨k, hk⟩ = (⟨k - 1, by omega⟩ : Fin n) - 1 := by
                simpa using h1.symm
              rw [h2]
              ext
              have hv : ((⟨k - 1, by omega⟩ : Fin n) - 1).val = k - 2 := by
                rw [Fin.val_sub_one_of_ne_zero (by intro h; have := congrArg Fin.val h; simp at this; omega)]
                simp; omega
              exact hv
            have heq := hp_inj (hkp.trans hpm2.symm)
            have hval := congrArg Fin.val heq
            simp at hval; omega
  exact hi_diff (hp_eq_id i_diff hi_diff_lt)

end Helpers2

theorem h2_proof : OMA.SheehanR1.H2 :=
  fun G _ v c hc I hI_ind hI_dom => Helpers2.h2_main G v c hc I hI_ind hI_dom
end H2Section

theorem OMA.solution : type_of% @LovaszPlummerConjecture.sheehan_conjecture.variants.thomassen :=
  OMA.SheehanR1.main h1_proof h2_proof
