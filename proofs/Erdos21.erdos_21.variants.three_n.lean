import FormalConjectures.ErdosProblems.«21»
import Mathlib


/-!
# Polynomial-codegree edge coloring

This portion incorporates the indicated modules of Pippenger–Spencer in Lean,
copyright 2026 Juan Pablo Traverso Gianini, Apache-2.0.
Source: https://github.com/jtraverso/pippenger-spencer.
Modified by flattening its polynomial branch and porting to the pinned mathlib.
-/

/- PseudorandomLib.Defs -/
section FlattenedPS00
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/- # Hypergraphs, matchings and weights

Basic vocabulary for the formalization of Ehard–Glock–Joos, *Pseudorandom hypergraph
matchings* (arXiv:1907.09946).

A hypergraph on a finite vertex type `V` is a finite set `H : Finset (Finset V)` of edges.
It is `r`-uniform if every edge has exactly `r` vertices. A weight function is a function
`ω : Finset V → ℝ`; only its values on the edges of `H` matter.
-/

namespace Pseudorandom

open Finset

variable {V : Type*} [DecidableEq V]

/-- `H` is `r`-uniform: every edge has exactly `r` vertices. -/
def IsUniform (H : Finset (Finset V)) (r : ℕ) : Prop := ∀ e ∈ H, e.card = r

/-- The degree `deg_H(v)`: the number of edges containing `v`. -/
def degree (H : Finset (Finset V)) (v : V) : ℕ := (H.filter (fun e => v ∈ e)).card

/-- The codegree `deg_H(uv)`: the number of edges containing both `u` and `v`. -/
def codegree (H : Finset (Finset V)) (u v : V) : ℕ :=
  (H.filter (fun e => u ∈ e ∧ v ∈ e)).card

/-- A matching: a set of pairwise disjoint edges. -/
def IsMatching (M : Finset (Finset V)) : Prop :=
  ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f

/-- The weight `ω(X) = ∑_{e ∈ X} ω(e)` of a set of edges. -/
def weight (ω : Finset V → ℝ) (X : Finset (Finset V)) : ℝ := ∑ e ∈ X, ω e

end Pseudorandom

end FlattenedPS00

/- PseudorandomLib.PippengerSpencer.Basic -/
section FlattenedPS01
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/- # Proper edge colourings

Basic facts about proper edge colourings of hypergraphs:
* the definition `IsProperEdgeColouring`;
* the greedy bound: an `r`-uniform hypergraph of maximum degree `≤ Δ` has a proper edge
  colouring with `r Δ + 1` colours;
* gluing colourings of two edge sets with disjoint palettes.
-/

namespace Pseudorandom

open Finset

variable {V : Type*} [DecidableEq V]

/-- A proper edge colouring of `H` with `m` colours: edges of the same colour are disjoint. -/
def IsProperEdgeColouring (H : Finset (Finset V)) (m : ℕ) (c : Finset V → Fin m) : Prop :=
  ∀ e ∈ H, ∀ f ∈ H, e ≠ f → c e = c f → Disjoint e f

omit [DecidableEq V] in
theorem IsProperEdgeColouring.mono {H H' : Finset (Finset V)} {m : ℕ} {c : Finset V → Fin m}
    (h : IsProperEdgeColouring H m c) (hH : H' ⊆ H) : IsProperEdgeColouring H' m c :=
  fun e he f hf hef hc => h e (hH he) f (hH hf) hef hc

theorem degree_mono' {A B : Finset (Finset V)} (h : A ⊆ B) (v : V) :
    degree A v ≤ degree B v :=
  card_le_card (filter_subset_filter _ h)

/-- The edges of `H` meeting a set `e` number at most `∑_{v ∈ e} deg_H(v)`. -/
theorem card_filter_not_disjoint_le (H : Finset (Finset V)) (e : Finset V) :
    (H.filter (fun f => ¬ Disjoint e f)).card ≤ ∑ v ∈ e, degree H v := by
  have hsub : H.filter (fun f => ¬ Disjoint e f) ⊆
      e.biUnion (fun v => H.filter (fun f => v ∈ f)) := by
    intro f hf
    rw [mem_filter, Finset.not_disjoint_iff] at hf
    obtain ⟨hfH, v, hve, hvf⟩ := hf
    rw [mem_biUnion]
    exact ⟨v, hve, mem_filter.mpr ⟨hfH, hvf⟩⟩
  exact (card_le_card hsub).trans card_biUnion_le

/-- **Greedy colouring.** An `r`-uniform hypergraph with all degrees `≤ Δ` has a proper edge
colouring with `r Δ + 1` colours. -/
theorem exists_greedy_colouring (r Δ : ℕ) :
    ∀ (H : Finset (Finset V)), IsUniform H r → (∀ v, degree H v ≤ Δ) →
      ∃ c : Finset V → Fin (r * Δ + 1), IsProperEdgeColouring H (r * Δ + 1) c := by
  intro H
  induction H using Finset.induction_on with
  | empty => exact fun _ _ => ⟨fun _ => 0, fun e he => by simp at he⟩
  | @insert e H heH ih =>
    intro huni hdeg
    obtain ⟨c, hc⟩ := ih (fun f hf => huni f (mem_insert_of_mem hf))
      (fun v => (degree_mono' (subset_insert e H) v).trans (hdeg v))
    set used : Finset (Fin (r * Δ + 1)) := (H.filter (fun f => ¬ Disjoint e f)).image c
    have hused : used.card < r * Δ + 1 := by
      have h1 : used.card ≤ (H.filter (fun f => ¬ Disjoint e f)).card := card_image_le
      have h2 := card_filter_not_disjoint_le H e
      have h3 : ∑ v ∈ e, degree H v ≤ ∑ v ∈ e, Δ :=
        sum_le_sum fun v _ => (degree_mono' (subset_insert e H) v).trans (hdeg v)
      rw [sum_const, huni e (mem_insert_self e H), smul_eq_mul] at h3
      omega
    obtain ⟨k, hk⟩ : ∃ k : Fin (r * Δ + 1), k ∉ used := by
      by_contra h
      push Not at h
      have : (univ : Finset (Fin (r * Δ + 1))) ⊆ used := fun k _ => h k
      have := card_le_card this
      rw [card_univ, Fintype.card_fin] at this
      omega
    refine ⟨fun f => if f = e then k else c f, ?_⟩
    intro f hf g hg hfg hcol
    rw [mem_insert] at hf hg
    by_cases hfe : f = e
    · subst hfe
      have hge : g ≠ f := fun h => hfg h.symm
      have hgH : g ∈ H := hg.resolve_left hge
      simp only [hge, ite_true, ite_false] at hcol
      by_contra hd
      exact hk (hcol ▸ mem_image_of_mem c (mem_filter.mpr ⟨hgH, hd⟩))
    · have hfH : f ∈ H := hf.resolve_left hfe
      by_cases hge : g = e
      · subst hge
        simp only [hfe, ite_true, ite_false] at hcol
        by_contra hd
        exact hk (hcol.symm ▸ mem_image_of_mem c (mem_filter.mpr ⟨hfH, fun h => hd h.symm⟩))
      · have hgH : g ∈ H := hg.resolve_left hge
        simp only [hfe, hge, ite_false] at hcol
        exact hc f hfH g hgH hfg hcol

/-- Gluing two proper colourings with disjoint palettes. -/
theorem IsProperEdgeColouring.glue {H₁ H₂ : Finset (Finset V)} {m₁ m₂ : ℕ}
    {c₁ : Finset V → Fin m₁} {c₂ : Finset V → Fin m₂}
    (h₁ : IsProperEdgeColouring H₁ m₁ c₁) (h₂ : IsProperEdgeColouring H₂ m₂ c₂) :
    IsProperEdgeColouring (H₁ ∪ H₂) (m₁ + m₂)
      (fun e => if e ∈ H₁ then Fin.castAdd m₂ (c₁ e) else Fin.natAdd m₁ (c₂ e)) := by
  intro e he f hf hef hc
  rw [mem_union] at he hf
  by_cases he1 : e ∈ H₁ <;> by_cases hf1 : f ∈ H₁ <;>
    simp only [he1, hf1, ite_true, ite_false] at hc
  · exact h₁ e he1 f hf1 hef (Fin.castAdd_inj.mp hc)
  · exfalso
    have := congrArg Fin.val hc
    simp at this
    omega
  · exfalso
    have := congrArg Fin.val hc
    simp at this
    omega
  · exact h₂ e (he.resolve_left he1) f (hf.resolve_left hf1) hef (by
      have := congrArg Fin.val hc
      simp at this
      exact Fin.ext this)

omit [DecidableEq V] in
/-- Enlarging the palette. -/
theorem IsProperEdgeColouring.castLE {H : Finset (Finset V)} {m m' : ℕ} {c : Finset V → Fin m}
    (h : IsProperEdgeColouring H m c) (hm : m ≤ m') :
    IsProperEdgeColouring H m' (fun e => Fin.castLE hm (c e)) :=
  fun e he f hf hef hc => h e he f hf hef (Fin.castLE_inj.mp hc)

end Pseudorandom

end FlattenedPS01

/- PseudorandomLib.PippengerSpencer.ColourHypergraph -/
section FlattenedPS02
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/- # The colour hypergraph

For a hypergraph `H` on `V` and a number `C` of colours, the *colour hypergraph* lives on
`Finset V ⊕ (V × Fin C)`; its edges are `{e} ∪ {(v, c) : v ∈ e}` for `e ∈ H` and `c < C`.
A matching of the colour hypergraph is the same as a partial proper edge colouring of `H`
with `C` colours.
-/

namespace Pseudorandom.PS

open Finset

variable {V : Type*} [DecidableEq V] {C : ℕ}

/-- The edge `{e} ∪ {(v,c) : v ∈ e}` of the colour hypergraph. -/
def cedge (C : ℕ) (e : Finset V) (c : Fin C) : Finset (Finset V ⊕ (V × Fin C)) :=
  insert (Sum.inl e) (e.map ⟨fun v => Sum.inr (v, c), fun a b h => by simpa using h⟩)

theorem mem_cedge_inl {e e' : Finset V} {c : Fin C} :
    (Sum.inl e' : Finset V ⊕ (V × Fin C)) ∈ cedge C e c ↔ e' = e := by
  simp [cedge]

theorem mem_cedge_inr {e : Finset V} {c c' : Fin C} {v : V} :
    (Sum.inr (v, c') : Finset V ⊕ (V × Fin C)) ∈ cedge C e c ↔ v ∈ e ∧ c' = c := by
  simp only [cedge, mem_insert, reduceCtorEq, false_or, mem_map]
  constructor
  · rintro ⟨u, hu, h⟩
    have h' : Sum.inr (u, c) = (Sum.inr (v, c') : Finset V ⊕ (V × Fin C)) := h
    simp only [Sum.inr.injEq, Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl⟩ := h'
    exact ⟨hu, rfl⟩
  · rintro ⟨hv, rfl⟩; exact ⟨v, hv, rfl⟩

theorem card_cedge (e : Finset V) (c : Fin C) : (cedge C e c).card = e.card + 1 := by
  unfold cedge
  rw [card_insert_of_notMem (by simp), card_map]

theorem cedge_inj {e e' : Finset V} {c c' : Fin C} (he : e.Nonempty)
    (h : cedge C e c = cedge C e' c') : e = e' ∧ c = c' := by
  have h1 : e = e' := by
    have : (Sum.inl e : Finset V ⊕ (V × Fin C)) ∈ cedge C e' c' := by
      rw [← h]; exact mem_cedge_inl.mpr rfl
    exact mem_cedge_inl.mp this
  subst h1
  obtain ⟨v, hv⟩ := he
  have : (Sum.inr (v, c) : Finset V ⊕ (V × Fin C)) ∈ cedge C e c' := by
    rw [← h]; exact mem_cedge_inr.mpr ⟨hv, rfl⟩
  exact ⟨rfl, (mem_cedge_inr.mp this).2⟩

/-- The colour hypergraph. -/
def colourHyp (H : Finset (Finset V)) (C : ℕ) : Finset (Finset (Finset V ⊕ (V × Fin C))) :=
  (H ×ˢ (univ : Finset (Fin C))).image (fun p => cedge C p.1 p.2)

theorem colourHyp_uniform {H : Finset (Finset V)} {r : ℕ} (huni : IsUniform H r) :
    IsUniform (colourHyp H C) (r + 1) := by
  intro x hx
  simp only [colourHyp, mem_image, mem_product] at hx
  obtain ⟨⟨e, c⟩, ⟨he, -⟩, rfl⟩ := hx
  rw [card_cedge, huni e he]

theorem card_colourHyp_le (H : Finset (Finset V)) : (colourHyp H C).card ≤ H.card * C := by
  unfold colourHyp
  refine card_image_le.trans ?_
  simp

/-- Degrees and codegrees of the colour hypergraph are bounded by counting the pairs `(e,c)`. -/
theorem card_filter_colourHyp_le (H : Finset (Finset V)) (q : Finset (Finset V ⊕ (V × Fin C)) → Prop)
    [DecidablePred q] :
    ((colourHyp H C).filter q).card ≤
      ((H ×ˢ (univ : Finset (Fin C))).filter (fun p => q (cedge C p.1 p.2))).card := by
  unfold colourHyp
  rw [filter_image]
  exact card_image_le

theorem degree_colourHyp_inl (H : Finset (Finset V)) (e : Finset V) :
    degree (colourHyp H C) (Sum.inl e) ≤ C := by
  unfold degree
  refine (card_filter_colourHyp_le H _).trans ?_
  calc _ ≤ (({e} : Finset (Finset V)) ×ˢ (univ : Finset (Fin C))).card := by
        apply card_le_card
        intro p hp
        simp only [mem_filter, mem_product] at hp
        have := mem_cedge_inl.mp hp.2
        exact mem_product.mpr ⟨mem_singleton.mpr this.symm, mem_univ _⟩
    _ = C := by simp

theorem degree_colourHyp_inr (H : Finset (Finset V)) (v : V) (c : Fin C) :
    degree (colourHyp H C) (Sum.inr (v, c)) ≤ degree H v := by
  unfold degree
  refine (card_filter_colourHyp_le H _).trans ?_
  calc _ ≤ ((H.filter (fun e => v ∈ e)) ×ˢ ({c} : Finset (Fin C))).card := by
        apply card_le_card
        intro p hp
        simp only [mem_filter, mem_product] at hp
        have := mem_cedge_inr.mp hp.2
        exact mem_product.mpr ⟨mem_filter.mpr ⟨hp.1.1, this.1⟩, mem_singleton.mpr this.2.symm⟩
    _ = _ := by simp

theorem codegree_colourHyp_le (H : Finset (Finset V)) (y z : Finset V ⊕ (V × Fin C))
    (hyz : y ≠ z) :
    codegree (colourHyp H C) y z ≤ 1 ∨
      ∃ u v, u ≠ v ∧ codegree (colourHyp H C) y z ≤ codegree H u v := by
  unfold codegree
  have key := card_filter_colourHyp_le (C := C) H (fun x => y ∈ x ∧ z ∈ x)
  rcases y with e | ⟨u, c⟩ <;> rcases z with e' | ⟨v, c'⟩
  · left
    refine key.trans (le_of_eq_of_le ?_ zero_le_one)
    rw [card_eq_zero, filter_eq_empty_iff]
    rintro p - ⟨h1, h2⟩
    exact hyz (by rw [mem_cedge_inl.mp h1, mem_cedge_inl.mp h2])
  · left
    refine key.trans ((card_le_card (s := _) (t := {(e, c')}) ?_).trans (by simp))
    intro p hp
    simp only [mem_filter] at hp
    have h1 := mem_cedge_inl.mp hp.2.1
    have h2 := mem_cedge_inr.mp hp.2.2
    exact mem_singleton.mpr (Prod.ext h1.symm h2.2.symm)
  · left
    refine key.trans ((card_le_card (s := _) (t := {(e', c)}) ?_).trans (by simp))
    intro p hp
    simp only [mem_filter] at hp
    have h1 := mem_cedge_inl.mp hp.2.2
    have h2 := mem_cedge_inr.mp hp.2.1
    exact mem_singleton.mpr (Prod.ext h1.symm h2.2.symm)
  · by_cases huv : u = v
    · subst huv
      left
      refine key.trans (le_of_eq_of_le ?_ zero_le_one)
      rw [card_eq_zero, filter_eq_empty_iff]
      rintro p - ⟨h1, h2⟩
      have := (mem_cedge_inr.mp h1).2
      have := (mem_cedge_inr.mp h2).2
      exact hyz (by subst_vars; rfl)
    · right
      refine ⟨u, v, huv, key.trans ?_⟩
      calc _ ≤ ((H.filter (fun e => u ∈ e ∧ v ∈ e)) ×ˢ ({c} : Finset (Fin C))).card := by
            apply card_le_card
            intro p hp
            simp only [mem_filter, mem_product] at hp
            have h1 := mem_cedge_inr.mp hp.2.1
            have h2 := mem_cedge_inr.mp hp.2.2
            exact mem_product.mpr ⟨mem_filter.mpr ⟨hp.1.1, h1.1, h2.1⟩,
              mem_singleton.mpr h1.2.symm⟩
        _ = _ := by simp

/- ## Matchings of the colour hypergraph are partial colourings -/

/-- The weight function counting the colour-vertices `(v, ·)` of an edge. -/
def wv (v : V) (x : Finset (Finset V ⊕ (V × Fin C))) : ℝ :=
  ((x.filter (fun y => ∃ c, y = Sum.inr (v, c))).card : ℝ)

theorem wv_nonneg (v : V) (x : Finset (Finset V ⊕ (V × Fin C))) : 0 ≤ wv v x :=
  Nat.cast_nonneg _

theorem wv_cedge (v : V) (e : Finset V) (c : Fin C) :
    wv v (cedge C e c) = if v ∈ e then 1 else 0 := by
  unfold wv
  have : (cedge C e c).filter (fun y => ∃ c', y = Sum.inr (v, c')) =
      if v ∈ e then {Sum.inr (v, c)} else ∅ := by
    ext y
    rcases y with e' | ⟨u, c'⟩
    · simp only [mem_filter, reduceCtorEq, exists_false, and_false, false_iff]
      split_ifs <;> simp
    · simp only [mem_filter, mem_cedge_inr, Sum.inr.injEq, Prod.mk.injEq, exists_and_left,
        exists_eq', and_true]
      split_ifs with hv
      · simp only [mem_singleton, Sum.inr.injEq, Prod.mk.injEq]
        constructor
        · rintro ⟨⟨-, rfl⟩, rfl⟩; exact ⟨rfl, rfl⟩
        · rintro ⟨rfl, rfl⟩; exact ⟨⟨hv, rfl⟩, rfl⟩
      · simp only [notMem_empty, iff_false, not_and]
        rintro ⟨hu, -⟩ rfl
        exact hv hu
  rw [this]
  split_ifs <;> simp

theorem wv_le_one {H : Finset (Finset V)} {x : Finset (Finset V ⊕ (V × Fin C))}
    (hx : x ∈ colourHyp H C) (v : V) : wv v x ≤ 1 := by
  simp only [colourHyp, mem_image] at hx
  obtain ⟨p, -, rfl⟩ := hx
  rw [wv_cedge]; split_ifs <;> norm_num

theorem weight_image {H : Finset (Finset V)} (hne : ∀ e ∈ H, e.Nonempty)
    (S : Finset (Finset V × Fin C)) (hS : S ⊆ H ×ˢ univ) (v : V) :
    weight (wv v) (S.image (fun p => cedge C p.1 p.2)) =
      ((S.filter (fun p => v ∈ p.1)).card : ℝ) := by
  unfold weight
  rw [sum_image]
  · simp_rw [wv_cedge]
    rw [sum_boole]
  · intro p hp q _ hpq
    have hpH : p.1 ∈ H := (mem_product.mp (hS hp)).1
    obtain ⟨h1, h2⟩ := cedge_inj (hne _ hpH) hpq
    exact Prod.ext h1 h2

theorem weight_colourHyp {H : Finset (Finset V)} (hne : ∀ e ∈ H, e.Nonempty) (v : V) :
    weight (wv v) (colourHyp H C) = (degree H v : ℝ) * C := by
  unfold colourHyp
  rw [weight_image hne _ (subset_refl _)]
  have : (H ×ˢ (univ : Finset (Fin C))).filter (fun p => v ∈ p.1) =
      (H.filter (fun e => v ∈ e)) ×ˢ univ := by
    ext p; simp [and_assoc]
  rw [this, card_product, card_univ, Fintype.card_fin]
  unfold degree
  push_cast; ring

/-- The edges of `H` coloured by a matching `M` of the colour hypergraph. -/
def col (H : Finset (Finset V)) (M : Finset (Finset (Finset V ⊕ (V × Fin C)))) :
    Finset (Finset V) :=
  H.filter (fun e => ∃ c, cedge C e c ∈ M)

theorem col_subset (H : Finset (Finset V)) (M : Finset (Finset (Finset V ⊕ (V × Fin C)))) :
    col H M ⊆ H := filter_subset _ _

theorem weight_matching {H : Finset (Finset V)} (hne : ∀ e ∈ H, e.Nonempty)
    {M : Finset (Finset (Finset V ⊕ (V × Fin C)))} (hMH : M ⊆ colourHyp H C)
    (hM : IsMatching M) (v : V) :
    weight (wv v) M = (((col H M).filter (fun e => v ∈ e)).card : ℝ) := by
  set S := (H ×ˢ (univ : Finset (Fin C))).filter (fun p => cedge C p.1 p.2 ∈ M) with hSdef
  have hMS : M = S.image (fun p => cedge C p.1 p.2) := by
    ext x
    constructor
    · intro hx
      have := hMH hx
      simp only [colourHyp, mem_image] at this
      obtain ⟨p, hp, rfl⟩ := this
      exact mem_image.mpr ⟨p, mem_filter.mpr ⟨hp, hx⟩, rfl⟩
    · intro hx
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hx
      exact (mem_filter.mp hp).2
  have hw := weight_image (C := C) hne S (filter_subset _ _) v
  rw [← hMS] at hw
  rw [hw]
  congr 1
  have himg : (S.filter (fun p => v ∈ p.1)).image Prod.fst = (col H M).filter (fun e => v ∈ e) := by
    ext e
    simp only [mem_image, mem_filter, hSdef, mem_product, mem_univ, and_true, col]
    constructor
    · rintro ⟨p, ⟨⟨hp1, hp2⟩, hv⟩, rfl⟩
      exact ⟨⟨hp1, p.2, hp2⟩, hv⟩
    · rintro ⟨⟨he, c, hc⟩, hv⟩
      exact ⟨(e, c), ⟨⟨he, hc⟩, hv⟩, rfl⟩
  rw [← himg, card_image_of_injOn]
  intro p hp q hq hpq
  simp only [coe_filter, Set.mem_ofPred_eq, hSdef, mem_filter, mem_product] at hp hq
  have hpq' : p.1 = q.1 := hpq
  by_contra hne'
  have hc : p.2 ≠ q.2 := fun h => hne' (Prod.ext hpq' h)
  have hdiff : cedge C p.1 p.2 ≠ cedge C q.1 q.2 := by
    intro h
    exact hc (cedge_inj (hne _ hp.1.1.1) h).2
  have hd := hM _ hp.1.2 _ hq.1.2 hdiff
  have h1 : (Sum.inl p.1 : Finset V ⊕ (V × Fin C)) ∈ cedge C p.1 p.2 := mem_cedge_inl.mpr rfl
  have h2 : (Sum.inl p.1 : Finset V ⊕ (V × Fin C)) ∈ cedge C q.1 q.2 :=
    mem_cedge_inl.mpr hpq'
  exact Finset.disjoint_left.mp hd h1 h2

/-- The leftover degree: `deg_{H \ col}(v) = deg_H(v) - #(coloured edges at v)`. -/
theorem degree_sdiff_col (H : Finset (Finset V)) (M : Finset (Finset (Finset V ⊕ (V × Fin C))))
    (v : V) :
    degree (H \ col H M) v + ((col H M).filter (fun e => v ∈ e)).card = degree H v := by
  unfold degree
  have : (H \ col H M).filter (fun e => v ∈ e) =
      H.filter (fun e => v ∈ e) \ (col H M).filter (fun e => v ∈ e) := by
    ext e; simp only [mem_filter, mem_sdiff]; tauto
  rw [this, card_sdiff_add_card_eq_card]
  exact filter_subset_filter _ (col_subset H M)

open Classical in
/-- The colouring of the coloured edges given by a matching of the colour hypergraph. -/
noncomputable def colOf (M : Finset (Finset (Finset V ⊕ (V × Fin C)))) (hC : 0 < C) :
    Finset V → Fin C :=
  fun e => if h : ∃ c, cedge C e c ∈ M then h.choose else ⟨0, hC⟩

theorem colOf_proper (H : Finset (Finset V)) {M : Finset (Finset (Finset V ⊕ (V × Fin C)))}
    (hM : IsMatching M) (hC : 0 < C) : IsProperEdgeColouring (col H M) C (colOf M hC) := by
  intro e he f hf hef hcol
  have he' := (mem_filter.mp he).2
  have hf' := (mem_filter.mp hf).2
  have hce : cedge C e (colOf M hC e) ∈ M := by
    have := he'.choose_spec; simpa [colOf, he'] using this
  have hcf : cedge C f (colOf M hC e) ∈ M := by
    rw [hcol]; have := hf'.choose_spec; simpa [colOf, hf'] using this
  have hdiff : cedge C e (colOf M hC e) ≠ cedge C f (colOf M hC e) := by
    intro h
    have : (Sum.inl e : Finset V ⊕ (V × Fin C)) ∈ cedge C f (colOf M hC e) := by
      rw [← h]; exact mem_cedge_inl.mpr rfl
    exact hef (mem_cedge_inl.mp this)
  have hd := hM _ hce _ hcf hdiff
  rw [Finset.disjoint_left]
  intro v hve hvf
  exact Finset.disjoint_left.mp hd (mem_cedge_inr.mpr ⟨hve, rfl⟩) (mem_cedge_inr.mpr ⟨hvf, rfl⟩)

end Pseudorandom.PS

end FlattenedPS02

/- PseudorandomLib.FiniteProb -/
section FlattenedPS03
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/- # Finite product probability spaces

A product probability space over a finite index type `ι` with a finite coordinate type `α`
is given by a family `P : ι → α → ℝ` of probability mass functions (`IsPMF P`). An outcome is
a function `ω : ι → α`, with weight `pw P ω = ∏ i, P i (ω i)`. Expectations `pE` and
probabilities `pProb` are explicit finite sums, so nothing measure-theoretic is needed.
-/

namespace Pseudorandom

open Finset

section Basic

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

/-- `P` is a family of probability mass functions on `α`, one for each coordinate. -/
def IsPMF (P : ι → α → ℝ) : Prop := (∀ i a, 0 ≤ P i a) ∧ ∀ i, ∑ a, P i a = 1

/-- The product weight of an outcome. -/
def pw (P : ι → α → ℝ) (ω : ι → α) : ℝ := ∏ i, P i (ω i)

/-- Expectation in the product space. -/
def pE (P : ι → α → ℝ) (f : (ι → α) → ℝ) : ℝ := ∑ ω, pw P ω * f ω

open Classical in
/-- Probability of an event in the product space. -/
noncomputable def pProb (P : ι → α → ℝ) (S : (ι → α) → Prop) : ℝ :=
  pE P (fun ω => if S ω then 1 else 0)

variable {P : ι → α → ℝ}

omit [DecidableEq ι] in
theorem pw_nonneg (hP : IsPMF P) (ω : ι → α) : 0 ≤ pw P ω :=
  prod_nonneg fun i _ => hP.1 i (ω i)

theorem sum_pw (hP : IsPMF P) : ∑ ω, pw P ω = 1 := by
  unfold pw
  rw [← Fintype.prod_sum (fun i a => P i a)]
  simp [hP.2]

theorem pE_const (hP : IsPMF P) (c : ℝ) : pE P (fun _ => c) = c := by
  unfold pE
  rw [← sum_mul, sum_pw hP, one_mul]

theorem pE_add (f g : (ι → α) → ℝ) : pE P (fun ω => f ω + g ω) = pE P f + pE P g := by
  unfold pE
  rw [← sum_add_distrib]
  congr 1; funext ω; ring

theorem pE_sub (f g : (ι → α) → ℝ) : pE P (fun ω => f ω - g ω) = pE P f - pE P g := by
  unfold pE
  rw [← sum_sub_distrib]
  congr 1; funext ω; ring

theorem pE_const_mul (c : ℝ) (f : (ι → α) → ℝ) : pE P (fun ω => c * f ω) = c * pE P f := by
  unfold pE
  rw [mul_sum]
  congr 1; funext ω; ring

theorem pE_neg (f : (ι → α) → ℝ) : pE P (fun ω => -f ω) = -pE P f := by
  have := pE_const_mul (P := P) (-1) f
  simpa using this

theorem pE_sum {κ : Type*} (s : Finset κ) (f : κ → (ι → α) → ℝ) :
    pE P (fun ω => ∑ k ∈ s, f k ω) = ∑ k ∈ s, pE P (f k) := by
  unfold pE
  simp_rw [mul_sum]
  rw [sum_comm]

theorem pE_mono (hP : IsPMF P) {f g : (ι → α) → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    pE P f ≤ pE P g :=
  sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (pw_nonneg hP ω)

/-- Monotonicity only needs the inequality on outcomes of positive weight. -/
theorem pE_mono_supp (hP : IsPMF P) {f g : (ι → α) → ℝ} (h : ∀ ω, 0 < pw P ω → f ω ≤ g ω) :
    pE P f ≤ pE P g := by
  refine sum_le_sum fun ω _ => ?_
  rcases (pw_nonneg hP ω).lt_or_eq with hpos | hzero
  · exact mul_le_mul_of_nonneg_left (h ω hpos) hpos.le
  · rw [← hzero]; simp

theorem pE_nonneg (hP : IsPMF P) {f : (ι → α) → ℝ} (h : ∀ ω, 0 ≤ f ω) : 0 ≤ pE P f := by
  have := pE_mono hP (f := fun _ => (0 : ℝ)) h
  rwa [pE_const hP] at this

/-- Expectation of a product of functions of distinct coordinates (independence). -/
theorem pE_prod (g : ι → α → ℝ) :
    pE P (fun ω => ∏ i, g i (ω i)) = ∏ i, ∑ a, P i a * g i a := by
  unfold pE pw
  rw [Fintype.prod_sum (fun i a => P i a * g i a)]
  congr 1; funext ω
  rw [prod_mul_distrib]

/-- Expectation of a function of a single coordinate. -/
theorem pE_coord (hP : IsPMF P) (i : ι) (g : α → ℝ) :
    pE P (fun ω => g (ω i)) = ∑ a, P i a * g a := by
  have h := pE_prod (P := P) (fun j a => if j = i then g a else 1)
  have hl : (fun ω : ι → α => ∏ j, (if j = i then g (ω j) else 1)) = fun ω => g (ω i) := by
    funext ω
    rw [prod_ite_eq' univ i (fun j => g (ω j))]
    simp
  simp only [hl] at h
  rw [h, prod_eq_single i]
  · simp
  · intro j _ hj
    simp [hj, hP.2 j]
  · simp

theorem pProb_nonneg (hP : IsPMF P) (S : (ι → α) → Prop) : 0 ≤ pProb P S := by
  classical
  unfold pProb
  exact pE_nonneg hP fun ω => by split_ifs <;> norm_num

theorem pProb_le_one (hP : IsPMF P) (S : (ι → α) → Prop) : pProb P S ≤ 1 := by
  classical
  unfold pProb
  calc _ ≤ pE P (fun _ => (1 : ℝ)) := pE_mono hP fun ω => by split_ifs <;> norm_num
    _ = 1 := pE_const hP 1

theorem pProb_mono (hP : IsPMF P) {S T : (ι → α) → Prop} (h : ∀ ω, S ω → T ω) :
    pProb P S ≤ pProb P T := by
  classical
  unfold pProb
  refine pE_mono hP fun ω => ?_
  by_cases hs : S ω
  · simp [hs, h ω hs]
  · simp only [hs, if_false]; split_ifs <;> norm_num

/-- Union bound. -/
theorem pProb_exists_le {κ : Type*} (hP : IsPMF P) (s : Finset κ) (S : κ → (ι → α) → Prop) :
    pProb P (fun ω => ∃ k ∈ s, S k ω) ≤ ∑ k ∈ s, pProb P (S k) := by
  classical
  unfold pProb
  rw [← pE_sum]
  refine pE_mono hP fun ω => ?_
  split_ifs with h
  · obtain ⟨k, hk, hS⟩ := h
    calc (1 : ℝ) = if S k ω then 1 else 0 := by simp [hS]
      _ ≤ ∑ k ∈ s, if S k ω then (1 : ℝ) else 0 :=
          single_le_sum (f := fun k => if S k ω then (1 : ℝ) else 0)
            (fun k _ => by show (0:ℝ) ≤ if S k ω then 1 else 0; split_ifs <;> norm_num) hk
  · exact sum_nonneg fun k _ => by split_ifs <;> norm_num

theorem pProb_or_le (hP : IsPMF P) (S T : (ι → α) → Prop) :
    pProb P (fun ω => S ω ∨ T ω) ≤ pProb P S + pProb P T := by
  classical
  unfold pProb
  rw [← pE_add]
  refine pE_mono hP fun ω => ?_
  by_cases hs : S ω <;> by_cases ht : T ω <;> simp [hs, ht]

theorem pProb_not (hP : IsPMF P) (S : (ι → α) → Prop) :
    pProb P (fun ω => ¬ S ω) = 1 - pProb P S := by
  classical
  unfold pProb
  have h := pE_sub (P := P) (fun _ => (1 : ℝ)) (fun ω => if S ω then 1 else 0)
  rw [pE_const hP] at h
  rw [← h]
  congr 1; funext ω
  by_cases hs : S ω <;> simp [hs]

/-- If an event has probability `< 1`, some outcome of positive weight avoids it. -/
theorem exists_of_pProb_lt_one (hP : IsPMF P) {S : (ι → α) → Prop} (h : pProb P S < 1) :
    ∃ ω, 0 < pw P ω ∧ ¬ S ω := by
  classical
  by_contra hcon
  push_neg at hcon
  have : pProb P S = 1 := by
    unfold pProb pE
    have : ∑ ω, pw P ω * (if S ω then (1 : ℝ) else 0) = ∑ ω, pw P ω := by
      refine sum_congr rfl fun ω _ => ?_
      rcases (pw_nonneg hP ω).lt_or_eq with hpos | hzero
      · simp [hcon ω hpos]
      · rw [← hzero]; simp
    rw [this, sum_pw hP]
  linarith

/-- Probability of the event that a function is at least `t` is at most `E f / t`
(Markov's inequality, for nonnegative `f`). -/
theorem pProb_ge_le_markov (hP : IsPMF P) {f : (ι → α) → ℝ} (hf : ∀ ω, 0 ≤ f ω) {t : ℝ}
    (ht : 0 < t) : pProb P (fun ω => t ≤ f ω) ≤ pE P f / t := by
  classical
  rw [le_div_iff₀ ht]
  unfold pProb
  rw [mul_comm, ← pE_const_mul]
  refine pE_mono hP fun ω => ?_
  split_ifs with h
  · linarith
  · linarith [hf ω]


/-- A probability is the expectation of any indicator function of the event. -/
theorem pProb_eq_pE (S : (ι → α) → Prop) (g : (ι → α) → ℝ) (h1 : ∀ ω, S ω → g ω = 1)
    (h0 : ∀ ω, ¬ S ω → g ω = 0) : pProb P S = pE P g := by
  classical
  unfold pProb
  congr 1; funext ω
  by_cases hs : S ω
  · rw [if_pos hs, h1 ω hs]
  · rw [if_neg hs, h0 ω hs]

/-- Probability of a cylinder event: prescribed values on a finite set of coordinates. -/
theorem pProb_cylinder (hP : IsPMF P) (S : Finset ι) (x : ι → α) :
    pProb P (fun ω => ∀ i ∈ S, ω i = x i) = ∏ i ∈ S, P i (x i) := by
  classical
  rw [pProb_eq_pE _ (fun ω => ∏ i, (if i ∈ S then (if ω i = x i then (1 : ℝ) else 0) else 1))]
  · rw [pE_prod (fun i a => if i ∈ S then (if a = x i then (1 : ℝ) else 0) else 1)]
    have : ∀ i, ∑ a, P i a * (if i ∈ S then (if a = x i then (1 : ℝ) else 0) else 1) =
        if i ∈ S then P i (x i) else 1 := by
      intro i
      by_cases hi : i ∈ S
      · simp [hi]
      · simp [hi, hP.2 i]
    simp_rw [this]
    rw [prod_ite_mem univ S, univ_inter]
  · intro ω h
    refine prod_eq_one fun i _ => ?_
    split_ifs with h1 h2 <;> simp_all
  · intro ω h
    push_neg at h
    obtain ⟨i, hi, hne⟩ := h
    exact prod_eq_zero (mem_univ i) (by simp [hi, hne])

/-- Probability of the complement of a cylinder event. -/
theorem pProb_not_cylinder (hP : IsPMF P) (S : Finset ι) (x : ι → α) :
    pProb P (fun ω => ¬ ∀ i ∈ S, ω i = x i) = 1 - ∏ i ∈ S, P i (x i) := by
  rw [pProb_not hP, pProb_cylinder hP]

theorem pProb_congr {S T : (ι → α) → Prop} (h : ∀ ω, S ω ↔ T ω) : pProb P S = pProb P T := by
  have : S = T := funext fun ω => propext (h ω)
  rw [this]

end Basic

/- ## Transport along an equivalence of index types -/

section Transport

variable {ι κ α : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype α]

theorem pE_equiv (e : ι ≃ κ) (P : ι → α → ℝ) (f : (ι → α) → ℝ) :
    pE P f = pE (fun j => P (e.symm j)) (fun ω' => f (ω' ∘ e)) := by
  unfold pE pw
  refine Fintype.sum_equiv (Equiv.arrowCongr e (Equiv.refl α)) _ _ fun ω => ?_
  have h1 : (Equiv.arrowCongr e (Equiv.refl α) ω) ∘ e = ω := by
    funext i; simp [Equiv.arrowCongr_apply]
  dsimp only
  rw [h1]
  congr 1
  refine Fintype.prod_equiv e _ _ fun i => ?_
  simp [Equiv.arrowCongr_apply]

theorem pProb_equiv (e : ι ≃ κ) (P : ι → α → ℝ) (S : (ι → α) → Prop) :
    pProb P S = pProb (fun j => P (e.symm j)) (fun ω' => S (ω' ∘ e)) := by
  classical
  unfold pProb
  rw [pE_equiv e]

end Transport

end Pseudorandom

end FlattenedPS03

/- PseudorandomLib.Bernstein -/
section FlattenedPS04
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/- # A Bernstein-type bounded-differences inequality on finite product spaces

Let `f` be a function of independent coordinates. Suppose that changing coordinate `i`
changes `f` by at most `c i ≤ L`, and that coordinate `i` only matters through a set `R i`
of "rare" values: changing coordinate `i` between two values outside `R i` does not change
`f`. If `R i` has probability at most `q i`, then with `V = ∑ i, q i * c i ^ 2`

  `P(f - E f ≥ t) ≤ exp(-t² / (2 (V + L t)))`.

Taking `R i = univ`, `q i = 1` gives a McDiarmid-type inequality; taking two-point
coordinates gives a Chernoff-type inequality. Everything is proved from scratch: the
one-coordinate exponential bound comes from the exponential series, and it is iterated along
the coordinates (an exposure martingale written as a recursion).
-/

namespace Pseudorandom

open Finset

open Nat in
/-- `e^x ≤ 1 + x + x²/(2(1-r))` whenever `|x| ≤ r < 1`. -/
theorem exp_le_one_add_add_sq_div (x r : ℝ) (hx : |x| ≤ r) (hr : r < 1) :
    Real.exp x ≤ 1 + x + x ^ 2 / (2 * (1 - r)) := by
  have hE : HasSum (fun n : ℕ => x ^ n / (n ! : ℝ)) (Real.exp x) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp x
  set a := |x| with ha
  have ha0 : 0 ≤ a := abs_nonneg x
  have ha1 : a < 1 := lt_of_le_of_lt hx hr
  have hG : HasSum (fun n : ℕ => a ^ n) (1 - a)⁻¹ := hasSum_geometric_of_lt_one ha0 ha1
  have hG2 : HasSum (fun n : ℕ => a ^ (n + 2) / 2) (a ^ 2 * (1 - a)⁻¹ / 2) := by
    have := (hG.mul_left (a ^ 2)).div_const 2
    simpa [pow_add, mul_comm] using this
  have hE2 : HasSum (fun n : ℕ => x ^ (n + 2) / ((n + 2) ! : ℝ))
      (Real.exp x - ∑ i ∈ Finset.range 2, x ^ i / (i ! : ℝ)) :=
    (hasSum_nat_add_iff' 2).mpr hE
  have hle := hasSum_le (fun n => ?_) hE2 hG2
  · simp [Finset.sum_range_succ] at hle
    have h1 : a ^ 2 = x ^ 2 := by rw [ha, sq_abs]
    have h2 : a ^ 2 * (1 - a)⁻¹ / 2 ≤ x ^ 2 / (2 * (1 - r)) := by
      rw [h1, div_le_div_iff₀ (by norm_num) (by linarith), ← div_eq_mul_inv]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith [sq_nonneg x]
    linarith
  · have hf : (2 : ℝ) ≤ ((n + 2) ! : ℝ) := by
      have : 2 ≤ (n + 2) ! := by
        calc 2 = (2 : ℕ) ! := rfl
          _ ≤ (n + 2) ! := Nat.factorial_le (by omega)
      exact_mod_cast this
    have hxa : x ^ (n + 2) ≤ a ^ (n + 2) := by
      rw [ha, ← abs_pow]; exact le_abs_self _
    calc x ^ (n + 2) / ((n + 2) ! : ℝ) ≤ a ^ (n + 2) / ((n + 2) ! : ℝ) := by
          gcongr
      _ ≤ a ^ (n + 2) / 2 := by
          apply div_le_div_of_nonneg_left (by positivity) (by norm_num) hf

/-- One-coordinate exponential bound. -/
theorem coord_exp_bound {α : Type*} [Fintype α] (p : α → ℝ) (hp0 : ∀ a, 0 ≤ p a)
    (hp1 : ∑ a, p a = 1) (M : α → ℝ) (c L lam q : ℝ) (R : Finset α)
    (hgap : ∀ a b, |M a - M b| ≤ c) (hR : ∀ a b, a ∉ R → b ∉ R → M a = M b)
    (hq : ∑ a ∈ R, p a ≤ q) (hcL : c ≤ L) (hlam : 0 ≤ lam) (hlamL : lam * L < 1) :
    ∑ a, p a * Real.exp (lam * (M a - ∑ b, p b * M b)) ≤
      Real.exp (lam ^ 2 * (q * c ^ 2) / (2 * (1 - lam * L))) := by
  classical
  set m := ∑ b, p b * M b with hm
  have hne : Nonempty α := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hp1
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hgap (Classical.arbitrary _) (Classical.arbitrary _))
  have hY : ∀ a, |M a - m| ≤ c := by
    intro a
    have : M a - m = ∑ b, p b * (M a - M b) := by
      rw [hm]; simp_rw [mul_sub]; rw [sum_sub_distrib, ← sum_mul, hp1, one_mul]
    rw [this]
    calc |∑ b, p b * (M a - M b)| ≤ ∑ b, |p b * (M a - M b)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ b, p b * c := sum_le_sum fun b _ => by
          rw [abs_mul, abs_of_nonneg (hp0 b)]
          exact mul_le_mul_of_nonneg_left (hgap a b) (hp0 b)
      _ = c := by rw [← sum_mul, hp1, one_mul]
  have hK : 0 < 1 - lam * L := by linarith
  -- variance bound
  have hvar : ∑ a, p a * (M a - m) ^ 2 ≤ q * c ^ 2 := by
    have hdecomp : ∀ x : ℝ, ∑ a, p a * (M a - x) ^ 2 =
        ∑ a, p a * (M a - m) ^ 2 + (m - x) ^ 2 := by
      intro x
      have h0 : ∑ a, p a * (M a - m) = 0 := by
        simp_rw [mul_sub]; rw [sum_sub_distrib, ← sum_mul, hp1, one_mul, hm]; ring
      have : ∀ a, p a * (M a - x) ^ 2 =
          p a * (M a - m) ^ 2 + 2 * (m - x) * (p a * (M a - m)) + (m - x) ^ 2 * p a := by
        intro a; ring
      simp_rw [this]
      rw [sum_add_distrib, sum_add_distrib, ← mul_sum, h0, ← mul_sum, hp1]; ring
    by_cases hex : ∃ b0, b0 ∉ R
    · obtain ⟨b0, hb0⟩ := hex
      have := hdecomp (M b0)
      calc ∑ a, p a * (M a - m) ^ 2 ≤ ∑ a, p a * (M a - M b0) ^ 2 := by
            rw [this]; nlinarith [sq_nonneg (m - M b0)]
        _ ≤ ∑ a, if a ∈ R then p a * c ^ 2 else 0 := by
            refine sum_le_sum fun a _ => ?_
            split_ifs with ha
            · apply mul_le_mul_of_nonneg_left _ (hp0 a)
              have := hgap a b0
              rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
            · rw [hR a b0 ha hb0]; simp
        _ = (∑ a ∈ R, p a) * c ^ 2 := by
            rw [← sum_filter, sum_mul]; simp
        _ ≤ q * c ^ 2 := mul_le_mul_of_nonneg_right hq (sq_nonneg c)
    · push_neg at hex
      have hR1 : ∑ a ∈ R, p a = 1 := by
        rw [← hp1]; congr 1; ext a; simp [hex a]
      calc ∑ a, p a * (M a - m) ^ 2 ≤ ∑ a, p a * c ^ 2 := sum_le_sum fun a _ => by
            apply mul_le_mul_of_nonneg_left _ (hp0 a)
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hY a) 2
        _ = c ^ 2 := by rw [← sum_mul, hp1, one_mul]
        _ ≤ q * c ^ 2 := by
            have : 1 ≤ q := hR1 ▸ hq
            nlinarith [sq_nonneg c]
  have hpt : ∀ a, Real.exp (lam * (M a - m)) ≤
      1 + lam * (M a - m) + (lam * (M a - m)) ^ 2 / (2 * (1 - lam * L)) := by
    intro a
    apply exp_le_one_add_add_sq_div _ _ _ hlamL
    rw [abs_mul, abs_of_nonneg hlam]
    exact mul_le_mul_of_nonneg_left ((hY a).trans hcL) hlam
  calc ∑ a, p a * Real.exp (lam * (M a - m))
      ≤ ∑ a, p a * (1 + lam * (M a - m) + (lam * (M a - m)) ^ 2 / (2 * (1 - lam * L))) :=
        sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hpt a) (hp0 a)
    _ = 1 + lam * ∑ a, p a * (M a - m) +
          lam ^ 2 / (2 * (1 - lam * L)) * ∑ a, p a * (M a - m) ^ 2 := by
        have : ∀ a, p a * (1 + lam * (M a - m) + (lam * (M a - m)) ^ 2 / (2 * (1 - lam * L)))
            = p a + lam * (p a * (M a - m)) +
              lam ^ 2 / (2 * (1 - lam * L)) * (p a * (M a - m) ^ 2) := by
          intro a; ring
        simp_rw [this]
        rw [sum_add_distrib, sum_add_distrib, hp1, ← mul_sum, ← mul_sum]
    _ = 1 + lam ^ 2 / (2 * (1 - lam * L)) * ∑ a, p a * (M a - m) ^ 2 := by
        have h0 : ∑ a, p a * (M a - m) = 0 := by
          simp_rw [mul_sub]; rw [sum_sub_distrib, ← sum_mul, hp1, one_mul, hm]; ring
        rw [h0]; ring
    _ ≤ 1 + lam ^ 2 / (2 * (1 - lam * L)) * (q * c ^ 2) := by
        gcongr
    _ ≤ Real.exp (lam ^ 2 * (q * c ^ 2) / (2 * (1 - lam * L))) := by
        have := Real.add_one_le_exp (lam ^ 2 * (q * c ^ 2) / (2 * (1 - lam * L)))
        rw [div_mul_eq_mul_div] at *
        linarith

section Coord

variable {α : Type*}

/-- Bounded differences on coordinate `i`. -/
def CoordGap {ι : Type*} [DecidableEq ι] (f : (ι → α) → ℝ) (c : ι → ℝ) : Prop :=
  ∀ i ω a b, |f (Function.update ω i a) - f (Function.update ω i b)| ≤ c i

/-- Coordinate `i` only matters through the values in `R i`. -/
def CoordRare {ι : Type*} [DecidableEq ι] (f : (ι → α) → ℝ) (R : ι → Finset α) : Prop :=
  ∀ i ω a b, a ∉ R i → b ∉ R i → f (Function.update ω i a) = f (Function.update ω i b)

theorem CoordGap.tail {n : ℕ} {f : (Fin (n + 1) → α) → ℝ} {c : Fin (n + 1) → ℝ}
    (h : CoordGap f c) (b : α) :
    CoordGap (fun ω => f (Fin.cons b ω)) (fun i => c i.succ) := by
  intro i ω a a'
  have := h i.succ (Fin.cons b ω) a a'
  simpa [← Fin.cons_update] using this

theorem CoordRare.tail {n : ℕ} {f : (Fin (n + 1) → α) → ℝ} {R : Fin (n + 1) → Finset α}
    (h : CoordRare f R) (b : α) :
    CoordRare (fun ω => f (Fin.cons b ω)) (fun i => R i.succ) := by
  intro i ω a a' ha ha'
  have := h i.succ (Fin.cons b ω) a a' ha ha'
  simpa [← Fin.cons_update] using this

theorem CoordGap.neg {ι : Type*} [DecidableEq ι] {f : (ι → α) → ℝ} {c : ι → ℝ}
    (h : CoordGap f c) : CoordGap (fun ω => -f ω) c := by
  intro i ω a b
  have := h i ω a b
  rw [← abs_neg]; convert this using 2; ring

theorem CoordRare.neg {ι : Type*} [DecidableEq ι] {f : (ι → α) → ℝ} {R : ι → Finset α}
    (h : CoordRare f R) : CoordRare (fun ω => -f ω) R := by
  intro i ω a b ha hb
  simp [h i ω a b ha hb]

end Coord

/- ## The recursive (exposure) form of the product expectation -/

section Rec

variable {α : Type*} [Fintype α]

/-- The product expectation computed coordinate by coordinate. -/
def rmean : {n : ℕ} → (Fin n → α → ℝ) → ((Fin n → α) → ℝ) → ℝ
  | 0, _, f => f Fin.elim0
  | _ + 1, P, f => ∑ a, P 0 a * rmean (fun i => P i.succ) (fun ω => f (Fin.cons a ω))

theorem rmean_eq_pE : ∀ {n : ℕ} (P : Fin n → α → ℝ) (f : (Fin n → α) → ℝ),
    rmean P f = pE P f
  | 0, P, f => by
    simp only [rmean, pE, pw, univ_eq_empty, prod_empty, one_mul]
    rw [Fintype.sum_unique]
    congr 1
  | n + 1, P, f => by
    simp only [rmean]
    simp_rw [rmean_eq_pE]
    unfold pE
    rw [← Fintype.sum_equiv (Fin.consEquiv fun _ => α) (fun x => pw P (Fin.cons x.1 x.2) *
      f (Fin.cons x.1 x.2)) _ (fun x => rfl)]
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun a _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun ω _ => ?_
    simp only [pw, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    ring

theorem IsPMF.tail {n : ℕ} {P : Fin (n + 1) → α → ℝ} (hP : IsPMF P) :
    IsPMF (fun i : Fin n => P i.succ) :=
  ⟨fun _ a => hP.1 _ a, fun _ => hP.2 _⟩

/-- Exponential moment bound for the centered function. -/
theorem rmean_mgf_le : ∀ {n : ℕ} (P : Fin n → α → ℝ) (_hP : IsPMF P)
    (f : (Fin n → α) → ℝ) (c q : Fin n → ℝ) (R : Fin n → Finset α) (L lam : ℝ)
    (_hcL : ∀ i, c i ≤ L) (_hf : CoordGap f c) (_hfR : CoordRare f R)
    (_hq : ∀ i, ∑ a ∈ R i, P i a ≤ q i) (_hlam : 0 ≤ lam) (_hlamL : lam * L < 1),
    rmean P (fun ω => Real.exp (lam * (f ω - rmean P f))) ≤
      Real.exp (lam ^ 2 * (∑ i, q i * c i ^ 2) / (2 * (1 - lam * L)))
  | 0, P, _, f, c, q, R, L, lam, _, _, _, _, _, _ => by
    simp [rmean]
  | n + 1, P, hP, f, c, q, R, L, lam, hcL, hf, hfR, hq, hlam, hlamL => by
    set P' : Fin n → α → ℝ := fun i => P i.succ
    set M : α → ℝ := fun b => rmean P' (fun ω => f (Fin.cons b ω)) with hM
    have hmean : rmean P f = ∑ a, P 0 a * M a := rfl
    set K := 2 * (1 - lam * L)
    set V' := ∑ i : Fin n, q i.succ * (c i.succ) ^ 2
    have hstep : ∀ b, rmean P' (fun ω => Real.exp (lam * (f (Fin.cons b ω) -
        rmean P f))) ≤ Real.exp (lam * (M b - rmean P f)) *
          Real.exp (lam ^ 2 * V' / K) := by
      intro b
      have hsplit : (fun ω => Real.exp (lam * (f (Fin.cons b ω) - rmean P f))) =
          fun ω => Real.exp (lam * (M b - rmean P f)) *
            Real.exp (lam * (f (Fin.cons b ω) - M b)) := by
        funext ω
        rw [← Real.exp_add]
        ring_nf
      rw [hsplit, rmean_eq_pE, pE_const_mul, ← rmean_eq_pE]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact rmean_mgf_le P' hP.tail _ (fun i => c i.succ) (fun i => q i.succ)
        (fun i => R i.succ) L lam (fun i => hcL i.succ) (hf.tail b) (hfR.tail b)
        (fun i => hq i.succ) hlam hlamL
    have hgap : ∀ a b, |M a - M b| ≤ c 0 := by
      intro a b
      simp only [hM]
      rw [rmean_eq_pE, rmean_eq_pE, ← pE_sub]
      have hb : ∀ ω, |f (Fin.cons a ω) - f (Fin.cons b ω)| ≤ c 0 := by
        intro ω
        have := hf 0 (Fin.cons a ω) a b
        simpa [Fin.update_cons_zero] using this
      rw [abs_le]
      constructor
      · have := pE_mono hP.tail (f := fun _ => -c 0)
          (g := fun ω => f (Fin.cons a ω) - f (Fin.cons b ω))
          (fun ω => (abs_le.mp (hb ω)).1)
        rwa [pE_const hP.tail] at this
      · have := pE_mono hP.tail (g := fun _ => c 0)
          (f := fun ω => f (Fin.cons a ω) - f (Fin.cons b ω))
          (fun ω => (abs_le.mp (hb ω)).2)
        rwa [pE_const hP.tail] at this
    have hRM : ∀ a b, a ∉ R 0 → b ∉ R 0 → M a = M b := by
      intro a b ha hb
      simp only [hM]
      congr 1; funext ω
      have := hfR 0 (Fin.cons a ω) a b ha hb
      simpa [Fin.update_cons_zero] using this
    calc rmean P (fun ω => Real.exp (lam * (f ω - rmean P f)))
        = ∑ a, P 0 a * rmean P' (fun ω => Real.exp (lam *
            (f (Fin.cons a ω) - rmean P f))) := rfl
      _ ≤ ∑ a, P 0 a * (Real.exp (lam * (M a - rmean P f)) *
            Real.exp (lam ^ 2 * V' / K)) :=
          sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hstep a) (hP.1 0 a)
      _ = (∑ a, P 0 a * Real.exp (lam * (M a - ∑ b, P 0 b * M b))) *
            Real.exp (lam ^ 2 * V' / K) := by
          rw [sum_mul, hmean]; congr 1; funext a; ring
      _ ≤ Real.exp (lam ^ 2 * (q 0 * c 0 ^ 2) / K) * Real.exp (lam ^ 2 * V' / K) := by
          gcongr
          exact coord_exp_bound (P 0) (hP.1 0) (hP.2 0) M (c 0) L lam (q 0) (R 0) hgap hRM
            (hq 0) (hcL 0) hlam hlamL
      _ = _ := by
          rw [← Real.exp_add, Fin.sum_univ_succ]
          congr 1
          simp only [K, V']
          ring

end Rec

/- ## The tail bounds -/

section Tail

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

theorem pE_tail_le_of_lam_fin {n : ℕ} (P : Fin n → α → ℝ) (hP : IsPMF P)
    (f : (Fin n → α) → ℝ) (c q : Fin n → ℝ) (R : Fin n → Finset α) (L lam t : ℝ)
    (hcL : ∀ i, c i ≤ L) (hf : CoordGap f c) (hfR : CoordRare f R)
    (hq : ∀ i, ∑ a ∈ R i, P i a ≤ q i) (hlam : 0 ≤ lam) (hlamL : lam * L < 1) :
    pProb P (fun ω => t ≤ f ω - pE P f) ≤
      Real.exp (-(lam * t) + lam ^ 2 * (∑ i, q i * c i ^ 2) / (2 * (1 - lam * L))) := by
  classical
  have hind : ∀ ω, (if t ≤ f ω - pE P f then (1 : ℝ) else 0) ≤
      Real.exp (-(lam * t)) * Real.exp (lam * (f ω - pE P f)) := by
    intro ω
    rw [← Real.exp_add]
    split_ifs with h
    · apply Real.one_le_exp
      nlinarith
    · exact (Real.exp_pos _).le
  unfold pProb
  calc _ ≤ pE P (fun ω => Real.exp (-(lam * t)) *
        Real.exp (lam * (f ω - pE P f))) := pE_mono hP hind
    _ = Real.exp (-(lam * t)) * pE P (fun ω => Real.exp (lam * (f ω - pE P f))) :=
        pE_const_mul _ _
    _ ≤ Real.exp (-(lam * t)) *
          Real.exp (lam ^ 2 * (∑ i, q i * c i ^ 2) / (2 * (1 - lam * L))) := by
        gcongr
        have := rmean_mgf_le P hP f c q R L lam hcL hf hfR hq hlam hlamL
        simp only [rmean_eq_pE] at this
        exact this
    _ = _ := (Real.exp_add _ _).symm

theorem pE_upper_tail_fin {n : ℕ} (P : Fin n → α → ℝ) (hP : IsPMF P)
    (f : (Fin n → α) → ℝ) (c q : Fin n → ℝ) (R : Fin n → Finset α) (L : ℝ) (hL : 0 < L)
    (hc : ∀ i, 0 ≤ c i ∧ c i ≤ L) (hf : CoordGap f c) (hfR : CoordRare f R)
    (hq : ∀ i, ∑ a ∈ R i, P i a ≤ q i) (t : ℝ) (ht : 0 < t) :
    pProb P (fun ω => t ≤ f ω - pE P f) ≤
      Real.exp (-(t ^ 2 / (2 * ((∑ i, q i * c i ^ 2) + L * t)))) := by
  set V := ∑ i, q i * c i ^ 2 with hVdef
  have hq0 : ∀ i, 0 ≤ q i := fun i => (sum_nonneg fun a _ => hP.1 i a).trans (hq i)
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun i _ => mul_nonneg (hq0 i) (sq_nonneg _)
  have hcL : ∀ i, c i ≤ L := fun i => (hc i).2
  rcases hV0.lt_or_eq with hV | hV
  · have hD : 0 < V + L * t := by positivity
    set lam := t / (V + L * t)
    have hlam : 0 ≤ lam := by positivity
    have hlamL : lam * L < 1 := by
      rw [div_mul_eq_mul_div, div_lt_one hD]; nlinarith
    refine (pE_tail_le_of_lam_fin P hP f c q R L lam t hcL hf hfR hq hlam hlamL).trans
      (le_of_eq (congrArg Real.exp ?_))
    have h1 : 1 - lam * L = V / (V + L * t) := by
      simp only [lam]; field_simp; ring
    rw [h1]
    simp only [lam]
    field_simp
    ring
  · have hlamL : 1 / (2 * L) * L < 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]; linarith
    refine (pE_tail_le_of_lam_fin P hP f c q R L (1 / (2 * L)) t hcL hf hfR hq
      (by positivity) hlamL).trans (le_of_eq (congrArg Real.exp ?_))
    rw [← hVdef, ← hV]
    field_simp
    ring

/-- **Bernstein-type bounded differences, upper tail**, on a product space over any
finite index type. -/
theorem pE_upper_tail (P : ι → α → ℝ) (hP : IsPMF P)
    (f : (ι → α) → ℝ) (c q : ι → ℝ) (R : ι → Finset α) (L : ℝ) (hL : 0 < L)
    (hc : ∀ i, 0 ≤ c i ∧ c i ≤ L) (hf : CoordGap f c) (hfR : CoordRare f R)
    (hq : ∀ i, ∑ a ∈ R i, P i a ≤ q i) (t : ℝ) (ht : 0 < t) :
    pProb P (fun ω => t ≤ f ω - pE P f) ≤
      Real.exp (-(t ^ 2 / (2 * ((∑ i, q i * c i ^ 2) + L * t)))) := by
  set e := Fintype.equivFin ι
  rw [pProb_equiv e, pE_equiv e]
  have hP' : IsPMF (fun j => P (e.symm j)) := ⟨fun j a => hP.1 _ a, fun j => hP.2 _⟩
  have hV : ∑ i, q i * c i ^ 2 = ∑ j, q (e.symm j) * c (e.symm j) ^ 2 :=
    (Fintype.sum_equiv e.symm _ _ (fun j => rfl)).symm
  rw [hV]
  apply pE_upper_tail_fin _ hP' (fun ω' => f (ω' ∘ e)) (fun j => c (e.symm j))
    (fun j => q (e.symm j)) (fun j => R (e.symm j)) L hL (fun j => hc _) _ _
    (fun j => hq _) t ht
  · intro j ω' a b
    have := hf (e.symm j) (ω' ∘ e) a b
    simpa [Function.update_comp_equiv] using this
  · intro j ω' a b ha hb
    have := hfR (e.symm j) (ω' ∘ e) a b ha hb
    simpa [Function.update_comp_equiv] using this

/-- **Bernstein-type bounded differences, lower tail.** -/
theorem pE_lower_tail (P : ι → α → ℝ) (hP : IsPMF P)
    (f : (ι → α) → ℝ) (c q : ι → ℝ) (R : ι → Finset α) (L : ℝ) (hL : 0 < L)
    (hc : ∀ i, 0 ≤ c i ∧ c i ≤ L) (hf : CoordGap f c) (hfR : CoordRare f R)
    (hq : ∀ i, ∑ a ∈ R i, P i a ≤ q i) (t : ℝ) (ht : 0 < t) :
    pProb P (fun ω => t ≤ pE P f - f ω) ≤
      Real.exp (-(t ^ 2 / (2 * ((∑ i, q i * c i ^ 2) + L * t)))) := by
  have h := pE_upper_tail P hP (fun ω => -f ω) c q R L hL hc hf.neg hfR.neg hq t ht
  rw [pE_neg] at h
  convert h using 3
  constructor <;> intro h' <;> linarith

end Tail

end Pseudorandom

end FlattenedPS04

/- PseudorandomLib.Counting -/
section FlattenedPS05
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/- # Counting lemmas for hypergraphs

* `meet A T`: the edges of `A` meeting a vertex set `T`;
* `|meet A T| ≤ ∑_{u ∈ T} deg u` and the Bonferroni lower bound
  `∑_{u ∈ T} deg u ≤ |meet A T| + ∑_{u ≠ w ∈ T} codeg(u, w)`;
* `∑_{w ≠ v} codeg(v, w) = (r - 1) deg v` for `r`-uniform hypergraphs;
* an elementary bound for the difference of two filtered cardinalities.
-/

namespace Pseudorandom

open Finset

variable {V : Type*} [DecidableEq V]

/-- The edges of `A` meeting the vertex set `T`. -/
def meet (A : Finset (Finset V)) (T : Finset V) : Finset (Finset V) :=
  A.filter (fun f => ¬ Disjoint f T)

theorem mem_meet {A : Finset (Finset V)} {T : Finset V} {f : Finset V} :
    f ∈ meet A T ↔ f ∈ A ∧ ∃ u ∈ T, u ∈ f := by
  unfold meet
  rw [mem_filter, Finset.not_disjoint_iff]
  constructor
  · rintro ⟨h1, u, h2, h3⟩; exact ⟨h1, u, h3, h2⟩
  · rintro ⟨h1, u, h2, h3⟩; exact ⟨h1, u, h3, h2⟩

theorem degree_eq_sum (A : Finset (Finset V)) (u : V) :
    degree A u = ∑ f ∈ A, if u ∈ f then 1 else 0 := by
  unfold degree; rw [card_filter]

theorem codegree_eq_sum (A : Finset (Finset V)) (u w : V) :
    codegree A u w = ∑ f ∈ A, if u ∈ f ∧ w ∈ f then 1 else 0 := by
  unfold codegree; rw [card_filter]

theorem sum_degree_eq (A : Finset (Finset V)) (T : Finset V) :
    ∑ u ∈ T, degree A u = ∑ f ∈ A, (T.filter (· ∈ f)).card := by
  simp_rw [degree_eq_sum, card_filter]
  rw [sum_comm]

theorem card_meet_eq (A : Finset (Finset V)) (T : Finset V) :
    (meet A T).card = ∑ f ∈ A, if 0 < (T.filter (· ∈ f)).card then 1 else 0 := by
  unfold meet
  rw [card_filter]
  refine sum_congr rfl fun f _ => ?_
  congr 1
  apply propext
  rw [Finset.not_disjoint_iff, card_pos, filter_nonempty_iff]
  constructor
  · rintro ⟨u, h1, h2⟩; exact ⟨u, h2, h1⟩
  · rintro ⟨u, h1, h2⟩; exact ⟨u, h2, h1⟩

/-- `|meet A T| ≤ ∑_{u ∈ T} deg u`. -/
theorem card_meet_le (A : Finset (Finset V)) (T : Finset V) :
    (meet A T).card ≤ ∑ u ∈ T, degree A u := by
  rw [card_meet_eq, sum_degree_eq]
  refine sum_le_sum fun f _ => ?_
  split_ifs with h
  · exact h
  · exact Nat.zero_le _

theorem sum_codegree_eq (A : Finset (Finset V)) (T : Finset V) :
    ∑ u ∈ T, ∑ w ∈ T.erase u, codegree A u w =
      ∑ f ∈ A, (T.filter (· ∈ f)).card * ((T.filter (· ∈ f)).card - 1) := by
  simp_rw [codegree_eq_sum]
  have h1 : ∀ u ∈ T, ∑ w ∈ T.erase u, ∑ f ∈ A, (if u ∈ f ∧ w ∈ f then 1 else 0) =
      ∑ f ∈ A, ∑ w ∈ T.erase u, (if u ∈ f ∧ w ∈ f then 1 else 0) := fun u _ => sum_comm
  rw [sum_congr rfl h1, sum_comm]
  refine sum_congr rfl fun f _ => ?_
  set S := T.filter (· ∈ f)
  have h2 : ∀ u ∈ T, ∑ w ∈ T.erase u, (if u ∈ f ∧ w ∈ f then 1 else 0) =
      if u ∈ S then (S.erase u).card else 0 := by
    intro u hu
    by_cases huf : u ∈ f
    · have : u ∈ S := mem_filter.mpr ⟨hu, huf⟩
      rw [if_pos this]
      simp only [huf, true_and]
      rw [← card_filter]
      congr 1
      ext w
      simp [S, mem_filter, mem_erase]
      tauto
    · have : u ∉ S := fun h => huf (mem_filter.mp h).2
      rw [if_neg this]
      simp [huf]
  rw [sum_congr rfl h2, ← sum_filter]
  have h3 : T.filter (· ∈ S) = S := by
    ext u; simp only [mem_filter, S]; tauto
  rw [h3]
  have h4 : ∀ u ∈ S, (S.erase u).card = S.card - 1 := fun u hu => card_erase_of_mem hu
  rw [sum_congr rfl h4, sum_const, smul_eq_mul]

/-- Bonferroni: `∑_{u ∈ T} deg u ≤ |meet A T| + ∑_{u ∈ T} ∑_{w ∈ T, w ≠ u} codeg(u, w)`. -/
theorem sum_degree_le (A : Finset (Finset V)) (T : Finset V) :
    ∑ u ∈ T, degree A u ≤ (meet A T).card + ∑ u ∈ T, ∑ w ∈ T.erase u, codegree A u w := by
  rw [sum_codegree_eq, card_meet_eq, sum_degree_eq, ← sum_add_distrib]
  refine sum_le_sum fun f _ => ?_
  set k := (T.filter (· ∈ f)).card
  split_ifs with h
  · rcases k with _ | k
    · omega
    · simp only [Nat.add_sub_cancel]
      nlinarith
  · omega

/-- Two filters of the same finset that agree outside `B` differ in size by at most `|B|`. -/
theorem abs_card_filter_sub_le {β : Type*} [DecidableEq β] (s : Finset β) (p q : β → Prop)
    [DecidablePred p] [DecidablePred q] (B : Finset β)
    (hB : ∀ x ∈ s, x ∉ B → (p x ↔ q x)) :
    |((s.filter p).card : ℝ) - (s.filter q).card| ≤ B.card := by
  have hp := card_filter_add_card_filter_not (s := s.filter p) (fun x => x ∈ B)
  have hq := card_filter_add_card_filter_not (s := s.filter q) (fun x => x ∈ B)
  have heq : (s.filter p).filter (fun x => ¬ x ∈ B) = (s.filter q).filter (fun x => ¬ x ∈ B) := by
    ext x
    simp only [mem_filter]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, (hB x h1 h3).mp h2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, (hB x h1 h3).mpr h2⟩, h3⟩
  have hpB : ((s.filter p).filter (fun x => x ∈ B)).card ≤ B.card :=
    card_le_card fun x hx => (mem_filter.mp hx).2
  have hqB : ((s.filter q).filter (fun x => x ∈ B)).card ≤ B.card :=
    card_le_card fun x hx => (mem_filter.mp hx).2
  rw [heq] at hp
  rw [abs_le]
  constructor
  · have : ((s.filter q).card : ℝ) ≤ (s.filter p).card + B.card := by
      have : (s.filter q).card ≤ (s.filter p).card + B.card := by omega
      exact_mod_cast this
    linarith
  · have : ((s.filter p).card : ℝ) ≤ (s.filter q).card + B.card := by
      have : (s.filter p).card ≤ (s.filter q).card + B.card := by omega
      exact_mod_cast this
    linarith

theorem codegree_le_degree (A : Finset (Finset V)) (u w : V) : codegree A u w ≤ degree A u :=
  card_le_card fun f hf => by
    simp only [mem_filter] at hf ⊢; exact ⟨hf.1, hf.2.1⟩

theorem degree_mono {A B : Finset (Finset V)} (h : A ⊆ B) (v : V) : degree A v ≤ degree B v :=
  card_le_card (filter_subset_filter _ h)

theorem codegree_mono {A B : Finset (Finset V)} (h : A ⊆ B) (u w : V) :
    codegree A u w ≤ codegree B u w :=
  card_le_card (filter_subset_filter _ h)

/-- In an `r`-uniform hypergraph, `∑_{w ≠ v} codeg(v, w) = (r - 1) deg v`. -/
theorem sum_codegree_erase [Fintype V] (A : Finset (Finset V)) (r : ℕ) (hA : IsUniform A r)
    (v : V) : ∑ w ∈ univ.erase v, codegree A v w = (r - 1) * degree A v := by
  simp_rw [codegree_eq_sum]
  rw [sum_comm, degree_eq_sum, mul_sum]
  refine sum_congr rfl fun f hf => ?_
  by_cases hv : v ∈ f
  · simp only [hv, true_and, if_true, mul_one]
    rw [← card_filter]
    have : (univ.erase v).filter (· ∈ f) = f.erase v := by
      ext w; simp [mem_erase]
    rw [this, card_erase_of_mem hv, hA f hf]
  · simp [hv]

end Pseudorandom

end FlattenedPS05

/- PseudorandomLib.NibbleRound -/
section FlattenedPS06
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/- # One round of the (wasteful) Rödl nibble

The state is a set `A` of alive edges. In one round every alive edge `e` is *selected*
independently with probability `1 - e^{-a}`, and every vertex `v` gets an extra independent
*killing coin* with probability `1 - e^{-a (D - deg_A v)}` (this equalises the survival
probabilities of the vertices). A vertex *dies* if it lies in a selected edge or its killing
coin comes up. An edge is *accepted* if it is selected and no other selected alive edge meets
it. The accepted edges form a matching, and the new alive edges are the alive edges all of
whose vertices survive.

All coins are coordinates of one finite product space indexed by `Finset V ⊕ V`.
-/

namespace Pseudorandom.Nibble

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Coin indices: one coin per (potential) edge and one per vertex. -/
abbrev Coin (V : Type*) := Finset V ⊕ V

/-- The probability that a coin comes up `true`. -/
noncomputable def qTrue (A : Finset (Finset V)) (a D : ℝ) : Coin V → ℝ
  | Sum.inl e => if e ∈ A then 1 - Real.exp (-a) else 0
  | Sum.inr v => 1 - Real.exp (-(a * max 0 (D - degree A v)))

/-- The coin distributions of one round. -/
noncomputable def roundP (A : Finset (Finset V)) (a D : ℝ) : Coin V → Bool → ℝ :=
  fun i b => if b then qTrue A a D i else 1 - qTrue A a D i

omit [Fintype V] in
theorem qTrue_mem (A : Finset (Finset V)) {a : ℝ} (ha : 0 ≤ a) (D : ℝ) (i : Coin V) :
    0 ≤ qTrue A a D i ∧ qTrue A a D i ≤ 1 := by
  cases i with
  | inl e =>
    simp only [qTrue]
    split_ifs
    · constructor
      · have : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        linarith
      · linarith [Real.exp_pos (-a)]
    · norm_num
  | inr v =>
    simp only [qTrue]
    constructor
    · have : Real.exp (-(a * max 0 (D - degree A v))) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [le_max_left 0 (D - degree A v)])
      linarith
    · linarith [Real.exp_pos (-(a * max 0 (D - degree A v)))]

omit [Fintype V] in
theorem roundP_isPMF (A : Finset (Finset V)) {a : ℝ} (ha : 0 ≤ a) (D : ℝ) :
    IsPMF (roundP A a D) := by
  refine ⟨fun i b => ?_, fun i => ?_⟩
  · have := qTrue_mem A ha D i
    cases b <;> simp [roundP] <;> linarith
  · simp [roundP]

/- ## The deterministic part of a round -/

/-- A vertex dies if it lies in a selected alive edge or its killing coin comes up. -/
def Dead (A : Finset (Finset V)) (ω : Coin V → Bool) (v : V) : Prop :=
  (∃ f ∈ A, v ∈ f ∧ ω (Sum.inl f) = true) ∨ ω (Sum.inr v) = true

instance (A : Finset (Finset V)) (ω : Coin V → Bool) : DecidablePred (Dead A ω) :=
  fun v => inferInstanceAs (Decidable ((∃ f ∈ A, v ∈ f ∧ ω (Sum.inl f) = true) ∨
    ω (Sum.inr v) = true))

/-- The new alive edges: alive edges all of whose vertices survive. -/
def alive (A : Finset (Finset V)) (ω : Coin V → Bool) : Finset (Finset V) :=
  A.filter (fun e => ∀ v ∈ e, ¬ Dead A ω v)

/-- The accepted edges: selected alive edges meeting no other selected alive edge. -/
def acc (A : Finset (Finset V)) (ω : Coin V → Bool) : Finset (Finset V) :=
  A.filter (fun e => ω (Sum.inl e) = true ∧
    ∀ f ∈ A, f ≠ e → ¬ Disjoint f e → ω (Sum.inl f) = false)

/-- The number of alive edges at `v` whose other vertices survive. -/
def degP (A : Finset (Finset V)) (ω : Coin V → Bool) (v : V) : ℕ :=
  (A.filter (fun e => v ∈ e ∧ ∀ u ∈ e, u ≠ v → ¬ Dead A ω u)).card

theorem alive_subset (A : Finset (Finset V)) (ω : Coin V → Bool) : alive A ω ⊆ A :=
  filter_subset _ _

theorem acc_subset (A : Finset (Finset V)) (ω : Coin V → Bool) : acc A ω ⊆ A :=
  filter_subset _ _

theorem acc_isMatching (A : Finset (Finset V)) (ω : Coin V → Bool) :
    IsMatching (acc A ω) := by
  intro e he f hf hef
  simp only [acc, mem_filter] at he hf
  by_contra hd
  have := he.2.2 f hf.1 (Ne.symm hef) (fun h => hd h.symm)
  rw [hf.2.1] at this
  exact Bool.noConfusion this

theorem disjoint_alive_acc (A : Finset (Finset V)) (ω : Coin V → Bool) :
    ∀ f ∈ alive A ω, ∀ g ∈ acc A ω, Disjoint f g := by
  intro f hf g hg
  simp only [alive, acc, mem_filter] at hf hg
  rw [Finset.disjoint_left]
  intro v hvf hvg
  exact hf.2 v hvf (Or.inl ⟨g, hg.1, hvg, hg.2.1⟩)

theorem degree_alive_le_degP (A : Finset (Finset V)) (ω : Coin V → Bool) (v : V) :
    degree (alive A ω) v ≤ degP A ω v := by
  unfold degree degP alive
  apply card_le_card
  intro e he
  simp only [mem_filter] at he ⊢
  exact ⟨he.1.1, he.2, fun u hu _ => he.1.2 u hu⟩

/- ## Exact probabilities -/

section Prob

variable (A : Finset (Finset V)) {a : ℝ} (D : ℝ)

omit [Fintype V] in
theorem roundP_inl_true {f : Finset V} (hf : f ∈ A) :
    roundP A a D (Sum.inl f) true = 1 - Real.exp (-a) := by
  simp [roundP, qTrue, hf]

omit [Fintype V] in
theorem roundP_inl_false {f : Finset V} (hf : f ∈ A) :
    roundP A a D (Sum.inl f) false = Real.exp (-a) := by
  simp [roundP, qTrue, hf]

omit [Fintype V] in
theorem roundP_inr_false (v : V) :
    roundP A a D (Sum.inr v) false = Real.exp (-(a * max 0 (D - degree A v))) := by
  simp [roundP, qTrue]

omit [Fintype V] in
theorem notDead_iff (T : Finset V) (ω : Coin V → Bool) :
    (∀ u ∈ T, ¬ Dead A ω u) ↔ ∀ i ∈ (meet A T).disjSum T, ω i = (fun _ => false) i := by
  constructor
  · intro h i hi
    cases i with
    | inl f =>
      rw [inl_mem_disjSum, mem_meet] at hi
      obtain ⟨hfA, u, huT, huf⟩ := hi
      by_contra hc
      exact h u huT (Or.inl ⟨f, hfA, huf, by simpa using hc⟩)
    | inr u =>
      rw [inr_mem_disjSum] at hi
      by_contra hc
      exact h u hi (Or.inr (by simpa using hc))
  · intro h u huT hd
    rcases hd with ⟨f, hfA, huf, hω⟩ | hω
    · have := h (Sum.inl f) (inl_mem_disjSum.mpr (mem_meet.mpr ⟨hfA, u, huT, huf⟩))
      rw [hω] at this; exact Bool.noConfusion this
    · have := h (Sum.inr u) (inr_mem_disjSum.mpr huT)
      rw [hω] at this; exact Bool.noConfusion this

/-- The exact probability that every vertex of `T` survives. -/
theorem prob_notDead (ha : 0 ≤ a) (T : Finset V) :
    pProb (roundP A a D) (fun ω => ∀ u ∈ T, ¬ Dead A ω u) =
      Real.exp (-a) ^ (meet A T).card *
        ∏ u ∈ T, Real.exp (-(a * max 0 (D - degree A u))) := by
  rw [pProb_congr (notDead_iff A T), pProb_cylinder (roundP_isPMF A ha D), prod_disjSum]
  congr 1
  · rw [prod_congr rfl (fun f hf => roundP_inl_false A D (mem_meet.mp hf).1), prod_const]
  · exact prod_congr rfl (fun u _ => roundP_inr_false A D u)

/-- The survival probability as a single exponential. -/
theorem prob_notDead_eq_exp (ha : 0 ≤ a) (T : Finset V) (hdeg : ∀ u ∈ T, (degree A u : ℝ) ≤ D) :
    pProb (roundP A a D) (fun ω => ∀ u ∈ T, ¬ Dead A ω u) =
      Real.exp (-(a * ((meet A T).card + ∑ u ∈ T, (D - degree A u)))) := by
  rw [prob_notDead A D ha, ← Real.exp_nat_mul, ← Real.exp_sum, ← Real.exp_add]
  congr 1
  have : ∀ u ∈ T, max 0 (D - degree A u) = D - degree A u := fun u hu =>
    max_eq_right (by linarith [hdeg u hu])
  rw [sum_congr rfl (fun u hu => by rw [this u hu])]
  rw [mul_add, mul_sum, sum_neg_distrib]
  ring

/-- Lower bound for the survival probability: `≥ e^{-a |T| D}`. -/
theorem prob_notDead_ge (ha : 0 ≤ a) (T : Finset V) (hdeg : ∀ u ∈ T, (degree A u : ℝ) ≤ D) :
    Real.exp (-(a * (T.card * D))) ≤ pProb (roundP A a D) (fun ω => ∀ u ∈ T, ¬ Dead A ω u) := by
  rw [prob_notDead_eq_exp A D ha T hdeg]
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  apply mul_le_mul_of_nonneg_left _ ha
  have h1 : ((meet A T).card : ℝ) ≤ ∑ u ∈ T, (degree A u : ℝ) := by
    exact_mod_cast card_meet_le A T
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
  linarith

/-- Upper bound for the survival probability, using codegrees: `≤ e^{-a (|T| D - |T|² K)}`. -/
theorem prob_notDead_le (ha : 0 ≤ a) (T : Finset V) (hdeg : ∀ u ∈ T, (degree A u : ℝ) ≤ D)
    (K : ℝ) (hK : 0 ≤ K) (hcod : ∀ u ∈ T, ∀ w ∈ T, u ≠ w → (codegree A u w : ℝ) ≤ K) :
    pProb (roundP A a D) (fun ω => ∀ u ∈ T, ¬ Dead A ω u) ≤
      Real.exp (-(a * (T.card * D - T.card ^ 2 * K))) := by
  rw [prob_notDead_eq_exp A D ha T hdeg]
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  apply mul_le_mul_of_nonneg_left _ ha
  have h1 : (∑ u ∈ T, (degree A u : ℝ)) ≤ (meet A T).card +
      ∑ u ∈ T, ∑ w ∈ T.erase u, (codegree A u w : ℝ) := by
    exact_mod_cast sum_degree_le A T
  have h2 : ∑ u ∈ T, ∑ w ∈ T.erase u, (codegree A u w : ℝ) ≤ T.card ^ 2 * K := by
    calc ∑ u ∈ T, ∑ w ∈ T.erase u, (codegree A u w : ℝ)
        ≤ ∑ u ∈ T, ∑ w ∈ T.erase u, K := sum_le_sum fun u hu => sum_le_sum fun w hw =>
          hcod u hu w (mem_of_mem_erase hw) (ne_of_mem_erase hw).symm
      _ = T.card * ((T.card - 1 : ℕ) : ℝ) * K := by
          rw [sum_congr rfl (fun u hu => by rw [sum_const, card_erase_of_mem hu]), sum_const]
          simp only [nsmul_eq_mul]; ring
      _ ≤ T.card ^ 2 * K := by
          have : ((T.card - 1 : ℕ) : ℝ) ≤ T.card := by exact_mod_cast Nat.sub_le _ _
          rw [sq]; gcongr
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
  linarith

theorem alive_iff (ω : Coin V → Bool) {e : Finset V} (he : e ∈ A) :
    e ∈ alive A ω ↔ ∀ u ∈ e, ¬ Dead A ω u := by
  simp [alive, he]

/-- Lower bound on the probability that an alive edge stays alive. -/
theorem prob_alive_ge (ha : 0 ≤ a) {e : Finset V} (he : e ∈ A) (r : ℕ) (her : e.card = r)
    (hdeg : ∀ u ∈ e, (degree A u : ℝ) ≤ D) :
    Real.exp (-(a * (r * D))) ≤ pProb (roundP A a D) (fun ω => e ∈ alive A ω) := by
  rw [pProb_congr (fun ω => alive_iff A ω he), ← her]
  exact prob_notDead_ge A D ha e hdeg

theorem acc_iff (ω : Coin V → Bool) {e : Finset V} (he : e ∈ A) (hne : e.Nonempty) :
    e ∈ acc A ω ↔ ∀ i ∈ (meet A e).disjSum (∅ : Finset V),
      ω i = (fun j => decide (j = Sum.inl e)) i := by
  have hem : e ∈ meet A e := mem_meet.mpr ⟨he, hne.choose, hne.choose_spec, hne.choose_spec⟩
  simp only [acc, mem_filter, he, true_and]
  constructor
  · rintro ⟨h1, h2⟩ i hi
    cases i with
    | inl f =>
      rw [inl_mem_disjSum] at hi
      by_cases hfe : f = e
      · subst hfe; simpa using h1
      · have hfA := (mem_meet.mp hi).1
        have hnd : ¬ Disjoint f e := by
          obtain ⟨_, u, hu1, hu2⟩ := mem_meet.mp hi
          rw [Finset.not_disjoint_iff]; exact ⟨u, hu2, hu1⟩
        simp [h2 f hfA hfe hnd, hfe]
    | inr u => simp at hi
  · intro h
    refine ⟨by simpa using h (Sum.inl e) (inl_mem_disjSum.mpr hem), fun f hfA hfe hnd => ?_⟩
    have hfm : f ∈ meet A e := by
      obtain ⟨u, hu1, hu2⟩ := Finset.not_disjoint_iff.mp hnd
      exact mem_meet.mpr ⟨hfA, u, hu2, hu1⟩
    simpa [hfe] using h (Sum.inl f) (inl_mem_disjSum.mpr hfm)

/-- The exact acceptance probability. -/
theorem prob_acc (ha : 0 ≤ a) {e : Finset V} (he : e ∈ A) (hne : e.Nonempty) :
    pProb (roundP A a D) (fun ω => e ∈ acc A ω) =
      (1 - Real.exp (-a)) * Real.exp (-a) ^ ((meet A e).card - 1) := by
  have hem : e ∈ meet A e := mem_meet.mpr ⟨he, hne.choose, hne.choose_spec, hne.choose_spec⟩
  rw [pProb_congr (fun ω => acc_iff A ω he hne), pProb_cylinder (roundP_isPMF A ha D),
    prod_disjSum]
  simp only [prod_empty, mul_one]
  rw [← mul_prod_erase _ _ hem]
  simp only [decide_true]
  rw [roundP_inl_true A D he]
  congr 1
  rw [prod_congr rfl (g := fun _ => Real.exp (-a)) (fun f hf => by
      have h1 : decide (Sum.inl f = (Sum.inl e : Coin V)) = false := by
        simpa using ne_of_mem_erase hf
      rw [h1]; exact roundP_inl_false A D (mem_meet.mp (mem_of_mem_erase hf)).1),
    prod_const, card_erase_of_mem hem]

/-- Lower bound on the acceptance probability: `≥ (1 - e^{-a}) e^{-a r D}`. -/
theorem prob_acc_ge (ha : 0 ≤ a) {e : Finset V} (he : e ∈ A) (hne : e.Nonempty) (r : ℕ)
    (her : e.card = r) (hdeg : ∀ u ∈ e, (degree A u : ℝ) ≤ D) :
    (1 - Real.exp (-a)) * Real.exp (-(a * (r * D))) ≤
      pProb (roundP A a D) (fun ω => e ∈ acc A ω) := by
  rw [prob_acc A D ha he hne]
  apply mul_le_mul_of_nonneg_left _ (by linarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr ha)])
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have h1 : (((meet A e).card - 1 : ℕ) : ℝ) ≤ r * D := by
    have h2 : (((meet A e).card - 1 : ℕ) : ℝ) ≤ (meet A e).card := by
      exact_mod_cast Nat.sub_le _ _
    have h3 : ((meet A e).card : ℝ) ≤ ∑ u ∈ e, (degree A u : ℝ) := by
      exact_mod_cast card_meet_le A e
    have h4 : ∑ u ∈ e, (degree A u : ℝ) ≤ ∑ u ∈ e, D := sum_le_sum hdeg
    rw [sum_const, her, nsmul_eq_mul] at h4
    linarith
  nlinarith

end Prob

end Pseudorandom.Nibble

end FlattenedPS06

/- PseudorandomLib.NibbleDegree -/
section FlattenedPS07
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/- # Degrees after one nibble round

`degP A ω v` counts the alive edges at `v` whose other vertices survive the round; it
dominates the new degree of `v`. We compute its expectation, bound it using codegrees, and
prove a Bernstein-type upper tail for it.
-/

namespace Pseudorandom.Nibble

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

section Expectation

variable (A : Finset (Finset V)) {a : ℝ} (D : ℝ)

theorem degP_eq_sum (ω : Coin V → Bool) (v : V) :
    (degP A ω v : ℝ) = ∑ e ∈ A.filter (v ∈ ·),
      (if ∀ u ∈ e.erase v, ¬ Dead A ω u then (1 : ℝ) else 0) := by
  unfold degP
  have : A.filter (fun e => v ∈ e ∧ ∀ u ∈ e, u ≠ v → ¬ Dead A ω u) =
      (A.filter (v ∈ ·)).filter (fun e => ∀ u ∈ e.erase v, ¬ Dead A ω u) := by
    rw [filter_filter]
    congr 1
    ext e
    simp only [mem_erase]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun u ⟨hu1, hu2⟩ => h2 u hu2 hu1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun u hu1 hu2 => h2 u ⟨hu2, hu1⟩⟩
  rw [this, card_filter]
  push_cast
  rfl

theorem pE_degP (v : V) :
    pE (roundP A a D) (fun ω => (degP A ω v : ℝ)) =
      ∑ e ∈ A.filter (v ∈ ·), pProb (roundP A a D) (fun ω => ∀ u ∈ e.erase v, ¬ Dead A ω u) := by
  simp_rw [degP_eq_sum]
  rw [pE_sum]
  refine sum_congr rfl fun e _ => ?_
  exact (pProb_eq_pE _ _ (fun ω h => if_pos h) (fun ω h => if_neg h)).symm

/-- `E[degP v] ≤ D e^{-a((r-1) D - (r-1)² K)}`. -/
theorem pE_degP_le (ha : 0 ≤ a) (r : ℕ) (huni : IsUniform A r)
    (hdeg : ∀ u, (degree A u : ℝ) ≤ D) (K : ℝ) (hK : 0 ≤ K)
    (hcod : ∀ u w, u ≠ w → (codegree A u w : ℝ) ≤ K) (v : V) :
    pE (roundP A a D) (fun ω => (degP A ω v : ℝ)) ≤
      D * Real.exp (-(a * (((r - 1 : ℕ) : ℝ) * D - ((r - 1 : ℕ) : ℝ) ^ 2 * K))) := by
  rw [pE_degP]
  have hterm : ∀ e ∈ A.filter (v ∈ ·),
      pProb (roundP A a D) (fun ω => ∀ u ∈ e.erase v, ¬ Dead A ω u) ≤
        Real.exp (-(a * (((r - 1 : ℕ) : ℝ) * D - ((r - 1 : ℕ) : ℝ) ^ 2 * K))) := by
    intro e he
    rw [mem_filter] at he
    have hc : (e.erase v).card = r - 1 := by rw [card_erase_of_mem he.2, huni e he.1]
    have := prob_notDead_le A D ha (e.erase v) (fun u _ => hdeg u) K hK
      (fun u _ w _ huw => hcod u w huw)
    rwa [hc] at this
  calc _ ≤ ∑ e ∈ A.filter (v ∈ ·),
        Real.exp (-(a * (((r - 1 : ℕ) : ℝ) * D - ((r - 1 : ℕ) : ℝ) ^ 2 * K))) :=
        sum_le_sum hterm
    _ = (degree A v : ℝ) *
        Real.exp (-(a * (((r - 1 : ℕ) : ℝ) * D - ((r - 1 : ℕ) : ℝ) ^ 2 * K))) := by
        rw [sum_const, nsmul_eq_mul]; rfl
    _ ≤ _ := mul_le_mul_of_nonneg_right (hdeg v) (Real.exp_pos _).le

end Expectation

/- ## Bounded differences for `degP` -/

section Gap

omit [Fintype V] in
theorem dead_update_inl (A : Finset (Finset V)) (ω : Coin V → Bool) (g : Finset V) (b : Bool)
    (u : V) (h : g ∉ A ∨ u ∉ g) :
    Dead A (Function.update ω (Sum.inl g) b) u ↔ Dead A ω u := by
  unfold Dead
  have h2 : Function.update ω (Sum.inl g) b (Sum.inr u) = ω (Sum.inr u) :=
    Function.update_of_ne (by simp) _ _
  rw [h2]
  constructor
  · rintro (⟨f, hf, huf, hω⟩ | h3)
    · have hfg : f ≠ g := by rintro rfl; rcases h with h | h <;> contradiction
      rw [Function.update_of_ne (by simpa using hfg)] at hω
      exact Or.inl ⟨f, hf, huf, hω⟩
    · exact Or.inr h3
  · rintro (⟨f, hf, huf, hω⟩ | h3)
    · have hfg : f ≠ g := by rintro rfl; rcases h with h | h <;> contradiction
      refine Or.inl ⟨f, hf, huf, ?_⟩
      rw [Function.update_of_ne (by simpa using hfg)]; exact hω
    · exact Or.inr h3

omit [Fintype V] in
theorem dead_update_inr (A : Finset (Finset V)) (ω : Coin V → Bool) (w : V) (b : Bool)
    (u : V) (h : u ≠ w) :
    Dead A (Function.update ω (Sum.inr w) b) u ↔ Dead A ω u := by
  unfold Dead
  have h2 : Function.update ω (Sum.inr w) b (Sum.inr u) = ω (Sum.inr u) :=
    Function.update_of_ne (by simpa using h) _ _
  have h3 : ∀ f : Finset V, Function.update ω (Sum.inr w) b (Sum.inl f) = ω (Sum.inl f) :=
    fun f => Function.update_of_ne (by simp) _ _
  simp only [h2, h3]

omit [Fintype V] [DecidableEq V] in
theorem degP_pred_congr (A : Finset (Finset V)) (ω₁ ω₂ : Coin V → Bool) (v : V) (e : Finset V)
    (h : v ∈ e → ∀ u ∈ e, u ≠ v → (Dead A ω₁ u ↔ Dead A ω₂ u)) :
    (v ∈ e ∧ ∀ u ∈ e, u ≠ v → ¬ Dead A ω₁ u) ↔ (v ∈ e ∧ ∀ u ∈ e, u ≠ v → ¬ Dead A ω₂ u) := by
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun u hu huv hd => h2 u hu huv ((h h1 u hu huv).mpr hd)⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun u hu huv hd => h2 u hu huv ((h h1 u hu huv).mp hd)⟩

/-- The sensitivity of `degP v` to each coin. -/
noncomputable def cDeg (A : Finset (Finset V)) (v : V) : Coin V → ℝ
  | Sum.inl g => if g ∈ A then
      ((A.filter (fun e => v ∈ e ∧ ∃ u ∈ e, u ≠ v ∧ u ∈ g)).card : ℝ) else 0
  | Sum.inr w => if w = v then 0 else (codegree A v w : ℝ)

theorem degP_coordGap (A : Finset (Finset V)) (v : V) :
    CoordGap (fun ω => (degP A ω v : ℝ)) (cDeg A v) := by
  intro i ω b b'
  unfold degP
  cases i with
  | inl g =>
    by_cases hg : g ∈ A
    · simp only [cDeg, hg, if_true]
      apply abs_card_filter_sub_le
      intro e heA heB
      apply degP_pred_congr
      intro hve u hu huv
      have hug : u ∉ g := fun hug => heB (mem_filter.mpr ⟨heA, hve, u, hu, huv, hug⟩)
      rw [dead_update_inl A ω g b u (Or.inr hug), dead_update_inl A ω g b' u (Or.inr hug)]
    · simp only [cDeg, hg, if_false]
      have := abs_card_filter_sub_le A _ _ (∅ : Finset (Finset V))
        (fun e _ _ => degP_pred_congr A (Function.update ω (Sum.inl g) b)
          (Function.update ω (Sum.inl g) b') v e (fun _ u _ _ => by
            rw [dead_update_inl A ω g b u (Or.inl hg), dead_update_inl A ω g b' u (Or.inl hg)]))
      simpa using this
  | inr w =>
    by_cases hw : w = v
    · subst hw
      simp only [cDeg, if_true]
      have := abs_card_filter_sub_le A _ _ (∅ : Finset (Finset V))
        (fun e _ _ => degP_pred_congr A (Function.update ω (Sum.inr w) b)
          (Function.update ω (Sum.inr w) b') w e (fun _ u _ huv => by
            rw [dead_update_inr A ω w b u huv, dead_update_inr A ω w b' u huv]))
      simpa using this
    · simp only [cDeg, hw, if_false]
      unfold codegree
      apply abs_card_filter_sub_le
      intro e heA heB
      apply degP_pred_congr
      intro hve u hu huv
      have huw : u ≠ w := by
        rintro rfl
        exact heB (mem_filter.mpr ⟨heA, hve, hu⟩)
      rw [dead_update_inr A ω w b u huw, dead_update_inr A ω w b' u huw]

end Gap

/- ## The upper tail of `degP` -/

section Tail

variable (A : Finset (Finset V)) {a : ℝ} (D : ℝ)

omit [Fintype V] in
theorem cDeg_nonneg (v : V) (i : Coin V) : 0 ≤ cDeg A v i := by
  cases i <;> simp only [cDeg] <;> split_ifs <;> positivity

omit [Fintype V] in
theorem cDeg_le (r : ℕ) (huni : IsUniform A r) (hr : 1 ≤ r) (K : ℝ) (hK : 0 ≤ K)
    (hcod : ∀ u w, u ≠ w → (codegree A u w : ℝ) ≤ K) (v : V) (i : Coin V) :
    cDeg A v i ≤ r * K := by
  cases i with
  | inl g =>
    simp only [cDeg]
    split_ifs with hg
    · have hsub : A.filter (fun e => v ∈ e ∧ ∃ u ∈ e, u ≠ v ∧ u ∈ g) ⊆
          (g.erase v).biUnion (fun u => A.filter (fun e => v ∈ e ∧ u ∈ e)) := by
        intro e he
        simp only [mem_filter] at he
        obtain ⟨heA, hve, u, hue, huv, hug⟩ := he
        exact mem_biUnion.mpr ⟨u, mem_erase.mpr ⟨huv, hug⟩, mem_filter.mpr ⟨heA, hve, hue⟩⟩
      have h1 := (card_le_card hsub).trans card_biUnion_le
      have h2 : ((A.filter (fun e => v ∈ e ∧ ∃ u ∈ e, u ≠ v ∧ u ∈ g)).card : ℝ) ≤
          ∑ u ∈ g.erase v, (codegree A v u : ℝ) := by
        unfold codegree; exact_mod_cast h1
      have h3 : ∑ u ∈ g.erase v, (codegree A v u : ℝ) ≤ ∑ u ∈ g.erase v, K :=
        sum_le_sum fun u hu => hcod v u (ne_of_mem_erase hu).symm
      have h4 : ((g.erase v).card : ℝ) ≤ r := by
        have := card_erase_le (s := g) (a := v)
        rw [huni g hg] at this
        exact_mod_cast this
      rw [sum_const, nsmul_eq_mul] at h3
      nlinarith
    · have : (0 : ℝ) ≤ r := by positivity
      positivity
  | inr w =>
    simp only [cDeg]
    split_ifs with hw
    · positivity
    · have : (1 : ℝ) ≤ r := by exact_mod_cast hr
      have := hcod v w (Ne.symm hw)
      nlinarith

omit [Fintype V] in
theorem sum_card_filter_meet_le (r : ℕ) (huni : IsUniform A r)
    (hdeg : ∀ u, (degree A u : ℝ) ≤ D) (v : V) :
    ∑ g ∈ A, ((A.filter (fun e => v ∈ e ∧ ∃ u ∈ e, u ≠ v ∧ u ∈ g)).card : ℝ) ≤ r * D * D := by
  have hswap : ∑ g ∈ A, ((A.filter (fun e => v ∈ e ∧ ∃ u ∈ e, u ≠ v ∧ u ∈ g)).card : ℝ) =
      ∑ e ∈ A, ((A.filter (fun g => v ∈ e ∧ ∃ u ∈ e, u ≠ v ∧ u ∈ g)).card : ℝ) := by
    simp_rw [card_filter]
    push_cast
    exact sum_comm
  rw [hswap]
  have hterm : ∀ e ∈ A, ((A.filter (fun g => v ∈ e ∧ ∃ u ∈ e, u ≠ v ∧ u ∈ g)).card : ℝ) ≤
      if v ∈ e then r * D else 0 := by
    intro e he
    split_ifs with hve
    · have hsub : A.filter (fun g => v ∈ e ∧ ∃ u ∈ e, u ≠ v ∧ u ∈ g) ⊆ meet A (e.erase v) := by
        intro g hg
        simp only [mem_filter] at hg
        obtain ⟨hgA, _, u, hue, huv, hug⟩ := hg
        exact mem_meet.mpr ⟨hgA, u, mem_erase.mpr ⟨huv, hue⟩, hug⟩
      have h1 : ((A.filter (fun g => v ∈ e ∧ ∃ u ∈ e, u ≠ v ∧ u ∈ g)).card : ℝ) ≤
          ∑ u ∈ e.erase v, (degree A u : ℝ) := by
        exact_mod_cast (card_le_card hsub).trans (card_meet_le A _)
      have h2 : ∑ u ∈ e.erase v, (degree A u : ℝ) ≤ ∑ u ∈ e.erase v, D :=
        sum_le_sum fun u _ => hdeg u
      have h3 : ((e.erase v).card : ℝ) ≤ r := by
        have := card_erase_le (s := e) (a := v)
        rw [huni e he] at this
        exact_mod_cast this
      have hD : 0 ≤ D := (Nat.cast_nonneg _).trans (hdeg v)
      rw [sum_const, nsmul_eq_mul] at h2
      nlinarith
    · have : A.filter (fun g => v ∈ e ∧ ∃ u ∈ e, u ≠ v ∧ u ∈ g) = ∅ := by
        ext g; simp [hve]
      simp [this]
  calc _ ≤ ∑ e ∈ A, (if v ∈ e then r * D else 0) := sum_le_sum hterm
    _ = (degree A v : ℝ) * (r * D) := by
        rw [← sum_filter, sum_const, nsmul_eq_mul]; rfl
    _ ≤ D * (r * D) := by
        have hD : 0 ≤ D := (Nat.cast_nonneg _).trans (hdeg v)
        exact mul_le_mul_of_nonneg_right (hdeg v) (by positivity)
    _ = r * D * D := by ring

theorem sum_q_cDeg_sq_le (ha : 0 ≤ a) (hD : 0 ≤ D) (r : ℕ) (huni : IsUniform A r) (hr : 1 ≤ r)
    (hdeg : ∀ u, (degree A u : ℝ) ≤ D) (K : ℝ) (hK : 0 ≤ K)
    (hcod : ∀ u w, u ≠ w → (codegree A u w : ℝ) ≤ K) (v : V) :
    ∑ i, qTrue A a D i * cDeg A v i ^ 2 ≤ 2 * a * r ^ 2 * K * D ^ 2 := by
  have hcle := cDeg_le A r huni hr K hK hcod v
  have hc0 := cDeg_nonneg A v
  rw [Fintype.sum_sum_type]
  -- edge coins
  have h1 : ∑ g : Finset V, qTrue A a D (Sum.inl g) * cDeg A v (Sum.inl g) ^ 2 ≤
      a * (r * K) * (r * D * D) := by
    have hpt : ∀ g : Finset V, qTrue A a D (Sum.inl g) * cDeg A v (Sum.inl g) ^ 2 ≤
        a * (r * K) * cDeg A v (Sum.inl g) := by
      intro g
      have hq : qTrue A a D (Sum.inl g) ≤ a ∨ cDeg A v (Sum.inl g) = 0 := by
        by_cases hg : g ∈ A
        · left; simp only [qTrue, hg, if_true]; linarith [Real.one_sub_le_exp_neg a]
        · right; simp [cDeg, hg]
      have hq0 := (qTrue_mem A ha D (Sum.inl g)).1
      rcases hq with hq | hq
      · have := hcle (Sum.inl g)
        have := hc0 (Sum.inl g)
        calc _ = qTrue A a D (Sum.inl g) * cDeg A v (Sum.inl g) * cDeg A v (Sum.inl g) := by
              ring
          _ ≤ a * cDeg A v (Sum.inl g) * (r * K) := by gcongr
          _ = _ := by ring
      · rw [hq]; simp
    have hsum : ∑ g : Finset V, cDeg A v (Sum.inl g) ≤ r * D * D := by
      have : ∑ g : Finset V, cDeg A v (Sum.inl g) =
          ∑ g ∈ A, ((A.filter (fun e => v ∈ e ∧ ∃ u ∈ e, u ≠ v ∧ u ∈ g)).card : ℝ) := by
        simp only [cDeg]
        rw [← sum_filter]
        simp
      rw [this]
      exact sum_card_filter_meet_le A D r huni hdeg v
    calc _ ≤ ∑ g : Finset V, a * (r * K) * cDeg A v (Sum.inl g) := sum_le_sum fun g _ => hpt g
      _ = a * (r * K) * ∑ g : Finset V, cDeg A v (Sum.inl g) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)
  -- vertex coins
  have h2 : ∑ w : V, qTrue A a D (Sum.inr w) * cDeg A v (Sum.inr w) ^ 2 ≤
      (a * D) * (r * K) * (r * D) := by
    have hpt : ∀ w : V, qTrue A a D (Sum.inr w) * cDeg A v (Sum.inr w) ^ 2 ≤
        (a * D) * (r * K) * cDeg A v (Sum.inr w) := by
      intro w
      have hq : qTrue A a D (Sum.inr w) ≤ a * D := by
        simp only [qTrue]
        have h3 := Real.one_sub_le_exp_neg (a * max 0 (D - degree A w))
        have h4 : max 0 (D - degree A w) ≤ D := max_le hD (by linarith [Nat.cast_nonneg (α := ℝ) (degree A w)])
        have h5 : a * max 0 (D - degree A w) ≤ a * D := mul_le_mul_of_nonneg_left h4 ha
        linarith
      have hq0 := (qTrue_mem A ha D (Sum.inr w)).1
      have := hcle (Sum.inr w)
      have := hc0 (Sum.inr w)
      calc _ = qTrue A a D (Sum.inr w) * cDeg A v (Sum.inr w) * cDeg A v (Sum.inr w) := by ring
        _ ≤ (a * D) * cDeg A v (Sum.inr w) * (r * K) := by gcongr
        _ = _ := by ring
    have hsum : ∑ w : V, cDeg A v (Sum.inr w) ≤ r * D := by
      have : ∑ w : V, cDeg A v (Sum.inr w) = ∑ w ∈ univ.erase v, (codegree A v w : ℝ) := by
        rw [← add_sum_erase _ _ (mem_univ v)]
        simp only [cDeg, if_true, zero_add]
        refine sum_congr rfl fun w hw => ?_
        rw [if_neg (ne_of_mem_erase hw)]
      rw [this]
      have h3 := sum_codegree_erase A r huni v
      have h4 : ∑ w ∈ univ.erase v, (codegree A v w : ℝ) = ((r - 1 : ℕ) : ℝ) * degree A v := by
        exact_mod_cast h3
      rw [h4]
      have h5 : ((r - 1 : ℕ) : ℝ) ≤ r := by exact_mod_cast Nat.sub_le r 1
      have := hdeg v
      have : (0 : ℝ) ≤ degree A v := Nat.cast_nonneg _
      nlinarith
    calc _ ≤ ∑ w : V, (a * D) * (r * K) * cDeg A v (Sum.inr w) := sum_le_sum fun w _ => hpt w
      _ = (a * D) * (r * K) * ∑ w : V, cDeg A v (Sum.inr w) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)
  calc _ ≤ a * (r * K) * (r * D * D) + (a * D) * (r * K) * (r * D) := add_le_add h1 h2
    _ = 2 * a * r ^ 2 * K * D ^ 2 := by ring

/-- **Upper tail of `degP`**:
`P(degP v ≥ E[degP v] + λ) ≤ exp(-λ² / (2 (2 a r² K D² + r K λ)))`. -/
theorem degP_tail (ha : 0 ≤ a) (hD : 0 ≤ D) (r : ℕ) (hr : 1 ≤ r) (huni : IsUniform A r)
    (hdeg : ∀ u, (degree A u : ℝ) ≤ D) (K : ℝ) (hK : 0 < K)
    (hcod : ∀ u w, u ≠ w → (codegree A u w : ℝ) ≤ K) (v : V) (lam : ℝ) (hlam : 0 < lam) :
    pProb (roundP A a D) (fun ω => lam ≤ (degP A ω v : ℝ) -
        pE (roundP A a D) (fun ω => (degP A ω v : ℝ))) ≤
      Real.exp (-(lam ^ 2 / (2 * (2 * a * r ^ 2 * K * D ^ 2 + r * K * lam)))) := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have h := pE_upper_tail (roundP A a D) (roundP_isPMF A ha D) (fun ω => (degP A ω v : ℝ))
    (cDeg A v) (qTrue A a D) (fun _ => {true}) (r * K) (by positivity)
    (fun i => ⟨cDeg_nonneg A v i, cDeg_le A r huni hr K hK.le hcod v i⟩) (degP_coordGap A v)
    (by
      intro i ω b b' hb hb'
      simp only [mem_singleton] at hb hb'
      rw [Bool.eq_false_iff.mpr hb, Bool.eq_false_iff.mpr hb'])
    (fun i => by simp [roundP]) lam hlam
  refine h.trans (Real.exp_le_exp.mpr (neg_le_neg ?_))
  have hV := sum_q_cDeg_sq_le A D ha hD r huni hr hdeg K hK.le hcod v
  have hV0 : 0 ≤ ∑ i, qTrue A a D i * cDeg A v i ^ 2 :=
    sum_nonneg fun i _ => mul_nonneg (qTrue_mem A ha D i).1 (sq_nonneg _)
  apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
  nlinarith

end Tail

end Pseudorandom.Nibble

end FlattenedPS07

/- PseudorandomLib.NibbleIterate -/
section FlattenedPS08
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/- # Iterating the nibble

We first summarise one round on a *good* state (all degrees at most `D`): an alive edge is
accepted with probability at least `(1 - e^{-a}) e^{-a r D}`, and it stays alive while all new
degrees stay below `D'` with probability at least `e^{-a r D} - β`.

Then we run the rounds one after the other. The state of the process is a pair `(A, M)` of
alive edges and the matching built so far, and the law of the state after `t` rounds is a
probability mass function `proc H a D t` on the finite type of states. If a state is not good,
the process simply stops there.
-/

namespace Pseudorandom.Nibble

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/- ## One round on a good state -/

section Round

variable (A : Finset (Finset V)) {a D : ℝ}

/-- Union bound for the new degrees. -/
theorem round_bad_le (ha : 0 ≤ a) (hD : 0 ≤ D) (r : ℕ) (hr : 1 ≤ r) (huni : IsUniform A r)
    (hdeg : ∀ u, (degree A u : ℝ) ≤ D) (K : ℝ) (hK : 0 < K)
    (hcod : ∀ u w, u ≠ w → (codegree A u w : ℝ) ≤ K) (lam D' : ℝ) (hlam : 0 < lam)
    (hD' : D * Real.exp (-(a * (((r - 1 : ℕ) : ℝ) * D - ((r - 1 : ℕ) : ℝ) ^ 2 * K))) + lam ≤ D')
    (U : Finset V) (hU : ∀ e ∈ A, e ⊆ U) :
    pProb (roundP A a D) (fun ω => ∃ v, D' < degree (alive A ω) v) ≤
      U.card * Real.exp (-(lam ^ 2 / (2 * (2 * a * r ^ 2 * K * D ^ 2 + r * K * lam)))) := by
  have hP := roundP_isPMF A ha D
  have hsub : ∀ ω, (∃ v, D' < degree (alive A ω) v) →
      ∃ v ∈ U, lam ≤ (degP A ω v : ℝ) - pE (roundP A a D) (fun ω => (degP A ω v : ℝ)) := by
    rintro ω ⟨v, hv⟩
    have hEle := pE_degP_le A D ha r huni hdeg K hK.le hcod v
    have h1 : (degree (alive A ω) v : ℝ) ≤ degP A ω v := by
      exact_mod_cast degree_alive_le_degP A ω v
    have hD'pos : 0 < D' := by
      have : 0 ≤ D * Real.exp (-(a * (((r - 1 : ℕ) : ℝ) * D - ((r - 1 : ℕ) : ℝ) ^ 2 * K))) :=
        mul_nonneg hD (Real.exp_pos _).le
      linarith
    have hvU : v ∈ U := by
      have hpos : 0 < degree (alive A ω) v := by
        have : (0 : ℝ) < degree (alive A ω) v := lt_trans hD'pos hv
        exact_mod_cast this
      unfold degree at hpos
      obtain ⟨e, he⟩ := card_pos.mp hpos
      rw [mem_filter] at he
      exact hU e (alive_subset A ω he.1) he.2
    exact ⟨v, hvU, by linarith⟩
  calc _ ≤ pProb (roundP A a D) (fun ω => ∃ v ∈ U,
        lam ≤ (degP A ω v : ℝ) - pE (roundP A a D) (fun ω => (degP A ω v : ℝ))) :=
        pProb_mono hP hsub
    _ ≤ ∑ v ∈ U, pProb (roundP A a D) (fun ω =>
        lam ≤ (degP A ω v : ℝ) - pE (roundP A a D) (fun ω => (degP A ω v : ℝ))) :=
        pProb_exists_le hP U _
    _ ≤ ∑ v ∈ U, Real.exp (-(lam ^ 2 / (2 * (2 * a * r ^ 2 * K * D ^ 2 + r * K * lam)))) :=
        sum_le_sum fun v _ => degP_tail A D ha hD r hr huni hdeg K hK hcod v lam hlam
    _ = _ := by rw [sum_const, nsmul_eq_mul]

/-- An alive edge stays alive and the state stays good with probability `≥ e^{-a r D} - β`. -/
theorem round_alive_good_ge (ha : 0 ≤ a) (hD : 0 ≤ D) (r : ℕ) (hr : 1 ≤ r)
    (huni : IsUniform A r) (hdeg : ∀ u, (degree A u : ℝ) ≤ D) (K : ℝ) (hK : 0 < K)
    (hcod : ∀ u w, u ≠ w → (codegree A u w : ℝ) ≤ K) (lam D' : ℝ) (hlam : 0 < lam)
    (hD' : D * Real.exp (-(a * (((r - 1 : ℕ) : ℝ) * D - ((r - 1 : ℕ) : ℝ) ^ 2 * K))) + lam ≤ D')
    (U : Finset V) (hU : ∀ e ∈ A, e ⊆ U) {e : Finset V} (he : e ∈ A) :
    Real.exp (-(a * (r * D))) -
        U.card * Real.exp (-(lam ^ 2 / (2 * (2 * a * r ^ 2 * K * D ^ 2 + r * K * lam)))) ≤
      pProb (roundP A a D) (fun ω => e ∈ alive A ω ∧ ∀ v, (degree (alive A ω) v : ℝ) ≤ D') := by
  have hP := roundP_isPMF A ha D
  have h1 := prob_alive_ge A D ha he r (huni e he) (fun u _ => hdeg u)
  have h2 := round_bad_le A ha hD r hr huni hdeg K hK hcod lam D' hlam hD' U hU
  have h3 : pProb (roundP A a D) (fun ω => e ∈ alive A ω) ≤
      pProb (roundP A a D) (fun ω => e ∈ alive A ω ∧ ∀ v, (degree (alive A ω) v : ℝ) ≤ D') +
      pProb (roundP A a D) (fun ω => ∃ v, D' < degree (alive A ω) v) := by
    refine (pProb_mono hP (T := fun ω => (e ∈ alive A ω ∧ ∀ v, (degree (alive A ω) v : ℝ) ≤ D') ∨
      ∃ v, D' < degree (alive A ω) v) ?_).trans (pProb_or_le hP _ _)
    intro ω h
    by_cases hg : ∀ v, (degree (alive A ω) v : ℝ) ≤ D'
    · exact Or.inl ⟨h, hg⟩
    · push_neg at hg; exact Or.inr hg
  linarith

end Round

/- ## The process -/

/-- States: alive edges and the matching built so far. -/
abbrev State (V : Type*) := Finset (Finset V) × Finset (Finset V)

/-- A state is good if all degrees are at most `D`. -/
def Good (D : ℝ) (A : Finset (Finset V)) : Prop := ∀ v, (degree A v : ℝ) ≤ D

/-- The state after a round with coins `ω`. -/
def next (S : State V) (ω : Coin V → Bool) : State V := (alive S.1 ω, S.2 ∪ acc S.1 ω)

/-- The invariant of the process. -/
def Inv (H : Finset (Finset V)) (S : State V) : Prop :=
  S.1 ⊆ H ∧ S.2 ⊆ H ∧ IsMatching S.2 ∧ ∀ f ∈ S.1, ∀ g ∈ S.2, Disjoint f g

open Classical in
/-- One step of the process, as a transformation of probability mass functions on states. -/
noncomputable def step (a D : ℝ) (μ : State V → ℝ) : State V → ℝ := fun S' =>
  ∑ S, μ S * (if Good D S.1 then
    pE (roundP S.1 a D) (fun ω => if next S ω = S' then 1 else 0)
    else if S = S' then 1 else 0)

open Classical in
/-- The law of the state after `t` rounds. -/
noncomputable def proc (H : Finset (Finset V)) (a D : ℕ → ℝ) : ℕ → State V → ℝ
  | 0 => fun S => if S = (H, ∅) then 1 else 0
  | t + 1 => step (a t) (D t) (proc H a D t)

open Classical in
theorem step_sum (a D : ℝ) (μ : State V → ℝ) (g : State V → ℝ) :
    ∑ S', step a D μ S' * g S' =
      ∑ S, μ S * (if Good D S.1 then pE (roundP S.1 a D) (fun ω => g (next S ω)) else g S) := by
  unfold step
  simp_rw [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun S _ => ?_
  simp_rw [mul_assoc]
  rw [← mul_sum]
  congr 1
  split_ifs with hg
  · have : ∀ S', pE (roundP S.1 a D) (fun ω => if next S ω = S' then (1 : ℝ) else 0) * g S' =
        pE (roundP S.1 a D) (fun ω => (if next S ω = S' then (1 : ℝ) else 0) * g S') := by
      intro S'
      rw [mul_comm, ← pE_const_mul]
      congr 1; funext ω; ring
    simp_rw [this]
    rw [← pE_sum]
    congr 1; funext ω
    simp
  · simp

theorem step_nonneg (a D : ℝ) (ha : 0 ≤ a) {μ : State V → ℝ} (hμ : ∀ S, 0 ≤ μ S) (S' : State V) :
    0 ≤ step a D μ S' := by
  classical
  unfold step
  refine sum_nonneg fun S _ => mul_nonneg (hμ S) ?_
  split_ifs
  · exact pE_nonneg (roundP_isPMF S.1 ha D) fun ω => by split_ifs <;> norm_num
  · norm_num
  · norm_num

theorem inv_next {H : Finset (Finset V)} {S : State V} (hS : Inv H S) (ω : Coin V → Bool) :
    Inv H (next S ω) := by
  obtain ⟨h1, h2, h3, h4⟩ := hS
  refine ⟨(alive_subset _ ω).trans h1, union_subset h2 ((acc_subset _ ω).trans h1), ?_, ?_⟩
  · intro e he f hf hef
    simp only [next] at he hf
    rw [mem_union] at he hf
    rcases he with he | he <;> rcases hf with hf | hf
    · exact h3 e he f hf hef
    · exact (h4 f (acc_subset _ ω hf) e he).symm
    · exact h4 e (acc_subset _ ω he) f hf
    · exact acc_isMatching _ ω e he f hf hef
  · intro f hf g hg
    simp only [next] at hf hg
    rw [mem_union] at hg
    rcases hg with hg | hg
    · exact h4 f (alive_subset _ ω hf) g hg
    · exact disjoint_alive_acc _ ω f hf g hg

/- ## Properties of the process -/

/-- The hypotheses under which the process is analysed. -/
structure Params (H : Finset (Finset V)) (r : ℕ) (K : ℝ) (U : Finset V) (a D lam : ℕ → ℝ) :
    Prop where
  hr : 1 ≤ r
  huni : IsUniform H r
  hK : 0 < K
  hcod : ∀ u w, u ≠ w → (codegree H u w : ℝ) ≤ K
  hU : ∀ e ∈ H, e ⊆ U
  ha : ∀ t, 0 ≤ a t
  hD : ∀ t, 0 ≤ D t
  hlam : ∀ t, 0 < lam t
  hstep : ∀ t, D t * Real.exp (-(a t * (((r - 1 : ℕ) : ℝ) * D t - ((r - 1 : ℕ) : ℝ) ^ 2 * K)))
    + lam t ≤ D (t + 1)
  hdeg0 : ∀ v, (degree H v : ℝ) ≤ D 0

/-- The failure probability of a round. -/
noncomputable def beta (r : ℕ) (K : ℝ) (U : Finset V) (a D lam : ℕ → ℝ) (t : ℕ) : ℝ :=
  U.card * Real.exp (-(lam t ^ 2 / (2 * (2 * a t * r ^ 2 * K * D t ^ 2 + r * K * lam t))))

/-- Lower bound for the probability that a fixed edge is alive (and the state good). -/
noncomputable def Lseq (r : ℕ) (K : ℝ) (U : Finset V) (a D lam : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | t + 1 => Lseq r K U a D lam t * Real.exp (-(a t * (r * D t))) - beta r K U a D lam t

variable {H : Finset (Finset V)} {r : ℕ} {K : ℝ} {U : Finset V} {a D lam : ℕ → ℝ}

omit [Fintype V] [DecidableEq V] in
theorem beta_nonneg (t : ℕ) : 0 ≤ beta r K U a D lam t := by
  unfold beta; positivity

theorem proc_nonneg (P : Params H r K U a D lam) : ∀ t S, 0 ≤ proc H a D t S
  | 0, S => by simp only [proc]; split_ifs <;> norm_num
  | t + 1, S => step_nonneg _ _ (P.ha t) (proc_nonneg P t) S

theorem proc_sum (P : Params H r K U a D lam) : ∀ t, ∑ S, proc H a D t S = 1
  | 0 => by simp [proc]
  | t + 1 => by
    classical
    have h := step_sum (a t) (D t) (proc H a D t) (fun _ => 1)
    simp only [mul_one] at h
    simp only [proc]
    rw [h]
    calc _ = ∑ S, proc H a D t S := by
          refine sum_congr rfl fun S _ => ?_
          split_ifs
          · rw [pE_const (roundP_isPMF _ (P.ha t) _), mul_one]
          · rw [mul_one]
      _ = 1 := proc_sum P t

theorem proc_inv (P : Params H r K U a D lam) : ∀ t S, proc H a D t S ≠ 0 → Inv H S
  | 0, S => by
    intro h
    simp only [proc] at h
    split_ifs at h with hS
    · subst hS
      refine ⟨subset_refl _, empty_subset _, ?_, ?_⟩
      · intro e he; simp at he
      · intro f _ g hg; simp at hg
    · exact absurd rfl h
  | t + 1, S' => by
    classical
    intro h
    by_contra hinv
    apply h
    simp only [proc, step]
    refine sum_eq_zero fun S _ => ?_
    by_cases hμ : proc H a D t S = 0
    · rw [hμ, zero_mul]
    · have hS := proc_inv P t S hμ
      split_ifs with hg hSS
      · have : (fun ω => if next S ω = S' then (1 : ℝ) else 0) = fun _ => 0 := by
          funext ω
          rw [if_neg]
          intro heq
          exact hinv (heq ▸ inv_next hS ω)
        rw [this, pE_const (roundP_isPMF _ (P.ha t) _), mul_zero]
      · exact absurd (hSS ▸ hS) hinv
      · rw [mul_zero]

omit [Fintype V] in
theorem Params.uni_of_sub (P : Params H r K U a D lam) {A : Finset (Finset V)} (h : A ⊆ H) :
    IsUniform A r := fun e he => P.huni e (h he)

omit [Fintype V] in
theorem Params.cod_of_sub (P : Params H r K U a D lam) {A : Finset (Finset V)} (h : A ⊆ H) :
    ∀ u w, u ≠ w → (codegree A u w : ℝ) ≤ K := fun u w huw =>
  le_trans (by exact_mod_cast codegree_mono h u w) (P.hcod u w huw)

open Classical in
/-- The probability that a fixed edge is alive in a good state after `t` rounds. -/
theorem alive_ge (P : Params H r K U a D lam) {e : Finset V} (he : e ∈ H) : ∀ t,
    Lseq r K U a D lam t ≤
      ∑ S, proc H a D t S * (if e ∈ S.1 ∧ Good (D t) S.1 then 1 else 0)
  | 0 => by
    simp only [proc, Lseq]
    rw [sum_eq_single (H, ∅)]
    · simp only [if_true, one_mul]
      rw [if_pos ⟨he, P.hdeg0⟩]
    · intro S _ hS; rw [if_neg hS, zero_mul]
    · intro h; exact absurd (mem_univ _) h
  | t + 1 => by
    have ih := alive_ge P he t
    simp only [proc]
    rw [step_sum]
    have hper : ∀ S, proc H a D t S *
        (if e ∈ S.1 ∧ Good (D t) S.1 then 1 else 0) * Real.exp (-(a t * (r * D t))) -
          proc H a D t S * beta r K U a D lam t ≤
        proc H a D t S * (if Good (D t) S.1 then pE (roundP S.1 (a t) (D t))
          (fun ω => if e ∈ (next S ω).1 ∧ Good (D (t + 1)) (next S ω).1 then 1 else 0)
          else if e ∈ S.1 ∧ Good (D (t + 1)) S.1 then 1 else 0) := by
      intro S
      have hμ0 := proc_nonneg P t S
      have hb := beta_nonneg (r := r) (K := K) (U := U) (a := a) (D := D) (lam := lam) t
      by_cases hμ : proc H a D t S = 0
      · simp [hμ]
      have hS := proc_inv P t S hμ
      rw [mul_assoc, ← mul_sub]
      apply mul_le_mul_of_nonneg_left _ hμ0
      by_cases hg : Good (D t) S.1
      · rw [if_pos hg]
        by_cases heS : e ∈ S.1
        · rw [if_pos ⟨heS, hg⟩, one_mul]
          have hround := round_alive_good_ge S.1 (P.ha t) (P.hD t) r P.hr (P.uni_of_sub hS.1)
            hg K P.hK (P.cod_of_sub hS.1) (lam t) (D (t + 1)) (P.hlam t) (P.hstep t) U
            (fun f hf => P.hU f (hS.1 hf)) heS
          rw [← pProb_eq_pE _ _ (fun ω h => if_pos h) (fun ω h => if_neg h)]
          exact hround
        · rw [if_neg (fun h => heS h.1), zero_mul, zero_sub]
          have := pE_nonneg (roundP_isPMF S.1 (P.ha t) (D t))
            (f := fun ω => if e ∈ (next S ω).1 ∧ Good (D (t + 1)) (next S ω).1 then (1 : ℝ) else 0)
            (fun ω => by dsimp (config := { failIfUnchanged := false }) only; split_ifs <;> norm_num)
          linarith
      · rw [if_neg hg, if_neg (show ¬(e ∈ S.1 ∧ Good (D t) S.1) from fun h => hg h.2), zero_mul,
          zero_sub]
        have : (0 : ℝ) ≤ if e ∈ S.1 ∧ Good (D (t + 1)) S.1 then 1 else 0 := by
          split_ifs <;> norm_num
        linarith
    calc Lseq r K U a D lam (t + 1)
        = Lseq r K U a D lam t * Real.exp (-(a t * (r * D t))) - beta r K U a D lam t := rfl
      _ ≤ (∑ S, proc H a D t S * (if e ∈ S.1 ∧ Good (D t) S.1 then 1 else 0)) *
            Real.exp (-(a t * (r * D t))) - beta r K U a D lam t := by
          gcongr
      _ = ∑ S, (proc H a D t S * (if e ∈ S.1 ∧ Good (D t) S.1 then 1 else 0) *
            Real.exp (-(a t * (r * D t))) - proc H a D t S * beta r K U a D lam t) := by
          rw [sum_sub_distrib, ← sum_mul, ← sum_mul, proc_sum P t, one_mul]
      _ ≤ _ := sum_le_sum fun S _ => hper S

open Classical in
/-- The probability that a fixed edge is in the matching after `T` rounds. -/
theorem inM_ge (P : Params H r K U a D lam) {e : Finset V} (he : e ∈ H) : ∀ T,
    ∑ t ∈ range T, Lseq r K U a D lam t * ((1 - Real.exp (-a t)) * Real.exp (-(a t * (r * D t))))
      ≤ ∑ S, proc H a D T S * (if e ∈ S.2 then 1 else 0)
  | 0 => by
    simp only [range_zero, sum_empty, proc]
    exact sum_nonneg fun S _ => by split_ifs <;> norm_num
  | T + 1 => by
    have ih := inM_ge P he T
    have hal := alive_ge P he T
    have hne : e.Nonempty := by
      rw [← card_pos, P.huni e he]; exact P.hr
    set acc0 := (1 - Real.exp (-a T)) * Real.exp (-(a T * (r * D T))) with hacc0
    have hacc_nonneg : 0 ≤ acc0 := by
      have : Real.exp (-a T) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [P.ha T])
      have : 0 ≤ 1 - Real.exp (-a T) := by linarith
      positivity
    simp only [proc]
    rw [step_sum, sum_range_succ]
    have hper : ∀ S, proc H a D T S * (if e ∈ S.2 then 1 else 0) +
        proc H a D T S * (if e ∈ S.1 ∧ Good (D T) S.1 then 1 else 0) * acc0 ≤
        proc H a D T S * (if Good (D T) S.1 then pE (roundP S.1 (a T) (D T))
          (fun ω => if e ∈ (next S ω).2 then 1 else 0)
          else if e ∈ S.2 then 1 else 0) := by
      intro S
      have hμ0 := proc_nonneg P T S
      by_cases hμ : proc H a D T S = 0
      · simp [hμ]
      have hS := proc_inv P T S hμ
      rw [mul_assoc, ← mul_add]
      apply mul_le_mul_of_nonneg_left _ hμ0
      by_cases hg : Good (D T) S.1
      · rw [if_pos hg]
        by_cases heM : e ∈ S.2
        · have heA : e ∉ S.1 := by
            intro heA
            have := hS.2.2.2 e heA e heM
            rw [disjoint_self_iff_empty] at this
            exact hne.ne_empty this
          rw [if_pos heM, if_neg (fun h => heA h.1), zero_mul, add_zero]
          have : (fun ω => if e ∈ (next S ω).2 then (1 : ℝ) else 0) = fun _ => 1 := by
            funext ω; rw [if_pos]; simp [next, heM]
          rw [this, pE_const (roundP_isPMF _ (P.ha T) _)]
        · rw [if_neg heM, zero_add]
          have heq : (fun ω => if e ∈ (next S ω).2 then (1 : ℝ) else 0) =
              fun ω => if e ∈ acc S.1 ω then 1 else 0 := by
            funext ω
            simp [next, heM]
          rw [heq, ← pProb_eq_pE _ _ (fun ω h => if_pos h) (fun ω h => if_neg h)]
          by_cases heA : e ∈ S.1
          · rw [if_pos ⟨heA, hg⟩, one_mul]
            exact prob_acc_ge S.1 (D T) (P.ha T) heA hne r (P.huni e he) (fun u _ => hg u)
          · rw [if_neg (fun h => heA h.1), zero_mul]
            exact pProb_nonneg (roundP_isPMF _ (P.ha T) _) _
      · rw [if_neg hg, if_neg (show ¬(e ∈ S.1 ∧ Good (D T) S.1) from fun h => hg h.2), zero_mul,
          add_zero]
    calc _ ≤ (∑ S, proc H a D T S * (if e ∈ S.2 then 1 else 0)) +
          (∑ S, proc H a D T S * (if e ∈ S.1 ∧ Good (D T) S.1 then 1 else 0)) * acc0 := by
          gcongr
      _ = ∑ S, (proc H a D T S * (if e ∈ S.2 then 1 else 0) +
          proc H a D T S * (if e ∈ S.1 ∧ Good (D T) S.1 then 1 else 0) * acc0) := by
          rw [sum_add_distrib, sum_mul]
      _ ≤ _ := sum_le_sum fun S _ => hper S

/- ## The output: a random matching -/

/-- The law of the matching after `T` rounds. -/
noncomputable def outM (H : Finset (Finset V)) (a D : ℕ → ℝ) (T : ℕ) :
    Finset (Finset V) → ℝ :=
  fun M => ∑ A : Finset (Finset V), proc H a D T (A, M)

theorem outM_nonneg (P : Params H r K U a D lam) (T : ℕ) (M : Finset (Finset V)) :
    0 ≤ outM H a D T M :=
  sum_nonneg fun _ _ => proc_nonneg P T _

theorem outM_sum (P : Params H r K U a D lam) (T : ℕ) : ∑ M, outM H a D T M = 1 := by
  unfold outM
  rw [sum_comm, ← proc_sum P T, ← Fintype.sum_prod_type']

theorem outM_support (P : Params H r K U a D lam) (T : ℕ) (M : Finset (Finset V))
    (h : outM H a D T M ≠ 0) : IsMatching M ∧ M ⊆ H := by
  unfold outM at h
  obtain ⟨_, _, hA⟩ := exists_ne_zero_of_sum_ne_zero h
  have := proc_inv P T _ hA
  exact ⟨this.2.2.1, this.2.1⟩

open Classical in
theorem outM_marginal (P : Params H r K U a D lam) (T : ℕ) {e : Finset V} (he : e ∈ H) :
    ∑ t ∈ range T, Lseq r K U a D lam t * ((1 - Real.exp (-a t)) * Real.exp (-(a t * (r * D t))))
      ≤ ∑ M, outM H a D T M * (if e ∈ M then 1 else 0) := by
  refine (inM_ge P he T).trans (le_of_eq ?_)
  unfold outM
  simp_rw [sum_mul]
  rw [sum_comm, ← Fintype.sum_prod_type']

end Pseudorandom.Nibble

end FlattenedPS08

/- PseudorandomLib.Asymptotics -/
section FlattenedPS09
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/- # Elementary asymptotic facts used to choose `Δ₀`

All statements are of the form "eventually (as `D → ∞`) some explicit inequality holds".
-/

namespace Pseudorandom

open Filter Asymptotics

/-- `C ≤ D^c` eventually, for `c > 0`. -/
theorem eventually_const_le_rpow {c : ℝ} (hc : 0 < c) (C : ℝ) :
    ∀ᶠ D : ℝ in atTop, C ≤ D ^ c :=
  (tendsto_rpow_atTop hc).eventually_ge_atTop C

/-- `C log D ≤ D^c` eventually, for `c > 0`. -/
theorem eventually_mul_log_le_rpow {c : ℝ} (hc : 0 < c) (C : ℝ) :
    ∀ᶠ D : ℝ in atTop, C * Real.log D ≤ D ^ c := by
  have h := (isLittleO_log_rpow_atTop hc).bound (c := 1 / (|C| + 1)) (by positivity)
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with D hD hD1
  have hlog : 0 ≤ Real.log D := Real.log_nonneg hD1
  have hpow : 0 ≤ D ^ c := Real.rpow_nonneg (by linarith) c
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog, abs_of_nonneg hpow] at hD
  calc C * Real.log D ≤ |C| * Real.log D :=
        mul_le_mul_of_nonneg_right (le_abs_self C) hlog
    _ ≤ |C| * (1 / (|C| + 1) * D ^ c) := mul_le_mul_of_nonneg_left hD (abs_nonneg C)
    _ = (|C| / (|C| + 1)) * D ^ c := by ring
    _ ≤ 1 * D ^ c := by
        apply mul_le_mul_of_nonneg_right _ hpow
        rw [div_le_one (by positivity)]; linarith
    _ = D ^ c := one_mul _

/-- `D^σ ≤ c D^γ` eventually, for `σ < γ` and `c > 0`. -/
theorem eventually_rpow_le_mul_rpow {σ γ c : ℝ} (hσγ : σ < γ) (hc : 0 < c) :
    ∀ᶠ D : ℝ in atTop, D ^ σ ≤ c * D ^ γ := by
  filter_upwards [eventually_const_le_rpow (sub_pos.mpr hσγ) (1 / c),
    eventually_gt_atTop (0 : ℝ)] with D hD hD0
  have h1 : D ^ γ = D ^ σ * D ^ (γ - σ) := by
    rw [← Real.rpow_add hD0]; ring_nf
  rw [h1]
  have h2 : 0 < D ^ σ := Real.rpow_pos_of_pos hD0 σ
  calc D ^ σ = c * (D ^ σ * (1 / c)) := by field_simp
    _ ≤ c * (D ^ σ * D ^ (γ - σ)) := by gcongr

end Pseudorandom

end FlattenedPS09

/- PseudorandomLib.NibbleMarginal -/
section FlattenedPS10
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/- # The nibble produces a random matching with almost uniform marginals

**Theorem (nibble marginals).** Let `r ≥ 2` and `ρ > 0`, `κ, σ ≥ 0` with
`(2r + 4) ρ + κ + σ < 1`. For all large `D`, every `r`-uniform hypergraph `H` with maximum
degree `≤ D`, codegrees `≤ D^κ` and at most `exp(D^σ)` edges carries a probability
distribution on its matchings in which every edge is used with probability at least
`(1 - D^{-ρ}) / D`.

The proof runs the nibble of `NibbleIterate.lean` with `θ = D^{-2ρ}`, `η = θ²`,
`⌈2ρ log D / θ⌉` rounds and degree bounds `D_t = D (e^{-(r-1)θ} (1 + 2η))^t`.
-/

namespace Pseudorandom.Nibble

open Finset Filter

/- ## The numerical conditions on `D` -/

/-- The numerical conditions on `D` used by the nibble. -/
structure NibbleFacts (r : ℕ) (ρ κ σ D : ℝ) : Prop where
  h1 : 1 ≤ D
  h2 : 4 * r ≤ D ^ (2 * ρ)
  h4 : 4 * r ^ 2 * Real.exp r ≤ D ^ (1 - κ - 2 * r * ρ)
  h5 : Real.exp r ≤ D ^ (1 - 2 * (r - 1) * ρ)
  h6 : Real.log r + (3 + 2 * ρ) * Real.log D + D ^ σ ≤
    D ^ (1 - (2 * r + 4) * ρ - κ) / (24 * r ^ 2 * Real.exp r)
  h7 : r + 5 ≤ D ^ ρ
  h8 : 2 * ρ * Real.log D * D ^ (2 * ρ) + 1 ≤ D

theorem eventually_nibbleFacts (r : ℕ) (hr : 1 ≤ r) {ρ κ σ : ℝ} (hρ : 0 < ρ) (hκ : 0 ≤ κ)
    (hσ : 0 ≤ σ) (hsum : (2 * r + 4) * ρ + κ + σ < 1) :
    ∀ᶠ D : ℝ in atTop, NibbleFacts r ρ κ σ D := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  set C := 24 * (r : ℝ) ^ 2 * Real.exp r with hC
  have hCpos : 0 < C := by positivity
  set γ := 1 - (2 * r + 4) * ρ - κ with hγ
  have hγσ : σ < γ := by rw [hγ]; linarith
  have hγ0 : 0 < γ := by linarith
  have e4 : 0 < 1 - κ - 2 * r * ρ := by nlinarith
  have e5 : 0 < 1 - 2 * (r - 1) * ρ := by nlinarith
  have e8 : 0 < 1 - 2 * ρ := by nlinarith
  have hA := eventually_const_le_rpow (c := γ) hγ0 (4 * C * Real.log r)
  have hB := eventually_mul_log_le_rpow (c := γ) hγ0 (4 * C * (3 + 2 * ρ))
  have hS := eventually_rpow_le_mul_rpow (σ := σ) (γ := γ) (c := 1 / (2 * C)) hγσ (by positivity)
  have hL := eventually_mul_log_le_rpow (c := 1 - 2 * ρ) e8 (4 * ρ)
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    eventually_const_le_rpow (by positivity : (0 : ℝ) < 2 * ρ) (4 * r),
    eventually_const_le_rpow e4 (4 * r ^ 2 * Real.exp r),
    eventually_const_le_rpow e5 (Real.exp r),
    eventually_const_le_rpow hρ (r + 5), hA, hB, hS, hL] with D hD2 h2 h4 h5 h7 hA hB hS hL
  have hD0 : 0 < D := by linarith
  refine ⟨by linarith, h2, h4, h5, ?_, h7, ?_⟩
  · have hlog : 0 ≤ Real.log D := Real.log_nonneg (by linarith)
    have h1 : Real.log r ≤ D ^ γ / (4 * C) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have h2' : (3 + 2 * ρ) * Real.log D ≤ D ^ γ / (4 * C) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    have h3 : D ^ σ ≤ D ^ γ / (2 * C) := by
      rw [div_eq_mul_inv, mul_comm]; simpa [one_div] using hS
    have : D ^ γ / (4 * C) + D ^ γ / (4 * C) + D ^ γ / (2 * C) = D ^ γ / C := by
      field_simp; ring
    linarith
  · have hpow : D ^ (1 - 2 * ρ) * D ^ (2 * ρ) = D := by
      rw [← Real.rpow_add hD0]; simp
    have hpos : 0 < D ^ (2 * ρ) := Real.rpow_pos_of_pos hD0 _
    have : 4 * ρ * Real.log D * D ^ (2 * ρ) ≤ D := by
      calc 4 * ρ * Real.log D * D ^ (2 * ρ) ≤ D ^ (1 - 2 * ρ) * D ^ (2 * ρ) :=
            mul_le_mul_of_nonneg_right hL hpos.le
        _ = D := hpow
    have hlog : 0 ≤ Real.log D := Real.log_nonneg (by linarith)
    nlinarith

/- ## Elementary inequalities -/

theorem exp_le_one_add_two_mul {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    Real.exp y ≤ 1 + 2 * y := by
  have h := exp_le_one_add_add_sq_div y (1 / 2) (by rw [abs_of_nonneg hy0]; exact hy1)
    (by norm_num)
  have : y ^ 2 / (2 * (1 - 1 / 2)) = y ^ 2 := by ring
  rw [this] at h
  nlinarith

theorem one_sub_exp_neg_le {a : ℝ} : 1 - Real.exp (-a) ≤ a := by
  linarith [Real.one_sub_le_exp_neg a]

theorem one_sub_exp_neg_ge {a : ℝ} (ha : 0 ≤ a) : a - a ^ 2 / 2 ≤ 1 - Real.exp (-a) := by
  have h1 := Real.quadratic_le_exp_of_nonneg ha
  have hpos : 0 < 1 + a + a ^ 2 / 2 := by positivity
  have h2 : Real.exp (-a) ≤ 1 / (1 + a + a ^ 2 / 2) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le hpos h1
  have h3 : 1 / (1 + a + a ^ 2 / 2) ≤ 1 - a + a ^ 2 / 2 := by
    rw [div_le_iff₀ hpos]
    nlinarith [sq_nonneg (a ^ 2)]
  linarith

/-- `q^t - t β ≤ Lseq t` when every round has survival factor `q` and failure `≤ β`. -/
theorem Lseq_ge {V : Type*} [DecidableEq V] {r : ℕ} {K : ℝ} {U : Finset V} {a D lam : ℕ → ℝ}
    (q bb : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hbb : 0 ≤ bb)
    (hq : ∀ t, Real.exp (-(a t * (r * D t))) = q) (hb : ∀ t, beta r K U a D lam t ≤ bb) :
    ∀ t : ℕ, q ^ t - t * bb ≤ Lseq r K U a D lam t
  | 0 => by simp [Lseq]
  | t + 1 => by
    have ih := Lseq_ge q bb hq0 hq1 hbb hq hb t
    simp only [Lseq, hq t]
    have h1 : (q ^ t - t * bb) * q ≤ Lseq r K U a D lam t * q :=
      mul_le_mul_of_nonneg_right ih hq0
    have h2 : t * bb * q ≤ t * bb := by
      have : (0 : ℝ) ≤ t * bb := by positivity
      nlinarith
    have h3 := hb t
    have h4 : (q ^ t - t * bb) * q = q ^ (t + 1) - t * bb * q := by ring
    push_cast
    linarith

/-- The final numerical estimate for the marginals. -/
theorem marginal_sum_bound (T : ℕ) (r θ q y bb D : ℝ) (as L : ℕ → ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 8) (hD : 1 ≤ D) (hTD : (T : ℝ) ≤ D) (hbb : 0 ≤ bb)
    (hDbb : D ^ 3 * bb ≤ θ) (hy1 : y < 1) (h1y : 1 - y ≤ θ * (1 + 2 * θ))
    (hyT : y ^ T ≤ θ) (hr0 : 0 ≤ r) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hqr : 1 - r * θ ≤ q) (has0 : ∀ t, 0 ≤ as t) (has1 : ∀ t, as t ≤ θ)
    (hmain : ∀ t < T, q ^ (t + 1) * as t = θ * q * y ^ t / D)
    (hL : ∀ t, q ^ t - t * bb ≤ L t) :
    1 - (r + 5) * θ ≤ D * ∑ t ∈ range T, L t * ((1 - Real.exp (-as t)) * q) := by
  have hD0 : 0 < D := by linarith
  have hterm : ∀ t ∈ range T, θ * q * y ^ t / D * (1 - θ / 2) - t * bb * θ ≤
      L t * ((1 - Real.exp (-as t)) * q) := by
    intro t ht
    have htT := mem_range.mp ht
    have ha0 := has0 t
    have ha1 := has1 t
    have hF0 : 0 ≤ (1 - Real.exp (-as t)) * q := by
      have : Real.exp (-as t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      exact mul_nonneg (by linarith) hq0
    have hFle : (1 - Real.exp (-as t)) * q ≤ as t * q :=
      mul_le_mul_of_nonneg_right one_sub_exp_neg_le hq0
    have hFge : (as t - as t ^ 2 / 2) * q ≤ (1 - Real.exp (-as t)) * q :=
      mul_le_mul_of_nonneg_right (one_sub_exp_neg_ge ha0) hq0
    have hqt0 : 0 ≤ q ^ t := pow_nonneg hq0 t
    have h1 : (q ^ t - t * bb) * ((1 - Real.exp (-as t)) * q) ≤
        L t * ((1 - Real.exp (-as t)) * q) := mul_le_mul_of_nonneg_right (hL t) hF0
    have h2 : q ^ t * ((as t - as t ^ 2 / 2) * q) ≤ q ^ t * ((1 - Real.exp (-as t)) * q) :=
      mul_le_mul_of_nonneg_left hFge hqt0
    have htb : (0 : ℝ) ≤ t * bb := by positivity
    have h3 : t * bb * ((1 - Real.exp (-as t)) * q) ≤ t * bb * θ := by
      apply mul_le_mul_of_nonneg_left _ htb
      calc _ ≤ as t * q := hFle
        _ ≤ θ * 1 := mul_le_mul ha1 hq1 hq0 hθ0.le
        _ = θ := mul_one θ
    have h4 : q ^ t * ((as t - as t ^ 2 / 2) * q) =
        q ^ (t + 1) * as t * (1 - as t / 2) := by ring
    have h5 : θ * q * y ^ t / D * (1 - θ / 2) ≤ q ^ (t + 1) * as t * (1 - as t / 2) := by
      rw [← hmain t htT]
      apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
    linarith
  have hsum := sum_le_sum hterm
  rw [sum_sub_distrib, ← sum_mul, ← sum_mul] at hsum
  have hs1 : ∑ i ∈ range T, θ * q * y ^ i / D = θ * q / D * ∑ i ∈ range T, y ^ i := by
    rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
  rw [hs1] at hsum
  have hgeom : ∑ t ∈ range T, y ^ t = (1 - y ^ T) / (1 - y) := by
    rw [geom_sum_eq hy1.ne, div_eq_div_iff (by linarith) (by linarith)]; ring
  have hgeom2 : (1 - θ) / (1 + 2 * θ) ≤ θ * ∑ t ∈ range T, y ^ t := by
    rw [hgeom, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by linarith)]
    have : 0 ≤ 1 - θ := by linarith
    nlinarith
  have hcnt : ∑ t ∈ range T, (t : ℝ) ≤ D ^ 2 := by
    calc ∑ t ∈ range T, (t : ℝ) ≤ ∑ t ∈ range T, (T : ℝ) :=
          sum_le_sum fun t ht => by exact_mod_cast (mem_range.mp ht).le
      _ = (T : ℝ) ^ 2 := by rw [sum_const, card_range, nsmul_eq_mul]; ring
      _ ≤ D ^ 2 := by gcongr
  have hA : 1 - 7 / 2 * θ ≤ (1 - θ / 2) * ((1 - θ) / (1 + 2 * θ)) := by
    rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg θ, mul_pos hθ0 hθ0, mul_pos (mul_pos hθ0 hθ0) hθ0]
  have hstep1 : D * (θ * q / D * (∑ t ∈ range T, y ^ t) * (1 - θ / 2)) =
      q * (1 - θ / 2) * (θ * ∑ t ∈ range T, y ^ t) := by
    field_simp
  have hstep2 : D * ((∑ t ∈ range T, (t : ℝ)) * bb * θ) ≤ θ ^ 2 := by
    have : D * ((∑ t ∈ range T, (t : ℝ)) * bb * θ) ≤ D * (D ^ 2 * bb * θ) := by
      gcongr
    calc _ ≤ D * (D ^ 2 * bb * θ) := this
      _ = (D ^ 3 * bb) * θ := by ring
      _ ≤ θ * θ := by gcongr
      _ = θ ^ 2 := by ring
  have hmul := mul_le_mul_of_nonneg_left hsum hD0.le
  rw [mul_sub, hstep1] at hmul
  have hB : q * (1 - θ / 2) * ((1 - θ) / (1 + 2 * θ)) ≤
      q * (1 - θ / 2) * (θ * ∑ t ∈ range T, y ^ t) :=
    mul_le_mul_of_nonneg_left hgeom2 (by nlinarith)
  have hC : (1 - r * θ) * (1 - 7 / 2 * θ) ≤ q * ((1 - θ / 2) * ((1 - θ) / (1 + 2 * θ))) := by
    apply mul_le_mul hqr hA (by linarith) hq0
  rw [← sum_mul] at hmul
  have hθθ : θ ^ 2 ≤ θ / 8 := by nlinarith
  have hrθθ : 0 ≤ r * θ ^ 2 := by positivity
  nlinarith

/- ## The main statement -/

set_option maxHeartbeats 4000000 in
/-- **Nibble marginals.** -/
theorem nibble_marginal (r : ℕ) (hr : 2 ≤ r) {ρ κ σ : ℝ} (hρ : 0 < ρ) (hκ : 0 ≤ κ)
    (hσ : 0 ≤ σ) (hsum : (2 * r + 4) * ρ + κ + σ < 1) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∀ (V : Type) [Fintype V] [DecidableEq V]
      (H : Finset (Finset V)), IsUniform H r → (∀ v, (degree H v : ℝ) ≤ D) →
      (∀ u w, u ≠ w → (codegree H u w : ℝ) ≤ D ^ κ) → (H.card : ℝ) ≤ Real.exp (D ^ σ) →
      ∃ μ : Finset (Finset V) → ℝ, (∀ M, 0 ≤ μ M) ∧ ∑ M, μ M = 1 ∧
        (∀ M, μ M ≠ 0 → IsMatching M ∧ M ⊆ H) ∧
        ∀ e ∈ H, (1 - D ^ (-ρ)) / D ≤ ∑ M, μ M * (if e ∈ M then 1 else 0) := by
  obtain ⟨D₀, hD₀⟩ := Filter.eventually_atTop.mp
    (eventually_nibbleFacts r (by omega) hρ hκ hσ hsum)
  refine ⟨D₀, fun D hD V _ _ H huni hdeg hcod hcard => ?_⟩
  have F := hD₀ D hD
  have hD1 : 1 ≤ D := F.h1
  have hD0 : 0 < D := by linarith
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hr1 : ((r - 1 : ℕ) : ℝ) = r - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  -- the parameters
  set θ : ℝ := D ^ (-(2 * ρ)) with hθdef
  have hθpos : 0 < θ := Real.rpow_pos_of_pos hD0 _
  have hθinv : θ * D ^ (2 * ρ) = 1 := by
    rw [hθdef, ← Real.rpow_add hD0]; simp
  have hθsmall : θ ≤ 1 / (4 * r) := by
    have h := F.h2
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hθ1 : θ ≤ 1 / 8 := by
    have : 1 / (4 * (r : ℝ)) ≤ 1 / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  set η : ℝ := θ ^ 2 with hηdef
  set K : ℝ := D ^ κ with hKdef
  have hKpos : 0 < K := Real.rpow_pos_of_pos hD0 _
  set c : ℝ := Real.exp (-(((r - 1 : ℕ) : ℝ) * θ)) with hcdef
  have hc0 : 0 < c := Real.exp_pos _
  have hc1 : c ≤ 1 := Real.exp_le_one_iff.mpr (by rw [hr1]; nlinarith)
  have hc34 : 3 / 4 ≤ c := by
    have h0 := Real.add_one_le_exp (-(((r - 1 : ℕ) : ℝ) * θ))
    rw [hr1] at h0
    rw [hcdef, hr1]
    have : (r - 1 : ℝ) * θ ≤ 1 / 4 := by
      have : (r : ℝ) * θ ≤ 1 / 4 := by
        rw [le_div_iff₀ (by positivity)] at hθsmall
        nlinarith
      nlinarith
    linarith
  set x : ℝ := c * (1 + 2 * η) with hxdef
  have hx0 : 0 < x := by positivity
  have hcx : c ≤ x := by nlinarith [sq_nonneg θ]
  have hx1 : x ≤ 1 := by
    have h1 : 1 + 2 * η ≤ Real.exp (((r - 1 : ℕ) : ℝ) * θ) := by
      have := Real.add_one_le_exp (((r - 1 : ℕ) : ℝ) * θ)
      rw [hr1] at this ⊢
      have : 2 * η ≤ (r - 1) * θ := by
        rw [hηdef]; nlinarith
      linarith
    calc x = c * (1 + 2 * η) := rfl
      _ ≤ c * Real.exp (((r - 1 : ℕ) : ℝ) * θ) := mul_le_mul_of_nonneg_left h1 hc0.le
      _ = 1 := by rw [hcdef, ← Real.exp_add]; simp
  set T : ℕ := ⌈2 * ρ * Real.log D / θ⌉₊ with hTdef
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD1
  have hθT1 : 2 * ρ * Real.log D ≤ θ * T := by
    have := Nat.le_ceil (2 * ρ * Real.log D / θ)
    rw [← hTdef, div_le_iff₀ hθpos] at this
    linarith
  have hθT2 : θ * T ≤ 2 * ρ * Real.log D + θ := by
    have := Nat.ceil_lt_add_one (show 0 ≤ 2 * ρ * Real.log D / θ by positivity)
    rw [← hTdef] at this
    have h2 : θ * T ≤ θ * (2 * ρ * Real.log D / θ + 1) :=
      mul_le_mul_of_nonneg_left this.le hθpos.le
    rw [mul_add, mul_div_cancel₀ _ hθpos.ne', mul_one] at h2
    exact h2
  have hTD : (T : ℝ) ≤ D := by
    have := Nat.ceil_lt_add_one (show 0 ≤ 2 * ρ * Real.log D / θ by positivity)
    rw [← hTdef] at this
    have h8 := F.h8
    have : 2 * ρ * Real.log D / θ = 2 * ρ * Real.log D * D ^ (2 * ρ) := by
      rw [div_eq_iff hθpos.ne']
      linear_combination (2 * ρ * Real.log D) * hθinv.symm
    linarith
  -- degree bounds
  obtain ⟨Ds, hDs_eq⟩ : ∃ Ds : ℕ → ℝ, ∀ t, Ds t = D * x ^ (min t T) := ⟨_, fun t => rfl⟩
  obtain ⟨as, has_eq⟩ : ∃ as : ℕ → ℝ, ∀ t, as t = θ / Ds t := ⟨_, fun t => rfl⟩
  obtain ⟨ls, hls_eq⟩ : ∃ ls : ℕ → ℝ, ∀ t, ls t = η * Ds t * c := ⟨_, fun t => rfl⟩
  set Dmin : ℝ := D ^ (1 - 2 * (r - 1) * ρ) / Real.exp r with hDmin
  have hDmin1 : 1 ≤ Dmin := by
    rw [hDmin, le_div_iff₀ (Real.exp_pos _), one_mul]; exact F.h5
  have hDT : Dmin ≤ D * c ^ T := by
    have hcT : c ^ T = Real.exp (-((r - 1 : ℝ) * θ * T)) := by
      rw [hcdef, ← Real.exp_nat_mul, hr1]; ring_nf
    have h2 : Dmin = D * Real.exp (-((r - 1 : ℝ) * (2 * ρ * Real.log D)) - r) := by
      rw [hDmin, Real.rpow_def_of_pos hD0, ← Real.exp_sub,
        show Real.log D * (1 - 2 * (r - 1) * ρ) - r =
          Real.log D + (-((r - 1 : ℝ) * (2 * ρ * Real.log D)) - r) by ring,
        Real.exp_add, Real.exp_log hD0]
    have hr0 : (0 : ℝ) ≤ r - 1 := by linarith
    have h1 : -((r - 1 : ℝ) * (2 * ρ * Real.log D)) - r ≤ -((r - 1 : ℝ) * θ * T) := by
      have := mul_le_mul_of_nonneg_left hθT2 hr0
      nlinarith
    rw [hcT, h2]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h1) hD0.le
  have hDs : ∀ t, Dmin ≤ Ds t := by
    intro t
    rw [hDs_eq]
    refine hDT.trans (mul_le_mul_of_nonneg_left ?_ hD0.le)
    exact (pow_le_pow_left₀ hc0.le hcx T).trans
      (pow_le_pow_of_le_one hx0.le hx1 (min_le_right _ _))
  have hDs1 : ∀ t, 1 ≤ Ds t := fun t => hDmin1.trans (hDs t)
  have hDspos : ∀ t, 0 < Ds t := fun t => lt_of_lt_of_le one_pos (hDs1 t)
  -- two identities between the parameters
  have hθDmin : 4 * (r : ℝ) ^ 2 * K ≤ θ * Dmin := by
    have h4 := F.h4
    have e1 : θ * Dmin = D ^ (1 - 2 * r * ρ) / Real.exp r := by
      rw [hDmin, hθdef, mul_div_assoc', ← Real.rpow_add hD0]; congr 2; ring
    have e2 : D ^ (1 - κ - 2 * r * ρ) * K = D ^ (1 - 2 * r * ρ) := by
      rw [hKdef, ← Real.rpow_add hD0]; congr 1; ring
    rw [e1, le_div_iff₀ (Real.exp_pos _)]
    calc 4 * (r : ℝ) ^ 2 * K * Real.exp r = (4 * r ^ 2 * Real.exp r) * K := by ring
      _ ≤ D ^ (1 - κ - 2 * r * ρ) * K := mul_le_mul_of_nonneg_right h4 hKpos.le
      _ = _ := e2
  set γ : ℝ := 1 - (2 * r + 4) * ρ - κ with hγ
  have hθ3 : θ ^ 3 * Dmin = D ^ γ * K / Real.exp r := by
    rw [hDmin, hθdef, hKdef, hγ, ← Real.rpow_natCast, ← Real.rpow_mul hD0.le, mul_div_assoc',
      ← Real.rpow_add hD0, ← Real.rpow_add hD0]
    congr 2; push_cast; ring
  -- the degree recursion
  have hxs : ∀ t, Ds t * x ≤ Ds (t + 1) := by
    intro t
    rw [hDs_eq, hDs_eq, mul_assoc, ← pow_succ]
    apply mul_le_mul_of_nonneg_left _ hD0.le
    apply pow_le_pow_of_le_one hx0.le hx1
    omega
  have hη1 : η ≤ θ := by
    rw [hηdef]; exact pow_le_of_le_one hθpos.le (by linarith) two_ne_zero
  have hstep : ∀ t, Ds t * Real.exp (-(as t * (((r - 1 : ℕ) : ℝ) * Ds t -
      ((r - 1 : ℕ) : ℝ) ^ 2 * K))) + ls t ≤ Ds (t + 1) := by
    intro t
    have hp := hDspos t
    set y := θ * (((r - 1 : ℕ) : ℝ)) ^ 2 * K / Ds t with hydef
    have hy0 : 0 ≤ y := by positivity
    have hyη : y ≤ η / 2 := by
      rw [hydef, div_le_iff₀ hp, hηdef]
      have hr1' : (((r - 1 : ℕ) : ℝ)) ^ 2 ≤ r ^ 2 := by rw [hr1]; nlinarith
      have h1 : θ * (((r - 1 : ℕ) : ℝ)) ^ 2 * K ≤ θ * (r ^ 2 * K) := by
        rw [mul_assoc]; gcongr
      have h2 : θ * (r ^ 2 * K) ≤ θ * (θ * Dmin / 4) := by
        gcongr; linarith
      have h3 : θ * (θ * Dmin / 4) ≤ θ ^ 2 / 2 * Ds t := by
        have := hDs t
        have : θ * θ * Dmin ≤ θ * θ * Ds t := by gcongr
        nlinarith
      linarith
    have hey : Real.exp y ≤ 1 + η := by
      have := exp_le_one_add_two_mul hy0 (by linarith); linarith
    have heq : Real.exp (-(as t * (((r - 1 : ℕ) : ℝ) * Ds t - ((r - 1 : ℕ) : ℝ) ^ 2 * K))) =
        c * Real.exp y := by
      rw [hcdef, ← Real.exp_add, has_eq, hydef]; congr 1; field_simp; ring
    rw [heq, hls_eq]
    calc Ds t * (c * Real.exp y) + η * Ds t * c ≤ Ds t * (c * (1 + η)) + η * Ds t * c := by
          gcongr
      _ = Ds t * x := by rw [hxdef]; ring
      _ ≤ _ := hxs t
  set U : Finset V := H.biUnion id with hUdef
  have P : Params H r K U as Ds ls :=
    { hr := by omega
      huni := huni
      hK := hKpos
      hcod := hcod
      hU := fun e he => subset_biUnion_of_mem id he
      ha := fun t => by rw [has_eq]; exact div_nonneg hθpos.le (hDspos t).le
      hD := fun t => (hDspos t).le
      hlam := fun t => by rw [hls_eq]; have := hDspos t; positivity
      hstep := hstep
      hdeg0 := fun v => by rw [hDs_eq]; simpa using hdeg v }
  -- the survival factor and the failure probabilities
  set q : ℝ := Real.exp (-(r * θ)) with hqdef
  have hq : ∀ t, Real.exp (-(as t * (r * Ds t))) = q := by
    intro t
    rw [hqdef, has_eq]; congr 2; field_simp [(hDspos t).ne']
  set E : ℝ := D ^ γ / (24 * r ^ 2 * Real.exp r) with hEdef
  set bb : ℝ := r * Real.exp (D ^ σ) * Real.exp (-E) with hbbdef
  have hbb0 : 0 ≤ bb := by positivity
  have hUcard : (U.card : ℝ) ≤ r * Real.exp (D ^ σ) := by
    have h1 : U.card ≤ ∑ e ∈ H, (id e).card := card_biUnion_le
    have h2 : ∑ e ∈ H, (id e).card = H.card * r := by
      exact sum_const_nat (fun e he => huni e he)
    have h3 : (U.card : ℝ) ≤ H.card * r := by exact_mod_cast h2 ▸ h1
    nlinarith
  have hb : ∀ t, beta r K U as Ds ls t ≤ bb := by
    intro t
    have hp := hDspos t
    unfold beta
    rw [hbbdef]
    apply mul_le_mul hUcard _ (Real.exp_pos _).le (by positivity)
    rw [Real.exp_le_exp, neg_le_neg_iff]
    have hden : 0 < 2 * (2 * as t * r ^ 2 * K * Ds t ^ 2 + r * K * ls t) := by
      have := P.hlam t; have := P.ha t; positivity
    rw [le_div_iff₀ hden]
    have hZ : 6 * E * r ^ 2 * K = D ^ γ * K / Real.exp r / 4 := by
      rw [hEdef]; field_simp; ring
    have hden2 : 2 * (2 * as t * r ^ 2 * K * Ds t ^ 2 + r * K * ls t) ≤
        6 * θ * r ^ 2 * K * Ds t := by
      rw [has_eq, hls_eq]
      have hrr : (r : ℝ) ≤ r ^ 2 := by nlinarith
      have h1 : r * K * (η * Ds t * c) ≤ r ^ 2 * K * (θ * Ds t * 1) := by
        gcongr
      have h2 : 2 * (θ / Ds t) * r ^ 2 * K * Ds t ^ 2 = 2 * θ * r ^ 2 * K * Ds t := by
        field_simp
      nlinarith
    have hZle : D ^ γ * K / Real.exp r * (9 / 16) ≤ θ ^ 3 * Ds t * c ^ 2 := by
      rw [← hθ3]
      have : θ ^ 3 * Dmin ≤ θ ^ 3 * Ds t := by gcongr; exact hDs t
      have hc2 : 9 / 16 ≤ c ^ 2 := by nlinarith
      have : 0 ≤ θ ^ 3 * Dmin := by positivity
      nlinarith
    have hE0 : 0 ≤ E := by positivity
    calc E * (2 * (2 * as t * r ^ 2 * K * Ds t ^ 2 + r * K * ls t))
        ≤ E * (6 * θ * r ^ 2 * K * Ds t) := mul_le_mul_of_nonneg_left hden2 hE0
      _ = θ * Ds t * (6 * E * r ^ 2 * K) := by ring
      _ ≤ θ * Ds t * (θ ^ 3 * Ds t * c ^ 2) := by
          rw [hZ]; gcongr
          have hZ0 : 0 ≤ D ^ γ * K / Real.exp r := by positivity
          linarith
      _ = ls t ^ 2 := by rw [hls_eq, hηdef]; ring
  have hDbb : D ^ 3 * bb ≤ θ := by
    have h6 := F.h6
    have hrpos : (0 : ℝ) < r := by linarith
    have e1 : D ^ 3 * bb = Real.exp (3 * Real.log D + Real.log r + D ^ σ - E) := by
      rw [Real.exp_sub, Real.exp_add, Real.exp_add, Real.exp_log hrpos,
        show 3 * Real.log D = ((3 : ℕ) : ℝ) * Real.log D by norm_num, Real.exp_nat_mul,
        Real.exp_log hD0, hbbdef, Real.exp_neg]
      field_simp
    have e2 : θ = Real.exp (-(2 * ρ) * Real.log D) := by
      rw [hθdef, Real.rpow_def_of_pos hD0, mul_comm]
    rw [e1, e2, Real.exp_le_exp]
    have : E = D ^ (1 - (2 * r + 4) * ρ - κ) / (24 * r ^ 2 * Real.exp r) := by rw [hEdef, hγ]
    linarith
  -- the auxiliary ratio y
  have hqc : q = c * Real.exp (-θ) := by
    rw [hqdef, hcdef, ← Real.exp_add, hr1]; congr 1; ring
  set y : ℝ := q / x with hydef
  have hy_eq : y = Real.exp (-θ) / (1 + 2 * η) := by
    rw [hydef, hqc, hxdef]; field_simp
  have hyle : y ≤ Real.exp (-θ) := by
    rw [hy_eq]; exact div_le_self (Real.exp_pos _).le (by nlinarith)
  have hy0 : 0 ≤ y := by rw [hy_eq]; positivity
  have hy1 : y < 1 := hyle.trans_lt (Real.exp_lt_one_iff.mpr (by linarith))
  have h1y : 1 - y ≤ θ * (1 + 2 * θ) := by
    have he := Real.add_one_le_exp (-θ)
    have hpos : 0 < 1 + 2 * η := by positivity
    have : (1 - θ - 2 * θ ^ 2) * (1 + 2 * η) ≤ Real.exp (-θ) := by
      rw [hηdef]; nlinarith [pow_pos hθpos 3, pow_pos hθpos 4]
    have : 1 - θ * (1 + 2 * θ) ≤ y := by
      rw [hy_eq, le_div_iff₀ hpos]; linarith
    linarith
  have hyT : y ^ T ≤ θ := by
    calc y ^ T ≤ Real.exp (-θ) ^ T := pow_le_pow_left₀ hy0 hyle T
      _ = Real.exp (-(θ * T)) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (-(2 * ρ) * Real.log D) := Real.exp_le_exp.mpr (by nlinarith)
      _ = θ := by rw [hθdef, Real.rpow_def_of_pos hD0, mul_comm]
  have hrθ : (r : ℝ) * θ ≤ 1 / 4 := by
    rw [le_div_iff₀ (by positivity)] at hθsmall; nlinarith
  have hqr : 1 - r * θ ≤ q := by
    have := Real.add_one_le_exp (-(r * θ)); rw [hqdef]; linarith
  have hq1 : q ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have has1 : ∀ t, as t ≤ θ := fun t => by rw [has_eq]; exact div_le_self hθpos.le (hDs1 t)
  have hmain : ∀ t < T, q ^ (t + 1) * as t = θ * q * y ^ t / D := by
    intro t ht
    rw [has_eq, hDs_eq, min_eq_left ht.le, hydef, div_pow]
    field_simp
    ring
  have hL := Lseq_ge (r := r) (K := K) (U := U) (a := as) (D := Ds) (lam := ls) q bb
    (Real.exp_pos _).le hq1 hbb0 hq hb
  have hfinal := marginal_sum_bound T r θ q y bb D as (Lseq r K U as Ds ls) hθpos hθ1 hD1 hTD
    hbb0 hDbb hy1 h1y hyT (by linarith) (Real.exp_pos _).le hq1 hqr P.ha has1 hmain hL
  have hrho : ((r : ℝ) + 5) * θ ≤ D ^ (-ρ) := by
    have e1 : θ = D ^ (-ρ) * D ^ (-ρ) := by rw [hθdef, ← Real.rpow_add hD0]; congr 1; ring
    have e2 : D ^ (-ρ) * D ^ ρ = 1 := by rw [← Real.rpow_add hD0]; simp
    have hpos : 0 < D ^ (-ρ) := Real.rpow_pos_of_pos hD0 _
    rw [e1]
    calc (r + 5) * (D ^ (-ρ) * D ^ (-ρ)) = D ^ (-ρ) * ((r + 5) * D ^ (-ρ)) := by ring
      _ ≤ D ^ (-ρ) * (D ^ ρ * D ^ (-ρ)) := by gcongr; exact F.h7
      _ = D ^ (-ρ) := by rw [mul_comm (D ^ ρ), e2, mul_one]
  refine ⟨outM H as Ds T, outM_nonneg P T, outM_sum P T,
    fun M hM => outM_support P T M hM, fun e he => ?_⟩
  have hm := outM_marginal P T he
  simp_rw [hq] at hm
  rw [div_le_iff₀ hD0]
  have := mul_le_mul_of_nonneg_left hm hD0.le
  rw [mul_comm]
  linarith

end Pseudorandom.Nibble

end FlattenedPS10

/- PseudorandomLib.Cylinder -/
section FlattenedPS11
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/- # Concentration of weighted counts of monochromatic sets

Colour every coordinate `v ∈ ι` independently and uniformly with one of `m` colours. For a
family of sets `B s ⊆ ι` with weights `w s ≥ 0`, consider the weighted number of sets that are
entirely coloured with the fixed colour `a`:

  `cyl S w B a ω = ∑_{s ∈ S} w s · [ω ≡ a on B s]`.

Its expectation is `∑ w s m^{-|B s|}`, and it is concentrated by the Bernstein-type
bounded-differences inequality of `Bernstein.lean`: coordinate `v` changes it by at most
`c v = ∑_{s : v ∈ B s} w s`, and only if one of the two colours is `a`.
-/

namespace Pseudorandom

open Finset

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι]

/-- The uniform distribution on `m` colours at every coordinate. -/
noncomputable def unif (ι : Type*) (m : ℕ) : ι → Fin m → ℝ := fun _ _ => 1 / m

omit [Fintype ι] [DecidableEq ι] in
theorem unif_isPMF (m : ℕ) (hm : 0 < m) : IsPMF (unif ι m) := by
  refine ⟨fun _ _ => by unfold unif; positivity, fun _ => ?_⟩
  simp only [unif, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

open Classical in
/-- The weighted count of sets coloured entirely with colour `a`. -/
noncomputable def cyl {m : ℕ} (S : Finset σ) (w : σ → ℝ) (B : σ → Finset ι) (a : Fin m)
    (ω : ι → Fin m) : ℝ :=
  ∑ s ∈ S, w s * (if ∀ v ∈ B s, ω v = a then 1 else 0)

/-- The influence of a coordinate. -/
noncomputable def cylGap (S : Finset σ) (w : σ → ℝ) (B : σ → Finset ι) (v : ι) : ℝ :=
  ∑ s ∈ S.filter (fun s => v ∈ B s), w s

theorem cyl_pE {m : ℕ} (hm : 0 < m) (S : Finset σ) (w : σ → ℝ) (B : σ → Finset ι)
    (a : Fin m) : pE (unif ι m) (cyl S w B a) = ∑ s ∈ S, w s * (1 / m) ^ (B s).card := by
  classical
  unfold cyl
  rw [pE_sum]
  refine sum_congr rfl fun s _ => ?_
  rw [pE_const_mul]
  congr 1
  have h := pProb_cylinder (unif_isPMF (ι := ι) m hm) (B s) (fun _ => a)
  simp only [unif, prod_const] at h
  rw [← h]; unfold pProb; congr 1; funext ω; split_ifs <;> rfl

theorem cyl_gap {m : ℕ} (S : Finset σ) (w : σ → ℝ) (hw : ∀ s ∈ S, 0 ≤ w s)
    (B : σ → Finset ι) (a : Fin m) : CoordGap (cyl S w B a) (cylGap S w B) := by
  classical
  intro v ω b b'
  unfold cyl cylGap
  rw [← sum_sub_distrib, sum_filter]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun s hs => ?_)
  rw [← mul_sub, abs_mul, abs_of_nonneg (hw s hs)]
  by_cases hv : v ∈ B s
  · rw [if_pos hv]
    have : |(if ∀ u ∈ B s, Function.update ω v b u = a then (1 : ℝ) else 0) -
        (if ∀ u ∈ B s, Function.update ω v b' u = a then 1 else 0)| ≤ 1 := by
      split_ifs <;> norm_num
    exact mul_le_of_le_one_right (hw s hs) this
  · rw [if_neg hv]
    have : (∀ u ∈ B s, Function.update ω v b u = a) ↔
        (∀ u ∈ B s, Function.update ω v b' u = a) := by
      constructor <;> intro h u hu <;> have := h u hu <;>
        rwa [Function.update_of_ne (show u ≠ v from fun h => hv (h ▸ hu))] at this ⊢
    simp [this]

theorem cyl_rare {m : ℕ} (S : Finset σ) (w : σ → ℝ) (B : σ → Finset ι) (a : Fin m) :
    CoordRare (cyl S w B a) (fun _ => {a}) := by
  classical
  intro v ω b b' hb hb'
  rw [mem_singleton] at hb hb'
  unfold cyl
  refine sum_congr rfl fun s _ => ?_
  congr 1
  by_cases hv : v ∈ B s
  · have h1 : ¬ ∀ u ∈ B s, Function.update ω v b u = a := fun h => hb (by simpa using h v hv)
    have h2 : ¬ ∀ u ∈ B s, Function.update ω v b' u = a := fun h => hb' (by simpa using h v hv)
    rw [if_neg h1, if_neg h2]
  · have : (∀ u ∈ B s, Function.update ω v b u = a) ↔
        (∀ u ∈ B s, Function.update ω v b' u = a) := by
      constructor <;> intro h u hu <;> have := h u hu <;>
        rwa [Function.update_of_ne (show u ≠ v from fun h => hv (h ▸ hu))] at this ⊢
    simp [this]

theorem sum_cylGap (S : Finset σ) (w : σ → ℝ) (B : σ → Finset ι) :
    ∑ v, cylGap S w B v = ∑ s ∈ S, w s * (B s).card := by
  classical
  unfold cylGap
  simp_rw [sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun s _ => ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  simp

omit [Fintype ι] in
theorem cylGap_nonneg (S : Finset σ) (w : σ → ℝ) (hw : ∀ s ∈ S, 0 ≤ w s)
    (B : σ → Finset ι) (v : ι) : 0 ≤ cylGap S w B v :=
  sum_nonneg fun s hs => hw s (mem_filter.mp hs).1

/-- Variance proxy for `cyl`. -/
theorem cyl_var_le {m : ℕ} (S : Finset σ) (w : σ → ℝ) (hw : ∀ s ∈ S, 0 ≤ w s)
    (B : σ → Finset ι) (L Wt : ℝ) (hL : ∀ v, cylGap S w B v ≤ L)
    (hWt : ∑ s ∈ S, w s * (B s).card ≤ Wt) (hL0 : 0 ≤ L) :
    ∑ v, (1 / (m : ℝ)) * cylGap S w B v ^ 2 ≤ L * Wt / m := by
  have h1 : ∀ v, (1 / (m : ℝ)) * cylGap S w B v ^ 2 ≤ (L / m) * cylGap S w B v := by
    intro v
    have h0 := cylGap_nonneg S w hw B v
    have : cylGap S w B v ^ 2 ≤ L * cylGap S w B v := by
      rw [sq]; exact mul_le_mul_of_nonneg_right (hL v) h0
    rw [div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right this (Nat.cast_nonneg m)
  calc _ ≤ ∑ v, (L / m) * cylGap S w B v := sum_le_sum fun v _ => h1 v
    _ = (L / m) * ∑ s ∈ S, w s * (B s).card := by rw [← mul_sum, sum_cylGap]
    _ ≤ (L / m) * Wt := mul_le_mul_of_nonneg_left hWt (by positivity)
    _ = L * Wt / m := by ring

/-- **Upper tail** for weighted monochromatic counts. -/
theorem cyl_upper {m : ℕ} (hm : 0 < m) (S : Finset σ) (w : σ → ℝ) (hw : ∀ s ∈ S, 0 ≤ w s)
    (B : σ → Finset ι) (a : Fin m) (L Wt : ℝ) (hL0 : 0 < L) (hL : ∀ v, cylGap S w B v ≤ L)
    (hWt : ∑ s ∈ S, w s * (B s).card ≤ Wt) (t : ℝ) (ht : 0 < t) :
    pProb (unif ι m) (fun ω => t ≤ cyl S w B a ω - pE (unif ι m) (cyl S w B a)) ≤
      Real.exp (-(t ^ 2 / (2 * (L * Wt / m + L * t)))) := by
  have h := pE_upper_tail (unif ι m) (unif_isPMF m hm) (cyl S w B a) (cylGap S w B)
    (fun _ => 1 / (m : ℝ)) (fun _ => {a}) L hL0 (fun v => ⟨cylGap_nonneg S w hw B v, hL v⟩)
    (cyl_gap S w hw B a) (cyl_rare S w B a) (fun v => by simp [unif]) t ht
  refine h.trans (Real.exp_le_exp.mpr (neg_le_neg ?_))
  have hv := cyl_var_le (m := m) S w hw B L Wt hL hWt hL0.le
  have hpos : 0 < 2 * ((∑ v, (1 / (m : ℝ)) * cylGap S w B v ^ 2) + L * t) := by
    have : 0 ≤ ∑ v, (1 / (m : ℝ)) * cylGap S w B v ^ 2 :=
      sum_nonneg fun v _ => by positivity
    positivity
  exact div_le_div_of_nonneg_left (by positivity) hpos (by linarith)

/-- **Lower tail** for weighted monochromatic counts. -/
theorem cyl_lower {m : ℕ} (hm : 0 < m) (S : Finset σ) (w : σ → ℝ) (hw : ∀ s ∈ S, 0 ≤ w s)
    (B : σ → Finset ι) (a : Fin m) (L Wt : ℝ) (hL0 : 0 < L) (hL : ∀ v, cylGap S w B v ≤ L)
    (hWt : ∑ s ∈ S, w s * (B s).card ≤ Wt) (t : ℝ) (ht : 0 < t) :
    pProb (unif ι m) (fun ω => t ≤ pE (unif ι m) (cyl S w B a) - cyl S w B a ω) ≤
      Real.exp (-(t ^ 2 / (2 * (L * Wt / m + L * t)))) := by
  have h := pE_lower_tail (unif ι m) (unif_isPMF m hm) (cyl S w B a) (cylGap S w B)
    (fun _ => 1 / (m : ℝ)) (fun _ => {a}) L hL0 (fun v => ⟨cylGap_nonneg S w hw B v, hL v⟩)
    (cyl_gap S w hw B a) (cyl_rare S w B a) (fun v => by simp [unif]) t ht
  refine h.trans (Real.exp_le_exp.mpr (neg_le_neg ?_))
  have hv := cyl_var_le (m := m) S w hw B L Wt hL hWt hL0.le
  have hpos : 0 < 2 * ((∑ v, (1 / (m : ℝ)) * cylGap S w B v ^ 2) + L * t) := by
    have : 0 ≤ ∑ v, (1 / (m : ℝ)) * cylGap S w B v ^ 2 :=
      sum_nonneg fun v _ => by positivity
    positivity
  exact div_le_div_of_nonneg_left (by positivity) hpos (by linarith)

end Pseudorandom

end FlattenedPS11

/- PseudorandomLib.VertexPartition -/
section FlattenedPS12
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/- # Step 1: a random vertex partition

Colour every vertex uniformly at random with one of `p` colours and let `H_i` be the set of
edges all of whose vertices have colour `i`. With positive probability
* every vertex has degree at most `(1 + ξ) Δ / p^{r-1}` in every `H_i`, and
* every relevant weight function satisfies `ω(H_i) = (1 ± ξ) ω(H) / p^r` for every `i`.
-/

namespace Pseudorandom

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edges of `H` all of whose vertices have colour `i`. -/
def part {p : ℕ} (H : Finset (Finset V)) (τ : V → Fin p) (i : Fin p) : Finset (Finset V) :=
  H.filter (fun e => ∀ v ∈ e, τ v = i)

theorem part_subset {p : ℕ} (H : Finset (Finset V)) (τ : V → Fin p) (i : Fin p) :
    part H τ i ⊆ H := filter_subset _ _

/- ## Degrees -/

/-- Number of edges at `x` whose other vertices all have colour `i`. -/
noncomputable def degCyl {p : ℕ} (H : Finset (Finset V)) (x : V) (i : Fin p) (τ : V → Fin p) :
    ℝ :=
  cyl (H.filter (fun e => x ∈ e)) (fun _ => 1) (fun e => e.erase x) i τ

theorem degree_part_le_degCyl {p : ℕ} (H : Finset (Finset V)) (x : V) (i : Fin p)
    (τ : V → Fin p) : (degree (part H τ i) x : ℝ) ≤ degCyl H x i τ := by
  classical
  unfold degree part degCyl cyl
  rw [filter_filter]
  have : ((H.filter (fun e => (∀ v ∈ e, τ v = i) ∧ x ∈ e)).card : ℝ) =
      ∑ e ∈ H.filter (fun e => x ∈ e), (if ∀ v ∈ e, τ v = i then (1 : ℝ) else 0) := by
    rw [← sum_boole, sum_filter]
    refine sum_congr rfl fun e _ => ?_
    by_cases hx : x ∈ e <;> simp [hx]
  rw [this]
  refine sum_le_sum fun e _ => ?_
  rw [one_mul]
  split_ifs with h1 h2 h2 <;> try norm_num
  exact absurd (fun v hv => h1 v (mem_of_mem_erase hv)) h2

theorem pE_degCyl {p : ℕ} (hp : 0 < p) (H : Finset (Finset V)) (r : ℕ) (huni : IsUniform H r)
    (x : V) (i : Fin p) :
    pE (unif V p) (degCyl H x i) = degree H x * (1 / (p : ℝ)) ^ (r - 1) := by
  unfold degCyl
  rw [cyl_pE hp]
  have : ∀ e ∈ H.filter (fun e => x ∈ e), (1 : ℝ) * (1 / (p : ℝ)) ^ (e.erase x).card =
      (1 / (p : ℝ)) ^ (r - 1) := by
    intro e he
    rw [mem_filter] at he
    rw [card_erase_of_mem he.2, huni e he.1, one_mul]
  rw [sum_congr rfl this, sum_const, nsmul_eq_mul]
  rfl

omit [Fintype V] in
theorem degCyl_gap_le (H : Finset (Finset V)) (x : V) (C : ℝ) (hC : 0 ≤ C)
    (hcod : ∀ u v, u ≠ v → (codegree H u v : ℝ) ≤ C) (v : V) :
    cylGap (ι := V) (H.filter (fun e => x ∈ e)) (fun _ => (1 : ℝ)) (fun e => e.erase x) v ≤ C := by
  classical
  unfold cylGap
  rw [sum_const, nsmul_eq_mul, mul_one]
  by_cases hv : v = x
  · subst hv
    have : (H.filter (fun e => v ∈ e)).filter (fun e => v ∈ e.erase v) = ∅ := by
      ext e; simp
    rw [this]; simpa using hC
  · refine le_trans ?_ (hcod x v (Ne.symm hv))
    have hsub : (H.filter (fun e => x ∈ e)).filter (fun e => v ∈ e.erase x) ⊆
        H.filter (fun e => x ∈ e ∧ v ∈ e) := by
      intro e he
      simp only [mem_filter, mem_erase] at he ⊢
      exact ⟨he.1.1, he.1.2, he.2.2⟩
    unfold codegree
    exact_mod_cast card_le_card hsub

/-- Tail bound for the degrees. -/
theorem degCyl_tail {p : ℕ} (hp : 0 < p) (H : Finset (Finset V)) (r : ℕ) (hr : 1 ≤ r)
    (huni : IsUniform H r) (Δ C ξ : ℝ) (hΔ : 0 < Δ) (hC : 0 < C) (hξ : 0 < ξ)
    (hdeg : ∀ v, (degree H v : ℝ) ≤ Δ) (hcod : ∀ u v, u ≠ v → (codegree H u v : ℝ) ≤ C)
    (x : V) (i : Fin p) :
    pProb (unif V p) (fun τ => ξ * Δ / (p : ℝ) ^ (r - 1) ≤
        degCyl H x i τ - pE (unif V p) (degCyl H x i)) ≤
      Real.exp (-(ξ ^ 2 * Δ / (2 * C * (r * ((p : ℝ) ^ (r - 1)) ^ 2 / p + ξ * (p : ℝ) ^ (r - 1))))) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hP : (0 : ℝ) < (p : ℝ) ^ (r - 1) := by positivity
  have hWt : ∑ e ∈ H.filter (fun e => x ∈ e), (1 : ℝ) * (e.erase x).card ≤ r * Δ := by
    have : ∀ e ∈ H.filter (fun e => x ∈ e), (1 : ℝ) * (e.erase x).card ≤ r := by
      intro e he
      rw [mem_filter] at he
      rw [card_erase_of_mem he.2, huni e he.1, one_mul]
      exact_mod_cast Nat.sub_le r 1
    refine (sum_le_sum this).trans ?_
    rw [sum_const, nsmul_eq_mul, mul_comm]
    have : ((H.filter (fun e => x ∈ e)).card : ℝ) ≤ Δ := hdeg x
    have : (0 : ℝ) ≤ r := by positivity
    nlinarith
  have h := cyl_upper (ι := V) hp (H.filter (fun e => x ∈ e)) (fun _ => (1 : ℝ))
    (fun _ _ => zero_le_one) (fun e => e.erase x) i C (r * Δ) hC
    (degCyl_gap_le H x C hC.le hcod) hWt (ξ * Δ / (p : ℝ) ^ (r - 1)) (by positivity)
  refine h.trans (le_of_eq ?_)
  congr 2
  field_simp

/- ## Weights -/

theorem weight_part_eq_cyl {p : ℕ} (H : Finset (Finset V)) (w : Finset V → ℝ) (i : Fin p)
    (τ : V → Fin p) : weight w (part H τ i) = cyl H w id i τ := by
  classical
  unfold weight part cyl
  rw [sum_filter]
  refine sum_congr rfl fun e _ => ?_
  simp only [id]
  split_ifs <;> simp

theorem pE_weight_cyl {p : ℕ} (hp : 0 < p) (H : Finset (Finset V)) (r : ℕ)
    (huni : IsUniform H r) (w : Finset V → ℝ) (i : Fin p) :
    pE (unif V p) (cyl H w id i) = weight w H * (1 / (p : ℝ)) ^ r := by
  rw [cyl_pE hp, weight, sum_mul]
  refine sum_congr rfl fun e he => ?_
  simp [huni e he]

omit [Fintype V] in
theorem weight_gap_le (H : Finset (Finset V)) (Δ : ℝ)
    (hdeg : ∀ v, (degree H v : ℝ) ≤ Δ) (w : Finset V → ℝ) (m : ℝ) (hm : 0 ≤ m)
    (hw : ∀ e ∈ H, w e ≤ m) (v : V) : cylGap (ι := V) H w id v ≤ Δ * m := by
  unfold cylGap
  calc ∑ e ∈ H.filter (fun e => v ∈ id e), w e ≤ ∑ e ∈ H.filter (fun e => v ∈ id e), m :=
        sum_le_sum fun e he => hw e (mem_filter.mp he).1
    _ = (degree H v : ℝ) * m := by rw [sum_const, nsmul_eq_mul]; rfl
    _ ≤ Δ * m := mul_le_mul_of_nonneg_right (hdeg v) hm

/-- Tail bounds for the weights (both directions at once). -/
theorem weight_cyl_tail {p : ℕ} (hp : 0 < p) (H : Finset (Finset V)) (r : ℕ)
    (huni : IsUniform H r) (Δ η ξ : ℝ) (hΔ : 0 < Δ) (hη : 0 < η) (hξ : 0 < ξ)
    (hdeg : ∀ v, (degree H v : ℝ) ≤ Δ) (w : Finset V → ℝ) (hw0 : ∀ e ∈ H, 0 ≤ w e)
    (hwpos : 0 < weight w H) (hwmax : ∀ e ∈ H, w e ≤ η * weight w H) (i : Fin p) :
    pProb (unif V p) (fun τ => ξ * (weight w H / (p : ℝ) ^ r) ≤
        cyl H w id i τ - pE (unif V p) (cyl H w id i)) ≤
      Real.exp (-(ξ ^ 2 / (2 * Δ * η * (r * ((p : ℝ) ^ r) ^ 2 / p + ξ * (p : ℝ) ^ r)))) ∧
    pProb (unif V p) (fun τ => ξ * (weight w H / (p : ℝ) ^ r) ≤
        pE (unif V p) (cyl H w id i) - cyl H w id i τ) ≤
      Real.exp (-(ξ ^ 2 / (2 * Δ * η * (r * ((p : ℝ) ^ r) ^ 2 / p + ξ * (p : ℝ) ^ r)))) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  set ω := weight w H with hω
  have hL0 : 0 < Δ * (η * ω) := by positivity
  have hWt : ∑ e ∈ H, w e * (id e).card ≤ r * ω := by
    rw [hω, weight, mul_sum]
    exact le_of_eq (sum_congr rfl fun e he => by simp [huni e he, mul_comm])
  have hgap := weight_gap_le H Δ hdeg w (η * ω) (by positivity) hwmax
  have ht : 0 < ξ * (ω / (p : ℝ) ^ r) := by positivity
  have heq : (ξ * (ω / (p : ℝ) ^ r)) ^ 2 / (2 * (Δ * (η * ω) * (r * ω) / p +
      Δ * (η * ω) * (ξ * (ω / (p : ℝ) ^ r)))) =
      ξ ^ 2 / (2 * Δ * η * (r * ((p : ℝ) ^ r) ^ 2 / p + ξ * (p : ℝ) ^ r)) := by
    field_simp
  constructor
  · have h := cyl_upper (ι := V) hp H w hw0 id i (Δ * (η * ω)) (r * ω) hL0 hgap hWt _ ht
    rwa [heq] at h
  · have h := cyl_lower (ι := V) hp H w hw0 id i (Δ * (η * ω)) (r * ω) hL0 hgap hWt _ ht
    rwa [heq] at h

/- ## Existence of a good vertex partition -/

omit [Fintype V] in
theorem degree_eq_zero_of_not_mem_biUnion (A H : Finset (Finset V)) (hA : A ⊆ H) {x : V}
    (hx : x ∉ H.biUnion id) : degree A x = 0 := by
  unfold degree
  rw [card_eq_zero, filter_eq_empty_iff]
  intro e he hxe
  exact hx (mem_biUnion.mpr ⟨e, hA he, hxe⟩)

/-- **Step 1.** A random vertex partition is good with positive probability; an additional bad
event `Bad` of probability at most `πB` can be avoided at the same time. -/
theorem vertex_partition_ext {p : ℕ} (hp : 0 < p) (H : Finset (Finset V)) (r : ℕ) (hr : 1 ≤ r)
    (huni : IsUniform H r) (Δ C η ξ : ℝ) (hΔ : 0 < Δ) (hC : 0 < C) (hη : 0 < η) (hξ : 0 < ξ)
    (hdeg : ∀ v, (degree H v : ℝ) ≤ Δ) (hcod : ∀ u v, u ≠ v → (codegree H u v : ℝ) ≤ C)
    {ι : Type*} (W : ι → Finset V → ℝ) (K : Finset ι)
    (hW0 : ∀ k ∈ K, ∀ e ∈ H, 0 ≤ W k e) (hWpos : ∀ k ∈ K, 0 < weight (W k) H)
    (hWmax : ∀ k ∈ K, ∀ e ∈ H, W k e ≤ η * weight (W k) H)
    (Bad : (V → Fin p) → Prop) (πB : ℝ) (hBad : pProb (unif V p) Bad ≤ πB)
    (hfail : ((H.biUnion id).card * p : ℝ) * Real.exp (-(ξ ^ 2 * Δ /
        (2 * C * (r * ((p : ℝ) ^ (r - 1)) ^ 2 / p + ξ * (p : ℝ) ^ (r - 1))))) +
      (2 * K.card * p : ℝ) * Real.exp (-(ξ ^ 2 /
        (2 * Δ * η * (r * ((p : ℝ) ^ r) ^ 2 / p + ξ * (p : ℝ) ^ r)))) + πB < 1) :
    ∃ τ : V → Fin p, (∀ x i, (degree (part H τ i) x : ℝ) ≤ (1 + ξ) * Δ / (p : ℝ) ^ (r - 1)) ∧
      (∀ k ∈ K, ∀ i, |weight (W k) (part H τ i) - weight (W k) H / (p : ℝ) ^ r| ≤
        ξ * (weight (W k) H / (p : ℝ) ^ r)) ∧ ¬ Bad τ := by
  classical
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hP := unif_isPMF (ι := V) p hp
  set U := H.biUnion id with hU
  set E2 := ξ ^ 2 * Δ / (2 * C * (r * ((p : ℝ) ^ (r - 1)) ^ 2 / p + ξ * (p : ℝ) ^ (r - 1)))
  set E1 := ξ ^ 2 / (2 * Δ * η * (r * ((p : ℝ) ^ r) ^ 2 / p + ξ * (p : ℝ) ^ r))
  set bad1 : (V → Fin p) → Prop := fun τ => ∃ xi ∈ U ×ˢ (univ : Finset (Fin p)),
    ξ * Δ / (p : ℝ) ^ (r - 1) ≤ degCyl H xi.1 xi.2 τ - pE (unif V p) (degCyl H xi.1 xi.2)
  set bad2 : (V → Fin p) → Prop := fun τ => ∃ ki ∈ K ×ˢ (univ : Finset (Fin p)),
    ξ * (weight (W ki.1) H / (p : ℝ) ^ r) ≤
      cyl H (W ki.1) id ki.2 τ - pE (unif V p) (cyl H (W ki.1) id ki.2)
  set bad3 : (V → Fin p) → Prop := fun τ => ∃ ki ∈ K ×ˢ (univ : Finset (Fin p)),
    ξ * (weight (W ki.1) H / (p : ℝ) ^ r) ≤
      pE (unif V p) (cyl H (W ki.1) id ki.2) - cyl H (W ki.1) id ki.2 τ
  have h1 : pProb (unif V p) bad1 ≤ (U.card * p : ℝ) * Real.exp (-E2) := by
    refine (pProb_exists_le hP _ _).trans ?_
    refine (sum_le_sum fun xi _ => degCyl_tail hp H r hr huni Δ C ξ hΔ hC hξ hdeg hcod
      xi.1 xi.2).trans (le_of_eq ?_)
    rw [sum_const, card_product, card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  have h2 : pProb (unif V p) bad2 ≤ (K.card * p : ℝ) * Real.exp (-E1) := by
    refine (pProb_exists_le hP _ _).trans ?_
    refine (sum_le_sum fun ki hki => (weight_cyl_tail hp H r huni Δ η ξ hΔ hη hξ hdeg (W ki.1)
      (hW0 _ (mem_product.mp hki).1) (hWpos _ (mem_product.mp hki).1)
      (hWmax _ (mem_product.mp hki).1) ki.2).1).trans (le_of_eq ?_)
    rw [sum_const, card_product, card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  have h3 : pProb (unif V p) bad3 ≤ (K.card * p : ℝ) * Real.exp (-E1) := by
    refine (pProb_exists_le hP _ _).trans ?_
    refine (sum_le_sum fun ki hki => (weight_cyl_tail hp H r huni Δ η ξ hΔ hη hξ hdeg (W ki.1)
      (hW0 _ (mem_product.mp hki).1) (hWpos _ (mem_product.mp hki).1)
      (hWmax _ (mem_product.mp hki).1) ki.2).2).trans (le_of_eq ?_)
    rw [sum_const, card_product, card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  have hall : pProb (unif V p) (fun τ => bad1 τ ∨ bad2 τ ∨ bad3 τ ∨ Bad τ) < 1 := by
    have := pProb_or_le hP bad1 (fun τ => bad2 τ ∨ bad3 τ ∨ Bad τ)
    have := pProb_or_le hP bad2 (fun τ => bad3 τ ∨ Bad τ)
    have := pProb_or_le hP bad3 Bad
    linarith
  obtain ⟨τ, _, hτ⟩ := exists_of_pProb_lt_one hP hall
  simp only [not_or] at hτ
  obtain ⟨n1, n2, n3, n4⟩ := hτ
  refine ⟨τ, fun x i => ?_, fun k hk i => ?_, n4⟩
  · have hrhs : 0 ≤ (1 + ξ) * Δ / (p : ℝ) ^ (r - 1) := by positivity
    by_cases hx : x ∈ U
    · have hn : ¬ (ξ * Δ / (p : ℝ) ^ (r - 1) ≤
          degCyl H x i τ - pE (unif V p) (degCyl H x i)) :=
        fun h => n1 ⟨(x, i), mem_product.mpr ⟨hx, mem_univ _⟩, h⟩
      push_neg at hn
      rw [pE_degCyl hp H r huni x i, one_div_pow] at hn
      have hd := degree_part_le_degCyl H x i τ
      have : (degree H x : ℝ) * (1 / (p : ℝ) ^ (r - 1)) ≤ Δ * (1 / (p : ℝ) ^ (r - 1)) :=
        mul_le_mul_of_nonneg_right (hdeg x) (by positivity)
      have e : (1 + ξ) * Δ / (p : ℝ) ^ (r - 1) =
          Δ * (1 / (p : ℝ) ^ (r - 1)) + ξ * Δ / (p : ℝ) ^ (r - 1) := by ring
      rw [e]; linarith
    · rw [degree_eq_zero_of_not_mem_biUnion _ H (part_subset H τ i) hx]
      simpa using hrhs
  · have hn2 : ¬ (ξ * (weight (W k) H / (p : ℝ) ^ r) ≤
        cyl H (W k) id i τ - pE (unif V p) (cyl H (W k) id i)) :=
      fun h => n2 ⟨(k, i), mem_product.mpr ⟨hk, mem_univ _⟩, h⟩
    have hn3 : ¬ (ξ * (weight (W k) H / (p : ℝ) ^ r) ≤
        pE (unif V p) (cyl H (W k) id i) - cyl H (W k) id i τ) :=
      fun h => n3 ⟨(k, i), mem_product.mpr ⟨hk, mem_univ _⟩, h⟩
    push_neg at hn2 hn3
    rw [pE_weight_cyl hp H r huni, one_div_pow, ← div_eq_mul_one_div] at hn2 hn3
    rw [weight_part_eq_cyl, abs_le]
    constructor <;> linarith

/-- **Step 1.** A random vertex partition is good with positive probability. -/
theorem vertex_partition {p : ℕ} (hp : 0 < p) (H : Finset (Finset V)) (r : ℕ) (hr : 1 ≤ r)
    (huni : IsUniform H r) (Δ C η ξ : ℝ) (hΔ : 0 < Δ) (hC : 0 < C) (hη : 0 < η) (hξ : 0 < ξ)
    (hdeg : ∀ v, (degree H v : ℝ) ≤ Δ) (hcod : ∀ u v, u ≠ v → (codegree H u v : ℝ) ≤ C)
    {ι : Type*} (W : ι → Finset V → ℝ) (K : Finset ι)
    (hW0 : ∀ k ∈ K, ∀ e ∈ H, 0 ≤ W k e) (hWpos : ∀ k ∈ K, 0 < weight (W k) H)
    (hWmax : ∀ k ∈ K, ∀ e ∈ H, W k e ≤ η * weight (W k) H)
    (hfail : ((H.biUnion id).card * p : ℝ) * Real.exp (-(ξ ^ 2 * Δ /
        (2 * C * (r * ((p : ℝ) ^ (r - 1)) ^ 2 / p + ξ * (p : ℝ) ^ (r - 1))))) +
      (2 * K.card * p : ℝ) * Real.exp (-(ξ ^ 2 /
        (2 * Δ * η * (r * ((p : ℝ) ^ r) ^ 2 / p + ξ * (p : ℝ) ^ r)))) < 1) :
    ∃ τ : V → Fin p, (∀ x i, (degree (part H τ i) x : ℝ) ≤ (1 + ξ) * Δ / (p : ℝ) ^ (r - 1)) ∧
      ∀ k ∈ K, ∀ i, |weight (W k) (part H τ i) - weight (W k) H / (p : ℝ) ^ r| ≤
        ξ * (weight (W k) H / (p : ℝ) ^ r) := by
  classical
  obtain ⟨τ, h1, h2, -⟩ := vertex_partition_ext hp H r hr huni Δ C η ξ hΔ hC hη hξ hdeg hcod W K
    hW0 hWpos hWmax (fun _ => False) 0 (by unfold pProb pE; simp) (by linarith)
  exact ⟨τ, h1, h2⟩

end Pseudorandom

end FlattenedPS12

/- PseudorandomLib.EdgePartition -/
section FlattenedPS13
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/- # Step 2: a random edge partition

Every edge receives one of `q` colours uniformly at random. For a family of edge sets `A i`
(the parts of Step 1) let `cls A f i j` be the edges of `A i` with colour `j`. With positive
probability all degrees, codegrees and relevant weights of all classes are close to their
expectations (upper bounds only).
-/

namespace Pseudorandom

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edges of `A i` with colour `j`. -/
def cls {p q : ℕ} (A : Fin p → Finset (Finset V)) (f : Finset V → Fin q) (i : Fin p)
    (j : Fin q) : Finset (Finset V) :=
  (A i).filter (fun e => f e = j)

omit [Fintype V] [DecidableEq V] in
theorem cls_subset {p q : ℕ} (A : Fin p → Finset (Finset V)) (f : Finset V → Fin q) (i : Fin p)
    (j : Fin q) : cls A f i j ⊆ A i := filter_subset _ _

/- ## Colour classes of single edges -/

section Single

variable {q : ℕ}

theorem cyl_single_eq (S : Finset (Finset V)) (w : Finset V → ℝ) (j : Fin q)
    (f : Finset V → Fin q) :
    cyl S w (fun e => {e}) j f = ∑ e ∈ S.filter (fun e => f e = j), w e := by
  classical
  unfold cyl
  rw [sum_filter]
  refine sum_congr rfl fun e _ => ?_
  simp only [mem_singleton, forall_eq]
  split_ifs <;> simp

theorem pE_cyl_single (hq : 0 < q) (S : Finset (Finset V)) (w : Finset V → ℝ) (j : Fin q) :
    pE (unif (Finset V) q) (cyl S w (fun e => {e}) j) = (∑ e ∈ S, w e) * (1 / q) := by
  rw [cyl_pE hq, sum_mul]
  simp

omit [Fintype V] in
theorem cylGap_single_le (S : Finset (Finset V)) (w : Finset V → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hw : ∀ e ∈ S, w e ≤ L) (v : Finset V) : cylGap S w (fun e => {e}) v ≤ L := by
  classical
  unfold cylGap
  by_cases hv : v ∈ S
  · have : S.filter (fun s => v ∈ ({s} : Finset (Finset V))) = {v} := by
      ext s; simp only [mem_filter, mem_singleton]; constructor
      · rintro ⟨_, h⟩; exact h.symm
      · rintro rfl; exact ⟨hv, rfl⟩
    rw [this, sum_singleton]; exact hw v hv
  · have : S.filter (fun s => v ∈ ({s} : Finset (Finset V))) = ∅ := by
      rw [filter_eq_empty_iff]; intro s hs h; rw [mem_singleton] at h; exact hv (h ▸ hs)
    rw [this, sum_empty]; exact hL

/-- Tail bound for the weight of a colour class. -/
theorem single_tail (hq : 0 < q) (S : Finset (Finset V)) (w : Finset V → ℝ)
    (hw0 : ∀ e ∈ S, 0 ≤ w e) (L Wt : ℝ) (hL : 0 < L) (hwL : ∀ e ∈ S, w e ≤ L)
    (hWt : ∑ e ∈ S, w e ≤ Wt) (j : Fin q) (t : ℝ) (ht : 0 < t) :
    pProb (unif (Finset V) q) (fun f => t ≤ cyl S w (fun e => {e}) j f -
        pE (unif (Finset V) q) (cyl S w (fun e => {e}) j)) ≤
      Real.exp (-(t ^ 2 / (2 * (L * Wt / q + L * t)))) := by
  refine cyl_upper hq S w hw0 (fun e => {e}) j L Wt hL
    (cylGap_single_le S w L hL.le hwL) ?_ t ht
  simpa using hWt

end Single

/- ## Degrees and codegrees outside the vertex set of `H` -/

omit [Fintype V] in
theorem codegree_eq_zero_of_not_mem (A H : Finset (Finset V)) (hA : A ⊆ H) {x y : V}
    (h : x ∉ H.biUnion id ∨ y ∉ H.biUnion id) : codegree A x y = 0 := by
  unfold codegree
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro e he ⟨hx, hy⟩
  rcases h with h | h
  · exact h (mem_biUnion.mpr ⟨e, hA he, hx⟩)
  · exact h (mem_biUnion.mpr ⟨e, hA he, hy⟩)

/- ## Existence of a good edge partition -/

/-- **Step 2.** A random edge partition is good with positive probability; an additional bad
event `Bad` of probability at most `πB` can be avoided at the same time. -/
theorem edge_partition_ext {p q : ℕ} (hq : 0 < q) (H : Finset (Finset V))
    (A : Fin p → Finset (Finset V)) (hA : ∀ i, A i ⊆ H) (D₁ C t₃ t₄ : ℝ) (ht₃ : 0 < t₃)
    (ht₄ : 0 < t₄) (hdeg : ∀ i x, (degree (A i) x : ℝ) ≤ D₁)
    (hcod : ∀ i x y, x ≠ y → (codegree (A i) x y : ℝ) ≤ C)
    {ι : Type*} (W : ι → Finset V → ℝ) (K : Finset ι) (η β γ : ℝ) (hη : 0 < η) (hβ : 0 ≤ β) (hγ : 0 < γ)
    (hW0 : ∀ k ∈ K, ∀ e ∈ H, 0 ≤ W k e) (hWpos : ∀ k ∈ K, 0 < weight (W k) H)
    (hWmax : ∀ k ∈ K, ∀ e ∈ H, W k e ≤ η * weight (W k) H)
    (hWA : ∀ k ∈ K, ∀ i, weight (W k) (A i) ≤ β * weight (W k) H)
    (Bad : (Finset V → Fin q) → Prop) (πB : ℝ) (hBad : pProb (unif (Finset V) q) Bad ≤ πB)
    (hfail : ((H.biUnion id).card * p * q : ℝ) *
        Real.exp (-(t₃ ^ 2 / (2 * (1 * D₁ / q + 1 * t₃)))) +
      ((H.biUnion id).card ^ 2 * p * q : ℝ) *
        Real.exp (-(t₄ ^ 2 / (2 * (1 * C / q + 1 * t₄)))) +
      (K.card * p * q : ℝ) * Real.exp (-(γ ^ 2 / (2 * η * (β / q + γ)))) + πB < 1) :
    ∃ f : Finset V → Fin q,
      (∀ i j x, (degree (cls A f i j) x : ℝ) ≤ D₁ / q + t₃) ∧
      (∀ i j x y, x ≠ y → (codegree (cls A f i j) x y : ℝ) ≤ C / q + t₄) ∧
      (∀ k ∈ K, ∀ i j, weight (W k) (cls A f i j) ≤ β * weight (W k) H / q +
        γ * weight (W k) H) ∧ ¬ Bad f := by
  classical
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hP := unif_isPMF (ι := Finset V) q hq
  set U := H.biUnion id with hU
  set Sd : Fin p → V → Finset (Finset V) := fun i x => (A i).filter (fun e => x ∈ e)
  set Sc : Fin p → V × V → Finset (Finset V) :=
    fun i xy => (A i).filter (fun e => xy.1 ∈ e ∧ xy.2 ∈ e)
  have hdegS : ∀ i x (j : Fin q) (f : Finset V → Fin q), (degree (cls A f i j) x : ℝ) =
      cyl (Sd i x) (fun _ => 1) (fun e => {e}) j f := by
    intro i x j f
    rw [cyl_single_eq, sum_const, nsmul_eq_mul, mul_one]
    unfold degree cls
    congr 2
    ext e; simp only [Sd, mem_filter]; tauto
  have hcodS : ∀ i x y (j : Fin q) (f : Finset V → Fin q), (codegree (cls A f i j) x y : ℝ) =
      cyl (Sc i (x, y)) (fun _ => 1) (fun e => {e}) j f := by
    intro i x y j f
    rw [cyl_single_eq, sum_const, nsmul_eq_mul, mul_one]
    unfold codegree cls
    congr 2
    ext e; simp only [Sc, mem_filter]; tauto
  have hwS : ∀ k i (j : Fin q) (f : Finset V → Fin q), weight (W k) (cls A f i j) = cyl (A i) (W k) (fun e => {e}) j f := by
    intro k i j f
    rw [cyl_single_eq]; rfl
  set P3 := U ×ˢ ((univ : Finset (Fin p)) ×ˢ (univ : Finset (Fin q)))
  set P4 := (U ×ˢ U).filter (fun xy => xy.1 ≠ xy.2) ×ˢ
    ((univ : Finset (Fin p)) ×ˢ (univ : Finset (Fin q)))
  set P5 := K ×ˢ ((univ : Finset (Fin p)) ×ˢ (univ : Finset (Fin q)))
  set bad3 : (Finset V → Fin q) → Prop := fun f => ∃ a ∈ P3,
    t₃ ≤ cyl (Sd a.2.1 a.1) (fun _ => 1) (fun e => {e}) a.2.2 f -
      pE (unif (Finset V) q) (cyl (Sd a.2.1 a.1) (fun _ => 1) (fun e => {e}) a.2.2)
  set bad4 : (Finset V → Fin q) → Prop := fun f => ∃ a ∈ P4,
    t₄ ≤ cyl (Sc a.2.1 a.1) (fun _ => 1) (fun e => {e}) a.2.2 f -
      pE (unif (Finset V) q) (cyl (Sc a.2.1 a.1) (fun _ => 1) (fun e => {e}) a.2.2)
  set bad5 : (Finset V → Fin q) → Prop := fun f => ∃ a ∈ P5,
    γ * weight (W a.1) H ≤ cyl (A a.2.1) (W a.1) (fun e => {e}) a.2.2 f -
      pE (unif (Finset V) q) (cyl (A a.2.1) (W a.1) (fun e => {e}) a.2.2)
  have h3 : pProb (unif (Finset V) q) bad3 ≤
      (U.card * p * q : ℝ) * Real.exp (-(t₃ ^ 2 / (2 * (1 * D₁ / q + 1 * t₃)))) := by
    refine (pProb_exists_le hP _ _).trans ?_
    refine (sum_le_sum fun a _ => single_tail hq (Sd a.2.1 a.1) (fun _ => 1)
      (fun _ _ => zero_le_one) 1 D₁ one_pos (fun _ _ => le_rfl) ?_ a.2.2 t₃ ht₃).trans
      (le_of_eq ?_)
    · have := hdeg a.2.1 a.1
      unfold degree at this
      simpa [Sd] using this
    · rw [sum_const, card_product, card_product, card_univ, card_univ, Fintype.card_fin,
        Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  have h4 : pProb (unif (Finset V) q) bad4 ≤
      (U.card ^ 2 * p * q : ℝ) * Real.exp (-(t₄ ^ 2 / (2 * (1 * C / q + 1 * t₄)))) := by
    refine (pProb_exists_le hP _ _).trans ?_
    refine (sum_le_sum fun a ha => single_tail hq (Sc a.2.1 a.1) (fun _ => 1)
      (fun _ _ => zero_le_one) 1 C one_pos (fun _ _ => le_rfl) ?_ a.2.2 t₄ ht₄).trans ?_
    · have hne : a.1.1 ≠ a.1.2 := (mem_filter.mp (mem_product.mp ha).1).2
      have := hcod a.2.1 a.1.1 a.1.2 hne
      unfold codegree at this
      simpa [Sc] using this
    · rw [sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      rw [card_product, card_product, card_univ, card_univ, Fintype.card_fin,
        Fintype.card_fin]
      have : ((U ×ˢ U).filter (fun xy => xy.1 ≠ xy.2)).card ≤ U.card ^ 2 := by
        refine (card_filter_le _ _).trans ?_
        rw [card_product, sq]
      push_cast
      have h' : (((U ×ˢ U).filter (fun xy => xy.1 ≠ xy.2)).card : ℝ) ≤ U.card ^ 2 := by
        exact_mod_cast this
      have : (0 : ℝ) ≤ p * q := by positivity
      nlinarith
  have h5 : pProb (unif (Finset V) q) bad5 ≤
      (K.card * p * q : ℝ) * Real.exp (-(γ ^ 2 / (2 * η * (β / q + γ)))) := by
    refine (pProb_exists_le hP _ _).trans ?_
    refine (sum_le_sum (g := fun _ => Real.exp (-(γ ^ 2 / (2 * η * (β / q + γ)))))
      fun a ha => ?_).trans (le_of_eq ?_)
    · have hk := (mem_product.mp ha).1
      set ω := weight (W a.1) H
      have hω := hWpos a.1 hk
      have h := single_tail hq (A a.2.1) (W a.1) (fun e he => hW0 a.1 hk e (hA _ he))
        (η * ω) (β * ω) (by positivity) (fun e he => hWmax a.1 hk e (hA _ he))
        (hWA a.1 hk a.2.1) a.2.2 (γ * ω) (by positivity)
      refine h.trans (le_of_eq ?_)
      have : 0 < β + γ * q := by positivity
      have hω0 : ω ≠ 0 := hω.ne'
      congr 2
      field_simp
    · rw [sum_const, card_product, card_product, card_univ, card_univ, Fintype.card_fin,
        Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  have hall : pProb (unif (Finset V) q) (fun f => bad3 f ∨ bad4 f ∨ bad5 f ∨ Bad f) < 1 := by
    have := pProb_or_le hP bad3 (fun f => bad4 f ∨ bad5 f ∨ Bad f)
    have := pProb_or_le hP bad4 (fun f => bad5 f ∨ Bad f)
    have := pProb_or_le hP bad5 Bad
    linarith
  obtain ⟨f, _, hf⟩ := exists_of_pProb_lt_one hP hall
  simp only [not_or] at hf
  obtain ⟨n3, n4, n5, n6⟩ := hf
  refine ⟨f, fun i j x => ?_, fun i j x y hxy => ?_, fun k hk i j => ?_, n6⟩
  · by_cases hx : x ∈ U
    · have hn : ¬ (t₃ ≤ cyl (Sd i x) (fun _ => 1) (fun e => {e}) j f -
          pE (unif (Finset V) q) (cyl (Sd i x) (fun _ => 1) (fun e => {e}) j)) :=
        fun h => n3 ⟨(x, i, j), by simp [P3, hx], h⟩
      push_neg at hn
      rw [pE_cyl_single hq] at hn
      rw [hdegS]
      have hd := hdeg i x
      have : (∑ e ∈ Sd i x, (fun _ => (1 : ℝ)) e) = degree (A i) x := by
        simp only [sum_const, nsmul_eq_mul, mul_one]; rfl
      rw [this] at hn
      have : (degree (A i) x : ℝ) * (1 / q) ≤ D₁ / q := by
        rw [mul_one_div]; exact div_le_div_of_nonneg_right hd hqR.le
      linarith
    · rw [degree_eq_zero_of_not_mem_biUnion _ H ((cls_subset A f i j).trans (hA i)) hx]
      have : 0 ≤ D₁ := le_trans (by positivity) (hdeg i x)
      simp only [Nat.cast_zero]
      positivity
  · by_cases hU2 : x ∈ U ∧ y ∈ U
    · have hn : ¬ (t₄ ≤ cyl (Sc i (x, y)) (fun _ => 1) (fun e => {e}) j f -
          pE (unif (Finset V) q) (cyl (Sc i (x, y)) (fun _ => 1) (fun e => {e}) j)) :=
        fun h => n4 ⟨((x, y), i, j), by simp [P4, hU2.1, hU2.2, hxy], h⟩
      push_neg at hn
      rw [pE_cyl_single hq] at hn
      rw [hcodS]
      have hd := hcod i x y hxy
      have : (∑ e ∈ Sc i (x, y), (fun _ => (1 : ℝ)) e) = codegree (A i) x y := by
        simp only [sum_const, nsmul_eq_mul, mul_one]; rfl
      rw [this] at hn
      have : (codegree (A i) x y : ℝ) * (1 / q) ≤ C / q := by
        rw [mul_one_div]; exact div_le_div_of_nonneg_right hd hqR.le
      linarith
    · rw [not_and_or] at hU2
      rw [codegree_eq_zero_of_not_mem _ H ((cls_subset A f i j).trans (hA i)) hU2]
      have : 0 ≤ C := le_trans (by positivity) (hcod i x y hxy)
      simp only [Nat.cast_zero]
      positivity
  · have hn : ¬ (γ * weight (W k) H ≤ cyl (A i) (W k) (fun e => {e}) j f -
        pE (unif (Finset V) q) (cyl (A i) (W k) (fun e => {e}) j)) :=
      fun h => n5 ⟨(k, i, j), by simp [P5, hk], h⟩
    push_neg at hn
    rw [pE_cyl_single hq] at hn
    rw [hwS]
    have hb := hWA k hk i
    have : (∑ e ∈ A i, W k e) * (1 / q) ≤ β * weight (W k) H / q := by
      rw [mul_one_div]; exact div_le_div_of_nonneg_right hb hqR.le
    linarith

/-- **Step 2.** A random edge partition is good with positive probability. -/
theorem edge_partition {p q : ℕ} (hq : 0 < q) (H : Finset (Finset V))
    (A : Fin p → Finset (Finset V)) (hA : ∀ i, A i ⊆ H) (D₁ C t₃ t₄ : ℝ) (ht₃ : 0 < t₃)
    (ht₄ : 0 < t₄) (hdeg : ∀ i x, (degree (A i) x : ℝ) ≤ D₁)
    (hcod : ∀ i x y, x ≠ y → (codegree (A i) x y : ℝ) ≤ C)
    {ι : Type*} (W : ι → Finset V → ℝ) (K : Finset ι) (η β γ : ℝ) (hη : 0 < η) (hβ : 0 ≤ β) (hγ : 0 < γ)
    (hW0 : ∀ k ∈ K, ∀ e ∈ H, 0 ≤ W k e) (hWpos : ∀ k ∈ K, 0 < weight (W k) H)
    (hWmax : ∀ k ∈ K, ∀ e ∈ H, W k e ≤ η * weight (W k) H)
    (hWA : ∀ k ∈ K, ∀ i, weight (W k) (A i) ≤ β * weight (W k) H)
    (hfail : ((H.biUnion id).card * p * q : ℝ) *
        Real.exp (-(t₃ ^ 2 / (2 * (1 * D₁ / q + 1 * t₃)))) +
      ((H.biUnion id).card ^ 2 * p * q : ℝ) *
        Real.exp (-(t₄ ^ 2 / (2 * (1 * C / q + 1 * t₄)))) +
      (K.card * p * q : ℝ) * Real.exp (-(γ ^ 2 / (2 * η * (β / q + γ)))) < 1) :
    ∃ f : Finset V → Fin q,
      (∀ i j x, (degree (cls A f i j) x : ℝ) ≤ D₁ / q + t₃) ∧
      (∀ i j x y, x ≠ y → (codegree (cls A f i j) x y : ℝ) ≤ C / q + t₄) ∧
      ∀ k ∈ K, ∀ i j, weight (W k) (cls A f i j) ≤ β * weight (W k) H / q +
        γ * weight (W k) H := by
  classical
  obtain ⟨f, h1, h2, h3, -⟩ := edge_partition_ext hq H A hA D₁ C t₃ t₄ ht₃ ht₄ hdeg hcod W K
    η β γ hη hβ hγ hW0 hWpos hWmax hWA (fun _ => False) 0 (by unfold pProb pE; simp) (by linarith)
  exact ⟨f, h1, h2, h3⟩

end Pseudorandom

end FlattenedPS13

/- PseudorandomLib.Thinning -/
section FlattenedPS14
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/- # Thinning a random set of edges to exact marginals

If a random set of edges `M` contains every edge `e ∈ A` with probability at least `x`, then
deleting every edge `e` independently with a suitable probability produces a random subset
`N ⊆ M ∩ A` that contains every edge of `A` with probability exactly `x`.
-/

namespace Pseudorandom

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The marginal probability of an edge. -/
noncomputable def marg (μ : Finset (Finset V) → ℝ) (e : Finset V) : ℝ :=
  ∑ M, μ M * (if e ∈ M then 1 else 0)

/-- **Thinning.** -/
theorem thinning (A : Finset (Finset V)) (μ : Finset (Finset V) → ℝ) (hμ0 : ∀ M, 0 ≤ μ M)
    (hμ1 : ∑ M, μ M = 1) (x : ℝ) (hx0 : 0 ≤ x) (hmarg : ∀ e ∈ A, x ≤ marg μ e) :
    ∃ ν : Finset (Finset V) → ℝ, (∀ N, 0 ≤ ν N) ∧ ∑ N, ν N = 1 ∧
      (∀ N, ν N ≠ 0 → ∃ M, μ M ≠ 0 ∧ N ⊆ M ∧ N ⊆ A) ∧ ∀ e ∈ A, marg ν e = x := by
  classical
  -- keep probabilities
  set s : Finset V → ℝ := fun e => if e ∈ A then x / marg μ e else 0 with hs
  have hs0 : ∀ e, 0 ≤ s e := by
    intro e
    simp only [hs]
    split_ifs with he
    · exact div_nonneg hx0 (hx0.trans (hmarg e he))
    · exact le_rfl
  have hs1 : ∀ e, s e ≤ 1 := by
    intro e
    simp only [hs]
    split_ifs with he
    · rcases (hx0.trans (hmarg e he)).lt_or_eq with hpos | hzero
      · rw [div_le_one hpos]; exact hmarg e he
      · rw [← hzero, div_zero]; norm_num
    · norm_num
  set Pc : Finset V → Bool → ℝ := fun e b => if b then s e else 1 - s e with hPc
  have hP : IsPMF Pc := by
    refine ⟨fun e b => ?_, fun e => ?_⟩
    · simp only [hPc]; split_ifs
      · exact hs0 e
      · linarith [hs1 e]
    · simp [hPc]
  set thin : Finset (Finset V) → (Finset V → Bool) → Finset (Finset V) :=
    fun M c => M.filter (fun e => e ∈ A ∧ c e = true) with hthin
  set ν : Finset (Finset V) → ℝ :=
    fun N => ∑ M, μ M * pE Pc (fun c => if thin M c = N then 1 else 0) with hν
  refine ⟨ν, fun N => ?_, ?_, fun N hN => ?_, fun e he => ?_⟩
  · exact sum_nonneg fun M _ => mul_nonneg (hμ0 M)
      (pE_nonneg hP fun c => by split_ifs <;> norm_num)
  · simp only [hν]
    rw [sum_comm]
    conv_rhs => rw [← hμ1]
    refine sum_congr rfl fun M _ => ?_
    rw [← mul_sum, ← pE_sum]
    have : (fun c => ∑ N, (if thin M c = N then (1 : ℝ) else 0)) = fun _ => 1 := by
      funext c; simp
    rw [this, pE_const hP, mul_one]
  · obtain ⟨M, _, hM⟩ := exists_ne_zero_of_sum_ne_zero hN
    have hμM : μ M ≠ 0 := left_ne_zero_of_mul hM
    have hE := right_ne_zero_of_mul hM
    obtain ⟨c, _, hc⟩ := exists_ne_zero_of_sum_ne_zero hE
    have hc' := right_ne_zero_of_mul hc
    have hNc : thin M c = N := by by_contra h; exact hc' (if_neg h)
    refine ⟨M, hμM, ?_, ?_⟩
    · rw [← hNc]; exact filter_subset _ _
    · rw [← hNc]; intro f hf; exact (mem_filter.mp hf).2.1
  · unfold marg
    simp only [hν]
    simp_rw [sum_mul]
    rw [sum_comm]
    have key : ∀ M, ∑ N, μ M * pE Pc (fun c => if thin M c = N then (1 : ℝ) else 0) *
        (if e ∈ N then 1 else 0) = μ M * ((if e ∈ M then 1 else 0) * s e) := by
      intro M
      simp_rw [mul_assoc]
      rw [← mul_sum]
      congr 1
      have h1 : ∀ N, pE Pc (fun c => if thin M c = N then (1 : ℝ) else 0) *
          (if e ∈ N then 1 else 0) =
          pE Pc (fun c => (if thin M c = N then (1 : ℝ) else 0) * (if e ∈ N then 1 else 0)) := by
        intro N; rw [mul_comm, ← pE_const_mul]; congr 1; funext c; ring
      simp_rw [h1]
      rw [← pE_sum]
      have h2 : (fun c => ∑ N, (if thin M c = N then (1 : ℝ) else 0) *
          (if e ∈ N then 1 else 0)) = fun c => (if e ∈ M then 1 else 0) *
            (if c e = true then 1 else 0) := by
        funext c
        rw [sum_eq_single (thin M c)]
        · simp only [if_true, one_mul, hthin, mem_filter]
          by_cases heM : e ∈ M <;> by_cases hce : c e = true <;> simp [heM, hce, he]
        · intro N _ hN; rw [if_neg (Ne.symm hN), zero_mul]
        · intro h; exact absurd (mem_univ _) h
      rw [h2, pE_const_mul, pE_coord hP e (fun b => if b = true then (1 : ℝ) else 0)]
      simp [hPc]
    simp_rw [key]
    have : ∀ M, μ M * ((if e ∈ M then (1 : ℝ) else 0) * s e) =
        μ M * (if e ∈ M then 1 else 0) * s e := fun M => by ring
    simp_rw [this]
    rw [← sum_mul]
    change marg μ e * s e = x
    simp only [hs, if_pos he]
    rcases (hx0.trans (hmarg e he)).lt_or_eq with hpos | hzero
    · field_simp
    · have hx : x = 0 := le_antisymm (hzero ▸ hmarg e he) hx0
      rw [← hzero, hx]; simp

end Pseudorandom

end FlattenedPS14

/- PseudorandomLib.RandomMatching -/
section FlattenedPS15
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/- # Step 3: combining random matchings of the parts

We are given vertex-disjoint parts `i ∈ [p]`, each split into `q` edge classes `A i j`, and
for each class a random matching `N ⊆ A i j` that contains every edge of `A i j` with
probability exactly `x`. For every part independently we pick a uniformly random class `j`
and a random matching of that class. The union `M` is a matching, every edge of every class
is in `M` with probability `x / q`, and the weight of `M` is concentrated by the
bounded-differences inequality (one coordinate per part).
-/

namespace Pseudorandom

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- `ω(N ∩ A)` as a sum over `A`. -/
theorem weight_inter_eq (w : Finset V → ℝ) (N A : Finset (Finset V)) :
    weight w (N ∩ A) = ∑ e ∈ A, w e * (if e ∈ N then 1 else 0) := by
  classical
  unfold weight
  rw [inter_comm, ← filter_mem_eq_inter, sum_filter]
  refine sum_congr rfl fun e _ => ?_
  split_ifs <;> simp

/-- Expected weight of `N ∩ A` for a random `N` with exact marginals on `A`. -/
theorem sum_weight_inter (w : Finset V → ℝ) (A : Finset (Finset V))
    (ν : Finset (Finset V) → ℝ) (x : ℝ) (hmarg : ∀ e ∈ A, marg ν e = x) :
    ∑ N, ν N * weight w (N ∩ A) = x * weight w A := by
  simp_rw [weight_inter_eq, mul_sum]
  rw [sum_comm, weight, mul_sum]
  refine sum_congr rfl fun e he => ?_
  rw [← hmarg e he, marg, sum_mul]
  exact sum_congr rfl fun N _ => by ring

/-- **Step 3.** -/
theorem random_matching {p q : ℕ} (hq : 0 < q) (H : Finset (Finset V))
    (hne : ∀ e ∈ H, e.Nonempty)
    (A : Fin p → Fin q → Finset (Finset V)) (hAH : ∀ i j, A i j ⊆ H)
    (hdisj : ∀ i i', i ≠ i' → ∀ j j', ∀ e ∈ A i j, ∀ f ∈ A i' j', Disjoint e f)
    (ν : Fin p → Fin q → Finset (Finset V) → ℝ) (hν0 : ∀ i j N, 0 ≤ ν i j N)
    (hν1 : ∀ i j, ∑ N, ν i j N = 1)
    (hνsupp : ∀ i j N, ν i j N ≠ 0 → IsMatching N ∧ N ⊆ A i j)
    (x : ℝ) (hνmarg : ∀ i j, ∀ e ∈ A i j, marg (ν i j) e = x)
    {ι : Type*} (W : ι → Finset V → ℝ) (K : Finset ι) (hW0 : ∀ k ∈ K, ∀ e ∈ H, 0 ≤ W k e)
    (c t : ι → ℝ) (hc : ∀ k ∈ K, 0 < c k) (ht : ∀ k ∈ K, 0 < t k)
    (hcb : ∀ k ∈ K, ∀ i j, weight (W k) (A i j) ≤ c k)
    (hfail : ∑ k ∈ K, 2 * Real.exp (-(t k ^ 2 / (2 * (p * c k ^ 2 + c k * t k)))) < 1) :
    ∃ M ⊆ H, IsMatching M ∧ ∀ k ∈ K,
      |weight (W k) M - x / q * ∑ i, ∑ j, weight (W k) (A i j)| < t k := by
  classical
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  -- the product space
  set P : Fin p → Fin q × Finset (Finset V) → ℝ := fun i a => ν i a.1 a.2 / q with hPdef
  have hP : IsPMF P := by
    refine ⟨fun i a => div_nonneg (hν0 _ _ _) hqR.le, fun i => ?_⟩
    rw [Fintype.sum_prod_type]
    simp only [hPdef]
    simp_rw [← sum_div, hν1]
    simp [hqR.ne']
  set g : ι → Fin p → Fin q × Finset (Finset V) → ℝ :=
    fun k i a => weight (W k) (a.2 ∩ A i a.1) with hgdef
  set F : ι → (Fin p → Fin q × Finset (Finset V)) → ℝ := fun k ω => ∑ i, g k i (ω i)
    with hFdef
  set Mω : (Fin p → Fin q × Finset (Finset V)) → Finset (Finset V) :=
    fun ω => univ.biUnion (fun i => (ω i).2 ∩ A i (ω i).1) with hMdef
  -- basic facts
  have hg0 : ∀ k ∈ K, ∀ i a, 0 ≤ g k i a := fun k hk i a =>
    sum_nonneg fun e he => hW0 k hk e (hAH _ _ (mem_inter.mp he).2)
  have hgc : ∀ k ∈ K, ∀ i a, g k i a ≤ c k := by
    intro k hk i a
    refine le_trans ?_ (hcb k hk i a.1)
    exact sum_le_sum_of_subset_of_nonneg inter_subset_right
      fun e he _ => hW0 k hk e (hAH _ _ he)
  have hEF : ∀ k, pE P (F k) = x / q * ∑ i, ∑ j, weight (W k) (A i j) := by
    intro k
    simp only [hFdef]
    rw [pE_sum, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [pE_coord hP i (g k i), Fintype.sum_prod_type, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    simp only [hPdef, hgdef]
    have := sum_weight_inter (W k) (A i j) (ν i j) x (hνmarg i j)
    have e2 : ∑ N, ν i j N / q * weight (W k) (N ∩ A i j) =
        (∑ N, ν i j N * weight (W k) (N ∩ A i j)) / q := by
      rw [sum_div]; exact sum_congr rfl fun N _ => by ring
    rw [e2, this]; ring
  have hgap : ∀ k ∈ K, CoordGap (F k) (fun _ => c k) := by
    intro k hk i ω a b
    simp only [hFdef]
    rw [← sum_sub_distrib, sum_eq_single i]
    · simp only [Function.update_self]
      have h1 := hg0 k hk i a; have h2 := hg0 k hk i b
      have h3 := hgc k hk i a; have h4 := hgc k hk i b
      rw [abs_le]; constructor <;> linarith
    · intro i' _ hi'
      simp [Function.update_of_ne hi']
    · intro h; exact absurd (mem_univ i) h
  have hrare : ∀ k, CoordRare (F k) (fun _ => (univ : Finset (Fin q × Finset (Finset V)))) :=
    fun k i ω a b ha _ => absurd (mem_univ a) ha
  have hq1 : ∀ i, ∑ a ∈ (univ : Finset (Fin q × Finset (Finset V))), P i a ≤ 1 :=
    fun i => le_of_eq (hP.2 i)
  have htail : ∀ k ∈ K, pProb P (fun ω => t k ≤ F k ω - pE P (F k)) +
      pProb P (fun ω => t k ≤ pE P (F k) - F k ω) ≤
        2 * Real.exp (-(t k ^ 2 / (2 * (p * c k ^ 2 + c k * t k)))) := by
    intro k hk
    have hsum : (∑ _i : Fin p, (1 : ℝ) * c k ^ 2) = p * c k ^ 2 := by
      rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, one_mul]
    have h1 := pE_upper_tail P hP (F k) (fun _ => c k) (fun _ => 1) _ (c k) (hc k hk)
      (fun _ => ⟨(hc k hk).le, le_rfl⟩) (hgap k hk) (hrare k) hq1 (t k) (ht k hk)
    have h2 := pE_lower_tail P hP (F k) (fun _ => c k) (fun _ => 1) _ (c k) (hc k hk)
      (fun _ => ⟨(hc k hk).le, le_rfl⟩) (hgap k hk) (hrare k) hq1 (t k) (ht k hk)
    rw [hsum] at h1 h2
    linarith
  set bad : (Fin p → Fin q × Finset (Finset V)) → Prop := fun ω =>
    ∃ k ∈ K, t k ≤ F k ω - pE P (F k) ∨ t k ≤ pE P (F k) - F k ω
  have hbad : pProb P bad < 1 := by
    refine lt_of_le_of_lt ((pProb_exists_le hP K _).trans ?_) hfail
    exact sum_le_sum fun k hk => (pProb_or_le hP _ _).trans (htail k hk)
  obtain ⟨ω, hω, hgood⟩ := exists_of_pProb_lt_one hP hbad
  -- the outcome has positive weight in every coordinate
  have hpos : ∀ i, ν i (ω i).1 (ω i).2 ≠ 0 := by
    intro i h
    have : pw P ω = 0 := by
      unfold pw
      exact prod_eq_zero (mem_univ i) (by simp [hPdef, h])
    linarith
  have hsupp : ∀ i, IsMatching (ω i).2 ∧ (ω i).2 ⊆ A i (ω i).1 := fun i =>
    hνsupp i _ _ (hpos i)
  have hpd : ((univ : Finset (Fin p)) : Set (Fin p)).PairwiseDisjoint
      (fun i => (ω i).2 ∩ A i (ω i).1) := by
    intro i _ i' _ hii'
    rw [Function.onFun, Finset.disjoint_left]
    intro e he he'
    have h1 := (mem_inter.mp he).2
    have h2 := (mem_inter.mp he').2
    have := hdisj i i' hii' _ _ e h1 e h2
    rw [disjoint_self_iff_empty] at this
    exact (hne e (hAH _ _ h1)).ne_empty this
  have hweight : ∀ k, weight (W k) (Mω ω) = F k ω := by
    intro k
    simp only [hMdef, hFdef, hgdef, weight]
    rw [sum_biUnion hpd]
  refine ⟨Mω ω, ?_, ?_, fun k hk => ?_⟩
  · intro e he
    simp only [hMdef, mem_biUnion] at he
    obtain ⟨i, _, hi⟩ := he
    exact hAH _ _ (mem_inter.mp hi).2
  · intro e he f hf hef
    simp only [hMdef, mem_biUnion] at he hf
    obtain ⟨i, _, hi⟩ := he
    obtain ⟨i', _, hi'⟩ := hf
    by_cases hii : i = i'
    · subst hii
      exact (hsupp i).1 e (mem_inter.mp hi).1 f (mem_inter.mp hi').1 hef
    · exact hdisj i i' hii _ _ e (mem_inter.mp hi).2 f (mem_inter.mp hi').2
  · rw [hweight, ← hEF k, abs_sub_lt_iff]
    have h1 : ¬ (t k ≤ F k ω - pE P (F k)) := fun h => hgood ⟨k, hk, Or.inl h⟩
    have h2 : ¬ (t k ≤ pE P (F k) - F k ω) := fun h => hgood ⟨k, hk, Or.inr h⟩
    push_neg at h1 h2
    exact ⟨h1, h2⟩

end Pseudorandom

end FlattenedPS15

/- PseudorandomLib.Numerics12 -/
section FlattenedPS16
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/- # Numerical estimates for the proof of Theorem 1.2

Each lemma bounds one of the exponents appearing in the failure probabilities of Steps 1–3
from below by `Δ^ε / 64`.
-/

namespace Pseudorandom

theorem rpow_sq' {Δ : ℝ} (hΔ : 0 < Δ) (x : ℝ) : (Δ ^ x) ^ 2 = Δ ^ (2 * x) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hΔ.le]; norm_num; ring_nf

/-- Degrees in Step 1. -/
theorem e2_bound {Δ ε δ ξ C P p X : ℝ} (r : ℕ) (hΔ : 0 < Δ) (hξ : ξ = Δ ^ (-(2 * ε)))
    (hξ1 : ξ ≤ 1) (hC : C = Δ ^ (1 - δ)) (hp1 : 1 ≤ p) (hP1 : 1 ≤ P)
    (hPX : P ^ 2 ≤ X ^ (2 * r))
    (h5 : 128 * (r + 1) * X ^ (2 * r) * Δ ^ ε ≤ Δ ^ (δ - 4 * ε)) :
    Δ ^ ε / 64 ≤ ξ ^ 2 * Δ / (2 * C * (r * P ^ 2 / p + ξ * P)) := by
  have hξ0 : 0 < ξ := by rw [hξ]; exact Real.rpow_pos_of_pos hΔ _
  have hC0 : 0 < C := by rw [hC]; exact Real.rpow_pos_of_pos hΔ _
  have hid : ξ ^ 2 * Δ / C = Δ ^ (δ - 4 * ε) := by
    rw [hξ, hC, rpow_sq' hΔ, div_eq_iff (Real.rpow_pos_of_pos hΔ _).ne',
      ← Real.rpow_add_one hΔ.ne', ← Real.rpow_add hΔ]; ring_nf
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hden : r * P ^ 2 / p + ξ * P ≤ (r + 1) * X ^ (2 * r) := by
    have h1 : r * P ^ 2 / p ≤ r * P ^ 2 := div_le_self (by positivity) hp1
    have h2 : ξ * P ≤ P ^ 2 := by nlinarith
    nlinarith
  have hpos : 0 < r * P ^ 2 / p + ξ * P := by positivity
  have hX : 0 < X ^ (2 * r) := lt_of_lt_of_le (by positivity) hPX
  have hεp : 0 < Δ ^ ε := Real.rpow_pos_of_pos hΔ _
  calc Δ ^ ε / 64 ≤ 64 * Δ ^ ε := by linarith
    _ = 128 * (r + 1) * X ^ (2 * r) * Δ ^ ε / (2 * ((r + 1) * X ^ (2 * r))) := by
        field_simp; ring
    _ ≤ Δ ^ (δ - 4 * ε) / (2 * ((r + 1) * X ^ (2 * r))) := by gcongr
    _ ≤ Δ ^ (δ - 4 * ε) / (2 * (r * P ^ 2 / p + ξ * P)) := by
        gcongr
    _ = ξ ^ 2 * Δ / (2 * C * (r * P ^ 2 / p + ξ * P)) := by
        rw [← hid]; field_simp

/-- Weights in Step 1. -/
theorem e1_bound {Δ ε δ ξ η p X : ℝ} (r : ℕ) (hΔ : 0 < Δ) (hξ : ξ = Δ ^ (-(2 * ε)))
    (hξ1 : ξ ≤ 1) (hη : η = Δ ^ (-(1 + δ))) (hp1 : 1 ≤ p)
    (hpX : (p ^ r) ^ 2 ≤ X ^ (2 * r))
    (h5 : 128 * (r + 1) * X ^ (2 * r) * Δ ^ ε ≤ Δ ^ (δ - 4 * ε)) :
    Δ ^ ε / 64 ≤ ξ ^ 2 / (2 * Δ * η * (r * (p ^ r) ^ 2 / p + ξ * p ^ r)) := by
  have hξ0 : 0 < ξ := by rw [hξ]; exact Real.rpow_pos_of_pos hΔ _
  have hη0 : 0 < η := by rw [hη]; exact Real.rpow_pos_of_pos hΔ _
  have hid : ξ ^ 2 / (Δ * η) = Δ ^ (δ - 4 * ε) := by
    rw [hξ, hη, rpow_sq' hΔ, div_eq_iff (by positivity), mul_comm Δ,
      ← Real.rpow_add_one hΔ.ne', ← Real.rpow_add hΔ]; ring_nf
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hpr : 1 ≤ p ^ r := one_le_pow₀ hp1
  have hden : r * (p ^ r) ^ 2 / p + ξ * p ^ r ≤ (r + 1) * X ^ (2 * r) := by
    have h1 : r * (p ^ r) ^ 2 / p ≤ r * (p ^ r) ^ 2 := div_le_self (by positivity) hp1
    have h2 : ξ * p ^ r ≤ (p ^ r) ^ 2 := by nlinarith
    nlinarith
  have hpos : 0 < r * (p ^ r) ^ 2 / p + ξ * p ^ r := by positivity
  have hX : 0 < X ^ (2 * r) := lt_of_lt_of_le (by positivity) hpX
  have hεp : 0 < Δ ^ ε := Real.rpow_pos_of_pos hΔ _
  calc Δ ^ ε / 64 ≤ 64 * Δ ^ ε := by linarith
    _ = 128 * (r + 1) * X ^ (2 * r) * Δ ^ ε / (2 * ((r + 1) * X ^ (2 * r))) := by
        field_simp; ring
    _ ≤ Δ ^ (δ - 4 * ε) / (2 * ((r + 1) * X ^ (2 * r))) := by gcongr
    _ ≤ Δ ^ (δ - 4 * ε) / (2 * (r * (p ^ r) ^ 2 / p + ξ * p ^ r)) := by
        gcongr
    _ = ξ ^ 2 / (2 * Δ * η * (r * (p ^ r) ^ 2 / p + ξ * p ^ r)) := by
        rw [← hid]; field_simp

/-- Degrees in Step 2. -/
theorem e3_bound {Δ ε a ξ m : ℝ} (hΔ : 1 ≤ Δ) (hξ : ξ = Δ ^ (-(2 * ε)))
    (hξ1 : ξ ≤ 1 / 2) (hm : Δ ^ a / 2 ≤ m) (ha : 5 * ε ≤ a) :
    Δ ^ ε / 64 ≤ (ξ * m) ^ 2 / (2 * (1 * ((1 + ξ) * m) + 1 * (ξ * m))) := by
  have hΔ0 : 0 < Δ := by linarith
  have hξ0 : 0 < ξ := by rw [hξ]; exact Real.rpow_pos_of_pos hΔ0 _
  have hm0 : 0 < m := lt_of_lt_of_le (by positivity) hm
  have heq : (ξ * m) ^ 2 / (2 * (1 * ((1 + ξ) * m) + 1 * (ξ * m))) =
      ξ ^ 2 * m / (2 * (1 + 2 * ξ)) := by
    field_simp; ring
  rw [heq]
  have hid : ξ ^ 2 * Δ ^ a = Δ ^ (a - 4 * ε) := by
    rw [hξ, rpow_sq' hΔ0, ← Real.rpow_add hΔ0]; ring_nf
  have hpow : Δ ^ ε ≤ Δ ^ (a - 4 * ε) := Real.rpow_le_rpow_of_exponent_le hΔ (by linarith)
  have h1 : ξ ^ 2 * (Δ ^ a / 2) ≤ ξ ^ 2 * m := by gcongr
  rw [le_div_iff₀ (by positivity)]
  have h2 : 2 * (1 + 2 * ξ) ≤ 4 := by linarith
  have : 0 ≤ ξ ^ 2 * m := by positivity
  nlinarith

/-- Codegrees in Step 2. -/
theorem e4_bound {Δ ε c t : ℝ} (hΔ : 0 < Δ) (ht : t = Δ ^ ε / 2) (hc0 : 0 ≤ c) (hct : c ≤ t) :
    Δ ^ ε / 64 ≤ t ^ 2 / (2 * (1 * c + 1 * t)) := by
  have ht0 : 0 < t := by rw [ht]; have := Real.rpow_pos_of_pos hΔ ε; positivity
  rw [le_div_iff₀ (by positivity)]
  have : Δ ^ ε = 2 * t := by rw [ht]; ring
  rw [this]
  nlinarith

/-- Weights in Step 2. -/
theorem e5_bound {Δ ε ξ η β γ q pr : ℝ} (hΔ : 0 < Δ) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 2)
    (hη : 0 < η) (hq : 0 < q) (hpr : 0 < pr) (hβ : β = (1 + ξ) / pr) (hγ : γ = 1 / (2 * q * pr))
    (hηqp : η * (q * pr) ≤ 4 * Δ ^ (-ε)) :
    Δ ^ ε / 64 ≤ γ ^ 2 / (2 * η * (β / q + γ)) := by
  have hu : β / q + γ ≤ 2 / (q * pr) := by
    have : β / q + γ = (3 + 2 * ξ) / (2 * (q * pr)) := by rw [hβ, hγ]; field_simp; ring
    rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hq hpr]
  have hu0 : 0 < β / q + γ := by rw [hβ, hγ]; positivity
  have hneg : Δ ^ (-ε) = 1 / Δ ^ ε := by rw [Real.rpow_neg hΔ.le, one_div]
  have hεp : 0 < Δ ^ ε := Real.rpow_pos_of_pos hΔ _
  rw [hneg] at hηqp
  have hkey : η * (q * pr) * Δ ^ ε ≤ 4 := by
    calc η * (q * pr) * Δ ^ ε ≤ 4 * (1 / Δ ^ ε) * Δ ^ ε :=
          mul_le_mul_of_nonneg_right hηqp hεp.le
      _ = 4 := by field_simp
  rw [le_div_iff₀ (by positivity)]
  calc Δ ^ ε / 64 * (2 * η * (β / q + γ)) ≤ Δ ^ ε / 64 * (2 * η * (2 / (q * pr))) := by
        gcongr
    _ = (η * (q * pr) * Δ ^ ε) / (16 * (q * pr) ^ 2) := by field_simp; ring
    _ ≤ 4 / (16 * (q * pr) ^ 2) := by gcongr
    _ = γ ^ 2 := by rw [hγ]; field_simp; ring

/-- Concentration in Step 3. -/
theorem e6_bound {Δ ε a b ξ β γ q p P ω Y : ℝ} (r : ℕ) (hΔ : 1 ≤ Δ) (hξ0 : 0 ≤ ξ)
    (hξ1 : ξ ≤ 1 / 2) (hε : 0 ≤ ε) (ha : 0 ≤ a) (hq : 0 < q) (hp : Δ ^ b ≤ p) (hP : 0 < P) (hY : Y = Δ ^ (1 - a))
    (hqP : Y ≤ q * P) (hpr : p ^ r = p * P) (hβ : β = (1 + ξ) / p ^ r)
    (hγ : γ = 1 / (2 * q * p ^ r)) (hb : b = 2 * a + 3 * ε) (hω : 0 < ω) :
    Δ ^ ε / 64 ≤ (Δ ^ (-ε) * ω / (2 * Δ)) ^ 2 /
      (2 * (p * ((β / q + γ) * ω) ^ 2 + (β / q + γ) * ω * (Δ ^ (-ε) * ω / (2 * Δ)))) := by
  have hΔ0 : 0 < Δ := by linarith
  have hp0 : 0 < p := lt_of_lt_of_le (Real.rpow_pos_of_pos hΔ0 _) hp
  have hY0 : 0 < Y := by rw [hY]; exact Real.rpow_pos_of_pos hΔ0 _
  set s := Δ ^ (-ε) / (2 * Δ) with hs
  have hs0 : 0 < s := by positivity
  set u := β / q + γ with hudef
  have hu0 : 0 < u := by rw [hudef, hβ, hγ]; positivity
  have hpr0 : 0 < p ^ r := by positivity
  have hu : u ≤ 2 / (q * (p * P)) := by
    have : u = (3 + 2 * ξ) / (2 * (q * (p * P))) := by
      rw [hudef, hβ, hγ, hpr]; field_simp; ring
    rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 < q * (p * P) := by positivity
    nlinarith
  -- reduce to `ω`-free statement
  have hred : (Δ ^ (-ε) * ω / (2 * Δ)) ^ 2 /
      (2 * (p * (u * ω) ^ 2 + u * ω * (Δ ^ (-ε) * ω / (2 * Δ)))) =
      s ^ 2 / (2 * (p * u ^ 2 + u * s)) := by
    have hsω : Δ ^ (-ε) * ω / (2 * Δ) = s * ω := by rw [hs]; ring
    rw [hsω, show (s * ω) ^ 2 = s ^ 2 * ω ^ 2 by ring,
      show 2 * (p * (u * ω) ^ 2 + u * ω * (s * ω)) = 2 * (p * u ^ 2 + u * s) * ω ^ 2 by ring,
      mul_div_mul_right _ _ (by positivity)]
  rw [hred]
  -- the key powers
  have hsY_eq : s * Y = Δ ^ (-ε - a) / 2 := by
    have e : Δ ^ (-ε) * Δ ^ (1 - a) = Δ ^ (-ε - a) * Δ := by
      rw [← Real.rpow_add hΔ0, ← Real.rpow_add_one hΔ0.ne']; ring_nf
    rw [hs, hY, div_mul_eq_mul_div, e]
    field_simp
  have hsY : s * Y ≤ 1 / 2 := by
    rw [hsY_eq]
    have : Δ ^ (-ε - a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hΔ (by linarith)
    linarith
  have hB : s ^ 2 * (Y ^ 2 * Δ ^ b) = Δ ^ ε / 4 := by
    have : s ^ 2 * (Y ^ 2 * Δ ^ b) = (s * Y) ^ 2 * Δ ^ b := by ring
    rw [this, hsY_eq, div_pow, rpow_sq' hΔ0, div_mul_eq_mul_div, ← Real.rpow_add hΔ0, hb]
    ring_nf
  set w := u * (q * (p * P)) with hw
  have hw2 : w ≤ 2 := by
    rw [hw]; rwa [le_div_iff₀ (by positivity)] at hu
  have hw0 : 0 ≤ w := by positivity
  have hZ : Y ^ 2 * Δ ^ b ≤ (q * P) ^ 2 * p := by
    have h1 : Y ^ 2 ≤ (q * P) ^ 2 := by gcongr
    have : 0 ≤ Δ ^ b := (Real.rpow_pos_of_pos hΔ0 _).le
    calc Y ^ 2 * Δ ^ b ≤ (q * P) ^ 2 * Δ ^ b := by gcongr
      _ ≤ (q * P) ^ 2 * p := by gcongr
  have hA : (p * u ^ 2 + u * s) * (Y ^ 2 * Δ ^ b) ≤ 5 := by
    have h1 : p * u ^ 2 * (Y ^ 2 * Δ ^ b) ≤ w ^ 2 := by
      calc p * u ^ 2 * (Y ^ 2 * Δ ^ b) ≤ p * u ^ 2 * ((q * P) ^ 2 * p) := by gcongr
        _ = w ^ 2 := by rw [hw]; ring
    have h2 : u * s * (Y ^ 2 * Δ ^ b) ≤ w * (s * Y) := by
      have : Y * Δ ^ b ≤ (q * P) * p := by
        have : 0 ≤ Δ ^ b := (Real.rpow_pos_of_pos hΔ0 _).le
        calc Y * Δ ^ b ≤ (q * P) * Δ ^ b := by gcongr
          _ ≤ (q * P) * p := by gcongr
      calc u * s * (Y ^ 2 * Δ ^ b) = u * s * Y * (Y * Δ ^ b) := by ring
        _ ≤ u * s * Y * ((q * P) * p) := by gcongr
        _ = w * (s * Y) := by rw [hw]; ring
    have h3 : w * (s * Y) ≤ 2 * (1 / 2) := by
      apply mul_le_mul hw2 hsY (by positivity) (by norm_num)
    have hw4 : w ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ hw0 hw2 2
    have : (p * u ^ 2 + u * s) * (Y ^ 2 * Δ ^ b) =
        p * u ^ 2 * (Y ^ 2 * Δ ^ b) + u * s * (Y ^ 2 * Δ ^ b) := by ring
    linarith
  have hZ0 : 0 < Y ^ 2 * Δ ^ b := by
    have := Real.rpow_pos_of_pos hΔ0 b; positivity
  have hεp : 0 < Δ ^ ε := Real.rpow_pos_of_pos hΔ0 _
  have hden0 : 0 < 2 * (p * u ^ 2 + u * s) := by positivity
  rw [le_div_iff₀ hden0]
  refine le_of_mul_le_mul_right ?_ hZ0
  rw [hB]
  have := mul_le_mul_of_nonneg_left hA (show 0 ≤ Δ ^ ε / 32 by positivity)
  calc Δ ^ ε / 64 * (2 * (p * u ^ 2 + u * s)) * (Y ^ 2 * Δ ^ b) =
        Δ ^ ε / 32 * ((p * u ^ 2 + u * s) * (Y ^ 2 * Δ ^ b)) := by ring
    _ ≤ Δ ^ ε / 32 * 5 := this
    _ ≤ Δ ^ ε / 4 := by linarith

end Pseudorandom

end FlattenedPS16

/- PseudorandomLib.Assembly12 -/
section FlattenedPS17
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/- # Assembling the proof of Theorem 1.2

`core_1_2` carries out Steps 1–3 for a fixed (large) `Δ` satisfying the numerical conditions
collected in `Facts12`. The nibble theorem enters as the hypothesis `hnib`.
-/

namespace Pseudorandom

open Finset

/-- The numerical conditions on `Δ`. -/
structure Facts12 (r : ℕ) (δ ε a b ρ κ σ D₀ D : ℝ) : Prop where
  h1 : 2 ≤ D
  h2 : (2 * D ^ b) ^ (r - 1) ≤ D ^ (1 - a)
  h3 : 2 * (2 * D ^ b) ^ (r - 1) * D ^ (a - δ) ≤ D ^ ε
  h4 : D ^ (-(2 * ε)) ≤ 1 / 2
  h5 : 128 * (r + 1) * (2 * D ^ b) ^ (2 * r) * D ^ ε ≤ D ^ (δ - 4 * ε)
  h6 : 64 * r ^ 2 * D ^ 2 * Real.exp (2 * D ^ (ε ^ 2) - D ^ ε / 64) < 1
  h7 : D₀ ≤ D ^ a / 2
  h8 : D ^ ε ≤ (D ^ a / 2) ^ κ
  h9 : D ^ (ε ^ 2) ≤ (D ^ a / 2) ^ σ
  h10 : (D ^ a / 2) ^ (-ρ) + 4 * D ^ (-(2 * ε)) ≤ D ^ (-ε) / 2
  h11 : 1 ≤ D ^ a / 2

theorem num_aux1 {r Δ e : ℝ} (hr : 2 ≤ r) (hΔ : 1 ≤ Δ) (he : 1 ≤ e) :
    (r * e + 2 * e) * (2 * Δ) ≤ 64 * r ^ 2 * Δ ^ 2 * (e * e) := by
  have h1 : r * e + 2 * e ≤ 2 * r * e := by nlinarith
  have h2 : e ≤ e * e := by nlinarith
  have h3 : Δ ≤ Δ ^ 2 := by nlinarith
  have h4 : r ≤ r ^ 2 := by nlinarith
  calc (r * e + 2 * e) * (2 * Δ) ≤ 2 * r * e * (2 * Δ) := by gcongr
    _ = 4 * (r * (e * Δ)) := by ring
    _ ≤ 64 * (r ^ 2 * ((e * e) * Δ ^ 2)) := by
        have : r * (e * Δ) ≤ r ^ 2 * ((e * e) * Δ ^ 2) :=
          mul_le_mul h4 (mul_le_mul h2 h3 (by linarith) (by nlinarith)) (by nlinarith)
            (by nlinarith)
        have : 0 ≤ r * (e * Δ) := mul_nonneg (by linarith) (by nlinarith)
        linarith
    _ = 64 * r ^ 2 * Δ ^ 2 * (e * e) := by ring

theorem num_aux2 {r Δ e : ℝ} (hr : 2 ≤ r) (hΔ : 1 ≤ Δ) (he : 1 ≤ e) :
    r * e * (2 * Δ) * (2 * Δ) + (r * e) ^ 2 * (2 * Δ) * (2 * Δ) + e * (2 * Δ) * (2 * Δ) ≤
      64 * r ^ 2 * Δ ^ 2 * (e * e) := by
  have h2 : e ≤ e * e := by nlinarith
  have h4 : r ≤ r ^ 2 := by nlinarith
  have h5 : r * e ≤ r ^ 2 * (e * e) := mul_le_mul h4 h2 (by linarith) (by nlinarith)
  have h6 : e ≤ r ^ 2 * (e * e) := by nlinarith
  have hΔ2 : 0 ≤ Δ ^ 2 := by positivity
  have : r * e * (2 * Δ) * (2 * Δ) + (r * e) ^ 2 * (2 * Δ) * (2 * Δ) + e * (2 * Δ) * (2 * Δ) =
      4 * Δ ^ 2 * (r * e + r ^ 2 * (e * e) + e) := by ring
  rw [this]
  have : r * e + r ^ 2 * (e * e) + e ≤ 3 * (r ^ 2 * (e * e)) := by linarith
  nlinarith

theorem num_aux3 {r Δ e : ℝ} (hr : 2 ≤ r) (hΔ : 1 ≤ Δ) (he : 1 ≤ e) :
    2 * e ≤ 64 * r ^ 2 * Δ ^ 2 * (e * e) := by
  have h2 : e ≤ e * e := by nlinarith
  have h1 : 1 ≤ r ^ 2 * Δ ^ 2 := by
    have hr1 : 1 ≤ r ^ 2 := by nlinarith
    have hD1 : 1 ≤ Δ ^ 2 := by nlinarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ r ^ 2 * Δ ^ 2 := mul_le_mul hr1 hD1 zero_le_one (by linarith)
  have h3 : e * e ≤ r ^ 2 * Δ ^ 2 * (e * e) := le_mul_of_one_le_left (by nlinarith) h1
  calc 2 * e ≤ 64 * (e * e) := by linarith
    _ ≤ 64 * (r ^ 2 * Δ ^ 2 * (e * e)) := by linarith
    _ = 64 * r ^ 2 * Δ ^ 2 * (e * e) := by ring

/-- The final comparison of expectations. -/
theorem final_estimate {ω wM S P Δ ξ ν Dt q x₀ e : ℝ} (hω : 0 < ω) (hΔ : 0 < Δ) (hξ0 : 0 ≤ ξ)
    (hξ1 : ξ ≤ 1 / 2) (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (hP : 0 < P) (hq : 0 < q) (hDt : 0 < Dt)
    (hDtq : q * Dt = (1 + 2 * ξ) * Δ / P) (hx₀ : x₀ = (1 - ν) / Dt)
    (hS : |S - ω / P| ≤ ξ * (ω / P)) (hM : |wM - x₀ / q * S| < e * ω / (2 * Δ))
    (hsmall : ν + 4 * ξ ≤ e / 2) :
    |wM - ω / Δ| ≤ e * (ω / Δ) := by
  have hE : x₀ / q * S = (1 - ν) * (S * P) / ((1 + 2 * ξ) * Δ) := by
    have : Dt = (1 + 2 * ξ) * Δ / P / q := by rw [← hDtq]; field_simp
    rw [hx₀, this]; field_simp
  rw [abs_le] at hS
  have hZ1 : (1 - ξ) * ω ≤ S * P := by
    have := mul_le_mul_of_nonneg_right hS.1 hP.le
    have e1 : (ω / P - ξ * (ω / P)) * P = (1 - ξ) * ω := by field_simp
    nlinarith [this]
  have hZ2 : S * P ≤ (1 + ξ) * ω := by
    have := mul_le_mul_of_nonneg_right hS.2 hP.le
    have e1 : (ω / P + ξ * (ω / P)) * P = (1 + ξ) * ω := by field_simp
    nlinarith [this]
  have hden : 0 < (1 + 2 * ξ) * Δ := by positivity
  have hup : x₀ / q * S ≤ ω / Δ := by
    rw [hE, div_le_div_iff₀ hden hΔ]
    have h1 : (1 - ν) * (S * P) ≤ 1 * ((1 + ξ) * ω) := by
      apply mul_le_mul (by linarith) hZ2 _ zero_le_one
      nlinarith
    nlinarith
  have hlo : (1 - ν - 3 * ξ) * (ω / Δ) ≤ x₀ / q * S := by
    rw [hE, mul_div_assoc', div_le_div_iff₀ hΔ hden]
    have h1 : (1 - ν) * ((1 - ξ) * ω) ≤ (1 - ν) * (S * P) :=
      mul_le_mul_of_nonneg_left hZ1 (by linarith)
    have h2 : (1 - ν - 3 * ξ) * (1 + 2 * ξ) ≤ (1 - ν) * (1 - ξ) := by nlinarith
    have hωΔ : 0 < ω * Δ := by positivity
    nlinarith
  rw [abs_lt] at hM
  rw [abs_le]
  have hωΔ : 0 < ω / Δ := by positivity
  have hsplit : e * ω / (2 * Δ) = e / 2 * (ω / Δ) := by ring
  rw [hsplit] at hM
  constructor
  · nlinarith
  · nlinarith

set_option maxHeartbeats 4000000 in
/-- Steps 1–3 of the proof of Theorem 1.2 for a fixed `Δ`. -/
theorem core_1_2 (r : ℕ) (hr : 2 ≤ r) (δ ε a b ρ κ σ D₀ : ℝ) (hε : 0 < ε) (ha0 : 0 < a)
    (hb : b = 2 * a + 3 * ε) (hb1 : b ≤ 1) (ha5 : 5 * ε ≤ a)
    (hδa : a + 4 * ε ≤ δ) (hρ : 0 ≤ ρ) (hκ : 0 ≤ κ) (hσ : 0 ≤ σ)
    (hnib : ∀ D : ℝ, D₀ ≤ D → ∀ (V : Type) [Fintype V] [DecidableEq V]
      (H : Finset (Finset V)), IsUniform H r → (∀ v, (degree H v : ℝ) ≤ D) →
      (∀ u w, u ≠ w → (codegree H u w : ℝ) ≤ D ^ κ) → (H.card : ℝ) ≤ Real.exp (D ^ σ) →
      ∃ μ : Finset (Finset V) → ℝ, (∀ M, 0 ≤ μ M) ∧ ∑ M, μ M = 1 ∧
        (∀ M, μ M ≠ 0 → IsMatching M ∧ M ⊆ H) ∧
        ∀ e ∈ H, (1 - D ^ (-ρ)) / D ≤ ∑ M, μ M * (if e ∈ M then 1 else 0))
    (Δ : ℝ) (F : Facts12 r δ ε a b ρ κ σ D₀ Δ)
    (V : Type) [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (huni : IsUniform H r)
    (hdeg : ∀ v, (degree H v : ℝ) ≤ Δ)
    (hcod : ∀ u v, u ≠ v → (codegree H u v : ℝ) ≤ Δ ^ (1 - δ))
    (hcard : (H.card : ℝ) ≤ Real.exp (Δ ^ (ε ^ 2)))
    (ι : Type) [Fintype ι] (W : ι → Finset V → ℝ) (hW0 : ∀ k, ∀ e ∈ H, 0 ≤ W k e)
    (hι : (Fintype.card ι : ℝ) ≤ Real.exp (Δ ^ (ε ^ 2))) :
    ∃ M ⊆ H, IsMatching M ∧
      ∀ k, (∀ e ∈ H, W k e * Δ ^ (1 + δ) ≤ weight (W k) H) →
        |weight (W k) M - weight (W k) H / Δ| ≤ Δ ^ (-ε) * (weight (W k) H / Δ) := by
  classical
  have hD2 := F.h1
  have hD0 : 0 < Δ := by linarith
  have hD1 : 1 ≤ Δ := by linarith
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  set ξ : ℝ := Δ ^ (-(2 * ε)) with hξ
  have hξ0 : 0 < ξ := Real.rpow_pos_of_pos hD0 _
  have hξ1 : ξ ≤ 1 / 2 := F.h4
  set C : ℝ := Δ ^ (1 - δ) with hC
  have hC0 : 0 < C := Real.rpow_pos_of_pos hD0 _
  set η : ℝ := Δ ^ (-(1 + δ)) with hη
  have hη0 : 0 < η := Real.rpow_pos_of_pos hD0 _
  set Xb : ℝ := 2 * Δ ^ b with hXb
  have hDb1 : 1 ≤ Δ ^ b := Real.one_le_rpow hD1 (by linarith)
  have hDbD : Δ ^ b ≤ Δ := by
    simpa using Real.rpow_le_rpow_of_exponent_le hD1 hb1
  have hXb1 : 1 ≤ Xb := by rw [hXb]; linarith
  -- the number of parts
  set p : ℕ := ⌈Δ ^ b⌉₊ with hpdef
  have hp_ge : Δ ^ b ≤ p := Nat.le_ceil _
  have hp_le : (p : ℝ) ≤ Xb := by
    have := Nat.ceil_lt_add_one (show 0 ≤ Δ ^ b by linarith)
    rw [hXb]; linarith
  have hp1 : (1 : ℝ) ≤ p := hDb1.trans hp_ge
  have hp0 : 0 < p := by exact_mod_cast (lt_of_lt_of_le one_pos hp1)
  have hpD : (p : ℝ) ≤ 2 * Δ := by rw [hXb] at hp_le; linarith
  set P : ℝ := (p : ℝ) ^ (r - 1) with hPdef
  have hP1 : 1 ≤ P := one_le_pow₀ hp1
  have hPX : P ≤ Xb ^ (r - 1) := pow_le_pow_left₀ (by linarith) hp_le _
  set Y : ℝ := Δ ^ (1 - a) with hY
  have hPY : P ≤ Y := hPX.trans F.h2
  have hY1 : 1 ≤ Y := hP1.trans hPY
  have hpr : (p : ℝ) ^ r = p * P := by
    rw [hPdef, ← pow_succ']; congr 1; omega
  -- the number of edge classes
  set q : ℕ := ⌈Y / P⌉₊ with hqdef
  have hq_ge : Y / P ≤ q := Nat.le_ceil _
  have hq0 : 0 < q := Nat.ceil_pos.mpr (by positivity)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hqP_ge : Y ≤ q * P := by rwa [div_le_iff₀ (by linarith)] at hq_ge
  have hqP_le : q * P ≤ 2 * Y := by
    have := Nat.ceil_lt_add_one (show 0 ≤ Y / P by positivity)
    rw [← hqdef] at this
    have h2 : (q : ℝ) * P < (Y / P + 1) * P := mul_lt_mul_of_pos_right this (by linarith)
    rw [add_mul, div_mul_cancel₀ _ (by linarith), one_mul] at h2
    linarith
  have hYD : Y ≤ Δ := by
    simpa using Real.rpow_le_rpow_of_exponent_le hD1 (show 1 - a ≤ 1 by linarith)
  have hq_le : (q : ℝ) ≤ 2 * Δ := by
    have : (q : ℝ) ≤ q * P := le_mul_of_one_le_right hqR.le hP1
    linarith
  -- the hypergraph
  have hne : ∀ e ∈ H, e.Nonempty := fun e he => by rw [← card_pos, huni e he]; omega
  set U := H.biUnion id with hU
  set X₀ : ℝ := Δ ^ (ε ^ 2) with hX₀
  set Y₀ : ℝ := Δ ^ ε / 64 with hY₀
  have heX : 1 ≤ Real.exp X₀ := Real.one_le_exp (Real.rpow_pos_of_pos hD0 _).le
  have hUcard : (U.card : ℝ) ≤ r * Real.exp X₀ := by
    have h1 : U.card ≤ ∑ e ∈ H, (id e).card := card_biUnion_le
    have h2 : ∑ e ∈ H, (id e).card = H.card * r := sum_const_nat (fun e he => huni e he)
    have h3 : (U.card : ℝ) ≤ H.card * r := by exact_mod_cast h2 ▸ h1
    have : (0 : ℝ) ≤ r := by positivity
    calc (U.card : ℝ) ≤ H.card * r := h3
      _ ≤ Real.exp X₀ * r := mul_le_mul_of_nonneg_right hcard this
      _ = r * Real.exp X₀ := mul_comm _ _
  -- the relevant weight functions
  set K : Finset ι := univ.filter (fun k => (∀ e ∈ H, W k e * Δ ^ (1 + δ) ≤ weight (W k) H) ∧
    0 < weight (W k) H) with hK
  have hKcard : (K.card : ℝ) ≤ Real.exp X₀ :=
    le_trans (by exact_mod_cast card_le_univ K) hι
  have hWpos : ∀ k ∈ K, 0 < weight (W k) H := fun k hk => (mem_filter.mp hk).2.2
  have hWmax : ∀ k ∈ K, ∀ e ∈ H, W k e ≤ η * weight (W k) H := by
    intro k hk e he
    have h := (mem_filter.mp hk).2.1 e he
    have hpos : 0 < Δ ^ (1 + δ) := Real.rpow_pos_of_pos hD0 _
    rw [hη, Real.rpow_neg hD0.le, ← div_eq_inv_mul, le_div_iff₀ hpos]
    exact h
  have hunion : 64 * r ^ 2 * Δ ^ 2 * (Real.exp X₀ * Real.exp X₀) * Real.exp (-Y₀) < 1 := by
    have := F.h6
    rw [show 2 * Δ ^ (ε ^ 2) - Δ ^ ε / 64 = X₀ + X₀ + -Y₀ by rw [hX₀, hY₀]; ring,
      Real.exp_add, Real.exp_add] at this
    linarith
  have hexpY : ∀ E : ℝ, Y₀ ≤ E → Real.exp (-E) ≤ Real.exp (-Y₀) := fun E h =>
    Real.exp_le_exp.mpr (by linarith)
  have hY₀pos : 0 < Real.exp (-Y₀) := Real.exp_pos _
  -- Step 1: the vertex partition
  have hXb2 : P ^ 2 ≤ Xb ^ (2 * r) := by
    calc P ^ 2 ≤ (Xb ^ (r - 1)) ^ 2 := pow_le_pow_left₀ (by linarith) hPX 2
      _ = Xb ^ (2 * (r - 1)) := by rw [← pow_mul, mul_comm]
      _ ≤ Xb ^ (2 * r) := pow_le_pow_right₀ hXb1 (by omega)
  have hXbr : ((p : ℝ) ^ r) ^ 2 ≤ Xb ^ (2 * r) := by
    calc ((p : ℝ) ^ r) ^ 2 ≤ (Xb ^ r) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by positivity) hp_le r) 2
      _ = Xb ^ (2 * r) := by rw [← pow_mul, mul_comm]
  have hE2 := e2_bound r hD0 hξ (by linarith) hC hp1 hP1 hXb2 F.h5
  have hE1 := e1_bound r hD0 hξ (by linarith) hη hp1 hXbr F.h5
  obtain ⟨τ, hτdeg, hτw⟩ := vertex_partition hp0 H r (by omega) huni Δ C η ξ hD0 hC0 hη0 hξ0
    hdeg hcod W K (fun k _ => hW0 k) hWpos hWmax (by
      refine lt_of_le_of_lt ?_ hunion
      have e1 := hexpY _ hE2
      have e2 := hexpY _ hE1
      have hU0 : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _
      have hK0 : (0 : ℝ) ≤ K.card := Nat.cast_nonneg _
      have hp0' : (0 : ℝ) ≤ p := Nat.cast_nonneg _
      calc (U.card * p : ℝ) * Real.exp (-(ξ ^ 2 * Δ / (2 * C * (r * P ^ 2 / p + ξ * P)))) +
            (2 * K.card * p : ℝ) * Real.exp (-(ξ ^ 2 / (2 * Δ * η *
              (r * ((p : ℝ) ^ r) ^ 2 / p + ξ * (p : ℝ) ^ r))))
          ≤ (U.card * p : ℝ) * Real.exp (-Y₀) + (2 * K.card * p : ℝ) * Real.exp (-Y₀) := by
            gcongr
        _ = (U.card + 2 * K.card) * p * Real.exp (-Y₀) := by ring
        _ ≤ (r * Real.exp X₀ + 2 * Real.exp X₀) * (2 * Δ) * Real.exp (-Y₀) := by gcongr
        _ ≤ 64 * r ^ 2 * Δ ^ 2 * (Real.exp X₀ * Real.exp X₀) * Real.exp (-Y₀) :=
            mul_le_mul_of_nonneg_right (num_aux1 hrR hD1 heX) hY₀pos.le)
  -- Step 2: the edge partition
  set A : Fin p → Finset (Finset V) := part H τ with hAdef
  set m : ℝ := Δ / (q * P) with hmdef
  have hqP0 : 0 < (q : ℝ) * P := by positivity
  have hm_ge : Δ ^ a / 2 ≤ m := by
    have hDY : Δ / Y = Δ ^ a := by
      rw [hY, div_eq_iff (Real.rpow_pos_of_pos hD0 _).ne', ← Real.rpow_add hD0]
      simp
    rw [hmdef, ← hDY, div_div]
    exact div_le_div_of_nonneg_left hD0.le (by positivity) (by linarith)
  set D₁ : ℝ := (1 + ξ) * Δ / P with hD₁
  set t₃ : ℝ := ξ * Δ / (q * P) with ht₃
  set t₄ : ℝ := Δ ^ ε / 2 with ht₄
  set β : ℝ := (1 + ξ) / (p : ℝ) ^ r with hβ
  set γ : ℝ := 1 / (2 * q * (p : ℝ) ^ r) with hγ
  have ht₃0 : 0 < t₃ := by positivity
  have ht₄0 : 0 < t₄ := by have := Real.rpow_pos_of_pos hD0 ε; positivity
  have hβ0 : 0 ≤ β := by positivity
  have hγ0 : 0 < γ := by positivity
  have hD₁q : D₁ / q = (1 + ξ) * m := by
    rw [hD₁, hmdef]; field_simp
  have ht₃m : t₃ = ξ * m := by rw [ht₃, hmdef]; ring
  have hWA : ∀ k ∈ K, ∀ i, weight (W k) (A i) ≤ β * weight (W k) H := by
    intro k hk i
    have h := hτw k hk i
    rw [abs_le] at h
    have : β * weight (W k) H = weight (W k) H / (p : ℝ) ^ r +
        ξ * (weight (W k) H / (p : ℝ) ^ r) := by rw [hβ]; ring
    rw [this]; linarith [h.2]
  have hCq : C / q ≤ t₄ := by
    have h1 : C / q ≤ C * P / Y := by
      rw [div_le_div_iff₀ hqR (by linarith)]
      nlinarith
    have h2 : C * P / Y = P * Δ ^ (a - δ) := by
      rw [hC, hY, mul_comm, mul_div_assoc, ← Real.rpow_sub hD0]; ring_nf
    have h3 : P * Δ ^ (a - δ) ≤ Xb ^ (r - 1) * Δ ^ (a - δ) :=
      mul_le_mul_of_nonneg_right hPX (Real.rpow_pos_of_pos hD0 _).le
    have h4 := F.h3
    rw [ht₄]
    rw [← hXb] at h4
    linarith
  have hCq0 : 0 ≤ C / q := by positivity
  have hE3 : Y₀ ≤ t₃ ^ 2 / (2 * (1 * D₁ / q + 1 * t₃)) := by
    have := e3_bound hD1 hξ hξ1 hm_ge ha5
    rw [mul_div_assoc, hD₁q, ht₃m]; exact this
  have hE4 : Y₀ ≤ t₄ ^ 2 / (2 * (1 * C / q + 1 * t₄)) := by
    have := e4_bound hD0 ht₄ hCq0 hCq
    rw [mul_div_assoc]; exact this
  have hηqp : η * (q * (p : ℝ) ^ r) ≤ 4 * Δ ^ (-ε) := by
    have h1 : η * (q * (p : ℝ) ^ r) = η * ((q * P) * p) := by rw [hpr]; ring
    have h2 : η * ((q * P) * p) ≤ η * ((2 * Y) * Xb) := by
      gcongr
    have h3 : η * ((2 * Y) * Xb) = 4 * Δ ^ (-(1 + δ) + (1 - a) + b) := by
      rw [hη, hY, hXb, Real.rpow_add hD0, Real.rpow_add hD0]; ring
    have h4 : Δ ^ (-(1 + δ) + (1 - a) + b) ≤ Δ ^ (-ε) :=
      Real.rpow_le_rpow_of_exponent_le hD1 (by rw [hb]; linarith)
    linarith
  have hE5 : Y₀ ≤ γ ^ 2 / (2 * η * (β / q + γ)) :=
    e5_bound hD0 hξ0.le hξ1 hη0 hqR (by positivity) hβ hγ hηqp
  obtain ⟨f, hfdeg, hfcod, hfw⟩ := edge_partition hq0 H A (fun i => part_subset H τ i) D₁ C
    t₃ t₄ ht₃0 ht₄0 (fun i x => hτdeg x i)
    (fun i x y hxy => le_trans (by exact_mod_cast codegree_mono (part_subset H τ i) x y)
      (hcod x y hxy))
    W K η β γ hη0 hβ0 hγ0 (fun k _ => hW0 k) hWpos hWmax hWA (by
      refine lt_of_le_of_lt ?_ hunion
      have e3 := hexpY _ hE3
      have e4 := hexpY _ hE4
      have e5 := hexpY _ hE5
      have hU0 : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _
      have hK0 : (0 : ℝ) ≤ K.card := Nat.cast_nonneg _
      have hp0' : (0 : ℝ) ≤ p := Nat.cast_nonneg _
      calc (U.card * p * q : ℝ) * Real.exp (-(t₃ ^ 2 / (2 * (1 * D₁ / q + 1 * t₃)))) +
            (U.card ^ 2 * p * q : ℝ) * Real.exp (-(t₄ ^ 2 / (2 * (1 * C / q + 1 * t₄)))) +
            (K.card * p * q : ℝ) * Real.exp (-(γ ^ 2 / (2 * η * (β / q + γ))))
          ≤ (U.card * p * q : ℝ) * Real.exp (-Y₀) + (U.card ^ 2 * p * q : ℝ) * Real.exp (-Y₀) +
            (K.card * p * q : ℝ) * Real.exp (-Y₀) := by gcongr
        _ = (U.card * p * q + U.card ^ 2 * p * q + K.card * p * q : ℝ) * Real.exp (-Y₀) := by
            ring
        _ ≤ (r * Real.exp X₀ * (2 * Δ) * (2 * Δ) + (r * Real.exp X₀) ^ 2 * (2 * Δ) * (2 * Δ) +
            Real.exp X₀ * (2 * Δ) * (2 * Δ)) * Real.exp (-Y₀) := by gcongr
        _ ≤ 64 * r ^ 2 * Δ ^ 2 * (Real.exp X₀ * Real.exp X₀) * Real.exp (-Y₀) :=
            mul_le_mul_of_nonneg_right (num_aux2 hrR hD1 heX) hY₀pos.le)
  -- Step 3: random matchings of the classes
  set B : Fin p → Fin q → Finset (Finset V) := fun i j => cls A f i j with hBdef
  have hBH : ∀ i j, B i j ⊆ H := fun i j => (cls_subset A f i j).trans (part_subset H τ i)
  set Dt : ℝ := D₁ / q + t₃ with hDt
  have hm0 : 0 < m := lt_of_lt_of_le (by have := F.h11; linarith) hm_ge
  have hDt_eq : Dt = (1 + 2 * ξ) * m := by rw [hDt, hD₁q, ht₃m]; ring
  have hDt_ge : Δ ^ a / 2 ≤ Dt := by
    rw [hDt_eq]; nlinarith
  have hDt1 : 1 ≤ Dt := F.h11.trans hDt_ge
  have hDt0 : 0 < Dt := by linarith
  set νr : ℝ := Dt ^ (-ρ) with hνr
  have hνr0 : 0 ≤ νr := (Real.rpow_pos_of_pos hDt0 _).le
  have hνr_le : νr ≤ (Δ ^ a / 2) ^ (-ρ) :=
    Real.rpow_le_rpow_of_nonpos (by linarith [F.h11]) hDt_ge (by linarith)
  have hνr1 : νr ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hDt1 (by linarith)
  set x₀ : ℝ := (1 - νr) / Dt with hx₀
  have hx₀0 : 0 ≤ x₀ := div_nonneg (by linarith) hDt0.le
  have hdist : ∀ i j, ∃ ν : Finset (Finset V) → ℝ, (∀ N, 0 ≤ ν N) ∧ ∑ N, ν N = 1 ∧
      (∀ N, ν N ≠ 0 → IsMatching N ∧ N ⊆ B i j) ∧ ∀ e ∈ B i j, marg ν e = x₀ := by
    intro i j
    have hcodB : ∀ u w, u ≠ w → (codegree (B i j) u w : ℝ) ≤ Dt ^ κ := by
      intro u w huw
      have h1 := hfcod i j u w huw
      have h2 : Δ ^ ε ≤ Dt ^ κ :=
        F.h8.trans (Real.rpow_le_rpow (by linarith [F.h11]) hDt_ge hκ)
      have : C / q + t₄ ≤ Δ ^ ε := by rw [ht₄] at hCq ⊢; linarith
      linarith
    have hcardB : ((B i j).card : ℝ) ≤ Real.exp (Dt ^ σ) := by
      have h1 : ((B i j).card : ℝ) ≤ H.card := by exact_mod_cast card_le_card (hBH i j)
      have h2 : X₀ ≤ Dt ^ σ := F.h9.trans (Real.rpow_le_rpow (by linarith [F.h11]) hDt_ge hσ)
      exact h1.trans (hcard.trans (Real.exp_le_exp.mpr h2))
    obtain ⟨μ, hμ0, hμ1, hμsupp, hμmarg⟩ := hnib Dt (F.h7.trans hDt_ge) V (B i j)
      (fun e he => huni e (hBH i j he)) (fun v => hfdeg i j v) hcodB hcardB
    obtain ⟨ν, hν0, hν1, hνsupp, hνmarg⟩ := thinning (B i j) μ hμ0 hμ1 x₀ hx₀0
      (fun e he => hμmarg e he)
    refine ⟨ν, hν0, hν1, fun N hN => ?_, hνmarg⟩
    obtain ⟨M, hM, hNM, hNB⟩ := hνsupp N hN
    have hMm := (hμsupp M hM).1
    exact ⟨fun e he g hg heg => hMm e (hNM he) g (hNM hg) heg, hNB⟩
  choose ν hν0 hν1 hνsupp hνmarg using hdist
  have hdisj : ∀ i i', i ≠ i' → ∀ j j', ∀ e ∈ B i j, ∀ g ∈ B i' j', Disjoint e g := by
    intro i i' hii j j' e he g hg
    have he' : ∀ v ∈ e, τ v = i := (mem_filter.mp ((cls_subset A f i j) he)).2
    have hg' : ∀ v ∈ g, τ v = i' := (mem_filter.mp ((cls_subset A f i' j') hg)).2
    rw [Finset.disjoint_left]
    intro v hve hvg
    exact hii ((he' v hve).symm.trans (hg' v hvg))
  set c : ι → ℝ := fun k => (β / q + γ) * weight (W k) H with hcdef
  set t : ι → ℝ := fun k => Δ ^ (-ε) * weight (W k) H / (2 * Δ) with htdef
  have hu0 : 0 < β / q + γ := by positivity
  have hc : ∀ k ∈ K, 0 < c k := fun k hk => mul_pos hu0 (hWpos k hk)
  have ht : ∀ k ∈ K, 0 < t k := fun k hk => by
    have := hWpos k hk; have := Real.rpow_pos_of_pos hD0 (-ε); simp only [htdef]; positivity
  have hcb : ∀ k ∈ K, ∀ i j, weight (W k) (B i j) ≤ c k := by
    intro k hk i j
    have := hfw k hk i j
    simp only [hcdef]
    calc weight (W k) (B i j) ≤ β * weight (W k) H / q + γ * weight (W k) H := this
      _ = (β / q + γ) * weight (W k) H := by ring
  have hE6 : ∀ k ∈ K, Y₀ ≤ t k ^ 2 / (2 * (p * c k ^ 2 + c k * t k)) := by
    intro k hk
    simp only [htdef, hcdef]
    exact e6_bound r hD1 hξ0.le hξ1 hε.le ha0.le hqR hp_ge (by linarith) hY hqP_ge hpr hβ hγ hb
      (hWpos k hk)
  obtain ⟨M, hMH, hMm, hMw⟩ := random_matching hq0 H hne B hBH hdisj ν hν0 hν1 hνsupp x₀
    hνmarg W K (fun k _ => hW0 k) c t hc ht hcb (by
      refine lt_of_le_of_lt ?_ hunion
      calc ∑ k ∈ K, 2 * Real.exp (-(t k ^ 2 / (2 * (p * c k ^ 2 + c k * t k))))
          ≤ ∑ k ∈ K, 2 * Real.exp (-Y₀) :=
            sum_le_sum fun k hk => by have := hexpY _ (hE6 k hk); linarith
        _ = 2 * K.card * Real.exp (-Y₀) := by rw [sum_const, nsmul_eq_mul]; ring
        _ ≤ 2 * Real.exp X₀ * Real.exp (-Y₀) := by gcongr
        _ ≤ 64 * r ^ 2 * Δ ^ 2 * (Real.exp X₀ * Real.exp X₀) * Real.exp (-Y₀) :=
            mul_le_mul_of_nonneg_right (num_aux3 hrR hD1 heX) hY₀pos.le)
  refine ⟨M, hMH, hMm, fun k hk => ?_⟩
  by_cases hkK : k ∈ K
  · have hω := hWpos k hkK
    have hfib : ∑ i, ∑ j, weight (W k) (B i j) = ∑ i, weight (W k) (A i) :=
      sum_congr rfl fun i _ => sum_fiberwise (A i) f (W k)
    have hS : |∑ i, weight (W k) (A i) - weight (W k) H / P| ≤ ξ * (weight (W k) H / P) := by
      have e1 : weight (W k) H / P = ∑ _i : Fin p, weight (W k) H / (p : ℝ) ^ r := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, hpr]
        field_simp
      rw [e1, ← sum_sub_distrib, mul_sum]
      exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => hτw k hkK i)
    have hDtq : (q : ℝ) * Dt = (1 + 2 * ξ) * Δ / P := by
      rw [hDt_eq, hmdef]; field_simp
    have hM := hMw k hkK
    rw [hfib] at hM
    exact final_estimate hω hD0 hξ0.le hξ1 hνr0 hνr1 (by linarith) hqR hDt0 hDtq hx₀ hS hM
      (by linarith [F.h10])
  · have h0 : weight (W k) H = 0 := by
      refine le_antisymm ?_ (sum_nonneg fun e he => hW0 k e he)
      by_contra hpos
      push_neg at hpos
      exact hkK (mem_filter.mpr ⟨mem_univ _, hk, hpos⟩)
    have hz : ∀ e ∈ H, W k e = 0 := (sum_eq_zero_iff_of_nonneg (fun e he => hW0 k e he)).mp h0
    have hM0 : weight (W k) M = 0 := sum_eq_zero fun e he => hz e (hMH he)
    rw [h0, hM0]; simp

end Pseudorandom

end FlattenedPS17

/- PseudorandomLib.Eventually12 -/
section FlattenedPS18
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/- # The numerical conditions of Theorem 1.2 hold for all large `Δ` -/

namespace Pseudorandom

open Filter

/-- `C D^α ≤ D^β` eventually, for `α < β`. -/
theorem eventually_mul_rpow_le_rpow {α β : ℝ} (h : α < β) (C : ℝ) :
    ∀ᶠ D : ℝ in atTop, C * D ^ α ≤ D ^ β := by
  rcases le_or_gt C 0 with hC | hC
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with D hD
    have h1 : C * D ^ α ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC (Real.rpow_pos_of_pos hD _).le
    exact h1.trans (Real.rpow_pos_of_pos hD _).le
  · filter_upwards [eventually_rpow_le_mul_rpow (σ := α) (γ := β) (c := 1 / C) h (by positivity)]
      with D hD
    calc C * D ^ α ≤ C * (1 / C * D ^ β) := mul_le_mul_of_nonneg_left hD hC.le
      _ = D ^ β := by field_simp

theorem two_mul_rpow_pow {D : ℝ} (hD : 0 < D) (b : ℝ) (n : ℕ) :
    (2 * D ^ b) ^ n = 2 ^ n * D ^ (b * n) := by
  rw [mul_pow, ← Real.rpow_natCast (D ^ b), ← Real.rpow_mul hD.le]

theorem rpow_div_two_rpow {D : ℝ} (hD : 0 < D) (a κ : ℝ) :
    (D ^ a / 2) ^ κ = D ^ (a * κ) / 2 ^ κ := by
  rw [Real.div_rpow (Real.rpow_pos_of_pos hD _).le (by norm_num), ← Real.rpow_mul hD.le]

/-- All numerical conditions hold for large `Δ`. -/
theorem eventually_facts12 (r : ℕ) (hr : 2 ≤ r) {δ ε a b ρ κ σ : ℝ} (D₀ : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (ha : 0 < a)
    (e2 : b * ((r - 1 : ℕ) : ℝ) < 1 - a) (e3 : b * ((r - 1 : ℕ) : ℝ) + (a - δ) < ε)
    (e5 : b * ((2 * r : ℕ) : ℝ) + ε < δ - 4 * ε) (e8 : ε < a * κ) (e9 : ε ^ 2 < a * σ)
    (e10 : ε < a * ρ) :
    ∀ᶠ D : ℝ in atTop, Facts12 r δ ε a b ρ κ σ D₀ D := by
  have hε2 : ε ^ 2 < ε := by nlinarith
  have hε2pos : 0 < ε ^ 2 := by positivity
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    eventually_mul_rpow_le_rpow e2 (2 ^ (r - 1)),
    eventually_mul_rpow_le_rpow e3 (2 * 2 ^ (r - 1)),
    eventually_const_le_rpow (by positivity : (0 : ℝ) < 2 * ε) 2,
    eventually_mul_rpow_le_rpow e5 (128 * (r + 1) * 2 ^ (2 * r)),
    eventually_rpow_le_mul_rpow (c := 1 / 512) hε2 (by norm_num),
    eventually_const_le_rpow hε (512 * Real.log (64 * r ^ 2)),
    eventually_mul_log_le_rpow hε 1024,
    eventually_const_le_rpow ha (2 * D₀),
    eventually_mul_rpow_le_rpow e8 (2 ^ κ),
    eventually_mul_rpow_le_rpow e9 (2 ^ σ),
    eventually_mul_rpow_le_rpow (show -(a * ρ) < -ε by linarith) (4 * 2 ^ ρ),
    eventually_mul_rpow_le_rpow (show -(2 * ε) < -ε by linarith) 16,
    eventually_const_le_rpow ha 2]
    with D hD2 f2 f3 f4 f5 f6a f6b f6c f7 f8 f9 f10a f10b f11
  have hD0 : 0 < D := by linarith
  have hDε : 0 < D ^ ε := Real.rpow_pos_of_pos hD0 _
  refine ⟨hD2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [two_mul_rpow_pow hD0]; exact f2
  · rw [two_mul_rpow_pow hD0, mul_assoc (2 : ℝ), mul_assoc, ← Real.rpow_add hD0, ← mul_assoc]
    exact f3
  · rw [Real.rpow_neg hD0.le, inv_eq_one_div, div_le_div_iff₀ (Real.rpow_pos_of_pos hD0 _)
      (by norm_num)]
    linarith
  · rw [two_mul_rpow_pow hD0]
    calc 128 * (r + 1) * (2 ^ (2 * r) * D ^ (b * ((2 * r : ℕ) : ℝ))) * D ^ ε =
        128 * (r + 1) * 2 ^ (2 * r) * D ^ (b * ((2 * r : ℕ) : ℝ) + ε) := by
          rw [Real.rpow_add hD0]; ring
      _ ≤ _ := f5
  · -- the union bound
    have hlog : 0 ≤ Real.log D := Real.log_nonneg (by linarith)
    have hsum : Real.log (64 * r ^ 2) + 2 * Real.log D + (2 * D ^ (ε ^ 2) - D ^ ε / 64) < 0 := by
      have : 2 * Real.log D ≤ D ^ ε / 512 := by linarith
      have : Real.log (64 * r ^ 2) ≤ D ^ ε / 512 := by linarith
      have : D ^ (ε ^ 2) ≤ D ^ ε / 512 := by linarith
      linarith
    have hr0 : (0 : ℝ) < 64 * r ^ 2 := by
      have : (2 : ℝ) ≤ r := by exact_mod_cast hr
      positivity
    have : 64 * r ^ 2 * D ^ 2 * Real.exp (2 * D ^ (ε ^ 2) - D ^ ε / 64) =
        Real.exp (Real.log (64 * r ^ 2) + 2 * Real.log D + (2 * D ^ (ε ^ 2) - D ^ ε / 64)) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log hr0, show 2 * Real.log D = Real.log (D ^ 2)
        by rw [Real.log_pow]; norm_num, Real.exp_log (by positivity)]
    rw [this]
    calc _ < Real.exp 0 := Real.exp_lt_exp.mpr hsum
      _ = 1 := Real.exp_zero
  · linarith
  · rw [rpow_div_two_rpow hD0, le_div_iff₀ (Real.rpow_pos_of_pos (by norm_num) _), mul_comm]
    exact f8
  · rw [rpow_div_two_rpow hD0, le_div_iff₀ (Real.rpow_pos_of_pos (by norm_num) _), mul_comm]
    exact f9
  · have e : (D ^ a / 2) ^ (-ρ) = 2 ^ ρ * D ^ (-(a * ρ)) := by
      rw [rpow_div_two_rpow hD0, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul,
        mul_comm, mul_neg]
    rw [e]; linarith
  · linarith

end Pseudorandom

end FlattenedPS18

/- PseudorandomLib.Theorem12 -/
section FlattenedPS19
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/- # Theorem 1.2 of Ehard–Glock–Joos (statement and proof)

**Theorem 1.2.** Suppose `δ ∈ (0,1)` and `r ∈ ℕ` with `r ≥ 2`, and let `ε := δ / (50 r²)`.
Then there exists `Δ₀` such that for all `Δ ≥ Δ₀` the following holds. Let `H` be an
`r`-uniform hypergraph with `Δ(H) ≤ Δ`, `Δ_c(H) ≤ Δ^{1-δ}` and `e(H) ≤ exp(Δ^{ε²})`. Suppose
that `W` is a set of at most `exp(Δ^{ε²})` weight functions on `E(H)`. Then there is a matching
`M` in `H` such that `ω(M) = (1 ± Δ^{-ε}) ω(E(H)) / Δ` for all `ω ∈ W` with
`ω(E(H)) ≥ max_{e ∈ E(H)} ω(e) Δ^{1+δ}`.

Formalization choices:
* The family `W` is an indexed family `W : ι → (Finset V → ℝ)` over a finite type `ι`
  (repetitions are allowed, which only makes the statement more general).
* Weights only need to be nonnegative on the edges of `H`.
* The condition `ω(E(H)) ≥ max_e ω(e) Δ^{1+δ}` is written edge by edge; for nonempty `H` this
  is the same condition, and for empty `H` both sides of the conclusion are `0`.
* `ω(M) = (1 ± Δ^{-ε}) ω(E(H))/Δ` is written as `|ω(M) - ω(E(H))/Δ| ≤ Δ^{-ε} ω(E(H))/Δ`.
-/

namespace Pseudorandom

open Finset

/-- **Theorem 1.2** (Ehard–Glock–Joos). -/
theorem theorem_1_2 (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (r : ℕ) (hr : 2 ≤ r) :
    ∃ Δ₀ : ℝ, ∀ Δ : ℝ, Δ₀ ≤ Δ →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (H : Finset (Finset V)),
      IsUniform H r →
      (∀ v, (degree H v : ℝ) ≤ Δ) →
      (∀ u v, u ≠ v → (codegree H u v : ℝ) ≤ Δ ^ (1 - δ)) →
      (H.card : ℝ) ≤ Real.exp (Δ ^ ((δ / (50 * r ^ 2)) ^ 2)) →
      ∀ (ι : Type) [Fintype ι] (W : ι → Finset V → ℝ),
      (∀ k, ∀ e ∈ H, 0 ≤ W k e) →
      (Fintype.card ι : ℝ) ≤ Real.exp (Δ ^ ((δ / (50 * r ^ 2)) ^ 2)) →
      ∃ M ⊆ H, IsMatching M ∧
        ∀ k, (∀ e ∈ H, W k e * Δ ^ (1 + δ) ≤ weight (W k) H) →
          |weight (W k) M - weight (W k) H / Δ| ≤
            Δ ^ (-(δ / (50 * r ^ 2))) * (weight (W k) H / Δ) := by
  set ε : ℝ := δ / (50 * r ^ 2) with hεdef
  have hR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hR0 : (0 : ℝ) < r := by linarith
  have hεδ : ε * (50 * r ^ 2) = δ := by rw [hεdef]; field_simp
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hε1 : ε < 1 := by nlinarith
  set a : ℝ := 10 * r * ε with ha
  set b : ℝ := 2 * a + 3 * ε with hb
  set ρ : ℝ := 3 / (20 * r) with hρ
  set σ : ℝ := 3 * ε / (20 * r) with hσ
  have ha0 : 0 < a := by positivity
  have hρ0 : 0 < ρ := by positivity
  have hσ0 : 0 ≤ σ := by positivity
  have haρ : a * ρ = 3 / 2 * ε := by rw [ha, hρ]; field_simp; ring
  have haσ : a * σ = 3 / 2 * ε ^ 2 := by rw [ha, hσ]; field_simp; ring
  have hr1 : ((r - 1 : ℕ) : ℝ) = r - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hr2 : ((2 * r : ℕ) : ℝ) = 2 * r := by push_cast; ring
  have hsum : (2 * r + 4) * ρ + ρ + σ < 1 := by
    have : (2 * r + 4) * ρ + ρ + σ = (6 * r + 15 + 3 * ε) / (20 * r) := by
      rw [hρ, hσ]; field_simp; ring
    rw [this, div_lt_one (by positivity)]
    linarith
  have hr2' : (20 * r + 3 : ℝ) ≤ 50 * r ^ 2 := by nlinarith
  have hb1 : b ≤ 1 := by
    calc b = (20 * r + 3) * ε := by rw [hb, ha]; ring
      _ ≤ 50 * r ^ 2 * ε := mul_le_mul_of_nonneg_right hr2' hε.le
      _ = δ := by rw [← hεδ]; ring
      _ ≤ 1 := hδ1.le
  have ha5 : 5 * ε ≤ a := by
    have := mul_le_mul_of_nonneg_right (show (5 : ℝ) ≤ 10 * r by linarith) hε.le
    rw [ha]; linarith
  have hδa : a + 4 * ε ≤ δ := by
    have h1 : (10 * r + 4 : ℝ) ≤ 50 * r ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_right h1 hε.le
    rw [ha, ← hεδ]; linarith
  obtain ⟨D₀, hD₀⟩ := Nibble.nibble_marginal r hr hρ0 hρ0.le hσ0 hsum
  have e2 : b * ((r - 1 : ℕ) : ℝ) < 1 - a := by
    rw [hr1, hb, ha]
    have : (20 * r ^ 2 - 7 * r - 3) * ε < 50 * r ^ 2 * ε := by nlinarith
    nlinarith
  have e3 : b * ((r - 1 : ℕ) : ℝ) + (a - δ) < ε := by
    rw [hr1, hb, ha, ← hεδ]; nlinarith
  have e5 : b * ((2 * r : ℕ) : ℝ) + ε < δ - 4 * ε := by
    rw [hr2, hb, ha, ← hεδ]
    have : 0 < (10 * r ^ 2 - 6 * r - 5) * ε := by
      apply mul_pos _ hε; nlinarith
    nlinarith
  have e8 : ε < a * ρ := by rw [haρ]; linarith
  have e9 : ε ^ 2 < a * σ := by
    rw [haσ]; have : 0 < ε ^ 2 := by positivity
    linarith
  obtain ⟨Δ₀, hΔ₀⟩ := Filter.eventually_atTop.mp (eventually_facts12 r hr D₀ hε hε1 ha0
    e2 e3 e5 e8 e9 e8)
  refine ⟨Δ₀, fun Δ hΔ V _ _ H huni hdeg hcod hcard ι _ W hW0 hι => ?_⟩
  exact core_1_2 r hr δ ε a b ρ ρ σ D₀ hε ha0 rfl hb1 ha5 hδa hρ0.le hρ0.le hσ0
    (fun D hD V _ _ H => hD₀ D hD V H) Δ (hΔ₀ Δ hΔ) V H huni hdeg hcod hcard ι W hW0 hι

end Pseudorandom

end FlattenedPS19

/- PseudorandomLib.PippengerSpencer.Polynomial -/
section FlattenedPS20
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/- # Chromatic index under polynomial codegrees

**Theorem.** Let `r ≥ 2` and `δ ∈ (0,1)`. There are `γ > 0` and `D₀` such that every
`r`-uniform hypergraph `H` with maximum degree `≤ D`, codegrees `≤ D^{1-δ}` and at most
`exp(D^γ)` edges has a proper edge colouring with at most `D + D^{1-γ}` colours, whenever
`D ≥ D₀`.

Proof: apply Theorem 1.2 to the `(r+1)`-uniform colour hypergraph with `⌊D⌋` colours, with one
weight function per vertex `v` counting the edges at `v`. The resulting matching colours all but
`O(D^{1-ε})` edges at every vertex of large degree, and the leftover hypergraph has maximum degree
`O(D^{1-ε} + D^δ)`; it is coloured greedily.
-/

namespace Pseudorandom.PS

open Finset Filter

/-- `D exp(D^γ) ≤ exp(D^κ)` eventually, for `0 < γ < κ`. -/
theorem eventually_mul_exp_le_exp {γ κ : ℝ} (hγκ : γ < κ) (hκ : 0 < κ) :
    ∀ᶠ D : ℝ in atTop, D * Real.exp (D ^ γ) ≤ Real.exp (D ^ κ) := by
  filter_upwards [eventually_mul_log_le_rpow hκ 2,
    eventually_rpow_le_mul_rpow hγκ (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_gt_atTop (0 : ℝ)] with D h1 h2 h3
  calc D * Real.exp (D ^ γ) = Real.exp (Real.log D + D ^ γ) := by
        rw [Real.exp_add, Real.exp_log h3]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

/-- The final numerical inequality for the number of colours. -/
theorem eventually_colour_count (r : ℝ) (hr : 0 < r) {δ e γ : ℝ} (hδ : δ < 1 - γ)
    (he : 1 - e < 1 - γ) (hγ : γ < 1) :
    ∀ᶠ D : ℝ in atTop, r * (2 * D ^ δ + 2 + D ^ (1 - e)) + 1 ≤ D ^ (1 - γ) := by
  filter_upwards [eventually_rpow_le_mul_rpow hδ (by positivity : (0 : ℝ) < 1 / (8 * r)),
    eventually_rpow_le_mul_rpow he (by positivity : (0 : ℝ) < 1 / (4 * r)),
    eventually_const_le_rpow (by linarith : (0 : ℝ) < 1 - γ) (2 * (2 * r + 1))]
    with D h1 h2 h3
  have e1 : r * (2 * D ^ δ) ≤ D ^ (1 - γ) / 4 := by
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * r)
    calc r * (2 * D ^ δ) = 2 * r * D ^ δ := by ring
      _ ≤ 2 * r * (1 / (8 * r) * D ^ (1 - γ)) := this
      _ = D ^ (1 - γ) / 4 := by field_simp; ring
  have e2 : r * D ^ (1 - e) ≤ D ^ (1 - γ) / 4 := by
    have := mul_le_mul_of_nonneg_left h2 hr.le
    calc r * D ^ (1 - e) ≤ r * (1 / (4 * r) * D ^ (1 - γ)) := this
      _ = D ^ (1 - γ) / 4 := by field_simp
  nlinarith

end PS

open Finset Filter PS in
/-- **Chromatic index under polynomial codegrees.** -/
theorem chromatic_index_polynomial (r : ℕ) (hr : 2 ≤ r) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ D₀ : ℝ, ∀ (V : Type) [Fintype V] [DecidableEq V] (H : Finset (Finset V))
      (D : ℝ), D₀ ≤ D → IsUniform H r → (∀ v, (degree H v : ℝ) ≤ D) →
      (∀ u v, u ≠ v → (codegree H u v : ℝ) ≤ D ^ (1 - δ)) →
      (H.card : ℝ) ≤ Real.exp (D ^ γ) →
      ∃ (m : ℕ) (c : Finset V → Fin m), (m : ℝ) ≤ D + D ^ (1 - γ) ∧
        IsProperEdgeColouring H m c := by
  set e : ℝ := δ / (50 * ((r + 1 : ℕ) : ℝ) ^ 2) with he_def
  have hR : (3 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by push_cast; exact_mod_cast (by omega : 3 ≤ r + 1)
  have he0 : 0 < e := by positivity
  have he1 : e < 1 := by
    rw [he_def, div_lt_one (by positivity)]; nlinarith
  have heδ : e < δ := by
    have h50 : (1 : ℝ) < 50 * ((r + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
    rw [he_def, div_lt_iff₀ (by positivity)]
    nlinarith [mul_lt_mul_of_pos_left h50 hδ0]
  set γ : ℝ := min (e ^ 2 / 2) ((1 - δ) / 2) with hγ_def
  have hγ0 : 0 < γ := lt_min (by positivity) (by linarith)
  have hγe2 : γ < e ^ 2 := by
    have := sq_pos_of_pos he0
    have : γ ≤ e ^ 2 / 2 := min_le_left _ _
    linarith
  have he2e : e ^ 2 < e := by nlinarith
  have hγδ : δ < 1 - γ := by
    have : γ ≤ (1 - δ) / 2 := min_le_right _ _
    linarith
  have hγ1 : γ < 1 := by linarith
  obtain ⟨Δ₀, hT⟩ := theorem_1_2 δ hδ0 hδ1 (r + 1) (by omega)
  have hrR : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  obtain ⟨D₀, hD₀⟩ := eventually_atTop.mp ((eventually_ge_atTop Δ₀).and
    ((eventually_ge_atTop (max 2 (r : ℝ))).and
    ((eventually_mul_exp_le_exp hγe2 (by positivity)).and
    (eventually_colour_count (r : ℝ) hrR (e := e) hγδ (by linarith) hγ1))))
  refine ⟨γ, hγ0, D₀, fun V _ _ H D hD huni hdeg hcod hcard => ?_⟩
  obtain ⟨hΔ₀, hD2, hexp, hcount⟩ := hD₀ D hD
  have hD2' : (2 : ℝ) ≤ D := (le_max_left _ _).trans hD2
  have hDr : (r : ℝ) ≤ D := (le_max_right _ _).trans hD2
  have hDpos : 0 < D := by linarith
  set C : ℕ := ⌊D⌋₊ with hC_def
  have hCD : (C : ℝ) ≤ D := Nat.floor_le hDpos.le
  have hDC : D < C + 1 := Nat.lt_floor_add_one D
  have hC0 : 0 < C := by
    have : (0 : ℝ) < C := by linarith
    exact_mod_cast this
  have hne : ∀ f ∈ H, f.Nonempty := fun f hf => by
    rw [← card_pos, huni f hf]; omega
  set G := colourHyp H C with hG_def
  set s : Finset V := H.biUnion id with hs_def
  -- hypotheses of Theorem 1.2 for the colour hypergraph
  have hGuni : IsUniform G (r + 1) := colourHyp_uniform huni
  have hGdeg : ∀ y, (degree G y : ℝ) ≤ D := by
    intro y
    rcases y with f | ⟨v, c⟩
    · exact (Nat.cast_le.mpr (degree_colourHyp_inl H f)).trans hCD
    · exact (Nat.cast_le.mpr (degree_colourHyp_inr H v c)).trans (hdeg v)
  have hone : (1 : ℝ) ≤ D ^ (1 - δ) := Real.one_le_rpow (by linarith) (by linarith)
  have hGcod : ∀ y z, y ≠ z → (codegree G y z : ℝ) ≤ D ^ (1 - δ) := by
    intro y z hyz
    rcases codegree_colourHyp_le (C := C) H y z hyz with h | ⟨u, v, huv, h⟩
    · exact (Nat.cast_le.mpr h).trans (by simpa using hone)
    · exact (Nat.cast_le.mpr h).trans (hcod u v huv)
  have hcap : D * Real.exp (D ^ γ) ≤ Real.exp (D ^ ((δ / (50 * ((r + 1 : ℕ) : ℝ) ^ 2)) ^ 2)) :=
    hexp
  have hGcard : (G.card : ℝ) ≤ Real.exp (D ^ ((δ / (50 * ((r + 1 : ℕ) : ℝ) ^ 2)) ^ 2)) := by
    have h1 : (G.card : ℝ) ≤ H.card * C := by exact_mod_cast card_colourHyp_le H
    have h2 : (H.card : ℝ) * C ≤ Real.exp (D ^ γ) * D :=
      mul_le_mul hcard hCD (Nat.cast_nonneg _) (Real.exp_pos _).le
    linarith
  have hscard : (Fintype.card {v // v ∈ s} : ℝ) ≤
      Real.exp (D ^ ((δ / (50 * ((r + 1 : ℕ) : ℝ) ^ 2)) ^ 2)) := by
    rw [Fintype.card_coe]
    have h1 : s.card ≤ ∑ f ∈ H, (id f).card := card_biUnion_le
    have h2 : ∑ f ∈ H, (id f).card = H.card * r := by
      rw [sum_const_nat (m := r) (fun f hf => by simpa using huni f hf)]
    have h3 : (s.card : ℝ) ≤ H.card * r := by exact_mod_cast h2 ▸ h1
    have h4 : (H.card : ℝ) * r ≤ Real.exp (D ^ γ) * D :=
      mul_le_mul hcard hDr (Nat.cast_nonneg _) (Real.exp_pos _).le
    linarith
  obtain ⟨M, hMG, hM, hW⟩ := hT D hΔ₀ (Finset V ⊕ (V × Fin C)) G hGuni hGdeg hGcod hGcard
    {v // v ∈ s} (fun v => wv v.1) (fun k x _ => wv_nonneg _ _) hscard
  -- the leftover hypergraph has small degrees
  set L := H \ col H M with hL_def
  set Lb : ℝ := 2 * D ^ δ + 2 + D ^ (1 - e) with hLb_def
  have hDδ : 0 ≤ D ^ δ := Real.rpow_nonneg hDpos.le _
  have hDe : 0 ≤ D ^ (1 - e) := Real.rpow_nonneg hDpos.le _
  have hLdeg : ∀ v, (degree L v : ℝ) ≤ Lb := by
    intro v
    have hsplit := degree_sdiff_col H M v
    have hsplitR : (degree L v : ℝ) =
        degree H v - (((col H M).filter (fun f => v ∈ f)).card : ℝ) := by
      rw [← hsplit]; push_cast; ring
    by_cases hv : v ∈ s
    · by_cases hbig : D ^ (1 + δ) ≤ (degree H v : ℝ) * C
      · have hcond : ∀ x ∈ G, wv v x * D ^ (1 + δ) ≤ weight (wv v) G := by
          intro x hx
          rw [weight_colourHyp hne]
          have := wv_le_one hx v
          have hp : 0 ≤ D ^ (1 + δ) := Real.rpow_nonneg hDpos.le _
          exact (mul_le_of_le_one_left hp this).trans hbig
        have hk := hW ⟨v, hv⟩ hcond
        simp only at hk
        rw [weight_matching hne hMG hM, weight_colourHyp hne] at hk
        have habs := (abs_le.mp hk).1
        set d : ℝ := (degree H v : ℝ) with hd_def
        have hd0 : 0 ≤ d := Nat.cast_nonneg _
        have hdD : d ≤ D := hdeg v
        have hDneg : D ^ (-e) * (d * C / D) ≤ D ^ (1 - e) := by
          have h1 : d * C / D ≤ D := by
            rw [div_le_iff₀ hDpos]
            exact mul_le_mul hdD hCD (Nat.cast_nonneg _) hDpos.le
          have h2 : D ^ (-e) * D = D ^ (1 - e) := by
            rw [show (1 - e) = -e + 1 by ring, Real.rpow_add hDpos, Real.rpow_one]
          calc D ^ (-e) * (d * C / D) ≤ D ^ (-e) * D :=
                mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hDpos.le _)
            _ = _ := h2
        have hdC : d - d * C / D ≤ 1 := by
          have : d - d * C / D = d * (D - C) / D := by field_simp
          rw [this, div_le_one hDpos]
          have : D - C ≤ 1 := by linarith
          calc d * (D - C) ≤ d * 1 := mul_le_mul_of_nonneg_left this hd0
            _ ≤ D := by linarith
        rw [hsplitR]
        linarith
      · push Not at hbig
        have hCD2 : D ≤ 2 * C := by linarith
        have hdsmall : (degree H v : ℝ) ≤ 2 * D ^ δ := by
          have hpow : D ^ (1 + δ) = D * D ^ δ := by
            rw [Real.rpow_add hDpos, Real.rpow_one]
          rw [hpow] at hbig
          by_contra hcon
          push Not at hcon
          have hC0' : (0 : ℝ) ≤ C := Nat.cast_nonneg _
          have h1 := mul_le_mul_of_nonneg_right hcon.le hC0'
          have h2 := mul_le_mul_of_nonneg_right hCD2 hDδ
          linarith
        have : (degree L v : ℝ) ≤ degree H v := by
          rw [hsplitR]; linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤
            (((col H M).filter (fun f => v ∈ f)).card : ℝ))]
        linarith
    · have h0 : degree H v = 0 := by
        unfold degree
        rw [card_eq_zero, filter_eq_empty_iff]
        intro f hf hvf
        exact hv (mem_biUnion.mpr ⟨f, hf, hvf⟩)
      have : degree L v ≤ degree H v := degree_mono' sdiff_subset v
      rw [h0] at this
      have : (degree L v : ℝ) = 0 := by exact_mod_cast Nat.le_zero.mp this
      rw [this]; positivity
  set Δ' : ℕ := ⌊Lb⌋₊ with hΔ'_def
  have hLdeg' : ∀ v, degree L v ≤ Δ' := fun v => Nat.le_floor (hLdeg v)
  obtain ⟨c₂, hc₂⟩ := exists_greedy_colouring r Δ' L
    (fun f hf => huni f (sdiff_subset hf)) hLdeg'
  have hglue := (colOf_proper H hM hC0).glue hc₂
  rw [union_sdiff_of_subset (col_subset H M)] at hglue
  refine ⟨C + (r * Δ' + 1), _, ?_, hglue⟩
  have hΔ'le : (Δ' : ℝ) ≤ Lb := Nat.floor_le (by positivity)
  push_cast
  have : (r : ℝ) * Δ' ≤ r * Lb := mul_le_mul_of_nonneg_left hΔ'le hrR.le
  linarith

end Pseudorandom

end FlattenedPS20


/-
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/
/-
Adapts the Lean ancillary of Varun Sivashankar, An Improved Lower Bound for the
Erdos–Lovasz Cover Number Problem, arXiv:2606.24878v2, CC BY 4.0.
Source: https://arxiv.org/src/2606.24878v2/anc/lean-proof/RequestProject/Theorem1.lean.
License: https://creativecommons.org/licenses/by/4.0/.
Changes include porting to the pinned Mathlib and restricting the matching
input to the polynomial-size auxiliary hypergraphs used in the proof.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise




/-
# An improved lower bound for the Erdős–Lovász cover-number problem

Complete formalization of **Theorem 1** of *An improved lower bound for the
Erdős–Lovász cover-number problem*, in a single file.

Let `g(r)` be the minimum number of edges in an `r`-uniform intersecting
hypergraph with cover number `r`.  Theorem 1 has two parts:

* **(i)** For every positive integer `r`,  `g(r) ≥ 3r − 4`.
* **(ii)** For every `ε > 0`, there is `r₀` such that, for every `r ≥ r₀`,
  `g(r) ≥ ((41 - √19)/12 − ε) r`.

Since `(41 - √19)/12 > 3`, part (ii) implies the **corollary** `g(r) > 3r`
for all sufficiently large `r`, crossing the threshold Erdős explicitly
noted was unresolved.

We model a (simple) hypergraph as a `Finset (Finset V)` of edges, and encode the
lower bounds on `g(r)` in the standard "for every admissible `H`" form (a lower
bound on `g(r)` is exactly a lower bound on `|E(H)|` valid for every `r`-uniform
intersecting `H` with `coverNum H = r`).

Part (ii) uses **Kahn's small-codegree edge-colouring theorem** (Theorem 2 of the
paper), assumed as a black box via the hypothesis `KahnTheorem`; it is never
introduced as an axiom.  The intermediate `Corollary 1` of the paper
(`KahnDegreeCorollary`) is *proved* from `KahnTheorem` in
`ErdosLovasz.kahnDegreeCorollary_of_kahnTheorem`, so `KahnTheorem` is the
only unverified input of the development.

* Part (i): `ErdosLovasz.theorem1_i` (and `ErdosLovasz.theorem1_i'`).
* Part (ii): `ErdosLovasz.theorem1_ii`.
* Both parts together: `ErdosLovasz.theorem1`.
* The corollary: `ErdosLovasz.corollary_gt_3r`.
* Kahn's theorem → actual-degree corollary:
  `ErdosLovasz.kahnDegreeCorollary_of_kahnTheorem`.
-/

namespace ErdosLovasz

/-- Selecting a pair from each block injects a linear block family into the square of its ground set. -/
lemma linear_blocks_card_bound {V : Type*} [DecidableEq V]
    (J : Finset (Finset V)) (W : Finset V) (B : V → Finset (Finset V))
    (hsub : ∀ w ∈ W, B w ⊆ J)
    (h4 : ∀ w ∈ W, (B w).card = 4)
    (hlin : ∀ p ∈ J, ∀ q ∈ J, p ≠ q →
      (W.filter (fun w ↦ p ∈ B w ∧ q ∈ B w)).card ≤ 1) :
    W.card ≤ J.card ^ 2 := by
  classical
  have hpairs (w : W) : ∃ p ∈ B w.val, ∃ q ∈ B w.val, p ≠ q := by
    have hw : 1 < (B w.val).card := by rw [h4 w.val w.prop]; decide
    exact Finset.one_lt_card.mp hw
  choose p hp q hq hne using hpairs
  let pick (w : W) : J × J :=
    (⟨p w, hsub w.val w.prop (hp w)⟩, ⟨q w, hsub w.val w.prop (hq w)⟩)
  have hinj : Function.Injective pick := by
    intro w w' heq
    have hp' : p w = p w' := congrArg (fun x : J × J ↦ x.1.val) heq
    have hq' : q w = q w' := congrArg (fun x : J × J ↦ x.2.val) heq
    have hcard := hlin (p w) (hsub w.val w.prop (hp w))
      (q w) (hsub w.val w.prop (hq w)) (hne w)
    apply Subtype.ext
    apply Finset.card_le_one.mp hcard
    · exact Finset.mem_filter.mpr ⟨w.prop, hp w, hq w⟩
    · exact Finset.mem_filter.mpr ⟨w'.prop, hp' ▸ hp w', hq' ▸ hq w'⟩
  simpa [Fintype.card_prod, pow_two] using Fintype.card_le_of_injective pick hinj


universe u

variable {V : Type*} [DecidableEq V]
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
def edgeDeg (H : Finset (Finset V)) (v : V) : ℕ :=
  (H.filter (fun E => v ∈ E)).card

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- `H` is `r`-uniform: every edge has exactly `r` vertices. -/
def IsUniform (r : ℕ) (H : Finset (Finset V)) : Prop :=
  ∀ E ∈ H, E.card = r

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- `H` is intersecting: every two edges meet. -/
def Intersecting (H : Finset (Finset V)) : Prop :=
  ∀ E ∈ H, ∀ F ∈ H, (E ∩ F).Nonempty

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- `C` is a cover (transversal) of `H`: it meets every edge. -/
def IsCover (H : Finset (Finset V)) (C : Finset V) : Prop :=
  ∀ E ∈ H, ∃ v ∈ C, v ∈ E

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- The set of cardinalities of covers of `H`. -/
def coverCards (H : Finset (Finset V)) : Set ℕ :=
  {n | ∃ C : Finset V, IsCover H C ∧ C.card = n}

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- The cover number `τ(H)`: the minimum size of a cover. -/
noncomputable def coverNum (H : Finset (Finset V)) : ℕ :=
  sInf (coverCards H)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
omit [DecidableEq V] in
/-- Any cover gives an upper bound on the cover number. -/
lemma coverNum_le {H : Finset (Finset V)} {C : Finset V} (hC : IsCover H C) :
    coverNum H ≤ C.card :=
  Nat.sInf_le ⟨C, hC, rfl⟩

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- If every edge of `H` is nonempty, then a cover exists. -/
lemma coverCards_nonempty {H : Finset (Finset V)} (hne : ∀ E ∈ H, E.Nonempty) :
    (coverCards H).Nonempty := by
  refine ⟨(H.biUnion id).card, H.biUnion id, ?_, rfl⟩
  intro E hE
  obtain ⟨v, hv⟩ := hne E hE
  exact ⟨v, Finset.mem_biUnion.2 ⟨E, hE, hv⟩, hv⟩

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- If every edge of `H` is nonempty, the cover number is attained by some cover. -/
lemma exists_opt_cover {H : Finset (Finset V)} (hne : ∀ E ∈ H, E.Nonempty) :
    ∃ C : Finset V, IsCover H C ∧ C.card = coverNum H := by
  obtain ⟨C, hC, hn⟩ := Nat.sInf_mem (coverCards_nonempty hne)
  exact ⟨C, hC, hn⟩

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- An intersecting hypergraph has nonempty edges. -/
lemma Intersecting.edge_nonempty {H : Finset (Finset V)} (hint : Intersecting H)
    {E : Finset V} (hE : E ∈ H) : E.Nonempty := by
  obtain ⟨v, hv⟩ := hint E hE E hE
  exact ⟨v, (Finset.mem_inter.1 hv).1⟩

/- ## Lemma 1 -/

/-
**Lemma 1.** An `r`-uniform intersecting hypergraph of maximum degree `≤ 3`
has at most `2r + 1` edges.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma lemma1 (r : ℕ) (J : Finset (Finset V)) (huni : IsUniform r J)
    (hint : Intersecting J) (hdeg : ∀ v, edgeDeg J v ≤ 3) :
    J.card ≤ 2 * r + 1 := by
  by_contra! h_contra;
  -- By double counting, we have $\sum_{F \in J} |E \cap F| = \sum_{v \in E} \deg_J(v)$.
  have h_double_count : ∀ E ∈ J, ∑ F ∈ J, (E ∩ F).card = ∑ v ∈ E, edgeDeg J v := by
    intro E hE
    have h_double_count : ∑ F ∈ J, (E ∩ F).card = ∑ v ∈ E, ∑ F ∈ J, if v ∈ F then 1 else 0 := by
      rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop;
    simp_all +decide [ edgeDeg ];
  -- Since J is intersecting, for each F ∈ J, (E ∩ F).Nonempty, so 1 ≤ (E ∩ F).card. Therefore
  have h_card_inter : ∀ E ∈ J, ∑ F ∈ J, (E ∩ F).card ≥ (J.card - 1) + r := by
    intro E hE
    have h_card_inter : ∀ F ∈ J, F ≠ E → (E ∩ F).card ≥ 1 := by
      exact fun F hF hne => Finset.card_pos.mpr ( by have := ‹Intersecting J› E hE F hF; aesop );
    rw [ ← Finset.sum_erase_add _ _ hE ];
    exact add_le_add ( le_trans ( by simp +decide [ Finset.card_erase_of_mem hE ] ) ( Finset.sum_le_sum fun x hx => h_card_inter x ( Finset.mem_of_mem_erase hx ) ( Finset.ne_of_mem_erase hx ) ) ) ( by simp +decide [ huni E hE ] );
  rcases J.eq_empty_or_nonempty with ( rfl | ⟨ E, hE ⟩ ) <;> simp_all +decide;
  exact absurd ( h_card_inter E hE ) ( by have := huni E hE; have := Finset.sum_le_sum fun v ( hv : v ∈ E ) => hdeg v; norm_num at *; omega )

/- ## Lemma 2 (link-graph support bound) -/

/-
Geometric fact: a 2-edge `g` meeting two disjoint 2-edges `e`, `f` lies in `e ∪ f`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma edge_in_union {e f g : Finset V} (he : e.card = 2) (hf : f.card = 2)
    (hef : Disjoint e f) (hg : g.card = 2)
    (hge : (g ∩ e).Nonempty) (hgf : (g ∩ f).Nonempty) : g ⊆ e ∪ f := by
  obtain ⟨ x, hx ⟩ := hge; obtain ⟨ y, hy ⟩ := hgf; simp_all +decide [ Finset.disjoint_left ] ;
  intro z hz; have := Finset.card_eq_two.mp hg; obtain ⟨ u, v, huv ⟩ := this; aesop;

/-
The support of a graph whose edges are subsets of `U` is contained in `U`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma support_card_le {U : Finset V} {G : Finset (Finset V)}
    (hG : ∀ e ∈ G, e ⊆ U) : (G.biUnion id).card ≤ U.card := by
  exact Finset.card_le_card ( Finset.biUnion_subset.mpr hG )

/-
A pairwise-intersecting family of 2-element edges is a star or a triangle:
either its support has size at most `3`, or all edges share a common vertex.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma star_or_triangle {G : Finset (Finset V)} (hcard : ∀ e ∈ G, e.card = 2)
    (hpi : ∀ e ∈ G, ∀ f ∈ G, (e ∩ f).Nonempty) :
    (G.biUnion id).card ≤ 3 ∨ ∃ c, ∀ e ∈ G, c ∈ e := by
  by_cases h : ∃ c, ∀ e ∈ G, c ∈ e;
  · exact Or.inr h;
  · by_cases hG_empty : G = ∅;
    · aesop;
    · obtain ⟨e0, he0⟩ : ∃ e0 ∈ G, True := by
        exact Exists.elim ( Finset.nonempty_of_ne_empty hG_empty ) fun e he => ⟨ e, he, trivial ⟩
      obtain ⟨a, b, hab⟩ : ∃ a b : V, a ≠ b ∧ e0 = {a, b} := by
        have := Finset.card_eq_two.mp ( hcard e0 he0.1 ) ; tauto;
      obtain ⟨e1, he1, ha⟩ : ∃ e1 ∈ G, a ∉ e1 := by
        exact by push_neg at h; exact h a;
      obtain ⟨c, hc⟩ : ∃ c : V, c ≠ a ∧ c ≠ b ∧ e1 = {b, c} := by
        have := hpi e0 he0.1 e1 he1; simp_all +decide [ Finset.Nonempty ] ;
        have := Finset.card_eq_two.mp ( hcard e1 he1 ) ; obtain ⟨ c, d, hcd ⟩ := this; use if c = b then d else c; aesop;
      obtain ⟨e2, he2, hb⟩ : ∃ e2 ∈ G, b ∉ e2 := by
        exact not_forall_not.mp fun contra => h ⟨ b, fun e he => by aesop ⟩
      obtain ⟨ha2, hc2⟩ : a ∈ e2 ∧ c ∈ e2 := by
        obtain ⟨ x, hx ⟩ := hpi _ he0.1 _ he2; obtain ⟨ y, hy ⟩ := hpi _ he1 _ he2; simp_all +decide [ Finset.Nonempty ] ;
        grind
      have he2_eq : e2 = {a, c} := by
        rw [ Finset.eq_of_subset_of_card_le ( Finset.insert_subset_iff.mpr ⟨ ha2, Finset.singleton_subset_iff.mpr hc2 ⟩ ) ] ; aesop
      have h_support : ∀ e ∈ G, e = {a, b} ∨ e = {b, c} ∨ e = {a, c} := by
        intro e he; specialize hpi e he; simp_all +decide [ Finset.Nonempty ] ;
        have := Finset.card_eq_two.mp ( hcard e he ) ; obtain ⟨ x, y, hxy ⟩ := this; simp_all +decide [ Finset.ext_iff ] ;
        grind
      have h_support_card : (G.biUnion id).card ≤ 3 := by
        refine' le_trans ( Finset.card_le_card _ ) _;
        exact { a, b, c };
        · intro x hx; obtain ⟨ e, he, hx ⟩ := Finset.mem_biUnion.mp hx; specialize h_support e he; aesop;
        · grind +qlia
      exact Or.inl h_support_card

/-
**Lemma 2, Case A.** The colour class `Ga` contains two vertex-disjoint edges.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma lemma2_caseA (U : Finset V) (Ga Gb Gc : Finset (Finset V))
    (ha : ∀ e ∈ Ga, e.card = 2 ∧ e ⊆ U) (hb : ∀ e ∈ Gb, e.card = 2 ∧ e ⊆ U)
    (hc : ∀ e ∈ Gc, e.card = 2 ∧ e ⊆ U)
    (hdab : Disjoint Ga Gb) (hdac : Disjoint Ga Gc) (hdbc : Disjoint Gb Gc)
    (hcab : ∀ e ∈ Ga, ∀ f ∈ Gb, (e ∩ f).Nonempty)
    (hcac : ∀ e ∈ Ga, ∀ f ∈ Gc, (e ∩ f).Nonempty)
    (hcbc : ∀ e ∈ Gb, ∀ f ∈ Gc, (e ∩ f).Nonempty)
    (e f : Finset V) (he : e ∈ Ga) (hf : f ∈ Ga) (hef : Disjoint e f) :
    (Ga.biUnion id).card + (Gb.biUnion id).card + (Gc.biUnion id).card
      ≤ max 12 (U.card + 4) := by
  -- Let W := e ∪ f; e ∩ f = ∅ and W.card = 4.
  set W := e ∪ f with hW_def
  have hW_card : W.card = 4 := by
    rw [ Finset.card_union_of_disjoint hef, ha e he |>.1, ha f hf |>.1 ];
  -- First establish hW : ∀ g ∈ Gb ∪ Gc, g ⊆ W.
  have hW : ∀ g ∈ Gb ∪ Gc, g ⊆ W := by
    intro g hg; by_cases hg' : g ∈ Gb <;> simp_all +decide [ Finset.disjoint_left ] ;
    · have hW : (g ∩ e).Nonempty ∧ (g ∩ f).Nonempty := by
        exact ⟨ by simpa only [ Finset.inter_comm ] using hcab e he g hg', by simpa only [ Finset.inter_comm ] using hcab f hf g hg' ⟩;
      have := edge_in_union ( ha e he |>.1 ) ( ha f hf |>.1 ) ( Finset.disjoint_left.mpr hef ) ( hb g hg' |>.1 ) hW.1 hW.2; aesop;
    · apply edge_in_union;
      any_goals rw [ Finset.inter_comm ] ; exact hcac _ ‹_› _ ‹_›;
      · exact ha e he |>.1;
      · exact ha f hf |>.1;
      · exact Finset.disjoint_left.mpr hef;
      · exact hc g hg |>.1;
  by_cases h_common : ∃ c, ∀ g ∈ Gb ∪ Gc, c ∈ g;
  · obtain ⟨ c, hc ⟩ := h_common
    have hGbGc_card : (Gb ∪ Gc).card ≤ 2 := by
      -- Choose f' ∈ {e,f} with c ∉ f'.
      obtain ⟨f', hf'⟩ : ∃ f' ∈ [e, f], c ∉ f' := by
        by_cases hc_e : c ∈ e <;> by_cases hc_f : c ∈ f <;> simp_all +decide [ Finset.disjoint_left ];
      -- Every g ∈ Gb ∪ Gc satisfies c ∈ g, g ⊆ W, and (g ∩ f').Nonempty (g meets the Ga-edge f' by the relevant cross hypothesis + inter_comm); with g.card = 2 and c ∉ f', g = {c, y}, y ∈ f'.
      have hGbGc_subset : ∀ g ∈ Gb ∪ Gc, ∃ y ∈ f', g = {c, y} := by
        intro g hg
        have hg_subset : g ⊆ W := hW g hg
        have hg_card : g.card = 2 := by
          grind
        have hg_inter : (g ∩ f').Nonempty := by
          by_cases hgGb : g ∈ Gb <;> by_cases hgGc : g ∈ Gc <;> simp_all +decide [ Finset.disjoint_left ];
          · exact hcab _ ( hf'.1.elim ( fun h => h.symm ▸ he ) fun h => h.symm ▸ hf ) _ hgGb |> fun ⟨ x, hx ⟩ => ⟨ x, by aesop ⟩;
          · exact hcac _ ( hf'.1.elim ( fun h => h.symm ▸ he ) fun h => h.symm ▸ hf ) _ hgGc |> fun ⟨ x, hx ⟩ => ⟨ x, by aesop ⟩
        have hg_form : ∃ y ∈ f', g = {c, y} := by
          obtain ⟨ y, hy ⟩ := hg_inter;
          use y;
          rw [ Finset.eq_of_subset_of_card_le ( Finset.insert_subset_iff.mpr ⟨ hc g hg, Finset.singleton_subset_iff.mpr ( Finset.mem_of_mem_inter_left hy ) ⟩ ) ] ; aesop;
          grind
        exact hg_form;
      have hGbGc_subset : Gb ∪ Gc ⊆ Finset.image (fun y => {c, y}) f' := by
        intro g hg; obtain ⟨ y, hy, rfl ⟩ := hGbGc_subset g hg; exact Finset.mem_image_of_mem _ hy;
      exact le_trans ( Finset.card_le_card hGbGc_subset ) ( Finset.card_image_le.trans ( by aesop ) );
    have hGbGc_card : (Gb.biUnion id).card ≤ 2 * Gb.card ∧ (Gc.biUnion id).card ≤ 2 * Gc.card := by
      exact ⟨ le_trans ( Finset.card_biUnion_le ) ( by simpa [ mul_comm ] using Finset.sum_le_sum fun x hx => hb x hx |>.1.le ), le_trans ( Finset.card_biUnion_le ) ( by simpa [ mul_comm ] using Finset.sum_le_sum fun x hx => ‹∀ e ∈ Gc, e.card = 2 ∧ e ⊆ U› x hx |>.1.le ) ⟩;
    have hGa_card : (Ga.biUnion id).card ≤ U.card := by
      exact Finset.card_le_card ( Finset.biUnion_subset.mpr fun x hx => ha x hx |>.2 );
    simp_all +decide [ Finset.disjoint_iff_inter_eq_empty ];
    grind;
  · -- Prove ∀ h ∈ Ga, h ⊆ W.
    have hGa_subset_W : ∀ h ∈ Ga, h ⊆ W := by
      intro h hh
      have h_meet : ∀ g ∈ Gb ∪ Gc, (h ∩ g).Nonempty := by
        grind;
      -- If ∃ p q ∈ Gb ∪ Gc with Disjoint p q, then p,q ⊆ W (hW) disjoint card-2, h meets both, edge_in_union gives h ⊆ p ∪ q ⊆ W.
      by_cases h_disjoint : ∃ p q, p ∈ Gb ∪ Gc ∧ q ∈ Gb ∪ Gc ∧ Disjoint p q;
      · obtain ⟨ p, q, hp, hq, hpq ⟩ := h_disjoint;
        have h_subset : h ⊆ p ∪ q := by
          apply edge_in_union;
          any_goals solve_by_elim;
          · grind;
          · grind;
          · exact ha h hh |>.1;
        exact h_subset.trans ( Finset.union_subset ( hW p hp ) ( hW q hq ) );
      · -- Apply star_or_triangle to Gb ∪ Gc; the common-vertex disjunct is excluded by hypothesis, so its support T := (Gb∪Gc).biUnion id has T.card ≤ 3 and (by hW) T ⊆ W.
        obtain ⟨T, hT⟩ : ∃ T : Finset V, T = (Gb ∪ Gc).biUnion id ∧ T.card ≤ 3 ∧ T ⊆ W := by
          have := star_or_triangle ( show ∀ e ∈ Gb ∪ Gc, e.card = 2 from ?_ ) ( show ∀ e ∈ Gb ∪ Gc, ∀ f ∈ Gb ∪ Gc, ( e ∩ f ).Nonempty from ?_ );
          · exact ⟨ _, rfl, this.resolve_right h_common, Finset.biUnion_subset.mpr fun x hx => hW x hx ⟩;
          · grind;
          · simp_all +decide [ Finset.disjoint_left ];
            exact fun e he f hf => by obtain ⟨ x, hx₁, hx₂ ⟩ := h_disjoint e he f hf; exact ⟨ x, Finset.mem_inter_of_mem hx₁ hx₂ ⟩ ;
        -- If h had a vertex outside T, h's other vertex would lie in every edge of Gb∪Gc (to meet each), i.e. be a common vertex — contradiction; so both vertices of h are in T, giving h ⊆ T ⊆ W.
        by_contra h_contra
        obtain ⟨v, hv⟩ : ∃ v ∈ h, v ∉ T := by
          exact Finset.not_subset.mp fun h' => h_contra <| h'.trans hT.2.2;
        obtain ⟨w, hw⟩ : ∃ w ∈ h, w ≠ v := by
          exact Finset.exists_mem_ne ( by linarith [ ha h hh ] ) v;
        have h_w_in_T : ∀ g ∈ Gb ∪ Gc, w ∈ g := by
          intro g hg; specialize h_meet g hg; simp_all +decide [ Finset.Nonempty ] ;
          obtain ⟨ x, hx₁, hx₂ ⟩ := h_meet; have := Finset.card_eq_two.mp ( ha _ hh |>.1 ) ; obtain ⟨ y, z, hy, hz, h ⟩ := this; simp_all +decide [ Finset.subset_iff ] ;
          grind +revert;
        exact h_common ⟨ w, h_w_in_T ⟩;
    -- Then Va, Vb, Vc ⊆ W (Va by this, Vb,Vc by hW), each card ≤ 4, total ≤ 12 (le_max_left).
    have hVa_subset_W : (Ga.biUnion id) ⊆ W := by
      exact Finset.biUnion_subset.mpr hGa_subset_W
    have hVb_subset_W : (Gb.biUnion id) ⊆ W := by
      exact Finset.biUnion_subset.mpr fun g hg => hW g ( Finset.mem_union_left _ hg )
    have hVc_subset_W : (Gc.biUnion id) ⊆ W := by
      exact Finset.biUnion_subset.mpr fun g hg => hW g ( Finset.mem_union_right _ hg );
    exact le_trans ( add_le_add_three ( Finset.card_le_card hVa_subset_W ) ( Finset.card_le_card hVb_subset_W ) ( Finset.card_le_card hVc_subset_W ) ) ( by simp +decide [ hW_card ] )

/-
**Lemma 2, Case B.** Every colour class is pairwise intersecting.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma lemma2_caseB (U : Finset V) (G1 G2 G3 : Finset (Finset V))
    (h1 : ∀ e ∈ G1, e.card = 2 ∧ e ⊆ U) (h2 : ∀ e ∈ G2, e.card = 2 ∧ e ⊆ U)
    (h3 : ∀ e ∈ G3, e.card = 2 ∧ e ⊆ U)
    (hd12 : Disjoint G1 G2) (hd13 : Disjoint G1 G3) (hd23 : Disjoint G2 G3)
    (hc12 : ∀ e ∈ G1, ∀ f ∈ G2, (e ∩ f).Nonempty)
    (hc13 : ∀ e ∈ G1, ∀ f ∈ G3, (e ∩ f).Nonempty)
    (hc23 : ∀ e ∈ G2, ∀ f ∈ G3, (e ∩ f).Nonempty)
    (hpi1 : ∀ e ∈ G1, ∀ f ∈ G1, (e ∩ f).Nonempty)
    (hpi2 : ∀ e ∈ G2, ∀ f ∈ G2, (e ∩ f).Nonempty)
    (hpi3 : ∀ e ∈ G3, ∀ f ∈ G3, (e ∩ f).Nonempty) :
    (G1.biUnion id).card + (G2.biUnion id).card + (G3.biUnion id).card
      ≤ max 12 (U.card + 4) := by
  by_cases h : ( G1.biUnion id ).card ≤ 4 ∧ ( G2.biUnion id ).card ≤ 4 ∧ ( G3.biUnion id ).card ≤ 4 <;> simp_all +decide;
  · grind;
  · -- By the symmetry of the hypotheses you may treat the three possibilities the same way; describe it for the class whose support is ≥ 5, call it Ga (one of G1,G2,G3), with the other two Gb, Gc.
    suffices h_symm : ∀ (Ga Gb Gc : Finset (Finset V)),
      (∀ e ∈ Ga, e.card = 2 ∧ e ⊆ U) →
      (∀ e ∈ Gb, e.card = 2 ∧ e ⊆ U) →
      (∀ e ∈ Gc, e.card = 2 ∧ e ⊆ U) →
      Disjoint Ga Gb →
      Disjoint Ga Gc →
      Disjoint Gb Gc →
      (∀ e ∈ Ga, ∀ f ∈ Gb, (e ∩ f).Nonempty) →
      (∀ e ∈ Ga, ∀ f ∈ Gc, (e ∩ f).Nonempty) →
      (∀ e ∈ Gb, ∀ f ∈ Gc, (e ∩ f).Nonempty) →
      (∀ e ∈ Ga, ∀ f ∈ Ga, (e ∩ f).Nonempty) →
      (∀ e ∈ Gb, ∀ f ∈ Gb, (e ∩ f).Nonempty) →
      (∀ e ∈ Gc, ∀ f ∈ Gc, (e ∩ f).Nonempty) →
      (Ga.biUnion id).card ≥ 5 →
      (Ga.biUnion id).card + (Gb.biUnion id).card + (Gc.biUnion id).card ≤ U.card + 4 by
        by_cases h1 : (G1.biUnion id).card ≥ 5;
        · exact Or.inr ( h_symm G1 G2 G3 ‹_› ‹_› ‹_› hd12 hd13 hd23 hc12 hc13 hc23 hpi1 hpi2 hpi3 h1 );
        · by_cases h2 : (G2.biUnion id).card ≥ 5;
          · specialize h_symm G2 G1 G3 ; simp_all +decide [ add_comm, add_left_comm, add_assoc ];
            exact Or.inr ( h_symm ( Finset.disjoint_left.mpr fun x hx1 hx2 => Finset.disjoint_left.mp hd12 hx2 hx1 ) fun e he f hf => by simpa only [ Finset.inter_comm ] using hc12 f hf e he );
          · specialize h_symm G3 G1 G2 ; simp_all +decide [ add_comm, add_left_comm, add_assoc ];
            exact Or.inr ( h_symm ( Finset.disjoint_left.mpr fun x hx1 hx2 => Finset.disjoint_left.mp hd13 hx2 hx1 ) ( Finset.disjoint_left.mpr fun x hx1 hx2 => Finset.disjoint_left.mp hd23 hx2 hx1 ) ( fun e he f hf => by simpa only [ Finset.inter_comm ] using hc13 f hf e he ) ( fun e he f hf => by simpa only [ Finset.inter_comm ] using hc23 f hf e he ) ( by linarith [ h ( by linarith ) ( by linarith ) ] ) );
    intros Ga Gb Gc ha hb hc hdab hdac hdbc hcab hcac hcbc hpiGa hpiGb hpiGc hGa_card
    obtain ⟨c, hcGa⟩ : ∃ c, ∀ e ∈ Ga, c ∈ e := by
      have := star_or_triangle ( fun e he => ha e he |>.1 ) hpiGa;
      exact this.resolve_left ( by linarith )
    have hcU : c ∈ U := by
      exact ha _ ( Classical.choose_spec ( Finset.nonempty_of_ne_empty ( by aesop_cat ) ) ) |>.2 ( hcGa _ ( Classical.choose_spec ( Finset.nonempty_of_ne_empty ( by aesop_cat ) ) ) )
    have hcGb : ∀ g ∈ Gb, c ∈ g := by
      intro g hg
      by_contra hcGb_contra
      have h_leaves : (Ga.biUnion id \ {c}).card ≥ 4 := by
        grind;
      have h_leaves_subset : ∀ x ∈ Ga.biUnion id \ {c}, x ∈ g := by
        simp_all +decide [ Finset.Nonempty ];
        intro x e he hx hx'; specialize hcab e he g hg; obtain ⟨ y, hy, hy' ⟩ := hcab; have := ha e he; have := hb g hg; simp_all +decide [ Finset.card_eq_two ] ;
        grind;
      exact absurd ( Finset.card_le_card h_leaves_subset ) ( by linarith [ hb g hg ] )
    have hcGc : ∀ g ∈ Gc, c ∈ g := by
      intro g hg
      by_contra hgc
      have h_leaves : (Ga.biUnion id \ {c}).card ≥ 4 := by
        grind;
      have h_leaves_subset : (Ga.biUnion id \ {c}) ⊆ g := by
        intro x hx; simp_all +decide ;
        obtain ⟨ ⟨ e, he, hx ⟩, hx' ⟩ := hx;
        obtain ⟨ y, hy ⟩ := hcac e he g hg;
        have := Finset.eq_of_subset_of_card_le ( Finset.insert_subset hx ( Finset.singleton_subset_iff.mpr ( hcGa e he ) ) ) ; simp_all +decide ;
        grind;
      exact absurd ( Finset.card_le_card h_leaves_subset ) ( by linarith [ hc g hg ] );
    have h_inter : ∀ x ≠ c, (x ∈ (Ga.biUnion id) ∧ x ∈ (Gb.biUnion id)) ∨ (x ∈ (Ga.biUnion id) ∧ x ∈ (Gc.biUnion id)) ∨ (x ∈ (Gb.biUnion id) ∧ x ∈ (Gc.biUnion id)) → False := by
      simp_all +decide [ Finset.disjoint_left ];
      refine' fun x hx => ⟨ _, _, _ ⟩;
      · intro e he hx f hf; have := ha e he; have := hb f hf; simp_all +decide [ Finset.card_eq_two ] ;
        grind;
      · intro e he hx f hf hxf; have := ha e he; have := hc f hf; simp_all +decide [ Finset.card_eq_two ] ;
        grind;
      · intro e he hx f hf hx'; have := hb e he; have := hc f hf; simp_all +decide [ Finset.subset_iff ] ;
        have := Finset.eq_of_subset_of_card_le ( show { x, c } ⊆ e from Finset.insert_subset_iff.mpr ⟨ hx, Finset.singleton_subset_iff.mpr ( hcGb e he ) ⟩ ) ; have := Finset.eq_of_subset_of_card_le ( show { x, c } ⊆ f from Finset.insert_subset_iff.mpr ⟨ hx', Finset.singleton_subset_iff.mpr ( hcGc f hf ) ⟩ ) ; simp_all +decide ;
    have h_inter_card : (Ga.biUnion id ∩ Gb.biUnion id).card ≤ 1 ∧ (Ga.biUnion id ∩ Gc.biUnion id).card ≤ 1 ∧ (Gb.biUnion id ∩ Gc.biUnion id).card ≤ 1 := by
      refine' ⟨ Finset.card_le_one.mpr _, Finset.card_le_one.mpr _, Finset.card_le_one.mpr _ ⟩;
      · grind;
      · grind +splitIndPred;
      · grind;
    have h_union_card : (Ga.biUnion id ∪ Gb.biUnion id ∪ Gc.biUnion id).card ≤ U.card := by
      exact Finset.card_le_card ( Finset.union_subset ( Finset.union_subset ( Finset.biUnion_subset.mpr fun e he => ha e he |>.2 ) ( Finset.biUnion_subset.mpr fun e he => hb e he |>.2 ) ) ( Finset.biUnion_subset.mpr fun e he => hc e he |>.2 ) );
    have := Finset.card_union_add_card_inter ( Ga.biUnion id ) ( Gb.biUnion id ) ; simp_all +decide ;
    have := Finset.card_union_add_card_inter ( Ga.biUnion id ∪ Gb.biUnion id ) ( Gc.biUnion id ) ; simp_all +decide ;
    rw [ Finset.union_inter_distrib_right ] at this;
    linarith [ show Finset.card ( Ga.biUnion id ∩ Gc.biUnion id ∪ Gb.biUnion id ∩ Gc.biUnion id ) ≤ 2 by exact le_trans ( Finset.card_union_le _ _ ) ( by linarith ) ]

/-
**Lemma 2.** Let `G1, G2, G3` be the three colour classes of a simple graph on
the vertex set `U`, with edges being `2`-element subsets of `U`.  Assume the three
classes are pairwise edge-disjoint and that no two vertex-disjoint edges have
different colours (cross-intersecting condition).  Then the total size of the
three colour supports is at most `max 12 (|U| + 4)`.

The proof is split into helper lemmas `edge_in_union`, `support_card_le`,
`star_or_triangle`, and the two cases `lemma2_caseA` and `lemma2_caseB`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma lemma2 (U : Finset V) (G1 G2 G3 : Finset (Finset V))
    (h1 : ∀ e ∈ G1, e.card = 2 ∧ e ⊆ U) (h2 : ∀ e ∈ G2, e.card = 2 ∧ e ⊆ U)
    (h3 : ∀ e ∈ G3, e.card = 2 ∧ e ⊆ U)
    (hd12 : Disjoint G1 G2) (hd13 : Disjoint G1 G3) (hd23 : Disjoint G2 G3)
    (hc12 : ∀ e ∈ G1, ∀ f ∈ G2, (e ∩ f).Nonempty)
    (hc13 : ∀ e ∈ G1, ∀ f ∈ G3, (e ∩ f).Nonempty)
    (hc23 : ∀ e ∈ G2, ∀ f ∈ G3, (e ∩ f).Nonempty) :
    (G1.biUnion id).card + (G2.biUnion id).card + (G3.biUnion id).card
      ≤ max 12 (U.card + 4) := by
  by_cases h_caseA : ∃ e ∈ G1, ∃ f ∈ G1, Disjoint e f;
  · obtain ⟨ e, he, f, hf, hef ⟩ := h_caseA; exact lemma2_caseA U G1 G2 G3 h1 h2 h3 hd12 hd13 hd23 hc12 hc13 hc23 e f he hf hef;
  · by_cases h_caseB : ∃ e ∈ G2, ∃ f ∈ G2, Disjoint e f;
    · convert lemma2_caseA U G2 G1 G3 _ _ _ _ _ _ _ _ using 1;
      any_goals tauto;
      · grind;
      · exact fun e he f hf => by simpa only [ Finset.inter_comm ] using hc12 f hf e he;
    · by_cases h_caseC : ∃ e ∈ G3, ∃ f ∈ G3, Disjoint e f;
      · have := lemma2_caseA U G3 G1 G2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_;
        any_goals tauto;
        · grind;
        · exact fun e he f hf => by simpa only [ Finset.inter_comm ] using hc13 f hf e he;
        · exact fun e he f hf => by simpa only [ Finset.inter_comm ] using hc23 f hf e he;
      · apply lemma2_caseB U G1 G2 G3 h1 h2 h3 hd12 hd13 hd23 hc12 hc13 hc23;
        · exact fun e he f hf => Finset.not_disjoint_iff_nonempty_inter.mp fun h => h_caseA ⟨ e, he, f, hf, h ⟩;
        · exact fun e he f hf => Finset.not_disjoint_iff_nonempty_inter.mp fun h => h_caseB ⟨ e, he, f, hf, h ⟩;
        · exact fun e he f hf => Finset.not_disjoint_iff_nonempty_inter.mp fun h => h_caseC ⟨ e, he, f, hf, h ⟩

/- ## Lemma 3 (arithmetic) -/

/-
**Lemma 3.** A purely arithmetic inequality used to bound the cover number.
Here `K = max 12 (u + 4)` and `d` is allowed to be negative.  The hypothesis
`h2` is the integer form of `d ≤ 1 + (K - u) t / (2u)`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma lemma3 (u : ℕ) (hu : 1 ≤ u) (t : ℕ) (d : ℤ) (K : ℤ)
    (hK : K = max 12 ((u : ℤ) + 4))
    (h1 : (t : ℤ) ≤ (u : ℤ) - 2 * d + 1)
    (h2 : 2 * (u : ℤ) * (d - 1) ≤ (K - u) * t) :
    d + 4 * (((u + 1) / 2 : ℕ) : ℤ) - 2 * (u : ℤ) ≤ 4 := by
  norm_num [ Nat.cast_div ] at *;
  cases max_cases ( 12 : ℤ ) ( u + 4 ) <;> nlinarith [ Int.mul_ediv_add_emod ( u + 1 ) 2, Int.emod_nonneg ( u + 1 ) two_ne_zero, Int.emod_lt_of_pos ( u + 1 ) two_pos ]

/- ## Lemma 4 (residual cover bound)

We form the auxiliary `3`-uniform system `T` on the points `E(J)` whose edges are
the size-`3` blocks `B_v = {A ∈ E(J) : v ∈ A}`, take a maximum matching `M`, and
count around the unmatched points.  The deep counting step is `eq4_nat`. -/

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- The block of a vertex `v`: the edges of `J` (as points) that contain `v`. -/
def block (J : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  J.filter (fun A => v ∈ A)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- A *good triple* is a `3`-element set of edges sharing a common vertex; i.e. a
size-`3` block. -/
def IsGoodTriple (J : Finset (Finset V)) (S : Finset (Finset V)) : Prop :=
  S.card = 3 ∧ ∃ v, S = block J v

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- A *matching* in the auxiliary triple system: pairwise-disjoint good triples. -/
def IsMatching (J : Finset (Finset V)) (M : Finset (Finset (Finset V))) : Prop :=
  (∀ S ∈ M, IsGoodTriple J S) ∧ ∀ S ∈ M, ∀ T ∈ M, S ≠ T → Disjoint S T

/-
A maximum matching exists.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma exists_max_matching (J : Finset (Finset V)) :
    ∃ M : Finset (Finset (Finset V)), IsMatching J M ∧
      ∀ M', IsMatching J M' → M'.card ≤ M.card := by
  apply Classical.byContradiction
  intro h_no_max;
  -- Let's denote the set of all matchings by `𝓜`.
  set M_set := {M : Finset (Finset (Finset V)) | IsMatching J M};
  -- Since $M_set$ is nonempty and finite, it must have a maximum element.
  have h_max : ∃ M ∈ M_set, ∀ M' ∈ M_set, M'.card ≤ M.card := by
    apply_rules [ Set.exists_max_image ];
    · exact Set.finite_iff_bddAbove.mpr ⟨ Finset.powerset J, fun M hM => Finset.le_iff_subset.mpr fun S hS => Finset.mem_powerset.mpr <| hM.1 S hS |> fun h => h.2.choose_spec ▸ Finset.filter_subset _ _ ⟩;
    · exact ⟨ ∅, by unfold M_set IsMatching; simp +decide ⟩;
  exact h_no_max ⟨ h_max.choose, h_max.choose_spec.1, fun M' hM' => h_max.choose_spec.2 M' hM' ⟩

/-
Maximality forbids a good triple inside the unmatched set `U = E(J) \ ⋃ M`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma no_good_triple_in_U (J : Finset (Finset V)) (M : Finset (Finset (Finset V)))
    (hM : IsMatching J M) (hMmax : ∀ M', IsMatching J M' → M'.card ≤ M.card)
    {S : Finset (Finset V)} (hS : IsGoodTriple J S) (hSU : S ⊆ J \ M.biUnion id) :
    False := by
  contrapose! hMmax;
  refine' ⟨ Insert.insert S M, _, _ ⟩ <;> simp_all +decide [ IsMatching ];
  · simp_all +decide [ Finset.subset_iff, Finset.disjoint_left ];
    grind;
  · rw [ Finset.card_insert_of_notMem ];
    · exact Nat.lt_succ_self _;
    · intro hSM; have := hSU ( Classical.choose_spec ( Finset.card_pos.mp ( by linarith [ hS.1 ] ) ) ) ; simp_all +decide [ Finset.subset_iff ] ;
      exact this.2 _ hSM ( Classical.choose_spec ( Finset.card_pos.mp ( by linarith [ hS.1 ] ) ) )

/-
The number of edges splits as `q = 3t + u` (`t = |M|`, `u = |U|`).
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma matching_q (J : Finset (Finset V)) (M : Finset (Finset (Finset V)))
    (hM : IsMatching J M) :
    J.card = 3 * M.card + (J \ M.biUnion id).card := by
  rw [ show J.card = ( M.biUnion id ).card + ( J \ M.biUnion id ).card from ?_, show 3 * M.card = ( M.biUnion id ).card from ?_ ];
  · rw [ Finset.card_biUnion ];
    · rw [ Finset.sum_const_nat ];
      rw [ mul_comm ];
      exact fun x hx => hM.1 x hx |>.1;
    · exact fun x hx y hy hxy => hM.2 x hx y hy hxy;
  · rw [ ← Finset.card_union_of_disjoint, Finset.union_sdiff_of_subset ];
    · intro x hx
      obtain ⟨S, hS⟩ := Finset.mem_biUnion.mp hx
      have hS_block : S = block J (Classical.choose (hM.1 S hS.1).2) := by
        exact Classical.choose_spec ( hM.1 S hS.1 |>.2 );
      exact Finset.mem_filter.mp ( hS_block ▸ hS.2 ) |>.1;
    · exact Finset.disjoint_sdiff

/-
An intersecting family can be covered by `⌈n/2⌉` vertices (pair up edges; each
pair shares a vertex).
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma intersecting_cover_half (F : Finset (Finset V))
    (hF : ∀ x ∈ F, ∀ y ∈ F, (x ∩ y).Nonempty) :
    ∃ C : Finset V, (∀ E ∈ F, ∃ v ∈ C, v ∈ E) ∧ C.card ≤ (F.card + 1) / 2 := by
  induction' hn : F.card using Nat.strong_induction_on with n ih generalizing F;
  by_cases h_empty : F = ∅;
  · exact ⟨ ∅, by simp +decide [ h_empty ] ⟩;
  · by_cases h_card : F.card ≤ 1;
    · obtain ⟨ E, hE ⟩ := Finset.card_pos.mp ( Finset.card_pos.mpr ( Finset.nonempty_of_ne_empty h_empty ) );
      obtain ⟨ v, hv ⟩ := hF E hE E hE;
      use {v}; simp [hv];
      rw [ Finset.card_le_one_iff_subset_singleton ] at h_card ; aesop;
    · obtain ⟨x, y, hx, hy, hxy⟩ : ∃ x y : Finset V, x ∈ F ∧ y ∈ F ∧ x ≠ y ∧ (x ∩ y).Nonempty := by
        obtain ⟨ x, hx, y, hy, hxy ⟩ := Finset.one_lt_card.1 ( lt_of_not_ge h_card ) ; exact ⟨ x, y, hx, hy, hxy, hF x hx y hy ⟩ ;
      obtain ⟨ v, hv ⟩ := hxy.2;
      obtain ⟨ C, hC₁, hC₂ ⟩ := ih ( F.card - 2 ) ( by omega ) ( F \ { x, y } ) ( fun E hE F hF => hF |> fun hF => by aesop ) ( by rw [ Finset.card_sdiff ] ; aesop );
      refine' ⟨ Insert.insert v C, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
      · intro E hE; by_cases hE' : E = x <;> by_cases hE'' : E = y <;> simp_all +decide ;
      · exact le_trans ( Finset.card_insert_le _ _ ) ( by omega )

/-
Cover bound from a matching: `τ(J) ≤ t + ⌈u/2⌉`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma matching_cover (J : Finset (Finset V)) (hint : Intersecting J)
    (M : Finset (Finset (Finset V))) (hM : IsMatching J M) :
    coverNum J ≤ M.card + ((J \ M.biUnion id).card + 1) / 2 := by
  -- Construct a cover of $J$ of size at most $M.card + ((J \ M.biUnion id).card + 1) / 2$.
  obtain ⟨C, hC⟩ : ∃ C : Finset V, (∀ E ∈ J, ∃ v ∈ C, v ∈ E) ∧ C.card ≤ M.card + ((J \ M.biUnion id).card + 1) / 2 := by
    -- Let $C_c$ be the set of vertices in the matched part.
    obtain ⟨Cc, hCc⟩ : ∃Cc : Finset V, (∀ E ∈ M.biUnion id, ∃ v ∈ Cc, v ∈ E) ∧ Cc.card ≤ M.card := by
      have hCc : ∀ S ∈ M, ∃ v, v ∈ S.biUnion id ∧ S = block J v := by
        intro S hS
        obtain ⟨v, hv⟩ := hM.left S hS |>.2
        use v
        simp [hv];
        have := hM.1 S hS; simp_all +decide [ IsGoodTriple ] ;
        exact Exists.elim ( Finset.card_pos.mp ( by linarith ) ) fun x hx => ⟨ x, hx, by unfold block at hx; aesop ⟩;
      choose! v hv hv' using hCc;
      refine' ⟨ Finset.image ( fun S : M => v S S.2 ) Finset.univ, _, _ ⟩;
      · simp +decide [ Finset.mem_biUnion ];
        grind +locals;
      · exact Finset.card_image_le.trans ( by simp +decide );
    -- Let $C_u$ be the set of vertices in the unmatched part.
    obtain ⟨Cu, hCu⟩ : ∃ Cu : Finset V, (∀ E ∈ J \ M.biUnion id, ∃ v ∈ Cu, v ∈ E) ∧ Cu.card ≤ ((J \ M.biUnion id).card + 1) / 2 := by
      apply intersecting_cover_half;
      exact fun x hx y hy => ‹∀ E ∈ J, ∀ F ∈ J, ( E ∩ F ).Nonempty› x ( Finset.mem_sdiff.mp hx |>.1 ) y ( Finset.mem_sdiff.mp hy |>.1 );
    use Cc ∪ Cu;
    exact ⟨ fun E hE => if hE' : E ∈ M.biUnion id then by obtain ⟨ v, hv₁, hv₂ ⟩ := hCc.1 E hE'; exact ⟨ v, Finset.mem_union_left _ hv₁, hv₂ ⟩ else by obtain ⟨ v, hv₁, hv₂ ⟩ := hCu.1 E ( Finset.mem_sdiff.mpr ⟨ hE, hE' ⟩ ) ; exact ⟨ v, Finset.mem_union_right _ hv₁, hv₂ ⟩, le_trans ( Finset.card_union_le _ _ ) ( add_le_add hCc.2 hCu.2 ) ⟩;
  exact le_trans ( coverNum_le hC.1 ) hC.2

/- ### Machinery for equation (4)

We abbreviate `C = ⋃ M` (matched points), `U = E(J) \ C` (unmatched points),
`t = |M|`, `u = |U|`.  `selVerts` are the chosen witnesses for `2`-subsets of `U`,
`coveredUC` the set of `U`–`C` pairs covered by a selected witness, and
`linkGraph p` the colour class of `p` in a matched triple. -/

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- The witness vertices chosen for the `2`-element subsets of `U` (via `ω`). -/
def selVerts (J : Finset (Finset V)) (M : Finset (Finset (Finset V)))
    (ω : Finset (Finset V) → V) : Finset V :=
  ((J \ M.biUnion id).powersetCard 2).image ω

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- `U`–`C` pairs covered by a selected witness. -/
def coveredUC (J : Finset (Finset V)) (M : Finset (Finset (Finset V)))
    (ω : Finset (Finset V) → V) : Finset (Finset V × Finset V) :=
  ((J \ M.biUnion id) ×ˢ M.biUnion id).filter
    (fun pr => ∃ v ∈ selVerts J M ω, v ∈ pr.1 ∧ v ∈ pr.2)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- For a point `p ∈ C`, the number of `U`-points `x` with `(x,p)` covered. -/
def gCount (J : Finset (Finset V)) (M : Finset (Finset (Finset V)))
    (ω : Finset (Finset V) → V) (p : Finset V) : ℕ :=
  ((J \ M.biUnion id).filter
    (fun x => ∃ v ∈ selVerts J M ω, v ∈ x ∧ v ∈ p)).card

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- The colour class of `p`: `2`-subsets `s` of `U` whose witness block is `s ∪ {p}`. -/
def linkGraph (J : Finset (Finset V)) (M : Finset (Finset (Finset V)))
    (ω : Finset (Finset V) → V) (p : Finset V) : Finset (Finset (Finset V)) :=
  ((J \ M.biUnion id).powersetCard 2).filter (fun s => block J (ω s) = insert p s)

/-
Double counting: total vertex–`U` incidences equal `u * r`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma incid_total (r : ℕ) (J : Finset (Finset V)) (huni : IsUniform r J)
    (M : Finset (Finset (Finset V))) :
    ∑ v ∈ J.biUnion id, (block J v ∩ (J \ M.biUnion id)).card
      = (J \ M.biUnion id).card * r := by
  have h_double_counting : ∀ x ∈ J \ M.biUnion id, ∑ v ∈ J.biUnion id, (if v ∈ x then 1 else 0) = r := by
    intro x hx
    have hx_card : x.card = r := by
      exact huni x ( Finset.mem_sdiff.mp hx |>.1 ) ▸ rfl
    simp [hx_card];
    convert hx_card using 2 ; ext v ; aesop;
  convert Finset.sum_congr rfl h_double_counting using 1;
  · rw [ Finset.sum_comm, Finset.sum_congr rfl ];
    simp +contextual [ block ];
    exact fun x y hy hx => congr_arg Finset.card ( by ext; aesop );
  · rw [ Finset.sum_const, smul_eq_mul, mul_comm ]

/-
The matched points number `3t`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma card_matched (J : Finset (Finset V)) (M : Finset (Finset (Finset V)))
    (hM : IsMatching J M) : (M.biUnion id).card = 3 * M.card := by
  rw [ Finset.card_biUnion ];
  · rw [ Finset.sum_const_nat ];
    rw [ mul_comm ];
    exact fun x hx => hM.1 x hx |>.1;
  · exact fun x hx y hy hxy => hM.2 x hx y hy hxy

/-
A witness function for `U`-pairs: injective, with `ω s` a common vertex of the
two edges of `s`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma exists_witness (J : Finset (Finset V)) (hint : Intersecting J)
    (hdeg : ∀ v, edgeDeg J v ≤ 3)
    (M : Finset (Finset (Finset V))) (hM : IsMatching J M)
    (hMmax : ∀ M', IsMatching J M' → M'.card ≤ M.card)
    (hu : 0 < (J \ M.biUnion id).card) :
    ∃ ω : Finset (Finset V) → V,
      (∀ s ∈ (J \ M.biUnion id).powersetCard 2, ∀ x ∈ s, ω s ∈ x) ∧
      Set.InjOn ω ↑((J \ M.biUnion id).powersetCard 2) := by
  by_contra! h_contra;
  obtain ⟨ω, hω⟩ : ∃ ω : Finset (Finset V) → V, (∀ s ∈ Finset.powersetCard 2 (J \ M.biUnion id), ∀ x ∈ s, ω s ∈ x) := by
    have hω_exists : ∀ s ∈ Finset.powersetCard 2 (J \ M.biUnion id), ∃ v, ∀ x ∈ s, v ∈ x := by
      simp +decide [ Finset.mem_powersetCard ];
      intro s hs hs'; rw [ Finset.card_eq_two ] at hs'; obtain ⟨ x, y, hxy ⟩ := hs'; simp_all +decide [ Finset.subset_iff ] ;
      exact Exists.elim ( ‹Intersecting J› x hs.1.1 y hs.2.1 ) fun v hv => ⟨ v, by aesop ⟩;
    exact ⟨ fun s => if hs : s ∈ Finset.powersetCard 2 ( J \ M.biUnion id ) then Classical.choose ( hω_exists s hs ) else Classical.choice ( show Nonempty V from by
                                                                                                                                              obtain ⟨ x, hx ⟩ := Finset.card_pos.mp hu; exact ⟨ Classical.choose ( Finset.card_pos.mp ( show 0 < Finset.card x from Finset.card_pos.mpr ( Intersecting.edge_nonempty ‹_› ( Finset.mem_sdiff.mp hx |>.1 ) ) ) ) ⟩ ; ), fun s hs x hx => by simpa [ hs ] using Classical.choose_spec ( hω_exists s hs ) x hx ⟩;
  obtain ⟨s, s', hs, hs', h_eq⟩ : ∃ s s' : Finset (Finset V), s ∈ Finset.powersetCard 2 (J \ M.biUnion id) ∧ s' ∈ Finset.powersetCard 2 (J \ M.biUnion id) ∧ s ≠ s' ∧ ω s = ω s' := by
    specialize h_contra ω hω;
    simp_all +decide [ Set.InjOn ];
    exact ⟨ _, ⟨ h_contra.choose_spec.1, h_contra.choose_spec.2.1 ⟩, _, ⟨ h_contra.choose_spec.2.2.choose_spec.1, h_contra.choose_spec.2.2.choose_spec.2.1 ⟩, h_contra.choose_spec.2.2.choose_spec.2.2.2, h_contra.choose_spec.2.2.choose_spec.2.2.1 ⟩;
  have h_card : (s ∪ s').card ≤ 3 := by
    have h_card : (s ∪ s').card ≤ (J.filter (fun A => ω s ∈ A)).card := by
      refine Finset.card_le_card ?_;
      grind;
    exact h_card.trans ( hdeg _ );
  have h_card_eq : (s ∪ s').card = 3 := by
    have h_card_eq : (s ∩ s').card ≤ 1 := by
      have := Finset.mem_powersetCard.mp hs; have := Finset.mem_powersetCard.mp hs'; simp_all +decide ;
      exact Nat.le_of_lt_succ ( lt_of_le_of_ne ( Nat.le_trans ( Finset.card_le_card ( Finset.inter_subset_left ) ) ( by linarith ) ) fun h => h_eq.1 <| Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left ) ( by linarith ) |> fun h' => Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right ) ( by linarith ) |> fun h'' => by aesop );
    grind;
  have h_card_eq : s ∪ s' = block J (ω s) := by
    refine' Finset.eq_of_subset_of_card_le ( fun x hx => _ ) _;
    · grind +locals;
    · exact le_trans ( hdeg _ ) ( by linarith );
  have h_card_eq : IsGoodTriple J (block J (ω s)) := by
    exact ⟨ by aesop, ω s, rfl ⟩;
  apply no_good_triple_in_U J M hM hMmax h_card_eq;
  grind

/-
Lower bound from witnesses: `∑_{v ∈ Sel} a(v) ≥ u(u-1)`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma witness_lower (J : Finset (Finset V))
    (M : Finset (Finset (Finset V)))
    (ω : Finset (Finset V) → V)
    (hωmem : ∀ s ∈ (J \ M.biUnion id).powersetCard 2, ∀ x ∈ s, ω s ∈ x)
    (hωinj : Set.InjOn ω ↑((J \ M.biUnion id).powersetCard 2)) :
    (J \ M.biUnion id).card * ((J \ M.biUnion id).card - 1)
      ≤ ∑ v ∈ selVerts J M ω, (block J v ∩ (J \ M.biUnion id)).card := by
  rw [ selVerts ];
  rw [ Finset.sum_image <| by tauto ];
  refine' le_trans _ ( Finset.sum_le_sum fun s hs => Finset.card_mono <| show s ⊆ block J ( ω s ) ∩ ( J \ M.biUnion id ) from _ );
  · rw [ Finset.sum_congr rfl fun x hx => Finset.mem_powersetCard.mp hx |>.2 ] ; simp +decide [ Nat.choose_two_right ];
    rw [ Nat.div_mul_cancel ( even_iff_two_dvd.mp ( Nat.even_mul_pred_self _ ) ) ];
  · simp_all +decide [ Finset.subset_iff, block ]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- Matched points are edges of `J`. -/
lemma matched_subset (J : Finset (Finset V)) (M : Finset (Finset (Finset V)))
    (hM : IsMatching J M) : M.biUnion id ⊆ J := by
  intro b hb
  obtain ⟨S, hSM, hbS⟩ := Finset.mem_biUnion.mp hb
  obtain ⟨_, v, rfl⟩ := hM.1 S hSM
  exact Finset.filter_subset _ _ hbS

/-
Unselected lower bound: total `U`–`C` pairs `≤` covered-by-selected plus
`2 ∑_{w ∉ Sel} a(w)`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma unsel_lower (J : Finset (Finset V)) (hint : Intersecting J)
    (hdeg : ∀ v, edgeDeg J v ≤ 3)
    (M : Finset (Finset (Finset V))) (hM : IsMatching J M)
    (ω : Finset (Finset V) → V) :
    ((J \ M.biUnion id) ×ˢ M.biUnion id).card
      ≤ (coveredUC J M ω).card
        + 2 * ∑ v ∈ J.biUnion id \ selVerts J M ω,
            (block J v ∩ (J \ M.biUnion id)).card := by
  have h_card_biUnion : ((J \ M.biUnion id) ×ˢ M.biUnion id \ coveredUC J M ω).card ≤ ∑ v ∈ (J.biUnion id) \ selVerts J M ω, ((J \ M.biUnion id).filter (fun x => v ∈ x)).card * ((M.biUnion id).filter (fun x => v ∈ x)).card := by
    have h_card_biUnion : ((J \ M.biUnion id) ×ˢ M.biUnion id \ coveredUC J M ω) ⊆ Finset.biUnion ((J.biUnion id) \ selVerts J M ω) (fun v => ((J \ M.biUnion id).filter (fun x => v ∈ x)) ×ˢ ((M.biUnion id).filter (fun x => v ∈ x))) := by
      intro x hx; simp_all +decide ;
      obtain ⟨ v, hv ⟩ := Finset.nonempty_iff_ne_empty.2 ( show x.1 ∩ x.2 ≠ ∅ from by
                                                            exact Finset.Nonempty.ne_empty ( by have := ‹Intersecting J› x.1 hx.1.1.1 x.2 ( by obtain ⟨ a, ha, ha' ⟩ := hx.1.2; exact Finset.mem_of_subset ( matched_subset J M hM ) ( Finset.mem_biUnion.2 ⟨ a, ha, ha' ⟩ ) ) ; aesop ) );
      refine' ⟨ v, ⟨ ⟨ x.1, hx.1.1.1, Finset.mem_of_mem_inter_left hv ⟩, _ ⟩, Finset.mem_of_mem_inter_left hv, Finset.mem_of_mem_inter_right hv ⟩;
      contrapose! hx; unfold coveredUC at *; aesop;
    exact le_trans ( Finset.card_le_card h_card_biUnion ) ( Finset.card_biUnion_le.trans ( Finset.sum_le_sum fun _ _ => by rw [ Finset.card_product ] ) );
  -- For each $v \in J.biUnion id \ selVerts J M ω$, we have $(J \ M.biUnion id).filter (fun x => v ∈ x)).card * ((M.biUnion id).filter (fun x => v ∈ x)).card ≤ 2 * (block J v ∩ (J \ M.biUnion id)).card$.
  have h_card_filter : ∀ v ∈ (J.biUnion id) \ selVerts J M ω, ((J \ M.biUnion id).filter (fun x => v ∈ x)).card * ((M.biUnion id).filter (fun x => v ∈ x)).card ≤ 2 * (block J v ∩ (J \ M.biUnion id)).card := by
    intro v hv
    have h_card_filter : ((J \ M.biUnion id).filter (fun x => v ∈ x)).card + ((M.biUnion id).filter (fun x => v ∈ x)).card ≤ 3 := by
      rw [ ← Finset.card_union_of_disjoint ];
      · refine' le_trans ( Finset.card_le_card _ ) ( hdeg v );
        simp +contextual [ Finset.subset_iff ];
        rintro x ( hx | hx ) <;> simp_all +decide [ Finset.mem_biUnion ];
        exact matched_subset J M hM ( Finset.mem_biUnion.mpr ⟨ _, hx.1.choose_spec.1, hx.1.choose_spec.2 ⟩ );
      · simp +contextual [ Finset.disjoint_left ];
    have h_card_filter : (block J v ∩ (J \ M.biUnion id)).card = ((J \ M.biUnion id).filter (fun x => v ∈ x)).card := by
      congr 1 with x ; simp +decide [ block ];
      tauto;
    rcases n : Finset.card ( Finset.filter ( fun x => v ∈ x ) ( J \ M.biUnion id ) ) with ( _ | _ | _ | _ | n ) <;> rcases n' : Finset.card ( Finset.filter ( fun x => v ∈ x ) ( M.biUnion id ) ) with ( _ | _ | _ | _ | n' ) <;> simp_all +arith +decide only;
  rw [ ← Finset.card_sdiff_add_card_inter ];
  rw [ add_comm ];
  refine' add_le_add _ _;
  any_goals exact coveredUC J M ω;
  · exact Finset.card_le_card fun x hx => by aesop;
  · exact h_card_biUnion.trans ( by rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum h_card_filter )

/-
Regrouping: `|coveredUC| = ∑_{p ∈ C} g(p)`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma coveredUC_regroup (J : Finset (Finset V)) (M : Finset (Finset (Finset V)))
    (ω : Finset (Finset V) → V) :
    (coveredUC J M ω).card = ∑ p ∈ M.biUnion id, gCount J M ω p := by
  simp +decide only [coveredUC, Finset.card_filter];
  rw [ Finset.sum_product ];
  rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop

/-
For each point `p ∈ C`, `g(p) ≤ |support(linkGraph p)|`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma gCount_le_support (J : Finset (Finset V)) (hdeg : ∀ v, edgeDeg J v ≤ 3)
    (M : Finset (Finset (Finset V))) (hM : IsMatching J M)
    (ω : Finset (Finset V) → V)
    (hωmem : ∀ s ∈ (J \ M.biUnion id).powersetCard 2, ∀ x ∈ s, ω s ∈ x)
    {p : Finset V} (hp : p ∈ M.biUnion id) :
    gCount J M ω p ≤ ((linkGraph J M ω p).biUnion id).card := by
  refine Finset.card_mono ?_;
  intro x hx
  obtain ⟨v, hv_sel, hv_x, hv_p⟩ := Finset.mem_filter.mp hx |>.2
  have hv_block : block J v = insert p (Classical.choose (Finset.mem_image.mp hv_sel)) := by
    have hv_block : block J v ⊇ insert p (Classical.choose (Finset.mem_image.mp hv_sel)) := by
      grind +locals;
    have hv_block_card : (block J v).card ≤ 3 := by
      exact hdeg v;
    have hv_block_card_eq : (insert p (Classical.choose (Finset.mem_image.mp hv_sel))).card = 3 := by
      grind +suggestions;
    rw [ Finset.eq_of_subset_of_card_le hv_block ( by linarith ) ];
  refine' Finset.mem_biUnion.mpr ⟨ Classical.choose ( Finset.mem_image.mp hv_sel ), _, _ ⟩ <;> simp_all +decide [ Finset.ext_iff ];
  · simp_all +decide [ Finset.mem_powersetCard, linkGraph ];
    grind;
  · grind +locals

/-
Edges of a link graph are `2`-subsets of `U`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma linkGraph_edges (J : Finset (Finset V)) (M : Finset (Finset (Finset V)))
    (ω : Finset (Finset V) → V) (p : Finset V) :
    ∀ e ∈ linkGraph J M ω p, e.card = 2 ∧ e ⊆ (J \ M.biUnion id) := by
  intro e he; rw [ linkGraph ] at he; rw [ Finset.mem_filter ] at he; rw [ Finset.mem_powersetCard ] at he; aesop;

/-
Distinct colours give edge-disjoint link graphs (for matched points `p, p'`).
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma linkGraph_disjoint (J : Finset (Finset V)) (M : Finset (Finset (Finset V)))
    (ω : Finset (Finset V) → V) {p p' : Finset V}
    (hpC : p ∈ M.biUnion id) (hp'C : p' ∈ M.biUnion id) (h : p ≠ p') :
    Disjoint (linkGraph J M ω p) (linkGraph J M ω p') := by
  refine Finset.disjoint_left.mpr ?_;
  intro e he he'; simp_all +decide ;
  have := Finset.mem_filter.mp he; have := Finset.mem_filter.mp he'; simp_all +decide [ Finset.subset_iff, Finset.ext_iff ] ;
  grind +splitImp

/-
**Cross-intersecting (maximality).** Two link edges of different colours within a
matched triple cannot be vertex-disjoint.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma linkGraph_cross (J : Finset (Finset V))
    (M : Finset (Finset (Finset V))) (hM : IsMatching J M)
    (hMmax : ∀ M', IsMatching J M' → M'.card ≤ M.card)
    (ω : Finset (Finset V) → V)
    {S : Finset (Finset V)} (hS : S ∈ M) {p p' : Finset V}
    (hp : p ∈ S) (hp' : p' ∈ S) (hpp' : p ≠ p')
    {e f : Finset (Finset V)}
    (he : e ∈ linkGraph J M ω p) (hf : f ∈ linkGraph J M ω p') :
    (e ∩ f).Nonempty := by
  contrapose! hMmax;
  refine' ⟨ Insert.insert ( { p } ∪ e ) ( Insert.insert ( { p' } ∪ f ) ( M.erase S ) ), _, _ ⟩ <;> simp_all +decide [ IsMatching ];
  · refine' ⟨ _, _, _, _ ⟩;
    · unfold linkGraph at he hf; simp_all +decide [ IsGoodTriple ] ;
      grind +suggestions;
    · refine' ⟨ _, _ ⟩;
      · simp_all +decide [ Finset.disjoint_left, Finset.ext_iff ];
        intro x hx; have := Finset.mem_powersetCard.mp ( Finset.mem_filter.mp he |>.1 ) ; have := Finset.mem_powersetCard.mp ( Finset.mem_filter.mp hf |>.1 ) ; simp_all +decide [ Finset.subset_iff ] ;
        grind;
      · intro a ha₁ ha₂ ha₃; have := hM.2 _ hS _ ha₂; simp_all +decide [ Finset.disjoint_left ] ;
        grind +locals;
    · refine' ⟨ _, _ ⟩;
      · intro h; simp_all +decide [ Finset.disjoint_left, Finset.ext_iff ] ;
        refine' ⟨ _, _, _ ⟩ <;> contrapose! hMmax <;> simp_all +decide [ linkGraph ];
        · grind;
        · grind;
        · exact ⟨ _, hMmax.choose_spec.2, hMmax.choose_spec.1 ⟩;
      · intro a ha₁ ha₂ ha₃; have := hM.2 _ hS _ ha₂; simp_all +decide [ Finset.disjoint_left ] ;
        refine' ⟨ this ( Ne.symm ha₁ ) hp', _ ⟩;
        intro x hx₁ hx₂; have := Finset.mem_sdiff.mp ( Finset.mem_powersetCard.mp ( Finset.mem_filter.mp hf |>.1 ) |>.1 hx₁ ) ; simp_all +decide ;
    · intro T hTS hTM; have := hM.2 _ hTM _ hS hTS; simp_all +decide [ Finset.disjoint_left ] ;
      simp_all +decide [ linkGraph ];
      grind;
  · simp_all +decide [ Finset.subset_iff, linkGraph ];
    grind

/-
Per matched triple, the colour-support sum is `≤ K` (link graphs + `lemma2`).
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma per_triple_bound (J : Finset (Finset V))
    (hdeg : ∀ v, edgeDeg J v ≤ 3)
    (M : Finset (Finset (Finset V))) (hM : IsMatching J M)
    (hMmax : ∀ M', IsMatching J M' → M'.card ≤ M.card)
    (ω : Finset (Finset V) → V)
    (hωmem : ∀ s ∈ (J \ M.biUnion id).powersetCard 2, ∀ x ∈ s, ω s ∈ x)
    {S : Finset (Finset V)} (hS : S ∈ M) :
    ∑ p ∈ S, gCount J M ω p ≤ max 12 ((J \ M.biUnion id).card + 4) := by
  rcases hM.1 S hS with ⟨ hS₁, hS₂ ⟩;
  rcases Finset.card_eq_three.mp hS₁ with ⟨ a, b, c, hab, hbc, hac ⟩;
  have h_sum_le_K : (gCount J M ω a) + (gCount J M ω b) + (gCount J M ω c) ≤ max 12 ((J \ M.biUnion id).card + 4) := by
    refine' le_trans _ ( lemma2 ( J \ M.biUnion id ) ( linkGraph J M ω a ) ( linkGraph J M ω b ) ( linkGraph J M ω c ) _ _ _ _ _ _ _ _ _ );
    any_goals intro e he f hf; exact linkGraph_cross J M hM hMmax ω hS (by simp +decide [ hac ] ) (by simp +decide [ hac ] ) (by tauto) he hf;
    any_goals exact linkGraph_edges J M ω _;
    · gcongr;
      · apply gCount_le_support J hdeg M hM ω hωmem;
        exact Finset.mem_biUnion.mpr ⟨ S, hS, by simp +decide [ hac ] ⟩;
      · apply gCount_le_support J hdeg M hM ω hωmem;
        exact Finset.mem_biUnion.mpr ⟨ S, hS, by simp +decide [ hac ] ⟩;
      · apply gCount_le_support J hdeg M hM ω hωmem;
        exact Finset.mem_biUnion.mpr ⟨ S, hS, by simp +decide [ hac ] ⟩;
    · apply linkGraph_disjoint;
      · exact Finset.mem_biUnion.mpr ⟨ S, hS, by simp +decide [ hac ] ⟩;
      · exact Finset.mem_biUnion.mpr ⟨ S, hS, by simp +decide [ hac ] ⟩;
      · exact hab;
    · apply linkGraph_disjoint;
      · exact Finset.mem_biUnion.mpr ⟨ S, hS, by simp +decide [ hac ] ⟩;
      · exact Finset.mem_biUnion.mpr ⟨ S, hS, by simp +decide [ hac ] ⟩;
      · exact hbc;
    · apply linkGraph_disjoint;
      · exact Finset.mem_biUnion.mpr ⟨ S, hS, by simp +decide [ hac ] ⟩;
      · exact Finset.mem_biUnion.mpr ⟨ S, hS, by simp +decide [ hac ] ⟩;
      · tauto;
  grind

/-
`S ≤ t K`: covered `U`–`C` pairs are at most `t · K`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma S_bound (J : Finset (Finset V))
    (hdeg : ∀ v, edgeDeg J v ≤ 3)
    (M : Finset (Finset (Finset V))) (hM : IsMatching J M)
    (hMmax : ∀ M', IsMatching J M' → M'.card ≤ M.card)
    (ω : Finset (Finset V) → V)
    (hωmem : ∀ s ∈ (J \ M.biUnion id).powersetCard 2, ∀ x ∈ s, ω s ∈ x) :
    (coveredUC J M ω).card ≤ M.card * max 12 ((J \ M.biUnion id).card + 4) := by
  rw [ coveredUC_regroup ];
  rw [ Finset.sum_biUnion ];
  · have hsum :
        (∑ x ∈ M, ∑ p ∈ x, gCount J M ω p) ≤
          ∑ _x ∈ M, max 12 ((J \ M.biUnion id).card + 4) :=
      Finset.sum_le_sum (fun _ hx ↦ per_triple_bound J hdeg M hM hMmax ω hωmem hx)
    simpa [nsmul_eq_mul] using hsum
  · exact fun x hx y hy hxy => hM.2 x hx y hy hxy

/-
**Equation (4).** The core counting inequality obtained from a maximum matching
via the link graphs and `lemma2`.  Here `t = |M|`, `u = |U|`, and
`K = max 12 (u + 4)`; the inequality is the cleared-denominators form of
`u r ≥ u(u-1) + (3tu - tK)/2`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma eq4_nat (r : ℕ) (J : Finset (Finset V)) (huni : IsUniform r J)
    (hint : Intersecting J) (hdeg : ∀ v, edgeDeg J v ≤ 3)
    (M : Finset (Finset (Finset V))) (hM : IsMatching J M)
    (hMmax : ∀ M', IsMatching J M' → M'.card ≤ M.card)
    (hu : 0 < (J \ M.biUnion id).card) :
    2 * (J \ M.biUnion id).card * ((J \ M.biUnion id).card - 1)
        + 3 * M.card * (J \ M.biUnion id).card
      ≤ 2 * (J \ M.biUnion id).card * r
        + M.card * max 12 ((J \ M.biUnion id).card + 4) := by
  obtain ⟨ω, hωmem, hωinj⟩ := exists_witness J ‹_› ‹_› M ‹_› ‹_› hu;
  have hsplit : ∑ v ∈ J.biUnion id, (block J v ∩ (J \ M.biUnion id)).card = ∑ v ∈ selVerts J M ω, (block J v ∩ (J \ M.biUnion id)).card + ∑ v ∈ J.biUnion id \ selVerts J M ω, (block J v ∩ (J \ M.biUnion id)).card := by
    rw [ add_comm, Finset.sum_sdiff <| show selVerts J M ω ⊆ J.biUnion id from ?_ ];
    intro v hv; obtain ⟨ s, hs, rfl ⟩ := Finset.mem_image.mp hv; specialize hωmem s hs; simp_all +decide [ Finset.subset_iff ] ;
    exact Exists.elim ( Finset.card_pos.mp ( by linarith ) ) fun x hx => ⟨ x, hs.1 hx |>.1, hωmem x hx ⟩;
  have := unsel_lower J ‹_› ‹_› M ‹_› ω; simp_all +decide [ Finset.card_product ] ;
  have := S_bound J hdeg M hM hMmax ω; simp_all +decide ;
  have := card_matched J M hM; simp_all +decide [ mul_comm, mul_assoc ] ;
  linarith [ incid_total r J huni M, witness_lower J M ω ( fun s hs x hx => hωmem s ( Finset.mem_powersetCard.mp hs |>.1 ) ( Finset.mem_powersetCard.mp hs |>.2 ) x hx ) hωinj ]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- **Lemma 4.** An `r`-uniform intersecting hypergraph `J` of maximum degree `≤ 3`
with `q` edges satisfies `4 τ(J) ≤ q + r + 4`. -/
lemma lemma4 (r : ℕ) (J : Finset (Finset V)) (huni : IsUniform r J)
    (hint : Intersecting J) (hdeg : ∀ v, edgeDeg J v ≤ 3) :
    4 * coverNum J ≤ J.card + r + 4 := by
  obtain ⟨M, hM, hMmax⟩ := exists_max_matching J
  have hq := matching_q J M hM
  have hcov := matching_cover J hint M hM
  have hl1 := lemma1 r J huni hint hdeg
  set t := M.card with ht
  set u := (J \ M.biUnion id).card with hudef
  -- hq : J.card = 3*t + u ; hcov : coverNum J ≤ t + (u+1)/2 ; hl1 : J.card ≤ 2r+1
  rcases Nat.eq_zero_or_pos u with hu0 | hupos
  · omega
  · have heq4 := eq4_nat r J huni hint hdeg M hM hMmax hupos
    rw [← ht, ← hudef] at heq4
    have h5 := lemma3 u hupos t ((u : ℤ) + t - r) (max 12 ((u : ℤ) + 4)) rfl
      (by omega)
      (by
        have h : ((2 * u * (u - 1) + 3 * t * u : ℕ) : ℤ)
            ≤ ((2 * u * r + t * max 12 (u + 4) : ℕ) : ℤ) := by exact_mod_cast heq4
        push_cast [Nat.cast_sub (show 1 ≤ u by omega)] at h
        nlinarith [h])
    omega

/- ## The peeling reduction (Key Lemma) -/

/-
**Key Lemma.** For every `r`-uniform intersecting hypergraph `H`,
`4 τ(H) ≤ |E(H)| + r + 4`.

Proved by induction on the number of edges: if some vertex has degree `≥ 4`, peel
it off; otherwise the maximum degree is `≤ 3` and `lemma4` applies.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma keyLemma (r : ℕ) (H : Finset (Finset V)) (huni : IsUniform r H)
    (hint : Intersecting H) :
    4 * coverNum H ≤ H.card + r + 4 := by
  induction' n : H.card using Nat.strong_induction_on with n ih generalizing H;
  -- Assume there exists a vertex $v$ with degree $\geq 4$.
  by_cases h_deg : ∃ v, 4 ≤ edgeDeg H v;
  · -- Let $H'$ be the subhypergraph of $H$ obtained by removing all edges containing $v$.
    obtain ⟨v, hv⟩ := h_deg
    set H' := H.filter (fun E => v ∉ E) with hH';
    -- Then $H'$ is an $r$-uniform intersecting hypergraph with fewer edges than $H$.
    have hH'_uniform : IsUniform r H' := by
      exact fun E hE => huni E ( Finset.mem_filter.mp hE |>.1 )
    have hH'_intersecting : Intersecting H' := by
      exact fun E hE F hF => ‹Intersecting H› E ( Finset.filter_subset _ _ hE ) F ( Finset.filter_subset _ _ hF )
    have hH'_card : H'.card < H.card := by
      refine' Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.filter_subset _ _, _ ⟩ );
      simp_all +decide [ Finset.ext_iff, edgeDeg ];
      exact Exists.elim ( Finset.card_pos.mp ( pos_of_gt hv ) ) fun x hx => ⟨ x, Finset.mem_filter.mp hx |>.1, Finset.mem_filter.mp hx |>.2 ⟩;
    -- By the induction hypothesis, we have $4 * coverNum H' ≤ H'.card + r + 4$.
    have h_ind : 4 * coverNum H' ≤ H'.card + r + 4 := by
      exact ih _ ( by linarith ) _ hH'_uniform hH'_intersecting rfl;
    -- Now bound coverNum H ≤ 1 + coverNum H'.
    have h_coverNum : coverNum H ≤ 1 + coverNum H' := by
      -- Since $H'$ is intersecting, its edges are nonempty (Intersecting.edge_nonempty), so `exists_opt_cover` gives a cover $C'$ of $H'$ with $C'.card = coverNum H'$.
      obtain ⟨C', hC'⟩ : ∃ C' : Finset V, IsCover H' C' ∧ C'.card = coverNum H' := by
        apply exists_opt_cover;
        exact fun E hE => Intersecting.edge_nonempty hH'_intersecting hE;
      -- Then $C' \cup \{v\}$ (or insert $v$ $C'$) is a cover of $H$: any edge $E \in H$ either contains $v$ (covered by $v$) or lies in $H'$ (covered by $C'$).
      have h_cover : IsCover H (insert v C') := by
        intro E hE; by_cases hvE : v ∈ E <;> simp_all +decide [ IsCover ] ;
      exact le_trans ( coverNum_le h_cover ) ( by rw [ add_comm ] ; exact Finset.card_insert_le _ _ |> le_trans <| by linarith );
    -- Since $H$ is the disjoint union of $H'$ and $H.filter (fun E => v ∈ E)$, we have $H.card = H'.card + edgeDeg H v$.
    have h_card : H.card = H'.card + edgeDeg H v := by
      rw [ show edgeDeg H v = Finset.card ( Finset.filter ( fun E => v ∈ E ) H ) from rfl, ← Finset.card_union_of_disjoint ( Finset.disjoint_filter.mpr fun _ _ _ => by tauto ) ] ; congr ; ext ; by_cases h : v ∈ ‹Finset V› <;> aesop;
    grind;
  · grind +suggestions

/- ## Theorem 1 -/

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- **Theorem 1.** Every `r`-uniform intersecting hypergraph `H` with cover number
`r` has at least `3r − 4` edges (stated as `3 * r ≤ |E(H)| + 4`).

The hypothesis `hr : 0 < r` is kept to match the paper's statement ("for every
positive integer `r`"); the proof does not actually need it. -/
theorem theorem1 (r : ℕ) (hr : 0 < r) (H : Finset (Finset V))
    (huni : IsUniform r H) (hint : Intersecting H) (hcover : coverNum H = r) :
    3 * r ≤ H.card + 4 := by
  have hkey := keyLemma r H huni hint
  rw [hcover] at hkey
  omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- **Theorem 1**, in the form `g(r) ≥ 3r − 4` using truncated subtraction.

The hypothesis `hr : 0 < r` is kept to match the paper's statement; it is not
needed by the proof. -/
theorem theorem1' (r : ℕ) (hr : 0 < r) (H : Finset (Finset V))
    (huni : IsUniform r H) (hint : Intersecting H) (hcover : coverNum H = r) :
    3 * r - 4 ≤ H.card := by
  have := theorem1 r hr H huni hint hcover
  omega
/- ## The black-box input: Corollary 1 (Kahn's small-codegree theorem) -/

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- **Corollary 1 (assumed as a black box).**  The matching consequence of Kahn's
small-codegree list edge-colouring theorem for rank-`4` hypergraphs.

A `4`-uniform hypergraph is presented as a ground set `ground` of `n` vertices
together with an index set `W` of edge-copies and a block map `B : ι → Finset α`
with `B w ⊆ ground` and `|B w| = 4`.  The codegree condition `∆₂ ≤ 1` says every
pair of distinct ground vertices lies in at most one edge-copy.  The conclusion
is the existence of a *matching* (a subset `M ⊆ W` of pairwise vertex-disjoint
edge-copies) of size at least `3|W|/n − ε n`, encoding `matching ≥ 3|E|/n − o(n)`.
-/
def KahnCorollary : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (n : ℕ), n₀ ≤ n →
    ∀ {α : Type u} [DecidableEq α] {ι : Type u} [DecidableEq ι]
      (ground : Finset α) (W : Finset ι) (B : ι → Finset α),
      ground.card = n →
      (∀ w ∈ W, B w ⊆ ground) →
      (∀ w ∈ W, (B w).card = 4) →
      (∀ p ∈ ground, ∀ q ∈ ground, p ≠ q →
        (W.filter (fun w => p ∈ B w ∧ q ∈ B w)).card ≤ 1) →
      ∃ M ⊆ W, (∀ w ∈ M, ∀ w' ∈ M, w ≠ w' → Disjoint (B w) (B w')) ∧
        (3 : ℝ) * (W.card : ℝ) / (n : ℝ) - ε * (n : ℝ) ≤ (M.card : ℝ)

/- ## Kahn's theorem and the deduction of `KahnCorollary` from it

The genuinely unverified input of this development is **Kahn's small-codegree
list edge-colouring theorem** (Theorem 2 of the paper).  We state the (ordinary,
non-list) chromatic-index form actually used — `χ'(G) ≤ (1 + γ)D`, which follows
from the list version since `χ'(G) ≤ χ'_ℓ(G)` — as the black box `KahnTheorem`,
and then *prove* `KahnCorollary` from it (this is the content of Corollary 1 of
the paper).  After this, `KahnTheorem` is the only assumption that is not
formally verified. -/

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- **Kahn's small-codegree edge-colouring theorem (Theorem 2, chromatic-index
form).**  Stated as a black box.

A hypergraph `G` is presented as an index set `W` of edge-copies together with a
block map `B : ι → Finset α` (vertices live in `α`).  `rank(G) ≤ s` is
`∀ w ∈ W, (B w).card ≤ s`; `∆(G) ≤ D` and `∆₂(G) ≤ δD` are the maximum vertex
degree and the maximum codegree of a pair, counted with multiplicity over the
index set `W`.  A *proper edge colouring* by `k` colours is a `col : ι → ℕ` whose
values on `W` are `< k` and which assigns the same colour only to disjoint blocks
(each colour class is a matching).  The conclusion `χ'(G) ≤ (1 + γ)D` is the
existence of such a colouring with `k ≤ (1 + γ)D` colours.

This is the form used in the paper (Theorem 2 specialised via `χ' ≤ χ'_ℓ`); it is
the only statement of the development that is not formally proved. -/
def KahnTheorem : Prop :=
  ∀ (s : ℕ), 2 ≤ s → ∀ γ : ℝ, 0 < γ →
    ∃ δ : ℝ, 0 < δ ∧ ∃ D₀ : ℕ, ∀ (D : ℕ), D₀ ≤ D →
      ∀ {α : Type u} [DecidableEq α] {ι : Type u} [DecidableEq ι]
        (W : Finset ι) (B : ι → Finset α),
        (∀ w ∈ W, (B w).card ≤ s) →
        (∀ v : α, (W.filter (fun w => v ∈ B w)).card ≤ D) →
        (∀ p q : α, p ≠ q →
          ((W.filter (fun w => p ∈ B w ∧ q ∈ B w)).card : ℝ) ≤ δ * (D : ℝ)) →
        ∃ (k : ℕ) (col : ι → ℕ),
          (k : ℝ) ≤ (1 + γ) * (D : ℝ) ∧
          (∀ w ∈ W, col w < k) ∧
          (∀ w ∈ W, ∀ w' ∈ W, w ≠ w' → col w = col w' → Disjoint (B w) (B w'))

/-
**Degree bound (Corollary 1, degree step).**  In a `4`-uniform block family
`B` with all blocks inside `ground` and codegree `≤ 1` on `ground`, every vertex
has degree at most `(|ground| − 1)/3`: the `3` other vertices of the blocks
through a fixed `v` are pairwise disjoint, hence `3·d(v) ≤ |ground| − 1`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma kahn_degree_bound {α : Type u} [DecidableEq α] {ι : Type u} [DecidableEq ι]
    (ground : Finset α) (W : Finset ι) (B : ι → Finset α)
    (hsub : ∀ w ∈ W, B w ⊆ ground)
    (hb4 : ∀ w ∈ W, (B w).card = 4)
    (hcodeg : ∀ p ∈ ground, ∀ q ∈ ground, p ≠ q →
        (W.filter (fun w => p ∈ B w ∧ q ∈ B w)).card ≤ 1)
    (v : α) :
    3 * (W.filter (fun w => v ∈ B w)).card ≤ ground.card - 1 := by
  by_cases hv : v ∈ ground <;> simp_all +decide;
  · -- Consider the family of sets $S_w := (B_w).erase v$ for $w \in F$. For $w \in F$ we have $v \in B_w$ and $(B_w).card = 4$, so $(S_w).card = 3$, and $S_w \subseteq ground.erase v$.
    set F := Finset.filter (fun w => v ∈ B w) W with hF_def
    have hS_card : ∀ w ∈ F, (B w).erase v ⊆ ground.erase v ∧ ((B w).erase v).card = 3 := by
      grind;
    -- Key disjointness: for $w, w' \in F$ with $w \ne w'$, $S_w$ and $S_{w'}$ are disjoint.
    have hS_disjoint : ∀ w ∈ F, ∀ w' ∈ F, w ≠ w' → Disjoint ((B w).erase v) ((B w').erase v) := by
      intro w hw w' hw' hne; rw [ Finset.disjoint_left ] ; intro x hx hx'; specialize hcodeg x ; simp_all +decide [ Finset.subset_iff ] ;
      exact absurd ( hcodeg ( hsub _ hw.1 hx.2 ) v hv hx.1 ) ( by exact not_le_of_gt ( Finset.one_lt_card.2 ⟨ w, by aesop, w', by aesop ⟩ ) );
    have hS_card_biUnion : (Finset.biUnion F (fun w => (B w).erase v)).card = ∑ w ∈ F, ((B w).erase v).card := by
      exact Finset.card_biUnion fun w hw w' hw' hww' => hS_disjoint w hw w' hw' hww';
    exact le_trans ( by rw [ Finset.sum_congr rfl fun x hx => hS_card x hx |>.2 ] ; simp +decide [ mul_comm ] ) ( hS_card_biUnion ▸ Finset.card_le_card ( Finset.biUnion_subset.mpr fun x hx => hS_card x hx |>.1 ) |> le_trans <| by simp +decide [ hv ] );
  · rw [ Finset.filter_eq_empty_iff.mpr fun w hw => fun hw' => hv <| hsub w hw hw' ] ; aesop;

/-
**Degree sum (handshake).**  Summing vertex degrees over `ground` counts
incidences, giving `Σ_v d(v) = 4·|W|` for a `4`-uniform block family.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma kahn_degree_sum {α : Type u} [DecidableEq α] {ι : Type u} [DecidableEq ι]
    (ground : Finset α) (W : Finset ι) (B : ι → Finset α)
    (hsub : ∀ w ∈ W, B w ⊆ ground)
    (hb4 : ∀ w ∈ W, (B w).card = 4) :
    ∑ v ∈ ground, (W.filter (fun w => v ∈ B w)).card = 4 * W.card := by
  -- Rewrite the sum using the definition of the degree.
  have hsum : ∑ v ∈ ground, (∑ w ∈ W, if v ∈ B w then 1 else 0) = ∑ w ∈ W, (∑ v ∈ ground, if v ∈ B w then 1 else 0) := by
    exact Finset.sum_comm;
  simp_all +decide [ mul_comm ];
  rw [ Finset.sum_congr rfl fun x hx => by rw [ Finset.inter_eq_right.mpr ( hsub x hx ), hb4 x hx ] ] ; simp +decide

/-
**Pigeonhole on colour classes.**  A proper edge colouring of `W` by `k`
colours has a colour class (a matching) of relative size at least `1/k`:
`|W| ≤ k·|M|`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma kahn_pigeonhole_matching {α : Type u} {ι : Type u} [DecidableEq ι]
    (W : Finset ι) (B : ι → Finset α) (k : ℕ) (col : ι → ℕ)
    (hcol : ∀ w ∈ W, col w < k)
    (hproper : ∀ w ∈ W, ∀ w' ∈ W, w ≠ w' → col w = col w' → Disjoint (B w) (B w')) :
    ∃ M ⊆ W, (∀ w ∈ M, ∀ w' ∈ M, w ≠ w' → Disjoint (B w) (B w')) ∧
      (W.card : ℝ) ≤ (k : ℝ) * (M.card : ℝ) := by
  by_contra h;
  -- By assumption, for each color $c$, the size of the color class $W_c$ is strictly less than $|W| / k$.
  have h_class_size : ∀ c < k, (W.filter (fun w => col w = c)).card < (W.card : ℝ) / k := by
    intro c hc; contrapose! h; use Finset.filter ( fun w => col w = c ) W; simp_all +decide ;
    rwa [ div_le_iff₀' ( Nat.cast_pos.mpr ( pos_of_gt hc ) ) ] at h;
  -- Summing over all colors, we get that the total size of all color classes is strictly less than $k \cdot |W| / k = |W|$.
  have h_sum_class_size : ∑ c ∈ Finset.range k, (W.filter (fun w => col w = c)).card < (W.card : ℝ) := by
    rcases eq_or_ne k 0 <;> simp_all +decide;
    · exact Finset.nonempty_of_ne_empty ( h ∅ ( Finset.empty_subset _ ) ( by simp +decide ) );
    · exact lt_of_lt_of_le ( Finset.sum_lt_sum_of_nonempty ⟨ _, Finset.mem_range.mpr ( Nat.pos_of_ne_zero ‹_› ) ⟩ fun x hx => h_class_size x ( Finset.mem_range.mp hx ) ) ( by simp +decide [ mul_div_cancel₀, * ] );
  rw_mod_cast [ ← Finset.card_biUnion ] at h_sum_class_size;
  · exact h_sum_class_size.ne ( congr_arg Finset.card <| Finset.ext fun x => by aesop );
  · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun w hw₁ hw₂ => hxy <| by aesop;

/-
**Corollary 1, deduced from Kahn's theorem.**  `KahnTheorem` implies
`KahnCorollary`: the only assumption of the development is now `KahnTheorem`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
theorem kahnCorollary_of_kahnTheorem (kahn : KahnTheorem.{u}) : KahnCorollary.{u} := by
  intro ε hε;
  obtain ⟨ δ, hδ, D₀, hD₀ ⟩ := kahn 4 ( by norm_num ) ε hε;
  refine' ⟨ 3 * D₀ + 3 * ⌈1 / δ⌉₊ + 12, fun n hn => _ ⟩;
  intro α _ ι _ ground W B hground hsub hb4 hcodeg
  set D := (n - 1) / 3 with hD_def
  have hD_ge_D₀ : D₀ ≤ D := by
    omega
  have hD_pos : 1 ≤ D := by
    omega
  have hD_ceil : 1 ≤ δ * D := by
    have hD_ceil : (⌈1 / δ⌉₊ : ℝ) ≤ D := by
      exact_mod_cast Nat.le_div_iff_mul_le three_pos |>.2 ( Nat.le_sub_one_of_lt ( by linarith ) );
    nlinarith [ Nat.le_ceil ( 1 / δ ), mul_div_cancel₀ 1 hδ.ne' ]
  have hD_le_n : (D : ℝ) ≤ n / 3 := by
    rw [ le_div_iff₀ ] <;> norm_cast ; linarith [ Nat.div_mul_le_self ( n - 1 ) 3, Nat.sub_add_cancel ( by linarith : 1 ≤ n ) ];
  -- Apply `kahn` to obtain `k`, `col` with `(k : ℝ) ≤ (1 + ε) * D`, `col w < k` for `w ∈ W`, and the proper-colouring property.
  obtain ⟨ k, col, hk, hcol, hproper ⟩ := hD₀ D hD_ge_D₀ W B (fun w hw => (hb4 w hw).le) (fun v => by
    have := kahn_degree_bound ground W B hsub hb4 (fun p hp q hq hpq => hcodeg p hp q hq hpq) v;
    omega) (fun p q hpq => by
    by_cases hp : p ∈ ground <;> by_cases hq : q ∈ ground <;> simp +decide [ * ] at hpq ⊢;
    · exact le_trans ( Nat.cast_le.mpr ( hcodeg p hp q hq hpq ) ) ( by norm_num; linarith );
    · rw [ Finset.card_eq_zero.mpr ] <;> norm_num;
      · positivity;
      · exact fun w hw hpq hq' => hq <| hsub w hw hq';
    · rw [ Finset.card_eq_zero.mpr ] <;> norm_num;
      · positivity;
      · exact fun w hw hpq' hq' => hp <| hsub w hw hpq';
    · rw [ Finset.card_eq_zero.mpr ] <;> norm_num;
      · positivity;
      · exact fun w hw hpq' hq' => hp <| hsub w hw hpq');
  obtain ⟨ M, hM₁, hM₂, hM₃ ⟩ := kahn_pigeonhole_matching W B k col hcol hproper;
  refine' ⟨ M, hM₁, hM₂, _ ⟩;
  rw [ div_sub', div_le_iff₀ ] <;> try norm_num ; linarith;
  have h_step_A : (W.card : ℝ) ≤ n^2 / 3 := by
    have h_step_A : ∑ v ∈ ground, (W.filter (fun w => v ∈ B w)).card ≤ n * D := by
      have h_sum_deg : ∀ v ∈ ground, (W.filter (fun w => v ∈ B w)).card ≤ D := by
        intros v hv
        have h_deg_v : 3 * (W.filter (fun w => v ∈ B w)).card ≤ n - 1 := by
          convert kahn_degree_bound ground W B hsub hb4 hcodeg v using 1;
          rw [ hground ];
        grind;
      exact le_trans ( Finset.sum_le_sum h_sum_deg ) ( by norm_num [ hground ] );
    have h_step_A : ∑ v ∈ ground, (W.filter (fun w => v ∈ B w)).card = 4 * W.card := by
      convert kahn_degree_sum ground W B hsub hb4 using 1;
    rw [ le_div_iff₀ ] <;> norm_cast;
    nlinarith [ Nat.div_mul_le_self ( n - 1 ) 3, Nat.sub_add_cancel ( by linarith : 1 ≤ n ) ];
  nlinarith [ show ( 0 : ℝ ) ≤ ε * n by positivity, show ( 0 : ℝ ) ≤ ε * M.card by positivity, show ( 0 : ℝ ) ≤ n * M.card by positivity ]

/-
## The actual-degree consequence of Kahn's theorem

The optimized argument uses the actual maximum degree of the linear auxiliary
`4`-graph, rather than the universal bound `(q - 1) / 3`.
-/

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- The rank-`4`, codegree-`1` consequence of Kahn's theorem with an arbitrary
degree bound `D`. -/
def KahnDegreeCorollary : Prop :=
  ∀ γ : ℝ, 0 < γ → ∃ D₀ : ℕ, ∀ (D : ℕ), D₀ ≤ D →
    ∀ {α : Type u} [DecidableEq α] {ι : Type u} [DecidableEq ι]
      (W : Finset ι) (B : ι → Finset α),
      W.card ≤ 100 * D ^ 2 →
      (∀ w ∈ W, (B w).card = 4) →
      (∀ v : α, (W.filter (fun w => v ∈ B w)).card ≤ D) →
      (∀ p q : α, p ≠ q →
        (W.filter (fun w => p ∈ B w ∧ q ∈ B w)).card ≤ 1) →
      ∃ M ⊆ W,
        (∀ w ∈ M, ∀ w' ∈ M, w ≠ w' → Disjoint (B w) (B w')) ∧
        (W.card : ℝ) ≤ (1 + γ) * (D : ℝ) * (M.card : ℝ)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- `KahnTheorem` implies the actual-degree rank-`4` corollary. -/
theorem kahnDegreeCorollary_of_kahnTheorem
    (kahn : KahnTheorem.{u}) : KahnDegreeCorollary.{u} := by
  intro γ hγ
  obtain ⟨δ, hδ, D₀, hD₀⟩ := kahn 4 (by norm_num) γ hγ
  refine ⟨max D₀ (⌈1 / δ⌉₊ + 1), ?_⟩
  intro D hD α _ ι _ W B _ hB4 hdeg hcodeg
  have hDD₀ : D₀ ≤ D := le_trans (le_max_left _ _) hD
  have hDceil : (⌈1 / δ⌉₊ : ℝ) ≤ (D : ℝ) := by
    exact_mod_cast le_trans (Nat.le_add_right _ 1) (le_trans (le_max_right _ _) hD)
  have hδD : 1 ≤ δ * (D : ℝ) := by
    nlinarith [Nat.le_ceil (1 / δ), mul_div_cancel₀ 1 hδ.ne']
  obtain ⟨k, col, hk, hcol, hproper⟩ :=
    hD₀ D hDD₀ W B
      (fun w hw => (hB4 w hw).le)
      hdeg
      (fun p q hpq =>
        le_trans (Nat.cast_le.mpr (hcodeg p q hpq)) (by norm_num; exact hδD))
  obtain ⟨M, hMsub, hMdisj, hMcard⟩ :=
    kahn_pigeonhole_matching W B k col hcol hproper
  refine ⟨M, hMsub, hMdisj, ?_⟩
  exact hMcard.trans
    (mul_le_mul_of_nonneg_right hk (Nat.cast_nonneg M.card))

/- ## The peeling reduction for degree `≥ 5` -/

/-
**The degree-`5` peeling reduction (equation (6)).**  Starting from an
`r`-uniform intersecting hypergraph `H`, repeatedly remove all edges through a
vertex of current degree at least `5`.  This produces a subfamily `J ⊆ H` of
maximum degree `≤ 4`, together with a count `k` of peeled vertices, with
`|E(J)| + 5k ≤ |E(H)|` and `τ(H) ≤ k + τ(J)`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma peel5 (r : ℕ) (H : Finset (Finset V)) (huni : IsUniform r H)
    (hint : Intersecting H) :
    ∃ (J : Finset (Finset V)) (k : ℕ),
      J ⊆ H ∧ (∀ v, edgeDeg J v ≤ 4) ∧
      J.card + 5 * k ≤ H.card ∧
      coverNum H ≤ k + coverNum J := by
  induction' h : Finset.card H using Nat.strong_induction_on with n ih generalizing H;
  by_cases h_deg : ∃ v, edgeDeg H v ≥ 5;
  · obtain ⟨ v, hv ⟩ := h_deg;
    obtain ⟨J, k, hJ_sub, hJ_deg, hJ_card, hJ_cover⟩ : ∃ J : Finset (Finset V), ∃ k : ℕ, J ⊆ H.filter (fun E => v ∉ E) ∧ (∀ w, edgeDeg J w ≤ 4) ∧ J.card + 5 * k ≤ (H.filter (fun E => v ∉ E)).card ∧ coverNum (H.filter (fun E => v ∉ E)) ≤ k + coverNum J := by
      apply ih ((H.filter (fun E => v ∉ E)).card);
      · refine' h ▸ Finset.card_lt_card _;
        simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ];
        exact Exists.elim ( Finset.card_pos.mp ( pos_of_gt hv ) ) fun x hx => ⟨ x, Finset.mem_filter.mp hx |>.1, Finset.mem_filter.mp hx |>.2 ⟩;
      · exact fun E hE => huni E ( Finset.mem_filter.mp hE |>.1 );
      · intro E hE F hF; have := ‹Intersecting H› E ( Finset.mem_filter.mp hE |>.1 ) F ( Finset.mem_filter.mp hF |>.1 ) ; aesop;
      · rfl;
    refine' ⟨ J, k + 1, _, _, _, _ ⟩;
    · exact fun x hx => Finset.mem_filter.mp ( hJ_sub hx ) |>.1;
    · exact hJ_deg;
    · have h_card_split : H.card = (H.filter (fun E => v ∈ E)).card + (H.filter (fun E => v ∉ E)).card := by
        rw [ Finset.card_filter_add_card_filter_not ];
      linarith! [ show Finset.card ( Finset.filter ( fun E => v ∈ E ) H ) ≥ 5 by exact hv ];
    · have h_cover : ∃ C : Finset V, IsCover (H.filter (fun E => v ∉ E)) C ∧ C.card = coverNum (H.filter (fun E => v ∉ E)) := by
        apply exists_opt_cover;
        exact fun E hE => Intersecting.edge_nonempty ‹_› ( Finset.mem_filter.mp hE |>.1 );
      obtain ⟨ C, hC₁, hC₂ ⟩ := h_cover;
      have h_cover : IsCover H (insert v C) := by
        intro E hE; by_cases hvE : v ∈ E <;> simp_all +decide [ IsCover ] ;
      exact le_trans ( coverNum_le h_cover ) ( by linarith [ Finset.card_insert_le v C ] );
  · exact ⟨ H, 0, Finset.Subset.refl _, fun v => not_lt.1 fun contra => h_deg ⟨ v, contra ⟩, by simp +decide [ h ], by simp +decide ⟩

/- ## Equation (7): the size of the residual hypergraph -/

/-
**Equation (7).**  An `r`-uniform intersecting hypergraph of maximum degree
`≤ 4` has at most `3r + 1` edges.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma lemma1_deg4 (r : ℕ) (J : Finset (Finset V)) (huni : IsUniform r J)
    (hint : Intersecting J) (hdeg : ∀ v, edgeDeg J v ≤ 4) :
    J.card ≤ 3 * r + 1 := by
  by_cases hJ : J = ∅;
  · grind;
  · obtain ⟨E, hE⟩ : ∃ E ∈ J, True := by
      exact Exists.elim ( Finset.nonempty_of_ne_empty hJ ) fun E hE => ⟨ E, hE, trivial ⟩;
    have h_double_counting : (J.card - 1) ≤ ∑ v ∈ E, (edgeDeg J v - 1) := by
      have h_double_counting : (J.card - 1) ≤ ∑ F ∈ J.erase E, (E ∩ F).card := by
        exact le_trans ( by simp +decide [ Finset.card_erase_of_mem hE.1 ] ) ( Finset.sum_le_sum fun x hx => Finset.card_pos.mpr <| by have := ‹∀ E ∈ J, ∀ F ∈ J, ( E ∩ F ).Nonempty› E hE.1 x ( Finset.mem_of_mem_erase hx ) ; aesop );
      have h_double_counting : ∑ F ∈ J.erase E, (E ∩ F).card = ∑ v ∈ E, ∑ F ∈ J.erase E, (if v ∈ F then 1 else 0) := by
        rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop;
      simp_all +decide [ Finset.filter_erase, edgeDeg ];
    have h_double_counting : (J.card - 1) ≤ ∑ v ∈ E, 3 := by
      exact h_double_counting.trans ( Finset.sum_le_sum fun v hv => Nat.sub_le_of_le_add <| by linarith [ hdeg v ] );
    simp_all +decide [ mul_comm, huni E hE.1 ]

/- ## A cover bound from a matching of degree-`4` blocks -/

/-
A cover bound from a *matching* in the auxiliary `4`-uniform system: if `M`
is a set of vertices whose blocks have size `4` and are pairwise disjoint, then
covering each block by its centre and pairing up the remaining edges gives
`τ(J) ≤ |M| + ⌈(q − 4|M|)/2⌉`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma matching_cover4 (J : Finset (Finset V)) (hint : Intersecting J)
    (M : Finset V)
    (hM4 : ∀ v ∈ M, (block J v).card = 4)
    (hMdisj : ∀ v ∈ M, ∀ w ∈ M, v ≠ w → Disjoint (block J v) (block J w)) :
    coverNum J ≤ M.card + (J.card - 4 * M.card + 1) / 2 := by
  obtain ⟨C, hC⟩ : ∃ C : Finset V, (∀ E ∈ J \ (M.biUnion (fun v => block J v)), ∃ v ∈ C, v ∈ E) ∧ C.card ≤ (J.card - 4 * M.card + 1) / 2 := by
    convert intersecting_cover_half ( J \ M.biUnion ( fun v => block J v ) ) _;
    · rw [ Finset.card_sdiff ];
      rw [ Finset.inter_eq_left.mpr ];
      · rw [ Finset.card_biUnion ];
        · rw [ Finset.sum_congr rfl hM4, Finset.sum_const, smul_eq_mul, mul_comm ];
        · exact fun v hv w hw hvw => hMdisj v hv w hw hvw;
      · exact Finset.biUnion_subset.mpr fun v hv => Finset.filter_subset _ _;
    · exact fun x hx y hy => ‹Intersecting J› x ( Finset.mem_sdiff.mp hx |>.1 ) y ( Finset.mem_sdiff.mp hy |>.1 );
  refine' le_trans ( coverNum_le _ ) _;
  exact M ∪ C;
  · intro E hE; by_cases hE' : E ∈ M.biUnion ( fun v => block J v ) <;> simp_all +decide ;
    · obtain ⟨ v, hv, hv' ⟩ := hE'; use v; simp_all +decide [ block ] ;
    · exact Exists.elim ( hC.1 E hE hE' ) fun v hv => ⟨ v, Or.inr hv.1, hv.2 ⟩;
  · grind

/-
The matched blocks are pairwise disjoint and contained in `J`, so they use up
`4|M|` distinct edges.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma matched_blocks_card (J : Finset (Finset V)) (M : Finset V)
    (hM4 : ∀ v ∈ M, (block J v).card = 4) (hMsub : ∀ v ∈ M, block J v ⊆ J)
    (hMdisj : ∀ v ∈ M, ∀ w ∈ M, v ≠ w → Disjoint (block J v) (block J w)) :
    4 * M.card ≤ J.card := by
  have h_union : (M.biUnion (fun v => block J v)).card = 4 * M.card := by
    rw [ Finset.card_biUnion ];
    · rw [ Finset.sum_congr rfl hM4, Finset.sum_const, smul_eq_mul, mul_comm ];
    · exact fun v hv w hw hvw => hMdisj v hv w hw hvw;
  exact h_union ▸ Finset.card_le_card ( Finset.biUnion_subset.mpr hMsub )

/-
A high-degree vertex of a linear auxiliary `4`-graph gives a complementary
cover.  If `d` auxiliary blocks contain the point `p`, then their other
three points are pairwise disjoint.  Selecting all `d` block centres and
pairing the remaining edges proves `2τ(J) + d ≤ |J|`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma star_cover4 (J : Finset (Finset V)) (hint : Intersecting J)
    (W : Finset V) (hW4 : ∀ v ∈ W, (block J v).card = 4)
    (hcodeg : ∀ p ∈ J, ∀ q ∈ J, p ≠ q →
      (W.filter (fun v => p ∈ block J v ∧ q ∈ block J v)).card ≤ 1)
    (p : Finset V) (hp : p ∈ J)
    (hpos : 0 < (W.filter (fun v => p ∈ block J v)).card) :
    2 * coverNum J + (W.filter (fun v => p ∈ block J v)).card ≤ J.card := by
  let S := W.filter (fun v => p ∈ block J v)
  have hSne : S.Nonempty := Finset.card_pos.mp hpos
  have hS4 : ∀ v ∈ S, (block J v).card = 4 := by
    intro v hv
    exact hW4 v (Finset.mem_filter.mp hv |>.1)
  have hSsub : ∀ v ∈ S, block J v ⊆ J :=
    fun v _ => Finset.filter_subset _ _
  have hpS : ∀ v ∈ S, p ∈ block J v :=
    fun v hv => Finset.mem_filter.mp hv |>.2
  have hEraseCard : ∀ v ∈ S, ((block J v).erase p).card = 3 := by
    intro v hv
    rw [Finset.card_erase_of_mem (hpS v hv), hS4 v hv]
  have hEraseDisj :
      ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
        Disjoint ((block J v).erase p) ((block J w).erase p) := by
    intro v hv w hw hvw
    rw [Finset.disjoint_left]
    intro x hxv hxw
    have hxp : x ≠ p := by
      exact fun h => (Finset.mem_erase.mp hxv |>.1) h
    have hxJ : x ∈ J := hSsub v hv (Finset.mem_erase.mp hxv |>.2)
    have htwo :
        2 ≤ (W.filter (fun z => x ∈ block J z ∧ p ∈ block J z)).card := by
      apply Finset.one_lt_card.mpr
      refine ⟨v, ?_, w, ?_, hvw⟩
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mp hv |>.1,
            Finset.mem_erase.mp hxv |>.2, hpS v hv⟩
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mp hw |>.1,
            Finset.mem_erase.mp hxw |>.2, hpS w hw⟩
    exact (not_le_of_gt htwo) (hcodeg x hxJ p hp hxp)
  let U := S.biUnion (fun v => (block J v).erase p)
  have hUcard : U.card = 3 * S.card := by
    dsimp [U]
    rw [Finset.card_biUnion]
    · rw [Finset.sum_congr rfl hEraseCard, Finset.sum_const,
        smul_eq_mul, mul_comm]
    · exact hEraseDisj
  have hUnion :
      S.biUnion (fun v => block J v) = insert p U := by
    ext E
    simp only [Finset.mem_biUnion, Finset.mem_insert, U, Finset.mem_erase]
    constructor
    · rintro ⟨v, hv, hEv⟩
      by_cases hEp : E = p
      · exact Or.inl hEp
      · exact Or.inr ⟨v, hv, hEp, hEv⟩
    · rintro (rfl | ⟨v, hv, hne, hEv⟩)
      · obtain ⟨v, hv⟩ := hSne
        exact ⟨v, hv, hpS v hv⟩
      · exact ⟨v, hv, hEv⟩
  have hpU : p ∉ U := by
    simp [U]
  have hUnionCard :
      (S.biUnion (fun v => block J v)).card = 1 + 3 * S.card := by
    rw [hUnion, Finset.card_insert_of_notMem hpU, hUcard]
    omega
  obtain ⟨C, hCcover, hCcard⟩ :=
    intersecting_cover_half
      (J \ S.biUnion (fun v => block J v))
      (fun E hE F hF =>
        hint E (Finset.mem_sdiff.mp hE |>.1)
          F (Finset.mem_sdiff.mp hF |>.1))
  have hCover : IsCover J (S ∪ C) := by
    intro E hE
    by_cases hEU : E ∈ S.biUnion (fun v => block J v)
    · obtain ⟨v, hvS, hvE⟩ := Finset.mem_biUnion.mp hEU
      exact ⟨v, Finset.mem_union_left _ hvS,
        Finset.mem_filter.mp hvE |>.2⟩
    · obtain ⟨v, hvC, hvE⟩ :=
        hCcover E (Finset.mem_sdiff.mpr ⟨hE, hEU⟩)
      exact ⟨v, Finset.mem_union_right _ hvC, hvE⟩
  have hCoverCard :
      coverNum J ≤ S.card +
        ((J \ S.biUnion (fun v => block J v)).card + 1) / 2 := by
    calc
      coverNum J ≤ (S ∪ C).card := coverNum_le hCover
      _ ≤ S.card + C.card := Finset.card_union_le S C
      _ ≤ S.card +
          ((J \ S.biUnion (fun v => block J v)).card + 1) / 2 := by omega
  have hUnionSub : S.biUnion (fun v => block J v) ⊆ J :=
    Finset.biUnion_subset.mpr hSsub
  have hRemainCard :
      (J \ S.biUnion (fun v => block J v)).card =
        J.card - (1 + 3 * S.card) := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hUnionSub, hUnionCard]
  have hUnionLe : 1 + 3 * S.card ≤ J.card := by
    rw [← hUnionCard]
    exact Finset.card_le_card hUnionSub
  change 2 * coverNum J + S.card ≤ J.card
  rw [hRemainCard] at hCoverCard
  omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- For any degree threshold `D` above Kahn's threshold, either a degree-`D`
linear star gives a cover saving `D/2`, or Kahn gives a matching whose saving
is at least `|W| / ((1+γ)D)`. -/
lemma matching_or_star_cover (kahn : KahnDegreeCorollary.{u})
    (γ : ℝ) (hγ : 0 < γ) :
    ∃ D₀ : ℕ, ∀ {V : Type u} [DecidableEq V]
      (J : Finset (Finset V)) (hint : Intersecting J)
      (W : Finset V) (D : ℕ), D₀ ≤ D → 0 < D → W.card ≤ 100 * D ^ 2 →
      (∀ v ∈ W, (block J v).card = 4) →
      (∀ v ∈ W, block J v ⊆ J) →
      (∀ p ∈ J, ∀ q ∈ J, p ≠ q →
        (W.filter (fun v => p ∈ block J v ∧ q ∈ block J v)).card ≤ 1) →
      ((coverNum J : ℝ) ≤ (J.card : ℝ) / 2 - (D : ℝ) / 2) ∨
      ((coverNum J : ℝ) ≤ (J.card : ℝ) / 2 -
        (W.card : ℝ) / ((1 + γ) * (D : ℝ)) + 1 / 2) := by
  obtain ⟨D₀, hD₀⟩ := kahn γ hγ
  refine ⟨D₀, ?_⟩
  intro V _ J hint W D hDD₀ hDpos hWcard hW4 hWsub hcodeg
  by_cases hhigh :
      ∃ p ∈ J, D ≤ (W.filter (fun v => p ∈ block J v)).card
  · left
    obtain ⟨p, hpJ, hpD⟩ := hhigh
    have hstar :=
      star_cover4 J hint W hW4 hcodeg p hpJ
        (lt_of_lt_of_le hDpos hpD)
    have hstarR :
        2 * (coverNum J : ℝ) +
          ((W.filter (fun v => p ∈ block J v)).card : ℝ)
            ≤ (J.card : ℝ) := by
      exact_mod_cast hstar
    have hpDR :
        (D : ℝ) ≤
          ((W.filter (fun v => p ∈ block J v)).card : ℝ) := by
      exact_mod_cast hpD
    linarith
  · right
    have hdeg :
        ∀ p : Finset V, (W.filter (fun v => p ∈ block J v)).card ≤ D := by
      intro p
      by_cases hp : p ∈ J
      · have hnot :
            ¬D ≤ (W.filter (fun v => p ∈ block J v)).card := by
          exact fun hpD => hhigh ⟨p, hp, hpD⟩
        have := not_le.mp hnot
        omega
      · have hempty :
            W.filter (fun v => p ∈ block J v) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro v hv hvp
          exact hp (hWsub v hv hvp)
        rw [hempty]
        simp
    have hcodeg' :
        ∀ p q : Finset V, p ≠ q →
          (W.filter (fun v => p ∈ block J v ∧ q ∈ block J v)).card ≤ 1 := by
      intro p q hpq
      by_cases hp : p ∈ J <;> by_cases hq : q ∈ J
      · exact hcodeg p hp q hq hpq
      · have hempty :
            W.filter (fun v =>
              p ∈ block J v ∧ q ∈ block J v) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro v hv hvpq
          exact hq (hWsub v hv hvpq.2)
        rw [hempty]
        simp
      · have hempty :
            W.filter (fun v =>
              p ∈ block J v ∧ q ∈ block J v) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro v hv hvpq
          exact hp (hWsub v hv hvpq.1)
        rw [hempty]
        simp
      · have hempty :
            W.filter (fun v =>
              p ∈ block J v ∧ q ∈ block J v) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro v hv hvpq
          exact hp (hWsub v hv hvpq.1)
        rw [hempty]
        simp
    obtain ⟨M, hMsub, hMdisj, hMbound⟩ :=
      hD₀ D hDD₀ W (block J) hWcard hW4 hdeg hcodeg'
    have hM4 : ∀ v ∈ M, (block J v).card = 4 :=
      fun v hv => hW4 v (hMsub hv)
    have hMblocksub : ∀ v ∈ M, block J v ⊆ J :=
      fun v hv => hWsub v (hMsub hv)
    have hcover := matching_cover4 J hint M hM4 hMdisj
    have hmatched :=
      matched_blocks_card J M hM4 hMblocksub hMdisj
    have hτ :
        (coverNum J : ℝ) ≤ (J.card : ℝ) / 2 -
          (M.card : ℝ) + 1 / 2 :=
      by
        field_simp
        norm_cast
        rw [Int.subNatNat_eq_coe]
        omega
    have hden : 0 < (1 + γ) * (D : ℝ) := by positivity
    have hfrac :
        (W.card : ℝ) / ((1 + γ) * (D : ℝ)) ≤ (M.card : ℝ) := by
      rw [div_le_iff₀ hden]
      simpa [mul_assoc, mul_comm, mul_left_comm] using hMbound
    linarith

/- ## Counting machinery for the auxiliary `4`-uniform hypergraph `Q` -/

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- The set of vertices appearing in some edge of `J`. -/
def verts (J : Finset (Finset V)) : Finset V := J.biUnion id

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- The number of vertices of `J` of degree exactly `i`. -/
def numDeg (J : Finset (Finset V)) (i : ℕ) : ℕ :=
  ((verts J).filter (fun v => edgeDeg J v = i)).card

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- The vertices of `J` of degree exactly `4`; these index the edges of the
auxiliary `4`-uniform hypergraph `Q`. -/
def deg4Verts (J : Finset (Finset V)) : Finset V :=
  (verts J).filter (fun v => edgeDeg J v = 4)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- The codegree of a `2`-set `s` of edges in the block family indexed by `W`:
the number of vertices `v ∈ W` whose block contains both edges of `s`. -/
def codeg (J : Finset (Finset V)) (W : Finset V) (s : Finset (Finset V)) : ℕ :=
  (W.filter (fun v => s ⊆ block J v)).card

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- The "potential" `X = Σ_{s} (codeg s − 1)₊` used to bound the number of
edge-copies deleted while reducing the codegree to `≤ 1`. -/
def potential (J : Finset (Finset V)) (W : Finset V) : ℕ :=
  ∑ s ∈ J.powersetCard 2, (codeg J W s - 1)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- The number `z` of pairs of edges of `J` with no common degree-`4` vertex. -/
def zCount (J : Finset (Finset V)) : ℕ :=
  ((J.powersetCard 2).filter (fun s => codeg J (deg4Verts J) s = 0)).card

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma edgeDeg_eq_block_card (J : Finset (Finset V)) (v : V) :
    edgeDeg J v = (block J v).card := rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma deg4Verts_card (J : Finset (Finset V)) :
    (deg4Verts J).card = numDeg J 4 := rfl

/-
**The deletion lemma.**  Removing edge-copies one at a time from any pair of
current codegree `≥ 2` terminates after at most `potential J W` deletions, leaving
a subfamily `W'` of codegree `≤ 1`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma exists_codeg_le_one (J : Finset (Finset V)) (W : Finset V) :
    ∃ W' ⊆ W, (∀ s ∈ J.powersetCard 2, codeg J W' s ≤ 1) ∧
      W.card ≤ W'.card + potential J W := by
  induction' n : potential J W using Nat.strong_induction_on with n ih generalizing W;
  by_cases h : ∃ s ∈ J.powersetCard 2, codeg J W s > 1;
  · obtain ⟨ s, hs₁, hs₂ ⟩ := h;
    obtain ⟨ v, hv₁, hv₂ ⟩ : ∃ v ∈ W, s ⊆ block J v := by
      contrapose! hs₂
      simp_all +decide [codeg]
    have h_potential_lt : potential J (W.erase v) < potential J W := by
      refine' Finset.sum_lt_sum _ _;
      · intro i hi; exact Nat.sub_le_sub_right ( Finset.card_le_card ( Finset.filter_subset_filter _ ( Finset.erase_subset _ _ ) ) ) _;
      · refine' ⟨ s, hs₁, _ ⟩;
        unfold codeg at *;
        rw [ Finset.filter_erase ] ; aesop;
    grind;
  · exact ⟨ W, Finset.Subset.refl _, fun s hs => le_of_not_gt fun hs' => h ⟨ s, hs, hs' ⟩, by linarith ⟩

/-
**Double count of codegrees.**  The total codegree over all `2`-subsets of
`E(J)`, counted in the degree-`4` block family, equals `6` times the number of
degree-`4` vertices (each contributes `C(4,2) = 6`).
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma codeg_sum (J : Finset (Finset V)) (huni : ∀ v ∈ deg4Verts J, (block J v).card = 4)
    (hsub : ∀ v ∈ deg4Verts J, block J v ⊆ J) :
    ∑ s ∈ J.powersetCard 2, codeg J (deg4Verts J) s = 6 * numDeg J 4 := by
  -- First, rewrite `codeg` using the alternative definition.
  -- `codeg J (deg4Verts J) s = (deg4Verts J).filter (fun v => s ⊆ block J v)).card`.
  -- This will allow us to switch the order of the sums in the double counting argument.
  unfold codeg;
  simp +decide only [Finset.card_filter];
  rw [ Finset.sum_comm, Finset.sum_eq_card_nsmul ] <;> norm_num;
  rw [ mul_comm, deg4Verts_card ];
  intro v hv; rw [ show { x ∈ Finset.powersetCard 2 J | x ⊆ block J v } = Finset.powersetCard 2 ( block J v ) from ?_ ] ; simp +decide [ huni v hv ] ;
  grind

/-
**The potential identity** `X + C(q,2) = 6 x₄ + z`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma potential_add_choose (J : Finset (Finset V))
    (huni : ∀ v ∈ deg4Verts J, (block J v).card = 4)
    (hsub : ∀ v ∈ deg4Verts J, block J v ⊆ J) :
    potential J (deg4Verts J) + (J.card).choose 2 = 6 * numDeg J 4 + zCount J := by
  have h_potential : potential J (deg4Verts J) + (Finset.powersetCard 2 J).card = ∑ s ∈ Finset.powersetCard 2 J, (codeg J (deg4Verts J) s + if codeg J (deg4Verts J) s = 0 then 1 else 0) := by
    unfold potential;
    rw [ Finset.card_eq_sum_ones, ← Finset.sum_add_distrib ];
    refine Finset.sum_congr rfl fun x hx => ?_
    rcases Nat.eq_zero_or_pos (codeg J (deg4Verts J) x) with h | h
    · simp +decide [h]
    · rw [if_neg (by omega)]; omega
  convert h_potential using 1;
  · rw [ Finset.card_powersetCard ];
  · rw [ Finset.sum_add_distrib, codeg_sum J huni hsub ];
    simp +decide [ zCount ]

/-
**The degree-sum identity (equation (9)).** `x₁ + 2x₂ + 3x₃ + 4x₄ = qr`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma degree_sum (r : ℕ) (J : Finset (Finset V)) (huni : IsUniform r J)
    (hdeg : ∀ v, edgeDeg J v ≤ 4) :
    numDeg J 1 + 2 * numDeg J 2 + 3 * numDeg J 3 + 4 * numDeg J 4 = J.card * r := by
  have h_sum_deg : (J.biUnion id).sum (fun v => edgeDeg J v) = J.card * r := by
    convert incid_total r J huni ∅ using 1;
    · simp +decide [ edgeDeg, block ];
      exact Finset.sum_congr rfl fun x hx => by rw [ Finset.inter_eq_left.mpr ( Finset.filter_subset _ _ ) ] ;
    · simp +decide;
  unfold numDeg;
  rw [ ← h_sum_deg, Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.card_filter ];
  rw [ Finset.mul_sum _ _ _, Finset.mul_sum _ _ _, Finset.mul_sum _ _ _ ];
  simpa only [verts, ← Finset.sum_add_distrib] using Finset.sum_congr rfl fun x hx => by have := hdeg x; interval_cases edgeDeg J x <;> trivial;

/-
**The bound on `z`.**  A pair of edges with no common degree-`4` vertex has a
common vertex of degree `2` or `3`; a degree-`2` vertex serves `1` pair and a
degree-`3` vertex serves `3` pairs, so `z ≤ x₂ + 3x₃`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma z_le (J : Finset (Finset V)) (hint : Intersecting J)
    (hdeg : ∀ v, edgeDeg J v ≤ 4) :
    zCount J ≤ numDeg J 2 + 3 * numDeg J 3 := by
  refine' le_trans _ ( _ : _ ≤ numDeg J 2 + 3 * numDeg J 3 );
  exact ∑ v ∈ ( verts J ).filter ( fun v => edgeDeg J v = 2 ∨ edgeDeg J v = 3 ), ( ( block J v ).powersetCard 2 ).card;
  · refine' le_trans ( Finset.card_le_card _ ) ( Finset.card_biUnion_le );
    intro s hs; simp_all +decide [ codeg ] ;
    obtain ⟨A, B, hAB⟩ : ∃ A B : Finset V, A ∈ J ∧ B ∈ J ∧ s = {A, B} ∧ A ≠ B := by
      rcases Finset.card_eq_two.mp hs.1.2 with ⟨ A, B, hAB ⟩ ; use A, B ; aesop;
    obtain ⟨v, hv⟩ : ∃ v ∈ A ∩ B, edgeDeg J v ≤ 3 := by
      obtain ⟨v, hv⟩ : ∃ v ∈ A ∩ B, edgeDeg J v ≠ 4 := by
        contrapose! hs; simp_all +decide [ Finset.subset_iff ] ;
        obtain ⟨ v, hv ⟩ := Finset.nonempty_iff_ne_empty.mpr ( show A ∩ B ≠ ∅ from Finset.Nonempty.ne_empty ( by simpa using ‹Intersecting J› A hAB.1 B hAB.2.1 ) ) ; use v; simp_all +decide [ deg4Verts, block ] ;
        exact Finset.mem_biUnion.mpr ⟨ A, hAB.1, hv.1 ⟩;
      exact ⟨ v, hv.1, Nat.le_of_lt_succ ( lt_of_le_of_ne ( hdeg v ) hv.2 ) ⟩;
    refine' ⟨ v, ⟨ _, _ ⟩, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
    · exact Finset.mem_biUnion.mpr ⟨ A, hAB.1, hv.1.1 ⟩;
    · have h_edgeDeg_ge_2 : 2 ≤ edgeDeg J v := by
        exact Finset.one_lt_card.2 ⟨ A, by aesop, B, by aesop ⟩;
      grind;
    · exact ⟨ Finset.mem_filter.mpr ⟨ hAB.1, hv.1.1 ⟩, Finset.mem_filter.mpr ⟨ hAB.2.1, hv.1.2 ⟩ ⟩;
  · unfold numDeg; simp +decide ;
    rw [ Finset.sum_congr rfl fun x hx => by rw [ ← edgeDeg_eq_block_card ] ] ; simp +decide [ Finset.sum_filter ] ;
    rw [ Finset.card_filter, Finset.card_filter ] ; rw [ Finset.mul_sum _ _ _ ] ; rw [ ← Finset.sum_add_distrib ] ; exact Finset.sum_le_sum fun x hx => by have := hdeg x; interval_cases edgeDeg J x <;> trivial;

/-
**Equation (10), packaged.**  There is a codegree-`≤ 1` subfamily `W'` of the
degree-`4` vertices with `4·C(q,2) ≤ 4|W'| + 5qr`, i.e. `|E(Qlin)| ≥ C(q,2) − 5qr/4`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma Qlin_exists (r : ℕ) (J : Finset (Finset V)) (huni : IsUniform r J)
    (hint : Intersecting J) (hdeg : ∀ v, edgeDeg J v ≤ 4) :
    ∃ W' ⊆ deg4Verts J,
      (∀ p ∈ J, ∀ q ∈ J, p ≠ q →
        (W'.filter (fun v => p ∈ block J v ∧ q ∈ block J v)).card ≤ 1) ∧
      4 * (J.card).choose 2 ≤ 4 * W'.card + 5 * (J.card * r) := by
  obtain ⟨ W', hW' ⟩ := exists_codeg_le_one J ( deg4Verts J );
  use W';
  refine' ⟨ hW'.1, _, _ ⟩;
  · intro p hp q hq hpq; specialize hW'; have := hW'.2.1 { p, q } ; simp_all +decide [ codeg ] ;
    convert hW'.2.1 { p, q } ( by aesop_cat ) ( by rw [ Finset.card_insert_of_notMem, Finset.card_singleton ] ; aesop_cat ) using 1 ; simp +decide [ Finset.subset_iff, block ];
  · have := potential_add_choose J ?_ ?_;
    · have := z_le J ‹_› ‹_›;
      have := degree_sum r J huni hdeg;
      linarith [ show ( deg4Verts J ).card = numDeg J 4 from deg4Verts_card J ];
    · exact fun v hv => edgeDeg_eq_block_card J v ▸ Finset.mem_filter.mp hv |>.2;
    · exact fun v hv => Finset.filter_subset _ _

/- ## The large-`q` cover bound (equations (10)–(11)) -/

/-
Pure real-arithmetic core of the large-`q` cover bound.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma tau_real_arith (τ m4 w q r ε : ℝ) (hq : 0 < q)
    (hτ : τ ≤ q / 2 - m4 + 1 / 2)
    (hm : 3 * w - ε * q * q ≤ q * m4)
    (hw : 2 * q * (q - 1) ≤ 4 * w + 5 * q * r) :
    τ ≤ 15 * r / 4 - q + ε * q + 2 := by
  nlinarith [ mul_pos hq hq ]

/-
Casting helper for the cover bound `τ ≤ q/2 − m + 1/2`.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma tau_cast (c m q : ℕ) (h : c ≤ m + (q - 4 * m + 1) / 2) (h2 : 4 * m ≤ q) :
    (c : ℝ) ≤ (q : ℝ) / 2 - (m : ℝ) + 1 / 2 := by
  field_simp;
  norm_cast;
  rw [ Int.subNatNat_eq_coe ] ; omega

/-
Casting helper: clearing the denominator in the Kahn matching bound.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma kahn_mul (w q ε a : ℝ) (hq : 0 < q) (h : 3 * w / q - ε * q ≤ a) :
    3 * w - ε * q * q ≤ q * a := by
  nlinarith [ mul_div_cancel₀ ( 3 * w ) hq.ne' ]

/-
Casting helper: `2·C(q,2) = q(q−1)` turns equation (10) into real form.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma choose_cast (w q r : ℕ) (hq : 1 ≤ q)
    (h : 4 * (q.choose 2) ≤ 4 * w + 5 * (q * r)) :
    2 * (q : ℝ) * ((q : ℝ) - 1) ≤ 4 * (w : ℝ) + 5 * (q : ℝ) * (r : ℝ) := by
  norm_cast;
  rw [ Nat.choose_two_right ] at h;
  linarith [ Nat.div_mul_cancel ( show 2 ∣ q * ( q - 1 ) from even_iff_two_dvd.mp ( Nat.even_mul_pred_self _ ) ) ]

/- ## Arithmetic for the optimized matching-or-star bound -/

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
noncomputable def betaCut : ℝ := (4 + Real.sqrt 19) / 3

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
noncomputable def asymptoticConstant : ℝ :=
  (41 - Real.sqrt 19) / 12

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
noncomputable def savingTarget (q r : ℝ) : ℝ :=
  3 * q / 10 - (19 + Real.sqrt 19) * r / 60

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma sqrt19_sq : (Real.sqrt 19) ^ 2 = (19 : ℝ) := by
  norm_num

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma sqrt19_one_le : (1 : ℝ) ≤ Real.sqrt 19 := by
  nlinarith [sqrt19_sq, Real.sqrt_nonneg (19 : ℝ)]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- At and above the new cutoff, the linearization count dominates twice the
square of the target cover saving. -/
lemma savingTarget_sq_le (q r : ℝ) (hr : 0 ≤ r)
    (hq : betaCut * r ≤ q) :
    2 * (savingTarget q r) ^ 2 ≤ q ^ 2 / 2 - 5 * q * r / 4 := by
  have hs0 : 0 ≤ Real.sqrt 19 := Real.sqrt_nonneg _
  have hs1 : 1 ≤ Real.sqrt 19 := sqrt19_one_le
  have hfactor :
      0 ≤ 96 * q + (38 * Real.sqrt 19 - 133) * r := by
    dsimp [betaCut] at hq
    nlinarith
  have hprod :=
    mul_nonneg (sub_nonneg.mpr hq) hfactor
  have hid :
      300 * (q ^ 2 / 2 - 5 * q * r / 4 -
        2 * (savingTarget q r) ^ 2) =
      (q - betaCut * r) *
        (96 * q + (38 * Real.sqrt 19 - 133) * r) := by
    dsimp [betaCut, savingTarget]
    field_simp
    ring_nf
    nlinarith [sqrt19_sq]
  nlinarith

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma savingTarget_bounds (q r : ℝ) (hr : 1 ≤ r)
    (hqlow : betaCut * r ≤ q) (hqhigh : q ≤ 3 * r + 1) :
    0 < savingTarget q r ∧ q / 10 ≤ savingTarget q r ∧
      savingTarget q r ≤ r := by
  have hs0 : 0 ≤ Real.sqrt 19 := Real.sqrt_nonneg _
  have hs1 : 1 ≤ Real.sqrt 19 := sqrt19_one_le
  dsimp [betaCut, savingTarget] at *
  constructor
  · nlinarith
  constructor <;> nlinarith

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- The real-arithmetic estimate in the low-maximum-degree branch. -/
lemma matching_saving_arith (q r γ L D w a : ℝ)
    (hr : 1 ≤ r) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hL0 : 0 < L) (hLq : q / 10 ≤ L) (hLr : L ≤ r)
    (hD0 : 0 < D) (hDhi : D ≤ 2 * L + 1)
    (hw : 2 * L ^ 2 - q / 2 ≤ w)
    (ha0 : 0 ≤ a)
    (hmatch : w ≤ (1 + γ) * D * a) :
    L - 2 * γ * r - 3 ≤ a := by
  by_contra h
  have ha : a < L - 2 * γ * r - 3 := lt_of_not_ge h
  have hApos : 0 < L - 2 * γ * r - 3 := lt_of_le_of_lt ha0 ha
  have hcoef : 0 < (1 + γ) * D := by positivity
  have hupper₁ :
      (1 + γ) * D * a <
        (1 + γ) * D * (L - 2 * γ * r - 3) :=
    mul_lt_mul_of_pos_left ha hcoef
  have hupper₂ :
      (1 + γ) * D * (L - 2 * γ * r - 3) ≤
        (1 + γ) * (2 * L + 1) * (L - 2 * γ * r - 3) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hDhi (by positivity)) hApos.le
  have hbase : 0 ≤ 5 * L - q / 2 + 3 := by nlinarith
  have hquad : 0 ≤ -2 * L ^ 2 + 4 * L * r := by
    have := mul_nonneg hL0.le (sub_nonneg.mpr (by linarith : L ≤ 2 * r))
    nlinarith
  have hlin :
      0 ≤ -2 * L ^ 2 + 4 * L * r + 5 * L + 2 * r + 3 := by
    nlinarith
  have hpoly₁ :
      0 ≤ γ ^ 2 * (4 * L * r + 2 * r) := by positivity
  have hpoly₂ :
      0 ≤ γ * (-2 * L ^ 2 + 4 * L * r + 5 * L + 2 * r + 3) :=
    mul_nonneg hγ.le hlin
  have hbudget :
      (1 + γ) * (2 * L + 1) * (L - 2 * γ * r - 3)
        ≤ 2 * L ^ 2 - q / 2 := by
    nlinarith
  linarith

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- **The large-`q` cover bound.**  For every `ε > 0` there is a threshold `n₀`
so that any `r`-uniform intersecting hypergraph `J` of maximum degree `≤ 4` with
at least `n₀` edges satisfies `τ(J) ≤ 15r/4 − q + ε q + 2`. -/
lemma tau_largeQ (kahn : KahnCorollary.{u}) (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ (r : ℕ) {V : Type u} [DecidableEq V] (J : Finset (Finset V)),
      IsUniform r J → Intersecting J → (∀ v, edgeDeg J v ≤ 4) → n₀ ≤ J.card →
      (coverNum J : ℝ) ≤ 15 * (r : ℝ) / 4 - (J.card : ℝ) + ε * (J.card : ℝ) + 2 := by
  obtain ⟨n₀, hn₀⟩ := kahn ε hε
  refine ⟨max n₀ 1, ?_⟩
  intro r V _ J hJ₁ hJ₂ hJ₃ hJ₄
  have hq1 : 1 ≤ J.card := le_trans (le_max_right n₀ 1) hJ₄
  have hqn₀ : n₀ ≤ J.card := le_trans (le_max_left n₀ 1) hJ₄
  obtain ⟨W', hW'sub, hW'codeg, hW'count⟩ := Qlin_exists r J hJ₁ hJ₂ hJ₃
  have hBsub : ∀ v ∈ W', block J v ⊆ J := fun v _ => Finset.filter_subset _ _
  have hBcard : ∀ v ∈ W', (block J v).card = 4 := by
    intro v hv
    have hv4 := hW'sub hv
    simp only [deg4Verts, Finset.mem_filter] at hv4
    rw [← edgeDeg_eq_block_card]; exact hv4.2
  obtain ⟨M, hMsub, hMdisj, hMbound⟩ :=
    hn₀ J.card hqn₀ (α := Finset V) (ι := V) (ground := J) (W := W') (B := block J)
      rfl hBsub hBcard hW'codeg
  have hMblockcard : ∀ v ∈ M, (block J v).card = 4 := fun v hv => hBcard v (hMsub hv)
  have hMblocksub : ∀ v ∈ M, block J v ⊆ J := fun v hv => hBsub v (hMsub hv)
  have hcover := matching_cover4 J hJ₂ M hMblockcard hMdisj
  have hmatched := matched_blocks_card J M hMblockcard hMblocksub hMdisj
  have hqpos : (0 : ℝ) < (J.card : ℝ) := by exact_mod_cast hq1
  have hτ : (coverNum J : ℝ) ≤ (J.card : ℝ) / 2 - (M.card : ℝ) + 1 / 2 :=
    tau_cast _ _ _ hcover hmatched
  have hm : 3 * (W'.card : ℝ) - ε * (J.card : ℝ) * (J.card : ℝ) ≤ (J.card : ℝ) * (M.card : ℝ) :=
    kahn_mul _ _ _ _ hqpos hMbound
  have hwineq : 2 * (J.card : ℝ) * ((J.card : ℝ) - 1)
      ≤ 4 * (W'.card : ℝ) + 5 * (J.card : ℝ) * (r : ℝ) :=
    choose_cast _ _ _ hq1 hW'count
  exact tau_real_arith _ _ _ _ _ _ hqpos hτ hm hwineq

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- The optimized large-`q` cover bound obtained by balancing the
actual-degree Kahn matching against the linear-star cover. -/
lemma tau_largeQ_optimized (kahn : KahnDegreeCorollary.{u})
    (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ∃ r₀ : ℕ, ∀ (r : ℕ), r₀ ≤ r →
      ∀ {V : Type u} [DecidableEq V] (J : Finset (Finset V)),
        IsUniform r J → Intersecting J → (∀ v, edgeDeg J v ≤ 4) →
        betaCut * (r : ℝ) ≤ (J.card : ℝ) →
        (J.card : ℝ) ≤ 3 * (r : ℝ) + 1 →
        (coverNum J : ℝ) ≤
          (J.card : ℝ) / 2 -
          savingTarget (J.card : ℝ) (r : ℝ) +
          2 * γ * (r : ℝ) + 4 := by
  obtain ⟨D₀, hD₀⟩ := matching_or_star_cover kahn γ hγ
  refine ⟨max (5 * D₀ + 1) 1, ?_⟩
  intro r hr V _ J hJuni hJint hJdeg hqlow hqhigh
  have hr1 : 1 ≤ r := le_trans (le_max_right _ _) hr
  have hrr : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hs4 : (4 : ℝ) ≤ Real.sqrt 19 := by
    nlinarith [sqrt19_sq, Real.sqrt_nonneg (19 : ℝ)]
  have hq1real : (1 : ℝ) ≤ (J.card : ℝ) := by
    dsimp [betaCut] at hqlow
    nlinarith
  have hq1 : 1 ≤ J.card := by exact_mod_cast hq1real
  obtain ⟨W, hWsub, hWcodeg, hWcount⟩ :=
    Qlin_exists r J hJuni hJint hJdeg
  have hW4 : ∀ v ∈ W, (block J v).card = 4 := by
    intro v hv
    have hv4 := hWsub hv
    simp only [deg4Verts, Finset.mem_filter] at hv4
    rw [← edgeDeg_eq_block_card]
    exact hv4.2
  have hBsub : ∀ v ∈ W, block J v ⊆ J :=
    fun v _ => Finset.filter_subset _ _
  let L : ℝ := savingTarget (J.card : ℝ) (r : ℝ)
  have hLbounds :
      0 < L ∧ (J.card : ℝ) / 10 ≤ L ∧ L ≤ (r : ℝ) := by
    exact savingTarget_bounds _ _ hrr hqlow hqhigh
  let D : ℕ := ⌈2 * L⌉₊
  have hDlow : 2 * L ≤ (D : ℝ) := by
    exact Nat.le_ceil (2 * L)
  have hDhi : (D : ℝ) ≤ 2 * L + 1 := by
    exact (Nat.ceil_lt_add_one (mul_nonneg (by norm_num) hLbounds.1.le)).le
  have hq2r : (2 : ℝ) * r ≤ J.card := by
    dsimp [betaCut] at hqlow
    nlinarith
  have hLr5 : (r : ℝ) / 5 ≤ L := by
    nlinarith [hLbounds.2.1]
  have hDlarge : D₀ ≤ D := by
    have hrD₀ : 5 * D₀ + 1 ≤ r :=
      le_trans (le_max_left _ _) hr
    have hcast : (5 * D₀ : ℝ) ≤ (r : ℝ) := by
      exact_mod_cast (show 5 * D₀ ≤ r by omega)
    have hD₀r : (D₀ : ℝ) ≤ (r : ℝ) / 5 := by
      push_cast at hcast
      linarith
    exact_mod_cast (show (D₀ : ℝ) ≤ (D : ℝ) by linarith)
  have hDpos : 0 < D := by
    exact_mod_cast (show (0 : ℝ) < (D : ℝ) by linarith)
  have hJD : J.card ≤ 10 * D := by
    have hreal : (J.card : ℝ) ≤ 10 * (D : ℝ) := by linarith
    exact_mod_cast hreal
  have hWcard : W.card ≤ 100 * D ^ 2 := calc
    W.card ≤ J.card ^ 2 := linear_blocks_card_bound J W (block J) hBsub hW4 hWcodeg
    _ ≤ (10 * D) ^ 2 := Nat.pow_le_pow_left hJD _
    _ = 100 * D ^ 2 := by ring
  have hAlt :=
    hD₀ J hJint W D hDlarge hDpos hWcard hW4 hBsub hWcodeg
  rcases hAlt with hstar | hmatch
  · have hLD : L ≤ (D : ℝ) / 2 := by linarith
    have herr : 0 ≤ 2 * γ * (r : ℝ) + 4 := by positivity
    change (coverNum J : ℝ) ≤
      (J.card : ℝ) / 2 - L + 2 * γ * (r : ℝ) + 4
    linarith
  · have hwreal :
        2 * (J.card : ℝ) * ((J.card : ℝ) - 1)
          ≤ 4 * (W.card : ℝ) +
            5 * (J.card : ℝ) * (r : ℝ) :=
      choose_cast _ _ _ hq1 hWcount
    have hsq :
        2 * L ^ 2 ≤
          (J.card : ℝ) ^ 2 / 2 -
            5 * (J.card : ℝ) * (r : ℝ) / 4 := by
      exact savingTarget_sq_le _ _ (by positivity) hqlow
    have hw :
        2 * L ^ 2 - (J.card : ℝ) / 2 ≤ (W.card : ℝ) := by
      nlinarith
    have hden : 0 < (1 + γ) * (D : ℝ) := by positivity
    let a : ℝ := (W.card : ℝ) / ((1 + γ) * (D : ℝ))
    have ha0 : 0 ≤ a := by positivity
    have hWa : (W.card : ℝ) ≤ (1 + γ) * (D : ℝ) * a := by
      dsimp [a]
      rw [mul_div_cancel₀ _ hden.ne']
    have ha :
        L - 2 * γ * (r : ℝ) - 3 ≤ a :=
      matching_saving_arith _ _ _ _ _ _ _
        hrr hγ hγ1 hLbounds.1 hLbounds.2.1 hLbounds.2.2
        (by positivity) hDhi hw ha0 hWa
    dsimp [a] at ha
    linarith

/- ## Theorem 3 -/

/-
Pure real-arithmetic combine for the small-`q` regime.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma combineA (m q r ε : ℝ)
    (hA : 15 * r ≤ 4 * m + q + 20)
    (hcase : q ≤ betaCut * r) (hεr : 5 ≤ ε * r) :
    (asymptoticConstant - ε) * r ≤ m := by
  dsimp [betaCut, asymptoticConstant] at *
  nlinarith

/-
Pure real-arithmetic combine for the large-`q` regime.
-/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
lemma combineB (m q r τ ε γ : ℝ)
    (hm : q + 5 * r - 5 * τ ≤ m)
    (hτ : τ ≤ q / 2 - savingTarget q r + 2 * γ * r + 4)
    (hε : 0 < ε) (hγ : γ ≤ ε / 20) (hlarge : 40 ≤ ε * r) :
    (asymptoticConstant - ε) * r ≤ m := by
  have hid :
      5 * r - 3 * q / 2 + 5 * savingTarget q r =
        asymptoticConstant * r := by
    dsimp [savingTarget, asymptoticConstant]
    ring
  have hγr : γ * r ≤ (ε / 20) * r := by
    have hr0 : 0 ≤ r := by nlinarith
    exact mul_le_mul_of_nonneg_right hγ hr0
  nlinarith

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- **Theorem 3.**  As `r → ∞`,
`g(r) ≥ ((41 - √19)/12 - o(1)) r`: for every `ε > 0` there is `r₀` so that
every `r`-uniform intersecting hypergraph `H` with cover number `r` and
`r ≥ r₀` has at least `((41 - √19)/12 - ε)r` edges. -/
theorem theorem3 (kahn : KahnDegreeCorollary.{u}) :
    ∀ ε : ℝ, 0 < ε → ∃ r₀ : ℕ, ∀ (r : ℕ), r₀ ≤ r →
      ∀ {V : Type u} [DecidableEq V] (H : Finset (Finset V)),
        IsUniform r H → Intersecting H → coverNum H = r →
        (asymptoticConstant - ε) * (r : ℝ) ≤ (H.card : ℝ) := by
  intro ε hε
  let γ : ℝ := min (ε / 20) (1 / 2)
  have hγ : 0 < γ := lt_min (by positivity) (by norm_num)
  have hγ1 : γ ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
  have hγε : γ ≤ ε / 20 := min_le_left _ _
  obtain ⟨n₀, hn₀⟩ := tau_largeQ_optimized kahn γ hγ hγ1
  refine ⟨max n₀ (⌈(40 : ℝ) / ε⌉₊ + 1), ?_⟩
  intro r hr V _ H huni hint hcov
  have hrn₀ : n₀ ≤ r := le_trans (le_max_left _ _) hr
  have hr_big : (40 : ℝ) / ε + 1 ≤ (r : ℝ) := by
    have h1 : (⌈(40 : ℝ) / ε⌉₊ : ℝ) + 1 ≤ (r : ℝ) := by
      have := le_trans (le_max_right n₀ (⌈(40 : ℝ) / ε⌉₊ + 1)) hr
      have := (Nat.cast_le (α := ℝ)).2 this
      push_cast at this; linarith
    have h2 : (40 : ℝ) / ε ≤ (⌈(40 : ℝ) / ε⌉₊ : ℝ) := Nat.le_ceil _
    linarith
  have hεr : 40 ≤ ε * r := by
    have : ε * ((40 : ℝ) / ε + 1) ≤ ε * r := by
      apply mul_le_mul_of_nonneg_left hr_big hε.le
    rw [mul_add, mul_one, mul_div_cancel₀ _ hε.ne'] at this
    linarith
  obtain ⟨J, k, hJsub, hJdeg, hJcard, hJcov⟩ := peel5 r H huni hint
  have hJuni : IsUniform r J := fun E hE => huni E (hJsub hE)
  have hJint : Intersecting J := fun E hE F hF => hint E (hJsub hE) F (hJsub hF)
  have hkey := keyLemma r J hJuni hJint
  have hr_le : r ≤ k + coverNum J := hcov ▸ hJcov
  by_cases hcase :
      (J.card : ℝ) ≤ betaCut * (r : ℝ)
  ·
    have hA : 15 * r ≤ 4 * H.card + J.card + 20 := by omega
    apply combineA (H.card : ℝ) (J.card : ℝ) (r : ℝ) ε
    · exact_mod_cast hA
    · exact hcase
    · linarith
  ·
    have hcaseB :
        betaCut * (r : ℝ) ≤ (J.card : ℝ) :=
      le_of_lt (lt_of_not_ge hcase)
    have hq37 := lemma1_deg4 r J hJuni hJint hJdeg
    have hqreal : (J.card : ℝ) ≤ 3 * (r : ℝ) + 1 := by
      exact_mod_cast hq37
    have htau :=
      hn₀ r hrn₀ J hJuni hJint hJdeg hcaseB hqreal
    have hm : (J.card : ℝ) + 5 * r - 5 * (coverNum J : ℝ) ≤ (H.card : ℝ) := by
      have h1 : (r : ℝ) ≤ (k : ℝ) + (coverNum J : ℝ) := by exact_mod_cast hr_le
      have h2 : (J.card : ℝ) + 5 * (k : ℝ) ≤ (H.card : ℝ) := by exact_mod_cast hJcard
      linarith
    exact combineB (H.card : ℝ) (J.card : ℝ) (r : ℝ)
      (coverNum J : ℝ) ε γ hm htau hε hγε hεr

/-
## Theorem 1, assembled (parts (i) and (ii)) and its corollary

The two parts were proved above:

* Part (i) is `theorem1` (additive form `3r ≤ |E(H)| + 4`) and `theorem1'`
  (subtractive form `3r − 4 ≤ |E(H)|`).
* Part (ii) is `theorem3`.

We record convenient aliases `theorem1_i`, `theorem1_ii`, the combined statement
`theorem1_full`, and the corollary `corollary_gt_3r`.
-/

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- **Theorem 1 (i).**  For every positive integer `r`, every `r`-uniform
intersecting hypergraph `H` with cover number `r` has `g(r) ≥ 3r − 4` edges. -/
theorem theorem1_i (r : ℕ) (hr : 0 < r) {V : Type u} [DecidableEq V]
    (H : Finset (Finset V))
    (huni : IsUniform r H) (hint : Intersecting H) (hcover : coverNum H = r) :
    3 * r - 4 ≤ H.card :=
  theorem1' r hr H huni hint hcover

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- **Theorem 1 (ii).**  For every `ε > 0` there is `r₀` such that, for every
`r ≥ r₀`, every `r`-uniform intersecting hypergraph `H` with cover number `r`
has `g(r) ≥ ((41 - √19)/12 − ε) r` edges. -/
theorem theorem1_ii (kahn : KahnTheorem.{u}) :
    ∀ ε : ℝ, 0 < ε → ∃ r₀ : ℕ, ∀ (r : ℕ), r₀ ≤ r →
      ∀ {V : Type u} [DecidableEq V] (H : Finset (Finset V)),
        IsUniform r H → Intersecting H → coverNum H = r →
        ((41 - Real.sqrt 19) / 12 - ε) * (r : ℝ) ≤ (H.card : ℝ) := by
  simpa [asymptoticConstant] using
    theorem3 (kahnDegreeCorollary_of_kahnTheorem kahn)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- **Theorem 1.**  Both parts (i) and (ii) together, given Kahn's theorem as a
black box. -/
theorem theorem1_full (kahn : KahnTheorem.{u}) :
    (∀ (r : ℕ), 0 < r → ∀ {V : Type u} [DecidableEq V] (H : Finset (Finset V)),
        IsUniform r H → Intersecting H → coverNum H = r → 3 * r - 4 ≤ H.card)
    ∧
    (∀ ε : ℝ, 0 < ε → ∃ r₀ : ℕ, ∀ (r : ℕ), r₀ ≤ r →
        ∀ {V : Type u} [DecidableEq V] (H : Finset (Finset V)),
          IsUniform r H → Intersecting H → coverNum H = r →
          ((41 - Real.sqrt 19) / 12 - ε) * (r : ℝ) ≤ (H.card : ℝ)) :=
  ⟨fun r hr _ _ H huni hint hcov => theorem1_i r hr H huni hint hcov,
   theorem1_ii kahn⟩

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
/-- **Corollary.**  Since `(41 - √19)/12 > 3`, part (ii) implies `g(r) > 3r`
for all sufficiently large `r`: there is `r₀` such that, for every `r ≥ r₀`,
every `r`-uniform intersecting hypergraph `H` with cover number `r` has more
than `3r` edges.  This crosses the threshold `g(r) < 3r` that Erdős explicitly
noted was unresolved. -/
theorem corollary_gt_3r (kahn : KahnTheorem.{u}) :
    ∃ r₀ : ℕ, ∀ (r : ℕ), r₀ ≤ r →
      ∀ {V : Type u} [DecidableEq V] (H : Finset (Finset V)),
        IsUniform r H → Intersecting H → coverNum H = r →
        3 * r < H.card := by
  obtain ⟨r₀, h⟩ := theorem1_ii kahn (1 / 100) (by norm_num)
  refine ⟨max r₀ 1, ?_⟩
  intro r hr V _ H huni hint hcov
  have hr₀ : r₀ ≤ r := le_trans (le_max_left _ _) hr
  have hr1 : 1 ≤ r := le_trans (le_max_right _ _) hr
  have hb := h r hr₀ H huni hint hcov
  have hreal : (3 : ℝ) * (r : ℝ) < (H.card : ℝ) := by
    have hs0 : 0 ≤ Real.sqrt 19 := Real.sqrt_nonneg _
    have hs2 : (Real.sqrt 19) ^ 2 = (19 : ℝ) := sqrt19_sq
    have hrpos : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    nlinarith
  exact_mod_cast hreal

end ErdosLovasz
namespace ErdosLovasz

open Finset Filter

lemma kahnDegreeCorollary_of_chromatic_index
    (hpoly : ∃ γ : ℝ, 0 < γ ∧ ∃ D₀ : ℝ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (D : ℝ),
        D₀ ≤ D → Pseudorandom.IsUniform H 4 → (∀ v, (Pseudorandom.degree H v : ℝ) ≤ D) →
        (∀ u v, u ≠ v → (Pseudorandom.codegree H u v : ℝ) ≤ D ^ (1 - 1 / 2 : ℝ)) →
        (H.card : ℝ) ≤ Real.exp (D ^ γ) →
        ∃ (m : ℕ) (c : Finset V → Fin m), (m : ℝ) ≤ D + D ^ (1 - γ) ∧
          Pseudorandom.IsProperEdgeColouring H m c) :
    KahnDegreeCorollary.{0} := by
  intro ε hε
  obtain ⟨γ, hγ, D₀, hcolor⟩ := hpoly
  have hExp : ∀ᶠ x : ℝ in atTop, 100 * x ^ 2 ≤ Real.exp (x ^ γ) := by
    have hTo := (tendsto_exp_div_rpow_atTop (2 / γ)).comp (tendsto_rpow_atTop hγ)
    filter_upwards [hTo.eventually_ge_atTop 100, eventually_gt_atTop (0 : ℝ)] with x hx hx0
    change 100 ≤ Real.exp (x ^ γ) / (x ^ γ) ^ (2 / γ) at hx
    have heq : γ * (2 / γ) = 2 := by field_simp
    rw [← Real.rpow_mul hx0.le, heq, Real.rpow_two] at hx
    exact (le_div_iff₀ (by positivity)).mp hx
  have hErr : ∀ᶠ x : ℝ in atTop, x + x ^ (1 - γ) ≤ (1 + ε) * x := by
    filter_upwards [(tendsto_rpow_neg_atTop hγ).eventually (gt_mem_nhds hε),
      eventually_gt_atTop (0 : ℝ)] with x hx hx0
    rw [sub_eq_add_neg, Real.rpow_add hx0, Real.rpow_one]
    nlinarith [mul_le_mul_of_nonneg_left hx.le hx0.le]
  obtain ⟨D₁, hD₁⟩ := eventually_atTop.mp
    (hExp.and (hErr.and ((eventually_ge_atTop D₀).and (eventually_ge_atTop (1 : ℝ)))))
  refine ⟨⌈D₁⌉₊, ?_⟩
  intro D hD α instα ι instι W B hSize hB hdeg hcod
  have hD_R : D₁ ≤ (D : ℝ) := (Nat.le_ceil D₁).trans (by exact_mod_cast hD)
  obtain ⟨hExpD, hErrD, hD₀, hDpos⟩ := hD₁ D hD_R
  let U := W.biUnion B
  let V := ↥U
  let emb : V ↪ α := ⟨Subtype.val, Subtype.val_injective⟩
  let B' : ι → Finset V := fun w ↦ U.attach.filter (fun v ↦ v.val ∈ B w)
  have hmap (w : ι) (hw : w ∈ W) : (B' w).map emb = B w := by
    ext a
    constructor
    · intro ha
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp ha
      exact (Finset.mem_filter.mp hv).2
    · intro ha
      have hu : a ∈ U := Finset.mem_biUnion.mpr ⟨w, hw, ha⟩
      let v : V := ⟨a, hu⟩
      exact Finset.mem_map.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, ha⟩, rfl⟩
  have hmem (w : ι) (v : V) : v ∈ B' w ↔ v.val ∈ B w :=
    ⟨fun h ↦ (Finset.mem_filter.mp h).2,
      fun h ↦ Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, h⟩⟩
  have hBInj : Set.InjOn B W := by
    intro w hw w' hw' heq
    by_contra hne
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by rw [hB w hw]; decide :
      1 < (B w).card)
    have haw : a ∈ B w' := heq ▸ ha
    have hbw : b ∈ B w' := heq ▸ hb
    have hlt : 1 < (W.filter (fun w ↦ a ∈ B w ∧ b ∈ B w)).card :=
      Finset.one_lt_card.mpr ⟨w, Finset.mem_filter.mpr ⟨hw, ha, hb⟩,
        w', Finset.mem_filter.mpr ⟨hw', haw, hbw⟩, hne⟩
    exact (not_lt_of_ge (hcod a b hab)) hlt
  have hB'Inj : Set.InjOn B' W := by
    intro w hw w' hw' heq
    apply hBInj hw hw'
    rw [← hmap w hw, ← hmap w' hw', heq]
  let H := W.image B'
  have hH (P : Finset V → Prop) [DecidablePred P] :
      H.filter P = (W.filter (fun w ↦ P (B' w))).image B' := by
    ext E
    simp only [H, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨w, hw, rfl⟩, hp⟩
      exact ⟨w, ⟨hw, hp⟩, rfl⟩
    · rintro ⟨w, ⟨hw, hp⟩, rfl⟩
      exact ⟨⟨w, hw, rfl⟩, hp⟩
  have hUni : Pseudorandom.IsUniform H 4 := by
    rintro E hE
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hE
    rw [← Finset.card_map emb, hmap w hw, hB w hw]
  have hDeg : ∀ v, (Pseudorandom.degree H v : ℝ) ≤ D := by
    intro v
    have heq : W.filter (fun w ↦ v ∈ B' w) = W.filter (fun w ↦ v.val ∈ B w) := by
      ext w
      simp only [Finset.mem_filter, hmem]
    exact_mod_cast (show Pseudorandom.degree H v ≤ D by
      rw [Pseudorandom.degree, hH, heq]
      exact Finset.card_image_le.trans (hdeg v.val))
  have hCod : ∀ u v, u ≠ v →
      (Pseudorandom.codegree H u v : ℝ) ≤ (D : ℝ) ^ (1 - 1 / 2 : ℝ) := by
    intro u v huv
    have heq : W.filter (fun w ↦ u ∈ B' w ∧ v ∈ B' w) =
        W.filter (fun w ↦ u.val ∈ B w ∧ v.val ∈ B w) := by
      ext w
      simp only [Finset.mem_filter, hmem]
    have hvv : u.val ≠ v.val := fun eq ↦ huv (Subtype.ext eq)
    have ht : Pseudorandom.codegree H u v ≤ 1 := by
      rw [Pseudorandom.codegree, hH, heq]
      exact Finset.card_image_le.trans (hcod u.val v.val hvv)
    refine (show (Pseudorandom.codegree H u v : ℝ) ≤ 1 by exact_mod_cast ht).trans ?_
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hDpos (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2)
  have hCard : (H.card : ℝ) ≤ Real.exp ((D : ℝ) ^ γ) :=
    (show (H.card : ℝ) ≤ W.card by exact_mod_cast Finset.card_image_le).trans
      ((show (W.card : ℝ) ≤ 100 * (D : ℝ) ^ 2 by exact_mod_cast hSize).trans hExpD)
  obtain ⟨k, c, hk, hProper⟩ := hcolor V H D hD₀ hUni hDeg hCod hCard
  let col (w : ι) := (c (B' w)).val
  have hP (w : ι) (hw : w ∈ W) (w' : ι) (hw' : w' ∈ W) (hne : w ≠ w')
      (hEq : col w = col w') : Disjoint (B w) (B w') := by
    rw [← hmap w hw, ← hmap w' hw', Finset.disjoint_map]
    exact hProper _ (Finset.mem_image_of_mem B' hw) _ (Finset.mem_image_of_mem B' hw')
      (fun heq ↦ hne (hB'Inj hw hw' heq)) (Fin.ext hEq)
  obtain ⟨M, hMW, hDisj, hCount⟩ :=
    kahn_pigeonhole_matching W B k col (fun w _ ↦ (c (B' w)).isLt) hP
  exact ⟨M, hMW, hDisj, hCount.trans
    (mul_le_mul_of_nonneg_right (hk.trans hErrD) (Nat.cast_nonneg M.card))⟩

end ErdosLovasz
namespace Erdos21Bridge

private lemma exists_family (n : ℕ) (hn : 0 < n) :
    ∃ F : Finset (Finset ℕ), Erdos21.IsErdosLovaszFamily n F := by
  classical
  let U := Finset.range (2 * n - 1)
  have hU : U.card = 2 * n - 1 := Finset.card_range _
  refine ⟨U.powersetCard n, ?_, ?_, ?_⟩
  · intro A hA
    exact (Finset.mem_powersetCard.mp hA).2
  · intro A hA B hB
    obtain ⟨hAU, hAc⟩ := Finset.mem_powersetCard.mp hA
    obtain ⟨hBU, hBc⟩ := Finset.mem_powersetCard.mp hB
    by_contra! h
    have hAB : Disjoint A B := Finset.disjoint_iff_inter_eq_empty.mpr
      h
    have hcard := Finset.card_le_card (Finset.union_subset hAU hBU)
    rw [Finset.card_union_of_disjoint hAB, hAc, hBc, hU] at hcard
    omega
  · intro S hS
    have hs : (U \ S).card + (U ∩ S).card = U.card :=
      Finset.card_sdiff_add_card_inter U S
    have hi : (U ∩ S).card ≤ S.card := Finset.card_le_card Finset.inter_subset_right
    obtain ⟨A, hA, hAc⟩ := Finset.exists_subset_card_eq (s := U \ S) (n := n) (by omega)
    refine ⟨A, Finset.mem_powersetCard.mpr ⟨hA.trans Finset.sdiff_subset, hAc⟩, ?_⟩
    exact Finset.disjoint_left.mpr (fun _ hx hy ↦ (Finset.mem_sdiff.mp (hA hy)).2 hx)

private lemma coverNum_eq {n : ℕ} {F : Finset (Finset ℕ)}
    (hF : Erdos21.IsErdosLovaszFamily n F) : ErdosLovasz.coverNum F = n := by
  obtain ⟨E, hE, _⟩ := hF.2.2 ∅ (by simp)
  apply le_antisymm
  · rw [← hF.1 E hE]
    apply ErdosLovasz.coverNum_le
    intro A hA
    obtain ⟨v, hv⟩ := hF.2.1 E hE A hA
    exact ⟨v, (Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hv).2⟩
  · obtain ⟨S, hS, hSc⟩ :=
      ErdosLovasz.exists_opt_cover (fun A hA ↦
        (ErdosLovasz.Intersecting.edge_nonempty hF.2.1 hA))
    by_contra! h
    obtain ⟨A, hA, hdisj⟩ := hF.2.2 S (by omega)
    obtain ⟨v, hvS, hvA⟩ := hS A hA
    exact (Finset.disjoint_left.mp hdisj) hvS hvA

/-- Sivashankar's linear gap disproves the pinned asymptotic claim. -/
theorem disproof (hK : ErdosLovasz.KahnDegreeCorollary.{0}) :
    ¬ (type_of% @Erdos21.erdos_21.variants.three_n) := by
  classical
  rintro ⟨C, hC⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hC
  obtain ⟨N', hN'⟩ := ErdosLovasz.theorem3 hK (1 / 100) (by norm_num)
  let n := max N (max N' (25 * C + 1))
  have hn : 0 < n := by dsimp [n]; omega
  have hnN : N ≤ n := le_max_left _ _
  have hnN' : N' ≤ n := (le_max_left _ _).trans (le_max_right _ _)
  have hnC : 25 * C + 1 ≤ n := (le_max_right _ _).trans (le_max_right _ _)
  have hne : {m : ℕ | ∃ F : Finset (Finset ℕ),
      Erdos21.IsErdosLovaszFamily n F ∧ F.card = m}.Nonempty := by
    obtain ⟨F, hF⟩ := exists_family n hn
    exact ⟨F.card, F, hF, rfl⟩
  obtain ⟨F, hF, hFc⟩ := Nat.sInf_mem hne
  change F.card = Erdos21.f n at hFc
  have hlo := hN' n hnN' F hF.1 hF.2.1 (coverNum_eq hF)
  have hup := (hN n hnN).1
  rw [← hFc] at hup
  have hupr : (F.card : ℝ) ≤ 3 * (n : ℝ) + (C : ℝ) := by exact_mod_cast hup
  have hnCr : 25 * (C : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hnC
  have hsqrt : Real.sqrt (19 : ℝ) ≤ 22 / 5 := (Real.sqrt_le_iff).2 (by norm_num)
  have hconst : (3 : ℝ) + 1 / 25 ≤ ErdosLovasz.asymptoticConstant - 1 / 100 := by
    unfold ErdosLovasz.asymptoticConstant
    linarith
  have h := mul_le_mul_of_nonneg_right hconst (Nat.cast_nonneg (α := ℝ) n)
  linarith

end Erdos21Bridge

theorem OMA.disproof : ¬ (type_of% @Erdos21.erdos_21.variants.three_n) := by
  apply Erdos21Bridge.disproof
  exact ErdosLovasz.kahnDegreeCorollary_of_chromatic_index
    (Pseudorandom.chromatic_index_polynomial 4 (by decide) (1 / 2) (by norm_num) (by norm_num))
