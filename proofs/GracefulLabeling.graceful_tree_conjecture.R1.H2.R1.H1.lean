import OMAReductions.R_GracefulLabeling_graceful_tree_conjecture_R1_H2_R1
import Mathlib

/-! Step GracefulLabeling.graceful_tree_conjecture.R1.H2.R1.H1: hypothesis H1 of reduction GracefulLabeling.graceful_tree_conjecture.R1.H2.R1.
Credit: @ivillar (original proof). A fold set must contain t (its label q would otherwise stay q)
and is closed under both propagation rules (edge lengths and injectivity), so it contains the
component of t, where the reflected label q + h - f x < q forces h < f x. Conversely the
component of t itself is a valid fold set. -/

namespace OMAGraceH1

open SimpleGraph
open scoped Classical

theorem main_H1 : OMA.R_GracefulLabeling_graceful_tree_conjecture_R1_H2_R1.H1 := by
  intro V T f q h t hinj hle ht hhq
  constructor
  · rintro ⟨s, hginj, hglt, hgd⟩
    have hts : t ∈ s := by
      by_contra hn
      have := hglt t
      simp only [if_neg hn, ht] at this
      omega
    have closed : ∀ a b, a ∈ s →
        ((T.Adj a b ∧ 2 * f a ≠ q + h ∧ 2 * f b ≠ q + h) ∨ f a + f b = q + h) → b ∈ s := by
      intro a b ha hab
      by_contra hb
      have hla := hle a
      have hlb := hle b
      rcases hab with ⟨hadj, h1, h2⟩ | hsum
      · have := hgd a b hadj
        simp only [if_pos ha, if_neg hb] at this
        unfold Nat.dist at this
        omega
      · have := @hginj a b (by simp only [if_pos ha, if_neg hb]; omega)
        exact hb (this ▸ ha)
    intro x hx
    have hxs : x ∈ s := by
      induction hx with
      | refl => exact hts
      | tail _ hbc ih => exact closed _ _ ih hbc
    have := hglt x
    simp only [if_pos hxs] at this
    have := hle x
    omega
  · intro hreach
    set C : Set V := {x | Relation.ReflTransGen (fun a b =>
      (T.Adj a b ∧ 2 * f a ≠ q + h ∧ 2 * f b ≠ q + h) ∨ f a + f b = q + h) t x} with hC
    have hmem : ∀ x, x ∈ C ↔ Relation.ReflTransGen (fun a b =>
        (T.Adj a b ∧ 2 * f a ≠ q + h ∧ 2 * f b ≠ q + h) ∨ f a + f b = q + h) t x :=
      fun x => Iff.rfl
    have step : ∀ a b, a ∈ C →
        ((T.Adj a b ∧ 2 * f a ≠ q + h ∧ 2 * f b ≠ q + h) ∨ f a + f b = q + h) → b ∈ C :=
      fun a b ha hab => (hmem b).mpr (Relation.ReflTransGen.tail ((hmem a).mp ha) hab)
    have hbig : ∀ x, x ∈ C → h < f x := fun x hx => hreach x ((hmem x).mp hx)
    have htC : t ∈ C := (hmem t).mpr Relation.ReflTransGen.refl
    refine ⟨C, ?_, ?_, ?_⟩
    · intro x y hxy
      have hlx := hle x
      have hly := hle y
      by_cases hx : x ∈ C <;> by_cases hy : y ∈ C
      · simp only [if_pos hx, if_pos hy] at hxy
        exact hinj (by omega)
      · simp only [if_pos hx, if_neg hy] at hxy
        exact absurd (step x y hx (Or.inr (by omega))) hy
      · simp only [if_neg hx, if_pos hy] at hxy
        exact absurd (step y x hy (Or.inr (by omega))) hx
      · simp only [if_neg hx, if_neg hy] at hxy
        exact hinj hxy
    · intro x
      have hlx := hle x
      by_cases hx : x ∈ C
      · simp only [if_pos hx]
        have := hbig x hx
        omega
      · simp only [if_neg hx]
        rcases Nat.lt_or_ge (f x) q with hlt | hge
        · exact hlt
        · have hfx : f x = f t := by omega
          exact absurd (hinj hfx ▸ htC) hx
    · intro a b hadj
      have hla := hle a
      have hlb := hle b
      by_cases ha : a ∈ C <;> by_cases hb : b ∈ C
      · simp only [if_pos ha, if_pos hb]
        unfold Nat.dist
        omega
      · simp only [if_pos ha, if_neg hb]
        have hn : ¬ ((T.Adj a b ∧ 2 * f a ≠ q + h ∧ 2 * f b ≠ q + h) ∨ f a + f b = q + h) :=
          fun hab => hb (step a b ha hab)
        have : 2 * f a = q + h ∨ 2 * f b = q + h := by
          by_cases h1 : 2 * f a = q + h
          · exact Or.inl h1
          by_cases h2 : 2 * f b = q + h
          · exact Or.inr h2
          exact absurd (Or.inl ⟨hadj, h1, h2⟩) hn
        unfold Nat.dist
        omega
      · simp only [if_neg ha, if_pos hb]
        have hn : ¬ ((T.Adj b a ∧ 2 * f b ≠ q + h ∧ 2 * f a ≠ q + h) ∨ f b + f a = q + h) :=
          fun hab => ha (step b a hb hab)
        have : 2 * f a = q + h ∨ 2 * f b = q + h := by
          by_cases h1 : 2 * f a = q + h
          · exact Or.inl h1
          by_cases h2 : 2 * f b = q + h
          · exact Or.inr h2
          exact absurd (Or.inl ⟨hadj.symm, h2, h1⟩) hn
        unfold Nat.dist
        omega
      · simp only [if_neg ha, if_neg hb]

end OMAGraceH1

theorem OMA.solution : OMA.R_GracefulLabeling_graceful_tree_conjecture_R1_H2_R1.H1 :=
  OMAGraceH1.main_H1
