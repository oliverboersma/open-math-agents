import OMAReductions.R_Erdos20_erdos_20_R1
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Rainbow extraction for Erdős Problem 20
This proves reduction step H1 by counting pairs of colorings and rainbow members.
Formalization by @kenanwienberg with Codex.

The counting argument is the rainbow extraction used in OpenAI,
*An exponential bound for sunflowers* (November 24, 2026).
https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/Sunflower/ColorCount.lean
-/

open Finset
open scoped BigOperators

namespace OMA.Erdos20Rainbow

/-- A coloring on the union can be extended arbitrarily outside it. -/
private noncomputable def extend {α : Type} [DecidableEq α] (U : Finset α)
    {n : ℕ} (hn : 0 < n) (c : U → Fin n) (x : α) : Fin n :=
  if hx : x ∈ U then c ⟨x, hx⟩ else ⟨0, hn⟩

/-- A coloring that is bijective on A is specified by that bijection
and an arbitrary coloring on the complement of A in U. -/
private noncomputable def splitColor {α : Type} [DecidableEq α] {n : ℕ}
    (hn : 0 < n) {A U : Finset α} (hAU : A ⊆ U) :
    {c : U → Fin n // Function.Bijective (fun x : A => extend U hn c x)} ≃
      (A ≃ Fin n) × ((U \ A : Finset α) → Fin n) where
  toFun c :=
    (Equiv.ofBijective _ c.property,
      fun x => c.val ⟨x, (mem_sdiff.mp x.property).1⟩)
  invFun p := by
    let c (x : U) : Fin n :=
      if hx : x.val ∈ A then p.1 ⟨x, hx⟩
      else p.2 ⟨x, mem_sdiff.mpr ⟨x.property, hx⟩⟩
    refine ⟨c, ?_⟩
    convert p.1.bijective using 1
    funext x
    simp [extend, c, hAU x.property, x.property]
  left_inv c := by
    apply Subtype.ext
    funext x
    by_cases hx : x.val ∈ A
    · simp [hx, extend, x.property]
    · simp [hx]
  right_inv p := by
    apply Prod.ext
    · apply Equiv.ext
      intro x
      simp [extend, hAU x.property]
    · funext x
      simp [(mem_sdiff.mp x.property).2]

private theorem countColors {α : Type} [DecidableEq α] {n : ℕ}
    (hn : 0 < n) {A U : Finset α} (hAU : A ⊆ U) (hA : A.card = n) :
    (univ.filter fun c : U → Fin n =>
      Function.Bijective (fun x : A => extend U hn c x)).card * n ^ n =
      n.factorial * n ^ U.card := by
  classical
  have hcount := Fintype.card_congr (splitColor hn hAU)
  have hperm : Fintype.card (A ≃ Fin n) = n.factorial := by
    rw [Fintype.card_equiv (A.equivFinOfCardEq hA), Fintype.card_coe, hA]
  rw [Fintype.card_of_subtype
    (univ.filter fun c : U → Fin n => Function.Bijective (fun x : A => extend U hn c x))
    (fun _ => by simp only [mem_filter, mem_univ, true_and]),
    Fintype.card_prod, hperm, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_coe] at hcount
  rw [hcount, mul_assoc, ← pow_add, ← hA, card_sdiff_add_card_eq_card hAU, hA]

theorem rainbowSubfamily : OMA.R_Erdos20_erdos_20_R1.H1 := by
  classical
  intro α n hn F hF
  let U := F.biUnion id
  let Good (c : U → Fin n) (A : Finset α) :=
    Function.Bijective (fun x : A => extend U hn c x)
  let count (c : U → Fin n) := (F.filter (Good c)).card
  let _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨c, _, hmax⟩ :=
    (univ : Finset (U → Fin n)).exists_max_image count univ_nonempty
  refine ⟨extend U hn c, F.filter (Good c), filter_subset _ _, ?_, ?_⟩
  · exact fun A hA => (mem_filter.mp hA).2
  have hswap : ∑ A ∈ F, (univ.filter fun d => Good d A).card = ∑ d, count d := by
    simp only [count, card_filter]
    exact sum_comm
  have h :
      F.card * (n.factorial * n ^ U.card) ≤
        n ^ U.card * ((F.filter (Good c)).card * n ^ n) := by
    calc
      _ = ∑ _A ∈ F, n.factorial * n ^ U.card := by simp
      _ = ∑ A ∈ F, (univ.filter fun d => Good d A).card * n ^ n := by
        apply sum_congr rfl
        intro A hA
        exact (countColors hn (subset_biUnion_of_mem id hA) (hF A hA)).symm
      _ = (∑ d, count d) * n ^ n := by rw [← sum_mul, hswap]
      _ ≤ (∑ _d : U → Fin n, count c) * n ^ n :=
        Nat.mul_le_mul_right _ (sum_le_sum hmax)
      _ = _ := by
        simp [count, mul_assoc]
  exact Nat.le_of_mul_le_mul_left
    (by simpa only [mul_left_comm, mul_assoc, mul_comm] using h) (Nat.pow_pos hn)

end OMA.Erdos20Rainbow

theorem OMA.solution : OMA.R_Erdos20_erdos_20_R1.H1 := by
  exact OMA.Erdos20Rainbow.rainbowSubfamily
