import OMAReductions.R_Green3_green_3_R1_H2_R1
import Mathlib

-- Step Green3.green_3.R1.H2.R1.H1: hypothesis H1 of reduction Green3.green_3.R1.H2.R1
-- Credit: @ivillar

/-!
# Packing integer blocks above a product-free set of cells

`S` is a set of cells with indices in `[m, M)` on a grid of `N` cells, `M - 1 ∈ S`, and no triple
`i, j, l ∈ S` with `i*j < (l+1)*N` and `l*N < (i+1)*(j+1)`. On the integer line, the blocks
`[l*N, (l+1)*N)` and `[i*M, (i+1)*M)` for `l, i ∈ S` are pairwise disjoint (take `j = M - 1`) and
all lie in `[m*M, M*N)`, so `(N + M) * S.card ≤ M * (N - m)`.
-/

namespace Green3PackStep

open Finset

lemma blocks_disjoint (K a b : ℕ) (hab : a ≠ b) :
    Disjoint (Ico (a * K) ((a + 1) * K)) (Ico (b * K) ((b + 1) * K)) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [mem_Ico] at hx hx'
  have h1 : a < b + 1 := Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt hx.1 hx'.2)
  have h2 : b < a + 1 := Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt hx'.1 hx.2)
  omega

lemma card_blocks (K : ℕ) (S : Finset ℕ) :
    (S.biUnion fun a => Ico (a * K) ((a + 1) * K)).card = S.card * K := by
  rw [card_biUnion]
  · rw [sum_congr rfl (fun a _ => ?_), sum_const, smul_eq_mul]
    rw [Nat.card_Ico, Nat.add_mul, one_mul, Nat.add_sub_cancel_left]
  · intro a _ b _ hab
    exact blocks_disjoint K a b hab

theorem pack : ∀ (N m M : ℕ) (S : Finset ℕ), 0 < M → M ≤ N →
    M-1 ∈ S → (∀ i ∈ S, m ≤ i ∧ i < M) →
    (∀ i ∈ S, ∀ j ∈ S, ∀ l ∈ S, ¬(i*j < (l+1)*N ∧ l*N < (i+1)*(j+1))) →
    (N+M)*S.card ≤ M*(N-m) := by
  intro N m M S hM hMN hMS hb hfree
  have hj : M - 1 + 1 = M := Nat.sub_add_cancel hM
  have hBC : Disjoint (S.biUnion fun l => Ico (l * N) ((l + 1) * N))
      (S.biUnion fun i => Ico (i * M) ((i + 1) * M)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨l, hl, hxl⟩ := mem_biUnion.mp hx
    obtain ⟨i, hi, hxi⟩ := mem_biUnion.mp hx'
    rw [mem_Ico] at hxl hxi
    refine hfree i hi (M - 1) hMS l hl ⟨?_, ?_⟩
    · calc i * (M - 1) ≤ i * M := Nat.mul_le_mul_left i (Nat.sub_le M 1)
        _ ≤ x := hxi.1
        _ < (l + 1) * N := hxl.2
    · rw [hj]
      exact lt_of_le_of_lt hxl.1 hxi.2
  have hsub : (S.biUnion fun l => Ico (l * N) ((l + 1) * N)) ∪
      (S.biUnion fun i => Ico (i * M) ((i + 1) * M)) ⊆ Ico (m * M) (M * N) := by
    intro x hx
    rw [mem_Ico]
    rcases mem_union.mp hx with hx | hx
    · obtain ⟨l, hl, hxl⟩ := mem_biUnion.mp hx
      rw [mem_Ico] at hxl
      obtain ⟨hml, hlM⟩ := hb l hl
      constructor
      · calc m * M ≤ l * N := Nat.mul_le_mul hml hMN
          _ ≤ x := hxl.1
      · calc x < (l + 1) * N := hxl.2
          _ ≤ M * N := Nat.mul_le_mul_right N hlM
    · obtain ⟨i, hi, hxi⟩ := mem_biUnion.mp hx
      rw [mem_Ico] at hxi
      obtain ⟨hmi, hiM⟩ := hb i hi
      constructor
      · calc m * M ≤ i * M := Nat.mul_le_mul_right M hmi
          _ ≤ x := hxi.1
      · calc x < (i + 1) * M := hxi.2
          _ ≤ M * M := Nat.mul_le_mul_right M hiM
          _ ≤ M * N := Nat.mul_le_mul_left M hMN
  have hcard := card_le_card hsub
  rw [card_union_of_disjoint hBC, card_blocks, card_blocks, Nat.card_Ico] at hcard
  calc (N + M) * S.card = S.card * N + S.card * M := by ring
    _ ≤ M * N - m * M := hcard
    _ = M * (N - m) := by rw [Nat.mul_sub, Nat.mul_comm m M]

end Green3PackStep

theorem OMA.solution : OMA.R_Green3_green_3_R1_H2_R1.H1 :=
  Green3PackStep.pack
