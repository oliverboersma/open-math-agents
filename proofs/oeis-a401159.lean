import OMAStatements.S_oeis_a401159
import Mathlib

-- Problem: A401159: Triangle T(n,m) read by rows: the number of binary n X m matrices with at most two 1's in each row or column.
-- Upstream: formal-conjectures statements/oeis-a401159.lean:0 (declaration OMA.S_oeis_a401159.main)
-- Credit: @caa1982 (the owner of the agent is credited as the solver)

namespace A401159Aux

open Finset

def P (n : ℕ) : Finset (Finset (Fin n)) := univ.filter (fun s => s.card ≤ 2)

def toCols (n m : ℕ) : (Fin n → Fin m → Bool) ≃ (Fin m → Finset (Fin n)) where
  toFun A j := univ.filter (fun i => A i j = true)
  invFun c i j := decide (i ∈ c j)
  left_inv A := by funext i j; simp
  right_inv c := by funext j; ext i; simp

abbrev Good (n m : ℕ) (c : Fin m → Finset (Fin n)) : Prop :=
  ∀ i, (univ.filter (fun j => i ∈ c j)).card ≤ 2

theorem T_eq (n m : ℕ) : OMA.S_oeis_a401159.T n m =
    ((Fintype.piFinset (fun _ : Fin m => P n)).filter (fun c => Good n m c)).card := by
  classical
  unfold OMA.S_oeis_a401159.T
  rw [Fintype.card_congr ((toCols n m).subtypeEquiv
    (p := fun A => OMA.S_oeis_a401159.Admissible A)
    (q := fun c => (∀ j, (c j).card ≤ 2) ∧ Good n m c) ?_)]
  · rw [Fintype.card_subtype]
    apply congrArg Finset.card
    ext c
    simp [P, Fintype.mem_piFinset]
  · intro A
    simp [OMA.S_oeis_a401159.Admissible, toCols, Good]

theorem card_P (n : ℕ) : (P n).card = 1 + n + n.choose 2 := by
  have : P n = (range 3).biUnion (fun k => powersetCard k (univ : Finset (Fin n))) := by
    ext s; simp [P, mem_powersetCard]; omega
  rw [this, card_biUnion]
  · simp [sum_range_succ, card_powersetCard]
  · intro a _ b _ hab
    exact pairwise_disjoint_powersetCard _ hab

theorem T2 (n : ℕ) : OMA.S_oeis_a401159.T n 2 = (1 + n + n.choose 2)^2 := by
  rw [T_eq, filter_true_of_mem, Fintype.card_piFinset]
  · simp [card_P]
  · intro c _ i
    calc _ ≤ Fintype.card (Fin 2) := card_le_univ _
      _ = 2 := by simp

abbrev I {n : ℕ} (t : Fin 3 → Finset (Fin n)) : Finset (Fin n) := univ.filter (fun i => ∀ j, i ∈ t j)

def X (n : ℕ) : Finset (Fin 3 → Finset (Fin n)) := Fintype.piFinset (fun _ : Fin 3 => P n)

theorem good3 (n : ℕ) (t : Fin 3 → Finset (Fin n)) : Good n 3 t ↔ I t = ∅ := by
  unfold Good I
  rw [Finset.filter_eq_empty_iff]
  apply forall_congr'; intro i
  simp only [mem_univ, true_implies]
  rw [card_filter, Fin.sum_univ_three]
  by_cases h0 : i ∈ t 0 <;> by_cases h1 : i ∈ t 1 <;> by_cases h2 : i ∈ t 2 <;>
    simp [Fin.forall_fin_succ, h0, h1, h2]

theorem L1 (n : ℕ) (x : Fin n) : ((P n).filter (fun s => x ∈ s)).card = n := by
  have : (P n).filter (fun s => x ∈ s) = univ.image (fun y => ({x, y} : Finset (Fin n))) := by
    ext s
    simp only [P, mem_filter, mem_univ, true_and, mem_image]
    constructor
    · rintro ⟨hs, hx⟩
      have h0 : s.card ≠ 0 := by
        intro h; rw [card_eq_zero] at h; simp [h] at hx
      have : s.card = 1 ∨ s.card = 2 := by omega
      rcases this with h | h
      · obtain ⟨a, rfl⟩ := card_eq_one.1 h
        simp at hx; subst hx; exact ⟨x, by simp⟩
      · obtain ⟨a, b, hab, rfl⟩ := card_eq_two.1 h
        simp at hx
        rcases hx with rfl | rfl
        · exact ⟨b, rfl⟩
        · exact ⟨a, pair_comm _ _⟩
    · rintro ⟨y, rfl⟩
      refine ⟨?_, by simp⟩
      calc _ ≤ ({y} : Finset (Fin n)).card + 1 := card_insert_le _ _
        _ = 2 := by simp
  rw [this, card_image_of_injective]
  · simp
  · intro y z h
    simp only at h
    have hy : y ∈ ({x, z} : Finset (Fin n)) := h ▸ (by simp)
    have hz : z ∈ ({x, y} : Finset (Fin n)) := h.symm ▸ (by simp)
    simp at hy hz
    rcases hy with rfl | rfl
    · rcases hz with rfl | rfl <;> rfl
    · rfl

theorem L2 (n : ℕ) (p s : Finset (Fin n)) (hp : p.card = 2) : (s ∈ P n ∧ p ⊆ s) ↔ s = p := by
  simp only [P, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hs, hps⟩
    exact (eq_of_subset_of_card_le hps (by omega)).symm
  · rintro rfl; exact ⟨by omega, subset_refl _⟩

theorem subset_I {n : ℕ} (p : Finset (Fin n)) (t : Fin 3 → Finset (Fin n)) :
    p ⊆ I t ↔ ∀ j, p ⊆ t j := by
  simp only [I, subset_iff, mem_filter, mem_univ, true_and]
  constructor
  · intro h j a ha; exact h ha j
  · intro h a ha j; exact h j ha

theorem sumI (n : ℕ) : ∑ t ∈ X n, (I t).card = n * n ^ 3 := by
  calc ∑ t ∈ X n, (I t).card = ∑ t ∈ X n, ∑ x : Fin n, if (∀ j, x ∈ t j) then 1 else 0 := by
        apply sum_congr rfl; intro t _; rw [I, card_filter]
    _ = ∑ x : Fin n, ∑ t ∈ X n, if (∀ j, x ∈ t j) then 1 else 0 := sum_comm
    _ = ∑ x : Fin n, n ^ 3 := by
        apply sum_congr rfl; intro x _
        rw [← card_filter]
        have : (X n).filter (fun t => ∀ j, x ∈ t j) =
            Fintype.piFinset (fun _ => (P n).filter (fun s => x ∈ s)) := by
          ext t; simp [X, Fintype.mem_piFinset, forall_and]
        rw [this, Fintype.card_piFinset, L1]; simp
    _ = n * n ^ 3 := by simp

theorem sumC (n : ℕ) : ∑ t ∈ X n, (I t).card.choose 2 = n.choose 2 := by
  calc ∑ t ∈ X n, (I t).card.choose 2 = ∑ t ∈ X n,
        ∑ p ∈ powersetCard 2 (univ : Finset (Fin n)), if p ⊆ I t then 1 else 0 := by
        apply sum_congr rfl; intro t _
        rw [← card_powersetCard, ← card_filter]; congr 1; ext p
        simp [mem_powersetCard]; tauto
    _ = ∑ p ∈ powersetCard 2 (univ : Finset (Fin n)), ∑ t ∈ X n, if p ⊆ I t then 1 else 0 :=
        sum_comm
    _ = ∑ p ∈ powersetCard 2 (univ : Finset (Fin n)), 1 := by
        apply sum_congr rfl; intro p hp
        rw [← card_filter]
        have hp2 : p.card = 2 := (mem_powersetCard.1 hp).2
        have : (X n).filter (fun t => p ⊆ I t) = Fintype.piFinset (fun _ => {p}) := by
          ext t
          simp only [X, mem_filter, Fintype.mem_piFinset, mem_singleton, subset_I]
          rw [← forall_and]
          apply forall_congr'; intro j
          exact L2 n p (t j) hp2
        rw [this, Fintype.card_piFinset]; simp
    _ = n.choose 2 := by simp [card_powersetCard]

theorem key3 (n : ℕ) : OMA.S_oeis_a401159.T n 3 + n * n ^ 3 = (1 + n + n.choose 2) ^ 3 + n.choose 2 := by
  have hX : (X n).card = (1 + n + n.choose 2) ^ 3 := by
    rw [X, Fintype.card_piFinset, card_P]; simp
  rw [T_eq, card_filter]
  suffices h : (∑ t ∈ X n, if Good n 3 t then 1 else 0) + ∑ t ∈ X n, (I t).card =
      (X n).card + ∑ t ∈ X n, (I t).card.choose 2 by
    rw [sumI, sumC, hX] at h; exact h
  rw [card_eq_sum_ones, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro t ht
  have hle : (I t).card ≤ 2 := by
    have h0 : t 0 ∈ P n := Fintype.mem_piFinset.1 ht 0
    have hs : I t ⊆ t 0 := by
      intro a ha; exact (mem_filter.1 ha).2 0
    exact (card_le_card hs).trans (mem_filter.1 h0).2
  have hg : (Good n 3 t) ↔ (I t).card = 0 := by rw [good3, card_eq_zero]
  rw [if_congr hg rfl rfl]
  generalize (I t).card = k at hle ⊢
  interval_cases k <;> simp

theorem T3 (n : ℕ) : 8 * OMA.S_oeis_a401159.T n 3 =
    8 + 8 * n + 22 * n ^ 2 + 13 * n ^ 3 + n ^ 4 + 3 * n ^ 5 + n ^ 6 := by
  have h1 := key3 n
  have h2 : 2 * n.choose 2 = n * (n - 1) := by
    rw [Nat.choose_two_right]; exact Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp at h1; omega
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h2
  set c := (k + 1).choose 2
  set G := OMA.S_oeis_a401159.T (k + 1) 3
  have h1' : (G : ℤ) + (k + 1) * (k + 1) ^ 3 = (1 + (k + 1) + c) ^ 3 + c := by exact_mod_cast h1
  have h2' : (2 * c : ℤ) = (k + 1) * k := by exact_mod_cast h2
  have : (8 * G : ℤ) = 8 + 8 * (k + 1) + 22 * (k + 1) ^ 2 + 13 * (k + 1) ^ 3 + (k + 1) ^ 4 +
      3 * (k + 1) ^ 5 + (k + 1) ^ 6 := by
    linear_combination (exp := 1) 8 * h1' + ((2 + 2 * (k+1) + 2 * c) ^ 2 + (2 + 2 * (k+1) + 2 * c) * (2 + (k+1) + (k+1)^2) + (2 + (k+1) + (k+1)^2) ^ 2 + 4) * h2'
  exact_mod_cast this

end A401159Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a401159.main := by
  exact ⟨fun n _ => A401159Aux.T2 n, fun n _ => A401159Aux.T3 n⟩
