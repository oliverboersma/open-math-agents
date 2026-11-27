import OMAStatements.S_oeis_a027424
import Mathlib

namespace A027424Proof

open Finset OMA.S_oeis_a027424

lemma mem_prods (n m : ℕ) :
    m ∈ prods n ↔ ∃ i j, 1 ≤ i ∧ i ≤ n ∧ 1 ≤ j ∧ j ≤ n ∧ i * j = m := by
  unfold prods
  simp only [Finset.mem_image, Finset.mem_product, Finset.mem_Icc, Prod.exists]
  constructor
  · rintro ⟨i, j, ⟨⟨h1, h2⟩, h3, h4⟩, h5⟩
    exact ⟨i, j, h1, h2, h3, h4, h5⟩
  · rintro ⟨i, j, h1, h2, h3, h4, h5⟩
    exact ⟨i, j, ⟨⟨h1, h2⟩, h3, h4⟩, h5⟩

lemma prods_subset (n : ℕ) : prods n ⊆ Icc 1 (n ^ 2) := by
  intro m hm
  obtain ⟨i, j, h1, h2, h3, h4, rfl⟩ := (mem_prods n m).mp hm
  rw [Finset.mem_Icc]
  constructor
  · exact Nat.mul_pos h1 h3
  · calc i * j ≤ n * n := Nat.mul_le_mul h2 h4
      _ = n ^ 2 := by ring

lemma term_nonneg (n m k : ℕ) :
    (0 : ℤ) ≤ (if k ∣ m then 1 else 0) * (if m ≤ n * k then 1 else 0) * (if k ≤ n then 1 else 0) := by
  split_ifs <;> norm_num

lemma sign_inner (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    Int.sign (inner n m) = if m ∈ prods n then 1 else 0 := by
  by_cases h : m ∈ prods n
  · rw [if_pos h]
    obtain ⟨i, j, h1, h2, h3, h4, h5⟩ := (mem_prods n m).mp h
    have hi : i ∈ Icc 1 (n ^ 2) := by
      rw [Finset.mem_Icc]
      refine ⟨h1, ?_⟩
      calc i ≤ n := h2
        _ = n * 1 := (Nat.mul_one n).symm
        _ ≤ n * n := Nat.mul_le_mul_left n hn
        _ = n ^ 2 := by ring
    have hterm : ((if i ∣ m then 1 else 0) * (if m ≤ n * i then 1 else 0)
        * (if i ≤ n then 1 else 0) : ℤ) = 1 := by
      have d1 : i ∣ m := ⟨j, h5.symm⟩
      have d2 : m ≤ n * i := by
        rw [← h5, Nat.mul_comm i j]
        exact Nat.mul_le_mul_right i h4
      rw [if_pos d1, if_pos d2, if_pos h2]
      norm_num
    have hsum : ((if i ∣ m then 1 else 0) * (if m ≤ n * i then 1 else 0)
        * (if i ≤ n then 1 else 0) : ℤ) ≤ inner n m := by
      unfold OMA.S_oeis_a027424.inner
      exact Finset.single_le_sum
        (f := fun k : ℕ => ((if k ∣ m then 1 else 0) * (if m ≤ n * k then 1 else 0)
          * (if k ≤ n then 1 else 0) : ℤ))
        (fun k _ => term_nonneg n m k) hi
    have hle : (1 : ℤ) ≤ inner n m := by
      rw [hterm] at hsum
      exact hsum
    exact Int.sign_eq_one_of_pos (by omega)
  · rw [if_neg h]
    have hz : inner n m = 0 := by
      unfold OMA.S_oeis_a027424.inner
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.mem_Icc] at hk
      by_cases c1 : k ∣ m
      · by_cases c2 : m ≤ n * k
        · by_cases c3 : k ≤ n
          · exfalso
            apply h
            obtain ⟨j, rfl⟩ := c1
            have hk0 : 0 < k := hk.1
            have hj1 : 1 ≤ j := by
              rcases Nat.eq_zero_or_pos j with h0 | h0
              · subst h0
                simp at hm
              · exact h0
            have hj2 : j ≤ n := by
              have c2' : j * k ≤ n * k := by
                rw [Nat.mul_comm j k]
                exact c2
              exact Nat.le_of_mul_le_mul_right c2' hk0
            exact (mem_prods n (k * j)).mpr ⟨k, j, hk.1, c3, hj1, hj2, rfl⟩
          · rw [if_neg c3]; ring
        · rw [if_neg c2]; ring
      · rw [if_neg c1]; ring
    rw [hz]
    rfl

end A027424Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a027424.main := by
  intro n hn
  have h1 : ∀ m ∈ Finset.Icc 1 (n ^ 2), Int.sign (OMA.S_oeis_a027424.inner n m)
      = if m ∈ OMA.S_oeis_a027424.prods n then 1 else 0 := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    exact A027424Proof.sign_inner n m hn hm.1
  rw [Finset.sum_congr rfl h1, Finset.sum_boole, Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.mpr (A027424Proof.prods_subset n)]
  rfl
