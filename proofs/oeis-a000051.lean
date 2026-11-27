import OMAStatements.S_oeis_a000051
import Mathlib

-- Problem: A000051: a(n) = 2^n + 1.
-- Upstream: formal-conjectures statements/oeis-a000051.lean:0 (declaration OMA.S_oeis_a000051.main)
-- Credit: @caa1982 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.A000051Aux

open Equiv Finset

def H (i j : ℕ) : ℤ := if i ≤ j + 1 then 1 else 0

def w {m : ℕ} (σ : Perm (Fin m)) : ℤ := ∏ i, H i.val (σ i).val

lemma H_zero (j : ℕ) : H 0 j = 1 := by simp [H]

lemma H_succ (i j : ℕ) : H (i+1) (j+1) = H i j := by simp [H]

lemma w_decomp_zero {m : ℕ} (e : Perm (Fin (m+1))) :
    w (Perm.decomposeFin.symm (0, e)) = w e := by
  unfold w
  rw [Fin.prod_univ_succ]
  simp [Perm.decomposeFin_symm_apply_zero, Perm.decomposeFin_symm_apply_succ, H_zero, H_succ]

lemma w_decomp_succ {m : ℕ} (q : Fin (m+1)) (e : Perm (Fin (m+1))) :
    w (Perm.decomposeFin.symm (q.succ, e)) = if e 0 = q then w e else 0 := by
  unfold w
  rw [Fin.prod_univ_succ]
  simp only [Perm.decomposeFin_symm_apply_zero, Perm.decomposeFin_symm_apply_succ]
  rw [Fin.val_zero, H_zero, one_mul]
  have key : ∀ i : Fin (m+1), H (i.succ).val (swap 0 q.succ (e i).succ).val
      = if e i = q then (if i = 0 then 1 else 0) else H i.val (e i).val := by
    intro i
    rw [swap_apply_def]
    by_cases h : e i = q
    · simp [h, Fin.succ_ne_zero, H]
    · simp [h, Fin.succ_ne_zero, Fin.succ_inj, H_succ]
  simp only [key]
  split_ifs with h
  · apply Finset.prod_congr rfl
    intro i _
    by_cases hi : e i = q
    · have : i = 0 := e.injective (hi.trans h.symm)
      subst this
      simp [H_zero]
    · simp [hi]
  · apply Finset.prod_eq_zero (i := e.symm q) (Finset.mem_univ _)
    have : e.symm q ≠ 0 := by
      intro h0
      apply h
      rw [← h0]; simp
    simp [this]

lemma W_succ (m : ℕ) : ∑ σ : Perm (Fin (m+2)), w σ = 2 * ∑ σ : Perm (Fin (m+1)), w σ := by
  rw [← (Perm.decomposeFin).symm.sum_comp, Fintype.sum_prod_type, Fin.sum_univ_succ]
  simp only [w_decomp_zero, w_decomp_succ]
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq]
  ring

lemma W_eq (m : ℕ) : ∑ σ : Perm (Fin (m+1)), w σ = 2 ^ m := by
  induction m with
  | zero => simp [w, H]
  | succ m ih => rw [W_succ, ih]; ring

lemma V_succ (m : ℕ) : ∑ σ : Perm (Fin (m+2)), (if σ 0 = Fin.last (m+1) then w σ else 0)
    = ∑ σ : Perm (Fin (m+1)), (if σ 0 = Fin.last m then w σ else 0) := by
  rw [← (Perm.decomposeFin).symm.sum_comp, Fintype.sum_prod_type, Fin.sum_univ_succ]
  simp only [Perm.decomposeFin_symm_apply_zero, w_decomp_succ, ← Fin.succ_last, Fin.succ_inj]
  have h0 : (0 : Fin (m+2)) ≠ (Fin.last m).succ := (Fin.succ_ne_zero _).symm
  simp only [h0, if_false, Finset.sum_const_zero, zero_add]
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq']

lemma V_eq (m : ℕ) : ∑ σ : Perm (Fin (m+1)), (if σ 0 = Fin.last m then w σ else 0) = 1 := by
  induction m with
  | zero => simp [w, H, Fin.fin_one_eq_zero]
  | succ m ih => rw [V_succ, ih]

lemma entry (n j k : ℕ) (hj : j ≤ n) (hk : k ≤ n) :
    -⌊(((j:ℚ)+1) - ((k:ℚ)+1) - 2)/((n:ℚ)+1)⌋ = H j k * (if j = 0 ∧ k = n then 2 else 1) := by
  have hn : (0:ℚ) < (n:ℚ)+1 := by positivity
  have hj' : (j:ℚ) ≤ n := by exact_mod_cast hj
  have hk' : (k:ℚ) ≤ n := by exact_mod_cast hk
  unfold H
  by_cases h1 : j ≤ k + 1
  · by_cases h2 : j = 0 ∧ k = n
    · obtain ⟨rfl, rfl⟩ := h2
      have : ⌊(((0:ℕ):ℚ)+1 - (((k:ℕ):ℚ)+1) - 2)/((k:ℚ)+1)⌋ = -2 := by
        rw [Int.floor_eq_iff]
        constructor
        · rw [le_div_iff₀ hn]; push_cast; linarith
        · rw [div_lt_iff₀ hn]; push_cast; linarith
      rw [this]; simp
    · rw [if_pos h1, if_neg h2]
      have h3 : (k:ℚ) + 1 ≤ j + n := by exact_mod_cast (by omega : k + 1 ≤ j + n)
      have h4 : (j:ℚ) ≤ k + 1 := by exact_mod_cast h1
      have : ⌊(((j:ℚ)+1) - ((k:ℚ)+1) - 2)/((n:ℚ)+1)⌋ = -1 := by
        rw [Int.floor_eq_iff]
        constructor
        · rw [le_div_iff₀ hn]; push_cast; linarith
        · rw [div_lt_iff₀ hn]; push_cast; linarith
      rw [this]; simp
  · rw [if_neg h1]
    have h4 : (k:ℚ) + 2 ≤ j := by exact_mod_cast (by omega : k + 2 ≤ j)
    have : ⌊(((j:ℚ)+1) - ((k:ℚ)+1) - 2)/((n:ℚ)+1)⌋ = 0 := by
      rw [Int.floor_eq_iff]
      constructor
      · push_cast; apply div_nonneg <;> linarith
      · rw [div_lt_iff₀ hn]; push_cast; linarith
    rw [this]; simp

end OMA.A000051Aux

open OMA.A000051Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a000051.main := by
  intro n M
  rw [← Matrix.permanent_transpose]
  have hprod : ∀ σ : Equiv.Perm (Fin (n+1)), ∏ i, M i (σ i)
      = w σ + (if σ 0 = Fin.last n then w σ else 0) := by
    intro σ
    have hM : ∀ j k : Fin (n+1), M j k = H j.val k.val * (if j = 0 ∧ k = Fin.last n then 2 else 1) := by
      intro j k
      have := entry n j.val k.val (Nat.lt_succ_iff.mp j.isLt) (Nat.lt_succ_iff.mp k.isLt)
      have e1 : (j = 0 ∧ k = Fin.last n) ↔ (j.val = 0 ∧ k.val = n) := by
        rw [Fin.ext_iff, Fin.ext_iff, Fin.val_zero, Fin.val_last]
      simp only [e1]
      exact this
    simp only [hM]
    rw [Finset.prod_mul_distrib, Fin.prod_univ_succ (fun i => if i = 0 ∧ σ i = Fin.last n then (2:ℤ) else 1)]
    simp only [Fin.succ_ne_zero, false_and, if_false, Finset.prod_const_one, mul_one, true_and]
    unfold w
    split_ifs <;> ring
  unfold Matrix.permanent
  simp only [Matrix.transpose_apply]
  rw [Finset.sum_congr rfl (fun σ _ => hprod σ), Finset.sum_add_distrib, W_eq, V_eq]
