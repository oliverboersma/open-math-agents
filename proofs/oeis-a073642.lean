import OMAStatements.S_oeis_a073642
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Proof sketch: write S(n) for the sum of the bit indices, s(n) for their number,
-- W(n) for the sum of v2(j) and V(n) for the sum of v2(j)^2 over 1 <= j <= n.
-- Splitting j into odd and even values gives W(2m) = W(m) + m and
-- V(2m) = V(m) + 2W(m) + m, while the odd value 2m+1 adds nothing. Binary recursion
-- gives S(2m) = S(2m+1) = S(m) + s(m), s(2m) = s(m), s(2m+1) = s(m) + 1. Strong induction
-- on n then yields W(n) + s(n) = n and 2S(n) + V(n) + 3s(n) = 3n, which is the claim.

namespace OMA.A073642Proof

def W (n : ℕ) : ℕ := ∑ j ∈ Finset.range n, padicValNat 2 (j + 1)

def V (n : ℕ) : ℕ := ∑ j ∈ Finset.range n, (padicValNat 2 (j + 1)) ^ 2

theorem v_odd (m : ℕ) : padicValNat 2 (2 * m + 1) = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  omega

theorem v_even (m : ℕ) : padicValNat 2 (2 * (m + 1)) = padicValNat 2 (m + 1) + 1 := by
  rw [padicValNat.mul (by norm_num) (by omega)]
  simp [add_comm]

theorem W_double (m : ℕ) : W (2 * m) = W m + m := by
  induction m with
  | zero => simp [W]
  | succ m ih =>
    have e : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
    unfold W at *
    rw [e, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    have h1 : padicValNat 2 (2 * m + 1) = 0 := v_odd m
    have h2 : padicValNat 2 (2 * m + 1 + 1) = padicValNat 2 (m + 1) + 1 := by
      rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring]; exact v_even m
    rw [h1, h2]
    ring

theorem V_double (m : ℕ) : V (2 * m) = V m + 2 * W m + m := by
  induction m with
  | zero => simp [V, W]
  | succ m ih =>
    have e : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
    unfold V W at *
    rw [e, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ,
      Finset.sum_range_succ]
    have h1 : padicValNat 2 (2 * m + 1) = 0 := v_odd m
    have h2 : padicValNat 2 (2 * m + 1 + 1) = padicValNat 2 (m + 1) + 1 := by
      rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring]; exact v_even m
    rw [h1, h2]
    ring

theorem W_odd (m : ℕ) : W (2 * m + 1) = W (2 * m) := by
  unfold W
  rw [Finset.sum_range_succ, v_odd]
  simp

theorem V_odd (m : ℕ) : V (2 * m + 1) = V (2 * m) := by
  unfold V
  rw [Finset.sum_range_succ, v_odd]
  simp

theorem sum_map_succ (L : List ℕ) : (L.map (· + 1)).sum = L.sum + L.length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    ring

theorem key : ∀ n : ℕ, W n + n.bitIndices.length = n ∧
    2 * n.bitIndices.sum + V n + 3 * n.bitIndices.length = 3 * n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos m with h0 | hpos
      · subst h0; simp [W, V]
      · obtain ⟨h1, h2⟩ := ih m (by omega)
        rw [Nat.bitIndices_two_mul, List.length_map, sum_map_succ, W_double, V_double]
        constructor <;> omega
    · obtain ⟨h1, h2⟩ := ih m (by omega)
      rw [Nat.bitIndices_two_mul_add_one, List.length_cons, List.length_map,
        List.sum_cons, sum_map_succ, W_odd, V_odd, W_double, V_double]
      constructor <;> omega

end OMA.A073642Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a073642.main := by
  intro n _
  obtain ⟨h1, h2⟩ := OMA.A073642Proof.key n
  unfold OMA.A073642Proof.V at h2
  omega
