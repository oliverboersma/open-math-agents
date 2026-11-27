import OMAStatements.S_oeis_a325695
import Mathlib

-- Problem: A325695: Number of length-3 strict integer partitions of n such that the largest
-- part is not the sum of the other two.
-- Upstream: statements/oeis-a325695.lean (declaration OMA.S_oeis_a325695.main)
-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Proof: for fixed u the admissible v are those with 3u+2v+5 < n and n /= 4u+2v+6, so the
-- inner count is (n-(3u+5)+1)/2, minus one exactly when n is even and 4u+6 <= n.
-- Shifting u by 4 in the first part and by 3 in the correction gives the explicit step
-- term (n+12) + 3*((n+1)%2) = term n + (n+8)/2 + (n+5)/2 + (n+2)/2 + (n-1)/2 for n >= 1.
-- The order-9 recurrence then follows by induction in steps of 12 (omega for the step,
-- kernel evaluation for k < 12), and the generating function identity is the recurrence
-- read coefficientwise, with the coefficients of degree at most 9 checked directly.

namespace OMA.P_a325695
open OMA.S_oeis_a325695 PowerSeries

def A' (n u : ℕ) : ℕ := (n - (3*u+5) + 1)/2
def B' (n u : ℕ) : ℕ := if n % 2 = 0 ∧ 4*u+6 ≤ n then 1 else 0

lemma allowed_iff (n u v : ℕ) :
    allowed n u v = true ↔ 3*u+2*v+5 < n ∧ n ≠ 4*u+2*v+6 := by
  simp only [allowed, decide_eq_true_eq]
  omega

lemma card_eq (n u : ℕ) :
    ((Finset.range (n+1)).filter (fun v => allowed n u v)).card + B' n u = A' n u := by
  unfold A' B'
  split_ifs with h
  · have hs : (Finset.range (n+1)).filter (fun v => allowed n u v) =
        (Finset.range ((n - (3*u+5) + 1)/2)).erase ((n - (4*u+6))/2) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase, allowed_iff]
      omega
    have hm : (n - (4*u+6))/2 ∈ Finset.range ((n - (3*u+5) + 1)/2) := by
      simp only [Finset.mem_range]; omega
    rw [hs, Finset.card_erase_of_mem hm, Finset.card_range]
    omega
  · have hs : (Finset.range (n+1)).filter (fun v => allowed n u v) =
        Finset.range ((n - (3*u+5) + 1)/2) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_range, allowed_iff]
      omega
    rw [hs, Finset.card_range, add_zero]

lemma term_eq (n : ℕ) :
    term n + ∑ u ∈ Finset.range (n+1), B' n u = ∑ u ∈ Finset.range (n+1), A' n u := by
  simp only [term, ← Finset.sum_add_distrib, card_eq]

lemma sumA_ext (n j : ℕ) :
    ∑ u ∈ Finset.range (n+1+j), A' n u = ∑ u ∈ Finset.range (n+1), A' n u := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show n+1+(j+1) = (n+1+j)+1 by omega, Finset.sum_range_succ, ih]
    have : A' n (n+1+j) = 0 := by unfold A'; omega
    rw [this, add_zero]

lemma sumB_ext (n j : ℕ) :
    ∑ u ∈ Finset.range (n+1+j), B' n u = ∑ u ∈ Finset.range (n+1), B' n u := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show n+1+(j+1) = (n+1+j)+1 by omega, Finset.sum_range_succ, ih]
    have : B' n (n+1+j) = 0 := by unfold B'; split_ifs <;> omega
    rw [this, add_zero]

lemma sumA_shift (n : ℕ) :
    ∑ u ∈ Finset.range (n+12+1), A' (n+12) u = ∑ u ∈ Finset.range (n+1), A' n u +
      (A' (n+12) 0 + A' (n+12) 1 + A' (n+12) 2 + A' (n+12) 3) := by
  rw [show n+12+1 = 4 + (n+1+8) by omega, Finset.sum_range_add]
  have : ∀ u, A' (n+12) (4+u) = A' n u := by intro u; unfold A'; omega
  simp only [this]
  rw [sumA_ext]
  have hs : ∑ u ∈ Finset.range 4, A' (n+12) u =
      A' (n+12) 0 + A' (n+12) 1 + A' (n+12) 2 + A' (n+12) 3 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [hs]
  ring

lemma sumB_shift (n : ℕ) :
    ∑ u ∈ Finset.range (n+12+1), B' (n+12) u = ∑ u ∈ Finset.range (n+1), B' n u +
      (B' (n+12) 0 + B' (n+12) 1 + B' (n+12) 2) := by
  rw [show n+12+1 = 3 + (n+1+9) by omega, Finset.sum_range_add]
  have : ∀ u, B' (n+12) (3+u) = B' n u := by
    intro u; unfold B'
    have : (4*(3+u)+6 ≤ n+12) ↔ 4*u+6 ≤ n := by omega
    have h2 : (n+12) % 2 = n % 2 := by omega
    simp only [this, h2]
  simp only [this]
  rw [sumB_ext]
  have hs : ∑ u ∈ Finset.range 3, B' (n+12) u = B' (n+12) 0 + B' (n+12) 1 + B' (n+12) 2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [hs]
  ring

lemma key (n : ℕ) (hn : 1 ≤ n) :
    term (n+12) + 3*((n+1)%2) = term n + ((n+8)/2 + (n+5)/2 + (n+2)/2 + (n-2+1)/2) := by
  have h1 := term_eq (n+12)
  have h2 := term_eq n
  rw [sumA_shift, sumB_shift] at h1
  have hB : B' (n+12) 0 + B' (n+12) 1 + B' (n+12) 2 = 3*((n+1)%2) := by
    unfold B'; split_ifs <;> omega
  have hA : A' (n+12) 0 + A' (n+12) 1 + A' (n+12) 2 + A' (n+12) 3 =
      (n+8)/2 + (n+5)/2 + (n+2)/2 + (n-2+1)/2 := by
    unfold A'; omega
  omega

set_option maxRecDepth 100000 in
lemma base (k : ℕ) (hk : k < 12) :
    term (k+10)+term (k+5)+term (k+4)+term (k+3) =
      term (k+8)+term (k+7)+term (k+6)+term (k+1) := by
  interval_cases k <;> decide +kernel

lemma recur : ∀ k : ℕ, term (k+10)+term (k+5)+term (k+4)+term (k+3) =
      term (k+8)+term (k+7)+term (k+6)+term (k+1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k < 12
    · exact base k hk
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 12 := ⟨k - 12, by omega⟩
      have IH := ih j (by omega)
      have e1 := key (j+10) (by omega)
      have e2 := key (j+5) (by omega)
      have e3 := key (j+4) (by omega)
      have e4 := key (j+3) (by omega)
      have e5 := key (j+8) (by omega)
      have e6 := key (j+7) (by omega)
      have e7 := key (j+6) (by omega)
      have e8 := key (j+1) (by omega)
      rw [show j+12+10 = j+10+12 by omega, show j+12+5 = j+5+12 by omega,
        show j+12+4 = j+4+12 by omega, show j+12+3 = j+3+12 by omega,
        show j+12+8 = j+8+12 by omega, show j+12+7 = j+7+12 by omega,
        show j+12+6 = j+6+12 by omega, show j+12+1 = j+1+12 by omega]
      omega

set_option maxRecDepth 100000 in
lemma small : term 0 = 0 ∧ term 1 = 0 ∧ term 2 = 0 ∧ term 3 = 0 ∧ term 4 = 0 ∧
    term 5 = 0 ∧ term 6 = 0 ∧ term 7 = 1 ∧ term 8 = 1 ∧ term 9 = 3 := by
  decide +kernel

lemma poly_eq : ((1-X)^3*(1+X)^2*(1+X^2)*(1+X+X^2) : PowerSeries ℚ) =
    1 - X^2 - X^3 - X^4 + X^5 + X^6 + X^7 - X^9 := by ring

lemma gf : ((1-X)^3*(1+X)^2*(1+X^2)*(1+X+X^2))*series =
    (X^7*(1+X+2*X^2) : PowerSeries ℚ) := by
  rw [poly_eq, show (X^7*(1+X+2*X^2) : PowerSeries ℚ) = X^7 + X^8 + X^9 + X^9 by ring]
  ext n
  simp only [sub_mul, add_mul, one_mul, map_sub, map_add, coeff_X_pow_mul', series, coeff_mk,
    coeff_X_pow]
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9⟩ := small
  by_cases hn : 10 ≤ n
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
    have h := recur k
    have h' : ((term (k+10) : ℚ) + term (k+5) + term (k+4) + term (k+3)) =
        term (k+8) + term (k+7) + term (k+6) + term (k+1) := by exact_mod_cast h
    simp only [show 2 ≤ k+10 by omega, show 3 ≤ k+10 by omega, show 4 ≤ k+10 by omega,
      show 5 ≤ k+10 by omega, show 6 ≤ k+10 by omega, show 7 ≤ k+10 by omega,
      show 9 ≤ k+10 by omega, if_true, show k+10 ≠ 7 by omega, show k+10 ≠ 8 by omega,
      show k+10 ≠ 9 by omega, if_false,
      show k+10-2 = k+8 by omega, show k+10-3 = k+7 by omega, show k+10-4 = k+6 by omega,
      show k+10-5 = k+5 by omega, show k+10-6 = k+4 by omega, show k+10-7 = k+3 by omega,
      show k+10-9 = k+1 by omega]
    linarith
  · interval_cases n <;> simp [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9] <;> norm_num

end OMA.P_a325695

theorem OMA.solution : type_of% @OMA.S_oeis_a325695.main :=
  ⟨OMA.P_a325695.recur, OMA.P_a325695.gf⟩
