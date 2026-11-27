import OMAReductions.R_OeisA7406_conjecture_R1
import Mathlib

/-! # The prime case of the A007406 gcd conjecture

For a prime `p > 3` put `m = p - 1`, `F = m!` and `N = ∑_{k=1}^{m} (F / k)^2`. Then
`∑_{k=1}^{m} 1/k^2 = N / F^2` with `p ∤ F`. Modulo `p`, `F / k = F * k⁻¹`, inversion permutes
`1, ..., p - 1`, and `6 * ∑ k^2 = m (m + 1) (2 m + 1)` is a multiple of `p`, coprime to `6`.
So `p ∣ N`, hence `p` divides the numerator and the gcd is `p`. -/

open Finset

namespace OMA.A7406

lemma sum_sq_six (m : ℕ) : 6 * ∑ k ∈ Icc 1 m, k ^ 2 = m * (m + 1) * (2 * m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
    ring

lemma natCast_ne_zero_of_mem {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : k ∈ Icc 1 (p - 1)) :
    (k : ZMod p) ≠ 0 := by
  rw [mem_Icc] at hk
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  have := Nat.le_of_dvd (by omega) h
  omega

lemma inv_sq_sum (p : ℕ) [hp : Fact p.Prime] :
    ∑ k ∈ Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 2 = ∑ k ∈ Icc 1 (p - 1), ((k : ZMod p)) ^ 2 := by
  have hp1 := hp.out.one_lt
  have hmaps : ∀ k ∈ Icc 1 (p - 1), ((k : ZMod p)⁻¹).val ∈ Icc 1 (p - 1) := by
    intro k hk
    have h0 := natCast_ne_zero_of_mem hp.out hk
    rw [mem_Icc]
    constructor
    · rw [Nat.one_le_iff_ne_zero, Ne, ZMod.val_eq_zero]
      exact inv_ne_zero h0
    · have := ZMod.val_lt ((k : ZMod p)⁻¹)
      omega
  have hinv : ∀ k ∈ Icc 1 (p - 1), ((((k : ZMod p)⁻¹).val : ZMod p)⁻¹).val = k := by
    intro k hk
    rw [ZMod.natCast_zmod_val, inv_inv, ZMod.val_natCast, Nat.mod_eq_of_lt]
    rw [mem_Icc] at hk
    omega
  refine Finset.sum_nbij' (fun k : ℕ => ((k : ZMod p)⁻¹).val) (fun k : ℕ => ((k : ZMod p)⁻¹).val)
    hmaps hmaps hinv hinv ?_
  intro k hk
  rw [ZMod.natCast_zmod_val]

end OMA.A7406

open OMA.A7406 in
theorem OMA.solution : OMA.R_OeisA7406_conjecture_R1.H1 := by
  unfold OMA.R_OeisA7406_conjecture_R1.H1
  intro n hn hp
  have := Fact.mk hp
  have hA : OeisA89026.a n = n := by simp [OeisA89026.a, hp]
  rw [hA]
  apply Nat.gcd_eq_left
  unfold OeisA7406.a
  have hdvdF : ∀ k ∈ Icc 1 (n - 1), k ∣ (n - 1).factorial := fun k hk =>
    Nat.dvd_factorial (mem_Icc.1 hk).1 (mem_Icc.1 hk).2
  have hS : ∑ k ∈ Icc 1 (n - 1), (1 : ℚ) / (k : ℚ) ^ 2 =
      ((∑ k ∈ Icc 1 (n - 1), ((n - 1).factorial / k) ^ 2 : ℕ) : ℚ) /
        (((n - 1).factorial : ℕ) : ℚ) ^ 2 := by
    rw [Nat.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    have hk1 := (mem_Icc.1 hk).1
    have hk0 : (k : ℚ) ≠ 0 := by positivity
    have hF0 : (((n - 1).factorial : ℕ) : ℚ) ≠ 0 := by positivity
    rw [Nat.cast_pow, Nat.cast_div (hdvdF k hk) hk0]
    field_simp
  -- `n` divides the sum of squares of `1, ..., n - 1`.
  have hsq : n ∣ ∑ k ∈ Icc 1 (n - 1), k ^ 2 := by
    have h6 := sum_sq_six (n - 1)
    have hcop : Nat.Coprime n 6 := by
      rw [hp.coprime_iff_not_dvd]
      intro h
      have := Nat.le_of_dvd (by norm_num) h
      interval_cases n <;> first | omega | (norm_num at hp; done) | (norm_num at h; done)
    apply hcop.dvd_of_dvd_mul_left
    rw [h6, show n - 1 + 1 = n by omega]
    exact Dvd.dvd.mul_right (dvd_mul_left n (n - 1)) _
  -- `n` divides `N`.
  have hNdvd : n ∣ ∑ k ∈ Icc 1 (n - 1), ((n - 1).factorial / k) ^ 2 := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sum]
    have hterm : ∀ k ∈ Icc 1 (n - 1), ((((n - 1).factorial / k) ^ 2 : ℕ) : ZMod n) =
        (((n - 1).factorial : ℕ) : ZMod n) ^ 2 * ((k : ZMod n)⁻¹) ^ 2 := by
      intro k hk
      have hk0 := natCast_ne_zero_of_mem hp hk
      have h1 : ((((n - 1).factorial / k : ℕ)) : ZMod n) * (k : ZMod n) =
          (((n - 1).factorial : ℕ) : ZMod n) := by
        rw [← Nat.cast_mul, Nat.div_mul_cancel (hdvdF k hk)]
      rw [Nat.cast_pow, ← h1]
      field_simp
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, inv_sq_sum n]
    have : (∑ k ∈ Icc 1 (n - 1), (k : ZMod n) ^ 2) = 0 := by
      rw [← ZMod.natCast_eq_zero_iff] at hsq
      rw [← hsq]
      push_cast
      rfl
    rw [this, mul_zero]
  -- Pass to the numerator.
  rw [hS]
  set N : ℕ := ∑ k ∈ Icc 1 (n - 1), ((n - 1).factorial / k) ^ 2 with hNdef
  set F : ℕ := (n - 1).factorial with hFdef
  set S : ℚ := (N : ℚ) / (F : ℚ) ^ 2 with hSdef
  have hF0 : (F : ℚ) ≠ 0 := by positivity
  have key : (S.num : ℚ) * (F : ℚ) ^ 2 = (N : ℚ) * (S.den : ℚ) := by
    rw [← Rat.mul_den_eq_num S, hSdef]
    field_simp
  have keyZ : S.num * (F : ℤ) ^ 2 = (N : ℤ) * (S.den : ℤ) := by exact_mod_cast key
  have hmul : (n : ℤ) ∣ S.num * (F : ℤ) ^ 2 := by
    rw [keyZ]
    exact Dvd.dvd.mul_right (Int.natCast_dvd_natCast.2 hNdvd) _
  have hnF : ¬ (n : ℤ) ∣ (F : ℤ) ^ 2 := by
    intro h
    have h' : n ∣ F ^ 2 := by exact_mod_cast h
    have h'' := hp.dvd_of_dvd_pow h'
    rw [hFdef, hp.dvd_factorial] at h''
    omega
  have hpz : Prime (n : ℤ) := Nat.prime_iff_prime_int.1 hp
  exact Int.natCast_dvd.1 ((hpz.dvd_or_dvd hmul).resolve_right hnF)
