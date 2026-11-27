import OMAStatements.S_oeis_a001595
import Mathlib

-- Problem: A001595, a(n) = a(n-1) + a(n-2) + 1 with a(0) = a(1) = 1.
-- Credit: @canneyi
-- The generating function identity is checked coefficient by coefficient:
-- a(k+3) - 2 a(k+2) + a(k) = 0 for every k, and the first three coefficients are 1, -1, 1.

open OMA.S_oeis_a001595

namespace OMAa001595

theorem step (k : ℕ) : a (k + 3) - 2 * a (k + 2) + a k = 0 := by
  have h3 : a (k + 3) = a (k + 2) + a (k + 1) + 1 := rfl
  have h2 : a (k + 2) = a (k + 1) + a k + 1 := rfl
  linarith

theorem step' (n : ℕ) (hn : 2 < n) : a n - 2 * a (n - 1) + a (n - 3) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 3 = k by omega]
  exact step k

theorem initials : a 0 = 1 ∧ a 1 = 1 ∧ a 2 = 3 :=
  ⟨rfl, rfl, rfl⟩

open PowerSeries in
theorem gf : mk a * (1 - 2 * (X : PowerSeries ℤ) + X ^ 3) = 1 - X + X ^ 2 := by
  have product : mk a * (1 - 2 * (X : PowerSeries ℤ) + X ^ 3) =
      mk a - 2 • (mk a * X ^ 1) + mk a * X ^ 3 := by
    simp only [nsmul_eq_mul]
    ring
  rw [product]
  ext n
  simp only [map_add, map_sub, map_nsmul, coeff_mul_X_pow', coeff_mk, coeff_one, coeff_X,
    coeff_X_pow]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  by_cases h : 2 < n
  · have h1 : 1 ≤ n := by omega
    have h3 : 3 ≤ n := by omega
    have h0' : n ≠ 0 := by omega
    have h1' : n ≠ 1 := by omega
    have h2' : n ≠ 2 := by omega
    simp only [h1, h3, h0', h1', h2', if_true, if_false]
    have hr := step' n h
    linarith
  · obtain ⟨h0, h1, h2⟩ := initials
    interval_cases n <;> norm_num [h0, h1, h2]

open PowerSeries in
theorem gf2 : mk a * ((1 - (X : PowerSeries ℤ) - X ^ 2) * (1 - X)) =
    2 * (1 - X) - (1 - X - X ^ 2) := by
  have e1 : (1 - (X : PowerSeries ℤ) - X ^ 2) * (1 - X) = 1 - 2 * X + X ^ 3 := by ring
  have e2 : 2 * (1 - (X : PowerSeries ℤ)) - (1 - X - X ^ 2) = 1 - X + X ^ 2 := by ring
  rw [e1, e2]
  exact gf

end OMAa001595

theorem OMA.solution : type_of% @OMA.S_oeis_a001595.main :=
  ⟨OMAa001595.gf, OMAa001595.gf2⟩
