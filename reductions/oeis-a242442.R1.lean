import OMAStatements.S_oeis_a242442

/-!
Verify the finite prefix and the exception at 18, and reduce the tail to
the ternary form with coefficients 3, 24, and 1. The lower bound on its
last coordinate preserves the ordinary, rather than generalized,
pentagonal numbers in the original question.
-/

namespace OMA.R_oeis_a242442_R1

open OMA.S_oeis_a242442

/-- Represent the odd tail by the ternary quadratic form. -/
def H1 : Prop :=
  ∀ n : ℕ, 128 < n → n % 2 = 1 →
    ∃ u v : ℕ, ∃ w : ℤ, Odd u ∧ Odd v ∧ -1 ≤ w ∧ w % 6 = 5 ∧
      24 * (n : ℤ) + 4 = 3 * (u : ℤ) ^ 2 + 24 * (v : ℤ) ^ 2 + w ^ 2

/-- Represent the even tail by the ternary quadratic form. -/
def H2 : Prop :=
  ∀ n : ℕ, 128 < n → n % 2 = 0 →
    ∃ u v : ℕ, ∃ w : ℤ, Odd u ∧ Odd v ∧ -1 ≤ w ∧ w % 6 = 5 ∧
      24 * (n : ℤ) + 4 = 3 * (u : ℤ) ^ 2 + 24 * (v : ℤ) ^ 2 + w ^ 2

section Proof

private theorem triangular_identity (x : ℕ) :
    24 * ((x * (x + 1) / 2 : ℕ) : ℤ) + 3 = 3 * (2 * (x : ℤ) + 1) ^ 2 := by
  have hdiv : 2 ∣ x * (x + 1) := by
    rcases Nat.even_or_odd x with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact dvd_mul_of_dvd_left (by omega) _
    · exact dvd_mul_of_dvd_right (by omega) _
  have h : 2 * (x * (x + 1) / 2) = x * (x + 1) := Nat.mul_div_cancel' hdiv
  have hcast : (2 : ℤ) * ((x * (x + 1) / 2 : ℕ) : ℤ) = (x : ℤ) * (x + 1) := by
    exact_mod_cast h
  nlinarith only [hcast]

private theorem pentagonal_identity (z : ℕ) :
    24 * ((z * (3 * z - 1) / 2 : ℕ) : ℤ) + 1 = (6 * (z : ℤ) - 1) ^ 2 := by
  rcases Nat.eq_zero_or_pos z with rfl | hz
  · decide
  have hdiv : 2 ∣ z * (3 * z - 1) := by
    rcases Nat.even_or_odd z with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact dvd_mul_of_dvd_left (by omega) _
    · exact dvd_mul_of_dvd_right (by omega) _
  have h : 2 * (z * (3 * z - 1) / 2) = z * (3 * z - 1) := Nat.mul_div_cancel' hdiv
  have hcast : (2 : ℤ) * ((z * (3 * z - 1) / 2 : ℕ) : ℤ) =
      (z : ℤ) * (3 * (z : ℤ) - 1) := by
    calc
      _ = ((2 * (z * (3 * z - 1) / 2) : ℕ) : ℤ) := by
        simp only [Nat.cast_mul, Nat.cast_ofNat]
      _ = ((z * (3 * z - 1) : ℕ) : ℤ) := congrArg (fun n : ℕ => (n : ℤ)) h
      _ = _ := by simp [Nat.cast_sub (by omega : 1 ≤ 3 * z)]
  nlinarith only [hcast]

private theorem from_quadratic {n u v : ℕ} {w : ℤ} (hu : Odd u) (hv : Odd v)
    (hw : -1 ≤ w) (hmod : w % 6 = 5)
    (he : 24 * (n : ℤ) + 4 = 3 * (u : ℤ) ^ 2 + 24 * (v : ℤ) ^ 2 + w ^ 2) :
    IsRepresentable n := by
  obtain ⟨x, rfl⟩ := hu
  obtain ⟨y, rfl⟩ := hv
  let z := ((w + 1) / 6).toNat
  have hz : (z : ℤ) = (w + 1) / 6 := Int.toNat_of_nonneg (by omega)
  have hw' : w = 6 * (z : ℤ) - 1 := by omega
  rw [hw'] at he
  push_cast at he
  refine ⟨x, y, z, ?_⟩
  have hcast :
      ((x * (x + 1) / 2 : ℕ) : ℤ) + (2 * (y : ℤ) + 1) ^ 2 +
        ((z * (3 * z - 1) / 2 : ℕ) : ℤ) = (n : ℤ) := by
    nlinarith only [he, triangular_identity x, pentagonal_identity z]
  exact_mod_cast hcast

private theorem eighteen : ¬ IsRepresentable 18 := by
  rintro ⟨x, y, z, he⟩
  have hx : x < 7 := by
    by_contra! h
    have hp := Nat.mul_le_mul h (show 8 ≤ x + 1 by omega)
    omega
  have hy : y < 2 := by
    by_contra! h
    have hp := Nat.pow_le_pow_left (show 5 ≤ 2*y+1 by omega) 2
    omega
  have hz : z < 4 := by
    by_contra! h
    have hp := Nat.mul_le_mul h (show 11 ≤ 3*z-1 by omega)
    omega
  have table : ∀ a : Fin 7, ∀ b : Fin 2, ∀ c : Fin 4,
      a.val * (a.val + 1) / 2 + (2 * b.val + 1)^2 + c.val * (3 * c.val - 1) / 2 ≠ 18 := by
    decide
  exact table ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ he

set_option maxRecDepth 30000 in
private theorem finite_prefix {n : ℕ} (h0 : 1 ≤ n) (hn : n ≤ 128) (h18 : n ≠ 18) :
    IsRepresentable n := by
  let witnesses : List (ℕ × ℕ × ℕ) :=
    [
      (0, 0, 0), (0, 0, 0), (0, 0, 1), (1, 0, 1), (2, 0, 0), (2, 0, 1), (0, 0, 2), (1, 0, 2),
      (3, 0, 1), (0, 1, 0), (0, 1, 1), (1, 1, 1), (2, 1, 0), (0, 0, 3), (0, 1, 2), (1, 1, 2),
      (2, 0, 3), (2, 1, 2), (0, 0, 0), (3, 0, 3), (3, 1, 2), (0, 1, 3), (1, 1, 3), (0, 0, 4),
      (1, 0, 4), (0, 2, 0), (0, 2, 1), (1, 2, 1), (2, 2, 0), (2, 2, 1), (0, 2, 2), (0, 1, 4),
      (1, 1, 4), (2, 2, 2), (2, 1, 4), (4, 2, 0), (0, 0, 5), (0, 2, 3), (1, 2, 3), (2, 0, 5),
      (2, 2, 3), (4, 1, 4), (3, 0, 5), (3, 2, 3), (0, 1, 5), (1, 1, 5), (4, 0, 5), (0, 2, 4),
      (1, 2, 4), (0, 3, 0), (0, 3, 1), (1, 3, 1), (0, 0, 6), (1, 0, 6), (0, 3, 2), (1, 3, 2),
      (3, 3, 1), (2, 3, 2), (3, 0, 6), (4, 3, 0), (0, 1, 6), (0, 3, 3), (1, 3, 3), (2, 1, 6),
      (2, 3, 3), (5, 3, 1), (3, 1, 6), (3, 3, 3), (6, 2, 4), (5, 3, 2), (4, 1, 6), (0, 0, 7),
      (1, 0, 7), (6, 0, 6), (2, 0, 7), (5, 1, 6), (0, 2, 6), (1, 2, 6), (7, 3, 1), (0, 1, 7),
      (1, 1, 7), (0, 4, 0), (0, 4, 1), (1, 4, 1), (0, 3, 5), (1, 3, 5), (0, 4, 2), (1, 4, 2),
      (3, 4, 1), (2, 4, 2), (3, 3, 5), (4, 4, 0), (3, 4, 2), (0, 0, 8), (1, 0, 8), (0, 2, 7),
      (1, 2, 7), (5, 4, 1), (2, 2, 7), (3, 0, 8), (0, 3, 6), (0, 1, 8), (1, 1, 8), (0, 4, 4),
      (1, 4, 4), (4, 2, 7), (2, 4, 4), (3, 1, 8), (5, 0, 8), (3, 4, 4), (4, 3, 6), (4, 1, 8),
      (7, 3, 5), (4, 4, 4), (6, 0, 8), (5, 3, 6), (0, 4, 5), (0, 2, 8), (0, 0, 9), (0, 3, 7),
      (1, 3, 7), (0, 5, 0), (0, 5, 1), (1, 5, 1), (2, 5, 0), (2, 5, 1), (0, 1, 9), (1, 1, 9),
      (3, 5, 1)]
  have h : ∀ k : Fin 129, 1 ≤ k.val → k.val ≠ 18 →
      let (a, b, c) := witnesses.getD k.val (0, 0, 0)
      a * (a + 1) / 2 + (2 * b + 1) ^ 2 + c * (3 * c - 1) / 2 = k.val := by
    dsimp [witnesses]
    decide +kernel
  have hcase := h ⟨n, by omega⟩ h0 h18
  rcases he : witnesses.getD n (0, 0, 0) with ⟨a, b, c⟩
  exact ⟨a, b, c, by simpa only [he, Fin.val_mk] using hcase⟩

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a242442.main := by
  intro odd_tail even_tail n h0
  constructor
  · rintro hn rfl
    exact eighteen hn
  · intro h18
    by_cases hn : n ≤ 128
    · exact finite_prefix h0 hn h18
    · have hex :
          ∃ u v : ℕ, ∃ w : ℤ, Odd u ∧ Odd v ∧ -1 ≤ w ∧ w % 6 = 5 ∧
            24 * (n : ℤ) + 4 = 3 * (u : ℤ)^2 + 24 * (v : ℤ)^2 + w^2 := by
        rcases Nat.mod_two_eq_zero_or_one n with h | h
        · exact even_tail n (by omega) h
        · exact odd_tail n (by omega) h
      obtain ⟨u, v, w, hu, hv, hw, hmod, he⟩ := hex
      exact from_quadratic hu hv hw hmod he

end Proof
end OMA.R_oeis_a242442_R1
