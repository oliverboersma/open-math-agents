import OMAReductions.R_Mathoverflow17560_mathoverflow_17560_R1

-- If x is rational and 2^x is a natural number then x is a natural number.
-- Original Lean proof of the elementary case: a negative x gives a value strictly between 0 and 1; for
-- x = a / b >= 0 with 2^x = m one has m^b = 2^a, so m is a power 2^j of two and j * b = a, hence x = j.
-- The elementary case, not progress on the open question for irrational x.

namespace OMA.MO17560

theorem rational_case (x : ℝ) (hq : ∃ q : ℚ, x = q) (hx : ∃ m : ℕ, (2 : ℝ) ^ x = m) :
    ∃ m : ℕ, x = m := by
  obtain ⟨q, rfl⟩ := hq
  obtain ⟨m, hm⟩ := hx
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (q : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  by_cases hneg : q < 0
  · exfalso
    have hlt : (2 : ℝ) ^ (q : ℝ) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by exact_mod_cast hneg)
    rw [hm] at hpos hlt
    have h1 : 0 < m := by exact_mod_cast hpos
    have h2 : m < 1 := by exact_mod_cast hlt
    omega
  · have hq0 : 0 ≤ q := not_lt.mp hneg
    have hnum : 0 ≤ q.num := Rat.num_nonneg.mpr hq0
    obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le hnum
    have hb : 0 < q.den := q.den_pos
    have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
    have hxb : (q : ℝ) * (q.den : ℝ) = (a : ℝ) := by
      rw [Rat.cast_def, ha]
      push_cast
      field_simp
    have hpow : (m : ℝ) ^ q.den = (2 : ℝ) ^ a := by
      rw [← hm, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), hxb, Real.rpow_natCast]
    have hpowN : m ^ q.den = 2 ^ a := by exact_mod_cast hpow
    have hdvd : m ∣ 2 ^ a := by
      rw [← hpowN]
      exact dvd_pow_self m hb.ne'
    obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rw [← pow_mul] at hpowN
    have hja : j * q.den = a := Nat.pow_right_injective (le_refl 2) hpowN
    refine ⟨j, ?_⟩
    have h3 : (q : ℝ) * (q.den : ℝ) = (j : ℝ) * (q.den : ℝ) := by
      rw [hxb, ← hja]
      push_cast
      ring
    exact mul_right_cancel₀ hd h3

end OMA.MO17560

theorem OMA.solution : OMA.R_Mathoverflow17560_mathoverflow_17560_R1.H1 := by
  intro x hq hx
  exact OMA.MO17560.rational_case x hq hx
