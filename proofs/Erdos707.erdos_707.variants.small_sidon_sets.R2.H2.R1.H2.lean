import OMAReductions.R_Erdos707_erdos_707_variants_small_sidon_sets_R2_H2_R1

/-! # Scaling by a nonzero base-field element preserves the Singer predicate

Both conditions are homogeneous: `(x * c) ^ g = x ^ g * c ^ g`, and the base-field
coefficients absorb the powers of `c`. -/

theorem OMA.solution : OMA.R_Erdos707_erdos_707_variants_small_sidon_sets_R2_H2_R1.H2 := by
  intro F K _ _ _ u v x c hc
  have hC : algebraMap F K c ≠ 0 := (map_ne_zero _).mpr hc
  dsimp only
  constructor
  · rintro ⟨h1, s, t, h2⟩
    refine ⟨?_, s / c ^ v, t * c ^ u / c ^ v, ?_⟩
    · rintro ⟨a, ha⟩
      apply h1
      refine ⟨a * c ^ (u.gcd v), ?_⟩
      rw [mul_pow, ha, map_mul, map_pow]
    · rw [mul_pow, mul_pow] at h2
      simp only [map_div₀, map_mul, map_pow]
      field_simp
      linear_combination h2
  · rintro ⟨h1, s, t, h2⟩
    refine ⟨?_, s * c ^ v, t * c ^ v / c ^ u, ?_⟩
    · rintro ⟨a, ha⟩
      apply h1
      refine ⟨a / c ^ (u.gcd v), ?_⟩
      rw [mul_pow] at ha
      rw [map_div₀, map_pow, ← ha, mul_div_cancel_right₀ _ (pow_ne_zero _ hC)]
    · rw [mul_pow, mul_pow, h2]
      simp only [map_div₀, map_mul, map_pow]
      field_simp
