import OMAReductions.R_Erdos288_erdos_288_variants_i2_card_eq_1_R1
import Mathlib

-- Step Erdos288.erdos_288.variants.i2_card_eq_1.R1.H1: hypothesis H1 of reduction Erdos288.erdos_288.variants.i2_card_eq_1.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! If r + 1/d = z then r = (z d - 1)/d, and gcd(z d - 1, d) = 1, so den r = d and num r + 1 = z d.
Conversely, if den r = d divides num r + 1, then r + 1/d = (num r + 1)/d is an integer. -/

theorem OMA.solution : OMA.R_Erdos288_erdos_288_variants_i2_card_eq_1_R1.H1 := by
  intro r d
  have hd0 : (0 : ℚ) < (d : ℚ) := by exact_mod_cast d.pos
  constructor
  · rintro ⟨z, hz⟩
    have hr : r = ((z * d - 1 : ℤ) : ℚ) / ((d : ℤ) : ℚ) := by
      rw [eq_div_iff (by positivity)]
      have : r = z - (d : ℚ)⁻¹ := by linarith
      rw [this]; push_cast; field_simp
    have hcop : Nat.Coprime (z * d - 1 : ℤ).natAbs (d : ℤ).natAbs := by
      have h : IsCoprime (z * d - 1 : ℤ) (d : ℤ) := ⟨-1, z, by ring⟩
      have := Int.isCoprime_iff_gcd_eq_one.mp h
      rwa [Int.gcd_eq_natAbs] at this
    have hden := Rat.den_div_eq_of_coprime (a := z * d - 1) (b := (d : ℤ)) (by exact_mod_cast d.pos) hcop
    have hnum := Rat.num_div_eq_of_coprime (a := z * d - 1) (b := (d : ℤ)) (by exact_mod_cast d.pos) hcop
    rw [← hr] at hden hnum
    refine ⟨by exact_mod_cast hden, ?_⟩
    rw [hden, hnum]
    exact ⟨z, by ring⟩
  · rintro ⟨hden, ⟨k, hk⟩⟩
    refine ⟨k, ?_⟩
    have h1 : r = (r.num : ℚ) / (r.den : ℚ) := (Rat.num_div_den r).symm
    rw [h1, hden]
    have h2 : (r.num : ℚ) = (d : ℚ) * k - 1 := by
      have : ((r.num + 1 : ℤ) : ℚ) = ((r.den * k : ℤ) : ℚ) := by rw [hk]
      push_cast at this; rw [hden] at this; linarith
    rw [h2]; field_simp; ring
