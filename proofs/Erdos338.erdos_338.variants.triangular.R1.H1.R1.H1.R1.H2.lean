import OMAReductions.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1
import Mathlib

-- Step Erdos338.erdos_338.variants.triangular.R1.H1.R1.H1.R1.H2: hypothesis H2 of reduction Erdos338.erdos_338.variants.triangular.R1.H1.R1.H1.R1
-- Credit: @ivillar

/-! With `s = ⌊√⌊√N⌋⌋` we have `s^4 ≤ N`, so `(3 s)^20 = 3^20 s^20 ≤ 3^20 N^5 < N^6` once
`N > 3^20`; taking 20th roots gives `3 s < N^(3/10)`. -/

namespace O2E338
open Filter

theorem main_H2 : OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1.H2 := by
  unfold OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1.H2
  filter_upwards [eventually_ge_atTop 3486784401] with m hm
  dsimp only
  set N := 8 * m + 3 with hNdef
  have hN : 3486784401 < N := by omega
  set s := N.sqrt.sqrt with hsdef
  have hs2 : s ^ 2 ≤ N.sqrt := Nat.sqrt_le' N.sqrt
  have hs4 : s ^ 4 ≤ N := by
    calc s ^ 4 = (s ^ 2) ^ 2 := by ring
      _ ≤ N.sqrt ^ 2 := Nat.pow_le_pow_left hs2 2
      _ ≤ N := Nat.sqrt_le' N
  have key : (3 * s) ^ 20 < N ^ 6 := by
    have h5 : s ^ 20 ≤ N ^ 5 := by
      calc s ^ 20 = (s ^ 4) ^ 5 := by ring
        _ ≤ N ^ 5 := Nat.pow_le_pow_left hs4 5
    have hpos : 0 < N ^ 5 := by positivity
    calc (3 * s) ^ 20 = 3486784401 * s ^ 20 := by ring
      _ ≤ 3486784401 * N ^ 5 := Nat.mul_le_mul_left _ h5
      _ < N * N ^ 5 := Nat.mul_lt_mul_of_pos_right hN hpos
      _ = N ^ 6 := by ring
  have keyR : ((3 : ℝ) * (s : ℝ)) ^ (20 : ℕ) < (N : ℝ) ^ (6 : ℕ) := by exact_mod_cast key
  have ha : (0 : ℝ) ≤ 3 * (s : ℝ) := by positivity
  have hb : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  calc (3 : ℝ) * (s : ℝ) = ((3 * (s : ℝ)) ^ (20 : ℕ)) ^ ((1 : ℝ) / 20) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul ha]; norm_num
    _ < ((N : ℝ) ^ (6 : ℕ)) ^ ((1 : ℝ) / 20) :=
        Real.rpow_lt_rpow (by positivity) keyR (by norm_num)
    _ = (N : ℝ) ^ (3 / 10 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hb]; norm_num

end O2E338

theorem OMA.solution : OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1.H2 :=
  O2E338.main_H2
