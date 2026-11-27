import OMAStatements.S_oeis_a341254
import Mathlib

/-!
# Proof of OEIS-A341254 conjecture

Credit: @AkiRA-COM-FP
-/

open OMA.S_oeis_a341254

theorem OMA.solution : type_of% @OMA.S_oeis_a341254.main := by
  intro n hn
  have hsquare : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hr_sq : r ^ 2 = 2 * r + 1 / 4 := by
    unfold r
    nlinarith only [hsquare]
  have hslo : (2 : ℝ) < Real.sqrt 5 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hshi : Real.sqrt 5 < (5 : ℝ) / 2 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hr₀ : 0 < r - 2 := by unfold r; linarith only [hslo]
  have hr₁ : r - 2 < 1 / 4 := by unfold r; linarith only [hshi]
  have hsirr : Irrational (Real.sqrt 5) := by norm_num
  have hrirr : Irrational r := by
    unfold r
    simpa only [Nat.cast_ofNat] using (hsirr.natCast_add 2).div_natCast (m := 2) (by decide)
  let m : ℤ := ⌊r * (n : ℝ)⌋
  let e : ℝ := r * (n : ℝ) - (m : ℝ)
  have he₀ : 0 < e := sub_pos.mpr
    (lt_of_le_of_ne (Int.floor_le _) ((hrirr.mul_natCast (by omega : n ≠ 0)).ne_int m).symm)
  have he₁ : e < 1 := by
    change r * (n : ℝ) - (m : ℝ) < 1
    have h : r * (n : ℝ) < (m : ℝ) + 1 := Int.lt_floor_add_one _
    linarith only [h]
  have hd₀ : 0 < (r - 2) * e := mul_pos hr₀ he₀
  have hd₁ : (r - 2) * e < 1 / 4 := by
    calc
      _ < (r - 2) * 1 := mul_lt_mul_of_pos_left he₁ hr₀
      _ < _ := by simpa only [mul_one] using hr₁
  let z : ℤ := 2 * m + ((n / 4 : ℕ) : ℤ)
  have hz : (z : ℝ) = 2 * (m : ℝ) + ((n / 4 : ℕ) : ℝ) := by
    simp only [z, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
  have hnqr : (n : ℝ) = 4 * ((n / 4 : ℕ) : ℝ) + ((n % 4 : ℕ) : ℝ) := by
    exact_mod_cast (show n = 4 * (n / 4) + n % 4 by omega)
  have htotal : (n : ℝ) * r ^ 2 = (z : ℝ) + ((n % 4 : ℕ) : ℝ) / 4 + 2 * e := by
    rw [hr_sq, hz]
    dsimp only [e]
    linarith only [hnqr]
  have houter : r * (m : ℝ) = (z : ℝ) + ((n % 4 : ℕ) : ℝ) / 4 - (r - 2) * e := by
    have h : r * (m : ℝ) = (n : ℝ) * r ^ 2 - r * e := by
      dsimp only [e]
      ring
    rw [h, htotal]
    ring
  have ha : a n = ⌊r * (m : ℝ)⌋ := rfl
  by_cases hrem : n % 4 = 0
  · norm_num [hrem] at houter htotal
    have hf : a n = z - 1 := by
      rw [ha]
      apply Int.floor_eq_iff.mpr
      push_cast
      constructor <;> linarith only [houter, hd₀, hd₁]
    rw [hf]
    push_cast
    constructor <;> linarith only [htotal, he₀, he₁]
  · have hlo : (1 : ℝ) ≤ ((n % 4 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ n % 4 by omega)
    have hhi : ((n % 4 : ℕ) : ℝ) ≤ 3 := by
      exact_mod_cast (show n % 4 ≤ 3 by omega)
    have hf : a n = z := by
      rw [ha]
      exact Int.floor_eq_iff.mpr
        ⟨by linarith only [houter, hlo, hd₁], by linarith only [houter, hhi, hd₀]⟩
    rw [hf]
    constructor <;> linarith only [htotal, hlo, hhi, he₀, he₁]
