import OMAStatements.S_oeis_a341239

open OMA.S_oeis_a341239 in
theorem OMA.solution : type_of% @OMA.S_oeis_a341239.main := by
  intro n hn
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 2 := by positivity
  have hs2 : Real.sqrt 2 < 2 := by nlinarith
  set x : ℝ := Real.sqrt 2 * (n : ℝ) with hx
  set m : ℤ := ⌊x⌋ with hm
  set f : ℝ := x - m with hf
  have hirr : Irrational x := irrational_sqrt_two.mul_natCast (by omega)
  have hf0 : 0 < f := by
    have h1 : (m : ℝ) ≤ x := Int.floor_le x
    have h3 : x ≠ (m : ℝ) := hirr.ne_int m
    rw [hf]; exact sub_pos.mpr (lt_of_le_of_ne h1 (Ne.symm h3))
  have hf1 : f < 1 := by
    have := Int.lt_floor_add_one x
    rw [hf]; linarith
  have hsplit : r * (m : ℝ) = ((m + 2 * n : ℤ) : ℝ) + (-(Real.sqrt 2 * f)) := by
    rw [hf, hx, r]; push_cast; nlinarith
  have ha : a n = (m + 2 * n : ℤ) + ⌊-(Real.sqrt 2 * f)⌋ := by
    unfold a; rw [s, ← hx, ← hm, hsplit, Int.floor_intCast_add]
  set k : ℤ := ⌊-(Real.sqrt 2 * f)⌋ with hk
  have hk1 : (k : ℝ) ≤ -(Real.sqrt 2 * f) := Int.floor_le _
  have hk2 : -(Real.sqrt 2 * f) < k + 1 := Int.lt_floor_add_one _
  have hpos : 0 < Real.sqrt 2 * f := mul_pos hs0 hf0
  have hlt : Real.sqrt 2 * f < 2 := by nlinarith
  have kle : k ≤ -1 := by
    have : (k : ℝ) < 0 := by linarith
    have : k < 0 := by exact_mod_cast this
    omega
  have kge : -2 ≤ k := by
    have : (-3 : ℝ) < k := by linarith
    have : -3 < k := by exact_mod_cast this
    omega
  have kle' : (k : ℝ) ≤ -1 := by exact_mod_cast kle
  have kge' : (-2 : ℝ) ≤ k := by exact_mod_cast kge
  have hval : r * s * (n : ℝ) - (a n : ℝ) = f - k := by
    rw [ha, r, s, hf]; push_cast
    rw [hx]; nlinarith
  rw [hval]
  constructor <;> linarith
