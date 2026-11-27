import FormalConjectures.Wikipedia.Mahler32

open Filter

theorem OMA.solution : type_of% @Mahler32.mahler_conjecture.variants.consequence := by
  intro h x hx
  let f (y : ℝ) (n : ℕ) := Int.fract (y * (3 / 2 : ℝ) ^ n)
  have bounds (y : ℝ) :
      IsBoundedUnder (· ≤ ·) atTop (f y) ∧ IsBoundedUnder (· ≥ ·) atTop (f y) :=
    ⟨isBoundedUnder_of ⟨1, fun n => (Int.fract_lt_one (y * (3 / 2 : ℝ) ^ n)).le⟩,
      isBoundedUnder_of ⟨0, fun n => Int.fract_nonneg (y * (3 / 2 : ℝ) ^ n)⟩⟩
  refine (not_lt_of_ge ?_) h
  calc
    Mahler32.Ω (3 / 2) ≤ limsup (f x) atTop - liminf (f x) atTop := by
      refine csInf_le ⟨0, ?_⟩ ⟨x, hx.1, rfl⟩
      rintro _ ⟨y, -, rfl⟩
      exact sub_nonneg.mpr (liminf_le_limsup (bounds y).1 (bounds y).2)
    _ ≤ 1 / 2 := by
      have hs : limsup (f x) atTop ≤ 1 / 2 :=
        limsup_le_of_le (bounds x).2.isCoboundedUnder_le
          ((eventually_ge_atTop 1).mono fun n hn => (hx.2 n hn).le)
      have hi : 0 ≤ liminf (f x) atTop :=
        le_liminf_of_le (bounds x).1.isCoboundedUnder_ge
          (Eventually.of_forall fun n => Int.fract_nonneg (x * (3 / 2 : ℝ) ^ n))
      linarith
