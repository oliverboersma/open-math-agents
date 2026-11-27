import OMAReductions.R_Mills_exists_prime_R1

-- Step Mills.exists-prime.R1.H2
-- Credit: @caa1982

open Real

theorem OMA.solution : OMA.R_Mills_exists_prime_R1.H2 := by
  intro q hq2 hlo hhi
  let u : ℕ → ℝ := fun n => (q n : ℝ) ^ (((3 ^ (n + 1) : ℕ) : ℝ)⁻¹)
  let v : ℕ → ℝ := fun n => ((q n + 1 : ℕ) : ℝ) ^ (((3 ^ (n + 1) : ℕ) : ℝ)⁻¹)
  have hu_nonneg : ∀ n, 0 ≤ u n := fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hv_nonneg : ∀ n, 0 ≤ v n := fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hu_pow : ∀ n, u n ^ (3 ^ (n + 1)) = (q n : ℝ) := fun n =>
    Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) (by positivity)
  have hv_pow : ∀ n, v n ^ (3 ^ (n + 1)) = ((q n + 1 : ℕ) : ℝ) := fun n =>
    Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) (by positivity)
  have hu_mono : Monotone u := by
    apply monotone_nat_of_le_succ
    intro n
    apply le_of_pow_le_pow_left₀ (show 3 ^ (n + 2) ≠ 0 by positivity) (hu_nonneg (n + 1))
    rw [show 3 ^ (n + 2) = 3 ^ (n + 1) * 3 by ring, pow_mul, hu_pow n,
      show 3 ^ (n + 1) * 3 = 3 ^ (n + 2) by ring, hu_pow (n + 1)]
    exact_mod_cast hlo n
  have hv_anti : StrictAnti v := by
    apply strictAnti_nat_of_succ_lt
    intro n
    apply lt_of_pow_lt_pow_left₀ (3 ^ (n + 2)) (hv_nonneg n)
    rw [hv_pow (n + 1), show 3 ^ (n + 2) = 3 ^ (n + 1) * 3 by ring, pow_mul, hv_pow n]
    exact_mod_cast hhi n
  have huv : ∀ n, u n < v n := by
    intro n
    apply lt_of_pow_lt_pow_left₀ (3 ^ (n + 1)) (hv_nonneg n)
    rw [hu_pow n, hv_pow n]
    push_cast
    linarith
  have huv_all : ∀ m n, u m < v n := by
    intro m n
    calc u m ≤ u (max m n) := hu_mono (le_max_left m n)
      _ < v (max m n) := huv (max m n)
      _ ≤ v n := hv_anti.antitone (le_max_right m n)
  have hbdd : BddAbove (Set.range u) := ⟨v 0, by rintro _ ⟨m, rfl⟩; exact (huv_all m 0).le⟩
  let A : ℝ := ⨆ m, u m
  have h1_lt_u0 : 1 < u 0 := by
    apply lt_of_pow_lt_pow_left₀ (3 ^ 1) (hu_nonneg 0)
    rw [one_pow, hu_pow 0]
    have : (2 : ℝ) ≤ q 0 := by exact_mod_cast hq2 0
    linarith
  have hA_ge : ∀ n, u n ≤ A := fun n => le_ciSup hbdd n
  have hA_lt : ∀ n, A < v n := by
    intro n
    have hle : A ≤ v (n + 1) := ciSup_le fun m => (huv_all m (n + 1)).le
    exact lt_of_le_of_lt hle (hv_anti (Nat.lt_succ_self n))
  refine ⟨A, lt_of_lt_of_le h1_lt_u0 (hA_ge 0), ?_⟩
  intro n
  have hA_nonneg : 0 ≤ A := le_trans (hu_nonneg 0) (hA_ge 0)
  have hlow : (q n : ℝ) ≤ A ^ (3 ^ (n + 1)) := by
    rw [← hu_pow n]
    exact pow_le_pow_left₀ (hu_nonneg n) (hA_ge n) _
  have hup : A ^ (3 ^ (n + 1)) < (q n : ℝ) + 1 := by
    have : A ^ (3 ^ (n + 1)) < v n ^ (3 ^ (n + 1)) :=
      pow_lt_pow_left₀ (hA_lt n) hA_nonneg (by positivity)
    rw [hv_pow n] at this
    push_cast at this
    exact this
  exact (Nat.floor_eq_iff (by positivity)).mpr ⟨hlow, hup⟩
