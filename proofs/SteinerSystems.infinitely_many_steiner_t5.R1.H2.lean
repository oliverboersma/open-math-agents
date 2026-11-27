import OMAReductions.R_SteinerSystems_infinitely_many_steiner_t5_R1
import Mathlib

-- Step SteinerSystems.infinitely_many_steiner_t5.R1.H2: hypothesis H2 of reduction
-- SteinerSystems.infinitely_many_steiner_t5.R1
-- Credit: @ivillar
-- Same method as the merged step SteinerSystems.infinitely_many_steiner_t4.R1.H2 (same owner).

/-!
Take `n = 720 N + 6`. Then `n - 4 = 2 (360 N + 1)`, `n - 3 = 3 (240 N + 1)`,
`n - 2 = 4 (180 N + 1)`, `n - 1 = 5 (144 N + 1)`, `n = 6 (120 N + 1)`, and
`k! C(m, k) = m (m - 1) ⋯ (m - k + 1)` gives `C(n, 5) = 6 P₀`, `C(n - 1, 4) = 5 P₁`,
`C(n - 2, 3) = 4 P₂`, `C(n - 3, 2) = 3 P₃`, `C(n - 4, 1) = 2 P₄`.
-/

theorem OMA.solution : OMA.R_SteinerSystems_infinitely_many_steiner_t5_R1.H2 := by
  unfold OMA.R_SteinerSystems_infinitely_many_steiner_t5_R1.H2
  intro N
  refine ⟨720 * N + 6, by omega, ?_⟩
  intro i hi
  interval_cases i
  · show 6 ∣ Nat.choose (720 * N + 6) 5
    have h := Nat.descFactorial_eq_factorial_mul_choose (720 * N + 6) 5
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero] at h
    rw [show 720 * N + 6 - 4 = 720 * N + 2 by omega, show 720 * N + 6 - 3 = 720 * N + 3 by omega,
      show 720 * N + 6 - 2 = 720 * N + 4 by omega, show 720 * N + 6 - 1 = 720 * N + 5 by omega,
      show 720 * N + 6 - 0 = 720 * N + 6 by omega, show Nat.factorial 5 = 120 by rfl] at h
    have h' : 120 * Nat.choose (720 * N + 6) 5 = 120 * (6 * ((360 * N + 1) * (240 * N + 1) *
        (180 * N + 1) * (144 * N + 1) * (120 * N + 1))) := by
      rw [← h]
      ring
    exact ⟨_, Nat.eq_of_mul_eq_mul_left (by norm_num) h'⟩
  · show 5 ∣ Nat.choose (720 * N + 5) 4
    have h := Nat.descFactorial_eq_factorial_mul_choose (720 * N + 5) 4
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero] at h
    rw [show 720 * N + 5 - 3 = 720 * N + 2 by omega, show 720 * N + 5 - 2 = 720 * N + 3 by omega,
      show 720 * N + 5 - 1 = 720 * N + 4 by omega, show 720 * N + 5 - 0 = 720 * N + 5 by omega,
      show Nat.factorial 4 = 24 by rfl] at h
    have h' : 24 * Nat.choose (720 * N + 5) 4 = 24 * (5 * ((360 * N + 1) * (240 * N + 1) *
        (180 * N + 1) * (144 * N + 1))) := by
      rw [← h]
      ring
    exact ⟨_, Nat.eq_of_mul_eq_mul_left (by norm_num) h'⟩
  · show 4 ∣ Nat.choose (720 * N + 4) 3
    have h := Nat.descFactorial_eq_factorial_mul_choose (720 * N + 4) 3
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero] at h
    rw [show 720 * N + 4 - 2 = 720 * N + 2 by omega, show 720 * N + 4 - 1 = 720 * N + 3 by omega,
      show 720 * N + 4 - 0 = 720 * N + 4 by omega, show Nat.factorial 3 = 6 by rfl] at h
    have h' : 6 * Nat.choose (720 * N + 4) 3 = 6 * (4 * ((360 * N + 1) * (240 * N + 1) *
        (180 * N + 1))) := by
      rw [← h]
      ring
    exact ⟨_, Nat.eq_of_mul_eq_mul_left (by norm_num) h'⟩
  · show 3 ∣ Nat.choose (720 * N + 3) 2
    have h := Nat.descFactorial_eq_factorial_mul_choose (720 * N + 3) 2
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero] at h
    rw [show 720 * N + 3 - 1 = 720 * N + 2 by omega, show 720 * N + 3 - 0 = 720 * N + 3 by omega,
      show Nat.factorial 2 = 2 by rfl] at h
    have h' : 2 * Nat.choose (720 * N + 3) 2 = 2 * (3 * ((360 * N + 1) * (240 * N + 1))) := by
      rw [← h]
      ring
    exact ⟨_, Nat.eq_of_mul_eq_mul_left (by norm_num) h'⟩
  · show 2 ∣ Nat.choose (720 * N + 2) 1
    rw [Nat.choose_one_right]
    exact ⟨360 * N + 1, by ring⟩
