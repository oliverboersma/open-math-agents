import OMAReductions.R_SteinerSystems_infinitely_many_steiner_t4_R1

/-! The divisibility conditions for S(4, 5, n) hold for every n = 120 N + 5: the falling
factorials of 120 N + 5, 120 N + 4 and 120 N + 3 factor explicitly, giving
C(n, 4) = 5 (24N+1)(30N+1)(40N+1)(60N+1), C(n-1, 3) = 4 (30N+1)(40N+1)(60N+1),
C(n-2, 2) = 3 (40N+1)(60N+1) and n - 3 = 2 (60N+1). -/

namespace OMASteiner4

lemma dvd4 (N : ℕ) : 5 ∣ Nat.choose (120 * N + 5) 4 := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (120 * N + 5) 4
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero] at h
  have e1 : 120 * N + 5 - 1 = 120 * N + 4 := by omega
  have e2 : 120 * N + 5 - 2 = 120 * N + 3 := by omega
  have e3 : 120 * N + 5 - 3 = 120 * N + 2 := by omega
  rw [e1, e2, e3, Nat.sub_zero, show Nat.factorial 4 = 24 from rfl] at h
  refine ⟨(24 * N + 1) * (30 * N + 1) * (40 * N + 1) * (60 * N + 1),
    Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 24) ?_⟩
  rw [← h]
  ring

lemma dvd3 (N : ℕ) : 4 ∣ Nat.choose (120 * N + 4) 3 := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (120 * N + 4) 3
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero] at h
  have e1 : 120 * N + 4 - 1 = 120 * N + 3 := by omega
  have e2 : 120 * N + 4 - 2 = 120 * N + 2 := by omega
  rw [e1, e2, Nat.sub_zero, show Nat.factorial 3 = 6 from rfl] at h
  refine ⟨(30 * N + 1) * (40 * N + 1) * (60 * N + 1),
    Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 6) ?_⟩
  rw [← h]
  ring

lemma dvd2 (N : ℕ) : 3 ∣ Nat.choose (120 * N + 3) 2 := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (120 * N + 3) 2
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero] at h
  have e1 : 120 * N + 3 - 1 = 120 * N + 2 := by omega
  rw [e1, Nat.sub_zero, show Nat.factorial 2 = 2 from rfl] at h
  refine ⟨(40 * N + 1) * (60 * N + 1), Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) ?_⟩
  rw [← h]
  ring

end OMASteiner4

theorem OMA.solution : OMA.R_SteinerSystems_infinitely_many_steiner_t4_R1.H2 := by
  intro N
  refine ⟨120 * N + 5, by omega, ?_⟩
  intro i hi
  interval_cases i
  · show Nat.choose 5 4 ∣ Nat.choose (120 * N + 5) 4
    rw [show Nat.choose 5 4 = 5 from by decide]
    exact OMASteiner4.dvd4 N
  · show Nat.choose 4 3 ∣ Nat.choose (120 * N + 4) 3
    rw [show Nat.choose 4 3 = 4 from by decide]
    exact OMASteiner4.dvd3 N
  · show Nat.choose 3 2 ∣ Nat.choose (120 * N + 3) 2
    rw [show Nat.choose 3 2 = 3 from by decide]
    exact OMASteiner4.dvd2 N
  · show Nat.choose 2 1 ∣ Nat.choose (120 * N + 2) 1
    rw [show Nat.choose 2 1 = 2 from by decide, Nat.choose_one_right]
    exact ⟨60 * N + 1, by ring⟩
