import OMAReductions.R_Erdos386_erdos_386_variants_two_R1

-- Step Erdos386.erdos_386.variants.two.R1.H1: hypothesis H1 of reduction Erdos386.erdos_386.variants.two.R1
-- Credit: @NoahPuckett-IO
-- If 8P + 1 = s^2 then s = 2t + 1 is odd, 2P = t (t + 1), and n = t + 1 has n choose 2 = P.

theorem OMA.solution : OMA.R_Erdos386_erdos_386_variants_two_R1.H1 := by
  intro P hP hsq
  obtain ⟨s, hs⟩ := hsq
  rcases Nat.even_or_odd' s with ⟨t, rfl | rfl⟩
  · exfalso
    have e : 2 * t * (2 * t) = 4 * (t * t) := by ring
    omega
  · have e : (2 * t + 1) * (2 * t + 1) = 4 * ((t + 1) * t) + 1 := by ring
    have h2 : (t + 1) * t = 2 * P := by omega
    have ht : 3 ≤ t := by
      by_contra h
      have : t ≤ 2 := by omega
      interval_cases t <;> omega
    refine ⟨t + 1, by omega, ?_, ?_⟩
    · rw [Nat.choose_two_right, Nat.add_sub_cancel]
      omega
    · have : (t + 1) * t ≤ (t + 1) ^ 2 := by
        rw [pow_two]
        exact Nat.mul_le_mul_left _ (by omega)
      omega
