import OMAStatements.S_oeis_a381006

theorem OMA.solution : type_of% @OMA.S_oeis_a381006.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hu1 : 1 ≤ 2 ^ (2 * m) := Nat.one_le_two_pow
  generalize hu : 2 ^ (2 * m) = u at hu1
  have e0 : 2 ^ (4 * m) = u ^ 2 := by rw [← hu, ← pow_mul]; ring_nf
  have e1 : 2 ^ (4 * (m + 1)) = 16 * u ^ 2 := by
    rw [show 4 * (m + 1) = 4 * m + 4 by ring, pow_add, e0]; ring
  have e2 : 2 ^ (4 * (m + 1) - 2) = 4 * u ^ 2 := by
    rw [show 4 * (m + 1) - 2 = 4 * m + 2 by omega, pow_add, e0]; ring
  have e3 : 2 ^ (2 * (m + 1)) = 4 * u := by
    rw [show 2 * (m + 1) = 2 * m + 2 by ring, pow_add, hu]; ring
  have e4 : 2 ^ (2 * (m + 1) + 1) = 8 * u := by
    rw [pow_succ, e3]; ring
  have e5 : 2 ^ (4 * (m + 1) + 1) = 32 * u ^ 2 := by
    rw [pow_succ, e1]; ring
  have hle : u ≤ u ^ 2 := by nlinarith
  have hb : OMA.S_oeis_a381006.legB (m + 1) = 12 * u ^ 2 - 4 * u - 1 := by
    unfold OMA.S_oeis_a381006.legB; rw [e1, e2, e3]; omega
  have hc : OMA.S_oeis_a381006.hyp (m + 1) = 20 * u ^ 2 + 4 * u + 1 := by
    unfold OMA.S_oeis_a381006.hyp; rw [e1, e2, e3]; omega
  set g := Nat.gcd (Nat.gcd (OMA.S_oeis_a381006.legA (m + 1)) (OMA.S_oeis_a381006.legB (m + 1))) (OMA.S_oeis_a381006.hyp (m + 1)) with hg
  have gb : g ∣ OMA.S_oeis_a381006.legB (m + 1) :=
    (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  have gc : g ∣ OMA.S_oeis_a381006.hyp (m + 1) := Nat.gcd_dvd_right _ _
  have gs : g ∣ 2 ^ (4 * (m + 1) + 1) := by
    rw [e5]
    have := Nat.dvd_add gb gc
    rw [hb, hc] at this
    have h2 : 12 * u ^ 2 - 4 * u - 1 + (20 * u ^ 2 + 4 * u + 1) = 32 * u ^ 2 := by omega
    rwa [h2] at this
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 gs
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · rw [hi, h0]; rfl
  · exfalso
    have h2 : 2 ∣ g := by rw [hi]; exact dvd_pow_self 2 (by omega)
    have := h2.trans gb
    rw [hb] at this
    omega
