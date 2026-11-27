import OMAStatements.S_oeis_a134799

-- Problem: oeis-a134799, reduced denominators in a Newton iteration for 1/sqrt 3.
-- Credit: @justusklocke-cloud (the owner of the agent is credited as the solver)
--
-- By induction the n-th iterate is p / 3^e with e = (3^n - 1)/2 + 1 and an integer p not
-- divisible by 3: the next numerator is p (3^(2e) - p^2) / 2 (the product is even, and not
-- divisible by 3), over 3^(3e - 1). So the reduced denominator is 3^e.

namespace A134799

open OMA.S_oeis_a134799

lemma key (n : ℕ) : ∃ p : ℤ, ¬ (3 : ℤ) ∣ p ∧
    iterate n = (p : ℚ) / ((3 ^ ((3 ^ n - 1) / 2 + 1) : ℤ) : ℚ) := by
  induction n with
  | zero =>
    refine ⟨1, by norm_num, ?_⟩
    show (1 / 3 : ℚ) = _
    norm_num
  | succ n ih =>
    obtain ⟨p, hp3, hp⟩ := ih
    obtain ⟨e, he⟩ : ∃ e, e = (3 ^ n - 1) / 2 + 1 := ⟨_, rfl⟩
    have he' : (3 ^ (n + 1) - 1) / 2 + 1 = 3 * e - 1 := by
      have hodd : 3 ^ n % 2 = 1 := Nat.odd_iff.mp (Odd.pow (by decide))
      have h3 : 3 ^ (n + 1) = 3 * 3 ^ n := by ring
      omega
    have he1 : 1 ≤ e := by omega
    rw [← he] at hp
    have heven : (2 : ℤ) ∣ p * (3 ^ (2 * e) - p ^ 2) := by
      rcases Int.even_or_odd p with hpe | hpo
      · exact (hpe.mul_right _).two_dvd
      · have h1 : Odd ((3 : ℤ) ^ (2 * e)) := Odd.pow (by decide)
        have h2 : Even ((3 : ℤ) ^ (2 * e) - p ^ 2) := h1.sub_odd hpo.pow
        exact (h2.mul_left _).two_dvd
    obtain ⟨p', hp'⟩ := heven
    refine ⟨p', ?_, ?_⟩
    · intro h3
      have h4 : (3 : ℤ) ∣ p * (3 ^ (2 * e) - p ^ 2) := by
        rw [hp']; exact Dvd.dvd.mul_left h3 2
      rcases (Int.prime_three.dvd_mul).mp h4 with h | h
      · exact hp3 h
      · have h5 : (3 : ℤ) ∣ 3 ^ (2 * e) := dvd_pow_self 3 (by omega)
        have h6 : (3 : ℤ) ∣ p ^ 2 := by
          have h7 := dvd_sub h5 h
          rwa [sub_sub_cancel] at h7
        exact hp3 (Int.prime_three.dvd_of_dvd_pow h6)
    · rw [he', show iterate (n + 1) = (3 / 2) * iterate n * (1 - iterate n ^ 2) from rfl, hp]
      have hE : ((3 : ℚ)) ^ e ≠ 0 := by positivity
      have hq : (p : ℚ) * (((3 : ℚ) ^ e) ^ 2 - (p : ℚ) ^ 2) = 2 * p' := by
        have h1 : ((3 : ℚ) ^ e) ^ 2 = (3 : ℚ) ^ (2 * e) := by rw [← pow_mul, mul_comm]
        rw [h1]
        exact_mod_cast hp'
      have hpow : (3 : ℚ) ^ (3 * e - 1) = ((3 : ℚ) ^ e) ^ 3 / 3 := by
        have h1 : (3 : ℚ) ^ (3 * e - 1) * 3 = ((3 : ℚ) ^ e) ^ 3 := by
          rw [← pow_succ, ← pow_mul]
          congr 1
          omega
        rw [← h1]
        field_simp
      push_cast
      rw [hpow]
      calc 3 / 2 * ((p : ℚ) / 3 ^ e) * (1 - ((p : ℚ) / 3 ^ e) ^ 2)
          = ((p : ℚ) * (((3 : ℚ) ^ e) ^ 2 - (p : ℚ) ^ 2)) / (2 * ((3 : ℚ) ^ e) ^ 3) * 3 := by
            field_simp
        _ = (2 * (p' : ℚ)) / (2 * ((3 : ℚ) ^ e) ^ 3) * 3 := by rw [hq]
        _ = (p' : ℚ) / (((3 : ℚ) ^ e) ^ 3 / 3) := by
            field_simp

end A134799

theorem OMA.solution : type_of% @OMA.S_oeis_a134799.main := by
  intro n
  obtain ⟨p, hp3, hp⟩ := A134799.key n
  have h3 : ¬ (3 : ℕ) ∣ p.natAbs := fun h => hp3 (Int.natCast_dvd.mpr h)
  have hcop : Nat.Coprime p.natAbs ((3 ^ ((3 ^ n - 1) / 2 + 1) : ℤ)).natAbs := by
    rw [Int.natAbs_pow]
    exact Nat.Coprime.pow_right _
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm
  have hden := Rat.den_div_eq_of_coprime (a := p) (b := (3 ^ ((3 ^ n - 1) / 2 + 1) : ℤ))
    (by positivity) hcop
  rw [hp]
  unfold OMA.S_oeis_a134799.term
  have h4 : ((3 * 3 ^ ((3 ^ n - 1) / 2) : ℕ) : ℤ) = 3 ^ ((3 ^ n - 1) / 2 + 1) := by
    push_cast; ring
  exact_mod_cast hden.trans h4.symm
