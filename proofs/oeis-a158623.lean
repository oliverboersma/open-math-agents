import OMAStatements.S_oeis_a158623

-- Problem: oeis-a158623, recurrence for the denominators of the product of (k^3-1)/(k^3+1).
-- Credit: @justusklocke-cloud (the owner of the agent is credited as the solver)
--
-- The product telescopes to 2 (m^2 + m + 1) / (3 m (m + 1)). Since m^2 + m + 1 = m (m + 1) + 1
-- is coprime to m (m + 1) and divisible by 3 exactly when m = 1 mod 3, the reduced denominator
-- is m (m + 1) / 2 for m = 1 mod 3 and 3 m (m + 1) / 2 otherwise. On each residue class mod 3
-- this is a quadratic polynomial, so its third difference with step 3 vanishes.

namespace A158623

open OMA.S_oeis_a158623

lemma fraction_closed (m : ℕ) (hm : 1 ≤ m) :
    fraction m = (2 * ((m : ℚ) ^ 2 + m + 1)) / (3 * m * (m + 1)) := by
  induction m, hm using Nat.le_induction with
  | base =>
    unfold fraction
    rw [Finset.Icc_eq_empty (by norm_num), Finset.prod_empty]
    norm_num
  | succ k hk ih =>
    unfold fraction at ih ⊢
    rw [Finset.prod_Icc_succ_top (by omega), ih]
    have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h1 : (k : ℚ) + 1 ≠ 0 := by positivity
    have h2 : (k : ℚ) + 1 + 1 ≠ 0 := by positivity
    have h3 : ((k : ℚ) + 1) ^ 3 + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring

lemma coprime_core (m : ℕ) : Nat.Coprime (m ^ 2 + m + 1) (m * (m + 1)) :=
  Nat.isCoprime_iff_coprime.mp ⟨1, -1, by push_cast; ring⟩

lemma den_of (m : ℕ) (hm : 1 ≤ m) (A B : ℕ) (hB : 0 < B) (hcop : Nat.Coprime A B)
    (hAB : 2 * (m ^ 2 + m + 1) * B = A * (3 * (m * (m + 1)))) : term m = B := by
  have hfrac : fraction m = ((A : ℤ) : ℚ) / ((B : ℤ) : ℚ) := by
    rw [fraction_closed m hm]
    have hm0 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hB0 : (B : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hB.ne'
    have hq : (2 : ℚ) * ((m : ℚ) ^ 2 + m + 1) * B = A * (3 * (m * (m + 1))) := by
      exact_mod_cast hAB
    push_cast
    rw [div_eq_div_iff (by positivity) hB0]
    linear_combination hq
  have hden := Rat.den_div_eq_of_coprime (a := (A : ℤ)) (b := (B : ℤ)) (by exact_mod_cast hB)
    (by simpa using hcop)
  unfold term
  rw [hfrac]
  exact_mod_cast hden

lemma two_tri (m : ℕ) : 2 * (m * (m + 1) / 2) = m * (m + 1) :=
  Nat.mul_div_cancel' (Nat.even_mul_succ_self m).two_dvd

lemma term_formula (m : ℕ) (hm : 1 ≤ m) :
    (m % 3 = 1 → 2 * term m = m * (m + 1)) ∧
      (m % 3 ≠ 1 → 2 * term m = 3 * (m * (m + 1))) := by
  have hT2 := two_tri m
  obtain ⟨T, hT⟩ : ∃ T, T = m * (m + 1) / 2 := ⟨_, rfl⟩
  rw [← hT] at hT2
  have hTpos : 0 < T := by
    have h2 : 1 * 2 ≤ m * (m + 1) := Nat.mul_le_mul hm (by omega)
    omega
  have hTdvd : T ∣ m * (m + 1) := ⟨2, by rw [← hT2]; ring⟩
  have hcore := coprime_core m
  constructor
  · intro h
    obtain ⟨j, hj⟩ : ∃ j, m = 3 * j + 1 := ⟨m / 3, by omega⟩
    have hP : m ^ 2 + m + 1 = 3 * (3 * j ^ 2 + 3 * j + 1) := by rw [hj]; ring
    have hcop : Nat.Coprime (3 * j ^ 2 + 3 * j + 1) T :=
      (hcore.coprime_dvd_left ⟨3, by rw [hP]; ring⟩).coprime_dvd_right hTdvd
    have ht := den_of m hm (3 * j ^ 2 + 3 * j + 1) T hTpos hcop (by rw [hP, ← hT2]; ring)
    rw [ht, hT2]
  · intro h
    have h3 : ¬ 3 ∣ m ^ 2 + m + 1 := by
      rcases (by omega : m % 3 = 0 ∨ m % 3 = 2) with h0 | h2
      · obtain ⟨j, hj⟩ : ∃ j, m = 3 * j := ⟨m / 3, by omega⟩
        have h4 : m ^ 2 + m + 1 = 3 * (3 * j ^ 2 + j) + 1 := by rw [hj]; ring
        omega
      · obtain ⟨j, hj⟩ : ∃ j, m = 3 * j + 2 := ⟨m / 3, by omega⟩
        have h4 : m ^ 2 + m + 1 = 3 * (3 * j ^ 2 + 5 * j + 2) + 1 := by rw [hj]; ring
        omega
    have hc3 : Nat.Coprime (m ^ 2 + m + 1) 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm
    have hcop : Nat.Coprime (m ^ 2 + m + 1) (3 * T) :=
      hc3.mul_right (hcore.coprime_dvd_right hTdvd)
    have ht := den_of m hm (m ^ 2 + m + 1) (3 * T) (by omega) hcop (by rw [← hT2]; ring)
    rw [ht]; omega

end A158623

theorem OMA.solution : type_of% @OMA.S_oeis_a158623.main := by
  intro n hn
  have f0 := A158623.term_formula n (by omega)
  have f3 := A158623.term_formula (n + 3) (by omega)
  have f6 := A158623.term_formula (n + 6) (by omega)
  have f9 := A158623.term_formula (n + 9) (by omega)
  by_cases h : n % 3 = 1
  · have e0 := f0.1 h
    have e3 := f3.1 (by omega)
    have e6 := f6.1 (by omega)
    have e9 := f9.1 (by omega)
    zify at e0 e3 e6 e9
    have key : (2 : ℤ) * ((OMA.S_oeis_a158623.term (n + 9) : ℤ) -
        (3 * (OMA.S_oeis_a158623.term (n + 6) : ℤ) - 3 * (OMA.S_oeis_a158623.term (n + 3) : ℤ)
          + (OMA.S_oeis_a158623.term n : ℤ))) = 0 := by
      linear_combination e9 - 3 * e6 + 3 * e3 - e0
    omega
  · have e0 := f0.2 h
    have e3 := f3.2 (by omega)
    have e6 := f6.2 (by omega)
    have e9 := f9.2 (by omega)
    zify at e0 e3 e6 e9
    have key : (2 : ℤ) * ((OMA.S_oeis_a158623.term (n + 9) : ℤ) -
        (3 * (OMA.S_oeis_a158623.term (n + 6) : ℤ) - 3 * (OMA.S_oeis_a158623.term (n + 3) : ℤ)
          + (OMA.S_oeis_a158623.term n : ℤ))) = 0 := by
      linear_combination e9 - 3 * e6 + 3 * e3 - e0
    omega
