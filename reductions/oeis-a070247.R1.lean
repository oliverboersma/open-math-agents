import OMAStatements.S_oeis_a070247

/-! A decimal palindrome of digit sum two is either 2 or a string of the form
100...001. An odd prime divisor of the gap exponent gives a proper factor.
The remaining primality tests are for generalized Fermat numbers in base ten. -/

namespace OMA.R_oeis_a070247_R1

def H1 : Prop := ∀ k : ℕ, 2 ≤ k → k ≤ 14 → ¬ Nat.Prime (10 ^ (2 ^ k) + 1)

def H2 : Prop := ∀ k : ℕ, 14 < k → ¬ Nat.Prime (10 ^ (2 ^ k) + 1)

lemma ofDigits_zero_sum (l : List ℕ) (h : l.sum = 0) : Nat.ofDigits 10 l = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.sum_cons] at h
    have ha : a = 0 := by omega
    have ht : t.sum = 0 := by omega
    simp [Nat.ofDigits_cons, ha, ih ht]

lemma digit_shape {p : ℕ} (hp : p.Prime) (pal : (Nat.digits 10 p).reverse = Nat.digits 10 p)
    (sum : (Nat.digits 10 p).sum = 2) : p = 2 ∨ ∃ m : ℕ, 0 < m ∧ p = 10 ^ m + 1 := by
  have value := Nat.ofDigits_digits 10 p
  have last := Nat.getLast_digit_ne_zero 10 hp.ne_zero
  cases hd : Nat.digits 10 p with
  | nil => simp [hd] at sum
  | cons a t =>
    rw [hd] at pal sum value
    cases hrev : t.reverse with
    | nil =>
      have ht : t = [] := by simpa using congrArg List.reverse hrev
      simp [ht] at sum
      simpa [ht, sum] using Or.inl value.symm
    | cons b u =>
      have ht : t = u.reverse ++ [b] := by simpa using congrArg List.reverse hrev
      have hab : b = a := by
        have e := congrArg List.head? pal
        simpa [List.reverse_cons, hrev] using e
      subst b
      have hnz : a ≠ 0 := by
        simpa [hd, ht] using last
      have total : a + u.sum + a = 2 := by simpa [ht, add_assoc] using sum
      have ha : a = 1 := by omega
      have hu : u.reverse.sum = 0 := by rw [List.sum_reverse]; omega
      right
      refine ⟨u.length + 1, by omega, ?_⟩
      simpa [ht, ha, Nat.ofDigits_cons, Nat.ofDigits_append, ofDigits_zero_sum _ hu,
        pow_succ, Nat.mul_comm, Nat.add_comm] using value.symm

lemma prime_exponent {m : ℕ} (hm : 0 < m) (hp : Nat.Prime (10 ^ m + 1)) : ∃ k, m = 2 ^ k := by
  rcases m.eq_two_pow_or_exists_odd_prime_and_dvd with h | ⟨q, hq, ⟨u, rfl⟩, odd⟩
  · exact h
  · exfalso
    have hu : 0 < u := by by_contra! hz; simp [show u = 0 by omega] at hm
    have factor : 10 ^ u + 1 ∣ 10 ^ (q * u) + 1 := by
      rw [Nat.mul_comm q u, pow_mul]
      simpa using odd.nat_add_dvd_pow_add_pow (10 ^ u) 1
    have pos : 0 < 10 ^ u := by positivity
    have smaller : u < q * u := by nlinarith [hq.two_le]
    have lt : (10 : ℕ) ^ u < 10 ^ (q * u) := Nat.pow_lt_pow_right (by decide) smaller
    rcases (Nat.dvd_prime hp).mp factor with h | h <;> omega

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a070247.main := by
  intro finite tail
  ext p
  change (p.Prime ∧ (Nat.digits 10 p).reverse = Nat.digits 10 p ∧
    (Nat.digits 10 p).sum = 2) ↔ p = 2 ∨ p = 11 ∨ p = 101
  constructor
  · rintro ⟨hp, pal, sum⟩
    rcases digit_shape hp pal sum with h | ⟨m, hm, rfl⟩
    · exact Or.inl h
    obtain ⟨k, rfl⟩ := prime_exponent hm hp
    by_cases h : k ≤ 1
    · interval_cases k <;> decide
    · by_cases h' : k ≤ 14
      · exact (finite k (by omega) h' hp).elim
      · exact (tail k (by omega) hp).elim
  · rintro (rfl | rfl | rfl) <;> decide

end OMA.R_oeis_a070247_R1
