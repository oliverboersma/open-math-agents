import OMAStatements.S_mo_439892

-- Reduction mo-439892.R1 of Is the Goldbach conjecture easier if we allow 1 as a prime?
-- Credit: @jared-jasinski
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_mo_439892_R1

def H1 : Prop :=
  OMA.S_mo_439892.GoldbachWith (fun p => p = 1 ∨ p.Prime) →
    ∀ p : ℕ, p.Prime → p % 6 = 1 → ¬ (p - 2).Prime →
      ∃ q r : ℕ, q.Prime ∧ r.Prime ∧ q + r = p + 1

def H2 : Prop :=
  OMA.S_mo_439892.GoldbachWith (fun p => p = 1 ∨ p.Prime) →
    ∀ p : ℕ, p.Prime → p % 6 = 5 → ¬ (p - 4).Prime →
      ∃ q r : ℕ, q.Prime ∧ r.Prime ∧ q + r = p + 1

lemma prime_mod_six_of_gt_three {p : ℕ} (hp : p.Prime) (h3 : 3 < p) :
    p % 6 = 1 ∨ p % 6 = 5 := by
  have h2 : ¬ 2 ∣ p := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h
    omega
  have h3d : ¬ 3 ∣ p := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h
    omega
  omega

lemma shifted_prime_goldbach (h1 : H1) (h2 : H2)
    (hG1 : OMA.S_mo_439892.GoldbachWith (fun p => p = 1 ∨ p.Prime))
    {p : ℕ} (hp : p.Prime) (heven : Even (p + 1)) :
    ∃ q r : ℕ, q.Prime ∧ r.Prime ∧ q + r = p + 1 := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    rcases heven with ⟨k, hk⟩
    omega
  have hp_ge3 : 3 ≤ p := by
    have := hp.two_le
    omega
  by_cases h3 : p = 3
  · subst h3
    exact ⟨2, 2, Nat.prime_two, Nat.prime_two, rfl⟩
  · have hgt3 : 3 < p := by omega
    rcases prime_mod_six_of_gt_three hp hgt3 with hmod1 | hmod5
    · by_cases htwin : (p - 2).Prime
      · exact ⟨3, p - 2, Nat.prime_three, htwin, by omega⟩
      · exact h1 hG1 p hp hmod1 htwin
    · by_cases h5 : p = 5
      · subst h5
        exact ⟨3, 3, Nat.prime_three, Nat.prime_three, rfl⟩
      · by_cases hcousin : (p - 4).Prime
        · exact ⟨5, p - 4, by decide, hcousin, by omega⟩
        · exact h2 hG1 p hp hmod5 hcousin

theorem main : H1 → H2 → type_of% @OMA.S_mo_439892.main := by
  intro h1 h2 hG1 n hn heven
  rcases hG1 n hn heven with ⟨a, b, ha, hb, hab⟩
  rcases ha with rfl | ha'
  · rcases hb with rfl | hb'
    · omega
    · subst hab
      rw [add_comm]
      exact shifted_prime_goldbach h1 h2 hG1 hb' (by simpa [add_comm] using heven)
  · rcases hb with rfl | hb'
    · subst hab
      exact shifted_prime_goldbach h1 h2 hG1 ha' heven
    · exact ⟨a, b, ha', hb', hab⟩

end OMA.R_mo_439892_R1
