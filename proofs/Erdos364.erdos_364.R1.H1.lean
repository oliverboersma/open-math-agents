import OMAReductions.R_Erdos364_erdos_364_R1

-- Three consecutive powerful numbers n, n + 1, n + 2 need n = 3 mod 4.
-- Original Lean proof of the classical remark: otherwise one of the three is 2 mod 4, and such a number is
-- divisible by 2 but not by 4. An elementary observation, not progress on the problem.

namespace OMA.E364a

lemma not_powerful_two {m : ℕ} (h : m % 4 = 2) : ¬ Nat.Powerful m := by
  intro hp
  have hmem : 2 ∈ m.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, by omega, by omega⟩
  have hd : 2 ^ 2 ∣ m := hp 2 hmem
  omega

lemma not_powerful_three {m : ℕ} (h : m % 9 = 3 ∨ m % 9 = 6) : ¬ Nat.Powerful m := by
  intro hp
  have hmem : 3 ∈ m.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_three, by omega, by omega⟩
  have hd : 3 ^ 2 ∣ m := hp 3 hmem
  omega

theorem mod_four (n : ℕ) (h : n % 4 ≠ 3) :
    ¬ (Nat.Powerful n ∧ Nat.Powerful (n + 1) ∧ Nat.Powerful (n + 2)) := by
  rintro ⟨h0, h1, h2⟩
  have hc : n % 4 = 2 ∨ (n + 1) % 4 = 2 ∨ (n + 2) % 4 = 2 := by omega
  rcases hc with hc | hc | hc
  · exact not_powerful_two hc h0
  · exact not_powerful_two hc h1
  · exact not_powerful_two hc h2

end OMA.E364a

theorem OMA.solution : OMA.R_Erdos364_erdos_364_R1.H1 := by
  intro n h
  exact OMA.E364a.mod_four n h
