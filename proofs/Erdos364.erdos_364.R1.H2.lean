import OMAReductions.R_Erdos364_erdos_364_R1

-- Three consecutive powerful numbers n, n + 1, n + 2 need n = 0, 7 or 8 mod 9.
-- Original Lean proof of the classical remark: exactly one of the three is a multiple of 3, and it must be a
-- multiple of 9. An elementary observation, not progress on the problem.

namespace OMA.E364b

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

theorem mod_nine (n : ℕ) (h0 : n % 9 ≠ 0) (h7 : n % 9 ≠ 7) (h8 : n % 9 ≠ 8) :
    ¬ (Nat.Powerful n ∧ Nat.Powerful (n + 1) ∧ Nat.Powerful (n + 2)) := by
  rintro ⟨p0, p1, p2⟩
  have hc : (n % 9 = 3 ∨ n % 9 = 6) ∨ ((n + 1) % 9 = 3 ∨ (n + 1) % 9 = 6) ∨
      ((n + 2) % 9 = 3 ∨ (n + 2) % 9 = 6) := by omega
  rcases hc with hc | hc | hc
  · exact not_powerful_three hc p0
  · exact not_powerful_three hc p1
  · exact not_powerful_three hc p2

end OMA.E364b

theorem OMA.solution : OMA.R_Erdos364_erdos_364_R1.H2 := by
  intro n h0 h7 h8
  exact OMA.E364b.mod_nine n h0 h7 h8
