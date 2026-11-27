import OMAReductions.R_Erdos242_erdos_242_R1

/-! Split the remaining prime denominators at Mordell's six residue classes. -/

namespace OMA.R_Erdos242_erdos_242_R1_H1_R1

/-- The six residue classes left by Mordell's explicit identities. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → p%24 = 1 →
    (p%840 = 1 ∨ p%840 = 121 ∨ p%840 = 169 ∨ p%840 = 289 ∨ p%840 = 361 ∨ p%840 = 529) →
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (4/p : ℚ) = 1/x+1/y+1/z

/-- All other primes in the original residue class admit explicit expansions. -/
def H2 : Prop :=
  ∀ p : ℕ, p.Prime → p%24 = 1 →
    ¬ (p%840 = 1 ∨ p%840 = 121 ∨ p%840 = 169 ∨ p%840 = 289 ∨ p%840 = 361 ∨ p%840 = 529) →
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (4/p : ℚ) = 1/x+1/y+1/z

section Proof

theorem main : H1 → H2 → OMA.R_Erdos242_erdos_242_R1.H1 := by
  intro hSix hOther p hp h24
  by_cases h : p%840 = 1 ∨ p%840 = 121 ∨ p%840 = 169 ∨ p%840 = 289 ∨ p%840 = 361 ∨ p%840 = 529
  · exact hSix p hp h24 h
  · exact hOther p hp h24 h

end Proof

end OMA.R_Erdos242_erdos_242_R1_H1_R1
