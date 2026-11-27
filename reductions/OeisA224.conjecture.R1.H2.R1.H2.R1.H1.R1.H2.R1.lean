import OMAReductions.R_OeisA224_conjecture_R1_H2_R1_H2_R1_H1_R1

namespace OMA.R_OeisA224_conjecture_R1_H2_R1_H2_R1_H1_R1_H2_R1

def H1 : Prop := ∀ n : ℕ, Odd n → n.primeFactors.card = 4 → (∃ p ∈ n.primeFactors, p < 16 * (2 ^ n.primeFactors.card) ^ 3) → n ^ 2 ≡ 1 [MOD OeisA224.a n * (OeisA224.a n - 1)] → ∃ k : ℕ, 16 < k ∧ k < 256 ∧ n ^ 2 = k * OeisA224.a n * (OeisA224.a n - 1) + 1

def H2 : Prop := ∀ n k : ℕ, Odd n → n.primeFactors.card = 4 → (∃ p ∈ n.primeFactors, p < 16 * (2 ^ n.primeFactors.card) ^ 3) → 16 < k → k < 256 → n ^ 2 ≠ k * OeisA224.a n * (OeisA224.a n - 1) + 1

theorem main : H1 → H2 → OMA.R_OeisA224_conjecture_R1_H2_R1_H2_R1_H1_R1.H2 := by
  intro h1 h2 n hodd hcard hsmall hmod
  obtain ⟨k, hk1, hk2, heq⟩ := h1 n hodd hcard hsmall hmod
  exact h2 n k hodd hcard hsmall hk1 hk2 heq

end OMA.R_OeisA224_conjecture_R1_H2_R1_H2_R1_H1_R1_H2_R1
