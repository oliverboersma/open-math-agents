import OMAReductions.R_OeisA63880_mod_216_of_a_R1_H1_R2

-- Reduction OeisA63880.mod_216_of_a.R1.H1.R2.H2.R1 of step OeisA63880.mod_216_of_a.R1.H1.R2.H2
-- Credit: @Ciphore

namespace OMA.R_OeisA63880_mod_216_of_a_R1_H1_R2_H2_R1

/-- Every odd solution has a coprime “powerful core” obtained by deleting exactly the
prime factors of exponent one.  The point is that a prime occurring to exponent one
contributes the same factor `p+1` to both `σ` and `usigma`, so it cancels from the
defining equation. -/
def H1 : Prop := ∀ n : ℕ, Odd n → OeisA63880.A n →
  ∃ d : ℕ, d ∣ n ∧ Odd d ∧ OeisA63880.A d ∧
    (∀ q : ℕ, q.Prime → q ∣ d → 2 ≤ d.factorization q) ∧
    (∀ q : ℕ, q.Prime → q ∣ n → ¬ q ∣ d → n.factorization q = 1)

/-- The powerful-core case of the odd problem. -/
def H2 : Prop := ∀ d : ℕ, Odd d →
  (∀ q : ℕ, q.Prime → q ∣ d → 2 ≤ d.factorization q) → ¬ OeisA63880.A d

theorem main : H1 → H2 → OMA.R_OeisA63880_mod_216_of_a_R1_H1_R2.H2 := by
  intro hstrip hpowerful n ho _ hA
  obtain ⟨d, _, hod, hAd, hpow, _⟩ := hstrip n ho hA
  exact hpowerful d hod hpow hAd

end OMA.R_OeisA63880_mod_216_of_a_R1_H1_R2_H2_R1
