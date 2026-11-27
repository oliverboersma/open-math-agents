import OMAReductions.R_OeisA63880_mod_216_of_a_R1

-- Reduction OeisA63880.mod_216_of_a.R1.H3.R1 of step OeisA63880.mod_216_of_a.R1.H3
-- Credit: @Ciphore

open OeisA63880
open scoped ArithmeticFunction.sigma

namespace OMA.R_OeisA63880_mod_216_of_a_R1_H3_R1

/-- The exponent of `3` cannot vanish in an odd `10/7` ratio instance. -/
def H1 : Prop := ∀ m : ℕ, Odd m → 7 * σ 1 m = 10 * usigma m →
  m.factorization 3 ≠ 0

/-- The exponent of `3` cannot be one in an odd `10/7` ratio instance. -/
def H2 : Prop := ∀ m : ℕ, Odd m → 7 * σ 1 m = 10 * usigma m →
  m.factorization 3 ≠ 1

/-- The exponent of `3` cannot be two in an odd `10/7` ratio instance. -/
def H3 : Prop := ∀ m : ℕ, Odd m → 7 * σ 1 m = 10 * usigma m →
  m.factorization 3 ≠ 2

theorem main : H1 → H2 → H3 → OMA.R_OeisA63880_mod_216_of_a_R1.H3 := by
  intro h0 h1 h2 m ho hr
  have hm : m ≠ 0 := by
    obtain ⟨k, hk⟩ := ho
    omega
  have e0 := h0 m ho hr
  have e1 := h1 m ho hr
  have e2 := h2 m ho hr
  have le : 3 ≤ m.factorization 3 := by omega
  exact ((show Nat.Prime 3 by norm_num).pow_dvd_iff_le_factorization hm).2 le

end OMA.R_OeisA63880_mod_216_of_a_R1_H3_R1
