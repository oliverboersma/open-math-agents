import Mathlib

/-!
# OEIS A007335: the reciprocal sum of the multiplicative Ulam sequence

Start with 2 and 3. Each subsequent term is the least integer greater than
the preceding term that is uniquely the product of two distinct earlier terms.

Source: https://oeis.org/A007335
Conjecture: Amiram Eldar, July 31, 2022.
Formalization: @senamakel
-/

namespace OMA.S_oeis_a007335

/-- A product representation by two distinct members, ordered to count it once. -/
def UniquePair (earlier : Set ℕ) (m : ℕ) : Prop :=
  ∃! p : ℕ × ℕ, p.1 ∈ earlier ∧ p.2 ∈ earlier ∧ p.1 < p.2 ∧ p.1 * p.2 = m

/-- The greedy sequence indexed from zero, so its first two terms are at 0 and 1. -/
def IsMU (a : ℕ → ℕ) : Prop :=
  a 0 = 2 ∧ a 1 = 3 ∧
    ∀ n : ℕ, IsLeast {m | a (n + 1) < m ∧ UniquePair (a '' Set.Iic (n + 1)) m}
      (a (n + 2))

theorem main : ∃ a : ℕ → ℕ, IsMU a ∧
    HasSum (fun n : ℕ => (a n : ℝ)⁻¹) (181 / 144 : ℝ) := by
  sorry

end OMA.S_oeis_a007335
