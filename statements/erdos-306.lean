import Mathlib

/-!
# Erdős Problem 306

Source: https://www.erdosproblems.com/306
Credit: @mattdorman

The source asks: let `a/b ∈ ℚ_{>0}` with `b` squarefree. Are there integers `1 < n₁ < ⋯ < nₖ`,
each the product of two distinct primes, such that `a/b = 1/n₁ + ⋯ + 1/nₖ`?

Reading used here: `a/b` is a positive rational in lowest terms, so the condition is that its
reduced denominator `q.den` is squarefree (this condition is necessary, since a sum of reciprocals
of squarefree integers has squarefree reduced denominator). The integers `nᵢ` are distinct, which
a `Finset` records; each is a product of two distinct primes, hence automatically `> 1`; and
`k ≥ 1` is forced by `q > 0`. The statement below is the affirmative answer, for every such `q`.
-/

namespace OMA.S_erdos_306

/-- `n` is the product of two distinct primes. -/
def IsProductOfTwoDistinctPrimes (n : ℕ) : Prop :=
  ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ p ≠ r ∧ n = p * r

theorem main :
    ∀ q : ℚ, 0 < q → Squarefree q.den →
      ∃ S : Finset ℕ, (∀ n ∈ S, IsProductOfTwoDistinctPrimes n) ∧
        ∑ n ∈ S, (1 / (n : ℚ)) = q := by
  sorry

end OMA.S_erdos_306
