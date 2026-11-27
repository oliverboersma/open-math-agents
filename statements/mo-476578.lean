import Mathlib

/-!
# MathOverflow 476578: is `{σ(n)/φ(n) : n ≥ 1}` the set of all rationals `r ≥ 1`?

Source: https://mathoverflow.net/questions/476578
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question (Zhi-Wei Sun): with `σ(n)` the sum of the positive divisors of `n` and `φ` Euler's
totient function, let `S = {σ(n)/φ(n) : n ∈ ℤ_{≥1}}`. Is it true that `S = {r ∈ ℚ : r ≥ 1}`?
The asker conjectures that it is (all `a/b` with `36 ≥ a ≥ b ≥ 1` were found in `S`).

We state the affirmative answer (a disproof of `main` answers the question negatively).

Conventions: `σ(n)` is `ArithmeticFunction.sigma 1 n` and `φ(n)` is `Nat.totient n`; the quotient
is taken in `ℚ`, and `φ(n) ≥ 1` for `n ≥ 1`, so there is no division by zero. The inclusion
`S ⊆ {r ≥ 1}` is the easy half (`σ(n) ≥ n ≥ φ(n)`); the content is the reverse inclusion.
-/

namespace OMA.S_mo_476578

/-- `S = {σ(n)/φ(n) : n ≥ 1}` as a set of rationals. -/
def S : Set ℚ :=
  {r | ∃ n : ℕ, 0 < n ∧ r = (ArithmeticFunction.sigma 1 n : ℚ) / (n.totient : ℚ)}

/-- Sun's conjecture: `S` is exactly the set of rationals `r ≥ 1`. -/
theorem main : S = {r : ℚ | 1 ≤ r} := by
  sorry

end OMA.S_mo_476578
