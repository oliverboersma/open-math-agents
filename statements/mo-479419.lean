import Mathlib

/-!
# MathOverflow 479419: is `2↑↑∞ + 3` divisible by a prime?

Source: https://mathoverflow.net/questions/479419
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question (hzy): with `a↑↑b` the power tower of `b` copies of `a`, the limit
`a↑↑∞ ≡ lim_{n→∞} a↑↑n (mod m)` exists for all positive integers `a, m` (the residues are
eventually constant; OEIS A245970). Is there a prime `p` with `2↑↑∞ ≡ -3 (mod p)`?

We state the affirmative answer (a disproof of `main` answers the question negatively).

Conventions:
* `tower2 n = 2↑↑n`, with `2↑↑0 = 1` and `2↑↑(n+1) = 2^(2↑↑n)` (so `2↑↑1 = 2`, `2↑↑2 = 4`).
* Since `2↑↑n mod p` is eventually constant with value `2↑↑∞ mod p`, the congruence
  `2↑↑∞ ≡ -3 (mod p)` holds iff `p ∣ 2↑↑n + 3` for all sufficiently large `n`. We state the
  latter, which needs no separate definition of the limit.
-/

namespace OMA.S_mo_479419

/-- The power tower `2↑↑n`. -/
def tower2 : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 ^ tower2 n

/-- There is a prime `p` with `2↑↑∞ ≡ -3 (mod p)`, i.e. `p ∣ 2↑↑n + 3` for all large `n`. -/
theorem main : ∃ p : ℕ, p.Prime ∧ ∀ᶠ n in Filter.atTop, p ∣ tower2 n + 3 := by
  sorry

end OMA.S_mo_479419
