import Mathlib

/-!
# Marshall Hall's conjecture

Source: https://en.wikipedia.org/wiki/Marshall_Hall's_conjecture
(redirects to https://en.wikipedia.org/wiki/Hall's_conjecture)
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

The source gives two forms. The original strong form (Hall, 1970): there is a positive constant
`C` with `|y ^ 2 - x ^ 3| > C |x| ^ (1/2)` for all integers `x, y` with `y ^ 2 ≠ x ^ 3`; the
source says it has never been disproved but is no longer believed to be true, and that the term
Hall's conjecture now generally means the weak form (Stark–Trotter, around 1980):
for any `ε > 0` there is some constant `c(ε)` such that for any integers `x` and `y` with
`y ^ 2 ≠ x ^ 3`, `|y ^ 2 - x ^ 3| > c(ε) |x| ^ (1/2 - ε)`.

`main` states the weak form, following the source's remark on current usage.

Conventions:
* `x, y : ℤ`; the inequality is read in `ℝ`, with `|x| ^ (1/2 - ε)` the real power `Real.rpow`;
* the constant `c(ε)` is required to be positive (with `c = 0` the statement would be trivial);
* `ε` ranges over all positive reals. For `x = 0` Mathlib's `0 ^ t` is `0` for `t ≠ 0` and `1`
  for `t = 0`; since `y ^ 2 ≠ 0` forces `|y ^ 2| ≥ 1`, this costs nothing once `c < 1`, so the
  junk value does not make the statement trivially true or false.
-/

namespace OMA.S_wp_marshall_hall_s_conjecture

theorem main : ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧
    ∀ x y : ℤ, y ^ 2 ≠ x ^ 3 →
      c * (|(x : ℝ)|) ^ ((1 : ℝ) / 2 - ε) < |((y : ℝ) ^ 2 - (x : ℝ) ^ 3)| := by
  sorry

end OMA.S_wp_marshall_hall_s_conjecture
