import Mathlib

/-!
# Is there always one integer between these two rational numbers?

Source: https://mathoverflow.net/questions/280192/is-there-always-one-integer-between-these-two-rational-numbers
Credit: @mgv27

It appears that for each integer $k \geq 2$ there is always one integer $c$ satisfying
$$\frac{3^k-2^k}{2^k-1} < c \leq \frac{3^k-1}{2^k}.$$
Can this be proved?

Formalization notes:
* `main` states the expected "yes": for every `k ≥ 2` some integer `c` lies in the half-open
  interval `((3^k - 2^k)/(2^k - 1), (3^k - 1)/2^k]`, computed in `ℚ`.
* Writing `3^k = q 2^k + r` with `0 ≤ r < 2^k` (so `q = ⌊(3/2)^k⌋` is the only candidate), the
  condition is equivalent to `q + r < 2^k`, i.e. `2^k {(3/2)^k} + ⌊(3/2)^k⌋ ≤ 2^k - 1`.
  This is the classical open condition from the ideal Waring problem (`g(k) = 2^k + q - 2`);
  Mahler showed only finitely many `k` can fail, non-effectively. Verified numerically for
  `2 ≤ k < 3000`.
-/

namespace OMA.S_mo_280192

/-- The lower (strict) endpoint `(3^k - 2^k) / (2^k - 1)`. -/
def lower (k : ℕ) : ℚ := ((3 : ℚ) ^ k - 2 ^ k) / (2 ^ k - 1)

/-- The upper (inclusive) endpoint `(3^k - 1) / 2^k`. -/
def upper (k : ℕ) : ℚ := ((3 : ℚ) ^ k - 1) / 2 ^ k

/-- For every `k ≥ 2` there is an integer `c` with `lower k < c ≤ upper k`. -/
theorem main : ∀ k : ℕ, 2 ≤ k → ∃ c : ℤ, lower k < c ∧ (c : ℚ) ≤ upper k := by
  sorry

end OMA.S_mo_280192
