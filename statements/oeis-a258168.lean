import Mathlib

/-!
# A258168: Number of ways to write n as floor((p^2+q)/5) with p and q both prime.

Source: https://oeis.org/A258168
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A258168): Let `n` be any positive integer. Then `a(n) > 0`.
Moreover, one of the four consecutive numbers `5n, 5n+1, 5n+2, 5n+3` can be written as `p^2 + q`
with `p` and `q` both prime.

Formalization notes:
* `floor((p^2 + q)/5)` is natural-number division in `ℕ`.
* The second part (which implies the first) is stated separately, as in the source.
* With this definition `a(1), ..., a(8)` = 3, 4, 3, 4, 5, 4, 4, 4 (data of A258168), and the second
  part holds for `1 ≤ n ≤ 1500`.
-/

namespace OMA.S_oeis_a258168

/-- Sun's conjecture, both parts. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ (p ^ 2 + q) / 5 = n) ∧
      ∀ n : ℕ, 1 ≤ n → ∃ i < 4, ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 5 * n + i = p ^ 2 + q := by
  sorry

end OMA.S_oeis_a258168
