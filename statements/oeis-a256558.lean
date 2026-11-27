import Mathlib

/-!
# A256558: Number of ways to write n = p + floor(k*(k+1)/4), where p is a prime and k is a positive integer.

Source: https://oeis.org/A256558
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A256558):
(i) `a(n) > 0` for all `n > 1`.
(ii) For any integer `m > 4` not equal to 12, each integer `n > 1` can be written as
`p + floor((k^2 - 1)/m)`, where `p` is a prime and `k` is a positive integer.

Formalization notes:
* `floor` of a quotient of natural numbers is natural-number division in `ℕ`; for `k ≥ 1`,
  `k ^ 2 - 1` in `ℕ` is the integer `k^2 - 1`.
* With these definitions the number of representations in (i) for `n = 1, ..., 20` is
  0, 1, 2, 1, 2, 2, 2, 3, 1, 3, 1, 4, 2, 3, 1, 3, 3, 3, 2, 4 (data of A256558), and part (ii)
  holds for `2 ≤ n < 602` and `m ∈ {5, 6, 7, 8, 9, 10, 11, 13}`.
-/

namespace OMA.S_oeis_a256558

/-- Sun's conjecture, parts (i) and (ii). -/
theorem main :
    (∀ n : ℕ, 1 < n → ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ n = p + k * (k + 1) / 4) ∧
      ∀ m : ℕ, 4 < m → m ≠ 12 → ∀ n : ℕ, 1 < n →
        ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ n = p + (k ^ 2 - 1) / m := by
  sorry

end OMA.S_oeis_a256558
