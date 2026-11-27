import Mathlib

/-!
# A257109: Number of ways to write n = 3*x^2 + y^2 + z^2, where x,y,z are nonnegative integers with gcd(3,x) = 1 and y <= z.

Source: https://oeis.org/A257109
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A257109):
(i) If `n` is not divisible by 3, then `a(n) > 0` except for
`n = 1, 2, 10, 26, 31, 34, 47, 59, 166, 278, 451`.
(ii) Any integer `n > 14986` not divisible by 3 can be written as `3(3x)^2 + y^2 + z^2` with
`x, y, z` integers.

Formalization notes:
* The order condition `y ≤ z` of the counting function does not affect existence.
* Part (i) is stated as an equivalence for every `n` not divisible by 3: `n` has a representation
  `3x^2 + y^2 + z^2` with `gcd(3, x) = 1` iff `n` is not one of the eleven exceptions.
* With this definition the counts for `n = 0, ..., 19` are 0, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 2, 2,
  1, 0, 2, 1, 0, 1 (data of A257109), and the `n < 3000` not divisible by 3 without a
  representation are exactly the eleven listed numbers.
-/

namespace OMA.S_oeis_a257109

/-- Sun's conjecture, parts (i) and (ii). -/
theorem main :
    (∀ n : ℕ, ¬ 3 ∣ n →
        ((∃ x y z : ℕ, Nat.gcd 3 x = 1 ∧ n = 3 * x ^ 2 + y ^ 2 + z ^ 2) ↔
          n ∉ ({1, 2, 10, 26, 31, 34, 47, 59, 166, 278, 451} : Finset ℕ))) ∧
      ∀ n : ℕ, 14986 < n → ¬ 3 ∣ n → ∃ x y z : ℤ, (n : ℤ) = 3 * (3 * x) ^ 2 + y ^ 2 + z ^ 2 := by
  sorry

end OMA.S_oeis_a257109
