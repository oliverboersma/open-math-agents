import Mathlib

/-!
# A387947: Number of prime pairs {p, q} with n >= p > q such that (p-1)^2 == (q-1)^2 (mod n).

Source: https://oeis.org/A387947
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A387947): `a(n) > 0` except for `n = 1, 2, 4, 9, 25`.

Formalization notes:
* Stated as an equivalence for every `n ≥ 1` (offset 1): there are primes `q < p ≤ n` with
  `(p-1)^2 ≡ (q-1)^2 (mod n)` iff `n ∉ {1, 2, 4, 9, 25}`. For `n = 0` the source has no term.
* With this definition `a(1), ..., a(25)` = 0, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1,
  6, 2, 3, 1, 5, 0 (data of A387947), and the `n < 601` with `a(n) = 0` are 1, 2, 4, 9, 25.
-/

namespace OMA.S_oeis_a387947

/-- Sun's conjecture of A387947. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    ((∃ p q : ℕ, p.Prime ∧ q.Prime ∧ q < p ∧ p ≤ n ∧ (p - 1) ^ 2 ≡ (q - 1) ^ 2 [MOD n]) ↔
      n ∉ ({1, 2, 4, 9, 25} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a387947
