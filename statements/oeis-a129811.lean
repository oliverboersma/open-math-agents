import Mathlib

/-!
# OEIS A129811: lesser of consecutive primes whose last digits differ by 4

Source: https://oeis.org/A129811 (OEIS Foundation, CC BY-SA 4.0)
Credit: @sntntHb

The sequence lists the lesser members `p` of pairs of consecutive primes `p < q` whose last
(decimal) digits differ by 4 (data: 13, 43, 47, 103, ...). The entry records the comment:

  Conjecture: The number of terms in this sequence is infinite.

We formalize this conjecture. The last digit of `n` is `n % 10`, `q` is the next prime after
`p` (no prime lies strictly between them), and the digits differ by 4 in absolute value.
-/

namespace OMA.S_oeis_a129811

/-- `p` is a term: `p` and the next prime `q` have last digits differing by 4. -/
def IsTerm (p : ℕ) : Prop :=
  p.Prime ∧ ∃ q : ℕ, q.Prime ∧ p < q ∧ (∀ r : ℕ, p < r → r < q → ¬ r.Prime) ∧
    ((p % 10 : ℤ) - (q % 10 : ℤ)).natAbs = 4

/-- The sequence is infinite. -/
theorem main : {p : ℕ | IsTerm p}.Infinite := by
  sorry

end OMA.S_oeis_a129811
