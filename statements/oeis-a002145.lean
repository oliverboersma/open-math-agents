import Mathlib

/-!
# A002145: Primes of the form 4*k + 3.

Source: https://oeis.org/A002145
Credit: @ShoQo

Conjecture (Thomas Scheuerle, Feb 09 2023): a(n) for n > 4 can be written as a sum of 3 primes
of the form 4k+1, which would imply that primes of the form 4k+3 >= 23 can be decomposed into a
sum of 6 nonzero squares.

Formalization notes:
* The sequence has offset 1 and starts 3, 7, 11, 19, 23, .... `Nat.nth` is 0-indexed, so
  a(n) = `Nat.nth (fun p => p.Prime ∧ p % 4 = 3) (n - 1)` and "n > 4" becomes "index ≥ 4".
  Equivalently: every prime `p` with `p % 4 = 3` and `p ≥ 23`.
* The three primes need not be distinct (none of the source's wording asks for it).
* The "which would imply ..." clause is a consequence (Fermat: a prime `≡ 1 (mod 4)` is a sum
  of two nonzero squares), not a separate conjecture, so it is not stated.
-/

namespace OMA.S_oeis_a002145

/-- `p` is a sum of three primes, each of the form `4k + 1`. -/
def SumOfThreePrimesOneModFour (p : ℕ) : Prop :=
  ∃ q r s : ℕ, q.Prime ∧ r.Prime ∧ s.Prime ∧ q % 4 = 1 ∧ r % 4 = 1 ∧ s % 4 = 1 ∧ p = q + r + s

theorem main :
    ∀ n : ℕ, 4 ≤ n →
      SumOfThreePrimesOneModFour (Nat.nth (fun p => p.Prime ∧ p % 4 = 3) n) := by
  sorry

end OMA.S_oeis_a002145
