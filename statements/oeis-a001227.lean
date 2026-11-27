import Mathlib

/-!
# A001227: Number of odd divisors of n.

Source: https://oeis.org/A001227
Credit: @rot13maxi

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a001227

/-- A001227: the number of odd divisors of `n`. -/
def A001227 (n : ℕ) : ℕ :=
  ((Nat.divisors n).filter (fun d => Odd d)).card

/-- A067742: number of middle divisors of `n`, i.e. divisors in the
half-open interval `[sqrt(n/2), sqrt(n*2))`. -/
def A067742 (n : ℕ) : ℕ :=
  ((Nat.divisors n).filter (fun d => n ≤ 2 * d ^ 2 ∧ d ^ 2 < 2 * n)).card

/-- A131576: number of odd divisors of `n` greater than `sqrt(2*n)`,
equivalently the number of representations of `n` as a sum of an even
number of consecutive positive integers (OEIS comment by Hirschhorn). -/
def A131576 (n : ℕ) : ℕ :=
  ((Nat.divisors n).filter (fun d => Odd d ∧ 2 * n < d ^ 2)).card

/-- A082647: number of odd divisors of `n` less than `sqrt(2*n)`,
equivalently the number of representations of `n` as a sum of an odd
number of consecutive positive integers (OEIS comments). -/
def A082647 (n : ℕ) : ℕ :=
  ((Nat.divisors n).filter (fun d => Odd d ∧ d ^ 2 < 2 * n)).card

/-- Omar E. Pol's conjectures on A001227:
`a(n) = A067742(n) + 2*A131576(n) = A082647(n) + A131576(n)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    A001227 n = A067742 n + 2 * A131576 n ∧
    A001227 n = A082647 n + A131576 n := by
  sorry

end OMA.S_oeis_a001227
