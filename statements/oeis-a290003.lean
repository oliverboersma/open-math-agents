import Mathlib

/-!
# OEIS A290003: the coefficients at prime-successor indices

Source: https://oeis.org/A290003
Credit: @Heart-galaxy

The sequence has offset 0 and starts a(0)=1, a(1)=-1. For n>=2 we use the independent
explicit divisor-sum formula recorded by Peter Bala on March 2, 2025. This formula
is given in the source's Formula and Maple sections. A binomial coefficient with
negative lower index is zero: in the d=1 term the first binomial therefore vanishes.
The guard below implements this convention before using natural subtraction.

The conjecture a(p+1)=1 for prime p>3 is reported to follow from that formula.
This is a known result. The formal target retains exactly the recorded prime range.
-/

namespace OMA.S_oeis_a290003

/-- The first binomial in Bala's formula, with the negative lower-index convention. -/
def firstChoose (m d : ℕ) : ℕ := if 2 ≤ d then Nat.choose m (d - 2) else 0

def term (n d : ℕ) : ℤ :=
  (-1 : ℤ) ^ (d - 1) *
    ((firstChoose ((n - 1) / d) d + Nat.choose ((n + d - 1) / d) (d - 1) : ℕ) : ℤ)

/-- The sequence by its two initial values and the source's independent divisor formula. -/
def a (n : ℕ) : ℤ :=
  if n = 0 then 1 else if n = 1 then -1 else ∑ d ∈ (n - 1).divisors, term n d

/-- The original prime-successor-index conjecture. -/
theorem main : ∀ p : ℕ, p.Prime → 3 < p → a (p + 1) = 1 := by
  sorry

end OMA.S_oeis_a290003
