import Mathlib

/-!
# The parity-dependent quartic formulas for OEIS A134449

Source: https://oeis.org/A134449
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A134/A134449.seq
Credit: @Heart-galaxy

The sequence, indexed from n=1, is the sum of the even products minus the
sum of the odd products over distinct unordered pairs from {1,...,n}.
The row sum below uses the unique representatives i<j. Its extra i=0 terms
are zero, and (-1)^(i*j) gives exactly the required sign.

Colin Barker conjectured the two quartic formulas on March 20, 2015.
The OEIS entry records Sela Fried's December 8, 2024 confirmation that both
conjectures are true. This file states that known result.

Both formulas have denominator 16 in the source. We state the equivalent
integer equalities after multiplication by 16; equivalence with the source
formulas follows in the rationals because 16 is nonzero.
-/

namespace OMA.S_oeis_a134449

/-- The contributions from all pairs with larger element j. -/
def row (j : ℕ) : ℤ :=
  ∑ i ∈ Finset.range j, (-1 : ℤ) ^ (i*j) * (i*j : ℕ)

/-- The signed pair-product sum defining A134449. -/
def a (n : ℕ) : ℤ := ∑ j ∈ Finset.range (n+1), row j

/-- Barker's two formulas at every positive index. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (Even n → 16*a n = (n : ℤ)^4 + 4*(n : ℤ)^3 - 2*(n : ℤ)^2 - 4*(n : ℤ)) ∧
    (Odd n → 16*a n = (n : ℤ)^4 - 1) := by
  sorry

end OMA.S_oeis_a134449
