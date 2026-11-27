import Mathlib

/-!
# Mathar's parity identity recorded in OEIS A002735

Source: https://oeis.org/A002735
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A002/A002735.seq
Credit: @Heart-galaxy

A002735 has offset 1. The source defines it as a(n)=b(2,n), where
b(m,1)=m^2, b(m,2*r)=Sum_{k=1..m+1} b(k,2*r-1), and
b(m,2*r+1)=m^2*b(m,2*r) for positive r. We implement that complete recursion
below, placing the stage argument first in B. Stage zero is an unused
convention and is never reached by the recurrence for positive stages.

Mathar conjectured a(2*n+1)=4*a(2*n) on February 3, 2025; Fried confirmed
it on December 8, 2025. We retain every index n>=1 for which both terms
are in the original offset-one sequence. The invalid comparison with a(0)
at n=0 is not asserted.
-/

namespace OMA.S_oeis_a002735

/-- Source array b(m,k), with the stage k as its first argument. -/
def B : ℕ → ℕ → ℕ
  | 0, _ => 0
  | 1, m => m^2
  | n+2, m => if (n+2)%2 = 0 then
      ∑ k ∈ Finset.range (m+1), B (n+1) (k+1)
    else m^2 * B (n+1) m

def a (n : ℕ) : ℕ := B n 2

theorem main : ∀ n : ℕ, 1 ≤ n → a (2*n+1) = 4*a (2*n) := by
  sorry

end OMA.S_oeis_a002735
