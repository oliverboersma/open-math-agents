import Mathlib

/-!
Source: https://oeis.org/A094822
Source text: https://github.com/oeis/oeisdata/blob/main/seq/A094/A094822.seq
Related source: https://oeis.org/A046716
Credit: @Heart-galaxy

Expanding the defining e.g.f. exp(3x)/(1-3x)^(1/3) gives the exact integer
coefficient formula used below. The denominator's binomial-series coefficient
at i is q(i)/i!, where q(i)=Product_{r=0..i-1}(3r+1); multiplication by
exp(3x) then gives the finite sum over i+j=n.

Both assertions in the imported text are retained: Mathar's recurrence and
Bala's eventual periodicity modulo each positive integer. Bala records the
recurrence as proved on October 27, 2026, and states the periodicity there.
The offset is zero, so the recurrence's full common domain is n>=2.
-/

namespace OMA.S_oeis_a094822

def q (n : ℕ) : ℤ := (Finset.range n).prod (fun j => 3*(j:ℤ)+1)

def weight (n : ℕ) (ij : ℕ × ℕ) : ℤ :=
  (n.choose ij.1:ℤ)*((3:ℤ)^ij.2*q ij.1)

def a (n : ℕ) : ℤ := ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, weight n ij

theorem main :
    (∀ n : ℕ, 2 ≤ n → a n-(3*(n:ℤ)+1)*a (n-1)+9*((n:ℤ)-1)*a (n-2)=0) ∧
    (∀ k : ℕ, 0<k → ∃ N p : ℕ, 0<p ∧ ∀ n, N ≤ n →
      Int.ModEq (k:ℤ) (a (n+p)) (a n)) := by
  sorry

end OMA.S_oeis_a094822
