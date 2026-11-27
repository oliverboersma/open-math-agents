import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The binomial identity in OEIS A284005

Source: https://oeis.org/A284005 (OEIS Foundation, CC BY-SA 4.0).
Mikhail Kurkov's April 2023 conjecture sums the terms at 2^k*n with
binomial weights. The recursion uses the binary digit sum and divides
the index by two. It gives a(1)=2 from a(0)=1.
The trureturing project records a proof of this binomial identity.
-/

namespace OMA.S_oeis_a284005

def weight (n : ℕ) : ℕ := (Nat.digits 2 n).sum

def a (n : ℕ) : ℕ :=
  if n=0 then 1 else (1+weight n)*a (n/2)
termination_by n
decreasing_by omega

theorem main : ∀ m n : ℕ,
    a (2^m*(2*n+1)) = ∑ k ∈ Finset.range (m+2), Nat.choose (m+1) k * a (2^k*n) := by
  sorry

end OMA.S_oeis_a284005
