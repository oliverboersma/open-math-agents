import Mathlib

/-!
Source: https://oeis.org/A372991
Source text: https://github.com/oeis/oeisdata/blob/main/seq/A372/A372991.seq
Credit: @Heart-galaxy

The source presents Mathar's recurrence as a conjecture (July 16, 2024)
and does not record a proof. The independent defining factorial quotient
is interpreted in Q, without truncated division. The companion proof
establishes positivity of every denominator and integrality of all values.
The offset is zero,
so the conjecture's complete common index range is n>=3.
-/

namespace OMA.S_oeis_a372991

def a : ℕ → ℚ
  | 0 => 1
  | 1 => 1
  | n+2 => (Nat.factorial (2*(n+2)) : ℚ)/(a (n+1)*a n)

theorem main : ∀ n : ℕ, 3 ≤ n →
    a n-2*(n:ℚ)*(2*(n:ℚ)-1)*a (n-3)=0 := by
  sorry

end OMA.S_oeis_a372991
