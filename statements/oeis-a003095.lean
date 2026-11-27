import Mathlib

/-!
# A003095: eventual periods of a(n) = a(n-1)^2 + 1 modulo 2^k, 10^k and 20^k

Source: https://oeis.org/A003095 (OEIS Foundation, CC BY-SA 4.0).

a(0) = 0 and a(n) = a(n-1)^2 + 1 for n >= 1. Peter Bala (Oct 31 2022)
conjectured, for every positive integer k:
1) the sequence a(n) mod 2^k is eventually periodic with period 2;
2) the sequence a(n) mod 10^k is eventually periodic with period 6;
3) the sequence a(n) mod 20^k is eventually periodic with period 6.
(A fourth conjecture in the same comment, about the eventual values of
a(6n+i) mod 10^k and the 10-adic numbers A318135 to A318140, is not
formalized here.)

The period of an eventually periodic sequence is read as its least eventual
period: the sequence eventually repeats with shift p, and with no smaller
positive shift.
-/

namespace OMA.S_oeis_a003095

/-- `a 0 = 0`, `a (n + 1) = a n ^ 2 + 1`. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => a n ^ 2 + 1

/-- `a` reduced modulo `M` is eventually periodic with least period `p`. -/
def HasEventualPeriod (M p : ℕ) : Prop :=
  (∃ N, ∀ n ≥ N, a (n + p) ≡ a n [MOD M]) ∧
    ∀ q, 0 < q → q < p → ¬ ∃ N, ∀ n ≥ N, a (n + q) ≡ a n [MOD M]

theorem main : ∀ k : ℕ, 0 < k →
    HasEventualPeriod (2 ^ k) 2 ∧ HasEventualPeriod (10 ^ k) 6 ∧
      HasEventualPeriod (20 ^ k) 6 := by
  sorry

end OMA.S_oeis_a003095
