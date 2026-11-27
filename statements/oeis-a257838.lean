import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Fib.Basic

/-!
# Mathar's recurrence for the diagonal of repeated Fibonacci sums

Row zero below is the Fibonacci sequence F(0)=0, F(1)=1. Row one is the
first row displayed in A257838. Consequently the OEIS term a(n) is the
entry in column n of row n+1. Setting n=t+3 covers every index of the
four-term recurrence starting from the published offset zero.

Source: https://oeis.org/A257838
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a257838

def partialSums : ℕ → ℕ → ℤ
  | 0, j => (Nat.fib j : ℤ)
  | r+1, j => ∑ k ∈ Finset.range (j+1), partialSums r k

def diagonal (n : ℕ) := partialSums (n+1) n

theorem main : ∀ t : ℕ, let n : ℤ := (t : ℤ)+3;
    n*(n-3)*diagonal (t+3) + 2*(-4*n^2+13*n-6)*diagonal (t+2) +
    (15*n^2-53*n+48)*diagonal (t+1) + 2*(2*n-3)*(n-2)*diagonal t = 0 := by
  sorry

end OMA.S_oeis_a257838
