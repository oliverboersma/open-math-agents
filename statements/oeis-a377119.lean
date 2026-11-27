import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Basic

/-!
# OEIS A377119

Clark Kimberling considers the coefficient of the square of the real cube root
of two in the powers of the sum of this root and its square. He conjectures an
eventual period for every prime's divisibility gaps and specifies gap blocks for
the first six primes. Indices start at zero. The companion guide A377109 uses
successive differences of the positions at which a coefficient vanishes modulo p.

Source: https://oeis.org/A377119
Formalization: @ecirak42.
-/

namespace OMA.S_oeis_a377119

/-- Multiplication by t+t² in the basis 1,t,t², where t³=2. -/
def advance {R : Type*} [Semiring R] (v : R × R × R) : R × R × R :=
  (2 * (v.2.1 + v.2.2), v.1 + 2 * v.2.2, v.1 + v.2.1)

def coefficients (R : Type*) [Semiring R] : Nat → R × R × R
  | 0 => (1, 0, 0)
  | n + 1 => advance (coefficients R n)

def a (n : Nat) : Nat := (coefficients Nat n).2.2

/-- The successive gaps of the increasing sequence of all qualifying indices. -/
noncomputable def gap (p i : Nat) : Nat :=
  Nat.nth (fun n => p ∣ a n) (i+1) - Nat.nth (fun n => p ∣ a n) i

def generalClaim : Prop :=
  ∀ p : Nat, Nat.Prime p →
    {n : Nat | p ∣ a n}.Infinite ∧
      ∃ N T : Nat, 0 < T ∧ ∀ i ≥ N, gap p (i+T) = gap p i

/-- A stated block repeats from the first gap, with the phase shown by OEIS. -/
def repeats (p : Nat) (block : List Nat) : Prop :=
  ∀ i : Nat, gap p i = block[i % block.length]!

theorem main :
    generalClaim ∧ repeats 2 [2,1] ∧ repeats 3 [7,1] ∧
    repeats 5 [21,5,13,1] ∧ repeats 7 [15,17,20,43,1] ∧
    repeats 11 [9,1] ∧ repeats 13 [102,5,17,15,1] := by
  sorry

end OMA.S_oeis_a377119
