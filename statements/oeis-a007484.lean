import Mathlib

/-!
# A007484: a(n) = 3*a(n-1) + 2*a(n-2), with a(0)=2, a(1)=7.

Source: https://oeis.org/A007484
Credit: @JeremyDevs

Formalizes the identity recorded as a conjecture in OEIS A007484 (Creighton Dement, Apr 15 2005):
8*a(n) = A007482(n+2) + A007483(n+1).
The entry notes (Robert Israel, Jul 12 2018) that the conjecture was verified using generating
functions, so this is a known result; the statement below is its Lean form.

Conventions (all three sequences have offset 0 and natural-number terms):
* A007484: a(0) = 2, a(1) = 7, a(n) = 3*a(n-1) + 2*a(n-2); data 2, 7, 25, 89, 317, ...
* A007482 is named in the OEIS by a combinatorial description (the number of subsequences of
  [1, ..., 2n] in which each odd number has an even neighbor). It is taken here through the
  recurrence given in its FORMULA section, a(n) = 3*a(n-1) + 2*a(n-2), with the initial terms
  a(0) = 1, a(1) = 3 of its data 1, 3, 11, 39, 139, ... This is the function `b`.
* A007483: a(0) = 1, a(1) = 5, a(n) = 3*a(n-1) + 2*a(n-2); data 1, 5, 17, 61, 217, ... This is the
  function `c`.
* The identity is asserted for every `n ≥ 0`, the full range of the offset-0 sequence
  (e.g. n = 0: 8*2 = 11 + 5).
-/

namespace OMA.S_oeis_a007484

/-- A007484: a(0) = 2, a(1) = 7, a(n) = 3*a(n-1) + 2*a(n-2). -/
def a : ℕ → ℕ
  | 0 => 2
  | 1 => 7
  | n + 2 => 3 * a (n + 1) + 2 * a n

/-- A007482: b(0) = 1, b(1) = 3, b(n) = 3*b(n-1) + 2*b(n-2). -/
def b : ℕ → ℕ
  | 0 => 1
  | 1 => 3
  | n + 2 => 3 * b (n + 1) + 2 * b n

/-- A007483: c(0) = 1, c(1) = 5, c(n) = 3*c(n-1) + 2*c(n-2). -/
def c : ℕ → ℕ
  | 0 => 1
  | 1 => 5
  | n + 2 => 3 * c (n + 1) + 2 * c n

/-- For every `n`, 8*A007484(n) = A007482(n+2) + A007483(n+1). -/
theorem main : ∀ n : ℕ, 8 * a n = b (n + 2) + c (n + 1) := by
  sorry

end OMA.S_oeis_a007484
