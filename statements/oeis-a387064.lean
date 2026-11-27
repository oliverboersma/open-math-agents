import Mathlib

/-!
# OEIS A387064

Source: https://oeis.org/A387064 (OEIS Foundation, CC BY-SA 4.0).
Credit: @bcrowther86-eng

A387064(n), for `n ≥ 0`, is the total number of entries in rows `0` to `n` of Pascal's triangle
that are multiples of `n`. Data (from n = 0): 0, 3, 1, 2, 2, 4, 3, 6, 4, 6, 10, 10, 12, ...

The entry notes `a(p) = p - 1` and `a(p^2) = p(p - 1)` for `p` prime, and states:
Conjecture: `a(p^k) = (p - 1) p^(k-1)` for `p` prime.

We state the conjecture for all primes `p` and all `k ≥ 1` (for `k = 0`, `p^0 = 1` and the
formula has no meaning in the source). "Multiple of `n`" is `n ∣ C(r, j)`; for `n = 0` this
counts entries equal to `0`, of which there are none, matching `a(0) = 0`.
-/

namespace OMA.S_oeis_a387064

/-- `a n`: the number of entries `C(r, j)`, `0 ≤ j ≤ r ≤ n`, that are multiples of `n`. -/
def a (n : ℕ) : ℕ :=
  ∑ r ∈ Finset.range (n + 1), ((Finset.range (r + 1)).filter fun j => n ∣ Nat.choose r j).card

theorem main : ∀ p k : ℕ, p.Prime → 1 ≤ k → a (p ^ k) = (p - 1) * p ^ (k - 1) := by
  sorry

end OMA.S_oeis_a387064
