import Mathlib

/-!
# OEIS A094061: stronger Gauss congruences for closed king walks

Source: https://oeis.org/A094061
Credit: @sntntHb

A094061: number of `n`-moves paths of a king starting and ending at the origin of an infinite
chessboard.

Conjecture (Peter Bala): the stronger congruences `a(n*p^k) == a(n*p^(k-1)) (mod p^(2*k))` hold
for all primes `p >= 5` and positive integers `n` and `k`.

Formalized: a king move is a nonzero vector in `{-1,0,1}^2`; `a n` counts the sequences of `n`
king moves whose sum is `(0,0)`. `main` states the congruence modulo `p^(2*k)` for every prime
`p >= 5` and all `n, k >= 1`.
-/

namespace OMA.S_oeis_a094061

/-- The eight king moves. -/
def moves : Finset (ℤ × ℤ) :=
  {(-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 1), (1, -1), (1, 0), (1, 1)}

/-- Number of `n`-move king paths from the origin back to the origin. -/
def a (n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin n => moves).filter (fun f => ∑ i, f i = 0)).card

theorem main :
    ∀ p n k : ℕ, p.Prime → 5 ≤ p → 0 < n → 0 < k →
      a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [MOD p ^ (2 * k)] := by
  sorry

end OMA.S_oeis_a094061
