import Mathlib

/-!
# Rare gaps between integers having the same number of co-primes

Source: https://math.stackexchange.com/questions/3369746/rare-gaps-between-integers-having-the-same-number-of-co-primes
Credit: @mgv27

Let $\varphi$ be Euler's totient function. Numerically, $\varphi(n) = \varphi(n+k)$ has very few
solutions when $k$ is an odd multiple of $3$ and very many when $k$ is a multiple of $6$.
Is the following claim true?

For any six consecutive positive integer values of $k$, and a sufficiently large $x$, the
number of integers $n \le x$ such that $\varphi(n) = \varphi(n+k)$ is the lowest when
$k \equiv 3 \pmod 6$ and is the highest when $k \equiv 0 \pmod 6$.

Formalization notes:
* `count k x` is the number of `n ∈ [1, x]` with `φ(n) = φ(n + k)` (`Nat.totient`).
* Six consecutive values are `k ∈ [j, j + 5]` for some `j ≥ 1`; exactly one is `≡ 3` and one is
  `≡ 0 (mod 6)`.
* "Lowest"/"highest" are read strictly: for each other `k'` in the window, eventually (in `x`)
  `count k₃ x < count k' x` and `count k' x < count k₀ x`.
* Sanity check (`x = 2·10^6`): counts for `k = 1..12` are
  80, 4481, 2, 2649, 26, 13122, 93, 1610, 2, 1545, 96, 7787.
-/

namespace OMA.S_mse_3369746

open Filter

/-- The number of `n` with `1 ≤ n ≤ x` and `φ(n) = φ(n + k)`. -/
def count (k x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter (fun n => Nat.totient n = Nat.totient (n + k))).card

/-- In every window of six consecutive positive `k`, for all large `x` the count is strictly
smallest at `k ≡ 3 (mod 6)` and strictly largest at `k ≡ 0 (mod 6)`. -/
theorem main :
    ∀ j : ℕ, 1 ≤ j → ∀ k ∈ Finset.Icc j (j + 5), ∀ k' ∈ Finset.Icc j (j + 5), k' ≠ k →
      ∀ᶠ x in atTop,
        (k % 6 = 3 → count k x < count k' x) ∧ (k % 6 = 0 → count k' x < count k x) := by
  sorry

end OMA.S_mse_3369746
