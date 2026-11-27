import Mathlib

/-!
# Erdős Problem 684

Source: https://www.erdosproblems.com/684
Credit: @YourFriendPollux

## The problem

For $0 \le k \le n$ write $\binom{n}{k} = uv$ where the only primes dividing $u$ are in
$[2,k]$ and the only primes dividing $v$ are in $(k,n]$. Let $f(n)$ be the smallest $k$
such that $u > n^2$. Give bounds for $f(n)$.

A classical theorem of Mahler implies $f(n) \to \infty$, but is ineffective. Tang proved
$f(n) \le n^{30/43+o(1)}$; the same proof gives $f(n) \le n^{2/3+o(1)}$ under the Riemann
Hypothesis.

## Formalization notes

* `smoothPart k m` is $u$: the product of the prime powers $p^{v_p(m)}$ over the primes
  $p \le k$ dividing $m$. Then $v = m / u$, so the factorisation of the source is
  `m = smoothPart k m * (m / smoothPart k m)`.
* `f n` is the least `k ≤ n` with `n ^ 2 < smoothPart k (n.choose k)`. (If no such `k`
  exists, `sInf ∅ = 0` is a junk value; the questions asked are asymptotic.)
* The problem asks for bounds; the statement records the known upper bound of Tang,
  $f(n) \le n^{30/43+o(1)}$, in the equivalent form
  `∀ ε > 0, ∀ᶠ n, f n ≤ n ^ (30/43 + ε)`.
-/

namespace OMA.S_erdos_684

open Filter
open scoped Topology Classical

/-- `smoothPart k m` is the largest divisor of `m` all of whose prime factors are `≤ k`. -/
def smoothPart (k m : ℕ) : ℕ :=
  ∏ p ∈ m.primeFactors.filter (· ≤ k), p ^ (m.factorization p)

/-- `f n`: the smallest `k ≤ n` for which the `k`-smooth part of `n.choose k` exceeds
`n ^ 2`. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {k : ℕ | k ≤ n ∧ n ^ 2 < smoothPart k (n.choose k)}

theorem main : ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ (n : ℝ) ^ (30 / 43 + ε) := by
  sorry

end OMA.S_erdos_684
