import Mathlib

/-!
# Erdős Problem 1054

Source: https://www.erdosproblems.com/1054
Credit: @YourFriendPollux

## The problem

Let $f(n)$ be the minimal integer $m$ such that $n$ is the sum of the $k$ smallest
divisors of $m$ for some $k \ge 1$. Is it true that $f(n) = o(n)$? Or is this true only
for almost all $n$, and $\limsup f(n)/n = \infty$?

A question of Erdős reported in problem B2 of Guy's collection. The function $f(n)$ is
undefined for $n = 2$ and $n = 5$, but is likely well-defined for all $n \ge 6$. Tao
disproved the strong claim $f(n) = o(n)$: the upper density of $\{n : f(n) \le \delta n\}$
is $\ll \delta^2$.

## Formalization notes

* `IsSumOfSmallestDivisors n m` says that `n` is the sum of the `k` smallest divisors of
  `m` for some `k ≥ 1`; the divisors are `m.divisors` sorted increasingly.
* `f n` is the least such `m`. (For the `n` for which no such `m` exists — the source notes
  `n = 2` and `n = 5` — `sInf ∅ = 0` gives a junk value; the questions asked are
  insensitive to these finitely many values.)
* The second and third questions of the source are stated: `f(n) = o(n)` for almost all
  `n` is `∀ ε > 0,` the set `{n : f n ≤ ε n}` has asymptotic density `1` (written out as
  the limit of the counting function), and `limsup f(n)/n = ∞` is
  `∀ C, ∃ᶠ n, C * n < f n`. The first question is known to be false (Tao), so it is
  recorded here only in the comment.
-/

namespace OMA.S_erdos_1054

open Filter
open scoped Topology Classical

/-- `n` is the sum of the `k` smallest divisors of `m`, for some `k ≥ 1`. -/
def IsSumOfSmallestDivisors (n m : ℕ) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ n = ((m.divisors.sort (· ≤ ·)).take k).sum

/-- `f n`: the least `m` such that `n` is a sum of the `k` smallest divisors of `m`. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {m : ℕ | IsSumOfSmallestDivisors n m}

theorem main :
    (∀ ε > (0 : ℝ),
      Tendsto (fun N : ℕ =>
        (((Finset.Icc 1 N).filter (fun n => (f n : ℝ) ≤ ε * n)).card : ℝ) / N)
        atTop (𝓝 1)) ∧
    (∀ C : ℝ, ∃ᶠ n : ℕ in atTop, C * n < (f n : ℝ)) := by
  sorry

end OMA.S_erdos_1054
