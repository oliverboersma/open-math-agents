import Mathlib

/-!
# Erdős Problem 301

Source: https://www.erdosproblems.com/301
Credit: @hermitokatt

## The problem

Let $f(N)$ be the size of the largest $A \subseteq \{1, \ldots, N\}$ such that there are no
solutions to
$$\frac{1}{a} = \frac{1}{b_1} + \cdots + \frac{1}{b_k}$$
with distinct $a, b_1, \ldots, b_k \in A$. Estimate $f(N)$. In particular, is it true that
$f(N) = (\tfrac12 + o(1))N$?

The example $A = (N/2, N] \cap \mathbb{N}$ shows $f(N) \ge N/2$. Wouter van Doorn gave an
elementary argument for $f(N) \le (25/28 + o(1))N$. If the $b_i$ need not be distinct, the
maximal size is at most $N/2$ (Cambie, van Doorn). See also Erdős Problems 302 and 327, and
OEIS A390394.

## Formalization notes

* The source places no restriction on $k$, so `k` is arbitrary. Distinctness of
  $a, b_1, \ldots, b_k$ is encoded by letting $\{b_1, \ldots, b_k\}$ be a `Finset` `B ⊆ A`
  with `a ∉ B`. The case $k = 0$ (`B = ∅`) never gives a solution, because `1 / a > 0`, and
  neither does $k = 1$, because `1 / a = 1 / b` forces `a = b`. So no lower bound on `k` is
  needed.
* The reciprocals are computed in `ℚ`, so the equation is exact. `A ⊆ {1, …, N}` excludes `0`.
* `f N` is the maximum of `A.card` over the admissible `A ⊆ Finset.Icc 1 N`, written as a
  `Finset.sup` over the powerset. The empty set is admissible, so this is a genuine maximum,
  and the definition is computable.
* "Estimate $f(N)$" is open-ended. The theorem states the specific question the source asks,
  $f(N) = (\tfrac12 + o(1))N$, in the form $f(N)/N \to 1/2$. A disproof refutes this
  specific question.
-/

namespace OMA.S_erdos_301

open Filter
open scoped Topology

/-- `A` has no solution to `1 / a = 1 / b₁ + ⋯ + 1 / bₖ` with distinct `a, b₁, …, bₖ ∈ A`. -/
def NoUnitFractionSolution (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ B ⊆ A, a ∉ B → (1 / (a : ℚ)) ≠ ∑ b ∈ B, 1 / (b : ℚ)

instance (A : Finset ℕ) : Decidable (NoUnitFractionSolution A) := by
  unfold NoUnitFractionSolution; infer_instance

/-- $f(N)$: the largest size of an `A ⊆ {1, …, N}` with no such solution. -/
def f (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.filter NoUnitFractionSolution).sup Finset.card

theorem main : Tendsto (fun N : ℕ => (f N : ℝ) / N) atTop (𝓝 (1 / 2)) := by
  sorry

end OMA.S_erdos_301
