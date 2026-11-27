import Mathlib

/-!
# Erdős Problem 671

Source: https://www.erdosproblems.com/671
Credit: @YourFriendPollux

## The problem

Given $a_i^n \in [-1,1]$ for all $1 \le i \le n < \infty$ we define $p_i^n$ as the unique
polynomial of degree $n-1$ such that $p_i^n(a_i^n) = 1$ and $p_i^n(a_{i'}^n) = 0$ for
$i' \ne i$. We similarly define

$$\mathcal{L}^n f(x) = \sum_{1 \le i \le n} f(a_i^n)\, p_i^n(x),$$

the Lagrange interpolation polynomial. Is there such a sequence $a_i^n$ such that for every
continuous $f : [-1,1] \to \mathbb{R}$ there exists some $x \in [-1,1]$ where

$$\limsup_{n \to \infty} \sum_{1 \le i \le n} \lvert p_i^n(x) \rvert = \infty$$

and yet $\mathcal{L}^n f(x) \to f(x)$?

## Formalization notes

* The nodes are a sequence `a : (n : ℕ) → Fin n → ℝ` of strictly increasing `n`-tuples in
  `[-1,1]` (the source indexes them by `1 ≤ i ≤ n`; `Fin n` is the same data).
* `lagrangeBasis a i` is $p_i^n$, `lebesgueFun a x` is $\sum_i \lvert p_i^n(x) \rvert$ and
  `interpPoly a f` is $\mathcal{L}^n f$.
* "$\limsup_n \sum_i \lvert p_i^n(x)\rvert = \infty$" is stated as
  `∀ M, ∃ᶠ n, M ≤ lebesgueFun (a n) x`, i.e. the values exceed every `M` infinitely often.
* The statement formalizes the *first* question of the source. The second question
  (the same, but with the divergence of the Lebesgue functions required at *every*
  `x ∈ [-1,1]`) is a strengthening and is not part of `main`.
-/

namespace OMA.S_erdos_671

open Filter Polynomial
open scoped Topology Classical

/-- The `i`-th Lagrange basis polynomial for the nodes `a`: the unique polynomial of degree
`< n` that is `1` at `a i` and `0` at the other nodes. -/
noncomputable def lagrangeBasis {n : ℕ} (a : Fin n → ℝ) (i : Fin n) : Polynomial ℝ :=
  ∏ j ∈ Finset.univ.erase i, Polynomial.C ((a i - a j)⁻¹) * (Polynomial.X - Polynomial.C (a j))

/-- The Lebesgue function of the nodes `a`: $\sum_i \lvert p_i(x) \rvert$. -/
noncomputable def lebesgueFun {n : ℕ} (a : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ i, |(lagrangeBasis a i).eval x|

/-- The Lagrange interpolation polynomial $\mathcal{L}^n f$ of `f` at the nodes `a`. -/
noncomputable def interpPoly {n : ℕ} (a : Fin n → ℝ) (f : ℝ → ℝ) : Polynomial ℝ :=
  ∑ i, Polynomial.C (f (a i)) * lagrangeBasis a i

theorem main :
    ∃ a : (n : ℕ) → Fin n → ℝ,
      (∀ n, 1 ≤ n → StrictMono (a n) ∧ ∀ i, a n i ∈ Set.Icc (-1 : ℝ) 1) ∧
      ∀ f : ℝ → ℝ, ContinuousOn f (Set.Icc (-1 : ℝ) 1) →
        ∃ x ∈ Set.Icc (-1 : ℝ) 1,
          (∀ M : ℝ, ∃ᶠ n : ℕ in atTop, M ≤ lebesgueFun (a n) x) ∧
          Tendsto (fun n : ℕ => (interpPoly (a n) f).eval x) atTop (𝓝 (f x)) := by
  sorry

end OMA.S_erdos_671
