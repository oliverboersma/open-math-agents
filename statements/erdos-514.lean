import Mathlib

/-!
# Erdős Problem 514

Source: https://www.erdosproblems.com/514
Credit: @YourFriendPollux

## The problem

Let $f(z)$ be an entire transcendental function. Does there exist a path $L$ so that, for
every $n$,

$$\lvert f(z)/z^n \rvert \to \infty$$

as $z \to \infty$ along $L$? Can the length of this path be estimated in terms of
$M(r) = \max_{\lvert z\rvert = r}\lvert f(z)\rvert$? Does there exist a path along which
$\lvert f(z)\rvert$ tends to $\infty$ faster than a fixed function of $M(r)$ (such as
$M(r)^\varepsilon$)?

Boas (unpublished) proved the first part, that such a path must exist.

## Formalization notes

* "Entire" is `Differentiable ℂ f`, and "transcendental" is stated as "`f` is not the
  evaluation map of a polynomial", i.e. `∀ p : ℂ[X], f ≠ fun z => p.eval z`. For an entire
  function this is equivalent to not being a polynomial.
* A path is a continuous map `γ : ℝ → ℂ`, and "$z \to \infty$ along $L$" is
  `Tendsto γ atTop (Bornology.cobounded ℂ)`, i.e. `‖γ t‖ → ∞`.
* "$\lvert f(z)/z^n\rvert \to \infty$ along $L$" is
  `Tendsto (fun t => f (γ t) / (γ t) ^ n) atTop (Bornology.cobounded ℂ)`: on `ℂ` the
  cobounded filter is convergence of the norm to infinity, so this says
  $\lvert f(\gamma t)/\gamma t^n\rvert \to \infty$.
* The statement formalizes the first question of the source, which asks for the existence
  of the path simultaneously for all `n` (the quantifier `∀ n` is inside the scope of the
  single path `γ`, exactly as in the source). The second and third questions concern
  quantitative estimates on the length of such a path in terms of `M(r)`; they are
  separate quantitative refinements and are not part of `main`.
-/

namespace OMA.S_erdos_514

open Filter Polynomial Bornology
open scoped Topology

theorem main :
    ∀ f : ℂ → ℂ, Differentiable ℂ f →
      (∀ p : Polynomial ℂ, f ≠ fun z => p.eval z) →
      ∃ γ : ℝ → ℂ, Continuous γ ∧ Tendsto γ atTop (cobounded ℂ) ∧
        ∀ n : ℕ, Tendsto (fun t : ℝ => f (γ t) / (γ t) ^ n) atTop (cobounded ℂ) := by
  sorry

end OMA.S_erdos_514
