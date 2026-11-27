import Mathlib

/-!
# An inequality for copulas

Source: https://mathoverflow.net/questions/195959
Credit: @koolkao

Question (Clark Kimberling, MathOverflow 195959, 2015). Suppose that `f` from `[0, ∞]` onto `[0, 1]`
is completely monotonic on `(0, ∞)`, and let `g` be the inverse of `f`. For `(u, v)` in `[0, 1]²`,
define `C(u, v) = f(g(u) + g(v))`, and let `a = (u + v)/2`. Is
`C(a, a) - a² ≥ C(u, v) - uv` for all `(u, v)` in `[0, 1]²`?

Here `f` is completely monotonic on `(a, b)` if `(-1)ᵏ f⁽ᵏ⁾(x) ≥ 0` for all `k` and all `x` in
`(a, b)` (Widder, The Laplace Transform, 1946, p. 145, as cited in the source). Then `C` is an
Archimedean copula with generator `g` (Nelsen, An Introduction to Copulas, 2nd ed., Ch. 4), and
`f(x) = exp(-x)` gives `C(u, v) = uv`.

Reading of the source (conventions it leaves implicit):
* `k` ranges over `0, 1, 2, …` (so `k = 0` gives `f ≥ 0`), as in Widder's definition.
* `f` is a real function. Only its values on `[0, ∞)` matter, plus its value at `∞`, which is
  read as the limit: `f(∞) = 0`. The hypotheses are `f(0) = 1`, `f` continuous on `[0, ∞)` and
  `f(x) → 0` as `x → ∞`. Justification: a completely monotonic `f` on `(0, ∞)` is continuous and
  nonincreasing there, so `f((0, ∞))` is a point or an open interval `(L, f(0+))`. For the image of
  `[0, ∞]` to be all of `[0, 1]` we need `L = 0`, `f(0+) = 1` and `{f(0), f(∞)} = {0, 1}`. The
  swapped assignment `f(0) = 0`, `f(∞) = 1` also gives a bijection, but then `C(0, v) = v` is not a
  copula, and the source states that `C` is an Archimedean copula; so the source's reading is
  `f(0) = 1`, `f(∞) = 0`, with `f` continuous on `[0, ∞]`. This is the standard inverse of a strict
  Archimedean generator (Nelsen, Ch. 4). Conversely, these hypotheses make `f` map `[0, ∞]` onto
  `[0, 1]`, so no generality is lost.
* Complete monotonicity includes that `f` is infinitely differentiable on `(0, ∞)` (the C^∞ class
  `⊤ : ℕ∞`, not analyticity, although every completely monotonic function is in fact analytic).
  The derivatives are the iterated derivatives within `(0, ∞)`, an open set, so they are ordinary
  derivatives.
* These hypotheses force `f` to be strictly decreasing on `[0, ∞)` with values in `(0, 1]` (a
  non-constant completely monotonic function is strictly decreasing and positive). So for
  `u ∈ (0, 1]` the inverse `g(u)` is the unique `x ≥ 0` with `f(x) = u`, which is what
  `Function.invFunOn f (Set.Ici 0) u` returns. For `u = 0` the inverse is `g(0) = ∞`, so
  `C(u, v) = f(∞) = 0` whenever `u = 0` or `v = 0`. The definition `archC` below encodes this
  explicitly, and the statement covers the whole closed square `[0, 1]²`, as in the source.

The source says (May 2015) that the question remains largely unanswered: the two MathOverflow
answers prove it only for simple examples, namely the Clayton copulas `f(x) = (1 + x)^(-1/t)` with
`t ≥ 1`. No general proof or counterexample is known to us (November 2026).
-/

namespace OMA.S_mo_195959

open Filter Topology

/-- `f` is completely monotonic on the open set `s`: it is infinitely differentiable on `s` and
`(-1)ᵏ f⁽ᵏ⁾(x) ≥ 0` for every `k` and every `x ∈ s` (Widder 1946). -/
def CompletelyMonotoneOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) f s ∧ ∀ k : ℕ, ∀ x ∈ s, 0 ≤ (-1 : ℝ) ^ k * iteratedDerivWithin k f s x

/-- The Archimedean copula `C(u, v) = f(g(u) + g(v))`, with `g` the inverse of `f` on `[0, ∞)`,
and with the value `0 = f(∞)` when `u = 0` or `v = 0` (as `g(0) = ∞`). -/
noncomputable def archC (f : ℝ → ℝ) (u v : ℝ) : ℝ :=
  if u = 0 ∨ v = 0 then 0
  else f (Function.invFunOn f (Set.Ici 0) u + Function.invFunOn f (Set.Ici 0) v)

theorem main :
    ∀ f : ℝ → ℝ, ContinuousOn f (Set.Ici 0) → f 0 = 1 → Tendsto f atTop (𝓝 0) →
      CompletelyMonotoneOn f (Set.Ioi 0) →
      ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ Set.Icc (0 : ℝ) 1,
        archC f u v - u * v ≤ archC f ((u + v) / 2) ((u + v) / 2) - ((u + v) / 2) ^ 2 := by
  sorry

end OMA.S_mo_195959
