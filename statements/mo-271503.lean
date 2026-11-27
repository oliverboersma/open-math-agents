import Mathlib

/-!
# Median and mean of the sample mean of i.i.d. log-normal

Source: https://mathoverflow.net/questions/271503
Credit: @koolkao

Question (Hans, MathOverflow 271503, 2017). Let `y = (1/n) ∑ᵢ xᵢ`, where `x₁, …, xₙ` are i.i.d.
random variables, each with a lognormal distribution `Lognormal(μ, σ²)`. Let `Med[y]` be the median
of `y`. Is `Med[y] < 𝔼[y]` for all `(n, μ, σ)`?

Reading of the source (conventions the question leaves implicit):
* `n ≥ 1`, since the sample mean of zero observations is undefined, and `μ` is any real number.
* `σ > 0`. The lognormal family `Lognormal(μ, σ²)` is the law of `exp G` with `G ~ N(μ, σ²)`,
  and the question concerns genuinely random samples. For `σ = 0` every `xᵢ` equals `exp μ`
  almost surely and `Med[y] = 𝔼[y]`, so the strict inequality would fail trivially. The sign of `σ`
  is immaterial, as only `σ²` enters.
* `xᵢ ~ Lognormal(μ, σ²)` means: `xᵢ > 0` almost surely and `log xᵢ` has law `N(μ, σ²)`, which
  is Mathlib's `gaussianReal μ σ²` (its second argument is the variance). Mutual independence is
  `iIndepFun`. Identical distribution follows, since every `xᵢ` has the same law.
* No separate measurability hypothesis is needed: `Measure.map` of a function that is not
  a.e.-measurable is the zero measure, so the law hypothesis forces `log ∘ xᵢ` to be
  a.e.-measurable, and then so is `xᵢ = exp ∘ log ∘ xᵢ` (a.e.).
* `Med[y]` is any median of `y`, that is any `m` with `ℙ(y ≤ m) ≥ 1/2` and `ℙ(y ≥ m) ≥ 1/2`.
  Here the law of `y` has a positive continuous density on `(0, ∞)`, so the median is unique and
  this reading agrees with the source. The statement asserts that every median is `< 𝔼[y]`.
* `𝔼[y]` is the true expectation, equal to `exp (μ + σ²/2)`: `y` is integrable because a lognormal
  variable has finite moments of every order, so the Lean convention of integral `0` for
  non-integrable functions never applies.
* The probability space is arbitrary (in `Type`, which loses no generality for real-valued random
  variables).

The case `n = 1` holds, since then `Med[y] = exp μ < exp (μ + σ²/2) = 𝔼[y]`. The MathOverflow
answers (2017) give only a heuristic large-`n` argument (Fenton–Wilkinson approximation) and an
approximate argument for `n = 2`; a 2024 comment notes that, for fixed `σ`, failures can occur for
only finitely many `n`.

Literature status (update): the statement follows from a known theorem. `y = f(Z)` with
`f(z) = (1/n) ∑ᵢ exp (μ + σ zᵢ)` convex and `Z` standard Gaussian in `ℝⁿ`. Kwapień, *A remark on the
median and the expectation of convex functions of Gaussian vectors*, in Probability in Banach Spaces 9
(Birkhäuser, 1994), pp. 271–272, proves `Med f(Z) ≤ 𝔼 f(Z)` for every integrable convex `f`, via
Ehrhard's inequality. Strictness here follows because `t ↦ Φ⁻¹(ℙ(f(Z) ≤ t))` is concave, so
`f(Z) = Q(G)` in law for a convex, strictly increasing `Q` that is bounded below and hence not affine,
and Jensen's inequality is strict. So this is a known result, not an open problem.
-/

namespace OMA.S_mo_271503

open MeasureTheory ProbabilityTheory

theorem main :
    ∀ (n : ℕ), 0 < n → ∀ (μ σ : ℝ), 0 < σ →
      ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] (x : Fin n → Ω → ℝ),
        iIndepFun x ℙ → (∀ i, ∀ᵐ ω ∂(ℙ : Measure Ω), 0 < x i ω) →
        (∀ i, Measure.map (fun ω => Real.log (x i ω)) ℙ = gaussianReal μ (Real.toNNReal (σ ^ 2))) →
        ∀ m : ℝ,
          1 / 2 ≤ (ℙ : Measure Ω).real {ω | (1 / (n : ℝ)) * ∑ i, x i ω ≤ m} →
          1 / 2 ≤ (ℙ : Measure Ω).real {ω | m ≤ (1 / (n : ℝ)) * ∑ i, x i ω} →
          m < 𝔼[fun ω => (1 / (n : ℝ)) * ∑ i, x i ω] := by
  sorry

end OMA.S_mo_271503
