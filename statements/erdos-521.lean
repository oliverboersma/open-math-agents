import Mathlib

/-!
# Erdős Problem 521

Source: https://www.erdosproblems.com/521
Credit: @YourFriendPollux

## The problem

Let $(\varepsilon_k)_{k \ge 0}$ be independently uniformly chosen at random from
$\{-1,1\}$. If $R_n$ counts the number of real roots of
$f_n(z) = \sum_{0 \le k \le n} \varepsilon_k z^k$, is it true that, almost surely,

$$\lim_{n \to \infty} \frac{R_n}{\log n} = \frac{2}{\pi}?$$

Erdős and Offord [EO56] showed that the number of real roots of a random degree $n$
polynomial with $\pm 1$ coefficients is $(\frac{2}{\pi} + o(1)) \log n$.

## Formalization notes

* The random signs are modelled on the probability space `ℕ → Bool` with the infinite
  product of the uniform measure on `Bool` (`signMeasure`); `eps k ω = 1` if `ω k = true`
  and `-1` otherwise, so the `ε k` are independent and uniform on `{-1, 1}`.
* `randPoly n ω` is $f_n = \sum_{k \le n} \varepsilon_k X^k$, and `realRootCount n ω`
  counts its real roots *with multiplicity*: the roots of `f_n` over `ℂ`, restricted to
  those that are images of real numbers. (This is the standard reading of "the number of
  real roots" of a polynomial of degree `n`; the answer is not affected by multiplicities
  for this problem, since almost surely no root is multiple.)
* The conclusion is stated `almost surely`, as in the source.
-/

namespace OMA.S_erdos_521

open MeasureTheory Filter
open scoped ENNReal Topology Classical

/-- The law of an i.i.d. sequence of uniform signs, as a measure on `ℕ → Bool`. -/
noncomputable def signMeasure : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ => (2 : ℝ≥0∞)⁻¹ • (Measure.dirac true + Measure.dirac false))

/-- The sign `ε k`, read off the `Bool`-valued sequence: `true ↦ 1`, `false ↦ -1`. -/
def eps (k : ℕ) (ω : ℕ → Bool) : ℤ := if ω k then 1 else -1

/-- The random polynomial $f_n(z) = \sum_{k \le n} \varepsilon_k z^k$. -/
noncomputable def randPoly (n : ℕ) (ω : ℕ → Bool) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.C ((eps k ω : ℂ)) * Polynomial.X ^ k

/-- `R_n`: the number of real roots of `f_n`, counted with multiplicity. -/
noncomputable def realRootCount (n : ℕ) (ω : ℕ → Bool) : ℕ :=
  ((randPoly n ω).roots.filter (fun z => ∃ r : ℝ, (r : ℂ) = z)).card

theorem main :
    ∀ᵐ ω ∂signMeasure,
      Tendsto (fun n : ℕ => (realRootCount n ω : ℝ) / Real.log n) atTop (𝓝 (2 / Real.pi)) := by
  sorry

end OMA.S_erdos_521
