import Mathlib

/-!
# Erdős Problem 265 — doubly exponential growth with rational reciprocal sums

Source: https://www.erdosproblems.com/265
Credit: @Andyi955

Let `1 ≤ a 1 < a 2 < ...` be an increasing sequence of integers. How fast can `a n` grow if both
`∑ 1 / a n` and `∑ 1 / (a n - 1)` are rational? Kovač and Tao (2024) proved that such a sequence
can grow doubly exponentially: there is such a sequence with `a n ^ (1 / β ^ n) → ∞` for some
`β > 1`. It remains open whether one can achieve `limsup a n ^ (1 / 2 ^ n) > 1`
(erdosproblems.com/265, the remaining open case).

## Encoding

* The sequence is a strictly increasing sequence of natural numbers with `2 ≤ a 0`, so that
  `a n - 1 > 0` and `1 / (a n - 1)` is the intended unit fraction. The source writes `1 ≤ a 1`;
  `a 1 = 1` would make the term `1 / (a 1 - 1)` undefined, so the source's condition is read as
  `a 1 ≥ 2`.
* Rationality of the two sums is stated as existence of a rational value that the series has as its
  sum: `HasSum (fun n => (a n)⁻¹) q` and `HasSum (fun n => (a n - 1)⁻¹) q` over `ℚ`, which also
  forces summability (so the sums are convergent, as the source implicitly assumes).
* The open question is the growth condition `1 < limsup a n ^ (2 ^ (-n))`, a real power, via
  `Real.rpow`; this is exactly the statement that the source lists as remaining open.
-/

namespace OMA.S_erdos_265

/-- **Erdős Problem 265, remaining open case**: there is a strictly increasing sequence `a` with
both `∑ 1 / a n` and `∑ 1 / (a n - 1)` rational and `limsup a n ^ (1 / 2 ^ n) > 1`. -/
theorem main : ∃ a : ℕ → ℕ, StrictMono a ∧ 2 ≤ a 0 ∧
    (∃ q : ℚ, HasSum (fun n : ℕ => ((a n : ℚ))⁻¹) q) ∧
      (∃ q : ℚ, HasSum (fun n : ℕ => ((a n : ℚ) - 1)⁻¹) q) ∧
        1 < Filter.limsup (fun n : ℕ => (a n : ℝ) ^ ((2 : ℝ) ^ (-(n : ℝ)))) Filter.atTop := by
  sorry

end OMA.S_erdos_265
