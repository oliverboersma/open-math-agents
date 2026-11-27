import Mathlib

/-!
# Kneser–Poulsen conjecture

Source: https://www.openproblemgarden.org/op/kneser_poulsen_conjecture
Credit: @LAPRAI

*References:* M. Kneser, Einige Bemerkungen über das Minkowskische Flächenmass, Arch. Math. 6
(1955); E. T. Poulsen, Problem 10, Math. Scand. 2 (1954).

If a finite set of unit balls in `ℝⁿ` is rearranged so that the distance between each pair of
centers does not decrease, then the volume of the union of the balls does not decrease.

## Encoding

* `ℝⁿ` is `EuclideanSpace ℝ (Fin n)` with Lebesgue measure `MeasureTheory.volume`.
* The finite set of balls is indexed by `Fin m`; `p i` are the original centers and `q i` the
  rearranged ones, with `dist (p i) (p j) ≤ dist (q i) (q j)` for every pair.
* Unit balls are closed balls of radius `1` (open balls give the same volumes, since spheres are
  null sets).
-/

namespace OMA.S_opg_kneser_poulsen_conjecture

open MeasureTheory Metric

/-- **Kneser–Poulsen conjecture.** -/
theorem main : ∀ (n m : ℕ) (p q : Fin m → EuclideanSpace ℝ (Fin n)),
    (∀ i j, dist (p i) (p j) ≤ dist (q i) (q j)) →
    volume (⋃ i, closedBall (p i) 1) ≤ volume (⋃ i, closedBall (q i) 1) := by
  sorry

end OMA.S_opg_kneser_poulsen_conjecture
