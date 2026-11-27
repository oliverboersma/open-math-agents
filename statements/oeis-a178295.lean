import Mathlib

/-!
# A178295: Mathar's closed form for collinear 4-point subsets of the `5^n` grid

Source: https://oeis.org/A178295
Credit: @sntntHb

`a(n)` is the number of collinear point 4-tuples in a 5 X 5 X ... n-dimensional cubic grid, i.e. the
number of `4`-element sets of points of `{0, ..., 4}^n` that lie on a common line. The entry
records a conjecture of R. J. Mathar (May 24 2010):
`a(n) = 9^n/2+3*7^n/2-2*5^n`, equivalently `a(n) = 21*a(n-1) - 143*a(n-2) + 315*a(n-3)`.

The grid point `p : Fin n → Fin 5` is viewed as the real point `fun i => (p i : ℝ)`, and a set of
grid points is collinear when its image is `Collinear ℝ` in `Fin n → ℝ`. `a n` counts the sets of
grid points of cardinality `4` with collinear image. This matches the data: for `n = 0` the grid
has a single point and `a 0 = 0`; for `n = 1` every `4`-subset of `5` points on a line counts,
giving `a 1 = 5`, and the line-by-line count gives `a 2 = 64` and `a 3 = 629` as listed.

`main` states the conjectured closed form, multiplied by `2` to clear denominators and read in `ℤ`.
-/

namespace OMA.S_oeis_a178295

/-- The grid point `p` of `{0, ..., 4}^n` as a point of `ℝ^n`. -/
def toReal {n : ℕ} (p : Fin n → Fin 5) : Fin n → ℝ := fun i => ((p i : ℕ) : ℝ)

/-- `a n`: the number of collinear `4`-element sets of points of the `5^n` grid (OEIS A178295). -/
noncomputable def a (n : ℕ) : ℕ :=
  {s : Finset (Fin n → Fin 5) | s.card = 4 ∧ Collinear ℝ (toReal '' (s : Set (Fin n → Fin 5)))}.ncard

/-- Mathar's conjectured closed form for OEIS A178295. -/
theorem main : ∀ n : ℕ, 2 * (a n : ℤ) = 9 ^ n + 3 * 7 ^ n - 4 * 5 ^ n := by
  sorry

end OMA.S_oeis_a178295
