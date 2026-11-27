import Mathlib

/-!
# A178297: Mathar's closed form for collinear 6-point subsets of the `7^n` grid

Source: https://oeis.org/A178297
Credit: @sntntHb

`a(n)` is the number of collinear point 6-tuples in a 7 X 7 X ... n-dimensional cubic grid, i.e. the
number of `6`-element sets of points of `{0, ..., 6}^n` that lie on a common line. The entry
records a conjecture of R. J. Mathar (May 24 2010):
`a(n) = 11^n/2+5*9^n/2-3*7^n`, equivalently `a(n) = 27*a(n-1) - 239*a(n-2) + 693*a(n-3)`.

The grid point `p : Fin n → Fin 7` is viewed as the real point `fun i => (p i : ℝ)`, and a set of
grid points is collinear when its image is `Collinear ℝ` in `Fin n → ℝ`. `a n` counts the sets of
grid points of cardinality `6` with collinear image. This matches the data: for `n = 0` the grid
has a single point and `a 0 = 0`; for `n = 1` every `6`-subset of `7` points on a line counts,
giving `a 1 = 7`, and the line-by-line count gives `a 2 = 116` and `a 3 = 1459` as listed.

`main` states the conjectured closed form, multiplied by `2` to clear denominators and read in `ℤ`.
-/

namespace OMA.S_oeis_a178297

/-- The grid point `p` of `{0, ..., 6}^n` as a point of `ℝ^n`. -/
def toReal {n : ℕ} (p : Fin n → Fin 7) : Fin n → ℝ := fun i => ((p i : ℕ) : ℝ)

/-- `a n`: the number of collinear `6`-element sets of points of the `7^n` grid (OEIS A178297). -/
noncomputable def a (n : ℕ) : ℕ :=
  {s : Finset (Fin n → Fin 7) | s.card = 6 ∧ Collinear ℝ (toReal '' (s : Set (Fin n → Fin 7)))}.ncard

/-- Mathar's conjectured closed form for OEIS A178297. -/
theorem main : ∀ n : ℕ, 2 * (a n : ℤ) = 11 ^ n + 5 * 9 ^ n - 6 * 7 ^ n := by
  sorry

end OMA.S_oeis_a178297
