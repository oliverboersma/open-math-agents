import Mathlib

/-!
# A178296: Mathar's closed form for collinear 5-point subsets of the `6^n` grid

Source: https://oeis.org/A178296
Credit: @sntntHb

`a(n)` is the number of collinear point 5-tuples in a 6 X 6 X ... n-dimensional cubic grid, i.e. the
number of `5`-element sets of points of `{0, ..., 5}^n` that lie on a common line. The entry
records a conjecture of R. J. Mathar (May 24 2010):
`a(n) = 10^n/2+2*8^n-5*6^n/2`, equivalently `a(n) = 24*a(n-1) - 188*a(n-2) + 480*a(n-3)`.

The grid point `p : Fin n → Fin 6` is viewed as the real point `fun i => (p i : ℝ)`, and a set of
grid points is collinear when its image is `Collinear ℝ` in `Fin n → ℝ`. `a n` counts the sets of
grid points of cardinality `5` with collinear image. This matches the data: for `n = 0` the grid
has a single point and `a 0 = 0`; for `n = 1` every `5`-subset of `6` points on a line counts,
giving `a 1 = 6`, and the line-by-line count gives `a 2 = 88` and `a 3 = 984` as listed.

`main` states the conjectured closed form, multiplied by `2` to clear denominators and read in `ℤ`.
-/

namespace OMA.S_oeis_a178296

/-- The grid point `p` of `{0, ..., 5}^n` as a point of `ℝ^n`. -/
def toReal {n : ℕ} (p : Fin n → Fin 6) : Fin n → ℝ := fun i => ((p i : ℕ) : ℝ)

/-- `a n`: the number of collinear `5`-element sets of points of the `6^n` grid (OEIS A178296). -/
noncomputable def a (n : ℕ) : ℕ :=
  {s : Finset (Fin n → Fin 6) | s.card = 5 ∧ Collinear ℝ (toReal '' (s : Set (Fin n → Fin 6)))}.ncard

/-- Mathar's conjectured closed form for OEIS A178296. -/
theorem main : ∀ n : ℕ, 2 * (a n : ℤ) = 10 ^ n + 4 * 8 ^ n - 5 * 6 ^ n := by
  sorry

end OMA.S_oeis_a178296
