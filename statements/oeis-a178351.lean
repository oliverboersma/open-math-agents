import Mathlib

/-!
# A178351: Mathar's closed form for collinear 5-point subsets of the `7^n` grid

Source: https://oeis.org/A178351
Credit: @sntntHb

`a(n)` is the number of collinear point 5-tuples in a 7 X 7 X ... n-dimensional cubic grid, i.e. the
number of `5`-element sets of points of `{0, ..., 6}^n` that lie on a common line. The entry
records a conjecture of R. J. Mathar (May 25 2010):
`a(n) = 2*11^n+13^n/2+5*9^n-15*7^n/2`, equivalently `a(n) = 40*a(n-1) - 590*a(n-2) + 3800*a(n-3) - 9009*a(n-4)`.

The grid point `p : Fin n → Fin 7` is viewed as the real point `fun i => (p i : ℝ)`, and a set of
grid points is collinear when its image is `Collinear ℝ` in `Fin n → ℝ`. `a n` counts the sets of
grid points of cardinality `5` with collinear image. This matches the data: for `n = 0` the grid
has a single point and `a 0 = 0`; for `n = 1` every `5`-subset of `7` points on a line counts,
giving `a 1 = 21`, and the line-by-line count gives `a 2 = 364` and `a 3 = 4833` as listed.

`main` states the conjectured closed form, multiplied by `2` to clear denominators and read in `ℤ`.
-/

namespace OMA.S_oeis_a178351

/-- The grid point `p` of `{0, ..., 6}^n` as a point of `ℝ^n`. -/
def toReal {n : ℕ} (p : Fin n → Fin 7) : Fin n → ℝ := fun i => ((p i : ℕ) : ℝ)

/-- `a n`: the number of collinear `5`-element sets of points of the `7^n` grid (OEIS A178351). -/
noncomputable def a (n : ℕ) : ℕ :=
  {s : Finset (Fin n → Fin 7) | s.card = 5 ∧ Collinear ℝ (toReal '' (s : Set (Fin n → Fin 7)))}.ncard

/-- Mathar's conjectured closed form for OEIS A178351. -/
theorem main : ∀ n : ℕ, 2 * (a n : ℤ) = 4 * 11 ^ n + 13 ^ n + 10 * 9 ^ n - 15 * 7 ^ n := by
  sorry

end OMA.S_oeis_a178351
