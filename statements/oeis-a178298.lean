import Mathlib

/-!
# A178298: Mathar's closed form for collinear 3-point subsets of the `5^n` grid

Source: https://oeis.org/A178298
Credit: @sntntHb

`a(n)` is the number of collinear point triples in a 5 X 5 X ... n-dimensional cubic grid, i.e. the
number of `3`-element sets of points of `{0, ..., 4}^n` that lie on a common line. The entry
records a conjecture of R. J. Mathar (May 24 2010):
`a(n) = 7^n - 5^(n+1)/2 + 13^n/2 + 9^n`, equivalently `a(n) = 34*a(n-1) - 416*a(n-2) + 2174*a(n-3) - 4095*a(n-4)`.

The grid point `p : Fin n → Fin 5` is viewed as the real point `fun i => (p i : ℝ)`, and a set of
grid points is collinear when its image is `Collinear ℝ` in `Fin n → ℝ`. `a n` counts the sets of
grid points of cardinality `3` with collinear image. This matches the data: for `n = 0` the grid
has a single point and `a 0 = 0`; for `n = 1` every `3`-subset of `5` points on a line counts,
giving `a 1 = 10`, and the line-by-line count gives `a 2 = 152` and `a 3 = 1858` as listed.

`main` states the conjectured closed form, multiplied by `2` to clear denominators and read in `ℤ`.
-/

namespace OMA.S_oeis_a178298

/-- The grid point `p` of `{0, ..., 4}^n` as a point of `ℝ^n`. -/
def toReal {n : ℕ} (p : Fin n → Fin 5) : Fin n → ℝ := fun i => ((p i : ℕ) : ℝ)

/-- `a n`: the number of collinear `3`-element sets of points of the `5^n` grid (OEIS A178298). -/
noncomputable def a (n : ℕ) : ℕ :=
  {s : Finset (Fin n → Fin 5) | s.card = 3 ∧ Collinear ℝ (toReal '' (s : Set (Fin n → Fin 5)))}.ncard

/-- Mathar's conjectured closed form for OEIS A178298. -/
theorem main : ∀ n : ℕ, 2 * (a n : ℤ) = 2 * 7 ^ n - 5 * 5 ^ n + 13 ^ n + 2 * 9 ^ n := by
  sorry

end OMA.S_oeis_a178298
