import Mathlib

/-!
# A178299: Mathar's closed form for collinear 4-point subsets of the `6^n` grid

Source: https://oeis.org/A178299
Credit: @sntntHb

`a(n)` is the number of collinear point 4-tuples in a 6 X 6 X ... n-dimensional cubic grid, i.e. the
number of `4`-element sets of points of `{0, ..., 5}^n` that lie on a common line. The entry
records a conjecture of R. J. Mathar (May 24 2010):
`a(n) = 3*8^n+3*10^n/2-5*6^n+12^n/2`, equivalently `a(n) = 36*a(n-1) - 476*a(n-2) + 2736*a(n-3) - 5760*a(n-4)`.

The grid point `p : Fin n → Fin 6` is viewed as the real point `fun i => (p i : ℝ)`, and a set of
grid points is collinear when its image is `Collinear ℝ` in `Fin n → ℝ`. `a n` counts the sets of
grid points of cardinality `4` with collinear image. This matches the data: for `n = 0` the grid
has a single point and `a 0 = 0`; for `n = 1` every `4`-subset of `6` points on a line counts,
giving `a 1 = 15`, and the line-by-line count gives `a 2 = 234` and `a 3 = 2820` as listed.

`main` states the conjectured closed form, multiplied by `2` to clear denominators and read in `ℤ`.
-/

namespace OMA.S_oeis_a178299

/-- The grid point `p` of `{0, ..., 5}^n` as a point of `ℝ^n`. -/
def toReal {n : ℕ} (p : Fin n → Fin 6) : Fin n → ℝ := fun i => ((p i : ℕ) : ℝ)

/-- `a n`: the number of collinear `4`-element sets of points of the `6^n` grid (OEIS A178299). -/
noncomputable def a (n : ℕ) : ℕ :=
  {s : Finset (Fin n → Fin 6) | s.card = 4 ∧ Collinear ℝ (toReal '' (s : Set (Fin n → Fin 6)))}.ncard

/-- Mathar's conjectured closed form for OEIS A178299. -/
theorem main : ∀ n : ℕ, 2 * (a n : ℤ) = 6 * 8 ^ n + 3 * 10 ^ n - 10 * 6 ^ n + 12 ^ n := by
  sorry

end OMA.S_oeis_a178299
