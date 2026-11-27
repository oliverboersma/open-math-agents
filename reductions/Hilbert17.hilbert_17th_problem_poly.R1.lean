import FormalConjectures.HilbertProblems.«17»

-- Reduction Hilbert17.hilbert_17th_problem_poly.R1 of Hilbert's 17th problem for homogeneous
-- polynomials
-- Credit: @ihateSAS
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The polynomial side of Hilbert's 17th problem, split into its two implications

A homogeneous polynomial of degree `2 * d` in `n` variables that is nonnegative on all of `ℝⁿ`
need not be a sum of squares of polynomials.  Hilbert classified exactly when it is:

`Hilbert17thProblemHomogenousPoly n d` holds if and only if
`n = 1 ∨ n = 2 ∨ d = 1 ∨ (n = 3 ∧ d = 2)`.

The two directions are of completely different nature, so they are separated here:

* `H1` is the *negative* direction: outside those parameters there is a nonnegative homogeneous
  polynomial that is not a sum of squares of polynomials.  Concretely the Motzkin polynomial
  `x ^ 4 * y ^ 2 + x ^ 2 * y ^ 4 - 3 * x ^ 2 * y ^ 2 + 1` (already in the file as `Hilbert17.f`)
  rules out `n = 2`, `d = 3`, and rescalings/embeddings of it rule out the rest of the complement.

* `H2` is the *positive* direction, Hilbert's theorem itself: in dimensions `n ≤ 2`, in degree
  `2` (`d = 1`), and for ternary quartics (`n = 3`, `d = 2`), every nonnegative homogeneous
  polynomial is a sum of squares of polynomials.

Neither direction implies the other, and neither is a formal consequence of the statement: `H1`
produces nonnegative non-sos forms, `H2` is an existence theorem for sos representations.
-/

namespace OMA.R_Hilbert17_hilbert_17th_problem_poly_R1

/-- The negative direction: if every nonnegative homogeneous polynomial of degree `2 * d` in `n`
variables is a sum of squares of polynomials, then `(n, d)` is one of the Hilbert cases. -/
def H1 : Prop :=
  ∀ {n d : ℕ}, 0 < n → 0 < d →
    Hilbert17.Hilbert17thProblemHomogenousPoly n d →
      (n = 1 ∨ n = 2 ∨ d = 1 ∨ n = 3 ∧ d = 2)

/-- The positive direction, Hilbert's theorem: for `n ≤ 2`, for `d = 1`, and for ternary quartics,
every nonnegative homogeneous polynomial is a sum of squares of polynomials. -/
def H2 : Prop :=
  ∀ {n d : ℕ}, 0 < n → 0 < d →
    (n = 1 ∨ n = 2 ∨ d = 1 ∨ n = 3 ∧ d = 2) →
      Hilbert17.Hilbert17thProblemHomogenousPoly n d

theorem main : H1 → H2 →
    type_of% @Hilbert17.hilbert_17th_problem_poly :=
  fun h1 h2 {_n _d} hn hd => ⟨h1 hn hd, h2 hn hd⟩

end OMA.R_Hilbert17_hilbert_17th_problem_poly_R1
