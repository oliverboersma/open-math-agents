import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Fin

/-!
Proposed formal statement of the two fixed-column conjectures in OEIS A401159.
Rows and columns are labelled; matrices are not identified under permutations.
The single placeholder below is required only for the site's statement-review
stage.  The accompanying proof file proves this proposition independently.
-/

namespace OMA.S_oeis_a401159

/-- Every column and every row has at most two entries equal to one. -/
def Admissible {n m : ℕ} (A : Fin n → Fin m → Bool) : Prop :=
  (∀ j, (Finset.univ.filter (fun i => A i j = true)).card ≤ 2) ∧
  (∀ i, (Finset.univ.filter (fun j => A i j = true)).card ≤ 2)

/-- The number of labelled binary matrices satisfying the row and column bounds. -/
noncomputable def T (n m : ℕ) : ℕ := by
  classical
  exact Fintype.card {A : Fin n → Fin m → Bool // Admissible A}

/-- Both conjectured formulas, on the original triangular-array domains.
The second equality clears the denominator eight in the OEIS polynomial. -/
theorem main :
    (∀ n : ℕ, 2 ≤ n → T n 2 = (1 + n + Nat.choose n 2) ^ 2) ∧
    (∀ n : ℕ, 3 ≤ n →
      8 * T n 3 =
        8 + 8 * n + 22 * n ^ 2 + 13 * n ^ 3 + n ^ 4 + 3 * n ^ 5 + n ^ 6) := by
  sorry

end OMA.S_oeis_a401159
