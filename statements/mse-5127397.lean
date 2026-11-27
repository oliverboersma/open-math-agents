import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Range

/-!
# Does the null-term criterion for series force the given norm to be ultrametric?

Credit: @lucasfreund2-cmd

Source: Mathematics Stack Exchange question 5127397,
https://math.stackexchange.com/questions/5127397/characterization-of-complete-ultrametric-vector-space

The question concerns normed vector spaces over arbitrary valued fields. It asks
whether convergence of a series exactly when its terms tend to zero implies
completeness and the strong triangle inequality for the given norm. Completeness
is not assumed. In the comments, the author confirms that the given norm is meant,
not merely the existence of an equivalent ultrametric norm. David Gao supplies
the counterexample consisting of two copies of a p-adic field with the sum norm.

Series convergence below means convergence of the ordinary sequence of partial
sums. It does not mean unconditional summability over all finite subsets.
-/

namespace OMA.S_mse_5127397

def SeriesConverges {E : Type*} [NormedAddCommGroup E] (u : ℕ → E) : Prop :=
  ∃ s : E, Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, u n)
    Filter.atTop (nhds s)

/-- The proposed converse to the null-term criterion in complete ultrametric spaces. -/
theorem main :
    ∀ (𝕜 E : Type) [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E],
      (∀ u : ℕ → E, SeriesConverges u ↔ Filter.Tendsto u Filter.atTop (nhds 0)) →
      CompleteSpace E ∧ ∀ x y : E, ‖x + y‖ ≤ max ‖x‖ ‖y‖ := by
  sorry

end OMA.S_mse_5127397
