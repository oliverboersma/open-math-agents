import Mathlib

/-!
# Ehrhart's volume conjecture

Source: https://en.wikipedia.org/wiki/Ehrhart's_volume_conjecture
Credit: @prophetlabs

Source statement (Wikipedia, *List of unsolved problems in mathematics*): a convex body `K` in
`n` dimensions containing a single lattice point in its interior as its center of mass cannot
have volume greater than `(n + 1)^n / n!`.

Conventions used here:
* a convex body in `ℝⁿ` is a compact convex set with nonempty interior;
* the lattice is the integer lattice `ℤⁿ ⊆ ℝⁿ`;
* the center of mass of `K` is `(1 / vol K) • ∫_K x dx` (Lebesgue measure);
* the hypothesis is that the interior of `K` contains exactly one lattice point `c`, and that
  `c` is the center of mass of `K`.
-/

namespace OMA.S_wp_ehrhart_s_volume_conjecture

open MeasureTheory

/-- The integer lattice `ℤⁿ` inside `ℝⁿ`. -/
def integerLattice (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i, ∃ z : ℤ, x i = z}

/-- The center of mass of a set `K ⊆ ℝⁿ` with respect to Lebesgue measure. -/
noncomputable def centerOfMass {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) :
    EuclideanSpace ℝ (Fin n) :=
  (volume K).toReal⁻¹ • ∫ x in K, x

theorem main :
    ∀ (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))) (c : EuclideanSpace ℝ (Fin n)),
      Convex ℝ K → IsCompact K → (interior K).Nonempty →
      interior K ∩ integerLattice n = {c} →
      centerOfMass K = c →
      volume K ≤ ENNReal.ofReal (((n : ℝ) + 1) ^ n / (n.factorial : ℝ)) := by
  sorry

end OMA.S_wp_ehrhart_s_volume_conjecture
