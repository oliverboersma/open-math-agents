import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Are finite interval orders well-quasi-ordered by induced containment?

Richard P. Stanley, MathOverflow question 487213 (5 February 2025).
Source: https://mathoverflow.net/questions/487213 (CC BY-SA 4.0).

The vertices of a finite interval order are represented by distinct nonempty
closed real intervals. The lower endpoint of a larger interval in the strict
order must exceed the upper endpoint of the smaller interval. An induced
embedding preserves and reflects that order. The sequential formulation of
well-quasi-ordering is invariant under relabelling.
-/

namespace OMA.S_mo_487213

structure FiniteIntervalOrder where
  Vertex : Type
  finite : Fintype Vertex
  left : Vertex → ℝ
  right : Vertex → ℝ
  valid : ∀ x, left x ≤ right x
  distinct : Function.Injective (fun x => (left x, right x))

def Induced (P Q : FiniteIntervalOrder) : Prop :=
  ∃ f : P.Vertex ↪ Q.Vertex, ∀ x y, P.right x < P.left y ↔ Q.right (f x) < Q.left (f y)

/-- The proposed well-quasi-ordering on finite interval orders up to isomorphism. -/
theorem main : ∀ s : ℕ → FiniteIntervalOrder, ∃ i j : ℕ, i < j ∧ Induced (s i) (s j) := by
  sorry

end OMA.S_mo_487213
