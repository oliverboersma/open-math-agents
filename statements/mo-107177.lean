import Mathlib.Probability.ProductMeasure
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Simultaneous strong laws and countable Glivenko–Cantelli decompositions

Alexander R. Pruss, MathOverflow 107177, September 14, 2012.
https://mathoverflow.net/questions/107177

The proposition is the proposed implication in the source. A negative answer
would prove its negation. We use the canonical iid sequence with law `μ`, the
coordinate projections on the infinite product with measure `μ` to each factor.
Every Borel iid sequence with this law has that same joint distribution.
-/

namespace OMA.S_mo_107177

open MeasureTheory Filter
open scoped Topology

/-- Empirical frequency among the first `n` observations. The value at zero
has no effect on convergence at infinity. -/
noncomputable def empirical {V : Type*} (x : ℕ → V) (A : Set V) (n : ℕ) : ℝ := by
  classical
  exact ((Finset.range n).filter (fun k => x k ∈ A)).card / (n : ℝ)

/-- One measurable event of full product measure on which the whole assertion
holds. This also handles classes whose supremum error is not measurable. -/
def onFullEvent {V : Type*} [MeasurableSpace V] (μ : Measure V)
    (P : (ℕ → V) → Prop) : Prop :=
  ∃ E : Set (ℕ → V), MeasurableSet E ∧
    (Measure.infinitePi (fun _ : ℕ => μ)) E = 1 ∧ ∀ x ∈ E, P x

/-- The full event is chosen once per law, before the member of `C`. -/
def simultaneousStrongLaw {V : Type*} [MeasurableSpace V] (C : Set (Set V)) : Prop :=
  ∀ μ : Measure V, IsProbabilityMeasure μ → onFullEvent μ (fun x =>
    ∀ A ∈ C, Tendsto (empirical x A) atTop (𝓝 (μ.real A)))

/-- One cutoff works for every member of the class, for each sample and
positive tolerance. The event may depend on the probability law. -/
def universallyGlivenkoCantelli {V : Type*} [MeasurableSpace V] (C : Set (Set V)) : Prop :=
  ∀ μ : Measure V, IsProbabilityMeasure μ → onFullEvent μ (fun x =>
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ A ∈ C, |empirical x A n - μ.real A| < ε)

theorem main :
    ∀ (V : Type) [TopologicalSpace V] [PolishSpace V] [MeasurableSpace V] [BorelSpace V]
      (C : Set (Set V)), (∀ A ∈ C, MeasurableSet A) → simultaneousStrongLaw C →
        ∃ G : ℕ → Set (Set V), C = (⋃ j, G j) ∧ ∀ j, universallyGlivenkoCantelli (G j) := by
  sorry

end OMA.S_mo_107177
