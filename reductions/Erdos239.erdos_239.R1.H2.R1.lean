import OMAReductions.R_Erdos239_erdos_239_R1
import Mathlib

-- Credit: @marcusbuffett
namespace OMA.R_Erdos239_erdos_239_R1_H2_R1
open Finset Filter Real
open scoped Topology

/-- Compactness upgrades pointwise divergence to a common finite prime sum. -/
def H1 : Prop :=
  ∀ f : ℕ → ℝ, (∀ n ≥ 1, |f n| ≤ 1) →
    (∀ t : ℝ, ¬ Summable (fun p : Nat.Primes =>
      (1 - f p * cos (t * log p.val)) / p.val)) →
    ∀ T B : ℝ, ∃ S : Finset Nat.Primes, ∀ t ∈ Set.Icc (-T) T,
      B < ∑ p ∈ S, (1 - f p * cos (t * log p.val)) / p.val

/-- The uniform-distance form of the Halász mean-value estimate. -/
def H2 : Prop :=
  ∀ f : ℕ → ℝ, (∀ n ≥ 1, |f n| ≤ 1) →
    (∀ m n, m.Coprime n → f (m*n) = f m * f n) → f 1 = 1 →
    (∀ T B : ℝ, ∃ S : Finset Nat.Primes, ∀ t ∈ Set.Icc (-T) T,
      B < ∑ p ∈ S, (1 - f p * cos (t * log p.val)) / p.val) →
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, f n) / N) atTop (𝓝 0)

theorem main : H1 → H2 → OMA.R_Erdos239_erdos_239_R1.H2 := by
  intro compact mean f hf hm hone hdiv
  exact mean f hf hm hone (compact f hf hdiv)

end OMA.R_Erdos239_erdos_239_R1_H2_R1
