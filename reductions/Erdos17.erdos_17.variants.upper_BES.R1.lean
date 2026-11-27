import FormalConjectures.ErdosProblems.«17»
import Mathlib

/-! The Blomer, Elsholtz and Schlage-Puchta bound for cluster primes from Elsholtz's stronger
one. Elsholtz, On cluster primes, Acta Arith. 109 (2003), bounds the number of cluster primes
up to x by x exp (-c (log log x)^2) for every c < 1/8; this is the catalogue's
Erdos17.erdos_17.variants.upper_Elsholtz. For every A the function x exp (-c (log log x)^2)
is O(x / (log x)^A), because (log x)^A = exp (A log log x) and c y^2 ≥ A y once y ≥ A / c.
That comparison is a statement about real functions only. -/

namespace OMA.R_Erdos17_erdos_17_variants_upper_BES_R1
open Filter Asymptotics

/-- Elsholtz's bound for the number of cluster primes. -/
def H1 : Prop := ∃ C : ℝ, 0 < C ∧ ∀ c ∈ Set.Ioo (0 : ℝ) (1 / 8),
  IsBigOWith C atTop (fun x : ℕ ↦ (Erdos17.clusterPrimeCount x : ℝ))
    (fun x : ℕ ↦ (x : ℝ) * Real.exp (-c * (Real.log (Real.log x)) ^ 2))

/-- x exp (-c (log log x)^2) is O(x / (log x)^A) for all positive A and c. -/
def H2 : Prop := ∀ A : ℝ, 0 < A → ∀ c : ℝ, 0 < c →
  (fun x : ℕ ↦ (x : ℝ) * Real.exp (-c * (Real.log (Real.log x)) ^ 2)) =O[atTop]
    (fun x : ℕ ↦ (x : ℝ) / (Real.log x) ^ A)

theorem main : H1 → H2 → type_of% @Erdos17.erdos_17.variants.upper_BES := by
  rintro ⟨C, _, hC⟩ h2 A hA
  exact (hC (1 / 16) ⟨by norm_num, by norm_num⟩).isBigO.trans (h2 A hA (1 / 16) (by norm_num))

end OMA.R_Erdos17_erdos_17_variants_upper_BES_R1
