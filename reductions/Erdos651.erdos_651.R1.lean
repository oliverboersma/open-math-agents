import FormalConjectures.ErdosProblems.«651»
import Mathlib

/-! Erdős Problem 651 asks whether f_k(n) grows exponentially for every k ≥ 3. Pohoata and
Zakharov, Convex polytopes from fewer points (arXiv 2208.04878), Theorem 1.1, proved
f_3(n) ≤ 2^(o(n)); for k = 3 this is the catalogue's
Erdos651.erdos_651.variants.pohoata_zakharov. A sequence with a bound 2^(eps n) for every
positive eps cannot eventually exceed (1 + c)^n for a fixed positive c, which is a statement
about real sequences only, so the answer is no already for k = 3. -/

namespace OMA.R_Erdos651_erdos_651_R1
open Filter

/-- Pohoata and Zakharov: f_3(n) ≤ 2^(eps n) for every positive eps and all large n. -/
def H1 : Prop := ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
  (Erdos651.f 3 n : ℝ) ≤ (2 : ℝ) ^ (ε * (n : ℝ))

/-- A real sequence bounded by 2^(eps n) for every positive eps is not eventually above
(1 + c)^n for any positive c. -/
def H2 : Prop := ∀ F : ℕ → ℝ,
  (∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, F n ≤ (2 : ℝ) ^ (ε * (n : ℝ))) →
  ¬ ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (1 + c) ^ n < F n

theorem main : H1 → H2 → type_of% @Erdos651.erdos_651 := by
  intro h1 h2 hall
  exact h2 (fun n => (Erdos651.f 3 n : ℝ)) h1 (hall 3 le_rfl)

end OMA.R_Erdos651_erdos_651_R1
