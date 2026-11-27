import FormalConjectures.ErdosProblems.«626»
import Mathlib

/-! For even m, Erdős expected the exponent of the largest chromatic number h^(m)(n) of a graph
on n vertices with girth greater than m to lie between 2/(m+2) and 2/m. The upper half is known:
girth greater than m implies girth greater than m - 1, and for the odd number m - 1 the bound of
Erdős (the catalogue's solved variant Erdos626.erdos_626.variants.h_upper_odd) gives the
exponent 2/m. The lower half is the open part; Erdős could not prove it even for m = 4. -/

namespace OMA.R_Erdos626_erdos_626_variants_h_even_conjecture_R1

open Filter

/-- The known upper half: h^(m)(n) <= n^(2/m + eps) for even m. -/
def H1 : Prop :=
  ∀ m : ℕ, Even m → 2 ≤ m → ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    (Erdos626.h m n : ℝ) ≤ (n : ℝ) ^ (2 / (m : ℝ) + ε)

/-- The open lower half: n^(2/(m+2) - eps) <= h^(m)(n) for even m. -/
def H2 : Prop :=
  ∀ m : ℕ, Even m → 2 ≤ m → ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    (n : ℝ) ^ (2 / ((m : ℝ) + 2) - ε) ≤ (Erdos626.h m n : ℝ)

theorem main : H1 → H2 → type_of% @Erdos626.erdos_626.variants.h_even_conjecture := by
  intro h1 h2 m hm hm2 ε hε
  filter_upwards [h1 m hm hm2 ε hε, h2 m hm hm2 ε hε] with n hu hl
  exact ⟨hl, hu⟩

end OMA.R_Erdos626_erdos_626_variants_h_even_conjecture_R1
