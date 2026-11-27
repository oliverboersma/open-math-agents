import FormalConjectures.ErdosProblems.«743»
import Mathlib

/-! The tree packing conjecture for trees of bounded degree (Joos, Kim, Kühn and Osthus)
from the theorem of Allen, Böttcher, Clemens, Hladký, Piguet and Taraz, The tree packing
conjecture for trees of almost linear maximum degree (arXiv 2106.11720): the trees pack for
large n whenever all maximum degrees are at most c n / log n. This is the catalogue's
Erdos743.erdos_743.variants.almost_linear_degree. A fixed degree bound d is eventually below
c n / log n, which is a statement about real functions only. -/

namespace OMA.R_Erdos743_erdos_743_variants_bounded_degree_R1
open Filter Classical

/-- The theorem of Allen, Böttcher, Clemens, Hladký, Piguet and Taraz. -/
def H1 : Prop := ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ T : (k : ℕ) → SimpleGraph (Fin k),
  (∀ k ∈ Set.Icc 2 n,
    (T k).IsTree ∧ ((T k).maxDegree : ℝ) ≤ c * (n : ℝ) / Real.log (n : ℝ)) →
    Erdos743.IsPacking n (Set.Icc 2 n) T

/-- Every constant is eventually at most c n / log n. -/
def H2 : Prop := ∀ c : ℝ, 0 < c → ∀ d : ℕ,
  ∀ᶠ n : ℕ in atTop, (d : ℝ) ≤ c * (n : ℝ) / Real.log (n : ℝ)

theorem main : H1 → H2 → type_of% @Erdos743.erdos_743.variants.bounded_degree := by
  rintro ⟨c, hc, h1⟩ h2 d
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h1.and (h2 c hc d))
  refine ⟨N, fun n hn T hT => (hN n hn).1 T fun k hk => ⟨(hT k hk).1, ?_⟩⟩
  exact le_trans (by exact_mod_cast (hT k hk).2) (hN n hn).2

end OMA.R_Erdos743_erdos_743_variants_bounded_degree_R1
