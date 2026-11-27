import FormalConjectures.ErdosProblems.«976»
import Mathlib

/-! Erdős's bound F(f, n) ≫ n (log n)^(c log log log n) for the greatest prime factor of
f(1) ... f(n) from Tenenbaum's stronger bound F(f, n) ≫ n exp ((log n)^c), which is the
catalogue's Erdos976.erdos_976.variants.tenenbaum. With y = log log n one has
(log n)^(log log log n) = exp (y log y) and exp ((log n)^c) = exp (exp (c y)), and
y log y ≤ exp (c y) for large y; that comparison is a statement about real functions only. -/

namespace OMA.R_Erdos976_erdos_976_variants_erdos_R1
open Filter Asymptotics

/-- Tenenbaum's lower bound for the greatest prime factor of f(1) ... f(n). -/
def H1 : Prop := ∀ f : Polynomial ℤ, Irreducible f → 2 ≤ f.natDegree →
  ∃ c > (0 : ℝ), (fun n : ℕ ↦ (n : ℝ) * Real.exp (Real.log n ^ c)) =O[atTop]
    fun n ↦ (Erdos976.F f n : ℝ)

/-- n (log n)^(log log log n) is O(n exp ((log n)^c)) for every positive c. -/
def H2 : Prop := ∀ c > (0 : ℝ),
  (fun n : ℕ ↦ (n : ℝ) * Real.log n ^ Real.log (Real.log (Real.log n))) =O[atTop]
    (fun n : ℕ ↦ (n : ℝ) * Real.exp (Real.log n ^ c))

theorem main : H1 → H2 → type_of% @Erdos976.erdos_976.variants.erdos := by
  intro h1 h2 f hf hd
  obtain ⟨c, hc, h⟩ := h1 f hf hd
  refine ⟨1, one_pos, ?_⟩
  simp only [one_mul]
  exact (h2 c hc).trans h

end OMA.R_Erdos976_erdos_976_variants_erdos_R1
