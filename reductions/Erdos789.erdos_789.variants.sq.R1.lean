import FormalConjectures.ErdosProblems.«789»
import Mathlib

/-! The question whether h(n) = Theta(sqrt n) for the Erdős--Straus subset-sum threshold has two
halves. The upper bound h(n) = O(sqrt n) is the theorem of Straus (On a problem in combinatorial
number theory, J. Math. Sci. 1966); it is the catalogue's solved variant
Erdos789.erdos_789.variants.isBigO_sq. The lower bound sqrt n = O(h(n)) is the open part; it is
the catalogue's Erdos789.erdos_789.variants.sq_isBigO. -/

namespace OMA.R_Erdos789_erdos_789_variants_sq_R1

open Filter Asymptotics

/-- Straus's upper bound for the subset-sum threshold. -/
def H1 : Prop :=
  (fun n : ℕ ↦ (Erdos789.subsetSumThreshold n : ℝ)) =O[atTop] fun n : ℕ ↦ Real.sqrt (n : ℝ)

/-- The open lower bound of order sqrt n. -/
def H2 : Prop :=
  (fun n : ℕ ↦ Real.sqrt (n : ℝ)) =O[atTop] fun n : ℕ ↦ (Erdos789.subsetSumThreshold n : ℝ)

theorem main : H1 → H2 → type_of% @Erdos789.erdos_789.variants.sq := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_Erdos789_erdos_789_variants_sq_R1
