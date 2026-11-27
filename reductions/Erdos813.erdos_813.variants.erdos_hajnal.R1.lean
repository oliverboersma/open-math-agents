import FormalConjectures.ErdosProblems.«813»
import Mathlib

/-! The Erdős and Hajnal bounds n^(1/3) ≪ h(n) ≪ n^(1/2), split into their two halves. The
upper bound is the construction of Erdős and Hajnal. The lower bound follows from the stronger
bound n^(2/5) ≪ h(n), a special case of Bucić and Sudakov, Large independent sets from local
considerations (arXiv 2007.03667), which is formalized as the catalogue's
Erdos813.erdos_813.variants.lower. -/

namespace OMA.R_Erdos813_erdos_813_variants_erdos_hajnal_R1
open Filter Asymptotics

/-- Erdős and Hajnal: the upper bound h(n) ≪ n^(1/2). -/
def H1 : Prop := (fun n : ℕ ↦ (Erdos813.h n : ℝ)) =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (1 / 2 : ℝ))

/-- The lower bound n^(1/3) ≪ h(n). -/
def H2 : Prop := (fun n : ℕ ↦ (n : ℝ) ^ (1 / 3 : ℝ)) =O[atTop] (fun n : ℕ ↦ (Erdos813.h n : ℝ))

theorem main : H1 → H2 → type_of% @Erdos813.erdos_813.variants.erdos_hajnal :=
  fun h1 h2 => ⟨h2, h1⟩

end OMA.R_Erdos813_erdos_813_variants_erdos_hajnal_R1
