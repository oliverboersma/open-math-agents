import Mathlib

/-!
# MathOverflow 386285

Source: https://mathoverflow.net/questions/386285
-/

namespace OMA.S_mo_386285

open Set Filter Topology

theorem main : ∃ (G : Type) (group : AddGroup G) (top : TopologicalSpace G),
    letI := group
    letI := top
    T2Space G ∧ Continuous (fun xy : G × G => xy.1 + xy.2) ∧
      ¬ Continuous (fun x : G => -x) := by
  sorry

end OMA.S_mo_386285
