import FormalConjectures.OptimizationConstants.«14»

namespace OMA.R_Constant14_c14_ge_5_R1

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory Turing BusyBeaver

/-- The existing three-state lower-bound project supplies this premise. -/
def H1 : Prop := 4 ≤ Constant14.C14

/-- Produce the embedded ZFC proof from a bounded four-state halting trace.
The step after the last executed instruction returns none. -/
def H2 : Prop := ∀ M : Machine (Fin 2) (Fin 4),
  M.multiStep (Machine.init []) 108 = none →
    FFL.Entailment.Provable 𝗭𝗙𝗖 (Constant14.halts M)

/-- Certify nonhalting in the embedded ZFC calculus for four-state machines
still live at the end of the bounded simulation. -/
def H3 : Prop := ∀ M : Machine (Fin 2) (Fin 4),
  M.multiStep (Machine.init []) 108 ≠ none →
    FFL.Entailment.Provable 𝗭𝗙𝗖 (∼Constant14.halts M)

theorem main : H1 → H2 → H3 → type_of% @Constant14.c14_ge_5 := by
  classical
  intro lower halted live
  let sizes : Set ℕ := {n | ∃ _ : NeZero n, ∃ M : Machine (Fin 2) (Fin n),
    𝗭𝗙𝗖 ⊬ Constant14.halts M ∧ 𝗭𝗙𝗖 ⊬ ∼Constant14.halts M}
  change 4 ≤ sInf sizes at lower
  change 5 ≤ sInf sizes
  have inhabitedSizes : sizes.Nonempty := by
    by_contra empty
    rw [Set.not_nonempty_iff_eq_empty.mp empty, Nat.sInf_empty] at lower
    omega
  have fourExcluded : 4 ∉ sizes := by
    rintro ⟨hn, M, noHaltProof, noNonhaltProof⟩
    by_cases h : M.multiStep (Machine.init []) 108 = none
    · exact noHaltProof (halted M h)
    · exact noNonhaltProof (live M h)
  have minimumIn := Nat.sInf_mem inhabitedSizes
  by_contra small
  have eqFour : sInf sizes = 4 := by omega
  exact fourExcluded (eqFour ▸ minimumIn)

end OMA.R_Constant14_c14_ge_5_R1
