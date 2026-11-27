import OMAReductions.R_Green14_W_3_15_R1
import Mathlib

/-! Split the red endpoint case by the midpoint and the distance to its next red point. -/

-- Credit: @Genbox

namespace OMA.R_Green14_W_3_15_R1_H1_R1

def H1 : Prop :=
  ∀ r : Fin 217 → Bool, r 108 = true →
    (∀ i : Fin 217, 109 ≤ i.val → i.val ≤ 115 → r i = false) →
    (∀ a d : Fin 217, 0 < d.val → a.val + 2 * d.val < 217 →
      ¬ ∀ t : Fin 3, r (Fin.ofNat 217 (a.val + t.val * d.val)) = true) →
    (∀ a d : Fin 217, 0 < d.val → a.val + 14 * d.val < 217 →
      ¬ ∀ t : Fin 15, r (Fin.ofNat 217 (a.val + t.val * d.val)) = false) →
    ∃ d : Fin 109, 0 < d.val ∧ ∀ t : Fin 2,
      r (Fin.ofNat 217 (217 - (2 - t.val) * d.val)) = true

def H2 : Prop :=
  ∀ r : Fin 217 → Bool, r 108 = true →
    (∃ i : Fin 217, 109 ≤ i.val ∧ i.val ≤ 115 ∧ r i = true) →
    (∀ a d : Fin 217, 0 < d.val → a.val + 2 * d.val < 217 →
      ¬ ∀ t : Fin 3, r (Fin.ofNat 217 (a.val + t.val * d.val)) = true) →
    (∀ a d : Fin 217, 0 < d.val → a.val + 14 * d.val < 217 →
      ¬ ∀ t : Fin 15, r (Fin.ofNat 217 (a.val + t.val * d.val)) = false) →
    ∃ d : Fin 109, 0 < d.val ∧ ∀ t : Fin 2,
      r (Fin.ofNat 217 (217 - (2 - t.val) * d.val)) = true

def H3 : Prop :=
  ∀ r : Fin 217 → Bool, r 108 = false →
    (∀ a d : Fin 217, 0 < d.val → a.val + 2 * d.val < 217 →
      ¬ ∀ t : Fin 3, r (Fin.ofNat 217 (a.val + t.val * d.val)) = true) →
    (∀ a d : Fin 217, 0 < d.val → a.val + 14 * d.val < 217 →
      ¬ ∀ t : Fin 15, r (Fin.ofNat 217 (a.val + t.val * d.val)) = false) →
    ∃ d : Fin 109, 0 < d.val ∧ ∀ t : Fin 2,
      r (Fin.ofNat 217 (217 - (2 - t.val) * d.val)) = true

theorem main : H1 → H2 → H3 → OMA.R_Green14_W_3_15_R1.H1 := by
  intro wide close blue r noRed noBlue
  cases midpoint : r 108
  · exact blue r midpoint noRed noBlue
  · by_cases gap : ∀ i : Fin 217, 109 ≤ i.val → i.val ≤ 115 → r i = false
    · exact wide r midpoint gap noRed noBlue
    · push_neg at gap
      obtain ⟨i, low, high, red⟩ := gap
      have redTrue : r i = true := by
        cases hc : r i
        · exact False.elim (red hc)
        · rfl
      exact close r midpoint ⟨i, low, high, redTrue⟩ noRed noBlue

end OMA.R_Green14_W_3_15_R1_H1_R1