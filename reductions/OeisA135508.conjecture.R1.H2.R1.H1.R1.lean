import OMAReductions.R_OeisA135508_conjecture_R1_H2_R1
import Mathlib

/-! The finite prime-witness step has 78496 eligible moduli. Independent
trial-division certificates give multipliers bounded by 257, 277 and 259 on
the three remaining intervals. Restricting the witness search to these finite
multiplier ranges allows the separate certificates to be checked in parallel.
The 23 prime moduli at most 100 are discharged directly. -/

namespace OMA.R_OeisA135508_conjecture_R1_H2_R1_H1_R1

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem small : ∀ q : Fin 101, q.val.Prime → 5 ≤ q.val →
    ∃ m : Fin 20, let r := m.val * q.val - 2
      r.Prime ∧ 5 < r ∧ r < q.val^2 ∧ r % 3 = 2 ∧ q.val ∣ r+2 := by
  decide +kernel

def H1 : Prop := ∀ q : ℕ, q.Prime → 100 < q → q ≤ 100000 →
  ∃ m : Fin 258, let r := m.val * q - 2
    r.Prime ∧ 5 < r ∧ r < q^2 ∧ r % 3 = 2 ∧ q ∣ r+2

def H2 : Prop := ∀ q : ℕ, q.Prime → 100000 < q → q ≤ 500000 →
  ∃ m : Fin 278, let r := m.val * q - 2
    r.Prime ∧ 5 < r ∧ r < q^2 ∧ r % 3 = 2 ∧ q ∣ r+2

def H3 : Prop := ∀ q : ℕ, q.Prime → 500000 < q → q ≤ 1000000 →
  ∃ m : Fin 260, let r := m.val * q - 2
    r.Prime ∧ 5 < r ∧ r < q^2 ∧ r % 3 = 2 ∧ q ∣ r+2

theorem main : H1 → H2 → H3 → OMA.R_OeisA135508_conjecture_R1_H2_R1.H1 := by
  intro h1 h2 h3 q hq hlo hhi
  by_cases hs : q ≤ 100
  · obtain ⟨m, hm⟩ := small ⟨q, by omega⟩ hq hlo
    exact ⟨m.val * q - 2, hm⟩
  by_cases ha : q ≤ 100000
  · obtain ⟨m, hm⟩ := h1 q hq (by omega) ha
    exact ⟨m.val * q - 2, hm⟩
  by_cases hb : q ≤ 500000
  · obtain ⟨m, hm⟩ := h2 q hq (by omega) hb
    exact ⟨m.val * q - 2, hm⟩
  · obtain ⟨m, hm⟩ := h3 q hq (by omega) hhi
    exact ⟨m.val * q - 2, hm⟩

end OMA.R_OeisA135508_conjecture_R1_H2_R1_H1_R1
