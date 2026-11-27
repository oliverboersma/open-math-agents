import OMAReductions.R_Green14_W_3_14_R1_H2_R1

/-! The leaves of a color decision tree are collected into finite proof groups. -/

namespace OMA.R_Green14_W_3_14_R1_H2_R1_H2_R1

def H1 : Prop :=
  ∀ c : Nat → Bool, c 89 = true → c 95 = true →
    ((c 88 = true) ∨ (c 88 = false ∧ c 96 = true) ∨ (c 88 = false ∧ c 96 = false ∧ c 86 = true)) →
    (∀ q : Nat, 89 < q → q < 95 → c q = false) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 185 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

def H2 : Prop :=
  ∀ c : Nat → Bool, c 89 = true → c 95 = true →
    ((c 88 = false ∧ c 96 = false ∧ c 86 = false)) →
    (∀ q : Nat, 89 < q → q < 95 → c q = false) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 185 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

theorem main : H1 → H2 → OMA.R_Green14_W_3_14_R1_H2_R1.H2 := by
  intro h1 h2 c anchor red blue
  cases col88 : c 88 with
  | false =>
    cases col96 : c 96 with
    | false =>
      cases col86 : c 86 with
      | false =>
        exact h2 c anchor red ⟨col88, col96, col86⟩ blue
      | true =>
        exact h1 c anchor red (Or.inr (Or.inr ⟨col88, col96, col86⟩)) blue
    | true =>
      exact h1 c anchor red (Or.inr (Or.inl ⟨col88, col96⟩)) blue
  | true =>
    exact h1 c anchor red (Or.inl col88) blue

end OMA.R_Green14_W_3_14_R1_H2_R1_H2_R1