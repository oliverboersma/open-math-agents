import OMAReductions.R_Green14_W_3_14_R1_H2_R1

/-! The leaves of a color decision tree are collected into finite proof groups. -/

namespace OMA.R_Green14_W_3_14_R1_H2_R1_H1_R1

def H1 : Prop :=
  ∀ c : Nat → Bool, c 89 = true → c 94 = true →
    ((c 96 = true) ∨ (c 96 = false ∧ c 87 = false ∧ c 102 = true)) →
    (∀ q : Nat, 89 < q → q < 94 → c q = false) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 185 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

def H2 : Prop :=
  ∀ c : Nat → Bool, c 89 = true → c 94 = true →
    ((c 96 = false ∧ c 87 = true) ∨ (c 96 = false ∧ c 87 = false ∧ c 102 = false ∧ c 81 = true)) →
    (∀ q : Nat, 89 < q → q < 94 → c q = false) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 185 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

def H3 : Prop :=
  ∀ c : Nat → Bool, c 89 = true → c 94 = true →
    ((c 96 = false ∧ c 87 = false ∧ c 102 = false ∧ c 81 = false)) →
    (∀ q : Nat, 89 < q → q < 94 → c q = false) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 185 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

theorem main : H1 → H2 → H3 → OMA.R_Green14_W_3_14_R1_H2_R1.H1 := by
  intro h1 h2 h3 c anchor red blue
  cases col96 : c 96 with
  | false =>
    cases col87 : c 87 with
    | false =>
      cases col102 : c 102 with
      | false =>
        cases col81 : c 81 with
        | false =>
          exact h3 c anchor red ⟨col96, col87, col102, col81⟩ blue
        | true =>
          exact h2 c anchor red (Or.inr ⟨col96, col87, col102, col81⟩) blue
      | true =>
        exact h1 c anchor red (Or.inr ⟨col96, col87, col102⟩) blue
    | true =>
      exact h2 c anchor red (Or.inl ⟨col96, col87⟩) blue
  | true =>
    exact h1 c anchor red (Or.inl col96) blue

end OMA.R_Green14_W_3_14_R1_H2_R1_H1_R1