import OMAReductions.R_Green14_W_3_14_R1_H2_R1

/-! Six first-red cases in the same 182-position interval as the outer gaps. -/

namespace OMA.R_Green14_W_3_14_R1_H2_R1_H4_R1

def H1 : Prop :=
  ∀ (c : Nat → Bool) (p : Nat), p ∈ ([98] : List Nat) →
    c 86 = true → c p = true → (∀ q : Nat, 86 < q → q < p → c q = false) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 182 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

def H2 : Prop :=
  ∀ (c : Nat → Bool) (p : Nat), p ∈ ([95,100] : List Nat) →
    c 86 = true → c p = true → (∀ q : Nat, 86 < q → q < p → c q = false) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 182 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

def H3 : Prop :=
  ∀ (c : Nat → Bool) (p : Nat), p ∈ ([96,97] : List Nat) →
    c 86 = true → c p = true → (∀ q : Nat, 86 < q → q < p → c q = false) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 182 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

def H4 : Prop :=
  ∀ (c : Nat → Bool) (p : Nat), p ∈ ([99] : List Nat) →
    c 86 = true → c p = true → (∀ q : Nat, 86 < q → q < p → c q = false) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 182 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

theorem main : H1 → H2 → H3 → H4 → OMA.R_Green14_W_3_14_R1_H2_R1.H4 := by
  intro h1 h2 h3 h4 c p lower upper anchor red gap
  rcases (show p = 95 ∨ p = 96 ∨ p = 97 ∨ p = 98 ∨ p = 99 ∨ p = 100 by omega) with
    h | h | h | h | h | h
  · exact h2 c p (by simp [h]) anchor red gap
  · exact h3 c p (by simp [h]) anchor red gap
  · exact h3 c p (by simp [h]) anchor red gap
  · exact h1 c p (by simp [h]) anchor red gap
  · exact h4 c p (by simp [h]) anchor red gap
  · exact h2 c p (by simp [h]) anchor red gap

end OMA.R_Green14_W_3_14_R1_H2_R1_H4_R1