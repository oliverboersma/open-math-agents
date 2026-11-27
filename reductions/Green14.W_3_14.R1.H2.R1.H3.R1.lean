import OMAReductions.R_Green14_W_3_14_R1_H2_R1

/-! Each possible first red has a separate finite certificate. -/

namespace OMA.R_Green14_W_3_14_R1_H2_R1_H3_R1

def H1 : Prop :=
  ∀ c : Nat → Bool, c 89 = true → c 96 = true →
    (∀ q : Nat, 89 < q → q < 96 → c q = false) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 185 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

def H2 : Prop :=
  ∀ c : Nat → Bool, c 89 = true → c 97 = true →
    (∀ q : Nat, 89 < q → q < 97 → c q = false) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 185 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

theorem main : H1 → H2 → OMA.R_Green14_W_3_14_R1_H2_R1.H3 := by
  intro left right c p lower upper anchor red blue
  rcases (show p = 96 ∨ p = 97 by omega) with rfl | rfl
  · exact left c anchor red blue
  · exact right c anchor red blue

end OMA.R_Green14_W_3_14_R1_H2_R1_H3_R1