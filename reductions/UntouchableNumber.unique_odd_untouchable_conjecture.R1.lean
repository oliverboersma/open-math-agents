import FormalConjectures.Wikipedia.UntouchableNumber

-- Reduction UntouchableNumber.unique_odd_untouchable_conjecture.R1 of the unique odd untouchable number conjecture
-- Credit: @ivillar
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
The conjecture is an equivalence for odd m. `H1` is the direction that 5 is untouchable.
`H2` is the open direction: no other odd number is untouchable.
-/

namespace OMA.R_UntouchableNumber_unique_odd_untouchable_conjecture_R1

/-- The number 5 is untouchable. -/
def H1 : Prop := Nat.IsUntouchable 5

/-- The open direction: an odd untouchable number is 5. -/
def H2 : Prop := ∀ m : ℕ, Odd m → m.IsUntouchable → m = 5

theorem main : H1 → H2 → type_of% @UntouchableNumber.unique_odd_untouchable_conjecture := by
  intro h1 h2 m hodd
  refine ⟨h2 m hodd, ?_⟩
  rintro rfl
  exact h1

end OMA.R_UntouchableNumber_unique_odd_untouchable_conjecture_R1
