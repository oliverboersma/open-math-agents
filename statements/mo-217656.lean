import Mathlib

/-!
# MathOverflow 217656

Source: https://mathoverflow.net/questions/217656
-/

namespace OMA.S_mo_217656

abbrev Selection (n r : ℕ) := {A : Finset (Fin n) // A.card = r}
abbrev Element {n r : ℕ} (A : Selection n r) := {a : Fin n // a ∈ A.val}

def hasExchangeFamily (n r : ℕ) : Prop :=
  ∃ maps : (A B : Selection n r) → Element A ≃ Element B,
    (∀ A B, (maps A B).symm = maps B A) ∧
    (∀ (A B : Selection n r) (e : Fin n) (hA : e ∈ A.val) (hB : e ∈ B.val),
      maps A B ⟨e, hA⟩ = ⟨e, hB⟩) ∧
    (∀ (A B C : Selection n r) (c : Element C), maps A B (maps C A c) = maps C B c)

theorem main : ∀ n r : ℕ, r ≤ n → hasExchangeFamily n r := by
  sorry

end OMA.S_mo_217656
