import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.List.Basic

/-!
# Arrays avoiding prime prefix and suffix sums

Source: https://oeis.org/A254211 (R. H. Hardin, OEIS Foundation, CC BY-SA 4.0).
Alois P. Heinz conjectures that infinitely many positive lengths admit an array
on {1,2,3} with unequal neighbors and no prime prefix or suffix sum.
-/

namespace OMA.S_oeis_a254211

def validSteps (previous : ℕ) : List ℕ → Prop
  | [] => True
  | d::xs => 1 ≤ d ∧ d ≤ 3 ∧ d ≠ previous ∧ validSteps d xs

/-- Test each nonempty prefix, starting with sum s. -/
def sumsSatisfy (P : ℕ → Prop) (s : ℕ) : List ℕ → Prop
  | [] => True
  | d::xs => P (s+d) ∧ sumsSatisfy P (s+d) xs

def valid (xs : List ℕ) : Prop :=
  validSteps 0 xs ∧ sumsSatisfy (fun x => ¬ x.Prime) 0 xs ∧
    sumsSatisfy (fun x => ¬ x.Prime) 0 xs.reverse

theorem main : ∀ B : ℕ, ∃ xs : List ℕ, B < xs.length ∧ valid xs := by
  sorry

end OMA.S_oeis_a254211
