import Mathlib

/-!
# Black-square queens and the five residue-class formulas in A352241

Source: https://oeis.org/A352241 (OEIS Foundation, CC BY-SA 4.0).
Formalization: @physbuzz.

Use the source's offset 1 and zero-based coordinates, with the top-left
square black. Distinct occupied squares must occupy distinct rows, columns,
and diagonals of both slopes. Andy Huchala reported counterexamples to the
displayed conjecture at board orders 52 and 57 in April 2024.
-/

namespace OMA.S_oeis_a352241

abbrev Square (n : ℕ) := Fin n × Fin n

/-- Label of the diagonal on which the sum of coordinates is constant. -/
def sumLine {n : ℕ} (p : Square n) : Fin (2*n) :=
  ⟨p.1.val+p.2.val, by have := p.1.isLt; have := p.2.isLt; omega⟩

/-- The difference of the coordinates shifted up by n-1. -/
def diffLine {n : ℕ} (p : Square n) : Fin (2*n) :=
  ⟨p.1.val+(n-1-p.2.val), by have := p.1.isLt; have := p.2.isLt; omega⟩

def valid {n : ℕ} (s : Finset (Square n)) : Prop :=
  (∀ p ∈ s, (p.1.val+p.2.val)%2 = 0) ∧
  Set.InjOn Prod.fst (s : Set (Square n)) ∧ Set.InjOn Prod.snd (s : Set (Square n)) ∧
  Set.InjOn sumLine (s : Set (Square n)) ∧ Set.InjOn diffLine (s : Set (Square n))

/-- The five proposed values, according to n modulo five. -/
def proposed (n : ℕ) : ℕ :=
  let k := n/5
  match n%5 with
  | 0 => 4*k-1
  | 1 => 4*k
  | 2 => 4*k+1
  | 3 => 4*k+1
  | _ => 4*k+2

theorem main : ∀ n : ℕ, 1 ≤ n →
    IsGreatest {k : ℕ | ∃ s : Finset (Square n), valid s ∧ s.card=k} (proposed n) := by
  sorry

end OMA.S_oeis_a352241
