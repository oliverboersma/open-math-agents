import FormalConjectures.OEIS.«69004»
import Mathlib

/-!
Separate the surviving asymptotic inequality from the three small values.
The sieve tests only the two possible square-root residues for each prime
congruent to one modulo four, after the parity and coprimality conditions.
-/

open Finset
open scoped Classical

namespace OMA.R_OeisA69004_conjecture2_variants_without_upper_bound_R1

def H1 : Prop :=
  ∀ n : ℕ, 1 < n → n.primeCounting ≤
    5 * ((Ico 1 n).filter (fun s => n%2 ≠ s%2 ∧ n.Coprime s ∧
      ∀ p ∈ range ((n^2+s^2).sqrt+1), p.Prime → p%4 = 1 → ¬ p ∣ n^2+s^2)).card

def H2 : Prop :=
  ∀ n : ℕ, OeisA69004.a n =
    ((Ico 1 n).filter (fun s => n%2 ≠ s%2 ∧ n.Coprime s ∧
      ∀ p ∈ range ((n^2+s^2).sqrt+1), p.Prime → p%4 = 1 → ¬ p ∣ n^2+s^2)).card

def H3 : Prop :=
  Nat.primeCounting 2 = OeisA69004.a 2 ∧ Nat.primeCounting 10 = OeisA69004.a 10 ∧
    5 * OeisA69004.a 12 = Nat.primeCounting 12

section Proof

theorem main : H1 → H2 → H3 →
    type_of% @OeisA69004.conjecture2.variants.without_upper_bound := by
  intro hsieve hCount hValues
  refine ⟨fun n hn => ?_,hValues⟩
  rw [hCount n]
  exact hsieve n hn

end Proof

end OMA.R_OeisA69004_conjecture2_variants_without_upper_bound_R1
