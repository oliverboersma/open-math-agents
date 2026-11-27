import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Set.Card

/-!
# Size of a b-matching constructed from b maximal matchings

Source: https://mathoverflow.net/questions/148821
Credit: @jpollard-cs

Mikkelsen asks which approximation ratios successive maximal matchings guarantee
against a maximum b-matching in a finite simple graph. The question gives no
candidate formula for general b. We state an exact characterization of the
guaranteed rational ratios by a finite system of endpoint-label inequalities.
Testing against every feasible comparison set is equivalent to testing the largest.
-/

namespace OMA.S_mo_148821

abbrev Edges (n : ℕ) := Finset (Sym2 (Fin n))

def degreeAt {n : ℕ} (E : Edges n) (v : Fin n) : ℕ :=
  (E.filter fun e => v ∈ e).card

def feasible {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (E : Edges n) : Prop :=
  (∀ e ∈ E, e ∈ G.edgeSet) ∧ ∀ v, degreeAt E v ≤ k

def legalRounds {b n : ℕ} (G : SimpleGraph (Fin n)) (R : Fin b → Edges n) : Prop :=
  (∀ i, feasible G 1 (R i)) ∧
  (∀ i j, i < j → Disjoint (R i) (R j)) ∧
  ∀ (i : Fin b) (e : Sym2 (Fin n)), e ∈ G.edgeSet →
    (∀ j, j ≤ i → e ∉ R j) → ∃ f ∈ R i, ∃ v : Fin n, v ∈ e ∧ v ∈ f

def guaranteed (b p q : ℕ) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (R : Fin b → Edges n) (O : Edges n),
    legalRounds G R → feasible G b O → p * O.card ≤ q * ∑ i, (R i).card

abbrev Label (b : ℕ) := Finset (Fin b)

def certified (b p q : ℕ) : Prop :=
  ∃ (L : ℕ) (h : Label b → ℕ) (a : Label b → Fin b → ℤ), 0 < L ∧
    (∀ s, (b : ℤ) * (h s : ℤ) ≤ ∑ i ∈ s, a s i) ∧
    (∀ s t, (∀ i : Fin b, i ∈ s ∨ i ∈ t) → L * p ≤ h s + h t) ∧
    ∀ (s t : Label b) (i : Fin b), i ∈ s → i ∈ t →
      (∀ j, j < i → j ∈ s ∨ j ∈ t) →
      a s i + a t i ≤ (L : ℤ) * (q : ℤ) ∧
      (L : ℤ) * (p : ℤ) + a s i + a t i ≤ (L : ℤ) * (q : ℤ) + h s + h t

theorem main : ∀ (b p q : ℕ), 0 < b → 0 < q →
    (guaranteed b p q ↔ certified b p q) := by
  sorry

end OMA.S_mo_148821
