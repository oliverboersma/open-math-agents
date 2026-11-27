import FormalConjectures.ErdosProblems.«1020»
import Mathlib.Data.Fin.Embedding

/-!
The two classical examples give the lower bound. The complete family
bounds the edge count when n is one below r*k, and a matching of size
one is present in every nonempty family.
-/

namespace OMA.R_Erdos1020_erdos_1020_R1

open Finset Erdos1020

def H1 : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∀ n k : ℕ, 0 < k → r * k - 1 ≤ n →
    max ((r * k - 1).choose r) (n.choose r - (n - k + 1).choose r) ≤ f n r k

def H2 : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∀ n k : ℕ, 2 ≤ k → r * k ≤ n →
    f n r k ≤ max ((r * k - 1).choose r) (n.choose r - (n - k + 1).choose r)

section Proof

private theorem full_family_upper (n r k : ℕ) : f n r k ≤ n.choose r := by
  classical
  unfold f Hypergraph.extremalNumber
  apply Finset.sup_le
  intro H hH
  rw [@Finset.mem_filter _ (fun X : Finset (Finset (Fin n)) => ¬ X.HasHypergraphMatching k)
    (fun X => Classical.propDecidable (¬ X.HasHypergraphMatching k))] at hH
  exact (card_le_card (mem_powerset.mp hH.1)).trans_eq (by simp)

private theorem zero_for_one (n r : ℕ) : f n r 1 = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  unfold f Hypergraph.extremalNumber
  apply Finset.sup_le
  intro H hH
  by_contra! hPos
  obtain ⟨e, he⟩ := card_pos.mp hPos
  rw [@Finset.mem_filter _ (fun X : Finset (Finset (Fin n)) => ¬ X.HasHypergraphMatching 1)
    (fun X => Classical.propDecidable (¬ X.HasHypergraphMatching 1))] at hH
  exact hH.2 ⟨{e}, by simpa using he, by simp, by simp [Set.pairwise_singleton]⟩

theorem main : H1 → H2 → type_of% @Erdos1020.erdos_1020 := by
  intro lower upper r hr n k hk hn
  apply le_antisymm ?_ (lower r hr n k hk hn)
  by_cases hOne : k = 1
  · rw [hOne, zero_for_one]
    exact Nat.zero_le _
  by_cases hBig : r * k ≤ n
  · exact upper r hr n k (by omega) hBig
  have hBoundary : n = r * k - 1 := by omega
  exact (full_family_upper n r k).trans
    (by rw [hBoundary]; exact le_max_left _ _)

end Proof

end OMA.R_Erdos1020_erdos_1020_R1
