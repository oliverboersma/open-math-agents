import Mathlib

/-!
# Is there a Ramsey theory for Kneser graphs?

Source: https://mathoverflow.net/questions/228227
Credit: @zarnab222-dev

The question: if in a two-colouring of the edges of the Kneser graph `KG(n,k)` every sub-Kneser graph
`KG(3k,k)` (induced by `3k` of the `n` ground elements) has a red edge and every triangle has a blue edge,
how large can `n` be?  The accepted answer: for `k ≥ 3` there is no upper bound on `n`.  That claim is stated.

Translation choices.  The ground set is `Fin n`; the vertices of `KG(n,k)` are the `A : Finset (Fin n)` with
`A.card = k`; two vertices are adjacent iff they are disjoint.  A two-colouring of the edges is a symmetric
relation `red` (an edge is blue iff it is not red; the value of `red` on non-edges is never used).
A triangle is three pairwise disjoint `k`-sets; it has a blue edge iff not all three of its edges are red.
`No upper bound on n` is rendered literally: for every `N` there is `n ≥ N` admitting such a colouring.
For `n < 3k` the first condition is vacuous, exactly as in the source.
-/

namespace OMA.S_mo_228227

theorem main : ∀ k : ℕ, 3 ≤ k → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
    ∃ red : Finset (Fin n) → Finset (Fin n) → Prop,
      (∀ A B : Finset (Fin n), red A B ↔ red B A) ∧
      (∀ S : Finset (Fin n), S.card = 3 * k →
        ∃ A B : Finset (Fin n), A ⊆ S ∧ B ⊆ S ∧ A.card = k ∧ B.card = k ∧ Disjoint A B ∧ red A B) ∧
      (∀ A B C : Finset (Fin n), A.card = k → B.card = k → C.card = k →
        Disjoint A B → Disjoint B C → Disjoint A C → ¬ (red A B ∧ red B C ∧ red A C)) := by
  sorry

end OMA.S_mo_228227
