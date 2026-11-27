import Mathlib

/-!
# Frankl's union-closed sets conjecture

Source: https://www.openproblemgarden.org/op/frankls_union_closed_sets_conjecture

Conjecture (Frankl). Let F be a finite family of finite sets, not all empty, that is
closed under taking unions. Then there exists x such that x is an element of at least
half the members of F.

Conventions:
* The sets are finite subsets of an arbitrary ambient type α (with decidable equality),
  and the finite family is `F : Finset (Finset α)`.
* not all empty: some member of F is nonempty. (This also forces F to be nonempty.)
* closed under taking unions: A ∪ B ∈ F whenever A, B ∈ F (pairwise unions; this is
  equivalent to closure under all finite nonempty unions).
* x is an element of at least half the members of F: 2 · #{A ∈ F | x ∈ A} ≥ #F,
  stated in ℕ without division.
-/

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

namespace OMA.S_opg_frankls_union_closed_sets_conjecture

theorem main :
    ∀ (α : Type) [DecidableEq α] (F : Finset (Finset α)),
      (∃ A ∈ F, A.Nonempty) →
      (∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F) →
      ∃ x : α, F.card ≤ 2 * (F.filter (fun A => x ∈ A)).card := by
  sorry

end OMA.S_opg_frankls_union_closed_sets_conjecture
