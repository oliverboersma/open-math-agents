import Mathlib

/-!
# Frankl conjecture (union-closed sets conjecture)

Source: https://en.wikipedia.org/wiki/Frankl_conjecture
(redirects to https://en.wikipedia.org/wiki/Union-closed_sets_conjecture)
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Source statement (Frankl, 1979): a family of sets is union-closed if the union of any two sets
from the family belongs to the family. For every finite union-closed family of sets, other than
the empty family, there exists an element that belongs to at least half of the sets in the
family.

Conventions:
* the sets live in an arbitrary type `α` and are arbitrary (not necessarily finite) subsets
  `Set α`; the family `F` is a finite family, a `Finset (Set α)`;
* union-closed: `A ∈ F → B ∈ F → A ∪ B ∈ F`;
* nondegeneracy: the source excludes only the empty family, but read literally the family
  `{∅}` (union-closed, non-empty) has no element at all, so it would be a trivial
  counterexample. The standard reading (e.g. Bruhn–Schaudt's survey, cited by the source)
  requires the family to contain a non-empty set; we assume `∃ A ∈ F, A.Nonempty`, which also
  excludes the empty family;
* at least half: `#F ≤ 2 * #{A ∈ F | a ∈ A}`, in `ℕ`, which is exactly `#{A ∈ F | a ∈ A} ≥ #F / 2`
  over the rationals.
-/

namespace OMA.S_wp_frankl_conjecture

open Classical in
theorem main : ∀ (α : Type) (F : Finset (Set α)),
    (∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F) →
    (∃ A ∈ F, A.Nonempty) →
    ∃ a : α, F.card ≤ 2 * (F.filter (fun A => a ∈ A)).card := by
  sorry

end OMA.S_wp_frankl_conjecture
