import Mathlib

/-!
# Algebraically closed

Source: https://en.wikipedia.org/wiki/algebraically_closed_field
Credit: @LAPRAI

The question: is every infinite, minimal field of characteristic zero algebraically closed?
Here *minimal* means that every definable subset of the structure is finite or co-finite.

## Encoding

* The structure is the field `K` in the first-order language of rings
  `FirstOrder.Language.ring` (symbols `+`, `*`, `-`, `0`, `1`). As Mathlib recommends, the
  language structure is supplied by `FirstOrder.Ring.CompatibleRing K`, which forces its
  interpretation to agree with the `Field K` operations.
* *Definable* is the standard model-theoretic notion: definable by a first-order formula of that
  language with parameters from `K` (`Set.Definable₁` over the parameter set `Set.univ`).
* *Definable subset of the structure* means a subset of the universe `K` itself, as in the
  standard definition of a minimal structure.
* The question is stated in its expected positive form; a disproof would answer it negatively.
-/

namespace OMA.S_wp_algebraically_closed

/-- A field `K`, viewed as a structure in the language of rings, is *minimal* if every subset of
`K` definable with parameters is finite or co-finite. -/
def IsMinimalField (K : Type) [Field K] [FirstOrder.Ring.CompatibleRing K] : Prop :=
  ∀ s : Set K, (Set.univ : Set K).Definable₁ FirstOrder.Language.ring s → s.Finite ∨ sᶜ.Finite

/-- Every infinite minimal field of characteristic zero is algebraically closed. -/
theorem main : ∀ (K : Type) [Field K] [FirstOrder.Ring.CompatibleRing K] [CharZero K] [Infinite K],
    IsMinimalField K → IsAlgClosed K := by
  sorry

end OMA.S_wp_algebraically_closed
