import Mathlib

/-!
# Beneš Conjecture

Source: https://www.openproblemgarden.org/op/bene_conjecture
Credit: @AkiRA-COM-FP

Formalizes the partition-stabilizer formulation of Beneš's conjecture as stated on
Open Problem Garden: for a nonempty finite set `E`, a uniform partition `u` of `E`,
and a permutation `φ` of `E` with `u ∧ φ(u) = 0`, if `(φ S(u))^n` is transitive on `E`
for some `n ≥ 2`, then `(φ S(u))^(2n - 1)` equals the full symmetric group `Sym(E)`.
-/

namespace OMA.S_opg_bene_conjecture

/-- The block stabilizer `S(u)` of a partition `u` of `E`: all permutations of `E`
that preserve every block of `u` setwise. -/
def blockStabilizer {E : Type} [Fintype E] [DecidableEq E]
    (u : Finpartition (Finset.univ : Finset E)) : Set (Equiv.Perm E) :=
  {σ | ∀ P ∈ u.parts, ∀ x ∈ P, σ x ∈ P}

/-- A partition `u` of `E` is uniform if all its blocks have the same cardinality. -/
def IsUniform {E : Type} [Fintype E] [DecidableEq E]
    (u : Finpartition (Finset.univ : Finset E)) : Prop :=
  ∃ k : ℕ, ∀ P ∈ u.parts, P.card = k

/-- The infimum `u ∧ φ(u)` is the discrete partition `0`, meaning every block of `u`
meets the `φ`-image of every block of `u` in at most one element. -/
def InfImageTrivial {E : Type} [Fintype E] [DecidableEq E]
    (u : Finpartition (Finset.univ : Finset E)) (φ : Equiv.Perm E) : Prop :=
  ∀ P ∈ u.parts, ∀ Q ∈ u.parts, (P ∩ Q.image φ).card ≤ 1

/-- The `m`-fold product `T^m` of a subset `T` of a group (`m ≥ 1`). -/
def setPow {G : Type*} [Monoid G] (T : Set G) : ℕ → Set G
  | 0 => {1}
  | 1 => T
  | m + 1 => {g | ∃ a ∈ T, ∃ b ∈ setPow T m, g = a * b}

/-- The left coset `φ S(u)`. -/
def coset {E : Type} [Fintype E] [DecidableEq E]
    (u : Finpartition (Finset.univ : Finset E)) (φ : Equiv.Perm E) : Set (Equiv.Perm E) :=
  {g | ∃ σ ∈ blockStabilizer u, g = φ * σ}

/-- A set `T` of permutations of `E` is transitive if for every `x, y : E` there exists
`g ∈ T` with `g x = y`. -/
def IsTransitive {E : Type} (T : Set (Equiv.Perm E)) : Prop :=
  ∀ x y : E, ∃ g ∈ T, g x = y

/-- **Beneš's conjecture** (partition-stabilizer formulation): if `u` is a uniform
partition of a nonempty finite set `E`, `φ` is a permutation with `u ∧ φ(u) = 0`, and
`(φ S(u))^n` is transitive for some `n ≥ 2`, then `(φ S(u))^(2n - 1) = Sym(E)`. -/
theorem main :
    ∀ (E : Type) [Fintype E] [DecidableEq E] [Nonempty E]
      (u : Finpartition (Finset.univ : Finset E)) (φ : Equiv.Perm E) (n : ℕ),
      IsUniform u →
      InfImageTrivial u φ →
      2 ≤ n →
      IsTransitive (setPow (coset u φ) n) →
      setPow (coset u φ) (2 * n - 1) = Set.univ := by
  sorry

end OMA.S_opg_bene_conjecture
