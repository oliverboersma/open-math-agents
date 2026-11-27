import Mathlib

/-!
# AEC: Shelah's eventual categoricity conjecture for abstract elementary classes

Source: https://en.wikipedia.org/wiki/Abstract_elementary_class
Credit: @biondadave

For every cardinal `λ` there exists a cardinal `μ(λ)` such that if an AEC `K` with
`LS(K) ≤ λ` is categorical in a cardinal above `μ(λ)` then it is categorical in all cardinals
above `μ(λ)`.

Formalization notes:
* An abstract elementary class `(K, ≼_K)` in a language `L` is encoded by a predicate `mem` on
  `L`-structures (membership in `K`) and a predicate `strong` on `L`-embeddings between members
  of `K` (the strong embeddings: `f : M ↪ N` is strong iff its image `f[M] ≼_K N`). This is the
  usual embedding form of the definition (as in the source): `K` and `≼_K` are closed under
  isomorphism, `≼_K` refines the substructure relation and is a partial order, coherence holds,
  and the Tarski–Vaught chain axioms hold.
* The chain axioms are stated for a chain `(Sᵢ)_{i ∈ I}` of substructures of an ambient
  structure, indexed by a nonempty linear order `I`, with union `⨆ i, Sᵢ`. Chains indexed by
  arbitrary linear orders are equivalent to the usual ordinal-indexed chains (pass to a cofinal
  well-ordered subchain), and every abstract chain of strong embeddings is realized as such a
  chain inside its direct limit.
* `LS(K) ≤ λ` is encoded as: `|L| + ℵ₀ ≤ λ` and the downward Löwenheim–Skolem axiom with the
  number `λ` (every subset `A` of a member `N` is contained in some `M ≼_K N` with
  `|M| ≤ |A| + λ`). The axiom is monotone in the number, so this is equivalent to the existence
  of the Löwenheim–Skolem number with `LS(K) ≤ λ`.
* `K` is categorical in `κ` if it has, up to isomorphism, exactly one model of cardinality `κ`
  (in particular at least one).
* Structures and cardinals live in a fixed universe `w`; the language too.
-/

namespace OMA.S_wp_aec

universe w

open FirstOrder Language Cardinal

/-- An abstract elementary class in the language `L`, presented by its members and its
strong embeddings. -/
structure AEC (L : FirstOrder.Language.{w, w}) where
  /-- Membership of an `L`-structure in `K`. -/
  mem : ∀ (M : Type w) [L.Structure M], Prop
  /-- The strong embeddings: `f : M ↪[L] N` is strong iff `f[M] ≼_K N`. -/
  strong : ∀ {M N : Type w} [L.Structure M] [L.Structure N], (M ↪[L] N) → Prop
  /-- `≼_K` is a relation on `K`. -/
  mem_of_strong : ∀ {M N : Type w} [L.Structure M] [L.Structure N] (f : M ↪[L] N),
    strong f → mem M ∧ mem N
  /-- `K` is closed under isomorphism. -/
  mem_of_equiv : ∀ {M N : Type w} [L.Structure M] [L.Structure N], mem M → (M ≃[L] N) → mem N
  /-- Isomorphisms between members are strong (with `strong_comp`: `≼_K` is reflexive and
  closed under isomorphism). -/
  strong_equiv : ∀ {M N : Type w} [L.Structure M] [L.Structure N] (e : M ≃[L] N),
    mem M → strong e.toEmbedding
  /-- Transitivity of `≼_K`. -/
  strong_comp : ∀ {M N P : Type w} [L.Structure M] [L.Structure N] [L.Structure P]
    (f : M ↪[L] N) (g : N ↪[L] P), strong f → strong g → strong (g.comp f)
  /-- Coherence: if `M₀ ⊆ M₁ ≼_K M₂` and `M₀ ≼_K M₂` (with `M₀, M₁ ∈ K`), then `M₀ ≼_K M₁`. -/
  coherence : ∀ {M N P : Type w} [L.Structure M] [L.Structure N] [L.Structure P]
    (f : M ↪[L] N) (g : N ↪[L] P), mem M → mem N → strong g → strong (g.comp f) → strong f
  /-- Tarski–Vaught chain axioms: the union of a `≼_K`-chain is in `K`, every member of the
  chain is `≼_K` the union, and if every member is `≼_K` some `T ∈ K` then so is the union. -/
  chain : ∀ (U : Type w) [L.Structure U] (I : Type w) [LinearOrder I] [Nonempty I]
    (S : I → L.Substructure U) (hS : Monotone S),
    (∀ i, mem (S i)) → (∀ i j (h : i ≤ j), strong (Substructure.inclusion (hS h))) →
      mem ↥(⨆ i, S i) ∧
      (∀ i, strong (Substructure.inclusion (le_iSup S i))) ∧
      (∀ T : L.Substructure U, mem T → (∀ i, ∃ h : S i ≤ T, strong (Substructure.inclusion h)) →
        ∃ h : (⨆ i, S i) ≤ T, strong (Substructure.inclusion h))

variable {L : FirstOrder.Language.{w, w}}

/-- `LS(K) ≤ λ`: `|L| + ℵ₀ ≤ λ` and the downward Löwenheim–Skolem axiom holds with `λ`. -/
def AEC.LSLe (K : AEC L) (lam : Cardinal.{w}) : Prop :=
  L.card + ℵ₀ ≤ lam ∧
  ∀ (N : Type w) [L.Structure N], K.mem N → ∀ A : Set N,
    ∃ S : L.Substructure N, A ⊆ S ∧ K.strong S.subtype ∧ #S ≤ #A + lam

/-- `K` is categorical in `κ`: it has a model of cardinality `κ`, and any two of its models of
cardinality `κ` are isomorphic. -/
def AEC.Categorical (K : AEC L) (κ : Cardinal.{w}) : Prop :=
  (∃ (M : Type w) (_ : L.Structure M), K.mem M ∧ #M = κ) ∧
  ∀ (M N : Type w) [L.Structure M] [L.Structure N], K.mem M → K.mem N → #M = κ → #N = κ →
    Nonempty (M ≃[L] N)

/-- Shelah's eventual categoricity conjecture for abstract elementary classes. -/
theorem main :
    ∀ lam : Cardinal.{w}, ∃ μ : Cardinal.{w},
      ∀ (L : FirstOrder.Language.{w, w}) (K : AEC L), K.LSLe lam →
      (∃ κ, μ < κ ∧ K.Categorical κ) → ∀ κ, μ < κ → K.Categorical κ := by
  sorry

end OMA.S_wp_aec
