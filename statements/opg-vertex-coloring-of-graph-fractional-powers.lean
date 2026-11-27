import Mathlib

/-!
# Vertex Coloring of Graph Fractional Powers

Source: https://www.openproblemgarden.org/op/vertex_coloring_of_graph_fractional_powers
Credit: @AkiRA-COM-FP

Formalizes Iradmusa's conjecture on vertex colorings of fractional powers of graphs:
for a finite connected graph `G` with maximum degree `Δ(G) ≥ 3` and integers `1 < m < n`,
the fractional power `G^(m/n) = (G^(1/n))^m` satisfies `χ(G^(m/n)) = ω(G^(m/n))`.
-/

namespace OMA.S_opg_vertex_coloring_of_graph_fractional_powers

/-- Pre-vertices for the `n`-subdivision `G^(1/n)`: either an original branch vertex of `G`
or an oriented internal vertex `k ∈ Fin (n - 1)` along an edge `(u, v)` of `G`. -/
def SubdivPre {V : Type} (G : SimpleGraph V) (n : ℕ) : Type :=
  V ⊕ {t : V × V × Fin (n - 1) // G.Adj t.1 t.2.1}

/-- Equivalence relation identifying the two orientations of each subdivided edge path:
position `k` from `u` toward `v` equals position `k.rev` from `v` toward `u`. -/
def subdivRel {V : Type} (G : SimpleGraph V) (n : ℕ) :
    SubdivPre G n → SubdivPre G n → Prop
  | Sum.inl u, Sum.inl v => u = v
  | Sum.inr ⟨⟨u, v, k⟩, _⟩, Sum.inr ⟨⟨u', v', k'⟩, _⟩ =>
      (u = u' ∧ v = v' ∧ k = k') ∨ (u = v' ∧ v = u' ∧ k = k'.rev)
  | _, _ => False

/-- Setoid for the vertices of the `n`-subdivision `G^(1/n)`. -/
def subdivSetoid {V : Type} (G : SimpleGraph V) (n : ℕ) : Setoid (SubdivPre G n) where
  r := subdivRel G n
  iseqv :=
    { refl := fun x => by
        cases x with
        | inl u => rfl
        | inr t => exact Or.inl ⟨rfl, rfl, rfl⟩
      symm := fun {x y} h => by
        cases x with
        | inl u =>
          cases y with
          | inl v => exact h.symm
          | inr _ => exact False.elim h
        | inr t =>
          cases y with
          | inl _ => exact False.elim h
          | inr s =>
            rcases t with ⟨⟨u, v, k⟩, ht⟩
            rcases s with ⟨⟨u', v', k'⟩, hs⟩
            rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
            · exact Or.inl ⟨rfl, rfl, rfl⟩
            · exact Or.inr ⟨rfl, rfl, (Fin.rev_rev k').symm⟩
      trans := fun {x y z} hxy hyz => by
        cases x with
        | inl u =>
          cases y with
          | inl v =>
            cases z with
            | inl w => exact hxy.trans hyz
            | inr _ => exact False.elim hyz
          | inr _ => exact False.elim hxy
        | inr t =>
          cases y with
          | inl _ => exact False.elim hxy
          | inr s =>
            cases z with
            | inl _ => exact False.elim hyz
            | inr r =>
              rcases t with ⟨⟨u, v, k⟩, ht⟩
              rcases s with ⟨⟨u', v', k'⟩, hs⟩
              rcases r with ⟨⟨u'', v'', k''⟩, hr⟩
              rcases hxy with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
              · exact hyz
              · rcases hyz with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
                · exact Or.inr ⟨rfl, rfl, rfl⟩
                · exact Or.inl ⟨rfl, rfl, Fin.rev_rev k''⟩ }

/-- Vertex type of the `n`-subdivision `G^(1/n)`. -/
def SubdivVert {V : Type} (G : SimpleGraph V) (n : ℕ) : Type :=
  Quotient (subdivSetoid G n)

/-- Raw adjacency relation on `SubdivVert G n` before symmetrizing and removing loops:
for `n = 1`, original edges of `G`; for `n ≥ 2`, each edge `u-v` becomes a path of length `n`
joining `inl u` to `k = 0`, `k` to `k + 1`, and `k = n - 2` to `inl v` (via reversal). -/
def subdivStep {V : Type} (G : SimpleGraph V) (n : ℕ) (x y : SubdivVert G n) : Prop :=
  (n = 1 ∧ ∃ u v, G.Adj u v ∧ x = Quotient.mk _ (Sum.inl u) ∧ y = Quotient.mk _ (Sum.inl v)) ∨
  (∃ (u v : V) (h : G.Adj u v) (h0 : 0 < n - 1),
    x = Quotient.mk _ (Sum.inl u) ∧
    y = Quotient.mk _ (Sum.inr ⟨⟨u, v, ⟨0, h0⟩⟩, h⟩)) ∨
  (∃ (u v : V) (h : G.Adj u v) (k : ℕ) (hk : k + 1 < n - 1),
    x = Quotient.mk _ (Sum.inr ⟨⟨u, v, ⟨k, Nat.lt_of_succ_lt hk⟩⟩, h⟩) ∧
    y = Quotient.mk _ (Sum.inr ⟨⟨u, v, ⟨k + 1, hk⟩⟩, h⟩))

/-- The `n`-subdivision `G^(1/n)` of a simple graph `G`. -/
def subdivision {V : Type} (G : SimpleGraph V) (n : ℕ) : SimpleGraph (SubdivVert G n) :=
  SimpleGraph.fromRel (subdivStep G n)

/-- The `m`-th power `H^m` of a simple graph `H`: distinct vertices at distance at most `m`. -/
def graphPower {W : Type} (H : SimpleGraph W) (m : ℕ) : SimpleGraph W where
  Adj x y := x ≠ y ∧ H.edist x y ≤ m
  symm := ⟨fun _ _ h => ⟨h.1.symm, by rw [SimpleGraph.edist_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The fractional power `G^(m/n) = (G^(1/n))^m`. -/
def fractionalPower {V : Type} (G : SimpleGraph V) (m n : ℕ) : SimpleGraph (SubdivVert G n) :=
  graphPower (subdivision G n) m

/-- **Iradmusa's conjecture on vertex coloring of graph fractional powers**:
for every finite connected simple graph `G` with `Δ(G) ≥ 3` and every integers `1 < m < n`,
`χ(G^(m/n)) = ω(G^(m/n))`. -/
theorem main :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.Connected →
      3 ≤ G.maxDegree →
      ∀ m n : ℕ, 1 < m → m < n →
        (fractionalPower G m n).chromaticNumber = ((fractionalPower G m n).cliqueNum : ℕ∞) := by
  sorry

end OMA.S_opg_vertex_coloring_of_graph_fractional_powers
