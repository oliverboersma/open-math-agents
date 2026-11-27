import Mathlib

/-!
# Erdős Problem 550

Source: https://www.erdosproblems.com/550
Credit: @sntntHb

Let `m_1 ≤ ⋯ ≤ m_k` and `n` be sufficiently large. If `T` is a tree on `n` vertices and `G` is
the complete multipartite graph with vertex class sizes `m_1, …, m_k`, then
`R(T, G) ≤ (χ(G) - 1)(R(T, K_{m_1,m_2}) - 1) + m_1`.
(Problem #16 in the Ramsey Theory in graphs problem collection.)

Conventions:
- `R(H₁, H₂)` (`graphRamsey`) is the least `N` such that for every simple graph `C` on `N`
  vertices, `H₁` is contained in `C` (as a not necessarily induced subgraph) or `H₂` is
  contained in the complement of `C`.
- `completeMultipartite m` is the complete multipartite graph whose vertex classes are
  `Fin (m i)`: two vertices are adjacent iff they lie in different classes.
- The source needs `m_2`, so there are at least two classes; we index the classes by
  `Fin (k + 2)`, so the source's `k` is `k + 2` here, `m_1 = m 0` and `m_2 = m 1`.
- "Sufficiently large" applies, as in the source, to both the class sizes and `n`: for each
  number of classes there is a threshold `M` such that the inequality holds whenever
  `M ≤ m_1 ≤ ⋯ ≤ m_k` and `M ≤ n`. The source does not say whether the threshold may depend on
  the number of classes; we take the standard reading that it may.
- `χ(G)` is `SimpleGraph.chromaticNumber`, valued in `ℕ∞`, so the inequality is stated in `ℕ∞`.
-/

namespace OMA.S_erdos_550

open SimpleGraph

/-- The two-colour graph Ramsey number `R(H₁, H₂)`. -/
noncomputable def graphRamsey {α β : Type*} (H₁ : SimpleGraph α) (H₂ : SimpleGraph β) : ℕ :=
  sInf {N : ℕ | ∀ C : SimpleGraph (Fin N), H₁.IsContained C ∨ H₂.IsContained Cᶜ}

/-- The complete multipartite graph with vertex classes of sizes `m i`. -/
def completeMultipartite {ι : Type*} (m : ι → ℕ) : SimpleGraph (Σ i : ι, Fin (m i)) where
  Adj x y := x.1 ≠ y.1
  symm := ⟨fun _ _ h => Ne.symm h⟩
  loopless := ⟨fun _ h => h rfl⟩

theorem main :
    ∀ k : ℕ, ∃ M : ℕ, ∀ m : Fin (k + 2) → ℕ, Monotone m → M ≤ m 0 →
      ∀ n : ℕ, M ≤ n → ∀ T : SimpleGraph (Fin n), T.IsTree →
        (graphRamsey T (completeMultipartite m) : ℕ∞) ≤
          ((completeMultipartite m).chromaticNumber - 1) *
            ((graphRamsey T (completeBipartiteGraph (Fin (m 0)) (Fin (m 1))) - 1 : ℕ) : ℕ∞) +
            (m 0 : ℕ∞) := by
  sorry

end OMA.S_erdos_550
