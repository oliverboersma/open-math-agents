import OMAReductions.R_Erdos128_erdos_128_R2

/-!
# Reduction Erdos128.erdos_128.R2.H2.R3 of step Erdos128.erdos_128.R2.H2

Splits `Erdos128.erdos_128.R2.H2` cleanly into the two halves of the Brandt-Thomasse
structural proof for Erdos Problem 128 on the entire `3 * delta(G) > n` band:
- `H1`: Any finite triangle-free graph `M` (`n > 0`) with `5 * alpha(M) < 2 * n`,
  `3 * delta(M) > n`, admitting a surjective edge-reflecting map onto an active Vega graph
  `V_i(dy, de)` (`i >= 2`), satisfies the sparse-half bound `50 * e(M[V']) <= n^2` for some
  `V'` with `2 * |V'| + 1 >= n` (hence cannot satisfy the strict-inequality negation).
- `H2`: Every maximal triangle-free non-3-colorable graph `M` with `3 * delta(M) > n`
  admits a surjective edge-reflecting map onto an active Vega graph `V_i(dy, de)` (`i >= 2`).

`main` extends `G` to a maximal triangle-free supergraph `M >= G` via
`OMA.R_Erdos128_erdos_128_R2.exists_maximal_triangleFree`, verifies that `M` inherits
`5 * alpha(M) < 2 * n`, `not M.Colorable 3`, `3 * delta(M) > n`, and the sparse-half negation,
and composes `H2` with `H1`.
-/

-- Reduction Erdos128.erdos_128.R2.H2.R3 of step Erdos128.erdos_128.R2.H2
-- Credit: @iskamag

namespace OMA.R_Erdos128_erdos_128_R2_H2_R3

def H1 : Prop :=
  ∀ (V : Type) [Fintype V] (M : SimpleGraph V),
    0 < Fintype.card V → M.CliqueFree 3 →
    (∀ I : Set V, M.IsIndepSet I → 5 * I.ncard < 2 * Fintype.card V) →
    (∀ v : V, Fintype.card V < 3 * (M.neighborSet v).ncard) →
    (∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (M.induce V').edgeSet.ncard > Fintype.card V ^ 2) →
    (∃ (i : ℕ) (dy de : Bool) (ψ : V → Fin (3 * i - 1) ⊕ Fin 8),
      2 ≤ i ∧
      let act : Fin (3 * i - 1) ⊕ Fin 8 → Prop := fun v => match v with
        | .inl k => ¬ (de = true ∧ k.val = 2 * i - 1)
        | .inr j => ¬ (dy = true ∧ j.val = 1)
      let adj : Fin (3 * i - 1) ⊕ Fin 8 → Fin (3 * i - 1) ⊕ Fin 8 → Prop := fun a b => match a, b with
        | .inl p, .inl q => let N := 3 * i - 1; let d := (q.val + N - p.val) % N; i ≤ d ∧ d ≤ 2 * i - 1
        | .inl p, .inr q | .inr q, .inl p =>
            (p.val < i ∧ (q.val = 2 ∨ q.val = 5)) ∨
            (i ≤ p.val ∧ p.val < 2 * i ∧ (q.val = 3 ∨ q.val = 6)) ∨
            (2 * i ≤ p.val ∧ (q.val = 4 ∨ q.val = 7))
        | .inr p, .inr q =>
            (p.val = 0 ∧ (q.val = 1 ∨ q.val = 2 ∨ q.val = 3 ∨ q.val = 4)) ∨
            (q.val = 0 ∧ (p.val = 1 ∨ p.val = 2 ∨ p.val = 3 ∨ p.val = 4)) ∨
            (p.val = 1 ∧ (q.val = 5 ∨ q.val = 6 ∨ q.val = 7)) ∨
            (q.val = 1 ∧ (p.val = 5 ∨ p.val = 6 ∨ p.val = 7)) ∨
            (p.val = 2 ∧ (q.val = 6 ∨ q.val = 7)) ∨ (q.val = 2 ∧ (p.val = 6 ∨ p.val = 7)) ∨
            (p.val = 3 ∧ (q.val = 5 ∨ q.val = 7)) ∨ (q.val = 3 ∧ (p.val = 5 ∨ p.val = 7)) ∨
            (p.val = 4 ∧ (q.val = 5 ∨ q.val = 6)) ∨ (q.val = 4 ∧ (p.val = 5 ∨ p.val = 6))
      (∀ v, act (ψ v)) ∧ (∀ w, act w → ∃ v, ψ v = w) ∧ ∀ u v, M.Adj u v ↔ adj (ψ u) (ψ v)) → False

def H2 : Prop :=
  ∀ (V : Type) [Fintype V] (M : SimpleGraph V),
    M.CliqueFree 3 →
    (∀ u v : V, u ≠ v → ¬ M.Adj u v → ∃ w : V, M.Adj u w ∧ M.Adj v w) →
    (∀ v : V, Fintype.card V < 3 * (M.neighborSet v).ncard) →
    ¬ M.Colorable 3 →
    (∃ (i : ℕ) (dy de : Bool) (ψ : V → Fin (3 * i - 1) ⊕ Fin 8),
      2 ≤ i ∧
      let act : Fin (3 * i - 1) ⊕ Fin 8 → Prop := fun v => match v with
        | .inl k => ¬ (de = true ∧ k.val = 2 * i - 1)
        | .inr j => ¬ (dy = true ∧ j.val = 1)
      let adj : Fin (3 * i - 1) ⊕ Fin 8 → Fin (3 * i - 1) ⊕ Fin 8 → Prop := fun a b => match a, b with
        | .inl p, .inl q => let N := 3 * i - 1; let d := (q.val + N - p.val) % N; i ≤ d ∧ d ≤ 2 * i - 1
        | .inl p, .inr q | .inr q, .inl p =>
            (p.val < i ∧ (q.val = 2 ∨ q.val = 5)) ∨
            (i ≤ p.val ∧ p.val < 2 * i ∧ (q.val = 3 ∨ q.val = 6)) ∨
            (2 * i ≤ p.val ∧ (q.val = 4 ∨ q.val = 7))
        | .inr p, .inr q =>
            (p.val = 0 ∧ (q.val = 1 ∨ q.val = 2 ∨ q.val = 3 ∨ q.val = 4)) ∨
            (q.val = 0 ∧ (p.val = 1 ∨ p.val = 2 ∨ p.val = 3 ∨ p.val = 4)) ∨
            (p.val = 1 ∧ (q.val = 5 ∨ q.val = 6 ∨ q.val = 7)) ∨
            (q.val = 1 ∧ (p.val = 5 ∨ p.val = 6 ∨ p.val = 7)) ∨
            (p.val = 2 ∧ (q.val = 6 ∨ q.val = 7)) ∨ (q.val = 2 ∧ (p.val = 6 ∨ p.val = 7)) ∨
            (p.val = 3 ∧ (q.val = 5 ∨ q.val = 7)) ∨ (q.val = 3 ∧ (p.val = 5 ∨ p.val = 7)) ∨
            (p.val = 4 ∧ (q.val = 5 ∨ q.val = 6)) ∨ (q.val = 4 ∧ (p.val = 5 ∨ p.val = 6))
      (∀ v, act (ψ v)) ∧ (∀ w, act w → ∃ v, ψ v = w) ∧ ∀ u v, M.Adj u v ↔ adj (ψ u) (ψ v))

theorem main : H1 → H2 → OMA.R_Erdos128_erdos_128_R2.H2 := by
  intro h1 h2 V _ G h12 _ _ hα _ _ _ hNot3 hδ _ h50 hTF
  obtain ⟨M, hGM, hMTF, hMmax⟩ := OMA.R_Erdos128_erdos_128_R2.exists_maximal_triangleFree G hTF
  have hMα : ∀ I : Set V, M.IsIndepSet I → 5 * I.ncard < 2 * Fintype.card V :=
    fun I hI => hα I (fun u hu v hv huv hadj => hI hu hv huv (hGM hadj))
  have hMNot3 : ¬ M.Colorable 3 := by
    rintro ⟨c⟩
    exact hNot3 ⟨SimpleGraph.Coloring.mk c (fun {u v} hadj => c.valid (hGM hadj))⟩
  have hMδ : ∀ v : V, Fintype.card V < 3 * (M.neighborSet v).ncard := by
    intro v
    have hsub : G.neighborSet v ⊆ M.neighborSet v := fun w hw => hGM hw
    have hle : (G.neighborSet v).ncard ≤ (M.neighborSet v).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    have hv := hδ v
    omega
  have hM50 : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (M.induce V').edgeSet.ncard > Fintype.card V ^ 2 := by
    intro V' hV'
    have hsub : (G.induce V').edgeSet ⊆ (M.induce V').edgeSet := by
      intro e he
      induction e using Sym2.ind with
      | _ u v => exact hGM he
    have hle : (G.induce V').edgeSet.ncard ≤ (M.induce V').edgeSet.ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    have hG50 := h50 V' hV'
    omega
  exact h1 V M (by omega) hMTF hMα hMδ hM50 (h2 V M hMTF hMmax hMδ hMNot3)

end OMA.R_Erdos128_erdos_128_R2_H2_R3
