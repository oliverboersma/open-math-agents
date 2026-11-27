import OMAStatements.S_opg_forcing_a_2_regular_minor

-- Reduction opg-forcing-a-2-regular-minor.R1 of Forcing a 2-regular minor.
-- Credit: @lzvxck
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- Connected H (a single cycle C_t, t >= 3): (4/3) t - 2 >= t - 1, so Erdos-Gallai gives a cycle of
-- length >= t in G, and contracting arcs of that cycle gives C_t. Disconnected H is the open core.

namespace OMA.R_opg_forcing_a_2_regular_minor_R1

open SimpleGraph OMA.S_opg_forcing_a_2_regular_minor

/-- Erdos-Gallai (1959): a nonempty graph on `n` vertices with at least `(k - 1) n / 2` edges
(more than `(k - 1)(n - 1) / 2`), `k >= 3`, has a cycle of length at least `k`. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ),
    3 ≤ k → (k - 1) * Fintype.card V ≤ 2 * G.edgeFinset.card →
      ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ k ≤ c.length

/-- A connected 2-regular graph on `t` vertices (the cycle `C_t`) is a minor of every graph
containing a cycle of length at least `t`: contract consecutive arcs of that cycle. -/
def H2 : Prop :=
  ∀ (t : ℕ) (H : SimpleGraph (Fin t)) [DecidableRel H.Adj],
    H.IsRegularOfDegree 2 → H.Connected →
      ∀ (V : Type) (G : SimpleGraph V) (u : V) (c : G.Walk u u),
        c.IsCycle → t ≤ c.length → IsMinor H G

/-- The open core: 2-regular graphs with at least two components (disjoint unions of cycles). -/
def H3 : Prop :=
  ∀ (t : ℕ) (H : SimpleGraph (Fin t)) [DecidableRel H.Adj],
    H.IsRegularOfDegree 2 → ¬ H.Connected →
      ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj],
        (4 / 3 : ℝ) * t - 2 ≤ 2 * (G.edgeFinset.card : ℝ) / Fintype.card V →
          IsMinor H G

theorem main : H1 → H2 → H3 → type_of% @OMA.S_opg_forcing_a_2_regular_minor.main := by
  intro eg cyc rest t H _ hreg V _ _ G _ havg
  by_cases hc : H.Connected
  · have h3 : 3 ≤ t := by
      obtain ⟨i⟩ := hc.nonempty
      have hnot : i ∉ H.neighborFinset i := by simp
      have hcard : (insert i (H.neighborFinset i)).card = 3 := by
        rw [Finset.card_insert_of_notMem hnot, card_neighborFinset_eq_degree, hreg i]
      have := Finset.card_le_univ (insert i (H.neighborFinset i))
      rw [hcard, Fintype.card_fin] at this
      exact this
    have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
    have ht : (3 : ℝ) ≤ t := by exact_mod_cast h3
    have hle : ((t : ℝ) - 1) * Fintype.card V ≤ 2 * (G.edgeFinset.card : ℝ) := by
      rw [← le_div_iff₀ hn]; linarith
    have hnat : (t - 1) * Fintype.card V ≤ 2 * G.edgeFinset.card := by
      have hcast : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]
      have : (((t - 1) * Fintype.card V : ℕ) : ℝ) ≤ ((2 * G.edgeFinset.card : ℕ) : ℝ) := by
        push_cast [Nat.cast_mul]; rw [hcast]; exact hle
      exact_mod_cast this
    obtain ⟨u, c, hcyc, hlen⟩ := eg V G t h3 hnat
    exact cyc t H hreg hc V G u c hcyc hlen
  · exact rest t H hreg hc V G havg

end OMA.R_opg_forcing_a_2_regular_minor_R1
