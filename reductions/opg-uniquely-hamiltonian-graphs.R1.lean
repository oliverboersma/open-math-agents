import OMAStatements.S_opg_uniquely_hamiltonian_graphs

-- Reduction opg-uniquely-hamiltonian-graphs.R1 of R-regular graphs are not uniquely hamiltonian.
-- Credit: @lzvxck
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- Split by the degree r: odd r (Thomason's parity argument), r >= 300 (Thomassen 1998),
-- r = 4 (Sheehan's conjecture proper) and the remaining even r with 6 <= r < 300.

namespace OMA.R_opg_uniquely_hamiltonian_graphs_R1

open SimpleGraph OMA.S_opg_uniquely_hamiltonian_graphs

/-- Thomason's edge-parity argument: if every vertex of even degree lies on one edge `e` of a
Hamilton cycle `c`, then there is a second Hamilton cycle. This is the same statement as the step
LovaszPlummerConjecture.sheehan_conjecture.R1.H1; it covers every odd `r`. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    ∀ (v : V) (c : G.Walk v v), IsHamiltonCycle G c →
      ∀ (e : Sym2 V), e ∈ c.edges →
        (∀ u, G.degree u % 2 ≠ 1 → u ∈ e) →
        ∃ (w : V) (d : G.Walk w w), IsHamiltonCycle G d ∧
          d.edges.toFinset ≠ c.edges.toFinset

/-- Thomassen (1998): regular graphs of degree at least 300 (the variant
LovaszPlummerConjecture.sheehan_conjecture.variants.thomassen). -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ), 300 ≤ r → G.IsRegularOfDegree r →
      ∀ (v : V) (c : G.Walk v v), IsHamiltonCycle G c →
        ∃ (w : V) (d : G.Walk w w), IsHamiltonCycle G d ∧
          d.edges.toFinset ≠ c.edges.toFinset

/-- Sheehan's conjecture: the 4-regular case (LovaszPlummerConjecture.sheehan_conjecture). -/
def H3 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.IsRegularOfDegree 4 →
      ∀ (v : V) (c : G.Walk v v), IsHamiltonCycle G c →
        ∃ (w : V) (d : G.Walk w w), IsHamiltonCycle G d ∧
          d.edges.toFinset ≠ c.edges.toFinset

/-- The remaining even degrees `6 ≤ r < 300`. -/
def H4 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ), Even r → 6 ≤ r → r < 300 → G.IsRegularOfDegree r →
      ∀ (v : V) (c : G.Walk v v), IsHamiltonCycle G c →
        ∃ (w : V) (d : G.Walk w w), IsHamiltonCycle G d ∧
          d.edges.toFinset ≠ c.edges.toFinset

theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_opg_uniquely_hamiltonian_graphs.main := by
  intro parity large four rest V _ _ G _ r hr hreg v c hc
  by_cases hodd : r % 2 = 1
  · have hlen : 3 ≤ c.edges.length := by
      rw [Walk.length_edges]; exact hc.1.three_le_length
    obtain ⟨e, he⟩ : ∃ e, e ∈ c.edges :=
      List.exists_mem_of_ne_nil _ (by intro h; rw [h] at hlen; simp at hlen)
    refine parity V G v c hc e he (fun u hu => absurd ?_ hu)
    rw [hreg u]; exact hodd
  · by_cases hbig : 300 ≤ r
    · exact large V G r hbig hreg v c hc
    · by_cases h4 : r = 4
      · subst h4; exact four V G hreg v c hc
      · exact rest V G r (Nat.even_iff.mpr (by omega)) (by omega) (by omega) hreg v c hc

end OMA.R_opg_uniquely_hamiltonian_graphs_R1
