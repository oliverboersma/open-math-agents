import FormalConjectures.Arxiv.«2605.02731».DeanCycles
import Mathlib

/-! Reduction of Dean's conjecture for k >= 6 (Luo-Ma-Zhao 2026) to connected graphs,
splitting into the even case k >= 6 (H1) and the odd case k >= 7 (H2). In `main`, we prove
nonemptiness of V from `6 <= G.minDegree`, pass to the induced connected component of a vertex
while preserving `minDegree >= k`, and lift cycles of the induced component back to G with
identical length. -/

namespace OMA.R_Arxiv_2605_02731_dean_conjecture_variants_six_le_R1

open SimpleGraph

private lemma nonempty_of_pos_minDegree {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hpos : 0 < G.minDegree) : Nonempty V := by
  by_contra h
  rw [not_nonempty_iff] at h
  have : G.minDegree = 0 := by
    simp [SimpleGraph.minDegree]
  omega

private lemma minDegree_le_induce_component {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v₀ : V)
    [DecidablePred (fun v : V => G.Reachable v₀ v)] :
    G.minDegree ≤ (G.induce {v | G.Reachable v₀ v}).minDegree := by
  let S : Set V := {v | G.Reachable v₀ v}
  have : Nonempty S := ⟨⟨v₀, SimpleGraph.Reachable.refl v₀⟩⟩
  obtain ⟨u, hu⟩ := (G.induce S).exists_minimal_degree_vertex
  rw [hu]
  have hle : G.minDegree ≤ G.degree u.1 := G.minDegree_le_degree u.1
  refine le_trans hle ?_
  rw [← G.card_neighborFinset_eq_degree, ← (G.induce S).card_neighborFinset_eq_degree]
  refine Finset.card_le_card_of_injOn (fun w => if hw : w ∈ S then ⟨w, hw⟩ else u) ?_ ?_
  · intro w hw
    have hadj : G.Adj u.1 w := (G.mem_neighborFinset u.1 w).1 hw
    have hwS : w ∈ S := u.2.trans hadj.reachable
    simp only [dif_pos hwS, Finset.mem_coe, SimpleGraph.mem_neighborFinset]
    exact hadj
  · intro w1 hw1 w2 hw2 h
    have hw1S : w1 ∈ S := u.2.trans ((G.mem_neighborFinset u.1 w1).1 hw1).reachable
    have hw2S : w2 ∈ S := u.2.trans ((G.mem_neighborFinset u.1 w2).1 hw2).reachable
    simp only [dif_pos hw1S, dif_pos hw2S] at h
    exact congrArg Subtype.val h

private lemma reachable_induce_of_walk {V : Type} (G : SimpleGraph V) (v₀ : V)
    {x y : V} (w : G.Walk x y) (hx : G.Reachable v₀ x) :
    (G.induce {v | G.Reachable v₀ v}).Reachable ⟨x, hx⟩ ⟨y, hx.trans ⟨w⟩⟩ := by
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hab p ih =>
    have hb : G.Reachable v₀ b := hx.trans hab.reachable
    have hadj : (G.induce {v | G.Reachable v₀ v}).Adj ⟨a, hx⟩ ⟨b, hb⟩ := hab
    exact hadj.reachable.trans (ih hb)

private lemma cycleLengths_induce_subset {V : Type} (G : SimpleGraph V) (S : Set V) :
    (G.induce S).cycleLengths ⊆ G.cycleLengths := by
  intro m hm
  rcases hm with ⟨v, p, hp, rfl⟩
  let f : G.induce S ↪g G := SimpleGraph.Embedding.induce S
  refine ⟨f v, p.map f.toHom, ?_, by simp⟩
  exact hp.map f.injective

/-- Even case of Luo-Ma-Zhao (2026): every connected finite simple graph with minimum degree
at least k (for even k >= 6) contains a cycle of length divisible by k. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ},
    6 ≤ k → Even k → ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      G.Connected → k ≤ G.minDegree → ∃ m ∈ G.cycleLengths, k ∣ m

/-- Odd case of Luo-Ma-Zhao (2026): every connected finite simple graph with minimum degree
at least k (for odd k >= 7) contains a cycle of length divisible by k. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ},
    7 ≤ k → Odd k → ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      G.Connected → k ≤ G.minDegree → ∃ m ∈ G.cycleLengths, k ∣ m

theorem main : H1 → H2 →
    type_of% @Arxiv.«2605.02731».dean_conjecture.variants.six_le := by
  classical
  intro h1 h2 V _ _ k hk G _ hG
  have hne : Nonempty V := nonempty_of_pos_minDegree G (by omega)
  obtain ⟨v₀⟩ := hne
  let S : Set V := {v | G.Reachable v₀ v}
  have : Nonempty S := ⟨⟨v₀, SimpleGraph.Reachable.refl v₀⟩⟩
  have hconn : (G.induce S).Connected := by
    refine SimpleGraph.Connected.mk fun a b => ?_
    obtain ⟨w⟩ := a.2.symm.trans b.2
    exact reachable_induce_of_walk G v₀ w a.2
  have hdeg : k ≤ (G.induce S).minDegree :=
    le_trans hG (minDegree_le_induce_component G v₀)
  rcases Nat.even_or_odd k with heven | hodd
  · obtain ⟨m, hm, hdvd⟩ := h1 hk heven (G.induce S) hconn hdeg
    exact ⟨m, cycleLengths_induce_subset G S hm, hdvd⟩
  · have hk7 : 7 ≤ k := by
      rcases hodd with ⟨t, rfl⟩
      omega
    obtain ⟨m, hm, hdvd⟩ := h2 hk7 hodd (G.induce S) hconn hdeg
    exact ⟨m, cycleLengths_induce_subset G S hm, hdvd⟩

end OMA.R_Arxiv_2605_02731_dean_conjecture_variants_six_le_R1
