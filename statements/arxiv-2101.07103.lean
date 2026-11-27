import Mathlib

/-!
# Hubs-biased Kirchhoff indices

Source: Estrada and Mugnolo, arXiv:2101.07103, Conjecture 4.13, equations
(3.1), (3.6), (4.9), and (4.15). Credit: @rleshner.

Adjacency and degree determine rational directed edge conductances. We embed
the Laplacians in the reals and characterize their Moore–Penrose inverses
by the four Penrose equations. The half-sum over ordered pairs equals the
sum over unordered pairs of distinct vertices.
-/

namespace OMA.S_arxiv_2101_07103

inductive Bias
  | repelling | ordinary | attracting

def lap {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (b : Bias) :
    Matrix (Fin n) (Fin n) ℚ :=
  let c (i j : Fin n) : ℚ :=
    if G.Adj i j then
      match b with
      | .repelling => (G.degree i : ℚ) / G.degree j
      | .ordinary => 1
      | .attracting => (G.degree j : ℚ) / G.degree i
    else 0
  fun i j => if i = j then ∑ k, c i k else -c i j

def Penrose {n : ℕ} {K : Type*} [Field K] (L P : Matrix (Fin n) (Fin n) K) : Prop :=
  L * P * L = L ∧ P * L * P = P ∧ (L * P).transpose = L * P ∧ (P * L).transpose = P * L

def index {n : ℕ} {K : Type*} [Field K] (P : Matrix (Fin n) (Fin n) K) : K :=
  (∑ i, ∑ j, (P i i + P j j - P i j - P j i)) / 2

theorem main : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.Connected →
    ∀ P : Bias → Matrix (Fin n) (Fin n) ℝ,
    (∀ b, Penrose ((lap G b).map (Rat.castHom ℝ)) (P b)) →
    index (P .attracting) ≤ index (P .ordinary) ∧
    index (P .ordinary) ≤ index (P .repelling) ∧
    ((index (P .attracting) = index (P .ordinary) ∧
      index (P .ordinary) = index (P .repelling)) ↔ ∀ i j, G.degree i = G.degree j) := by
  sorry

end OMA.S_arxiv_2101_07103
