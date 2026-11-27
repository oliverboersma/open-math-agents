import FormalConjectures.ErdosProblems.«552»
import Mathlib

/-!
# A minimum-degree obstruction for the quadrilateral versus star problem

For every integer saving k it is enough to give one pair n,d for which
(d+k)²≤n and every C₄-free graph on n+d vertices has a vertex of degree
less than d. This formulation removes Ramsey numbers, real square roots,
prime-square endpoints and the requirement of infinitely many constructions
at each fixed saving from the remaining graph problem.
-/

namespace OMA.R_Erdos552_erdos_552_parts_ii_R2
open SimpleGraph

/-- The complement contains the requested star exactly when a vertex of the
original graph has degree below the proposed threshold. -/
def H1 : Prop := ∀ (n d : ℕ) (G : SimpleGraph (Fin (n+d))) [DecidableRel G.Adj],
    (completeBipartiteGraph (Fin 1) (Fin n)).IsContained Gᶜ ↔
      ∃ v, G.degree v < d

/-- The remaining extremal graph problem, involving only finite graphs and integers. -/
def H2 : Prop := ∀ k : ℕ, ∃ n d : ℕ, (d+k)^2 ≤ n ∧
    ∀ (G : SimpleGraph (Fin (n+d))) [DecidableRel G.Adj],
      ¬(cycleGraph 4).IsContained G → ∃ v, G.degree v < d

theorem main : H1 → H2 → type_of% @Erdos552.erdos_552.parts.ii := by
  classical
  intro stars obstructions c hc
  rw [Set.infinite_iff_exists_gt]
  intro B
  obtain ⟨a,ha⟩ := exists_nat_ge c
  let k := max a B + 1
  have ka : a ≤ k := (le_max_left a B).trans (by dsimp [k]; omega)
  have kb : B < k := (le_max_right a B).trans_lt (by dsimp [k]; omega)
  obtain ⟨n,d,size,low⟩ := obstructions k
  have index : B < n := by
    have h : k ≤ d+k := by omega
    have sq : 1 ≤ d+k := by omega
    have bigger := Nat.mul_le_mul_left (d+k) sq
    rw [pow_two] at size
    omega
  have cutoff : graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin n)) ≤ n+d := by
    apply Nat.sInf_le
    intro G
    by_cases red : (cycleGraph 4).IsContained G
    · exact Or.inl red
    · exact Or.inr ((stars n d G).mpr (low G red))
  have sizeR : ((d:ℝ)+(k:ℝ))^2 ≤ (n:ℝ) := by exact_mod_cast size
  have root := Real.sqrt_le_sqrt sizeR
  rw [Real.sqrt_sq (by positivity)] at root
  have ck : c ≤ (k:ℝ) := ha.trans (by exact_mod_cast ka)
  have cutoffR : (graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin n)) : ℝ)
      ≤ (n:ℝ)+(d:ℝ) := by exact_mod_cast cutoff
  refine ⟨n, ?_, index⟩
  change (graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin n)) : ℝ)
      ≤ (n:ℝ)+Real.sqrt n-c
  linarith

end OMA.R_Erdos552_erdos_552_parts_ii_R2
