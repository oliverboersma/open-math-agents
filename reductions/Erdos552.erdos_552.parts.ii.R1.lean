import FormalConjectures.ErdosProblems.«552»
import Mathlib

/-!
# A jump-count criterion for the four-cycle versus star problem

Between integer arguments Chen's bound permits increments of zero, one or two.
In an interval ending at a prime square, Parsons' exact value anchors their sum.
The remaining problem is a signed count of the exceptional steps of size zero and two.
The interval may be restricted to the first prime square above its left endpoint.
-/

namespace OMA.R_Erdos552_erdos_552_parts_ii_R1
open SimpleGraph Finset
open scoped Classical

/-- Parsons' prime-square values, supplying the endpoint for each count. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime →
    graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin (p^2))) = p^2+p+1

/-- Monotonicity and Chen's upper bound on the single-step increment. -/
def H2 : Prop :=
  let f := fun n : ℕ => graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin n))
  ∀ n : ℕ, 1 ≤ n → f n ≤ f (n+1) ∧ f (n+1) ≤ f n + 2

/-- In a prime-square interval count the double jumps and stationary steps.
Only the first prime square above the proposed index needs to be tested. -/
def H3 : Prop :=
  let f := fun n : ℕ => graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin n))
  ∀ K B : ℕ, ∃ n p : ℕ, B < n ∧ p.Prime ∧ n ≤ p^2 ∧
    (∀ r : ℕ, r.Prime → n ≤ r^2 → p ≤ r) ∧
    ((Ico n (p^2)).filter (fun i => f (i+1) = f i)).card + p + K + 1 ≤
      ((Ico n (p^2)).filter (fun i => f (i+1) = f i+2)).card + Nat.sqrt n

theorem count_jumps (f : ℕ → ℕ) (a b : ℕ) (pos : 1 ≤ a) (ab : a ≤ b)
    (step : ∀ i, 1 ≤ i → f i ≤ f (i+1) ∧ f (i+1) ≤ f i+2) :
    f b + ((Ico a b).filter (fun i => f (i+1) = f i)).card + a =
    f a + b + ((Ico a b).filter (fun i => f (i+1) = f i+2)).card := by
  induction b, ab using Nat.le_induction with
  | base => simp [add_comm]
  | succ b hab ih =>
    have next : Ico a (b+1) = insert b (Ico a b) := by
      rw [Ico_add_one_right_eq_Icc, Ico_insert_right hab]
    have notin : b ∉ Ico a b := by simp
    obtain ⟨lo,hi⟩ := step b (by omega)
    have cases : f (b+1)=f b ∨ f (b+1)=f b+1 ∨ f (b+1)=f b+2 := by omega
    rcases cases with h|h|h <;> rw [next] <;>
      simp [Finset.filter_insert,h,notin] at * <;> omega

theorem main : H1 → H2 → H3 → type_of% @Erdos552.erdos_552.parts.ii := by
  classical
  intro anchor step excursions c hc
  rw [Set.infinite_iff_exists_gt]
  intro B
  obtain ⟨K,hK⟩ := exists_nat_ge c
  obtain ⟨n,p,hn,hp,upper,_,gain⟩ := excursions K B
  refine ⟨n,?_,hn⟩
  let f := fun j : ℕ => graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin j))
  have sum := count_jumps f n (p^2) (by omega) upper step
  have atp : f (p^2) = p^2+p+1 := anchor p hp
  change ((Ico n (p^2)).filter (fun i => f (i+1) = f i)).card + p + K + 1 ≤
    ((Ico n (p^2)).filter (fun i => f (i+1) = f i+2)).card + Nat.sqrt n at gain
  have bound : f n + K ≤ n + Nat.sqrt n := by omega
  have realbound : (f n : ℝ) + (K : ℝ) ≤ (n : ℝ) + (Nat.sqrt n : ℝ) := by exact_mod_cast bound
  change (f n : ℝ) ≤ (n : ℝ) + Real.sqrt n - c
  linarith [Real.nat_sqrt_le_real_sqrt (a:=n)]
end OMA.R_Erdos552_erdos_552_parts_ii_R1
