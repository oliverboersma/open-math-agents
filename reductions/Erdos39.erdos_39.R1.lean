import FormalConjectures.ErdosProblems.«39»

-- Reduction of Erdős Problem 39
-- Credit: @missionaryj

namespace OMA.R_Erdos39_erdos_39_R1

open Filter Asymptotics

-- One counting envelope must work for every finite horizon.
def H1 : Prop :=
  ∃ f : ℕ → ℕ, (∀ k, ∃ n, k ≤ f n) ∧
    (∀ ε > (0 : ℝ), (· ^ (1 / 2 - ε) : ℕ → ℝ) =O[atTop] fun n => (f n : ℝ)) ∧
    ∀ K : ℕ, ∃ B : Finset ℕ, IsSidon (B : Set ℕ) ∧
      ∀ n ≤ K, f n ≤ ((Set.Icc 1 n) ∩ (B : Set ℕ)).ncard

-- Compactness for finite Sidon prefixes with any unbounded envelope.
def H2 : Prop :=
  ∀ f : ℕ → ℕ, (∀ k, ∃ n, k ≤ f n) →
    (∀ K : ℕ, ∃ B : Finset ℕ, IsSidon (B : Set ℕ) ∧
      ∀ n ≤ K, f n ≤ ((Set.Icc 1 n) ∩ (B : Set ℕ)).ncard) →
    ∃ A : Set ℕ, A.Infinite ∧ IsSidon A ∧ ∀ n, f n ≤ ((Set.Icc 1 n) ∩ A).ncard

theorem main : H1 → H2 → type_of% @Erdos39.erdos_39 := by
  intro hfin hcomp
  obtain ⟨f, hu, hg, hprefix⟩ := hfin
  obtain ⟨A, hA, hS, hcount⟩ := hcomp f hu hprefix
  refine ⟨A, hA, hS, ?_⟩
  intro ε hε
  apply (hg ε hε).trans
  apply Asymptotics.IsBigO.of_bound'
  apply Filter.Eventually.of_forall
  intro n
  simp only [Real.norm_natCast]
  exact_mod_cast hcount n

end OMA.R_Erdos39_erdos_39_R1
