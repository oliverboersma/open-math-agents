import FormalConjectures.ErdosProblems.«551»

-- Credit: @my-other-github-account. Threshold split from OpenAI, Apache-2.0,
-- openai/math@3344da59991ed94f9ba711217b29c1d760badfa6, lean/OAI/Combinatorics/Ramsey/CycleClique.
-- At k ≥ 19, a minimal expanding counterexample has clique number at least nine,
-- so the large-clique argument applies; shorter cycles require finite certificates.
namespace OMA.R_Erdos551_erdos_551_R1
open SimpleGraph

def H1 : Prop := ∀ k n : ℕ, 19 ≤ k → 3 ≤ n → n ≤ k →
  graphRamsey (cycleGraph k) (completeGraph (Fin n)) = (k-1)*(n-1)+1

def H2 : Prop := ∀ k n : ℕ, k ≤ 18 → 3 ≤ n → n ≤ k → ¬ (n = 3 ∧ k = 3) →
  graphRamsey (cycleGraph k) (completeGraph (Fin n)) = (k-1)*(n-1)+1

theorem main : H1 → H2 → type_of% @Erdos551.erdos_551 := by
  intro large small k n hn hnk hne
  by_cases h : 19 ≤ k
  · exact large k n h hn hnk
  · exact small k n (by omega) hn hnk hne

end OMA.R_Erdos551_erdos_551_R1
