import FormalConjectures.ErdosProblems.«562»
import Mathlib

/-! The iterated logarithm of the hypergraph Ramsey number R_r(n) is conjectured to be of order
n for every r >= 3. The upper bound is the theorem of Erdős and Rado (Combinatorial theorems on
classifications of subsets of a given set, Proc. London Math. Soc. 1952): the stepping-up
inequality R_r(n) <= 2 ^ (R_{r-1}(n-1) ^ (r-1)) iterated down to graphs gives a tower of height r
in n. The lower bound is the open part: the stepping-up lemma of Erdős and Hajnal only gives a
tower of height r - 1, and already for r = 3 the lower bound 2 ^ (2 ^ (c n)) is the well-known
open problem. -/

namespace OMA.R_Erdos562_erdos_562_R1

open Filter Asymptotics

/-- Erdős and Rado: the (r-1)-fold iterated logarithm of R_r(n) is O(n). -/
def H1 : Prop :=
  ∀ r ≥ 3, (fun n : ℕ ↦ Real.log^[r - 1] (Combinatorics.hypergraphRamsey r n : ℝ)) =O[atTop]
    (fun n : ℕ ↦ (n : ℝ))

/-- The open lower bound: n is O of the (r-1)-fold iterated logarithm of R_r(n). -/
def H2 : Prop :=
  ∀ r ≥ 3, (fun n : ℕ ↦ (n : ℝ)) =O[atTop]
    (fun n : ℕ ↦ Real.log^[r - 1] (Combinatorics.hypergraphRamsey r n : ℝ))

theorem main : H1 → H2 → type_of% @Erdos562.erdos_562 := by
  intro h1 h2 r hr
  exact ⟨h1 r hr, h2 r hr⟩

end OMA.R_Erdos562_erdos_562_R1
