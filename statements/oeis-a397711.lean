/-
OEIS A397711, the congruences of Tyler Satchel Orden and the general divisibility theorem.
Reference: https://oeis.org/A397711
Credit: @Heart-galaxy
Text credit: OEIS Foundation, CC BY-SA 4.0.

We define the bounded-indegree DAG counts by the sink inclusion-exclusion
recurrence in Lemma 4 (with s = 1) of Roberto Blanco Gómez, “Congruences for
labeled acyclic digraphs of bounded in-degree” (2026),
https://doi.org/10.5281/zenodo.23201448.

In that lemma, choosing a set of sinks reduces the graph on the remaining
vertices and chooses each sink's parent set independently. The paper proves
the equivalence of this recurrence and the DAG count. This formalization uses
the recurrence and takes that enumeration identity from the cited lemma.
The two congruences and the general divisibility are Theorems 2 and 3.
-/

import Mathlib

open Finset

namespace OMA.S_oeis_a397711

def parentChoices (r m : ℕ) : ℤ :=
  1 + ∑ i ∈ range r, (m.choose (i + 1) : ℤ)

def a (r : ℕ) : (n : ℕ) → ℤ
  | 0 => 1
  | n + 1 => ∑ m ∈ (range (n + 1)).attach,
      (-1 : ℤ) ^ (n - m) * ((n + 1).choose m : ℤ) *
        (a r m * parentChoices r m ^ (n + 1 - m))
termination_by n => n
decreasing_by exact mem_range.mp m.property

def multiplier (r : ℕ) : ℕ := (range r).lcm (· + 1)

theorem main :
    (∀ n : ℕ, 3 ≤ n → Odd n → a 2 n ≡ 1 [ZMOD (n : ℤ)]) ∧
    (∀ n : ℕ, 4 ≤ n → Even n → a 2 n ≡ ((n / 2 : ℕ) : ℤ) + 1 [ZMOD (n : ℤ)]) ∧
    (∀ r n : ℕ, 1 ≤ r → 1 ≤ n → (n : ℤ) ∣ (multiplier r : ℤ) * (a r n - 1)) := by
  sorry

end OMA.S_oeis_a397711
