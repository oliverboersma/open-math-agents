import FormalConjectures.Wikipedia.Bunyakovsky

-- Reduction Bunyakovsky.bunyakovsky_conjecture.R1 of the Bunyakovsky conjecture
-- Credit: @marcusbuffett

/-!
# The Bunyakovsky conjecture: degree one is Dirichlet's theorem, and the open rest

The conjecture says that an irreducible integer polynomial with positive leading coefficient and
no fixed prime divisor takes infinitely many prime values.

* `H1` (Dirichlet 1837): the conjecture in degree one. For `f = a x + b` the condition says
  `gcd(a, b) = 1`, and Dirichlet's theorem gives infinitely many primes `p ≡ b (mod a)`.
* `H2`: the conjecture in degree at least two. This is open; no polynomial of degree at least
  two is known to take infinitely many prime values.
-/

namespace OMA.R_Bunyakovsky_bunyakovsky_conjecture_R1

open Polynomial

/-- Degree one: Dirichlet's theorem. -/
def H1 : Prop :=
  ∀ f : ℤ[X], f.natDegree = 1 → BunyakovskyCondition f → SchinzelCondition {f} →
    Infinite {n : ℕ | (f.eval (n : ℤ)).natAbs.Prime}

/-- The open part: degree at least two. -/
def H2 : Prop :=
  ∀ f : ℤ[X], 2 ≤ f.natDegree → BunyakovskyCondition f → SchinzelCondition {f} →
    Infinite {n : ℕ | (f.eval (n : ℤ)).natAbs.Prime}

theorem main : H1 → H2 → type_of% @Bunyakovsky.bunyakovsky_conjecture := by
  intro h1 h2 f hf
  obtain ⟨hb, hs⟩ := hf
  have hdeg : 1 ≤ f.natDegree := by
    have h := hb.1
    exact Polynomial.natDegree_pos_iff_degree_pos.mpr (lt_of_lt_of_le (by norm_num) h)
  by_cases h : f.natDegree = 1
  · exact h1 f h hb hs
  · exact h2 f (by omega) hb hs

end OMA.R_Bunyakovsky_bunyakovsky_conjecture_R1
