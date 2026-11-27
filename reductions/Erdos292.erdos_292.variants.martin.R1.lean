import FormalConjectures.ErdosProblems.«292»
import Mathlib

/-! Martin's theorem (Denser Egyptian fractions, Acta Arith. 95 (2000)) says that the
complement B of A satisfies |B ∩ [1, x]| / x ≍ log log x / log x. The two hypotheses are its
two halves. The upper bound is the deep one: all integers except small multiples of prime
powers are the largest denominator of some Egyptian fraction for 1. The lower bound is the
other half of the paper: a multiple m p of a prime p > m * m! is never in A, by looking at the
terms divisible by p, and there are at least c x log log x / log x such integers up to x by
Chebyshev's lower bound for the number of primes. -/

namespace OMA.R_Erdos292_erdos_292_variants_martin_R1

open Filter Asymptotics

/-- Martin's upper bound: the complement of `A` has `O(x log log x / log x)` elements up to
`x`. -/
def H1 : Prop :=
  (fun x : ℕ ↦ ((Erdos292.Aᶜ ∩ Set.Icc 1 x).ncard : ℝ) / x) =O[atTop]
    (fun x : ℕ ↦ Real.log (Real.log x) / Real.log x)

/-- Martin's lower bound: the complement of `A` has at least `c x log log x / log x`
elements up to `x`. -/
def H2 : Prop :=
  (fun x : ℕ ↦ Real.log (Real.log x) / Real.log x) =O[atTop]
    (fun x : ℕ ↦ ((Erdos292.Aᶜ ∩ Set.Icc 1 x).ncard : ℝ) / x)

theorem main : H1 → H2 → type_of% @Erdos292.erdos_292.variants.martin := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_Erdos292_erdos_292_variants_martin_R1
