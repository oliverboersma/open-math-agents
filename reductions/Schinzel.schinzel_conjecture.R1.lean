import FormalConjectures.Wikipedia.Schinzel

-- Reduction Schinzel.schinzel_conjecture.R1 of Schinzel's hypothesis H
-- Credit: @marcusbuffett

/-!
# Schinzel's hypothesis H: one linear polynomial is Dirichlet's theorem, and the open rest

The hypothesis says that finitely many irreducible integer polynomials with positive leading
coefficients, with no fixed prime divisor of their product, are simultaneously prime for
infinitely many arguments.

* `H1` (Dirichlet 1837): the hypothesis for at most one polynomial, of degree one.
* `H2`: every other case (two or more polynomials, or a polynomial of degree at least two).
  This is open.
-/

namespace OMA.R_Schinzel_schinzel_conjecture_R1

open Polynomial

/-- At most one polynomial, of degree one: Dirichlet's theorem. -/
def H1 : Prop :=
  ∀ fs : Finset ℤ[X], (∀ f ∈ fs, BunyakovskyCondition f) → SchinzelCondition fs →
    fs.card ≤ 1 → (∀ f ∈ fs, f.natDegree = 1) →
    Infinite {n : ℕ | ∀ f ∈ fs, (f.eval (n : ℤ)).natAbs.Prime}

/-- The open part: everything else. -/
def H2 : Prop :=
  ∀ fs : Finset ℤ[X], (∀ f ∈ fs, BunyakovskyCondition f) → SchinzelCondition fs →
    ¬ (fs.card ≤ 1 ∧ ∀ f ∈ fs, f.natDegree = 1) →
    Infinite {n : ℕ | ∀ f ∈ fs, (f.eval (n : ℤ)).natAbs.Prime}

theorem main : H1 → H2 → type_of% @Schinzel.schinzel_conjecture := by
  intro h1 h2 fs hfs hfs'
  by_cases h : fs.card ≤ 1 ∧ ∀ f ∈ fs, f.natDegree = 1
  · exact h1 fs hfs hfs' h.1 h.2
  · exact h2 fs hfs hfs' h

end OMA.R_Schinzel_schinzel_conjecture_R1
