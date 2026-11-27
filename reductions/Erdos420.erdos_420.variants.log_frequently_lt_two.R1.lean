import FormalConjectures.ErdosProblems.«420»
import Mathlib

/-! The logarithmic statement from the printed form of Corollary 2 of Erdős, Graham, Ivić
and Pomerance, On the number of divisors of n! (1996): F(f, n) < 2 for infinitely many n,
where f(n) = log n log log n log log log log n / (9 (log log log n)^3). The quotient F(f, n)
is nondecreasing in the value f(n), and for every c > 0 the function c log n is eventually
below f(n), so F(c log n, n) < 2 for infinitely many n as well. -/

namespace OMA.R_Erdos420_erdos_420_variants_log_frequently_lt_two_R1
open Filter

/-- Corollary 2 of Erdős, Graham, Ivić and Pomerance, as printed. -/
def H1 : Prop :=
  ∃ᶠ n : ℕ in atTop, Erdos420.F (fun m ↦ Real.log m * Real.log (Real.log m) *
    Real.log (Real.log (Real.log (Real.log m))) /
      (9 * Real.log (Real.log (Real.log m)) ^ 3)) n < 2

/-- The quotient of divisor counts is nondecreasing in the length of the shift. -/
def H2 : Prop := ∀ (f g : ℕ → ℝ) (n : ℕ), f n ≤ g n → Erdos420.F f n ≤ Erdos420.F g n

/-- Every multiple of the logarithm is eventually below the function of Corollary 2. -/
def H3 : Prop := ∀ c > (0 : ℝ), ∀ᶠ m : ℕ in atTop,
  c * Real.log m ≤ Real.log m * Real.log (Real.log m) *
    Real.log (Real.log (Real.log (Real.log m))) /
      (9 * Real.log (Real.log (Real.log m)) ^ 3)

theorem main : H1 → H2 → H3 →
    type_of% @Erdos420.erdos_420.variants.log_frequently_lt_two := by
  intro hrankin hmono hcomp c hc
  refine (hrankin.and_eventually (hcomp c hc)).mono ?_
  rintro n ⟨h1, h2⟩
  exact lt_of_le_of_lt (hmono _ _ n h2) h1

end OMA.R_Erdos420_erdos_420_variants_log_frequently_lt_two_R1
