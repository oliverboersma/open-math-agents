import FormalConjectures.ErdosProblems.«933»
import Mathlib

/-! Mahler's bound 2^k 3^l < n^(1 + o(1)) for the part of n (n + 1) composed of 2 and 3.
Mahler, Über den grössten Primteiler spezieller Polynome zweiten Grades, Arch. Math.
Naturvid. 41 (1935), gives for every fixed eps > 0 that the part of n (n + 1) composed of
primes from a fixed finite set is below n^(1 + eps) for all large n; that is H1 for the set
{2, 3}. Passing from a bound for every eps to a single exponent 1 + c(n) with c(n) tending
to 0 is a statement about an arbitrary real sequence. -/

namespace OMA.R_Erdos933_erdos_933_variants_mahler_R1
open Filter Asymptotics

/-- Mahler: for every eps > 0, the {2, 3}-part of n (n + 1) is below n^(1 + eps) for large n. -/
def H1 : Prop := ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
  ((2 ^ Erdos933.k n * 3 ^ Erdos933.l n : ℕ) : ℝ) < (n : ℝ) ^ (1 + ε)

/-- A sequence that is eventually below n^(1 + eps) for every eps > 0 is eventually below
n^(1 + c(n)) for some c(n) tending to 0. -/
def H2 : Prop := ∀ F : ℕ → ℝ,
  (∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, F n < (n : ℝ) ^ (1 + ε)) →
  ∃ c : ℕ → ℝ, (c =o[atTop] (1 : ℕ → ℝ)) ∧ ∀ᶠ n in atTop, F n < (n : ℝ) ^ (1 + c n)

theorem main : H1 → H2 → type_of% @Erdos933.erdos_933.variants.mahler := by
  intro h1 h2
  exact h2 (fun n => ((2 ^ Erdos933.k n * 3 ^ Erdos933.l n : ℕ) : ℝ)) h1

end OMA.R_Erdos933_erdos_933_variants_mahler_R1
