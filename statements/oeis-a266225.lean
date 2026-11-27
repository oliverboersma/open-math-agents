import Mathlib

/-!
# The least prime-producing parameter in OEIS A266225

Source: https://oeis.org/A266225
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A266/A266225.seq
Credit: @Heart-galaxy

The primes are indexed starting at one. The value is the least qualifying
integer greater than one, and the failure value is minus one, as in the
entry. The claim excludes that failure value for every index in the domain.
David Radcliffe noted that this follows from Dirichlet's theorem.
-/

namespace OMA.S_oeis_a266225

noncomputable def primeAt (n : ℕ) : ℕ := (n - 1).nth Nat.Prime

def qualifies (n x : ℕ) : Prop := 1 < x ∧ (primeAt n * x + x - 1).Prime

open scoped Classical in
noncomputable def a (n : ℕ) : ℤ :=
  if h : ∃ x : ℕ, qualifies n x then (Nat.find h : ℤ) else -1

theorem main : ∀ n : ℕ, 1 ≤ n → 1 < a n := by
  sorry

end OMA.S_oeis_a266225
