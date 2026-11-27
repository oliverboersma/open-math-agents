import FormalConjectures.Wikipedia.Oppermann
import Mathlib

/-! Oppermann's conjecture for large x from a prime gap bound below the square root. Ferreira,
Real exponential sums over primes and prime gaps (arXiv 2307.08725), states an asymptotic for
the number of primes in (x, x + x^l] for every 0 < l < 1; for l below 1/2 it gives consecutive
primes p < q with q - p < p^(1/2 - c) from some point on, which is the hypothesis of the
catalogue's LegendreConjecture.bounded_gap_legendre. The passage to Oppermann is elementary:
a gap below sqrt p after the largest prime p ≤ M puts the next prime in (M, M + sqrt M), and
M = x (x - 1) and M = x^2 give the two intervals. -/

namespace OMA.R_Oppermann_oppermann_conjecture_ferreira_large_x_R1

/-- Prime gaps are eventually below a fixed power of the prime less than 1/2 (Ferreira). -/
def H1 : Prop := ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in Filter.atTop,
  ((n + 1).nth Nat.Prime : ℝ) - (n.nth Nat.Prime : ℝ) < (n.nth Nat.Prime : ℝ) ^ (1 / (2 : ℝ) - c)

/-- Prime gaps below the square root from the N-th prime on imply both parts of Oppermann's
conjecture for every x with x (x - 1) above the N-th prime. -/
def H2 : Prop := ∀ N : ℕ,
  (∀ n ≥ N, ((n + 1).nth Nat.Prime : ℝ) - (n.nth Nat.Prime : ℝ) <
    Real.sqrt (n.nth Nat.Prime)) →
  ∀ x : ℕ, N.nth Nat.Prime < x * (x - 1) →
    (∃ p ∈ Finset.Ioo (x * (x - 1)) (x ^ 2), p.Prime) ∧
    (∃ p ∈ Finset.Ioo (x ^ 2) (x * (x + 1)), p.Prime)

theorem main : H1 → H2 → type_of% @Oppermann.oppermann_conjecture.ferreira_large_x := by
  rintro ⟨c, hc, h1⟩ h2
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h1
  have hgap : ∀ n ≥ N, ((n + 1).nth Nat.Prime : ℝ) - (n.nth Nat.Prime : ℝ) <
      Real.sqrt (n.nth Nat.Prime) := by
    intro n hn
    have hp1 : (1 : ℝ) ≤ (n.nth Nat.Prime : ℝ) := by
      exact_mod_cast (Nat.prime_nth_prime n).one_lt.le
    calc ((n + 1).nth Nat.Prime : ℝ) - (n.nth Nat.Prime : ℝ)
        < (n.nth Nat.Prime : ℝ) ^ (1 / (2 : ℝ) - c) := hN n hn
      _ ≤ (n.nth Nat.Prime : ℝ) ^ (1 / (2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
      _ = Real.sqrt (n.nth Nat.Prime) := (Real.sqrt_eq_rpow _).symm
  refine Filter.eventually_atTop.2 ⟨N.nth Nat.Prime + 2, fun x hx => ?_⟩
  refine h2 N hgap x ?_
  have h1x : 1 ≤ x - 1 := by omega
  calc N.nth Nat.Prime < x := by omega
    _ = x * 1 := (mul_one x).symm
    _ ≤ x * (x - 1) := Nat.mul_le_mul_left x h1x

end OMA.R_Oppermann_oppermann_conjecture_ferreira_large_x_R1
