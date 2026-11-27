import OMAReductions.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1

-- Step FeitThompsonPrimeConjecture.feit_thompson_primes.R1.H2: hypothesis H2 of reduction FeitThompsonPrimeConjecture.feit_thompson_primes.R1
-- Credit: @ivillar
-- Proof (the Jacobi symbol argument sketched in the reduction): N = sum of q^i (i < p) is 3 mod 4
-- (q = 1 mod 4, p = 3 mod 4) and 1 mod p (Fermat, q not 1 mod p). If N divides M = sum of p^i
-- (i < q) then p^q = 1 mod N, so J(p | N) = 1 as q is odd; reciprocity gives J(p | N) = -J(N | p)
-- = -J(1 | p) = -1.

namespace OMA.W3FeitThompsonH2

open Finset

theorem key : ∀ (p q : ℕ), p.Prime → q.Prime → p < q → q % p ≠ 1 → p % 4 = 3 → q % 4 = 1 →
    ¬ (q ^ p - 1) / (q - 1) ∣ (p ^ q - 1) / (p - 1) := by
  intro p q hp hq hpq hqp hp4 hq4 hdvd
  have := Fact.mk hp
  rw [← Nat.geomSum_eq hq.two_le p, ← Nat.geomSum_eq hp.two_le q] at hdvd
  set N := ∑ i ∈ range p, q ^ i with hN
  set M := ∑ i ∈ range q, p ^ i with hM
  -- N mod 4
  have hN4 : N % 4 = 3 := by
    rw [hN, Finset.sum_nat_mod]
    have : ∀ i ∈ range p, q ^ i % 4 = 1 := by
      intro i _
      simp [Nat.pow_mod, hq4]
    rw [Finset.sum_congr rfl this]
    simp [hp4]
  -- N mod p
  have hNp : N % p = 1 := by
    have hq1 : (q : ZMod p) ≠ 1 := by
      intro h
      have := (ZMod.natCast_eq_natCast_iff' q 1 p).1 (by simpa using h)
      rw [Nat.one_mod_eq_one.2 hp.ne_one] at this
      exact hqp this
    have hgeom : ((N : ℕ) : ZMod p) * ((q : ZMod p) - 1) = (q : ZMod p) ^ p - 1 := by
      rw [hN]; push_cast; exact geom_sum_mul _ _
    rw [ZMod.pow_card] at hgeom
    have hsub : (q : ZMod p) - 1 ≠ 0 := sub_ne_zero.2 hq1
    have h1 : ((N : ℕ) : ZMod p) = 1 := by
      exact mul_right_cancel₀ hsub (by rw [hgeom, one_mul])
    have := (ZMod.natCast_eq_natCast_iff' N 1 p).1 (by simpa using h1)
    rwa [Nat.one_mod_eq_one.2 hp.ne_one] at this
  -- coprimality
  have hcop : Int.gcd (p : ℤ) (N : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]
    rw [Nat.gcd_rec, hNp, Nat.gcd_one_left]
  -- p ^ q = 1 mod N
  have hMgeom : ((M : ℕ) : ℤ) * ((p : ℤ) - 1) = (p : ℤ) ^ q - 1 := by
    rw [hM]; push_cast; exact geom_sum_mul _ _
  have hdvdZ : (N : ℤ) ∣ (p : ℤ) ^ q - 1 := by
    rw [← hMgeom]
    exact Dvd.dvd.mul_right (Int.natCast_dvd_natCast.2 hdvd) _
  have hJpow : jacobiSym ((p : ℤ) ^ q) N = 1 := by
    rw [jacobiSym.mod_left' (a₂ := 1), jacobiSym.one_left]
    exact ((Int.modEq_iff_dvd).2 hdvdZ).symm
  rw [jacobiSym.pow_left] at hJpow
  have hJ : jacobiSym p N = 1 := by
    rcases jacobiSym.eq_one_or_neg_one hcop with h | h
    · exact h
    · rw [h, (hq.odd_of_ne_two (by omega)).neg_one_pow] at hJpow
      norm_num at hJpow
  have hrec := jacobiSym.quadratic_reciprocity_three_mod_four hp4 hN4
  have hJN : jacobiSym N p = 1 := by
    rw [jacobiSym.mod_left, ← Int.natCast_mod, hNp]
    exact jacobiSym.one_left p
  rw [hJ, hJN] at hrec
  norm_num at hrec

end OMA.W3FeitThompsonH2

theorem OMA.solution : OMA.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1.H2 := by
  unfold OMA.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1.H2
  exact OMA.W3FeitThompsonH2.key
