import OMAReductions.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1

-- Step FeitThompsonPrimeConjecture.feit_thompson_primes.R1.H1: hypothesis H1 of reduction FeitThompsonPrimeConjecture.feit_thompson_primes.R1
-- Credit: @ivillar
-- Proof: write both quotients as geometric sums. Since q = 1 mod p, the sum of q^i for i < p is
-- p = 0 mod p, while the sum of p^i for i < q is 1 mod p. So the first cannot divide the second.

namespace OMA.W3FeitThompsonH1

open Finset

theorem geom (m n : ℕ) (hm : 2 ≤ m) : (m ^ n - 1) / (m - 1) = ∑ i ∈ range n, m ^ i :=
  (Nat.geomSum_eq hm n).symm

theorem key : ∀ (p q : ℕ), p.Prime → q.Prime → p < q → q % p = 1 →
    ¬ (q ^ p - 1) / (q - 1) ∣ (p ^ q - 1) / (p - 1) := by
  intro p q hp hq hpq hqp hdvd
  rw [geom q p hq.two_le, geom p q hp.two_le] at hdvd
  have hA : p ∣ ∑ i ∈ range p, q ^ i := by
    apply Nat.dvd_of_mod_eq_zero
    rw [Finset.sum_nat_mod]
    have : ∀ i ∈ range p, q ^ i % p = 1 := by
      intro i _
      rw [Nat.pow_mod, hqp, one_pow, Nat.mod_eq_of_lt hp.one_lt]
    rw [Finset.sum_congr rfl this]
    simp
  have hB : (∑ i ∈ range q, p ^ i) % p = 1 := by
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    rw [Finset.sum_range_succ', pow_zero]
    have : p ∣ ∑ i ∈ range r, p ^ (i + 1) :=
      Finset.dvd_sum (fun i _ => dvd_pow_self p (Nat.succ_ne_zero i))
    obtain ⟨c, hc⟩ := this
    rw [hc, Nat.mul_add_mod, Nat.mod_eq_of_lt hp.one_lt]
  have := (Nat.dvd_trans hA hdvd)
  rw [Nat.dvd_iff_mod_eq_zero, hB] at this
  exact one_ne_zero this

end OMA.W3FeitThompsonH1

theorem OMA.solution : OMA.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1.H1 := by
  unfold OMA.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1.H1
  exact OMA.W3FeitThompsonH1.key
