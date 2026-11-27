import OMAStatements.S_oeis_a301517

/-!
Source: https://oeis.org/A301517
Credit: @anmolspace (counterexample and Lean proof). Michel Lagneau posed the
conjecture in 2018.

Take `n = 2^7 * 337^3`. The four squarefree divisors sum to 1014, and all
divisors together sum to 9788598300. The nonsquarefree-to-squarefree ratio is
therefore `3107^2`, yet `3107 = 13 * 239`.
-/

namespace OMA.A301517Proof

open Finset OMA.S_oeis_a301517

private abbrev witness : ℕ := 2 ^ 7 * 337 ^ 3

private theorem squarefree_product {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ha : a ≠ 0) (hb : b ≠ 0) : squarefreeSum (p ^ a * q ^ b) =
      ∑ s ∈ (({p} : Finset ℕ) ∪ {q}).powerset, s.val.prod := by
  have hx := pow_ne_zero a hp.ne_zero
  have hy := pow_ne_zero b hq.ne_zero
  rw [squarefreeSum, Nat.sum_divisors_filter_squarefree (mul_ne_zero hx hy), Nat.factors_eq]
  change ∑ s ∈ (p ^ a * q ^ b).primeFactors.powerset, s.val.prod = _
  rw [Nat.primeFactors_mul hx hy, Nat.primeFactors_prime_pow ha hp,
    Nat.primeFactors_prime_pow hb hq]

private theorem squarefree_sum : squarefreeSum witness = 1014 :=
  (squarefree_product Nat.prime_two (show Nat.Prime 337 by norm_num)
    (show (7 : ℕ) ≠ 0 by decide) (show (3 : ℕ) ≠ 0 by decide)).trans (by decide)

private theorem total_product {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hc : p.Coprime q) : ∑ d ∈ (p ^ a * q ^ b).divisors, d =
      (∑ i ∈ range (a + 1), p ^ i) * ∑ j ∈ range (b + 1), q ^ j := by
  rw [(hc.pow a b).sum_divisors_mul, Nat.sum_divisors_prime_pow hp,
    Nat.sum_divisors_prime_pow hq]

private theorem total_sum : ∑ d ∈ witness.divisors, d = 9788598300 :=
  (total_product (a := 7) (b := 3) Nat.prime_two (show Nat.Prime 337 by norm_num)
    (show Nat.Coprime 2 337 by decide)).trans (by decide)

private theorem split_sum (n : ℕ) : squarefreeSum n + nonsquarefreeSum n = ∑ d ∈ n.divisors, d :=
  Finset.sum_filter_add_sum_filter_not _ _ _

private theorem ratio_of_sums {s t : ℕ} (hs : s = 1014) (ht : s + t = 9788598300) :
    t = s * 3107 ^ 2 := by
  subst s
  omega

end OMA.A301517Proof

open OMA.A301517Proof OMA.S_oeis_a301517 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a301517.main) := by
  intro conjecture
  have htotal := (split_sum witness).trans total_sum
  have hratio : nonsquarefreeSum witness = squarefreeSum witness * 3107 ^ 2 := by
    exact ratio_of_sums squarefree_sum htotal
  have hprime := conjecture witness 3107 (by decide) (by decide) hratio
  exact (show ¬ Nat.Prime 3107 by norm_num) hprime
