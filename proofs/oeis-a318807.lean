import OMAStatements.S_oeis_a318807

/-!
Source: https://oeis.org/A318807
Credit: @anmolspace (counterexample and Lean proof). Michel Lagneau posed the
two-square divisor-sum conjecture in 2018.

Multiplying the counterexample `2^7 * 337^3` for A301517 by the new prime 5
multiplies both divisor sums by 6. This makes the sums themselves perfect
squares, `78^2` and `242346^2`, and preserves the ratio `3107^2`.
-/

namespace OMA.A318807Proof

open Finset OMA.S_oeis_a318807

private abbrev witness : ℕ := 2 ^ 7 * 337 ^ 3 * 5

/-- A squarefree divisor is the product of a subset of the prime divisors. -/
private theorem squarefree_formula {n : ℕ} (hn : n ≠ 0) :
    squarefreeSum n = ∏ p ∈ n.primeFactors, (1 + p) := by
  rw [squarefreeSum, Nat.sum_divisors_filter_squarefree hn, Nat.factors_eq]
  change ∑ s ∈ n.primeFactors.powerset, s.val.prod = _
  rw [Finset.prod_one_add]
  exact Finset.sum_congr rfl fun s _ => Finset.prod_val s

private theorem prime_factors {p q r a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (ha : a ≠ 0) (hb : b ≠ 0) : (p ^ a * q ^ b * r).primeFactors = ({p} ∪ {q}) ∪ {r} := by
  have hx := pow_ne_zero a hp.ne_zero
  have hy := pow_ne_zero b hq.ne_zero
  rw [Nat.primeFactors_mul (mul_ne_zero hx hy) hr.ne_zero, Nat.primeFactors_mul hx hy,
    Nat.primeFactors_prime_pow ha hp, Nat.primeFactors_prime_pow hb hq, hr.primeFactors]

private theorem squarefree_sum : squarefreeSum witness = 6084 := by
  apply (squarefree_formula (show witness ≠ 0 by decide)).trans
  rw [prime_factors Nat.prime_two (show Nat.Prime 337 by norm_num) (show Nat.Prime 5 by norm_num)
    (show (7 : ℕ) ≠ 0 by decide) (show (3 : ℕ) ≠ 0 by decide)]
  decide

private theorem total_product {p q r a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hc : p.Coprime q) (hd : (p ^ a * q ^ b).Coprime r) :
    ∑ d ∈ (p ^ a * q ^ b * r).divisors, d =
      (∑ i ∈ range (a + 1), p ^ i) * (∑ j ∈ range (b + 1), q ^ j) * (1 + r) := by
  rw [hd.sum_divisors_mul, (hc.pow a b).sum_divisors_mul, Nat.sum_divisors_prime_pow hp,
    Nat.sum_divisors_prime_pow hq]
  simp [hr.divisors, hr.ne_one.symm]

private theorem total_sum : ∑ d ∈ witness.divisors, d = 58731589800 :=
  (total_product (a := 7) (b := 3) Nat.prime_two (show Nat.Prime 337 by norm_num)
    (show Nat.Prime 5 by norm_num) (by decide) (by decide)).trans (by decide)

private theorem split_sum (n : ℕ) : squarefreeSum n + nonsquarefreeSum n = ∑ d ∈ n.divisors, d :=
  Finset.sum_filter_add_sum_filter_not _ _ _

private theorem values {s t : ℕ} (hs : s = 6084) (ht : s + t = 58731589800) :
    IsSquare s ∧ IsSquare t ∧ t = s * 3107 ^ 2 := by
  subst s
  have h : t = 58731583716 := by omega
  subst t
  exact ⟨⟨78, by decide⟩, ⟨242346, by decide⟩, by decide⟩

end OMA.A318807Proof

open OMA.A318807Proof OMA.S_oeis_a318807 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a318807.main) := by
  intro conjecture
  obtain ⟨hs, ht, hr⟩ := values squarefree_sum ((split_sum witness).trans total_sum)
  obtain ⟨p, hp, he⟩ := conjecture witness (3107 ^ 2) (by decide) hs ht (by decide) hr
  have h : p = 3107 := by nlinarith
  exact (show ¬ Nat.Prime 3107 by norm_num) (h ▸ hp)
