import FormalConjectures.ErdosProblems.«977»
import Mathlib.NumberTheory.Primorial

-- Reduction Erdos977.erdos_977.variants.factorial.R1 of Erdős Problem 977 (factorial case)
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# P(n! + 1) / n tends to infinity, from an abc estimate

The conditional argument of Murty and Wong, *The ABC conjecture and prime divisors of the Lucas
and Lehmer sequences* (2002), who get `P(n! + 1) > (1 + o(1)) n log n` from the abc conjecture.
Here `P` is the greatest prime factor and `rad` the product of the prime factors.

* `H1` (open core): the abc inequality with exponent 3/2 for the triples `(1, n!, n! + 1)`,
  whose radical is `primorial n * rad (n! + 1)`. This is word for word `H3` of
  `Erdos936.erdos_936.variants.factorial_add_one.R1`.
* `H2` (elementary): factorials eventually dominate every fixed geometric sequence.

`main`: every prime factor of `c = n! + 1` is at most `P`, so `rad c ≤ primorial P ≤ 4 ^ P`,
and `primorial n ≤ 4 ^ n`. If `P ≤ A * n` then `H1` gives `c ^ 2 ≤ C * (64 ^ (1 + A)) ^ n`,
which `H2` contradicts for large `n`. So `P > A * n` eventually, for every `A`.
-/

open Finset Filter Nat

namespace OMA.R_Erdos977_erdos_977_variants_factorial_R1

/-- The abc estimate with exponent 3/2 for the triples `(1, n!, n! + 1)`, written with
integer powers. -/
def H1 : Prop :=
  ∃ C : ℕ, ∀ n : ℕ,
    let c := n.factorial + 1
    c ^ 2 ≤ C * (primorial n * (∏ p ∈ c.primeFactors, p)) ^ 3

/-- Factorials eventually dominate every fixed geometric sequence. -/
def H2 : Prop :=
  ∀ C K : ℕ, ∀ᶠ n : ℕ in atTop, C * K ^ n < n.factorial

/-- The radical of `m` is at most `4 ^ P(m)`, by the Chebyshev bound on primorials. -/
lemma radical_le_four_pow (m : ℕ) (hm : m ≠ 0) :
    ∏ p ∈ m.primeFactors, p ≤ 4 ^ Nat.maxPrimeFac m := by
  refine le_trans ?_ (primorial_le_four_pow _)
  unfold primorial
  refine Finset.prod_le_prod_of_subset_of_one_le' ?_ ?_
  · intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le
      (Nat.le_maxPrimeFac hm hp' (Nat.dvd_of_mem_primeFactors hp))), hp'⟩
  · intro p hp _
    exact (Finset.mem_filter.mp hp).2.one_le

theorem main : H1 → H2 → type_of% @Erdos977.erdos_977.variants.factorial := by
  intro ⟨C, hABC⟩ growth
  rw [tendsto_atTop]
  intro b
  obtain ⟨A, hA⟩ := exists_nat_ge b
  filter_upwards [growth C (64 ^ (1 + A)), eventually_gt_atTop 0] with n hn hn0
  let c := n.factorial + 1
  let r := ∏ p ∈ c.primeFactors, p
  have key : A * n < Nat.maxPrimeFac c := by
    by_contra hle
    have hP : Nat.maxPrimeFac c ≤ A * n := not_lt.mp hle
    have hr : r ≤ 4 ^ (A * n) :=
      (radical_le_four_pow c (by dsimp [c]; omega)).trans (Nat.pow_le_pow_right (by norm_num) hP)
    have hABCn : c ^ 2 ≤ C * (primorial n * r) ^ 3 := hABC n
    have hprod : (primorial n * r) ^ 3 ≤ (64 ^ (1 + A)) ^ n := by
      calc
        (primorial n * r) ^ 3 ≤ (4 ^ n * 4 ^ (A * n)) ^ 3 :=
          Nat.pow_le_pow_left (Nat.mul_le_mul (primorial_le_four_pow n) hr) 3
        _ = (64 ^ (1 + A)) ^ n := by
          rw [show (64 : ℕ) = 4 ^ 3 by norm_num, ← pow_add, ← pow_mul, ← pow_mul, ← pow_mul]
          congr 1
          ring
    have hc : c ≤ c ^ 2 := Nat.le_self_pow (by norm_num) c
    have hfac : n.factorial < c := Nat.lt_succ_self _
    have hle2 : c ^ 2 ≤ C * (64 ^ (1 + A)) ^ n := hABCn.trans (Nat.mul_le_mul_left _ hprod)
    omega
  have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
  have keyR : (A : ℝ) * n ≤ (Nat.maxPrimeFac c : ℝ) := by exact_mod_cast key.le
  exact hA.trans ((le_div_iff₀ hn0').mpr keyR)

end OMA.R_Erdos977_erdos_977_variants_factorial_R1
