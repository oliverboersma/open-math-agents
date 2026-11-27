import FormalConjectures.ErdosProblems.«457»
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Prime.Factorial

/-!
A prime above the block length divides the block product precisely when
it divides the binomial coefficient obtained by canceling the factorial.
Primes at most the block length already divide the factorial.
-/

namespace OMA.R_Erdos457_erdos_457_variants_one_sub_R1

open Finset Filter

def H1 : Prop :=
  ∀ n k : ℕ,
    (∏ i ∈ Icc 1 k, (n + i)) = k.factorial * (n + k).choose k

def H2 : Prop :=
  ∃ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    let k := ⌊Real.log n⌋₊
    let B := ⌈(1 - ε) * Real.log n ^ 2⌉₊
    ¬ (∏ p ∈ (range B).filter (fun p => p.Prime ∧ k < p), p) ∣ (n + k).choose k

section Proof

theorem main : H1 → H2 → type_of% @Erdos457.erdos_457.variants.one_sub := by
  intro blockProduct missingProduct
  obtain ⟨ε, hε, hevents⟩ := missingProduct
  refine ⟨ε, hε, ?_⟩
  filter_upwards [hevents] with n hmissing
  let k := ⌊Real.log n⌋₊
  let B := ⌈(1 - ε) * Real.log n ^ 2⌉₊
  let candidates := (range B).filter (fun p => p.Prime ∧ k < p)
  let c := (n + k).choose k
  have hc : 0 < c := Nat.choose_pos (Nat.le_add_left k n)
  have hnotDvd : ∃ p ∈ candidates, ¬ p ∣ c := by
    by_contra! h
    have hsub : candidates ⊆ c.primeFactors := by
      intro p hp
      have hprime := (mem_filter.mp hp).2.1
      exact Nat.mem_primeFactors.mpr ⟨hprime, h p hp, hc.ne'⟩
    have hprod : (∏ p ∈ candidates, p) ∣ ∏ p ∈ c.primeFactors, p :=
      prod_dvd_prod_of_subset _ _ id hsub
    exact hmissing (hprod.trans (Nat.prod_primeFactors_dvd c))
  obtain ⟨p, hp, hpDvd⟩ := hnotDvd
  obtain ⟨hpB, hpPrime, hpk⟩ := mem_filter.mp hp
  have hpBlock : ¬ p ∣ ∏ i ∈ Icc 1 k, (n + i) := by
    rw [blockProduct n k, hpPrime.dvd_mul, hpPrime.dvd_factorial]
    exact fun h => h.elim hpk.not_ge hpDvd
  have hpQ : Erdos457.q n (Real.log n) ≤ p :=
    Nat.find_min' _ ⟨hpPrime, hpBlock⟩
  have hpR : (p : ℝ) < (1 - ε) * Real.log n ^ 2 :=
    Nat.lt_ceil.mp (mem_range.mp hpB)
  exact lt_of_le_of_lt (by exact_mod_cast hpQ) hpR

end Proof

end OMA.R_Erdos457_erdos_457_variants_one_sub_R1
