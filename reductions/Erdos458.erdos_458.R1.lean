import FormalConjectures.ErdosProblems.«458»
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Prime.Nth

/-!
The quotient of the two least common multiples counts one base prime
for every prime power in the gap. In logarithms this is a von Mangoldt sum.
For lower endpoints at least 32, a gap whose support fits inside one
square-or-higher power and one cube-or-higher power below twice the
endpoint satisfies the bound automatically.
-/

namespace OMA.R_Erdos458_erdos_458_R1

open Finset ArithmeticFunction

def H1 : Prop :=
  ∀ a b : ℕ, a ≤ b →
    Real.log (Erdos458.lcm_upto b : ℝ) - Real.log (Erdos458.lcm_upto a : ℝ) =
      ∑ n ∈ Ioc a b, vonMangoldt n

def H2 : Prop :=
  ∀ k : ℕ,
    let a := k.nth (_root_.Prime : ℕ → Prop)
    let b := (k + 1).nth (_root_.Prime : ℕ → Prop) - 1
    (¬ (32 ≤ a ∧ ∃ r s u v : ℕ, r.Prime ∧ s.Prime ∧ 2 ≤ u ∧ 3 ≤ v ∧
      r ^ u < 2 * a ∧ s ^ v < 2 * a ∧
      ∀ n ∈ Ioc a b, IsPrimePow n → n = r ^ u ∨ n = s ^ v)) →
    (∑ n ∈ Ioc a b, vonMangoldt n) < Real.log (a : ℝ)

section Proof


private theorem two_powers_product_lt (a r s u v : ℕ)
    (ha : 32 ≤ a) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (hu : 2 ≤ u) (hv : 3 ≤ v) (hru : r ^ u < 2 * a) (hsv : s ^ v < 2 * a) :
    r * s < a := by
  have hr2 : r ^ 2 < 2 * a := (Nat.pow_le_pow_right hr hu).trans_lt hru
  have hs3 : s ^ 3 < 2 * a := (Nat.pow_le_pow_right hs hv).trans_lt hsv
  have hr6 : r ^ 6 < (2 * a) ^ 3 := by
    rw [show (6 : ℕ) = 2 * 3 by decide, pow_mul]
    exact Nat.pow_lt_pow_left hr2 (by decide)
  have hs6 : s ^ 6 < (2 * a) ^ 2 := by
    rw [show (6 : ℕ) = 3 * 2 by decide, pow_mul]
    exact Nat.pow_lt_pow_left hs3 (by decide)
  have hmul := Nat.mul_lt_mul_of_lt_of_lt hr6 hs6
  have htop : (2 * a) ^ 3 * (2 * a) ^ 2 ≤ a ^ 6 := by
    have h := Nat.mul_le_mul_right (a ^ 5) ha
    convert h using 1 <;> ring
  have hpow : (r * s) ^ 6 < a ^ 6 := by
    rw [mul_pow]
    exact hmul.trans_le htop
  apply lt_of_not_ge
  intro h
  exact (not_lt_of_ge (Nat.pow_le_pow_left h 6)) hpow

private theorem sum_for_two_powers (a b r s u v : ℕ)
    (ha : 32 ≤ a) (hr : r.Prime) (hs : s.Prime)
    (hu : 2 ≤ u) (hv : 3 ≤ v) (hru : r ^ u < 2 * a) (hsv : s ^ v < 2 * a)
    (hsupport : ∀ n ∈ Ioc a b, IsPrimePow n → n = r ^ u ∨ n = s ^ v) :
    (∑ n ∈ Ioc a b, vonMangoldt n) < Real.log (a : ℝ) := by
  let S := (Ioc a b).filter (fun n => n = r ^ u ∨ n = s ^ v)
  have hsum : (∑ n ∈ S, vonMangoldt n) = ∑ n ∈ Ioc a b, vonMangoldt n := by
    apply sum_subset (filter_subset _ _)
    intro n hn hnS
    apply vonMangoldt_eq_zero_iff.mpr
    exact fun hp => hnS (mem_filter.mpr ⟨hn, hsupport n hn hp⟩)
  have hsub : S ⊆ ({r ^ u, s ^ v} : Finset ℕ) := by
    intro n hn
    simpa only [mem_insert, mem_singleton] using (mem_filter.mp hn).2
  have hPairBound : (∑ n ∈ ({r ^ u, s ^ v} : Finset ℕ), vonMangoldt n) ≤
      Real.log r + Real.log s := by
    have hrlog : 0 ≤ Real.log (r : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hr.one_lt.le)
    have hevalR : vonMangoldt (r ^ u) = Real.log r := by
      rw [vonMangoldt_apply_pow (by omega : u ≠ 0), vonMangoldt_apply_prime hr]
    have hevalS : vonMangoldt (s ^ v) = Real.log s := by
      rw [vonMangoldt_apply_pow (by omega : v ≠ 0), vonMangoldt_apply_prime hs]
    by_cases heq : r ^ u = s ^ v
    · have hset : ({r ^ u, s ^ v} : Finset ℕ) = {s ^ v} := by simp [heq]
      rw [hset, sum_singleton, hevalS]
      linarith
    · rw [sum_pair heq, hevalR, hevalS]
  have hprod := two_powers_product_lt a r s u v ha hr.one_lt.le hs.one_lt.le hu hv hru hsv
  have hlog : Real.log (r : ℝ) + Real.log (s : ℝ) < Real.log (a : ℝ) := by
    rw [← Real.log_mul (by exact_mod_cast hr.ne_zero) (by exact_mod_cast hs.ne_zero)]
    exact Real.log_lt_log (by exact_mod_cast Nat.mul_pos hr.pos hs.pos) (by exact_mod_cast hprod)
  rw [← hsum]
  exact (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => vonMangoldt_nonneg)).trans_lt
    (hPairBound.trans_lt hlog)

theorem main : H1 → H2 → type_of% @Erdos458.erdos_458 := by
  intro intervalLog gapBound k
  let a := k.nth (_root_.Prime : ℕ → Prop)
  let b := (k + 1).nth (_root_.Prime : ℕ → Prop) - 1
  have hPrimeSet : Set.ofPred (_root_.Prime : ℕ → Prop) = Set.ofPred Nat.Prime := by
    ext p
    exact Nat.prime_iff.symm
  have hinf : (Set.ofPred (_root_.Prime : ℕ → Prop)).Infinite := by
    rw [hPrimeSet]
    exact Nat.infinite_setOfPred_prime
  have ha : _root_.Prime a := Nat.nth_mem_of_infinite hinf k
  have hasucc : a < (k + 1).nth (_root_.Prime : ℕ → Prop) :=
    (Nat.nth_strictMono hinf) (Nat.lt_succ_self k)
  have hab : a ≤ b := Nat.le_sub_one_of_lt hasucc
  have haR : 0 < (a : ℝ) := by exact_mod_cast (Nat.prime_iff.mpr ha).pos
  have haL : 0 < (Erdos458.lcm_upto a : ℝ) := by
    exact_mod_cast Nat.lcmUpto_pos a
  have hbL : 0 < (Erdos458.lcm_upto b : ℝ) := by
    exact_mod_cast Nat.lcmUpto_pos b
  have hgap : (∑ n ∈ Ioc a b, vonMangoldt n) < Real.log (a : ℝ) := by
    by_cases hEasy : 32 ≤ a ∧ ∃ r s u v : ℕ, r.Prime ∧ s.Prime ∧ 2 ≤ u ∧ 3 ≤ v ∧
        r ^ u < 2 * a ∧ s ^ v < 2 * a ∧
        ∀ n ∈ Ioc a b, IsPrimePow n → n = r ^ u ∨ n = s ^ v
    · obtain ⟨ha32, r, s, u, v, hr, hs, hu, hv, hru, hsv, hsupport⟩ := hEasy
      exact sum_for_two_powers a b r s u v ha32 hr hs hu hv hru hsv hsupport
    · exact gapBound k hEasy
  have hEq := intervalLog a b hab
  have hreal : (Erdos458.lcm_upto b : ℝ) <
      ((a * Erdos458.lcm_upto a : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    apply (Real.log_lt_log_iff hbL (mul_pos haR haL)).mp
    rw [Real.log_mul haR.ne' haL.ne']
    linarith
  exact_mod_cast hreal

end Proof

end OMA.R_Erdos458_erdos_458_R1
