import FormalConjectures.OEIS.«56777»
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Nat.Prime.Basic

/-!
# Reduction of OEIS A056777 by prime factors counted with multiplicity

The target is the converse of the construction in Conjecture 1.1 of
[Choudhury and Wei](https://arxiv.org/abs/2606.10331). Their Theorem 2.2 treats
pairs of squarefree semiprimes. [Earlier Lean work](https://github.com/Kuberwastaken/c5-k4)
also covers the small-excess classification used in the semiprime step.

A possible counterexample has at least three prime factors counted with multiplicity
at both endpoints, and some prime repeats at one of them. The equalities exclude
three-versus-three, three-versus-four, and four-versus-four. The last three-versus-four case
is reduced to an exact discriminant certificate for the elementary symmetric
functions of two primes. The four-versus-four proof first removes the cube-times-prime
shapes. Odd survivors have totients divisible by eight. For even survivors divisible
by four, the divisor sums are divisible by seven. Removing a single factor of two
from the other even cases gives odd three-factor cores with shifted jump equations.

H1 leaves both multiplicity counts at least four, with at least one at least five. H2 leaves exactly three
at one endpoint and at least five at the other. Each residual hypothesis also
records the necessary bounds on the numbers of odd primes with odd exponents.
-/

namespace OMA.R_OeisA56777_comesFromPrimeQuadruple_of_a_R2

section
open scoped ArithmeticFunction.sigma
open Nat Finset ArithmeticFunction

namespace A056777Closure

private theorem sigma_prime {p : ℕ} (hp : p.Prime) : σ 1 p = p + 1 := by
  simpa using sigma_one_apply_prime_pow (i := 1) hp

private theorem le_sigma (n : ℕ) (hn : 1 < n) : n + 1 ≤ σ 1 n := by
  rw [sigma_one_apply]
  calc
    n + 1 = ∑ d ∈ ({n, 1} : Finset ℕ), d := by simp [show n ≠ 1 by omega]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> exact Nat.mem_divisors.mpr ⟨by simp, by omega⟩) (by omega)

private theorem lt_sigma_of_not_prime (n : ℕ) (hn : 1 < n) (hp : ¬n.Prime) :
    n + 2 < σ 1 n := by
  obtain ⟨p, hprime, hdiv⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
  have hne : p ≠ n := fun h => hp (h ▸ hprime)
  have hp1 := hprime.one_lt
  have : n + p + 1 ≤ σ 1 n := by
    rw [sigma_one_apply]
    calc
      n + p + 1 = ∑ d ∈ ({n, p, 1} : Finset ℕ), d := by
        simp [show n ≠ 1 by omega, show n ≠ p by omega, hprime.ne_one, add_assoc]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
        (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl <;>
              exact Nat.mem_divisors.mpr ⟨by first | exact hdiv | simp, by omega⟩) (by omega)
  omega

/-- The excess of the sum of the divisor sum and the totient for a prime power. -/
private theorem prime_pow_excess (p k : ℕ) (hp : p.Prime) :
    σ 1 (p ^ (k + 2)) + (p ^ (k + 2)).totient =
      2 * p ^ (k + 2) + ∑ j ∈ Finset.range (k + 1), p ^ j := by
  rw [sigma_one_apply_prime_pow hp, totient_prime_pow_succ hp,
    Finset.sum_range_succ, Finset.sum_range_succ, pow_succ p (k + 1)]
  have h : p - 1 + 1 = p := by have := hp.one_lt; omega
  have hh := congrArg (fun x : ℕ => p ^ (k + 1) * x) h
  simp only [Nat.mul_add, mul_one] at hh
  omega

/-- The divisor sum and totient together are at least twice the argument. -/
private theorem le_sigma_add_totient (n : ℕ) : 2 * n ≤ σ 1 n + n.totient := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one => simp
  | prime_pow p k hp hk =>
    rcases k with _ | _ | k
    · omega
    · rw [show 0 + 1 = 1 by rfl, pow_one]
      rw [sigma_prime hp, totient_prime hp]
      have := hp.one_lt
      omega
    · change 2 * p ^ (k + 2) ≤ σ 1 (p ^ (k + 2)) + (p ^ (k + 2)).totient
      rw [prime_pow_excess p k hp]
      omega
  | coprime a b ha hb hc iha ihb =>
    have hsa := le_sigma a ha
    have hsb := le_sigma b hb
    have hta := Nat.totient_lt a ha
    have htb := Nat.totient_lt b hb
    rw [isMultiplicative_sigma.map_mul_of_coprime hc, Nat.totient_mul hc]
    have hprod := Nat.mul_le_mul iha ihb
    have hdiff := mul_nonneg
      (show 0 ≤ (σ 1 a : ℤ) - a.totient by omega)
      (show 0 ≤ (σ 1 b : ℤ) - b.totient by omega)
    zify at hprod ⊢
    nlinarith

/-- A positive integer has excess two precisely when it is a product of distinct primes. -/
theorem excess_two_iff (n : ℕ) :
    σ 1 n + n.totient = 2 * n + 2 ↔
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n = p * q := by
  constructor
  · intro h
    induction n using Nat.recOnPosPrimePosCoprime with
    | zero => simp at h
    | one => simp at h
    | prime_pow p k hp hk =>
      rcases k with _ | _ | _ | k
      · omega
      · rw [show 0 + 1 = 1 by rfl, pow_one] at h
        rw [sigma_prime hp, totient_prime hp] at h
        have := hp.one_lt
        omega
      · rw [prime_pow_excess p 0 hp] at h
        simp at h
      · change σ 1 (p ^ ((k + 1) + 2)) + (p ^ ((k + 1) + 2)).totient =
          2 * p ^ ((k + 1) + 2) + 2 at h
        rw [prime_pow_excess p (k + 1) hp] at h
        have hs : 1 + p ≤ ∑ j ∈ Finset.range (k + 1 + 1), p ^ j := by
          calc
            1 + p = ∑ j ∈ Finset.range 2, p ^ j := by simp [Finset.sum_range_succ]
            _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.range_subset_range.mpr (by omega)) (by omega)
        have := hp.one_lt
        omega
    | coprime a b ha hb hc _ _ =>
      have hsa := le_sigma a ha
      have hsb := le_sigma b hb
      have hta := Nat.totient_lt a ha
      have htb := Nat.totient_lt b hb
      rw [isMultiplicative_sigma.map_mul_of_coprime hc, Nat.totient_mul hc] at h
      have hprod := Nat.mul_le_mul (le_sigma_add_totient a) (le_sigma_add_totient b)
      zify at h hprod
      have hforce (x y : ℕ) (hx : ¬x.Prime) (hx1 : 1 < x) (hy1 : 1 < y) :
          8 ≤ ((σ 1 x : ℤ) - x.totient) * ((σ 1 y : ℤ) - y.totient) := by
        have hsx := lt_sigma_of_not_prime x hx1 hx
        have hsy := le_sigma y hy1
        have htx := Nat.totient_lt x hx1
        have hty := Nat.totient_lt y hy1
        exact mul_le_mul (show (4 : ℤ) ≤ σ 1 x - (x.totient : ℤ) by omega)
          (show (2 : ℤ) ≤ σ 1 y - (y.totient : ℤ) by omega) (by decide) (by omega)
      have hpa : a.Prime := by
        by_contra hn
        linarith only [h, hprod, hforce a b hn ha hb]
      have hpb : b.Prime := by
        by_contra hn
        have he := hforce b a hn hb ha
        rw [mul_comm] at he
        linarith only [h, hprod, he]
      exact ⟨a, b, hpa, hpb, ((Nat.coprime_primes hpa hpb).mp hc), rfl⟩
  · rintro ⟨p, q, hp, hq, hne, rfl⟩
    have hc := (Nat.coprime_primes hp hq).mpr hne
    rw [isMultiplicative_sigma.map_mul_of_coprime hc, Nat.totient_mul hc,
      sigma_prime hp, sigma_prime hq, Nat.totient_prime hp, Nat.totient_prime hq]
    zify [hp.pos, hq.pos]
    ring


/-- Excess one classifies squares of primes. -/
theorem excess_one_iff (n : ℕ) :
    σ 1 n + n.totient = 2 * n + 1 ↔ ∃ p : ℕ, p.Prime ∧ n = p ^ 2 := by
  constructor
  · intro h
    induction n using Nat.recOnPosPrimePosCoprime with
    | zero => simp at h
    | one => simp at h
    | prime_pow p k hp hk =>
      rcases k with _ | _ | _ | k
      · omega
      · rw [show 0 + 1 = 1 by rfl, pow_one, sigma_prime hp, totient_prime hp] at h
        have := hp.one_lt
        omega
      · exact ⟨p, hp, rfl⟩
      · change σ 1 (p ^ ((k + 1) + 2)) + (p ^ ((k + 1) + 2)).totient =
          2 * p ^ ((k + 1) + 2) + 1 at h
        rw [prime_pow_excess p (k + 1) hp] at h
        have hs : 1 + p ≤ ∑ j ∈ Finset.range (k + 1 + 1), p ^ j := by
          calc
            1 + p = ∑ j ∈ Finset.range 2, p ^ j := by simp [Finset.sum_range_succ]
            _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.range_subset_range.mpr (by omega)) (by omega)
        have := hp.one_lt
        omega
    | coprime a b ha hb hc _ _ =>
      rw [isMultiplicative_sigma.map_mul_of_coprime hc, Nat.totient_mul hc] at h
      have hprod := Nat.mul_le_mul (le_sigma_add_totient a) (le_sigma_add_totient b)
      zify at h hprod
      have hsa := le_sigma a ha
      have hsb := le_sigma b hb
      have hta := Nat.totient_lt a ha
      have htb := Nat.totient_lt b hb
      have hdiff : 4 ≤ ((σ 1 a : ℤ) - a.totient) * ((σ 1 b : ℤ) - b.totient) :=
        mul_le_mul (show (2 : ℤ) ≤ σ 1 a - (a.totient : ℤ) by omega)
          (show (2 : ℤ) ≤ σ 1 b - (b.totient : ℤ) by omega) (by decide) (by omega)
      linarith only [h, hprod, hdiff]
  · rintro ⟨p, hp, rfl⟩
    simpa using prime_pow_excess p 0 hp

private theorem no_prime_squares_at_distance_twelve {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : p ^ 2 + 12 = q ^ 2) : False := by
  have hp2 := hp.two_le
  have hpq : p < q := by
    by_contra! hle
    have := Nat.mul_le_mul hle hle
    rw [pow_two, pow_two] at h
    omega
  by_cases heq : q = p + 1
  · rw [heq] at h
    have hh : 2 * p + 1 = 12 := by nlinarith
    omega
  · have hle : p + 2 ≤ q := by omega
    have hsq := Nat.mul_le_mul hle hle
    have hp_le : p ≤ 2 := by nlinarith
    have hq_le : q ≤ 4 := by
      have hp_eq : p = 2 := by omega
      rw [hp_eq] at h
      by_contra! H
      have hh := Nat.mul_le_mul H H
      norm_num at h
      nlinarith
    have hq_eq : q = 4 := by omega
    exact (by decide : ¬Nat.Prime 4) (hq_eq ▸ hq)

private theorem ordered_factors {n : ℕ}
    (h : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n = p * q) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ n = p * q := by
  obtain ⟨p, q, hp, hq, hne, hn⟩ := h
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨p, q, hp, hq, h, hn⟩
  · exact ⟨q, p, hq, hp, h, by simpa [mul_comm] using hn⟩

private theorem sum_eq_of_totient {n p q r s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p < q) (hrs : r < s) (hn : n = p * q) (hm : n + 12 = r * s)
    (ht : (n + 12).totient = n.totient + 12) :
    p + q = r + s := by
  rw [hm, hn, Nat.totient_mul ((Nat.coprime_primes hr hs).mpr hrs.ne),
    Nat.totient_mul ((Nat.coprime_primes hp hq).mpr hpq.ne),
    Nat.totient_prime hp, Nat.totient_prime hq, Nat.totient_prime hr, Nat.totient_prime hs] at ht
  zify [hp.pos, hq.pos, hr.pos, hs.pos] at hn hm ht ⊢
  linarith

/-- If either argument has excess two, the simultaneous totient and divisor-sum
increments by twelve force the pair to come from a prime quadruple. -/
theorem prime_quadruple_of_one_excess_two {n : ℕ}
    (ht : (n + 12).totient = n.totient + 12)
    (hs : σ 1 (n + 12) = σ 1 n + 12)
    (he : σ 1 n + n.totient = 2 * n + 2 ∨
      σ 1 (n + 12) + (n + 12).totient = 2 * (n + 12) + 2) :
    ∃ p : ℕ, p.Prime ∧ (p + 2).Prime ∧ (p + 6).Prime ∧ (p + 8).Prime ∧ n = p * (p + 8) := by
  have he₁ : σ 1 n + n.totient = 2 * n + 2 := by omega
  have he₂ : σ 1 (n + 12) + (n + 12).totient = 2 * (n + 12) + 2 := by omega
  obtain ⟨p, q, hp, hq, hpq, hn⟩ := ordered_factors ((excess_two_iff n).mp he₁)
  obtain ⟨r, s, hr, hs', hrs, hm⟩ := ordered_factors ((excess_two_iff (n + 12)).mp he₂)
  have hsum := sum_eq_of_totient hp hq hr hs' hpq hrs hn hm ht
  have hpr : p < r := by
    by_contra! h
    have hsr : (r : ℤ) ≤ s := by exact_mod_cast hrs.le
    have hrp : (r : ℤ) ≤ p := by exact_mod_cast h
    zify at hn hm hsum
    have H := mul_nonneg (show 0 ≤ (p : ℤ) - r by omega)
      (show 0 ≤ (q : ℤ) - r by omega)
    linarith only [hn, hm, hsum, H, show
      (p : ℤ) * q - r * s = ((p : ℤ) - r) * (q - r) from by
        linear_combination (r : ℤ) * hsum]
  have hq2 : q % 2 = 1 := hq.eq_two_or_odd.resolve_left (by
    have := hp.two_le
    omega)
  have hr2 : r % 2 = 1 := hr.eq_two_or_odd.resolve_left (by
    have := hp.two_le
    omega)
  have hs2 : s % 2 = 1 := hs'.eq_two_or_odd.resolve_left (by
    have := hr.two_le
    omega)
  have hp2 : p % 2 = 1 := by omega
  let d := r - p
  let e := q - r
  have hd : 0 < d := by dsimp [d]; omega
  have hde : d ≤ e := by dsimp [d, e]; omega
  have hdp : d % 2 = 0 := by dsimp [d]; omega
  have hprod : d * e = 12 := by
    have hd' : d + p = r := by dsimp [d]; omega
    have he' : e + r = q := by dsimp [e]; omega
    have hs'' : s = p + e := by omega
    rw [← hd'] at he'
    rw [← hd', hs''] at hm
    rw [← he'] at hn
    nlinarith only [hn, hm]
  have hd4 : d < 4 := by
    by_contra! hd4
    have hm16 : 4 * 4 ≤ d * e := Nat.mul_le_mul hd4 (hd4.trans hde)
    omega
  have hd2 : d = 2 := by omega
  have he6 : e = 6 := by rw [hd2] at hprod; omega
  have hrp : r = p + 2 := by dsimp [d] at hd2; omega
  have hsp : s = p + 6 := by dsimp [e] at he6; omega
  have hqp : q = p + 8 := by dsimp [e] at he6; omega
  refine ⟨p, hp, hrp ▸ hr, hsp ▸ hs', hqp ▸ hq, ?_⟩
  simpa [hqp] using hn

/-- The prime-quadruple conjecture holds whenever either member of the pair
is semiprime, including the case of a square of a prime. -/
theorem prime_quadruple_of_one_semiprime {n : ℕ}
    (ht : (n + 12).totient = n.totient + 12)
    (hs : σ 1 (n + 12) = σ 1 n + 12)
    (hp : (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p * q) ∨
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n + 12 = p * q) :
    ∃ p : ℕ, p.Prime ∧ (p + 2).Prime ∧ (p + 6).Prime ∧ (p + 8).Prime ∧ n = p * (p + 8) := by
  rcases hp with ⟨p, q, hp, hq, hn⟩ | ⟨p, q, hp, hq, hn⟩
  · by_cases h : p = q
    · subst q
      have he := (excess_one_iff n).mpr ⟨p, hp, by simpa [pow_two] using hn⟩
      obtain ⟨q, hq, hm⟩ := (excess_one_iff (n + 12)).mp (by omega)
      exact (no_prime_squares_at_distance_twelve hp hq (by simp_all [pow_two])).elim
    · exact prime_quadruple_of_one_excess_two ht hs
        (Or.inl ((excess_two_iff n).mpr ⟨p, q, hp, hq, h, hn⟩))
  · by_cases h : p = q
    · subst q
      have he := (excess_one_iff (n + 12)).mpr ⟨p, hp, by simpa [pow_two] using hn⟩
      obtain ⟨q, hq, hm⟩ := (excess_one_iff n).mp (by omega)
      exact (no_prime_squares_at_distance_twelve hq hp (by simp_all [pow_two])).elim
    · exact prime_quadruple_of_one_excess_two ht hs
        (Or.inr ((excess_two_iff (n + 12)).mpr ⟨p, q, hp, hq, h, hn⟩))

theorem factor_count_of_nonsemiprime {n : ℕ} (hn : 1 < n) (hp : ¬n.Prime)
    (hs : ¬∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p * q) :
    3 ≤ n.primeFactorsList.length := by
  have hprod := Nat.prod_primeFactorsList (n := n) (by omega)
  have hprime {p : ℕ} (hm : p ∈ n.primeFactorsList) := Nat.prime_of_mem_primeFactorsList hm
  cases h : n.primeFactorsList with
  | nil => simp [h] at hprod; omega
  | cons p tail =>
    cases tail with
    | nil =>
      have hp' := hprime (p := p) (by simp [h])
      simp [h] at hprod
      exact (hp (hprod ▸ hp')).elim
    | cons q tail =>
      cases tail with
      | nil =>
        exact (hs ⟨p, q, hprime (by simp [h]), hprime (by simp [h]),
          by simpa [h] using hprod.symm⟩).elim
      | cons r tail => simp

/-- A counterexample to the converse for A056777 must have at least three
prime factors, counted with multiplicity, in both positions. -/
theorem factor_count_of_counterexample {n : ℕ} (hn : 1 < n) (hp : ¬n.Prime)
    (ht : (n + 12).totient = n.totient + 12)
    (hs : σ 1 (n + 12) = σ 1 n + 12)
    (hc : ¬∃ p : ℕ, p.Prime ∧ (p + 2).Prime ∧ (p + 6).Prime ∧
      (p + 8).Prime ∧ n = p * (p + 8)) :
    3 ≤ n.primeFactorsList.length ∧ 3 ≤ (n + 12).primeFactorsList.length := by
  have hm : ¬(n + 12).Prime := by
    intro hm
    rw [sigma_prime hm] at hs
    have := lt_sigma_of_not_prime n hn hp
    omega
  exact ⟨factor_count_of_nonsemiprime hn hp
      (fun h => hc (prime_quadruple_of_one_semiprime ht hs (Or.inl h))),
    factor_count_of_nonsemiprime (by omega) hm
      (fun h => hc (prime_quadruple_of_one_semiprime ht hs (Or.inr h)))⟩

/-- The low values of the excess for an odd squarefree number are zero and two. -/
theorem low_excess_of_odd_squarefree (n : ℕ) (ho : Odd n) (hs : Squarefree n) :
    σ 1 n + n.totient = 2 * n ∨ σ 1 n + n.totient = 2 * n + 2 ∨
      2 * n + 10 ≤ σ 1 n + n.totient := by
  suffices h : n = 1 ∨ n.Prime ∨ σ 1 n + n.totient = 2 * n + 2 ∨
      2 * n + 10 ≤ σ 1 n + n.totient by
    rcases h with rfl | hp | h | h
    · left; simp
    · left
      rw [sigma_prime hp, Nat.totient_prime hp]
      have := hp.one_lt
      omega
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp at ho
  | one => exact Or.inl rfl
  | prime_pow p k hp hk =>
    have h := hs.natFactorization_le_one p
    rw [hp.factorization_pow, Finsupp.single_eq_same] at h
    have h1 : k = 1 := by omega
    subst k
    exact Or.inr (Or.inl (by simpa using hp))
  | coprime a b ha hb hc iha ihb =>
    obtain ⟨hoa, hob⟩ := Nat.odd_mul.mp ho
    have hsa := hs.squarefree_of_dvd (dvd_mul_right a b)
    have hsb := hs.squarefree_of_dvd (dvd_mul_left b a)
    by_cases hab : a.Prime ∧ b.Prime
    · exact Or.inr (Or.inr (Or.inl ((excess_two_iff _).mpr
        ⟨a, b, hab.1, hab.2, (Nat.coprime_primes hab.1 hab.2).mp hc, rfl⟩)))
    · have hhelper (x y : ℕ) (hx : 1 < x) (hy : 1 < y) (hyod : Odd y)
          (hcop : x.Coprime y) (hnp : ¬x.Prime)
          (hi : x = 1 ∨ x.Prime ∨ σ 1 x + x.totient = 2 * x + 2 ∨
            2 * x + 10 ≤ σ 1 x + x.totient) :
          2 * (x * y) + 10 ≤ σ 1 (x * y) + (x * y).totient := by
        have hDx : 2 * x + 2 ≤ σ 1 x + x.totient := by
          rcases hi with h | h | h | h
          · omega
          · exact (hnp h).elim
          · omega
          · omega
        have hDy := le_sigma_add_totient y
        have hy3 : 3 ≤ y := by have := Nat.odd_iff.mp hyod; omega
        have hprod := Nat.mul_le_mul hDx hDy
        have hσx := lt_sigma_of_not_prime x hx hnp
        have hσy := le_sigma y hy
        have htx := Nat.totient_lt x hx
        have hty := Nat.totient_lt y hy
        have hdiff : 8 ≤ ((σ 1 x : ℤ) - x.totient) * ((σ 1 y : ℤ) - y.totient) :=
          mul_le_mul (show (4 : ℤ) ≤ σ 1 x - (x.totient : ℤ) by omega)
            (show (2 : ℤ) ≤ σ 1 y - (y.totient : ℤ) by omega) (by decide) (by omega)
        rw [isMultiplicative_sigma.map_mul_of_coprime hcop, Nat.totient_mul hcop]
        zify at hprod hy3 ⊢
        linarith only [hprod, hy3, hdiff]
      refine Or.inr (Or.inr (Or.inr ?_))
      by_cases hap : a.Prime
      · have hbp : ¬b.Prime := fun hp => hab ⟨hap, hp⟩
        simpa [mul_comm] using hhelper b a hb ha hoa hc.symm hbp (ihb hob hsb)
      · exact hhelper a b ha hb hob hc hap (iha hoa hsa)

end A056777Closure
end

section
open scoped ArithmeticFunction.sigma
open Nat Finset ArithmeticFunction

namespace A056777Parity

theorem geom_odd_mod_two {p : ℕ} (hp : p % 2 = 1) (k : ℕ) :
    (∑ i ∈ Finset.range k, p ^ i) % 2 = k % 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih, Nat.pow_mod, hp]
    simp [Nat.add_mod]

private theorem prime_pow_square_shape {p k : ℕ} (hp : p.Prime)
    (h : Odd (σ 1 (p ^ k))) :
    (∃ a : ℕ, p ^ k = a ^ 2) ∨ ∃ a : ℕ, p ^ k = 2 * a ^ 2 := by
  rcases hp.eq_two_or_odd with rfl | hpodd
  · by_cases hk : k % 2 = 0
    · left
      exact ⟨2 ^ (k / 2), by rw [← pow_mul, show k / 2 * 2 = k by omega]⟩
    · right
      exact ⟨2 ^ (k / 2), by rw [← pow_mul, ← pow_succ', show (k / 2 * 2).succ = k by omega]⟩
  · have ho := Nat.odd_iff.mp h
    rw [sigma_one_apply_prime_pow hp, geom_odd_mod_two hpodd] at ho
    left
    exact ⟨p ^ (k / 2), by rw [← pow_mul, show k / 2 * 2 = k by omega]⟩

/-- Odd divisor sums occur only for squares and twice squares. -/
theorem square_or_twice_square {n : ℕ} (h : Odd (σ 1 n)) :
    (∃ a : ℕ, n = a ^ 2) ∨ ∃ a : ℕ, n = 2 * a ^ 2 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => left; exact ⟨0, by decide⟩
  | one => left; exact ⟨1, by decide⟩
  | prime_pow p k hp hk => exact prime_pow_square_shape hp h
  | coprime a b ha hb hc iha ihb =>
    rw [isMultiplicative_sigma.map_mul_of_coprime hc, Nat.odd_mul] at h
    rcases iha h.1 with ⟨x, rfl⟩ | ⟨x, rfl⟩ <;>
      rcases ihb h.2 with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact Or.inl ⟨x * y, by ring⟩
    · exact Or.inr ⟨x * y, by ring⟩
    · exact Or.inr ⟨x * y, by ring⟩
    · have := Nat.dvd_gcd (dvd_mul_right 2 (x ^ 2)) (dvd_mul_right 2 (y ^ 2))
      rw [hc.gcd_eq_one] at this
      omega

private theorem geom_two_mod_two (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1), (2 : ℕ) ^ i) % 2 = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih, pow_succ', Nat.mul_mod]
    simp

private theorem odd_sigma_of_even_odd_prime_exponents (n : ℕ) (hn : n ≠ 0)
    (hf : ∀ p, p.Prime → p ≠ 2 → Even (n.factorization p)) :
    Odd (σ 1 n) := by
  rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn]
  simp only [Nat.mul_one]
  suffices h : ∀ s : Finset ℕ, s ⊆ n.primeFactors →
      Odd (∏ p ∈ s, ∑ i ∈ Finset.range (n.factorization p + 1), p ^ i) by
    exact h _ Subset.rfl
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    intro hsub
    have hprime := Nat.prime_of_mem_primeFactors (hsub (Finset.mem_insert_self p s))
    rw [Finset.prod_insert hp, Nat.odd_mul]
    refine ⟨?_, ih (fun q hq => hsub (Finset.mem_insert_of_mem hq))⟩
    rw [Nat.odd_iff]
    rcases hprime.eq_two_or_odd with hp' | hp'
    · rw [hp', geom_two_mod_two]
    · have hne : p ≠ 2 := by omega
      obtain ⟨k, hk⟩ := hf p hprime hne
      rw [geom_odd_mod_two hp', hk]
      omega

/-- A positive number has odd divisor sum precisely when it is a square or twice a square. -/
theorem odd_sigma_iff_square_or_twice_square {n : ℕ} (hn : n ≠ 0) :
    Odd (σ 1 n) ↔ (∃ a : ℕ, n = a ^ 2) ∨ ∃ a : ℕ, n = 2 * a ^ 2 := by
  refine ⟨square_or_twice_square, ?_⟩
  intro h
  apply odd_sigma_of_even_odd_prime_exponents _ hn
  intro p _ hp
  rcases h with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    exact ⟨a.factorization p, by omega⟩
  · have ha : a ≠ 0 := by rintro rfl; simp at hn
    rw [Nat.factorization_mul (by decide) (pow_ne_zero _ ha),
      Nat.prime_two.factorization, Nat.factorization_pow,
      Finsupp.add_apply, Finsupp.single_eq_of_ne hp, Finsupp.smul_apply, smul_eq_mul, zero_add]
    exact ⟨a.factorization p, by omega⟩

private theorem sq_mod_four (a : ℕ) : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
  rw [Nat.pow_mod]
  have h := Nat.mod_lt a (by decide : 0 < 4)
  interval_cases (a % 4) <;> decide

private theorem sq_mod_eight (a : ℕ) : a ^ 2 % 8 = 0 ∨ a ^ 2 % 8 = 1 ∨ a ^ 2 % 8 = 4 := by
  rw [Nat.pow_mod]
  have h := Nat.mod_lt a (by decide : 0 < 8)
  interval_cases (a % 8) <;> decide

private theorem not_sq_add_twelve_eq_twice_sq (a b : ℕ) : a ^ 2 + 12 ≠ 2 * b ^ 2 := by
  intro h
  have ha : a % 2 = 0 := by
    have hh := congrArg (· % 4) h
    rw [Nat.add_mod, Nat.mul_mod, Nat.pow_mod a, Nat.pow_mod b] at hh
    have ha4 := Nat.mod_lt a (by decide : 0 < 4)
    have hb4 := Nat.mod_lt b (by decide : 0 < 4)
    have ha' : a % 2 = a % 4 % 2 := by omega
    rw [ha']
    interval_cases (a % 4) <;> interval_cases (b % 4) <;> (norm_num at hh) <;> decide
  have hb : b % 2 = 0 := by
    have hh := congrArg (· % 4) h
    rw [Nat.add_mod, Nat.mul_mod, Nat.pow_mod a, Nat.pow_mod b] at hh
    have ha4 := Nat.mod_lt a (by decide : 0 < 4)
    have hb4 := Nat.mod_lt b (by decide : 0 < 4)
    have hb' : b % 2 = b % 4 % 2 := by omega
    rw [hb']
    interval_cases (a % 4) <;> interval_cases (b % 4) <;> (norm_num at hh) <;> decide
  have ha' : a = 2 * (a / 2) := by omega
  have hb' : b = 2 * (b / 2) := by omega
  have H : (a / 2) ^ 2 + 3 = 2 * (b / 2) ^ 2 := by
    nlinarith only [h, congrArg (· ^ 2) ha', congrArg (· ^ 2) hb']
  have hh := congrArg (· % 8) H
  rw [Nat.add_mod, Nat.mul_mod] at hh
  rcases sq_mod_eight (a / 2) with A | A | A <;>
    rcases sq_mod_eight (b / 2) with B | B | B <;> norm_num [A, B] at hh

private theorem not_twice_sq_add_twelve_eq_sq (a b : ℕ) : 2 * a ^ 2 + 12 ≠ b ^ 2 := by
  intro h
  have ha : a % 2 = 0 := by
    have hh := congrArg (· % 4) h
    rw [Nat.add_mod, Nat.mul_mod, Nat.pow_mod a, Nat.pow_mod b] at hh
    have ha4 := Nat.mod_lt a (by decide : 0 < 4)
    have hb4 := Nat.mod_lt b (by decide : 0 < 4)
    have ha' : a % 2 = a % 4 % 2 := by omega
    rw [ha']
    interval_cases (a % 4) <;> interval_cases (b % 4) <;> (norm_num at hh) <;> decide
  have hb : b % 2 = 0 := by
    have hh := congrArg (· % 4) h
    rw [Nat.add_mod, Nat.mul_mod, Nat.pow_mod a, Nat.pow_mod b] at hh
    have ha4 := Nat.mod_lt a (by decide : 0 < 4)
    have hb4 := Nat.mod_lt b (by decide : 0 < 4)
    have hb' : b % 2 = b % 4 % 2 := by omega
    rw [hb']
    interval_cases (a % 4) <;> interval_cases (b % 4) <;> (norm_num at hh) <;> decide
  have ha' : a = 2 * (a / 2) := by omega
  have hb' : b = 2 * (b / 2) := by omega
  have H : 2 * (a / 2) ^ 2 + 3 = (b / 2) ^ 2 := by
    nlinarith only [h, congrArg (· ^ 2) ha', congrArg (· ^ 2) hb']
  have hh := congrArg (· % 8) H
  rw [Nat.add_mod, Nat.mul_mod] at hh
  rcases sq_mod_eight (a / 2) with A | A | A <;>
    rcases sq_mod_eight (b / 2) with B | B | B <;> norm_num [A, B] at hh

private theorem eq_two_of_sq_add_twelve_eq_sq (a b : ℕ) (h : a ^ 2 + 12 = b ^ 2) : a = 2 := by
  have hab : a < b := by
    by_contra! hab
    have hh := Nat.mul_le_mul hab hab
    rw [pow_two, pow_two] at h
    omega
  by_cases heq : b = a + 1
  · subst b
    have hh : 2 * a + 1 = 12 := by nlinarith
    omega
  · have hle : a + 2 ≤ b := by omega
    have hsq := Nat.mul_le_mul hle hle
    have ha2 : a ≤ 2 := by nlinarith
    interval_cases a
    · have hb : 3 < b := by
        by_contra! hh
        have := Nat.mul_le_mul hh hh
        nlinarith
      have := Nat.mul_le_mul (show 4 ≤ b by omega) (show 4 ≤ b by omega)
      nlinarith
    · have hb : 3 < b := by
        by_contra! hh
        have := Nat.mul_le_mul hh hh
        nlinarith
      have := Nat.mul_le_mul (show 4 ≤ b by omega) (show 4 ≤ b by omega)
      nlinarith
    · rfl

/-- Any pair satisfying the divisor-sum condition of A056777 has even divisor sums.
This excludes all square and twice-square endpoints with odd divisor sum. -/
theorem even_sigma_of_sigma_step {n : ℕ} (h : σ 1 (n + 12) = σ 1 n + 12) :
    Even (σ 1 n) ∧ Even (σ 1 (n + 12)) := by
  have he : Even (σ 1 n) := by
    by_contra hnot
    have h₁ : Odd (σ 1 n) := Nat.not_even_iff_odd.mp hnot
    have h₂ : Odd (σ 1 (n + 12)) := by rw [Nat.odd_iff, h]; have := Nat.odd_iff.mp h₁; omega
    rcases square_or_twice_square h₁ with ⟨a, ha⟩ | ⟨a, ha⟩ <;>
      rcases square_or_twice_square h₂ with ⟨b, hb⟩ | ⟨b, hb⟩
    · have : a = 2 := eq_two_of_sq_add_twelve_eq_sq a b (ha ▸ hb)
      subst a
      subst n
      revert h
      decide
    · exact not_sq_add_twelve_eq_twice_sq a b (ha ▸ hb)
    · exact not_twice_sq_add_twelve_eq_sq a b (ha ▸ hb)
    · have h' : a ^ 2 + 6 = b ^ 2 := by omega
      have hh := congrArg (· % 4) h'
      rw [Nat.add_mod] at hh
      rcases sq_mod_four a with A | A <;> rcases sq_mod_four b with B | B <;>
        norm_num [A, B] at hh
  exact ⟨he, by rw [h]; exact he.add (by decide)⟩

/-- The divisor-sum condition alone excludes squares and twice squares at both endpoints. -/
theorem no_square_shapes_of_sigma_step {n : ℕ} (hn : n ≠ 0)
    (h : σ 1 (n + 12) = σ 1 n + 12) :
    (¬ ((∃ a : ℕ, n = a ^ 2) ∨ ∃ a : ℕ, n = 2 * a ^ 2)) ∧
    (¬ ((∃ a : ℕ, n + 12 = a ^ 2) ∨ ∃ a : ℕ, n + 12 = 2 * a ^ 2)) := by
  rw [← odd_sigma_iff_square_or_twice_square hn,
      ← odd_sigma_iff_square_or_twice_square (show n + 12 ≠ 0 by omega)]
  obtain ⟨he₁, he₂⟩ := even_sigma_of_sigma_step h
  exact ⟨fun ho => (Nat.not_even_iff_odd.mpr ho) he₁,
    fun ho => (Nat.not_even_iff_odd.mpr ho) he₂⟩

/-- Both arguments have some odd prime occurring to an odd exponent. -/
theorem odd_prime_exponents_of_sigma_step {n : ℕ} (hn : n ≠ 0)
    (h : σ 1 (n + 12) = σ 1 n + 12) :
    (∃ p, p.Prime ∧ p ≠ 2 ∧ Odd (n.factorization p)) ∧
    (∃ p, p.Prime ∧ p ≠ 2 ∧ Odd ((n + 12).factorization p)) := by
  have hexists {m : ℕ} (hm : m ≠ 0) (he : Even (σ 1 m)) :
      ∃ p, p.Prime ∧ p ≠ 2 ∧ Odd (m.factorization p) := by
    by_contra! hall
    apply (Nat.not_even_iff_odd.mpr (odd_sigma_of_even_odd_prime_exponents m hm ?_)) he
    intro p hp hp2
    by_contra hn
    exact hall p hp hp2 (Nat.not_even_iff_odd.mp hn)
  obtain ⟨he₁, he₂⟩ := even_sigma_of_sigma_step h
  exact ⟨hexists hn he₁, hexists (by omega) he₂⟩

end A056777Parity
end

section
/-
# Odd squarefree pairs in the A056777 conjecture

The converse in [OEIS A056777](https://oeis.org/A056777) is Conjecture 1.1 of
[Choudhury and Wei](https://arxiv.org/abs/2606.10331). Their Theorem 2.2 covers
pairs of squarefree semiprimes. [Previous formal work](https://github.com/Kuberwastaken/c5-k4)
also covers the small-excess classification used in the one-sided semiprime step.
The divisor-sum shift by twelve forces one of the arguments to be semiprime
when both arguments are odd and squarefree.
-/

open scoped ArithmeticFunction.sigma
open Nat Finset ArithmeticFunction

namespace A056777Squarefree

/-- Each odd prime with odd exponent contributes at least one factor of two
to the divisor sum. -/
theorem two_pow_card_odd_exponents_dvd_sigma {n : ℕ} (hn : n ≠ 0) :
    2 ^ (n.primeFactors.filter fun p => p ≠ 2 ∧ Odd (n.factorization p)).card ∣ σ 1 n := by
  rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn]
  simp only [Nat.mul_one]
  let s := n.primeFactors.filter fun p => p ≠ 2 ∧ Odd (n.factorization p)
  let f (p : ℕ) := ∑ i ∈ Finset.range (n.factorization p + 1), p ^ i
  change 2 ^ s.card ∣ ∏ p ∈ n.primeFactors, f p
  have hsub : s ⊆ n.primeFactors := Finset.filter_subset _ _
  refine dvd_trans ?_ (Finset.prod_dvd_prod_of_subset s n.primeFactors f hsub)
  rw [← Finset.prod_const]
  apply Finset.prod_dvd_prod_of_dvd
  intro p hp
  have ⟨hmem, hp2, hexp⟩ := Finset.mem_filter.mp hp
  have hprime := Nat.prime_of_mem_primeFactors hmem
  have hodd := hprime.eq_two_or_odd.resolve_left hp2
  apply Nat.dvd_of_mod_eq_zero
  dsimp [f]
  rw [A056777Parity.geom_odd_mod_two hodd]
  have := Nat.odd_iff.mp hexp
  omega

/-- The divisor-sum step by twelve forces at least one endpoint to have
at most two odd primes occurring to odd exponents. -/
theorem at_most_two_odd_exponents_of_sigma_step {n : ℕ} (hn : n ≠ 0)
    (hs : σ 1 (n + 12) = σ 1 n + 12) :
    (n.primeFactors.filter fun p => p ≠ 2 ∧ Odd (n.factorization p)).card ≤ 2 ∨
    ((n + 12).primeFactors.filter fun p => p ≠ 2 ∧ Odd ((n + 12).factorization p)).card ≤ 2 := by
  by_contra! h
  have h₁ := dvd_trans (pow_dvd_pow 2 (show 3 ≤ _ from h.1))
    (two_pow_card_odd_exponents_dvd_sigma hn)
  have h₂ := dvd_trans (pow_dvd_pow 2 (show 3 ≤ _ from h.2))
    (two_pow_card_odd_exponents_dvd_sigma (show n + 12 ≠ 0 by omega))
  change 8 ∣ σ 1 n at h₁
  change 8 ∣ σ 1 (n + 12) at h₂
  omega

private theorem filter_eq_primeFactors {n : ℕ} (hs : Squarefree n) (ho : Odd n) :
    (n.primeFactors.filter fun p => p ≠ 2 ∧ Odd (n.factorization p)) = n.primeFactors := by
  apply Finset.filter_eq_self.mpr
  intro p hp
  have ⟨hprime, hdiv, hn⟩ := Nat.mem_primeFactors.mp hp
  have hp2 : p ≠ 2 := by
    rintro rfl
    have := Nat.odd_iff.mp ho
    omega
  have hpos := hprime.factorization_pos_of_dvd hn hdiv
  have hle := hs.natFactorization_le_one p
  have he : n.factorization p = 1 := by omega
  exact ⟨hp2, he ▸ (by decide : Odd 1)⟩

private theorem factor_count_eq_of_squarefree {n : ℕ} (hs : Squarefree n) :
    n.primeFactors.card = n.primeFactorsList.length := by
  rw [← Nat.toFinset_factors, List.toFinset_card_of_nodup hs.nodup_primeFactorsList]

/-- The A056777 pair comes from a prime quadruple if both endpoints are odd and squarefree. -/
theorem prime_quadruple_of_odd_squarefree_pair {n : ℕ}
    (hn : 1 < n) (hnp : ¬n.Prime) (ho : Odd n)
    (h₁ : Squarefree n) (h₂ : Squarefree (n + 12))
    (ht : (n + 12).totient = n.totient + 12)
    (hs : σ 1 (n + 12) = σ 1 n + 12) :
    ∃ p : ℕ, p.Prime ∧ (p + 2).Prime ∧ (p + 6).Prime ∧ (p + 8).Prime ∧ n = p * (p + 8) := by
  by_contra h
  obtain ⟨hc₁, hc₂⟩ := A056777Closure.factor_count_of_counterexample hn hnp ht hs h
  have ho' : Odd (n + 12) := by
    rw [Nat.odd_iff]
    have := Nat.odd_iff.mp ho
    omega
  have hcount := at_most_two_odd_exponents_of_sigma_step (show n ≠ 0 by omega) hs
  rw [filter_eq_primeFactors h₁ ho, filter_eq_primeFactors h₂ ho',
    factor_count_eq_of_squarefree h₁, factor_count_eq_of_squarefree h₂] at hcount
  omega

private theorem dvd_eight_sigma_of_card_ge_three {n : ℕ} (hn : Squarefree n) (ho : Odd n)
    (hc : 3 ≤ n.primeFactors.card) : 8 ∣ σ 1 n := by
  have h := two_pow_card_odd_exponents_dvd_sigma (n := n) hn.ne_zero
  rw [filter_eq_primeFactors hn ho] at h
  exact (pow_dvd_pow 2 hc).trans h

private theorem low_excess_of_card_le_two {n : ℕ} (hn : Squarefree n)
    (hc : n.primeFactors.card ≤ 2) :
    σ 1 n + n.totient = 2 * n ∨ σ 1 n + n.totient = 2 * n + 2 := by
  by_cases hn1 : n = 1
  · subst n
    simp
  by_cases hp : n.Prime
  · left
    have hσ : σ 1 n = n + 1 := by simpa using sigma_one_apply_prime_pow (i := 1) hp
    rw [hσ, Nat.totient_prime hp]
    have := hp.one_lt
    omega
  · right
    have hnn : 1 < n := by have := hn.ne_zero; omega
    have hh (h : ¬∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p * q) : False := by
      have hlen := A056777Closure.factor_count_of_nonsemiprime hnn hp h
      rw [← factor_count_eq_of_squarefree hn] at hlen
      omega
    obtain ⟨p, q, hpp, hq, rfl⟩ := not_not.mp (fun h => hh h)
    have hne : p ≠ q := by
      rintro rfl
      exact (Nat.squarefree_iff_prime_squarefree.mp hn p hpp) (dvd_refl _)
    exact (A056777Closure.excess_two_iff _).mpr ⟨p, q, hpp, hq, hne, rfl⟩

/-- The A056777 conditions are incompatible with both endpoints being even and squarefree. -/
theorem no_even_squarefree_pair {n : ℕ}
    (he : Even n) (h₁ : Squarefree n) (h₂ : Squarefree (n + 12))
    (ht : (n + 12).totient = n.totient + 12)
    (hs : σ 1 (n + 12) = σ 1 n + 12) : False := by
  obtain ⟨m, hm⟩ := he
  have hn : n = 2 * m := by omega
  have hn' : n + 12 = 2 * (m + 6) := by omega
  rw [hn] at h₁
  rw [hn'] at h₂
  have hcop₁ := Nat.coprime_of_squarefree_mul h₁
  have hcop₂ := Nat.coprime_of_squarefree_mul h₂
  have ho₁ := hcop₁.odd_of_left
  have ho₂ := hcop₂.odd_of_left
  have hsq₁ := h₁.squarefree_of_dvd (dvd_mul_left m 2)
  have hsq₂ := h₂.squarefree_of_dvd (dvd_mul_left (m + 6) 2)
  rw [hn', hn, Nat.totient_mul hcop₁, Nat.totient_mul hcop₂] at ht
  norm_num at ht
  rw [hn', hn, isMultiplicative_sigma.map_mul_of_coprime hcop₁,
    isMultiplicative_sigma.map_mul_of_coprime hcop₂, show σ 1 2 = 3 by decide] at hs
  have hadd : σ 1 (m + 6) = σ 1 m + 4 := by omega
  have hsmall : m.primeFactors.card ≤ 2 ∨ (m + 6).primeFactors.card ≤ 2 := by
    by_contra! h
    have hd₁ := dvd_eight_sigma_of_card_ge_three hsq₁ ho₁ (by omega)
    have hd₂ := dvd_eight_sigma_of_card_ge_three hsq₂ ho₂ (by omega)
    omega
  rcases hsmall with hc | hc
  · rcases low_excess_of_card_le_two hsq₁ hc with h | h <;>
      rcases A056777Closure.low_excess_of_odd_squarefree (m + 6) ho₂ hsq₂ with h' | h' | h' <;>
      omega
  · rcases low_excess_of_card_le_two hsq₂ hc with h | h <;>
      rcases A056777Closure.low_excess_of_odd_squarefree m ho₁ hsq₁ with h' | h' | h' <;>
      omega

/-- The A056777 converse holds whenever both endpoints are squarefree. -/
theorem prime_quadruple_of_squarefree_pair {n : ℕ}
    (hn : 1 < n) (hnp : ¬n.Prime) (h₁ : Squarefree n) (h₂ : Squarefree (n + 12))
    (ht : (n + 12).totient = n.totient + 12)
    (hs : σ 1 (n + 12) = σ 1 n + 12) :
    ∃ p : ℕ, p.Prime ∧ (p + 2).Prime ∧ (p + 6).Prime ∧ (p + 8).Prime ∧ n = p * (p + 8) := by
  by_cases he : Even n
  · exact (no_even_squarefree_pair he h₁ h₂ ht hs).elim
  · exact prime_quadruple_of_odd_squarefree_pair hn hnp
      (Nat.not_even_iff_odd.mp he) h₁ h₂ ht hs


end A056777Squarefree
end

section
/-
# Injectivity of the totient deficit and divisor surplus for prime products `p²q`

For distinct primes `p` and `q`, the values of `n - φ(n)` and `σ(n) - n`
determine both primes when `n = p²q`. In particular, two such numbers at
distance 12 cannot satisfy both gap equalities of OEIS A056777.

Integer-valued differences avoid truncated subtraction.
-/

namespace A056777

open scoped ArithmeticFunction.sigma

theorem totientDeficit_prime_sq_mul_prime {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ((↑(p ^ 2 * q) : ℤ) - (p ^ 2 * q).totient) = (p : ℤ) ^ 2 + p * (q : ℤ) - p := by
  have hc : (p ^ 2).Coprime q := ((Nat.coprime_primes hp hq).mpr hpq).pow_left 2
  rw [Nat.totient_mul hc, Nat.totient_prime_pow_succ hp 1, pow_one, Nat.totient_prime hq]
  push_cast [hp.one_lt.le, hq.one_lt.le]
  ring

theorem divisorSurplus_prime_sq_mul_prime {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ((σ 1 (p ^ 2 * q) : ℤ) - (p ^ 2 * q)) = (p : ℤ) ^ 2 + ((p : ℤ) + 1) * (q + 1) := by
  have hc : (p ^ 2).Coprime q := ((Nat.coprime_primes hp hq).mpr hpq).pow_left 2
  have hsq : σ 1 (p ^ 2) = 1 + p + p ^ 2 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
    simp [Finset.sum_range_succ]
  have hq' : σ 1 q = 1 + q := by
    simpa [Finset.sum_range_succ] using
      (ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) hq)
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hc, hsq, hq']
  push_cast
  ring

/-- The two arithmetic invariants identify the ordered primes in a product `p²q`. -/
theorem prime_sq_mul_prime_invariants_injective {p q r s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s)
    (hf : ((↑(p ^ 2 * q) : ℤ) - (p ^ 2 * q).totient) = ((↑(r ^ 2 * s) : ℤ) - (r ^ 2 * s).totient))
    (hg : ((σ 1 (p ^ 2 * q) : ℤ) - (p ^ 2 * q)) = ((σ 1 (r ^ 2 * s) : ℤ) - (r ^ 2 * s))) :
    p = r ∧ q = s := by
  rw [totientDeficit_prime_sq_mul_prime hp hq hpq,
    totientDeficit_prime_sq_mul_prime hr hs hrs] at hf
  rw [divisorSurplus_prime_sq_mul_prime hp hq hpq,
    divisorSurplus_prime_sq_mul_prime hr hs hrs] at hg
  have hsum : (q : ℤ) + 2 * p = (s : ℤ) + 2 * r := by
    linear_combination hg - hf
  have hfactor : ((p : ℤ) - r) * ((q : ℤ) + 2 * p - p - r - 1) = 0 := by
    linear_combination hf - (r : ℤ) * hsum
  rcases mul_eq_zero.mp hfactor with heq | heq
  · have hpr : p = r := by omega
    omega
  · have hq' := hq.two_le
    have hs' := hs.two_le
    omega

/-- No two distinct-prime products of this shape satisfy both gap equalities at positive gap. -/
theorem no_positive_gap_prime_sq_mul_prime {p q r s d : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s) (hd : 0 < d)
    (hprod : r ^ 2 * s = p ^ 2 * q + d)
    (htot : (r ^ 2 * s).totient = (p ^ 2 * q).totient + d)
    (hsigma : σ 1 (r ^ 2 * s) = σ 1 (p ^ 2 * q) + d) :
    False := by
  have hf : ((↑(p ^ 2 * q) : ℤ) - (p ^ 2 * q).totient) = ((↑(r ^ 2 * s) : ℤ) - (r ^ 2 * s).totient) := by
    simp only [htot]
    rw [show (↑(r ^ 2 * s) : ℤ) = ↑(p ^ 2 * q + d) by exact_mod_cast hprod]
    push_cast
    omega
  have hg : ((σ 1 (p ^ 2 * q) : ℤ) - (p ^ 2 * q)) = ((σ 1 (r ^ 2 * s) : ℤ) - (r ^ 2 * s)) := by
    have hprodZ : (r:ℤ)^2*s=(p:ℤ)^2*q+d := by exact_mod_cast hprod
    rw [hsigma]
    push_cast
    omega
  obtain ⟨rfl, rfl⟩ := prime_sq_mul_prime_invariants_injective hp hq hr hs hpq hrs hf hg
  omega




end A056777
end

section
open Nat

namespace A056777RepeatedTriple

/-- A nonsquarefree number with exactly three prime factors has the form p²q. -/
theorem pow_two_mul_of_nonsquarefree_length_three {n : ℕ}
    (h : n.primeFactorsList.length = 3) (hs : ¬ Squarefree n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p ^ 2 * q := by
  have hn : n ≠ 0 := by rintro rfl; simp at h
  have hn' := Nat.prod_primeFactorsList hn
  have hd : ¬ n.primeFactorsList.Nodup := fun hnd =>
    hs ((Nat.squarefree_iff_nodup_primeFactorsList hn).mpr hnd)
  have hp {p : ℕ} (hm : p ∈ n.primeFactorsList) := Nat.prime_of_mem_primeFactorsList hm
  obtain ⟨a, b, c, heq⟩ : ∃ a b c, n.primeFactorsList = [a,b,c] := by
    generalize hl : n.primeFactorsList = l at h ⊢
    cases l with
    | nil => simp at h
    | cons a l =>
      cases l with
      | nil => simp at h
      | cons b l =>
        cases l with
        | nil => simp at h
        | cons c l =>
          cases l with
          | nil => exact ⟨a,b,c,rfl⟩
          | cons d l => simp at h
  have ha := hp (p := a) (by simp [heq])
  have hb := hp (p := b) (by simp [heq])
  have hc := hp (p := c) (by simp [heq])
  simp only [heq, List.prod_cons, List.prod_nil, mul_one] at hn'
  have hrepeated : a = b ∨ a = c ∨ b = c := by
    by_contra! H
    apply hd
    simp [heq, H.1, H.2.1, H.2.2]
  rcases hrepeated with rfl | rfl | rfl
  · exact ⟨a, c, ha, hc, by nlinarith only [hn']⟩
  · exact ⟨a, b, ha, hb, by nlinarith only [hn']⟩
  · exact ⟨b, a, hb, ha, by nlinarith only [hn']⟩

private theorem totient_defect_cube {p : ℕ} (hp : p.Prime) :
    (p ^ 3).totient + p ^ 2 = p ^ 3 := by
  rw [show 3 = 2 + 1 by rfl, Nat.totient_prime_pow_succ hp]
  have h : p - 1 + 1 = p := by have := hp.one_lt; omega
  calc
    p ^ 2 * (p - 1) + p ^ 2 = p ^ 2 * (p - 1 + 1) := by rw [Nat.mul_add, Nat.mul_one]
    _ = p ^ (2 + 1) := by rw [h]; exact (pow_succ p 2).symm

private theorem totient_defect_repeated {r s : ℕ} (hr : r.Prime) (hs : s.Prime)
    (hne : r ≠ s) :
    (r ^ 2 * s).totient + r * (r + s - 1) = r ^ 2 * s := by
  have hcop := ((Nat.coprime_primes hr hs).mpr hne).pow_left 2
  rw [Nat.totient_mul hcop, show 2 = 1 + 1 by rfl, Nat.totient_prime_pow_succ hr,
    pow_one, Nat.totient_prime hs]
  have hr1 : 1 ≤ r := hr.pos
  have hs1 : 1 ≤ s := hs.pos
  have hrs : 1 ≤ r + s := by omega
  zify [hr1, hs1, hrs]
  ring

/-- A prime cube and a product r²s of distinct primes have different totient defects. -/
theorem cube_defect_ne_repeated_defect {p r s : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hs : s.Prime) (hne : r ≠ s) :
    ¬ ((p ^ 3).totient + r ^ 2 * s = (r ^ 2 * s).totient + p ^ 3) := by
  intro he
  have hc := totient_defect_cube hp
  have hq := totient_defect_repeated hr hs hne
  have heq : p ^ 2 = r * (r + s - 1) := by omega
  have hdiv : r ∣ p ^ 2 := ⟨r + s - 1, heq⟩
  have hdivp := hr.dvd_of_dvd_pow hdiv
  obtain h | h := (Nat.dvd_prime hp).mp hdivp
  · exact hr.ne_one h
  · subst r
    have hcancel : p = p + s - 1 := by
      apply Nat.eq_of_mul_eq_mul_left hp.pos
      simpa [pow_two] using heq
    have := hs.one_lt
    omega

/-- If both endpoints have three prime factors including repetitions, neither endpoint can
be a prime cube. Only the products of two distinct primes with one repeated remain. -/
theorem distinct_repeated_endpoints_of_totient_step {n : ℕ}
    (hn : n.primeFactorsList.length = 3) (hm : (n+12).primeFactorsList.length = 3)
    (hn' : ¬ Squarefree n) (hm' : ¬ Squarefree (n + 12))
    (ht : (n + 12).totient = n.totient + 12) :
    ∃ p q r s : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ s.Prime ∧ p ≠ q ∧ r ≠ s ∧
      n = p ^ 2 * q ∧ n + 12 = r ^ 2 * s := by
  obtain ⟨p, q, hp, hq, hpq⟩ := pow_two_mul_of_nonsquarefree_length_three hn hn'
  obtain ⟨r, s, hr, hs, hrs⟩ := pow_two_mul_of_nonsquarefree_length_three hm hm'
  have hbal : n.totient + (n+12) = (n+12).totient + n := by omega
  have hbal' : (p ^ 2 * q).totient + r ^ 2 * s = (r ^ 2 * s).totient + p ^ 2 * q := by
    rw [← hpq, ← hrs]
    exact hbal
  clear hbal

  by_cases he₁ : p = q
  · subst q
    rw [← pow_succ] at hbal' hpq
    by_cases he₂ : r = s
    · subst s
      rw [← pow_succ] at hrs hbal'
      change (p ^ 3).totient + r ^ 3 = (r ^ 3).totient + p ^ 3 at hbal'
      have h₁ := totient_defect_cube hp
      have h₂ := totient_defect_cube hr
      have he : p ^ 2 = r ^ 2 := by omega
      have he' := (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp he
      subst r
      change n = p ^ 3 at hpq
      change n + 12 = p ^ 3 at hrs
      omega
    · exact (cube_defect_ne_repeated_defect hp hr hs he₂ hbal').elim
  · by_cases he₂ : r = s
    · subst s
      rw [← pow_succ] at hbal'
      exact (cube_defect_ne_repeated_defect hr hp hq he₁ hbal'.symm).elim
    · exact ⟨p, q, r, s, hp, hq, hr, hs, he₁, he₂, hpq, hrs⟩

end A056777RepeatedTriple
end

section
open scoped ArithmeticFunction.sigma

namespace A056777RepeatedTriple

/-- The simultaneous jumps by twelve cannot occur when both endpoints are nonsquarefree
and each has three prime factors counted with multiplicity. -/
theorem no_pair_of_nonsquarefree_length_three {n : ℕ}
    (hlen₁ : n.primeFactorsList.length = 3)
    (hlen₂ : (n + 12).primeFactorsList.length = 3)
    (hns₁ : ¬ Squarefree n) (hns₂ : ¬ Squarefree (n + 12))
    (ht : (n + 12).totient = n.totient + 12)
    (hs : σ 1 (n + 12) = σ 1 n + 12) : False := by
  obtain ⟨p, q, r, s, hp, hq, hr, hs', hpq, hrs, hn, hm⟩ :=
    distinct_repeated_endpoints_of_totient_step hlen₁ hlen₂ hns₁ hns₂ ht
  have hprod : r ^ 2 * s = p ^ 2 * q + 12 := by rw [← hm, ← hn]
  have htot : (r ^ 2 * s).totient = (p ^ 2 * q).totient + 12 := by
    rw [← hm, ← hn]
    exact ht
  have hσ : σ 1 (r ^ 2 * s) = σ 1 (p ^ 2 * q) + 12 := by
    rw [← hm, ← hn]
    exact hs
  exact A056777.no_positive_gap_prime_sq_mul_prime hp hq hr hs' hpq hrs (by decide) hprod htot hσ

end A056777RepeatedTriple
end

section
open scoped ArithmeticFunction.sigma
open Nat ArithmeticFunction

namespace A056777CubeSquarefreeTriple

private theorem excess_cube {p : ℕ} (hp : p.Prime) :
    σ 1 (p ^ 3) + (p ^ 3).totient = 2 * p ^ 3 + p + 1 := by
  have hsig : σ 1 (p ^ 3) = 1 + p + p ^ 2 + p ^ 3 := by
    simp only [sigma_one_apply_prime_pow hp, Finset.sum_range_succ, Finset.sum_range_zero,
      pow_zero, pow_one, zero_add]
  have htot : (p ^ 3).totient = p ^ 2 * (p - 1) := Nat.totient_prime_pow_succ hp 2
  rw [hsig, htot]
  have h₁ := hp.pos
  zify [h₁]
  ring

private theorem excess_squarefree_triple {r s t : ℕ} (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    σ 1 (r * s * t) + (r * s * t).totient = 2 * (r * s * t) + 2 * (r + s + t) := by
  have hc₁ := (Nat.coprime_primes hr hs).mpr hrs
  have hc₂ := ((Nat.coprime_primes hr ht).mpr hrt).mul_left
    ((Nat.coprime_primes hs ht).mpr hst)
  have hσ {p : ℕ} (hp : p.Prime) : σ 1 p = p + 1 := by
    simpa using sigma_one_apply_prime_pow (i := 1) hp
  rw [Nat.totient_mul hc₂, Nat.totient_mul hc₁,
    isMultiplicative_sigma.map_mul_of_coprime hc₂,
    isMultiplicative_sigma.map_mul_of_coprime hc₁,
    Nat.totient_prime hr, Nat.totient_prime hs, Nat.totient_prime ht, hσ hr, hσ hs, hσ ht]
  have h₁ := hr.pos
  have h₂ := hs.pos
  have h₃ := ht.pos
  zify [h₁, h₂, h₃]
  ring

/-- Equal excess for a prime cube and a squarefree triple makes the latter more
than twelve smaller. This excludes either orientation of the A056777 step. -/
theorem no_cube_squarefree_triple_at_distance_twelve {p r s t : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (he : σ 1 (p ^ 3) + (p ^ 3).totient + 2 * (r * s * t) =
      σ 1 (r * s * t) + (r * s * t).totient + 2 * p ^ 3) :
    r * s * t + 12 < p ^ 3 := by
  rw [excess_cube hp, excess_squarefree_triple hr hs ht hrs hrt hst] at he
  have hr2 := hr.two_le
  have hs2 := hs.two_le
  have ht2 := ht.two_le
  have hsum : p + 1 = 2 * (r + s + t) := by omega
  have hp3 : 3 ≤ p := by omega
  have hrp : r ≤ p - 1 := by omega
  have hsp : s ≤ p - 1 := by omega
  have htp : t ≤ p - 1 := by omega
  have hprod := Nat.mul_le_mul (Nat.mul_le_mul hrp hsp) htp
  have hp1 : 1 ≤ p := by omega
  zify [hp1] at hprod hp3 ⊢
  have hh : 9 ≤ (p : ℤ) * p := calc
    9 = (3 : ℤ) * 3 := by decide
    _ ≤ _ := mul_le_mul hp3 hp3 (by decide) (by omega)
  nlinarith [sq_nonneg ((p : ℤ) - 3)]

end A056777CubeSquarefreeTriple
end

section
open scoped ArithmeticFunction.sigma
open Nat ArithmeticFunction

namespace A056777MixedTriple

private theorem newton_two (r s t : ℕ) :
    3 * (r + s + t) * (r * s * t) ≤ (r * s + r * t + s * t) ^ 2 := by
  zify
  nlinarith [sq_nonneg ((r : ℤ)*s - (r : ℤ)*t), sq_nonneg ((r : ℤ)*s - (s : ℤ)*t),
    sq_nonneg ((r : ℤ)*t - (s : ℤ)*t)]

private theorem newton_one (r s t : ℕ) :
    3 * (r * s + r * t + s * t) ≤ (r + s + t) ^ 2 := by
  zify
  nlinarith [sq_nonneg ((r : ℤ)-s), sq_nonneg ((r : ℤ)-t), sq_nonneg ((s : ℤ)-t)]

private theorem inconsistent_symmetric_bounds (p x S E₂ E₃ : ℤ)
    (hp : 3 ≤ p) (hx : 0 ≤ x) (hS : 2 * S = 2 * p + x)
    (he : E₂ = (2 * p + 1) * S - (p + 1)^2)
    (hgap : p^2 * (x - 1) - 12 ≤ E₃)
    (hN₁ : 3 * E₂ ≤ S^2) (hN₂ : 3 * S * E₃ ≤ E₂^2)
    (hp4 : p ≠ 4) : False := by
  have hf : 0 ≤ x^2 - (8*p + 6)*x - 8*p^2 + 12*p + 12 := by
    have h := congrArg (fun t : ℤ => t^2) hS
    have h' := congrArg (fun t : ℤ => (2*p+1)*t) hS
    nlinarith only [h, h', he, hN₁]
  have hxx : 8*p + 6 < x := by
    by_contra! h
    have hmul := mul_nonneg hx (show 0 ≤ 8*p + 6 - x by omega)
    have hquad := mul_nonneg (show 0 ≤ p - 3 by omega) (show 0 ≤ 8*p + 12 by omega)
    nlinarith only [hf, hmul, hquad, hp]
  have hSL : 5*p + 3 < S := by omega
  have hS0 : 0 ≤ S := by omega
  have hN : 3*S*(p^2*(2*S-2*p-1)-12) ≤ ((2*p+1)*S-(p+1)^2)^2 := by
    rw [← he]
    have hh : p^2 * (2*S - 2*p - 1) - 12 ≤ E₃ := by
      have h' : 2*S-2*p-1 = x-1 := by omega
      simpa [h'] using hgap
    have := mul_le_mul_of_nonneg_left hh (show 0 ≤ 3*S by omega)
    exact this.trans hN₂
  by_cases hp3 : p = 3
  · subst p
    have h18 : 18 < S := by omega
    have hquad := mul_nonneg (show 0 ≤ S - 18 by omega) (show 0 ≤ 5*S + 89 by omega)
    nlinarith only [hN, hquad]
  · have hp5 : 5 ≤ p := by omega
    have hp0 : 0 ≤ p := by omega
    have hp2 : 0 ≤ p^2 := sq_nonneg p
    have hA : p^2 ≤ 2*p^2-4*p-1 := by
      have := mul_nonneg hp0 (show 0 ≤ p-5 by omega)
      nlinarith
    have hB : -2*p^3 ≤ -2*p^3+7*p^2+8*p-34 := by
      nlinarith
    have hp1 : (p + 1)^2 ≤ 2*p^2 := by
      have := mul_nonneg (show 0 ≤ p-3 by omega) (show 0 ≤ p by omega)
      nlinarith
    have hC : (p+1)^4 ≤ 4*p^4 := by
      have hh := mul_le_mul hp1 hp1 (sq_nonneg _) (by positivity : 0 ≤ 2*p^2)
      nlinarith only [hh]
    have hA' := mul_le_mul_of_nonneg_right hA (sq_nonneg S)
    have hB' := mul_le_mul_of_nonneg_right hB hS0
    have hS' : 5*p ≤ S := by omega
    have hS'' : 0 ≤ S*(S-5*p) := mul_nonneg hS0 (by omega)
    have h1 := mul_nonneg hp2 hS''
    have h2 := mul_nonneg (show 0 ≤ p^3 by positivity) (show 0 ≤ S-5*p by omega)
    have h3 : 0 < p^4 := by positivity
    nlinarith only [hN, hA', hB', hC, h1, h2, h3]

/-- Prime squares times a different prime and squarefree triples cannot share the two
arithmetic-function defects across a gap of twelve. Both orientations are covered. -/
theorem no_mixed_triple_gap_twelve {p q r s t : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (hgap : p ^ 2 * q + 12 = r * s * t ∨ r * s * t + 12 = p ^ 2 * q)
    (hφ : (p ^ 2 * q).totient + r * s * t = (r * s * t).totient + p ^ 2 * q)
    (hσ : σ 1 (p ^ 2 * q) + r * s * t = σ 1 (r * s * t) + p ^ 2 * q) : False := by
  have hc₁ := (Nat.coprime_primes hr hs).mpr hrs
  have hc₂ := ((Nat.coprime_primes hr ht).mpr hrt).mul_left
    ((Nat.coprime_primes hs ht).mpr hst)
  have hc₃ := ((Nat.coprime_primes hp hq).mpr hpq).pow_left 2
  have hp2 := hp.two_le
  by_cases he : p = 2
  · subst p
    have hsq : Squarefree (r*s*t) :=
      Nat.squarefree_mul_iff.mpr ⟨hc₂, Nat.squarefree_mul_iff.mpr ⟨hc₁, hr.squarefree, hs.squarefree⟩,
        ht.squarefree⟩
    have hdiv : 2 * 2 ∣ r*s*t := by
      norm_num at hgap ⊢
      omega
    exact (Nat.squarefree_iff_prime_squarefree.mp hsq 2 Nat.prime_two) hdiv
  have hp3 : 3 ≤ p := by omega
  have hp4 : p ≠ 4 := fun h => (by decide : ¬Nat.Prime 4) (h ▸ hp)
  have hσp {u : ℕ} (hu : u.Prime) : σ 1 u = u + 1 := by
    simpa using sigma_one_apply_prime_pow (i := 1) hu
  have hσpp : σ 1 (p ^ 2) = 1 + p + p ^ 2 := by
    simp only [sigma_one_apply_prime_pow hp, Finset.sum_range_succ, Finset.sum_range_zero,
      pow_zero, pow_one, zero_add]
  have hφpp : (p ^ 2).totient = p * (p - 1) := by
    simpa using (Nat.totient_prime_pow_succ hp 1)
  rw [Nat.totient_mul hc₂, Nat.totient_mul hc₁, Nat.totient_mul hc₃,
    hφpp, Nat.totient_prime hq, Nat.totient_prime hr, Nat.totient_prime hs,
    Nat.totient_prime ht] at hφ
  rw [isMultiplicative_sigma.map_mul_of_coprime hc₂,
    isMultiplicative_sigma.map_mul_of_coprime hc₁,
    isMultiplicative_sigma.map_mul_of_coprime hc₃, hσpp, hσp hq, hσp hr, hσp hs, hσp ht] at hσ
  have hN₁ := newton_one r s t
  have hN₂ := newton_two r s t
  have hg : p ^ 2 * q ≤ r * s * t + 12 := by omega
  have hp₁ := hp.pos
  have hq₁ := hq.pos
  have hr₁ := hr.pos
  have hs₁ := hs.pos
  have ht₁ := ht.pos
  zify [hp₁, hq₁, hr₁, hs₁, ht₁] at hφ hσ hN₁ hN₂ hg hp3 hp4
  have hsum : 2*((r:ℤ)+s+t) = 2*p+(q+1) := by nlinarith only [hφ, hσ]
  have htwo : (r:ℤ)*s+r*t+s*t = (2*p+1)*((r:ℤ)+s+t) - (p+1)^2 := by
    have hh := congrArg (fun x : ℤ => (2*p+1)*x) hsum
    nlinarith only [hφ, hσ, hsum, hh]
  exact inconsistent_symmetric_bounds p (q+1) (r+s+t) (r*s+r*t+s*t) (r*s*t)
    hp3 (by positivity) hsum htwo (by nlinarith only [hg]) hN₁ hN₂ hp4

end A056777MixedTriple
end

section
open scoped ArithmeticFunction.sigma
open Nat

namespace A056777LengthThree

private theorem prime_triple_of_squarefree_length_three {n : ℕ}
    (h : n.primeFactorsList.length = 3) (hs : Squarefree n) :
    ∃ r s t : ℕ, r.Prime ∧ s.Prime ∧ t.Prime ∧ r ≠ s ∧ r ≠ t ∧ s ≠ t ∧ n = r*s*t := by
  have hprod := Nat.prod_primeFactorsList hs.ne_zero
  have hnd := hs.nodup_primeFactorsList
  obtain ⟨r,s,t,heq⟩ : ∃ r s t, n.primeFactorsList = [r,s,t] := by
    generalize hl : n.primeFactorsList = l at h ⊢
    cases l with
    | nil => simp at h
    | cons a l =>
      cases l with
      | nil => simp at h
      | cons b l =>
        cases l with
        | nil => simp at h
        | cons c l =>
          cases l with
          | nil => exact ⟨a,b,c,rfl⟩
          | cons d l => simp at h
  have hr := Nat.prime_of_mem_primeFactorsList (n := n) (p := r) (by simp [heq])
  have hsp := Nat.prime_of_mem_primeFactorsList (n := n) (p := s) (by simp [heq])
  have ht := Nat.prime_of_mem_primeFactorsList (n := n) (p := t) (by simp [heq])
  simp only [heq, List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at hnd
  exact ⟨r,s,t,hr,hsp,ht,hnd.1.1,hnd.1.2,hnd.2,by simpa [heq, mul_assoc] using hprod.symm⟩

private theorem no_mixed_squarefree_nonsquarefree {n m : ℕ}
    (hlen₁ : n.primeFactorsList.length = 3) (hlen₂ : m.primeFactorsList.length = 3)
    (hns₁ : ¬ Squarefree n) (hsf₂ : Squarefree m)
    (hgap : n + 12 = m ∨ m + 12 = n)
    (hφ : n.totient + m = m.totient + n)
    (hσ : σ 1 n + m = σ 1 m + n) : False := by
  obtain ⟨p,q,hp,hq,rfl⟩ :=
    A056777RepeatedTriple.pow_two_mul_of_nonsquarefree_length_three hlen₁ hns₁
  obtain ⟨r,s,t,hr,hs,ht,hrs,hrt,hst,rfl⟩ :=
    prime_triple_of_squarefree_length_three hlen₂ hsf₂
  by_cases he : p = q
  · subst q
    rw [← pow_succ] at hgap hφ hσ
    change (p ^ 3).totient + r*s*t = (r*s*t).totient + p ^ 3 at hφ
    change σ 1 (p ^ 3) + r*s*t = σ 1 (r*s*t) + p ^ 3 at hσ
    have hh := A056777CubeSquarefreeTriple.no_cube_squarefree_triple_at_distance_twelve
      hp hr hs ht hrs hrt hst (by omega)
    change p ^ 3 + 12 = r*s*t ∨ r*s*t + 12 = p ^ 3 at hgap
    omega
  · exact A056777MixedTriple.no_mixed_triple_gap_twelve hp hq hr hs ht he hrs hrt hst hgap hφ hσ

/-- The A056777 conditions cannot hold when both endpoints have exactly three prime factors
counted with multiplicity. This includes all repeated-factor shapes. -/
theorem no_pair_of_length_three {n : ℕ}
    (hlen₁ : n.primeFactorsList.length = 3)
    (hlen₂ : (n + 12).primeFactorsList.length = 3)
    (ht : (n + 12).totient = n.totient + 12)
    (hs : σ 1 (n + 12) = σ 1 n + 12) : False := by
  have hn : 1 < n := by
    by_contra! h
    interval_cases n <;> simp at hlen₁
  have hnp : ¬n.Prime := by
    intro hp
    simp [Nat.primeFactorsList_prime hp] at hlen₁
  have hφ : n.totient + (n + 12) = (n + 12).totient + n := by omega
  have hσ : σ 1 n + (n + 12) = σ 1 (n + 12) + n := by omega
  by_cases hsf₁ : Squarefree n <;> by_cases hsf₂ : Squarefree (n + 12)
  · obtain ⟨p,hp,_,_,hp',he⟩ := A056777Squarefree.prime_quadruple_of_squarefree_pair
      hn hnp hsf₁ hsf₂ ht hs
    have hlist := Nat.perm_primeFactorsList_mul hp.ne_zero hp'.ne_zero
    rw [← he, Nat.primeFactorsList_prime hp, Nat.primeFactorsList_prime hp'] at hlist
    have := hlist.length_eq
    simp [hlen₁] at this
  · exact no_mixed_squarefree_nonsquarefree hlen₂ hlen₁ hsf₂ hsf₁ (Or.inr rfl) hφ.symm hσ.symm
  · exact no_mixed_squarefree_nonsquarefree hlen₁ hlen₂ hsf₁ hsf₂ (Or.inl rfl) hφ hσ
  · exact A056777RepeatedTriple.no_pair_of_nonsquarefree_length_three hlen₁ hlen₂ hsf₁ hsf₂ ht hs

end A056777LengthThree
end

section
open scoped ArithmeticFunction.sigma
open Nat ArithmeticFunction

namespace A056777CubeFour

private theorem sigma_prime {p : ℕ} (hp : p.Prime) : σ 1 p = p + 1 := by
  simpa using sigma_one_apply_prime_pow (i := 1) hp

private theorem sigma_square {p : ℕ} (hp : p.Prime) : σ 1 (p ^ 2) = 1 + p + p ^ 2 := by
  simp only [sigma_one_apply_prime_pow hp, Finset.sum_range_succ, Finset.sum_range_zero,
    pow_zero, pow_one, zero_add]

private theorem sigma_cube {p : ℕ} (hp : p.Prime) : σ 1 (p ^ 3) = 1 + p + p ^ 2 + p ^ 3 := by
  simp only [sigma_one_apply_prime_pow hp, Finset.sum_range_succ, Finset.sum_range_zero,
    pow_zero, pow_one, zero_add]

private theorem excess_cube {p : ℕ} (hp : p.Prime) :
    σ 1 (p ^ 3) + (p ^ 3).totient = 2 * p ^ 3 + p + 1 := by
  rw [sigma_cube hp, show (p ^ 3).totient = p ^ 2 * (p - 1) from Nat.totient_prime_pow_succ hp 2]
  have hp₁ := hp.pos
  zify [hp₁]
  ring

private theorem excess_cube_mul_prime {r s : ℕ} (hr : r.Prime) (hs : s.Prime) (hne : r ≠ s) :
    σ 1 (r ^ 3 * s) + (r ^ 3 * s).totient =
      2 * (r ^ 3 * s) + ((r + 1) * s + 2 * r ^ 2 + r + 1) := by
  have hc := ((Nat.coprime_primes hr hs).mpr hne).pow_left 3
  rw [isMultiplicative_sigma.map_mul_of_coprime hc, sigma_cube hr, sigma_prime hs,
    Nat.totient_mul hc, show (r ^ 3).totient = r ^ 2 * (r - 1) from Nat.totient_prime_pow_succ hr 2,
    Nat.totient_prime hs]
  have hr₁ := hr.pos
  have hs₁ := hs.pos
  zify [hr₁, hs₁]
  ring

private theorem excess_square_mul_primes {r s t : ℕ} (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    σ 1 (r ^ 2 * s * t) + (r ^ 2 * s * t).totient =
      2 * (r ^ 2 * s * t) + (s * t + (2*r+1)*(s+t) + 2*r^2 + 1) := by
  have hc₁ := ((Nat.coprime_primes hr hs).mpr hrs).pow_left 2
  have hc₂ := (((Nat.coprime_primes hr ht).mpr hrt).pow_left 2).mul_left
    ((Nat.coprime_primes hs ht).mpr hst)
  have hφ : (r ^ 2).totient = r * (r - 1) := by
    simpa using (Nat.totient_prime_pow_succ hr 1)
  rw [isMultiplicative_sigma.map_mul_of_coprime hc₂, isMultiplicative_sigma.map_mul_of_coprime hc₁,
    sigma_square hr, sigma_prime hs, sigma_prime ht,
    Nat.totient_mul hc₂, Nat.totient_mul hc₁, hφ, Nat.totient_prime hs, Nat.totient_prime ht]
  have hr₁ := hr.pos
  have hs₁ := hs.pos
  have ht₁ := ht.pos
  zify [hr₁, hs₁, ht₁]
  ring

private theorem excess_four_primes {r s t u : ℕ} (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hu : u.Prime) (hrs : r ≠ s) (hrt : r ≠ t) (hru : r ≠ u) (hst : s ≠ t) (hsu : s ≠ u)
    (htu : t ≠ u) :
    σ 1 (r*s*t*u) + (r*s*t*u).totient =
      2*(r*s*t*u)+2*(r*s+r*t+r*u+s*t+s*u+t*u)+2 := by
  have hc₁ := (Nat.coprime_primes hr hs).mpr hrs
  have hc₂ := ((Nat.coprime_primes hr ht).mpr hrt).mul_left ((Nat.coprime_primes hs ht).mpr hst)
  have hc₃ := (((Nat.coprime_primes hr hu).mpr hru).mul_left
    ((Nat.coprime_primes hs hu).mpr hsu)).mul_left ((Nat.coprime_primes ht hu).mpr htu)
  rw [isMultiplicative_sigma.map_mul_of_coprime hc₃,
    isMultiplicative_sigma.map_mul_of_coprime hc₂, isMultiplicative_sigma.map_mul_of_coprime hc₁,
    sigma_prime hr, sigma_prime hs, sigma_prime ht, sigma_prime hu, Nat.totient_mul hc₃,
    Nat.totient_mul hc₂, Nat.totient_mul hc₁, Nat.totient_prime hr, Nat.totient_prime hs,
    Nat.totient_prime ht, Nat.totient_prime hu]
  have hr₁ := hr.pos
  have hs₁ := hs.pos
  have ht₁ := ht.pos
  have hu₁ := hu.pos
  zify [hr₁, hs₁, ht₁, hu₁]
  ring

theorem four_factor_shape {n : ℕ} (h : n.primeFactorsList.length = 4) :
    (∃ k, n = k^2) ∨
    (∃ r s, r.Prime ∧ s.Prime ∧ r ≠ s ∧ n = r^3*s) ∨
    (∃ r s t, r.Prime ∧ s.Prime ∧ t.Prime ∧ r ≠ s ∧ r ≠ t ∧ s ≠ t ∧ n = r^2*s*t) ∨
    ∃ r s t u, r.Prime ∧ s.Prime ∧ t.Prime ∧ u.Prime ∧
      r ≠ s ∧ r ≠ t ∧ r ≠ u ∧ s ≠ t ∧ s ≠ u ∧ t ≠ u ∧ n = r*s*t*u := by
  have hn : n ≠ 0 := by rintro rfl; simp at h
  have hprod := Nat.prod_primeFactorsList hn
  obtain ⟨a,b,c,d,he⟩ : ∃ a b c d, n.primeFactorsList = [a,b,c,d] := by
    generalize hl : n.primeFactorsList = l at h ⊢
    rcases l with _ | ⟨a,l⟩
    · simp at h
    rcases l with _ | ⟨b,l⟩
    · simp at h
    rcases l with _ | ⟨c,l⟩
    · simp at h
    rcases l with _ | ⟨d,l⟩
    · simp at h
    rcases l with _ | ⟨e,l⟩
    · exact ⟨a,b,c,d,rfl⟩
    · simp at h
  have ha := Nat.prime_of_mem_primeFactorsList (n := n) (p := a) (by simp [he])
  have hb := Nat.prime_of_mem_primeFactorsList (n := n) (p := b) (by simp [he])
  have hc := Nat.prime_of_mem_primeFactorsList (n := n) (p := c) (by simp [he])
  have hd := Nat.prime_of_mem_primeFactorsList (n := n) (p := d) (by simp [he])
  have hsort := (Nat.primeFactorsList_sorted n).pairwise
  simp only [he, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false] at hsort
  have hab : a ≤ b := hsort.1 b (Or.inl rfl)
  have hbc : b ≤ c := hsort.2.1 c (Or.inl rfl)
  have hcd : c ≤ d := hsort.2.2.1 d rfl
  simp only [he, List.prod_cons, List.prod_nil, mul_one] at hprod
  by_cases hab' : a = b <;> by_cases hbc' : b = c <;> by_cases hcd' : c = d
  · left
    refine ⟨a*a, ?_⟩
    subst b c d
    rw [← hprod]
    ring
  · right; left
    refine ⟨a,d,ha,hd,by omega,?_⟩
    subst b c
    rw [← hprod]
    ring
  · left
    refine ⟨a*c, ?_⟩
    subst b d
    rw [← hprod]
    ring
  · right; right; left
    refine ⟨a,c,d,ha,hc,hd,by omega,by omega,hcd',?_⟩
    subst b
    rw [← hprod]
    ring
  · right; left
    refine ⟨b,a,hb,ha,Ne.symm hab',?_⟩
    subst c d
    rw [← hprod]
    ring
  · right; right; left
    refine ⟨b,a,d,hb,ha,hd,Ne.symm hab',by omega,by omega,?_⟩
    subst c
    rw [← hprod]
    ring
  · right; right; left
    refine ⟨c,a,b,hc,ha,hb,by omega,Ne.symm hbc',hab',?_⟩
    subst d
    rw [← hprod]
    ring
  · right; right; right
    refine ⟨a,b,c,d,ha,hb,hc,hd,hab',by omega,by omega,hbc',by omega,hcd',?_⟩
    rw [← hprod]
    ring

private theorem product_three_far_below_cube {p a b c : ℕ} (hp : 3 ≤ p)
    (ha : a < p) (hb : b < p) (hc : c < p) :
    a*b*c + 12 < p^3 := by
  have h₁ : a ≤ p-1 := by omega
  have h₂ : b ≤ p-1 := by omega
  have h₃ : c ≤ p-1 := by omega
  have hprod := Nat.mul_le_mul (Nat.mul_le_mul h₁ h₂) h₃
  have hp₁ : 1 ≤ p := by omega
  zify [hp₁] at hprod hp ⊢
  have hh : 9 ≤ (p : ℤ)*p := calc
    9 = (3 : ℤ)*3 := by decide
    _ ≤ _ := mul_le_mul hp hp (by decide) (by omega)
  have hq := mul_nonneg (show 0 ≤ (p : ℤ) by omega) (show 0 ≤ (p : ℤ)-3 by omega)
  nlinarith only [hprod, hh, hq]

/-- No odd prime cube is twelve from a four-factor number satisfying both jump conditions.
The equality of arithmetic defects treats both orientations at once. -/
theorem no_odd_cube_four_pair {p m : ℕ} (hp : p.Prime) (ho : Odd p)
    (hl : m.primeFactorsList.length = 4)
    (hgap : p^3 + 12 = m ∨ m + 12 = p^3)
    (hφ : (p^3).totient + m = m.totient + p^3)
    (hσ : σ 1 (p^3) + m = σ 1 m + p^3) : False := by
  have hpo := Nat.odd_iff.mp ho
  have hp₃ : 3 ≤ p := by have := hp.two_le; omega
  have hpcube : Odd (p^3) := by simpa [pow_succ, Nat.odd_mul] using ho
  have hσeven : Even (σ 1 (p^3)) := by
    rw [sigma_cube hp]
    have h₂ := Nat.odd_iff.mp (show Odd (p^2) by simpa [pow_two, Nat.odd_mul] using ho)
    have h₃ := Nat.odd_iff.mp hpcube
    exact Nat.even_iff.mpr (by omega)
  have he : σ 1 m + m.totient = 2*m + p + 1 := by
    have := excess_cube hp
    omega
  rcases four_factor_shape hl with ⟨k,hk⟩ | ⟨r,s,hr,hs,hne,hm⟩ |
    ⟨r,s,t,hr,hs,ht,hrs,hrt,hst,hm⟩ | ⟨r,s,t,u,hr,hs,ht,hu,hrs,hrt,hru,hst,hsu,htu,hm⟩
  · have hm0 : m ≠ 0 := by rintro rfl; simp at hl
    have hodd := Nat.odd_iff.mp ((A056777Parity.odd_sigma_iff_square_or_twice_square hm0).mpr
      (Or.inl ⟨k,hk⟩))
    have := Nat.even_iff.mp hσeven
    omega
  · rw [hm, excess_cube_mul_prime hr hs hne] at he
    have h : p = (r+1)*s + 2*r^2 + r := by omega
    have hr2 := hr.two_le
    have hs2 := hs.two_le
    have h₁ : r^2 < p := by nlinarith
    have h₂ : r < p := by nlinarith
    have h₃ : s < p := by nlinarith
    have hlt := product_three_far_below_cube hp₃ h₁ h₂ h₃
    have hmul : r^3*s = r^2*r*s := by ring
    rw [hm, hmul] at hgap
    omega
  · rw [hm, excess_square_mul_primes hr hs ht hrs hrt hst] at he
    have h : p = s*t + (2*r+1)*(s+t) + 2*r^2 := by omega
    have h₁ : r^2 < p := by have := hr.two_le; nlinarith
    have h₂ : s < p := by have := ht.two_le; have := hs.two_le; nlinarith
    have h₃ : t < p := by have := hs.two_le; have := ht.two_le; nlinarith
    have hlt := product_three_far_below_cube hp₃ h₁ h₂ h₃
    rw [hm] at hgap
    omega
  · rw [hm, excess_four_primes hr hs ht hu hrs hrt hru hst hsu htu] at he
    have h₁ : r*s < p := by omega
    have h₂ : t*u < p := by omega
    have hlt := product_three_far_below_cube hp₃ h₁ h₂ (show 1 < p by omega)
    have hmul : r*s*t*u = (r*s)*(t*u)*1 := by ring
    rw [hm, hmul] at hgap
    omega

/-- A prime cube cannot be paired with an endpoint of total prime multiplicity four. -/
theorem no_cube_four_pair {p m : ℕ} (hp : p.Prime)
    (hl : m.primeFactorsList.length = 4)
    (hgap : p^3 + 12 = m ∨ m + 12 = p^3)
    (hφ : (p^3).totient + m = m.totient + p^3)
    (hσ : σ 1 (p^3) + m = σ 1 m + p^3) : False := by
  rcases hp.eq_two_or_odd with rfl | ho
  · have hm : m = 20 := by norm_num at hgap; omega
    subst m
    have hp5 : Nat.Prime 5 := Nat.prime_five
    have hlen := (Nat.perm_primeFactorsList_mul (a := 2^2) (b := 5)
      (by decide) (by decide)).length_eq
    rw [show (2 : ℕ)^2*5 = 20 by decide, Nat.prime_two.primeFactorsList_pow,
      Nat.primeFactorsList_prime hp5, List.length_append, List.length_replicate] at hlen
    change (20 : ℕ).primeFactorsList.length = 3 at hlen
    omega
  · exact no_odd_cube_four_pair hp (Nat.odd_iff.mpr ho) hl hgap hφ hσ

end A056777CubeFour
end

section
open scoped ArithmeticFunction.sigma
open Nat ArithmeticFunction

namespace A056777MixedFour

private theorem comp_pair_square_bound (r s t u : ℤ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    36 * (r*s*t*u) ≤ (r*s+r*t+r*u+s*t+s*u+t*u)^2 := by
  have hpair (a b c d : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
      4*(a*b*c*d) ≤ (a*b+c*d)*(a*c+b*d) := by
    nlinarith only [mul_nonneg (mul_nonneg hb hc) (sq_nonneg (a-d)),
      mul_nonneg (mul_nonneg ha hd) (sq_nonneg (b-c))]
  have h₁ := hpair r s t u hr hs ht hu
  have h₂ := hpair r s u t hr hs hu ht
  have h₃ := hpair r t u s hr ht hu hs
  nlinarith only [h₁,h₂,h₃,sq_nonneg (r*s-t*u),sq_nonneg (r*t-s*u),sq_nonneg (r*u-s*t)]

private theorem newton_four (r s t u : ℤ) :
    8 * (r*s+r*t+r*u+s*t+s*u+t*u) * (r*s*t*u) ≤
    3 * (r*s*t+r*s*u+r*t*u+s*t*u)^2 := by
  let a := r*s*t
  let b := r*s*u
  let c := r*t*u
  let d := s*t*u
  have h : 8*(a*b+a*c+a*d+b*c+b*d+c*d) ≤ 3*(a+b+c+d)^2 := by
    nlinarith only [sq_nonneg (a-b),sq_nonneg (a-c),sq_nonneg (a-d),
      sq_nonneg (b-c),sq_nonneg (b-d),sq_nonneg (c-d)]
  dsimp [a,b,c,d] at h
  nlinarith only [h]

private theorem inconsistent_bounds (p q x y z : ℤ)
    (hp : 5 ≤ p) (hq : 2 ≤ q) (hx : 0 < x) (hy : 0 ≤ y)
    (hqx : q = 2*x-2*p+1) (hE : y ≤ (2*p+1)*x)
    (hprod : p^2*q - 12 ≤ z)
    (hA : 36*z ≤ x^2) (hN : 8*x*z ≤ 3*y^2) : False := by
  have hp0 : 0 ≤ p := by omega
  have hp2 : 25 ≤ p^2 := by
    have hh := mul_le_mul hp hp (by decide : (0:ℤ) ≤ 5) hp0
    nlinarith only [hh]
  have hx3 : 3*p < x := by
    by_contra! hx3
    have hsq := mul_le_mul hx3 hx3 hx.le (by omega : 0 ≤ 3*p)
    have hq2 := mul_le_mul_of_nonneg_left hq (sq_nonneg p)
    nlinarith only [hprod,hA,hsq,hq2,hp2]
  have hlo : 4*p^2*x ≤ 3*z := by
    have hh := mul_nonneg (sq_nonneg p) (show 0 ≤ 2*x-6*p by omega)
    have hq' := congrArg (fun u : ℤ => p^2*u) hqx
    nlinarith only [hprod,hh,hq',hp2]
  have hx48 : 48*p^2 ≤ x := by
    by_contra! hh
    have hn := mul_pos (show 0 < 48*p^2 - x by omega) hx
    nlinarith only [hA,hlo,hn]
  have hx16 : 16*p ≤ x := by
    have hh := mul_nonneg hp0 (show 0 ≤ p-1 by omega)
    nlinarith only [hx48,hh,hp0]
  have hstrong : 15*p^2*x ≤ 8*z := by
    have hh := mul_nonneg (sq_nonneg p) (show 0 ≤ x-16*p by omega)
    have hq' := congrArg (fun u : ℤ => p^2*u) hqx
    nlinarith only [hprod,hh,hq',hp2]
  have hysq := mul_le_mul hE hE hy
    (mul_nonneg (show 0 ≤ 2*p+1 by omega) hx.le)
  have hstrong' := mul_le_mul_of_nonneg_right hstrong hx.le
  have hcoeff : 3*(2*p+1)^2 < 15*p^2 := by
    have hh := mul_nonneg hp0 (show 0 ≤ p-5 by omega)
    nlinarith only [hh,hp,hp2]
  have hs := mul_lt_mul_of_pos_right hcoeff (mul_pos hx hx : 0 < x*x)
  nlinarith only [hs,hN,hysq,hstrong']

private theorem three_core_impossible {q r s t : ℕ} (hq : q.Prime) (hq3 : q ≠ 3)
    (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hr3 : r ≠ 3) (hs3 : s ≠ 3) (ht3 : t ≠ 3)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (hgap : 3^2*q + 12 = 3*(r*s*t) ∨ 3*(r*s*t) + 12 = 3^2*q)
    (hφ : (3^2*q).totient + 3*(r*s*t) = (3*(r*s*t)).totient + 3^2*q) : False := by
  have h3 := Nat.prime_three
  have hcop := ((Nat.coprime_primes h3 hq).mpr hq3.symm).pow_left 2
  have hc₁ := (Nat.coprime_primes hr hs).mpr hrs
  have hc₂ := ((Nat.coprime_primes hr ht).mpr hrt).mul_left ((Nat.coprime_primes hs ht).mpr hst)
  have hc₃ := (((Nat.coprime_primes h3 hr).mpr hr3.symm).mul_right
    ((Nat.coprime_primes h3 hs).mpr hs3.symm)).mul_right ((Nat.coprime_primes h3 ht).mpr ht3.symm)
  rw [Nat.totient_mul hcop, Nat.totient_mul hc₃, Nat.totient_prime hq,
    show ((3 : ℕ)^2).totient = 6 by decide, Nat.totient_prime h3] at hφ
  norm_num at hφ hgap
  have hcl : r*s*t - (r*s*t).totient ≤ 5 := by
    have hq₂ := hq.two_le
    omega
  have hrp : 1 ≤ r := hr.pos
  have hsp : 1 ≤ s := hs.pos
  have htp : 1 ≤ t := ht.pos
  have hbound : (r*s*t).totient + s*t ≤ r*s*t := by
    rw [Nat.totient_mul hc₂, Nat.totient_mul hc₁, Nat.totient_prime hr,
      Nat.totient_prime hs, Nat.totient_prime ht]
    have hh := Nat.mul_le_mul (Nat.mul_le_mul (le_refl (r-1)) (Nat.sub_le s 1)) (Nat.sub_le t 1)
    zify [hrp,hsp,htp] at hh ⊢
    nlinarith only [hh]
  have hs₂ := hs.two_le
  have ht₂ := ht.two_le
  have hst_big : 6 ≤ s*t := by
    by_cases hs₂' : s = 2
    · subst s
      have ht₃ : 3 ≤ t := by omega
      exact Nat.mul_le_mul (le_refl 2) ht₃
    · have hs₃ : 3 ≤ s := by omega
      exact Nat.mul_le_mul hs₃ ht₂
  omega

private theorem no_three_squarefree_four {q r s t u : ℕ} (hq : q.Prime) (hq3 : q ≠ 3)
    (hr : r.Prime) (hs : s.Prime) (ht : t.Prime) (hu : u.Prime)
    (hrs : r ≠ s) (hrt : r ≠ t) (hru : r ≠ u) (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u)
    (hgap : 3^2*q + 12 = r*s*t*u ∨ r*s*t*u + 12 = 3^2*q)
    (hφ : (3^2*q).totient + r*s*t*u = (r*s*t*u).totient + 3^2*q) : False := by
  have hd : 3 ∣ r*s*t*u := by omega
  simp only [Nat.prime_three.dvd_mul] at hd
  have from_dvd (v : ℕ) (hv : v.Prime) (h : 3 ∣ v) : v = 3 := by
    rcases (Nat.dvd_prime hv).mp h with h | h
    · omega
    · exact h.symm
  rcases hd with ((hd | hd) | hd) | hd
  · obtain rfl := from_dvd r hr hd
    have hh : 3*s*t*u = 3*(s*t*u) := by ring
    rw [hh] at hgap hφ
    exact three_core_impossible hq hq3 hs ht hu hrs.symm hrt.symm hru.symm hst hsu htu hgap hφ
  · obtain rfl := from_dvd s hs hd
    have hh : r*3*t*u = 3*(r*t*u) := by ring
    rw [hh] at hgap hφ
    exact three_core_impossible hq hq3 hr ht hu hrs hst.symm hsu.symm hrt hru htu hgap hφ
  · obtain rfl := from_dvd t ht hd
    have hh : r*s*3*u = 3*(r*s*u) := by ring
    rw [hh] at hgap hφ
    exact three_core_impossible hq hq3 hr hs hu hrt hst htu.symm hrs hru hsu hgap hφ
  · obtain rfl := from_dvd u hu hd
    have hh : r*s*t*3 = 3*(r*s*t) := by ring
    rw [hh] at hgap hφ
    exact three_core_impossible hq hq3 hr hs ht hru hsu htu hrs hrt hst hgap hφ

/-- A product of a prime square and a different prime cannot satisfy the simultaneous
A056777 shifts with a product of four distinct primes. Both orientations are covered. -/
theorem no_mixed_four_gap_twelve {p q r s t u : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime) (ht : t.Prime) (hu : u.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s) (hrt : r ≠ t) (hru : r ≠ u) (hst : s ≠ t)
    (hsu : s ≠ u) (htu : t ≠ u)
    (hgap : p^2*q + 12 = r*s*t*u ∨ r*s*t*u + 12 = p^2*q)
    (hφ : (p^2*q).totient + r*s*t*u = (r*s*t*u).totient + p^2*q)
    (hσ : σ 1 (p^2*q) + r*s*t*u = σ 1 (r*s*t*u) + p^2*q) : False := by
  have hc₁ := (Nat.coprime_primes hr hs).mpr hrs
  have hc₂ := ((Nat.coprime_primes hr ht).mpr hrt).mul_left ((Nat.coprime_primes hs ht).mpr hst)
  have hc₃ := (((Nat.coprime_primes hr hu).mpr hru).mul_left
    ((Nat.coprime_primes hs hu).mpr hsu)).mul_left ((Nat.coprime_primes ht hu).mpr htu)
  by_cases hp2 : p = 2
  · subst p
    have hsq : Squarefree (r*s*t*u) :=
      Nat.squarefree_mul_iff.mpr ⟨hc₃, Nat.squarefree_mul_iff.mpr
        ⟨hc₂, Nat.squarefree_mul_iff.mpr ⟨hc₁, hr.squarefree, hs.squarefree⟩, ht.squarefree⟩,
        hu.squarefree⟩
    have hdiv : 2*2 ∣ r*s*t*u := by norm_num at hgap ⊢; omega
    exact (Nat.squarefree_iff_prime_squarefree.mp hsq 2 Nat.prime_two) hdiv
  by_cases hp3 : p = 3
  · subst p
    exact no_three_squarefree_four hq hpq.symm hr hs ht hu hrs hrt hru hst hsu htu hgap hφ
  have hp5 : 5 ≤ p := by
    have hp4 : p ≠ 4 := fun h => (by decide : ¬Nat.Prime 4) (h ▸ hp)
    have := hp.two_le
    omega
  have hcp := ((Nat.coprime_primes hp hq).mpr hpq).pow_left 2
  have hσp {a : ℕ} (ha : a.Prime) : σ 1 a = a+1 := by
    simpa using sigma_one_apply_prime_pow (i := 1) ha
  have hσpp : σ 1 (p^2) = 1+p+p^2 := by
    simp only [sigma_one_apply_prime_pow hp, Finset.sum_range_succ, Finset.sum_range_zero,
      pow_zero,pow_one,zero_add]
  have hφpp : (p^2).totient = p*(p-1) := by
    simpa using Nat.totient_prime_pow_succ hp 1
  rw [Nat.totient_mul hcp, hφpp, Nat.totient_prime hq, Nat.totient_mul hc₃, Nat.totient_mul hc₂,
    Nat.totient_mul hc₁, Nat.totient_prime hr, Nat.totient_prime hs, Nat.totient_prime ht,
    Nat.totient_prime hu] at hφ
  rw [isMultiplicative_sigma.map_mul_of_coprime hcp, hσpp, hσp hq,
    isMultiplicative_sigma.map_mul_of_coprime hc₃, isMultiplicative_sigma.map_mul_of_coprime hc₂,
    isMultiplicative_sigma.map_mul_of_coprime hc₁, hσp hr, hσp hs, hσp ht, hσp hu] at hσ
  have hpr := hp.pos
  have hqr := hq.pos
  have hrr := hr.pos
  have hsr := hs.pos
  have htr := ht.pos
  have hur := hu.pos
  have hq2 := hq.two_le
  have hgap' : p^2*q ≤ r*s*t*u+12 := by omega
  zify [hpr,hqr,hrr,hsr,htr,hur] at hp5 hq2 hgap' hφ hσ
  let x : ℤ := r*s+r*t+r*u+s*t+s*u+t*u
  let y : ℤ := r*s*t+r*s*u+r*t*u+s*t*u
  let z : ℤ := r*s*t*u
  have hqx : (q : ℤ) = 2*x-2*p+1 := by dsimp [x]; nlinarith only [hφ,hσ]
  have hE : y ≤ (2*(p:ℤ)+1)*x := by
    have hh := congrArg (fun a : ℤ => p*a) hqx
    have hsq := sq_nonneg ((p : ℤ)-1)
    have hrz : (1 : ℤ) ≤ r := by exact_mod_cast hrr
    have hsz : (1 : ℤ) ≤ s := by exact_mod_cast hsr
    have htz : (1 : ℤ) ≤ t := by exact_mod_cast htr
    have huz : (1 : ℤ) ≤ u := by exact_mod_cast hur
    dsimp [x,y] at *
    nlinarith only [hφ,hqx,hh,hsq,hrz,hsz,htz,huz,hp5]
  have xpos : 0 < x := by dsimp [x]; positivity
  have ypos : 0 ≤ y := by dsimp [y]; positivity
  exact inconsistent_bounds p q x y z hp5 hq2 xpos ypos hqx hE
    (by dsimp [z]; omega)
    (comp_pair_square_bound r s t u (by positivity) (by positivity) (by positivity) (by positivity))
    (newton_four r s t u)

end A056777MixedFour
end

section
open scoped ArithmeticFunction.sigma
open Nat

namespace A056777MixedFour

private theorem four_distinct_primes {m : ℕ} (hl : m.primeFactorsList.length = 4)
    (hs : Squarefree m) : ∃ r s t u, r.Prime ∧ s.Prime ∧ t.Prime ∧ u.Prime ∧
      r ≠ s ∧ r ≠ t ∧ r ≠ u ∧ s ≠ t ∧ s ≠ u ∧ t ≠ u ∧ m = r*s*t*u := by
  rcases A056777CubeFour.four_factor_shape hl with ⟨k,hk⟩ | ⟨r,s,hr,hsp,hne,hm⟩ |
    ⟨r,s,t,hr,hsp,ht,hrs,hrt,hst,hm⟩ | h
  · have hk1 : k = 1 := by
      have hdiv : k*k ∣ m := by rw [hk, pow_two]
      exact Nat.isUnit_iff.mp (hs k hdiv)
    subst k
    simp [hk] at hl
  · have hd : r*r ∣ m := ⟨r*s, by rw [hm]; ring⟩
    exact ((Nat.squarefree_iff_prime_squarefree.mp hs _ hr) hd).elim
  · have hd : r*r ∣ m := ⟨s*t, by rw [hm]; ring⟩
    exact ((Nat.squarefree_iff_prime_squarefree.mp hs _ hr) hd).elim
  · exact h

private theorem composite_of_length_ge_three {n : ℕ} (h : 3 ≤ n.primeFactorsList.length) :
    1 < n ∧ ¬n.Prime := by
  constructor
  · by_contra! hle
    interval_cases n <;> simp at h
  · intro hp
    simp [Nat.primeFactorsList_prime hp] at h

private theorem not_quadruple_of_length_ge_three {n : ℕ} (h : 3 ≤ n.primeFactorsList.length)
    (hp : ∃ p : ℕ, p.Prime ∧ (p+2).Prime ∧ (p+6).Prime ∧ (p+8).Prime ∧ n = p*(p+8)) :
    False := by
  obtain ⟨p,hp,_,_,hp',hn⟩ := hp
  have hh := (Nat.perm_primeFactorsList_mul hp.ne_zero hp'.ne_zero).length_eq
  rw [← hn, Nat.primeFactorsList_prime hp, Nat.primeFactorsList_prime hp'] at hh
  simp [hh] at h

/-- The two arithmetic jumps cannot occur between a three-factor endpoint and a squarefree
four-factor endpoint, regardless of which one is smaller or which primes are repeated. -/
theorem no_length_three_squarefree_length_four_pair {n m : ℕ}
    (h₁ : n.primeFactorsList.length = 3) (h₂ : m.primeFactorsList.length = 4)
    (hsf : Squarefree m) (hgap : n+12=m ∨ m+12=n)
    (hφ : n.totient+m=m.totient+n) (hσ : σ 1 n+m = σ 1 m+n) : False := by
  by_cases hsf' : Squarefree n
  · rcases hgap with h | h
    · subst m
      obtain ⟨hn, hnp⟩ := composite_of_length_ge_three (by omega : 3 ≤ n.primeFactorsList.length)
      exact not_quadruple_of_length_ge_three (by omega : 3 ≤ n.primeFactorsList.length)
        (A056777Squarefree.prime_quadruple_of_squarefree_pair hn hnp hsf' hsf (by omega) (by omega))
    · subst n
      obtain ⟨hm, hmp⟩ := composite_of_length_ge_three (by omega : 3 ≤ m.primeFactorsList.length)
      exact not_quadruple_of_length_ge_three (by omega : 3 ≤ m.primeFactorsList.length)
        (A056777Squarefree.prime_quadruple_of_squarefree_pair hm hmp hsf hsf' (by omega) (by omega))
  · obtain ⟨p,q,hp,hq,rfl⟩ :=
      A056777RepeatedTriple.pow_two_mul_of_nonsquarefree_length_three h₁ hsf'
    by_cases he : p = q
    · subst q
      rw [← pow_succ] at hgap hφ hσ
      exact A056777CubeFour.no_cube_four_pair hp h₂ hgap hφ hσ
    · obtain ⟨r,s,t,u,hr,hs,ht,hu,hrs,hrt,hru,hst,hsu,htu,rfl⟩ := four_distinct_primes h₂ hsf
      exact no_mixed_four_gap_twelve hp hq hr hs ht hu he hrs hrt hru hst hsu htu hgap hφ hσ

end A056777MixedFour
end

section
open scoped ArithmeticFunction.sigma
open Nat Finset ArithmeticFunction

namespace A056777OddFour

private theorem odd_prime_of_mem {n p : ℕ} (hn : Odd n) (hp : p ∈ n.primeFactors) : Odd p := by
  have hd := (Nat.mem_primeFactors.mp hp).2.1
  rcases (Nat.prime_of_mem_primeFactors hp).eq_two_or_odd with rfl | h
  · have := Nat.odd_iff.mp hn
    omega
  · exact Nat.odd_iff.mpr h

/-- Every distinct prime factor of an odd integer contributes a factor of two to its totient. -/
theorem two_pow_card_dvd_totient {n : ℕ} (hn : Odd n) :
    2 ^ n.primeFactors.card ∣ n.totient := by
  have hz : n ≠ 0 := by have := Nat.odd_iff.mp hn; omega
  rw [Nat.totient_eq_prod_factorization hz, Finsupp.prod, Nat.support_factorization,
    ← Finset.prod_const]
  apply Finset.prod_dvd_prod_of_dvd
  intro p hp
  apply dvd_mul_of_dvd_right
  have := Nat.odd_iff.mp (odd_prime_of_mem hn hp)
  omega

private theorem four_dvd_geom_even_length {p : ℕ} (hp : 4 ∣ p + 1) (k : ℕ) :
    4 ∣ ∑ i ∈ Finset.range (2 * k), p ^ i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k+1) = 2*k+1+1 by omega, Finset.sum_range_succ, Finset.sum_range_succ, add_assoc]
    apply dvd_add ih
    have h := dvd_mul_of_dvd_right hp (p ^ (2*k))
    rw [pow_succ p (2*k)]
    simpa [Nat.mul_add, add_comm] using h

private theorem even_sigma_prime_powers_mul {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (hop : Odd p) (hoq : Odd q)
    (ha : 0 < a) (hb : 0 < b) (hcount : Even (a+b))
    (ht : ¬ 8 ∣ (p^a*q^b).totient) :
    Odd (σ 1 (p^a*q^b)) ∨ 8 ∣ σ 1 (p^a*q^b) := by
  have hco := (((Nat.coprime_primes hp hq).mpr hne).pow_left a).pow_right b
  have hφ : (p^a*q^b).totient =
      (p^(a-1)*(p-1))*(q^(b-1)*(q-1)) := by
    rw [Nat.totient_mul hco, Nat.totient_prime_pow hp ha, Nat.totient_prime_pow hq hb]
  have hp1 := Nat.odd_iff.mp hop
  have hq1 := Nat.odd_iff.mp hoq
  have hpp : 4 ∣ p+1 := by
    by_contra h
    have hp4 : 4 ∣ p - 1 := by omega
    have hq2 : 2 ∣ q - 1 := by omega
    exact ht (hφ ▸ mul_dvd_mul (dvd_mul_of_dvd_right hp4 _) (dvd_mul_of_dvd_right hq2 _))
  have hqp : 4 ∣ q+1 := by
    by_contra h
    have hq4 : 4 ∣ q - 1 := by omega
    have hp2 : 2 ∣ p - 1 := by omega
    exact ht (hφ ▸ mul_dvd_mul (dvd_mul_of_dvd_right hp2 _) (dvd_mul_of_dvd_right hq4 _))
  have hh := Nat.even_iff.mp hcount
  by_cases hae : a % 2 = 0
  · left
    have hbe : b % 2 = 0 := by omega
    have hz : p^a*q^b ≠ 0 := mul_ne_zero (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero)
    apply (A056777Parity.odd_sigma_iff_square_or_twice_square hz).mpr
    exact Or.inl ⟨p^(a/2)*q^(b/2), by rw [mul_pow, ← pow_mul, ← pow_mul,
      show a/2*2 = a by omega, show b/2*2 = b by omega]⟩
  · right
    rw [isMultiplicative_sigma.map_mul_of_coprime hco, sigma_one_apply_prime_pow hp,
      sigma_one_apply_prime_pow hq]
    have ha' : a+1 = 2*((a+1)/2) := by omega
    have hb' : b+1 = 2*((b+1)/2) := by omega
    have hd₁ : 4 ∣ ∑ i ∈ Finset.range (a+1), p^i := by
      calc
        4 ∣ ∑ i ∈ Finset.range (2*((a+1)/2)), p^i := four_dvd_geom_even_length hpp _
        _ = _ := by rw [← ha']
    have hd₂ : 4 ∣ ∑ i ∈ Finset.range (b+1), q^i := by
      calc
        4 ∣ ∑ i ∈ Finset.range (2*((b+1)/2)), q^i := four_dvd_geom_even_length hqp _
        _ = _ := by rw [← hb']
    exact (show 8 ∣ 4*4 by decide).trans (mul_dvd_mul hd₁ hd₂)

private theorem sigma_of_odd_even_count {n : ℕ} (hn : Odd n)
    (hl : Even n.primeFactorsList.length)
    (ht : ¬ 8 ∣ n.totient) :
    Odd (σ 1 n) ∨ 8 ∣ σ 1 n := by
  by_cases hone : n = 1
  · subst n
    exact Or.inl (by decide)
  have hz : n ≠ 0 := by have := Nat.odd_iff.mp hn; omega
  have hcard : n.primeFactors.card ≤ 2 := by
    by_contra! h
    exact ht ((pow_dvd_pow 2 h).trans (two_pow_card_dvd_totient hn))
  have hpos : 0 < n.primeFactors.card := by
    by_contra! h
    have he : n.primeFactors = ∅ := Finset.card_eq_zero.mp (by omega)
    exact (Nat.primeFactors_eq_empty.mp he).elim hz hone
  have hprod := Nat.prod_factorization_pow_eq_self hz
  rw [Finsupp.prod, Nat.support_factorization] at hprod
  rcases (show n.primeFactors.card = 1 ∨ n.primeFactors.card = 2 by omega) with h₁ | h₂
  · obtain ⟨p, hpF⟩ := Finset.card_eq_one.mp h₁
    have hp : p.Prime := Nat.prime_of_mem_primeFactors (n := n) (by simp [hpF])
    rw [hpF, Finset.prod_singleton] at hprod
    have he := hl
    rw [← hprod, hp.primeFactorsList_pow, List.length_replicate] at he
    have hh := Nat.even_iff.mp he
    left
    apply (A056777Parity.odd_sigma_iff_square_or_twice_square hz).mpr
    exact Or.inl ⟨p ^ (n.factorization p / 2),
      hprod.symm.trans (by rw [← pow_mul, show n.factorization p / 2 * 2 = n.factorization p by omega])⟩
  · obtain ⟨p,q,hne,hpF⟩ := Finset.card_eq_two.mp h₂
    have hpm : p ∈ n.primeFactors := by simp [hpF]
    have hqm : q ∈ n.primeFactors := by simp [hpF]
    have hp := Nat.prime_of_mem_primeFactors hpm
    have hq := Nat.prime_of_mem_primeFactors hqm
    have hop := odd_prime_of_mem hn hpm
    have hoq := odd_prime_of_mem hn hqm
    let a := n.factorization p
    let b := n.factorization q
    have ha : 0 < a := hp.factorization_pos_of_dvd hz (Nat.mem_primeFactors.mp hpm).2.1
    have hb : 0 < b := hq.factorization_pos_of_dvd hz (Nat.mem_primeFactors.mp hqm).2.1
    rw [hpF, Finset.prod_insert (by simpa using hne), Finset.prod_singleton] at hprod
    change p ^ a * q ^ b = n at hprod
    have hlen := (Nat.perm_primeFactorsList_mul (pow_ne_zero a hp.ne_zero)
      (pow_ne_zero b hq.ne_zero)).length_eq
    rw [hprod, hp.primeFactorsList_pow, hq.primeFactorsList_pow,
      List.length_append, List.length_replicate, List.length_replicate] at hlen
    rw [hlen] at hl
    rw [← hprod] at ht ⊢
    exact even_sigma_prime_powers_mul hp hq hne hop hoq ha hb hl ht

/-- An odd endpoint with an even number of prime factors (with multiplicity) cannot be
twelve away from an odd squarefree endpoint
with at least three prime factors if both arithmetic-function jumps equal the gap. -/
theorem no_squarefree_odd_even_count_pair {n m : ℕ}
    (hn : Odd n) (hm : Odd m) (hnf : Squarefree n)
    (hncard : 3 ≤ n.primeFactors.card)
    (hmeven : Even m.primeFactorsList.length)
    (hgap : n + 12 = m ∨ m + 12 = n)
    (hφ : n.totient + m = m.totient + n)
    (hσ : σ 1 n + m = σ 1 m + n) : False := by
  have hdφ : 8 ∣ n.totient := (pow_dvd_pow 2 hncard).trans (two_pow_card_dvd_totient hn)
  have hfilt : (n.primeFactors.filter fun p => p ≠ 2 ∧ Odd (n.factorization p)) =
      n.primeFactors := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    have ho := Nat.odd_iff.mp (odd_prime_of_mem hn hp)
    have hpos := hp'.factorization_pos_of_dvd hnf.ne_zero (Nat.mem_primeFactors.mp hp).2.1
    have hle := hnf.natFactorization_le_one p
    have he : n.factorization p = 1 := by omega
    exact ⟨by omega, he ▸ (by decide : Odd 1)⟩
  have hdσ := A056777Squarefree.two_pow_card_odd_exponents_dvd_sigma hnf.ne_zero
  rw [hfilt] at hdσ
  have hdσ' : 8 ∣ σ 1 n := (pow_dvd_pow 2 hncard).trans hdσ
  have hmφ : ¬ 8 ∣ m.totient := by omega
  rcases sigma_of_odd_even_count hm hmeven hmφ with ho | hd
  · have := Nat.odd_iff.mp ho
    omega
  · omega

/-- The odd squarefree case with an odd four-factor partner is excluded. -/
theorem no_squarefree_odd_four_pair {n m : ℕ}
    (hn : Odd n) (hm : Odd m) (hnf : Squarefree n)
    (hncard : 3 ≤ n.primeFactors.card)
    (hmfour : m.primeFactorsList.length = 4)
    (hgap : n + 12 = m ∨ m + 12 = n)
    (hφ : n.totient + m = m.totient + n)
    (hσ : σ 1 n + m = σ 1 m + n) : False :=
  no_squarefree_odd_even_count_pair hn hm hnf hncard (hmfour ▸ (by decide : Even 4))
    hgap hφ hσ

end A056777OddFour
end

section
open scoped ArithmeticFunction.sigma
open Nat ArithmeticFunction

namespace A056777ThreeFourShapes

private theorem length_mul_two_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (2*n).primeFactorsList.length = 1 + n.primeFactorsList.length := by
  have hh := (Nat.perm_primeFactorsList_mul (by decide : (2 : ℕ) ≠ 0) hn).length_eq
  rwa [Nat.primeFactorsList_two, List.length_append, List.length_singleton] at hh

private theorem excess_repeated {r s : ℕ} (hr : r.Prime) (hs : s.Prime) (hne : r ≠ s) :
    σ 1 (r^2*s) + (r^2*s).totient = 2*(r^2*s) + s + 2*r + 1 := by
  have hc := ((Nat.coprime_primes hr hs).mpr hne).pow_left 2
  have hσr : σ 1 (r^2) = 1+r+r^2 := by
    simp only [sigma_one_apply_prime_pow hr, Finset.sum_range_succ, Finset.sum_range_zero,
      pow_zero, pow_one, zero_add]
  have hσs : σ 1 s = s+1 := by simpa using sigma_one_apply_prime_pow (i := 1) hs
  have hφr : (r^2).totient = r*(r-1) := by simpa using Nat.totient_prime_pow_succ hr 1
  rw [isMultiplicative_sigma.map_mul_of_coprime hc, hσr, hσs,
    Nat.totient_mul hc, hφr, Nat.totient_prime hs]
  have hr₁ := hr.pos
  have hs₁ := hs.pos
  zify [hr₁,hs₁]
  ring

private theorem excess_cube {r : ℕ} (hr : r.Prime) :
    σ 1 (r^3) + (r^3).totient = 2*r^3+r+1 := by
  have hσ : σ 1 (r^3) = 1+r+r^2+r^3 := by
    simp only [sigma_one_apply_prime_pow hr, Finset.sum_range_succ, Finset.sum_range_zero,
      pow_zero, pow_one, zero_add]
  rw [hσ, show (r^3).totient = r^2*(r-1) from Nat.totient_prime_pow_succ hr 2]
  have hr₁ := hr.pos
  zify [hr₁]
  ring

private theorem totient_238 : (238 : ℕ).totient = 96 := by
  have h₂ : (2 : ℕ).Coprime 119 := by decide
  have h₇ : (7 : ℕ).Coprime 17 := by decide
  have hp₇ : Nat.Prime 7 := by decide
  have hp₁₇ : Nat.Prime 17 := by decide
  rw [show (238 : ℕ) = 2*119 by decide, Nat.totient_mul h₂, Nat.totient_prime Nat.prime_two,
    show (119 : ℕ) = 7*17 by decide, Nat.totient_mul h₇,
    Nat.totient_prime hp₇, Nat.totient_prime hp₁₇]

private theorem totient_250 : (250 : ℕ).totient = 100 := by
  have h₂ : Nat.Coprime 2 (5^3) := by decide
  rw [show (250 : ℕ) = 2*5^3 by decide, Nat.totient_mul h₂, Nat.totient_prime Nat.prime_two,
    show ((5 : ℕ)^3).totient = 5^2*(5-1) from Nat.totient_prime_pow_succ Nat.prime_five 2]
  decide

/-- The even squarefree length-three endpoint cannot have a nonsquarefree length-four
partner. On dividing out 2, the only possible odd core on the four-factor side is 5³,
and the resulting pair 238 and 250 fails the totient shift. -/
theorem no_even_squarefree_three_nonsquarefree_four_pair {n m : ℕ}
    (he : Even n) (hns : Squarefree n) (hms : ¬Squarefree m)
    (hn : n.primeFactorsList.length = 3) (hm : m.primeFactorsList.length = 4)
    (hgap : n+12=m ∨ m+12=n)
    (hφ : n.totient+m=m.totient+n) (hσ : σ 1 n+m = σ 1 m+n) : False := by
  obtain ⟨a,ha⟩ := he
  have hna : n = 2*a := by omega
  have hns' : Squarefree (2*a) := hna ▸ hns
  have hca := Nat.coprime_of_squarefree_mul hns'
  have hoa := hca.odd_of_left
  have ham := Nat.odd_iff.mp hoa
  have hme : Even m := Nat.even_iff.mpr (by omega)
  obtain ⟨b,hb⟩ := hme
  have hmb : m = 2*b := by omega
  have hob : Odd b := Nat.odd_iff.mpr (by omega)
  have hcb := hob.coprime_two_left
  have has : Squarefree a := hns'.squarefree_of_dvd (dvd_mul_left a 2)
  have hbs : ¬Squarefree b := fun h => hms (hmb ▸ ((Nat.squarefree_mul hcb).mpr
    ⟨Nat.prime_two.squarefree,h⟩))
  have haz : a ≠ 0 := has.ne_zero
  have hbz : b ≠ 0 := by have := Nat.odd_iff.mp hob; omega
  have hal : a.primeFactorsList.length = 2 := by
    have hh := length_mul_two_of_ne_zero haz
    rw [hna] at hn
    omega
  have hbl : b.primeFactorsList.length = 3 := by
    have hh := length_mul_two_of_ne_zero hbz
    rw [hmb] at hm
    omega
  have ha1 : 1 < a := by
    by_contra! h
    interval_cases a <;> simp at hal
  have hap : ¬a.Prime := by
    intro hp
    simp [Nat.primeFactorsList_prime hp] at hal
  have hsem : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ a = p*q := by
    by_contra h
    have hh := A056777Closure.factor_count_of_nonsemiprime ha1 hap h
    omega
  obtain ⟨p,q,hp,hq,hapq⟩ := hsem
  have hpq : p ≠ q := by
    rintro rfl
    exact Nat.squarefree_iff_prime_squarefree.mp has p hp ⟨1, by simp [hapq]⟩
  have hsmall := (A056777Closure.excess_two_iff a).mpr ⟨p,q,hp,hq,hpq,hapq⟩
  have hcoreφ := hφ
  have hcoreσ := hσ
  rw [hna,hmb,Nat.totient_mul hca,Nat.totient_mul hcb,Nat.totient_prime Nat.prime_two] at hcoreφ
  norm_num at hcoreφ
  rw [hna,hmb,isMultiplicative_sigma.map_mul_of_coprime hca,
    isMultiplicative_sigma.map_mul_of_coprime hcb, show σ 1 2 = 3 by decide] at hcoreσ
  have hlarge : σ 1 b + b.totient = 2*b+6 ∨ σ 1 b + b.totient + 2 = 2*b := by omega
  obtain ⟨r,s,hr,hs,hbrs⟩ := A056777RepeatedTriple.pow_two_mul_of_nonsquarefree_length_three hbl hbs
  by_cases hrs : r = s
  · subst s
    have hbr : b = r^3 := by simpa [pow_succ] using hbrs
    have hr5 : r = 5 := by
      rw [hbr, excess_cube hr] at hlarge
      have := hr.two_le
      omega
    subst r
    have hm250 : m = 250 := by omega
    have hex : σ 1 b + b.totient = 2*b+6 := by
      rw [hbr]
      exact excess_cube hr
    have hn238 : n = 238 := by omega
    rw [hn238, hm250, totient_238, totient_250] at hφ
    omega
  · rw [hbrs, excess_repeated hr hs hrs] at hlarge
    have hr₂ := hr.two_le
    have hs₂ := hs.two_le
    omega

/-- The only shapes remaining for three factors versus four factors are p²q versus r³s
or r²st, with distinct prime bases within each product. The smaller endpoint is arbitrary. -/
theorem remaining_shapes_three_four_pair {n m : ℕ}
    (hn : n.primeFactorsList.length = 3) (hm : m.primeFactorsList.length = 4)
    (hgap : n+12=m ∨ m+12=n)
    (hφ : n.totient+m=m.totient+n) (hσ : σ 1 n+m = σ 1 m+n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n = p^2*q ∧
      ((∃ r s : ℕ, r.Prime ∧ s.Prime ∧ r ≠ s ∧ m = r^3*s) ∨
        (∃ r s t : ℕ, r.Prime ∧ s.Prime ∧ t.Prime ∧
          r ≠ s ∧ r ≠ t ∧ s ≠ t ∧ m = r^2*s*t)) := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hms : ¬Squarefree m := fun h => A056777MixedFour.no_length_three_squarefree_length_four_pair
    hn hm h hgap hφ hσ
  have hns : ¬Squarefree n := by
    intro h
    by_cases he : Even n
    · exact no_even_squarefree_three_nonsquarefree_four_pair he h hms hn hm hgap hφ hσ
    · have ho := Nat.not_even_iff_odd.mp he
      have hom : Odd m := Nat.odd_iff.mpr (by have := Nat.odd_iff.mp ho; omega)
      have hc : 3 ≤ n.primeFactors.card := by
        rw [← Nat.toFinset_factors, List.toFinset_card_of_nodup h.nodup_primeFactorsList, hn]
      exact A056777OddFour.no_squarefree_odd_four_pair ho hom h hc hm hgap hφ hσ
  obtain ⟨p,q,hp,hq,heq⟩ :=
    A056777RepeatedTriple.pow_two_mul_of_nonsquarefree_length_three hn hns
  have hpq : p ≠ q := by
    rintro rfl
    have heq' : n = p^3 := by simpa [pow_succ] using heq
    rw [heq'] at hgap hφ hσ
    exact A056777CubeFour.no_cube_four_pair hp hm hgap hφ hσ
  refine ⟨p,q,hp,hq,hpq,heq,?_⟩
  rcases A056777CubeFour.four_factor_shape hm with ⟨k,hk⟩ | h | h |
    ⟨r,s,t,u,hr,hs,ht,hu,hrs,hrt,hru,hst,hsu,htu,hm'⟩
  · exfalso
    rcases hgap with he | he
    · have hstep : σ 1 (n+12) = σ 1 n+12 := by rw [he]; omega
      exact (A056777Parity.no_square_shapes_of_sigma_step hn0 hstep).2
        (Or.inl ⟨k,he.trans hk⟩)
    · have hstep : σ 1 (m+12) = σ 1 m+12 := by rw [he]; omega
      exact (A056777Parity.no_square_shapes_of_sigma_step hm0 hstep).1 (Or.inl ⟨k,hk⟩)
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    rw [heq,hm'] at hgap hφ hσ
    exact A056777MixedFour.no_mixed_four_gap_twelve hp hq hr hs ht hu hpq hrs hrt hru hst hsu htu
      hgap hφ hσ

end A056777ThreeFourShapes
end

section
open scoped ArithmeticFunction.sigma
open Nat ArithmeticFunction

namespace A056777EvenRepeatedFour

private theorem prime_of_length_one {n : ℕ} (hn : n ≠ 0)
    (h : n.primeFactorsList.length = 1) : n.Prime := by
  obtain ⟨p, hp⟩ := List.length_eq_one_iff.mp h
  have hprod := Nat.prod_primeFactorsList hn
  rw [hp, List.prod_singleton] at hprod
  have hmem : p ∈ n.primeFactorsList := by simp [hp]
  exact hprod ▸ Nat.prime_of_mem_primeFactorsList hmem

private theorem no_square_endpoints {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0)
    (hgap : n + 12 = m ∨ m + 12 = n) (hσ : σ 1 n + m = σ 1 m + n) :
    (¬ ((∃ k : ℕ, n = k ^ 2) ∨ ∃ k : ℕ, n = 2 * k ^ 2)) ∧
    (¬ ((∃ k : ℕ, m = k ^ 2) ∨ ∃ k : ℕ, m = 2 * k ^ 2)) := by
  rcases hgap with he | he
  · subst m
    exact A056777Parity.no_square_shapes_of_sigma_step hn (by omega)
  · subst n
    exact (A056777Parity.no_square_shapes_of_sigma_step hm (by omega)).symm

private theorem no_four_times_prime_pair {q m : ℕ} (hq : q.Prime) (hq₂ : q ≠ 2)
    (hml : m.primeFactorsList.length = 4) (hgap : 4 * q + 12 = m ∨ m + 12 = 4 * q)
    (hφ : (4 * q).totient + m = m.totient + 4 * q)
    (hmns : ¬ ∃ k : ℕ, m = k ^ 2) : False := by
  have hqo := hq.odd_of_ne_two hq₂
  have hqmod := Nat.odd_iff.mp hqo
  have hm₈ : 8 ∣ m := by omega
  obtain ⟨t, rfl⟩ := hm₈
  have ht₀ : t ≠ 0 := by rintro rfl; simp at hml
  have hlen := (Nat.perm_primeFactorsList_mul (by decide : (8 : ℕ) ≠ 0) ht₀).length_eq
  rw [List.length_append, hml,
    show (8 : ℕ).primeFactorsList.length = 3 by
      rw [show (8 : ℕ) = 2 ^ 3 by decide, Nat.prime_two.primeFactorsList_pow,
        List.length_replicate]] at hlen
  have ht := prime_of_length_one ht₀ (by omega : t.primeFactorsList.length = 1)
  have ht₂ : t ≠ 2 := by
    rintro rfl
    exact hmns ⟨4, by decide⟩
  have hqcop : (4 : ℕ).Coprime q := by
    simpa using hqo.coprime_two_left.pow_left 2
  have htcop : (8 : ℕ).Coprime t := by
    simpa using (ht.odd_of_ne_two ht₂).coprime_two_left.pow_left 3
  rw [Nat.totient_mul hqcop, Nat.totient_mul htcop, Nat.totient_prime hq,
    Nat.totient_prime ht, show (4 : ℕ).totient = 2 by decide,
    show (8 : ℕ).totient = 4 by decide] at hφ
  have := hq.pos
  have := ht.pos
  omega

/-- An even length-three endpoint of the form `p²q` cannot have a length-four partner
at distance twelve with the same totient deficit and divisor surplus. -/
theorem no_even_repeated_three_four_pair {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (he : Even (p ^ 2 * q)) (hm : m.primeFactorsList.length = 4)
    (hgap : p ^ 2 * q + 12 = m ∨ m + 12 = p ^ 2 * q)
    (hφ : (p ^ 2 * q).totient + m = m.totient + p ^ 2 * q)
    (hσ : σ 1 (p ^ 2 * q) + m = σ 1 m + p ^ 2 * q) : False := by
  have hn₀ : p ^ 2 * q ≠ 0 := mul_ne_zero (pow_ne_zero _ hp.ne_zero) hq.ne_zero
  have hm₀ : m ≠ 0 := by rintro rfl; simp at hm
  have hshapes := no_square_endpoints hn₀ hm₀ hgap hσ
  rcases hp.eq_two_or_odd' with rfl | hpo
  · exact no_four_times_prime_pair hq hpq.symm hm hgap hφ (fun hs => hshapes.2 (Or.inl hs))
  rcases hq.eq_two_or_odd' with rfl | hqo
  · exact hshapes.1 (Or.inr ⟨p, by rw [Nat.mul_comm]⟩)
  exact (Nat.not_even_iff_odd.mpr ((hpo.pow).mul hqo)) he

end A056777EvenRepeatedFour
end

section
open scoped ArithmeticFunction.sigma
open Nat ArithmeticFunction

namespace A056777SquarePrimeCubePrime

private theorem no_defect_collision {p q r s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hF : p * (p + q - 1) = r^2 * (r + s - 1))
    (hK : q + 2*p = (r+1)*s + 2*r^2 + r) : False := by
  have hp1 := hp.pos
  have hq1 := hq.pos
  have hr1 := hr.pos
  have hs1 := hs.pos
  by_cases hpr : p = r
  · subst r
    have hF' : p + q - 1 = p*(p+s-1) := by
      apply Nat.eq_of_mul_eq_mul_left hp1
      calc
        p*(p+q-1) = p^2*(p+s-1) := hF
        _ = p*(p*(p+s-1)) := by ring
    have hpq : 1 ≤ p + q := by omega
    have hps : 1 ≤ p + s := by omega
    zify [hpq, hps] at hF' hK hp1 hs1
    nlinarith [sq_nonneg (p : ℤ)]
  have hcop := (Nat.coprime_primes hp hr).mpr hpr
  have hdiv : p ∣ r+s-1 :=
    (hcop.pow_right 2).dvd_of_dvd_mul_left ⟨p+q-1, hF.symm⟩
  obtain ⟨t, ht⟩ := hdiv
  have ht1 : 1 ≤ t := by
    by_contra! h
    have hz : t = 0 := by omega
    simp [hz] at ht
    omega
  have hx : p + q - 1 = r^2*t := by
    apply Nat.eq_of_mul_eq_mul_left hp1
    rw [hF, ht]
    ring
  have hpq : 1 ≤ p+q := by omega
  have hrs : 1 ≤ r+s := by omega
  have hrz : 0 < (r : ℤ) := by exact_mod_cast hr1
  have hpz : 0 < (p : ℤ) := by exact_mod_cast hp1
  have htz : 1 ≤ (t : ℤ) := by exact_mod_cast ht1
  have hz : ((r : ℤ)^2 - p*(r+1))*((t : ℤ)-1) = r*(p+1) := by
    zify [hpq, hrs] at hx ht hK
    have hmul := congrArg (fun a : ℤ => ((r : ℤ)+1)*a) ht
    nlinarith only [hx, hmul, hK]
  have hDpos : (0 : ℤ) < (r : ℤ)^2 - p*(r+1) := by
    by_contra! hn
    have hn' := mul_nonpos_of_nonpos_of_nonneg hn (show (0 : ℤ) ≤ (t : ℤ)-1 by omega)
    rw [hz] at hn'
    have hpos : (0 : ℤ) < (r : ℤ)*(p+1) := mul_pos hrz (by omega)
    omega
  have hle : p*(r+1) ≤ r^2 := by
    zify
    omega
  let D := r^2-p*(r+1)
  have hsum : D+p*(r+1) = r^2 := by dsimp [D]; omega
  have hprod : D*(t-1) = r*(p+1) := by
    dsimp [D]
    zify [hle, ht1]
    exact hz
  have hrd : ¬r ∣ D := by
    intro hd
    have hr2 : r ∣ r^2 := ⟨r, by ring⟩
    have hadd : r ∣ D+p*(r+1) := hsum ▸ hr2
    have hpm : r ∣ p*(r+1) := (Nat.dvd_add_iff_right hd).mpr hadd
    rcases hr.dvd_mul.mp hpm with hh | hh
    · exact hpr ((Nat.prime_dvd_prime_iff_eq hr hp).mp hh).symm
    · have h := (Nat.dvd_add_iff_right (dvd_refl r)).mpr hh
      exact hr.not_dvd_one h
  have hrprod : r ∣ D*(t-1) := ⟨p+1, hprod⟩
  obtain ⟨u, hu⟩ := (hr.dvd_mul.mp hrprod).resolve_left hrd
  have hdu : D*u = p+1 := by
    apply Nat.eq_of_mul_eq_mul_left hr1
    calc
      r*(D*u) = D*(r*u) := by ring
      _ = r*(p+1) := by rw [← hu, hprod]
  have hu1 : 1 ≤ u := by
    by_contra! hn
    have hu0 : u = 0 := by omega
    simp [hu0] at hdu
  have hDle : D ≤ p+1 := by
    calc D = D*1 := by simp
      _ ≤ D*u := Nat.mul_le_mul_left D hu1
      _ = p+1 := hdu
  have hpr' : p < r := by
    by_contra! hn
    have h := Nat.mul_le_mul_right (r+1) hn
    zify at h
    nlinarith only [h, hDpos, hrz]
  have hrp : r = p+1 := by
    by_contra he
    have hprt : p+2 ≤ r := by omega
    have hh := Nat.mul_le_mul_right (r+1) hprt
    zify at hh hDle
    have hcast : (D : ℤ) = (r : ℤ)^2-p*(r+1) := by
      dsimp [D]
      push_cast [Nat.cast_sub hle]
      rfl
    rw [hcast] at hDle
    zify at hprt
    nlinarith only [hh, hDle, hprt]
  have hp2 : p = 2 := by
    rcases hp.eq_two_or_odd with he | ho
    · exact he
    rcases hr.eq_two_or_odd with he | hodd
    · have := hp.two_le
      omega
    · omega
  have hr3 : r = 3 := by omega
  subst p
  subst r
  have hD1 : D = 1 := by decide
  rw [hD1, one_mul] at hprod
  have hs18 : s = 18 := by omega
  subst s
  exact (by decide : ¬Nat.Prime 18) hs

/-- No square-times-prime and cube-times-prime endpoints have equal totient and
divisor-sum defects. This excludes the two orientations of a gap of twelve. -/
theorem no_squarePrime_cubePrime {p q r s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s)
    (hφ : (p^2*q).totient + r^3*s = (r^3*s).totient + p^2*q)
    (hσ : σ 1 (p^2*q) + r^3*s = σ 1 (r^3*s) + p^2*q) : False := by
  have hcp := ((Nat.coprime_primes hp hq).mpr hpq).pow_left 2
  have hcr := ((Nat.coprime_primes hr hs).mpr hrs).pow_left 3
  have hσp {a : ℕ} (ha : a.Prime) : σ 1 a = a+1 := by
    simpa using sigma_one_apply_prime_pow (i := 1) ha
  have hσ₂ : σ 1 (p^2) = 1+p+p^2 := by
    simp only [sigma_one_apply_prime_pow hp, Finset.sum_range_succ, Finset.sum_range_zero,
      pow_zero, pow_one, zero_add]
  have hσ₃ : σ 1 (r^3) = 1+r+r^2+r^3 := by
    simp only [sigma_one_apply_prime_pow hr, Finset.sum_range_succ, Finset.sum_range_zero,
      pow_zero, pow_one, zero_add]
  have hφ₂ : (p^2).totient = p*(p-1) := by
    simpa using Nat.totient_prime_pow_succ hp 1
  have hφ₃ : (r^3).totient = r^2*(r-1) := Nat.totient_prime_pow_succ hr 2
  rw [Nat.totient_mul hcp, Nat.totient_mul hcr, hφ₂, hφ₃,
    Nat.totient_prime hq, Nat.totient_prime hs] at hφ
  rw [isMultiplicative_sigma.map_mul_of_coprime hcp, isMultiplicative_sigma.map_mul_of_coprime hcr,
    hσ₂, hσ₃, hσp hq, hσp hs] at hσ
  apply no_defect_collision hp hq hr hs
  · have hpq1 : 1 ≤ p+q := by have := hp.pos; omega
    have hrs1 : 1 ≤ r+s := by have := hr.pos; omega
    have hp1 := hp.pos
    have hq1 := hq.pos
    have hr1 := hr.pos
    have hs1 := hs.pos
    zify [hpq1, hrs1, hp1, hq1, hr1, hs1] at hφ ⊢
    nlinarith only [hφ]
  · have hp1 := hp.pos
    have hq1 := hq.pos
    have hr1 := hr.pos
    have hs1 := hs.pos
    zify [hp1, hq1, hr1, hs1] at hφ hσ ⊢
    nlinarith only [hφ, hσ]

end A056777SquarePrimeCubePrime
end

section
open scoped ArithmeticFunction.sigma
open Nat ArithmeticFunction

namespace A056777OddRepeatedFour

private theorem totient_repeated {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    (p^2*q).totient = p*(p-1)*(q-1) := by
  have hc := ((Nat.coprime_primes hp hq).mpr hne).pow_left 2
  have hφ : (p^2).totient = p*(p-1) := by simpa using Nat.totient_prime_pow_succ hp 1
  rw [Nat.totient_mul hc,hφ,Nat.totient_prime hq]

private theorem sigma_repeated {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    σ 1 (p^2*q) = (p^2+p+1)*(q+1) := by
  have hc := ((Nat.coprime_primes hp hq).mpr hne).pow_left 2
  have hσp : σ 1 (p^2) = 1+p+p^2 := by
    simp only [sigma_one_apply_prime_pow hp,Finset.sum_range_succ,Finset.sum_range_zero,
      pow_zero,pow_one,zero_add]
  have hσq : σ 1 q = q+1 := by simpa using sigma_one_apply_prime_pow (i := 1) hq
  rw [isMultiplicative_sigma.map_mul_of_coprime hc,hσp,hσq]
  ring

private theorem totient_repeated_triple {r s t : ℕ} (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    (r^2*s*t).totient = r*(r-1)*(s-1)*(t-1) := by
  have hc := (((Nat.coprime_primes hr ht).mpr hrt).pow_left 2).mul_left
    ((Nat.coprime_primes hs ht).mpr hst)
  rw [Nat.totient_mul hc,totient_repeated hr hs hrs,Nat.totient_prime ht]

private theorem sigma_repeated_triple {r s t : ℕ} (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    σ 1 (r^2*s*t) = (r^2+r+1)*(s+1)*(t+1) := by
  have hc := (((Nat.coprime_primes hr ht).mpr hrt).pow_left 2).mul_left
    ((Nat.coprime_primes hs ht).mpr hst)
  have hσt : σ 1 t = t+1 := by simpa using sigma_one_apply_prime_pow (i := 1) ht
  rw [isMultiplicative_sigma.map_mul_of_coprime hc,sigma_repeated hr hs hrs,hσt]

private theorem odd_square_mod_eight {p : ℕ} (hp : Odd p) : p^2 % 8 = 1 := by
  have hp2 := Nat.odd_iff.mp hp
  have hres : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
  rw [Nat.pow_mod]
  rcases hres with h | h | h | h <;> rw [h]

private theorem shifted_mod_eight {a b f g : ℕ}
    (hgap : a+12=b ∨ b+12=a) (h : f+b=g+a) : f%8=(g+4)%8 := by omega

private theorem product_gap_moduli {a b : ℕ} (hgap : a+12=b ∨ b+12=a) :
    a%4=b%4 ∧ b%8=(a+4)%8 := by omega

private theorem residues {p q r s t : ℕ}
    (hop : Odd p) (hoq : Odd q) (hor : Odd r) (hos : Odd s) (hot : Odd t)
    (hgap : p^2*q+12 = r^2*s*t ∨ r^2*s*t+12 = p^2*q)
    (hφ : p*(p-1)*(q-1)+r^2*s*t = r*(r-1)*(s-1)*(t-1)+p^2*q)
    (hσ : (p^2+p+1)*(q+1)+r^2*s*t = (r^2+r+1)*(s+1)*(t+1)+p^2*q) :
    p % 4 = 3 ∧ q % 8 = 3 ∧ (s*t)%8 = 7 ∧ (s+t)%8 = 0 := by
  have hφmod := shifted_mod_eight hgap hφ
  have hσmod := shifted_mod_eight hgap hσ
  have ⟨hgap4,hgap8⟩ := product_gap_moduli hgap
  clear hφ hσ hgap
  have hp2 := Nat.odd_iff.mp hop
  have hq2 := Nat.odd_iff.mp hoq
  have hr2 := Nat.odd_iff.mp hor
  have hs2 := Nat.odd_iff.mp hos
  have ht2 := Nat.odd_iff.mp hot
  have hrφ : 2 ∣ r-1 := by omega
  have hsφ : 2 ∣ s-1 := by omega
  have htφ : 2 ∣ t-1 := by omega
  have hφ8 : 8 ∣ r*(r-1)*(s-1)*(t-1) :=
    mul_dvd_mul (mul_dvd_mul (dvd_mul_of_dvd_right hrφ _) hsφ) htφ
  have hdiv : ¬ 8 ∣ p*(p-1)*(q-1) := by omega
  have hp4 : p % 4 = 3 := by
    by_contra h
    have hpφ : 4 ∣ p-1 := by omega
    have hqφ : 2 ∣ q-1 := by omega
    exact hdiv (mul_dvd_mul (dvd_mul_of_dvd_right hpφ _) hqφ)
  have hq4 : q % 4 = 3 := by
    by_contra h
    have hpφ : 2 ∣ p-1 := by omega
    have hqφ : 4 ∣ q-1 := by omega
    exact hdiv (mul_dvd_mul (dvd_mul_of_dvd_right hpφ _) hqφ)
  have hp8 := odd_square_mod_eight hop
  have hr8 := odd_square_mod_eight hor
  have hp4' : p^2 % 4 = 1 := by omega
  have hr4' : r^2 % 4 = 1 := by omega
  have hn4 : (p^2*q)%4 = 3 := by rw [Nat.mul_mod,hp4',hq4]
  have hm4 : (r^2*s*t)%4 = (s*t)%4 := by
    rw [mul_assoc, Nat.mul_mod (r^2), hr4', one_mul, Nat.mod_mod]
  have hst4 : (s*t)%4 = 3 := by omega
  have hh : 4 ∣ s+1 ∨ 4 ∣ t+1 := by
    by_contra! h
    have hss : s%4=1 := by omega
    have htt : t%4=1 := by omega
    rw [Nat.mul_mod,hss,htt] at hst4
    contradiction
  have hsσ : 2 ∣ s+1 := by omega
  have htσ : 2 ∣ t+1 := by omega
  have hσ8 : 8 ∣ (r^2+r+1)*(s+1)*(t+1) := by
    rcases hh with h | h
    · exact mul_dvd_mul (dvd_mul_of_dvd_right h _) htσ
    · exact mul_dvd_mul (dvd_mul_of_dvd_right hsσ _) h
  have hq8 : q%8=3 := by
    by_contra h
    have h : 8 ∣ q+1 := by omega
    have h' := dvd_mul_of_dvd_right h (p^2+p+1)
    omega
  have hn8 : (p^2*q)%8=3 := by rw [Nat.mul_mod,hp8,hq8]
  have hm8 : (r^2*s*t)%8=(s*t)%8 := by
    rw [mul_assoc,Nat.mul_mod (r^2),hr8,one_mul,Nat.mod_mod]
  have hst8 : (s*t)%8=7 := by omega
  have hsum8 : (s+t)%8=0 := by
    rw [Nat.mul_mod] at hst8
    rw [Nat.add_mod]
    have hs8 : s%8=1 ∨ s%8=3 ∨ s%8=5 ∨ s%8=7 := by omega
    have ht8 : t%8=1 ∨ t%8=3 ∨ t%8=5 ∨ t%8=7 := by omega
    rcases hs8 with hs | hs | hs | hs <;> rcases ht8 with ht | ht | ht | ht <;>
      simp only [hs,ht] at hst8 ⊢ <;>
      first | decide | (norm_num at hst8)
  exact ⟨hp4,hq8,hst8,hsum8⟩

private theorem repeated_base_separation (p q r A B D : ℤ)
    (hp : 3 ≤ p) (hr : 3 ≤ r) (hq : 2 ≤ q) (hA : 0 ≤ A)
    (hδ : D = 12 ∨ D = -12)
    (hK : q-B-(2*r+1)*A-2*r^2+2*p=0)
    (hF : p*(p+q-1)-r*B-r*(r-1)*(A-1)=0)
    (hG : r^2*B-p^2*q-D=0)
    (hpar : p%2=1) (hrpar : r%2=1) : p+4 ≤ r := by
  have hpr : p < r := by
    by_contra! hh
    have hdiff := mul_nonneg (show 0 ≤ p-r by omega) (show 0 ≤ p+q-r-1 by omega)
    have hrK := congrArg (fun x : ℤ => r*x) hK
    have hrA := mul_nonneg (show 0 ≤ r*(r+2) by positivity) hA
    have hr₂ : 9 ≤ r^2 := by
      have hh := mul_le_mul hr hr (by decide : (0:ℤ) ≤ 3) (by omega : 0 ≤ r)
      nlinarith only [hh]
    have hpos := mul_pos (show 0 < r by omega) (show 0 < 2*r^2-2 by omega)
    nlinarith only [hF,hrK,hdiff,hrA,hpos]
  by_contra! hh
  have hre : r=p+2 := by omega
  have hL : r*(p*r+2*p-r^2+r)*A =
      D-p^3+p^2*r+p^2-2*p*r^3-p*r^2+2*p*r-r^3+r^2 := by
    linear_combination (-p*r)*hK+(p+r)*hF+hG
  rw [hre] at hL
  have hl := mul_nonneg (mul_nonneg (show 0 ≤ p+2 by omega)
    (show 0 ≤ p-2 by omega)) hA
  have hp0 : 0 ≤ p := by omega
  have hp2 : 0 ≤ p^2 := sq_nonneg p
  have hp3 : 0 ≤ p^3 := by positivity
  have hp4 : 0 ≤ p^4 := by positivity
  have hD : D ≤ 12 := by omega
  nlinarith only [hL,hl,hp,hp0,hp2,hp3,hp4,hD]

private theorem p_three_impossible {q r s t : ℕ} (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hr3 : r ≠ 3) (hq2 : 2 ≤ q)
    (hgap : 3^2*q+12 = r^2*s*t ∨ r^2*s*t+12 = 3^2*q)
    (hφ : 3*(3-1)*(q-1)+r^2*s*t = r*(r-1)*(s-1)*(t-1)+3^2*q) : False := by
  have hdiv : 3 ∣ r^2*s*t := by norm_num at hgap; omega
  simp only [Nat.prime_three.dvd_mul] at hdiv
  have hex {u : ℕ} (hu : u.Prime) (h : 3 ∣ u) : u = 3 := by
    rcases (Nat.dvd_prime hu).mp h with h | h
    · omega
    · exact h.symm
  have obstruction (v : ℕ) (hv : v.Prime)
      (hg : 3^2*q+12 = 3*(r^2*v) ∨ 3*(r^2*v)+12 = 3^2*q)
      (h : 3*(3-1)*(q-1)+3*(r^2*v) = 2*(r*(r-1)*(v-1))+3^2*q) : False := by
    norm_num at h hg
    have hmax : r^2*v ≤ r*(r-1)*(v-1)+5 := by omega
    have hr₂ := hr.two_le
    have hv₂ := hv.two_le
    have hr₁ : 1 ≤ r := hr.pos
    have hv₁ : 1 ≤ v := hv.pos
    zify [hr₁,hv₁] at hmax hr₂ hv₂
    have hprod : 6 ≤ (r:ℤ)*((r:ℤ)+v-1) :=
      mul_le_mul hr₂ (by omega : (3:ℤ) ≤ (r:ℤ)+v-1) (by decide) (by omega)
    nlinarith only [hmax,hprod]
  rcases hdiv with (hd|hd)|hd
  · exact hr3 (hex hr (Nat.prime_three.dvd_of_dvd_pow hd))
  · have he := hex hs hd
    subst s
    have he : r^2*3*t=3*(r^2*t) := by ring
    rw [he] at hgap hφ
    apply obstruction t ht hgap
    simpa only [show (3:ℕ)-1=2 by decide, mul_assoc, mul_comm, mul_left_comm] using hφ
  · have he := hex ht hd
    subst t
    have he : r^2*s*3=3*(r^2*s) := by ring
    rw [he] at hgap hφ
    apply obstruction s hs hgap
    simpa only [show (3:ℕ)-1=2 by decide, mul_assoc, mul_comm, mul_left_comm] using hφ

/-- Congruence and base separation constraints for the odd repeated/repeated
three-factor versus four-factor case of A056777. -/
theorem odd_square_prime_square_two_primes_constraints {p q r s t : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (hop : Odd p) (hoq : Odd q) (hor : Odd r) (hos : Odd s) (hot : Odd t)
    (hgap : p^2*q+12 = r^2*s*t ∨ r^2*s*t+12 = p^2*q)
    (hφ : (p^2*q).totient+r^2*s*t = (r^2*s*t).totient+p^2*q)
    (hσ : σ 1 (p^2*q)+r^2*s*t = σ 1 (r^2*s*t)+p^2*q) :
    p+4 ≤ r ∧ p%4=3 ∧ q%8=3 ∧ (s*t)%8=7 ∧ (s+t)%8=0 := by
  rw [totient_repeated hp hq hpq,totient_repeated_triple hr hs ht hrs hrt hst] at hφ
  rw [sigma_repeated hp hq hpq,sigma_repeated_triple hr hs ht hrs hrt hst] at hσ
  have hrules := residues hop hoq hor hos hot hgap hφ hσ
  refine ⟨?_,hrules⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; have := Nat.odd_iff.mp hop; omega
  have hr3 : 3 ≤ r := by have := hr.two_le; have := Nat.odd_iff.mp hor; omega
  have hq2 := hq.two_le
  have hpp := Nat.odd_iff.mp hop
  have hrr := Nat.odd_iff.mp hor
  have hp1 := hp.pos
  have hq1 := hq.pos
  have hr1 := hr.pos
  have hs1 := hs.pos
  have ht1 := ht.pos
  zify [hp1,hq1,hr1,hs1,ht1] at hφ hσ hgap hp3 hr3 hq2 hpp hrr ⊢
  let D : ℤ := (r:ℤ)^2*s*t-(p:ℤ)^2*q
  have hD : D=12 ∨ D=-12 := by dsimp [D]; omega
  exact repeated_base_separation p q r (s+t) (s*t) D hp3 hr3 hq2
    (by positivity) hD (by nlinarith only [hφ,hσ]) (by nlinarith only [hφ])
    (by dsimp [D]; ring) hpp hrr

/-- The smaller repeated prime is at least seven in the odd remaining shape. -/
theorem odd_square_prime_square_two_primes_seven_le {p q r s t : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (hop : Odd p) (hoq : Odd q) (hor : Odd r) (hos : Odd s) (hot : Odd t)
    (hgap : p^2*q+12 = r^2*s*t ∨ r^2*s*t+12 = p^2*q)
    (hφ : (p^2*q).totient+r^2*s*t = (r^2*s*t).totient+p^2*q)
    (hσ : σ 1 (p^2*q)+r^2*s*t = σ 1 (r^2*s*t)+p^2*q) : 7 ≤ p := by
  have hc := odd_square_prime_square_two_primes_constraints hp hq hr hs ht hpq hrs hrt hst
    hop hoq hor hos hot hgap hφ hσ
  have hp3 : p ≠ 3 := by
    intro he
    subst p
    rw [totient_repeated hp hq hpq,totient_repeated_triple hr hs ht hrs hrt hst] at hφ
    exact p_three_impossible hr hs ht (by have := hc.1; omega) hq.two_le hgap hφ
  have := hc.2.1
  omega


/-- The signed gap and the two equal-defect equations are equivalent to these
three equations for the prime q and the elementary symmetric functions of s,t. -/
theorem moment_criterion {p q r s t : ℕ} (D : ℤ)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    let A : ℤ := s+t
    let B : ℤ := s*t
    ((r:ℤ)^2*B-(p:ℤ)^2*q = D ∧
      (p^2*q).totient+r^2*s*t = (r^2*s*t).totient+p^2*q ∧
      σ 1 (p^2*q)+r^2*s*t = σ 1 (r^2*s*t)+p^2*q) ↔
    ((q:ℤ) = B+(2*r+1)*A+2*r^2-2*p ∧
      (r:ℤ)*((p:ℤ)*r+2*p-r^2+r)*A =
        D-(p:ℤ)^3+(p:ℤ)^2*r+(p:ℤ)^2-2*(p:ℤ)*r^3-(p:ℤ)*r^2+
          2*(p:ℤ)*r-(r:ℤ)^3+(r:ℤ)^2 ∧
      ((r:ℤ)^2-(p:ℤ)^2)*B = (p:ℤ)^2*((2*r+1)*A+2*r^2-2*p)+D) := by
  dsimp
  rw [totient_repeated hp hq hpq, totient_repeated_triple hr hs ht hrs hrt hst,
    sigma_repeated hp hq hpq, sigma_repeated_triple hr hs ht hrs hrt hst]
  have hp1 := hp.pos
  have hq1 := hq.pos
  have hr1 := hr.pos
  have hs1 := hs.pos
  have ht1 := ht.pos
  zify [hp1,hq1,hr1,hs1,ht1]
  constructor
  · rintro ⟨hG,hφ,hσ⟩
    have hK : (q:ℤ) - (s:ℤ)*t - (2*r+1)*((s:ℤ)+t)-2*(r:ℤ)^2+2*p = 0 := by
      nlinarith only [hφ,hσ]
    have hF : (p:ℤ)*((p:ℤ)+q-1)-(r:ℤ)*((s:ℤ)*t)-
        (r:ℤ)*((r:ℤ)-1)*((s:ℤ)+t-1)=0 := by
      nlinarith only [hφ]
    refine ⟨by nlinarith only [hK], ?_, ?_⟩
    · linear_combination (-(p:ℤ)*r)*hK+((p:ℤ)+r)*hF+hG
    · linear_combination (p:ℤ)^2*hK+hG
  · rintro ⟨hK,hA,hB⟩
    have hG : (r:ℤ)^2*((s:ℤ)*t)-(p:ℤ)^2*q = D := by
      linear_combination hB-(p:ℤ)^2*hK
    have hcancel : ((p:ℤ)+r) *
        ((p:ℤ)*((p:ℤ)+q-1)-(r:ℤ)*((s:ℤ)*t)-
          (r:ℤ)*((r:ℤ)-1)*((s:ℤ)+t-1))=0 := by
      linear_combination hA+((p:ℤ)*r)*hK-hG
    have hsum : 0 < (p:ℤ) + r := by positivity
    have hF := (mul_eq_zero.mp hcancel).resolve_left hsum.ne'
    exact ⟨hG,by nlinarith only [hF],by nlinarith only [hF,hK]⟩


/-- The repeated prime on the four-factor side divides an explicit integer
depending only on the other repeated prime and the signed gap. -/
theorem prime_divisor_sieve {p q r s t : ℕ} (D : ℤ)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (h : (r:ℤ)^2*((s:ℤ)*t)-(p:ℤ)^2*q = D ∧
      (p^2*q).totient+r^2*s*t = (r^2*s*t).totient+p^2*q ∧
      σ 1 (p^2*q)+r^2*s*t = σ 1 (r^2*s*t)+p^2*q) :
    (r:ℤ) ∣ (p:ℤ)^2*((p:ℤ)-1)-D := by
  have hA := ((moment_criterion D hp hq hr hs ht hpq hrs hrt hst).mp h).2.1
  refine ⟨(p:ℤ)^2-2*(p:ℤ)*r^2-(p:ℤ)*r+2*p-(r:ℤ)^2+r-
    ((p:ℤ)*r+2*p-r^2+r)*((s:ℤ)+t),?_⟩
  linear_combination hA

/-- The same prime divisor criterion expressed through the distance between the repeated primes. -/
theorem repeated_prime_distance_sieve {p r : ℕ} (D : ℤ)
    (h : (r:ℤ) ∣ (p:ℤ)^2*((p:ℤ)-1)-D) :
    (r:ℤ) ∣ ((r:ℤ)-p)^2*((r:ℤ)-p+1)+D := by
  obtain ⟨k,hk⟩ := h
  refine ⟨(r:ℤ)^2-3*(r:ℤ)*p+r+3*(p:ℤ)^2-2*p-k,?_⟩
  linear_combination -hk




end A056777OddRepeatedFour
end

section
open scoped ArithmeticFunction.sigma
open Nat

namespace A056777OddRepeatedFourDiscriminant

private theorem negative_discriminant_positive (P J : ℤ)
    (hP : 0 ≤ P) (hJ : 0 ≤ J) :
    (let C := ((P+7+(J+6))*((P+7)*(P+7+(J+6))+2*(P+7)-(P+7+(J+6))^2+(P+7+(J+6)))); let N := ((12)-(P+7)^3+(P+7)^2*(P+7+(J+6))+(P+7)^2-2*(P+7)*(P+7+(J+6))^3-(P+7)*(P+7+(J+6))^2+2*(P+7)*(P+7+(J+6))-(P+7+(J+6))^3+(P+7+(J+6))^2); ((P+7+(J+6))^2-(P+7)^2)*N^2-4*((P+7)^2*((2*(P+7+(J+6))+1)*N+(2*(P+7+(J+6))^2-2*(P+7))*C)+(12)*C)*C) < 0 := by
  let c : ℤ := (11111035680 + P * (9560359728 + P * (3477284496 + P * (702370608 + P * (86539872 + P * (6680400 + P * (316176 + P * (8400 + P * (96))))))))) + J * ((23791396824 + P * (20204722512 + P * (7431611784 + P * (1560716088 + P * (207133352 + P * (18092584 + P * (1044536 + P * (38600 + P * (832 + P * (8)))))))))) + J * ((10349002332 + P * (8075711568 + P * (2690368956 + P * (501632872 + P * (57465032 + P * (4155616 + P * (185836 + P * (4712 + P * (52))))))))) + J * ((2110708104 + P * (1488566160 + P * (438170504 + P * (70027952 + P * (6586632 + P * (365840 + P * (11144 + P * (144)))))))) + J * ((244697100 + P * (153708960 + P * (39033836 + P * (5146108 + P * (372972 + P * (14144 + P * (220))))))) + J * ((17138866 + P * (9427206 + P * (2001736 + P * (205584 + P * (10260 + P * (200)))))) + J * ((720739 + P * (339604 + P * (57532 + P * (4148 + P * (108))))) + J * ((16796 + P * (6578 + P * (820 + P * (32)))) + J * ((167 + P * (52 + P * (4)))))))))))
  have hc : 0 < c := by dsimp [c]; positivity
  have he : -(let C := ((P+7+(J+6))*((P+7)*(P+7+(J+6))+2*(P+7)-(P+7+(J+6))^2+(P+7+(J+6)))); let N := ((12)-(P+7)^3+(P+7)^2*(P+7+(J+6))+(P+7)^2-2*(P+7)*(P+7+(J+6))^3-(P+7)*(P+7+(J+6))^2+2*(P+7)*(P+7+(J+6))-(P+7+(J+6))^3+(P+7+(J+6))^2); ((P+7+(J+6))^2-(P+7)^2)*N^2-4*((P+7)^2*((2*(P+7+(J+6))+1)*N+(2*(P+7+(J+6))^2-2*(P+7))*C)+(12)*C)*C) = c := by
    dsimp [c]
    ring
  omega

private theorem negative_discriminant_negative (P J : ℤ)
    (hP : 0 ≤ P) (hJ : 0 ≤ J) :
    (let C := ((P+7+(J+6))*((P+7)*(P+7+(J+6))+2*(P+7)-(P+7+(J+6))^2+(P+7+(J+6)))); let N := ((-12)-(P+7)^3+(P+7)^2*(P+7+(J+6))+(P+7)^2-2*(P+7)*(P+7+(J+6))^3-(P+7)*(P+7+(J+6))^2+2*(P+7)*(P+7+(J+6))-(P+7+(J+6))^3+(P+7+(J+6))^2); ((P+7+(J+6))^2-(P+7)^2)*N^2-4*((P+7)^2*((2*(P+7+(J+6))+1)*N+(2*(P+7+(J+6))^2-2*(P+7))*C)+(-12)*C)*C) < 0 := by
  let c : ℤ := (10960405920 + P * (9501175152 + P * (3467757456 + P * (701582640 + P * (86506464 + P * (6679824 + P * (316176 + P * (8400 + P * (96))))))))) + J * ((23711473656 + P * (20179880784 + P * (7428687432 + P * (1560560568 + P * (207130184 + P * (18092584 + P * (1044536 + P * (38600 + P * (832 + P * (8)))))))))) + J * ((10329260508 + P * (8070685680 + P * (2689913724 + P * (501616072 + P * (57464840 + P * (4155616 + P * (185836 + P * (4712 + P * (52))))))))) + J * ((2108109672 + P * (1488047376 + P * (438137288 + P * (70027280 + P * (6586632 + P * (365840 + P * (11144 + P * (144)))))))) + J * ((244512444 + P * (153683328 + P * (39032972 + P * (5146108 + P * (372972 + P * (14144 + P * (220))))))) + J * ((17132194 + P * (9426726 + P * (2001736 + P * (205584 + P * (10260 + P * (200)))))) + J * ((720643 + P * (339604 + P * (57532 + P * (4148 + P * (108))))) + J * ((16796 + P * (6578 + P * (820 + P * (32)))) + J * ((167 + P * (52 + P * (4)))))))))))
  have hc : 0 < c := by dsimp [c]; positivity
  have he : -(let C := ((P+7+(J+6))*((P+7)*(P+7+(J+6))+2*(P+7)-(P+7+(J+6))^2+(P+7+(J+6)))); let N := ((-12)-(P+7)^3+(P+7)^2*(P+7+(J+6))+(P+7)^2-2*(P+7)*(P+7+(J+6))^3-(P+7)*(P+7+(J+6))^2+2*(P+7)*(P+7+(J+6))-(P+7+(J+6))^3+(P+7+(J+6))^2); ((P+7+(J+6))^2-(P+7)^2)*N^2-4*((P+7)^2*((2*(P+7+(J+6))+1)*N+(2*(P+7+(J+6))^2-2*(P+7))*C)+(-12)*C)*C) = c := by
    dsimp [c]
    ring
  omega

private theorem negative_discriminant (p r D : ℤ) (hp : 7 ≤ p) (hr : p+6 ≤ r)
    (hD : D=12 ∨ D=-12) : (let C := (r*(p*r+2*p-r^2+r)); let N := (D-p^3+p^2*r+p^2-2*p*r^3-p*r^2+2*p*r-r^3+r^2); (r^2-p^2)*N^2-4*(p^2*((2*r+1)*N+(2*r^2-2*p)*C)+D*C)*C) < 0 := by
  let P := p-7
  let J := r-p-6
  have hP : 0 ≤ P := by dsimp [P]; omega
  have hJ : 0 ≤ J := by dsimp [J]; omega
  have hp' : P+7=p := by dsimp [P]; omega
  have hr' : P+7+(J+6)=r := by dsimp [P,J]; omega
  rcases hD with rfl | rfl
  · have h := negative_discriminant_positive P J hP hJ
    rw [hr',hp'] at h
    exact h
  · have h := negative_discriminant_negative P J hP hJ
    rw [hr',hp'] at h
    exact h

private theorem nonnegative_discriminant (p r A B D : ℤ) (hpr : 0 < r^2-p^2)
    (hA : ((r:ℤ)*((p:ℤ)*(r:ℤ)+2*(p:ℤ)-(r:ℤ)^2+(r:ℤ))) * A = (D-(p:ℤ)^3+(p:ℤ)^2*(r:ℤ)+(p:ℤ)^2-2*(p:ℤ)*(r:ℤ)^3-(p:ℤ)*(r:ℤ)^2+2*(p:ℤ)*(r:ℤ)-(r:ℤ)^3+(r:ℤ)^2))
    (hB : (r^2-p^2)*B=p^2*((2*r+1)*A+2*r^2-2*p)+D)
    (hdisc : 4*B ≤ A^2) :
    0 ≤ (let C := (r*(p*r+2*p-r^2+r)); let N := (D-p^3+p^2*r+p^2-2*p*r^3-p*r^2+2*p*r-r^3+r^2); (r^2-p^2)*N^2-4*(p^2*((2*r+1)*N+(2*r^2-2*p)*C)+D*C)*C) := by
  have he : (let C := (r*(p*r+2*p-r^2+r)); let N := (D-p^3+p^2*r+p^2-2*p*r^3-p*r^2+2*p*r-r^3+r^2); (r^2-p^2)*N^2-4*(p^2*((2*r+1)*N+(2*r^2-2*p)*C)+D*C)*C) =
      (r^2-p^2)*(((r:ℤ)*((p:ℤ)*(r:ℤ)+2*(p:ℤ)-(r:ℤ)^2+(r:ℤ))))^2*(A^2-4*B) := by
    dsimp only
    rw [← hA]
    linear_combination 4*(((r:ℤ)*((p:ℤ)*(r:ℤ)+2*(p:ℤ)-(r:ℤ)^2+(r:ℤ))))^2*hB
  rw [he]
  exact mul_nonneg (mul_nonneg hpr.le (sq_nonneg _)) (sub_nonneg.mpr hdisc)

private theorem prime_of_dvd_four_times_prime {r a : ℕ} (hr : r.Prime) (ha : a.Prime)
    (hbig : 2 < r) (h : r ∣ 4*a) : r=a := by
  rcases hr.dvd_mul.mp h with h₄ | hₐ
  · have hh : r ∣ 2^2 := h₄
    have h₂ := hr.dvd_of_dvd_pow hh
    rcases (Nat.dvd_prime Nat.prime_two).mp h₂ with h | h <;> omega
  · rcases (Nat.dvd_prime ha).mp hₐ with h | h <;> omega

/-- The last odd three-versus-four shape cannot satisfy both jump conditions. -/
theorem no_odd_square_prime_square_two_primes_pair {p q r s t : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (hop : Odd p) (hoq : Odd q) (hor : Odd r) (hos : Odd s) (hot : Odd t)
    (hgap : p^2*q+12 = r^2*s*t ∨ r^2*s*t+12 = p^2*q)
    (hφ : (p^2*q).totient+r^2*s*t = (r^2*s*t).totient+p^2*q)
    (hσ : σ 1 (p^2*q)+r^2*s*t = σ 1 (r^2*s*t)+p^2*q) : False := by
  obtain ⟨hsep,hp4,_,_,_⟩ :=
    A056777OddRepeatedFour.odd_square_prime_square_two_primes_constraints hp hq hr hs ht
      hpq hrs hrt hst hop hoq hor hos hot hgap hφ hσ
  have hp7 := A056777OddRepeatedFour.odd_square_prime_square_two_primes_seven_le hp hq hr hs ht
    hpq hrs hrt hst hop hoq hor hos hot hgap hφ hσ
  let D : ℤ := (r:ℤ)^2*((s:ℤ)*t)-(p:ℤ)^2*q
  have hD : D=12 ∨ D=-12 := by
    zify at hgap
    dsimp [D]
    simp only [mul_assoc] at hgap ⊢
    omega
  have h : (r:ℤ)^2*((s:ℤ)*t)-(p:ℤ)^2*q=D ∧
      (p^2*q).totient+r^2*s*t = (r^2*s*t).totient+p^2*q ∧
      σ 1 (p^2*q)+r^2*s*t = σ 1 (r^2*s*t)+p^2*q := ⟨rfl,hφ,hσ⟩
  obtain ⟨_, hA, hB⟩ :=
    (A056777OddRepeatedFour.moment_criterion D hp hq hr hs ht hpq hrs hrt hst).mp h
  have hA' : ((r:ℤ)*((p:ℤ)*(r:ℤ)+2*(p:ℤ)-(r:ℤ)^2+(r:ℤ))) *((s:ℤ)+t) = (D-(p:ℤ)^3+(p:ℤ)^2*(r:ℤ)+(p:ℤ)^2-2*(p:ℤ)*(r:ℤ)^3-(p:ℤ)*(r:ℤ)^2+2*(p:ℤ)*(r:ℤ)-(r:ℤ)^3+(r:ℤ)^2) := hA
  have hpr : 0 < (r:ℤ)^2-(p:ℤ)^2 := by
    have h₁ : 0 < (r:ℤ)-(p:ℤ) := by
      have h' : (p:ℤ) < r := by exact_mod_cast (show p < r by omega)
      omega
    have h₂ : 0 < (r:ℤ)+(p:ℤ) := by
      have := hr.pos
      positivity
    nlinarith only [mul_pos h₁ h₂]
  have hdisc : 4*((s:ℤ)*t) ≤ ((s:ℤ)+t)^2 := by nlinarith only [sq_nonneg ((s:ℤ)-t)]
  have hNonneg := nonnegative_discriminant p r ((s:ℤ)+t) ((s:ℤ)*t) D hpr hA' hB hdisc
  have hclose : r < p+6 := by
    by_contra! hh
    exact (not_lt_of_ge hNonneg) (negative_discriminant p r D
      (by exact_mod_cast hp7) (by exact_mod_cast hh) hD)
  have hop2 := Nat.odd_iff.mp hop
  have hor2 := Nat.odd_iff.mp hor
  have hrp : r = p+4 := by omega
  have hdist : (r:ℤ)-(p:ℤ)=4 := by
    have h' : (r:ℤ)=(p:ℤ)+4 := by exact_mod_cast hrp
    omega
  have hdvd := A056777OddRepeatedFour.repeated_prime_distance_sieve D
    (A056777OddRepeatedFour.prime_divisor_sieve D hp hq hr hs ht hpq hrs hrt hst h)
  rw [hdist] at hdvd
  rcases hD with hD | hD
  · rw [hD] at hdvd hA
    have hd : r ∣ 4*23 := by exact_mod_cast hdvd
    have hr23 := prime_of_dvd_four_times_prime hr (by decide : Nat.Prime 23) (by omega) hd
    have hp19 : p=19 := by omega
    rw [hr23,hp19] at hA
    norm_num at hA
    omega
  · rw [hD] at hdvd
    norm_num at hdvd
    have hd : r ∣ 4*17 := by exact_mod_cast hdvd
    have hr17 := prime_of_dvd_four_times_prime hr (by decide : Nat.Prime 17) (by omega) hd
    omega

end A056777OddRepeatedFourDiscriminant
end

section
open Nat

namespace A056777CubePrimeFourFour

private theorem totient_defect_cube_mul_prime {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    (p^3*q).totient + p^2*(p+q-1) = p^3*q := by
  have hc := ((Nat.coprime_primes hp hq).mpr hne).pow_left 3
  rw [Nat.totient_mul hc, show (p^3).totient=p^2*(p-1) from Nat.totient_prime_pow_succ hp 2,
    Nat.totient_prime hq]
  have hp₁ := hp.pos
  have hq₁ := hq.pos
  have hpq₁ : 1 ≤ p+q := by omega
  zify [hp₁,hq₁,hpq₁]
  ring

private theorem no_ordered_cube_prime_pair {p q r s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s) (hpr : p < r)
    (hgap : p^3*q+12 = r^3*s ∨ r^3*s+12 = p^3*q)
    (hφ : (p^3*q).totient+r^3*s = (r^3*s).totient+p^3*q) : False := by
  let F := p^2*(p+q-1)
  have hF : F=r^2*(r+s-1) := by
    dsimp [F]
    have h₁ := totient_defect_cube_mul_prime hp hq hpq
    have h₂ := totient_defect_cube_mul_prime hr hs hrs
    omega
  have hpD : p^2 ∣ F := dvd_mul_right _ _
  have hrD : r^2 ∣ F := hF ▸ dvd_mul_right _ _
  have hc := (((Nat.coprime_primes hp hr).mpr hpr.ne).pow_left 2).pow_right 2
  have hFD : p^2*r^2 ∣ F := hc.mul_dvd_of_dvd_of_dvd hpD hrD
  have hFpos : 0 < F := by
    have hpq' : 0 < p+q-1 := by have := hp.two_le; have := hq.two_le; omega
    dsimp [F]
    exact mul_pos (pow_pos hp.pos _) hpq'
  have hFlow := Nat.le_of_dvd hFpos hFD
  have hp₁ := hp.pos
  have hr₁ := hr.pos
  have hq₁ := hq.pos
  have hs₁ := hs.pos
  have hpq₁ : 1 ≤ p+q := by omega
  have hrs₁ : 1 ≤ r+s := by omega
  have hF₁ : F=p^2*(p+q-1) := rfl
  zify [hp₁,hr₁,hq₁,hs₁,hpq₁,hrs₁] at hF hF₁ hgap hFlow hpr
  let D : ℤ := (r:ℤ)^3*s-(p:ℤ)^3*q
  let K : ℤ := (r:ℤ)^3+(r:ℤ)^2*p+(r:ℤ)*p^2+(p:ℤ)^3-
    ((r:ℤ)^2+(r:ℤ)*p+(p:ℤ)^2)
  have hD : D=12 ∨ D=-12 := by dsimp [D]; omega
  have he : D=((r:ℤ)-p)*((F:ℤ)-K) := by
    dsimp only [D,K]
    linear_combination -(r:ℤ)*hF+(p:ℤ)*hF₁
  have hd : (r:ℤ)-p ∣ (12:ℤ) := by
    rcases hD with h | h
    · exact ⟨(F:ℤ)-K,h.symm.trans he⟩
    · refine ⟨-((F:ℤ)-K),?_⟩
      linear_combination h-he
  have hdiff_le : (r:ℤ)-p ≤ 12 := Int.le_of_dvd (by decide) hd
  have hKle : K ≤ 4*(r:ℤ)^3 := by
    have hp0 : (0:ℤ) ≤ p := by positivity
    have hr0 : (0:ℤ) ≤ r := by positivity
    have hpr' : (p:ℤ) ≤ r := hpr.le
    have hq2 := mul_le_mul hpr' hpr' hp0 hr0
    have h₁ := mul_le_mul_of_nonneg_left hpr' (sq_nonneg (r:ℤ))
    have h₂ := mul_le_mul_of_nonneg_left hq2 hr0
    have h₃ := mul_le_mul hq2 hpr' hp0 (mul_nonneg hr0 hr0)
    dsimp only [K]
    nlinarith only [h₁,h₂,h₃,sq_nonneg (r:ℤ),sq_nonneg (p:ℤ),mul_nonneg hr0 hp0]
  have hFup : (F:ℤ) ≤ 4*(r:ℤ)^3+12 := by
    have hsmall : (F:ℤ)-K ≤ 12 := by
      by_contra! h
      have hh := mul_le_mul_of_nonneg_right (show (1:ℤ) ≤ (r:ℤ)-p by omega)
        (show (0:ℤ) ≤ (F:ℤ)-K by omega)
      nlinarith only [hh,he,show D ≤ 12 by omega,h]
    omega
  have hp10 : p ≤ 10 := by
    by_contra! h
    have h11 : (11:ℤ) ≤ p := by exact_mod_cast h
    have h5 : 5*(r:ℤ) ≤ (p:ℤ)^2 := by
      have hh := mul_nonneg (show 0 ≤ (p:ℤ)-11 by omega) (show 0 ≤ (p:ℤ)+6 by omega)
      nlinarith only [hh,hdiff_le]
    have hh := mul_le_mul_of_nonneg_right h5 (sq_nonneg (r:ℤ))
    have hr3 : (3:ℤ) ≤ r := by omega
    have hr9 : 9 ≤ (r:ℤ)^2 := by
      have := mul_le_mul hr3 hr3 (by decide : (0:ℤ) ≤ 3) (show 0 ≤ (r:ℤ) by omega)
      nlinarith only [this]
    have hr27 : 27 ≤ (r:ℤ)^3 := by
      have := mul_le_mul hr9 hr3 (by decide : (0:ℤ) ≤ 3) (sq_nonneg (r:ℤ))
      nlinarith only [this]
    nlinarith only [hFlow,hFup,hh,hr27]
  have hr22 : r ≤ 22 := by omega
  have pchoices : p=2 ∨ p=3 ∨ p=5 ∨ p=7 := by
    interval_cases p <;> first | decide | (exfalso; exact (by decide : ¬Nat.Prime _) hp)
  have rchoices : r=2 ∨ r=3 ∨ r=5 ∨ r=7 ∨ r=11 ∨ r=13 ∨ r=17 ∨ r=19 := by
    interval_cases r <;> first | decide | (exfalso; exact (by decide : ¬Nat.Prime _) hr)
  rcases pchoices with rp|rp|rp|rp <;> rcases rchoices with rr|rr|rr|rr|rr|rr|rr|rr <;>
    subst p <;> subst r <;> norm_num [K] at he hFD hpr <;> omega

/-- Both orientations of a twelve-step between cube-times-prime four-factor
endpoints are impossible. The totient equation by itself suffices. -/
theorem no_cube_prime_cube_prime_gap_twelve {p q r s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s)
    (hgap : p^3*q+12 = r^3*s ∨ r^3*s+12 = p^3*q)
    (hφ : (p^3*q).totient+r^3*s = (r^3*s).totient+p^3*q) : False := by
  rcases lt_trichotomy p r with h | h | h
  · exact no_ordered_cube_prime_pair hp hq hr hs hpq hrs h hgap hφ
  · subst r
    have h₁ := totient_defect_cube_mul_prime hp hq hpq
    have h₂ := totient_defect_cube_mul_prime hp hs hrs
    have he : p^2*(p+q-1) = p^2*(p+s-1) := by omega
    have he' := Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) he
    have hqs : q=s := by have := hp.pos; omega
    subst s
    omega
  · refine no_ordered_cube_prime_pair hr hs hp hq hrs hpq h ?_ hφ.symm
    exact hgap.symm

end A056777CubePrimeFourFour
end

section
open scoped ArithmeticFunction.sigma
open Nat ArithmeticFunction

namespace A056777CubePrimeSquarefreeFour

private theorem fourth_newton (r s t u : ℤ) :
    8*(r*s+r*t+r*u+s*t+s*u+t*u)*(r*s*t*u) ≤
      3*(r*s*t+r*s*u+r*t*u+s*t*u)^2 := by
  let a := r*s*t
  let b := r*s*u
  let c := r*t*u
  let d := s*t*u
  have h : 8*(a*b+a*c+a*d+b*c+b*d+c*d) ≤ 3*(a+b+c+d)^2 := by
    nlinarith only [sq_nonneg (a-b),sq_nonneg (a-c),sq_nonneg (a-d),
      sq_nonneg (b-c),sq_nonneg (b-d),sq_nonneg (c-d)]
  dsimp [a,b,c,d] at h
  nlinarith only [h]

private theorem middle_newton (r s t u : ℤ) :
    9*(r+s+t+u)*(r*s*t+r*s*u+r*t*u+s*t*u) ≤
      4*(r*s+r*t+r*u+s*t+s*u+t*u)^2 := by
  -- The shared-edge squares carry weight one, and the complementary ones weight four.
  nlinarith only [sq_nonneg (r*s-r*t),sq_nonneg (r*s-r*u),
    sq_nonneg (r*s-s*t),sq_nonneg (r*s-s*u),
    sq_nonneg (r*t-r*u),sq_nonneg (r*t-s*t),sq_nonneg (r*t-t*u),
    sq_nonneg (r*u-s*u),sq_nonneg (r*u-t*u),sq_nonneg (s*t-s*u),
    sq_nonneg (s*t-t*u),sq_nonneg (s*u-t*u),
    sq_nonneg (r*s-t*u),sq_nonneg (r*t-s*u),sq_nonneg (r*u-s*t)]

private theorem pair_cube_bound (r s t u : ℤ)
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) (hu : 0 < u) :
    27*(r*s*t+r*s*u+r*t*u+s*t*u)^2 ≤
      2*(r*s+r*t+r*u+s*t+s*u+t*u)^3 := by
  let a := r+s+t+u
  let x := r*s+r*t+r*u+s*t+s*u+t*u
  let y := r*s*t+r*s*u+r*t*u+s*t*u
  have ha : 0 < a := by dsimp [a]; positivity
  have hx : 0 < x := by dsimp [x]; positivity
  have hy : 0 < y := by dsimp [y]; positivity
  have h₁ : 8*x ≤ 3*a^2 := by
    dsimp [x,a]
    nlinarith only [sq_nonneg (r-s),sq_nonneg (r-t),sq_nonneg (r-u),
      sq_nonneg (s-t),sq_nonneg (s-u),sq_nonneg (t-u)]
  have h₂ : 9*a*y ≤ 4*x^2 := middle_newton r s t u
  have h₂' := pow_le_pow_left₀ (show 0 ≤ 9*a*y by positivity) h₂ 2
  have h₁' := mul_le_mul_of_nonneg_right h₁ (show 0 ≤ 27*y^2 by positivity)
  change 27*y^2 ≤ 2*x^3
  by_contra! h
  have h' := mul_pos (show 0 < 27*y^2-2*x^3 by omega) hx
  nlinarith only [h₂',h₁',h']

private theorem positive_newton_margin (p q : ℤ) (hp : 3 ≤ p) (hq : 4*p+1 ≤ q) :
    let L := (p+1)*(q+1)+2*p^2-2
    0 < 16*L*(p^3*q-12)-3*(2*p^2*(p+q-1)+L)^2 := by
  let a := p-3
  let b := q-4*p-1
  have ha : 0 ≤ a := by dsimp [a]; omega
  have hb : 0 ≤ b := by dsimp [b]; omega
  let P := 4*a^4+52*a^3+237*a^2+444*a+276
  let Q := 40*a^5+644*a^4+3976*a^3+11736*a^2+16188*a+7656
  let R := 84*a^6+1632*a^5+12768*a^4+51480*a^3+111168*a^2+116352*a+39636
  have hpos : 0 < P*b^2+Q*b+R := by dsimp [P,Q,R]; positivity
  dsimp only
  have he : 16*((p+1)*(q+1)+2*p^2-2)*(p^3*q-12)-
      3*(2*p^2*(p+q-1)+((p+1)*(q+1)+2*p^2-2))^2 = P*b^2+Q*b+R := by
    dsimp [P,Q,R,a,b]
    ring
  rw [he]
  exact hpos

private theorem inconsistent_moments (p q x y z : ℤ)
    (hp : 3 ≤ p) (hq : 2 ≤ q) (hx : 0 < x) (hy : 0 < y)
    (hX : 2*x=(p+1)*(q+1)+2*p^2-2)
    (hYlow : p^2*(p+q-1) ≤ y) (hYhigh : y ≤ p^2*(p+q-1)+x)
    (hZ : p^3*q-12 ≤ z)
    (hNewton : 8*x*z ≤ 3*y^2) (hMac : 27*y^2 ≤ 2*x^3) : False := by
  by_cases hqsmall : q ≤ 4*p
  · let S := p+q
    have hp0 : 0 ≤ p := by omega
    have hS : 5 ≤ S := by dsimp [S]; omega
    have hS5 : S ≤ 5*p := by dsimp [S]; omega
    have hxup : x ≤ p*S := by
      dsimp [S]
      have hh := mul_nonneg (show 0 ≤ p-1 by omega) (show 0 ≤ q-1 by omega)
      nlinarith only [hh,hX]
    have hx3 := pow_le_pow_left₀ hx.le hxup 3
    have hupper := mul_le_mul_of_nonneg_left hS5 (show 0 ≤ p^3*S^2 by positivity)
    have hSq : 4*S ≤ 5*(S-1) := by omega
    have hSq2 := pow_le_pow_left₀ (show 0 ≤ 4*S by omega) hSq 2
    have hmid := mul_le_mul_of_nonneg_left hSq2 (show 0 ≤ p^4 by positivity)
    have hy2 := pow_le_pow_left₀ (mul_nonneg (sq_nonneg p) (show 0 ≤ S-1 by omega)) hYlow 2
    nlinarith only [hx3,hupper,hmid,hy2,hMac,sq_pos_of_pos hy]
  · have hlarge : 4*p+1 ≤ q := by omega
    have h := positive_newton_margin p q hp hlarge
    dsimp only at h
    rw [← hX] at h
    have hZ' := mul_le_mul_of_nonneg_left hZ (show 0 ≤ 8*x by omega)
    have hY' := pow_le_pow_left₀ hy.le hYhigh 2
    nlinarith only [h,hZ',hY',hNewton]

/-- Cube-times-prime and a squarefree product of four primes cannot be
twelve apart and satisfy both jump conditions. -/
theorem no_cube_prime_squarefree_four_gap_twelve {p q r s t u : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime) (ht : t.Prime) (hu : u.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s) (hrt : r ≠ t) (hru : r ≠ u) (hst : s ≠ t)
    (hsu : s ≠ u) (htu : t ≠ u)
    (hgap : p^3*q+12 = r*s*t*u ∨ r*s*t*u+12 = p^3*q)
    (hφ : (p^3*q).totient + r*s*t*u = (r*s*t*u).totient + p^3*q)
    (hσ : σ 1 (p^3*q) + r*s*t*u = σ 1 (r*s*t*u) + p^3*q) : False := by
  have hc₁ := (Nat.coprime_primes hr hs).mpr hrs
  have hc₂ := ((Nat.coprime_primes hr ht).mpr hrt).mul_left ((Nat.coprime_primes hs ht).mpr hst)
  have hc₃ := (((Nat.coprime_primes hr hu).mpr hru).mul_left
    ((Nat.coprime_primes hs hu).mpr hsu)).mul_left ((Nat.coprime_primes ht hu).mpr htu)
  by_cases hp2 : p = 2
  · subst p
    have hsq : Squarefree (r*s*t*u) :=
      Nat.squarefree_mul_iff.mpr ⟨hc₃, Nat.squarefree_mul_iff.mpr
        ⟨hc₂, Nat.squarefree_mul_iff.mpr ⟨hc₁,hr.squarefree,hs.squarefree⟩,ht.squarefree⟩,
        hu.squarefree⟩
    have hdiv : 2*2 ∣ r*s*t*u := by norm_num at hgap ⊢; omega
    exact (Nat.squarefree_iff_prime_squarefree.mp hsq 2 Nat.prime_two) hdiv
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hcp := ((Nat.coprime_primes hp hq).mpr hpq).pow_left 3
  have hσp {a : ℕ} (ha : a.Prime) : σ 1 a = a+1 := by
    simpa using sigma_one_apply_prime_pow (i := 1) ha
  have hσpp : σ 1 (p^3) = 1+p+p^2+p^3 := by
    simp only [sigma_one_apply_prime_pow hp, Finset.sum_range_succ, Finset.sum_range_zero,
      pow_zero,pow_one,zero_add]
  have hφpp : (p^3).totient = p^2*(p-1) := Nat.totient_prime_pow_succ hp 2
  rw [Nat.totient_mul hcp,hφpp,Nat.totient_prime hq,Nat.totient_mul hc₃,Nat.totient_mul hc₂,
    Nat.totient_mul hc₁,Nat.totient_prime hr,Nat.totient_prime hs,Nat.totient_prime ht,
    Nat.totient_prime hu] at hφ
  rw [isMultiplicative_sigma.map_mul_of_coprime hcp,hσpp,hσp hq,
    isMultiplicative_sigma.map_mul_of_coprime hc₃,isMultiplicative_sigma.map_mul_of_coprime hc₂,
    isMultiplicative_sigma.map_mul_of_coprime hc₁,hσp hr,hσp hs,hσp ht,hσp hu] at hσ
  have hpr := hp.pos
  have hqr := hq.pos
  have hrr := hr.pos
  have hsr := hs.pos
  have htr := ht.pos
  have hur := hu.pos
  have hq2 := hq.two_le
  have hr2 := hr.two_le
  have hs2 := hs.two_le
  have ht2 := ht.two_le
  have hu2 := hu.two_le
  have hg : p^3*q ≤ r*s*t*u+12 := by omega
  zify [hpr,hqr,hrr,hsr,htr,hur] at hp3 hq2 hr2 hs2 ht2 hu2 hg hφ hσ
  let a : ℤ := r+s+t+u
  let x : ℤ := r*s+r*t+r*u+s*t+s*u+t*u
  let y : ℤ := r*s*t+r*s*u+r*t*u+s*t*u
  let z : ℤ := r*s*t*u
  have hX : 2*x=((p:ℤ)+1)*(q+1)+2*(p:ℤ)^2-2 := by dsimp [x]; nlinarith only [hφ,hσ]
  have hY : y=(p:ℤ)^2*(p+q-1)+x-a+1 := by dsimp [a,x,y]; nlinarith only [hφ]
  have ha1 : 1 ≤ a := by dsimp [a]; omega
  have hax : a ≤ x := by
    dsimp [a,x]
    have h₁ := mul_nonneg (show 0 ≤ (r:ℤ)-2 by omega) (show 0 ≤ (s:ℤ)-1 by omega)
    have h₂ := mul_nonneg (show 0 ≤ (t:ℤ)-2 by omega) (show 0 ≤ (u:ℤ)-1 by omega)
    have h₃ : 0 ≤ (r:ℤ)*t+(r:ℤ)*u+(s:ℤ)*t+(s:ℤ)*u := by positivity
    nlinarith only [h₁,h₂,h₃,hs2,hu2]
  have hx : 0 < x := by
    dsimp [x]
    have hrr' : (0:ℤ)<r := by omega
    have hss' : (0:ℤ)<s := by omega
    have htt' : (0:ℤ)<t := by omega
    have huu' : (0:ℤ)<u := by omega
    positivity
  have hy : 0 < y := by
    dsimp [y]
    have hrr' : (0:ℤ)<r := by omega
    have hss' : (0:ℤ)<s := by omega
    have htt' : (0:ℤ)<t := by omega
    have huu' : (0:ℤ)<u := by omega
    positivity
  exact inconsistent_moments p q x y z hp3 hq2 hx hy hX (by omega) (by omega)
    (by dsimp [z]; omega) (fourth_newton r s t u)
    (pair_cube_bound r s t u (by omega) (by omega) (by omega) (by omega))

end A056777CubePrimeSquarefreeFour
end

section
open scoped ArithmeticFunction.sigma
open Nat

/-- The only remaining four-factor partner for p³q is r²st with three distinct
prime bases on the partner side. Either endpoint can be smaller. -/
theorem A056777.cube_prime_four_partner_shape {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hm : m.primeFactorsList.length = 4)
    (hgap : p^3*q+12=m ∨ m+12=p^3*q)
    (hφ : (p^3*q).totient+m=m.totient+p^3*q)
    (hσ : σ 1 (p^3*q)+m = σ 1 m+p^3*q) :
    ∃ r s t : ℕ, r.Prime ∧ s.Prime ∧ t.Prime ∧
      r ≠ s ∧ r ≠ t ∧ s ≠ t ∧ m = r^2*s*t := by
  rcases A056777CubeFour.four_factor_shape hm with ⟨k,hk⟩ | ⟨r,s,hr,hs,hrs,hm'⟩ |
    h | ⟨r,s,t,u,hr,hs,ht,hu,hrs,hrt,hru,hst,hsu,htu,hm'⟩
  · exfalso
    rcases hgap with he | he
    · have hste : σ 1 (p^3*q+12)=σ 1 (p^3*q)+12 := by rw [he]; omega
      have hn0 : p^3*q ≠ 0 := mul_ne_zero (pow_ne_zero _ hp.ne_zero) hq.ne_zero
      exact (A056777Parity.no_square_shapes_of_sigma_step hn0 hste).2 (Or.inl ⟨k,he.trans hk⟩)
    · have hste : σ 1 (m+12)=σ 1 m+12 := by rw [he]; omega
      have hm0 : m ≠ 0 := by rintro rfl; simp at hm
      exact (A056777Parity.no_square_shapes_of_sigma_step hm0 hste).1 (Or.inl ⟨k,hk⟩)
  · rw [hm'] at hgap hφ
    exact (A056777CubePrimeFourFour.no_cube_prime_cube_prime_gap_twelve hp hq hr hs
      hpq hrs hgap hφ).elim
  · exact h
  · rw [hm'] at hgap hφ hσ
    exact (A056777CubePrimeSquarefreeFour.no_cube_prime_squarefree_four_gap_twelve hp hq hr hs ht hu
      hpq hrs hrt hru hst hsu htu hgap hφ hσ).elim
end

section
open scoped ArithmeticFunction.sigma
open Nat ArithmeticFunction

namespace A056777CubePrimeRepeatedFour

private theorem moment_equations (p q r A B D : ℤ)
    (hK : (p+1)*(q+1)+2*p^2-(B+(2*r+1)*A+2*r^2+1)=0)
    (hF : p^2*(p+q-1)-r*B-r*(r-1)*(A-1)=0)
    (hG : r^2*B-p^3*q-D=0) :
    (r*(p^3*r+2*p^3-2*p^2*r^2-p^2*r+p*r^3-p*r^2+r^3-r^2)) * A = (p^2*r*(p-r)*(p+2*p^2-2*r^2)-(p^3-p*r^2-r^2)*(p^2*(p-1)+r*(r-1))+(p^2-p*r-r)*D) ∧
      (r*(p^3*r+2*p^3-2*p^2*r^2-p^2*r+p*r^3-p*r^2+r^3-r^2)) * B = (-p^3*r*(r-1)*(p+2*p^2-2*r^2)+p^3*(2*r+1)*(p^2*(p-1)+r*(r-1))+(-2*p^2*r-p^2+p*r^2-p*r+r^2-r)*D) := by
  constructor
  ·     linear_combination (-p^2*r*(p-r))*hK+(p^3-p*r^2-r^2)*hF+(p^2-p*r-r)*hG
  ·     linear_combination (p^3*r*(r-1))*hK+(-p^3*(2*r+1))*hF+
      (-2*p^2*r-p^2+p*r^2-p*r+r^2-r)*hG

/- The following five certificates are Horner decompositions after shifting the
two repeated bases into the appropriate nonnegative quadrant. The ring tactic
verifies each displayed polynomial identity over the integers. -/
private theorem negative_disc_positive_gap (U V : ℤ) (hU : 0 ≤ U) (hV : 0 ≤ V) :
    (((U+3)^2*(U+3+V)*((U+3)-(U+3+V))*((U+3)+2*(U+3)^2-2*(U+3+V)^2)-((U+3)^3-(U+3)*(U+3+V)^2-(U+3+V)^2)*((U+3)^2*((U+3)-1)+(U+3+V)*((U+3+V)-1))+((U+3)^2-(U+3)*(U+3+V)-(U+3+V))*(12))^2-4*(-(U+3)^3*(U+3+V)*((U+3+V)-1)*((U+3)+2*(U+3)^2-2*(U+3+V)^2)+(U+3)^3*(2*(U+3+V)+1)*((U+3)^2*((U+3)-1)+(U+3+V)*((U+3+V)-1))+(-2*(U+3)^2*(U+3+V)-(U+3)^2+(U+3)*(U+3+V)^2-(U+3)*(U+3+V)+(U+3+V)^2-(U+3+V))*(12))*((U+3+V)*((U+3)^3*(U+3+V)+2*(U+3)^3-2*(U+3)^2*(U+3+V)^2-(U+3)^2*(U+3+V)+(U+3)*(U+3+V)^3-(U+3)*(U+3+V)^2+(U+3+V)^3-(U+3+V)^2))) < 0 := by
  let c0 : ℤ := 741312+U*(3034368+U*(5533776+U*(5968800+U*(4246287+U*(2097558+U*(735569+U*(183388+U*(31889+U*(3686+U*(255+U*(8)))))))))))
  let c1 : ℤ := 644544+U*(2369664+U*(3961800+U*(3934572+U*(2556642+U*(1132638+U*(346120+U*(72040+U*(9778+U*(782+U*(28))))))))))
  let c2 : ℤ := 597744+U*(2113488+U*(3307176+U*(3006378+U*(1751721+U*(680794+U*(177738+U*(30506+U*(3241+U*(186+U*(4))))))))))
  let c3 : ℤ := 472464+U*(1543200+U*(2191140+U*(1775044+U*(903130+U*(298728+U*(64052+U*(8544+U*(638+U*(20)))))))))
  let c4 : ℤ := 322764+U*(904620+U*(1104219+U*(760428+U*(321462+U*(85138+U*(13758+U*(1236+U*(47))))))))
  let c5 : ℤ := 163944+U*(390672+U*(398602+U*(223550+U*(74040+U*(14440+U*(1532+U*(68)))))))
  let c6 : ℤ := 47684+U*(96252+U*(80257+U*(35180+U*(8528+U*(1082+U*(56))))))
  let c7 : ℤ := 6920+U*(11600+U*(7622+U*(2456+U*(388+U*(24)))))
  let c8 : ℤ := 380+U*(508+U*(247+U*(52+U*(4))))
  have hpos : 0 < c0+V*(c1+V*(c2+V*(c3+V*(c4+V*(c5+V*(c6+V*(c7+V*(c8)))))))) := by
    dsimp [c0, c1, c2, c3, c4, c5, c6, c7, c8]
    positivity
  have he : -((((U+3)^2*(U+3+V)*((U+3)-(U+3+V))*((U+3)+2*(U+3)^2-2*(U+3+V)^2)-((U+3)^3-(U+3)*(U+3+V)^2-(U+3+V)^2)*((U+3)^2*((U+3)-1)+(U+3+V)*((U+3+V)-1))+((U+3)^2-(U+3)*(U+3+V)-(U+3+V))*(12))^2-4*(-(U+3)^3*(U+3+V)*((U+3+V)-1)*((U+3)+2*(U+3)^2-2*(U+3+V)^2)+(U+3)^3*(2*(U+3+V)+1)*((U+3)^2*((U+3)-1)+(U+3+V)*((U+3+V)-1))+(-2*(U+3)^2*(U+3+V)-(U+3)^2+(U+3)*(U+3+V)^2-(U+3)*(U+3+V)+(U+3+V)^2-(U+3+V))*(12))*((U+3+V)*((U+3)^3*(U+3+V)+2*(U+3)^3-2*(U+3)^2*(U+3+V)^2-(U+3)^2*(U+3+V)+(U+3)*(U+3+V)^3-(U+3)*(U+3+V)^2+(U+3+V)^3-(U+3+V)^2)))) = c0+V*(c1+V*(c2+V*(c3+V*(c4+V*(c5+V*(c6+V*(c7+V*(c8)))))))) := by
    dsimp [c0, c1, c2, c3, c4, c5, c6, c7, c8]
    ring
  rw [← he] at hpos
  exact neg_pos.mp hpos

private theorem negative_sum_positive_gap (U V : ℤ) (hU : 0 ≤ U) (hV : 0 ≤ V) :
    ((U+3+1+V)^2*(U+3)*((U+3+1+V)-(U+3))*((U+3+1+V)+2*(U+3+1+V)^2-2*(U+3)^2)-((U+3+1+V)^3-(U+3+1+V)*(U+3)^2-(U+3)^2)*((U+3+1+V)^2*((U+3+1+V)-1)+(U+3)*((U+3)-1))+((U+3+1+V)^2-(U+3+1+V)*(U+3)-(U+3))*(12)) < 0 := by
  let c0 : ℤ := 150+U*(381+U*(289+U*(99+U*(16+U*(1)))))
  let c1 : ℤ := 694+U*(1289+U*(830+U*(250+U*(36+U*(2)))))
  let c2 : ℤ := 599+U*(745+U*(340+U*(68+U*(5))))
  let c3 : ℤ := 325+U*(249+U*(66+U*(6)))
  let c4 : ℤ := 106+U*(50+U*(6))
  let c5 : ℤ := 17+U*(4)
  let c6 : ℤ := 1
  have hpos : 0 < c0+V*(c1+V*(c2+V*(c3+V*(c4+V*(c5+V*(c6)))))) := by
    dsimp [c0, c1, c2, c3, c4, c5, c6]
    positivity
  have he : -(((U+3+1+V)^2*(U+3)*((U+3+1+V)-(U+3))*((U+3+1+V)+2*(U+3+1+V)^2-2*(U+3)^2)-((U+3+1+V)^3-(U+3+1+V)*(U+3)^2-(U+3)^2)*((U+3+1+V)^2*((U+3+1+V)-1)+(U+3)*((U+3)-1))+((U+3+1+V)^2-(U+3+1+V)*(U+3)-(U+3))*(12))) = c0+V*(c1+V*(c2+V*(c3+V*(c4+V*(c5+V*(c6)))))) := by
    dsimp [c0, c1, c2, c3, c4, c5, c6]
    ring
  rw [← he] at hpos
  exact neg_pos.mp hpos

private theorem negative_disc_negative_gap (U V : ℤ) (hU : 0 ≤ U) (hV : 0 ≤ V) :
    (((U+3)^2*(U+3+V)*((U+3)-(U+3+V))*((U+3)+2*(U+3)^2-2*(U+3+V)^2)-((U+3)^3-(U+3)*(U+3+V)^2-(U+3+V)^2)*((U+3)^2*((U+3)-1)+(U+3+V)*((U+3+V)-1))+((U+3)^2-(U+3)*(U+3+V)-(U+3+V))*(-12))^2-4*(-(U+3)^3*(U+3+V)*((U+3+V)-1)*((U+3)+2*(U+3)^2-2*(U+3+V)^2)+(U+3)^3*(2*(U+3+V)+1)*((U+3)^2*((U+3)-1)+(U+3+V)*((U+3+V)-1))+(-2*(U+3)^2*(U+3+V)-(U+3)^2+(U+3)*(U+3+V)^2-(U+3)*(U+3+V)+(U+3+V)^2-(U+3+V))*(-12))*((U+3+V)*((U+3)^3*(U+3+V)+2*(U+3)^3-2*(U+3)^2*(U+3+V)^2-(U+3)^2*(U+3+V)+(U+3)*(U+3+V)^3-(U+3)*(U+3+V)^2+(U+3+V)^3-(U+3+V)^2))) < 0 := by
  let c0 : ℤ := 912384+U*(3449088+U*(5962752+U*(6214464+U*(4330479+U*(2114838+U*(737537+U*(183484+U*(31889+U*(3686+U*(255+U*(8)))))))))))
  let c1 : ℤ := 514944+U*(2144160+U*(3800664+U*(3874476+U*(2544450+U*(1131390+U*(346072+U*(72040+U*(9778+U*(782+U*(28))))))))))
  let c2 : ℤ := 532944+U*(2009376+U*(3240792+U*(2985498+U*(1748505+U*(680602+U*(177738+U*(30506+U*(3241+U*(186+U*(4))))))))))
  let c3 : ℤ := 433008+U*(1482096+U*(2155716+U*(1765540+U*(901978+U*(298680+U*(64052+U*(8544+U*(638+U*(20)))))))))
  let c4 : ℤ := 276204+U*(849660+U*(1080699+U*(756108+U*(321174+U*(85138+U*(13758+U*(1236+U*(47))))))))
  let c5 : ℤ := 148968+U*(378288+U*(395290+U*(223262+U*(74040+U*(14440+U*(1532+U*(68)))))))
  let c6 : ℤ := 46148+U*(95484+U*(80161+U*(35180+U*(8528+U*(1082+U*(56))))))
  let c7 : ℤ := 6920+U*(11600+U*(7622+U*(2456+U*(388+U*(24)))))
  let c8 : ℤ := 380+U*(508+U*(247+U*(52+U*(4))))
  have hpos : 0 < c0+V*(c1+V*(c2+V*(c3+V*(c4+V*(c5+V*(c6+V*(c7+V*(c8)))))))) := by
    dsimp [c0, c1, c2, c3, c4, c5, c6, c7, c8]
    positivity
  have he : -((((U+3)^2*(U+3+V)*((U+3)-(U+3+V))*((U+3)+2*(U+3)^2-2*(U+3+V)^2)-((U+3)^3-(U+3)*(U+3+V)^2-(U+3+V)^2)*((U+3)^2*((U+3)-1)+(U+3+V)*((U+3+V)-1))+((U+3)^2-(U+3)*(U+3+V)-(U+3+V))*(-12))^2-4*(-(U+3)^3*(U+3+V)*((U+3+V)-1)*((U+3)+2*(U+3)^2-2*(U+3+V)^2)+(U+3)^3*(2*(U+3+V)+1)*((U+3)^2*((U+3)-1)+(U+3+V)*((U+3+V)-1))+(-2*(U+3)^2*(U+3+V)-(U+3)^2+(U+3)*(U+3+V)^2-(U+3)*(U+3+V)+(U+3+V)^2-(U+3+V))*(-12))*((U+3+V)*((U+3)^3*(U+3+V)+2*(U+3)^3-2*(U+3)^2*(U+3+V)^2-(U+3)^2*(U+3+V)+(U+3)*(U+3+V)^3-(U+3)*(U+3+V)^2+(U+3+V)^3-(U+3+V)^2)))) = c0+V*(c1+V*(c2+V*(c3+V*(c4+V*(c5+V*(c6+V*(c7+V*(c8)))))))) := by
    dsimp [c0, c1, c2, c3, c4, c5, c6, c7, c8]
    ring
  rw [← he] at hpos
  exact neg_pos.mp hpos

private theorem negative_sum_negative_gap (U V : ℤ) (hU : 0 ≤ U) (hV : 0 ≤ V) :
    ((U+3+1+V)^2*(U+3)*((U+3+1+V)-(U+3))*((U+3+1+V)+2*(U+3+1+V)^2-2*(U+3)^2)-((U+3+1+V)^3-(U+3+1+V)*(U+3)^2-(U+3)^2)*((U+3+1+V)^2*((U+3+1+V)-1)+(U+3)*((U+3)-1))+((U+3+1+V)^2-(U+3+1+V)*(U+3)-(U+3))*(-12)) < 0 := by
  let c0 : ℤ := 174+U*(381+U*(289+U*(99+U*(16+U*(1)))))
  let c1 : ℤ := 814+U*(1313+U*(830+U*(250+U*(36+U*(2)))))
  let c2 : ℤ := 623+U*(745+U*(340+U*(68+U*(5))))
  let c3 : ℤ := 325+U*(249+U*(66+U*(6)))
  let c4 : ℤ := 106+U*(50+U*(6))
  let c5 : ℤ := 17+U*(4)
  let c6 : ℤ := 1
  have hpos : 0 < c0+V*(c1+V*(c2+V*(c3+V*(c4+V*(c5+V*(c6)))))) := by
    dsimp [c0, c1, c2, c3, c4, c5, c6]
    positivity
  have he : -(((U+3+1+V)^2*(U+3)*((U+3+1+V)-(U+3))*((U+3+1+V)+2*(U+3+1+V)^2-2*(U+3)^2)-((U+3+1+V)^3-(U+3+1+V)*(U+3)^2-(U+3)^2)*((U+3+1+V)^2*((U+3+1+V)-1)+(U+3)*((U+3)-1))+((U+3+1+V)^2-(U+3+1+V)*(U+3)-(U+3))*(-12))) = c0+V*(c1+V*(c2+V*(c3+V*(c4+V*(c5+V*(c6)))))) := by
    dsimp [c0, c1, c2, c3, c4, c5, c6]
    ring
  rw [← he] at hpos
  exact neg_pos.mp hpos

private theorem positive_determinant (U V : ℤ) (hU : 0 ≤ U) (hV : 0 ≤ V) :
    0 < ((U+3)*((U+3+1+V)^3*(U+3)+2*(U+3+1+V)^3-2*(U+3+1+V)^2*(U+3)^2-(U+3+1+V)^2*(U+3)+(U+3+1+V)*(U+3)^3-(U+3+1+V)*(U+3)^2+(U+3)^3-(U+3)^2)) := by
  let c0 : ℤ := 222+U*(227+U*(87+U*(15+U*(1))))
  let c1 : ℤ := 270+U*(219+U*(58+U*(5)))
  let c2 : ℤ := 117+U*(81+U*(17+U*(1)))
  let c3 : ℤ := 15+U*(8+U*(1))
  have hpos : 0 < c0+V*(c1+V*(c2+V*(c3))) := by
    dsimp [c0, c1, c2, c3]
    positivity
  have he : ((U+3)*((U+3+1+V)^3*(U+3)+2*(U+3+1+V)^3-2*(U+3+1+V)^2*(U+3)^2-(U+3+1+V)^2*(U+3)+(U+3+1+V)*(U+3)^3-(U+3+1+V)*(U+3)^2+(U+3)^3-(U+3)^2)) = c0+V*(c1+V*(c2+V*(c3))) := by
    dsimp [c0, c1, c2, c3]
    ring
  rw [← he] at hpos
  exact hpos

private theorem impossible_moments (p q r A B D : ℤ)
    (hp : 3 ≤ p) (hr : 3 ≤ r) (hA : 0 ≤ A) (hdisc : 4*B ≤ A^2)
    (hD : D=12 ∨ D=-12)
    (hK : (p+1)*(q+1)+2*p^2-(B+(2*r+1)*A+2*r^2+1)=0)
    (hF : p^2*(p+q-1)-r*B-r*(r-1)*(A-1)=0)
    (hG : r^2*B-p^3*q-D=0) : False := by
  obtain ⟨hS,hP⟩ := moment_equations p q r A B D hK hF hG
  by_cases hpr : p ≤ r
  · let U := p-3
    let V := r-p
    have hU : 0 ≤ U := by dsimp [U]; omega
    have hV : 0 ≤ V := by dsimp [V]; omega
    have hbase : U+3=p := by dsimp [U]; omega
    have hbase' : U+3+V=r := by dsimp [U,V]; omega
    have hneg : ((p^2*r*(p-r)*(p+2*p^2-2*r^2)-(p^3-p*r^2-r^2)*(p^2*(p-1)+r*(r-1))+(p^2-p*r-r)*D)^2-4*(-p^3*r*(r-1)*(p+2*p^2-2*r^2)+p^3*(2*r+1)*(p^2*(p-1)+r*(r-1))+(-2*p^2*r-p^2+p*r^2-p*r+r^2-r)*D)*(r*(p^3*r+2*p^3-2*p^2*r^2-p^2*r+p*r^3-p*r^2+r^3-r^2))) < 0 := by
      rcases hD with rfl | rfl
      · have h := negative_disc_positive_gap U V hU hV
        rw [hbase',hbase] at h
        exact h
      · have h := negative_disc_negative_gap U V hU hV
        rw [hbase',hbase] at h
        exact h
    have hnneg : 0 ≤ ((p^2*r*(p-r)*(p+2*p^2-2*r^2)-(p^3-p*r^2-r^2)*(p^2*(p-1)+r*(r-1))+(p^2-p*r-r)*D)^2-4*(-p^3*r*(r-1)*(p+2*p^2-2*r^2)+p^3*(2*r+1)*(p^2*(p-1)+r*(r-1))+(-2*p^2*r-p^2+p*r^2-p*r+r^2-r)*D)*(r*(p^3*r+2*p^3-2*p^2*r^2-p^2*r+p*r^3-p*r^2+r^3-r^2))) := by
      rw [← hS,← hP]
      have he : ((r*(p^3*r+2*p^3-2*p^2*r^2-p^2*r+p*r^3-p*r^2+r^3-r^2))*A)^2-4*((r*(p^3*r+2*p^3-2*p^2*r^2-p^2*r+p*r^3-p*r^2+r^3-r^2))*B)*(r*(p^3*r+2*p^3-2*p^2*r^2-p^2*r+p*r^3-p*r^2+r^3-r^2)) =
          ((r*(p^3*r+2*p^3-2*p^2*r^2-p^2*r+p*r^3-p*r^2+r^3-r^2)))^2*(A^2-4*B) := by ring
      rw [he]
      exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hdisc)
    exact (not_lt_of_ge hnneg) hneg
  · let U := r-3
    let V := p-r-1
    have hU : 0 ≤ U := by dsimp [U]; omega
    have hV : 0 ≤ V := by dsimp [V]; omega
    have hbase : U+3=r := by dsimp [U]; omega
    have hbase' : U+3+1+V=p := by dsimp [U,V]; omega
    have hpos := positive_determinant U V hU hV
    rw [hbase',hbase] at hpos
    have hneg : (p^2*r*(p-r)*(p+2*p^2-2*r^2)-(p^3-p*r^2-r^2)*(p^2*(p-1)+r*(r-1))+(p^2-p*r-r)*D) < 0 := by
      rcases hD with rfl | rfl
      · have h := negative_sum_positive_gap U V hU hV
        rw [hbase',hbase] at h
        exact h
      · have h := negative_sum_negative_gap U V hU hV
        rw [hbase',hbase] at h
        exact h
    exact (not_lt_of_ge ((hS ▸ mul_nonneg hpos.le hA) : 0 ≤ (p^2*r*(p-r)*(p+2*p^2-2*r^2)-(p^3-p*r^2-r^2)*(p^2*(p-1)+r*(r-1))+(p^2-p*r-r)*D))) hneg

private theorem exclude_two_bases {q s t : ℕ} (hq : q.Prime) (hs : s.Prime) (ht : t.Prime)
    (hq2 : q ≠ 2) (hs2 : s ≠ 2) (ht2 : t ≠ 2) (hst : s ≠ t)
    (hgap : 2^3*q+12=2^2*s*t ∨ 2^2*s*t+12=2^3*q)
    (hφ : (2^3*q).totient+2^2*s*t = (2^2*s*t).totient+2^3*q) : False := by
  have hcq := ((Nat.coprime_primes Nat.prime_two hq).mpr hq2.symm).pow_left 3
  have hcs := ((Nat.coprime_primes Nat.prime_two hs).mpr hs2.symm).pow_left 2
  have hct := (((Nat.coprime_primes Nat.prime_two ht).mpr ht2.symm).pow_left 2).mul_left
    ((Nat.coprime_primes hs ht).mpr hst)
  rw [Nat.totient_mul hcq,Nat.totient_mul hct,Nat.totient_mul hcs,
    show ((2:ℕ)^3).totient=4 by decide,show ((2:ℕ)^2).totient=2 by decide,
    Nat.totient_prime hq,Nat.totient_prime hs,Nat.totient_prime ht] at hφ
  have hq1 := hq.pos
  have hs1 := hs.pos
  have ht1 := ht.pos
  have hs3 : 3 ≤ s := by have := hs.two_le; omega
  have ht3 : 3 ≤ t := by have := ht.two_le; omega
  zify [hq1,hs1,ht1] at hφ hgap hs3 ht3
  norm_num at hφ hgap
  have he : (s:ℤ)+t ≤ 6 := by
    rcases hgap with h | h <;> nlinarith only [hφ,h]
  omega

/-- The last cube-times-prime versus four-factor shape is impossible.
Both orientations of the twelve-step are covered. -/
theorem no_cube_prime_square_two_primes_gap_twelve {p q r s t : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (hgap : p^3*q+12=r^2*s*t ∨ r^2*s*t+12=p^3*q)
    (hφ : (p^3*q).totient+r^2*s*t = (r^2*s*t).totient+p^3*q)
    (hσ : σ 1 (p^3*q)+r^2*s*t = σ 1 (r^2*s*t)+p^3*q) : False := by
  by_cases hp2 : p=2
  · subst p
    by_cases hr2 : r=2
    · subst r
      exact exclude_two_bases hq hs ht hpq.symm hrs.symm hrt.symm hst hgap hφ
    · have hd : 4 ∣ r^2*(s*t) := by
        rw [← mul_assoc]
        norm_num at hgap
        omega
      have hcop := (((Nat.coprime_primes Nat.prime_two hr).mpr (Ne.symm hr2)).pow_left 2).pow_right 2
      have hd' : 4 ∣ s*t := hcop.dvd_of_dvd_mul_left hd
      have hsfree : Squarefree (s*t) :=
        Nat.squarefree_mul_iff.mpr ⟨(Nat.coprime_primes hs ht).mpr hst,hs.squarefree,ht.squarefree⟩
      exact (Nat.squarefree_iff_prime_squarefree.mp hsfree 2 Nat.prime_two) hd'
  by_cases hr2 : r=2
  · subst r
    have hd : 4 ∣ p^3*q := by
      norm_num at hgap
      simp only [mul_assoc] at hgap
      omega
    have hcop := (((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)).pow_left 2).pow_right 3
    have hd' : 4 ∣ q := hcop.dvd_of_dvd_mul_left hd
    rcases (Nat.dvd_prime hq).mp hd' with h | h
    · omega
    · have hn : ¬ Nat.Prime 4 := by decide
      exact hn (h.symm ▸ hq)
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hr3 : 3 ≤ r := by have := hr.two_le; omega
  have hcp := ((Nat.coprime_primes hp hq).mpr hpq).pow_left 3
  have hcrs := ((Nat.coprime_primes hr hs).mpr hrs).pow_left 2
  have hcrt := (((Nat.coprime_primes hr ht).mpr hrt).pow_left 2).mul_left
    ((Nat.coprime_primes hs ht).mpr hst)
  have hSigma {a : ℕ} (ha : a.Prime) : σ 1 a = a+1 := by
    simpa using sigma_one_apply_prime_pow (i := 1) ha
  have hSigma2 : σ 1 (r^2) = 1+r+r^2 := by
    simp only [sigma_one_apply_prime_pow hr,Finset.sum_range_succ,Finset.sum_range_zero,
      pow_zero,pow_one,zero_add]
  have hSigma3 : σ 1 (p^3) = 1+p+p^2+p^3 := by
    simp only [sigma_one_apply_prime_pow hp,Finset.sum_range_succ,Finset.sum_range_zero,
      pow_zero,pow_one,zero_add]
  have hPhi2 : (r^2).totient = r*(r-1) := by simpa using Nat.totient_prime_pow_succ hr 1
  have hPhi3 : (p^3).totient = p^2*(p-1) := Nat.totient_prime_pow_succ hp 2
  rw [Nat.totient_mul hcp,Nat.totient_mul hcrt,Nat.totient_mul hcrs,hPhi3,hPhi2,
    Nat.totient_prime hq,Nat.totient_prime hs,Nat.totient_prime ht] at hφ
  rw [isMultiplicative_sigma.map_mul_of_coprime hcp,isMultiplicative_sigma.map_mul_of_coprime hcrt,
    isMultiplicative_sigma.map_mul_of_coprime hcrs,hSigma3,hSigma2,hSigma hq,hSigma hs,hSigma ht] at hσ
  have hp1 := hp.pos
  have hq1 := hq.pos
  have hr1 := hr.pos
  have hs1 := hs.pos
  have ht1 := ht.pos
  zify [hp1,hq1,hr1,hs1,ht1] at hp3 hr3 hφ hσ hgap
  let D : ℤ := (r:ℤ)^2*s*t-(p:ℤ)^3*q
  have hD : D=12 ∨ D=-12 := by dsimp [D]; omega
  exact impossible_moments p q r (s+t) (s*t) D hp3 hr3 (by positivity)
    (by nlinarith only [sq_nonneg ((s:ℤ)-t)]) hD
    (by nlinarith only [hφ,hσ]) (by nlinarith only [hφ]) (by dsimp [D]; ring)

end A056777CubePrimeRepeatedFour
end

section
open scoped ArithmeticFunction.sigma

/-- A cube-times-prime endpoint cannot satisfy the A056777 jump conditions
with any endpoint having exactly four prime factors counted with multiplicity.
Either endpoint can be smaller. -/
theorem A056777.no_cube_prime_four_partner {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hm : m.primeFactorsList.length = 4)
    (hgap : p^3*q+12=m ∨ m+12=p^3*q)
    (hφ : (p^3*q).totient+m=m.totient+p^3*q)
    (hσ : σ 1 (p^3*q)+m=σ 1 m+p^3*q) : False := by
  obtain ⟨r,s,t,hr,hs,ht,hrs,hrt,hst,hm'⟩ :=
    A056777.cube_prime_four_partner_shape hp hq hpq hm hgap hφ hσ
  rw [hm'] at hgap hφ hσ
  exact A056777CubePrimeRepeatedFour.no_cube_prime_square_two_primes_gap_twelve
    hp hq hr hs ht hpq hrs hrt hst hgap hφ hσ
end

section
open scoped ArithmeticFunction.sigma

namespace A056777FourFour

theorem repeated_not_squarefree {n : ℕ} (h : (∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ n = p^2*q*r)) : ¬Squarefree n := by
  obtain ⟨p,q,r,hp,_,_,_,_,_,rfl⟩ := h
  intro hsq
  exact (Nat.squarefree_iff_prime_squarefree.mp hsq p hp) ⟨q*r,by ring⟩

private theorem squarefree_or_repeated {n m : ℕ}
    (hn : n.primeFactorsList.length = 4) (hm : m.primeFactorsList.length = 4)
    (hgap : n+12=m ∨ m+12=n)
    (hφ : n.totient+m=m.totient+n) (hσ : σ 1 n+m = σ 1 m+n) :
    Squarefree n ∨ (∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ n = p^2*q*r) := by
  rcases A056777CubeFour.four_factor_shape hn with ⟨k,hk⟩ | ⟨p,q,hp,hq,hpq,hn'⟩ |
    h | ⟨p,q,r,s,hp,hq,hr,hs,hpq,hpr,hps,hqr,hqs,hrs,hn'⟩
  · have hn0 : n ≠ 0 := by rintro rfl; simp at hn
    have hm0 : m ≠ 0 := by rintro rfl; simp at hm
    exfalso
    rcases hgap with he | he
    · have hstep : σ 1 (n+12)=σ 1 n+12 := by rw [he]; omega
      exact (A056777Parity.no_square_shapes_of_sigma_step hn0 hstep).1 (Or.inl ⟨k,hk⟩)
    · have hstep : σ 1 (m+12)=σ 1 m+12 := by rw [he]; omega
      exact (A056777Parity.no_square_shapes_of_sigma_step hm0 hstep).2
        (Or.inl ⟨k,he.trans hk⟩)
  · exfalso
    rw [hn'] at hgap hφ hσ
    exact A056777.no_cube_prime_four_partner hp hq hpq hm hgap hφ hσ
  · exact Or.inr h
  · left
    rw [hn']
    have hc₁ := (Nat.coprime_primes hp hq).mpr hpq
    have hc₂ := ((Nat.coprime_primes hp hr).mpr hpr).mul_left
      ((Nat.coprime_primes hq hr).mpr hqr)
    have hc₃ := (((Nat.coprime_primes hp hs).mpr hps).mul_left
      ((Nat.coprime_primes hq hs).mpr hqs)).mul_left ((Nat.coprime_primes hr hs).mpr hrs)
    exact Nat.squarefree_mul_iff.mpr ⟨hc₃,Nat.squarefree_mul_iff.mpr
      ⟨hc₂,Nat.squarefree_mul_iff.mpr ⟨hc₁,hp.squarefree,hq.squarefree⟩,hr.squarefree⟩,
      hs.squarefree⟩

private theorem no_squarefree_squarefree {n : ℕ}
    (hn : n.primeFactorsList.length = 4) (h₁ : Squarefree n) (h₂ : Squarefree (n+12))
    (hφ : (n+12).totient=n.totient+12) (hσ : σ 1 (n+12)=σ 1 n+12) : False := by
  have hn' : 1 < n := by
    by_contra! h
    interval_cases n <;> simp at hn
  have hnnp : ¬n.Prime := by intro hp; simp [Nat.primeFactorsList_prime hp] at hn
  obtain ⟨p,hp,_,_,hp',he⟩ :=
    A056777Squarefree.prime_quadruple_of_squarefree_pair hn' hnnp h₁ h₂ hφ hσ
  have hh := (Nat.perm_primeFactorsList_mul hp.ne_zero hp'.ne_zero).length_eq
  rw [← he,Nat.primeFactorsList_prime hp,Nat.primeFactorsList_prime hp'] at hh
  simp [hn] at hh

/-- Both endpoints have one of the two stated factorization shapes, and at least one is
a square times two other distinct primes. This is the unrestricted 4×4 shape reduction. -/
theorem remaining_four_four_shapes {n m : ℕ}
    (hn : n.primeFactorsList.length = 4) (hm : m.primeFactorsList.length = 4)
    (hgap : n+12=m ∨ m+12=n)
    (hφ : n.totient+m=m.totient+n) (hσ : σ 1 n+m = σ 1 m+n) :
    ((∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ n = p^2*q*r) ∧ (∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ m = p^2*q*r)) ∨
      ((∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ n = p^2*q*r) ∧ Squarefree m) ∨ (Squarefree n ∧ (∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ m = p^2*q*r)) := by
  rcases squarefree_or_repeated hn hm hgap hφ hσ with hn' | hn' <;>
    rcases squarefree_or_repeated hm hn hgap.symm hφ.symm hσ.symm with hm' | hm'
  · exfalso
    rcases hgap with h | h
    · rw [← h] at hm' hφ hσ
      exact no_squarefree_squarefree hn hn' hm' (by omega) (by omega)
    · rw [← h] at hn' hφ hσ
      exact no_squarefree_squarefree hm hm' hn' (by omega) (by omega)
  · exact Or.inr (Or.inr ⟨hn',hm'⟩)
  · exact Or.inr (Or.inl ⟨hn',hm'⟩)
  · exact Or.inl ⟨hn',hm'⟩

end A056777FourFour
end

section
open scoped ArithmeticFunction.sigma
open Nat ArithmeticFunction

namespace A056777EvenFourFour

theorem square_prime_formulas {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (p^2*q).totient + p*(p+q-1) = p^2*q ∧
    σ 1 (p^2*q) + (p^2*q).totient = 2*(p^2*q)+q+2*p+1 := by
  have hc := ((Nat.coprime_primes hp hq).mpr hpq).pow_left 2
  have hφ : (p^2).totient=p*(p-1) := by simpa using Nat.totient_prime_pow_succ hp 1
  have hσ : σ 1 (p^2)=1+p+p^2 := by
    simp only [sigma_one_apply_prime_pow hp,Finset.sum_range_succ,Finset.sum_range_zero,
      pow_zero,pow_one,zero_add]
  have hσq : σ 1 q=q+1 := by simpa using sigma_one_apply_prime_pow (i:=1) hq
  rw [Nat.totient_mul hc,hφ,Nat.totient_prime hq,
    isMultiplicative_sigma.map_mul_of_coprime hc,hσ,hσq]
  have hp1 := hp.pos
  have hq1 := hq.pos
  have hpq1 : 1 ≤ p+q := by omega
  zify [hp1,hq1,hpq1]
  constructor <;> ring

private theorem no_repeated_moments (p q r s : ℤ)
    (hq : 3 ≤ q) (hr : 3 ≤ r) (hs : 3 ≤ s)
    (hop : p%2=1) (hor : r%2=1)
    (hK : s+2*r=q+2*p+4)
    (hF : p*(p+q-1)=r*(r+s-1)+6)
    (hG : r^2*s=p^2*q+6) : False := by
  let d := p-r
  have hp' : p=r+d := by dsimp [d]; ring
  have hs' : s=q+2*d+4 := by dsimp [d]; omega
  have hF' : d*(d+q-1)=4*r+6 := by
    rw [hp',hs'] at hF
    nlinarith only [hF]
  have hG' : r^2*(2*d+4)-(2*r*d+d^2)*q=6 := by
    rw [hp',hs'] at hG
    nlinarith only [hG]
  have hdpos : 0 < d := by
    by_contra! h
    have hn : 0 ≤ d+q-1 := by
      by_cases he : d=0
      · omega
      · have hd2 : d ≤ -2 := by dsimp [d] at *; omega
        omega
    have hneg := mul_nonpos_of_nonpos_of_nonneg h hn
    nlinarith only [hneg,hF',hr]
  have hd2 : 2 ≤ d := by dsimp [d] at *; omega
  have hpoly : d^3+2*d^2*r-d^2+2*d*r^2-6*d*r-6*d-4*r^2-12*r-6=0 := by
    linear_combination hG'+(2*r+d)*hF'
  by_cases hd : d=2
  · rw [hd] at hpoly
    nlinarith only [hpoly,hr]
  · let U := d-4
    let V := r-3
    have hU : 0 ≤ U := by
      dsimp [U,d] at *
      omega
    have hV : 0 ≤ V := by dsimp [V]; omega
    have hpos : 0 < U^3+2*U^2*V+17*U^2+2*U*V^2+22*U*V+82*U+
        4*V^2+20*V+42 := by positivity
    have he : d^3+2*d^2*r-d^2+2*d*r^2-6*d*r-6*d-4*r^2-12*r-6 =
        U^3+2*U^2*V+17*U^2+2*U*V^2+22*U*V+82*U+4*V^2+20*V+42 := by
      dsimp [U,V]
      ring
    rw [← he,hpoly] at hpos
    omega

/-- After removing one factor of two, two repeated-prime length-three cores cannot
satisfy the shifted totient and divisor-sum equations. -/
theorem no_odd_repeated_cores {p q r s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s)
    (hop : Odd p) (hoq : Odd q) (hor : Odd r) (hos : Odd s)
    (hg : p^2*q+6=r^2*s)
    (hφ : (r^2*s).totient=(p^2*q).totient+12)
    (hσ : σ 1 (r^2*s)=σ 1 (p^2*q)+4) : False := by
  have ⟨hFp,hKp⟩ := square_prime_formulas hp hq hpq
  have ⟨hFr,hKr⟩ := square_prime_formulas hr hs hrs
  have hK : s+2*r=q+2*p+4 := by omega
  have hF : p*(p+q-1)=r*(r+s-1)+6 := by omega
  have hq3 : 3 ≤ q := by have := hq.two_le; have := Nat.odd_iff.mp hoq; omega
  have hr3 : 3 ≤ r := by have := hr.two_le; have := Nat.odd_iff.mp hor; omega
  have hs3 : 3 ≤ s := by have := hs.two_le; have := Nat.odd_iff.mp hos; omega
  have hpp := Nat.odd_iff.mp hop
  have hrr := Nat.odd_iff.mp hor
  have hpq1 : 1 ≤ p+q := by have := hp.pos; omega
  have hrs1 : 1 ≤ r+s := by omega
  zify [hpq1,hrs1] at hK hF hg hq3 hr3 hs3 hpp hrr
  exact no_repeated_moments p q r s hq3 hr3 hs3 hpp hrr hK hF hg.symm

end A056777EvenFourFour
end

section
open scoped ArithmeticFunction.sigma
open Nat ArithmeticFunction

namespace A056777EvenFourFour

private theorem triple_formulas {r s t : ℕ} (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    (r*s*t).totient+(r*s+r*t+s*t)+1=r*s*t+(r+s+t) ∧
    σ 1 (r*s*t)+(r*s*t).totient=2*(r*s*t)+2*(r+s+t) := by
  have hc₁ := (Nat.coprime_primes hr hs).mpr hrs
  have hc₂ := ((Nat.coprime_primes hr ht).mpr hrt).mul_left ((Nat.coprime_primes hs ht).mpr hst)
  have hσ {p : ℕ} (hp : p.Prime) : σ 1 p=p+1 := by
    simpa using sigma_one_apply_prime_pow (i:=1) hp
  rw [Nat.totient_mul hc₂,Nat.totient_mul hc₁,Nat.totient_prime hr,
    Nat.totient_prime hs,Nat.totient_prime ht,isMultiplicative_sigma.map_mul_of_coprime hc₂,
    isMultiplicative_sigma.map_mul_of_coprime hc₁,hσ hr,hσ hs,hσ ht]
  have hr1 := hr.pos
  have hs1 := hs.pos
  have ht1 := ht.pos
  zify [hr1,hs1,ht1]
  constructor <;> ring

private theorem first_newton (r s t : ℤ) : 3*(r*s+r*t+s*t) ≤ (r+s+t)^2 := by
  nlinarith only [sq_nonneg (r-s),sq_nonneg (r-t),sq_nonneg (s-t)]

private theorem second_newton (r s t : ℤ) :
    3*(r+s+t)*(r*s*t) ≤ (r*s+r*t+s*t)^2 := by
  nlinarith only [sq_nonneg (r*s-r*t),sq_nonneg (r*s-s*t),sq_nonneg (r*t-s*t)]

private theorem large_margin_plus (p S : ℤ) (hp : 11 ≤ p) (hS : 5*p+4 ≤ S) :
    0 < 3*S*(p^2*(2*S-2*p-1-4*(1))+6*(1))-
      ((2*p+1)*S-(p+1)^2-(4*p+6)*(1))^2 := by
  let U := p-11
  let V := S-5*p-4
  have hU : 0 ≤ U := by dsimp [U]; omega
  have hV : 0 ≤ V := by dsimp [V]; omega
  let P := 39*U^4+18*U^3*V^1+1731*U^3+2*U^2*V^2+581*U^2*V^1+28850*U^2+40*U^1*V^2+6246*U^1*V^1+214115*U^1+197*V^2+22387*V^1+597440
  have hpos : 0 < P := by dsimp [P]; positivity
  have he : 3*S*(p^2*(2*S-2*p-1-4*(1))+6*(1))-
      ((2*p+1)*S-(p+1)^2-(4*p+6)*(1))^2 = P := by
    dsimp [P,U,V]
    ring
  rw [he]
  exact hpos

private theorem large_margin_minus (p S : ℤ) (hp : 11 ≤ p) (hS : 5*p+4 ≤ S) :
    0 < 3*S*(p^2*(2*S-2*p-1-4*(-1))+6*(-1))-
      ((2*p+1)*S-(p+1)^2-(4*p+6)*(-1))^2 := by
  let U := p-11
  let V := S-5*p-4
  have hU : 0 ≤ U := by dsimp [U]; omega
  have hV : 0 ≤ V := by dsimp [V]; omega
  let P := 39*U^4+18*U^3*V^1+1707*U^3+2*U^2*V^2+573*U^2*V^1+27762*U^2+40*U^1*V^2+6006*U^1*V^1+198399*U^1+197*V^2+20655*V^1+524052
  have hpos : 0 < P := by dsimp [P]; positivity
  have he : 3*S*(p^2*(2*S-2*p-1-4*(-1))+6*(-1))-
      ((2*p+1)*S-(p+1)^2-(4*p+6)*(-1))^2 = P := by
    dsimp [P,U,V]
    ring
  rw [he]
  exact hpos

private theorem shifted_moments_impossible (p q S x z e : ℤ)
    (hq : 3 ≤ q) (hS : 15 ≤ S) (hp : p=5 ∨ p=7 ∨ 11≤p) (he : e=1 ∨ e=-1)
    (hQ : q=2*S-2*p-1-4*e)
    (hX : x=(2*p+1)*S-(p+1)^2-(4*p+6)*e)
    (hZ : z=p^2*q+6*e)
    (hN₁ : 3*x≤S^2) (hN₂ : 3*S*z≤x^2) : False := by
  have hZ' : z=p^2*(2*S-2*p-1-4*e)+6*e := by rw [hZ,hQ]
  rw [hX] at hN₁ hN₂
  rw [hZ'] at hN₂
  rcases hp with rfl | rfl | hp
  · have hS26 : 26≤S := by
      by_contra! h
      have hh := mul_nonneg (show 0≤S-15 by omega) (show 0≤25-S by omega)
      rcases he with rfl|rfl <;> nlinarith only [hh,hN₁,h]
    have hn := mul_nonneg (show 0≤S-26 by omega) (show 0≤29*S+431 by omega)
    rcases he with rfl|rfl <;> nlinarith only [hn,hN₂,hS26]
  · have hS38 : 38≤S := by
      by_contra! h
      have hh := mul_nonneg (show 0≤S-15 by omega) (show 0≤37-S by omega)
      rcases he with rfl|rfl <;> nlinarith only [hh,hN₁,h]
    have hn := mul_nonneg (show 0≤S-38 by omega) (show 0≤69*S+1887 by omega)
    rcases he with rfl|rfl <;> nlinarith only [hn,hN₂,hS38]
  · have hS' : 5*p+4 ≤ S := by
      by_contra! h
      let w := 2*(S-p)
      have hw : 0≤w := by dsimp [w]; rcases he with rfl|rfl <;> omega
      have hh := mul_nonneg hw (show 0≤8*p+6-w by dsimp [w]; omega)
      have hpp := mul_nonneg (show 0≤p-11 by omega) (show 0≤8*p+28 by omega)
      dsimp [w] at hh
      rcases he with rfl|rfl <;> nlinarith only [hh,hpp,hN₁,hp]
    rcases he with rfl|rfl
    · have hh := large_margin_plus p S hp hS'
      linarith only [hh,hN₂]
    · have hh := large_margin_minus p S hp hS'
      linarith only [hh,hN₂]

private theorem three_core_pair_impossible {q s t : ℕ}
    (hq : q.Prime) (hs : s.Prime) (ht : t.Prime)
    (hq3 : q ≠ 3) (hs3 : s ≠ 3) (ht3 : t ≠ 3) (hst : s ≠ t)
    (hos : Odd s) (hot : Odd t)
    (h : ((3^2*q+6=3*(s*t)) ∧ (3*(s*t)).totient=(3^2*q).totient+12) ∨
      ((3*(s*t)+6=3^2*q) ∧ (3^2*q).totient=(3*(s*t)).totient+12)) : False := by
  have hprime := Nat.prime_three
  have hcq := ((Nat.coprime_primes hprime hq).mpr hq3.symm).pow_left 2
  have hcst := (Nat.coprime_primes hs ht).mpr hst
  have hc := ((Nat.coprime_primes hprime hs).mpr hs3.symm).mul_right
    ((Nat.coprime_primes hprime ht).mpr ht3.symm)
  rw [Nat.totient_mul hcq,Nat.totient_mul hc,Nat.totient_mul hcst,
    show ((3:ℕ)^2).totient=6 by decide,Nat.totient_prime hprime,
    Nat.totient_prime hq,Nat.totient_prime hs,Nat.totient_prime ht] at h
  have hq1 := hq.pos
  have hs1 := hs.pos
  have ht1 := ht.pos
  have hs5 : 5 ≤ s := by have := hs.two_le; have := Nat.odd_iff.mp hos; omega
  have ht5 : 5 ≤ t := by have := ht.two_le; have := Nat.odd_iff.mp hot; omega
  zify [hq1,hs1,ht1] at h hs5 ht5
  norm_num at h
  rcases h with ⟨hg,hφ⟩ | ⟨hg,hφ⟩ <;> nlinarith only [hg,hφ,hs5,ht5]

/-- A repeated-prime odd core and a squarefree odd core cannot have the step of six
with totient step twelve and divisor-sum step four induced by dividing even endpoints by two. -/
theorem no_odd_mixed_cores {p q r s t : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (hop : Odd p) (hoq : Odd q) (hor : Odd r) (hos : Odd s) (hot : Odd t)
    (hstep : (p^2*q+6=r*s*t ∧ (r*s*t).totient=(p^2*q).totient+12 ∧
      σ 1 (r*s*t)=σ 1 (p^2*q)+4) ∨
      (r*s*t+6=p^2*q ∧ (p^2*q).totient=(r*s*t).totient+12 ∧
      σ 1 (p^2*q)=σ 1 (r*s*t)+4)) : False := by
  by_cases hp3 : p=3
  · subst p
    have hg := hstep.imp And.left And.left
    have hd : 3 ∣ r*s*t := by norm_num at hg; omega
    simp only [Nat.prime_three.dvd_mul] at hd
    have eq_three {a : ℕ} (ha : a.Prime) (h : 3 ∣ a) : a=3 := by
      rcases (Nat.dvd_prime ha).mp h with h | h
      · omega
      · exact h.symm
    rcases hd with (hd|hd)|hd
    · obtain rfl := eq_three hr hd
      rw [show 3*s*t=3*(s*t) by ring] at hstep
      exact three_core_pair_impossible hq hs ht hpq.symm hrs.symm hrt.symm hst hos hot
        (hstep.imp (fun h => ⟨h.1,h.2.1⟩) (fun h => ⟨h.1,h.2.1⟩))
    · obtain rfl := eq_three hs hd
      rw [show r*3*t=3*(r*t) by ring] at hstep
      exact three_core_pair_impossible hq hr ht hpq.symm hrs hst.symm hrt hor hot
        (hstep.imp (fun h => ⟨h.1,h.2.1⟩) (fun h => ⟨h.1,h.2.1⟩))
    · obtain rfl := eq_three ht hd
      rw [show r*s*3=3*(r*s) by ring] at hstep
      exact three_core_pair_impossible hq hr hs hpq.symm hrt hst hrs hor hos
        (hstep.imp (fun h => ⟨h.1,h.2.1⟩) (fun h => ⟨h.1,h.2.1⟩))
  have hpclass : p=5 ∨ p=7 ∨ 11≤p := by
    have hp2 := hp.two_le
    have hpo := Nat.odd_iff.mp hop
    have hp9 : p ≠ 9 := fun he => (by decide : ¬Nat.Prime 9) (he ▸ hp)
    omega
  have hq3 : 3≤q := by have := hq.two_le; have := Nat.odd_iff.mp hoq; omega
  have hS : 15≤r+s+t := by
    have := hr.two_le
    have := hs.two_le
    have := ht.two_le
    have := Nat.odd_iff.mp hor
    have := Nat.odd_iff.mp hos
    have := Nat.odd_iff.mp hot
    omega
  have ⟨hF,hK⟩ := square_prime_formulas hp hq hpq
  have ⟨hF',hK'⟩ := triple_formulas hr hs ht hrs hrt hst
  have hp1 := hp.pos
  have hq1 := hq.pos
  have hpq1 : 1 ≤ p+q := by omega
  zify [hp1,hq1,hpq1] at hpclass hq3 hS hF hK hF' hK' hstep
  let S : ℤ := r+s+t
  let x : ℤ := r*s+r*t+s*t
  let z : ℤ := r*s*t
  have hN₁ : 3*x≤S^2 := first_newton r s t
  have hN₂ : 3*S*z≤x^2 := second_newton r s t
  rcases hstep with ⟨hg,hφ,hσ⟩|⟨hg,hφ,hσ⟩
  · have he : (1:ℤ)=1 ∨ (1:ℤ)=-1 := Or.inl rfl
    exact shifted_moments_impossible p q S x z 1 hq3 hS hpclass he
      (by dsimp [S]; omega) (by dsimp [x,S]; nlinarith only [hF,hK,hF',hK',hg,hφ,hσ])
      (by dsimp [z]; omega) hN₁ hN₂
  · have he : (-1:ℤ)=1 ∨ (-1:ℤ)=-1 := Or.inr rfl
    exact shifted_moments_impossible p q S x z (-1) hq3 hS hpclass he
      (by dsimp [S]; omega) (by dsimp [x,S]; nlinarith only [hF,hK,hF',hK',hg,hφ,hσ])
      (by dsimp [z]; omega) hN₁ hN₂

end A056777EvenFourFour
end

section
open scoped ArithmeticFunction.sigma
open Nat ArithmeticFunction

namespace A056777EvenFourFour

private theorem seven_dvd_sigma_of_four_dvd {n : ℕ}
    (h : Squarefree n ∨ (∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ n = p^2*q*r)) (hd : 4 ∣ n) : 7 ∣ σ 1 n := by
  rcases h with hs | ⟨p,q,r,hp,hq,hr,hpq,hpr,hqr,rfl⟩
  · exact ((Nat.squarefree_iff_prime_squarefree.mp hs 2 Nat.prime_two) hd).elim
  have hp2 : p=2 := by
    by_contra hne
    have hc := (((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hne)).pow_left 2).pow_right 2
    rw [mul_assoc] at hd
    have hd' : 4 ∣ q*r := hc.dvd_of_dvd_mul_left hd
    have hs : Squarefree (q*r) := Nat.squarefree_mul_iff.mpr
      ⟨(Nat.coprime_primes hq hr).mpr hqr,hq.squarefree,hr.squarefree⟩
    exact (Nat.squarefree_iff_prime_squarefree.mp hs 2 Nat.prime_two) hd'
  subst p
  have hc := (((Nat.coprime_primes Nat.prime_two hq).mpr hpq).mul_right
    ((Nat.coprime_primes Nat.prime_two hr).mpr hpr)).pow_left 2
  rw [mul_assoc,isMultiplicative_sigma.map_mul_of_coprime hc,show σ 1 ((2:ℕ)^2)=7 by decide]
  exact dvd_mul_right _ _

private theorem length_mul_two {n : ℕ} (hn : n ≠ 0) :
    (2*n).primeFactorsList.length=1+n.primeFactorsList.length := by
  have hh := (Nat.perm_primeFactorsList_mul (by decide : (2:ℕ)≠0) hn).length_eq
  rwa [Nat.primeFactorsList_two,List.length_append,List.length_singleton] at hh

private theorem core_nonsquarefree {a : ℕ}
    (ha : Odd a) (h : (∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ (2*a) = p^2*q*r)) : ¬Squarefree a := by
  intro hs
  exact A056777FourFour.repeated_not_squarefree h ((Nat.squarefree_mul ha.coprime_two_left).mpr ⟨Nat.prime_two.squarefree,hs⟩)

private theorem core_repeated_shape {a m : ℕ}
    (ha : Odd a) (hlen : a.primeFactorsList.length=3) (hns : ¬Squarefree a)
    (hm : m.primeFactorsList.length=4)
    (hgap : 2*a+12=m ∨ m+12=2*a)
    (hφ : (2*a).totient+m=m.totient+2*a) (hσ : σ 1 (2*a)+m=σ 1 m+2*a) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p≠q ∧ Odd p ∧ Odd q ∧ a=p^2*q := by
  obtain ⟨p,q,hp,hq,hn⟩ :=
    A056777RepeatedTriple.pow_two_mul_of_nonsquarefree_length_three hlen hns
  have hos := ha
  rw [hn] at hos
  simp only [pow_two,Nat.odd_mul] at hos
  have hpq : p ≠ q := by
    rintro rfl
    have h2p : p ≠ 2 := by have := Nat.odd_iff.mp hos.1.1; omega
    have hh : 2*a=p^3*2 := by rw [hn]; ring
    rw [hh] at hgap hφ hσ
    exact A056777.no_cube_prime_four_partner hp Nat.prime_two h2p hm hgap hφ hσ
  exact ⟨p,q,hp,hq,hpq,hos.1.1,hos.2,hn⟩

private theorem core_squarefree_shape {a : ℕ}
    (ha : Odd a) (hlen : a.primeFactorsList.length=3) (hs : Squarefree a) :
    ∃ r s t : ℕ, r.Prime ∧ s.Prime ∧ t.Prime ∧
      r≠s ∧ r≠t ∧ s≠t ∧ Odd r ∧ Odd s ∧ Odd t ∧ a=r*s*t := by
  have hprod := Nat.prod_primeFactorsList hs.ne_zero
  have hnd := hs.nodup_primeFactorsList
  obtain ⟨r,s,t,heq⟩ : ∃ r s t, a.primeFactorsList=[r,s,t] := by
    generalize hl : a.primeFactorsList = l at hlen ⊢
    rcases l with _ | ⟨r,l⟩
    · simp at hlen
    rcases l with _ | ⟨s,l⟩
    · simp at hlen
    rcases l with _ | ⟨t,l⟩
    · simp at hlen
    rcases l with _ | ⟨k,l⟩
    · exact ⟨r,s,t,rfl⟩
    · simp at hlen
  have hr := Nat.prime_of_mem_primeFactorsList (n:=a) (p:=r) (by simp [heq])
  have hsp := Nat.prime_of_mem_primeFactorsList (n:=a) (p:=s) (by simp [heq])
  have ht := Nat.prime_of_mem_primeFactorsList (n:=a) (p:=t) (by simp [heq])
  simp only [heq,List.nodup_cons,List.mem_cons,not_or,List.not_mem_nil,not_false_eq_true,
    List.nodup_nil,and_true] at hnd
  have hform : a=r*s*t := by simpa [heq,mul_assoc] using hprod.symm
  rw [hform] at ha
  simp only [Nat.odd_mul] at ha
  exact ⟨r,s,t,hr,hsp,ht,hnd.1.1,hnd.1.2,hnd.2,ha.1.1,ha.1.2,ha.2,hform⟩

/-- No even endpoints with four prime factors each can satisfy the A056777 jump conditions. -/
theorem no_even_four_four_pair {n m : ℕ} (he : Even n)
    (hn : n.primeFactorsList.length=4) (hm : m.primeFactorsList.length=4)
    (hgap : n+12=m ∨ m+12=n)
    (hφ : n.totient+m=m.totient+n) (hσ : σ 1 n+m=σ 1 m+n) : False := by
  by_cases hn4 : 4 ∣ n
  · have hm4 : 4 ∣ m := by omega
    have hs := A056777FourFour.remaining_four_four_shapes hn hm hgap hφ hσ
    have han : Squarefree n ∨ (∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ n = p^2*q*r) := by
      rcases hs with h|h|h
      · exact Or.inr h.1
      · exact Or.inr h.1
      · exact Or.inl h.1
    have ham : Squarefree m ∨ (∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ m = p^2*q*r) := by
      rcases hs with h|h|h
      · exact Or.inr h.2
      · exact Or.inl h.2
      · exact Or.inr h.2
    have hsn := seven_dvd_sigma_of_four_dvd han hn4
    have hsm := seven_dvd_sigma_of_four_dvd ham hm4
    clear hs han ham
    omega
  have hme : Even m := Nat.even_iff.mpr (by have := Nat.even_iff.mp he; omega)
  obtain ⟨a,ha⟩ := he
  obtain ⟨b,hb⟩ := hme
  have hna : n=2*a := by omega
  have hmb : m=2*b := by omega
  have hoa : Odd a := Nat.odd_iff.mpr (by omega)
  have hob : Odd b := Nat.odd_iff.mpr (by omega)
  have ha0 : a≠0 := by have := Nat.odd_iff.mp hoa; omega
  have hb0 : b≠0 := by have := Nat.odd_iff.mp hob; omega
  have hal : a.primeFactorsList.length=3 := by
    rw [hna,length_mul_two ha0] at hn
    omega
  have hbl : b.primeFactorsList.length=3 := by
    rw [hmb,length_mul_two hb0] at hm
    omega
  have hcore :
      (a+6=b ∧ b.totient=a.totient+12 ∧ σ 1 b=σ 1 a+4) ∨
      (b+6=a ∧ a.totient=b.totient+12 ∧ σ 1 a=σ 1 b+4) := by
    have hca := hoa.coprime_two_left
    have hcb := hob.coprime_two_left
    rw [hna,hmb,Nat.totient_mul hca,Nat.totient_mul hcb,Nat.totient_prime Nat.prime_two] at hφ
    norm_num at hφ
    rw [hna,hmb,isMultiplicative_sigma.map_mul_of_coprime hca,
      isMultiplicative_sigma.map_mul_of_coprime hcb,show σ 1 2=3 by decide] at hσ
    omega
  have har (h : (∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ n = p^2*q*r)) :=
    core_repeated_shape hoa hal (core_nonsquarefree hoa (hna ▸ h)) hm
      (hna ▸ hgap) (hna ▸ hφ) (hna ▸ hσ)
  have hbr (h : (∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ m = p^2*q*r)) :=
    core_repeated_shape hob hbl (core_nonsquarefree hob (hmb ▸ h)) hn
      (hmb ▸ hgap.symm) (hmb ▸ hφ.symm) (hmb ▸ hσ.symm)
  have hs := A056777FourFour.remaining_four_four_shapes hn hm hgap hφ hσ
  rcases hs with ⟨han,hbn⟩ | ⟨han,hbn⟩ | ⟨han,hbn⟩
  · obtain ⟨p,q,hp,hq,hpq,hop,hoq,ha'⟩ := har han
    obtain ⟨r,s,hr,hs,hrs,hor,hos,hb'⟩ := hbr hbn
    rw [ha',hb'] at hcore
    rcases hcore with ⟨hg,hφ',hσ'⟩ | ⟨hg,hφ',hσ'⟩
    · exact no_odd_repeated_cores hp hq hr hs hpq hrs hop hoq hor hos hg hφ' hσ'
    · exact no_odd_repeated_cores hr hs hp hq hrs hpq hor hos hop hoq hg hφ' hσ'
  · obtain ⟨p,q,hp,hq,hpq,hop,hoq,ha'⟩ := har han
    have hfree : Squarefree b := (hmb ▸ hbn).squarefree_of_dvd (dvd_mul_left b 2)
    obtain ⟨r,s,t,hr,hs,ht,hrs,hrt,hst,hor,hos,hot,hb'⟩ :=
      core_squarefree_shape hob hbl hfree
    rw [ha',hb'] at hcore
    exact no_odd_mixed_cores hp hq hr hs ht hpq hrs hrt hst hop hoq hor hos hot hcore
  · obtain ⟨p,q,hp,hq,hpq,hop,hoq,hb'⟩ := hbr hbn
    have hfree : Squarefree a := (hna ▸ han).squarefree_of_dvd (dvd_mul_left a 2)
    obtain ⟨r,s,t,hr,hs,ht,hrs,hrt,hst,hor,hos,hot,ha'⟩ :=
      core_squarefree_shape hoa hal hfree
    rw [ha',hb'] at hcore
    exact no_odd_mixed_cores hp hq hr hs ht hpq hrs hrt hst hop hoq hor hos hot hcore.symm

/-- Every remaining 4×4 candidate is odd at both endpoints, and at least one endpoint is
a square times two other distinct primes. -/
theorem odd_four_four_residual {n m : ℕ}
    (hn : n.primeFactorsList.length=4) (hm : m.primeFactorsList.length=4)
    (hgap : n+12=m ∨ m+12=n)
    (hφ : n.totient+m=m.totient+n) (hσ : σ 1 n+m=σ 1 m+n) :
    Odd n ∧ Odd m ∧
      (((∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ n = p^2*q*r) ∧ (∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ m = p^2*q*r)) ∨
        ((∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ n = p^2*q*r) ∧ Squarefree m) ∨
        (Squarefree n ∧ (∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ m = p^2*q*r))) := by
  have hnodd := Nat.not_even_iff_odd.mp
    (fun he => no_even_four_four_pair he hn hm hgap hφ hσ)
  have hmod := Nat.odd_iff.mp hnodd
  exact ⟨hnodd,Nat.odd_iff.mpr (by omega),
    A056777FourFour.remaining_four_four_shapes hn hm hgap hφ hσ⟩

end A056777EvenFourFour
end

section
open scoped ArithmeticFunction.sigma

namespace A056777FourFour

private theorem repeated_distinct_count {n : ℕ} (h : (∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ n = p^2*q*r)) :
    3 ≤ n.primeFactors.card := by
  obtain ⟨p,q,r,hp,hq,hr,hpq,hpr,hqr,rfl⟩ := h
  have hz : p^2*q*r ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hp.ne_zero) hq.ne_zero) hr.ne_zero
  have hset : ({p,q,r} : Finset ℕ) ⊆ (p^2*q*r).primeFactors := by
    intro a ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with h|h|h <;> subst a
    · exact Nat.mem_primeFactors.mpr ⟨hp,⟨p*q*r,by ring⟩,hz⟩
    · exact Nat.mem_primeFactors.mpr ⟨hq,⟨p^2*r,by ring⟩,hz⟩
    · exact Nat.mem_primeFactors.mpr ⟨hr,⟨p^2*q,by ring⟩,hz⟩
  have hl := Finset.card_le_card hset
  simpa [hpq,hpr,hqr] using hl

private theorem squarefree_distinct_count {n : ℕ} (hn : n.primeFactorsList.length=4)
    (hs : Squarefree n) : 3 ≤ n.primeFactors.card := by
  rw [← Nat.toFinset_factors,List.toFinset_card_of_nodup hs.nodup_primeFactorsList,hn]
  decide

/-- If both endpoints are odd and each has at least three distinct prime factors,
their totients cannot have a step of twelve when the arguments do. -/
theorem no_odd_three_distinct_pair {n m : ℕ} (hn : Odd n) (hm : Odd m)
    (hcn : 3 ≤ n.primeFactors.card) (hcm : 3 ≤ m.primeFactors.card)
    (hgap : n+12=m ∨ m+12=n) (hφ : n.totient+m=m.totient+n) : False := by
  have hnd : 8 ∣ n.totient :=
    (pow_dvd_pow 2 hcn).trans (A056777OddFour.two_pow_card_dvd_totient hn)
  have hmd : 8 ∣ m.totient :=
    (pow_dvd_pow 2 hcm).trans (A056777OddFour.two_pow_card_dvd_totient hm)
  omega

end A056777FourFour

/-- The A056777 jump conditions exclude every pair of endpoints with exactly
four prime factors each, counted with multiplicity. Either endpoint can be smaller. -/
theorem A056777.no_four_four_pair {n m : ℕ}
    (hn : n.primeFactorsList.length=4) (hm : m.primeFactorsList.length=4)
    (hgap : n+12=m ∨ m+12=n)
    (hφ : n.totient+m=m.totient+n) (hσ : σ 1 n+m=σ 1 m+n) : False := by
  obtain ⟨ho,ho',hshape⟩ := A056777EvenFourFour.odd_four_four_residual hn hm hgap hφ hσ
  apply A056777FourFour.no_odd_three_distinct_pair ho ho' _ _ hgap hφ
  · rcases hshape with h|h|h
    · exact A056777FourFour.repeated_distinct_count h.1
    · exact A056777FourFour.repeated_distinct_count h.1
    · exact A056777FourFour.squarefree_distinct_count hn h.1
  · rcases hshape with h|h|h
    · exact A056777FourFour.repeated_distinct_count h.2
    · exact A056777FourFour.squarefree_distinct_count hm h.2
    · exact A056777FourFour.repeated_distinct_count h.2
end

open scoped ArithmeticFunction.sigma
open Nat Finset ArithmeticFunction OeisA56777

private theorem no_three_four_pair {n m : ℕ}
    (hn : n.primeFactorsList.length = 3) (hm : m.primeFactorsList.length = 4)
    (hgap : n+12=m ∨ m+12=n)
    (hφ : n.totient+m=m.totient+n) (hσ : σ 1 n+m = σ 1 m+n) : False := by
  obtain ⟨p,q,hp,hq,hpq,hndef,hfour⟩ :=
    A056777ThreeFourShapes.remaining_shapes_three_four_pair hn hm hgap hφ hσ
  rw [hndef] at hgap hφ hσ
  have hne : ¬ Even (p^2*q) := fun he =>
    A056777EvenRepeatedFour.no_even_repeated_three_four_pair hp hq hpq he hm hgap hφ hσ
  have ho := Nat.not_even_iff_odd.mp hne
  have hom : Odd m := by
    have hh := Nat.odd_iff.mp ho
    exact Nat.odd_iff.mpr (by omega)
  simp only [pow_two, Nat.odd_mul] at ho
  rcases hfour with ⟨r,s,hr,hs,hrs,hmdef⟩ | ⟨r,s,t,hr,hs,ht,hrs,hrt,hst,hmdef⟩
  · rw [hmdef] at hφ hσ
    exact A056777SquarePrimeCubePrime.no_squarePrime_cubePrime hp hq hr hs hpq hrs hφ hσ
  rw [hmdef] at hgap hφ hσ hom
  simp only [pow_two,Nat.odd_mul] at hom
  exact A056777OddRepeatedFourDiscriminant.no_odd_square_prime_square_two_primes_pair
    hp hq hr hs ht hpq hrs hrt hst ho.1.1 ho.2 hom.1.1.1 hom.1.2 hom.2 hgap hφ hσ

private theorem positive_odd_exponent_count {n : ℕ} (hn : n ≠ 0)
    (h : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Odd (n.factorization p)) :
    1 ≤ (n.primeFactors.filter fun p => p ≠ 2 ∧ Odd (n.factorization p)).card := by
  obtain ⟨p, hp, hp2, hodd⟩ := h
  have hpos : 0 < n.factorization p := by
    have := Nat.odd_iff.mp hodd
    omega
  have hmem := Nat.mem_primeFactors.mpr ⟨hp, Nat.dvd_of_factorization_pos hpos.ne', hn⟩
  exact Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨hmem, hp2, hodd⟩⟩


/-- Exclude the remaining candidates with at least four prime factors at each endpoint. -/
def H1 : Prop :=
  ∀ n : ℕ, A n →
    4 ≤ n.primeFactorsList.length →
    4 ≤ (n + 12).primeFactorsList.length →
    (5 ≤ n.primeFactorsList.length ∨ 5 ≤ (n + 12).primeFactorsList.length) →
    (¬ Squarefree n ∨ ¬ Squarefree (n + 12)) →
    1 ≤ (n.primeFactors.filter fun p => p ≠ 2 ∧ Odd (n.factorization p)).card →
    1 ≤ ((n + 12).primeFactors.filter fun p =>
      p ≠ 2 ∧ Odd ((n + 12).factorization p)).card →
    ((n.primeFactors.filter fun p => p ≠ 2 ∧ Odd (n.factorization p)).card ≤ 2 ∨
      ((n + 12).primeFactors.filter fun p =>
        p ≠ 2 ∧ Odd ((n + 12).factorization p)).card ≤ 2) →
    False

/-- Exclude the remaining candidates with exactly three prime factors at one endpoint
and at least five at the other. -/
def H2 : Prop :=
  ∀ n : ℕ, A n →
    ((n.primeFactorsList.length = 3 ∧ 5 ≤ (n + 12).primeFactorsList.length) ∨
      ((n + 12).primeFactorsList.length = 3 ∧ 5 ≤ n.primeFactorsList.length)) →
    (¬ Squarefree n ∨ ¬ Squarefree (n + 12)) →
    1 ≤ (n.primeFactors.filter fun p => p ≠ 2 ∧ Odd (n.factorization p)).card →
    1 ≤ ((n + 12).primeFactors.filter fun p =>
      p ≠ 2 ∧ Odd ((n + 12).factorization p)).card →
    ((n.primeFactors.filter fun p => p ≠ 2 ∧ Odd (n.factorization p)).card ≤ 2 ∨
      ((n + 12).primeFactors.filter fun p =>
        p ≠ 2 ∧ Odd ((n + 12).factorization p)).card ≤ 2) →
    False

theorem main : H1 → H2 → type_of% @OeisA56777.comesFromPrimeQuadruple_of_a := by
  intro h1 h2 n ha
  have ⟨hnp, hn, ht, hs⟩ := ha
  by_contra hc
  have hrepeat : ¬ Squarefree n ∨ ¬ Squarefree (n + 12) := by
    by_contra! hall
    exact hc (A056777Squarefree.prime_quadruple_of_squarefree_pair hn hnp hall.1 hall.2 ht hs)
  obtain ⟨hf₁, hf₂⟩ := A056777Closure.factor_count_of_counterexample hn hnp ht hs hc
  have hne : n ≠ 0 := by omega
  obtain ⟨hex₁, hex₂⟩ := A056777Parity.odd_prime_exponents_of_sigma_step hne hs
  have hc₁ := positive_odd_exponent_count hne hex₁
  have hc₂ := positive_odd_exponent_count (by omega) hex₂
  have hsupport := A056777Squarefree.at_most_two_odd_exponents_of_sigma_step hne hs
  by_cases h₁ : n.primeFactorsList.length = 3
  · by_cases h₃ : (n + 12).primeFactorsList.length = 3
    · exact A056777LengthThree.no_pair_of_length_three h₁ h₃ ht hs
    by_cases h₄ : (n + 12).primeFactorsList.length = 4
    · exact no_three_four_pair h₁ h₄ (Or.inl rfl) (by omega) (by omega)
    exact h2 n ha (Or.inl ⟨h₁,by omega⟩) hrepeat hc₁ hc₂ hsupport
  · by_cases h₃ : (n + 12).primeFactorsList.length = 3
    · by_cases h₄ : n.primeFactorsList.length = 4
      · exact no_three_four_pair h₃ h₄ (Or.inr rfl) (by omega) (by omega)
      exact h2 n ha (Or.inr ⟨h₃,by omega⟩) hrepeat hc₁ hc₂ hsupport
    by_cases hlarge : 5 ≤ n.primeFactorsList.length ∨ 5 ≤ (n + 12).primeFactorsList.length
    · exact h1 n ha (by omega) (by omega) hlarge hrepeat hc₁ hc₂ hsupport
    have hn4 : n.primeFactorsList.length = 4 := by omega
    have hm4 : (n + 12).primeFactorsList.length = 4 := by omega
    exact A056777.no_four_four_pair hn4 hm4 (Or.inl rfl) (by omega) (by omega)

end OMA.R_OeisA56777_comesFromPrimeQuadruple_of_a_R2
