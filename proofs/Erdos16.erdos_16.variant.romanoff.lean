import FormalConjectures.ErdosProblems.«16»
import Mathlib

/-!
# Romanoff's theorem (Erdős Problem 16 — romanoff)

Proves `Erdos16.erdos_16.variant.romanoff`: the numbers of the form `2^k + p` (`p` an odd prime,
`k ≥ 1`) have positive lower asymptotic density.
- `R1`: Cauchy–Schwarz reduction from first-moment lower bound (`H1`) and second-moment upper
  bound (`H2`) on `r(n) = #{k ≥ 1 : n - 2^k is an odd prime}` (credit: `@senamakel`).
- `H1` & `H2`: Mertens' theorems (`OMALib.Mertens`), upper Selberg sieve (`OMALib.Sieve`),
  Chebyshev prime counts, prime-pair sieve bound, and Romanoff's `∑ 1 / ord_2(d)` convergence
  estimate (`RomA`–`RomD`).
-/

section R1Part

-- Reduction Erdos16.erdos_16.variant.romanoff.R1 of Erdős Problem 16 — romanoff
-- Credit: @senamakel
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/- Romanoff's theorem from a first-moment lower bound (Chebyshev) and a second-moment upper
bound (Romanoff's sieve estimate) on `r(n) = #{k ≥ 1 : n - 2^k is an odd prime}`, glued by
Cauchy–Schwarz. -/

namespace OMA.R_Erdos16_erdos_16_variant_romanoff_R1

/-- Chebyshev-type lower count: the number of representations `n = 2^k + p`
(`k ≥ 1`, `p` an odd prime) with `n ≤ x` is at least `c * x`. -/
def H1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
    c * x ≤ ∑ n ∈ Finset.range (x + 1),
      (((Finset.range n).filter (fun k => 1 ≤ k ∧ 2 ^ k < n ∧ (n - 2 ^ k).Prime ∧
        n - 2 ^ k ≠ 2)).card : ℝ)

/-- Romanoff's second-moment bound: `∑_{n ≤ x} r(n)^2 ≤ C x`, where `r(n)` counts
the representations `n = 2^k + p` with `k ≥ 1` and `p` an odd prime. -/
def H2 : Prop :=
  ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
    ∑ n ∈ Finset.range (x + 1),
      (((Finset.range n).filter (fun k => 1 ≤ k ∧ 2 ^ k < n ∧ (n - 2 ^ k).Prime ∧
        n - 2 ^ k ≠ 2)).card : ℝ) ^ 2 ≤ C * x

theorem main : H1 → H2 → type_of% @Erdos16.erdos_16.variant.romanoff := by
  rintro ⟨c, hc, x₀, hx₀⟩ ⟨C, hC⟩
  intro S
  unfold Erdos16.positive_lower_density
  set r : ℕ → ℕ := fun n => ((Finset.range n).filter (fun k => 1 ≤ k ∧ 2 ^ k < n ∧
    (n - 2 ^ k).Prime ∧ n - 2 ^ k ≠ 2)).card with hr
  have memS : ∀ n, 0 < r n → n ∈ S := by
    intro n hn
    obtain ⟨k, hk⟩ := Finset.card_pos.1 hn
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨-, hk1, hlt, hp, hp2⟩ := hk
    refine ⟨?_, k, n - 2 ^ k, hp, by omega⟩
    have h1 : Odd (n - 2 ^ k) := hp.odd_of_ne_two hp2
    have h2 : Even (2 ^ k) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
    have : n = 2 ^ k + (n - 2 ^ k) := by omega
    rw [this]; exact h2.add_odd h1
  classical
  set N := max x₀ 2
  have hCpos : 0 < C := by
    have h1 := hx₀ N (le_max_left _ _)
    have h2 := hC N (le_max_right _ _)
    have hN : (2 : ℝ) ≤ N := by exact_mod_cast le_max_right x₀ 2
    have hs : (∑ n ∈ Finset.range (N + 1), (r n : ℝ)) ≤
        ∑ n ∈ Finset.range (N + 1), (r n : ℝ) ^ 2 := by
      apply Finset.sum_le_sum; intro n _
      rcases Nat.eq_zero_or_pos (r n) with h | h
      · simp [h]
      · have : (1 : ℝ) ≤ r n := by exact_mod_cast h
        nlinarith
    by_contra hneg; push Not at hneg
    have : C * N ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg (by linarith)
    have : 0 < c * N := by positivity
    simp only [hr] at hs
    linarith
  set δ : ℝ := c ^ 2 / (2 * C) with hδ
  have hδpos : 0 < δ := by positivity
  have key : ∀ x : ℕ, N ≤ x → δ ≤ (Nat.count (· ∈ S) (x + 1) : ℝ) / ((x + 1 : ℕ) : ℝ) := by
    intro x hx
    have hx0 : x₀ ≤ x := le_trans (le_max_left _ _) hx
    have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
    have hxr : (2 : ℝ) ≤ x := by exact_mod_cast hx2
    set A := (Finset.range (x + 1)).filter (fun n => 0 < r n)
    have hsumA : ∑ n ∈ Finset.range (x + 1), (r n : ℝ) = ∑ n ∈ A, (r n : ℝ) := by
      rw [Finset.sum_filter]; apply Finset.sum_congr rfl; intro n _
      split_ifs with h
      · rfl
      · simp [Nat.eq_zero_of_not_pos h]
    have hsqA : ∑ n ∈ A, (r n : ℝ) ^ 2 ≤ ∑ n ∈ Finset.range (x + 1), (r n : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => by positivity)
    have hcs := sq_sum_le_card_mul_sum_sq (s := A) (f := fun n => (r n : ℝ))
    have h1 : c * x ≤ ∑ n ∈ Finset.range (x + 1), (r n : ℝ) := hx₀ x hx0
    have h2 : ∑ n ∈ Finset.range (x + 1), (r n : ℝ) ^ 2 ≤ C * x := hC x hx2
    rw [hsumA] at h1
    have hAcount : (A.card : ℝ) ≤ Nat.count (· ∈ S) (x + 1) := by
      rw [Nat.count_eq_card_filter_range]
      exact_mod_cast Finset.card_le_card (fun n hn => by
        simp only [A, Finset.mem_filter] at hn ⊢
        exact ⟨hn.1, memS n hn.2⟩)
    have hA0 : (0 : ℝ) ≤ A.card := by positivity
    have hcx : 0 ≤ c * x := by positivity
    have hsq : (c * x) ^ 2 ≤ A.card * (C * x) := by
      calc (c * x) ^ 2 ≤ (∑ n ∈ A, (r n : ℝ)) ^ 2 := pow_le_pow_left₀ hcx h1 2
        _ ≤ A.card * ∑ n ∈ A, (r n : ℝ) ^ 2 := hcs
        _ ≤ A.card * (C * x) := mul_le_mul_of_nonneg_left (hsqA.trans h2) hA0
    have hxpos : (0 : ℝ) < x := by linarith
    have hAlow : c ^ 2 * x ≤ A.card * C := by
      have : (c ^ 2 * x) * x ≤ (A.card * C) * x := by nlinarith
      exact le_of_mul_le_mul_right this hxpos
    rw [le_div_iff₀ (by positivity), hδ]
    push_cast
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      ((δ : ℝ) : EReal) ≤ (((Nat.count (· ∈ S) n : ℝ) : EReal) / ((n : ℝ) : EReal)) := by
    refine Filter.eventually_atTop.2 ⟨N + 1, fun n hn => ?_⟩
    obtain ⟨x, rfl⟩ : ∃ x, n = x + 1 := ⟨n - 1, by omega⟩
    rw [← EReal.coe_div]
    exact EReal.coe_le_coe_iff.2 (key x (by omega))
  calc (0 : EReal) < (δ : EReal) := EReal.coe_pos.2 hδpos
    _ ≤ _ := by convert Filter.le_liminf_of_le (by isBoundedDefault) hev

end OMA.R_Erdos16_erdos_16_variant_romanoff_R1

end R1Part

section RomanoffProof

-- Step H1 of reduction Erdos16.erdos_16.variant.romanoff.R1 (Romanoff).
-- Proof: Chebyshev bounds, the prime-pair upper sieve bound and the order-of-2 sum (Romanoff 1934).


/-
Mertens' theorems.

Elementary proofs, over the reals, of the three theorems of Mertens (1874):

* `OMALib.Mertens.abs_sum_log_div_sub_log_le` (first theorem):
  `|∑_{p ≤ x} log p / p - log x| ≤ mertens1Const + log 2` for `x ≥ 1`;
* `OMALib.Mertens.abs_sum_inv_sub_log_log_le` (second theorem):
  `|∑_{p ≤ x} 1 / p - log log x| ≤ mertens2Const` for `x ≥ 2`;
* `OMALib.Mertens.prod_one_sub_inv_bounds` (third theorem, product form):
  `exp (-c) / log z ≤ ∏_{p ≤ z} (1 - 1 / p) ≤ exp mertens2Const / log z` for `z ≥ 2`;

with existential forms `mertens1`, `mertens2`, `mertens3`. Sums over primes `p ≤ x` are written
`∑ p ∈ Nat.primesLE ⌊x⌋₊`, as in `Mathlib.NumberTheory.Chebyshev`.

The first theorem follows from Legendre's formula for `log N!`, the bounds
`N log N - N ≤ log N! ≤ N log N` and Chebyshev's bound `θ(N) ≤ N log 4`. The second follows
from the first by discrete partial summation, run as an induction on `N`. The third follows from
the second and `-t / (1 - t) ≤ log (1 - t) ≤ -t`.
-/

open scoped Classical

namespace OMALib.Mertens

open Real Finset

theorem log_factorial_eq_sum (N : ℕ) :
    Real.log (N.factorial : ℝ) =
      ∑ p ∈ Nat.primesLE N, ((N.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  apply Finsupp.sum_of_support_subset
  · intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    rw [Nat.mem_primesLE]
    exact ⟨(Nat.Prime.dvd_factorial hp.1).1 hp.2.1, hp.1⟩
  · intro p _
    simp

theorem div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (N : ℕ) :
    N / p ≤ N.factorial.factorization p := by
  rcases lt_or_ge N p with h | h
  · simp [Nat.div_eq_of_lt h]
  rw [Nat.factorization_factorial hp (Nat.lt_add_one (Nat.log p N))]
  have h1 : 1 ∈ Ico 1 (Nat.log p N + 1) := by
    simp only [mem_Ico, le_refl, true_and]
    have := Nat.log_pos hp.one_lt h
    omega
  have := Finset.single_le_sum (f := fun i => N / p ^ i) (fun i _ => Nat.zero_le _) h1
  simpa using this

theorem real_div_sub_one_le_nat_div (N p : ℕ) (hp : 0 < p) :
    (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := by
  have h := Nat.lt_div_mul_add (a := N) hp
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h2 : (N : ℝ) < ((N / p : ℕ) : ℝ) * p + p := by exact_mod_cast h
  rw [div_sub_one hp'.ne', div_le_iff₀ hp']
  linarith

theorem log_factorial_le (N : ℕ) : Real.log (N.factorial : ℝ) ≤ N * Real.log N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  rw [← Real.log_pow]
  apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos N)
  exact_mod_cast Nat.factorial_le_pow N

theorem log_factorial_ge (N : ℕ) : N * Real.log N - N ≤ Real.log (N.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h := Real.pow_div_factorial_le_exp (N : ℝ) (Nat.cast_nonneg N) N
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hNp : (0 : ℝ) < (N : ℝ) ^ N := by positivity
  have h2 := Real.log_le_log (by positivity) h
  rw [Real.log_exp, Real.log_div hNp.ne' hf.ne', Real.log_pow] at h2
  linarith


theorem summable_log_div_mul_sub_one :
    Summable (fun n : ℕ => Real.log n / ((n : ℝ) * ((n : ℝ) - 1))) := by
  have hs : Summable (fun n : ℕ => 4 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left 4
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
  · rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
      apply div_nonneg (Real.log_nonneg (by linarith))
      nlinarith
  · rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
      have hn : (0 : ℝ) < n := by linarith
      have hlog : Real.log n ≤ (n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) :=
        Real.log_le_rpow_div hn.le (by norm_num)
      have hsq : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) = n * n := by
        rw [← Real.rpow_add hn]; norm_num; ring
      have hpos : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hn _
      have hden : (n : ℝ) * n / 2 ≤ (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
      have hden0 : 0 < (n : ℝ) * n / 2 := by positivity
      calc Real.log n / ((n : ℝ) * ((n : ℝ) - 1))
          ≤ Real.log n / ((n : ℝ) * n / 2) :=
            div_le_div_of_nonneg_left (Real.log_nonneg (by linarith)) hden0 hden
        _ ≤ ((n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2)) / ((n : ℝ) * n / 2) :=
            div_le_div_of_nonneg_right hlog hden0.le
        _ = 4 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
            rw [← hsq]; field_simp; ring

/-- Mertens' first theorem, upper half, over the naturals. -/
theorem sum_log_div_le_nat (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ Real.log N + Real.log 4 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Nat.primesLE_zero, Finset.sum_empty, Nat.cast_zero, Real.log_zero, zero_add]
    exact Real.log_nonneg (by norm_num)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p - 1) ≤ Real.log (N.factorial : ℝ) := by
    rw [log_factorial_eq_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_right _ hl
    calc (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := real_div_sub_one_le_nat_div N p hpp.pos
      _ ≤ _ := by exact_mod_cast div_le_factorization_factorial hpp N
  have hsplit : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p - 1) =
      N * ∑ p ∈ Nat.primesLE N, Real.log p / p - Chebyshev.theta N := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hth := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hf := log_factorial_le N
  rw [hsplit] at key
  have : (N : ℝ) * ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ N * (Real.log N + Real.log 4) := by
    nlinarith
  exact le_of_mul_le_mul_left this hNr

/-- The convergent sum over primes of `log p / (p (p - 1))`, which bounds the contribution of
higher prime powers in Legendre's formula. -/
noncomputable def primePowerConst : ℝ := ∑' n : ℕ, Real.log n / ((n : ℝ) * ((n : ℝ) - 1))

theorem sum_log_div_mul_sub_one_le (s : Finset ℕ) :
    ∑ p ∈ s, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ primePowerConst := by
  apply summable_log_div_mul_sub_one.sum_le_tsum s
  intro n _
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> simp
  · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
    apply div_nonneg (Real.log_nonneg (by linarith))
    nlinarith

/-- Mertens' first theorem, lower half, over the naturals. -/
theorem sum_log_div_ge_nat (N : ℕ) :
    Real.log N - 1 - primePowerConst ≤ ∑ p ∈ Nat.primesLE N, Real.log p / p := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have := sum_log_div_mul_sub_one_le ∅
    simp at this ⊢
    linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : Real.log (N.factorial : ℝ) ≤
      ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [log_factorial_eq_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ hl
    have h1 : ((N.factorial.factorization p : ℕ) : ℝ) ≤ ((N / (p - 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorization_factorial_le_div_pred hpp N
    have h2 : ((N / (p - 1) : ℕ) : ℝ) ≤ (N : ℝ) / ((p - 1 : ℕ) : ℝ) := Nat.cast_div_le
    have h3 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hpp.one_lt.le]; simp
    rw [h3] at h2
    have h4 : (N : ℝ) / ((p : ℝ) - 1) = (N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1)) := by
      have : (p : ℝ) - 1 ≠ 0 := by linarith
      have : (p : ℝ) ≠ 0 := by linarith
      field_simp
      ring
    linarith
  have hsplit : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1))) =
      N * (∑ p ∈ Nat.primesLE N, Real.log p / p +
        ∑ p ∈ Nat.primesLE N, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hsplit] at key
  have hK := sum_log_div_mul_sub_one_le (Nat.primesLE N)
  have hf := log_factorial_ge N
  have : (N : ℝ) * (Real.log N - 1 - primePowerConst) ≤ N * ∑ p ∈ Nat.primesLE N, Real.log p / p := by
    nlinarith
  exact le_of_mul_le_mul_left this hNr


theorem primePowerConst_nonneg : 0 ≤ primePowerConst := by
  have := sum_log_div_mul_sub_one_le ∅
  simpa using this

/-- The constant in Mertens' first theorem proved here. -/
noncomputable def mertens1Const : ℝ := Real.log 4 + 1 + primePowerConst

theorem abs_sum_log_div_sub_log_le_nat (N : ℕ) :
    |∑ p ∈ Nat.primesLE N, Real.log p / p - Real.log N| ≤ mertens1Const := by
  have h1 := sum_log_div_le_nat N
  have h2 := sum_log_div_ge_nat N
  have h3 := primePowerConst_nonneg
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [abs_le]; unfold mertens1Const; constructor <;> linarith

theorem log_le_log_floor_add (x : ℝ) (hx : 1 ≤ x) :
    Real.log ⌊x⌋₊ ≤ Real.log x ∧ Real.log x ≤ Real.log ⌊x⌋₊ + Real.log 2 := by
  have hN1 : 1 ≤ ⌊x⌋₊ := Nat.one_le_floor_iff _ |>.mpr hx
  have hN : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hN1
  have hle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hlt : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
  constructor
  · exact Real.log_le_log (by linarith) hle
  · rw [← Real.log_mul (by linarith) (by norm_num)]
    apply Real.log_le_log (by linarith)
    linarith

/-- **Mertens' first theorem.** For real `x ≥ 1`,
`|∑_{p ≤ x} log p / p - log x| ≤ log 4 + log 2 + 1 + primePowerConst`. -/
theorem abs_sum_log_div_sub_log_le (x : ℝ) (hx : 1 ≤ x) :
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p - Real.log x| ≤ mertens1Const + Real.log 2 := by
  have h := abs_sum_log_div_sub_log_le_nat ⌊x⌋₊
  obtain ⟨h1, h2⟩ := log_le_log_floor_add x hx
  have h3 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- **Mertens' first theorem**, existential form. -/
theorem mertens1 : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p - Real.log x| ≤ C :=
  ⟨mertens1Const + Real.log 2, fun x hx => abs_sum_log_div_sub_log_le x (by linarith)⟩

theorem sum_succ_eq (N : ℕ) (f : ℕ → ℝ) :
    ∑ p ∈ Nat.primesLE (N + 1), f p =
      (∑ p ∈ Nat.primesLE N, f p) + if (N + 1).Prime then f (N + 1) else 0 := by
  rw [Nat.primesLE_succ]
  split_ifs with h
  · rw [Finset.sum_insert, add_comm]
    intro hm
    have := (Nat.mem_primesLE.mp hm).1
    omega
  · simp

theorem recip_step (N : ℕ) :
    (∑ p ∈ Nat.primesLE (N + 1), (1 : ℝ) / p) - ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p =
      ((∑ p ∈ Nat.primesLE (N + 1), Real.log p / p) - ∑ p ∈ Nat.primesLE N, Real.log p / p) /
        Real.log ((N + 1 : ℕ) : ℝ) := by
  rw [sum_succ_eq, sum_succ_eq]
  split_ifs with h
  · have hl : 0 < Real.log ((N + 1 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast h.one_lt)
    field_simp
    ring
  · simp


/-- Elementary comparison of `log b - log a` with `(b - a) / b`, for `0 < a ≤ b ≤ a + 1`. -/
theorem abs_log_sub_log_sub_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ a + 1) :
    |(b - a) / b - (Real.log b - Real.log a)| ≤ 1 / a - 1 / b := by
  have hb : 0 < b := by linarith
  have hq : 0 < b / a := div_pos hb ha
  have hlog : Real.log b - Real.log a = Real.log (b / a) := (Real.log_div hb.ne' ha.ne').symm
  have hup := Real.log_le_sub_one_of_pos hq
  have hlo := Real.one_sub_inv_le_log_of_pos hq
  rw [inv_div] at hlo
  rw [hlog]
  have e1 : (b - a) / b = 1 - a / b := by field_simp
  have e2 : 1 / a - 1 / b = (b - a) / (a * b) := by field_simp
  have e3 : b / a - 1 - (1 - a / b) = (b - a) * ((b - a) / (a * b)) := by field_simp
  have hnn : 0 ≤ (b - a) / (a * b) := div_nonneg (by linarith) (by positivity)
  have e4 : (b - a) * ((b - a) / (a * b)) ≤ (b - a) / (a * b) := by
    have : b - a ≤ 1 := by linarith
    nlinarith
  rw [abs_le, e2, e1]
  constructor <;> nlinarith

/-- Partial sums used in the proof of Mertens' second theorem. -/
noncomputable def mertensG (N : ℕ) : ℝ :=
  (∑ p ∈ Nat.primesLE N, (1 : ℝ) / p) - Real.log (Real.log N) -
    ((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N

theorem mertensG_step (N : ℕ) (hN : 2 ≤ N) :
    |mertensG (N + 1) - mertensG N| ≤
      (mertens1Const + 1) * (1 / Real.log N - 1 / Real.log ((N + 1 : ℕ) : ℝ)) := by
  set a := Real.log N with ha_def
  set b := Real.log ((N + 1 : ℕ) : ℝ) with hb_def
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have ha : 0 < a := Real.log_pos (by linarith)
  have hab : a ≤ b := Real.log_le_log (by linarith) (by push_cast; linarith)
  have hb : 0 < b := by linarith
  have hb1 : b ≤ a + 1 := by
    have h1 : b - a = Real.log (((N + 1 : ℕ) : ℝ) / N) :=
      (Real.log_div (by positivity) (by positivity)).symm
    have h2 := Real.log_le_sub_one_of_pos (x := ((N + 1 : ℕ) : ℝ) / N) (by positivity)
    have h3 : ((N + 1 : ℕ) : ℝ) / N - 1 ≤ 1 := by
      push_cast
      rw [div_sub_one (by linarith), div_le_iff₀ (by linarith)]
      linarith
    linarith
  set S0 := ∑ p ∈ Nat.primesLE N, Real.log p / p
  set S1 := ∑ p ∈ Nat.primesLE (N + 1), Real.log p / p
  set F0 := ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p
  set F1 := ∑ p ∈ Nat.primesLE (N + 1), (1 : ℝ) / p
  have hstep : F1 - F0 = (S1 - S0) / b := recip_step N
  have hR : |S0 - a| ≤ mertens1Const := abs_sum_log_div_sub_log_le_nat N
  have hdiff : mertensG (N + 1) - mertensG N =
      (S0 - a) * (1 / a - 1 / b) + ((b - a) / b - (Real.log b - Real.log a)) := by
    have e : mertensG (N + 1) - mertensG N =
        (F1 - F0) - (Real.log b - Real.log a) - (S1 - b) / b + (S0 - a) / a := by
      simp only [mertensG]
      ring
    rw [e, hstep]
    field_simp
    ring
  have hE := abs_log_sub_log_sub_le ha hab hb1
  have hpos : 0 ≤ 1 / a - 1 / b := by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le ha hab
  rw [hdiff]
  calc |(S0 - a) * (1 / a - 1 / b) + ((b - a) / b - (Real.log b - Real.log a))|
      ≤ |(S0 - a) * (1 / a - 1 / b)| + |(b - a) / b - (Real.log b - Real.log a)| := abs_add_le _ _
    _ ≤ mertens1Const * (1 / a - 1 / b) + (1 / a - 1 / b) := by
      rw [abs_mul, abs_of_nonneg hpos]
      gcongr
    _ = (mertens1Const + 1) * (1 / a - 1 / b) := by ring

theorem abs_mertensG_sub_le (N : ℕ) (hN : 2 ≤ N) :
    |mertensG N - mertensG 2| ≤ (mertens1Const + 1) * (1 / Real.log 2 - 1 / Real.log N) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hs := mertensG_step n hn
    calc |mertensG (n + 1) - mertensG 2|
        = |(mertensG (n + 1) - mertensG n) + (mertensG n - mertensG 2)| := by ring_nf
      _ ≤ |mertensG (n + 1) - mertensG n| + |mertensG n - mertensG 2| := abs_add_le _ _
      _ ≤ _ := add_le_add hs ih
      _ = _ := by push_cast; ring


/-- The constant in Mertens' second theorem over the naturals. -/
noncomputable def mertens2NatConst : ℝ :=
  |mertensG 2| + (2 * mertens1Const + 1) / Real.log 2

theorem mertens1Const_nonneg : 0 ≤ mertens1Const := by
  have := primePowerConst_nonneg
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold mertens1Const; linarith

/-- **Mertens' second theorem** over the naturals: for `N ≥ 2`,
`|∑_{p ≤ N} 1 / p - log log N| ≤ mertens2NatConst`. -/
theorem abs_sum_inv_sub_log_log_le_nat (N : ℕ) (hN : 2 ≤ N) :
    |∑ p ∈ Nat.primesLE N, (1 : ℝ) / p - Real.log (Real.log N)| ≤ mertens2NatConst := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlN : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN2
  have hlN0 : 0 < Real.log N := by linarith
  have hG := abs_mertensG_sub_le N hN
  have hR := abs_sum_log_div_sub_log_le_nat N
  have hC := mertens1Const_nonneg
  have e : ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p - Real.log (Real.log N) =
      mertensG 2 + (mertensG N - mertensG 2) +
        ((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N := by
    rw [show mertensG 2 + (mertensG N - mertensG 2) = mertensG N by ring]
    unfold mertensG; ring
  rw [e]
  have h1 : |((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N| ≤
      mertens1Const / Real.log 2 := by
    rw [abs_div, abs_of_pos hlN0]
    calc _ ≤ mertens1Const / Real.log N := div_le_div_of_nonneg_right hR hlN0.le
      _ ≤ mertens1Const / Real.log 2 := div_le_div_of_nonneg_left hC hl2 hlN
  have h2 : (mertens1Const + 1) * (1 / Real.log 2 - 1 / Real.log N) ≤
      (mertens1Const + 1) / Real.log 2 := by
    have : 0 ≤ 1 / Real.log N := by positivity
    have : (mertens1Const + 1) * (1 / Real.log 2 - 1 / Real.log N) ≤
        (mertens1Const + 1) * (1 / Real.log 2) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
    rw [div_eq_mul_one_div (mertens1Const + 1)]
    exact this
  have h3 : mertens2NatConst =
      |mertensG 2| + (mertens1Const + 1) / Real.log 2 + mertens1Const / Real.log 2 := by
    unfold mertens2NatConst; ring
  rw [h3]
  calc _ ≤ |mertensG 2 + (mertensG N - mertensG 2)| +
        |((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N| := abs_add_le _ _
    _ ≤ |mertensG 2| + |mertensG N - mertensG 2| +
        |((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N| := by
      gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith

theorem log_log_floor_le (x : ℝ) (hx : 2 ≤ x) :
    Real.log (Real.log ⌊x⌋₊) ≤ Real.log (Real.log x) ∧
      Real.log (Real.log x) ≤ Real.log (Real.log ⌊x⌋₊) + 1 := by
  have hN2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hN2r : (2 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hN2
  have hlN : Real.log 2 ≤ Real.log ⌊x⌋₊ := Real.log_le_log (by norm_num) hN2r
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlN0 : 0 < Real.log ⌊x⌋₊ := by linarith
  obtain ⟨h1, h2⟩ := log_le_log_floor_add x (by linarith)
  have hlx : 0 < Real.log x := by linarith
  constructor
  · exact Real.log_le_log hlN0 h1
  · have hq := Real.log_le_sub_one_of_pos (div_pos hlx hlN0)
    rw [Real.log_div hlx.ne' hlN0.ne'] at hq
    have : Real.log x / Real.log ⌊x⌋₊ - 1 ≤ 1 := by
      rw [div_sub_one hlN0.ne', div_le_iff₀ hlN0]; linarith
    linarith

/-- The constant in Mertens' second theorem over the reals. -/
noncomputable def mertens2Const : ℝ := mertens2NatConst + 1

/-- **Mertens' second theorem.** For real `x ≥ 2`,
`|∑_{p ≤ x} 1 / p - log log x| ≤ mertens2Const`. -/
theorem abs_sum_inv_sub_log_log_le (x : ℝ) (hx : 2 ≤ x) :
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p - Real.log (Real.log x)| ≤ mertens2Const := by
  have hN2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have h := abs_sum_inv_sub_log_log_le_nat ⌊x⌋₊ hN2
  obtain ⟨h1, h2⟩ := log_log_floor_le x hx
  unfold mertens2Const
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- **Mertens' second theorem**, existential form. -/
theorem mertens2 : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p - Real.log (Real.log x)| ≤ C :=
  ⟨mertens2Const, abs_sum_inv_sub_log_log_le⟩

theorem log_one_sub_inv_bounds {p : ℕ} (hp : p.Prime) :
    -(1 / (p : ℝ)) - Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) / Real.log 2 ≤
        Real.log (1 - 1 / (p : ℝ)) ∧
      Real.log (1 - 1 / (p : ℝ)) ≤ -(1 / (p : ℝ)) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpos : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos hpos
    have e : 1 - (1 - 1 / (p : ℝ))⁻¹ = -(1 / (p : ℝ)) - 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
      have : (p : ℝ) - 1 ≠ 0 := by linarith
      have : (p : ℝ) ≠ 0 := by linarith
      field_simp
      ring
    rw [e] at h
    have hden : 0 < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
    have hlp : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp2
    have : 1 / ((p : ℝ) * ((p : ℝ) - 1)) ≤
        Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) / Real.log 2 := by
      rw [div_div, div_le_div_iff₀ hden (by positivity)]
      nlinarith
    linarith
  · have h := Real.log_le_sub_one_of_pos hpos
    linarith

/-- **Mertens' third theorem**, explicit form. For real `z ≥ 2`,
`exp (-c) / log z ≤ ∏_{p ≤ z} (1 - 1 / p) ≤ exp (mertens2Const) / log z`
with `c = mertens2Const + primePowerConst / log 2`. -/
theorem prod_one_sub_inv_bounds (z : ℝ) (hz : 2 ≤ z) :
    Real.exp (-(mertens2Const + primePowerConst / Real.log 2)) / Real.log z ≤
        ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ)) ∧
      ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ)) ≤ Real.exp mertens2Const / Real.log z := by
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hne : ∀ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ)) ≠ 0 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    intro h; linarith
  have hPpos : 0 < ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ)) := by
    apply Finset.prod_pos
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    linarith
  have hlogP := Real.log_prod (s := Nat.primesLE ⌊z⌋₊) (f := fun p => (1 - 1 / (p : ℝ))) hne
  have hup : Real.log (∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ))) ≤
      -∑ p ∈ Nat.primesLE ⌊z⌋₊, (1 : ℝ) / p := by
    rw [hlogP, ← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun p hp => (log_one_sub_inv_bounds (Nat.mem_primesLE.mp hp).2).2
  have hlo : -∑ p ∈ Nat.primesLE ⌊z⌋₊, (1 : ℝ) / p - primePowerConst / Real.log 2 ≤
      Real.log (∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ))) := by
    rw [hlogP]
    have hK := sum_log_div_mul_sub_one_le (Nat.primesLE ⌊z⌋₊)
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hK' : ∑ p ∈ Nat.primesLE ⌊z⌋₊, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) / Real.log 2 ≤
        primePowerConst / Real.log 2 := by
      rw [← Finset.sum_div]; exact div_le_div_of_nonneg_right hK hl2.le
    have hs := Finset.sum_le_sum (s := Nat.primesLE ⌊z⌋₊) fun p hp =>
      (log_one_sub_inv_bounds (Nat.mem_primesLE.mp hp).2).1
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hs
    linarith
  have hM := abs_sum_inv_sub_log_log_le z hz
  rw [abs_le] at hM
  have hexp : ∀ t : ℝ, Real.exp t / Real.log z = Real.exp (t - Real.log (Real.log z)) := by
    intro t
    rw [Real.exp_sub, Real.exp_log hlz]
  rw [hexp, hexp, ← Real.exp_log hPpos]
  constructor
  · apply Real.exp_le_exp.mpr; linarith [hM.1, hM.2]
  · apply Real.exp_le_exp.mpr; linarith [hM.1, hM.2]

/-- **Mertens' third theorem**, existential form: there are constants `0 < c₁` and `c₂` with
`c₁ / log z ≤ ∏_{p ≤ z} (1 - 1 / p) ≤ c₂ / log z` for all real `z ≥ 2`. -/
theorem mertens3 : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ z : ℝ, 2 ≤ z →
    c₁ / Real.log z ≤ ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ)) ∧
      ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ)) ≤ c₂ / Real.log z :=
  ⟨_, _, Real.exp_pos _, Real.exp_pos _, prod_one_sub_inv_bounds⟩


/-- Upper half of Mertens' second theorem for any subset of the primes, for instance the primes
in a residue class: `∑_{p ≤ x, P p} 1 / p ≤ log log x + mertens2Const` for real `x ≥ 2`. -/
theorem sum_inv_filter_le (P : ℕ → Prop) [DecidablePred P] (x : ℝ) (hx : 2 ≤ x) :
    ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter P, (1 : ℝ) / p ≤
      Real.log (Real.log x) + mertens2Const := by
  have h := abs_sum_inv_sub_log_log_le x hx
  rw [abs_le] at h
  have hsub : ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter P, (1 : ℝ) / p ≤
      ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun p _ _ => by positivity)
  linarith [h.2]

end OMALib.Mertens


open scoped Classical
open Finset

namespace OMALib.Sieve

variable {ι : Type*} [DecidableEq ι]

/-- The Selberg function `h(p) = g(p)/(1 - g(p))` attached to a local density `g`. -/
noncomputable def hFun (g : ι → ℝ) (p : ι) : ℝ := g p / (1 - g p)

/-- Selberg's normaliser `G = Σ_{S ∈ D} Π_{p ∈ S} h(p)` for a support family `D`. -/
noncomputable def selbergG (g : ι → ℝ) (D : Finset (Finset ι)) : ℝ :=
  ∑ S ∈ D, ∏ p ∈ S, hFun g p

/-- The optimal Selberg weights
`λ_S = (-1)^{|S|} (Π_{p∈S} g(p)⁻¹) G⁻¹ Σ_{T ∈ D, S ⊆ T} Π_{p∈T} h(p)`. -/
noncomputable def selbergWeight (g : ι → ℝ) (D : Finset (Finset ι)) (S : Finset ι) : ℝ :=
  (-1) ^ S.card * (∏ p ∈ S, (g p)⁻¹) / selbergG g D * ∑ T ∈ D with S ⊆ T, ∏ p ∈ T, hFun g p

/-- Inclusion-exclusion over an interval `[U, T]` of the subset lattice. -/
theorem sum_interval_neg_one_pow {U T : Finset ι} (hUT : U ⊆ T) :
    ∑ S ∈ T.powerset with U ⊆ S, ((-1 : ℝ)) ^ S.card = if T = U then (-1) ^ U.card else 0 := by
  have h1 : ∑ S ∈ T.powerset with U ⊆ S, ((-1 : ℝ)) ^ S.card
      = ∑ V ∈ (T \ U).powerset, (-1 : ℝ) ^ U.card * (-1) ^ V.card := by
    refine Finset.sum_nbij' (fun S => S \ U) (fun V => U ∪ V) ?_ ?_ ?_ ?_ ?_
    · intro S hS
      simp only [mem_filter, mem_powerset, coe_filter, mem_coe] at hS ⊢
      exact sdiff_subset_sdiff hS.1 le_rfl
    · intro V hV
      simp only [mem_filter, mem_powerset, coe_filter, mem_coe] at hV ⊢
      refine ⟨union_subset hUT (hV.trans sdiff_subset), subset_union_left⟩
    · intro S hS
      simp only [mem_filter, mem_powerset, coe_filter, mem_coe] at hS
      exact union_sdiff_of_subset hS.2
    · intro V hV
      simp only [mem_powerset, mem_coe] at hV
      have : Disjoint U V := by
        rw [disjoint_iff_ne]; intro a ha b hb hab; subst hab
        have := hV hb; simp at this; exact this.2 ha
      exact union_sdiff_cancel_left this
    · intro S hS
      simp only [mem_filter, mem_powerset, coe_filter, mem_coe] at hS
      rw [← pow_add, add_comm, card_sdiff_add_card_eq_card hS.2]
  have h2 : ∑ V ∈ (T \ U).powerset, ((-1 : ℝ)) ^ V.card = if T \ U = ∅ then 1 else 0 := by
    have := congrArg (Int.cast : ℤ → ℝ) (sum_powerset_neg_one_pow_card (x := T \ U))
    push_cast at this
    rw [this]
  rw [h1, ← mul_sum, h2]
  have : T \ U = ∅ ↔ T = U := by
    constructor
    · intro h; exact Subset.antisymm (sdiff_eq_empty_iff_subset.mp h) hUT
    · intro h; subst h; simp
  by_cases hT : T = U
  · simp [hT]
  · rw [if_neg (by rwa [this]), if_neg hT, mul_zero]

section Abstract

variable {Q : Finset ι} {g : ι → ℝ} {D : Finset (Finset ι)}

theorem hFun_pos (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1) {p : ι} (hp : p ∈ Q) :
    0 < hFun g p := div_pos (hg0 p hp) (by linarith [hg1 p hp])

theorem prod_hFun_pos (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1) {S : Finset ι}
    (hS : S ⊆ Q) : 0 < ∏ p ∈ S, hFun g p :=
  prod_pos fun p hp => hFun_pos hg0 hg1 (hS hp)

/-- `G ≥ 1`, since the empty set contributes `1`. -/
theorem one_le_selbergG (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1)
    (hDQ : ∀ S ∈ D, S ⊆ Q) (hemp : ∅ ∈ D) : 1 ≤ selbergG g D := by
  unfold selbergG
  have := single_le_sum (f := fun S => ∏ p ∈ S, hFun g p)
    (fun S hS => (prod_hFun_pos hg0 hg1 (hDQ S hS)).le) hemp
  simpa using this

theorem selbergWeight_mul_prod (hg0 : ∀ p ∈ Q, 0 < g p) {S : Finset ι} (hS : S ⊆ Q) :
    selbergWeight g D S * ∏ p ∈ S, g p
      = (-1) ^ S.card / selbergG g D * ∑ T ∈ D with S ⊆ T, ∏ p ∈ T, hFun g p := by
  unfold selbergWeight
  have h : (∏ p ∈ S, (g p)⁻¹) * ∏ p ∈ S, g p = 1 := by
    rw [← prod_mul_distrib]
    exact prod_eq_one fun p hp => inv_mul_cancel₀ (hg0 p (hS hp)).ne'
  calc _ = (-1) ^ S.card / selbergG g D * (∑ T ∈ D with S ⊆ T, ∏ p ∈ T, hFun g p) *
        ((∏ p ∈ S, (g p)⁻¹) * ∏ p ∈ S, g p) := by ring
    _ = _ := by rw [h, mul_one]

/-- The diagonalising variables `y_U = Σ_{S ∈ D, U ⊆ S} λ_S g(S)` of the Selberg weights. -/
theorem selbergY (hg0 : ∀ p ∈ Q, 0 < g p) (hDQ : ∀ S ∈ D, S ⊆ Q)
    (hdown : ∀ S ∈ D, ∀ T ⊆ S, T ∈ D) (U : Finset ι) :
    ∑ S ∈ D with U ⊆ S, selbergWeight g D S * ∏ p ∈ S, g p
      = if U ∈ D then (-1) ^ U.card * (∏ p ∈ U, hFun g p) / selbergG g D else 0 := by
  set G := selbergG g D
  set hS : Finset ι → ℝ := fun T => ∏ p ∈ T, hFun g p
  have e1 : ∑ S ∈ D with U ⊆ S, selbergWeight g D S * ∏ p ∈ S, g p
      = ∑ S ∈ D, ∑ T ∈ D, if U ⊆ S ∧ S ⊆ T then (-1) ^ S.card / G * hS T else 0 := by
    rw [sum_filter]
    refine sum_congr rfl fun S hSD => ?_
    by_cases hU : U ⊆ S
    · rw [if_pos hU, selbergWeight_mul_prod hg0 (hDQ S hSD), mul_sum, sum_filter]
      refine sum_congr rfl fun T _ => ?_
      by_cases hST : S ⊆ T <;> simp [hU, hST, hS, G]
    · rw [if_neg hU]; symm
      exact sum_eq_zero fun T _ => by simp [hU]
  rw [e1, sum_comm]
  have e2 : ∀ T ∈ D, (∑ S ∈ D, if U ⊆ S ∧ S ⊆ T then (-1) ^ S.card / G * hS T else 0)
      = if T = U then (-1) ^ U.card / G * hS U else 0 := by
    intro T hT
    rw [← sum_filter]
    by_cases hUT : U ⊆ T
    · have hf : D.filter (fun S => U ⊆ S ∧ S ⊆ T) = T.powerset.filter (fun S => U ⊆ S) := by
        ext S; simp only [mem_filter, mem_powerset]
        constructor
        · rintro ⟨_, h1, h2⟩; exact ⟨h2, h1⟩
        · rintro ⟨h2, h1⟩; exact ⟨hdown T hT S h2, h1, h2⟩
      rw [hf, ← sum_mul, ← sum_div, sum_interval_neg_one_pow hUT]
      by_cases hTU : T = U
      · subst hTU; simp
      · simp [hTU]
    · have hTU : T ≠ U := by rintro rfl; exact hUT le_rfl
      rw [if_neg hTU]
      refine sum_eq_zero fun S hS' => ?_
      simp only [mem_filter] at hS'
      exact absurd (hS'.2.1.trans hS'.2.2) hUT
  rw [sum_congr rfl e2, sum_ite_eq']
  split_ifs <;> ring

theorem prod_union_eq (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1) {S₁ S₂ : Finset ι}
    (h₁ : S₁ ⊆ Q) (h₂ : S₂ ⊆ Q) :
    ∏ p ∈ S₁ ∪ S₂, g p = (∏ p ∈ S₁, g p) * (∏ p ∈ S₂, g p) *
      ∑ U ∈ Q.powerset, if U ⊆ S₁ ∧ U ⊆ S₂ then (∏ p ∈ U, hFun g p)⁻¹ else 0 := by
  have hinv : (∏ p ∈ S₁ ∩ S₂, g p)⁻¹ = ∑ U ∈ (S₁ ∩ S₂).powerset, (∏ p ∈ U, hFun g p)⁻¹ := by
    rw [← prod_inv_distrib]
    have : ∀ p ∈ S₁ ∩ S₂, (g p)⁻¹ = 1 + (hFun g p)⁻¹ := by
      intro p hp
      have hp' : p ∈ Q := h₁ (mem_inter.mp hp).1
      have a := hg0 p hp'; have b := hg1 p hp'
      unfold hFun; rw [inv_div]; field_simp; ring
    rw [prod_congr rfl this, prod_one_add]
    exact sum_congr rfl fun U _ => by rw [prod_inv_distrib]
  have hsum : ∑ U ∈ Q.powerset, (if U ⊆ S₁ ∧ U ⊆ S₂ then (∏ p ∈ U, hFun g p)⁻¹ else 0)
      = ∑ U ∈ (S₁ ∩ S₂).powerset, (∏ p ∈ U, hFun g p)⁻¹ := by
    rw [← sum_filter]
    congr 1
    ext U; simp only [mem_filter, mem_powerset, subset_inter_iff]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨h.1.trans h₁, h⟩
  have hne : (∏ p ∈ S₁ ∩ S₂, g p) ≠ 0 :=
    (prod_pos fun p hp => hg0 p (h₁ (mem_inter.mp hp).1)).ne'
  rw [hsum, ← hinv, ← prod_union_inter (s₁ := S₁) (s₂ := S₂)]
  field_simp

/-- The Selberg quadratic form evaluated at the optimal weights equals `1 / G`. -/
theorem selberg_mainTerm (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1)
    (hDQ : ∀ S ∈ D, S ⊆ Q) (hdown : ∀ S ∈ D, ∀ T ⊆ S, T ∈ D) (hemp : ∅ ∈ D) :
    ∑ S₁ ∈ D, ∑ S₂ ∈ D, selbergWeight g D S₁ * selbergWeight g D S₂ * ∏ p ∈ S₁ ∪ S₂, g p
      = 1 / selbergG g D := by
  set G := selbergG g D with hG
  set a : Finset ι → ℝ := fun S => selbergWeight g D S * ∏ p ∈ S, g p
  set w : Finset ι → ℝ := fun U => (∏ p ∈ U, hFun g p)⁻¹
  have hG1 : 1 ≤ G := one_le_selbergG hg0 hg1 hDQ hemp
  have e1 : ∀ S₁ ∈ D, ∀ S₂ ∈ D,
      selbergWeight g D S₁ * selbergWeight g D S₂ * ∏ p ∈ S₁ ∪ S₂, g p
        = ∑ U ∈ Q.powerset, w U * ((if U ⊆ S₁ then a S₁ else 0) * (if U ⊆ S₂ then a S₂ else 0)) := by
    intro S₁ h₁ S₂ h₂
    rw [prod_union_eq hg0 hg1 (hDQ _ h₁) (hDQ _ h₂), mul_sum, mul_sum]
    refine sum_congr rfl fun U _ => ?_
    by_cases u1 : U ⊆ S₁ <;> by_cases u2 : U ⊆ S₂ <;> simp [u1, u2, a, w] <;> ring
  rw [sum_congr rfl fun S₁ h₁ => sum_congr rfl fun S₂ h₂ => e1 S₁ h₁ S₂ h₂]
  have eswap : ∑ S₁ ∈ D, ∑ S₂ ∈ D, ∑ U ∈ Q.powerset,
      w U * ((if U ⊆ S₁ then a S₁ else 0) * (if U ⊆ S₂ then a S₂ else 0))
      = ∑ U ∈ Q.powerset, w U * ((∑ S ∈ D with U ⊆ S, a S) * (∑ S ∈ D with U ⊆ S, a S)) := by
    simp_rw [sum_filter, sum_mul_sum, mul_sum]
    conv_lhs => arg 2; ext S₁; rw [sum_comm]
    rw [sum_comm]
  rw [eswap]
  have hy : ∀ U, ∑ S ∈ D with U ⊆ S, a S
      = if U ∈ D then (-1) ^ U.card * (∏ p ∈ U, hFun g p) / G else 0 :=
    selbergY hg0 hDQ hdown
  simp_rw [hy]
  have e3 : ∀ U ∈ Q.powerset, w U * ((if U ∈ D then (-1) ^ U.card * (∏ p ∈ U, hFun g p) / G else 0) *
      (if U ∈ D then (-1) ^ U.card * (∏ p ∈ U, hFun g p) / G else 0))
      = if U ∈ D then (∏ p ∈ U, hFun g p) / G ^ 2 else 0 := by
    intro U hU
    split_ifs with hUD
    · have hpos := prod_hFun_pos hg0 hg1 (hDQ U hUD)
      simp only [w]
      field_simp
      rw [← pow_mul, mul_comm (U.card) 2, pow_mul]; simp
    · simp
  rw [sum_congr rfl e3, ← sum_filter]
  have : Q.powerset.filter (fun U => U ∈ D) = D := by
    ext U; simp only [mem_filter, mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨hDQ U h, h⟩⟩
  rw [this, ← sum_div]
  change G / G ^ 2 = 1 / G
  field_simp

/-- The optimal Selberg weights satisfy `|λ_S| ≤ 1`. -/
theorem abs_selbergWeight_le (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1)
    (hDQ : ∀ S ∈ D, S ⊆ Q) (hdown : ∀ S ∈ D, ∀ T ⊆ S, T ∈ D) (hemp : ∅ ∈ D)
    {S : Finset ι} (hS : S ∈ D) : |selbergWeight g D S| ≤ 1 := by
  set G := selbergG g D with hG
  set hp : Finset ι → ℝ := fun T => ∏ p ∈ T, hFun g p
  have hG1 : 1 ≤ G := one_le_selbergG hg0 hg1 hDQ hemp
  have hSQ := hDQ S hS
  have hnn : ∀ T ⊆ Q, 0 ≤ hp T := fun T hT => (prod_hFun_pos hg0 hg1 hT).le
  have hginv : 0 < ∏ p ∈ S, (g p)⁻¹ := prod_pos fun p h => inv_pos.mpr (hg0 p (hSQ h))
  have habs : |selbergWeight g D S|
      = (∏ p ∈ S, (g p)⁻¹) * (∑ T ∈ D with S ⊆ T, hp T) / G := by
    unfold selbergWeight
    rw [abs_mul, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos hginv, abs_of_pos (by linarith : (0:ℝ) < G),
      abs_of_nonneg (sum_nonneg fun T hT => hnn T (hDQ T (mem_filter.mp hT).1))]
    ring
  rw [habs, div_le_one (by linarith)]
  have key : ∀ T ∈ D.filter (fun T => S ⊆ T),
      (∏ p ∈ S, (g p)⁻¹) * hp T = ∑ W ∈ S.powerset, hp (W ∪ (T \ S)) := by
    intro T hT
    have hST := (mem_filter.mp hT).2
    have h1 : hp T = hp S * hp (T \ S) := by
      simp only [hp]; rw [mul_comm, prod_sdiff hST]
    have h2 : (∏ p ∈ S, (g p)⁻¹) * hp S = ∏ p ∈ S, (1 + hFun g p) := by
      simp only [hp]; rw [← prod_mul_distrib]
      refine prod_congr rfl fun p h => ?_
      have a := hg0 p (hSQ h); have b := hg1 p (hSQ h)
      have c : 1 - g p ≠ 0 := by linarith
      unfold hFun; field_simp; ring
    rw [h1, ← mul_assoc, h2, prod_one_add, sum_mul]
    refine sum_congr rfl fun W hW => ?_
    simp only [hp]
    rw [prod_union]
    exact disjoint_of_subset_left (mem_powerset.mp hW) disjoint_sdiff
  rw [mul_sum, sum_congr rfl key, sum_comm, ← sum_product']
  rw [← sum_image (s := S.powerset ×ˢ D.filter (fun T => S ⊆ T)) (g := fun x => x.1 ∪ (x.2 \ S))
    (f := hp)]
  · apply sum_le_sum_of_subset_of_nonneg
    · intro U hU
      simp only [mem_image, mem_product, mem_powerset, mem_filter] at hU
      obtain ⟨⟨W, T⟩, ⟨hW, hT, _⟩, rfl⟩ := hU
      exact hdown T hT _ (union_subset (hW.trans (by assumption)) sdiff_subset)
    · intro U hU _
      exact hnn U (hDQ U hU)
  · intro x hx y hy hxy
    simp only [coe_product, Set.mem_prod, mem_coe, mem_powerset, mem_filter] at hx hy
    simp only at hxy
    have e1 : x.1 = (x.1 ∪ (x.2 \ S)) ∩ S := by
      rw [union_inter_distrib_right, sdiff_inter_self, union_empty, inter_eq_left.mpr hx.1]
    have e2 : y.1 = (y.1 ∪ (y.2 \ S)) ∩ S := by
      rw [union_inter_distrib_right, sdiff_inter_self, union_empty, inter_eq_left.mpr hy.1]
    have f1 : x.2 = S ∪ (x.1 ∪ (x.2 \ S)) := by
      rw [← union_assoc, union_eq_left.mpr hx.1, union_sdiff_of_subset hx.2.2]
    have f2 : y.2 = S ∪ (y.1 ∪ (y.2 \ S)) := by
      rw [← union_assoc, union_eq_left.mpr hy.1, union_sdiff_of_subset hy.2.2]
    exact Prod.ext (by rw [e1, e2, hxy]) (by rw [f1, f2, hxy])

theorem selbergWeight_empty (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1)
    (hDQ : ∀ S ∈ D, S ⊆ Q) (hemp : ∅ ∈ D) : selbergWeight g D ∅ = 1 := by
  have hG1 : 1 ≤ selbergG g D := one_le_selbergG hg0 hg1 hDQ hemp
  unfold selbergWeight
  simp only [card_empty, pow_zero, prod_empty, one_mul, empty_subset, filter_true_of_mem,
    implies_true]
  change 1 / selbergG g D * selbergG g D = 1
  field_simp

/-- **Selberg's upper-bound sieve, abstract form.**

`A` is a finite family of objects, `E a` is the set of primes dividing `a`, `Q` is the finite
set of sieving primes, and `D` is any down-closed family of subsets of `Q` containing `∅` (the
support of the Selberg weights; for the classical sieve, the sets of primes with product `< z`).
If for every `S ⊆ Q` the number of `a` divisible by all of `S` is `X * Π_{p∈S} g p + r S`, with
`0 < g p < 1`, then the number of `a` free of all primes of `Q` is at most
`X / G + Σ_{S₁, S₂ ∈ D} |r (S₁ ∪ S₂)|`, where `G = selbergG g D`. -/
theorem selberg_sieve_abstract {α : Type*} (A : Finset α) (E : α → Finset ι)
    (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1)
    (hDQ : ∀ S ∈ D, S ⊆ Q) (hdown : ∀ S ∈ D, ∀ T ⊆ S, T ∈ D) (hemp : ∅ ∈ D)
    (X : ℝ) (r : Finset ι → ℝ)
    (hr : ∀ S ⊆ Q, ((A.filter (fun a => S ⊆ E a)).card : ℝ) = X * ∏ p ∈ S, g p + r S) :
    ((A.filter (fun a => Disjoint Q (E a))).card : ℝ)
      ≤ X / selbergG g D + ∑ S₁ ∈ D, ∑ S₂ ∈ D, |r (S₁ ∪ S₂)| := by
  set lam := selbergWeight g D
  have step1 : ((A.filter (fun a => Disjoint Q (E a))).card : ℝ)
      ≤ ∑ a ∈ A, (∑ S ∈ D, if S ⊆ E a then lam S else 0) ^ 2 := by
    rw [card_filter]; push_cast
    refine sum_le_sum fun a _ => ?_
    split_ifs with hd
    · have : (∑ S ∈ D, if S ⊆ E a then lam S else 0) = lam ∅ := by
        have e := sum_ite_eq' D ∅ lam
        rw [if_pos hemp] at e
        rw [← e]
        refine sum_congr rfl fun S hS => ?_
        by_cases hS0 : S = ∅
        · subst hS0; simp
        · have : ¬ S ⊆ E a := by
            intro h
            apply hS0
            exact subset_empty.mp fun x hx =>
              (disjoint_left.mp hd (hDQ S hS hx) (h hx)).elim
          simp [this, hS0, Ne.symm hS0]
      have e1 : lam ∅ = 1 := selbergWeight_empty hg0 hg1 hDQ hemp
      rw [this, e1]; norm_num
    · positivity
  have step2 : ∑ a ∈ A, (∑ S ∈ D, if S ⊆ E a then lam S else 0) ^ 2
      = ∑ S₁ ∈ D, ∑ S₂ ∈ D, lam S₁ * lam S₂ *
          ((A.filter (fun a => S₁ ∪ S₂ ⊆ E a)).card : ℝ) := by
    simp_rw [sq, sum_mul_sum, card_filter]
    push_cast
    rw [sum_comm]
    refine sum_congr rfl fun S₁ _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun S₂ _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun a _ => ?_
    by_cases h1 : S₁ ⊆ E a <;> by_cases h2 : S₂ ⊆ E a <;> simp [h1, h2, union_subset_iff]
  have step3 : ∑ S₁ ∈ D, ∑ S₂ ∈ D, lam S₁ * lam S₂ *
          ((A.filter (fun a => S₁ ∪ S₂ ⊆ E a)).card : ℝ)
      = X * (∑ S₁ ∈ D, ∑ S₂ ∈ D, lam S₁ * lam S₂ * ∏ p ∈ S₁ ∪ S₂, g p)
        + ∑ S₁ ∈ D, ∑ S₂ ∈ D, lam S₁ * lam S₂ * r (S₁ ∪ S₂) := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun S₁ h₁ => ?_
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun S₂ h₂ => ?_
    rw [hr _ (union_subset (hDQ _ h₁) (hDQ _ h₂))]; ring
  have step4 : ∑ S₁ ∈ D, ∑ S₂ ∈ D, lam S₁ * lam S₂ * r (S₁ ∪ S₂)
      ≤ ∑ S₁ ∈ D, ∑ S₂ ∈ D, |r (S₁ ∪ S₂)| := by
    refine sum_le_sum fun S₁ h₁ => sum_le_sum fun S₂ h₂ => ?_
    have a1 := abs_selbergWeight_le hg0 hg1 hDQ hdown hemp h₁
    have a2 := abs_selbergWeight_le hg0 hg1 hDQ hdown hemp h₂
    calc lam S₁ * lam S₂ * r (S₁ ∪ S₂) ≤ |lam S₁ * lam S₂ * r (S₁ ∪ S₂)| := le_abs_self _
      _ = |lam S₁| * |lam S₂| * |r (S₁ ∪ S₂)| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * 1 * |r (S₁ ∪ S₂)| := by gcongr
      _ = _ := by ring
  rw [selberg_mainTerm hg0 hg1 hDQ hdown hemp] at step3
  calc _ ≤ _ := step1
    _ = _ := step2
    _ = _ := step3
    _ ≤ X / selbergG g D + ∑ S₁ ∈ D, ∑ S₂ ∈ D, |r (S₁ ∪ S₂)| := by
      rw [mul_one_div]; linarith

end Abstract

/- ## Counting residue conditions -/


theorem count_periodic_mul (P : ℕ → Prop) [DecidablePred P] {m : ℕ} (hper : ∀ n, P n ↔ P (n % m)) (q : ℕ) :
    Nat.count P (m * q) = q * Nat.count P m := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hfun : (fun k => P (m * q + k)) = P := by
      funext k; apply propext
      rw [hper (m * q + k), hper k, Nat.mul_add_mod]
    rw [Nat.mul_succ, Nat.count_add, ih]
    have : Nat.count (fun k => P (m * q + k)) m = Nat.count P m := by
      simp_rw [hfun]
    rw [this]; ring

/-- Counting a periodic set in an initial segment: if `P` is `m`-periodic with `K` solutions
in `[0, m)`, then the number of solutions in `[0, N)` is `N K / m` up to an error of at most `K`. -/
theorem card_filter_range_periodic (P : ℕ → Prop) [DecidablePred P] {m : ℕ} (hm : 0 < m)
    (hper : ∀ n, P n ↔ P (n % m)) (N : ℕ) :
    |(((range N).filter P).card : ℝ) - N * ((range m).filter P).card / m|
      ≤ ((range m).filter P).card := by
  rw [← Nat.count_eq_card_filter_range, ← Nat.count_eq_card_filter_range]
  set K := Nat.count P m
  have hN : N = m * (N / m) + N % m := (Nat.div_add_mod N m).symm
  have hc : Nat.count P N = (N / m) * K + Nat.count P (N % m) := by
    conv_lhs => rw [hN]
    rw [Nat.count_add, count_periodic_mul P hper]
    congr 1
    congr 1
    funext k; apply propext
    rw [hper (m * (N / m) + k), hper k, Nat.mul_add_mod]
  have hle : Nat.count P (N % m) ≤ K := Nat.count_monotone P (Nat.mod_lt N hm).le
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsR : ((N % m : ℕ) : ℝ) < m := by exact_mod_cast Nat.mod_lt N hm
  have hNR : (N : ℝ) = m * ((N / m : ℕ) : ℝ) + ((N % m : ℕ) : ℝ) := by exact_mod_cast hN
  rw [hc, abs_le]
  push_cast
  have hleR : ((Nat.count P (N % m) : ℕ) : ℝ) ≤ K := by exact_mod_cast hle
  have hK0 : (0 : ℝ) ≤ K := by positivity
  have e : (N : ℝ) * K / m = ((N / m : ℕ) : ℝ) * K + ((N % m : ℕ) : ℝ) * K / m := by
    rw [hNR]; field_simp
  have h2 : ((N % m : ℕ) : ℝ) * K / m ≤ K := by
    rw [div_le_iff₀ hmR]; nlinarith
  have h3 : 0 ≤ ((N % m : ℕ) : ℝ) * K / m := by positivity
  rw [e]
  constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.count P (N % m))]


theorem card_filter_range_mul (F : ℕ → Prop) [DecidablePred F] {p : ℕ} (hp : 0 < p) (m : ℕ) :
    ((range (p * m)).filter F).card
      = ∑ j ∈ range p, ((range m).filter (fun t => F (j + p * t))).card := by
  have : ((range (p * m)).filter F).card
      = ((range p ×ˢ range m).filter (fun x => F (x.1 + p * x.2))).card := by
    refine Finset.card_nbij' (fun r => (r % p, r / p)) (fun x => x.1 + p * x.2) ?_ ?_ ?_ ?_
    · intro r hr
      simp only [coe_filter, mem_range, Set.mem_setOf_eq, mem_product] at hr ⊢
      refine ⟨⟨Nat.mod_lt _ hp, ?_⟩, by rw [Nat.mod_add_div]; exact hr.2⟩
      exact Nat.div_lt_of_lt_mul hr.1
    · intro x hx
      simp only [coe_filter, mem_range, Set.mem_setOf_eq, mem_product] at hx ⊢
      refine ⟨?_, hx.2⟩
      calc x.1 + p * x.2 < p + p * x.2 := by omega
        _ = p * (x.2 + 1) := by ring
        _ ≤ p * m := Nat.mul_le_mul_left _ hx.1.2
    · intro r _
      simp only [Nat.mod_add_div]
    · intro x hx
      simp only [coe_filter, mem_range, Set.mem_setOf_eq, mem_product] at hx
      simp only
      refine Prod.ext ?_ ?_
      · simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx.1.1]
      · simp only [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hx.1.1, zero_add]
  rw [this, card_filter, sum_product]
  refine sum_congr rfl fun j _ => ?_
  rw [card_filter]

theorem card_filter_range_shift (P : ℕ → Prop) [DecidablePred P] {m p : ℕ} (hm : 0 < m) (hpm : Nat.Coprime p m)
    (hper : ∀ n, P n ↔ P (n % m)) (j : ℕ) :
    ((range m).filter (fun t => P (j + p * t))).card = ((range m).filter P).card := by
  set f : ℕ → ℕ := fun t => (j + p * t) % m
  have hinj : Set.InjOn f (range m) := by
    intro t ht t' ht' h
    simp only [coe_range, Set.mem_Iio] at ht ht'
    have h1 : j + p * t ≡ j + p * t' [MOD m] := h
    have h2 := Nat.ModEq.add_left_cancel' j h1
    have h3 := Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hpm) h2
    have := Nat.mod_eq_of_lt ht; have := Nat.mod_eq_of_lt ht'
    unfold Nat.ModEq at h3; omega
  have himg : (range m).image f = range m := by
    apply eq_of_subset_of_card_le
    · intro u hu
      simp only [mem_image, mem_range] at hu ⊢
      obtain ⟨t, _, rfl⟩ := hu
      exact Nat.mod_lt _ hm
    · rw [card_image_of_injOn hinj]
  have hfilt : (range m).filter (fun t => P (j + p * t)) = (range m).filter (fun t => P (f t)) := by
    refine filter_congr fun t _ => ?_
    simp only [f]; exact hper _
  have himg2 : (range m).filter P = ((range m).filter (fun t => P (f t))).image f := by
    ext u
    simp only [mem_filter, mem_image]
    constructor
    · rintro ⟨hu, hP⟩
      rw [← himg] at hu
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hu
      exact ⟨t, ⟨ht, hP⟩, rfl⟩
    · rintro ⟨t, ⟨ht, hP⟩, rfl⟩
      exact ⟨mem_range.mpr (Nat.mod_lt _ hm), hP⟩
  rw [hfilt, himg2, card_image_of_injOn (hinj.mono (filter_subset _ _))]

/-- Chinese remainder count: if each condition `C p` is `p`-periodic, the number of residues
modulo `Π_{p∈S} p` satisfying all of them is `Π_{p∈S} ω(p)`. -/
theorem card_filter_range_prod (C : ℕ → ℕ → Prop) (hper : ∀ p n, C p n ↔ C p (n % p))
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ((range (∏ p ∈ S, p)).filter (fun r => ∀ p ∈ S, C p r)).card
      = ∏ p ∈ S, ((range p).filter (C p)).card := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert p S hpS ih =>
    have hp := hS p (mem_insert_self p S)
    have hS' : ∀ q ∈ S, q.Prime := fun q hq => hS q (mem_insert_of_mem hq)
    have hm : 0 < ∏ q ∈ S, q := prod_pos fun q hq => (hS' q hq).pos
    have hcop : Nat.Coprime p (∏ q ∈ S, q) := Nat.Coprime.prod_right fun q hq =>
      (Nat.coprime_primes hp (hS' q hq)).mpr (fun h => hpS (h ▸ hq))
    rw [prod_insert hpS, prod_insert hpS, card_filter_range_mul (fun r => ∀ q ∈ insert p S, C q r) hp.pos, ← ih hS']
    have hperS : ∀ n, (∀ q ∈ S, C q n) ↔ (∀ q ∈ S, C q (n % ∏ q ∈ S, q)) := by
      intro n
      refine forall₂_congr fun q hq => ?_
      have := Nat.mod_mod_of_dvd n (dvd_prod_of_mem (fun i : ℕ => i) hq)
      rw [hper q (n % ∏ q ∈ S, q), this, ← hper q n]
    have step : ∀ j ∈ range p,
        ((range (∏ q ∈ S, q)).filter (fun t => ∀ q ∈ insert p S, C q (j + p * t))).card
          = if C p j then ((range (∏ q ∈ S, q)).filter (fun r => ∀ q ∈ S, C q r)).card else 0 := by
      intro j hj
      have hj' : ∀ t, C p (j + p * t) ↔ C p j := by
        intro t
        rw [hper p, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (mem_range.mp hj)]
      simp_rw [forall_mem_insert, hj']
      split_ifs with hc
      · simp only [hc, true_and]
        convert card_filter_range_shift (fun n => ∀ q ∈ S, C q n) hm hcop hperS j using 2 <;> (ext; simp)
      · simp [hc]
    rw [sum_congr rfl step, ← sum_filter, sum_const, smul_eq_mul]

/- ## Selberg's sieve for residue conditions -/

/-- The number `ω(p)` of residues `r ∈ [0, p)` that are removed by the local condition `C p`. -/
noncomputable def omega (C : ℕ → ℕ → Prop) (p : ℕ) : ℕ := ((range p).filter (C p)).card

/-- The classical Selberg support: sets of primes from `Q` whose product is `< z`. -/
noncomputable def levelFamily (Q : Finset ℕ) (z : ℕ) : Finset (Finset ℕ) :=
  Q.powerset.filter (fun S => ∏ p ∈ S, p < z)

/-- The number of `n < N` meeting every condition `C p`, `p ∈ S`, is `N Π_{p∈S} ω(p)/p` up to an
error of at most `Π_{p∈S} ω(p)`. -/
theorem card_residue_error (C : ℕ → ℕ → Prop) (hper : ∀ p n, C p n ↔ C p (n % p))
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (N : ℕ) :
    |(((range N).filter (fun n => ∀ p ∈ S, C p n)).card : ℝ)
        - N * ∏ p ∈ S, ((omega C p : ℝ) / p)| ≤ ∏ p ∈ S, (omega C p : ℝ) := by
  have hm : 0 < ∏ p ∈ S, p := prod_pos fun p hp => (hS p hp).pos
  have hper' : ∀ n, (∀ p ∈ S, C p n) ↔ (∀ p ∈ S, C p (n % ∏ q ∈ S, q)) := by
    intro n
    refine forall₂_congr fun q hq => ?_
    have := Nat.mod_mod_of_dvd n (dvd_prod_of_mem (fun i : ℕ => i) hq)
    rw [hper q (n % ∏ q ∈ S, q), this, ← hper q n]
  have hcount := card_filter_range_periodic (fun n => ∀ p ∈ S, C p n) hm hper' N
  have hK := card_filter_range_prod C hper S hS
  have hK' : (((range (∏ p ∈ S, p)).filter (fun n => ∀ p ∈ S, C p n)).card : ℝ)
      = ∏ p ∈ S, (omega C p : ℝ) := by
    have e : ∏ i ∈ S, omega C i = ∏ p ∈ S, ((range p).filter (C p)).card := rfl
    rw [← Nat.cast_prod, e, ← hK]
  rw [hK'] at hcount
  convert hcount using 3
  rw [prod_div_distrib]; push_cast; ring

/-- **Selberg's sieve for residue conditions.** For each prime `p ∈ Q` let `C p` be a
`p`-periodic condition on `ℕ` holding for `ω(p)` residues, with `0 < ω(p) < p`. Then the number
of `n < N` satisfying no condition `C p`, `p ∈ Q`, is at most
`N / G + Σ_{S₁,S₂ ∈ D} Π_{p ∈ S₁ ∪ S₂} ω(p)`, with `G = selbergG (ω/p) D`, for any down-closed
support family `D ∋ ∅` of subsets of `Q`. -/
theorem selberg_residue (N : ℕ) (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (C : ℕ → ℕ → Prop) (hper : ∀ p n, C p n ↔ C p (n % p))
    (hω0 : ∀ p ∈ Q, 0 < omega C p) (hω1 : ∀ p ∈ Q, omega C p < p)
    (D : Finset (Finset ℕ)) (hDQ : ∀ S ∈ D, S ⊆ Q) (hdown : ∀ S ∈ D, ∀ T ⊆ S, T ∈ D)
    (hemp : ∅ ∈ D) :
    (((range N).filter (fun n => ∀ p ∈ Q, ¬ C p n)).card : ℝ)
      ≤ N / selbergG (fun p => (omega C p : ℝ) / p) D
        + ∑ S₁ ∈ D, ∑ S₂ ∈ D, ∏ p ∈ S₁ ∪ S₂, (omega C p : ℝ) := by
  set g : ℕ → ℝ := fun p => (omega C p : ℝ) / p
  have hg0 : ∀ p ∈ Q, 0 < g p := fun p hp =>
    div_pos (by exact_mod_cast hω0 p hp) (by exact_mod_cast (hQ p hp).pos)
  have hg1 : ∀ p ∈ Q, g p < 1 := fun p hp => by
    have : (0 : ℝ) < p := by exact_mod_cast (hQ p hp).pos
    simp only [g]; rw [div_lt_one this]; exact_mod_cast hω1 p hp
  set E : ℕ → Finset ℕ := fun n => Q.filter (fun p => C p n)
  set r : Finset ℕ → ℝ := fun S =>
    (((range N).filter (fun n => S ⊆ E n)).card : ℝ) - N * ∏ p ∈ S, g p
  have key := selberg_sieve_abstract (range N) E hg0 hg1 hDQ hdown hemp (N : ℝ) r
    (fun S _ => by simp only [r]; rw [add_sub_cancel])
  have hrem : ∑ S₁ ∈ D, ∑ S₂ ∈ D, |r (S₁ ∪ S₂)|
      ≤ ∑ S₁ ∈ D, ∑ S₂ ∈ D, ∏ p ∈ S₁ ∪ S₂, (omega C p : ℝ) := by
    refine sum_le_sum fun S₁ h₁ => sum_le_sum fun S₂ h₂ => ?_
    have hSQ : S₁ ∪ S₂ ⊆ Q := union_subset (hDQ _ h₁) (hDQ _ h₂)
    have hc : ((range N).filter (fun n => S₁ ∪ S₂ ⊆ E n)).card
        = ((range N).filter (fun n => ∀ p ∈ S₁ ∪ S₂, C p n)).card := by
      congr 1; ext n
      simp only [E, mem_filter, subset_iff]
      exact ⟨fun h => ⟨h.1, fun p hp => (h.2 hp).2⟩, fun h => ⟨h.1, fun p hp => ⟨hSQ hp, h.2 p hp⟩⟩⟩
    have := card_residue_error C hper (S₁ ∪ S₂) (fun p hp => hQ p (hSQ hp)) N
    simp only [r]; rw [hc]
    exact this
  have k2 := key.trans (add_le_add le_rfl hrem)
  have hc : ((range N).filter (fun n => ∀ p ∈ Q, ¬ C p n)).card
      = ((range N).filter (fun n => Disjoint Q (E n))).card := by
    congr 1; ext n
    simp only [E, disjoint_left, mem_filter, not_and]
    exact ⟨fun h => ⟨h.1, fun p hp _ => h.2 p hp⟩, fun h => ⟨h.1, fun p hp => h.2 hp hp⟩⟩
  have hc' : (((range N).filter (fun n => ∀ p ∈ Q, ¬ C p n)).card : ℝ)
      = (((range N).filter (fun n => Disjoint Q (E n))).card : ℝ) := by
    exact_mod_cast hc
  rw [hc']
  exact k2

theorem levelFamily_subset {Q : Finset ℕ} {z : ℕ} : ∀ S ∈ levelFamily Q z, S ⊆ Q :=
  fun S hS => mem_powerset.mp (mem_filter.mp hS).1

theorem levelFamily_down {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime) {z : ℕ} :
    ∀ S ∈ levelFamily Q z, ∀ T ⊆ S, T ∈ levelFamily Q z := by
  intro S hS T hT
  simp only [levelFamily, mem_filter, mem_powerset] at hS ⊢
  refine ⟨hT.trans hS.1, lt_of_le_of_lt ?_ hS.2⟩
  exact prod_le_prod_of_subset_of_one_le' hT fun p hp _ => (hQ p (hS.1 hp)).one_lt.le

theorem empty_mem_levelFamily {Q : Finset ℕ} {z : ℕ} (hz : 2 ≤ z) : ∅ ∈ levelFamily Q z := by
  simp only [levelFamily, mem_filter, empty_mem_powerset, prod_empty, true_and]; omega

theorem card_levelFamily_le {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime) (z : ℕ) :
    (levelFamily Q z).card ≤ z := by
  have := card_le_card_of_injOn (s := levelFamily Q z) (t := range z) (fun S => ∏ p ∈ S, p)
    (fun S hS => by
      simp only [levelFamily, coe_filter, mem_powerset, Set.mem_setOf_eq] at hS
      simp only [coe_range, Set.mem_Iio]; exact hS.2)
    (fun S hS T hT h => by
      simp only [levelFamily, coe_filter, mem_powerset, Set.mem_setOf_eq] at hS hT
      have h1 := Nat.primeFactors_prod (s := S) fun p hp => hQ p (hS.1 hp)
      have h2 := Nat.primeFactors_prod (s := T) fun p hp => hQ p (hT.1 hp)
      simp only at h
      rw [← h1, ← h2, h])
  simpa using this

/-- **Selberg's sieve at level `z`, with a crude explicit remainder.** With the classical support
`levelFamily Q z` (products of primes `< z`), the number of `n < N` meeting no condition `C p`,
`p ∈ Q`, is at most `N / G + z ^ 4`. -/
theorem selberg_residue_level (N z : ℕ) (hz : 2 ≤ z) (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (C : ℕ → ℕ → Prop) (hper : ∀ p n, C p n ↔ C p (n % p))
    (hω0 : ∀ p ∈ Q, 0 < omega C p) (hω1 : ∀ p ∈ Q, omega C p < p) :
    (((range N).filter (fun n => ∀ p ∈ Q, ¬ C p n)).card : ℝ)
      ≤ N / selbergG (fun p => (omega C p : ℝ) / p) (levelFamily Q z) + (z : ℝ) ^ 4 := by
  have key := selberg_residue N Q hQ C hper hω0 hω1 (levelFamily Q z) levelFamily_subset
    (levelFamily_down hQ) (empty_mem_levelFamily hz)
  refine key.trans (add_le_add le_rfl ?_)
  have hterm : ∀ S₁ ∈ levelFamily Q z, ∀ S₂ ∈ levelFamily Q z,
      ∏ p ∈ S₁ ∪ S₂, (omega C p : ℝ) ≤ (z : ℝ) ^ 2 := by
    intro S₁ h₁ S₂ h₂
    have h₁' := h₁; have h₂' := h₂
    simp only [levelFamily, mem_filter, mem_powerset] at h₁' h₂'
    have hSQ : S₁ ∪ S₂ ⊆ Q := union_subset h₁'.1 h₂'.1
    have a : ∏ p ∈ S₁ ∪ S₂, (omega C p : ℝ) ≤ ∏ p ∈ S₁ ∪ S₂, (p : ℝ) :=
      prod_le_prod (fun p _ => by positivity)
        (fun p hp => by exact_mod_cast (hω1 p (hSQ hp)).le)
    have b : ∏ p ∈ S₁ ∪ S₂, p ≤ (∏ p ∈ S₁, p) * ∏ p ∈ S₂, p := by
      rw [← prod_union_inter]
      exact Nat.le_mul_of_pos_right _ (prod_pos fun p hp => (hQ p (h₁'.1 (mem_inter.mp hp).1)).pos)
    have c : (∏ p ∈ S₁, p) * ∏ p ∈ S₂, p ≤ z * z :=
      Nat.mul_le_mul h₁'.2.le h₂'.2.le
    have : ((∏ p ∈ S₁ ∪ S₂, p : ℕ) : ℝ) ≤ (z : ℝ) ^ 2 := by
      rw [sq]; exact_mod_cast b.trans c
    push_cast at this
    linarith
  calc ∑ S₁ ∈ levelFamily Q z, ∑ S₂ ∈ levelFamily Q z, ∏ p ∈ S₁ ∪ S₂, (omega C p : ℝ)
      ≤ ∑ S₁ ∈ levelFamily Q z, ∑ S₂ ∈ levelFamily Q z, (z : ℝ) ^ 2 :=
        sum_le_sum fun S₁ h₁ => sum_le_sum fun S₂ h₂ => hterm S₁ h₁ S₂ h₂
    _ = ((levelFamily Q z).card : ℝ) ^ 2 * (z : ℝ) ^ 2 := by
        simp only [sum_const, nsmul_eq_mul]; ring
    _ ≤ (z : ℝ) ^ 2 * (z : ℝ) ^ 2 := by
        have h1 : ((levelFamily Q z).card : ℝ) ≤ z := by exact_mod_cast card_levelFamily_le hQ z
        have h0 : (0 : ℝ) ≤ ((levelFamily Q z).card : ℝ) := Nat.cast_nonneg _
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 h1 2) (by positivity)
    _ = (z : ℝ) ^ 4 := by ring

/-- `selbergG` only depends on `g` on the primes of `Q`. -/
theorem selbergG_congr {Q : Finset ℕ} {D : Finset (Finset ℕ)} (hDQ : ∀ S ∈ D, S ⊆ Q)
    {g g' : ℕ → ℝ} (h : ∀ p ∈ Q, g p = g' p) : selbergG g D = selbergG g' D := by
  unfold selbergG hFun
  exact sum_congr rfl fun S hS => prod_congr rfl fun p hp => by rw [h p (hDQ S hS hp)]

/- ## Prime pairs `p, p + d` -/

/-- The local condition of the prime-pair sieve: `p ∣ n (n + d)`. -/
def pairCond (d : ℕ) (p n : ℕ) : Prop := p ∣ n * (n + d)

/-- The number of residues removed modulo `p` in the prime-pair sieve:
`1` if `p ∣ d`, otherwise `2`. -/
def pairOmega (d p : ℕ) : ℕ := if p ∣ d then 1 else 2

/-- Selberg's `G(z)` for the prime-pair sieve with difference `d`:
`G_d(z) = Σ_{m < z, m ∣ P(z)} Π_{p ∣ m} ω_d(p)/(p - ω_d(p))`, written over sets of primes
`< z` with product `< z`. -/
noncomputable def pairG (d z : ℕ) : ℝ :=
  selbergG (fun p => (pairOmega d p : ℝ) / p) (levelFamily (Nat.primesBelow z) z)

theorem pairCond_periodic (d p n : ℕ) : pairCond d p n ↔ pairCond d p (n % p) := by
  unfold pairCond
  simp only [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, Nat.add_mod, Nat.mod_mod]

theorem pairCond_iff_of_lt {d p r : ℕ} (hp : p.Prime) (hr : r < p) :
    pairCond d p r ↔ r = 0 ∨ r + d % p = p := by
  unfold pairCond
  rw [hp.dvd_mul]
  have hk : d % p < p := Nat.mod_lt _ hp.pos
  have e1 : p ∣ r ↔ r = 0 := ⟨fun h => Nat.eq_zero_of_dvd_of_lt h hr, fun h => h ▸ dvd_zero p⟩
  have e2 : p ∣ r + d ↔ p ∣ r + d % p := by
    have : r + d = (r + d % p) + p * (d / p) := by
      have := Nat.mod_add_div d p; omega
    rw [this, Nat.dvd_add_left (dvd_mul_right p _)]
  have e3 : p ∣ r + d % p ↔ r + d % p = 0 ∨ r + d % p = p := by
    constructor
    · rintro ⟨m, hm⟩
      have : m < 2 := by
        by_contra h; push_neg at h
        have : p * 2 ≤ p * m := Nat.mul_le_mul_left _ h
        omega
      interval_cases m <;> simp_all
    · rintro (h | h) <;> rw [h]
      · exact dvd_zero p
  rw [e1, e2, e3]
  omega

theorem omega_pairCond {d p : ℕ} (hp : p.Prime) : omega (pairCond d) p = pairOmega d p := by
  unfold omega pairOmega
  have hk : d % p < p := Nat.mod_lt _ hp.pos
  split_ifs with hd
  · have : (range p).filter (pairCond d p) = {0} := by
      ext r
      simp only [mem_filter, mem_range, mem_singleton]
      constructor
      · rintro ⟨hr, h⟩
        rw [pairCond_iff_of_lt hp hr, Nat.mod_eq_zero_of_dvd hd] at h
        omega
      · rintro rfl; exact ⟨hp.pos, (pairCond_iff_of_lt hp hp.pos).mpr (Or.inl rfl)⟩
    rw [this, card_singleton]
  · have hk0 : d % p ≠ 0 := fun h => hd (Nat.dvd_of_mod_eq_zero h)
    have : (range p).filter (pairCond d p) = {0, p - d % p} := by
      ext r
      simp only [mem_filter, mem_range, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hr, h⟩
        rw [pairCond_iff_of_lt hp hr] at h
        omega
      · intro h
        have hr : r < p := by omega
        refine ⟨hr, (pairCond_iff_of_lt hp hr).mpr ?_⟩
        omega
    rw [this, card_insert_of_notMem (by simp; omega), card_singleton]

theorem pairOmega_pos (d p : ℕ) : 0 < pairOmega d p := by
  unfold pairOmega; split_ifs <;> norm_num

theorem pairOmega_lt {d p : ℕ} (hd : Even d) (hp : p.Prime) : pairOmega d p < p := by
  unfold pairOmega
  split_ifs with h
  · exact hp.one_lt
  · have h2 : p ≠ 2 := by rintro rfl; exact h (even_iff_two_dvd.mp hd)
    have := hp.two_le; omega

/-- **Selberg upper bound for prime pairs, explicit form.** For even `d` and any level
`z ≥ 2`, the number of primes `p ≤ x` with `p + d` prime is at most
`z + (x + 1) / G_d(z) + z ^ 4`. -/
theorem card_prime_pairs_le_sieve (d x z : ℕ) (hd : Even d) (hz : 2 ≤ z) :
    (((range (x + 1)).filter (fun p => p.Prime ∧ (p + d).Prime)).card : ℝ)
      ≤ z + (x + 1) / pairG d z + (z : ℝ) ^ 4 := by
  set Q := Nat.primesBelow z
  have hQ : ∀ p ∈ Q, p.Prime := fun p hp => (Nat.mem_primesBelow.mp hp).2
  have hsub : (range (x + 1)).filter (fun p => p.Prime ∧ (p + d).Prime)
      ⊆ range z ∪ (range (x + 1)).filter (fun n => ∀ p ∈ Q, ¬ pairCond d p n) := by
    intro n hn
    simp only [mem_filter, mem_range] at hn
    simp only [mem_union, mem_range, mem_filter]
    by_cases hnz : n < z
    · exact Or.inl hnz
    · right
      refine ⟨hn.1, fun q hq hdiv => ?_⟩
      have hq' := Nat.mem_primesBelow.mp hq
      unfold pairCond at hdiv
      rcases (hq'.2.dvd_mul).mp hdiv with h | h
      · have := (Nat.prime_dvd_prime_iff_eq hq'.2 hn.2.1).mp h; omega
      · have := (Nat.prime_dvd_prime_iff_eq hq'.2 hn.2.2).mp h; omega
  have hω0 : ∀ p ∈ Q, 0 < omega (pairCond d) p := fun p hp => by
    rw [omega_pairCond (hQ p hp)]; exact pairOmega_pos d p
  have hω1 : ∀ p ∈ Q, omega (pairCond d) p < p := fun p hp => by
    rw [omega_pairCond (hQ p hp)]; exact pairOmega_lt hd (hQ p hp)
  have hsieve := selberg_residue_level (x + 1) z hz Q hQ (pairCond d) (pairCond_periodic d) hω0 hω1
  have hG : selbergG (fun p => (omega (pairCond d) p : ℝ) / p) (levelFamily Q z) = pairG d z :=
    selbergG_congr levelFamily_subset fun p hp => by rw [omega_pairCond (hQ p hp)]
  rw [hG] at hsieve
  push_cast at hsieve
  have hcard := card_le_card hsub
  have hu := card_union_le (range z) ((range (x + 1)).filter (fun n => ∀ p ∈ Q, ¬ pairCond d p n))
  rw [card_range] at hu
  have : (((range (x + 1)).filter (fun p => p.Prime ∧ (p + d).Prime)).card : ℝ)
      ≤ z + (((range (x + 1)).filter (fun n => ∀ p ∈ Q, ¬ pairCond d p n)).card : ℝ) := by
    exact_mod_cast hcard.trans hu
  linarith

/-- Choice of the sieve level: for `x ≥ 2^16` there is `z ≥ 2` with
`(z + z^4) (log x)^2 ≤ 32 x` and `log x ≤ 16 log z` (take `z = ⌊x^{1/8}⌋`). -/
theorem exists_level (x : ℕ) (hx : 65536 ≤ x) :
    ∃ z : ℕ, 2 ≤ z ∧ ((z : ℝ) + (z : ℝ) ^ 4) * Real.log x ^ 2 ≤ 32 * x ∧
      Real.log x ≤ 16 * Real.log z := by
  set y : ℝ := (x : ℝ) ^ ((1 : ℝ) / 8) with hydef
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hy0 : 0 ≤ y := Real.rpow_nonneg hx0 _
  have hy8 : y ^ 8 = x := by
    rw [hydef, ← Real.rpow_natCast, ← Real.rpow_mul hx0]; norm_num
  have hxR : (65536 : ℝ) ≤ x := by exact_mod_cast hx
  have hy4 : 4 ≤ y := by
    by_contra h; push_neg at h
    have : y ^ 8 < 4 ^ 8 := pow_lt_pow_left₀ h hy0 (by norm_num)
    rw [hy8] at this; norm_num at this; linarith
  set z := ⌊y⌋₊
  have hzle : (z : ℝ) ≤ y := Nat.floor_le hy0
  have hzgt : y < z + 1 := Nat.lt_floor_add_one y
  have hz3 : (3 : ℝ) < z := by linarith
  have hz2 : 2 ≤ z := by
    have : (2 : ℝ) < z := by linarith
    exact_mod_cast this.le
  have hzpos : (0 : ℝ) < z := by linarith
  have hlogx : Real.log x = 8 * Real.log y := by
    rw [← hy8, Real.log_pow]; norm_num
  have hlogy : Real.log y ≤ y := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hlogy0 : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  refine ⟨z, hz2, ?_, ?_⟩
  · have h1 : (z : ℝ) + (z : ℝ) ^ 4 ≤ 2 * y ^ 4 := by
      have : (z : ℝ) ^ 4 ≤ y ^ 4 := pow_le_pow_left₀ hzpos.le hzle 4
      have : y ≤ y ^ 4 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) (by linarith : (1:ℝ) ≤ y) 3]
      linarith
    have h2 : Real.log x ^ 2 ≤ 64 * y ^ 2 := by
      rw [hlogx]; nlinarith
    have h3 : (16 : ℝ) ≤ y ^ 2 := by nlinarith
    have h4 : 0 ≤ Real.log x ^ 2 := sq_nonneg _
    calc ((z : ℝ) + (z : ℝ) ^ 4) * Real.log x ^ 2 ≤ (2 * y ^ 4) * (64 * y ^ 2) := by
          apply mul_le_mul h1 h2 h4 (by positivity)
      _ = 128 * (y ^ 4 * y ^ 2) := by ring
      _ ≤ 8 * (y ^ 4 * y ^ 2 * y ^ 2) := by nlinarith [pow_nonneg hy0 4, pow_nonneg hy0 2]
      _ = 8 * y ^ 8 := by ring
      _ ≤ 32 * x := by rw [hy8]; linarith
  · have hzy : y / 2 ≤ z := by linarith
    have h1 : Real.log (y / 2) ≤ Real.log z := Real.log_le_log (by linarith) hzy
    rw [Real.log_div (by linarith) (by norm_num)] at h1
    have h2 : Real.log 4 ≤ Real.log y := Real.log_le_log (by norm_num) hy4
    have h3 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [hlogx]; linarith

/-- The singular-series factor `Π_{p ∣ d, p > 2} (1 + 1/p)` of the prime-pair bound. -/
noncomputable def pairSingularProduct (d : ℕ) : ℝ :=
  ∏ p ∈ d.primeFactors with 2 < p, (1 + 1 / (p : ℝ))

theorem one_le_pairSingularProduct (d : ℕ) : 1 ≤ pairSingularProduct d := by
  unfold pairSingularProduct
  have := prod_le_prod (s := d.primeFactors.filter (fun p => 2 < p)) (f := fun _ : ℕ => (1 : ℝ))
    (g := fun p : ℕ => 1 + 1 / (p : ℝ)) (fun _ _ => zero_le_one)
    (fun p _ => by
      have : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
      linarith)
  simpa using this

/-- **Mertens-type input for the prime-pair sieve** (an explicit hypothesis, to be discharged
by a Mertens library): `c log² z ≤ G_d(z) · Π_{p ∣ d, p > 2} (1 + 1/p)` for all even `d > 0`
and all `z ≥ 2`. Classically this holds for some absolute `c > 0`. -/
def PairGLowerBound (c : ℝ) : Prop :=
  ∀ d : ℕ, 0 < d → Even d → ∀ z : ℕ, 2 ≤ z →
    c * Real.log z ^ 2 ≤ pairG d z * pairSingularProduct d

/-- **Upper bound for prime pairs with a given difference (Romanoff-ready).**
Given the Mertens-type lower bound `PairGLowerBound c`, there is an absolute `C` such that for
every even `d > 0` and every `x ≥ 2`,
`#{p ≤ x : p and p + d prime} ≤ C · x / log² x · Π_{p ∣ d, p > 2} (1 + 1/p)`. -/
theorem prime_pairs_upper_bound {c : ℝ} (hc : 0 < c) (hG : PairGLowerBound c) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 0 < d → Even d → ∀ x : ℕ, 2 ≤ x →
      (((range (x + 1)).filter (fun p => p.Prime ∧ (p + d).Prime)).card : ℝ)
        ≤ C * ((x : ℝ) / Real.log x ^ 2) * pairSingularProduct d := by
  refine ⟨320 + 512 / c, by positivity, fun d hd0 hd x hx => ?_⟩
  set PP := pairSingularProduct d
  have hPP : 1 ≤ PP := one_le_pairSingularProduct d
  have hxR : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hL2 : 0 < Real.log x ^ 2 := by positivity
  set cnt := (((range (x + 1)).filter (fun p => p.Prime ∧ (p + d).Prime)).card : ℝ)
  have hcnt0 : cnt ≤ x + 1 := by
    have := card_filter_le (range (x + 1)) (fun p => p.Prime ∧ (p + d).Prime)
    rw [card_range] at this
    simp only [cnt]; exact_mod_cast this
  by_cases hbig : 65536 ≤ x
  · obtain ⟨z, hz2, hzrem, hlogz⟩ := exists_level x hbig
    have hs := card_prime_pairs_le_sieve d x z hd hz2
    have hGz := hG d hd0 hd z hz2
    have hGpos : 0 < pairG d z := by
      have := one_le_selbergG (Q := Nat.primesBelow z)
        (g := fun p => (pairOmega d p : ℝ) / p) (D := levelFamily (Nat.primesBelow z) z)
        (fun p hp => div_pos (by exact_mod_cast pairOmega_pos d p)
          (by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.pos))
        (fun p hp => by
          have hp' := (Nat.mem_primesBelow.mp hp).2
          rw [div_lt_one (by exact_mod_cast hp'.pos)]; exact_mod_cast pairOmega_lt hd hp')
        levelFamily_subset (empty_mem_levelFamily hz2)
      unfold pairG; linarith
    have hlz : Real.log x ^ 2 ≤ 256 * Real.log z ^ 2 := by nlinarith
    have hlz0 : 0 < Real.log z ^ 2 := by nlinarith
    -- main term
    have hmain : ((x : ℝ) + 1) / pairG d z ≤ (512 / c) * ((x : ℝ) / Real.log x ^ 2) * PP := by
      rw [div_le_iff₀ hGpos]
      have e : (512 / c) * ((x : ℝ) / Real.log x ^ 2) * PP * pairG d z
          = (512 * x) / (c * Real.log x ^ 2) * (pairG d z * PP) := by
        field_simp
      rw [e]
      have h1 : (512 * (x : ℝ)) / (c * Real.log x ^ 2) * (c * Real.log z ^ 2)
          ≤ (512 * x) / (c * Real.log x ^ 2) * (pairG d z * PP) :=
        mul_le_mul_of_nonneg_left hGz (by positivity)
      refine le_trans ?_ h1
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have k1 : ((x : ℝ) + 1) * Real.log x ^ 2 ≤ (2 * x) * (256 * Real.log z ^ 2) :=
        mul_le_mul (by linarith) hlz hL2.le (by linarith)
      have k2 := mul_le_mul_of_nonneg_left k1 hc.le
      nlinarith
    have hrem : (z : ℝ) + (z : ℝ) ^ 4 ≤ 32 * ((x : ℝ) / Real.log x ^ 2) * PP := by
      have : (z : ℝ) + (z : ℝ) ^ 4 ≤ 32 * ((x : ℝ) / Real.log x ^ 2) := by
        rw [mul_div_assoc', le_div_iff₀ hL2]; exact hzrem
      have h0 : 0 ≤ 32 * ((x : ℝ) / Real.log x ^ 2) := by positivity
      nlinarith
    have h0 : 0 ≤ ((x : ℝ) / Real.log x ^ 2) * PP := by positivity
    calc cnt ≤ z + (x + 1) / pairG d z + (z : ℝ) ^ 4 := hs
      _ ≤ 32 * ((x : ℝ) / Real.log x ^ 2) * PP + (512 / c) * ((x : ℝ) / Real.log x ^ 2) * PP := by
        linarith
      _ ≤ (320 + 512 / c) * ((x : ℝ) / Real.log x ^ 2) * PP := by nlinarith
  · push_neg at hbig
    have hxs : (x : ℝ) < 65536 := by exact_mod_cast hbig
    have hlog : Real.log x < 12 := by
      have h1 : Real.log x < Real.log 65536 := Real.log_lt_log (by linarith) hxs
      have h2 : Real.log (65536 : ℝ) = 16 * Real.log 2 := by
        rw [show (65536 : ℝ) = 2 ^ 16 by norm_num, Real.log_pow]; norm_num
      have := Real.log_two_lt_d9
      linarith
    have hLsq : Real.log x ^ 2 ≤ 144 := by nlinarith
    have h1 : cnt ≤ 288 * ((x : ℝ) / Real.log x ^ 2) := by
      rw [mul_div_assoc', le_div_iff₀ hL2]; nlinarith
    have h0 : 0 ≤ ((x : ℝ) / Real.log x ^ 2) := by positivity
    have h2 : 0 ≤ 512 / c * ((x : ℝ) / Real.log x ^ 2) * PP := by positivity
    nlinarith

/- ## Brun–Titchmarsh -/

/-- The sieving primes for an arithmetic progression modulo `q`: primes `< z` not dividing `q`. -/
noncomputable def apPrimes (q z : ℕ) : Finset ℕ := (Nat.primesBelow z).filter (fun p => ¬ p ∣ q)

/-- Selberg's `G(z)` for an arithmetic progression modulo `q`:
`Σ_{m < z, m ∣ P(z), (m, q) = 1} Π_{p ∣ m} 1/(p - 1)`. -/
noncomputable def apG (q z : ℕ) : ℝ :=
  selbergG (fun p : ℕ => (1 : ℝ) / p) (levelFamily (apPrimes q z) z)

/-- The local condition of the progression sieve: `p ∣ b + q t`. -/
def apCond (b q : ℕ) (p t : ℕ) : Prop := p ∣ b + q * t

theorem apCond_periodic (b q p t : ℕ) : apCond b q p t ↔ apCond b q p (t % p) := by
  unfold apCond
  simp only [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, Nat.add_mod, Nat.mod_mod]

theorem omega_apCond {b q p : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ q) : omega (apCond b q) p = 1 := by
  unfold omega apCond
  have hcop : Nat.Coprime q p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpq).symm
  have := card_filter_range_shift (fun u => p ∣ u) hp.pos hcop
    (fun n => by simp only [Nat.dvd_iff_mod_eq_zero, Nat.mod_mod]) b
  have h0 : (range p).filter (fun u => p ∣ u) = {0} := by
    ext u; simp only [mem_filter, mem_range, mem_singleton]
    exact ⟨fun h => Nat.eq_zero_of_dvd_of_lt h.2 h.1, fun h => h ▸ ⟨hp.pos, dvd_zero p⟩⟩
  have h2 : ((range p).filter (fun u => p ∣ u)).card = 1 := by rw [h0, card_singleton]
  convert this.trans h2 using 2
  ext t; simp

/-- **Brun–Titchmarsh, explicit sieve form.** For `q ≥ 1`, any `a`, `x` and level `z ≥ 2`,
the number of primes `p ≤ x` with `p ≡ a [MOD q]` is at most
`z + (x / q + 1) / G_q(z) + z ^ 4`. -/
theorem card_primes_ap_le_sieve (q a x z : ℕ) (hq : 0 < q) (hz : 2 ≤ z) :
    (((range (x + 1)).filter (fun p => p.Prime ∧ p ≡ a [MOD q])).card : ℝ)
      ≤ z + ((x / q + 1 : ℕ) : ℝ) / apG q z + (z : ℝ) ^ 4 := by
  set b := a % q
  set Q := apPrimes q z
  have hQ : ∀ p ∈ Q, p.Prime := fun p hp =>
    (Nat.mem_primesBelow.mp (mem_filter.mp hp).1).2
  have hQq : ∀ p ∈ Q, ¬ p ∣ q := fun p hp => (mem_filter.mp hp).2
  have hω0 : ∀ p ∈ Q, 0 < omega (apCond b q) p := fun p hp => by
    rw [omega_apCond (hQ p hp) (hQq p hp)]; norm_num
  have hω1 : ∀ p ∈ Q, omega (apCond b q) p < p := fun p hp => by
    rw [omega_apCond (hQ p hp) (hQq p hp)]; exact (hQ p hp).one_lt
  have hsieve := selberg_residue_level (x / q + 1) z hz Q hQ (apCond b q) (apCond_periodic b q)
    hω0 hω1
  have hG : selbergG (fun p => (omega (apCond b q) p : ℝ) / p) (levelFamily Q z) = apG q z := by
    show _ = selbergG (fun p : ℕ => (1 : ℝ) / p) (levelFamily Q z)
    refine selbergG_congr levelFamily_subset fun p hp => ?_
    rw [omega_apCond (hQ p hp) (hQq p hp)]; norm_num
  rw [hG] at hsieve
  set P := (range (x + 1)).filter (fun p => p.Prime ∧ p ≡ a [MOD q])
  have hsplit : P.card ≤ (P.filter (fun p => p < z)).card + (P.filter (fun p => ¬ p < z)).card := by
    rw [card_filter_add_card_filter_not]
  have h1 : (P.filter (fun p => p < z)).card ≤ z := by
    have := card_le_card (s := P.filter (fun p => p < z)) (t := range z)
      (fun p hp => mem_range.mpr (mem_filter.mp hp).2)
    simpa using this
  have h2 : (P.filter (fun p => ¬ p < z)).card
      ≤ ((range (x / q + 1)).filter (fun t => ∀ p ∈ Q, ¬ apCond b q p t)).card := by
    refine card_le_card_of_injOn (fun n => n / q) ?_ ?_
    · intro n hn
      simp only [P, coe_filter, mem_filter, mem_range, Set.mem_setOf_eq] at hn
      simp only [coe_filter, mem_range, Set.mem_setOf_eq]
      have hnb : n % q = b := hn.1.2.2
      have hdecomp : b + q * (n / q) = n := by rw [← hnb]; exact Nat.mod_add_div n q
      refine ⟨Nat.lt_succ_of_le (Nat.div_le_div_right (by omega)), fun p hp hdiv => ?_⟩
      unfold apCond at hdiv
      rw [hdecomp] at hdiv
      have hp' := Nat.mem_primesBelow.mp (mem_filter.mp hp).1
      have := (Nat.prime_dvd_prime_iff_eq hp'.2 hn.1.2.1).mp hdiv
      omega
    · intro n hn m hm h
      simp only [P, coe_filter, mem_filter, mem_range, Set.mem_setOf_eq] at hn hm
      simp only at h
      have e1 : n % q = m % q := hn.1.2.2.trans hm.1.2.2.symm
      rw [← Nat.mod_add_div n q, ← Nat.mod_add_div m q, e1, h]
  have hcard : (P.card : ℝ) ≤ z
      + (((range (x / q + 1)).filter (fun t => ∀ p ∈ Q, ¬ apCond b q p t)).card : ℝ) := by
    exact_mod_cast hsplit.trans (Nat.add_le_add h1 h2)
  linarith

/- ## A lower bound for `G` (Rankin's trick) -/

/-- **Rankin lower bound for Selberg's `G`.** If `Q ⊆ Qbig` consists of primes and `h ≥ 0`
on `Qbig`, then for every `ε ≥ 0`,
`Π_{p∈Q} (1 + h p) - z^{-ε} Π_{p∈Q} (1 + h p · p^ε) ≤ G` (support `levelFamily Qbig z`). -/
theorem selbergG_ge_rankin (g : ℕ → ℝ) (Q Qbig : Finset ℕ) (hQQ : Q ⊆ Qbig)
    (hQ : ∀ p ∈ Q, p.Prime) (hh : ∀ p ∈ Qbig, 0 ≤ hFun g p) (z : ℕ) (hz : 1 ≤ z)
    {ε : ℝ} (hε : 0 ≤ ε) :
    ∏ p ∈ Q, (1 + hFun g p) - (z : ℝ) ^ (-ε) * ∏ p ∈ Q, (1 + hFun g p * (p : ℝ) ^ ε)
      ≤ selbergG g (levelFamily Qbig z) := by
  have hzR : (1 : ℝ) ≤ z := by exact_mod_cast hz
  have hz0 : (0 : ℝ) < z := by linarith
  have hnn : ∀ S ∈ Q.powerset, 0 ≤ ∏ p ∈ S, hFun g p := fun S hS =>
    prod_nonneg fun p hp => hh p (hQQ (mem_powerset.mp hS hp))
  rw [prod_one_add, prod_one_add]
  rw [← sum_filter_add_sum_filter_not Q.powerset (fun S => ∏ p ∈ S, p < z)]
  have h1 : ∑ S ∈ Q.powerset with ∏ p ∈ S, p < z, ∏ p ∈ S, hFun g p
      ≤ selbergG g (levelFamily Qbig z) := by
    unfold selbergG
    apply sum_le_sum_of_subset_of_nonneg
    · intro S hS
      simp only [mem_filter, mem_powerset] at hS
      simp only [levelFamily, mem_filter, mem_powerset]
      exact ⟨hS.1.trans hQQ, hS.2⟩
    · intro S hS _
      simp only [levelFamily, mem_filter, mem_powerset] at hS
      exact prod_nonneg fun p hp => hh p (hS.1 hp)
  have h2 : ∑ S ∈ Q.powerset with ¬ ∏ p ∈ S, p < z, ∏ p ∈ S, hFun g p
      ≤ (z : ℝ) ^ (-ε) * ∑ S ∈ Q.powerset, ∏ p ∈ S, hFun g p * (p : ℝ) ^ ε := by
    rw [mul_sum]
    refine (sum_le_sum_of_subset_of_nonneg (filter_subset (fun S : Finset ℕ => ¬ ∏ p ∈ S, p < z) Q.powerset) ?_).trans' ?_
    · intro S hS _
      have := hnn S hS
      rw [prod_mul_distrib]
      exact mul_nonneg (Real.rpow_nonneg hz0.le _)
        (mul_nonneg this (prod_nonneg fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) _))
    · refine sum_le_sum fun S hS => ?_
      simp only [mem_filter, not_lt] at hS
      have hpos := hnn S hS.1
      rw [prod_mul_distrib, Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p)]
      have hge : (z : ℝ) ^ ε ≤ (∏ p ∈ S, (p : ℝ)) ^ ε := by
        apply Real.rpow_le_rpow hz0.le _ hε
        have := hS.2
        rw [← Nat.cast_prod]; exact_mod_cast this
      have hzz : (z : ℝ) ^ (-ε) * (z : ℝ) ^ ε = 1 := by
        rw [Real.rpow_neg hz0.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hz0 ε).ne']
      have : 1 ≤ (z : ℝ) ^ (-ε) * (∏ p ∈ S, (p : ℝ)) ^ ε := by
        rw [← hzz]
        exact mul_le_mul_of_nonneg_left hge (Real.rpow_nonneg hz0.le _)
      nlinarith
  linarith

/-- Weierstrass product inequality: `Π (1 - a i) ≥ 1 - Σ a i` for `0 ≤ a i ≤ 1`. -/
theorem one_sub_sum_le_prod (s : Finset ℕ) (a : ℕ → ℝ) (h0 : ∀ i ∈ s, 0 ≤ a i)
    (h1 : ∀ i ∈ s, a i ≤ 1) : 1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [sum_insert hj, prod_insert hj]
    have ih' := ih (fun i hi => h0 i (mem_insert_of_mem hi)) (fun i hi => h1 i (mem_insert_of_mem hi))
    have a0 := h0 j (mem_insert_self j s); have a1 := h1 j (mem_insert_self j s)
    have hP : 0 ≤ ∏ i ∈ s, (1 - a i) :=
      prod_nonneg fun i hi => by linarith [h1 i (mem_insert_of_mem hi)]
    have hS : 0 ≤ ∑ i ∈ s, a i := sum_nonneg fun i hi => h0 i (mem_insert_of_mem hi)
    nlinarith

theorem sum_Icc_three_inv_sq_le (N : ℕ) (hN : 2 ≤ N) :
    ∑ n ∈ Icc 3 N, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / 2 - 1 / N := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
    rw [sum_Icc_succ_top (by omega)]
    have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have : (1 : ℝ) / ((N + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / N - 1 / ((N + 1 : ℕ) : ℝ) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    linarith

/-- `Π_{p ∣ d, p > 2} (1 - 1/p) · Π_{p ∣ d, p > 2} (1 + 1/p) ≥ 1/2`. -/
theorem prod_odd_one_sub_mul_ge (d : ℕ) (hd : 0 < d) :
    1 / 2 ≤ (∏ p ∈ d.primeFactors with 2 < p, (1 - 1 / (p : ℝ))) * pairSingularProduct d := by
  unfold pairSingularProduct
  set T := d.primeFactors.filter (fun p => 2 < p)
  rw [← prod_mul_distrib]
  have e : ∀ p ∈ T, (1 - 1 / (p : ℝ)) * (1 + 1 / p) = 1 - 1 / (p : ℝ) ^ 2 := by
    intro p _; ring
  rw [prod_congr rfl e]
  have hT : ∀ p ∈ T, 3 ≤ p := fun p hp => (mem_filter.mp hp).2
  refine le_trans ?_ (one_sub_sum_le_prod T _ (fun p _ => by positivity) (fun p hp => by
    have : (3 : ℝ) ≤ p := by exact_mod_cast hT p hp
    rw [div_le_one (by positivity)]; nlinarith))
  have hsub : T ⊆ Icc 3 d := fun p hp => by
    have h1 := hT p hp
    have h2 : p ≤ d := Nat.le_of_dvd hd (Nat.dvd_of_mem_primeFactors (mem_filter.mp hp).1)
    exact mem_Icc.mpr ⟨h1, h2⟩
  have hle : ∑ p ∈ T, (1 : ℝ) / (p : ℝ) ^ 2 ≤ ∑ n ∈ Icc 3 d, (1 : ℝ) / (n : ℝ) ^ 2 :=
    sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
  rcases lt_or_ge d 2 with h | h
  · have : T = ∅ := by
      ext p; simp only [notMem_empty, iff_false]; intro hp
      have := hsub hp; simp at this; omega
    simp [this]; norm_num
  · have := sum_Icc_three_inv_sq_le d h
    have : (0 : ℝ) ≤ 1 / (d : ℝ) := by positivity
    linarith

theorem pair_hFun (d : ℕ) {p : ℕ} (hd : Even d) (hp : p.Prime) :
    hFun (fun p => (pairOmega d p : ℝ) / p) p
      = (pairOmega d p : ℝ) / ((p : ℝ) - pairOmega d p) := by
  have hlt : (pairOmega d p : ℝ) < p := by exact_mod_cast pairOmega_lt hd hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  unfold hFun
  have : (p : ℝ) - pairOmega d p ≠ 0 := by linarith
  field_simp

theorem pair_hFun_nonneg (d : ℕ) {p : ℕ} (hd : Even d) (hp : p.Prime) :
    0 ≤ hFun (fun p => (pairOmega d p : ℝ) / p) p := by
  rw [pair_hFun d hd hp]
  have hlt : (pairOmega d p : ℝ) < p := by exact_mod_cast pairOmega_lt hd hp
  exact div_nonneg (Nat.cast_nonneg _) (by linarith)

theorem pair_hFun_le (d : ℕ) {p : ℕ} (hd : Even d) (hp : p.Prime) :
    hFun (fun p => (pairOmega d p : ℝ) / p) p ≤ 6 / p := by
  rw [pair_hFun d hd hp]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  unfold pairOmega
  split_ifs with h
  · push_cast
    rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith
  · have h2 : p ≠ 2 := by rintro rfl; exact h (even_iff_two_dvd.mp hd)
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by have := hp.two_le; omega)
    push_cast
    rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith

theorem pair_one_add_hFun_ge (d : ℕ) {p : ℕ} (hd : Even d) (hp : p.Prime) :
    (1 - 1 / (p : ℝ))⁻¹ ^ 2 * (if p ∣ d then 1 - 1 / (p : ℝ) else 1)
      ≤ 1 + hFun (fun p => (pairOmega d p : ℝ) / p) p := by
  rw [pair_hFun d hd hp]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have e : 1 - 1 / (p : ℝ) = ((p : ℝ) - 1) / p := by field_simp
  rw [e, inv_div]
  unfold pairOmega
  split_ifs with h
  · push_cast
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    rw [div_pow, div_mul_div_comm, div_le_iff₀ (by positivity)]
    have : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp; nlinarith
  · have h2 : p ≠ 2 := by rintro rfl; exact h (even_iff_two_dvd.mp hd)
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by have := hp.two_le; omega)
    push_cast
    rw [mul_one, div_pow, div_le_iff₀ (by nlinarith)]
    have : (p : ℝ) - 2 ≠ 0 := by linarith
    rw [show (1 : ℝ) + 2 / ((p : ℝ) - 2) = p / ((p : ℝ) - 2) by field_simp; ring]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    nlinarith

/-- Rankin step for the prime-pair sieve: with `Y ≤ z^{1/37}`, `G_d(z) ≥ ½ Π_{p ≤ Y} (1 + h(p))`. -/
theorem pair_rankin_half (d z Y : ℕ) (hd : Even d) (hY3 : 3 ≤ Y) (hYz : Y < z)
    (hlYup : Real.log Y ≤ Real.log z / 37)
    (hM1 : ∀ N : ℕ, ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ Real.log N + Real.log 4) :
    (1 / 2) * ∏ p ∈ Nat.primesLE Y, (1 + hFun (fun p => (pairOmega d p : ℝ) / p) p)
      ≤ pairG d z := by
  set g : ℕ → ℝ := fun p => (pairOmega d p : ℝ) / p
  have hYR : (3 : ℝ) ≤ Y := by exact_mod_cast hY3
  have hlY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hzR : (2 : ℝ) ≤ z := by exact_mod_cast (show 2 ≤ z by omega)

  set Q := Nat.primesLE Y
  have hQp : ∀ p ∈ Q, p.Prime := fun p hp => (Nat.mem_primesLE.mp hp).2
  have hQQ : Q ⊆ Nat.primesBelow z := fun p hp => by
    have := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesBelow.mpr ⟨by omega, this.2⟩
  set ε : ℝ := 1 / Real.log Y
  have hε : 0 ≤ ε := by positivity
  have hrank := selbergG_ge_rankin g Q (Nat.primesBelow z) hQQ hQp
    (fun p hp => pair_hFun_nonneg d hd (Nat.mem_primesBelow.mp hp).2) z (by omega) hε
  change _ ≤ pairG d z at hrank
  set H : ℕ → ℝ := fun p => hFun g p
  have hH0 : ∀ p ∈ Q, 0 ≤ H p := fun p hp => pair_hFun_nonneg d hd (hQp p hp)
  -- the Rankin tail
  have hpe : ∀ p ∈ Q, (p : ℝ) ^ ε - 1 ≤ 2 * (Real.log p / Real.log Y) := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hQp p hp).one_lt.le
    have hlp : 0 ≤ Real.log p := Real.log_nonneg hp1
    have hlpY : Real.log p ≤ Real.log Y :=
      Real.log_le_log (by linarith) (by exact_mod_cast (Nat.mem_primesLE.mp hp).1)
    have ht : |Real.log p * ε| ≤ 1 := by
      rw [abs_of_nonneg (by positivity)]
      simp only [ε]; rw [mul_one_div, div_le_one hlY]; exact hlpY
    rw [Real.rpow_def_of_pos (by linarith)]
    have := (abs_le.mp (Real.abs_exp_sub_one_le ht)).2
    rw [abs_of_nonneg (by positivity)] at this
    have e : Real.log p * ε = Real.log p / Real.log Y := by simp only [ε]; ring
    rw [← e]; exact this
  have hsumtail : ∑ p ∈ Q, H p * ((p : ℝ) ^ ε - 1) ≤ 36 := by
    calc ∑ p ∈ Q, H p * ((p : ℝ) ^ ε - 1)
        ≤ ∑ p ∈ Q, (6 / (p : ℝ)) * (2 * (Real.log p / Real.log Y)) := by
          refine sum_le_sum fun p hp => ?_
          have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hQp p hp).one_lt.le
          have : (0 : ℝ) ≤ (p : ℝ) ^ ε - 1 := by
            have := Real.one_le_rpow hp1 hε; linarith
          exact mul_le_mul (pair_hFun_le d hd (hQp p hp)) (hpe p hp) this (by positivity)
      _ = (12 / Real.log Y) * ∑ p ∈ Q, Real.log p / p := by
          rw [mul_sum]; refine sum_congr rfl fun p _ => by ring
      _ ≤ (12 / Real.log Y) * (Real.log Y + Real.log 4) :=
          mul_le_mul_of_nonneg_left (hM1 Y) (by positivity)
      _ ≤ 36 := by
          have h4 : Real.log 4 ≤ 2 * Real.log Y := by
            have : Real.log 4 = 2 * Real.log 2 := by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
            have : Real.log 2 ≤ Real.log Y := Real.log_le_log (by norm_num) (by linarith)
            linarith
          rw [div_mul_eq_mul_div, div_le_iff₀ hlY]; nlinarith
  have hprod_tail : ∏ p ∈ Q, (1 + H p * (p : ℝ) ^ ε)
      ≤ (∏ p ∈ Q, (1 + H p)) * Real.exp 36 := by
    calc ∏ p ∈ Q, (1 + H p * (p : ℝ) ^ ε)
        ≤ ∏ p ∈ Q, ((1 + H p) * Real.exp (H p * ((p : ℝ) ^ ε - 1))) := by
          refine prod_le_prod (fun p hp => by
            have := hH0 p hp; positivity) fun p hp => ?_
          have h0 := hH0 p hp
          have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hQp p hp).one_lt.le
          have hb : 1 ≤ (p : ℝ) ^ ε := Real.one_le_rpow hp1 hε
          have := Real.add_one_le_exp (H p * ((p : ℝ) ^ ε - 1))
          nlinarith [mul_nonneg h0 (by linarith : (0:ℝ) ≤ (p : ℝ) ^ ε - 1)]
      _ = (∏ p ∈ Q, (1 + H p)) * Real.exp (∑ p ∈ Q, H p * ((p : ℝ) ^ ε - 1)) := by
          rw [prod_mul_distrib, Real.exp_sum]
      _ ≤ (∏ p ∈ Q, (1 + H p)) * Real.exp 36 :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsumtail)
            (prod_nonneg fun p hp => by have := hH0 p hp; linarith)
  have hzeps : (z : ℝ) ^ (-ε) ≤ Real.exp (-37) := by
    rw [Real.rpow_def_of_pos (by linarith), Real.exp_le_exp]
    simp only [ε]
    rw [mul_neg, mul_one_div, neg_le_neg_iff, le_div_iff₀ hlY]; linarith
  have hP0 : 0 ≤ ∏ p ∈ Q, (1 + H p) := prod_nonneg fun p hp => by have := hH0 p hp; linarith
  have hhalf : (1 / 2) * ∏ p ∈ Q, (1 + H p) ≤ pairG d z := by
    have he : Real.exp (-37) * Real.exp 36 ≤ 1 / 2 := by
      rw [← Real.exp_add]; norm_num
      have := Real.exp_one_gt_d9
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]; norm_num; linarith
    have ht : (z : ℝ) ^ (-ε) * ∏ p ∈ Q, (1 + H p * (p : ℝ) ^ ε)
        ≤ (1 / 2) * ∏ p ∈ Q, (1 + H p) := by
      calc (z : ℝ) ^ (-ε) * ∏ p ∈ Q, (1 + H p * (p : ℝ) ^ ε)
          ≤ Real.exp (-37) * ((∏ p ∈ Q, (1 + H p)) * Real.exp 36) :=
            mul_le_mul hzeps hprod_tail (prod_nonneg fun p hp => by
              have := hH0 p hp; positivity) (Real.exp_pos _).le
        _ = (Real.exp (-37) * Real.exp 36) * ∏ p ∈ Q, (1 + H p) := by ring
        _ ≤ (1 / 2) * ∏ p ∈ Q, (1 + H p) := mul_le_mul_of_nonneg_right he hP0
    linarith
  exact hhalf

/-- Euler-product lower bound: `Π_{p ≤ Y} (1 + h(p)) ≥ (Π_{p ≤ Y} (1 - 1/p))⁻² Π_{p ∣ d} (1 - 1/p)`. -/
theorem pair_euler_ge (d Y : ℕ) (hd0 : 0 < d) (hd : Even d) :
    ((∏ p ∈ Nat.primesLE Y, (1 - 1 / (p : ℝ)))⁻¹) ^ 2 * ∏ p ∈ d.primeFactors, (1 - 1 / (p : ℝ))
      ≤ ∏ p ∈ Nat.primesLE Y, (1 + hFun (fun p => (pairOmega d p : ℝ) / p) p) := by
  set Q := Nat.primesLE Y
  have hQp : ∀ p ∈ Q, p.Prime := fun p hp => (Nat.mem_primesLE.mp hp).2
  set H : ℕ → ℝ := fun p => hFun (fun p => (pairOmega d p : ℝ) / p) p

  -- Mertens lower bound for the Euler product
  have hE : ((∏ p ∈ Q, (1 - 1 / (p : ℝ)))⁻¹) ^ 2 * ∏ p ∈ d.primeFactors, (1 - 1 / (p : ℝ))
      ≤ ∏ p ∈ Q, (1 + H p) := by
    have hf : ∀ p ∈ Q, 0 ≤ 1 - 1 / (p : ℝ) := fun p hp => by
      have : (1 : ℝ) ≤ p := by exact_mod_cast (hQp p hp).one_lt.le
      rw [sub_nonneg, div_le_one (by linarith)]; exact this
    have step1 : ∏ p ∈ Q, ((1 - 1 / (p : ℝ))⁻¹ ^ 2 * (if p ∣ d then 1 - 1 / (p : ℝ) else 1))
        ≤ ∏ p ∈ Q, (1 + H p) :=
      prod_le_prod (fun p hp => by
        have := hf p hp
        split_ifs <;> positivity) fun p hp => pair_one_add_hFun_ge d hd (hQp p hp)
    rw [prod_mul_distrib, prod_pow, prod_inv_distrib] at step1
    refine le_trans ?_ step1
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← prod_filter]
    have hsub : Q.filter (fun p => p ∣ d) ⊆ d.primeFactors := fun p hp => by
      simp only [mem_filter] at hp
      exact Nat.mem_primeFactors.mpr ⟨hQp p hp.1, hp.2, hd0.ne'⟩
    rw [← prod_sdiff hsub]
    have h0 : 0 ≤ ∏ p ∈ Q.filter (fun p => p ∣ d), (1 - 1 / (p : ℝ)) :=
      prod_nonneg fun p hp => hf p (mem_filter.mp hp).1
    have h1 : ∏ p ∈ d.primeFactors \ Q.filter (fun p => p ∣ d), (1 - 1 / (p : ℝ)) ≤ 1 := by
      refine prod_le_one (fun p hp => ?_) (fun p hp => ?_)
      · have hp' := Nat.prime_of_mem_primeFactors (mem_sdiff.mp hp).1
        have : (1 : ℝ) ≤ p := by exact_mod_cast hp'.one_lt.le
        rw [sub_nonneg, div_le_one (by linarith)]; exact this
      · have : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
        linarith
    nlinarith
  exact hE

/-- **Discharging `PairGLowerBound` from Mertens' theorems.** The inputs are Mertens' first
theorem (upper half) and the upper half of Mertens' product theorem, in exactly the form proved
in `OMALib.Mertens` (`sum_log_div_le_nat`, `prod_one_sub_inv_bounds`). -/
theorem pairGLowerBound_of_mertens {M : ℝ} (hM : 0 < M)
    (hM1 : ∀ N : ℕ, ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ Real.log N + Real.log 4)
    (hM3 : ∀ N : ℕ, 2 ≤ N → ∏ p ∈ Nat.primesLE N, (1 - 1 / (p : ℝ)) ≤ M / Real.log N) :
    PairGLowerBound (min (1 / 2700) (1 / (43808 * M ^ 2))) := by
  intro d hd0 hd z hz
  set g : ℕ → ℝ := fun p => (pairOmega d p : ℝ) / p
  have hgQ0 : ∀ p ∈ Nat.primesBelow z, 0 < g p := fun p hp =>
    div_pos (by exact_mod_cast pairOmega_pos d p)
      (by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.pos)
  have hgQ1 : ∀ p ∈ Nat.primesBelow z, g p < 1 := fun p hp => by
    have hp' := (Nat.mem_primesBelow.mp hp).2
    simp only [g]; rw [div_lt_one (by exact_mod_cast hp'.pos)]; exact_mod_cast pairOmega_lt hd hp'
  have hG1 : 1 ≤ pairG d z :=
    one_le_selbergG hgQ0 hgQ1 levelFamily_subset (empty_mem_levelFamily hz)
  have hPP := one_le_pairSingularProduct d
  have hzR : (2 : ℝ) ≤ z := by exact_mod_cast hz
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hl2 := Real.log_two_lt_d9
  have hl2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmin1 : min (1 / 2700) (1 / (43808 * M ^ 2)) ≤ 1 / 2700 := min_le_left _ _
  have hmin2 : min (1 / 2700) (1 / (43808 * M ^ 2)) ≤ 1 / (43808 * M ^ 2) := min_le_right _ _
  have hmin0 : 0 < min (1 / 2700) (1 / (43808 * M ^ 2)) := lt_min (by norm_num) (by positivity)
  set c := min (1 / 2700) (1 / (43808 * M ^ 2))
  have hGP : 1 ≤ pairG d z * pairSingularProduct d := by nlinarith
  by_cases hbig : 74 * Real.log 2 ≤ Real.log z
  swap
  · push_neg at hbig
    have : Real.log z ^ 2 ≤ 2700 := by nlinarith
    calc c * Real.log z ^ 2 ≤ (1 / 2700) * 2700 := by
          apply mul_le_mul hmin1 this (sq_nonneg _) (by norm_num)
      _ = 1 := by norm_num
      _ ≤ _ := hGP
  -- large z
  set y : ℝ := (z : ℝ) ^ ((1 : ℝ) / 37) with hydef
  have hz0 : (0 : ℝ) ≤ z := Nat.cast_nonneg z
  have hy0 : 0 < y := Real.rpow_pos_of_pos (by linarith) _
  have hlogy : Real.log y = Real.log z / 37 := by
    rw [hydef, Real.log_rpow (by linarith)]; ring
  have hy4 : Real.log 4 ≤ Real.log y := by
    rw [hlogy, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
  have hy4' : 4 ≤ y := by
    have := Real.exp_le_exp.mpr hy4
    rwa [Real.exp_log (by norm_num), Real.exp_log hy0] at this
  set Y := ⌊y⌋₊
  have hYle : (Y : ℝ) ≤ y := Nat.floor_le hy0.le
  have hYgt : y < Y + 1 := Nat.lt_floor_add_one y
  have hY3 : 3 ≤ Y := by
    have : (3 : ℝ) < Y := by linarith
    exact_mod_cast this.le
  have hYR : (3 : ℝ) ≤ Y := by exact_mod_cast hY3
  have hlY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hlYup : Real.log Y ≤ Real.log z / 37 := by
    rw [← hlogy]; exact Real.log_le_log (by linarith) hYle
  have hlYlo : Real.log z / 74 ≤ Real.log Y := by
    have h1 : Real.log (y / 2) ≤ Real.log Y := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_div hy0.ne' (by norm_num), hlogy] at h1
    linarith
  have hYz : Y < z := by
    have h1 : Real.log Y < Real.log z := by linarith
    have := (Real.log_lt_log_iff (by linarith) (by linarith)).mp h1
    exact_mod_cast this
  set Q := Nat.primesLE Y
  have hQp : ∀ p ∈ Q, p.Prime := fun p hp => (Nat.mem_primesLE.mp hp).2
  set H : ℕ → ℝ := fun p => hFun g p
  have hhalf := pair_rankin_half d z Y hd hY3 hYz hlYup hM1
  have hE := pair_euler_ge d Y hd0 hd
  have hM3Y := hM3 Y (by omega)
  have hQpos : 0 < ∏ p ∈ Q, (1 - 1 / (p : ℝ)) := prod_pos fun p hp => by
    have : (2 : ℝ) ≤ p := by exact_mod_cast (hQp p hp).two_le
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) this
    linarith
  have hinv : Real.log Y / M ≤ (∏ p ∈ Q, (1 - 1 / (p : ℝ)))⁻¹ := by
    rw [le_inv_comm₀ (by positivity) hQpos, inv_div]; exact hM3Y
  -- the factor at the primes dividing d
  have h2d : 2 ∈ d.primeFactors := Nat.mem_primeFactors.mpr
    ⟨Nat.prime_two, even_iff_two_dvd.mp hd, hd0.ne'⟩
  have hsplit2 : ∏ p ∈ d.primeFactors, (1 - 1 / (p : ℝ))
      = (1 / 2) * ∏ p ∈ d.primeFactors with 2 < p, (1 - 1 / (p : ℝ)) := by
    have : d.primeFactors.filter (fun p => 2 < p) = d.primeFactors.erase 2 := by
      ext p; simp only [mem_filter, mem_erase]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h2, by have := (Nat.prime_of_mem_primeFactors h2).two_le; omega⟩
    rw [this, ← mul_prod_erase _ _ h2d]; norm_num
  have hodd := prod_odd_one_sub_mul_ge d hd0
  have hD : 1 / 4 ≤ (∏ p ∈ d.primeFactors, (1 - 1 / (p : ℝ))) * pairSingularProduct d := by
    rw [hsplit2]
    have : 1 / 2 * (∏ p ∈ d.primeFactors with 2 < p, (1 - 1 / (p : ℝ))) * pairSingularProduct d
        = 1 / 2 * ((∏ p ∈ d.primeFactors with 2 < p, (1 - 1 / (p : ℝ))) * pairSingularProduct d) := by
      ring
    linarith
  -- assemble
  have hY2 : (Real.log z / 74) ^ 2 / M ^ 2 ≤ ((∏ p ∈ Q, (1 - 1 / (p : ℝ)))⁻¹) ^ 2 := by
    have : Real.log z / 74 / M ≤ (∏ p ∈ Q, (1 - 1 / (p : ℝ)))⁻¹ :=
      le_trans (div_le_div_of_nonneg_right hlYlo hM.le) hinv
    rw [← div_pow]; exact pow_le_pow_left₀ (by positivity) this 2
  have hDpos : 0 ≤ ∏ p ∈ d.primeFactors, (1 - 1 / (p : ℝ)) := prod_nonneg fun p hp => by
    have : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
    rw [sub_nonneg, div_le_one (by linarith)]; exact this
  have hfinal : (Real.log z / 74) ^ 2 / M ^ 2 * (1 / 8) ≤ pairG d z * pairSingularProduct d := by
    set A := (Real.log z / 74) ^ 2 / M ^ 2
    set P := ∏ p ∈ d.primeFactors, (1 - 1 / (p : ℝ))
    set E := ∏ p ∈ Q, (1 + H p)
    set PP := pairSingularProduct d
    have hA0 : 0 ≤ A := by positivity
    have hPP0 : 0 ≤ PP := by linarith
    have a1 : A * P ≤ E := le_trans (mul_le_mul_of_nonneg_right hY2 hDpos) hE
    have a2 : A * (1 / 4) ≤ A * (P * PP) := mul_le_mul_of_nonneg_left hD hA0
    have a3 : A * P * PP ≤ E * PP := mul_le_mul_of_nonneg_right a1 hPP0
    have a4 : 1 / 2 * E * PP ≤ pairG d z * PP := mul_le_mul_of_nonneg_right hhalf hPP0
    have e1 : A * P * PP = A * (P * PP) := by ring
    have e2 : 1 / 2 * E * PP = 1 / 2 * (E * PP) := by ring
    linarith
  have hc : c * Real.log z ^ 2 ≤ (Real.log z / 74) ^ 2 / M ^ 2 * (1 / 8) := by
    have : (Real.log z / 74) ^ 2 / M ^ 2 * (1 / 8) = (1 / (43808 * M ^ 2)) * Real.log z ^ 2 := by
      field_simp; ring
    rw [this]; exact mul_le_mul_of_nonneg_right hmin2 (sq_nonneg _)
  linarith

end OMALib.Sieve


/-
Unconditional prime-pair bound: `Sieve.lean` combined with `Mertens.lean`.

This file is meant to be appended after the contents of `Mertens.lean` (namespace
`OMALib.Mertens`) and `Sieve.lean` (namespace `OMALib.Sieve`); it uses
`OMALib.Mertens.sum_log_div_le_nat` and `OMALib.Mertens.prod_one_sub_inv_bounds` to discharge
the Mertens-type hypothesis `OMALib.Sieve.PairGLowerBound`.
-/

open scoped Classical
open Finset

namespace OMALib.Sieve

/-- The Mertens-type input `PairGLowerBound c` holds for an explicit absolute `c > 0`. -/
theorem exists_pairGLowerBound : ∃ c : ℝ, 0 < c ∧ PairGLowerBound c := by
  set M := Real.exp OMALib.Mertens.mertens2Const
  have hM : 0 < M := Real.exp_pos _
  refine ⟨min (1 / 2700) (1 / (43808 * M ^ 2)), lt_min (by norm_num) (by positivity),
    pairGLowerBound_of_mertens hM OMALib.Mertens.sum_log_div_le_nat ?_⟩
  intro N hN
  have h := (OMALib.Mertens.prod_one_sub_inv_bounds (N : ℝ) (by exact_mod_cast hN)).2
  rwa [Nat.floor_natCast] at h

/-- **Upper bound for prime pairs with a given difference, unconditional (Romanoff-ready).**
There is an absolute `C > 0` such that for every even `d > 0` and every `x ≥ 2`,
`#{p ≤ x : p and p + d prime} ≤ C · x / log² x · Π_{p ∣ d, p > 2} (1 + 1/p)`. -/
theorem prime_pairs_upper_bound' :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 0 < d → Even d → ∀ x : ℕ, 2 ≤ x →
      (((range (x + 1)).filter (fun p => p.Prime ∧ (p + d).Prime)).card : ℝ)
        ≤ C * ((x : ℝ) / Real.log x ^ 2) * pairSingularProduct d := by
  obtain ⟨c, hc, hG⟩ := exists_pairGLowerBound
  exact prime_pairs_upper_bound hc hG

end OMALib.Sieve


open scoped Classical
open Finset

namespace RomA

noncomputable def F (n : ℕ) : ℝ := OMALib.Sieve.pairSingularProduct n

def oddPF (n : ℕ) : Finset ℕ := n.primeFactors.filter (fun p => 2 < p)

noncomputable def w (T : Finset ℕ) : ℝ := ∏ p ∈ T, (1 / (p : ℝ))

noncomputable def ordT (T : Finset ℕ) : ℕ := orderOf (2 : ZMod (∏ p ∈ T, p))

noncomputable def PP (Y : ℕ) : ℕ := ∏ e ∈ Ioc 0 Y, (2 ^ e - 1)

theorem F_eq_sum (n : ℕ) : F n = ∑ T ∈ (oddPF n).powerset, w T := by
  unfold F OMALib.Sieve.pairSingularProduct oddPF w
  exact Finset.prod_one_add _

theorem w_nonneg (T : Finset ℕ) : 0 ≤ w T := by
  unfold w; exact Finset.prod_nonneg fun p _ => by positivity

theorem F_nonneg (n : ℕ) : 0 ≤ F n :=
  le_trans zero_le_one (OMALib.Sieve.one_le_pairSingularProduct n)

theorem mem_oddPF {n p : ℕ} (h : p ∈ oddPF n) : p.Prime ∧ 2 < p := by
  simp only [oddPF, mem_filter, Nat.mem_primeFactors] at h
  exact ⟨h.1.1, h.2⟩

theorem coprime_two_prod {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime ∧ 2 < p) :
    Nat.Coprime 2 (∏ p ∈ T, p) := by
  apply Nat.Coprime.prod_right
  intro p hp
  exact (Nat.coprime_primes Nat.prime_two (hT p hp).1).mpr (by have := (hT p hp).2; omega)

theorem ordT_pos {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime ∧ 2 < p) : 0 < ordT T := by
  unfold ordT
  have hcop := coprime_two_prod hT
  have hq : 0 < ∏ p ∈ T, p := Finset.prod_pos fun p hp => (hT p hp).1.pos
  have h := Nat.ModEq.pow_totient hcop
  have h1 : (2 : ZMod (∏ p ∈ T, p)) ^ (∏ p ∈ T, p).totient = 1 := by
    have := (ZMod.natCast_eq_natCast_iff' _ _ _).mpr h
    simpa using this
  exact orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨_, Nat.totient_pos.mpr hq, h1⟩)

theorem pow_eq_one_of_dvd {q m : ℕ} (h : q ∣ 2 ^ m - 1) : (2 : ZMod q) ^ m = 1 := by
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have : ((2 ^ m - 1 : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
  rw [Nat.cast_sub h1] at this
  push_cast at this
  exact sub_eq_zero.mp this

theorem dvd_of_pow_eq_one {q m : ℕ} (h : (2 : ZMod q) ^ m = 1) : q ∣ 2 ^ m - 1 := by
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  rw [Nat.cast_sub h1]; push_cast; rw [h]; simp

theorem prod_dvd_of_subset {T : Finset ℕ} {n : ℕ} (h : T ⊆ oddPF n) : (∏ p ∈ T, p) ∣ n :=
  (Finset.prod_dvd_prod_of_subset _ _ _ (h.trans (filter_subset _ _))).trans
    (Nat.prod_primeFactors_dvd n)

theorem subset_of_prod_dvd {T : Finset ℕ} {n : ℕ} (hT : ∀ p ∈ T, p.Prime ∧ 2 < p) (hn : n ≠ 0)
    (h : (∏ p ∈ T, p) ∣ n) : T ⊆ oddPF n := by
  intro p hp
  simp only [oddPF, mem_filter, Nat.mem_primeFactors]
  exact ⟨⟨(hT p hp).1, (Finset.dvd_prod_of_mem _ hp).trans h, hn⟩, (hT p hp).2⟩

theorem card_le {T : Finset ℕ} (K : ℕ) :
    ((Ioc 0 K).filter (fun m => T ⊆ oddPF (2 ^ m - 1))).card ≤ K / ordT T := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div K (ordT T)]
  apply card_le_card
  intro m hm
  simp only [mem_filter] at hm ⊢
  refine ⟨hm.1, ?_⟩
  unfold ordT
  exact orderOf_dvd_iff_pow_eq_one.mpr (pow_eq_one_of_dvd (prod_dvd_of_subset hm.2))

theorem PP_pos (Y : ℕ) : 0 < PP Y := Finset.prod_pos fun e he => by
  have : 1 < 2 ^ e := Nat.one_lt_two_pow (by simp at he; omega)
  omega

theorem subset_PP {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime ∧ 2 < p) {Y : ℕ} (hY : ordT T ≤ Y) :
    T ⊆ oddPF (PP Y) := by
  apply subset_of_prod_dvd hT (PP_pos Y).ne'
  have he := ordT_pos hT
  have h1 : (∏ p ∈ T, p) ∣ 2 ^ ordT T - 1 := dvd_of_pow_eq_one (pow_orderOf_eq_one _)
  exact h1.trans (Finset.dvd_prod_of_mem _ (by simp; omega))

theorem PP_le (Y : ℕ) : PP Y ≤ 2 ^ (Y * Y) := by
  unfold PP
  calc ∏ e ∈ Ioc 0 Y, (2 ^ e - 1) ≤ ∏ _e ∈ Ioc 0 Y, 2 ^ Y := Finset.prod_le_prod' fun e he => by
        simp at he; exact (Nat.sub_le _ _).trans (Nat.pow_le_pow_right two_pos he.2)
    _ = 2 ^ (Y * Y) := by rw [prod_const, Nat.card_Ioc, ← pow_mul]; simp

theorem F_bound : ∃ A : ℝ, 0 < A ∧ ∀ N j : ℕ, 0 < N → N ≤ 2 ^ (4 ^ j) → F N ≤ A * (j + 1) := by
  set c := OMALib.Mertens.mertens2Const + OMALib.Mertens.primePowerConst / Real.log 2
  refine ⟨3 * (1 + 2 * Real.exp c), by positivity, ?_⟩
  intro N j hN hNle
  set L := 4 ^ j with hLdef
  have hsplit : F N = (∏ p ∈ (oddPF N).filter (fun p => p ≤ L), (1 + 1 / (p : ℝ))) *
      ∏ p ∈ (oddPF N).filter (fun p => ¬ p ≤ L), (1 + 1 / (p : ℝ)) := by
    unfold F OMALib.Sieve.pairSingularProduct
    exact (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
  have hbig : ∏ p ∈ (oddPF N).filter (fun p => ¬ p ≤ L), (1 + 1 / (p : ℝ)) ≤ 3 := by
    set B := (oddPF N).filter (fun p => ¬ p ≤ L) with hB
    have hLpos : (0 : ℝ) < L := by positivity
    have hcard : B.card ≤ L := by
      have h2 : 2 ^ B.card ≤ ∏ p ∈ B, p := Finset.pow_card_le_prod _ _ _ (fun p hp => by
        exact (mem_oddPF (mem_filter.mp hp).1).1.two_le)
      have h3 : ∏ p ∈ B, p ≤ N := Nat.le_of_dvd hN
        ((Finset.prod_dvd_prod_of_subset _ _ _ ((filter_subset _ _).trans (filter_subset _ _))).trans
          (Nat.prod_primeFactors_dvd N))
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (h2.trans (h3.trans hNle))
    calc ∏ p ∈ B, (1 + 1 / (p : ℝ)) ≤ ∏ _p ∈ B, (1 + 1 / (L : ℝ)) := by
          apply Finset.prod_le_prod (fun p _ => by positivity)
          intro p hp
          have hp' := (mem_filter.mp hp).2
          have : (L : ℝ) ≤ p := by exact_mod_cast (not_le.mp hp').le
          gcongr
      _ = (1 + 1 / (L : ℝ)) ^ B.card := prod_const _
      _ ≤ (1 + 1 / (L : ℝ)) ^ L := pow_le_pow_right₀ (by
            have : (0:ℝ) ≤ 1 / (L:ℝ) := by positivity
            linarith) hcard
      _ ≤ (Real.exp (1 / L)) ^ L := by
            gcongr; linarith [Real.add_one_le_exp (1 / (L : ℝ))]
      _ = Real.exp 1 := by rw [← Real.exp_nat_mul]; congr 1; field_simp
      _ ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have hsmall : ∏ p ∈ (oddPF N).filter (fun p => p ≤ L), (1 + 1 / (p : ℝ)) ≤
      1 + 2 * Real.exp c * j := by
    rcases Nat.eq_zero_or_pos j with hj | hj
    · have hL1 : L = 1 := by rw [hLdef, hj]; rfl
      have : (oddPF N).filter (fun p => p ≤ L) = ∅ := by
        ext p
        simp only [mem_filter, Finset.notMem_empty, iff_false, not_and, not_le]
        intro hp
        have := (mem_oddPF hp).2
        omega
      rw [this, hj]; simp
    · have hL4 : 4 ≤ L := by
        rw [hLdef]; calc 4 = 4 ^ 1 := by norm_num
          _ ≤ 4 ^ j := Nat.pow_le_pow_right (by norm_num) hj
      have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (by omega : 2 ≤ L)
      have hsub : (oddPF N).filter (fun p => p ≤ L) ⊆ Nat.primesLE ⌊(L : ℝ)⌋₊ := by
        intro p hp
        rw [Nat.floor_natCast]
        have h1 := mem_filter.mp hp
        exact Nat.mem_primesLE.mpr ⟨h1.2, (mem_oddPF h1.1).1⟩
      have hbd := (OMALib.Mertens.prod_one_sub_inv_bounds (L : ℝ) hL2).1
      have hlogL : 0 < Real.log (L : ℝ) := Real.log_pos (by linarith)
      have hpos : 0 < ∏ p ∈ Nat.primesLE ⌊(L : ℝ)⌋₊, (1 - 1 / (p : ℝ)) :=
        lt_of_lt_of_le (by positivity) hbd
      have hlog4 : Real.log (L : ℝ) ≤ 2 * j := by
        rw [hLdef]; push_cast; rw [Real.log_pow]
        have : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
        have h2 := Real.log_two_lt_d9
        have hj' : (0 : ℝ) ≤ j := by positivity
        nlinarith
      calc ∏ p ∈ (oddPF N).filter (fun p => p ≤ L), (1 + 1 / (p : ℝ))
          ≤ ∏ p ∈ Nat.primesLE ⌊(L : ℝ)⌋₊, (1 + 1 / (p : ℝ)) :=
            Finset.prod_le_prod_of_subset_of_one_le hsub (fun p _ => by positivity) (fun p _ _ => by
              have : (0:ℝ) ≤ 1 / (p:ℝ) := by positivity
              linarith)
        _ ≤ ∏ p ∈ Nat.primesLE ⌊(L : ℝ)⌋₊, (1 - 1 / (p : ℝ))⁻¹ := by
            apply Finset.prod_le_prod (fun p _ => by positivity)
            intro p hp
            have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
            have hq : 0 < 1 - 1 / (p : ℝ) := by
              have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
              linarith
            rw [← one_div, le_div_iff₀ hq]
            have : 0 ≤ 1 / (p : ℝ) := by positivity
            nlinarith
        _ = (∏ p ∈ Nat.primesLE ⌊(L : ℝ)⌋₊, (1 - 1 / (p : ℝ)))⁻¹ := prod_inv_distrib _
        _ ≤ (Real.exp (-c) / Real.log L)⁻¹ := inv_anti₀ (by positivity) hbd
        _ = Real.exp c * Real.log L := by rw [inv_div, Real.exp_neg]; field_simp
        _ ≤ Real.exp c * (2 * j) := by gcongr
        _ ≤ 1 + 2 * Real.exp c * j := by nlinarith
  rw [hsplit]
  have h0 : 0 ≤ ∏ p ∈ (oddPF N).filter (fun p => ¬ p ≤ L), (1 + 1 / (p : ℝ)) :=
    Finset.prod_nonneg fun p _ => by positivity
  have hj0 : (0 : ℝ) ≤ j := by positivity
  have he : 0 < Real.exp c := Real.exp_pos c
  calc _ ≤ (1 + 2 * Real.exp c * j) * 3 := mul_le_mul hsmall hbig h0 (by positivity)
    _ ≤ 3 * (1 + 2 * Real.exp c) * (j + 1) := by nlinarith

theorem div_le_sum (e K : ℕ) (he : 0 < e) :
    ((K / e : ℕ) : ℝ) ≤ K * ∑ j ∈ range (K + 1), (if e < 2 ^ (j + 1) then (1 / 2 : ℝ) ^ j else 0) := by
  have hnn : ∀ j ∈ range (K + 1), (0 : ℝ) ≤ (if e < 2 ^ (j + 1) then (1 / 2 : ℝ) ^ j else 0) := by
    intro j _; split_ifs <;> positivity
  rcases lt_or_ge K e with hKe | hKe
  · rw [Nat.div_eq_of_lt hKe]; simp only [Nat.cast_zero]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg hnn)
  · set j0 := Nat.log 2 e
    have h1 : 2 ^ j0 ≤ e := Nat.pow_log_le_self 2 he.ne'
    have h2 : e < 2 ^ (j0 + 1) := Nat.lt_pow_succ_log_self (by norm_num) e
    have hj0 : j0 ∈ range (K + 1) := by
      have := (Nat.lt_two_pow_self (n := j0)); simp; omega
    have hs := Finset.single_le_sum hnn hj0
    simp only [h2, if_true] at hs
    calc ((K / e : ℕ) : ℝ) ≤ (K : ℝ) / e := Nat.cast_div_le
      _ ≤ (K : ℝ) / 2 ^ j0 := by
          gcongr
          exact_mod_cast h1
      _ = K * (1 / 2 : ℝ) ^ j0 := by rw [div_eq_mul_inv, one_div, inv_pow]
      _ ≤ _ := by gcongr

theorem geom_sum (n : ℕ) :
    ∑ j ∈ range n, ((j : ℝ) + 2) * (1 / 2 : ℝ) ^ j = 6 - (2 * n + 6) * (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, pow_succ]; push_cast; ring

theorem S_bound : ∃ B : ℝ, 0 < B ∧ ∀ K : ℕ, ∑ m ∈ Ioc 0 K, F (2 ^ m - 1) ≤ B * K := by
  obtain ⟨A, hA, hF⟩ := F_bound
  refine ⟨6 * A, by positivity, ?_⟩
  intro K
  set U := oddPF (PP K)
  have hU : ∀ T ∈ U.powerset, ∀ p ∈ T, p.Prime ∧ 2 < p := fun T hT p hp =>
    mem_oddPF (mem_powerset.mp hT hp)
  have hsubU : ∀ m ∈ Ioc 0 K, oddPF (2 ^ m - 1) ⊆ U := by
    intro m hm p hp
    unfold oddPF at hp
    show p ∈ (PP K).primeFactors.filter (fun p => 2 < p)
    rw [mem_filter] at hp ⊢
    refine ⟨Nat.primeFactors_mono (Finset.dvd_prod_of_mem _ hm) (PP_pos K).ne' hp.1, hp.2⟩
  have step1 : ∑ m ∈ Ioc 0 K, F (2 ^ m - 1) =
      ∑ T ∈ U.powerset, w T * (((Ioc 0 K).filter (fun m => T ⊆ oddPF (2 ^ m - 1))).card : ℝ) := by
    have : ∀ m ∈ Ioc 0 K, F (2 ^ m - 1) =
        ∑ T ∈ U.powerset, if T ⊆ oddPF (2 ^ m - 1) then w T else 0 := by
      intro m hm
      rw [F_eq_sum, ← Finset.sum_filter]
      congr 1
      ext T
      simp only [mem_powerset, mem_filter]
      exact ⟨fun h => ⟨h.trans (hsubU m hm), h⟩, fun h => h.2⟩
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro T _
    rw [← Finset.sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  have step2 : ∀ T ∈ U.powerset,
      w T * (((Ioc 0 K).filter (fun m => T ⊆ oddPF (2 ^ m - 1))).card : ℝ) ≤
      K * ∑ j ∈ range (K + 1), (1 / 2 : ℝ) ^ j * (if ordT T < 2 ^ (j + 1) then w T else 0) := by
    intro T hT
    have hc : (((Ioc 0 K).filter (fun m => T ⊆ oddPF (2 ^ m - 1))).card : ℝ) ≤ ((K / ordT T : ℕ) : ℝ) :=
      by exact_mod_cast card_le K
    have hd := div_le_sum (ordT T) K (ordT_pos (hU T hT))
    calc w T * (((Ioc 0 K).filter (fun m => T ⊆ oddPF (2 ^ m - 1))).card : ℝ)
        ≤ w T * (K * ∑ j ∈ range (K + 1), (if ordT T < 2 ^ (j + 1) then (1 / 2 : ℝ) ^ j else 0)) :=
          mul_le_mul_of_nonneg_left (hc.trans hd) (w_nonneg T)
      _ = _ := by
          rw [mul_sum, mul_sum, mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          split_ifs <;> ring
  have step3 : ∀ j ∈ range (K + 1),
      ∑ T ∈ U.powerset, (if ordT T < 2 ^ (j + 1) then w T else 0) ≤ A * ((j : ℝ) + 2) := by
    intro j _
    rw [← Finset.sum_filter]
    calc ∑ T ∈ U.powerset with ordT T < 2 ^ (j + 1), w T
        ≤ ∑ T ∈ (oddPF (PP (2 ^ (j + 1)))).powerset, w T := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro T hT
            have hT' := mem_filter.mp hT
            exact mem_powerset.mpr (subset_PP (hU T hT'.1) hT'.2.le)
          · intro T _ _; exact w_nonneg T
      _ = F (PP (2 ^ (j + 1))) := (F_eq_sum _).symm
      _ ≤ A * ((j + 1 : ℕ) + 1) := by
          apply hF _ _ (PP_pos _)
          refine (PP_le _).trans (le_of_eq ?_)
          rw [← pow_add, ← two_mul, pow_mul]; norm_num
      _ = A * ((j : ℝ) + 2) := by push_cast; ring
  rw [step1]
  calc ∑ T ∈ U.powerset, w T * (((Ioc 0 K).filter (fun m => T ⊆ oddPF (2 ^ m - 1))).card : ℝ)
      ≤ ∑ T ∈ U.powerset, K * ∑ j ∈ range (K + 1),
          (1 / 2 : ℝ) ^ j * (if ordT T < 2 ^ (j + 1) then w T else 0) := Finset.sum_le_sum step2
    _ = K * ∑ j ∈ range (K + 1), (1 / 2 : ℝ) ^ j *
          ∑ T ∈ U.powerset, (if ordT T < 2 ^ (j + 1) then w T else 0) := by
        rw [← mul_sum, Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        rw [mul_sum]
    _ ≤ K * ∑ j ∈ range (K + 1), (1 / 2 : ℝ) ^ j * (A * ((j : ℝ) + 2)) := by
        gcongr with j hj
        exact step3 j hj
    _ = K * (A * ∑ j ∈ range (K + 1), ((j : ℝ) + 2) * (1 / 2 : ℝ) ^ j) := by
        congr 1; rw [mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    _ ≤ K * (A * 6) := by
        gcongr
        rw [geom_sum]
        have : 0 ≤ (2 * ((K + 1 : ℕ) : ℝ) + 6) * (1 / 2 : ℝ) ^ (K + 1) := by positivity
        linarith
    _ = 6 * A * K := by ring

end RomA


open scoped Classical
open Finset

namespace RomB
open RomA

theorem cs_image {α β : Type*} [DecidableEq β] (s : Finset α) (g : α → β) :
    s.card ^ 2 ≤ (s.image g).card * ∑ a ∈ s, ∑ b ∈ s, (if g a = g b then 1 else 0) := by
  have h1 := Finset.card_eq_sum_card_image g s
  have h2 : ∑ a ∈ s, ∑ b ∈ s, (if g a = g b then 1 else 0) =
      ∑ v ∈ s.image g, (s.filter (fun a => g a = v)).card ^ 2 := by
    have : ∀ a ∈ s, ∑ b ∈ s, (if g a = g b then 1 else 0) = (s.filter (fun b => g b = g a)).card := by
      intro a _
      rw [Finset.card_filter]
      apply sum_congr rfl
      intro b _
      by_cases h : g a = g b
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (fun h' => h h'.symm)]
    rw [sum_congr rfl this]
    rw [← Finset.sum_fiberwise_of_maps_to (g := g) (t := s.image g) (fun a ha => mem_image_of_mem g ha)]
    apply sum_congr rfl
    intro v _
    rw [Finset.sum_const_nat (m := (s.filter (fun b => g b = v)).card)
      (fun a ha => by rw [(mem_filter.mp ha).2]), sq]
  rw [h2, h1]
  have := sq_sum_le_card_mul_sum_sq (s := s.image g) (f := fun v => (s.filter (fun a => g a = v)).card)
  simpa using this

noncomputable def P (y : ℕ) : Finset ℕ := Nat.primesLE y

noncomputable def G (y d : ℕ) : ℕ := ((range (y + 1)).filter (fun p => p.Prime ∧ (p + d).Prime)).card

theorem E_eq (y K : ℕ) :
    ∑ a ∈ P y ×ˢ Ioc 0 K, ∑ b ∈ P y ×ˢ Ioc 0 K,
      (if a.1 + 2 ^ a.2 = b.1 + 2 ^ b.2 then 1 else 0) =
    ∑ k ∈ Ioc 0 K, ∑ l ∈ Ioc 0 K, ∑ p ∈ P y, ∑ q ∈ P y,
      (if p + 2 ^ k = q + 2 ^ l then 1 else 0) := by
  simp only [sum_product]
  rw [sum_comm]
  apply sum_congr rfl
  intro k _
  exact (sum_congr rfl fun p _ => sum_comm).trans sum_comm

theorem cnt_diag (y k : ℕ) :
    ∑ p ∈ P y, ∑ q ∈ P y, (if p + 2 ^ k = q + 2 ^ k then 1 else 0) = (P y).card := by
  simp only [add_left_inj]
  simp [Finset.sum_ite_eq]

theorem shift_le (y d : ℕ) : ∑ q ∈ P y, (if q + d ∈ P y then 1 else 0) ≤ G y d := by
  rw [← Finset.card_filter]
  unfold G
  apply card_le_card
  intro q hq
  simp only [mem_filter, P, Nat.mem_primesLE, mem_range] at hq ⊢
  exact ⟨by omega, hq.1.2, hq.2.2⟩

theorem cnt_lt (y k l : ℕ) (hkl : k < l) :
    ∑ p ∈ P y, ∑ q ∈ P y, (if p + 2 ^ k = q + 2 ^ l then 1 else 0) ≤ G y (2 ^ l - 2 ^ k) := by
  have hle : 2 ^ k ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) hkl.le
  have : ∀ p q : ℕ, (p + 2 ^ k = q + 2 ^ l) ↔ p = q + (2 ^ l - 2 ^ k) := fun p q => by omega
  simp only [this]
  rw [sum_comm]
  simp only [Finset.sum_ite_eq']
  exact shift_le y _

theorem cnt_gt (y k l : ℕ) (hlk : l < k) :
    ∑ p ∈ P y, ∑ q ∈ P y, (if p + 2 ^ k = q + 2 ^ l then 1 else 0) ≤ G y (2 ^ k - 2 ^ l) := by
  have hle : 2 ^ l ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hlk.le
  have : ∀ p q : ℕ, (p + 2 ^ k = q + 2 ^ l) ↔ q = p + (2 ^ k - 2 ^ l) := fun p q => by omega
  simp only [this]
  simp only [Finset.sum_ite_eq']
  exact shift_le y _

theorem F_two_pow_mul (k n : ℕ) : F (2 ^ k * n) = F n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  unfold F OMALib.Sieve.pairSingularProduct
  congr 1
  ext p
  simp only [mem_filter, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨hp, hd, _⟩, h2⟩
    refine ⟨⟨hp, ?_, hn.ne'⟩, h2⟩
    have hcop : Nat.Coprime p (2 ^ k) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega))
    exact hcop.dvd_of_dvd_mul_left hd
  · rintro ⟨⟨hp, hd, _⟩, h2⟩
    exact ⟨⟨hp, dvd_mul_of_dvd_right hd _, by positivity⟩, h2⟩

theorem diff_eq (k l : ℕ) (hkl : k ≤ l) : 2 ^ l - 2 ^ k = 2 ^ k * (2 ^ (l - k) - 1) := by
  rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' hkl]

theorem diff_pos_even (k l : ℕ) (hk : 0 < k) (hkl : k < l) :
    0 < 2 ^ l - 2 ^ k ∧ Even (2 ^ l - 2 ^ k) := by
  have : 2 ^ k < 2 ^ l := Nat.pow_lt_pow_right (by norm_num) hkl
  refine ⟨by omega, ?_⟩
  rw [diff_eq k l hkl.le]
  exact (Nat.even_pow.mpr ⟨even_two, hk.ne'⟩).mul_right _

theorem sum_sub_le (H : ℕ → ℝ) (hH : ∀ m, 0 ≤ H m) (k K : ℕ) :
    ∑ l ∈ Ioc 0 K, H (l - k) ≤ K * H 0 + ∑ m ∈ range (K + 1), H m := by
  rw [← sum_filter_add_sum_filter_not (Ioc 0 K) (fun l => k ≤ l)]
  have h1 : ∑ l ∈ (Ioc 0 K).filter (fun l => k ≤ l), H (l - k) ≤ ∑ m ∈ range (K + 1), H m := by
    rw [← sum_image (g := fun l => l - k) (fun a ha b hb hab => by
      simp only [coe_filter, Set.mem_ofPred_eq, mem_Ioc] at ha hb
      simp only at hab; omega)]
    apply sum_le_sum_of_subset_of_nonneg
    · intro m hm; simp only [mem_image, mem_filter, mem_Ioc] at hm; simp only [mem_range]; omega
    · intro m _ _; exact hH m
  have h2 : ∑ l ∈ (Ioc 0 K).filter (fun l => ¬ k ≤ l), H (l - k) ≤ K * H 0 := by
    calc _ = ∑ l ∈ (Ioc 0 K).filter (fun l => ¬ k ≤ l), H 0 :=
          sum_congr rfl (fun l hl => by simp only [mem_filter] at hl; congr 1; omega)
      _ ≤ _ := by
          rw [sum_const, nsmul_eq_mul]
          gcongr
          · exact hH 0
          · have := (card_filter_le (Ioc 0 K) (fun l => ¬ k ≤ l)); rw [Nat.card_Ioc] at this; exact_mod_cast this
  linarith

theorem sum_sub_le' (H : ℕ → ℝ) (hH : ∀ m, 0 ≤ H m) (k K : ℕ) (hk : k ≤ K) :
    ∑ l ∈ Ioc 0 K, H (k - l) ≤ K * H 0 + ∑ m ∈ range (K + 1), H m := by
  rw [← sum_filter_add_sum_filter_not (Ioc 0 K) (fun l => l ≤ k)]
  have h1 : ∑ l ∈ (Ioc 0 K).filter (fun l => l ≤ k), H (k - l) ≤ ∑ m ∈ range (K + 1), H m := by
    rw [← sum_image (g := fun l => k - l) (fun a ha b hb hab => by
      simp only [coe_filter, Set.mem_ofPred_eq, mem_Ioc] at ha hb
      simp only at hab; omega)]
    apply sum_le_sum_of_subset_of_nonneg
    · intro m hm; simp only [mem_image, mem_filter, mem_Ioc] at hm; simp only [mem_range]; omega
    · intro m _ _; exact hH m
  have h2 : ∑ l ∈ (Ioc 0 K).filter (fun l => ¬ l ≤ k), H (k - l) ≤ K * H 0 := by
    calc _ = ∑ l ∈ (Ioc 0 K).filter (fun l => ¬ l ≤ k), H 0 :=
          sum_congr rfl (fun l hl => by simp only [mem_filter] at hl; congr 1; omega)
      _ ≤ _ := by
          rw [sum_const, nsmul_eq_mul]
          gcongr
          · exact hH 0
          · have := (card_filter_le (Ioc 0 K) (fun l => ¬ l ≤ k)); rw [Nat.card_Ioc] at this; exact_mod_cast this
  linarith

theorem F_zero : F 0 = 1 := by simp [F, OMALib.Sieve.pairSingularProduct]

theorem range_sum (H : ℕ → ℝ) (K : ℕ) :
    ∑ m ∈ range (K + 1), H m = H 0 + ∑ m ∈ Ioc 0 K, H m := by
  have : range (K + 1) = insert 0 (Ioc 0 K) := by ext m; simp only [mem_range, mem_insert, mem_Ioc]; omega
  rw [this, sum_insert (by simp)]

/-- The collision count. -/
theorem E_bound : ∃ D : ℝ, 0 < D ∧ ∀ y K : ℕ, 2 ≤ y → 1 ≤ K →
    ((∑ a ∈ P y ×ˢ Ioc 0 K, ∑ b ∈ P y ×ˢ Ioc 0 K,
      (if a.1 + 2 ^ a.2 = b.1 + 2 ^ b.2 then 1 else 0) : ℕ) : ℝ) ≤
      K * (P y).card + D * ((y : ℝ) / Real.log y ^ 2) * K ^ 2 := by
  obtain ⟨C, hC, hpair⟩ := OMALib.Sieve.prime_pairs_upper_bound'
  obtain ⟨B, hB, hS⟩ := S_bound
  refine ⟨C * (2 * (2 + B)), by positivity, ?_⟩
  intro y K hy hK
  set C' := C * ((y : ℝ) / Real.log y ^ 2) with hC'
  have hC'0 : 0 ≤ C' := by positivity
  set H : ℕ → ℝ := fun m => F (2 ^ m - 1) with hHdef
  have hH : ∀ m, 0 ≤ H m := fun m => F_nonneg _
  have hH0 : H 0 = 1 := by simp [hHdef, F_zero]
  have hcnt : ∀ k ∈ Ioc 0 K, ∀ l ∈ Ioc 0 K,
      ((∑ p ∈ P y, ∑ q ∈ P y, (if p + 2 ^ k = q + 2 ^ l then 1 else 0) : ℕ) : ℝ) ≤
        (if k = l then ((P y).card : ℝ) else 0) + C' * (H (l - k) + H (k - l)) := by
    intro k hk l hl
    have hk0 : 0 < k := (mem_Ioc.mp hk).1
    have hl0 : 0 < l := (mem_Ioc.mp hl).1
    have hsum0 : 0 ≤ C' * (H (l - k) + H (k - l)) := mul_nonneg hC'0 (add_nonneg (hH _) (hH _))
    rcases lt_trichotomy k l with hkl | rfl | hlk
    · rw [if_neg hkl.ne]
      have h1 := cnt_lt y k l hkl
      obtain ⟨hd0, hde⟩ := diff_pos_even k l hk0 hkl
      have h2 := hpair _ hd0 hde y hy
      have h3 : F (2 ^ l - 2 ^ k) = H (l - k) := by
        rw [diff_eq k l hkl.le, F_two_pow_mul]
      unfold F at h3
      have hG : ((G y (2 ^ l - 2 ^ k) : ℕ) : ℝ) ≤ C' * H (l - k) := by
        rw [← h3]; unfold G; exact h2
      have : ((∑ p ∈ P y, ∑ q ∈ P y, (if p + 2 ^ k = q + 2 ^ l then 1 else 0) : ℕ) : ℝ) ≤
          (G y (2 ^ l - 2 ^ k) : ℝ) := by exact_mod_cast h1
      have := mul_nonneg hC'0 (hH (k - l))
      nlinarith
    · rw [if_pos rfl, cnt_diag]
      linarith
    · rw [if_neg hlk.ne']
      have h1 := cnt_gt y k l hlk
      obtain ⟨hd0, hde⟩ := diff_pos_even l k hl0 hlk
      have h2 := hpair _ hd0 hde y hy
      have h3 : F (2 ^ k - 2 ^ l) = H (k - l) := by
        rw [diff_eq l k hlk.le, F_two_pow_mul]
      unfold F at h3
      have hG : ((G y (2 ^ k - 2 ^ l) : ℕ) : ℝ) ≤ C' * H (k - l) := by
        rw [← h3]; unfold G; exact h2
      have : ((∑ p ∈ P y, ∑ q ∈ P y, (if p + 2 ^ k = q + 2 ^ l then 1 else 0) : ℕ) : ℝ) ≤
          (G y (2 ^ k - 2 ^ l) : ℝ) := by exact_mod_cast h1
      have := mul_nonneg hC'0 (hH (l - k))
      nlinarith
  have hrow : ∀ k ∈ Ioc 0 K, ∑ l ∈ Ioc 0 K, (H (l - k) + H (k - l)) ≤ 2 * (2 + B) * K := by
    intro k hk
    have hkK : k ≤ K := (mem_Ioc.mp hk).2
    rw [sum_add_distrib]
    have h1 := sum_sub_le H hH k K
    have h2 := sum_sub_le' H hH k K hkK
    have h3 := range_sum H K
    have h4 := hS K
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
    rw [hH0] at h1 h2 h3
    nlinarith
  rw [E_eq]
  push_cast
  calc _ ≤ ∑ k ∈ Ioc 0 K, ∑ l ∈ Ioc 0 K,
          ((if k = l then ((P y).card : ℝ) else 0) + C' * (H (l - k) + H (k - l))) := by
        apply sum_le_sum; intro k hk; apply sum_le_sum; intro l hl
        have := hcnt k hk l hl
        push_cast at this
        exact this
    _ = ∑ k ∈ Ioc 0 K, ((P y).card : ℝ) + C' * ∑ k ∈ Ioc 0 K, ∑ l ∈ Ioc 0 K, (H (l - k) + H (k - l)) := by
        rw [mul_sum, ← sum_add_distrib]
        apply sum_congr rfl; intro k hk
        rw [sum_add_distrib, Finset.sum_ite_eq, if_pos hk, mul_sum]
    _ ≤ ∑ k ∈ Ioc 0 K, ((P y).card : ℝ) + C' * ∑ k ∈ Ioc 0 K, (2 * (2 + B) * K) := by
        gcongr with k hk
        exact hrow k hk
    _ = K * (P y).card + C * (2 * (2 + B)) * ((y : ℝ) / Real.log y ^ 2) * K ^ 2 := by
        simp only [sum_const, Nat.card_Ioc, nsmul_eq_mul, hC', Nat.sub_zero]
        ring

end RomB


open scoped Classical
open Finset


namespace RomC
open RomA RomB

theorem pi_lower : ∃ y0 : ℕ, ∀ y : ℕ, y0 ≤ y → (y : ℝ) / 3 ≤ (P y).card * Real.log y := by
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp
    (Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < 1 / 4 by norm_num))
  refine ⟨max ⌈a⌉₊ 3, fun y hy => ?_⟩
  have hy3 : (3 : ℝ) ≤ y := by exact_mod_cast (le_max_right _ _).trans hy
  have hya : a ≤ (y : ℝ) + 1 := by
    have : (⌈a⌉₊ : ℝ) ≤ y := by exact_mod_cast (le_max_left _ _).trans hy
    linarith [Nat.le_ceil a]
  have h1 := ha _ hya
  simp only [Real.norm_eq_abs, id] at h1
  have h1' : Real.log ((y : ℝ) + 1) ≤ 1 / 4 * ((y : ℝ) + 1) := by
    have := le_abs_self (Real.log ((y : ℝ) + 1))
    rw [abs_of_pos (by linarith : (0 : ℝ) < y + 1)] at h1
    linarith
  have h2 := Chebyshev.psi_le_primeCounting_mul_log y
  have h3 := Chebyshev.psi_ge y
  have h4 := Real.log_two_gt_d9
  rw [P, Nat.primesLE_card_eq_primeCounting]
  nlinarith

theorem K_bound (y : ℕ) (hy : 4 ≤ y) :
    Real.log y ≤ 2 * Real.log 2 * (Nat.log 2 y : ℝ) ∧ 2 ≤ Nat.log 2 y := by
  have hK2 : 2 ≤ Nat.log 2 y := Nat.le_log_of_pow_le (by norm_num) (by omega)
  refine ⟨?_, hK2⟩
  have hlt : (y : ℝ) < 2 ^ (Nat.log 2 y + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) y
  have hl := Real.log_lt_log (by positivity) hlt
  rw [Real.log_pow] at hl
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK2' : (2 : ℝ) ≤ Nat.log 2 y := by exact_mod_cast hK2
  push_cast at hl
  nlinarith

theorem main_count : ∃ c : ℝ, 0 < c ∧ ∃ y0 : ℕ, ∀ y : ℕ, y0 ≤ y →
    c * y ≤ ((P y ×ˢ Ioc 0 (Nat.log 2 y)).image (fun a => a.1 + 2 ^ a.2)).card := by
  obtain ⟨D, hD, hE⟩ := E_bound
  obtain ⟨y0, hy0⟩ := pi_lower
  refine ⟨min (1 / 12) (1 / (18 * D)), by positivity, max y0 4, fun y hy => ?_⟩
  have hy4 : 4 ≤ y := (le_max_right _ _).trans hy
  have hπ := hy0 y ((le_max_left _ _).trans hy)
  obtain ⟨hK, hK2⟩ := K_bound y hy4
  have hcs := cs_image (P y ×ˢ Ioc 0 (Nat.log 2 y)) (fun a => a.1 + 2 ^ a.2)
  have hE' := hE y (Nat.log 2 y) (by omega) (by omega)
  set K := Nat.log 2 y with hKdef
  set m := ((P y ×ˢ Ioc 0 K).image (fun a => a.1 + 2 ^ a.2)).card with hm
  set E := ∑ a ∈ P y ×ˢ Ioc 0 K, ∑ b ∈ P y ×ˢ Ioc 0 K,
      (if a.1 + 2 ^ a.2 = b.1 + 2 ^ b.2 then 1 else 0) with hEdef
  have hT : (P y ×ˢ Ioc 0 K).card = (P y).card * K := by
    rw [card_product, Nat.card_Ioc, Nat.sub_zero]
  rw [hT] at hcs
  have hyR : (4 : ℝ) ≤ y := by exact_mod_cast hy4
  have hℓ : 0 < Real.log y := Real.log_pos (by linarith)
  set ℓ := Real.log y with hℓdef
  set p : ℝ := ((P y).card : ℝ) with hpdef
  have hp0 : 0 ≤ p := by positivity
  have hKR : (2 : ℝ) ≤ K := by exact_mod_cast hK2
  set t : ℝ := p * K with htdef
  have hcsR : t ^ 2 ≤ m * (E : ℝ) := by
    have : (((P y).card * K : ℕ) : ℝ) ^ 2 ≤ ((m * E : ℕ) : ℝ) := by exact_mod_cast hcs
    push_cast at this
    simpa [htdef, hpdef] using this
  set Q : ℝ := D * ((y : ℝ) / ℓ ^ 2) * K ^ 2 with hQdef
  have hE2 : (E : ℝ) ≤ t + Q := by
    have := hE'
    rw [htdef, hQdef]; linarith
  have hlog2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpl : (y : ℝ) / 3 ≤ p * ℓ := hπ
  have htl : p * ℓ ≤ t * (2 * Real.log 2) := by
    rw [htdef]; nlinarith
  have ht6 : (y : ℝ) / 6 ≤ t := by nlinarith
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hy0' : (0 : ℝ) < y := by linarith
  rcases le_or_gt Q t with hQt | hQt
  · -- E ≤ 2t
    have h1 : t ^ 2 ≤ m * (2 * t) := hcsR.trans (by nlinarith)
    have htpos : 0 < t := by linarith
    have h2 : t ≤ 2 * m := by nlinarith
    have : (1 / 12 : ℝ) * y ≤ m := by linarith
    calc min (1 / 12) (1 / (18 * D)) * (y : ℝ) ≤ 1 / 12 * y := by
          gcongr; exact min_le_left _ _
      _ ≤ m := this
  · have h1 : t ^ 2 ≤ m * (2 * Q) := hcsR.trans (by nlinarith)
    have hQl : Q * ℓ ^ 2 = D * y * K ^ 2 := by rw [hQdef]; field_simp
    have h2 : t ^ 2 * ℓ ^ 2 ≤ 2 * m * D * y * K ^ 2 := by
      have := mul_le_mul_of_nonneg_right h1 (sq_nonneg ℓ)
      calc t ^ 2 * ℓ ^ 2 ≤ m * (2 * Q) * ℓ ^ 2 := this
        _ = 2 * m * (Q * ℓ ^ 2) := by ring
        _ = 2 * m * D * y * K ^ 2 := by rw [hQl]; ring
    have h3 : t ^ 2 * ℓ ^ 2 = K ^ 2 * (p * ℓ) ^ 2 := by rw [htdef]; ring
    have h4 : ((y : ℝ) / 3) ^ 2 ≤ (p * ℓ) ^ 2 := by
      have : 0 ≤ (y : ℝ) / 3 := by positivity
      exact pow_le_pow_left₀ this hpl 2
    have hK0 : 0 < (K : ℝ) ^ 2 := by positivity
    have h5 : ((y : ℝ) / 3) ^ 2 ≤ 2 * m * D * y := by
      have : (K : ℝ) ^ 2 * ((y : ℝ) / 3) ^ 2 ≤ (K : ℝ) ^ 2 * (2 * m * D * y) := by
        calc (K : ℝ) ^ 2 * ((y : ℝ) / 3) ^ 2 ≤ (K : ℝ) ^ 2 * (p * ℓ) ^ 2 :=
              mul_le_mul_of_nonneg_left h4 hK0.le
          _ = t ^ 2 * ℓ ^ 2 := h3.symm
          _ ≤ 2 * m * D * y * K ^ 2 := h2
          _ = _ := by ring
      exact le_of_mul_le_mul_left this hK0
    have h6 : (y : ℝ) / 9 ≤ 2 * m * D := by
      have : (y : ℝ) * ((y : ℝ) / 9) ≤ (y : ℝ) * (2 * m * D) := by
        calc (y : ℝ) * ((y : ℝ) / 9) = ((y : ℝ) / 3) ^ 2 := by ring
          _ ≤ 2 * m * D * y := h5
          _ = _ := by ring
      exact le_of_mul_le_mul_left this hy0'
    have h7 : 1 / (18 * D) * (y : ℝ) ≤ m := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
      nlinarith
    calc min (1 / 12) (1 / (18 * D)) * (y : ℝ) ≤ 1 / (18 * D) * y := by
          gcongr; exact min_le_right _ _
      _ ≤ m := h7

end RomC


open scoped Classical
open Finset



namespace RomD
open RomA RomB RomC

/-- Chebyshev's upper bound in the form `π(x) log x ≤ 7 x`. -/
theorem pi_upper (x : ℕ) (hx : 2 ≤ x) : ((P x).card : ℝ) * Real.log x ≤ 7 * x := by
  have hxR : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hper : ∀ p ∈ P x, Real.log x ≤
      2 * Real.log p + (if p * p ≤ x then Real.log x else 0) := by
    intro p hp
    have hp' := Nat.mem_primesLE.mp hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp'.2.one_lt.le
    have hlp : 0 ≤ Real.log p := Real.log_nonneg hp1
    split_ifs with h
    · linarith
    · have hlt : (x : ℝ) < (p : ℝ) ^ 2 := by
        have : x < p * p := by omega
        rw [sq]; exact_mod_cast this
      have := Real.log_lt_log (by linarith) hlt
      rw [Real.log_pow] at this
      push_cast at this
      linarith
  have hsum := Finset.sum_le_sum hper
  rw [sum_const, nsmul_eq_mul, sum_add_distrib, ← mul_sum, ← sum_filter, sum_const,
    nsmul_eq_mul] at hsum
  have hθ : ∑ p ∈ P x, Real.log p ≤ Real.log 4 * x := by
    rw [P, ← Chebyshev.theta_eq_sum_primesLE_log]
    exact Chebyshev.theta_le_log4_mul_x (by positivity)
  set s := Nat.sqrt x with hs
  have hcard : ((P x).filter (fun p => p * p ≤ x)).card ≤ s + 1 := by
    calc ((P x).filter (fun p => p * p ≤ x)).card ≤ (range (s + 1)).card := by
          apply card_le_card
          intro p hp
          have := (mem_filter.mp hp).2
          simp only [mem_range]
          exact Nat.lt_succ_of_le (Nat.le_sqrt.mpr this)
      _ = s + 1 := card_range _
  have hs1 : 1 ≤ s := Nat.le_sqrt.mpr (by omega)
  have hss : s * s ≤ x := Nat.sqrt_le x
  have hlt : x < (s + 1) * (s + 1) := Nat.lt_succ_sqrt x
  have hlogx : Real.log x ≤ 2 * s := by
    have h1 : (x : ℝ) < ((s : ℝ) + 1) ^ 2 := by rw [sq]; exact_mod_cast hlt
    have h2 := Real.log_lt_log (by linarith) h1
    rw [Real.log_pow] at h2
    have h3 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (s : ℝ) + 1 by positivity)
    push_cast at h2
    linarith
  have hcardR : (((P x).filter (fun p => p * p ≤ x)).card : ℝ) ≤ s + 1 := by exact_mod_cast hcard
  have hs1R : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hssR : (s : ℝ) * s ≤ x := by exact_mod_cast hss
  have hlog4 : Real.log 4 < 3 / 2 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith [Real.log_two_lt_d9]
  have h5 : (((P x).filter (fun p => p * p ≤ x)).card : ℝ) * Real.log x ≤ 4 * x := by
    calc _ ≤ ((s : ℝ) + 1) * (2 * s) := mul_le_mul hcardR hlogx hlx.le (by positivity)
      _ ≤ 4 * (s * s) := by nlinarith
      _ ≤ 4 * x := by linarith
  have hx0 : (0 : ℝ) ≤ x := by positivity
  nlinarith

theorem sum_sq_fib {α β : Type*} [DecidableEq β] (s : Finset α) (g : α → β) :
    ∑ a ∈ s, ∑ b ∈ s, (if g a = g b then 1 else 0) =
      ∑ v ∈ s.image g, (s.filter (fun a => g a = v)).card ^ 2 := by
  have : ∀ a ∈ s, ∑ b ∈ s, (if g a = g b then 1 else 0) = (s.filter (fun b => g b = g a)).card := by
    intro a _
    rw [Finset.card_filter]
    apply sum_congr rfl
    intro b _
    by_cases h : g a = g b
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun h' => h h'.symm)]
  rw [sum_congr rfl this]
  rw [← Finset.sum_fiberwise_of_maps_to (g := g) (t := s.image g) (fun a ha => mem_image_of_mem g ha)]
  apply sum_congr rfl
  intro v _
  rw [Finset.sum_const_nat (m := (s.filter (fun b => g b = v)).card)
    (fun a ha => by rw [(mem_filter.mp ha).2]), sq]

/-- The representation function `r(n)` is at most the fibre size of `(p, k) ↦ p + 2^k`. -/
theorem r_le_fib (x n : ℕ) (hn : n ≤ x) :
    ((range n).filter (fun k => 1 ≤ k ∧ 2 ^ k < n ∧ (n - 2 ^ k).Prime ∧ n - 2 ^ k ≠ 2)).card ≤
      ((P x ×ˢ Ioc 0 (Nat.log 2 x)).filter (fun a => a.1 + 2 ^ a.2 = n)).card := by
  apply card_le_card_of_injOn (fun k => (n - 2 ^ k, k))
  · intro k hk
    simp only [coe_filter, Set.mem_ofPred_eq, mem_range] at hk
    simp only [coe_filter, Set.mem_ofPred_eq, mem_product, P, Nat.mem_primesLE, mem_Ioc]
    refine ⟨⟨⟨(Nat.sub_le _ _).trans hn, hk.2.2.2.1⟩, by omega,
      Nat.le_log_of_pow_le (by norm_num) ((hk.2.2.1.le).trans hn)⟩, Nat.sub_add_cancel hk.2.2.1.le⟩
  · intro a _ b _ hab
    simp only [Prod.mk.injEq] at hab
    exact hab.2

theorem H2_proof : OMA.R_Erdos16_erdos_16_variant_romanoff_R1.H2 := by
  obtain ⟨D, hD, hE⟩ := E_bound
  refine ⟨7 / Real.log 2 + D / Real.log 2 ^ 2, fun x hx => ?_⟩
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hxR : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  set K := Nat.log 2 x with hK
  have hK1 : 1 ≤ K := Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hKlog : (K : ℝ) * Real.log 2 ≤ Real.log x := by
    have h1 : ((2 : ℝ) ^ K) ≤ x := by exact_mod_cast Nat.pow_log_le_self 2 (by omega : x ≠ 0)
    have := Real.log_le_log (by positivity) h1
    rwa [Real.log_pow] at this
  set T := P x ×ˢ Ioc 0 K
  set g : ℕ × ℕ → ℕ := fun a => a.1 + 2 ^ a.2
  have hE' := hE x K hx hK1
  rw [sum_sq_fib T g] at hE'
  -- Σ r² ≤ Σ fib²
  have hstep : ∑ n ∈ Finset.range (x + 1),
      (((Finset.range n).filter (fun k => 1 ≤ k ∧ 2 ^ k < n ∧ (n - 2 ^ k).Prime ∧
        n - 2 ^ k ≠ 2)).card : ℝ) ^ 2 ≤
      ((∑ v ∈ T.image g, (T.filter (fun a => g a = v)).card ^ 2 : ℕ) : ℝ) := by
    push_cast
    calc _ ≤ ∑ n ∈ Finset.range (x + 1), ((T.filter (fun a => g a = n)).card : ℝ) ^ 2 := by
          apply sum_le_sum
          intro n hn
          have := r_le_fib x n (by simp at hn; omega)
          gcongr
      _ = ∑ n ∈ (Finset.range (x + 1)).filter (fun n => n ∈ T.image g),
            ((T.filter (fun a => g a = n)).card : ℝ) ^ 2 := by
          symm
          apply Finset.sum_filter_of_ne
          intro n _ hne
          by_contra hn
          apply hne
          have : T.filter (fun a => g a = n) = ∅ := by
            apply filter_eq_empty_iff.mpr
            intro a ha hga
            exact hn (mem_image.mpr ⟨a, ha, hga⟩)
          rw [this]; simp
      _ ≤ ∑ v ∈ T.image g, ((T.filter (fun a => g a = v)).card : ℝ) ^ 2 := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro n hn; exact (mem_filter.mp hn).2
          · intro _ _ _; positivity
  refine hstep.trans (hE'.trans ?_)
  have hpi := pi_upper x hx
  have hP0 : (0 : ℝ) ≤ (P x).card := by positivity
  have h1 : (K : ℝ) * (P x).card ≤ 7 / Real.log 2 * x := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
    calc (K : ℝ) * (P x).card * Real.log 2 = (P x).card * (K * Real.log 2) := by ring
      _ ≤ (P x).card * Real.log x := mul_le_mul_of_nonneg_left hKlog hP0
      _ ≤ 7 * x := hpi
  have h2 : D * ((x : ℝ) / Real.log x ^ 2) * K ^ 2 ≤ D / Real.log 2 ^ 2 * x := by
    have hK0 : (0 : ℝ) ≤ K := by positivity
    have hsq : ((K : ℝ) * Real.log 2) ^ 2 ≤ Real.log x ^ 2 := pow_le_pow_left₀ (by positivity) hKlog 2
    have hlx2 : 0 < Real.log x ^ 2 := by positivity
    have hl22 : 0 < Real.log 2 ^ 2 := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hl22]
    calc D * ((x : ℝ) / Real.log x ^ 2) * K ^ 2 * Real.log 2 ^ 2
        = D * x * (((K : ℝ) * Real.log 2) ^ 2 / Real.log x ^ 2) := by ring
      _ ≤ D * x * 1 := by
          gcongr
          rw [div_le_one hlx2]; exact hsq
      _ = D * x := by ring
  linarith

theorem H1_proof : OMA.R_Erdos16_erdos_16_variant_romanoff_R1.H1 := by
  obtain ⟨y0, hy0⟩ := pi_lower
  refine ⟨1 / 48, by norm_num, 2 * y0 + 8, fun x hx => ?_⟩
  set y := x / 2 with hy
  have hyy0 : y0 ≤ y := by omega
  have hy4 : 4 ≤ y := by omega
  obtain ⟨hK, hK2⟩ := K_bound y hy4
  have hπ := hy0 y hyy0
  set K := Nat.log 2 y with hKdef
  set T := ((P y).erase 2) ×ˢ Ioc 0 K
  set g : ℕ × ℕ → ℕ := fun a => a.1 + 2 ^ a.2
  have hmaps : ∀ a ∈ T, g a ∈ range (x + 1) := by
    intro a ha
    simp only [T, mem_product, mem_erase, P, Nat.mem_primesLE, mem_Ioc] at ha
    have : 2 ^ a.2 ≤ y := (Nat.pow_le_pow_right two_pos ha.2.2).trans
      (Nat.pow_log_le_self 2 (by omega))
    simp only [g, mem_range]
    omega
  have hcardT : T.card = ∑ n ∈ range (x + 1), (T.filter (fun a => g a = n)).card :=
    (Finset.card_eq_sum_card_fiberwise hmaps)
  have hfib : ∀ n ∈ range (x + 1), (T.filter (fun a => g a = n)).card ≤
      ((range n).filter (fun k => 1 ≤ k ∧ 2 ^ k < n ∧ (n - 2 ^ k).Prime ∧ n - 2 ^ k ≠ 2)).card := by
    intro n _
    apply card_le_card_of_injOn (fun a => a.2)
    · intro a ha
      simp only [coe_filter, Set.mem_ofPred_eq, T, mem_product, mem_erase, P, Nat.mem_primesLE,
        mem_Ioc, g] at ha
      obtain ⟨⟨⟨hp2, hpy, hpr⟩, hk0, hkK⟩, hgn⟩ := ha
      have hlt : a.2 < 2 ^ a.2 := Nat.lt_two_pow_self
      have h2 := hpr.two_le
      simp only [coe_filter, Set.mem_ofPred_eq, mem_range]
      have he : n - 2 ^ a.2 = a.1 := by omega
      refine ⟨by omega, hk0, by omega, ?_, ?_⟩
      · rw [he]; exact hpr
      · rw [he]; exact hp2
    · intro a ha b hb hab
      simp only [coe_filter, Set.mem_ofPred_eq, g] at ha hb
      simp only at hab
      have : a.1 = b.1 := by
        have h1 := ha.2; have h2 := hb.2; rw [hab] at h1; omega
      exact Prod.ext this hab
  have hsum : (T.card : ℝ) ≤ ∑ n ∈ Finset.range (x + 1),
      (((Finset.range n).filter (fun k => 1 ≤ k ∧ 2 ^ k < n ∧ (n - 2 ^ k).Prime ∧
        n - 2 ^ k ≠ 2)).card : ℝ) := by
    rw [hcardT]; push_cast
    exact sum_le_sum fun n hn => by exact_mod_cast hfib n hn
  refine le_trans ?_ hsum
  -- lower bound on |T|
  have h23 : ({2, 3} : Finset ℕ) ⊆ P y := by
    intro p hp
    simp only [mem_insert, mem_singleton] at hp
    simp only [P, Nat.mem_primesLE]
    rcases hp with rfl | rfl
    · exact ⟨by omega, Nat.prime_two⟩
    · exact ⟨by omega, Nat.prime_three⟩
  have hP2 : 2 ≤ (P y).card := by
    have := card_le_card h23; simpa using this
  have hTc : T.card = ((P y).card - 1) * K := by
    rw [card_product, card_erase_of_mem (h23 (mem_insert_self 2 _)), Nat.card_Ioc, Nat.sub_zero]
  have hPR : (2 : ℝ) ≤ (P y).card := by exact_mod_cast hP2
  have hTR : (T.card : ℝ) = ((P y).card - 1) * K := by
    rw [hTc]; push_cast [Nat.cast_sub (by omega : 1 ≤ (P y).card)]; ring
  rw [hTR]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hK0 : (0 : ℝ) ≤ K := by positivity
  have hP0 : (0 : ℝ) ≤ (P y).card := by positivity
  have h1 : (y : ℝ) / 3 ≤ (P y).card * (2 * Real.log 2 * K) :=
    hπ.trans (mul_le_mul_of_nonneg_left hK hP0)
  have h2 : (y : ℝ) / 6 ≤ (P y).card * K := by nlinarith
  have hyx : (x : ℝ) ≤ 4 * y := by
    have : x ≤ 4 * y := by omega
    exact_mod_cast this
  nlinarith

end RomD

end RomanoffProof

theorem OMA.solution : type_of% @Erdos16.erdos_16.variant.romanoff :=
  OMA.R_Erdos16_erdos_16_variant_romanoff_R1.main RomD.H1_proof RomD.H2_proof
