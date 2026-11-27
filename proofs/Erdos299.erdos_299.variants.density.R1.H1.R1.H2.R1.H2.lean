import OMAReductions.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1
import Mathlib

/-!
# The first forcing alternative for dense sets of denominators

This follows Proposition 6.3 of the Bloom formalization by Bhavik Mehta and
Thomas Bloom, b-mehta/unit-fractions, src/main_results.lean and
src/aux_lemmas.lean at commit 10ef71a300cf29e5f19beb2bbc723a035a0678de,
including contributions by Eric Rodriguez. Copyright (c) 2021 Bhavik Mehta,
Thomas Bloom. Used under Apache-2.0.

The common-divisor argument and Euler bound for the cofactor prime-power
mass use @marcusbuffett's Erdős 299 proofs. Their Mertens input was developed
in the merged Erdős 377 proof, starting with @senamakel's Erdős 962 proof
at d757b84b7870c7b80a9e62d5e93a293328aee0d4. The elementary bound on the
number of distinct prime factors below is adapted from Will Howe,
H0W4RD-dev/croot-unit-fractions, Prop1.lean at
c58a7d45114c3af27e6abb19dcfca9d82b49b4a1, used under Apache-2.0.

Each prime power whose multiples carry sufficient mass has a heavy interval
point. Three such points would carry more prime-power mass than is available.
If two distinct points x and y occur, an exceptional denominator hitting h
divides the nonzero product (x-h)(y-h). A uniform divisor bound controls
these exceptions, so one of the two points captures a third of the mass.
-/
open Filter Finset Real
open scoped Classical Topology
namespace OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1_H3_R1
noncomputable abbrev w (N : ℕ) := log (log N)
noncomputable abbrev e (N : ℕ) := (log N)^(-(1/100:ℝ))
noncomputable abbrev M (N : ℕ) := (N:ℝ)^(1-1/w N)
noncomputable abbrev K (N : ℕ) := M N*(N:ℝ)^(-2/w N)
noncomputable abbrev L (N : ℕ) := M N/(2*(log N)^(1/100:ℝ))
noncomputable abbrev mass (A : Finset ℕ) := ∑ n ∈ A, (1:ℝ)/n
noncomputable def powers (A : Finset ℕ) := A.biUnion fun n =>
  n.divisors.filter fun q => IsPrimePow q ∧ Nat.Coprime q (n/q)
noncomputable def part (A : Finset ℕ) (q : ℕ) := A.filter fun n => q∣n ∧ Nat.Coprime q (n/q)
def Regular (N n : ℕ) : Prop := M N ≤ n ∧
  (∀ q : ℕ, IsPrimePow q → q∣n → (q:ℝ) ≤ (N:ℝ)^(1-8/w N)) ∧
  (99/100:ℝ)*w N ≤ n.primeFactors.card ∧ (n.primeFactors.card:ℝ) ≤ 2*w N

/-- Extract a common divisor larger than the interval from a local family.
The coprime cofactors carry enough reciprocal mass and retain most prime factors. -/
def H1 : Prop := ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℕ) (q : ℕ), 0∉A → A⊆range N →
  (∀ n ∈ A, Regular N n) → IsPrimePow q → e N/2 ≤ ∑ n ∈ part A q,(q:ℝ)/n →
  ∃ (D : ℕ) (C : Finset ℕ), K N < D ∧ q∣D ∧
    (log N)^(-(1/99:ℝ)) ≤ mass C ∧
    (∀ m ∈ C, D*m ∈ A ∧ Nat.Coprime m D ∧
      (1-2/99:ℝ)*w N ≤ m.primeFactors.card ∧ (m.primeFactors.card:ℝ) ≤ 2*w N)

/-- A family of cofactors of sufficient mass and with almost the normal
number of distinct prime factors has large prime-power reciprocal mass. -/
def H2 : Prop := ∀ᶠ N : ℕ in atTop, ∀ C : Finset ℕ,
  (log N)^(-(1/99:ℝ)) ≤ mass C →
  (∀ m ∈ C, (1-2/99:ℝ)*w N ≤ m.primeFactors.card ∧ (m.primeFactors.card:ℝ) ≤ 2*w N) →
  (35/100:ℝ)*w N ≤ mass (powers C)

lemma power_mem {A : Finset ℕ} {q : ℕ} (h : q ∈ powers A) :
    IsPrimePow q ∧ ∃ n ∈ A, n ≠ 0 ∧ q∣n ∧ Nat.Coprime q (n/q) := by
  obtain ⟨n,hn,hq⟩ := mem_biUnion.mp h
  obtain ⟨dv,pp,cp⟩ := mem_filter.mp hq
  obtain ⟨hd,h0⟩ := Nat.mem_divisors.mp dv
  exact ⟨pp,n,hn,h0,hd,cp⟩
end OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1_H3_R1
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


end OMALib.Mertens

open Filter Finset Real Asymptotics
open scoped Topology BigOperators
open OMALib.Mertens
namespace Mass377
noncomputable abbrev S (x : ℝ) := ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1:ℝ)/p
lemma Cpos : 0 ≤ mertens1Const := by
  exact (abs_nonneg _).trans (abs_sum_log_div_sub_log_le_nat 2)
lemma Gdiff (m n : ℕ) (hm : 2 ≤ m) (hn : m ≤ n) :
    |mertensG n - mertensG m| ≤ (mertens1Const+1)*(1/log m-1/log n) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    calc |mertensG (n+1)-mertensG m| =
        |(mertensG (n+1)-mertensG n)+(mertensG n-mertensG m)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add (mertensG_step n (hm.trans hn)) ih
      _ = _ := by ring
lemma logTop : Tendsto (fun n : ℕ => log n) atTop atTop :=
  tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
lemma natMertens : ∃ b : ℝ, Tendsto (fun n : ℕ => (∑ p ∈ Nat.primesLE n, (1:ℝ)/p) -
    log (log n)) atTop (𝓝 b) := by
  have hC : CauchySeq mertensG := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hlim : Tendsto (fun n : ℕ => (mertens1Const+1)/log n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop logTop
    obtain ⟨m,hm,he⟩ := ((eventually_ge_atTop 2).and (hlim.eventually_lt_const hε)).exists
    refine ⟨m,fun n hn => ?_⟩
    rw [Real.dist_eq]
    apply (Gdiff m n hm hn).trans_lt
    have hn' : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
    have hp : 0≤(mertens1Const+1)*(1/log n) := mul_nonneg (by linarith [Cpos]) (by positivity [log_pos hn'])
    rw [mul_sub,←div_eq_mul_one_div]
    linarith
  obtain ⟨b,hb⟩ := cauchySeq_tendsto_of_complete hC
  let R (n : ℕ) := ((∑ p ∈ Nat.primesLE n, log p / p)-log n)/log n
  have hR : Tendsto R atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
      (show Tendsto (fun n : ℕ => mertens1Const/log n) atTop (𝓝 0) from tendsto_const_nhds.div_atTop logTop)
    filter_upwards [logTop.eventually_gt_atTop 0] with n hn
    dsimp only [R]
    rw [Real.norm_eq_abs, abs_div,abs_of_pos hn]
    exact div_le_div_of_nonneg_right (abs_sum_log_div_sub_log_le_nat n) hn.le
  refine ⟨b,?_⟩
  simpa [R,mertensG] using hb.add hR
lemma realMertens : ∃ b : ℝ, Tendsto (fun x : ℝ => S x-log (log x)) atTop (𝓝 b) := by
  obtain ⟨b,hb⟩ := natMertens
  have he := (isEquivalent_nat_floor (R:=ℝ)).log tendsto_id
  have hz := tendsto_log_atTop.eventually_ne_atTop 0
  have ht := ((isEquivalent_iff_tendsto_one hz).1 he).log (by norm_num)
  have hfloor : Tendsto (fun x : ℝ => log (⌊x⌋₊:ℝ)) atTop atTop := logTop.comp tendsto_nat_floor_atTop
  have hdiff : Tendsto (fun x : ℝ => log (log (⌊x⌋₊:ℝ)) - log (log x)) atTop (𝓝 0) := by
    rw [Real.log_one] at ht
    apply ht.congr'
    filter_upwards [hz,hfloor.eventually_ne_atTop 0] with x hx hf
    exact log_div hf hx
  refine ⟨b,?_⟩
  have h := (hb.comp tendsto_nat_floor_atTop).add hdiff
  simpa [S,Function.comp_def,sub_add_sub_cancel] using h
end Mass377

open Filter Finset Real
open scoped Classical Topology
namespace Param299
noncomputable abbrev w (N : ℕ) := log (log N)
noncomputable abbrev e (N : ℕ) := (log N)^(-(1/100:ℝ))
noncomputable abbrev M (N : ℕ) := (N:ℝ)^(1-1/w N)
lemma wtop : Tendsto w atTop atTop := tendsto_log_atTop.comp Mass377.logTop
lemma geom (p : ℕ) (hp : 2≤p) (N : ℕ) :
    (∑ k ∈ range N, (1:ℝ)/(p:ℝ)^(k+1)) ≤ 2/(p:ℝ) := by
  have h : (∑ k ∈ range N, (1:ℝ)/(p:ℝ)^(k+1))+2/(p:ℝ)^(N+1) ≤ 2/(p:ℝ) := by
    induction N with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ]
      have hpos : 0<(p:ℝ) := by exact_mod_cast (show 0<p by omega)
      have htwo : (2:ℝ)≤p := by exact_mod_cast hp
      have hh : 2/(p:ℝ)^(n+1+1) ≤ 1/(p:ℝ)^(n+1) := by
        rw [pow_succ _ (n+1),div_mul_eq_div_div]
        apply (div_le_iff₀ hpos).mpr
        rw [div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_right (by linarith) (by positivity)
      calc _ ≤ ((∑ k ∈ range n, (1:ℝ)/(p:ℝ)^(k+1))+1/(p:ℝ)^(n+1))+1/(p:ℝ)^(n+1) := add_le_add le_rfl hh
           _ = (∑ k ∈ range n, (1:ℝ)/(p:ℝ)^(k+1))+2/(p:ℝ)^(n+1) := by ring
           _ ≤ _ := ih
  linarith [show 0≤2/(p:ℝ)^(N+1) by positivity]
end Param299

open Real Filter Finset
open scoped Classical Topology
namespace Rough299
noncomputable abbrev w (N:ℕ) := log (log (N:ℝ))
noncomputable abbrev X (N:ℕ) := exp (log N/(2*(w N)^2))
noncomputable abbrev G (N:ℕ) := (range N).filter fun q : ℕ => IsPrimePow q ∧ X N < q
noncomputable abbrev R (N:ℕ) := (range N).filter fun d => 0<d ∧
  ∀ p : ℕ, p∈d.primeFactors → X N < (p:ℝ)^d.factorization p
lemma nonsimple : ∃ C : ℝ, ∀ (N : ℕ) (Q : Finset ℕ),
    (∀ q ∈ Q, IsPrimePow q ∧ ¬q.Prime ∧ q≤N) → ∑ q∈Q,(1:ℝ)/q ≤ C := by
  let C := ∑' n : ℕ, ((n:ℝ)^2)⁻¹
  refine ⟨2*C,?_⟩
  intro N Q hQ
  let U := Nat.primesLE N ×ˢ range N
  let f (z : ℕ×ℕ) := z.1^(z.2+2)
  have sub : Q⊆U.image f := by
    intro q hq
    obtain ⟨pp,no,le⟩ := hQ q hq
    obtain ⟨p,lp,k,lk,pr,pk,e⟩ := (isPrimePow_nat_iff_bounded q).mp pp
    have g : k≠1 := by rintro rfl; simp_all
    exact mem_image.mpr ⟨(p,k-2),mem_product.mpr ⟨Nat.mem_primesLE.mpr ⟨lp.trans le,pr⟩,mem_range.mpr (by omega)⟩,
      by dsimp [f]; rwa [show k-2+2=k by omega]⟩
  calc _ ≤ ∑ q∈U.image f,(1:ℝ)/q := sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => by positivity)
       _ ≤ ∑ z∈U,(1:ℝ)/(f z) := sum_image_le_of_nonneg (fun _ _ => by positivity)
       _ = ∑ p∈Nat.primesLE N, ∑ k∈ range N, (1:ℝ)/(p:ℝ)^(k+2) := by simp [U,f,sum_product]
       _ ≤ ∑ p∈Nat.primesLE N, 2*((p:ℝ)^2)⁻¹ := by
         apply sum_le_sum
         intro p hp
         have g := Param299.geom p (Nat.mem_primesLE.mp hp).2.two_le N
         have pp : (0:ℝ)<p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos
         simp_rw [show ∀ k : ℕ, (1:ℝ)/(p:ℝ)^(k+2)=(1/(p:ℝ)^(k+1))/p by intro k; rw [pow_succ,div_div]]
         rw [←sum_div]
         calc _ ≤ ((2:ℝ)/p)/p := div_le_div_of_nonneg_right g pp.le
              _ = _ := by ring
       _ ≤ _ := by
         rw [←mul_sum]
         exact mul_le_mul_of_nonneg_left ((Real.summable_nat_pow_inv.mpr (by norm_num : 1<2)).sum_le_tsum _ (fun _ _ => by positivity)) (by norm_num)
lemma small_mass (c : ℝ) (hc : 0<c) :
    ∀ᶠ N : ℕ in atTop, ∑ q∈G N,(1:ℝ)/q ≤ c*w N := by
  have wt : Tendsto w atTop atTop := Param299.wtop
  have xt : Tendsto X atTop atTop := by
    have ht := (tendsto_exp_div_pow_atTop 2).comp wt
    have h2 := ht.atTop_div_const (by norm_num : (0:ℝ)<2)
    apply tendsto_exp_atTop.comp
    apply h2.congr'
    filter_upwards [Mass377.logTop.eventually_gt_atTop 0] with N hN
    simp only [Function.comp_apply,w,exp_log hN,div_div]
    ring
  obtain ⟨b,hb⟩ := Mass377.realMertens
  obtain ⟨C,cc⟩ := nonsimple
  have little := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp wt).eventually_lt_const (show 0<c/4 by positivity)
  filter_upwards [(hb.comp xt).eventually_const_lt (show b-1<b by linarith),
    (hb.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_lt_const (show b<b+1 by linarith),
    little, wt.eventually_gt_atTop 2, wt.eventually_gt_atTop (2*(2+log 2+C)/c),
    Mass377.logTop.eventually_gt_atTop 0,eventually_ge_atTop 2] with N lower upper small hw huge nlog hn
  have wp : 0<w N := by linarith
  have xp : X N≤N := by
    apply (le_log_iff_exp_le (by positivity : (0:ℝ)<N)).mp
    exact div_le_self nlog.le (by nlinarith [sq_nonneg (w N-1)])
  have lt : log (log (X N)) = w N-log 2-2*log (w N) := by
    rw [X,log_exp,log_div nlog.ne' (by positivity),log_mul (by norm_num) (by positivity),log_pow]
    dsimp only [w]; ring
  let P := (G N).filter Nat.Prime
  let Q := G N \ P
  have sub : P ⊆ Nat.primesLE N \ Nat.primesLE ⌊X N⌋₊ := by
    intro q hq
    obtain ⟨qG,pr⟩ := mem_filter.mp hq
    obtain ⟨qr,_,gt⟩ := mem_filter.mp qG
    exact mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨(mem_range.mp qr).le,pr⟩,
      fun h => (not_le_of_gt gt) ((Nat.le_floor_iff (exp_pos _).le).mp (Nat.mem_primesLE.mp h).1)⟩
  have incl : Nat.primesLE ⌊X N⌋₊ ⊆ Nat.primesLE N := by
    intro p hp
    have le : ⌊X N⌋₊ ≤ N := Nat.floor_le_of_le (by exact_mod_cast xp)
    exact Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans le,(Nat.mem_primesLE.mp hp).2⟩
  have prim := sum_le_sum_of_subset_of_nonneg (f:=fun q : ℕ => (1:ℝ)/q) sub (fun _ _ _ => by positivity)
  have sumP := sum_sdiff (f:=fun q : ℕ => (1:ℝ)/q) incl
  have sP : ∑ q∈P,(1:ℝ)/q ≤ Mass377.S N-Mass377.S (X N) := by
    simp only [Mass377.S,Nat.floor_natCast]
    linarith
  have ns := cc N Q (fun q hq => by
    obtain ⟨qG,no⟩ := mem_sdiff.mp hq
    obtain ⟨qr,pr,_⟩ := mem_filter.mp qG
    exact ⟨pr,fun p => no (mem_filter.mpr ⟨qG,p⟩),(mem_range.mp qr).le⟩)
  have tot := sum_sdiff (f:=fun q : ℕ => (1:ℝ)/q) (show P⊆G N from filter_subset _ _)
  change (∑ q∈Q, _)+(∑ q∈P, _) = _ at tot
  change b-1 < Mass377.S (X N)-log (log (X N)) at lower
  change Mass377.S N-w N<b+1 at upper
  change log (w N)/w N<c/4 at small
  rw [div_lt_iff₀ wp] at small
  rw [div_lt_iff₀ hc] at huge
  rw [lt] at lower
  linarith
end Rough299

namespace Rough299
open Finset Real
open scoped BigOperators
def factors (n : ℕ) := n.primeFactors.image (fun p => p ^ n.factorization p)
lemma distinct (n : ℕ) : Set.InjOn (fun p => p ^ n.factorization p) (↑n.primeFactors) := by
  intro p hp q hq he
  have h (p : ℕ) (hp : p ∈ n.primeFactors) :
      (p^n.factorization p).primeFactors = {p} :=
    Nat.primeFactors_prime_pow (Finsupp.mem_support_iff.mp hp) (Nat.prime_of_mem_primeFactors hp)
  have eq := congrArg Nat.primeFactors he
  exact Finset.singleton_inj.mp ((h p hp).symm.trans (eq.trans (h q hq)))
lemma recover {n : ℕ} (hn : n ≠ 0) : ∏ q ∈ factors n, q = n := by
  rw [factors,prod_image (distinct n)]
  exact (Nat.prod_primeFactors_pow_factorization hn).symm
lemma exponential_bound (N : ℕ) (u : ℝ) :
    (∑ n ∈ R N, exp (u*(n.primeFactors.card:ℝ))/n) ≤
      exp (exp u*∑ q ∈ G N,(1:ℝ)/q) := by
  let C := R N
  have hz : 0∉C := fun h => (mem_filter.mp h).2.1.false
  classical
  let w (q : ℕ) := exp u / (q : ℝ)
  have reconstruct (n : ℕ) (hn : n ∈ C) : ∏ q ∈ factors n, w q = exp (u*(n.primeFactors.card:ℝ)) / n := by
    have hne : n ≠ 0 := fun e => hz (e ▸ hn)
    have den : (∏ q ∈ factors n, (q : ℝ)) = n := by
      change (∏ x ∈ factors n, (Nat.castRingHom ℝ) x) = (Nat.castRingHom ℝ) n
      rw [← map_prod,recover hne]
    simp only [w,prod_div_distrib,prod_const,den]
    rw [factors,card_image_of_injOn (distinct n),← exp_nat_mul,mul_comm]
  have inject : Set.InjOn factors (↑C) := by
    intro n hn m hm heq
    have h := congrArg (fun s : Finset ℕ => ∏ q ∈ s, q) heq
    simpa only [recover (show n≠0 from fun e => hz (e ▸ hn)),recover (show m≠0 from fun e => hz (e ▸ hm))] using h
  have included : C.image factors ⊆ (G N).powerset := by
    intro s hs
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hs
    apply mem_powerset.mpr
    intro q hq
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hq
    obtain ⟨ng,pos,rough⟩ := mem_filter.mp hn
    have pr := Nat.prime_of_mem_primeFactors hp
    exact mem_filter.mpr ⟨mem_range.mpr ((Nat.le_of_dvd pos (Nat.ordProj_dvd n p)).trans_lt (mem_range.mp ng)),
      pr.isPrimePow.pow (Finsupp.mem_support_iff.mp hp),by exact_mod_cast rough p hp⟩
  calc
    _ = ∑ s ∈ C.image factors, ∏ q ∈ s, w q := by
      rw [sum_image inject]
      exact sum_congr rfl (fun n hn => (reconstruct n hn).symm)
    _ ≤ ∑ s ∈ (G N).powerset, ∏ q ∈ s, w q :=
      sum_le_sum_of_subset_of_nonneg included (fun _ _ _ => prod_nonneg fun _ _ => by dsimp [w]; positivity)
    _ = ∏ q ∈ G N, (1+w q) := (prod_one_add _).symm
    _ ≤ ∏ q ∈ G N, exp (w q) := prod_le_prod
      (fun q _ => by dsimp [w]; positivity) (fun q _ => by linarith [add_one_le_exp (w q)])
    _ = _ := by rw [← Real.exp_sum,Finset.mul_sum]; congr 1; apply sum_congr rfl; intro q hq; dsimp [w]; ring
end Rough299

open Real Filter Finset
open scoped Classical Topology
namespace Rough299
lemma budget : ∀ᶠ N : ℕ in atTop,
    ∑ d∈R N, (if (d.primeFactors.card:ℝ)≤w N/110 then (log N)^(-(1/99:ℝ))
      else 1+log N)/d < (log N)^(-(1/100:ℝ))/2 := by
  let δ : ℝ := 1/30000
  have dil : 0<δ/exp 330 := by dsimp [δ]; positivity
  filter_upwards [small_mass _ dil,Param299.wtop.eventually_gt_atTop 0,
    Mass377.logTop.eventually_gt_atTop 2,Param299.wtop.eventually_gt_atTop (20000*log 2)]
    with N small hw hb big
  let b := log (N:ℝ)
  let a := b^(-(1/99:ℝ))
  have bp : 0<b := by dsimp [b]; linarith
  have ap : 0<a := rpow_pos_of_pos bp _
  have form : a=exp (-(1/99:ℝ)*w N) := by rw [show a=b^(-(1/99:ℝ)) by rfl,rpow_def_of_pos bp]; congr 1; ring
  have est := exponential_bound N 330
  have em : exp 330*(∑ q∈G N,(1:ℝ)/q) ≤ δ*w N := by
    calc _ ≤ exp 330*((δ/exp 330)*w N) := mul_le_mul_of_nonneg_left small (exp_pos 330).le
         _ = _ := by field_simp
  have point (d : ℕ) : (if (d.primeFactors.card:ℝ)≤w N/110 then a else 1+b) ≤
      a*exp (330*(d.primeFactors.card:ℝ)) := by
    split_ifs with h
    · have one : 1 ≤ exp (330*(d.primeFactors.card:ℝ)) := one_le_exp (by positivity)
      simpa using mul_le_mul_of_nonneg_left one ap.le
    · have lt := lt_of_not_ge h
      rw [form,←exp_add]
      have high : 2*w N < -(1/99:ℝ)*w N+330*d.primeFactors.card := by linarith
      have eq : exp (2*w N)=b^2 := by rw [show 2*w N=w N*2 by ring,Real.exp_mul]; norm_cast; rw [exp_log bp]
      have ge : 1+b ≤ b^2 := by change 2<b at hb; nlinarith [sq_nonneg (b-2)]
      exact ge.trans (eq ▸ (exp_le_exp.mpr high.le))
  calc
    _ ≤ ∑ d∈R N, a*(exp (330*(d.primeFactors.card:ℝ))/d) := by
      apply sum_le_sum
      intro d hd
      simpa only [mul_div_assoc] using (div_le_div_of_nonneg_right (point d) (Nat.cast_nonneg d : (0:ℝ)≤d))
    _ ≤ a*exp (δ*w N) := by
      rw [←mul_sum]
      exact mul_le_mul_of_nonneg_left (est.trans (exp_le_exp.mpr em)) ap.le
    _ < _ := by
      rw [form,←exp_add,lt_div_iff₀ (by norm_num : (0:ℝ)<2),
        show (2:ℝ)=exp (log 2) from (exp_log (by norm_num)).symm,←exp_add,rpow_def_of_pos bp,exp_lt_exp]
      change _ < w N * (-(1/100:ℝ))
      dsimp only [δ]
      linarith
end Rough299

open Real Finset Filter
open scoped Classical Topology
namespace Rough299
lemma select : ∀ᶠ N : ℕ in atTop,
  let M := (N:ℝ)^(1-1/w N)
  ∀ n q : ℕ, 0<n → n<N → M≤n → (n.primeFactors.card:ℝ)≤2*w N →
    IsPrimePow q → q∣n → Nat.Coprime q (n/q) → ∃ d∈R N,
    M*(N:ℝ)^(-2/w N) < q*(d:ℝ) ∧ q*d∣n ∧ Nat.Coprime (q*d) (n/(q*d)) := by
  filter_upwards [Param299.wtop.eventually_gt_atTop 1,Mass377.logTop.eventually_gt_atTop 0,eventually_gt_atTop 1]
    with N hw hb hn
  intro M n q nz nb nM count qp qn cp
  let m := n/q
  have mpos : 0 < m := Nat.div_pos (Nat.le_of_dvd nz qn) qp.pos
  have eqn : q*m=n := Nat.mul_div_cancel' qn
  let S := m.primeFactors.filter fun p : ℕ => X N < (p:ℝ)^m.factorization p
  let V := m.primeFactors \ S
  let F (p : ℕ) := p^m.factorization p
  let d := ∏ p∈S, F p
  let t := ∏ p∈V, F p
  have prod : d*t=m := by
    rw [mul_comm,show t*d = ∏ p∈m.primeFactors, F p from prod_sdiff (filter_subset _ _)]
    exact (Nat.prod_primeFactors_pow_factorization mpos.ne').symm
  have posprod : 0<d*t := prod.symm ▸ mpos
  have dpos : 0<d := by
    by_contra! he
    rw [show d=0 by omega,zero_mul] at posprod
    omega
  have tpos : 0<t := by
    by_contra! he
    rw [show t=0 by omega,mul_zero] at posprod
    omega
  have ddiv : d∣m := ⟨t,prod.symm⟩
  have mdiv : m∣n := ⟨q,by simpa [mul_comm] using eqn.symm⟩
  have split : Nat.Coprime d t := by
    apply Nat.coprime_prod_left_iff.mpr
    intro p hp
    apply Nat.coprime_prod_right_iff.mpr
    intro a ha
    exact (((Nat.coprime_primes (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1)
      (Nat.prime_of_mem_primeFactors (mem_sdiff.mp ha).1)).mpr (by rintro rfl; exact (mem_sdiff.mp ha).2 hp)).pow_left _).pow_right _
  have dR : d∈R N := by
    refine mem_filter.mpr ⟨mem_range.mpr ((Nat.le_of_dvd nz (ddiv.trans mdiv)).trans_lt nb),dpos,?_⟩
    intro p pd
    have pm := Nat.primeFactors_mono ddiv mpos.ne' pd
    have pp := Nat.prime_of_mem_primeFactors pd
    have pds := Nat.dvd_of_mem_primeFactors pd
    have npt := (pp.coprime_iff_not_dvd).mp (split.coprime_dvd_left pds)
    have e : m.factorization p=d.factorization p := by
      rw [←prod,Nat.factorization_mul_apply_of_coprime split,Nat.factorization_eq_zero_of_not_dvd npt,add_zero]
    rw [←e]
    by_contra! fail
    have pv : p∈V := mem_sdiff.mpr ⟨pm,by simpa [S,pm] using fail⟩
    exact npt ((dvd_pow_self _ (Finsupp.mem_support_iff.mp pm)).trans (dvd_prod_of_mem F pv))
  have nrep : (q*d)*t=n := by rw [mul_assoc,prod,eqn]
  have cop : Nat.Coprime (q*d) t := Nat.Coprime.mul_left (cp.coprime_dvd_right (show t∣m from ⟨d,by rw [mul_comm,prod]⟩)) split
  have divt : n/(q*d)=t := by rw [←nrep,Nat.mul_div_cancel_left _ (Nat.mul_pos qp.pos dpos)]
  refine ⟨d,dR,?_,⟨t,nrep.symm⟩,divt ▸ cop⟩
  have logt : log (t:ℝ) ≤ log N / w N := by
    have vp (p : ℕ) (hp : p∈V) : 0<(F p:ℝ) := by
      dsimp [F]
      positivity [(Nat.prime_of_mem_primeFactors (mem_sdiff.mp hp).1).pos]
    have val (p : ℕ) (hp : p∈V) : log (F p:ℝ)≤log N/(2*(w N)^2) := by
      have ne := (mem_sdiff.mp hp).2
      have h : (F p:ℝ)≤X N := by
        by_contra! no
        apply ne
        apply mem_filter.mpr
        exact ⟨(mem_sdiff.mp hp).1,by simpa [F] using no⟩
      exact (log_le_log (vp p hp) h).trans_eq (log_exp _)
    have vsub : V⊆n.primeFactors := (sdiff_subset).trans (Nat.primeFactors_mono mdiv nz.ne')
    have card : (V.card:ℝ)≤2*w N := (by exact_mod_cast card_le_card vsub : (V.card:ℝ)≤n.primeFactors.card).trans count
    have eval : log (t:ℝ)=∑ p∈V, log (F p:ℝ) := by
      simp only [t,Nat.cast_prod]
      exact log_prod (fun p hp => (vp p hp).ne')
    rw [eval]
    calc _ ≤ ∑ _p∈V, log N/(2*(w N)^2) := sum_le_sum val
         _ ≤ 2*w N*(log N/(2*(w N)^2)) := by
           simp only [sum_const,nsmul_eq_mul]
           exact mul_le_mul_of_nonneg_right card (by positivity)
         _ = _ := by field_simp <;> ring
  have nr : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have tr : (0:ℝ)<t := by exact_mod_cast tpos
  have upper : (t:ℝ)<(N:ℝ)^(2/w N) := by
    apply (log_lt_log_iff tr (rpow_pos_of_pos nr _)).mp
    rw [log_rpow nr]
    have bpos : 0<log N/w N := by positivity
    linarith [show 2/w N*log N=2*(log N/w N) by ring]
  have rho := rpow_pos_of_pos nr (2/w N)
  rw [show (-2:ℝ)/w N=-(2/w N) by ring,rpow_neg nr.le,←div_eq_mul_inv,div_lt_iff₀ rho]
  have eqr : (q:ℝ)*d*t=n := by exact_mod_cast nrep
  exact nM.trans_lt (eqr ▸ (mul_lt_mul_of_pos_left upper (by exact_mod_cast Nat.mul_pos qp.pos dpos : 0<(q:ℝ)*d)))
end Rough299

open Real Filter Finset
open scoped Classical Topology
namespace Rough299
lemma divisor_sample {N : ℕ} {S : Finset ℕ} (hN : 0<N) (sm : S⊆Icc 1 N) :
    (∑ n∈S,(1:ℝ)/n) ≤ 1+log N := by
  have e := harmonic_floor_le_one_add_log (N:ℝ) (by exact_mod_cast hN)
  rw [Nat.floor_natCast,harmonic_eq_sum_Icc,Rat.cast_sum] at e
  push_cast at e
  simpa [one_div] using (sum_le_sum_of_subset_of_nonneg (f:=fun n : ℕ => (n:ℝ)⁻¹) sm (fun _ _ _ => by positivity)).trans e
theorem result : OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1_H3_R1.H1 := by
  classical
  filter_upwards [select,budget,Param299.wtop.eventually_gt_atTop 1000,eventually_gt_atTop 2,
    Mass377.logTop.eventually_gt_atTop 0] with N hsel estimate hw hn hb
  intro A q ha an reg qp mass
  let J := A.filter (fun n => q∣n ∧ Nat.Coprime q (n/q))
  let M := (N:ℝ)^(1-1/w N)
  let K := M*(N:ℝ)^(-2/w N)
  let b := log (N:ℝ)
  let v (d : ℕ) := if (d.primeFactors.card:ℝ)≤w N/110 then b^(-(1/99:ℝ)) else 1+b
  let a := b^(-(1/99:ℝ))
  have ap : 0<a := rpow_pos_of_pos hb _
  have qp0 : 0<q := qp.pos
  have haveD {n : ℕ} (hn : n∈J) := hsel n q
    (Nat.pos_of_ne_zero (fun e => ha (e ▸ (mem_filter.mp hn).1))) (mem_range.mp (an (mem_filter.mp hn).1))
    (reg n (mem_filter.mp hn).1).1 (reg n (mem_filter.mp hn).1).2.2.2 qp (mem_filter.mp hn).2.1 (mem_filter.mp hn).2.2
  let f (n : ℕ) := if hn : n∈J then (haveD hn).choose else 1
  have spec {n : ℕ} (hn : n∈J) : f n∈R N ∧ K<q*(f n:ℝ) ∧ q*f n∣n ∧ Nat.Coprime (q*f n) (n/(q*f n)) := by
    simpa [f,hn,K,M] using (haveD hn).choose_spec
  let F (d : ℕ) := J.filter fun n => f n=d
  let C (d : ℕ) := (F d).image (fun n => n/(q*d))
  let m (S : Finset ℕ) := ∑ n∈S,(1:ℝ)/n
  have Dspec {d n : ℕ} (hn : n∈F d) : n∈A ∧ K<q*(d:ℝ) ∧ q*d∣n ∧ Nat.Coprime (q*d) (n/(q*d)) := by
    obtain ⟨j,e⟩ := mem_filter.mp hn
    exact ⟨(mem_filter.mp j).1,e ▸ (spec j).2⟩
  have factor {d n : ℕ} (hn : n∈F d) : q*d*(n/(q*d))=n := Nat.mul_div_cancel' (Dspec hn).2.2.1
  have fiber (d : ℕ) (hd : d∈R N) : m (C d)/d=∑ n∈F d,(q:ℝ)/n := by
    have dp := (mem_filter.mp hd).2.1
    dsimp only [m,C]
    rw [sum_image,sum_div]
    · apply sum_congr rfl
      intro n hn
      have pos : 0<n := Nat.pos_of_ne_zero (fun e => ha (e ▸ (Dspec hn).1))
      have rn : (0:ℝ)<n := by exact_mod_cast pos
      have rd : (0:ℝ)<d := by exact_mod_cast dp
      have rm : (0:ℝ)<(n/(q*d):ℕ) := by exact_mod_cast Nat.div_pos (Nat.le_of_dvd pos (Dspec hn).2.2.1) (Nat.mul_pos qp0 dp)
      have re : (q:ℝ)*d*(n/(q*d):ℕ)=n := by exact_mod_cast factor hn
      field_simp
      linarith
    · intro n h m hm eq
      exact (factor h).symm.trans ((congrArg (q*d*·) eq).trans (factor hm))
  have total := sum_fiberwise_of_maps_to (s:=J) (t:=R N) (g:=f) (fun n hn => (spec hn).1) (fun n => (q:ℝ)/n)
  have win : ∃ d∈R N, v d < m (C d) := by
    by_contra! fail
    have le := sum_le_sum (s:=R N) (fun d hd => div_le_div_of_nonneg_right (fail d hd) (Nat.cast_nonneg d : (0:ℝ)≤d))
    change ∑ d∈R N, v d / d < b^(-(1/100:ℝ))/2 at estimate
    change b^(-(1/100:ℝ))/2≤∑ n∈J,(q:ℝ)/n at mass
    have eq : ∑ d∈R N, m (C d)/d = ∑ n∈J,(q:ℝ)/n := (sum_congr rfl fiber).trans total
    linarith
  obtain ⟨d,hd,win⟩ := win
  have dp := (mem_filter.mp hd).2.1
  have hbnd : C d ⊆ Icc 1 N := by
    intro s hs
    obtain ⟨n,h,rfl⟩ := mem_image.mp hs
    have pos : 0<n := Nat.pos_of_ne_zero (fun e => ha (e ▸ (Dspec h).1))
    exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd pos (Dspec h).2.2.1) (Nat.mul_pos qp0 dp),
      (Nat.div_le_self _ _).trans (mem_range.mp (an (Dspec h).1)).le⟩
  have low : (d.primeFactors.card:ℝ)≤w N/110 := by
    by_contra no
    have h := divisor_sample (by omega : 0<N) hbnd
    change m (C d) ≤ 1+b at h
    exact (not_lt_of_ge h) (by simpa only [v,if_neg no] using win)
  change (if _ then _ else _) < m (C d) at win
  rw [if_pos low] at win
  have non : (F d).Nonempty := by
    by_contra! empty
    have e : C d=∅ := by simp [C,empty]
    rw [e] at win
    change a < ∑ n∈(∅:Finset ℕ), (1:ℝ)/n at win
    simp at win
    linarith
  obtain ⟨n,hnF⟩ := non
  refine ⟨q*d,C d,by change K < ((q*d:ℕ):ℝ); rw [Nat.cast_mul]; exact (Dspec hnF).2.1,dvd_mul_right _ _,win.le,?_⟩
  intro s hs
  obtain ⟨n,h,rfl⟩ := mem_image.mp hs
  have e := factor h
  have data := Dspec h
  refine ⟨by rw [e]; exact data.1,data.2.2.2.symm,?_,?_⟩
  · let s := n/(q*d)
    have spos : 0<s := (mem_Icc.mp (hbnd (mem_image.mpr ⟨n,h,rfl⟩))).1
    have qc : q.primeFactors.card=1 := by
      obtain ⟨p,k,pr,pk,eq⟩ := (isPrimePow_nat_iff q).mp qp
      rw [←eq,Nat.primeFactors_prime_pow (by omega) pr,card_singleton]
    have card : n.primeFactors.card ≤ 1+d.primeFactors.card+s.primeFactors.card := by
      rw [←e,Nat.primeFactors_mul (Nat.mul_pos qp0 dp).ne' spos.ne']
      have ab := card_union_le (q*d).primeFactors s.primeFactors
      have first := card_union_le q.primeFactors d.primeFactors
      rw [Nat.primeFactors_mul qp0.ne' dp.ne'] at ab ⊢
      omega
    have realc : (n.primeFactors.card:ℝ) ≤ 1+d.primeFactors.card+s.primeFactors.card := by exact_mod_cast card
    have lower := (reg n data.1).2.2.1
    change 99/100*w N ≤ n.primeFactors.card at lower
    change (1-2/99)*w N ≤ s.primeFactors.card
    change 1000<w N at hw
    linarith
  · have sub := Nat.primeFactors_mono (show n/(q*d)∣n from ⟨_,e.symm.trans (Nat.mul_comm _ _)⟩) (fun eq => ha (eq ▸ data.1))
    exact (show ((n/(q*d)).primeFactors.card:ℝ) ≤ n.primeFactors.card by exact_mod_cast card_le_card sub).trans (reg n data.1).2.2.2
end Rough299


namespace Param299
open Filter Real Finset
open scoped Topology
lemma Mtop : Tendsto M atTop atTop := by
  have h := (tendsto_rpow_atTop (by norm_num : 0<(1/2:ℝ))).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  apply tendsto_atTop_mono' _ _ h
  filter_upwards [wtop.eventually_ge_atTop 2,eventually_ge_atTop 1] with N hw hn
  apply rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
  linarith [one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hw]
lemma eMass : Tendsto (fun N => e N*w N) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1/100:ℝ) (by norm_num)).comp wtop
  apply h.congr'
  filter_upwards [Mass377.logTop.eventually_gt_atTop 0] with N hN
  simp only [Function.comp_apply,Real.rpow_one,e,Real.rpow_def_of_pos hN]
  dsimp only [w]
  ring_nf
end Param299

/-!
The set of maximal prime powers of a positive integer determines it by multiplication. Expanding a product of factors 1 + exp(1)/q bounds the weighted reciprocal sum of the cofactor family. Taking logarithms gives the required prime-power mass.
-/
namespace OMA.FactorMass
open Finset Real
open scoped BigOperators
def powers (C : Finset ℕ) := C.biUnion fun n =>
  n.divisors.filter fun q => IsPrimePow q ∧ Nat.Coprime q (n/q)
def factors (n : ℕ) := n.primeFactors.image (fun p => p ^ n.factorization p)
lemma distinct (n : ℕ) : Set.InjOn (fun p => p ^ n.factorization p) (↑n.primeFactors) := by
  intro p hp q hq he
  have h (p : ℕ) (hp : p ∈ n.primeFactors) :
      (p^n.factorization p).primeFactors = {p} :=
    Nat.primeFactors_prime_pow (Finsupp.mem_support_iff.mp hp) (Nat.prime_of_mem_primeFactors hp)
  have eq := congrArg Nat.primeFactors he
  exact Finset.singleton_inj.mp ((h p hp).symm.trans (eq.trans (h q hq)))
lemma recover {n : ℕ} (hn : n ≠ 0) : ∏ q ∈ factors n, q = n := by
  rw [factors,prod_image (distinct n)]
  exact (Nat.prod_primeFactors_pow_factorization hn).symm
lemma subset_powers {C : Finset ℕ} {n : ℕ} (hn : n ∈ C) (hz : n ≠ 0) :
    factors n ⊆ powers C := by
  intro q hq
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hq
  have prime := Nat.prime_of_mem_primeFactors hp
  exact mem_biUnion.mpr ⟨n,hn,mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.ordProj_dvd n p,hz⟩,
    prime.isPrimePow.pow (Finsupp.mem_support_iff.mp hp),(Nat.coprime_ordCompl prime hz).pow_left _⟩⟩
lemma exponential_bound (C : Finset ℕ) (hz : 0 ∉ C) :
    (∑ n ∈ C, exp (n.primeFactors.card : ℝ) / n) ≤
      exp (exp 1 * ∑ q ∈ powers C, (1:ℝ)/q) := by
  classical
  let w (q : ℕ) := exp 1 / (q : ℝ)
  have reconstruct (n : ℕ) (hn : n ∈ C) : ∏ q ∈ factors n, w q = exp (n.primeFactors.card : ℝ) / n := by
    have hne : n ≠ 0 := fun e => hz (e ▸ hn)
    have den : (∏ q ∈ factors n, (q : ℝ)) = n := by
      change (∏ x ∈ factors n, (Nat.castRingHom ℝ) x) = (Nat.castRingHom ℝ) n
      rw [← map_prod,recover hne]
    simp only [w,prod_div_distrib,prod_const,den]
    rw [factors,card_image_of_injOn (distinct n),← exp_nat_mul,mul_one]
  have inject : Set.InjOn factors (↑C) := by
    intro n hn m hm heq
    have h := congrArg (fun s : Finset ℕ => ∏ q ∈ s, q) heq
    simpa only [recover (show n≠0 from fun e => hz (e ▸ hn)),recover (show m≠0 from fun e => hz (e ▸ hm))] using h
  have included : C.image factors ⊆ (powers C).powerset := by
    intro s hs
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hs
    exact mem_powerset.mpr (subset_powers hn (fun e => hz (e ▸ hn)))
  calc
    _ = ∑ s ∈ C.image factors, ∏ q ∈ s, w q := by
      rw [sum_image inject]
      exact sum_congr rfl (fun n hn => (reconstruct n hn).symm)
    _ ≤ ∑ s ∈ (powers C).powerset, ∏ q ∈ s, w q :=
      sum_le_sum_of_subset_of_nonneg included (fun _ _ _ => prod_nonneg fun _ _ => by dsimp [w]; positivity)
    _ = ∏ q ∈ powers C, (1+w q) := (prod_one_add _).symm
    _ ≤ ∏ q ∈ powers C, exp (w q) := prod_le_prod
      (fun q _ => by dsimp [w]; positivity) (fun q _ => by linarith [add_one_le_exp (w q)])
    _ = _ := by rw [← Real.exp_sum,Finset.mul_sum]; congr 1; apply sum_congr rfl; intro q hq; dsimp [w]; ring
end OMA.FactorMass

namespace OMA.FactorMass
open Filter Finset Real

theorem density : ∀ᶠ N : ℕ in atTop, ∀ C : Finset ℕ,
    (log N)^(-(1/99:ℝ)) ≤ ∑ n ∈ C, (1:ℝ)/n →
    (∀ m ∈ C, (1-2/99:ℝ)*log (log N) ≤ m.primeFactors.card ∧
      (m.primeFactors.card:ℝ) ≤ 2*log (log N)) →
    (35/100:ℝ)*log (log N) ≤ ∑ q ∈ powers C, (1:ℝ)/q := by
  filter_upwards [eventually_ge_atTop 4] with N hN
  intro C hm hc
  let w := log (log N)
  have e := exp_one_lt_d9
  have hn : (4:ℝ) ≤ N := by exact_mod_cast hN
  have logbig : 1 < log N := (lt_log_iff_exp_lt (by linarith)).mpr (by linarith)
  have hw : 0 < w := log_pos logbig
  have hz : 0 ∉ C := by
    intro h
    have := (hc 0 h).1
    simp only [Nat.primeFactors_zero,card_empty,Nat.cast_zero] at this
    change (1-2/99:ℝ)*w ≤ 0 at this
    linarith
  have bound := exponential_bound C hz
  have mass : exp (-(1/99:ℝ)*w) ≤ ∑ n ∈ C, (1:ℝ)/n := by
    rw [Real.rpow_def_of_pos (by linarith : 0 < log N)] at hm
    simpa only [w,mul_comm] using hm
  have lower : exp ((1-3/99:ℝ)*w) ≤ exp (exp 1 * ∑ q ∈ powers C, (1:ℝ)/q) := calc
    _ = exp ((1-2/99:ℝ)*w) * exp (-(1/99:ℝ)*w) := by rw [← exp_add]; congr 1; ring
    _ ≤ exp ((1-2/99:ℝ)*w) * ∑ n ∈ C, (1:ℝ)/n := mul_le_mul_of_nonneg_left mass (exp_pos _).le
    _ ≤ ∑ n ∈ C, exp (n.primeFactors.card : ℝ)/n := by
      rw [mul_sum]
      apply sum_le_sum
      intro n hn
      rw [mul_one_div]
      apply div_le_div_of_nonneg_right (exp_le_exp.mpr (hc n hn).1) (by positivity)
    _ ≤ _ := bound
  have logbound := exp_le_exp.mp lower
  change 35/100*w ≤ _
  by_contra! bad
  have bad' := mul_lt_mul_of_pos_left bad (exp_pos 1)
  nlinarith only [bad', logbound, hw, mul_lt_mul_of_pos_right e hw]
end OMA.FactorMass


open Real Finset Filter
open scoped Classical Topology
namespace Wigert299
lemma divisor_bound : ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, 0 < m → m ≤ N^2 →
    (m.divisors.card:ℝ) ≤ exp ((9/5:ℝ)*log N/log (log N)) := by
  let B (N:ℕ) := log (N:ℝ)
  let W (N:ℕ) := log (B N)
  have bt : Tendsto B atTop atTop := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have l := (isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0:ℝ)<1/10)).tendsto_div_nhds_zero.comp bt
  filter_upwards [l.eventually_lt_const (by norm_num : (0:ℝ)<1/10),
    bt.eventually_gt_atTop 10,(tendsto_log_atTop.comp bt).eventually_gt_atTop 1,
    eventually_gt_atTop 1] with N small hb hw hn
  intro m mp mN
  have bp : 0<B N := by linarith
  have wp : 0<W N := by exact hw.trans' zero_lt_one
  have nr : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  let Y := (B N)^(9/10:ℝ)
  let S := m.primeFactors.filter fun p : ℕ => (p:ℝ)≤Y
  let T := m.primeFactors \ S
  let k (p : ℕ) := m.factorization p
  let f (p : ℕ) := log ((k p:ℝ)+1)
  let g (p : ℕ) := (k p:ℝ)*log p
  have gsum : ∑ p∈m.primeFactors,g p ≤ 2*B N := by
    have cast : (m:ℝ)=∏ p∈m.primeFactors,(p:ℝ)^(k p) := by exact_mod_cast Nat.prod_primeFactors_pow_factorization mp.ne'
    have eq : log (m:ℝ)=∑ p∈m.primeFactors,g p := by
      conv_lhs => rw [cast]
      rw [log_prod (s:=m.primeFactors) (f:=fun p : ℕ => (p:ℝ)^(k p)) (fun p hp => (pow_pos (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos : (0:ℝ)<p) _).ne')]
      simp only [g,log_pow]
    rw [←eq]
    have e := log_le_log (by exact_mod_cast mp : 0<(m:ℝ)) (by exact_mod_cast mN : (m:ℝ)≤(N:ℝ)^2)
    simpa [log_pow,B] using e
  have gn (p : ℕ) (hp : p∈m.primeFactors) : 0≤g p := mul_nonneg (Nat.cast_nonneg _) (log_nonneg
    (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le))
  have l2 : 1/2≤log (2:ℝ) := by linarith [Real.log_two_gt_d9]
  have smallp (p : ℕ) (hp : p∈S) : f p≤2*W N := by
    have pr := Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
    have lp : log 2≤log (p:ℝ) := log_le_log (by norm_num) (by exact_mod_cast pr.two_le)
    have bound := (single_le_sum gn (mem_filter.mp hp).1).trans gsum
    have kk := mul_le_mul_of_nonneg_left (l2.trans lp) (Nat.cast_nonneg (k p) : (0:ℝ)≤k p)
    change (k p:ℝ)*log p≤2*B N at bound
    have pwr : (k p:ℝ)+1≤(B N)^2 := by nlinarith [sq_nonneg (B N-5)]
    have est := log_le_log (by positivity : 0<(k p:ℝ)+1) pwr
    simpa [f,log_pow,W] using est
  have largep (p : ℕ) (hp : p∈T) : f p*W N≤(4/5:ℝ)*g p := by
    obtain ⟨pm,ns⟩ := mem_sdiff.mp hp
    have yp : Y < (p:ℝ) := lt_of_not_ge (fun le => ns (mem_filter.mpr ⟨pm,le⟩))
    have lp := log_lt_log (rpow_pos_of_pos bp (9/10:ℝ)) yp
    rw [log_rpow bp] at lp
    change (9/10:ℝ)*W N < log p at lp
    have ke : k p+1≤2^k p := Nat.lt_two_pow_self
    have le := log_le_log (by positivity : 0<(k p:ℝ)+1) (by exact_mod_cast ke : (k p:ℝ)+1≤(2:ℝ)^k p)
    rw [log_pow] at le
    have l2' : log 2≤(7/10:ℝ) := by linarith [Real.log_two_lt_d9]
    have c := mul_le_mul_of_nonneg_left l2' (Nat.cast_nonneg (k p) : (0:ℝ)≤k p)
    have d := mul_le_mul_of_nonneg_left lp.le (Nat.cast_nonneg (k p) : (0:ℝ)≤k p)
    have e := mul_le_mul_of_nonneg_right (le.trans c) wp.le
    dsimp [f,g]
    nlinarith only [d,e,mul_nonneg (Nat.cast_nonneg (k p) : (0:ℝ)≤k p) wp.le]
  have sc : (S.card:ℝ) ≤ Y := by
    have sub : S⊆Icc 1 ⌊Y⌋₊ := by
      intro p hp
      obtain ⟨pm,le⟩ := mem_filter.mp hp
      exact mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors pm).one_le,Nat.le_floor le⟩
    have e : S.card≤⌊Y⌋₊ := by simpa using card_le_card sub
    exact (show (S.card:ℝ)≤⌊Y⌋₊ by exact_mod_cast e).trans (Nat.floor_le (rpow_pos_of_pos bp _).le)
  have upperS : (∑ p∈S, f p)*W N ≤ (1/5:ℝ)*B N := by
    have h := sum_le_sum smallp
    simp only [sum_const,nsmul_eq_mul] at h
    have m := mul_le_mul_of_nonneg_right (h.trans (mul_le_mul_of_nonneg_right sc (by positivity))) wp.le
    change (log (B N))^(2:ℝ)/(B N)^(1/10:ℝ)<1/10 at small
    rw [rpow_two,div_lt_iff₀ (rpow_pos_of_pos bp _)] at small
    change W N^2<_ at small
    have rc := mul_lt_mul_of_pos_right small (rpow_pos_of_pos bp (9/10:ℝ))
    have eq : (B N)^(1/10:ℝ)*Y=B N := by rw [←rpow_add bp]; norm_num
    change W N^2*Y < 1/10*(B N)^(1/10:ℝ)*Y at rc
    rw [mul_assoc,eq] at rc
    nlinarith only [rc,m]
  have upperT : (∑ p∈T,f p)*W N≤(4/5:ℝ)*(2*B N) := by
    rw [sum_mul]
    apply (sum_le_sum largep).trans
    rw [←mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact (sum_le_sum_of_subset_of_nonneg (sdiff_subset : T⊆m.primeFactors) (fun p hp _ => gn p hp)).trans gsum
  have sp := sum_sdiff (f:=f) (show S⊆m.primeFactors from filter_subset _ _)
  change (∑ p∈T,f p)+(∑ p∈S,f p)=_ at sp
  have coeff : (∑ p∈m.primeFactors, f p) ≤ (9/5:ℝ)*B N/W N := by
    rw [le_div_iff₀ wp,←sp,add_mul]
    linarith
  have card : (m.divisors.card:ℝ)=∏ p∈m.primeFactors, ((k p:ℝ)+1) := by exact_mod_cast Nat.card_divisors mp.ne'
  have e : 0<(m.divisors.card:ℝ) := by rw [card]; positivity
  apply (log_le_iff_le_exp e).mp
  rw [card,log_prod (fun p _ => by positivity)]
  exact coeff
end Wigert299

open Filter Finset Real
open scoped Classical Topology
namespace TinyOverlap299
noncomputable abbrev mass (A : Finset ℕ) := ∑ n ∈ A, (1:ℝ)/n
lemma pp_bound (m : ℕ) (hm : 0 < m) (P : Finset ℕ) (hP : ∀ q ∈ P, IsPrimePow q ∧ q∣m) :
    mass P ≤ 2*mass m.primeFactors := by
  let U := m.primeFactors ×ˢ range m
  let f (p : ℕ×ℕ) := p.1^(p.2+1)
  have sub : P⊆U.image f := by
    intro q hq
    obtain ⟨pp,dvd⟩ := hP q hq
    obtain ⟨p,hp,k,hk,pr,hk0,eq⟩ := (isPrimePow_nat_iff_bounded q).mp pp
    have pd := (dvd_pow_self p hk0.ne').trans (eq ▸ dvd : p^k ∣ m)
    have le := Nat.le_of_dvd hm dvd
    cases k with
    | zero => omega
    | succ j => exact mem_image.mpr ⟨(p,j),mem_product.mpr ⟨Nat.mem_primeFactors.mpr ⟨pr,pd,hm.ne'⟩,
                    mem_range.mpr (by omega)⟩,eq⟩
  calc _ ≤ ∑ q ∈ U.image f, (1:ℝ)/q := sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => by positivity)
       _ ≤ ∑ a ∈ U, (1:ℝ)/(f a) := sum_image_le_of_nonneg (fun _ _ => by positivity)
       _ = ∑ p ∈ m.primeFactors, ∑ k ∈ range m, (1:ℝ)/(p:ℝ)^(k+1) := by simp [U,f,sum_product]
       _ ≤ ∑ p ∈ m.primeFactors, 2/(p:ℝ) := sum_le_sum fun p hp =>
          Param299.geom p (Nat.prime_of_mem_primeFactors hp).two_le m
       _ = _ := by simp only [mass,mul_sum]; congr 1; ext; ring
lemma card_le_log {s : ℕ} (hs : 0 < s) :
    (s.primeFactors.card : ℝ) ≤ log s / log 2 := by
  have h1 : 2 ^ s.primeFactors.card ≤ ∏ p ∈ s.primeFactors, p :=
    pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  have h2 := Nat.le_of_dvd hs (Nat.prod_primeFactors_dvd s)
  have h3 : ((2 : ℝ) ^ s.primeFactors.card) ≤ s := by exact_mod_cast h1.trans h2
  rw [le_div_iff₀ (log_pos one_lt_two)]
  have := log_le_log (by positivity) h3
  rwa [log_pow] at this
lemma overlap : ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, 0 < m → m≤N → ∀ P : Finset ℕ,
    (∀ q ∈ P, IsPrimePow q ∧ q∣m) → mass P < (1/500:ℝ)*Param299.w N := by
  obtain ⟨b,hb⟩ := Mass377.realMertens
  have hg := (tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp Param299.wtop
  filter_upwards [(hb.comp Mass377.logTop).eventually_lt_const (show b<b+1 by linarith),
    hg.eventually_lt_const (by norm_num : (0:ℝ)<1/10000),
    Param299.wtop.eventually_gt_atTop (10000*(|b|+1+1/log 2)),
    Mass377.logTop.eventually_gt_atTop 1] with N hprime hratio hw hN
  intro m hm hmN P hP
  let X := log (N:ℝ)
  let Q := m.primeFactors.filter fun p : ℕ => (p:ℝ)≤X
  let R := m.primeFactors \ Q
  have xp : 0<X := by dsimp [X]; linarith
  have p2 : 0<log 2 := log_pos one_lt_two
  have wpos : 0<Param299.w N := by linarith [abs_nonneg b,one_div_pos.mpr p2]
  change Mass377.S X - log (Param299.w N) < b+1 at hprime
  simp only [Function.comp_apply,pow_one,one_mul,add_zero] at hratio
  have small := (div_lt_iff₀ wpos).mp hratio
  have sub : Q ⊆ Nat.primesLE ⌊X⌋₊ := by
    intro p hp
    obtain ⟨hp,le⟩ := mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨Nat.le_floor le,Nat.prime_of_mem_primeFactors hp⟩
  have lo : mass Q ≤ Mass377.S X := sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => by positivity)
  have hi : mass R ≤ 1/log 2 := by
    have hh : mass R ≤ (R.card:ℝ)*(1/X) := by
      simpa [mass,nsmul_eq_mul] using sum_le_card_nsmul R (fun p : ℕ => (1:ℝ)/p) (1/X) (by
        intro p hp
        obtain ⟨h1,h2⟩ := mem_sdiff.mp hp
        exact one_div_le_one_div_of_le xp (le_of_not_ge (fun le => h2 (mem_filter.mpr ⟨h1,le⟩))))
    have size : (R.card:ℝ)≤ m.primeFactors.card := by exact_mod_cast card_le_card (sdiff_subset : R⊆m.primeFactors)
    have logle : log (m:ℝ) ≤ X := log_le_log (by exact_mod_cast hm) (by exact_mod_cast hmN)
    have cm := size.trans ((card_le_log hm).trans (div_le_div_of_nonneg_right logle p2.le))
    calc mass R ≤ (R.card:ℝ)*(1/X) := hh
         _ ≤ (X/log 2)*(1/X) := mul_le_mul_of_nonneg_right cm (by positivity)
         _ = _ := by field_simp
  have eq := sum_sdiff (filter_subset (fun p : ℕ => (p:ℝ)≤X) m.primeFactors) (f:=fun p : ℕ => (1:ℝ)/p)
  change mass R + mass Q = mass m.primeFactors at eq
  have pp := pp_bound m hm P hP
  linarith [le_abs_self b]
end TinyOverlap299

open Filter Real Finset
open scoped Classical Topology
namespace FirstForce299
open OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1_H3_R1
noncomputable abbrev I (t K : ℝ) := Icc (⌈t-K/2⌉:ℤ) ⌊t+K/2⌋
def hits (J : Finset ℤ) (n : ℕ) := ∃ x∈J,(n:ℤ)∣x
noncomputable abbrev pix (Q : Finset ℕ) (x : ℤ) := Q.filter fun q : ℕ => (q:ℤ)∣x
def regular (N n : ℕ) : Prop := Regular N n
noncomputable abbrev E (N : ℕ) (A U : Finset ℕ) := (powers A).filter fun q =>
  e N/2 ≤ ∑ n∈part U q,(q:ℝ)/n
lemma distance (x y : ℤ) {t K : ℝ} (hx : x∈I t K) (hy : y∈I t K) : |(x:ℝ)-y|≤K := by
  have bounds (j : ℤ) (hj : j∈I t K) : t-K/2≤j ∧ (j:ℝ)≤t+K/2 :=
    ⟨Int.ceil_le.mp (mem_Icc.mp hj).1,Int.le_floor.mp (mem_Icc.mp hj).2⟩
  obtain ⟨xl,xu⟩ := bounds x hx
  obtain ⟨yl,yu⟩ := bounds y hy
  exact abs_le.mpr ⟨by linarith,by linarith⟩
lemma heavy : ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℕ) (t : ℝ), 0∉A → A⊆range N →
    (∀ n∈A, regular N n) → let J := I t (K N)
    let U := A.filter (hits J)
    ∀ q∈E N A U, ∃ x∈J,(q:ℤ)∣x ∧ (35/100:ℝ)*w N ≤ mass (pix (powers A) x) := by
  filter_upwards [Rough299.result, OMA.FactorMass.density,Mass377.logTop.eventually_gt_atTop 0] with N co en hlog
  intro A t a0 aN reg J U q qe
  have ua : U⊆A := filter_subset _ _
  have pp := (power_mem (mem_filter.mp qe).1).1
  have bulk := (mem_filter.mp qe).2
  let F (x : ℤ) := pix (powers A) x
  have dist (x y : ℤ) (hx : x∈J) (hy : y∈J) := distance x y hx hy
  obtain ⟨D,C,big,qd,cm,cf⟩ := co U q (fun h => a0 (ua h)) (ua.trans aN)
    (fun n hn => reg n (ua hn)) pp bulk
  have cd := en C cm (fun m hm => (cf m hm).2.2)
  obtain ⟨m,hm⟩ := nonempty_of_ne_empty (s:=C) (fun eq => by
    have p := rpow_pos_of_pos hlog (-(1/99:ℝ))
    rw [eq] at cm
    exact p.not_ge (by simpa only [mass,sum_empty] using cm))
  obtain ⟨x,hx,dx⟩ := (mem_filter.mp (cf m hm).1).2
  have Dvd (m : ℕ) {y : ℤ} (hy : ((D*m:ℕ):ℤ)∣y) : (D:ℤ)∣y :=
    (show (D:ℤ) ∣ ((D*m:ℕ):ℤ) by exact_mod_cast (dvd_mul_right D m)).trans hy
  have uniq (y : ℤ) (hy : y∈J) (dy : (D:ℤ)∣y) : x=y := by
    have h : |x-y|<(D:ℤ) := by exact_mod_cast (dist x y hx hy).trans_lt big
    exact sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd (dvd_sub (Dvd m dx) dy) h)
  have inc : powers C ⊆ F x := by
    intro r hr
    obtain ⟨pr,j,hj,j0,rj,cp⟩ := power_mem hr
    obtain ⟨inU,cop,_⟩ := cf j hj
    obtain ⟨inA,y,hy,divy⟩ := mem_filter.mp inU
    have rDj := rj.trans (dvd_mul_left j D)
    have prA : r ∈ powers A := by
      apply mem_biUnion.mpr
      refine ⟨D*j,inA,mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨rDj,fun eq => a0 (eq ▸ inA)⟩,pr,?_⟩⟩
      rw [Nat.mul_div_assoc D rj]
      exact (cop.coprime_dvd_left rj).mul_right cp
    refine mem_filter.mpr ⟨prA,?_⟩
    rw [uniq y hy (Dvd j divy)]
    exact (show (r:ℤ) ∣ ((D*j:ℕ):ℤ) by exact_mod_cast rDj).trans divy
  exact ⟨x,hx,(show (q:ℤ)∣D by exact_mod_cast qd).trans (Dvd m dx),cd.trans
    (sum_le_sum_of_subset_of_nonneg inc (fun _ _ _ => by positivity))⟩
end FirstForce299

open Real Finset
open scoped Classical
namespace Trapped299
lemma product_dvd {n : ℕ} {x y : ℤ} (nz : 0<n)
    (split : ∀ p∈n.primeFactors, let q := p^n.factorization p
      (q:ℤ)∣x ∨ (q:ℤ)∣y) : (n:ℤ)∣x*y := by
  apply Int.natAbs_dvd_natAbs.mp
  rw [Int.natAbs_natCast,Int.natAbs_mul]
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p k pr pk
  by_cases zero : k=0
  · simp [zero]
  have pd := (dvd_pow_self p zero).trans pk
  have h := split p (Nat.mem_primeFactors.mpr ⟨pr,pd,nz.ne'⟩)
  have kf := (pr.pow_dvd_iff_le_factorization nz.ne').mp pk
  apply (pow_dvd_pow p kf).trans
  rcases h with hx|hy
  · exact dvd_mul_of_dvd_left (by simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hx) _
  · exact dvd_mul_of_dvd_right (by simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hy) _
lemma trapped (V : Finset ℕ) (J : Finset ℤ) {x y : ℤ} {N : ℕ} {C : ℝ} (cp : 0≤C)
    (width : ∀ h∈J,(x-h).natAbs≤N ∧ (y-h).natAbs≤N)
    (divs : ∀ m : ℕ, 0 < m → m≤N^2 → (m.divisors.card:ℝ)≤C)
    (membership : ∀ n∈V, (n:ℤ)∣x*y ∧ ¬(n:ℤ)∣x ∧ ¬(n:ℤ)∣y ∧ ∃ h∈J,(n:ℤ)∣h) :
    (V.card:ℝ)≤J.card*C := by
  let m (h : ℤ) := (x-h).natAbs*(y-h).natAbs
  have sub : V ⊆ J.biUnion (fun h => (m h).divisors) := by
    intro n hn
    obtain ⟨prod,xn,yn,h,hJ,hd⟩ := membership n hn
    have div : (n:ℤ) ∣ (x-h)*(y-h) := by
      rw [show (x-h)*(y-h)=x*y-h*(x+y-h) by ring]
      exact dvd_sub prod (hd.trans (dvd_mul_right _ _))
    have nz : m h≠0 := by
      apply Nat.mul_ne_zero
      · apply Int.natAbs_ne_zero.mpr
        exact sub_ne_zero.mpr (fun e => xn (e ▸ hd))
      · apply Int.natAbs_ne_zero.mpr
        exact sub_ne_zero.mpr (fun e => yn (e ▸ hd))
    exact mem_biUnion.mpr ⟨h,hJ,Nat.mem_divisors.mpr ⟨by simpa only [m,Int.natAbs_natCast,Int.natAbs_mul] using Int.natAbs_dvd_natAbs.mpr div,nz⟩⟩
  have count := (card_le_card sub).trans card_biUnion_le
  calc _ ≤ ∑ h∈J, ((m h).divisors.card:ℝ) := by exact_mod_cast count
       _ ≤ ∑ _h∈J, C := by
         apply sum_le_sum
         intro h hJ
         by_cases z : m h=0
         · simpa [z] using cp
         exact divs _ (Nat.pos_of_ne_zero z) (by simpa [m,pow_two] using Nat.mul_le_mul (width h hJ).1 (width h hJ).2)
       _ = _ := by simp
end Trapped299

open Real Filter Finset
open scoped Classical Topology
namespace FirstForce299
open OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1_H3_R1
noncomputable abbrev H (N:ℕ) := exp ((9/5:ℝ)*log N/w N)
lemma qmass : ∀ᶠ N : ℕ in atTop, ∀ Q : Finset ℕ,
    (∀ q∈Q, IsPrimePow q ∧ q≤N) → mass Q≤501/500*w N := by
  obtain ⟨b,hb⟩ := Mass377.natMertens
  obtain ⟨C,hC⟩ := Rough299.nonsimple
  filter_upwards [hb.eventually_lt_const (show b<b+1 by linarith),Param299.wtop.eventually_gt_atTop (500*(b+1+C))] with N pr big
  intro Q qQ
  let P := Q.filter Nat.Prime
  have sub : P ⊆ Nat.primesLE N := fun q hq => Nat.mem_primesLE.mpr ⟨(qQ q (mem_filter.mp hq).1).2,(mem_filter.mp hq).2⟩
  have p := sum_le_sum_of_subset_of_nonneg (f:=fun q : ℕ => (1:ℝ)/q) sub (fun _ _ _ => by positivity)
  have c := hC N (Q \ P) (fun q hq => ⟨(qQ q (mem_sdiff.mp hq).1).1,
    fun pp => (mem_sdiff.mp hq).2 (mem_filter.mpr ⟨(mem_sdiff.mp hq).1,pp⟩),(qQ q (mem_sdiff.mp hq).1).2⟩)
  have eq := sum_sdiff (f:=fun q : ℕ => (1:ℝ)/q) (show P⊆Q from filter_subset _ _)
  dsimp only [mass,w,Param299.w] at *
  linarith
lemma small_errors (z : ℕ) : ∀ᶠ N : ℕ in atTop,
    0<log (N:ℝ) ∧ 4≤w N ∧ 1≤K N ∧ K N≤N ∧ 0<M N ∧
    1/M N ≤ 1/(z+1:ℝ) ∧
    1/log N + (e N/2)*(501/500*w N) + 2*K N*H N/M N < (1/(z+1:ℝ))/3 := by
  have et := (tendsto_exp_div_pow_atTop 1).comp Param299.wtop
  have ht : Tendsto (fun N : ℕ => log N/w N) atTop atTop := by
    apply et.congr'
    filter_upwards [Mass377.logTop.eventually_gt_atTop 0] with N hp
    simp [w,Param299.w,hp,exp_log]
  have neg := tendsto_exp_neg_atTop_nhds_zero.comp (ht.const_mul_atTop (by norm_num : (0:ℝ)<1/5))
  have short : Tendsto (fun N : ℕ => 2*K N*H N/M N) atTop (𝓝 0) := by
    have f := neg.const_mul 2
    rw [mul_zero] at f
    apply f.congr'
    filter_upwards [eventually_gt_atTop 0] with N hn
    have np : (0:ℝ)<N := by exact_mod_cast hn
    have mp : 0<M N := rpow_pos_of_pos np _
    dsimp only [Function.comp_apply,K,H]
    rw [rpow_def_of_pos np]
    have eq : -(1/5*(log (N:ℝ)/w N)) = log N*(-2/w N)+(9/5:ℝ)*log N/w N := by ring
    rw [eq,exp_add]
    field_simp
  have lo : Tendsto (fun N : ℕ => 1/log (N:ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop Mass377.logTop
  have mid : Tendsto (fun N : ℕ => e N/2*(501/500*w N)) atTop (𝓝 0) := by
    have t := Param299.eMass.const_mul (501/1000:ℝ)
    rw [mul_zero] at t
    apply t.congr (fun N => ?_)
    change 501/1000*(e N*w N)=_
    ring
  have err := (lo.add mid).add short
  simp only [zero_add] at err
  have mt : Tendsto (fun N => 1/M N) atTop (𝓝 0) := tendsto_const_nhds.div_atTop Param299.Mtop
  filter_upwards [eventually_ge_atTop 1,Mass377.logTop.eventually_gt_atTop 0,
    Param299.wtop.eventually_ge_atTop 4,mt.eventually_lt_const (show 0<1/(z+1:ℝ) by positivity),
    err.eventually_lt_const (show 0<(1/(z+1:ℝ))/3 by positivity)] with N hn hb hw hM small
  have nr : (1:ℝ)≤N := by exact_mod_cast hn
  have np : (0:ℝ)<N := by linarith
  have keq : K N = (N:ℝ)^(1-3/w N) := by rw [K,M,←rpow_add np]; congr 1; ring
  change 4≤w N at hw
  have wp : 0<w N := by linarith
  have lower : 1≤K N := by rw [keq]; apply one_le_rpow nr; have := (div_le_one wp).mpr (by linarith : 3≤w N); linarith
  have upper : K N≤N := by
    rw [keq]; conv_rhs => rw [← rpow_one (N:ℝ)]
    exact rpow_le_rpow_of_exponent_le nr (by linarith [div_nonneg (by norm_num : (0:ℝ)≤3) wp.le])
  exact ⟨hb,hw,lower,upper,rpow_pos_of_pos np _,hM.le,small⟩
end FirstForce299

open Real Finset Filter
open scoped Classical Topology
namespace FirstForce299
open OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1_H3_R1
lemma mono_mass {A B : Finset ℕ} (h : A⊆B) : mass A≤ mass B :=
  sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => by positivity)
lemma union_mass (A B : Finset ℕ) : mass (A∪B) ≤ mass A+mass B := by
  have e : mass (A∪B)+mass (A∩B)=mass A+mass B := sum_union_inter
  have pos : 0≤ mass (A∩B) := sum_nonneg (fun _ _ => by positivity)
  linarith
lemma biMass {α : Type*} (s : Finset α) (f : α→Finset ℕ) :
    mass (s.biUnion f) ≤ ∑ a∈s,mass (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mass]
  | insert a s ha ih =>
    rw [biUnion_insert,sum_insert ha]
    exact (union_mass _ _).trans (add_le_add_right ih _)
lemma pair_overlap : ∀ᶠ N : ℕ in atTop, ∀ (Q : Finset ℕ), (∀ q∈Q, IsPrimePow q) →
    ∀ x y : ℤ, x≠y → |(x:ℝ)-y|≤N → mass (pix Q x ∩ pix Q y)<w N/500 := by
  filter_upwards [TinyOverlap299.overlap] with N ov
  intro Q qQ x y ne dist
  have nz : 0<(x-y).natAbs := Int.natAbs_pos.mpr (sub_ne_zero.mpr ne)
  have le : (x-y).natAbs≤N := by exact_mod_cast (show ((x-y).natAbs:ℝ)≤N by simpa using dist)
  have e := ov (x-y).natAbs nz le (pix Q x∩pix Q y) (by
    intro q hq
    obtain ⟨a,b⟩ := mem_inter.mp hq
    have dvd := dvd_sub (mem_filter.mp a).2 (mem_filter.mp b).2
    exact ⟨qQ q (mem_filter.mp a).1,by simpa using (Int.natAbs_dvd_natAbs.mpr dvd)⟩)
  change mass _ < (1/500:ℝ)*w N at e
  linarith
lemma two_heavy {Q : Finset ℕ} {W : ℝ} {f : ℤ→Finset ℕ} (wp : 0<W)
    (J : Finset ℤ) (cap : mass Q≤501/500*W) (sub : ∀ z, f z⊆Q)
    (overlapBound : ∀ x∈J, ∀ y∈J, x≠y → mass (f x∩f y) < W/500)
    {x y : ℤ} (xJ : x∈J) (yJ : y∈J) (xy : x≠y)
    (xh : 35/100*W≤ mass (f x)) (yh : 35/100*W≤ mass (f y)) :
    mass (f x)≤2/3*W ∧ mass (f y)≤2/3*W ∧
      ∀ z∈J, 35/100*W≤ mass (f z) → z=x ∨ z=y := by
  have ux := mono_mass (union_subset (sub x) (sub y))
  have e : mass (f x∪f y)+mass (f x∩f y)=mass (f x)+mass (f y) := sum_union_inter
  have ov := overlapBound x xJ y yJ xy
  refine ⟨by linarith,by linarith,?_⟩
  intro z zJ zh
  by_contra! both
  have a := overlapBound z zJ x xJ both.1
  have b := overlapBound z zJ y yJ both.2
  have e2 : mass (f z ∪ (f x∪f y))+mass (f z ∩ (f x∪f y))=mass (f z)+mass (f x∪f y) := sum_union_inter
  have t := mono_mass (union_subset (sub z) (union_subset (sub x) (sub y)))
  rw [inter_union_distrib_left] at e2
  linarith [union_mass (f z∩f x) (f z∩f y)]
end FirstForce299

open Real Finset
open scoped Classical
namespace FirstForce299
open OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1_H3_R1
lemma card_interval {t K : ℝ} (hK : 1≤K) : ((I t K).card:ℝ)≤2*K := by
  have ne : ⌈t-K/2⌉ ≤ ⌊t+K/2⌋ := by
    apply Int.le_floor.mpr
    linarith [Int.ceil_lt_add_one (t-K/2)]
  rw [I,Int.card_Icc]
  have p : 0≤⌊t+K/2⌋+1-⌈t-K/2⌉ := by omega
  rw [←Int.cast_natCast (R:=ℝ),Int.toNat_of_nonneg p]
  push_cast
  linarith [Int.le_ceil (t-K/2),Int.floor_le (t+K/2)]
lemma three_parts {N : ℕ} {A : Finset ℕ} (t : ℝ) (x y : ℤ)
    (hK : 1≤K N) (kN : K N≤N) (mp : 0<M N) (bp : 0<log (N:ℝ))
    (ha : 0∉A) (reg : ∀ n∈A, regular N n)
    (xJ : x∈I t (K N)) (yJ : y∈I t (K N))
    (smooth : ∀ m : ℕ, 0 < m → m≤N^2 → (m.divisors.card:ℝ)≤H N)
    (cap : mass (powers A)≤501/500*w N)
    (bad : ((A.filter fun n => ¬hits (I t (K N)) n).card:ℝ) < M N/log N)
    (qsplit : ∀ q∈E N A (A.filter (hits (I t (K N)))), (q:ℤ)∣x ∨ (q:ℤ)∣y) :
    mass A ≤ mass (A.filter fun n : ℕ => (n:ℤ)∣x)+mass (A.filter fun n : ℕ => (n:ℤ)∣y)+
      (1/log N+(e N/2)*(501/500*w N)+2*K N*H N/M N) := by
  classical
  let J := I t (K N)
  let U := A.filter (hits J)
  let O := A.filter (fun n => ¬hits J n)
  let X := A.filter fun n : ℕ => (n:ℤ)∣x
  let Y := A.filter fun n : ℕ => (n:ℤ)∣y
  let Q := powers A
  let D := Q \ E N A U
  let B := D.biUnion (part U)
  let V := (U \ B).filter fun n : ℕ => ¬(n:ℤ)∣x ∧ ¬(n:ℤ)∣y
  have ep : 0<e N := rpow_pos_of_pos bp _
  have ua : U⊆A := filter_subset _ _
  have ua' : V⊆U := (filter_subset _ _).trans sdiff_subset
  have boundCard (s : Finset ℕ) (hs : s⊆A) : mass s ≤ s.card/M N := by
    calc _ ≤ ∑ _n∈s, 1/M N := sum_le_sum fun n hn => one_div_le_one_div_of_le mp (reg n (hs hn)).1
         _ = _ := by simp [div_eq_mul_inv]
  have outside : mass O ≤ 1/log N := by
    have eq := (div_lt_div_iff_of_pos_right mp).mpr bad
    calc _ ≤ O.card/M N := boundCard _ (filter_subset _ _)
         _ ≤ _ := by
           apply eq.le.trans
           have e : (M N/log N)/M N=1/log N := by field_simp
           exact e.le
  have low : mass B ≤ (e N/2)*(501/500*w N) := by
    apply (biMass D (part U)).trans
    calc _ ≤ ∑ q∈D, (e N/2)*((1:ℝ)/q) := by
           apply sum_le_sum
           intro q hq
           obtain ⟨qQ,no⟩ := mem_sdiff.mp hq
           have p : (0:ℝ)<q := by exact_mod_cast (power_mem qQ).1.pos
           have le : ∑ n∈part U q,(q:ℝ)/n < e N/2 := lt_of_not_ge (fun le => no (mem_filter.mpr ⟨qQ,le⟩))
           have eq : ∑ n∈part U q,(q:ℝ)/n = (q:ℝ)*mass (part U q) := by
             rw [mass,mul_sum]; apply sum_congr rfl; intro n hn; ring
           rw [eq] at le
           rw [mul_one_div,le_div_iff₀ p,mul_comm]
           exact le.le
         _ ≤ _ := by
           rw [←mul_sum]
           exact mul_le_mul_of_nonneg_left ((mono_mass (sdiff_subset : D⊆Q)).trans cap) (by positivity)
  have width (h : ℤ) (hh : h∈J) : (x-h).natAbs≤N ∧ (y-h).natAbs≤N := by
    constructor
    · exact_mod_cast (show ((x-h).natAbs:ℝ)≤N by simpa using (distance x h xJ hh).trans kN)
    · exact_mod_cast (show ((y-h).natAbs:ℝ)≤N by simpa using (distance y h yJ hh).trans kN)
  have membership (n : ℕ) (hn : n∈V) :
      (n:ℤ)∣x*y ∧ ¬(n:ℤ)∣x ∧ ¬(n:ℤ)∣y ∧ ∃ h∈J,(n:ℤ)∣h := by
    obtain ⟨inU,notB⟩ := mem_sdiff.mp (mem_filter.mp hn).1
    have nA := ua inU
    have nz : n≠0 := fun e => ha (e ▸ nA)
    refine ⟨Trapped299.product_dvd (Nat.pos_of_ne_zero nz) ?_,(mem_filter.mp hn).2.1,(mem_filter.mp hn).2.2,(mem_filter.mp inU).2⟩
    intro p pm
    let q := p^n.factorization p
    have pr := Nat.prime_of_mem_primeFactors pm
    have dv : q∣n := Nat.ordProj_dvd n p
    have cp : Nat.Coprime q (n/q) := (Nat.coprime_ordCompl pr nz).pow_left _
    have qQ : q∈Q := mem_biUnion.mpr ⟨n,nA,mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨dv,nz⟩,
      pr.isPrimePow.pow (Finsupp.mem_support_iff.mp pm),cp⟩⟩
    apply qsplit q
    by_contra no
    exact notB (mem_biUnion.mpr ⟨q,mem_sdiff.mpr ⟨qQ,no⟩,mem_filter.mpr ⟨inU,dv,cp⟩⟩)
  have trapped := Trapped299.trapped V J (exp_pos _).le width smooth membership
  have massV : mass V≤2*K N*H N/M N := by
    exact (boundCard V (ua'.trans ua)).trans (div_le_div_of_nonneg_right
      (trapped.trans (mul_le_mul_of_nonneg_right (card_interval (t:=t) hK) (exp_pos _).le)) mp.le)
  have sub : A⊆(((X∪Y)∪O)∪B)∪V := by
    intro n hn
    by_cases hx : (n:ℤ)∣x
    · exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hn,hx⟩))))
    by_cases hy : (n:ℤ)∣y
    · exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hn,hy⟩))))
    by_cases hit : hits J n
    · by_cases nb : n∈B
      · exact mem_union_left _ (mem_union_right _ nb)
      · exact mem_union_right _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_filter.mpr ⟨hn,hit⟩,nb⟩,hx,hy⟩)
    · exact mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hn,hit⟩)))
  change mass A≤ mass X+mass Y+_
  linarith [mono_mass sub,union_mass X Y,union_mass (X∪Y) O,union_mass (X∪Y∪O) B,union_mass (X∪Y∪O∪B) V]
end FirstForce299

open Real Filter Finset
open scoped Classical Topology
namespace FirstForce299
open OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1_H3_R1
lemma rare_member {N : ℕ} {A : Finset ℕ} {t : ℝ} (q : ℕ) (hq : q∈powers A)
    (hp : 0<log (N:ℝ)) (mp : 0<M N) (reg : ∀ n∈A,regular N n)
    (bal : e N ≤ ∑ n∈part A q, (q:ℝ)/n)
    (rare : ((((part A q).filter (fun n => ¬hits (I t (K N)) n)).card):ℝ) < L N/q) :
    q∈E N A (A.filter (hits (I t (K N)))) := by
  let J := I t (K N)
  let B := (part A q).filter fun n => ¬hits J n
  have qp : (0:ℝ)<q := by exact_mod_cast (power_mem hq).1.pos
  have small : (∑ n∈B,(q:ℝ)/n) ≤ e N/2 := by
    have rem := sum_le_card_nsmul B (fun n : ℕ => (q:ℝ)/n) ((q:ℝ)/M N) (by
      intro n hn
      exact div_le_div_of_nonneg_left qp.le mp (reg n (mem_filter.mp (mem_filter.mp hn).1).1).1)
    rw [nsmul_eq_mul] at rem
    calc _ ≤ (B.card:ℝ)*((q:ℝ)/M N) := rem
         _ ≤ (L N/q)*((q:ℝ)/M N) := mul_le_mul_of_nonneg_right rare.le (by positivity)
         _ = _ := by
           rw [L,e,rpow_neg hp.le]
           field_simp [mp.ne',qp.ne',(rpow_pos_of_pos hp (1/100:ℝ)).ne']
  have spl := sum_filter_add_sum_filter_not (s:=part A q) (f:=fun n : ℕ => (q:ℝ)/n) (hits J)
  have eq : (part A q).filter (hits J)=part (A.filter (hits J)) q := by ext n; simp [part,and_comm,and_left_comm,and_assoc]
  rw [eq] at spl
  change _+(∑ n∈B,(q:ℝ)/n)=_ at spl
  exact mem_filter.mpr ⟨hq,by linarith⟩
lemma result : OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1.H2 := by
  classical
  intro z
  filter_upwards [small_errors z,qmass,pair_overlap,heavy,Wigert299.divisor_bound] with N par qcap pairs heav divider
  obtain ⟨bp,wp,k1,kN,mp,mz,errs⟩ := par
  intro A d dp dz az an reg bal
  let Q := powers A
  have qQ (q : ℕ) (hq : q∈Q) : IsPrimePow q ∧ q≤N := by
    obtain ⟨p,n,hn,nz,dv,_⟩ := power_mem hq
    exact ⟨p,(Nat.le_of_dvd (Nat.pos_of_ne_zero nz) dv).trans (mem_range.mp (an hn)).le⟩
  have cap := qcap Q qQ
  have dr : (0:ℝ)<d := by exact_mod_cast dp
  have lower : 1/(z+1:ℝ)≤ mass A := by
    have le : 1/(z+1:ℝ)≤1/(d:ℝ) := one_div_le_one_div_of_le dr (by exact_mod_cast (Nat.le_succ_of_le dz))
    have b := bal.2.1
    change 2/(d:ℝ)-1/M N≤ mass A at b
    rw [show (2:ℝ)/d=2*(1/d) by ring] at b
    linarith
  by_cases witness : ∃ B ⊆ A, mass A ≤ 3*mass B ∧ mass (powers B) ≤ (2/3:ℝ)*w N
  · exact Or.inr witness
  left
  intro t
  let J := I t (K N)
  let U := A.filter (hits J)
  let R := E N A U
  let X (x : ℤ) := A.filter fun n : ℕ => (n:ℤ)∣x
  let f := pix Q
  by_cases wide : M N/log N ≤ ((A.filter fun n => ¬hits J n).card:ℝ)
  · exact Or.inl (by simpa [hits,J,I,K,M,w,not_exists] using wide)
  right
  have ine : J.Nonempty := by
    refine ⟨⌈t-K N/2⌉,mem_Icc.mpr ⟨le_rfl,Int.le_floor.mpr ?_⟩⟩
    linarith [Int.ceil_lt_add_one (t-K N/2)]
  have rare (q : ℕ) (hq : q∈Q)
      (h : ((((part A q).filter fun n : ℕ => ∀ x∈J,¬(n:ℤ)∣x).card):ℝ)<L N/q) : q∈R :=
    rare_member q hq bp mp reg (bal.2.2.2 q hq) (by simpa [hits,J,I,not_exists] using h)
  have per (q : ℕ) (hq : q∈R) : ∃ x∈J,(q:ℤ)∣x ∧ (35/100:ℝ)*w N≤ mass (f x) := heav A t az an reg q hq
  let pick (q : ℕ) := if hq : q∈R then (per q hq).choose else 0
  have chosen (q : ℕ) (hq : q∈R) : pick q ∈ J ∧ (q:ℤ)∣pick q ∧ (35/100:ℝ)*w N≤ mass (f (pick q)) := by
    simpa only [pick,dif_pos hq] using (per q hq).choose_spec
  by_cases ex : R.Nonempty
  · obtain ⟨q,qe⟩ := ex
    let x := pick q
    have hx := chosen q qe
    refine ⟨x,hx.1,?_⟩
    intro r rq rr
    have re := rare r rq rr
    have hy := chosen r re
    let y := pick r
    by_contra no
    have xy : x≠y := fun eq => no (eq ▸ hy.2.1)
    have overB (a : ℤ) (aJ : a∈J) (b : ℤ) (bJ : b∈J) (ab : a≠b) : mass (f a∩f b)<w N/500 :=
      pairs Q (fun q h => (qQ q h).1) a b ab ((distance a b aJ bJ).trans kN)
    obtain ⟨cx,cy,all⟩ := two_heavy (Q:=Q) (f:=f) (by linarith : 0<w N) J cap (fun _ => filter_subset _ _)
       overB hx.1 hy.1 xy hx.2.2 hy.2.2
    have ps : ∀ p∈R,(p:ℤ)∣x ∨ (p:ℤ)∣y := by
      intro p pe
      have c := chosen p pe
      rcases all (pick p) c.1 c.2.2 with h|h
      · exact Or.inl (by change (p:ℤ)∣pick q; rw [←h]; exact c.2.1)
      · exact Or.inr (by change (p:ℤ)∣pick r; rw [←h]; exact c.2.1)
    have part := three_parts t x y k1 kN mp bp az reg hx.1 hy.1 divider cap (lt_of_not_ge wide) ps
    have smallMass (a : ℤ) : mass (powers (X a)) ≤ mass (f a) := by
      apply mono_mass
      intro p hp
      obtain ⟨pr,n,hn,nz,pn,cp⟩ := power_mem hp
      obtain ⟨na,ax⟩ := mem_filter.mp hn
      refine mem_filter.mpr ⟨mem_biUnion.mpr ⟨n,na,mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨pn,nz⟩,pr,cp⟩⟩,?_⟩
      exact (show (p:ℤ)∣n by exact_mod_cast pn).trans ax
    have thin (a : ℤ) (ca : mass (f a)≤2/3*w N) : 3*mass (X a)< mass A := by
      apply lt_of_not_ge
      intro success
      exact witness ⟨X a,filter_subset _ _,success,(smallMass a).trans ca⟩
    change mass A ≤ mass (X x)+mass (X y)+_ at part
    linarith only [part,thin x cx,thin y cy,lower,errs]
  · obtain ⟨x,hx⟩ := ine
    exact ⟨x,hx,fun q hq hr => False.elim (ex ⟨q,rare q hq hr⟩)⟩
end FirstForce299

theorem OMA.solution : OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1.H2 := FirstForce299.result
