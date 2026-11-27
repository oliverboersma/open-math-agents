import OMAReductions.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1
/-!
This adapts the common-divisor and cofactor argument for Lemma 5.4 in the
Bloom formalization by Bhavik Mehta and Thomas Bloom, with Eric Rodriguez
on src/aux_lemmas.lean, b-mehta/unit-fractions at commit
10ef71a300cf29e5f19beb2bbc723a035a0678de, src/aux_lemmas.lean and
src/main_results.lean. Copyright (c) 2021 Bhavik Mehta, Thomas Bloom.
All rights reserved. Used under Apache-2.0.

The bound on the number of distinct prime factors is adapted from Will Howe,
H0W4RD-dev/croot-unit-fractions at c58a7d45114c3af27e6abb19dcfca9d82b49b4a1,
Prop1.lean, under Apache-2.0. The Mertens bounds are from the merged Erdős
377 argument by @marcusbuffett, with the first estimate by @senamakel.

The common prime-power mass at two distinct interval points is negligible:
their difference is at most N, its large prime factors are few, and Mertens
bounds the small ones. A cofactor family supplies a heavy point for each
rare prime power. Its common divisor exceeds the interval width, hence
every denominator from the family hits the same point. The total prime-power
mass bound forces these heavy points to coincide.
-/
open Filter Finset Real Asymptotics
open scoped Classical Topology
namespace OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1_H3_R1
/-- Extract a common divisor larger than the interval from a local family.
The coprime cofactors carry enough reciprocal mass and retain most prime factors. -/
def H1 : Prop := 
  let w (N : ℕ) := log (log N)
  let e (N : ℕ) := (log N)^(-(1/100:ℝ))
  let M (N : ℕ) := (N:ℝ)^(1-1/w N)
  let K (N : ℕ) := M N*(N:ℝ)^(-2/w N)
  let mass (A : Finset ℕ) := ∑ n ∈ A, (1:ℝ)/n
  let part (A : Finset ℕ) (q : ℕ) := A.filter fun n => q∣n ∧ Nat.Coprime q (n/q)
  let Regular (N n : ℕ) : Prop := M N ≤ n ∧
    (∀ q : ℕ, IsPrimePow q → q∣n → (q:ℝ) ≤ (N:ℝ)^(1-8/w N)) ∧
    (99/100:ℝ)*w N ≤ n.primeFactors.card ∧ (n.primeFactors.card:ℝ) ≤ 2*w N
  ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℕ) (q : ℕ), 0∉A → A⊆range N →
  (∀ n ∈ A, Regular N n) → IsPrimePow q → e N/2 ≤ ∑ n ∈ part A q,(q:ℝ)/n →
  ∃ (D : ℕ) (C : Finset ℕ), K N < D ∧ q∣D ∧
    (log N)^(-(1/99:ℝ)) ≤ mass C ∧
    (∀ m ∈ C, D*m ∈ A ∧ Nat.Coprime m D ∧
      (1-2/99:ℝ)*w N ≤ m.primeFactors.card ∧ (m.primeFactors.card:ℝ) ≤ 2*w N)

/-- A family of cofactors of sufficient mass and with almost the normal
number of distinct prime factors has large prime-power reciprocal mass. -/
def H2 : Prop := 
  let w (N : ℕ) := log (log N)
  let mass (A : Finset ℕ) := ∑ n ∈ A, (1:ℝ)/n
  let powers (A : Finset ℕ) := A.biUnion fun n =>
    n.divisors.filter fun q => IsPrimePow q ∧ Nat.Coprime q (n/q)
  ∀ᶠ N : ℕ in atTop, ∀ C : Finset ℕ,
  (log N)^(-(1/99:ℝ)) ≤ mass C →
  (∀ m ∈ C, (1-2/99:ℝ)*w N ≤ m.primeFactors.card ∧ (m.primeFactors.card:ℝ) ≤ 2*w N) →
  (35/100:ℝ)*w N ≤ mass (powers C)

lemma common_prime_powers : ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, 0 < m → m≤N → ∀ P : Finset ℕ,
    (∀ q ∈ P, IsPrimePow q ∧ q∣m) → (∑ q ∈ P,(1:ℝ)/q) < (1/30:ℝ)*log (log N) := by
  classical
  have log_factorial_eq_sum (N : ℕ) :
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

  have div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (N : ℕ) :
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

  have real_div_sub_one_le_nat_div (N p : ℕ) (hp : 0 < p) :
      (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := by
    have h := Nat.lt_div_mul_add (a := N) hp
    have hp' : (0 : ℝ) < p := by exact_mod_cast hp
    have h2 : (N : ℝ) < ((N / p : ℕ) : ℝ) * p + p := by exact_mod_cast h
    rw [div_sub_one hp'.ne', div_le_iff₀ hp']
    linarith

  have log_factorial_le (N : ℕ) : Real.log (N.factorial : ℝ) ≤ N * Real.log N := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    rw [← Real.log_pow]
    apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos N)
    exact_mod_cast Nat.factorial_le_pow N

  have log_factorial_ge (N : ℕ) : N * Real.log N - N ≤ Real.log (N.factorial : ℝ) := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    have h := Real.pow_div_factorial_le_exp (N : ℝ) (Nat.cast_nonneg N) N
    have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
    have hNp : (0 : ℝ) < (N : ℝ) ^ N := by positivity
    have h2 := Real.log_le_log (by positivity) h
    rw [Real.log_exp, Real.log_div hNp.ne' hf.ne', Real.log_pow] at h2
    linarith


  have summable_log_div_mul_sub_one :
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


  have sum_log_div_le_nat (N : ℕ) :
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


  let primePowerConst : ℝ := ∑' n : ℕ, Real.log n / ((n : ℝ) * ((n : ℝ) - 1))

  have sum_log_div_mul_sub_one_le (s : Finset ℕ) :
      ∑ p ∈ s, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ primePowerConst := by
    apply summable_log_div_mul_sub_one.sum_le_tsum s
    intro n _
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
      apply div_nonneg (Real.log_nonneg (by linarith))
      nlinarith


  have sum_log_div_ge_nat (N : ℕ) :
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


  have primePowerConst_nonneg : 0 ≤ primePowerConst := by
    have := sum_log_div_mul_sub_one_le ∅
    simpa using this


  let mertens1Const : ℝ := Real.log 4 + 1 + primePowerConst

  have abs_sum_log_div_sub_log_le_nat (N : ℕ) :
      |∑ p ∈ Nat.primesLE N, Real.log p / p - Real.log N| ≤ mertens1Const := by
    have h1 := sum_log_div_le_nat N
    have h2 := sum_log_div_ge_nat N
    have h3 := primePowerConst_nonneg
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    rw [abs_le]; unfold mertens1Const; constructor <;> linarith

  have log_le_log_floor_add (x : ℝ) (hx : 1 ≤ x) :
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


  have abs_sum_log_div_sub_log_le (x : ℝ) (hx : 1 ≤ x) :
      |∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p - Real.log x| ≤ mertens1Const + Real.log 2 := by
    have h := abs_sum_log_div_sub_log_le_nat ⌊x⌋₊
    obtain ⟨h1, h2⟩ := log_le_log_floor_add x hx
    have h3 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    rw [abs_le] at h ⊢
    constructor <;> linarith [h.1, h.2]


  have mertens1 : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      |∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p - Real.log x| ≤ C :=
    ⟨mertens1Const + Real.log 2, fun x hx => abs_sum_log_div_sub_log_le x (by linarith)⟩

  have sum_succ_eq (N : ℕ) (f : ℕ → ℝ) :
      ∑ p ∈ Nat.primesLE (N + 1), f p =
        (∑ p ∈ Nat.primesLE N, f p) + if (N + 1).Prime then f (N + 1) else 0 := by
    rw [Nat.primesLE_succ]
    split_ifs with h
    · rw [Finset.sum_insert, add_comm]
      intro hm
      have := (Nat.mem_primesLE.mp hm).1
      omega
    · simp

  have recip_step (N : ℕ) :
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



  have abs_log_sub_log_sub_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ a + 1) :
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


  let mertensG (N : ℕ) : ℝ :=
    (∑ p ∈ Nat.primesLE N, (1 : ℝ) / p) - Real.log (Real.log N) -
      ((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N

  have mertensG_step (N : ℕ) (hN : 2 ≤ N) :
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


  let S (x : ℝ) := ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1:ℝ)/p
  have Cpos : 0 ≤ mertens1Const := by
    exact (abs_nonneg _).trans (abs_sum_log_div_sub_log_le_nat 2)
  have Gdiff (m n : ℕ) (hm : 2 ≤ m) (hn : m ≤ n) :
      |mertensG n - mertensG m| ≤ (mertens1Const+1)*(1/log m-1/log n) := by
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      calc |mertensG (n+1)-mertensG m| =
          |(mertensG (n+1)-mertensG n)+(mertensG n-mertensG m)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
        _ ≤ _ := add_le_add (mertensG_step n (hm.trans hn)) ih
        _ = _ := by ring
  have logTop : Tendsto (fun n : ℕ => log n) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have natMertens : ∃ b : ℝ, Tendsto (fun n : ℕ => (∑ p ∈ Nat.primesLE n, (1:ℝ)/p) -
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
  have realMertens : ∃ b : ℝ, Tendsto (fun x : ℝ => S x-log (log x)) atTop (𝓝 b) := by
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
  let w (N : ℕ) := log (log N)
  have wtop : Tendsto w atTop atTop := tendsto_log_atTop.comp logTop
  have geom (p : ℕ) (hp : 2≤p) (N : ℕ) :
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
  let mass (A : Finset ℕ) := ∑ n ∈ A, (1:ℝ)/n
  have pp_bound (m : ℕ) (hm : 0 < m) (P : Finset ℕ) (hP : ∀ q ∈ P, IsPrimePow q ∧ q∣m) :
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
            geom p (Nat.prime_of_mem_primeFactors hp).two_le m
         _ = _ := by simp only [mass,mul_sum]; congr 1; ext; ring
  have card_le_log {s : ℕ} (hs : 0 < s) :
      (s.primeFactors.card : ℝ) ≤ log s / log 2 := by
    have h1 : 2 ^ s.primeFactors.card ≤ ∏ p ∈ s.primeFactors, p :=
      pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    have h2 := Nat.le_of_dvd hs (Nat.prod_primeFactors_dvd s)
    have h3 : ((2 : ℝ) ^ s.primeFactors.card) ≤ s := by exact_mod_cast h1.trans h2
    rw [le_div_iff₀ (log_pos one_lt_two)]
    have := log_le_log (by positivity) h3
    rwa [log_pow] at this
  have overlap : ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, 0 < m → m≤N → ∀ P : Finset ℕ,
      (∀ q ∈ P, IsPrimePow q ∧ q∣m) → mass P < (1/30:ℝ)*w N := by
    obtain ⟨b,hb⟩ := realMertens
    have hg := (tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp wtop
    filter_upwards [(hb.comp logTop).eventually_lt_const (show b<b+1 by linarith),
      hg.eventually_lt_const (by norm_num : (0:ℝ)<1/200),
      wtop.eventually_gt_atTop (200*(|b|+1+1/log 2)),
      logTop.eventually_gt_atTop 1] with N hprime hratio hw hN
    intro m hm hmN P hP
    let X := log (N:ℝ)
    let Q := m.primeFactors.filter fun p : ℕ => (p:ℝ)≤X
    let R := m.primeFactors \ Q
    have xp : 0<X := by dsimp [X]; linarith
    have p2 : 0<log 2 := log_pos one_lt_two
    have wpos : 0<w N := by linarith [abs_nonneg b,one_div_pos.mpr p2]
    change S X - log (w N) < b+1 at hprime
    simp only [Function.comp_apply,pow_one,one_mul,add_zero] at hratio
    have small := (div_lt_iff₀ wpos).mp hratio
    have sub : Q ⊆ Nat.primesLE ⌊X⌋₊ := by
      intro p hp
      obtain ⟨hp,le⟩ := mem_filter.mp hp
      exact Nat.mem_primesLE.mpr ⟨Nat.le_floor le,Nat.prime_of_mem_primeFactors hp⟩
    have lo : mass Q ≤ S X := sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => by positivity)
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
  exact overlap

theorem main : H1 → H2 → OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1.H3 := by
  classical
  intro cof entropy
  let w (N : ℕ) := log (log N)
  let e (N : ℕ) := (log N)^(-(1/100:ℝ))
  let M (N : ℕ) := (N:ℝ)^(1-1/w N)
  let K (N : ℕ) := M N*(N:ℝ)^(-2/w N)
  let L (N : ℕ) := M N/(2*(log N)^(1/100:ℝ))
  let mass (A : Finset ℕ) := ∑ n ∈ A, (1:ℝ)/n
  let powers (A : Finset ℕ) := A.biUnion fun n =>
    n.divisors.filter fun q => IsPrimePow q ∧ Nat.Coprime q (n/q)
  let part (A : Finset ℕ) (q : ℕ) := A.filter fun n => q∣n ∧ Nat.Coprime q (n/q)
  let Regular (N n : ℕ) : Prop := M N ≤ n ∧
    (∀ q : ℕ, IsPrimePow q → q∣n → (q:ℝ) ≤ (N:ℝ)^(1-8/w N)) ∧
    (99/100:ℝ)*w N ≤ n.primeFactors.card ∧ (n.primeFactors.card:ℝ) ≤ 2*w N
  have power_mem {A : Finset ℕ} {q : ℕ} (h : q ∈ powers A) :
      IsPrimePow q ∧ ∃ n ∈ A, n ≠ 0 ∧ q∣n ∧ Nat.Coprime q (n/q) := by
    obtain ⟨n,hn,hq⟩ := mem_biUnion.mp h
    obtain ⟨dv,pp,cp⟩ := mem_filter.mp hq
    obtain ⟨hd,h0⟩ := Nat.mem_divisors.mp dv
    exact ⟨pp,n,hn,h0,hd,cp⟩
  intro z
  filter_upwards [cof,entropy,common_prime_powers,
    (tendsto_log_atTop.comp (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))).eventually_ge_atTop 4,
    (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_gt_atTop 0,
    eventually_ge_atTop 1] with N co en ov hw hlog hN
  change 0 < log (N:ℝ) at hlog
  intro A d hd hdz a0 aN reg bal total t
  let I := Icc (⌈t-K N/2⌉:ℤ) ⌊t+K N/2⌋
  let hit (n : ℕ) := ∃ x ∈ I, (n:ℤ)∣x
  let U := A.filter hit
  let rare (q : ℕ) := ((((part A q).filter fun n => ¬hit n).card):ℝ)<L N/q
  let Q := powers A
  let F (x : ℤ) := Q.filter fun r : ℕ => (r:ℤ)∣x
  have mpos : 0<M N := rpow_pos_of_pos (by exact_mod_cast (show 0<N by omega)) _
  have ep : 0<e N := rpow_pos_of_pos hlog _
  have hn : 1≤(N:ℝ) := by exact_mod_cast hN
  have hnp : (0:ℝ)<N := by linarith
  change 4≤w N at hw
  have keq : K N = (N:ℝ)^(1-3/w N) := by dsimp only [K,M]; rw [←rpow_add hnp]; congr 1; ring
  have k1 : 1≤K N := by rw [keq]; apply one_le_rpow hn; have := (div_le_one (by linarith : 0<w N)).mpr (by linarith : 3≤w N); linarith
  have kN : K N≤N := by
    rw [keq]; conv_rhs => rw [← rpow_one (N:ℝ)]
    apply rpow_le_rpow_of_exponent_le hn
    have : 0≤3/w N := div_nonneg (by norm_num) (by linarith); linarith
  have ine : I.Nonempty := by
    refine ⟨⌈t-K N/2⌉,mem_Icc.mpr ⟨le_rfl,Int.le_floor.mpr ?_⟩⟩
    have := Int.ceil_lt_add_one (t-K N/2)
    linarith
  have dist (x y : ℤ) (hx : x∈I) (hy : y∈I) : |(x:ℝ)-y| ≤ K N := by
    have bound (a : ℤ) (ha : a∈I) : t-K N/2 ≤ a ∧ (a:ℝ) ≤ t+K N/2 :=
      ⟨Int.ceil_le.mp (mem_Icc.mp ha).1,Int.le_floor.mp (mem_Icc.mp ha).2⟩
    obtain ⟨xl,xu⟩ := bound x hx
    obtain ⟨yl,yu⟩ := bound y hy
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have balanced : ∀ q ∈ Q, e N ≤ ∑ n ∈ part A q,(q:ℝ)/n := bal.2.2.2
  have heavy (q : ℕ) (hq : q∈Q) (hr : rare q) : ∃ x∈I, (q:ℤ)∣x ∧ (35/100:ℝ)*w N ≤ mass (F x) := by
    obtain ⟨pp,b,hb,hb0,hqb,hbc⟩ := power_mem hq
    have qp : (0:ℝ)<q := by exact_mod_cast pp.pos
    let B := (part A q).filter fun n => ¬hit n
    have small : (∑ n ∈ B,(q:ℝ)/n) ≤ e N/2 := by
      have rem := sum_le_card_nsmul B (fun n : ℕ => (q:ℝ)/n) ((q:ℝ)/M N) (by
        intro n hn
        exact div_le_div_of_nonneg_left qp.le mpos (reg n (mem_filter.mp (mem_filter.mp hn).1).1).1)
      rw [nsmul_eq_mul] at rem
      change (B.card:ℝ)<L N/q at hr
      calc _ ≤ (B.card:ℝ)*((q:ℝ)/M N) := rem
           _ ≤ (L N/q)*((q:ℝ)/M N) := mul_le_mul_of_nonneg_right hr.le (by positivity)
           _ = _ := by
             dsimp only [L,e]
             rw [Real.rpow_neg (by linarith : 0≤log N)]
             field_simp [mpos.ne',qp.ne', (rpow_pos_of_pos hlog (1/100:ℝ)).ne']
    have split : ((part A q).filter hit) = part U q := by ext n; simp [part,U,and_comm,and_left_comm,and_assoc]
    have splitSum := sum_filter_add_sum_filter_not (s:=part A q) (f:=fun n : ℕ => (q:ℝ)/n) hit
    rw [split] at splitSum
    change (∑ n ∈ part U q, (q:ℝ)/n)+(∑ n ∈ B,(q:ℝ)/n)=_ at splitSum
    have bulk : e N/2 ≤ ∑ n ∈ part U q,(q:ℝ)/n := by linarith [balanced q hq]
    have ua : U⊆A := filter_subset _ _
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
    have uniq (y : ℤ) (hy : y∈I) (dy : (D:ℤ)∣y) : x=y := by
      have h : |x-y|<(D:ℤ) := by exact_mod_cast (dist x y hx hy).trans_lt big
      exact sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd (dvd_sub (Dvd m dx) dy) h)
    have inc : powers C ⊆ F x := by
      intro r hr
      obtain ⟨pr,j,hj,j0,rj,cp⟩ := power_mem hr
      obtain ⟨inU,cop,_⟩ := cf j hj
      obtain ⟨inA,y,hy,divy⟩ := mem_filter.mp inU
      have rDj := rj.trans (dvd_mul_left j D)
      have prA : r ∈ Q := by
        apply mem_biUnion.mpr
        refine ⟨D*j,inA,mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨rDj,fun eq => a0 (eq ▸ inA)⟩,pr,?_⟩⟩
        rw [Nat.mul_div_assoc D rj]
        exact (cop.coprime_dvd_left rj).mul_right cp
      refine mem_filter.mpr ⟨prA,?_⟩
      rw [uniq y hy (Dvd j divy)]
      exact (show (r:ℤ) ∣ ((D*j:ℕ):ℤ) by exact_mod_cast rDj).trans divy
    exact ⟨x,hx,(show (q:ℤ)∣D by exact_mod_cast qd).trans (Dvd m dx),cd.trans
      (sum_le_sum_of_subset_of_nonneg inc (fun _ _ _ => by positivity))⟩
  right
  by_cases existsRare : ∃ q∈Q, rare q
  · obtain ⟨q,hq,hr⟩ := existsRare
    obtain ⟨x,hx,qx,hX⟩ := heavy q hq hr
    refine ⟨x,hx,?_⟩
    intro r hr hrr
    have hrare : rare r := by simpa [rare,hit,I,K,M,w,L,part,not_exists] using hrr
    obtain ⟨y,hy,ry,hY⟩ := heavy r hr hrare
    suffices x=y by simpa [this] using ry
    by_contra ne
    let P := F x ∩ F y
    have sub : F x ∪ F y ⊆ Q := union_subset (filter_subset _ _) (filter_subset _ _)
    have upper : mass (F x ∪ F y) ≤ mass Q := sum_le_sum_of_subset_of_nonneg sub fun _ _ _ => by positivity
    have sums : mass (F x ∪ F y)+mass P = mass (F x)+mass (F y) := sum_union_inter
    have rhs : mass Q ≤ (2/3:ℝ)*w N := total
    have nz : 0<(x-y).natAbs := Int.natAbs_pos.mpr (sub_ne_zero.mpr ne)
    have le : (x-y).natAbs ≤ N := by
      have h := (dist x y hx hy).trans kN
      exact_mod_cast (show ((x-y).natAbs:ℝ)≤N by simpa using h)
    have low := ov (x-y).natAbs nz le P (by
      intro s hs
      obtain ⟨a,b⟩ := mem_inter.mp hs
      have d := dvd_sub (mem_filter.mp a).2 (mem_filter.mp b).2
      exact ⟨(power_mem (mem_filter.mp a).1).1,by simpa using (Int.natAbs_dvd_natAbs.mpr d)⟩)
    change mass P<(1/30:ℝ)*w N at low
    change mass (F x ∪ F y)+mass P = mass (F x)+mass (F y) at sums
    linarith
  · obtain ⟨x,hx⟩ := ine
    refine ⟨x,hx,?_⟩
    intro r hr hrr
    exact False.elim (existsRare ⟨r,hr,by simpa [rare,hit,I,K,M,w,L,part,not_exists] using hrr⟩)
end OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1_H3_R1
