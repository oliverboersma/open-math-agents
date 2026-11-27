import FormalConjectures.ErdosProblems.«377»
import Mathlib

/-!
# Natural density one for convergence of the prime reciprocal sum

The moment proofs below are reused from @amp2600's PR #5081 with the
second-moment theorem renamed. The new density argument follows them.

The first-moment lemmas are adapted from Marcus Buffett's proof in PR #3569.
The elementary Mertens estimates through `mertensG_step` come from
senamakel's merged proof of the Tang lower bound for Erdős 962,
open-math-agents commit d757b84b7870c7b80a9e62d5e93a293328aee0d4.

For the second moment, the joint digit count is controlled by summation by
parts when the two lists of prime powers are well separated. The remaining
pairs have small reciprocal weight by Mertens' theorem. This implements
Theorem 3 of Erdős, Graham, Ruzsa, and Straus (1975).
-/

section
open Filter Finset
open scoped BigOperators Topology
namespace Digits377
abbrev good (p n : ℕ) := ¬p ∣ n.centralBinom
def cnt (p x : ℕ) := Nat.count (good p) x
def half (p : ℕ) := (p+1)/2

lemma small_good {p i : ℕ} (hp : p.Prime) (hi : 2*i<p) : good p i := by
  intro h
  have hf : p ∣ (i+i).factorial := by
    rw [← Nat.add_choose_mul_factorial_mul_factorial i i]
    apply dvd_mul_of_dvd_left _ _
    apply dvd_mul_of_dvd_left _ _
    simpa [Nat.centralBinom,two_mul] using h
  have := hp.dvd_factorial.mp hf
  omega

lemma good_append {p i : ℕ} (hp : p.Prime) (hi : i<p) (q : ℕ) :
    good p (q*p+i) ↔ i < half p ∧ good p q := by
  letI : Fact p.Prime := ⟨hp⟩
  have hl := Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (n:=2*(q*p+i)) (k:=q*p+i) (p:=p)
  rw [show 2*(q*p+i)=(2*q)*p+2*i by ring] at hl
  have hdiv (a b : ℕ) : (a*p+b)/p = a+b/p := by rw [Nat.mul_comm a p,Nat.mul_add_div hp.pos]
  simp only [Nat.mul_add_mod_self_right,hdiv,Nat.mod_eq_of_lt hi,Nat.div_eq_of_lt hi,add_zero] at hl
  have hh := hl.dvd_iff (dvd_refl p)
  change ¬p ∣ (2*(q*p+i)).choose (q*p+i) ↔ _
  rw [show 2*(q*p+i)=(2*q)*p+2*i by ring,hh,hp.dvd_mul]
  by_cases h : 2*i<p
  · rw [Nat.mod_eq_of_lt h,Nat.div_eq_of_lt h,add_zero]
    have hnd : ¬p∣(2*i).choose i := small_good hp h
    have hh' : i<half p := by unfold half; omega
    simp [hnd,hh',good,Nat.centralBinom]
  · have hmod : (2*i) % p < i := by
      rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
      omega
    rw [Nat.choose_eq_zero_of_lt hmod]
    have hh' : ¬i<half p := by unfold half; omega
    simp [hh']

lemma count_block {p : ℕ} (hp : p.Prime) (q : ℕ) :
    Nat.count (fun n => good p (q*p+n)) p = if good p q then half p else 0 := by
  rw [Nat.count_eq_card_filter_range]
  by_cases hq : good p q
  · rw [if_pos hq]
    have heq : (range p).filter (fun n => good p (q*p+n)) = range (half p) := by
      ext i
      simp only [mem_filter,mem_range]
      have hh : half p ≤ p := by dsimp [half]; omega
      exact ⟨fun ⟨hi,h⟩ => ((good_append hp hi q).1 h).1,
        fun h => ⟨h.trans_le hh,(good_append hp (h.trans_le hh) q).2 ⟨h,hq⟩⟩⟩
    rw [heq,card_range]
  · rw [if_neg hq,card_eq_zero,filter_eq_empty_iff]
    intro i hi h
    exact hq ((good_append hp (mem_range.1 hi) q).1 h).2

lemma count_mul {p : ℕ} (hp : p.Prime) (q : ℕ) : cnt p (q*p) = cnt p q * half p := by
  induction q with
  | zero => simp [cnt]
  | succ q ih =>
    simp only [Nat.succ_mul,cnt,Nat.count_add,Nat.count_succ,count_block hp]
    change cnt p (q*p) + _ = (cnt p q + _) * _
    rw [ih]; split_ifs <;> simp [Nat.add_mul]

lemma count_pow {p : ℕ} (hp : p.Prime) (q k : ℕ) : cnt p (q*p^k) = cnt p q * half p ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ,←Nat.mul_assoc,count_mul hp,ih,pow_succ,Nat.mul_assoc]

lemma count_small {p q : ℕ} (hp : p.Prime) (hq : 2*q ≤ p) : cnt p q = q := by
  rw [cnt,Nat.count_eq_card_filter_range]
  have h : (range q).filter (good p) = range q := filter_eq_self.2 fun i hi => small_good hp (by have := mem_range.1 hi; omega)
  simp [h]

lemma count_bounds {p x k : ℕ} (hp : p.Prime) :
    cnt p (x / p^k) * half p^k ≤ cnt p x ∧
    cnt p x ≤ cnt p (x / p^k+1) * half p^k := by
  have hd : 0<p^k := pow_pos hp.pos _
  rw [←count_pow hp,←count_pow hp]
  exact ⟨Nat.count_monotone _ (Nat.div_mul_le_self _ _),
    Nat.count_monotone _ (by simpa [Nat.mul_comm] using (Nat.lt_mul_div_succ x hd).le)⟩

end Digits377
end

section
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
end

section
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
end

section
open Real Filter Finset
open scoped Topology BigOperators
namespace Mass377
noncomputable abbrev root (a : ℝ) (k : ℕ) (x : ℝ) := (a*x)^((k:ℝ)⁻¹)
noncomputable def window (a b : ℝ) (k : ℕ) (x : ℝ) :=
  Nat.primesLE ⌊root b k x⌋₊ \ Nat.primesLE ⌊root a (k+1) x⌋₊
noncomputable abbrev weight (s : Finset ℕ) := ∑ p ∈ s, (1:ℝ)/p
lemma weight_mono {s t : Finset ℕ} (h : s⊆t) : weight s ≤ weight t :=
  sum_le_sum_of_subset_of_nonneg h fun i _ _ => by positivity
lemma primes_mono {x y : ℝ} (h : x≤y) : Nat.primesLE ⌊x⌋₊ ⊆ Nat.primesLE ⌊y⌋₊ := by
  intro p hp
  rw [Nat.mem_primesLE] at hp ⊢
  exact ⟨hp.1.trans (Nat.floor_mono h),hp.2⟩
lemma rootTop {a : ℝ} (ha : 0<a) {k : ℕ} (hk : 0<k) :
    Tendsto (root a k) atTop atTop :=
  (tendsto_rpow_atTop (inv_pos.2 (Nat.cast_pos.2 hk))).comp (tendsto_id.const_mul_atTop ha)
lemma root_mertens {B : ℝ} (hB : Tendsto (fun x : ℝ => S x-log (log x)) atTop (𝓝 B))
    {a : ℝ} (ha : 0<a) {k : ℕ} (hk : 0<k) :
    Tendsto (fun x : ℝ => S (root a k x)-log (log x)) atTop (𝓝 (B+log ((k:ℝ)⁻¹))) := by
  have hR := hB.comp (rootTop ha hk)
  have hq : Tendsto (fun x : ℝ => log a / log x + 1) atTop (𝓝 1) := by
    simpa using (show Tendsto (fun x : ℝ => log a / log x) atTop (𝓝 0) from
      tendsto_const_nhds.div_atTop tendsto_log_atTop).add_const 1
  have hL := hq.log (by norm_num)
  rw [log_one] at hL
  have h := (hR.add_const (log ((k:ℝ)⁻¹))).add hL
  rw [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 1,(tendsto_id.const_mul_atTop ha).eventually_gt_atTop 1] with x hx hax
  have hx' : 0<x := by linarith
  have h0 := (log_pos hx).ne'
  change 1<a*x at hax
  have h1 := (log_pos hax).ne'
  have hk' := (inv_pos.2 (Nat.cast_pos.2 hk) : 0<(k:ℝ)⁻¹).ne'
  have hlog : log a / log x + 1 = log (a*x) / log x := by
    rw [log_mul ha.ne' hx'.ne',add_div,div_self h0]
  simp only [Function.comp_apply,root,log_rpow (mul_pos ha hx'),log_mul hk' h1,hlog,log_div h1 h0]
  ring
lemma window_mass {a b : ℝ} (ha : 0<a) (hb : 0<b) {k : ℕ} (hk : 0<k) :
    Tendsto (fun x : ℝ => weight (window a b k x)) atTop
      (𝓝 (log (k+1:ℕ)-log k)) := by
  obtain ⟨B,hB⟩ := realMertens
  have h := (root_mertens hB hb hk).sub (root_mertens hB ha (Nat.succ_pos k))
  simp only [log_inv,add_sub_add_left_eq_sub,neg_sub_neg] at h
  have hpos : 0 < log (k+1:ℕ)-log k := sub_pos.2 (log_lt_log (Nat.cast_pos.2 hk) (by exact_mod_cast Nat.lt_succ_self k))
  apply h.congr'
  filter_upwards [h.eventually_const_lt hpos] with x hx
  change 0 < (S (root b k x) - log (log x)) - (S (root a (k+1) x) - log (log x)) at hx
  have horder : root a (k+1) x ≤ root b k x := by
    by_contra! hn
    have := weight_mono (primes_mono hn.le)
    change S (root b k x) ≤ S (root a (k+1) x) at this
    linarith
  have hs := sum_sdiff (primes_mono horder) (f:=fun p : ℕ => (1:ℝ)/p)
  change _ = ∑ p ∈ _ \ _, _
  linarith
lemma mem_window {a b x : ℝ} {p k : ℕ} (ha : 0≤a*x) (hb : 0≤b*x) (hk : 0<k) :
    p ∈ window a b k x ↔ p.Prime ∧ (p:ℝ)^k ≤ b*x ∧ a*x < (p:ℝ)^(k+1) := by
  have hr (c : ℝ) (hc : 0≤c*x) (j : ℕ) (hj : 0<j) :
      p≤⌊root c j x⌋₊ ↔ (p:ℝ)^j ≤ c*x := by
    rw [Nat.le_floor_iff (rpow_nonneg hc _),le_rpow_inv_iff_of_pos (Nat.cast_nonneg _) hc (Nat.cast_pos.2 hj),rpow_natCast]
  rw [window,Finset.mem_sdiff,Nat.mem_primesLE,Nat.mem_primesLE,hr b hb k hk,hr a ha (k+1) (Nat.succ_pos k)]
  constructor
  · rintro ⟨⟨hu,hp⟩,hn⟩
    exact ⟨hp,hu,lt_of_not_ge (fun hh => hn ⟨hh,hp⟩)⟩
  · rintro ⟨hp,hu,hl⟩
    exact ⟨⟨hu,hp⟩,fun hh => hl.not_ge hh.1⟩
end Mass377
end

section
open Filter Finset
open scoped Topology
namespace Digits377
noncomputable abbrev v (p : ℕ) := (half p : ℝ)/p
noncomputable abbrev dens (x p : ℕ) := (cnt p x : ℝ)/x
lemma half_bounds (p : ℕ) : p ≤ 2*half p ∧ 2*half p ≤ p+1 := by unfold half; omega
lemma v_bounds {p : ℕ} (hp : 2≤p) : (1/2:ℝ) ≤ v p ∧ v p ≤ 3/4 := by
  obtain ⟨h1,h2⟩ := half_bounds p
  have hp' : (2:ℝ)≤p := by exact_mod_cast hp
  have h1' : (p:ℝ)≤2*half p := by exact_mod_cast h1
  have h2' : 2*(half p:ℝ)≤p+1 := by exact_mod_cast h2
  constructor
  · apply (le_div_iff₀ (by linarith : 0<(p:ℝ))).2; linarith
  · apply (div_le_iff₀ (by linarith : 0<(p:ℝ))).2; linarith
lemma v_limit : Tendsto v atTop (𝓝 (1/2:ℝ)) := by
  have ht : Tendsto (fun p : ℕ => (1:ℝ)/p) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g:=fun _ : ℕ => (1/2:ℝ)) (h:=fun p : ℕ => 1/2+1/(p:ℝ))
    tendsto_const_nhds (by simpa using ht.const_add (1/2:ℝ))
  · filter_upwards [eventually_ge_atTop 2] with p hp using (v_bounds hp).1
  · filter_upwards [eventually_ge_atTop 2] with p hp
    have h2' : 2*(half p:ℝ) ≤ p+1 := by exact_mod_cast (half_bounds p).2
    have hp' : 0<(p:ℝ) := by exact_mod_cast (show 0<p by omega)
    apply (div_le_iff₀ hp').2
    rw [add_mul,div_mul_cancel₀ _ hp'.ne']; linarith
lemma cnt_estimates {p x k : ℕ} (hp : p.Prime) :
    (cnt p x:ℝ) ≤ ((x:ℝ)+p^k)*(v p)^k ∧
    (2*(x/p^k)≤p → ((x:ℝ)-p^k)*(v p)^k ≤ cnt p x) := by
  let q := x/p^k
  have hd : 0<p^k := pow_pos hp.pos _
  have hp' := Nat.cast_pos (α:=ℝ).2 hp.pos
  have hv : 0 ≤ (v p)^k := by unfold v; positivity
  have fact : (p:ℝ)^k * v p^k = (half p:ℝ)^k := by
    rw [←mul_pow]; congr 1; unfold v; field_simp
  have h0 : (q:ℝ)*(p:ℝ)^k ≤ x := by exact_mod_cast Nat.div_mul_le_self x (p^k)
  have h1 : (x:ℝ) ≤ ((q:ℝ)+1)*(p:ℝ)^k := by
    exact_mod_cast (show x≤(q+1)*p^k by simpa [q,Nat.mul_comm] using (Nat.lt_mul_div_succ x hd).le)
  obtain ⟨hl,hu⟩ := count_bounds (x:=x) (k:=k) hp
  have hc : cnt p (q+1) ≤ q+1 := Nat.count_le _
  have hu' : (cnt p x:ℝ) ≤ ((q:ℝ)+1)*(half p:ℝ)^k := by
    exact_mod_cast hu.trans (Nat.mul_le_mul_right _ hc)
  constructor
  · calc (cnt p x:ℝ) ≤ _ := hu'
         _ = (((q:ℝ)+1)*(p:ℝ)^k)*v p^k := by rw [mul_assoc,fact]
         _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hv
  · intro hsmall
    rw [count_small hp hsmall] at hl
    have hl' : (q:ℝ)*(half p:ℝ)^k ≤ cnt p x := by exact_mod_cast hl
    calc _ ≤ ((q:ℝ)*(p:ℝ)^k)*v p^k := mul_le_mul_of_nonneg_right (by linarith) hv
         _ = _ := by rw [mul_assoc,fact]
         _ ≤ _ := hl'
lemma dens_upper {p x k : ℕ} (hp : p.Prime) (hd : p^k≤x) :
    dens x p ≤ 2*(3/4:ℝ)^k := by
  have hx : 0<(x:ℝ) := by exact_mod_cast lt_of_lt_of_le (pow_pos hp.pos _) hd
  have hd' : (p:ℝ)^k ≤ x := by exact_mod_cast hd
  apply (div_le_iff₀ hx).2
  calc (cnt p x:ℝ) ≤ _ := (cnt_estimates (x:=x) (k:=k) hp).1
       _ ≤ (2*x)*(3/4:ℝ)^k := by
          apply mul_le_mul (by linarith) (pow_le_pow_left₀ (by unfold v; positivity) (v_bounds hp.two_le).2 _) (by unfold v; positivity) (by positivity)
       _ = _ := by ring
lemma dens_approx {p x k : ℕ} {η : ℝ} (hp : p.Prime) (hx : 0<x)
    (hd : (p:ℝ)^k ≤ η*x) (hlarge : 4*(x:ℝ) < (p:ℝ)^(k+1)) :
    |dens x p-v p^k| ≤ η := by
  have hx' : 0<(x:ℝ) := by exact_mod_cast hx
  have hp' := pow_pos (Nat.cast_pos (α:=ℝ).2 hp.pos) k
  have hq : (x/p^k:ℕ)*p^k ≤ x := Nat.div_mul_le_self _ _
  have hs : 2*(x/p^k) ≤ p := by
    have hg : 4*x < p^k*p := by rw [pow_succ] at hlarge; exact_mod_cast hlarge
    by_contra! hh
    nlinarith [Nat.mul_le_mul_right (p^k) (show p≤2*(x/p^k) by omega)]
  obtain ⟨hu,hl⟩ := cnt_estimates (x:=x) (k:=k) hp
  have hv : 0≤v p^k := by unfold v; positivity
  have hv1 : v p^k ≤ 1 := pow_le_one₀ (by unfold v; positivity) (by linarith [(v_bounds hp.two_le).2])
  have herr : (p:ℝ)^k * v p^k ≤ η*x := (mul_le_of_le_one_right hp'.le hv1).trans hd
  rw [abs_le]; constructor
  · rw [le_sub_iff_add_le,le_div_iff₀ hx']; linarith [hl hs]
  · rw [sub_le_iff_le_add,div_le_iff₀ hx']; linarith
end Digits377
end

section
open Real Filter Finset Digits377 Mass377
open scoped Topology
namespace Avg377
noncomputable abbrev outer (k x : ℕ) := window 1 1 k x
noncomputable abbrev row (k x : ℕ) := ∑ p ∈ outer k x, dens x p * (1/p)
lemma outer_mem {p k x : ℕ} (hk : 0<k) :
    p∈outer k x ↔ p.Prime ∧ p^k≤x ∧ x<p^(k+1) := by
  rw [mem_window (by positivity) (by positivity) hk]
  norm_cast
  simp
lemma mass_bound : ∃ C : ℝ, 0≤C ∧ ∀ k x : ℕ, 0<k → weight (outer k x) ≤ C := by
  have hw := window_mass (a:=1) (b:=1) (k:=1) (by norm_num) (by norm_num) (by decide)
  obtain ⟨T,hT⟩ := eventually_atTop.1 (hw.eventually_lt_const (show log (1+1:ℕ)-log (1:ℕ) < log (1+1:ℕ)-log (1:ℕ)+1 by linarith))
  let U : ℝ := max 2 T
  let C := max (S U) (log (1+1:ℕ)-log (1:ℕ)+1)
  refine ⟨C,(show 0≤S U from sum_nonneg (fun _ _ => by positivity)).trans (le_max_left _ _),?_⟩
  intro k x hk
  obtain rfl|hx := Nat.eq_zero_or_pos x
  · have he : outer k 0=∅ := eq_empty_iff_forall_notMem.2 fun p hp => by
      obtain ⟨hprime,h,_⟩ := (outer_mem hk).1 hp
      exact (pow_pos hprime.pos k).not_ge h
    simp only [he,weight,sum_empty]
    exact (show 0≤S U from sum_nonneg (fun _ _ => by positivity)).trans (le_max_left _ _)
  have hx1 : (1:ℝ)≤x := by exact_mod_cast hx
  let y := root 1 (k+1) (x:ℝ)
  have hy : 0≤y := by dsimp [y,root]; positivity
  have hk' : 0<(k:ℝ) := Nat.cast_pos.2 hk
  have hroot : root 1 k (x:ℝ) ≤ y^2 := by
    simp only [y,root,one_mul]
    rw [←Real.rpow_natCast _ 2,←Real.rpow_mul (Nat.cast_nonneg x)]
    apply Real.rpow_le_rpow_of_exponent_le hx1
    push_cast
    have hk1 : 1≤(k:ℝ) := by exact_mod_cast hk
    rw [inv_eq_one_div,inv_eq_one_div,div_mul_eq_mul_div,one_mul,div_le_div_iff₀ hk' (by linarith)]
    linarith
  have hsub : outer k x ⊆ window 1 1 1 (y^2) := by
    intro p hp
    obtain ⟨hpr,_,_⟩ := (outer_mem hk).1 hp
    obtain ⟨hup,hlo⟩ := Finset.mem_sdiff.1 hp
    obtain ⟨hle,_⟩ := Nat.mem_primesLE.1 hup
    have hlo' : y < p := by
      by_contra! h
      exact hlo (Nat.mem_primesLE.2 ⟨Nat.le_floor h,hpr⟩)
    have hle' := (Nat.floor_le (by dsimp [root]; positivity : 0≤root 1 k (x:ℝ)))
    have hp_le : (p:ℝ) ≤ root 1 k (x:ℝ) := (Nat.cast_le.2 hle).trans hle'
    apply (mem_window (by positivity) (by positivity) (by decide : 0<1)).2
    simp only [one_mul,pow_one]
    exact ⟨hpr,hp_le.trans hroot,by exact pow_lt_pow_left₀ hlo' hy (by decide : 2 ≠ 0)⟩
  apply (weight_mono hsub).trans
  by_cases ht : T ≤ y^2
  · exact (hT _ ht).le.trans (le_max_right _ _)
  · apply (weight_mono (t:=Nat.primesLE ⌊U⌋₊) ?_).trans (le_max_left _ _)
    intro p hp
    obtain ⟨hpr,hp',_⟩ := (mem_window (by positivity) (by positivity) (by decide : 0<1)).1 hp
    simp only [pow_one,one_mul] at hp'
    exact Nat.mem_primesLE.2 ⟨Nat.le_floor (hp'.trans ((le_of_not_ge ht).trans (le_max_right _ _))),hpr⟩
lemma row_bound {C : ℝ} (hC : ∀ k x : ℕ, 0<k → weight (outer k x) ≤ C)
    (k x : ℕ) (hk : 0<k) : ‖row k x‖ ≤ 2*C*(3/4:ℝ)^k := by
  have hpos : 0≤row k x := sum_nonneg fun _ _ => by unfold Digits377.dens; positivity
  rw [Real.norm_of_nonneg hpos]
  calc row k x ≤ ∑ p ∈ outer k x, (2*(3/4:ℝ)^k)*(1/p) := by
         apply sum_le_sum
         intro p hp
         obtain ⟨hpr,hd,_⟩ := (outer_mem hk).1 hp
         exact mul_le_mul_of_nonneg_right (dens_upper hpr hd) (by positivity)
       _ = (2*(3/4:ℝ)^k)*weight (outer k x) := (mul_sum ..).symm
       _ ≤ (2*(3/4:ℝ)^k)*C := mul_le_mul_of_nonneg_left (hC k x hk) (by positivity)
       _ = _ := by ring
end Avg377
end

section
open Real Filter Finset Digits377 Mass377 Avg377
open scoped Topology
namespace Avg377
lemma inner_sub {η : ℝ} (hη : 0<η) (hη1 : η≤1) {k x : ℕ} (hk : 0<k) :
    window 4 η k x ⊆ outer k x := by
  intro p hp
  obtain ⟨hpr,hu,hl⟩ := (mem_window (by positivity) (by positivity) hk).1 hp
  apply (mem_window (by positivity) (by positivity) hk).2
  simp only [one_mul]
  exact ⟨hpr,hu.trans (by nlinarith [Nat.cast_nonneg (α:=ℝ) x]),by linarith [Nat.cast_nonneg (α:=ℝ) x]⟩
lemma row_limit (k : ℕ) (hk : 0<k) : Tendsto (row k) atTop (𝓝 ((1/2:ℝ)^k * (log (k+1:ℕ)-log k))) := by
  let t := (1/2:ℝ)^k
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  let O (x : ℕ) := outer k x
  have hO : Tendsto (fun x : ℕ => weight (O x)) atTop (𝓝 (log (k+1:ℕ)-log k)) :=
    (window_mass (by norm_num) (by norm_num) hk).comp tendsto_natCast_atTop_atTop
  obtain ⟨C,hC,hbound⟩ := mass_bound
  have hdiff : Tendsto (fun x : ℕ => row k x - t*weight (O x)) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    let η := min 1 (ε/(4*(C+1)))
    have hη : 0<η := lt_min (by norm_num) (by positivity)
    have hη1 : η≤1 := min_le_left ..
    have hηε : 2*η*C ≤ ε/2 := by
      have hh := (le_div_iff₀ (by positivity : 0<4*(C+1))).1 (min_le_right 1 (ε/(4*(C+1))))
      change η*(4*(C+1))≤ε at hh
      linarith
    let I (x : ℕ) := window 4 η k x
    have hI : Tendsto (fun x : ℕ => weight (I x)) atTop (𝓝 (log (k+1:ℕ)-log k)) :=
      (window_mass (by norm_num) hη hk).comp tendsto_natCast_atTop_atTop
    have hEdge := hO.sub hI
    rw [sub_self] at hEdge
    obtain ⟨P,hP⟩ := eventually_atTop.1 ((Metric.tendsto_nhds.1 (v_limit.pow k)) η hη)
    have hPbig := ((rootTop (a:=4) (by norm_num) (Nat.succ_pos k)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (P:ℝ)
    filter_upwards [hEdge.eventually_lt_const (half_pos hε),hPbig,eventually_gt_atTop 0] with x hedge hbig hx
    change weight (O x)-weight (I x)<ε/2 at hedge
    have hsub : I x ⊆ O x := inner_sub hη hη1 hk
    let E (p : ℕ) := |dens x p - t| *(1/(p:ℝ))
    have hi : ∀ p ∈ I x, E p ≤ 2*η*(1/p) := by
      intro p hip
      obtain ⟨hp,hu,hl⟩ := (mem_window (by positivity) (by positivity) hk).1 hip
      have hlow : root 4 (k+1) (x:ℝ) < (p:ℝ) := by
        by_contra! hn
        exact (Finset.mem_sdiff.1 hip).2 (Nat.mem_primesLE.2 ⟨Nat.le_floor hn,hp⟩)
      have hpP : P ≤ p := by exact_mod_cast (show (P:ℝ) ≤ p from (hbig.trans_lt hlow).le)
      have ha := dens_approx hp hx hu hl
      have hv := hP p hpP
      rw [Real.dist_eq] at hv
      have h := abs_sub_le (dens x p) (v p^k) t
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    have ho (p : ℕ) : E p ≤ 1/p := by
      have hd0 : 0≤dens x p := by unfold Digits377.dens; positivity
      have hd1 : dens x p ≤ 1 := (div_le_one (Nat.cast_pos.2 hx)).2 (by exact_mod_cast (Nat.count_le (good p) : cnt p x ≤ x))
      exact mul_le_of_le_one_left (by positivity) (abs_le.2 ⟨by linarith,by linarith⟩)
    have hs := sum_sdiff hsub (f:=E)
    have hs' := sum_sdiff hsub (f:=fun p : ℕ => (1:ℝ)/p)
    have hsi : ∑ p ∈ I x, E p ≤ 2*η*weight (I x) := by
      simpa only [weight,mul_sum] using sum_le_sum hi
    have hso : ∑ p ∈ O x \ I x, E p ≤ weight (O x \ I x) := sum_le_sum fun p _ => ho p
    have hsum : |row k x - t*weight (O x)| ≤ ∑ p ∈ O x, E p := by
      change |(∑ p ∈ O x, _) - t*∑ p ∈ O x, _| ≤ _
      rw [mul_sum,← sum_sub_distrib]
      apply (abs_sum_le_sum_abs ..).trans
      apply sum_le_sum
      intro p _
      rw [←sub_mul,abs_mul,abs_of_nonneg (by positivity : 0≤1/(p:ℝ))]
    have hm := (weight_mono hsub).trans (hbound k x hk)
    have hhi := mul_le_mul_of_nonneg_left hm (by positivity : 0≤2*η)
    change weight (O x \ I x) + weight (I x) = weight (O x) at hs'
    rw [Real.dist_eq,sub_zero]
    linarith
  simpa [t] using hdiff.add (hO.const_mul t)
end Avg377
end

section
open Filter Finset Erdos377 Digits377
open scoped Topology BigOperators
namespace Avg377
noncomputable abbrev ob (p x : ℕ) := ((Icc p x).filter (good p)).card
noncomputable abbrev full (x : ℕ) := ∑ p ∈ Nat.primesLE x, Digits377.cnt p x / (p:ℝ)
noncomputable abbrev observed (x : ℕ) := ∑ n ∈ Icc 1 x, sumInvPrimesNotDvdCentralBinom n
lemma eq_obs (x : ℕ) : observed x = ∑ p ∈ Nat.primesLE x, (ob p x:ℝ)/p := by
  classical
  have hf (n : ℕ) (hn : n≤x) : sumInvPrimesNotDvdCentralBinom n =
      ∑ p ∈ Nat.primesLE x, if p≤n ∧ good p n then (1:ℝ)/p else 0 := by
    rw [sumInvPrimesNotDvdCentralBinom,←Nat.primesLE_eq_filter_Icc_one]
    have hs : (Nat.primesLE x).filter (fun p => p≤n) = Nat.primesLE n := by
      ext p
      rw [Finset.mem_filter,Nat.mem_primesLE,Nat.mem_primesLE]
      exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨h.1.trans hn,h.2⟩,h.1⟩⟩
    rw [←hs,sum_filter]
    apply sum_congr rfl
    intro p _
    by_cases hp : p≤n <;> by_cases hd : p ∣ n.centralBinom <;> simp [hp,hd,good]
  change (∑ n ∈ Icc 1 x, _) = _
  rw [sum_congr rfl (fun n hn => hf n (mem_Icc.1 hn).2),sum_comm]
  apply sum_congr rfl
  intro p hp
  have hpp := (Nat.mem_primesLE.1 hp).2.one_le
  have hs : (Icc 1 x).filter (fun n => p≤n ∧ good p n) = (Icc p x).filter (good p) := by
    ext n; simp only [mem_filter,mem_Icc]; omega
  rw [←sum_filter,hs]
  simp [ob,div_eq_mul_inv]
lemma ob_eq {p x : ℕ} (hp : p≤x) : ob p x + cnt p p = cnt p (x+1) := by
  classical
  let A := (range (x+1)).filter (good p)
  let B := (range p).filter (good p)
  have h : B ⊆ A := filter_subset_filter _ (range_mono (by omega))
  have he : A \ B = (Icc p x).filter (good p) := by
    ext n; simp only [A,B,Finset.mem_sdiff,mem_filter,mem_range,mem_Icc]; omega
  have hh := Finset.card_sdiff_add_card_eq_card h
  rw [he] at hh
  simpa only [ob,cnt,Nat.count_eq_card_filter_range,A,B] using hh
lemma ob_error {p x : ℕ} (hp : p≤x) (hpr : p.Prime) :
    |(ob p x:ℝ)/p - cnt p x / p| ≤ 2 := by
  have h := ob_eq hp
  have hs : cnt p (x+1) = cnt p x + if good p x then 1 else 0 := Nat.count_succ ..
  have hc : cnt p p ≤ p := Nat.count_le _
  have hlo : cnt p x ≤ ob p x+p := by split_ifs at hs <;> omega
  have hhi : ob p x ≤ cnt p x+p := by have := hpr.pos; split_ifs at hs <;> omega
  have hlo' : (cnt p x:ℝ) ≤ ob p x+p := by exact_mod_cast hlo
  have hhi' : (ob p x:ℝ) ≤ cnt p x+p := by exact_mod_cast hhi
  have hp' := Nat.cast_pos (α:=ℝ).2 hpr.pos
  rw [←sub_div,abs_div,abs_of_pos hp',div_le_iff₀ hp',abs_le]
  constructor <;> linarith
lemma mean_error : Tendsto (fun x : ℕ => (1:ℝ)/x*(observed x-full x)) atTop (𝓝 0) := by
  have hpi := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (Chebyshev.eventually_primeCounting_le (ε:=1) (by norm_num))
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hlim : Tendsto (fun x : ℕ => (2*(Real.log 4+1))/Real.log x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlog
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [hpi,eventually_ge_atTop 2] with x hpi hx
  simp only [Nat.floor_natCast] at hpi
  have hx' : (1:ℝ)<x := by exact_mod_cast (show 1<x by omega)
  have hraw : |observed x-full x| ≤ 2*Nat.primeCounting x := by
    rw [eq_obs,full,←sum_sub_distrib]
    calc _ ≤ _ := abs_sum_le_sum_abs ..
         _ ≤ ∑ _p ∈ Nat.primesLE x, (2:ℝ) := by
           apply sum_le_sum
           intro p hp
           exact ob_error (Nat.mem_primesLE.1 hp).1 (Nat.mem_primesLE.1 hp).2
         _ = _ := by simp [Nat.primesLE_card_eq_primeCounting,mul_comm]
  simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (by positivity : 0≤(1:ℝ)/x)]
  calc 1/(x:ℝ)*|observed x-full x| ≤ (1/x)*(2*((Real.log 4+1)*x/Real.log x)) := by gcongr; linarith
       _ = _ := by field_simp <;> ring
end Avg377
end

section
open Filter Finset Real Avg377 Digits377 Mass377
open scoped Topology BigOperators
namespace Avg377
lemma fibers (x j : ℕ) :
    outer (j+1) x = (Nat.primesLE x).filter (fun p => Nat.log p x - 1 = j) := by
  ext p
  rw [outer_mem (Nat.succ_pos j),Finset.mem_filter,Nat.mem_primesLE]
  have hlog := Nat.log_eq_iff (b:=p) (n:=x) (Or.inl (Nat.succ_ne_zero j))
  constructor
  · rintro ⟨hp,h1,h2⟩
    have hl := hlog.2 ⟨h1,h2⟩
    have hpx : p≤x := (show p≤p^(j+1) by
      simpa only [pow_one] using (Nat.pow_le_pow_right hp.pos (show 1≤j+1 by omega))).trans h1
    exact ⟨⟨hpx,hp⟩,by omega⟩
  · rintro ⟨⟨hpx,hp⟩,hl⟩
    have h := Nat.log_pos hp.one_lt hpx
    exact ⟨hp,hlog.1 (by omega)⟩
lemma row_sum (x : ℕ) : (∑' j : ℕ, row (j+1) x) = 1/(x:ℝ) * full x := by
  classical
  let f (p : ℕ) := Nat.log p x-1
  have hm (p : ℕ) (_ : p∈Nat.primesLE x) : f p∈range (x+1) := mem_range.2 (by dsimp [f]; have := Nat.log_le_self p x; omega)
  rw [tsum_eq_sum (s:=range (x+1)) (fun j hj => ?_)]
  · simp only [row,fibers]
    rw [sum_fiberwise_of_maps_to hm]
    rw [full,mul_sum]
    apply sum_congr rfl
    intro p _; unfold Digits377.dens; ring
  · rw [row,fibers]
    have he : (Nat.primesLE x).filter (fun p => Nat.log p x-1=j) = ∅ := by
      apply filter_eq_empty_iff.2
      rintro p hp rfl
      exact hj (hm p hp)
    rw [he,sum_empty]
lemma log_series : (∑' j : ℕ, (1/2:ℝ)^(j+1)*(log (j+1+1:ℕ)-log (j+1:ℕ))) =
    ∑' j : ℕ, log (j+2:ℝ)/2^(j+2) := by
  let a (n : ℕ) := log n*(1/2:ℝ)^n
  have ha : Summable a := by
    have hs := summable_pow_mul_geometric_of_norm_lt_one 1 (r:=(1/2:ℝ)) (by norm_num)
    simp only [pow_one] at hs
    apply hs.of_norm_bounded
    intro n
    obtain rfl|hn := Nat.eq_zero_or_pos n
    · simp [a]
    · have hlog := log_nonneg (show (1:ℝ)≤n by exact_mod_cast hn)
      have hl := log_le_sub_one_of_pos (Nat.cast_pos.2 hn : 0<(n:ℝ))
      rw [Real.norm_of_nonneg (show 0≤a n by dsimp [a]; positivity)]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have h1 := (summable_nat_add_iff 1).2 ha
  have h2 := (summable_nat_add_iff 2).2 ha
  have heq : (∑' j : ℕ, a (j+1)) = ∑' j : ℕ, a (j+2) := by
    rw [h1.tsum_eq_zero_add]
    simpa only [a,Nat.zero_add,Nat.cast_one,log_one,zero_mul,zero_add] using (rfl : (∑' b : ℕ, a (b+1+1)) = ∑' b : ℕ, a (b+2))
  calc _ = ∑' j : ℕ, (2*a (j+2) - a (j+1)) := by
          apply tsum_congr
          intro j
          simp only [a,show j+2=(j+1)+1 by omega,pow_succ]
          ring
       _ = 2*(∑' j : ℕ, a (j+2)) - ∑' j : ℕ, a (j+1) := by
          rw [(h2.mul_left 2).tsum_sub h1,tsum_mul_left]
       _ = ∑' j : ℕ, a (j+2) := by rw [heq]; ring
       _ = _ := by apply tsum_congr; intro j; simp [a,div_eq_mul_inv]
lemma full_limit : Tendsto (fun x : ℕ => 1/(x:ℝ)*full x) atTop
    (𝓝 (∑' j : ℕ, log (j+2:ℝ)/2^(j+2))) := by
  obtain ⟨C,hC,hb⟩ := mass_bound
  have hs : Summable (fun j : ℕ => 2*C*(3/4:ℝ)^(j+1)) :=
    ((summable_nat_add_iff 1).2 (summable_geometric_of_lt_one (by norm_num) (by norm_num : (3/4:ℝ)<1))).mul_left _
  have h := tendsto_tsum_of_dominated_convergence (f:=fun x j : ℕ => row (j+1) x) hs
    (fun j => row_limit _ (Nat.succ_pos j))
    (Eventually.of_forall (fun x j => row_bound hb _ x (Nat.succ_pos j)))
  rw [log_series] at h
  exact h.congr (fun x => row_sum x)
end Avg377

end

section

open Finset Filter Real Digits377
open scoped BigOperators Topology

namespace Correlation377

noncomputable def pulse (m n : ℕ) : ℝ :=
  if n % m < half m then 1 else 0

lemma pulse_nonneg (m n : ℕ) : 0 ≤ pulse m n := by
  unfold pulse; split <;> norm_num

lemma pulse_le_one (m n : ℕ) : pulse m n ≤ 1 := by
  unfold pulse; split <;> norm_num

lemma v_mem (m : ℕ) : 0 ≤ v m ∧ v m ≤ 1 := by
  refine ⟨by positivity, ?_⟩
  obtain rfl | hm := Nat.eq_zero_or_pos m
  · simp [v]
  · apply (div_le_one (Nat.cast_pos.2 hm)).2
    exact_mod_cast (show half m ≤ m by unfold half; omega)

lemma periodic_count_mul (P : ℕ → Prop) [DecidablePred P] (m k : ℕ) :
    Nat.count (fun n => P (n % m)) (k * m) =
      k * Nat.count (fun n => P (n % m)) m := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Nat.count_add, ih, Nat.succ_mul]
    simp

lemma pulse_count_period (m : ℕ) :
    Nat.count (fun n => n % m < half m) m = half m := by
  rw [Nat.count_eq_card_filter_range]
  have he : (range m).filter (fun n => n % m < half m) = range (half m) := by
    ext i
    have hhm : half m ≤ m := by unfold half; omega
    simp only [mem_filter, mem_range]
    exact ⟨fun ⟨hi, hh⟩ => by simpa only [Nat.mod_eq_of_lt hi] using hh,
      fun hi => ⟨hi.trans_le hhm, by simpa only [Nat.mod_eq_of_lt (hi.trans_le hhm)] using hi⟩⟩
  rw [he, card_range]

lemma pulse_sum (m n : ℕ) :
    (∑ i ∈ range n, pulse m i) = (Nat.count (fun i => i % m < half m) n : ℝ) := by
  simp [pulse, Nat.count_eq_card_filter_range]

lemma pulse_prefix (m : ℕ) (hm : 0 < m) (n : ℕ) :
    |∑ i ∈ range n, (pulse m i - v m)| ≤ m := by
  let q := n / m
  have hq : q * m ≤ n := Nat.div_mul_le_self _ _
  have hq' : n ≤ (q + 1) * m := by
    simpa [q, Nat.mul_comm] using (Nat.lt_mul_div_succ n hm).le
  have hL := Nat.count_monotone (fun i => i % m < half m) hq
  have hU := Nat.count_monotone (fun i => i % m < half m) hq'
  rw [periodic_count_mul (fun r => r < half m), pulse_count_period] at hL hU
  have hL' : (q : ℝ) * (half m : ℝ) ≤ Nat.count (fun i => i % m < half m) n := by exact_mod_cast hL
  have hU' : (Nat.count (fun i => i % m < half m) n : ℝ) ≤ ((q : ℝ) + 1) * (half m : ℝ) := by exact_mod_cast hU
  have hqm : (q : ℝ) * m ≤ n := by exact_mod_cast hq
  have hqm' : (n : ℝ) ≤ ((q : ℝ) + 1) * m := by exact_mod_cast hq'
  have he : (m : ℝ) * v m = half m := by
    unfold v; rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hm.ne')]
  have hMv := mul_le_mul_of_nonneg_left (v_mem m).2 (Nat.cast_nonneg (α := ℝ) m)
  have h1 := mul_le_mul_of_nonneg_right hqm (v_mem m).1
  have h2 := mul_le_mul_of_nonneg_right hqm' (v_mem m).1
  rw [mul_assoc, he] at h1 h2
  simp only [sum_sub_distrib, pulse_sum, sum_const, card_range, nsmul_eq_mul, abs_le]
  constructor <;> nlinarith

lemma boundary_count (m : ℕ) (hm : 0 < m) (r n : ℕ) :
    (Nat.count (fun i => i % m = r) n : ℝ) ≤ (n : ℝ) / m + 1 := by
  let q := n / m
  have hq : n ≤ (q + 1) * m := by
    simpa [q, Nat.mul_comm] using (Nat.lt_mul_div_succ n hm).le
  have h := Nat.count_monotone (fun i => i % m = r) hq
  rw [periodic_count_mul (fun n => n = r)] at h
  have hcard : Nat.count (fun i => i % m = r) m ≤ 1 := by
    rw [Nat.count_eq_card_filter_range]
    have hsub : (range m).filter (fun i => i % m = r) ⊆ {r} := by
      intro i hi
      simp only [mem_filter, mem_range] at hi
      simpa [Nat.mod_eq_of_lt hi.1] using hi.2
    simpa using card_le_card hsub
  have h' := h.trans (Nat.mul_le_mul_left _ hcard)
  rw [Nat.mul_one] at h'
  have hreal : (Nat.count (fun i => i % m = r) n : ℝ) ≤ (q : ℝ) + 1 := by exact_mod_cast h'
  apply hreal.trans
  gcongr
  apply (le_div_iff₀ (Nat.cast_pos.2 hm)).2
  exact_mod_cast Nat.div_mul_le_self n m

lemma pulse_jump (m : ℕ) (hm : 0 < m) (n : ℕ) :
    |pulse m (n + 1) - pulse m n| ≤
      (if n % m = m - 1 then (1 : ℝ) else 0) +
      (if n % m = half m - 1 then (1 : ℝ) else 0) := by
  have hr := Nat.mod_lt n hm
  have hh : 0 < half m := by unfold half; omega
  have h₁ : |pulse m (n + 1) - pulse m n| ≤ 1 := by
    unfold pulse; split <;> split <;> norm_num
  by_cases he : n % m = m - 1
  · simp only [he, if_true]
    exact h₁.trans (by split <;> norm_num)
  by_cases hf : n % m = half m - 1
  · rw [if_neg he, if_pos hf, zero_add]
    exact h₁
  have hs : (n + 1) % m = n % m + 1 := by
    have hm' : 1 < m := by omega
    have hx : n % m + 1 < m := by omega
    rw [Nat.add_mod, Nat.mod_eq_of_lt hm', Nat.mod_eq_of_lt hx]
  have hsame : n % m + 1 < half m ↔ n % m < half m := by omega
  simp [pulse, he, hf, hs, hsame]

lemma pulse_variation (m : ℕ) (hm : 0 < m) (n : ℕ) :
    (∑ i ∈ range n, |pulse m (i + 1) - pulse m i|) ≤ 2 * ((n : ℝ) / m + 1) := by
  have h := sum_le_sum fun i (_ : i ∈ range n) => pulse_jump m hm i
  rw [sum_add_distrib] at h
  have he (r : ℕ) : (∑ i ∈ range n, if i % m = r then (1 : ℝ) else 0) =
      (Nat.count (fun i => i % m = r) n : ℝ) := by
    simp [Nat.count_eq_card_filter_range]
  rw [he, he] at h
  linarith [boundary_count m hm (m - 1) n, boundary_count m hm (half m - 1) n]

noncomputable def simultaneous (ms : List ℕ) (n : ℕ) : ℝ :=
  (ms.map fun m => pulse m n).prod

lemma simultaneous_mem (ms : List ℕ) (n : ℕ) :
    0 ≤ simultaneous ms n ∧ simultaneous ms n ≤ 1 := by
  induction ms with
  | nil => simp [simultaneous]
  | cons m ms ih =>
    simp only [simultaneous, List.map_cons, List.prod_cons] at ih ⊢
    exact ⟨mul_nonneg (pulse_nonneg _ _) ih.1,
      mul_le_one₀ (pulse_le_one _ _) ih.1 ih.2⟩

lemma simultaneous_jump (ms : List ℕ) (n : ℕ) :
    |simultaneous ms (n + 1) - simultaneous ms n| ≤
      (ms.map fun m => |pulse m (n + 1) - pulse m n|).sum := by
  induction ms with
  | nil => simp [simultaneous]
  | cons m ms ih =>
    have he : simultaneous (m :: ms) (n + 1) - simultaneous (m :: ms) n =
        pulse m (n + 1) * (simultaneous ms (n + 1) - simultaneous ms n) +
        (pulse m (n + 1) - pulse m n) * simultaneous ms n := by
      simp only [simultaneous, List.map_cons, List.prod_cons]; ring
    rw [he]
    refine (abs_add_le ..).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (pulse_nonneg _ _),
      abs_of_nonneg (simultaneous_mem _ _).1]
    simp only [List.map_cons, List.sum_cons]
    have h1 := mul_le_of_le_one_left (abs_nonneg (simultaneous ms (n + 1) - simultaneous ms n))
      (pulse_le_one m (n + 1))
    have h2 := mul_le_of_le_one_right (abs_nonneg (pulse m (n + 1) - pulse m n))
      (simultaneous_mem ms n).2
    linarith

lemma simultaneous_variation (ms : List ℕ) (hms : ∀ m ∈ ms, 0 < m) (n : ℕ) :
    (∑ i ∈ range n, |simultaneous ms (i + 1) - simultaneous ms i|) ≤
      (ms.map fun m : ℕ => 2 * ((n : ℝ) / (m : ℝ) + 1)).sum := by
  refine (sum_le_sum fun i _ => simultaneous_jump ms i).trans ?_
  induction ms with
  | nil => simp
  | cons m ms ih =>
    simp only [List.map_cons, List.sum_cons, sum_add_distrib]
    exact add_le_add (pulse_variation m (hms m (by simp)) n)
      (ih fun t ht => hms t (by simp [ht]))

lemma extend (m : ℕ) (hm : 0 < m) (ms : List ℕ) (hms : ∀ w ∈ ms, 0 < w) (x : ℕ) :
    |(∑ i ∈ range x, simultaneous (m :: ms) i) - v m * ∑ i ∈ range x, simultaneous ms i| ≤
      m * (1 + (ms.map fun w : ℕ => 2 * ((x : ℝ) / (w : ℝ) + 1)).sum) := by
  have he : (∑ i ∈ range x, simultaneous (m :: ms) i) -
      v m * ∑ i ∈ range x, simultaneous ms i =
      ∑ i ∈ range x, simultaneous ms i * (pulse m i - v m) := by
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    simp only [simultaneous, List.map_cons, List.prod_cons]
    ring
  rw [he, ← Finset.sum_congr rfl (fun i _ => smul_eq_mul (simultaneous ms i) (pulse m i - v m)),
    Finset.sum_range_by_parts]
  simp only [smul_eq_mul]
  refine (abs_sub _ _).trans ?_
  have ha : |simultaneous ms (x - 1) * ∑ i ∈ range x, (pulse m i - v m)| ≤ m := by
    rw [abs_mul, abs_of_nonneg (simultaneous_mem _ _).1]
    exact (mul_le_of_le_one_left (abs_nonneg _) (simultaneous_mem _ _).2).trans (pulse_prefix m hm x)
  have hb : |∑ i ∈ range (x - 1),
      (simultaneous ms (i + 1) - simultaneous ms i) * ∑ j ∈ range (i + 1), (pulse m j - v m)| ≤
      (m : ℝ) * ∑ i ∈ range (x - 1), |simultaneous ms (i + 1) - simultaneous ms i| := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [mul_sum]
    apply sum_le_sum
    intro i _
    rw [abs_mul, mul_comm (m : ℝ)]
    exact mul_le_mul_of_nonneg_left (pulse_prefix m hm _) (abs_nonneg _)
  have hc : (∑ i ∈ range (x - 1), |simultaneous ms (i + 1) - simultaneous ms i|) ≤
      (ms.map fun w : ℕ => 2 * ((x : ℝ) / (w : ℝ) + 1)).sum := by
    exact (sum_le_sum_of_subset_of_nonneg (range_mono (Nat.sub_le ..))
      (fun i _ _ => abs_nonneg _)).trans (simultaneous_variation ms hms x)
  linarith [mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (α := ℝ) m)]

lemma separated_prefix (ms : List ℕ) (x L : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hlen : ms.length ≤ L)
    (hx : ∀ m ∈ ms, 0 < m ∧ m ≤ x ∧ (m : ℝ) ≤ δ * x)
    (hsep : ms.Pairwise fun m w : ℕ => (m : ℝ) ≤ δ * (w : ℝ)) :
    |(∑ i ∈ range x, simultaneous ms i) - x * (ms.map v).prod| ≤
       (ms.length : ℝ) * (1 + 4 * L) * δ * x := by
  induction ms with
  | nil => simp [simultaneous]
  | cons m ms ih =>
    have hlen' : ms.length ≤ L := by simpa using (Nat.le_succ _).trans hlen
    have hx' : ∀ w ∈ ms, 0 < w ∧ w ≤ x ∧ (w : ℝ) ≤ δ * x :=
      fun w hw => hx _ (List.mem_cons_of_mem _ hw)
    rcases List.pairwise_cons.1 hsep with ⟨hsm, hs⟩
    obtain ⟨hm, _, hmx⟩ := hx m (by simp)
    have hm0 : 0 ≤ (m : ℝ) := by positivity
    have hext := extend m hm ms (fun w hw => (hx' w hw).1) x
    have hlocal : ∀ w : ℕ, w ∈ ms → (m : ℝ) * (2 * ((x : ℝ) / (w : ℝ) + 1)) ≤ 4 * δ * x := by
      intro w hw
      obtain ⟨hw0, hwx, _⟩ := hx' w hw
      have hw0' : 0 < (w : ℝ) := by exact_mod_cast hw0
      have hwx' : (w : ℝ) ≤ x := by exact_mod_cast hwx
      have hdiv : 1 ≤ (x : ℝ) / w := (le_div_iff₀ hw0').2 (by simpa using hwx')
      calc (m : ℝ) * (2 * ((x : ℝ) / w + 1)) ≤ m * (4 * ((x : ℝ) / w)) :=
            mul_le_mul_of_nonneg_left (by linarith) hm0
        _ ≤ (δ * w) * (4 * ((x : ℝ) / w)) :=
            mul_le_mul_of_nonneg_right (hsm w hw) (by positivity)
        _ = 4 * δ * x := by field_simp
  -- The sum of the individual boundary errors is linear in the number of scales.
    have hsum : (m : ℝ) * (ms.map fun w : ℕ => 2 * ((x : ℝ) / (w : ℝ) + 1)).sum ≤
        (ms.length : ℝ) * (4 * δ * x) := by
      clear ih hext hsep hlen hs hlen' hx hx' hsm hmx
      induction ms with
      | nil => simp
      | cons w ws ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
        rw [mul_add]
        have h₁ := hlocal w (by simp)
        have h₂ := ih (fun t ht => hlocal t (by simp [ht]))
        linarith only [h₁, h₂]
    have hlen'' : (ms.length : ℝ) ≤ L := by exact_mod_cast hlen'
    have hbound : (m : ℝ) * (1 + (ms.map fun w : ℕ => 2 * ((x : ℝ) / (w : ℝ) + 1)).sum) ≤
        (1 + 4 * L) * δ * x := by
      rw [mul_add, mul_one]
      have := mul_le_mul_of_nonneg_right hlen'' (show 0 ≤ 4 * δ * x by positivity)
      linarith
    have he : (∑ i ∈ range x, simultaneous (m :: ms) i) -
        x * ((m :: ms).map v).prod =
        ((∑ i ∈ range x, simultaneous (m :: ms) i) - v m * ∑ i ∈ range x, simultaneous ms i) +
          v m * ((∑ i ∈ range x, simultaneous ms i) - x * (ms.map v).prod) := by
      simp only [List.map_cons, List.prod_cons]; ring
    rw [he]
    refine (abs_add_le ..).trans ?_
    rw [abs_mul, abs_of_nonneg (v_mem m).1]
    have hrec := (mul_le_of_le_one_left (abs_nonneg _) (v_mem m).2).trans
      (ih hlen' hx' hs)
    have hsum' := add_le_add (hext.trans hbound) hrec
    convert hsum' using 1
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    ring

lemma v_error (m : ℕ) (hm : 0 < m) :
    |v m - (1/2 : ℝ)| ≤ 1 / m := by
  have hL : (m : ℝ) ≤ 2 * half m := by exact_mod_cast (half_bounds m).1
  have hU : (2 : ℝ) * half m ≤ m + 1 := by exact_mod_cast (half_bounds m).2
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have h := one_div_nonneg.2 hm'.le
  have hv : v m * m = half m := by unfold v; field_simp
  rw [abs_le]
  constructor
  · have h₁ : (1/2 : ℝ) ≤ v m := by
      apply (le_div_iff₀ hm').2
      linarith
    linarith
  · have h₁ : v m ≤ 1/2 + 1/m := by
      apply (div_le_iff₀ hm').2
      rw [add_mul, div_mul_cancel₀ _ hm'.ne']
      linarith
    linarith

lemma product_error (ms : List ℕ) (δ : ℝ)
    (h : ∀ m ∈ ms, 0 < m ∧ (1 : ℝ) / m ≤ δ) :
    |(ms.map v).prod - (1/2 : ℝ)^ms.length| ≤ (ms.length : ℝ) * δ := by
  induction ms with
  | nil => simp
  | cons m ms ih =>
    obtain ⟨hm, hm'⟩ := h m (by simp)
    have htail := ih (fun w hw => h w (List.mem_cons_of_mem _ hw))
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ, Nat.cast_add, Nat.cast_one]
    have he : v m * (ms.map v).prod - (1/2 : ℝ)^ms.length * (1/2) =
        v m * ((ms.map v).prod - (1/2 : ℝ)^ms.length) +
          (v m - 1 / 2) * (1/2 : ℝ)^ms.length := by ring
    rw [he]
    refine (abs_add_le ..).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (v_mem m).1, abs_of_nonneg (by positivity : 0 ≤ (1/2 : ℝ)^ms.length)]
    have h₁ := (mul_le_of_le_one_left (abs_nonneg _) (v_mem m).2).trans htail
    have h₂ := (mul_le_of_le_one_right (abs_nonneg _)
      (pow_le_one₀ (n := ms.length) (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num))).trans
      ((v_error m hm).trans hm')
    linarith

end Correlation377
end

section

open Finset Filter Real Digits377 Mass377 Avg377 Correlation377
open scoped BigOperators Topology

namespace Pairs377

def powers (p k : ℕ) : List ℕ := (List.range k).map fun i => p^(i+1)

lemma powers_mem {m p k : ℕ} :
    m ∈ powers p k ↔ ∃ i < k, p^(i+1) = m := by
  simp [powers]

lemma simultaneous_eq (ms : List ℕ) (n : ℕ) :
    simultaneous ms n = if ∀ m ∈ ms, n % m < half m then 1 else 0 := by
  classical
  induction ms with
  | nil => simp [simultaneous]
  | cons m ms ih =>
    simp only [simultaneous, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih]
    by_cases hm : n % m < half m <;> simp [pulse, hm]

lemma good_mods {p n k : ℕ} (hp : p.Prime) (hk : 2*n < p^(k+1)) :
    good p n ↔ ∀ m ∈ powers p k, n % m < half m := by
  have hlog : Nat.log p (n+n) < k+1 := by
    by_cases hn : n = 0
    · simp [hn]
    · exact (Nat.log_lt_iff_lt_pow hp.one_lt (x := k+1)
        (y := n+n) (by omega)).2 (by simpa [two_mul] using hk)
  have hfac := Nat.factorization_choose' (n := n) (k := n) hp hlog
  have hne : n.centralBinom ≠ 0 := (Nat.centralBinom_pos n).ne'
  have hf : good p n ↔ n.centralBinom.factorization p = 0 :=
    ⟨Nat.factorization_eq_zero_of_not_dvd,
      fun hz hd => (hp.factorization_pos_of_dvd hne hd).ne' hz⟩
  rw [hf, show n.centralBinom = (n+n).choose n by simp [Nat.centralBinom,two_mul],
    hfac, card_eq_zero, filter_eq_empty_iff]
  simp only [powers_mem, mem_Ico]
  constructor
  · intro H m hm
    obtain ⟨i, hi, rfl⟩ := hm
    have h := H (x := i+1) ⟨by omega, by omega⟩
    unfold half
    omega
  · intro H i hi
    have h := H (p^i) ⟨i-1, by omega, by congr 1; omega⟩
    unfold half at h
    omega

noncomputable abbrev both (p q n : ℕ) : ℝ :=
    if good p n ∧ good q n then 1 else 0

noncomputable abbrev pairDensity (p q x : ℕ) : ℝ :=
  (∑ n ∈ range x, both p q n) / x

lemma pairDensity_nonneg (p q x : ℕ) : 0 ≤ pairDensity p q x := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply sum_nonneg
  intro n _
  unfold both; split <;> norm_num

lemma pairDensity_le (p q x : ℕ) :
    pairDensity p q x ≤ dens x p ∧ pairDensity p q x ≤ dens x q := by
  have hc (p : ℕ) : (∑ n ∈ range x, if good p n then (1 : ℝ) else 0) = cnt p x := by
    rw [cnt, Nat.count_eq_card_filter_range, sum_boole]
  constructor <;> apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  · rw [← hc]; apply sum_le_sum
    intro i _
    unfold both
    by_cases hi : good p i
    · rw [if_pos hi]
      split <;> norm_num
    · rw [if_neg hi, if_neg (fun h => hi h.1)]
  · rw [← hc]; apply sum_le_sum
    intro i _
    unfold both
    by_cases hi : good q i
    · rw [if_pos hi]
      split <;> norm_num
    · rw [if_neg hi, if_neg (fun h => hi h.2)]

lemma pairDensity_le_one (p q x : ℕ) : pairDensity p q x ≤ 1 := by
  apply (pairDensity_le ..).1.trans
  obtain rfl | hx := Nat.eq_zero_or_pos x
  · norm_num [Digits377.dens]
  · apply (div_le_one (Nat.cast_pos.2 hx)).2
    exact_mod_cast (Nat.count_le (good p) : cnt p x ≤ x)

noncomputable def band (a b : ℝ) (j : ℕ) (y : ℝ) : Finset ℕ :=
  Nat.primesLE ⌊root b j y⌋₊ \ Nat.primesLE ⌊root a j y⌋₊

lemma prime_le_root {a y : ℝ} (ha : 0 ≤ a*y) {j p : ℕ} (hj : 0<j) :
    p ≤ ⌊root a j y⌋₊ ↔ (p : ℝ)^j ≤ a*y := by
  rw [Nat.le_floor_iff (rpow_nonneg ha _),
    le_rpow_inv_iff_of_pos (Nat.cast_nonneg _) ha (Nat.cast_pos.2 hj), rpow_natCast]

lemma band_mem {a b y : ℝ} {j p : ℕ} (ha : 0 ≤ a*y) (hb : 0 ≤ b*y) (hj : 0<j) :
    p ∈ band a b j y ↔ p.Prime ∧ a*y < (p : ℝ)^j ∧ (p : ℝ)^j ≤ b*y := by
  rw [band, Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE,
    prime_le_root ha hj, prime_le_root hb hj]
  constructor
  · rintro ⟨⟨hu, hp⟩, hl⟩
    exact ⟨hp, lt_of_not_ge fun hh => hl ⟨hh, hp⟩, hu⟩
  · rintro ⟨hp, hl, hu⟩
    exact ⟨⟨hu, hp⟩, fun hh => hl.not_ge hh.1⟩

lemma band_mass {a b : ℝ} (ha : 0 < a) (hb : a ≤ b) {j : ℕ} (hj : 0 < j) :
    Tendsto (fun y : ℝ => weight (band a b j y)) atTop (𝓝 0) := by
  obtain ⟨B, hB⟩ := Mass377.realMertens
  have h := (root_mertens hB (ha.trans_le hb) hj).sub (root_mertens hB ha hj)
  rw [sub_self] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
  have hor : root a j y ≤ root b j y := by
    apply rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_right hb hy)
    positivity
  have hs := sum_sdiff (primes_mono hor) (f := fun p : ℕ => (1 : ℝ)/p)
  change (Mass377.S (root b j y) - log (log y)) -
    (Mass377.S (root a j y) - log (log y)) = _
  unfold band at *
  linarith

lemma within_base {p k : ℕ} {δ : ℝ} (hp : 1 < p) (hδ : 0 ≤ δ)
    (hlarge : 1 ≤ δ * p) :
    (powers p k).Pairwise (fun m w : ℕ => (m : ℝ) ≤ δ * w ∨ (w : ℝ) ≤ δ * m) := by
  rw [powers, List.pairwise_map]
  apply (List.pairwise_lt_range (n := k)).imp
  intro a b hab
  left
  simp only [Nat.cast_pow]
  have hh : (p : ℝ)^(a+2) ≤ (p : ℝ)^(b+1) := by
    exact pow_le_pow_right₀ (by exact_mod_cast hp.le) (by omega)
  calc (p : ℝ)^(a+1) = (p : ℝ)^(a+1) * 1 := (mul_one _).symm
    _ ≤ (p : ℝ)^(a+1) * (δ*p) := mul_le_mul_of_nonneg_left hlarge (by positivity)
    _ = δ * (p : ℝ)^(a+2) := by rw [show a+2=(a+1)+1 by omega, pow_succ]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hh hδ

lemma pointwise {p q x k l : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hx : 0<x) (hp : p.Prime) (hq : q.Prime)
    (h₁ : 1 ≤ δ*p) (h₂ : 1 ≤ δ*q)
    (hpU : (p : ℝ)^k ≤ δ*x) (hqU : (q : ℝ)^l ≤ δ*x)
    (hpL : 2*x < p^(k+1)) (hqL : 2*x < q^(l+1))
    (hcross : ∀ i < k, ∀ j < l,
      (p : ℝ)^(i+1) ≤ δ*(q : ℝ)^(j+1) ∨ (q : ℝ)^(j+1) ≤ δ*(p : ℝ)^(i+1)) :
    |pairDensity p q x - (1/2 : ℝ)^(k+l)| ≤ (k+l : ℝ) * (2+4*(k+l)) * δ := by
  let raw := powers p k ++ powers q l
  let ms := raw.mergeSort (· ≤ ·)
  have perm : ms.Perm raw := List.mergeSort_perm _ _
  have hlen : ms.length = k+l := by rw [perm.length_eq]; simp [raw,powers]
  have hx' : 0 < (x : ℝ) := Nat.cast_pos.2 hx
  have h' (b r : ℕ) (hb : b.Prime) (hU : (b : ℝ)^r ≤ δ*x) (hB : 1 ≤ δ*b) :
      ∀ m ∈ powers b r, 0 < m ∧ m ≤ x ∧ (m : ℝ) ≤ δ*x ∧ (1 : ℝ)/m ≤ δ := by
    intro m hm
    obtain ⟨i, hi, rfl⟩ := powers_mem.1 hm
    have hpos : 0 < b^(i+1) := pow_pos hb.pos _
    have hpow : (b : ℝ)^(i+1) ≤ (b : ℝ)^r :=
      pow_le_pow_right₀ (by exact_mod_cast hb.one_lt.le) (by omega)
    have hbp : b ≤ b^(i+1) := by
      simpa only [pow_one] using (Nat.pow_le_pow_right hb.pos (show 1 ≤ i+1 by omega))
    have hbp' : (b : ℝ) ≤ ((b^(i+1) : ℕ) : ℝ) := by exact_mod_cast hbp
    have hu : ((b^(i+1) : ℕ) : ℝ) ≤ δ*x := by simpa using hpow.trans hU
    refine ⟨hpos, ?_, hu, (div_le_iff₀ (Nat.cast_pos.2 hpos)).2 ?_⟩
    · exact_mod_cast hu.trans (mul_le_of_le_one_left hx'.le hδ1.le)
    · exact hB.trans (mul_le_mul_of_nonneg_left hbp' hδ.le)
  have hp' := h' p k hp hpU h₁
  have hq' := h' q l hq hqU h₂
  have hm : ∀ m ∈ ms, 0 < m ∧ m ≤ x ∧ (m : ℝ) ≤ δ*x ∧ (1 : ℝ)/m ≤ δ := by
    intro m hm
    have h := perm.mem_iff.1 hm
    simp only [raw, List.mem_append] at h
    exact h.elim (hp' m) (hq' m)
  let sep := fun m w : ℕ => (m : ℝ) ≤ δ * w ∨ (w : ℝ) ≤ δ * m
  have hsep0 : raw.Pairwise sep := by
    simp only [raw, List.pairwise_append]
    refine ⟨within_base hp.one_lt hδ.le h₁, within_base hq.one_lt hδ.le h₂, ?_⟩
    intro m hm w hw
    obtain ⟨i, hi, rfl⟩ := powers_mem.1 hm
    obtain ⟨j, hj, rfl⟩ := powers_mem.1 hw
    simpa [sep] using hcross i hi j hj
  have hsep1 : ms.Pairwise sep := (perm.pairwise_iff Or.symm).2 hsep0
  have hsorted : ms.Pairwise (· ≤ ·) := (List.sortedLE_mergeSort (l := raw)).pairwise
  have hsep : ms.Pairwise fun m w : ℕ => (m : ℝ) ≤ δ * w := by
    rw [List.pairwise_iff_get] at hsep1 hsorted ⊢
    intro i j hij
    have hi := (hm _ (List.get_mem ms i)).1
    have hs : (ms.get i : ℝ) ≤ ms.get j := by exact_mod_cast hsorted i j hij
    exact (hsep1 i j hij).elim id fun hbad => by
      have hlt := mul_lt_of_lt_one_left (Nat.cast_pos.2 hi : 0 < (ms.get i : ℝ)) hδ1
      linarith
  have he : (∑ n ∈ range x, both p q n) = ∑ n ∈ range x, simultaneous ms n := by
    apply sum_congr rfl
    intro n hn
    have hI : (∀ m ∈ ms, n % m < half m) ↔
        (∀ m ∈ powers p k, n % m < half m) ∧ (∀ m ∈ powers q l, n % m < half m) := by
      simp only [perm.mem_iff, raw, List.mem_append, or_imp, forall_and]
    have hp' := good_mods (k := k) (n := n) hp (by have := mem_range.1 hn; omega)
    have hq' := good_mods (k := l) (n := n) hq (by have := mem_range.1 hn; omega)
    have hBoth := (and_congr hp' hq').trans hI.symm
    rw [simultaneous_eq]
    unfold both
    by_cases h : good p n ∧ good q n
    · rw [if_pos h, if_pos (hBoth.mp h)]
    · rw [if_neg h, if_neg (fun hs => h (hBoth.mpr hs))]
  change |(∑ n ∈ range x, both p q n) / (x : ℝ) - (1/2 : ℝ) ^ (k+l)| ≤ _
  rw [he]
  have ha := separated_prefix ms x (k+l) δ hδ.le hlen.le
    (fun m hm' => ⟨(hm m hm').1, (hm m hm').2.1, (hm m hm').2.2.1⟩) hsep
  have hb := product_error ms δ (fun m hm' => ⟨(hm m hm').1,(hm m hm').2.2.2⟩)
  rw [hlen] at ha hb
  have ha' : |(∑ n ∈ range x, simultaneous ms n) / x - (ms.map v).prod| ≤
      ((k+l : ℕ) : ℝ) * (1+4*((k+l : ℕ) : ℝ)) * δ := by
    have heq : (∑ n ∈ range x, simultaneous ms n) / x - (ms.map v).prod =
        ((∑ n ∈ range x, simultaneous ms n) - x * (ms.map v).prod) / x := by
      field_simp <;> ring
    rw [heq, abs_div, abs_of_pos hx']
    exact (div_le_iff₀ hx').2 ha
  have he' : (∑ n ∈ range x, simultaneous ms n) / x - (1/2 : ℝ)^(k+l) =
      ((∑ n ∈ range x, simultaneous ms n) / x - (ms.map v).prod) +
      ((ms.map v).prod - (1/2 : ℝ)^(k+l)) := by ring
  rw [he']
  push_cast at ha' hb
  exact (abs_add_le ..).trans (by linarith)

end Pairs377
end

section

open Finset Filter Real Digits377 Mass377 Avg377 Correlation377 Pairs377
open scoped BigOperators Topology

namespace Moment377

noncomputable abbrev recip (p : ℕ) : ℝ := 1 / p

noncomputable def pairRow (k l x : ℕ) : ℝ :=
  ∑ p ∈ outer k x, ∑ q ∈ outer l x, recip p * recip q * pairDensity p q x

lemma outer_mass (k : ℕ) (hk : 0 < k) :
    Tendsto (fun x : ℕ => weight (outer k x)) atTop (𝓝 (log (k+1:ℕ)-log k)) :=
  (window_mass (by norm_num) (by norm_num) hk).comp tendsto_natCast_atTop_atTop

lemma edge_small (k : ℕ) (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, weight (outer k x \ window 4 δ k x) ≤ ε := by
  have hi : Tendsto (fun x : ℕ => weight (window 4 δ k x)) atTop
      (𝓝 (log (k+1:ℕ)-log k)) :=
    (window_mass (by norm_num) hδ hk).comp tendsto_natCast_atTop_atTop
  have he := (outer_mass k hk).sub hi
  rw [sub_self] at he
  filter_upwards [he.eventually_lt_const hε] with x hx
  have hs := sum_sdiff (inner_sub hδ hδ1 hk (x := x)) (f := recip)
  change weight (outer k x \ window 4 δ k x) + weight (window 4 δ k x) = weight (outer k x) at hs
  change weight (outer k x) - weight (window 4 δ k x) < ε at hx
  linarith

lemma outer_large (k : ℕ) (hk : 0 < k) (P : ℕ) :
    ∀ᶠ x : ℕ in atTop, ∀ p ∈ outer k x, P ≤ p := by
  filter_upwards [eventually_ge_atTop (P^(k+1))] with x hx p hp
  have hu := ((outer_mem hk).1 hp).2.2
  by_contra! h
  exact (hu.trans_le (Nat.pow_le_pow_left h.le _)).not_ge hx

lemma strips_small (k l : ℕ) (hk : 0<k) {δ : ℝ} (hδ : 0<δ) (hδ1 : δ<1)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ x : ℕ in atTop, ∀ p ∈ outer k x, ∀ i < k, ∀ j < l,
      weight (band δ (1/δ) (j+1) ((p : ℝ)^(i+1))) ≤ ε := by
  have hδε : δ ≤ 1/δ := by
    apply (le_div_iff₀ hδ).2
    nlinarith
  have hb (i j : ℕ) :
      Tendsto (fun p : ℕ => weight (band δ (1/δ) (j+1) ((p : ℝ)^(i+1))))
        atTop (𝓝 0) :=
    (band_mass hδ hδε (Nat.succ_pos j)).comp
      ((tendsto_pow_atTop (Nat.succ_ne_zero i)).comp tendsto_natCast_atTop_atTop)
  have he : ∀ᶠ p : ℕ in atTop, ∀ a : Fin k × Fin l,
      weight (band δ (1/δ) (a.2.val+1) ((p : ℝ)^(a.1.val+1))) ≤ ε := by
    rw [Filter.eventually_all]
    intro a
    exact (hb a.1 a.2).eventually_le_const hε
  obtain ⟨P, hP⟩ := eventually_atTop.1 he
  filter_upwards [outer_large k hk P] with x hx p hp i hi j hj
  exact hP p (hx p hp) (⟨i,hi⟩,⟨j,hj⟩)

lemma close_in_band {δ : ℝ} (hδ : 0 < δ) {p q i j : ℕ} (hq : q.Prime)
    (h : ¬ ((p : ℝ)^(i+1) ≤ δ*(q : ℝ)^(j+1) ∨ (q : ℝ)^(j+1) ≤ δ*(p : ℝ)^(i+1))) :
    q ∈ band δ (1/δ) (j+1) ((p : ℝ)^(i+1)) := by
  push_neg at h
  apply (band_mem (by positivity) (by positivity) (Nat.succ_pos j)).2
  refine ⟨hq, h.2, ?_⟩
  rw [one_div, inv_mul_eq_div]
  exact (le_div_iff₀ hδ).2 (by simpa only [Nat.succ_eq_add_one, mul_comm] using h.1.le)

lemma abs_pair_le_one (k l p q x : ℕ) :
    |pairDensity p q x - (1/2 : ℝ)^(k+l)| ≤ 1 := by
  have ha := pairDensity_nonneg p q x
  have hb := pairDensity_le_one p q x
  have hc : 0 ≤ (1/2 : ℝ)^(k+l) := by positivity
  have hd : (1/2 : ℝ)^(k+l) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  exact abs_le.2 ⟨by linarith, by linarith⟩

set_option maxHeartbeats 1600000 in
lemma pair_row_limit (k l : ℕ) (hk : 0<k) (hl : 0<l) :
    Tendsto (pairRow k l) atTop
      (𝓝 (((1/2 : ℝ)^k * (log (k+1:ℕ)-log k)) *
        ((1/2 : ℝ)^l * (log (l+1:ℕ)-log l)))) := by
  let c := (1/2 : ℝ)^(k+l)
  let K := (k+l : ℝ) * (2+4*(k+l))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨C,hC,hCbound⟩ := mass_bound
  have hdiff : Tendsto (fun x : ℕ =>
      pairRow k l x - c * (weight (outer k x) * weight (outer l x))) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    let δ := min (1/2 : ℝ) (ε / (4*(K+1)*(C+1)^2))
    have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
    have hδ1 : δ < 1 := (min_le_left ..).trans_lt (by norm_num)
    have hδerr : K * δ * C * C ≤ ε / 4 := by
      have hh := (le_div_iff₀ (show 0<4*(K+1)*(C+1)^2 by positivity)).1
        (min_le_right (1/2 : ℝ) (ε / (4*(K+1)*(C+1)^2)))
      have hh' : K * δ * C * C ≤ (K+1)*δ*(C+1)*(C+1) := by gcongr <;> linarith
      linarith
    let τ := ε / (4*(C+1)*((k : ℝ)*l+2))
    have hτ : 0 < τ := by dsimp [τ]; positivity
    have hτerr : C*(2+(k : ℝ)*l)*τ ≤ ε / 4 := by
      calc _ ≤ (C+1)*(2+(k : ℝ)*l)*τ := by gcongr; linarith
        _ = _ := by dsimp [τ]; field_simp; ring
    let P : ℕ := ⌈1/δ⌉₊
    have hP (p : ℕ) (hp : P ≤ p) : 1 ≤ δ * p := by
      have hh : 1 / δ ≤ (p : ℝ) := by
        exact (Nat.le_ceil (1/δ)).trans (by exact_mod_cast hp)
      have h := (div_le_iff₀ hδ).1 hh
      simpa [mul_comm] using h
    filter_upwards [edge_small k hk hδ hδ1.le hτ, edge_small l hl hδ hδ1.le hτ,
      outer_large k hk P, outer_large l hl P, strips_small k l hk hδ hδ1 hτ,
      eventually_gt_atTop (0 : ℕ)] with x heK heL hPK hPL hStrip hx
    let O := outer k x
    let Q := outer l x
    let I := window 4 δ k x
    let J := window 4 δ l x
    have hI : I ⊆ O := inner_sub hδ hδ1.le hk
    have hJ : J ⊆ Q := inner_sub hδ hδ1.le hl
    have hO : weight O ≤ C := hCbound k x hk
    have hQ : weight Q ≤ C := hCbound l x hl
    let E (p q : ℕ) := |pairDensity p q x - c|
    let strip (p i j : ℕ) := band δ (1/δ) (j+1) ((p : ℝ)^(i+1))
    let defect (p q : ℕ) : ℝ := ∑ i ∈ range k, ∑ j ∈ range l,
      if q ∈ strip p i j then (1 : ℝ) else 0
    have hdef_nonneg (p q : ℕ) : 0 ≤ defect p q := by
      apply sum_nonneg; intro i _
      apply sum_nonneg; intro j _
      split <;> norm_num
    have hE (p : ℕ) (hp : p ∈ I) (q : ℕ) (hq : q ∈ J) :
        E p q ≤ K*δ + defect p q := by
      by_cases hcross : ∀ i < k, ∀ j < l,
          (p : ℝ)^(i+1) ≤ δ*(q : ℝ)^(j+1) ∨ (q : ℝ)^(j+1) ≤ δ*(p : ℝ)^(i+1)
      · obtain ⟨hpr, hpU, hpL⟩ := (mem_window (by positivity) (by positivity) hk).1 hp
        obtain ⟨hqr, hqU, hqL⟩ := (mem_window (by positivity) (by positivity) hl).1 hq
        have hpL' : 2*x < p^(k+1) := by
          have h : (2 : ℝ)*x < (p : ℝ)^(k+1) := by linarith [Nat.cast_nonneg (α:=ℝ) x]
          exact_mod_cast h
        have hqL' : 2*x < q^(l+1) := by
          have h : (2 : ℝ)*x < (q : ℝ)^(l+1) := by linarith [Nat.cast_nonneg (α:=ℝ) x]
          exact_mod_cast h
        exact (pointwise hδ hδ1 hx hpr hqr (hP p (hPK p (hI hp))) (hP q (hPL q (hJ hq)))
          hpU hqU hpL' hqL' hcross).trans (le_add_of_nonneg_right (hdef_nonneg p q))
      · push_neg at hcross
        obtain ⟨i, hi, j, hj, hclose⟩ := hcross
        have hpr := ((outer_mem hl).1 (hJ hq)).1
        have hmem : q ∈ strip p i j :=
          close_in_band hδ hpr (fun h => h.elim hclose.1.not_ge hclose.2.not_ge)
        have hone : 1 ≤ defect p q := by
          calc (1 : ℝ) = (if q ∈ strip p i j then 1 else 0) := by rw [if_pos hmem]
            _ ≤ ∑ j ∈ range l, if q ∈ strip p i j then (1 : ℝ) else 0 :=
              single_le_sum (f := fun t => if q ∈ strip p i t then (1 : ℝ) else 0)
                (fun t _ => by split <;> norm_num) (mem_range.2 hj)
            _ ≤ defect p q := single_le_sum
              (f := fun a => ∑ b ∈ range l, if q ∈ strip p a b then (1 : ℝ) else 0)
              (fun a _ => sum_nonneg fun b _ => by split <;> norm_num) (mem_range.2 hi)
        exact (abs_pair_le_one ..).trans (by linarith [mul_nonneg hK hδ.le])
    have hInnerDef (p : ℕ) (hp : p ∈ I) :
        (∑ q ∈ J, recip q * defect p q) ≤ ((k : ℝ)*l) * τ := by
      dsimp [defect]
      simp_rw [mul_sum]
      rw [sum_comm]
      calc _ = ∑ i ∈ range k, ∑ j ∈ range l,
          weight (J.filter fun q => q ∈ strip p i j) := by
            apply sum_congr rfl
            intro i _
            rw [sum_comm]
            apply sum_congr rfl
            intro j _
            simp [weight, sum_filter, mul_ite]
        _ ≤ ∑ i ∈ range k, ∑ j ∈ range l, τ := by
          apply sum_le_sum
          intro i hi
          apply sum_le_sum
          intro j hj
          exact (weight_mono (fun q hq => (mem_filter.1 hq).2)).trans
            (hStrip p (hI hp) i (mem_range.1 hi) j (mem_range.1 hj))
        _ = _ := by simp [sum_const, nsmul_eq_mul]; ring
    let A (p : ℕ) := ∑ q ∈ Q, recip q * E p q
    have hAall (p : ℕ) : A p ≤ C := by
      calc _ ≤ weight Q := sum_le_sum fun q _ =>
          mul_le_of_le_one_right (by positivity) (abs_pair_le_one ..)
        _ ≤ C := hQ
    have hAin (p : ℕ) (hp : p ∈ I) : A p ≤ K*δ*C + (1+(k : ℝ)*l)*τ := by
      have hsum := sum_sdiff hJ (f := fun q => recip q * E p q)
      have hout : (∑ q ∈ Q \ J, recip q * E p q) ≤ τ :=
        (sum_le_sum fun q _ => mul_le_of_le_one_right (by positivity) (abs_pair_le_one ..)).trans heL
      have hin : (∑ q ∈ J, recip q * E p q) ≤ K*δ*C + ((k : ℝ)*l)*τ := by
        have hh : (∑ q ∈ J, recip q * E p q) ≤ ∑ q ∈ J, recip q * (K*δ + defect p q) :=
          sum_le_sum fun q hq => mul_le_mul_of_nonneg_left (hE p hp q hq) (by positivity)
        simp_rw [mul_add, sum_add_distrib, mul_comm (recip _) (K*δ), ← mul_sum] at hh
        exact hh.trans (add_le_add
          (mul_le_mul_of_nonneg_left ((weight_mono hJ).trans hQ) (by positivity)) (hInnerDef p hp))
      change _ + _ = A p at hsum
      linarith
    have hWA : (∑ p ∈ O, recip p * A p) ≤ K*δ*C*C + C*(2+(k : ℝ)*l)*τ := by
      have hsum := sum_sdiff hI (f := fun p => recip p * A p)
      have h₁ : (∑ p ∈ O \ I, recip p * A p) ≤ C*τ := by
        calc _ ≤ ∑ p ∈ O \ I, recip p * C :=
              sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (hAall p) (by positivity)
          _ = C * weight (O \ I) := by rw [← sum_mul]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left heK hC
      have h₂ : (∑ p ∈ I, recip p * A p) ≤ (K*δ*C + (1+(k : ℝ)*l)*τ)*C := by
        calc _ ≤ ∑ p ∈ I, recip p * (K*δ*C + (1+(k : ℝ)*l)*τ) :=
              sum_le_sum fun p hp => mul_le_mul_of_nonneg_left (hAin p hp) (by positivity)
          _ = (K*δ*C + (1+(k : ℝ)*l)*τ) * weight I := by rw [← sum_mul]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left ((weight_mono hI).trans hO) (by positivity)
      linarith
    have hmain : |pairRow k l x - c * (weight O * weight Q)| ≤ ∑ p ∈ O, recip p * A p := by
      have heq : pairRow k l x - c * (weight O * weight Q) =
          ∑ p ∈ O, ∑ q ∈ Q, recip p * recip q * (pairDensity p q x - c) := by
        simp only [pairRow, mul_sub, sum_sub_distrib, weight, sum_mul, mul_sum, O, Q]
        congr 1
        rw [sum_comm]
        apply sum_congr rfl; intro p _
        apply sum_congr rfl; intro q _; ring
      rw [heq]
      refine (abs_sum_le_sum_abs ..).trans (sum_le_sum fun p _ => ?_)
      refine (abs_sum_le_sum_abs ..).trans ?_
      dsimp [A]
      rw [mul_sum]
      apply sum_le_sum
      intro q _
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ recip p * recip q)]
      simp [E, mul_assoc]
    rw [Real.dist_eq, sub_zero]
    linarith
  have hp := ((outer_mass k hk).mul (outer_mass l hl)).const_mul c
  have hh := hdiff.add hp
  rw [zero_add] at hh
  have hfinal := hh.congr (fun x => sub_add_cancel _ _)
  convert hfinal using 1
  simp only [c, pow_add]
  ring

lemma pair_row_nonneg (k l x : ℕ) : 0 ≤ pairRow k l x := by
  apply sum_nonneg; intro p _
  apply sum_nonneg; intro q _
  exact mul_nonneg (by positivity) (pairDensity_nonneg p q x)

lemma pair_row_bound {C : ℝ} (hC : 0 ≤ C)
    (hC' : ∀ k x : ℕ, 0 < k → weight (outer k x) ≤ C)
    (k l x : ℕ) (hk : 0 < k) (hl : 0 < l) :
    ‖pairRow k l x‖ ≤ 2*C*C*(7/8 : ℝ)^k*(7/8 : ℝ)^l := by
  rw [Real.norm_of_nonneg (pair_row_nonneg k l x)]
  have hd (p q : ℕ) (hp : p ∈ outer k x) (hq : q ∈ outer l x) :
      pairDensity p q x ≤ 2*(7/8 : ℝ)^k*(7/8 : ℝ)^l := by
    obtain ⟨hpr, hpk, _⟩ := (outer_mem hk).1 hp
    obtain ⟨hqr, hql, _⟩ := (outer_mem hl).1 hq
    have hbound (a b : ℕ) (hab : a ≤ b) :
        (3/4 : ℝ)^b ≤ (7/8 : ℝ)^a * (7/8 : ℝ)^b := by
      calc _ ≤ ((7/8 : ℝ)^2)^b := pow_le_pow_left₀ (by norm_num) (by norm_num) _
        _ = (7/8 : ℝ)^b * (7/8 : ℝ)^b := by rw [pow_right_comm, pow_two]
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) hab) (by positivity)
    rcases le_total k l with h | h
    · have hb := mul_le_mul_of_nonneg_left (hbound k l h) (by norm_num : (0 : ℝ) ≤ 2)
      exact ((pairDensity_le p q x).2.trans (dens_upper hqr hql)).trans
        (by simpa only [mul_assoc] using hb)
    · have hb := mul_le_mul_of_nonneg_left (hbound l k h) (by norm_num : (0 : ℝ) ≤ 2)
      exact ((pairDensity_le p q x).1.trans (dens_upper hpr hpk)).trans
        (by simpa only [mul_assoc, mul_comm ((7/8 : ℝ)^l) ((7/8 : ℝ)^k)] using hb)
  let A := 2*(7/8 : ℝ)^k*(7/8 : ℝ)^l
  calc pairRow k l x ≤ ∑ p ∈ outer k x, ∑ q ∈ outer l x, recip p * recip q * A := by
         apply sum_le_sum; intro p hp
         apply sum_le_sum; intro q hq
         exact mul_le_mul_of_nonneg_left (hd p q hp hq) (by positivity)
       _ = A * (weight (outer k x) * weight (outer l x)) := by
         dsimp only [weight, recip]
         rw [sum_mul_sum, mul_sum]
         simp_rw [mul_sum]
         apply sum_congr rfl; intro p _
         apply sum_congr rfl; intro q _; ring
       _ ≤ A * (C*C) := by
         apply mul_le_mul_of_nonneg_left _ (by dsimp [A]; positivity)
         exact mul_le_mul (hC' k x hk) (hC' l x hl) (sum_nonneg fun _ _ => by positivity) hC
       _ = _ := by dsimp [A]; ring

noncomputable def massLimit (j : ℕ) : ℝ :=
  (1/2 : ℝ)^(j+1) * (log (j+1+1:ℕ)-log (j+1:ℕ))

noncomputable def geo (j : ℕ) : ℝ := (7/8 : ℝ)^(j+1)

lemma geo_nonneg (j : ℕ) : 0 ≤ geo j := by unfold geo; positivity

lemma geo_summable : Summable geo := by
  exact (summable_nat_add_iff 1).2 (summable_geometric_of_lt_one (by norm_num) (by norm_num))

noncomputable def second (x : ℕ) : ℝ :=
  ∑' k : ℕ, ∑' l : ℕ, pairRow (k+1) (l+1) x

lemma second_limit : Tendsto second atTop (𝓝 ((∑' j : ℕ, log (j+2:ℝ)/2^(j+2))^2)) := by
  obtain ⟨C,hC,hCbound⟩ := mass_bound
  have hbound (x k l : ℕ) : ‖pairRow (k+1) (l+1) x‖ ≤ 2*C*C*geo k*geo l :=
    pair_row_bound hC hCbound _ _ x (Nat.succ_pos _) (Nat.succ_pos _)
  have hs (k : ℕ) : Summable (fun l => 2*C*C*geo k*geo l) := geo_summable.mul_left _
  have h₁ (k : ℕ) : Tendsto (fun x : ℕ => ∑' l : ℕ, pairRow (k+1) (l+1) x) atTop
      (𝓝 (massLimit k * ∑' l : ℕ, massLimit l)) := by
    rw [← tsum_mul_left]
    exact tendsto_tsum_of_dominated_convergence (f := fun x l : ℕ => pairRow (k+1) (l+1) x)
      (hs k) (fun l => pair_row_limit _ _ (Nat.succ_pos _) (Nat.succ_pos _))
      (Eventually.of_forall fun x l => hbound x k l)
  let M := 2*C*C*(∑' l : ℕ, geo l)
  have hM : Summable (fun k => M * geo k) := geo_summable.mul_left _
  have h₂ (x k : ℕ) : ‖∑' l : ℕ, pairRow (k+1) (l+1) x‖ ≤ M * geo k := by
    calc _ ≤ ∑' l : ℕ, 2*C*C*geo k*geo l :=
        norm_tsum_le_tsum_norm ((hs k).of_nonneg_of_le (fun l => norm_nonneg _) (fun l => hbound x k l))
          |>.trans (Summable.tsum_le_tsum (fun l => hbound x k l)
            ((hs k).of_nonneg_of_le (fun l => norm_nonneg _) (fun l => hbound x k l)) (hs k))
      _ = _ := by rw [tsum_mul_left]; dsimp [M]; ring
  have h := tendsto_tsum_of_dominated_convergence
    (f := fun x k : ℕ => ∑' l : ℕ, pairRow (k+1) (l+1) x)
    hM h₁ (Eventually.of_forall h₂)
  have hf : (∑' k : ℕ, massLimit k * ∑' l : ℕ, massLimit l) =
      (∑' j : ℕ, log (j+2:ℝ)/2^(j+2))^2 := by
    rw [tsum_mul_right, ← pow_two]
    congr 1
    exact log_series
  rw [hf] at h
  exact h

noncomputable def topSum (x n : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE x, if good p n then recip p else 0

lemma second_eq (x : ℕ) : second x = (1 : ℝ)/x * ∑ n ∈ range x, (topSum x n)^2 := by
  classical
  let f (p : ℕ) := Nat.log p x - 1
  let s := Nat.primesLE x
  have hm (p : ℕ) (_ : p ∈ s) : f p ∈ range (x+1) := by
    apply mem_range.2
    dsimp [f]
    have := Nat.log_le_self p x
    omega
  have hempty (j : ℕ) (hj : j ∉ range (x+1)) :
      outer (j+1) x = ∅ := by
    rw [fibers]
    apply filter_eq_empty_iff.2
    rintro p hp rfl
    exact hj (hm p hp)
  have hor (k : ℕ) :
      (∑' l : ℕ, pairRow (k+1) (l+1) x) =
      ∑ p ∈ outer (k+1) x, ∑ q ∈ s, recip p * recip q * pairDensity p q x := by
    rw [tsum_eq_sum (s := range (x+1))]
    · simp only [pairRow]
      rw [sum_comm]
      apply sum_congr rfl
      intro p _
      simp only [fibers]
      rw [sum_fiberwise_of_maps_to hm]
    · intro l hl
      simp [pairRow, hempty l hl]
  rw [second]
  simp_rw [hor]
  rw [tsum_eq_sum (s := range (x+1))]
  · simp only [fibers]
    rw [sum_fiberwise_of_maps_to hm]
    let G (p q n : ℕ) := recip p * recip q * both p q n * (x : ℝ)⁻¹
    have h₁ : (∑ p ∈ s, ∑ q ∈ s, recip p * recip q * pairDensity p q x) =
        ∑ p ∈ s, ∑ q ∈ s, ∑ n ∈ range x, G p q n := by
      apply sum_congr rfl; intro p _
      apply sum_congr rfl; intro q _
      simp only [pairDensity, div_eq_mul_inv, sum_mul, mul_sum, G, mul_assoc]
    have h₂ : (∑ p ∈ s, ∑ q ∈ s, ∑ n ∈ range x, G p q n) =
        ∑ p ∈ s, ∑ n ∈ range x, ∑ q ∈ s, G p q n := by
      apply sum_congr rfl; intro p _
      rw [sum_comm]
    rw [h₁, h₂, sum_comm, mul_sum]
    apply sum_congr rfl
    intro n _
    rw [topSum, pow_two, sum_mul_sum, mul_sum]
    simp_rw [mul_sum]
    apply sum_congr rfl
    intro p _
    apply sum_congr rfl
    intro q _
    unfold G both
    by_cases hp : good p n <;> by_cases hq : good q n
    · rw [if_pos (And.intro hp hq), if_pos hp, if_pos hq, mul_one]
      rw [one_div, mul_comm]
    · rw [if_neg (fun h => hq h.2), if_pos hp, if_neg hq]
      simp
    · rw [if_neg (fun h => hp h.1), if_neg hp, if_pos hq]
      simp
    · rw [if_neg (fun h => hp h.1), if_neg hp, if_neg hq]
      simp
  · intro k hk
    simp [hempty k hk]

lemma observed_le (n x : ℕ) (hn : n ≤ x) :
    Erdos377.sumInvPrimesNotDvdCentralBinom n ≤ topSum x n := by
  have he : (Icc 1 n).filter Nat.Prime = Nat.primesLE n := by
    ext p
    simp only [mem_filter, mem_Icc, Nat.mem_primesLE]
    exact ⟨fun h => ⟨h.1.2,h.2⟩, fun h => ⟨⟨h.2.one_lt.le,h.1⟩,h.2⟩⟩
  change (∑ p ∈ (Icc 1 n).filter Nat.Prime, if p ∣ n.centralBinom then 0 else recip p) ≤ _
  rw [he]
  calc _ = topSum n n := by
         unfold topSum
         apply sum_congr rfl; intro p _
         by_cases hp : p ∣ n.centralBinom
         · rw [if_pos hp, if_neg (fun h => h hp)]
         · rw [if_neg hp, if_pos hp]
       _ ≤ topSum x n := by
         apply sum_le_sum_of_subset_of_nonneg
         · intro p hp
           rw [Nat.mem_primesLE] at hp ⊢
           exact ⟨hp.1.trans hn,hp.2⟩
         · intro p _ _
           split <;> positivity

lemma observed_nonneg (n : ℕ) : 0 ≤ Erdos377.sumInvPrimesNotDvdCentralBinom n := by
  apply sum_nonneg
  intro p _
  split <;> positivity

lemma mean_limit : Tendsto (fun x : ℕ => (1 : ℝ)/x * observed x) atTop
    (𝓝 (∑' j : ℕ, log (j+2:ℝ)/2^(j+2))) := by
  have h := mean_error.add full_limit
  rw [zero_add] at h
  apply h.congr
  intro x
  change (1/(x:ℝ)*(observed x-full x) + 1/x*full x) = 1/x*observed x
  ring

lemma lower_moment (x : ℕ) (hx : 0 < x) :
    ((1 : ℝ)/x * observed x)^2 ≤
       (1 : ℝ)/x * ∑ n ∈ Icc 1 x, Erdos377.sumInvPrimesNotDvdCentralBinom n ^ 2 := by
  have h := sum_mul_sq_le_sq_mul_sq (Icc 1 x)
    (fun _ => (1 : ℝ)) Erdos377.sumInvPrimesNotDvdCentralBinom
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc] at h
  rw [show x+1-1=x by omega] at h
  have hx' : 0<(x:ℝ) := Nat.cast_pos.2 hx
  simp only [one_div, observed, mul_pow]
  apply (mul_le_mul_of_nonneg_left h (sq_nonneg ((x : ℝ)⁻¹))).trans_eq
  field_simp

lemma upper_moment (x : ℕ) (hx : 0 < x) :
    (1 : ℝ)/x * ∑ n ∈ Icc 1 x, Erdos377.sumInvPrimesNotDvdCentralBinom n ^ 2
      ≤ ((x+1 : ℕ) : ℝ) / x * second (x+1) := by
  rw [second_eq]
  have hx' : 0 < (x : ℝ) := Nat.cast_pos.2 hx
  have hx1' : 0 < ((x+1 : ℕ) : ℝ) := by positivity
  rw [show (((x+1 : ℕ) : ℝ) / x) * (1 / ((x+1 : ℕ) : ℝ) *
      ∑ n ∈ range (x+1), (topSum (x+1) n)^2) =
      1/x * ∑ n ∈ range (x+1), (topSum (x+1) n)^2 by field_simp]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    (∑ n ∈ Icc 1 x, Erdos377.sumInvPrimesNotDvdCentralBinom n ^ 2)
        ≤ ∑ n ∈ Icc 1 x, (topSum (x+1) n)^2 := by
          apply sum_le_sum
          intro n hn
          exact pow_le_pow_left₀ (observed_nonneg n) (observed_le n _ (by have := (mem_Icc.1 hn).2; omega)) _
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (fun n hn => mem_range.2 (by have := (mem_Icc.1 hn).2; omega))
      (fun _ _ _ => sq_nonneg _)

lemma ratio_limit : Tendsto (fun x : ℕ => ((x+1 : ℕ) : ℝ) / x) atTop (𝓝 1) := by
  have hi : Tendsto (fun x : ℕ => (1 : ℝ) / x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h := hi.const_add 1
  rw [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with x hx
  have hx' : (x : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hx.ne'
  push_cast
  field_simp

end Moment377

open Moment377

private theorem oma377_second_moment : type_of% @Erdos377.erdos_377.variants.limit.ii := by
  intro γ hγ
  subst γ
  have hL := mean_limit.pow 2
  have hU := ratio_limit.mul (second_limit.comp (tendsto_add_atTop_nat 1))
  rw [one_mul] at hU
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with x hx using lower_moment x hx
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with x hx using upper_moment x hx

end

section

open Filter Finset
open scoped Topology

private theorem density_of_two_moments (f : ℕ → ℝ) (γ : ℝ)
    (hmean : Tendsto (fun x : ℕ => (1 : ℝ) / x * ∑ n ∈ Icc 1 x, f n) atTop (𝓝 γ))
    (hsecond : Tendsto (fun x : ℕ => (1 : ℝ) / x * ∑ n ∈ Icc 1 x, (f n)^2)
      atTop (𝓝 (γ^2))) (ε : ℝ) (hε : 0 < ε) :
    {n : ℕ | |f n - γ| < ε}.HasDensity 1 := by
  classical
  let variance := fun x : ℕ => (1 : ℝ) / x * ∑ n ∈ Icc 1 x, (f n - γ)^2
  have hv : Tendsto variance atTop (𝓝 0) := by
    have h := (hsecond.sub (hmean.const_mul (2*γ))).add_const (γ^2)
    rw [show γ^2 - 2*γ*γ + γ^2 = 0 by ring] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with x hx
    have hx' : 0 < (x : ℝ) := by exact_mod_cast hx
    have hc : (Icc 1 x).card = x := by rw [Nat.card_Icc]; omega
    unfold variance
    simp only [show ∀ n, (f n-γ)^2 = (f n)^2 - (2*γ)*f n + γ^2 by intro n; ring,
      sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul, hc]
    field_simp
  let good := {n : ℕ | |f n - γ| < ε}
  change Tendsto (fun x => good.partialDensity Set.univ x) atTop (𝓝 1)
  have htail : Tendsto (fun x : ℕ => 1 - ((1 : ℝ) / x + variance x / ε^2)) atTop (𝓝 1) := by
    have hz : Tendsto (fun x : ℕ => (1 : ℝ) / x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa using (hz.add (hv.div_const (ε^2))).const_sub 1
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' htail tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with x hx
    have hx' : 0 < (x : ℝ) := by exact_mod_cast hx
    have he : 0 < ε^2 := sq_pos_of_pos hε
    let hit := (range x).filter fun n => |f n - γ| < ε
    let miss := (range x).filter fun n => ¬ |f n - γ| < ε
    let inside := (Icc 1 x).filter fun n => ¬ |f n - γ| < ε
    have partition : hit.card + miss.card = x := by
      simpa [hit, miss] using card_filter_add_card_filter_not (s := range x)
        (p := fun n => |f n - γ| < ε)
    have miss_bound : miss.card ≤ inside.card + 1 := by
      have hs : miss ⊆ insert 0 inside := by
        intro n hn
        rw [mem_insert]
        by_cases h0 : n = 0
        · exact Or.inl h0
        · have h := mem_filter.mp hn
          exact Or.inr (mem_filter.mpr
            ⟨mem_Icc.mpr ⟨by omega, (mem_range.mp h.1).le⟩, h.2⟩)
      exact (card_le_card hs).trans (card_insert_le _ _)
    have bound : (inside.card : ℝ) * ε^2 ≤ ∑ n ∈ Icc 1 x, (f n - γ)^2 := calc
      _ = ∑ _n ∈ inside, ε^2 := by simp [nsmul_eq_mul]
      _ ≤ ∑ n ∈ inside, (f n - γ)^2 := by
        apply sum_le_sum
        intro n hn
        have h := pow_le_pow_left₀ hε.le (not_lt.mp (mem_filter.mp hn).2) 2
        simpa only [sq_abs] using h
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)
    have bound' : (inside.card : ℝ) ≤ (∑ n ∈ Icc 1 x, (f n - γ)^2) / ε^2 :=
      (le_div_iff₀ he).mpr bound
    have qcast : (hit.card : ℝ) + (miss.card : ℝ) = x := by exact_mod_cast partition
    have mcast : (miss.card : ℝ) ≤ (inside.card : ℝ) + 1 := by exact_mod_cast miss_bound
    have density_eq : good.partialDensity Set.univ x = (hit.card : ℝ) / x := by
      have hgood : (good ∩ Set.univ) ∩ Set.Iio x = (hit : Set ℕ) := by
        ext n
        simp [good, hit, and_comm]
      rw [show good.partialDensity Set.univ x =
        ((((good ∩ Set.univ) ∩ Set.Iio x).ncard : ℝ) / (Set.univ ∩ Set.Iio x).ncard) by rfl,
        hgood, Set.ncard_coe_finset, Set.univ_inter, ← Finset.coe_range,
        Set.ncard_coe_finset, card_range]
    rw [density_eq, ← sub_nonneg]
    have hdiv : (miss.card : ℝ) / x ≤ (1 : ℝ) / x + variance x / ε^2 := by
      apply (div_le_iff₀ hx').mpr
      dsimp [variance]
      have hfactor : (1 / (x : ℝ) + (1 / (x : ℝ) * ∑ n ∈ Icc 1 x, (f n - γ)^2) / ε^2) * x
            = 1 + (∑ n ∈ Icc 1 x, (f n - γ)^2) / ε^2 := by field_simp
      rw [hfactor]
      linarith
    have hdivsum : (hit.card : ℝ) / x + (miss.card : ℝ) / x = 1 := by
      rw [← add_div, qcast, div_self hx'.ne']
    linarith
  · exact Eventually.of_forall fun x => Set.partialDensity_le_one good Set.univ x

theorem OMA.solution : type_of% @Erdos377.erdos_377.variants.ae := by
  intro γ hγ ε hε
  apply density_of_two_moments _ γ _ _ ε hε
  · rw [hγ]
    exact Moment377.mean_limit
  · exact oma377_second_moment γ hγ

end
