import OMAReductions.R_Erdos297_erdos_297_variants_general_R1_H3_R1_H2_R1_H1_R1
import Mathlib

/-!
The modular subset-sum theorem and the prime count in a fixed-ratio interval come
from Will Howe (@H0W4RD-dev), H0W4RD-dev/croot-unit-fractions at
c58a7d45114c3af27e6abb19dcfca9d82b49b4a1, used under Apache-2.0 and adapted
from the @marcusbuffett port in open-math-agents at 5f7f37a. The Fourier
argument is Croot's Lemma 1 (Acta Arithmetica 99, 2001).

Partition the prime interval at five thirds of its lower endpoint. One part
still contains enough primes after removing the prime dividing the modulus.
Multiplying its primes by a common integer coprime to the modulus, two and
three moves all denominators into the required window. Inversion multiplies
the subset sums by a unit, so they still cover every residue. The lcm grid
and tail budget then lift the modular identities to rational ones.
-/
namespace Croot

open Real Finset Filter

/-- For every `n` and every `ε > 0`, eventually `(log x) ^ n ≤ ε √x`. -/
lemma eventually_log_pow_le_mul_sqrt (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ n ≤ ε * √x := by
  have h := (isLittleO_log_rpow_rpow_atTop (n : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).bound hε
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  have e1 : ‖Real.log x ^ (n : ℝ)‖ = Real.log x ^ n := by
    rw [Real.rpow_natCast, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hlog n)]
  have e2 : ‖x ^ (1 / 2 : ℝ)‖ = √x := by
    rw [Real.sqrt_eq_rpow, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  have hx' : ‖Real.log x ^ (n : ℝ)‖ ≤ ε * ‖x ^ (1 / 2 : ℝ)‖ := hx
  rw [e1, e2] at hx'
  exact hx'

/-- For large `x` there are at least `x / (5 log x)` primes in `(x, 2.7 x]`. -/
theorem eventually_card_primes_Ioc_ge : ∀ᶠ x : ℝ in atTop,
    x / (5 * Real.log x) ≤
      (((Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime).card : ℝ) := by
  filter_upwards [eventually_ge_atTop (10 : ℝ),
    eventually_log_pow_le_mul_sqrt 1 (ε := 1 / 2000) (by norm_num),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 : ℝ)] with x hx hlogx hL2
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hl2lo : (693 / 1000 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hl2hi : Real.log 2 < 7 / 10 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hfl : ⌊x⌋₊ ≤ ⌊(27 / 10 : ℝ) * x⌋₊ := Nat.floor_le_floor (by linarith)
  have hsplit : Chebyshev.theta ((27 / 10 : ℝ) * x) = Chebyshev.theta x +
      ∑ p ∈ (Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime, Real.log p := by
    simp only [Chebyshev.theta, Finset.sum_filter]
    rw [Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hfl]
  have hsum : ∑ p ∈ (Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime, Real.log p ≤
      (((Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime).card : ℝ) *
        Real.log ((27 / 10 : ℝ) * x) := by
    have h := Finset.sum_le_card_nsmul ((Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime)
      (fun p : ℕ => Real.log p) (Real.log ((27 / 10 : ℝ) * x)) (by
        intro p hp
        have hp' := Finset.mem_filter.mp hp
        have hpI := Finset.mem_Ioc.mp hp'.1
        have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp'.2.pos
        have hp_le : (p : ℝ) ≤ (27 / 10 : ℝ) * x :=
          le_trans (by exact_mod_cast hpI.2) (Nat.floor_le (by linarith))
        exact Real.log_le_log hp_pos hp_le)
    rw [nsmul_eq_mul] at h
    exact h
  have hlow := Chebyshev.theta_ge' (x := (27 / 10 : ℝ) * x) (by linarith)
  have hup := Chebyshev.theta_le_log4_mul_x hx0
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]; ring
  rw [hlog4] at hup
  have hs0 : 0 ≤ √x := Real.sqrt_nonneg x
  have hss : √x * √x = x := Real.mul_self_sqrt hx0
  have hs3 : 3 ≤ √x := Real.le_sqrt_of_sq_le (by linarith)
  have hlogx' : Real.log x ≤ 1 / 2000 * √x := by simpa using hlogx
  have hlog27 : Real.log ((27 / 10 : ℝ) * x) ≤ Real.log x + 17 / 10 := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    have : Real.log (27 / 10 : ℝ) ≤ 27 / 10 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hlog27' : 0 ≤ Real.log ((27 / 10 : ℝ) * x) := Real.log_nonneg (by linarith)
  have hlogx2 : Real.log ((27 / 10 : ℝ) * x + 2) ≤ Real.log x + 2 := by
    have h3x := Real.log_le_log (by linarith) (show (27 / 10 : ℝ) * x + 2 ≤ 3 * x by linarith)
    rw [Real.log_mul (by norm_num) (by linarith)] at h3x
    have : Real.log (3 : ℝ) ≤ 3 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hsqrt27 : √((27 / 10 : ℝ) * x) ≤ 2 * √x := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Real.sq_sqrt hx0]
  have hprod : √((27 / 10 : ℝ) * x) * Real.log ((27 / 10 : ℝ) * x) ≤
      (2 * √x) * (2 * Real.log x) :=
    mul_le_mul hsqrt27 (by linarith) hlog27' (by positivity)
  have hsL : √x * Real.log x ≤ √x * (1 / 2000 * √x) := mul_le_mul_of_nonneg_left hlogx' hs0
  have hsL3 : 3 ≤ √x * Real.log x := by nlinarith
  have hLsL : Real.log x ≤ √x * Real.log x := by nlinarith
  have hx2 : 693 / 1000 * x ≤ Real.log 2 * x := mul_le_mul_of_nonneg_right hl2lo.le hx0
  have hdiff : (48 / 100 : ℝ) * x ≤
      ∑ p ∈ (Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime, Real.log p := by
    linarith [hsplit, hlow, hup, hlogx2, hprod, hsL, hss, hsL3, hLsL, hx2]
  have hcard0 : (0 : ℝ) ≤ (((Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime).card : ℝ) := by
    positivity
  have hc1 := mul_le_mul_of_nonneg_left hlog27 hcard0
  have hc2 := mul_nonneg hcard0 (show (0 : ℝ) ≤ 5 / 2 * Real.log x - 17 / 4 by linarith)
  rw [div_le_iff₀ (by linarith)]
  linarith [hsum, hdiff, hc1, hc2]
lemma eventually_L_conds (x₀ : ℝ) : ∀ᶠ L : ℝ in atTop,
    1 ≤ L ∧ x₀ ≤ L ^ 4 / 4 ∧ 2 ≤ L ^ 4 / 4 ∧
    L ^ (39 / 10 : ℝ) ≤ L ^ 4 / (80 * Real.log L) - 18 * L - 1 := by
  have h1 := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).bound
    (by norm_num : (0 : ℝ) < 1 / 320)
  filter_upwards [h1, eventually_ge_atTop (4 * |x₀| + 8)] with L hL hL'
  have hx0 : x₀ ≤ |x₀| := le_abs_self x₀
  have habs : 0 ≤ |x₀| := abs_nonneg x₀
  have hL8 : 8 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hL4 : L ≤ L ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
  have hlogL : 0 < Real.log L := Real.log_pos (by linarith)
  have hu : 0 < L ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos hL0 _
  have hv : 0 < L ^ (39 / 10 : ℝ) := Real.rpow_pos_of_pos hL0 _
  have huv : L ^ (1 / 10 : ℝ) * L ^ (39 / 10 : ℝ) = L ^ 4 := by
    rw [← Real.rpow_add hL0, show (1 / 10 : ℝ) + 39 / 10 = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  have hlog' : Real.log L ≤ L ^ (1 / 10 : ℝ) / 320 := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlogL, abs_of_pos hu] at hL
    linarith
  have hv3 : L ^ 3 ≤ L ^ (39 / 10 : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ L by linarith)
      (show ((3 : ℕ) : ℝ) ≤ 39 / 10 by norm_num)
    rwa [Real.rpow_natCast] at this
  have hL3 : 9 * L ≤ L ^ 3 := by
    have : L ^ 3 = L * L ^ 2 := by ring
    nlinarith
  have key : 4 * L ^ (39 / 10 : ℝ) ≤ L ^ 4 / (80 * Real.log L) := by
    rw [le_div_iff₀ (by positivity), ← huv]
    nlinarith [mul_le_mul_of_nonneg_left hlog' hv.le]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩
end Croot
namespace Croot

open Real Finset Filter

namespace Lemma1Aux

/-! ### Step 1: the Fourier-analytic existence criterion -/

section Fourier

variable {n : ℕ} [NeZero n]

/-- An additive character turns finite sums into products. -/
lemma stdAddChar_sum {ι : Type*} [DecidableEq ι] (T : Finset ι) (f : ι → ZMod n) :
    ZMod.stdAddChar (∑ i ∈ T, f i) = ∏ i ∈ T, ZMod.stdAddChar (f i) := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

/-- Fourier criterion: if every nontrivial frequency `h` gives a product of norm at most
`2^|R| / n`, then every residue class is a subset sum of the `u i`. -/
theorem exists_subset_sum_of_norm_prod_le {ι : Type*} [DecidableEq ι] (R : Finset ι)
    (u : ι → ZMod n)
    (hbound : ∀ h : ZMod n, h ≠ 0 →
      ‖∏ i ∈ R, (1 + ZMod.stdAddChar (h * u i))‖ ≤ 2 ^ R.card / n)
    (c : ZMod n) : ∃ T ⊆ R, ∑ i ∈ T, u i = c := by
  by_contra hne
  push Not at hne
  set F : ZMod n → ℂ := fun h =>
    ZMod.stdAddChar (-(h * c)) * ∏ i ∈ R, (1 + ZMod.stdAddChar (h * u i)) with hF
  have hexpand : ∀ h : ZMod n,
      F h = ∑ T ∈ R.powerset, ZMod.stdAddChar (h * (∑ i ∈ T, u i - c)) := by
    intro h
    simp only [hF]
    rw [Finset.prod_one_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [← stdAddChar_sum T (fun i => h * u i), ← AddChar.map_add_eq_mul]
    congr 1
    rw [mul_sub, Finset.mul_sum]
    ring
  have key : ∑ h : ZMod n, F h = 0 := by
    rw [Finset.sum_congr rfl fun h _ => hexpand h, Finset.sum_comm]
    refine Finset.sum_eq_zero fun T hT => ?_
    have hT' : ∑ i ∈ T, u i - c ≠ 0 := sub_ne_zero.2 (hne T (Finset.mem_powerset.1 hT))
    have := AddChar.sum_mulShift (ψ := (ZMod.stdAddChar : AddChar (ZMod n) ℂ))
      (∑ i ∈ T, u i - c) (ZMod.isPrimitive_stdAddChar n)
    rw [if_neg hT', Nat.cast_zero] at this
    exact this
  rw [← Finset.add_sum_erase _ F (Finset.mem_univ (0 : ZMod n))] at key
  have h0 : F 0 = 2 ^ R.card := by
    simp only [hF, zero_mul, neg_zero, AddChar.map_zero_eq_one, one_mul, Finset.prod_const]
    norm_num
  rw [h0] at key
  set S := ∑ h ∈ Finset.univ.erase (0 : ZMod n), F h with hS
  have hn : (0 : ℝ) < n := by exact_mod_cast (NeZero.pos n)
  have hSnorm : ‖S‖ ≤ ((n : ℝ) - 1) * (2 ^ R.card / n) := by
    calc ‖S‖ ≤ ∑ h ∈ Finset.univ.erase (0 : ZMod n), ‖F h‖ := norm_sum_le _ _
    _ ≤ ∑ h ∈ Finset.univ.erase (0 : ZMod n), (2 ^ R.card / n : ℝ) := by
        refine Finset.sum_le_sum fun h hh => ?_
        simp only [hF]
        rw [norm_mul, AddChar.norm_apply, one_mul]
        exact hbound h (Finset.ne_of_mem_erase hh)
    _ = ((n : ℝ) - 1) * (2 ^ R.card / n) := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
          ZMod.card, nsmul_eq_mul, Nat.cast_sub NeZero.one_le, Nat.cast_one]
  have hSeq : S = -(2 : ℂ) ^ R.card := by linear_combination key
  rw [hSeq, norm_neg, norm_pow, Complex.norm_two] at hSnorm
  have h2 : (0 : ℝ) < 2 ^ R.card := by positivity
  have hlt : ((n : ℝ) - 1) * (2 ^ R.card / n) < 2 ^ R.card := by
    rw [mul_div_assoc', div_lt_iff₀ hn]
    nlinarith
  linarith

/-- `‖1 + e(x/n)‖² ≤ 4 - 16 (t/n)²`, where `t` is the least absolute residue of `x`. -/
lemma norm_one_add_stdAddChar_sq_le (x : ZMod n) :
    ‖1 + ZMod.stdAddChar x‖ ^ 2 ≤ 4 - 16 * ((x.valMinAbs : ℝ) / n) ^ 2 := by
  set t := x.valMinAbs with ht
  have hx : ((t : ℤ) : ZMod n) = x := ZMod.coe_valMinAbs x
  have hn : (0 : ℝ) < n := by exact_mod_cast (NeZero.pos n)
  set θ : ℝ := 2 * π * t / n with hθ
  have hpsi : ZMod.stdAddChar x = Complex.exp (θ * Complex.I) := by
    rw [← hx, ZMod.stdAddChar_coe]
    congr 1
    rw [hθ]
    push_cast
    ring
  have hθbound : |θ| ≤ π := by
    obtain ⟨h1, h2⟩ := ZMod.valMinAbs_mem_Ioc x
    have h1' : -(n : ℝ) < t * 2 := by exact_mod_cast h1
    have h2' : (t : ℝ) * 2 ≤ n := by exact_mod_cast h2
    rw [abs_le]
    constructor
    · rw [hθ, le_div_iff₀ hn]
      nlinarith [pi_pos]
    · rw [hθ, div_le_iff₀ hn]
      nlinarith [pi_pos]
  have hcos := Real.cos_le_one_sub_mul_cos_sq hθbound
  have hnorm : ‖1 + Complex.exp (θ * Complex.I)‖ ^ 2 = 2 + 2 * Real.cos θ := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    rw [show (1 : ℂ) + (↑(Real.cos θ) + ↑(Real.sin θ) * Complex.I)
        = ↑(1 + Real.cos θ) + ↑(Real.sin θ) * Complex.I by push_cast; ring]
    rw [Complex.norm_add_mul_I, Real.sq_sqrt (by positivity)]
    linear_combination Real.sin_sq_add_cos_sq θ
  rw [hpsi, hnorm]
  have : 2 / π ^ 2 * θ ^ 2 = 8 * ((t : ℝ) / n) ^ 2 := by
    rw [hθ]
    field_simp
    ring
  linarith

end Fourier

/-! ### Step 2: few primes of size `≥ y` divide a nonzero integer -/

lemma pow_card_le_of_primes_dvd (A : Finset ℕ) (y : ℝ) (hy : 0 ≤ y)
    (hA : ∀ a ∈ A, a.Prime ∧ y ≤ a) (z : ℤ) (hz : z ≠ 0) (hdvd : ∀ a ∈ A, (a : ℤ) ∣ z) :
    y ^ A.card ≤ |(z : ℝ)| := by
  have h1 : ∏ a ∈ A, a ∣ z.natAbs := by
    apply Finset.prod_primes_dvd
    · intro a ha
      exact (hA a ha).1.prime
    · intro a ha
      exact Int.ofNat_dvd_left.1 (hdvd a ha)
  have h2 : ∏ a ∈ A, a ≤ z.natAbs := Nat.le_of_dvd (Int.natAbs_pos.2 hz) h1
  calc y ^ A.card = ∏ a ∈ A, y := (Finset.prod_const y).symm
  _ ≤ ∏ a ∈ A, (a : ℝ) := Finset.prod_le_prod (fun _ _ => hy) (fun a ha => (hA a ha).2)
  _ = ((∏ a ∈ A, a : ℕ) : ℝ) := by push_cast; rfl
  _ ≤ (z.natAbs : ℝ) := by exact_mod_cast h2
  _ = |(z : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]

/-- The pigeonhole step: few `r` have `|r t_r|` small. -/
lemma card_bad_le (n H : ℕ) (hH0 : 0 < H) (hHn : H < n)
    (R : Finset ℕ) (y : ℝ) (hy : 1 ≤ y) (hR : ∀ r ∈ R, r.Prime ∧ y ≤ r)
    (t : ℕ → ℤ) (ht : ∀ r ∈ R, (n : ℤ) ∣ r * t r - H)
    (L : ℝ) (hL : 0 ≤ L) (m : ℕ) (hm : (L + 2) * n < y ^ (m + 1)) :
    ((R.filter (fun r : ℕ => |(r : ℝ) * t r| ≤ L * n)).card : ℝ) ≤ (2 * (L + 1) + 1) * m := by
  set M : ℤ := ⌊L + 1⌋ with hM
  have hM0 : 0 ≤ M := Int.floor_nonneg.2 (by linarith)
  have hML : (M : ℝ) ≤ L + 1 := Int.floor_le _
  have hn : (0 : ℝ) < n := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hHn)
  have hHnR : (H : ℝ) < n := by exact_mod_cast hHn
  have hH0R : (0 : ℝ) < H := by exact_mod_cast hH0
  -- each fibre is small
  have hfib : ∀ v ∈ Finset.Icc (-M) M,
      (R.filter (fun r : ℕ => (r : ℤ) ∣ H + n * v)).card ≤ m := by
    intro v hv
    rw [Finset.mem_Icc] at hv
    have hvR : |(v : ℝ)| ≤ L + 1 := by
      rw [abs_le]
      have h1 : ((-M : ℤ) : ℝ) ≤ v := by exact_mod_cast hv.1
      have h2 : (v : ℝ) ≤ (M : ℝ) := by exact_mod_cast hv.2
      push_cast at h1
      constructor <;> linarith
    have hz : (H : ℤ) + n * v ≠ 0 := by
      intro h0
      have h0' : (H : ℝ) + n * v = 0 := by exact_mod_cast h0
      rcases le_or_gt 0 (v : ℝ) with hv0 | hv0
      · nlinarith
      · have : (v : ℝ) ≤ -1 := by
          have : v ≤ -1 := by
            have : v < 0 := by exact_mod_cast hv0
            omega
          exact_mod_cast this
        nlinarith
    have hzabs : |(((H : ℤ) + n * v : ℤ) : ℝ)| < (L + 2) * n := by
      push_cast
      calc |(H : ℝ) + n * v| ≤ |(H : ℝ)| + |(n : ℝ) * v| := abs_add_le _ _
      _ = H + n * |(v : ℝ)| := by
          rw [abs_mul, abs_of_nonneg hH0R.le, abs_of_nonneg hn.le]
      _ < n + n * (L + 1) := by nlinarith
      _ = (L + 2) * n := by ring
    have hpow := pow_card_le_of_primes_dvd (R.filter (fun r : ℕ => (r : ℤ) ∣ H + n * v)) y
      (by linarith)
      (fun r hr => hR r (Finset.mem_filter.1 hr).1) _ hz (fun r hr => (Finset.mem_filter.1 hr).2)
    by_contra hcon
    push Not at hcon
    have : y ^ (m + 1) ≤ y ^ (R.filter (fun r : ℕ => (r : ℤ) ∣ H + n * v)).card :=
      pow_le_pow_right₀ hy hcon
    linarith
  -- the bad set is covered by the fibres
  have hsub : R.filter (fun r : ℕ => |(r : ℝ) * t r| ≤ L * n) ⊆
      (Finset.Icc (-M) M).biUnion (fun v => R.filter (fun r : ℕ => (r : ℤ) ∣ H + n * v)) := by
    intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨hrR, hrbad⟩ := hr
    obtain ⟨v, hv⟩ := ht r hrR
    have hvR : ((r : ℝ) * t r - H) = n * v := by exact_mod_cast hv
    rw [Finset.mem_biUnion]
    refine ⟨v, ?_, ?_⟩
    · have h1 : (n : ℝ) * |(v : ℝ)| < (L + 1) * n := by
        calc (n : ℝ) * |(v : ℝ)| = |(n : ℝ) * v| := by rw [abs_mul, abs_of_pos hn]
        _ = |(r : ℝ) * t r - H| := by rw [hvR]
        _ ≤ |(r : ℝ) * t r| + |(H : ℝ)| := abs_sub _ _
        _ < L * n + n := by rw [abs_of_nonneg hH0R.le]; linarith
        _ = (L + 1) * n := by ring
      have h2 : |(v : ℝ)| < L + 1 := by
        by_contra hcon
        push Not at hcon
        nlinarith
      rw [abs_lt] at h2
      rw [Finset.mem_Icc]
      constructor
      · have : -v ≤ M := Int.le_floor.2 (by push_cast; linarith)
        linarith
      · exact Int.le_floor.2 (by linarith)
    · rw [Finset.mem_filter]
      refine ⟨hrR, ⟨t r, ?_⟩⟩
      linear_combination -hv
  have hcard : (R.filter (fun r : ℕ => |(r : ℝ) * t r| ≤ L * n)).card ≤ (2 * M.toNat + 1) * m := by
    calc (R.filter (fun r : ℕ => |(r : ℝ) * t r| ≤ L * n)).card
        ≤ ((Finset.Icc (-M) M).biUnion
            (fun v => R.filter (fun r : ℕ => (r : ℤ) ∣ H + n * v))).card := Finset.card_le_card hsub
    _ ≤ ∑ v ∈ Finset.Icc (-M) M, (R.filter (fun r : ℕ => (r : ℤ) ∣ H + n * v)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ v ∈ Finset.Icc (-M) M, m := Finset.sum_le_sum hfib
    _ = (2 * M.toNat + 1) * m := by
        rw [Finset.sum_const, Int.card_Icc, smul_eq_mul]
        congr 1
        omega
  have hMnat : ((M.toNat : ℕ) : ℝ) = (M : ℝ) := by
    have : ((M.toNat : ℕ) : ℤ) = M := Int.toNat_of_nonneg hM0
    exact_mod_cast this
  calc ((R.filter (fun r : ℕ => |(r : ℝ) * t r| ≤ L * n)).card : ℝ)
      ≤ (((2 * M.toNat + 1) * m : ℕ) : ℝ) := by exact_mod_cast hcard
  _ = (2 * (M : ℝ) + 1) * m := by push_cast; rw [hMnat]
  _ ≤ (2 * (L + 1) + 1) * m := by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      linarith

/-! ### Step 3: elementary inequalities for large `w` -/

lemma ineq_bad (w : ℝ) (hw : 10 ≤ w) :
    (2 * (w ^ 28 + 1) + 1) * (2 * w ^ 10) ≤ w ^ 39 / 2 := by
  have h10 : 0 < w ^ 10 := by positivity
  have h28 : 6 ≤ w ^ 28 := by
    calc (6 : ℝ) ≤ 10 ^ 28 := by norm_num
    _ ≤ w ^ 28 := pow_le_pow_left₀ (by norm_num) hw 28
  have e1 : w ^ 38 = w ^ 28 * w ^ 10 := by ring
  have e2 : w ^ 39 = w * w ^ 38 := by ring
  have h38 : 6 * w ^ 10 ≤ w ^ 38 := by rw [e1]; nlinarith
  have h38' : 0 ≤ w ^ 38 := by positivity
  have h39 : 10 * w ^ 38 ≤ w ^ 39 := by rw [e2]; nlinarith
  have : (2 * (w ^ 28 + 1) + 1) * (2 * w ^ 10) = 4 * w ^ 38 + 6 * w ^ 10 := by ring
  rw [this]
  linarith

lemma ineq_good (w : ℝ) (hw : 10 ≤ w) :
    2 * w ^ 10 ≤ (w ^ 39 / 2) * (4 / (9 * w ^ 24)) := by
  have hw0 : 0 < w := by linarith
  have e : (w ^ 39 / 2) * (4 / (9 * w ^ 24)) = 2 / 9 * w ^ 15 := by
    field_simp
    ring
  rw [e]
  have h5 : 9 ≤ w ^ 5 := by
    calc (9 : ℝ) ≤ 10 ^ 5 := by norm_num
    _ ≤ w ^ 5 := pow_le_pow_left₀ (by norm_num) hw 5
  have e2 : w ^ 15 = w ^ 5 * w ^ 10 := by ring
  rw [e2]
  have h10 : 0 < w ^ 10 := by positivity
  nlinarith

lemma ineq_exp (w : ℝ) (hw : 10 ≤ w) : w ^ 28 + 2 ≤ Real.exp (w ^ 10) := by
  have h := Real.pow_div_factorial_le_exp (w ^ 10) (by positivity) 3
  have hf : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [hf] at h
  have e : (w ^ 10) ^ 3 = w ^ 2 * w ^ 28 := by ring
  rw [e] at h
  have h2 : 100 ≤ w ^ 2 := by nlinarith
  have h28 : 1 ≤ w ^ 28 := one_le_pow₀ (by linarith)
  nlinarith [mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ w ^ 28)]

lemma ineq_e (w : ℝ) (hw : 10 ≤ w) : Real.exp 1 ≤ w ^ 40 / 4 := by
  have h := Real.exp_one_lt_three
  have : (10 : ℝ) ^ 40 ≤ w ^ 40 := pow_le_pow_left₀ (by norm_num) hw 40
  have h' : (3 : ℝ) ≤ 10 ^ 40 / 4 := by norm_num
  linarith

/-! ### Step 4: the bound on each nontrivial Fourier coefficient -/

theorem norm_prod_le (n : ℕ) [NeZero n] (w : ℝ) (hw : 10 ≤ w)
    (hn_exp : (n : ℝ) = Real.exp (w ^ 10))
    (R : Finset ℕ) (hR : ∀ r ∈ R, r.Prime ∧ ¬ r ∣ n ∧ w ^ 40 / 4 ≤ r ∧ (r : ℝ) ≤ 3 * w ^ 40)
    (hk : w ^ 39 ≤ R.card) (h : ZMod n) (hh : h ≠ 0) :
    ‖∏ r ∈ R, (1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹))‖ ≤ 2 ^ R.card / n := by
  have hw0 : 0 < w := by linarith
  have hnpos : (0 : ℝ) < n := by rw [hn_exp]; exact Real.exp_pos _
  set H := h.val with hHdef
  have hH0 : 0 < H := ZMod.val_pos.2 hh
  have hHn : H < n := ZMod.val_lt h
  set t : ℕ → ℤ := fun r => (h * ((r : ZMod n))⁻¹).valMinAbs with htdef
  have hdiv : ∀ r ∈ R, (n : ℤ) ∣ r * t r - H := by
    intro r hr
    have hcop : Nat.Coprime r n := ((hR r hr).1.coprime_iff_not_dvd).2 (hR r hr).2.1
    have h1 : (((r : ℤ) * t r : ℤ) : ZMod n) = ((H : ℤ) : ZMod n) := by
      push_cast
      simp only [htdef, ZMod.coe_valMinAbs, hHdef, ZMod.natCast_zmod_val]
      rw [mul_left_comm, ZMod.coe_mul_inv_eq_one r hcop, mul_one]
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ n).1 h1.symm
  set L : ℝ := w ^ 28 with hLdef
  set B := R.filter (fun r : ℕ => |(r : ℝ) * t r| ≤ L * n) with hBdef
  set G := R.filter (fun r : ℕ => ¬ |(r : ℝ) * t r| ≤ L * n) with hGdef
  have hBG : B.card + G.card = R.card := Finset.card_filter_add_card_filter_not _
  -- few bad primes
  have hBcard : (B.card : ℝ) ≤ (2 * (L + 1) + 1) * ⌊2 * w ^ 10⌋₊ := by
    have he := ineq_e w hw
    apply card_bad_le n H hH0 hHn R (w ^ 40 / 4) _ _ t hdiv L (by positivity)
    · -- (L + 2) * n < y ^ (m + 1)
      have hL2 : L + 2 ≤ n := by rw [hn_exp, hLdef]; exact ineq_exp w hw
      have h1 : (L + 2) * n ≤ (n : ℝ) * n := mul_le_mul_of_nonneg_right hL2 hnpos.le
      have h2 : (n : ℝ) * n = Real.exp (2 * w ^ 10) := by
        rw [hn_exp, ← Real.exp_add]; ring_nf
      have h3 : Real.exp (2 * w ^ 10) < Real.exp ((⌊2 * w ^ 10⌋₊ + 1 : ℕ) : ℝ) := by
        rw [Real.exp_lt_exp]
        push_cast
        exact Nat.lt_floor_add_one _
      have h4 : Real.exp ((⌊2 * w ^ 10⌋₊ + 1 : ℕ) : ℝ) = Real.exp 1 ^ (⌊2 * w ^ 10⌋₊ + 1) :=
        (Real.exp_one_pow _).symm
      have h5 : Real.exp 1 ^ (⌊2 * w ^ 10⌋₊ + 1) ≤ (w ^ 40 / 4) ^ (⌊2 * w ^ 10⌋₊ + 1) :=
        pow_le_pow_left₀ (Real.exp_pos 1).le he _
      linarith
    · have : (1 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp 0
        simp at this
        linarith [Real.add_one_le_exp 1]
      linarith
    · intro r hr
      exact ⟨(hR r hr).1, (hR r hr).2.2.1⟩
  have hBhalf : (B.card : ℝ) ≤ R.card / 2 := by
    have h1 : (⌊2 * w ^ 10⌋₊ : ℝ) ≤ 2 * w ^ 10 := Nat.floor_le (by positivity)
    have h2 : (2 * (L + 1) + 1) * (⌊2 * w ^ 10⌋₊ : ℝ) ≤ (2 * (L + 1) + 1) * (2 * w ^ 10) := by
      apply mul_le_mul_of_nonneg_left h1
      positivity
    have h3 : (2 * (L + 1) + 1) * (2 * w ^ 10) ≤ w ^ 39 / 2 := by
      rw [hLdef]; exact ineq_bad w hw
    linarith
  have hGcard : w ^ 39 / 2 ≤ (G.card : ℝ) := by
    have : (B.card : ℝ) + G.card = R.card := by exact_mod_cast hBG
    linarith
  -- per-factor bounds
  have hfac : ∀ r ∈ R, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2
      ≤ 4 - 16 * ((t r : ℝ) / n) ^ 2 :=
    fun r _ => norm_one_add_stdAddChar_sq_le _
  set a : ℝ := 4 / (9 * w ^ 24) with hadef
  have hgood : ∀ r ∈ G, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2
      ≤ 4 * Real.exp (-a) := by
    intro r hr
    rw [hGdef, Finset.mem_filter] at hr
    obtain ⟨hrR, hrgood⟩ := hr
    push Not at hrgood
    have hr3 : (r : ℝ) ≤ 3 * w ^ 40 := (hR r hrR).2.2.2
    have hrpos : (0 : ℝ) < r := by exact_mod_cast (hR r hrR).1.pos
    have key : (n : ℝ) < 3 * w ^ 12 * |(t r : ℝ)| := by
      rw [abs_mul, abs_of_pos hrpos] at hrgood
      have : w ^ 28 * n < w ^ 28 * (3 * w ^ 12 * |(t r : ℝ)|) := by
        calc w ^ 28 * (n : ℝ) = L * n := by rw [hLdef]
        _ < r * |(t r : ℝ)| := hrgood
        _ ≤ 3 * w ^ 40 * |(t r : ℝ)| := mul_le_mul_of_nonneg_right hr3 (abs_nonneg _)
        _ = w ^ 28 * (3 * w ^ 12 * |(t r : ℝ)|) := by ring
      exact lt_of_mul_lt_mul_left this (by positivity)
    have key2 : 1 / (9 * w ^ 24) ≤ ((t r : ℝ) / n) ^ 2 := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      have : (n : ℝ) ^ 2 < (3 * w ^ 12 * |(t r : ℝ)|) ^ 2 :=
        pow_lt_pow_left₀ key hnpos.le (by norm_num)
      calc 1 * (n : ℝ) ^ 2 ≤ (3 * w ^ 12 * |(t r : ℝ)|) ^ 2 := by linarith
      _ = (t r : ℝ) ^ 2 * (9 * w ^ 24) := by rw [mul_pow, mul_pow, sq_abs]; ring
    have hexp : 1 - a ≤ Real.exp (-a) := by linarith [Real.add_one_le_exp (-a)]
    calc ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2
        ≤ 4 - 16 * ((t r : ℝ) / n) ^ 2 := hfac r hrR
    _ ≤ 4 - 16 * (1 / (9 * w ^ 24)) := by linarith
    _ = 4 * (1 - a) := by rw [hadef]; ring
    _ ≤ 4 * Real.exp (-a) := by linarith
  have hbad : ∀ r ∈ R, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2 ≤ 4 := by
    intro r hr
    have := hfac r hr
    nlinarith [sq_nonneg ((t r : ℝ) / n)]
  -- the product
  have hprod : ‖∏ r ∈ R, (1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹))‖ ^ 2
      ≤ 4 ^ R.card * Real.exp (-(2 * w ^ 10)) := by
    rw [norm_prod, ← Finset.prod_pow,
      ← Finset.prod_filter_mul_prod_filter_not R (fun r : ℕ => |(r : ℝ) * t r| ≤ L * n)]
    have hB' : ∏ r ∈ B, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2 ≤ 4 ^ B.card := by
      calc ∏ r ∈ B, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2 ≤ ∏ r ∈ B, (4 : ℝ) :=
            Finset.prod_le_prod (fun _ _ => by positivity)
              (fun r hr => hbad r (Finset.mem_filter.1 hr).1)
      _ = 4 ^ B.card := Finset.prod_const _
    have hG' : ∏ r ∈ G, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2
        ≤ (4 * Real.exp (-a)) ^ G.card := by
      calc ∏ r ∈ G, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2
          ≤ ∏ r ∈ G, (4 * Real.exp (-a)) :=
            Finset.prod_le_prod (fun _ _ => by positivity) hgood
      _ = (4 * Real.exp (-a)) ^ G.card := Finset.prod_const _
    have hexpG : Real.exp (-a) ^ G.card ≤ Real.exp (-(2 * w ^ 10)) := by
      rw [← Real.exp_nat_mul, Real.exp_le_exp]
      have ha : 0 ≤ a := by positivity
      have : 2 * w ^ 10 ≤ G.card * a := by
        calc 2 * w ^ 10 ≤ (w ^ 39 / 2) * a := by rw [hadef]; exact ineq_good w hw
        _ ≤ G.card * a := mul_le_mul_of_nonneg_right hGcard ha
      linarith
    calc (∏ r ∈ B, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2) *
          ∏ r ∈ G, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2
        ≤ 4 ^ B.card * (4 * Real.exp (-a)) ^ G.card :=
          mul_le_mul hB' hG' (Finset.prod_nonneg fun _ _ => by positivity) (by positivity)
    _ = 4 ^ R.card * Real.exp (-a) ^ G.card := by
          rw [mul_pow, ← mul_assoc, ← pow_add, hBG]
    _ ≤ 4 ^ R.card * Real.exp (-(2 * w ^ 10)) :=
          mul_le_mul_of_nonneg_left hexpG (by positivity)
  have hfinal : (2 ^ R.card / (n : ℝ)) ^ 2 = 4 ^ R.card * Real.exp (-(2 * w ^ 10)) := by
    have e1 : Real.exp (w ^ 10) ^ 2 = Real.exp (2 * w ^ 10) := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [hn_exp, div_pow, e1, Real.exp_neg, div_eq_mul_inv, ← pow_mul, mul_comm R.card 2,
      pow_mul]
    norm_num
  rw [← hfinal] at hprod
  exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hprod

end Lemma1Aux

/-! ### Step 5: Croot's Lemma 1 -/

theorem lemma1 : ∀ᶠ n : ℕ in atTop, ∀ R : Finset ℕ,
    (∀ r ∈ R, r.Prime ∧ ¬ r ∣ n ∧ (Real.log n) ^ 4 / 4 ≤ r ∧ (r : ℝ) ≤ 3 * (Real.log n) ^ 4) →
    (Real.log n) ^ (39 / 10 : ℝ) ≤ R.card →
    ∀ c : ZMod n, ∃ T ⊆ R, ∑ r ∈ T, ((r : ZMod n))⁻¹ = c := by
  have hw : ∀ᶠ n : ℕ in atTop, (10 : ℝ) ≤ (Real.log n) ^ (1 / 10 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually_ge_atTop 10
  filter_upwards [hw, eventually_ge_atTop 2] with n hwn hn2 R hR hk c
  have : NeZero n := ⟨by omega⟩
  set w := (Real.log n) ^ (1 / 10 : ℝ) with hwdef
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlogpos : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hlog : Real.log n = w ^ 10 := by
    rw [hwdef, ← Real.rpow_natCast, ← Real.rpow_mul hlogpos]
    norm_num
  have hn_exp : (n : ℝ) = Real.exp (w ^ 10) := by
    rw [← hlog, Real.exp_log hnpos]
  have h4 : (Real.log n) ^ 4 = w ^ 40 := by rw [hlog]; ring
  have h39 : (Real.log n) ^ (39 / 10 : ℝ) = w ^ 39 := by
    rw [hwdef, ← Real.rpow_natCast, ← Real.rpow_mul hlogpos]
    norm_num
  refine Lemma1Aux.exists_subset_sum_of_norm_prod_le R (fun r => ((r : ZMod n))⁻¹) ?_ c
  intro h hh
  refine Lemma1Aux.norm_prod_le n w hwn hn_exp R ?_ ?_ h hh
  · intro r hr
    obtain ⟨h1, h2, h3, h5⟩ := hR r hr
    rw [h4] at h3 h5
    exact ⟨h1, h2, h3, h5⟩
  · rw [← h39]
    exact hk

end Croot

open Finset Filter Real
open scoped BigOperators

private lemma split297 (P : Finset ℕ) (x b : ℝ)
    (h : ∀ r ∈ P, x ≤ r ∧ (r:ℝ) ≤ 27/10*x) (hc : 2*b ≤ P.card)
    (hx : 0≤x) :
    ∃ (a : ℝ) (S : Finset ℕ), S ⊆ P ∧ b ≤ S.card ∧ x ≤ a ∧ a ≤ 2*x ∧
      ∀ r ∈ S, a ≤ r ∧ (r:ℝ) ≤ (5/3)*a := by
  classical
  let Q := P.filter fun r : ℕ => (r:ℝ) ≤ 5/3*x
  by_cases first : b ≤ Q.card
  · refine ⟨x,Q,filter_subset _ _,first,le_rfl,by linarith,?_⟩
    intro r hr
    obtain ⟨hP,hm⟩ := mem_filter.mp hr
    exact ⟨(h r hP).1,hm⟩
  · have hcard := card_sdiff_add_card_eq_card (show Q ⊆ P from filter_subset _ _)
    have hc' : ((P\Q).card:ℝ) + Q.card = P.card := by exact_mod_cast hcard
    refine ⟨5/3*x,P\Q,sdiff_subset,by push_neg at first; linarith,by linarith,by linarith,?_⟩
    intro r hr
    obtain ⟨hP,hm⟩ := mem_sdiff.mp hr
    have hl : ¬ (r:ℝ) ≤ 5/3*x := fun he => hm (mem_filter.mpr ⟨hP,he⟩)
    exact ⟨by linarith,by linarith [(h r hP).2]⟩

theorem shortPrimes297 (ε : ℝ) (he : 0<ε) :
    ∀ᶠ i : ℕ in atTop, ∀ p : ℕ, p.Prime →
      ∃ (a : ℝ) (S : Finset ℕ), 0<a ∧ 100*a ≤ (i:ℝ)^ε ∧
        (S.card:ℝ) ≤ (i:ℝ)^(ε/2) ∧ (log i)^(39/10:ℝ) ≤ S.card ∧
        ∀ r ∈ S, r.Prime ∧ r ≠ p ∧ 3<r ∧ (log i)^4/4 ≤ r ∧ (r:ℝ) ≤ 3*(log i)^4 ∧
          a ≤ r ∧ (r:ℝ) ≤ 5/3*a := by
  have Ltop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have Xtop : Tendsto (fun i : ℕ => (log i)^4) atTop atTop :=
    (tendsto_pow_atTop (by decide : 4 ≠ 0)).comp Ltop
  have ho := ((isLittleO_log_rpow_rpow_atTop (4:ℝ) (show 0 < ε/2 by linarith)).bound
    (show (0:ℝ)<1/500 by norm_num))
  filter_upwards [Xtop.eventually Croot.eventually_card_primes_Ioc_ge,
    Ltop.eventually (Croot.eventually_L_conds 10),
    tendsto_natCast_atTop_atTop.eventually ho, eventually_ge_atTop 2] with i hP hL hrate hi
  intro p hp
  let L := log (i:ℝ)
  let X := L^4
  let P := (Ioc ⌊X⌋₊ ⌊27/10*X⌋₊).filter Nat.Prime
  have L1 : 1 ≤ L := hL.1
  have Xbig : 10 ≤ X/4 := hL.2.1
  have hXp : 0<X := by linarith
  have Lbig : 1<L := by
    by_contra! h
    have e : L=1 := le_antisymm h L1
    simp [X,e] at Xbig
    norm_num at Xbig
  have ll : 0<log L := log_pos Lbig
  have hlogx : log X = 4 * log L := by simp [X,Real.log_pow]
  change X/(5*log X) ≤ (P.card:ℝ) at hP
  rw [hlogx] at hP
  have hc := hL.2.2.2
  change L^(39/10:ℝ) ≤ X/(80*log L)-18*L-1 at hc
  have frac : X/(5*(4*log L)) = 4*(X/(80*log L)) := by ring
  rw [frac] at hP
  have hecard : P.card ≤ (P.erase p).card + 1 := by
    by_cases hpm : p∈P
    · exact (card_erase_add_one hpm).ge
    · simp [erase_eq_of_notMem hpm]
  have hecard' : (P.card:ℝ) ≤ ((P.erase p).card:ℝ)+1 := by exact_mod_cast hecard
  have count : 2*L^(39/10:ℝ) ≤ ((P.erase p).card:ℝ) := by
    have hpos := Real.rpow_nonneg (by linarith : 0≤L) (39/10:ℝ)
    linarith
  have props (r : ℕ) (hr : r ∈ P.erase p) :
      r.Prime ∧ r ≠ p ∧ X ≤ r ∧ (r:ℝ) ≤ 27/10*X := by
    obtain ⟨ne, hP⟩ := mem_erase.mp hr
    obtain ⟨mem,pr⟩ := mem_filter.mp hP
    obtain ⟨lo,up⟩ := mem_Ioc.mp mem
    exact ⟨pr,ne,(Nat.lt_of_floor_lt lo).le, (Nat.le_floor_iff (by positivity)).mp up⟩
  obtain ⟨a,S,sub,num,ax,au,mem⟩ := split297 (P.erase p) X (L^(39/10:ℝ))
    (fun r h => (props r h).2.2) count hXp.le
  have ip : 1 ≤ (i:ℝ) := by exact_mod_cast (show 1 ≤ i from by omega)
  have hhalf : (i:ℝ)^(ε/2) ≤ (i:ℝ)^ε := Real.rpow_le_rpow_of_exponent_le ip (by linarith)
  have xx : X ≤ 1/500 * (i:ℝ)^(ε/2) := by
    simpa [X,L,Real.rpow_natCast, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg ip),
      abs_of_nonneg (Real.rpow_nonneg (by positivity : 0≤(i:ℝ)) (ε/2))] using hrate
  have bound : S.card ≤ ⌊27/10*X⌋₊ := by
    calc
      _ ≤ (Ioc ⌊X⌋₊ ⌊27/10*X⌋₊).card :=
        card_le_card (sub.trans ((erase_subset _ _).trans (filter_subset _ _)))
      _ ≤ _ := by rw [Nat.card_Ioc]; omega
  have bc := (Nat.le_floor_iff (by positivity : 0 ≤ 27/10*X)).mp bound
  refine ⟨a,S,by linarith,by linarith,by linarith,num,?_⟩
  intro r hr
  obtain ⟨pr,ne,lo,up⟩ := props r (sub hr)
  have r3 : (3:ℝ)<r := by linarith
  exact ⟨pr,ne,by exact_mod_cast r3,by linarith,by linarith,mem r hr⟩


open Finset Real
open scoped BigOperators

private lemma multiplier297 {p : ℕ} (hp : p.Prime) (x : ℝ) (hx : 100 ≤ x) :
    ∃ u : ℕ, x ≤ u ∧ (u:ℝ) ≤ 6/5*x ∧ p.Coprime u ∧ ¬2∣u ∧ ¬3∣u := by
  let c := ⌈x/6⌉₊
  let v := 6*c+1
  let u := if p ∣ v then v+6 else v
  have vl : v ≤ u ∧ u ≤ v+6 := by dsimp [u]; split <;> omega
  have lo : x/6 ≤ (c:ℝ) := Nat.le_ceil _
  have up : (c:ℝ) < x/6+1 := Nat.ceil_lt_add_one (by linarith)
  have vdef : (v:ℝ) = 6*(c:ℝ)+1 := by dsimp [v]; push_cast; ring
  have l' : (v:ℝ) ≤ u := by exact_mod_cast vl.1
  have u' : (u:ℝ) ≤ (v:ℝ)+6 := by exact_mod_cast vl.2
  refine ⟨u,by linarith,by linarith,hp.coprime_iff_not_dvd.mpr ?_,?_,?_⟩
  · dsimp only [u]
    split_ifs with hd
    · intro h
      have hs := (Nat.dvd_add_right hd).mp h
      have hv : p ∣ 6*c := dvd_mul_of_dvd_left hs _
      exact hp.not_dvd_one ((Nat.dvd_add_right hv).mp hd)
    · exact hd
  · dsimp only [u,v]; split <;> omega
  · dsimp only [u,v]; split <;> omega

lemma rescale297 {p k : ℕ} (hp : p.Prime) {a Y : ℝ} (ha : 0 < a) (hY : 100*a ≤ Y)
    (S : Finset ℕ) (mem : ∀ r∈S, r.Prime ∧ r ≠ p ∧ 3<r ∧ a ≤ r ∧ (r:ℝ) ≤ 5/3*a)
    (full : ∀ c : ZMod (p^k), ∃ T ⊆ S, ∑ r ∈ T, (r : ZMod (p^k))⁻¹ = c)
    (z : ZMod (p^k)) :
    ∃ M : Finset ℕ, M.card ≤ S.card ∧
      (∀ m∈M, (p^k).Coprime m ∧ Y ≤ m ∧ (m:ℝ) ≤ 2*Y ∧ ¬6∣p^k*m) ∧
      ∑ m ∈ M, (m : ZMod (p^k))⁻¹ = z := by
  obtain ⟨u,lo,up,cop,u2,u3⟩ := multiplier297 hp (Y/a) ((le_div_iff₀ ha).mpr hY)
  have ua : Y ≤ (u:ℝ)*a := (div_le_iff₀ ha).mp lo
  have ub : (u:ℝ)*a ≤ 6/5*Y := (le_div_iff₀ ha).mp (show (u:ℝ) ≤ (6/5*Y)/a by
    convert up using 1 <;> ring)
  have upos : 0<u := by
    have h : (0:ℝ) < Y/a := by apply div_pos _ ha; nlinarith
    exact_mod_cast h.trans_le lo
  obtain ⟨T,hTS,hT⟩ := full ((u:ZMod (p^k))*z)
  have cu := ZMod.coe_mul_inv_eq_one (n := p^k) u (cop.pow_left k).symm
  refine ⟨T.image (u*·),card_image_le.trans (card_le_card hTS),?_,?_⟩
  · intro m hm
    obtain ⟨r,hr,rfl⟩ := mem_image.mp hm
    obtain ⟨pr,ne,r3,ar,ra⟩ := mem r (hTS hr)
    have cr := (Nat.coprime_primes hp pr).mpr ne.symm
    have u0 : (0:ℝ) ≤ u := by positivity
    have low := mul_le_mul_of_nonneg_left ar u0
    have high := mul_le_mul_of_nonneg_left ra u0
    push_cast
    refine ⟨(cop.mul_right cr).pow_left _,by linarith,by linarith,?_⟩
    intro bad
    have nr2 : ¬2∣r := fun h => by have := (Nat.dvd_prime pr).mp h; omega
    have nr3 : ¬3∣r := fun h => by have := (Nat.dvd_prime pr).mp h; omega
    have go (q : ℕ) (hq : q.Prime) (h6 : q∣6) (hu : ¬q∣u) (hr : ¬q∣r) : q∣p := by
      have h := hq.dvd_mul.mp (h6.trans bad)
      exact hq.dvd_of_dvd_pow (h.resolve_right (fun h => (hq.dvd_mul.mp h).elim hu hr))
    have := (Nat.dvd_prime hp).mp (go 2 Nat.prime_two (by decide) u2 nr2)
    have := (Nat.dvd_prime hp).mp (go 3 Nat.prime_three (by decide) u3 nr3)
    omega
  · rw [sum_image (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left upos h)]
    have per (r : ℕ) (hr : r∈T) :
        ((u*r:ℕ):ZMod (p^k))⁻¹ = (u:ZMod (p^k))⁻¹ * (r:ZMod (p^k))⁻¹ := by
      obtain ⟨pr,ne,_⟩ := mem r (hTS hr)
      have cr := ZMod.coe_mul_inv_eq_one (n := p^k) r (((Nat.coprime_primes pr hp).mpr ne).pow_right k)
      apply ZMod.inv_eq_of_mul_eq_one
      push_cast
      calc
        _ = ((u:ZMod (p^k))*(u:ZMod (p^k))⁻¹) * ((r:ZMod (p^k))*(r:ZMod (p^k))⁻¹) := by ring
        _ = _ := by rw [cu, cr, mul_one]
    rw [sum_congr rfl per, ← mul_sum, hT, ← mul_assoc, mul_comm ((u:ZMod (p^k))⁻¹), cu, one_mul]


open Finset Filter Real

theorem sparse297 (ε : ℝ) (he : 0<ε) :
    ∀ᶠ i : ℕ in atTop, IsPrimePow i → ∀ z : ZMod i, ∃ M : Finset ℕ,
      (M.card:ℝ) ≤ (i:ℝ)^(ε/2) ∧
      (∀ m ∈ M, i.Coprime m ∧ (i:ℝ)^ε ≤ m ∧ (m:ℝ) ≤ 2*(i:ℝ)^ε ∧ ¬6∣i*m) ∧
      ∑ m ∈ M, (m:ZMod i)⁻¹ = z := by
  filter_upwards [shortPrimes297 ε he,Croot.lemma1] with i window full
  intro pp z
  obtain ⟨p,k,hp,hk,rfl⟩ := (isPrimePow_nat_iff _).mp pp
  obtain ⟨a,S,ha,hY,card,count,mem⟩ := window p hp
  have good (r : ℕ) (hr : r∈S) :
      r.Prime ∧ ¬ r∣p^k ∧ (log (p^k:ℕ))^4/4 ≤ r ∧ (r:ℝ) ≤ 3*(log (p^k:ℕ))^4 := by
    obtain ⟨pr,ne,_,lo,hi,_⟩ := mem r hr
    refine ⟨pr,fun h => ?_,lo,hi⟩
    exact ne ((Nat.dvd_prime hp).mp (pr.dvd_of_dvd_pow h) |>.resolve_left pr.ne_one)
  have Sgood (r : ℕ) (hr : r∈S) := mem r hr
  obtain ⟨M,mc,md,ms⟩ := rescale297 (k := k) hp ha hY S
    (fun r hr => ⟨(Sgood r hr).1,(Sgood r hr).2.1,(Sgood r hr).2.2.1,(Sgood r hr).2.2.2.2.2⟩)
    (full S good count) z
  exact ⟨M,(show (M.card:ℝ) ≤ S.card by exact_mod_cast mc).trans card,md,ms⟩


open Finset Filter Nat
open scoped Classical
namespace Egyptian

lemma ongrid {m i : ℕ} (hm : 0 < m) (hmi : m ≤ i) : m ∣ lcmUpto i :=
  Finset.dvd_lcm (f := id) (mem_Icc.mpr ⟨hm,hmi⟩)

lemma unchanged {i : ℕ} (hi : 1 < i) (h : ¬ IsPrimePow i) :
    lcmUpto i = lcmUpto (i-1) := by
  have nz : i ≠ 0 := by omega
  have last : i ∣ lcmUpto (i-1) := by
    apply (Nat.factorization_prime_le_iff_dvd nz (lcmUpto_ne_zero _)).mp
    intro p hp
    apply (hp.pow_dvd_iff_le_factorization (lcmUpto_ne_zero _)).mp
    have hd := (hp.pow_dvd_iff_le_factorization nz).mpr (le_refl (i.factorization p))
    apply ongrid (pow_pos hp.pos _)
    have hl := Nat.le_of_dvd (by omega : 0 < i) hd
    by_contra! hf
    have eq : p ^ i.factorization p = i := by omega
    have he : 0 < i.factorization p := by
      by_contra! e
      simp [Nat.eq_zero_of_le_zero e] at eq
      omega
    exact h ((isPrimePow_nat_iff _).mpr ⟨p,_,hp,he,eq⟩)
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro n hn
    obtain ⟨hn,hle⟩ := mem_Icc.mp hn
    by_cases e : n = i
    · simpa [e] using last
    · exact ongrid (m := n) hn (by omega)
  · apply Finset.lcm_dvd
    intro n hn
    exact ongrid (m := n) (mem_Icc.mp hn).1 (by have := (mem_Icc.mp hn).2; omega)

lemma complement {i : ℕ} (hi : IsPrimePow i) :
    i.Coprime (lcmUpto i / i) := by
  obtain ⟨p,k,hp,hk,rfl⟩ := (isPrimePow_nat_iff _).mp hi
  apply (hp.coprime_iff_not_dvd.mpr ?_).pow_left
  have hi := pow_pos hp.pos k
  have dvd := ongrid hi le_rfl
  have nz : lcmUpto (p^k) / p^k ≠ 0 := Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (lcmUpto_pos _) dvd) hi)
  intro h
  have hf := hp.factorization_pos_of_dvd nz h
  rw [Nat.factorization_div dvd] at hf
  simpa [Finsupp.coe_tsub, factorization_lcmUpto _ hp, Nat.log_pow hp.one_lt, hp.factorization_pow] using hf

lemma complement_dvd {i : ℕ} (hi : 0 < i) : lcmUpto i / i ∣ lcmUpto (i-1) := by
  apply (Nat.mul_dvd_mul_iff_left hi).mp
  rw [Nat.mul_div_cancel' (ongrid hi le_rfl)]
  apply Finset.lcm_dvd
  intro n hn
  obtain ⟨hn,hle⟩ := mem_Icc.mp hn
  by_cases e : n = i
  · subst n
    exact dvd_mul_right _ _
  · exact dvd_trans (ongrid hn (show n ≤ i-1 by omega)) (dvd_mul_left _ _)

lemma cancel {i : ℕ} (hi : 0 < i) {M : Finset ℕ}
    (adm : ∀ m ∈ M, 0 < m ∧ m ≤ i ∧ i.Coprime m)
    (hc : i.Coprime (lcmUpto i / i)) (z : ℤ)
    (res : ∑ m ∈ M, (m : ZMod i)⁻¹ = (z : ZMod i) * ((lcmUpto i / i : ℕ) : ZMod i)⁻¹) :
    ∃ a : ℤ, (a:ℚ)/lcmUpto (i-1) = (z:ℚ)/lcmUpto i - ∑ m ∈ M, (1:ℚ)/((i:ℚ)*m) := by
  let D := lcmUpto i / i
  have he : i*D = lcmUpto i := Nat.mul_div_cancel' (ongrid hi le_rfl)
  have dvd (m : ℕ) (hm : m ∈ M) : m ∣ D :=
    (adm m hm).2.2.symm.dvd_of_dvd_mul_left (he.symm ▸ ongrid (adm m hm).1 (adm m hm).2.1)
  have hmz (m : ℕ) (hm : m ∈ M) : ((D/m : ℕ) : ZMod i) = (D : ZMod i) * (m : ZMod i)⁻¹ := by
    have hh : ((D/m : ℕ):ZMod i)*(m:ZMod i) = D := by rw [← Nat.cast_mul, Nat.div_mul_cancel (dvd m hm)]
    rw [← hh, mul_assoc, ZMod.mul_inv_of_unit _ ((ZMod.isUnit_iff_coprime _ _).mpr (adm m hm).2.2.symm), mul_one]
  have modzero : ((z - ∑ m ∈ M, ((D/m:ℕ):ℤ) : ℤ) : ZMod i) = 0 := by
    simp only [Int.cast_sub,Int.cast_sum,Int.cast_natCast]
    rw [sum_congr rfl hmz, ← mul_sum, res]
    change (z:ZMod i) - (D:ZMod i)*((z:ZMod i)*(D:ZMod i)⁻¹) = 0
    rw [mul_left_comm, ZMod.mul_inv_of_unit _ ((ZMod.isUnit_iff_coprime _ _).mpr hc.symm), mul_one, sub_self]
  obtain ⟨b,hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp modzero
  obtain ⟨c,hc'⟩ := complement_dvd hi
  refine ⟨b*c,?_⟩
  have rat (m : ℕ) (hm : m ∈ M) : (1:ℚ)/((i:ℚ)*m) = ((D/m:ℕ):ℚ)/lcmUpto i := by
    have mm : (m:ℚ) ≠ 0 := by exact_mod_cast (adm m hm).1.ne'
    apply (div_eq_div_iff (mul_ne_zero (by exact_mod_cast hi.ne') mm) (by exact_mod_cast lcmUpto_ne_zero i)).mpr
    have ff : ((D/m:ℕ):ℚ)*(m:ℚ) = D := by exact_mod_cast Nat.div_mul_cancel (dvd m hm)
    have gg : (i:ℚ)*D = lcmUpto i := by exact_mod_cast he
    linear_combination gg*(-1) + ((i:ℚ)*ff)*(-1)
  rw [sum_congr rfl rat, ← sum_div, ← sub_div]
  have rb : (z:ℚ) - ∑ m ∈ M, ((D/m:ℕ):ℚ) = (i:ℚ)*b := by simpa only [Int.cast_sub,Int.cast_sum,Int.cast_natCast,Int.cast_mul] using congrArg (Int.cast : ℤ → ℚ) hb
  rw [rb]
  push_cast
  have eq : (i:ℚ)*D = lcmUpto i := by exact_mod_cast he
  have eq' : (lcmUpto (i-1):ℚ) = (D:ℚ)*c := by exact_mod_cast hc'
  apply (div_eq_div_iff (by exact_mod_cast lcmUpto_ne_zero (i-1)) (by exact_mod_cast lcmUpto_ne_zero i)).mpr
  rw [← eq,eq']; ring

lemma budget {ε : ℝ} (he : 0 < ε) (d : ℚ) (hd : 0 < d) :
    let cost (i : ℕ) : ℚ := (⌊(i:ℝ)^(ε/2)⌋₊ : ℚ)/((i:ℚ)*⌈(i:ℝ)^ε⌉₊)
    ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ B, ∑ i ∈ Ioc L B, cost i < d := by
  dsimp only
  have sm := Real.summable_nat_rpow.mpr (show -1-ε/2 < -1 by linarith)
  obtain ⟨s,hs⟩ := summable_iff_vanishing_norm.mp sm (d:ℝ) (by exact_mod_cast hd)
  refine ⟨s.sup id,?_⟩
  intro L hL B
  have dj : Disjoint (Ioc L B) s := by
    apply disjoint_left.mpr
    intro i hi hs
    have : i ≤ s.sup id := le_sup (f := id) hs
    have := (mem_Ioc.mp hi).1
    omega
  have tail := hs _ dj
  have bound (i : ℕ) (hi : i ∈ Ioc L B) :
      (⌊(i:ℝ)^(ε/2)⌋₊:ℝ)/((i:ℝ)*⌈(i:ℝ)^ε⌉₊) ≤ (i:ℝ)^(-1-ε/2) := by
    have hp : 0 < (i:ℝ) := by exact_mod_cast (Nat.zero_le L).trans_lt (mem_Ioc.mp hi).1
    have v := Real.rpow_pos_of_pos hp ε
    have fl := Nat.floor_le (Real.rpow_nonneg hp.le (ε/2))
    have cl := Nat.le_ceil ((i:ℝ)^ε)
    calc
      _ ≤ (i:ℝ)^(ε/2)/((i:ℝ)*(i:ℝ)^ε) := by
        apply div_le_div₀ (Real.rpow_nonneg hp.le _) fl (mul_pos hp v) (mul_le_mul_of_nonneg_left cl hp.le)
      _ = _ := by
        rw [show (i:ℝ)*(i:ℝ)^ε = (i:ℝ)^(1+ε) by rw [Real.rpow_add hp, Real.rpow_one], ← Real.rpow_sub hp]
        congr 1; ring
  have est := sum_le_sum bound
  have pos : 0 ≤ ∑ i ∈ Ioc L B, (i:ℝ)^(-1-ε/2) := sum_nonneg fun i _ => Real.rpow_nonneg (by positivity) _
  rw [Real.norm_eq_abs,abs_of_nonneg pos] at tail
  apply (Rat.cast_lt (K := ℝ)).mp
  push_cast
  exact est.trans_lt tail

def Goal : Prop := ∀ ε : ℝ, 0 < ε → ε < 1/2 → ∀ d : ℚ, 0 < d →
  ∃ L₀ : ℕ, ∀ L ≥ L₀,
    let J (i : ℕ) := (Icc 1 i).lcm id
    let K := J L
    let R (i : ℕ) := (Icc 1 (i*i)).filter fun n => IsPrimePow i ∧ i∣n ∧ Nat.Coprime i (n/i) ∧
        (i:ℝ)^ε ≤ (n/i:ℕ) ∧ ((n/i:ℕ):ℝ) ≤ 2*(i:ℝ)^ε ∧ ¬ K ∣ n
    ∃ cost : ℕ → ℚ, (∀ B, ∑ i ∈ Ioc L B, cost i < d) ∧
      ∀ i : ℕ, L < i → ∀ z : ℤ, ∃ V ⊆ R i,
        (∑ n ∈ V, (1:ℚ)/n) ≤ cost i ∧ ∃ a : ℤ,
        (a:ℚ)/J (i-1) = (z:ℚ)/J i - ∑ n ∈ V, (1:ℚ)/n


theorem full297 : Goal := by
  intro ε he hsmall d hd
  let cost (i : ℕ) : ℚ := (⌊(i:ℝ)^(ε/2)⌋₊:ℚ)/((i:ℚ)*⌈(i:ℝ)^ε⌉₊)
  obtain ⟨L₁,small⟩ := budget he d hd
  have grows (a : ℝ) (ha : 0 < a) (b : ℝ) : ∀ᶠ i : ℕ in atTop, b ≤ (i:ℝ)^a :=
    ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  obtain ⟨L₂,large⟩ := eventually_atTop.mp ((sparse297 ε he).and
    ((grows ε he 100).and (grows (1-ε) (by linarith) 2)))
  refine ⟨max 6 (max L₁ L₂),?_⟩
  intro L hL
  have h6 : 6 ≤ L := by omega
  refine ⟨cost,small L (by omega),?_⟩
  intro i hLi z
  have hi : 0 < i := by omega
  have hpos : 0 < (i:ℝ) := by exact_mod_cast hi
  obtain ⟨mod,hr,hr'⟩ := large i (by omega)
  have upper : 2*(i:ℝ)^ε ≤ i := calc
    _ ≤ (i:ℝ)^(1-ε)*(i:ℝ)^ε := mul_le_mul_of_nonneg_right hr' (Real.rpow_nonneg hpos.le _)
    _ = _ := by rw [← Real.rpow_add hpos,sub_add_cancel,Real.rpow_one]
  by_cases pp : IsPrimePow i
  · obtain ⟨M,card,data,res⟩ := mod pp
      ((z:ZMod i)*((Nat.lcmUpto i / i : ℕ):ZMod i)⁻¹)
    have adm (m : ℕ) (hm : m ∈ M) : 0 < m ∧ m ≤ i ∧ i.Coprime m := by
      obtain ⟨cop,lo,up,_⟩ := data m hm
      exact ⟨by exact_mod_cast (Real.rpow_pos_of_pos hpos ε).trans_le lo,by exact_mod_cast up.trans upper,cop⟩
    have inj : Function.Injective (fun m : ℕ => i*m) := fun _ _ h => Nat.eq_of_mul_eq_mul_left hi h
    have imageSum : ∑ n ∈ M.image (i*·), (1:ℚ)/n = ∑ m ∈ M, (1:ℚ)/((i:ℚ)*m) := by
      rw [sum_image (fun _ _ _ _ eq => inj eq)]
      simp
    refine ⟨M.image (i*·),?_,?_,?_⟩
    · intro n hn
      obtain ⟨m,hm,rfl⟩ := mem_image.mp hn
      obtain ⟨mp,mi,cp⟩ := adm m hm
      obtain ⟨_,lo,up,avoid⟩ := data m hm
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hi mp,Nat.mul_le_mul_left _ mi⟩,pp,dvd_mul_right _ _,?_⟩
      simp only [Nat.mul_div_cancel_left _ hi]
      exact ⟨cp,lo,up,fun h => avoid (dvd_trans (ongrid (by decide : 0 < 6) h6) h)⟩
    · rw [imageSum]
      have count : M.card ≤ ⌊(i:ℝ)^(ε/2)⌋₊ := Nat.le_floor card
      have ceilpos : 0 < ⌈(i:ℝ)^ε⌉₊ := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hpos _)
      have cpos : 0 < (i:ℚ)*(⌈(i:ℝ)^ε⌉₊:ℕ) := by positivity
      calc
        _ ≤ ∑ _m ∈ M, (1:ℚ)/((i:ℚ)*⌈(i:ℝ)^ε⌉₊) := by
          apply sum_le_sum
          intro m hm
          have lower := Nat.ceil_le.mpr (data m hm).2.1
          exact one_div_le_one_div_of_le cpos (mul_le_mul_of_nonneg_left (by exact_mod_cast lower) (by positivity))
        _ = (M.card:ℚ)/((i:ℚ)*⌈(i:ℝ)^ε⌉₊) := by simp [div_eq_mul_inv]
        _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast count) cpos.le
    · rw [imageSum]
      exact cancel hi adm (complement pp) z res
  · refine ⟨∅,empty_subset _,by simp [cost]; positivity,z,?_⟩
    simp only [sum_empty,sub_zero]
    change (z:ℚ)/(Nat.lcmUpto (i-1)) = (z:ℚ)/Nat.lcmUpto i
    rw [unchanged (by omega) pp]

end Egyptian

theorem OMA.solution : OMA.R_Erdos297_erdos_297_variants_general_R1_H3_R1_H2_R1_H1_R1.H2 := Egyptian.full297
