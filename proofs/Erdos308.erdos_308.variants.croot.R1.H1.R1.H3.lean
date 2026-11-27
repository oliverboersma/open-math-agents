import OMAReductions.R_Erdos308_erdos_308_variants_croot_R1_H1_R1
import Mathlib

/-!
# Large prime powers in Croot's construction

The Fourier criterion, the count of exceptional primes and the prime interval
estimate are adapted from Will Howe (@H0W4RD-dev), H0W4RD-dev/croot-unit-fractions
at c58a7d45114c3af27e6abb19dcfca9d82b49b4a1, used under Apache-2.0, via
@marcusbuffett's open-math-agents proof of the corresponding Erdős 297 step.
The analytic argument originates in Croot's Lemma 1 (Acta Arithmetica 99, 2001).

For any exponent a above three, take b strictly between three and a. For
large prime powers i, inverse subset sums of primes of size (log i)^b cover
every residue modulo i. A common multiplier puts the resulting denominators
between N/6 and N. Their total cost over all layers is bounded by counting
prime powers up to the cutoff using Chebyshev's estimate and a separate bound
on proper powers. The lcm-grid identities are from @marcusbuffett's Erdős 297
and 308 proofs.
-/

section
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

theorem norm_prod_general (n : ℕ) [NeZero n] (v Y L D K : ℝ)
    (hv : 0<v) (hY : 0<Y) (hL : 0<L) (hD : 0<D) (hprodYL : Y=L*D)
    (he : Real.exp 1≤Y/4) (hL2 : L+2≤n) (hn_exp : (n:ℝ)=Real.exp v)
    (hbcount : (2*(L+1)+1)*(2*v) ≤ K/2)
    (hgcount : 2*v ≤ (K/2)*(4/(9*D^2)))
    (R : Finset ℕ) (hR : ∀ r ∈ R, r.Prime ∧ ¬r∣n ∧ Y/4≤r ∧ (r:ℝ)≤3*Y)
    (hk : K≤R.card) (h : ZMod n) (hh : h≠0) :
    ‖∏ r ∈ R, (1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹))‖ ≤ 2 ^ R.card / n := by
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
  set B := R.filter (fun r : ℕ => |(r : ℝ) * t r| ≤ L * n) with hBdef
  set G := R.filter (fun r : ℕ => ¬ |(r : ℝ) * t r| ≤ L * n) with hGdef
  have hBG : B.card + G.card = R.card := Finset.card_filter_add_card_filter_not _
  -- few bad primes
  have hBcard : (B.card : ℝ) ≤ (2 * (L + 1) + 1) * ⌊2 * v⌋₊ := by
    apply card_bad_le n H hH0 hHn R (Y / 4) _ _ t hdiv L (by positivity)
    · -- (L + 2) * n < y ^ (m + 1)
      have h1 : (L + 2) * n ≤ (n : ℝ) * n := mul_le_mul_of_nonneg_right hL2 hnpos.le
      have h2 : (n : ℝ) * n = Real.exp (2 * v) := by
        rw [hn_exp, ← Real.exp_add]; ring_nf
      have h3 : Real.exp (2 * v) < Real.exp ((⌊2 * v⌋₊ + 1 : ℕ) : ℝ) := by
        rw [Real.exp_lt_exp]
        push_cast
        exact Nat.lt_floor_add_one _
      have h4 : Real.exp ((⌊2 * v⌋₊ + 1 : ℕ) : ℝ) = Real.exp 1 ^ (⌊2 * v⌋₊ + 1) :=
        (Real.exp_one_pow _).symm
      have h5 : Real.exp 1 ^ (⌊2 * v⌋₊ + 1) ≤ (Y / 4) ^ (⌊2 * v⌋₊ + 1) :=
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
    have h1 : (⌊2 * v⌋₊ : ℝ) ≤ 2 * v := Nat.floor_le (by positivity)
    have h2 : (2 * (L + 1) + 1) * (⌊2 * v⌋₊ : ℝ) ≤ (2 * (L + 1) + 1) * (2 * v) := by
      apply mul_le_mul_of_nonneg_left h1
      positivity
    have h3 : (2 * (L + 1) + 1) * (2 * v) ≤ K / 2 := by
      exact hbcount
    linarith
  have hGcard : K / 2 ≤ (G.card : ℝ) := by
    have : (B.card : ℝ) + G.card = R.card := by exact_mod_cast hBG
    linarith
  -- per-factor bounds
  have hfac : ∀ r ∈ R, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2
      ≤ 4 - 16 * ((t r : ℝ) / n) ^ 2 :=
    fun r _ => norm_one_add_stdAddChar_sq_le _
  set a : ℝ := 4 / (9 * D ^ 2) with hadef
  have hgood : ∀ r ∈ G, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2
      ≤ 4 * Real.exp (-a) := by
    intro r hr
    rw [hGdef, Finset.mem_filter] at hr
    obtain ⟨hrR, hrgood⟩ := hr
    push Not at hrgood
    have hr3 : (r : ℝ) ≤ 3 * Y := (hR r hrR).2.2.2
    have hrpos : (0 : ℝ) < r := by exact_mod_cast (hR r hrR).1.pos
    have key : (n : ℝ) < 3 * D * |(t r : ℝ)| := by
      rw [abs_mul, abs_of_pos hrpos] at hrgood
      have : L * n < L * (3 * D * |(t r : ℝ)|) := by
        calc L * (n : ℝ) = L * n := rfl
        _ < r * |(t r : ℝ)| := hrgood
        _ ≤ 3 * Y * |(t r : ℝ)| := mul_le_mul_of_nonneg_right hr3 (abs_nonneg _)
        _ = L * (3 * D * |(t r : ℝ)|) := by rw [hprodYL]; ring
      exact lt_of_mul_lt_mul_left this (by positivity)
    have key2 : 1 / (9 * D ^ 2) ≤ ((t r : ℝ) / n) ^ 2 := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      have : (n : ℝ) ^ 2 < (3 * D * |(t r : ℝ)|) ^ 2 :=
        pow_lt_pow_left₀ key hnpos.le (by norm_num)
      calc 1 * (n : ℝ) ^ 2 ≤ (3 * D * |(t r : ℝ)|) ^ 2 := by linarith
      _ = (t r : ℝ) ^ 2 * (9 * D ^ 2) := by rw [mul_pow, mul_pow, sq_abs]; ring
    have hexp : 1 - a ≤ Real.exp (-a) := by linarith [Real.add_one_le_exp (-a)]
    calc ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2
        ≤ 4 - 16 * ((t r : ℝ) / n) ^ 2 := hfac r hrR
    _ ≤ 4 - 16 * (1 / (9 * D ^ 2)) := by linarith
    _ = 4 * (1 - a) := by rw [hadef]; ring
    _ ≤ 4 * Real.exp (-a) := by linarith
  have hbad : ∀ r ∈ R, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2 ≤ 4 := by
    intro r hr
    have := hfac r hr
    nlinarith [sq_nonneg ((t r : ℝ) / n)]
  -- the product
  have hprod : ‖∏ r ∈ R, (1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹))‖ ^ 2
      ≤ 4 ^ R.card * Real.exp (-(2 * v)) := by
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
    have hexpG : Real.exp (-a) ^ G.card ≤ Real.exp (-(2 * v)) := by
      rw [← Real.exp_nat_mul, Real.exp_le_exp]
      have ha : 0 ≤ a := by positivity
      have : 2 * v ≤ G.card * a := by
        calc 2 * v ≤ (K / 2) * a := by exact hgcount
        _ ≤ G.card * a := mul_le_mul_of_nonneg_right hGcard ha
      linarith
    calc (∏ r ∈ B, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2) *
          ∏ r ∈ G, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2
        ≤ 4 ^ B.card * (4 * Real.exp (-a)) ^ G.card :=
          mul_le_mul hB' hG' (Finset.prod_nonneg fun _ _ => by positivity) (by positivity)
    _ = 4 ^ R.card * Real.exp (-a) ^ G.card := by
          rw [mul_pow, ← mul_assoc, ← pow_add, hBG]
    _ ≤ 4 ^ R.card * Real.exp (-(2 * v)) :=
          mul_le_mul_of_nonneg_left hexpG (by positivity)
  have hfinal : (2 ^ R.card / (n : ℝ)) ^ 2 = 4 ^ R.card * Real.exp (-(2 * v)) := by
    have e1 : Real.exp (v) ^ 2 = Real.exp (2 * v) := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [hn_exp, div_pow, e1, Real.exp_neg, div_eq_mul_inv, ← pow_mul, mul_comm R.card 2,
      pow_mul]
    norm_num
  rw [← hfinal] at hprod
  exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hprod


end Lemma1Aux
end Croot
end

section
open Finset Real Filter
open scoped Topology
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
end Croot
namespace Big308

lemma pow_absorb (a b C : ℝ) (hab : a<b) :
    ∀ᶠ v : ℝ in atTop, C*v^a ≤ v^b := by
  filter_upwards [(tendsto_rpow_atTop (sub_pos.mpr hab)).eventually_ge_atTop C,eventually_gt_atTop (0:ℝ)] with v hv hpos
  calc
    _ ≤ v^(b-a)*v^a := mul_le_mul_of_nonneg_right hv (rpow_nonneg hpos.le _)
    _ = _ := by rw [←rpow_add hpos];congr 1;ring

lemma primes (η : ℝ) (hη : 0<η) : ∀ᶠ i : ℕ in atTop, ∀ p : ℕ, p.Prime →
    (∀ r : ℕ, r.Prime → r∣i → r=p) →
    let Y := (log i)^(3+12*η)
    ∃ S : Finset ℕ, (S.card:ℝ) ≤ 3*Y ∧
      (∀ r ∈ S, r.Prime ∧ r≠p ∧ Y≤r ∧ (r:ℝ)≤3*Y) ∧
      ∀ z : ZMod i, ∃ T ⊆ S, ∑ r ∈ T, (r:ZMod i)⁻¹=z := by
  let b := 3+12*η
  let k := 3+11*η
  let l := 2+9*η
  let d := 1+3*η
  have hbp : 0<b := by dsimp [b];linarith
  have hkp : 0<k := by dsimp [k];linarith
  have hlp : 0<l := by dsimp [l];linarith
  have tv : Tendsto (fun i : ℕ => log (i:ℝ)) atTop atTop := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ty := (tendsto_rpow_atTop hbp).comp tv
  have hab := tv.eventually (pow_absorb (l+1) k 20 (by dsimp [l,k];linarith))
  have hag := tv.eventually (pow_absorb (2*d+1) k 9 (by dsimp [d,k];linarith))
  have logsmall := tv.eventually ((isLittleO_log_rpow_atTop hη).bound
    (show 0<1/(10*b) by positivity))
  have lsmall := tendsto_natCast_atTop_atTop.eventually
    ((isLittleO_log_rpow_rpow_atTop l one_pos).bound (show (0:ℝ)<1/2 by norm_num))
  filter_upwards [eventually_ge_atTop 4,tv.eventually_ge_atTop 2,ty.eventually_ge_atTop 16,
    ty.eventually Croot.eventually_card_primes_Ioc_ge,hab,hag,logsmall,lsmall] with i hi hv hy hn ha hb hlog hLsmall
  intro p hp hall
  let v := log (i:ℝ)
  let Y := v^b
  let K := v^k
  let L := v^l
  let D := v^d
  change 2≤v at hv
  change (16:ℝ)≤Y at hy
  let X := (Ioc ⌊Y⌋₊ ⌊(27/10:ℝ)*Y⌋₊).filter Nat.Prime
  change Y/(5*log Y) ≤ (X.card:ℝ) at hn
  have vp : 0<v := by linarith
  have yp : 0<Y := by positivity
  have lp : 0<L := by positivity
  have dp : 0<D := by positivity
  have kp : 1≤K := one_le_rpow (by linarith) hkp.le
  have l1 : 1≤L := one_le_rpow (by linarith) hlp.le
  have ic : (4:ℝ) ≤ i := by exact_mod_cast hi
  have vpos := log_pos (show 1<v by linarith)
  have lo : 10*b*log v ≤ v^η := by
    change ‖log v‖ ≤ 1/(10*b)*‖v^η‖ at hlog
    rw [Real.norm_eq_abs,abs_of_pos vpos,Real.norm_eq_abs,abs_of_pos (rpow_pos_of_pos vp _)] at hlog
    field_simp at hlog
    linarith
  have bh : 2*K ≤ Y/(5*log Y) := by
    have ly : log Y=b*log v := Real.log_rpow vp _
    rw [ly, le_div_iff₀ (by positivity)]
    have yk : Y=v^η*K := by dsimp [Y,K];rw [←rpow_add vp];congr 1; dsimp [k,b];ring
    rw [yk]
    nlinarith only [mul_le_mul_of_nonneg_right lo (show 0≤K by linarith)]
  let S := X.erase p
  have sc : (K:ℝ) ≤ S.card := by
    have card : X.card ≤ S.card+1 := by
      by_cases h : p∈X
      · exact (card_erase_add_one h).ge
      · simp [S,h]
    have hh : (X.card:ℝ) ≤ S.card+1 := by exact_mod_cast card
    linarith
  have props : ∀ r∈S, r.Prime ∧ r≠p ∧ Y≤r ∧ (r:ℝ)≤3*Y := by
    intro r hr
    obtain ⟨ne,mem⟩ := mem_erase.mp hr
    obtain ⟨mem,pr⟩ := mem_filter.mp mem
    obtain ⟨hlo,hhi⟩ := mem_Ioc.mp mem
    exact ⟨pr,ne,(Nat.lt_of_floor_lt hlo).le,((Nat.le_floor_iff (by positivity)).mp hhi).trans (by linarith)⟩
  refine ⟨S,?_,props,?_⟩
  · have hsub : S ⊆ Icc 1 ⌊3*Y⌋₊ := fun r hr => mem_Icc.mpr ⟨(props r hr).1.pos,
      Nat.le_floor (props r hr).2.2.2⟩
    have hcard := card_le_card hsub
    rw [Nat.card_Icc,Nat.add_sub_cancel] at hcard
    exact (Nat.cast_le.mpr hcard).trans (Nat.floor_le (by positivity))
  · intro z
    letI : NeZero i := ⟨by omega⟩
    apply Croot.Lemma1Aux.exists_subset_sum_of_norm_prod_le S _ _ z
    intro h hh
    have hbcount : (2*(L+1)+1)*(2*v) ≤ K/2 := by
      change 20*v^(l+1) ≤ K at ha
      rw [rpow_add vp,rpow_one] at ha
      change 20*(L*v) ≤ K at ha
      nlinarith only [ha,mul_le_mul_of_nonneg_right l1 vp.le]
    have hgcount : 2*v ≤ (K/2)*(4/(9*D^2)) := by
      change 9*v^(2*d+1)≤K at hb
      have powD : v^(2*d+1)=D^2*v := by
        rw [rpow_add vp,rpow_one,mul_comm (2:ℝ) d,rpow_mul vp.le,rpow_two]
      rw [powD] at hb
      rw [mul_div_assoc', le_div_iff₀ (by positivity)]
      nlinarith only [hb]
    have lbound : L+2 ≤ (i:ℝ) := by
      change ‖L‖ ≤ (1/2)*‖(i:ℝ)^(1:ℝ)‖ at hLsmall
      rw [rpow_one,Real.norm_eq_abs,abs_of_pos lp,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)] at hLsmall
      linarith
    refine Croot.Lemma1Aux.norm_prod_general i v Y L D K vp yp lp dp ?_ (by linarith [Real.exp_one_lt_three]) lbound
      (Real.exp_log (by positivity : (0:ℝ) < i)).symm hbcount hgcount S ?_ sc h hh
    · dsimp [Y,L,D];rw [←rpow_add vp];congr 1;dsimp [l,d,b];ring
    · intro r hr
      obtain ⟨pr,ne,hlo,hhi⟩ := props r hr
      exact ⟨pr,fun hh => ne (hall r pr hh),by linarith,hhi⟩
end Big308
end

section
open Finset Nat
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

end Egyptian

namespace Mid308
abbrev J := Nat.lcmUpto
def layer (N i : ℕ) := (Icc 1 N).filter fun n => n∣J i ∧ ¬n∣J (i-1)
def desc (N i : ℕ) (c : ℚ) : Prop := ∀ z : ℤ, ∃ V ⊆ layer N i,
  (∑ n ∈ V,(1:ℚ)/n) ≤ c ∧ ∃ b : ℤ, (b:ℚ)/J (i-1) = (z:ℚ)/J i - ∑ n ∈ V,(1:ℚ)/n

lemma pp_not_prev {p k i : ℕ} (hp : p.Prime) (hk : 0<k) (eqi : p^k=i) :
    ¬i∣J (i-1) := by
  have hi := (isPrimePow_nat_iff _).mpr ⟨p,k,hp,hk,eqi⟩ |>.one_lt
  intro h
  have h' := (hp.pow_dvd_iff_le_factorization (lcmUpto_ne_zero (i-1))).mp (eqi ▸ h : p^k∣J (i-1))
  rw [factorization_lcmUpto _ hp] at h'
  have lt := Nat.log_lt_of_lt_pow (b:=p) (x:=k) (y:=i-1) (by omega) (by omega)
  omega

lemma empty_step {N i : ℕ} (hi : 1 < i) (h : ¬IsPrimePow i) :
    desc N i 0 := by
  intro z
  exact ⟨∅,empty_subset _,by simp,z,by simp [Egyptian.unchanged hi h]⟩


end Mid308
end

section
open Finset Real
open scoped Classical
namespace Egyptian
open Nat
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

end Egyptian
namespace Big308
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


open Mid308
lemma scaled {p k i N : ℕ} (hp : p.Prime) (hk : 0<k) (eqi : p^k=i)
    (hiN : N ≤ i*i) {Y : ℝ} (hY : 0<Y) (hroom : 600*(i:ℝ)*Y ≤ N) (S : Finset ℕ)
    (hc : (S.card:ℝ)≤3*Y) (mem : ∀ r∈S, r.Prime ∧ r≠p ∧ Y≤r ∧ (r:ℝ)≤3*Y)
    (full : ∀ z : ZMod i, ∃ T ⊆ S, ∑ r ∈ T,(r:ZMod i)⁻¹=z)
    {C : ℕ} (hC : 18*Y ≤ C) : desc N i ((C:ℚ)/N) := by
  classical
  obtain rfl := eqi
  let i := p^k
  have hi : 0 < i := pow_pos hp.pos _
  have ir : (0:ℝ)<(i:ℝ) := by exact_mod_cast hi
  have ip : IsPrimePow i := (isPrimePow_nat_iff _).mpr ⟨p,k,hp,hk,rfl⟩
  change 600*(i:ℝ)*Y ≤ N at hroom
  have nreal : (0:ℝ)<N := lt_of_lt_of_le (by positivity) hroom
  let W := (N:ℝ)/(6*(i:ℝ)*Y)
  have hW : 100 ≤ W := (le_div_iff₀ (by positivity)).mpr (by linarith)
  obtain ⟨u,hul,huu,cpu,-,-⟩ := multiplier297 hp W hW
  have ureal : (0:ℝ)<u := by linarith
  have upos : 0 < u := by exact_mod_cast ureal
  let g (r : ℕ) := u*r
  have inj : Function.Injective g := fun _ _ e => Nat.eq_of_mul_eq_mul_left upos e
  have lower : (N:ℝ) ≤ 6*(i:ℝ)*(u:ℝ)*Y := by
    have := (div_le_iff₀ (by positivity : 0<6*(i:ℝ)*Y)).mp hul
    linarith
  have upper : (i:ℝ)*(u:ℝ)*(3*Y) ≤ N := by
    have hW' : W*(6*(i:ℝ)*Y)=N := div_mul_cancel₀ _ (by positivity)
    have hm := mul_le_mul_of_nonneg_right huu (show 0≤6*(i:ℝ)*Y by positivity)
    nlinarith only [hm,hW',nreal]
  have num (r : ℕ) (hr : r∈S) : 0<g r ∧ i.Coprime (g r) ∧ N≤6*(i*g r) ∧ i*g r≤N := by
    obtain ⟨pr,ne,lo,hi'⟩ := mem r hr
    have cr := (Nat.coprime_primes hp pr).mpr ne.symm
    have hm : 0≤(i:ℝ)*u := by positivity
    refine ⟨Nat.mul_pos upos pr.pos,(cpu.mul_right cr).pow_left _,?_,?_⟩
    · change N ≤ 6*(i*(u*r))
      exact_mod_cast (show (N:ℝ) ≤ 6*((i:ℝ)*((u:ℝ)*r)) by
        nlinarith only [lower,mul_le_mul_of_nonneg_left lo hm])
    · change i*(u*r) ≤ N
      exact_mod_cast (show (i:ℝ)*((u:ℝ)*r) ≤ N by nlinarith only [upper,mul_le_mul_of_nonneg_left hi' hm])
  intro z
  let Z : ZMod i := (z:ZMod i)*((Nat.lcmUpto i/i:ℕ):ZMod i)⁻¹
  obtain ⟨T,hTS,hs⟩ := full ((u:ZMod i)*Z)
  let M := T.image g
  have ms : ∀ m∈M, 0 < m ∧ m ≤ i ∧ i.Coprime m ∧ N≤6*(i*m) ∧ i*m≤N := by
    intro m hm
    obtain ⟨r,hr,rfl⟩ := mem_image.mp hm
    obtain ⟨pos,cop,low,high⟩ := num r (hTS hr)
    exact ⟨pos,Nat.le_of_mul_le_mul_left (high.trans hiN) hi,cop,low,high⟩
  have val : ∑ m∈M,(m:ZMod i)⁻¹ = Z := by
    have uc := ZMod.coe_mul_inv_eq_one (n:=i) u (cpu.pow_left k).symm
    dsimp only [M];rw [sum_image (fun _ _ _ _ h => inj h)]
    have per (r : ℕ) (hr : r∈T) : (g r:ZMod i)⁻¹=(u:ZMod i)⁻¹*(r:ZMod i)⁻¹ := by
      obtain ⟨pr,ne,-,-⟩ := mem r (hTS hr)
      have rc := ZMod.coe_mul_inv_eq_one (n:=i) r (((Nat.coprime_primes pr hp).mpr ne).pow_right k)
      apply ZMod.inv_eq_of_mul_eq_one
      dsimp [g];push_cast
      calc
        _ = ((u:ZMod i)*(u:ZMod i)⁻¹)*((r:ZMod i)*(r:ZMod i)⁻¹) := by ring
        _ = _ := by rw [uc,rc,mul_one]
    rw [sum_congr rfl per,←mul_sum,hs,←mul_assoc,mul_comm ((u:ZMod i)⁻¹),uc,one_mul]
  let V := M.image (i*·)
  have admiss (m : ℕ) (h : m∈M) := And.intro (ms m h).1 (And.intro (ms m h).2.1 (ms m h).2.2.1)
  have sub : V ⊆ layer N i := by
    intro n hn
    obtain ⟨m,hm,rfl⟩ := mem_image.mp hn
    obtain ⟨pos,hmi,cop,-,up⟩ := ms m hm
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hi pos,up⟩,?_,?_⟩
    · exact cop.mul_dvd_of_dvd_of_dvd (Egyptian.ongrid hi le_rfl) (Egyptian.ongrid pos hmi)
    · exact fun hd => pp_not_prev hp hk rfl (dvd_trans (dvd_mul_right i m) hd)
  have imageSum : (∑ n∈V,(1:ℚ)/n) = ∑ m∈M,(1:ℚ)/((i:ℚ)*m) := by
    dsimp only [V]; rw [sum_image (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hi h)];simp
  refine ⟨V,sub,?_,?_⟩
  · rw [imageSum]
    have nr : (0:ℚ)<N := by exact_mod_cast nreal
    have count : 6*M.card ≤ C := by
      have hMC : (M.card:ℝ) ≤ S.card := by exact_mod_cast (card_image_le.trans (card_le_card hTS) : M.card ≤ S.card)
      exact_mod_cast (show 6*(M.card:ℝ)≤C by linarith)
    calc
      _ ≤ ∑ _m ∈ M, (6:ℚ)/N := by
        apply sum_le_sum
        intro m hm
        rw [div_le_div_iff₀ (by exact_mod_cast Nat.mul_pos hi (ms m hm).1) nr,one_mul]
        exact_mod_cast (ms m hm).2.2.2.1
      _ = ((6:ℚ)*M.card)/N := by simp [div_eq_mul_inv];ring
      _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast count) nr.le
  · rw [imageSum]
    exact Egyptian.cancel hi admiss (Egyptian.complement ip) z val
end Big308
end

section
open Finset Real Filter
open scoped Classical Topology
namespace Big308
noncomputable abbrev pp (N Q : ℕ) := (Ioc Q N).filter fun q => IsPrimePow q ∧ ¬q.Prime
lemma count_pp (N Q : ℕ) : (pp N Q).card ≤ N.sqrt*(Nat.log 2 N+1) := by
  let U := Icc 1 N.sqrt ×ˢ range (Nat.log 2 N+1)
  have sub : pp N Q ⊆ U.image (fun z : ℕ×ℕ => z.1^z.2) := by
    intro q hq
    obtain ⟨hh,pow,nop⟩ := mem_filter.mp hq
    obtain ⟨p,k,hp,hk,rfl⟩ := pow
    have pr := Nat.prime_iff.mpr hp
    have pk := (mem_Ioc.mp hh).2
    have k2 : 2≤k := by
      by_contra! h
      have : k=1 := by omega
      exact nop (by simpa [this] using pr)
    have p2 : p^2≤N := (Nat.pow_le_pow_right pr.pos k2).trans pk
    have pair : (p,k)∈U := mem_product.mpr ⟨mem_Icc.mpr ⟨pr.pos,Nat.le_sqrt.mpr (by simpa [sq] using p2)⟩,
      mem_range.mpr (Nat.lt_succ_of_le (Nat.le_log_of_pow_le (by decide)
        ((Nat.pow_le_pow_left pr.two_le k).trans pk)))⟩
    exact mem_image.mpr ⟨(p,k),pair,rfl⟩
  exact (card_le_card sub).trans (card_image_le.trans (by simp [U]))

lemma count : ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ q : ℕ in atTop,
    ((((Icc 1 q).filter IsPrimePow).card : ℝ)*log q) ≤ κ*q := by
  let c := 1/log 2+1
  have l2 : 0<log 2 := log_pos (by norm_num)
  have cp : 0<c := by dsimp [c];positivity
  refine ⟨log 4+2,by positivity,?_⟩
  have ts : Tendsto (fun q : ℕ => (q:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hsmall := ts.eventually ((isLittleO_log_rpow_rpow_atTop (2:ℝ) (by norm_num : (0:ℝ)<1/2)).bound (inv_pos.mpr cp))
  filter_upwards [hsmall,ts.eventually (Chebyshev.eventually_primeCounting_le one_pos),
    (tendsto_log_atTop.comp ts).eventually_ge_atTop 1] with q hsq hπ hl
  change 1 ≤ log q at hl
  have lp : 0<log q := by linarith
  have qr : 0 ≤ (q:ℝ) := Nat.cast_nonneg _
  have nl : (Nat.log 2 q:ℝ) ≤ log q/log 2 := by
    rw [←Real.natFloor_logb_natCast];exact Nat.floor_le (div_nonneg lp.le l2.le)
  have nup : (Nat.log 2 q:ℝ)+1 ≤ c*log q := by
    dsimp [c];rw [add_mul,one_mul];rw [div_mul_eq_mul_div,one_mul];linarith
  have hc : ((pp q 0).card:ℝ) ≤ sqrt q*(c*log q) := by
    calc _ ≤ (q.sqrt:ℝ)*((Nat.log 2 q:ℝ)+1) := by exact_mod_cast count_pp q 0
         _ ≤ _ := mul_le_mul Real.nat_sqrt_le_real_sqrt nup (by positivity) (sqrt_nonneg _)
  change ‖log (q:ℝ)^(2:ℝ)‖ ≤ c⁻¹*‖(q:ℝ)^(1/2:ℝ)‖ at hsq
  rw [rpow_two,←sqrt_eq_rpow,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),Real.norm_eq_abs,abs_of_nonneg (sqrt_nonneg _)] at hsq
  have hmul : c*log q^2 ≤ sqrt q := by
    calc _ ≤ c*(c⁻¹*sqrt q) := mul_le_mul_of_nonneg_left hsq cp.le
         _ = _ := by rw [←mul_assoc,mul_inv_cancel₀ cp.ne',one_mul]
  have hsub : (Icc 1 q).filter IsPrimePow ⊆ (Nat.primesLE q) ∪ pp q 0 := by
    intro n hn
    obtain ⟨mem,pr⟩ := mem_filter.mp hn
    obtain ⟨lo,hi⟩ := mem_Icc.mp mem
    by_cases h : n.Prime
    · exact mem_union_left _ (Nat.mem_primesLE.mpr ⟨hi,h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_Ioc.mpr ⟨lo,hi⟩,pr,h⟩)
  have hc' := (card_le_card hsub).trans (card_union_le _ _)
  rw [Nat.primesLE_card_eq_primeCounting] at hc'
  have cc : (((Icc 1 q).filter IsPrimePow).card:ℝ) ≤ (q.primeCounting:ℝ)+(pp q 0).card := by exact_mod_cast hc'
  change (Nat.primeCounting ⌊(q:ℝ)⌋₊:ℝ) ≤ (log 4+1)*q/log q at hπ
  rw [Nat.floor_natCast,le_div_iff₀ lp] at hπ
  nlinarith only [mul_le_mul_of_nonneg_right cc lp.le,hπ,mul_le_mul_of_nonneg_right hc lp.le,
    mul_le_mul_of_nonneg_left hmul (sqrt_nonneg (q:ℝ)),Real.sq_sqrt qr]
end Big308
end

section
open Finset Real Filter Mid308
open scoped Classical Topology
namespace Big308
lemma total {N Q C : ℕ} {κ ε a : ℝ} (nr : 0 < (N:ℝ)) (lp : 0 < log N)
    (cap : (Q:ℝ)*(log N)^a ≤ N) (cC : (C:ℝ) ≤ 19*(log N)^a)
    (hq : N.sqrt < Q → ((((Icc 1 Q).filter IsPrimePow).card:ℝ)*log Q) ≤ κ*Q)
    (kk : 0 < κ) (budget : 38*κ ≤ ε*log (log N)^2) (ep : 0<ε) :
    ((∑ i ∈ Ioc N.sqrt Q, if IsPrimePow i then (C:ℚ)/N else 0 : ℚ):ℝ)
      ≤ ε*log (log N)^2/log N := by
  by_cases h : N.sqrt < Q
  · let A := (Ioc N.sqrt Q).filter IsPrimePow
    let U := (Icc 1 Q).filter IsPrimePow
    have sub : A ⊆ U := by
      intro i hi
      obtain ⟨mem,pr⟩ := mem_filter.mp hi
      obtain ⟨lo,up⟩ := mem_Ioc.mp mem
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,up⟩,pr⟩
    have qpos : 0 < (Q:ℝ) := by exact_mod_cast (show 0<Q by omega)
    have qs : (N:ℝ) ≤ (Q:ℝ)*Q := by exact_mod_cast (Nat.sqrt_lt.mp h).le
    have ll := log_le_log nr qs
    rw [log_mul qpos.ne' qpos.ne'] at ll
    have card : (A.card:ℝ) ≤ U.card := by exact_mod_cast card_le_card sub
    have cA : (A.card:ℝ)*log N ≤ 2*κ*Q := by
      have b := hq h
      change (U.card:ℝ)*log Q ≤ κ*Q at b
      nlinarith only [mul_le_mul_of_nonneg_right card lp.le,
        mul_le_mul_of_nonneg_left ll (Nat.cast_nonneg (α:=ℝ) U.card),b]
    have main := mul_le_mul cA cC (Nat.cast_nonneg (α:=ℝ) C) (by positivity)
    rw [←sum_filter,sum_const,nsmul_eq_mul,Rat.cast_mul,Rat.cast_natCast,
      Rat.cast_div,Rat.cast_natCast,Rat.cast_natCast]
    change (A.card:ℝ)*((C:ℝ)/N) ≤ _
    rw [le_div_iff₀ lp]
    apply le_trans _ budget
    rw [←mul_div_assoc,div_mul_eq_mul_div,div_le_iff₀ nr]
    nlinarith only [main,mul_le_mul_of_nonneg_left cap (show 0≤38*κ by positivity)]
  · rw [Ioc_eq_empty_of_le (by omega),sum_empty,Rat.cast_zero]
    positivity

lemma result (a : ℝ) (ha : 3<a) (ε : ℝ) (he : 0<ε) : ∀ᶠ N : ℕ in atTop,
    let Q := ⌊(N:ℝ)/(log N)^a⌋₊
    ∃ cost : ℕ→ℚ, ((∑ i ∈ Ioc N.sqrt Q,cost i:ℚ):ℝ) ≤ ε*(log (log N))^2/log N ∧
      ∀ i ∈ Ioc N.sqrt Q, desc N i (cost i) := by
  let η := (a-3)/24
  let b := 3+12*η
  have hη : 0<η := by dsimp [η];linarith
  have hb : 0<b := by dsimp [b];linarith
  have hba : b<a := by dsimp [b,η];linarith
  obtain ⟨i₀,ipool⟩ := eventually_atTop.1 (primes η hη)
  obtain ⟨κ,kk,hκ⟩ := count
  obtain ⟨q₀,qcount⟩ := eventually_atTop.1 hκ
  have tp : Tendsto (fun N : ℕ => log (N:ℝ)) atTop atTop := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop ((max (max i₀ q₀) 2)^2),
    tp.eventually_ge_atTop 1,tp.eventually (pow_absorb b a 600 hba),
    (tendsto_log_atTop.comp tp).eventually_ge_atTop (max 1 (38*κ/ε))] with N hn hL hroom hB
  let L := log (N:ℝ)
  let Q := ⌊(N:ℝ)/L^a⌋₊
  let C := ⌈18*L^b⌉₊
  change 1 ≤ L at hL
  change 600*L^b ≤ L^a at hroom
  change max 1 (38*κ/ε) ≤ log L at hB
  have sqr := Nat.le_sqrt'.mpr hn
  have nr : 0 < (N:ℝ) := by
    have hn' : 2^2 ≤ N := (Nat.pow_le_pow_left (le_max_right _ _) 2).trans hn
    exact_mod_cast (show 0<N by omega)
  have lp : 0<L := by linarith
  have cceil := Nat.ceil_lt_add_one (show (0:ℝ)≤18*L^b by positivity)
  have lb1 := one_le_rpow hL hb.le
  have qfloor : (Q:ℝ) ≤ N/L^a := Nat.floor_le (by positivity)
  have cap := (le_div_iff₀ (rpow_pos_of_pos lp _)).mp qfloor
  have qN : Q ≤ N := by
    have hp1 := one_le_rpow hL (show 0≤a by linarith)
    exact_mod_cast (show (Q:ℝ) ≤ N by nlinarith only [cap,mul_le_mul_of_nonneg_left hp1 (Nat.cast_nonneg (α:=ℝ) Q)])
  let cost (i : ℕ) : ℚ := if IsPrimePow i then (C:ℚ)/N else 0
  refine ⟨cost,?_,?_⟩
  · apply total nr lp cap (by change (C:ℝ) ≤ 19*L^a;change (C:ℝ) < 18*L^b+1 at cceil;linarith)
      (fun h => qcount Q (by omega)) kk _ he
    have y := (div_le_iff₀ he).mp ((le_max_right _ _).trans hB)
    have z : 1≤log L := (le_max_left _ _).trans hB
    change 38*κ ≤ ε*(log L)^2
    nlinarith only [y,mul_le_mul_of_nonneg_left (show log L ≤ (log L)^2 by nlinarith [sq_nonneg (log L-1)]) he.le]
  · intro i hi
    obtain ⟨low,up⟩ := mem_Ioc.mp hi
    have i₁ : 1 < i := by omega
    by_cases pp : IsPrimePow i
    · obtain ⟨p,k,pr,hk,pk⟩ := (isPrimePow_nat_iff _).mp pp
      have onlyp (r : ℕ) (hr : r.Prime) (hd : r∣i) : r=p := by
        rw [←pk] at hd
        exact ((Nat.dvd_prime pr).mp (hr.dvd_of_dvd_pow hd)).resolve_left hr.ne_one
      obtain ⟨S,card,mem,full⟩ := ipool i (by omega) p pr onlyp
      let Y := (log (i:ℝ))^b
      have il : 0<log (i:ℝ) := log_pos (by exact_mod_cast i₁)
      have ub : Y ≤ L^b := rpow_le_rpow il.le (log_le_log (by positivity) (by exact_mod_cast up.trans qN)) hb.le
      change desc N i (if IsPrimePow i then (C:ℚ)/N else 0)
      rw [if_pos pp]
      refine scaled pr hk pk (Nat.sqrt_lt.mp low).le (rpow_pos_of_pos il _) ?_ S card mem full ?_
      · calc 600*(i:ℝ)*Y ≤ (i:ℝ)*(600*L^b) := by nlinarith only [mul_le_mul_of_nonneg_left ub (Nat.cast_nonneg (α:=ℝ) i)]
             _ ≤ (i:ℝ)*L^a := mul_le_mul_of_nonneg_left hroom (Nat.cast_nonneg _)
             _ ≤ (Q:ℝ)*L^a := mul_le_mul_of_nonneg_right (by exact_mod_cast up) (by positivity)
             _ ≤ _ := cap
      · exact (mul_le_mul_of_nonneg_left ub (by norm_num)).trans (Nat.le_ceil _)
    · simpa [cost,pp] using empty_step (N:=N) i₁ pp
end Big308
end

theorem OMA.solution : OMA.R_Erdos308_erdos_308_variants_croot_R1_H1_R1.H3 := Big308.result
