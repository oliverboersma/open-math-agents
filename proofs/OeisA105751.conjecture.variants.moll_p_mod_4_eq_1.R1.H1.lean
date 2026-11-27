import OMAReductions.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1
import Mathlib

/-!
The Gaussian integer comparison and square-root lifting are based on
Sheikh Azizul Hakim's second reduction in open-math-agents PR #2836.
We use these to count exact prime-power divisors and obtain factorial
divisibility without an upper estimate on the split valuations.
-/

namespace OMA.MollFactorial
open Finset

lemma prod_complex_eq_gaussianInt (n : ℕ) :
    ∏ k ∈ Finset.range (n + 1), ((1 : ℂ) + (k : ℂ) * Complex.I) =
      ((∏ k ∈ Finset.range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)).re : ℂ) +
      ((∏ k ∈ Finset.range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)).im : ℂ) * Complex.I := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ (n := n + 1), Finset.prod_range_succ (n := n + 1), ih]
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
    push_cast
    have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination ((∏ k ∈ Finset.range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)).im : ℂ) *
      ((n : ℂ) + 1) * hI2

lemma a_eq_gaussianInt_im (n : ℕ) :
    OeisA105751.a n = (∏ k ∈ Finset.range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)).im := by
  unfold OeisA105751.a
  dsimp only
  rw [prod_complex_eq_gaussianInt]
  simp only [Complex.add_im, Complex.intCast_im, Complex.mul_im, Complex.intCast_re,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
  exact Int.floor_intCast _

lemma gaussianInt_split_mod (n p M : ℕ) (r : ℤ)
    (hr : ((p ^ M : ℕ) : ℤ) ∣ r ^ 2 + 1) :
    ((p ^ M : ℕ) : ℤ) ∣
      ((∏ k ∈ Finset.range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)).re +
        r * (∏ k ∈ Finset.range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)).im) -
      ∏ k ∈ Finset.range (n + 1), (1 + (k : ℤ) * r) ∧
    ((p ^ M : ℕ) : ℤ) ∣
      ((∏ k ∈ Finset.range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)).re -
        r * (∏ k ∈ Finset.range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)).im) -
      ∏ k ∈ Finset.range (n + 1), (1 - (k : ℤ) * r) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases ih with ⟨ih1, ih2⟩
    set z := ∏ k ∈ Finset.range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)
    set Pp := ∏ k ∈ Finset.range (n + 1), (1 + (k : ℤ) * r)
    set Pm := ∏ k ∈ Finset.range (n + 1), (1 - (k : ℤ) * r)
    rw [Finset.prod_range_succ (n := n + 1), Finset.prod_range_succ (n := n + 1),
      Finset.prod_range_succ (n := n + 1)]
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
    constructor
    · have hid :
          (z.re * 1 + -1 * z.im * ↑(n + 1) + r * (z.re * ↑(n + 1) + z.im * 1)) -
            Pp * (1 + ↑(n + 1) * r) =
          (1 + ↑(n + 1) * r) * (z.re + r * z.im - Pp) - ↑(n + 1) * z.im * (r ^ 2 + 1) := by ring
      rw [hid]
      exact dvd_sub (dvd_mul_of_dvd_right ih1 _) (dvd_mul_of_dvd_right hr _)
    · have hid :
          (z.re * 1 + -1 * z.im * ↑(n + 1) - r * (z.re * ↑(n + 1) + z.im * 1)) -
            Pm * (1 - ↑(n + 1) * r) =
          (1 - ↑(n + 1) * r) * (z.re - r * z.im - Pm) - ↑(n + 1) * z.im * (r ^ 2 + 1) := by ring
      rw [hid]
      exact dvd_sub (dvd_mul_of_dvd_right ih2 _) (dvd_mul_of_dvd_right hr _)

lemma two_mul_r_mul_a_sub_split_dvd (n p M : ℕ) (r : ℤ)
    (hr : ((p ^ M : ℕ) : ℤ) ∣ r ^ 2 + 1) :
    ((p ^ M : ℕ) : ℤ) ∣
      2 * r * OeisA105751.a n -
        ((∏ k ∈ Finset.range (n + 1), (1 + (k : ℤ) * r)) -
         (∏ k ∈ Finset.range (n + 1), (1 - (k : ℤ) * r))) := by
  rw [a_eq_gaussianInt_im]
  obtain ⟨h1, h2⟩ := gaussianInt_split_mod n p M r hr
  have hid :
      2 * r * (∏ k ∈ Finset.range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)).im -
        ((∏ k ∈ Finset.range (n + 1), (1 + (k : ℤ) * r)) -
         (∏ k ∈ Finset.range (n + 1), (1 - (k : ℤ) * r))) =
      (((∏ k ∈ Finset.range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)).re +
          r * (∏ k ∈ Finset.range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)).im) -
        ∏ k ∈ Finset.range (n + 1), (1 + (k : ℤ) * r)) -
      (((∏ k ∈ Finset.range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)).re -
          r * (∏ k ∈ Finset.range (n + 1), (⟨1, (k : ℤ)⟩ : GaussianInt)).im) -
        ∏ k ∈ Finset.range (n + 1), (1 - (k : ℤ) * r)) := by ring
  rw [hid]
  exact dvd_sub h1 h2

lemma exists_sq_add_one_dvd_prime_pow (p : ℕ) (hp : p.Prime) (h4 : p % 4 = 1) (M : ℕ) :
    ∃ r : ℤ, ((p ^ M : ℕ) : ℤ) ∣ r ^ 2 + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  induction M with
  | zero => exact ⟨0, by simp⟩
  | succ M ih =>
    by_cases hM : M = 0
    · subst hM
      obtain ⟨u, hu⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mpr (by omega)
      refine ⟨(u.val : ℤ), ?_⟩
      rw [pow_one, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      simp only [ZMod.natCast_zmod_val]
      linear_combination -hu
    · obtain ⟨r, hr⟩ := ih
      obtain ⟨q, hq⟩ := hr
      have hp_dvd_r2 : (p : ℤ) ∣ r ^ 2 + 1 :=
        (dvd_pow_self (p : ℤ) hM).trans (by exact_mod_cast (⟨q, hq⟩ : ((p ^ M : ℕ) : ℤ) ∣ r ^ 2 + 1))
      have h2r_ne0 : ((2 * r : ℤ) : ZMod p) ≠ 0 := by
        intro h0
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
        have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
        rcases hpz.dvd_or_dvd h0 with h2 | hpr
        · have hle2 : p ≤ 2 := Nat.le_of_dvd (by decide) (Int.ofNat_dvd.mp h2)
          have := hp.two_le
          omega
        · have hp1 : (p : ℤ) ∣ 1 := by
            have : (1 : ℤ) = (r ^ 2 + 1) - r * r := by ring
            rw [this]
            exact dvd_sub hp_dvd_r2 (dvd_mul_of_dvd_left hpr _)
          exact hpz.not_isUnit (isUnit_of_dvd_one hp1)
      set tz : ZMod p := -((q : ZMod p) * ((2 * r : ℤ) : ZMod p)⁻¹)
      set t : ℤ := (tz.val : ℤ)
      have ht_mod : (p : ℤ) ∣ q + 2 * r * t := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        have ht_eq : (t : ZMod p) = tz := by simp [t]
        rw [ht_eq]
        have : ((2 : ZMod p) * (r : ZMod p)) * ((2 * r : ℤ) : ZMod p)⁻¹ = 1 := by
          push_cast at h2r_ne0 ⊢
          exact mul_inv_cancel₀ h2r_ne0
        simp only [tz]
        linear_combination (q : ZMod p) * (-this)
      obtain ⟨c, hc⟩ := ht_mod
      refine ⟨r + t * ((p ^ M : ℕ) : ℤ), ?_⟩
      refine ⟨c + t ^ 2 * ((p ^ (M - 1) : ℕ) : ℤ), ?_⟩
      have hpow1 : ((p ^ (M + 1) : ℕ) : ℤ) = ((p ^ M : ℕ) : ℤ) * (p : ℤ) := by
        push_cast; rw [pow_succ]
      have hpow2 : ((p ^ M : ℕ) : ℤ) = (p : ℤ) * ((p ^ (M - 1) : ℕ) : ℤ) := by
        have hM1 : M = (M - 1) + 1 := by omega
        conv_lhs => rw [hM1, pow_succ']
        push_cast; rfl
      have hpow_sq : ((p ^ M : ℕ) : ℤ) ^ 2 = ((p ^ M : ℕ) : ℤ) * (p : ℤ) * ((p ^ (M - 1) : ℕ) : ℤ) := by
        rw [sq]; conv_lhs => rhs; rw [hpow2]
        ring
      calc (r + t * ((p ^ M : ℕ) : ℤ)) ^ 2 + 1
          = (r ^ 2 + 1) + 2 * r * t * ((p ^ M : ℕ) : ℤ) + t ^ 2 * ((p ^ M : ℕ) : ℤ) ^ 2 := by ring
        _ = ((p ^ M : ℕ) : ℤ) * (q + 2 * r * t) + t ^ 2 * ((p ^ M : ℕ) : ℤ) ^ 2 := by rw [hq]; ring
        _ = ((p ^ M : ℕ) : ℤ) * ((p : ℤ) * c) +
            t ^ 2 * (((p ^ M : ℕ) : ℤ) * (p : ℤ) * ((p ^ (M - 1) : ℕ) : ℤ)) := by
            rw [hc, hpow_sq]
        _ = ((p ^ (M + 1) : ℕ) : ℤ) * (c + t ^ 2 * ((p ^ (M - 1) : ℕ) : ℤ)) := by rw [hpow1]; ring

private theorem enough_divisible_factors {m n : ℕ} (hm : 0 < m)
    {r : ℤ} (hr : (m : ℤ) ∣ r*r+1) :
    n/m ≤ #((range (n+1)).filter fun k : ℕ => (m : ℤ) ∣ 1+(k:ℤ)*r) := by
  let res := (r % (m:ℤ)).toNat
  have hz : (res : ℤ) = r % (m : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))
  have hRes : res < m := by
    have h := Int.emod_lt_of_pos r (by positivity : 0 < (m : ℤ))
    exact_mod_cast (show (res:ℤ) < (m:ℤ) by simpa only [hz] using h)
  have hd : (m:ℤ) ∣ (res:ℤ)-r := by
    rw [hz]
    exact Int.modEq_iff_dvd.mp (Int.mod_modEq r m).symm
  let image (x : Fin (n/m)) := x.val*m + res
  have hInjective : Function.Injective image := by
    intro a b hab
    apply Fin.ext
    exact Nat.eq_of_mul_eq_mul_right hm (Nat.add_right_cancel hab)
  let e : Fin (n/m) ↪ ℕ := ⟨image,hInjective⟩
  have hSubset : (univ.map e) ⊆ (range (n+1)).filter
      (fun k : ℕ => (m:ℤ) ∣ 1+(k:ℤ)*r) := by
    intro k hk
    obtain ⟨i,_,rfl⟩ := mem_map.mp hk
    apply mem_filter.mpr
    constructor
    · apply mem_range.mpr
      have hMul := Nat.mul_le_mul_right m (show i.val+1 ≤ n/m by omega)
      have hDiv := Nat.div_mul_le_self n m
      have hSize : i.val*m+res < (i.val+1)*m := by rw [Nat.add_mul]; omega
      exact ((hSize.trans_le (hMul.trans hDiv)).trans_le (Nat.le_succ _))
    · change (m : ℤ) ∣ 1 + ((i.val*m+res : ℕ) : ℤ)*r
      push_cast
      have hEq : 1+((i.val : ℤ)*m+res)*r =
          (r*r+1) + ((res:ℤ)-r)*r + m*((i.val:ℤ)*r) := by ring
      rw [hEq]
      exact dvd_add (dvd_add hr (dvd_mul_of_dvd_left hd _)) (dvd_mul_right _ _)
  simpa only [card_map,card_univ,Fintype.card_fin] using card_le_card hSubset

private theorem power_dvd_of_index_count {p : ℕ} (J : Finset ℕ) (hJ : ∀ j ∈ J, 1 ≤ j)
    (a : ℤ) :
    (p:ℤ) ^ #(J.filter fun j => (p:ℤ)^j ∣ a) ∣ a := by
  let C := J.filter fun j => (p:ℤ)^j ∣ a
  by_cases hc : C.Nonempty
  · have hMax : C.max' hc ∈ C := max'_mem _ _
    have hSubset : C ⊆ Icc 1 (C.max' hc) := by
      intro j hj
      exact mem_Icc.mpr ⟨hJ j (mem_filter.mp hj).1,le_max' C j hj⟩
    have hCard := card_le_card hSubset
    rw [Nat.card_Icc] at hCard
    have hLe : C.card ≤ C.max' hc := by omega
    exact (pow_dvd_pow (p:ℤ) hLe).trans ((mem_filter.mp hMax).2)
  · have hEmpty := not_nonempty_iff_eq_empty.mp hc
    change (p:ℤ)^C.card ∣ a
    simp [hEmpty]

private theorem factorial_power_dvd_split {p n : ℕ} (hp : p.Prime) {r : ℤ}
    (hr : (p:ℤ)^(n+1) ∣ r*r+1) :
    (p:ℤ)^padicValNat p n.factorial ∣ ∏ k ∈ range (n+1), (1+(k:ℤ)*r) := by
  let _ : Fact p.Prime := ⟨hp⟩
  let J := Ico 1 (Nat.log p n + 1)
  let A (k : ℕ) := J.filter fun j => (p:ℤ)^j ∣ 1+(k:ℤ)*r
  have hDvd : (p:ℤ)^(∑ k ∈ range (n+1), (A k).card) ∣
      ∏ k ∈ range (n+1), (1+(k:ℤ)*r) := by
    rw [← prod_pow_eq_pow_sum]
    apply prod_dvd_prod_of_dvd
    intro k _
    exact power_dvd_of_index_count J (fun j hj => (mem_Ico.mp hj).1) _
  have hCount (j : ℕ) (hj : j ∈ J) : n / p^j ≤
      #((range (n+1)).filter fun k : ℕ => (p:ℤ)^j ∣ 1+(k:ℤ)*r) := by
    have hLe : j ≤ n+1 := by
      have hLog := Nat.log_le_self p n
      have hJ := (mem_Ico.mp hj).2
      omega
    have hm : 0 < p^j := pow_pos hp.pos _
    have hRoot : ((p^j:ℕ):ℤ) ∣ r*r+1 := by
      push_cast
      exact (pow_dvd_pow (p:ℤ) hLe).trans hr
    simpa only [Nat.cast_pow] using enough_divisible_factors hm hRoot (n := n)
  have hSum :
      (∑ k ∈ range (n+1), (A k).card) =
        ∑ j ∈ J, #((range (n+1)).filter fun k : ℕ => (p:ℤ)^j ∣ 1+(k:ℤ)*r) := by
    simp only [A,Finset.card_filter]
    rw [sum_comm]
  have hBound : padicValNat p n.factorial ≤ ∑ k ∈ range (n+1), (A k).card := by
    rw [hSum,padicValNat_factorial (Nat.lt_succ_self (Nat.log p n))]
    exact sum_le_sum hCount
  exact (pow_dvd_pow (p:ℤ) hBound).trans hDvd

theorem factorial_power_dvd_a {p : ℕ} (hp : p.Prime) (h4 : p % 4 = 1) (n : ℕ) :
    (p:ℤ)^padicValNat p n.factorial ∣ OeisA105751.a n := by
  let _ : Fact p.Prime := ⟨hp⟩
  let e := padicValNat p n.factorial
  obtain ⟨r,hr⟩ := exists_sq_add_one_dvd_prime_pow p hp h4 (n+1)
  have hRoot : (p:ℤ)^(n+1) ∣ r*r+1 := by
    simpa only [Nat.cast_pow,pow_two] using hr
  have hMinusRoot : (p:ℤ)^(n+1) ∣ (-r)*(-r)+1 := by
    simpa only [neg_mul_neg] using hRoot
  have hPlus := factorial_power_dvd_split hp hRoot
  have hMinus := factorial_power_dvd_split hp hMinusRoot
  simp only [mul_neg,← sub_eq_add_neg] at hMinus
  have hCompare := two_mul_r_mul_a_sub_split_dvd n p (n+1) r hr
  have hBound : e ≤ n+1 := (padicValNat_factorial_le (p := p) n).trans (Nat.le_succ _)
  have hDvd : (p:ℤ)^e ∣ 2*r*OeisA105751.a n := by
    have hD := (pow_dvd_pow (p:ℤ) hBound).trans (by exact_mod_cast hCompare)
    simpa [e] using dvd_add hD (dvd_sub hPlus hMinus)
  have hpInt : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  have hCoprime : ¬ (p:ℤ) ∣ 2*r := by
    intro h
    rcases hpInt.dvd_or_dvd h with hTwo|hR
    · have hLe : p ≤ 2 := Nat.le_of_dvd (by decide) (Int.ofNat_dvd.mp hTwo)
      have := hp.two_le
      omega
    · have hP : (p:ℤ) ∣ r*r+1 := (dvd_pow_self _ (Nat.succ_ne_zero n)).trans hRoot
      have hOne := dvd_sub hP (dvd_mul_of_dvd_left hR r)
      have hp1 : (p:ℤ) ∣ 1 := by
        simpa [add_comm] using hOne
      exact hpInt.not_isUnit (isUnit_of_dvd_one hp1)
  exact hpInt.pow_dvd_of_dvd_mul_left e hCoprime hDvd

end OMA.MollFactorial

theorem OMA.solution : OMA.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1.H1 :=
  fun p hp h4 n => OMA.MollFactorial.factorial_power_dvd_a (p := p) hp h4 n
