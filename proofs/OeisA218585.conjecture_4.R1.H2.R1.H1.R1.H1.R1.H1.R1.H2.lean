import OMAReductions.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1_H1_R1
import Mathlib

-- Step OeisA218585.conjecture_4.R1.H2.R1.H1.R1.H1.R1.H1.R1.H2: hypothesis H2 of reduction OeisA218585.conjecture_4.R1.H2.R1.H1.R1.H1.R1.H1.R1
-- Credit: @ivillar

/-!
The three-four-one estimate. For primes in the class 1 mod 3 the combination
`4 cos x cos u + cos 2x cos 2u` is at least `-3`; prime powers contribute a bounded amount;
and the von Mangoldt series over the class 1 mod 3 has a simple pole of residue 1/2 at 1
(Mathlib's `LFunctionResidueClassAux`), so the limiting lower bound is `-3/2 > -7/4`.
-/
namespace F2Oeis
open Filter Real ArithmeticFunction
open scoped Topology Classical

theorem trig (x u : ℝ) : -3 ≤ 4 * (cos x * cos u) + cos (2 * x) * cos (2 * u) := by
  rw [Real.cos_two_mul, Real.cos_two_mul]
  have h1 := Real.cos_sq_le_one x
  have h2 := Real.cos_sq_le_one u
  nlinarith [sq_nonneg (1 + cos x * cos u), mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]

theorem cpow_neg_re (n : ℕ) (hn : n ≠ 0) (x y : ℝ) :
    ((n : ℂ) ^ (-(⟨x, y⟩ : ℂ))).re = (n : ℝ) ^ (-x) * cos (y * Real.log n) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [Complex.cpow_def_of_ne_zero hn', ← Complex.natCast_log, Complex.exp_re,
    Real.rpow_def_of_pos hpos]
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im]
  rw [show Real.log n * -x - 0 * -y = Real.log n * -x by ring,
    show Real.log n * -y + 0 * -x = -(y * Real.log n) by ring, Real.cos_neg]

theorem cpow_neg_norm (n : ℕ) (hn : n ≠ 0) (x y : ℝ) :
    ‖(n : ℂ) ^ (-(⟨x, y⟩ : ℂ))‖ = (n : ℝ) ^ (-x) := by
  rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
  simp

theorem term_eq (f : ℕ → ℂ) (s : ℂ) (n : ℕ) (hn : n ≠ 0) :
    LSeries.term f s n = f n * (n : ℂ) ^ (-s) := by
  rw [LSeries.term_of_ne_zero hn, Complex.cpow_neg, div_eq_mul_inv]

theorem summ (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ Λ n) {s : ℂ} (hs : 1 < s.re) : LSeriesSummable f s := by
  have h := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  refine Summable.of_norm_bounded (g := fun n => ‖LSeries.term (fun n => (Λ n : ℂ)) s n‖) h.norm
    (fun n => LSeries.norm_term_le s ?_)
  simpa [abs_of_nonneg vonMangoldt_nonneg] using hf n

theorem rho_le (n : ℕ) (hn : n ≠ 0) (h : ℝ) (hh : 0 < h) :
    (n : ℝ) ^ (-(1 + h)) ≤ 1 / n := by
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero hn
  calc (n : ℝ) ^ (-(1 + h)) ≤ (n : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    _ = 1 / n := by rw [Real.rpow_neg_one, one_div]

/-- The termwise bound. -/
theorem termwise (θ : ℕ → ℝ) (a b : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ Λ n) (hb : ∀ n, ‖b n‖ ≤ Λ n)
    (hap : ∀ p : ℕ, p.Prime → a p = ((Λ p * (if p % 3 = 1 then cos (θ p) else 0) : ℝ) : ℂ))
    (hbp : ∀ p : ℕ, p.Prime → b p = ((Λ p * (if p % 3 = 1 then cos (2 * θ p) else 0) : ℝ) : ℂ))
    (t h : ℝ) (hh : 0 < h) (n : ℕ) :
    (-3) * (LSeries.term (fun n => ((vonMangoldt.residueClass (1 : ZMod 3) n : ℝ) : ℂ))
        (⟨1 + h, 0⟩ : ℂ) n).re + (-5) * ((if n.Prime then 0 else Λ n) / n) ≤
      4 * (LSeries.term a (⟨1 + h, t⟩ : ℂ) n).re + (LSeries.term b (⟨1 + h, 2 * t⟩ : ℂ) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hρ : 0 < (n : ℝ) ^ (-(1 + h)) :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) _
  have hΛ : 0 ≤ Λ n := vonMangoldt_nonneg
  have hRn : 0 ≤ vonMangoldt.residueClass (1 : ZMod 3) n := vonMangoldt.residueClass_nonneg _ n
  have eR : (LSeries.term (fun n => ((vonMangoldt.residueClass (1 : ZMod 3) n : ℝ) : ℂ))
        (⟨1 + h, 0⟩ : ℂ) n).re = vonMangoldt.residueClass (1 : ZMod 3) n * (n : ℝ) ^ (-(1 + h)) := by
    rw [term_eq _ _ _ hn, Complex.re_ofReal_mul, cpow_neg_re n hn]
    simp
  rw [eR, term_eq a _ _ hn, term_eq b _ _ hn]
  by_cases hp : n.Prime
  · rw [hap n hp, hbp n hp, Complex.re_ofReal_mul, Complex.re_ofReal_mul, cpow_neg_re n hn,
      cpow_neg_re n hn, if_pos hp]
    have hmod : ((n : ZMod 3) = 1) ↔ n % 3 = 1 := by
      rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff']
    by_cases h3 : n % 3 = 1
    · have hR : vonMangoldt.residueClass (1 : ZMod 3) n = Λ n := by
        simp [vonMangoldt.residueClass, Set.indicator, hmod.mpr h3]
      rw [hR, if_pos h3, if_pos h3]
      have key := mul_nonneg (mul_nonneg hΛ hρ.le)
        (sub_nonneg.mpr (trig (θ n) (t * Real.log n)))
      have e2 : 2 * t * Real.log n = 2 * (t * Real.log n) := by ring
      rw [e2, zero_div, mul_zero, add_zero]
      have e3 : 4 * (Λ n * cos (θ n) * ((n : ℝ) ^ (-(1 + h)) * cos (t * Real.log n))) +
          Λ n * cos (2 * θ n) * ((n : ℝ) ^ (-(1 + h)) * cos (2 * (t * Real.log n))) -
          (-3 * (Λ n * (n : ℝ) ^ (-(1 + h)))) = Λ n * (n : ℝ) ^ (-(1 + h)) *
          (4 * (cos (θ n) * cos (t * Real.log n)) + cos (2 * θ n) * cos (2 * (t * Real.log n)) - -3) := by
        ring
      linarith
    · have hR : vonMangoldt.residueClass (1 : ZMod 3) n = 0 := by
        simp [vonMangoldt.residueClass, Set.indicator, mt hmod.mp h3]
      rw [hR, if_neg h3, if_neg h3]
      simp
  · rw [if_neg hp]
    have b1 : |(a n * (n : ℂ) ^ (-(⟨1 + h, t⟩ : ℂ))).re| ≤ Λ n / n := by
      calc |(a n * (n : ℂ) ^ (-(⟨1 + h, t⟩ : ℂ))).re|
          ≤ ‖a n * (n : ℂ) ^ (-(⟨1 + h, t⟩ : ℂ))‖ := Complex.abs_re_le_norm _
        _ = ‖a n‖ * (n : ℝ) ^ (-(1 + h)) := by rw [norm_mul, cpow_neg_norm n hn]
        _ ≤ Λ n * (1 / n) := mul_le_mul (ha n) (rho_le n hn h hh) hρ.le hΛ
        _ = Λ n / n := by ring
    have b2 : |(b n * (n : ℂ) ^ (-(⟨1 + h, 2 * t⟩ : ℂ))).re| ≤ Λ n / n := by
      calc |(b n * (n : ℂ) ^ (-(⟨1 + h, 2 * t⟩ : ℂ))).re|
          ≤ ‖b n * (n : ℂ) ^ (-(⟨1 + h, 2 * t⟩ : ℂ))‖ := Complex.abs_re_le_norm _
        _ = ‖b n‖ * (n : ℝ) ^ (-(1 + h)) := by rw [norm_mul, cpow_neg_norm n hn]
        _ ≤ Λ n * (1 / n) := mul_le_mul (hb n) (rho_le n hn h hh) hρ.le hΛ
        _ = Λ n / n := by ring
    have c1 := (abs_le.mp b1).1
    have c2 := (abs_le.mp b2).1
    have c3 := mul_nonneg hRn hρ.le
    linarith

theorem three_four_one : ∀ (θ : ℕ → ℝ) (a b : ℕ → ℂ), (∀ n, ‖a n‖ ≤ Λ n) → (∀ n, ‖b n‖ ≤ Λ n) →
  (∀ p : ℕ, p.Prime → a p = ((Λ p*(if p%3 = 1 then cos (θ p) else 0):ℝ):ℂ)) →
  (∀ p : ℕ, p.Prime → b p = ((Λ p*(if p%3 = 1 then cos (2*θ p) else 0):ℝ):ℂ)) →
  ∀ t : ℝ, ∀ᶠ h : ℝ in 𝓝[>] 0, -(7/4:ℝ) ≤ h *
    (4*(LSeries a ((⟨1,t⟩:ℂ)+h)).re + (LSeries b ((⟨1,2*t⟩:ℂ)+h)).re) := by
  intro θ a b ha hb hap hbp t
  have hGsum : Summable (fun n : ℕ => (if n.Prime then 0 else Λ n) / (n : ℝ)) := by
    have h := vonMangoldt.summable_residueClass_non_primes_div (0 : ZMod 1)
    refine h.congr (fun n => ?_)
    have : vonMangoldt.residueClass (0 : ZMod 1) n = Λ n := by
      simp [vonMangoldt.residueClass, Set.indicator, Subsingleton.elim (n : ZMod 1) 0]
    rw [this]
  have hRle : ∀ n, ‖((vonMangoldt.residueClass (1 : ZMod 3) n : ℝ) : ℂ)‖ ≤ Λ n := by
    intro n
    rw [Complex.norm_real, Real.norm_of_nonneg (vonMangoldt.residueClass_nonneg _ n)]
    exact vonMangoldt.residueClass_le _ n
  have key : ∀ h : ℝ, 0 < h →
      -(3/2) - 3 * (h * (vonMangoldt.LFunctionResidueClassAux (1 : ZMod 3) ((1 + h : ℝ) : ℂ)).re)
        - 5 * (h * ∑' n : ℕ, (if n.Prime then 0 else Λ n) / (n : ℝ)) ≤
      h * (4*(LSeries a ((⟨1,t⟩:ℂ)+h)).re + (LSeries b ((⟨1,2*t⟩:ℂ)+h)).re) := by
    intro h hh
    have e1 : (⟨1, t⟩ : ℂ) + (h : ℂ) = ⟨1 + h, t⟩ := by apply Complex.ext <;> simp
    have e2 : (⟨1, 2 * t⟩ : ℂ) + (h : ℂ) = ⟨1 + h, 2 * t⟩ := by apply Complex.ext <;> simp
    have e0 : ((1 + h : ℝ) : ℂ) = ⟨1 + h, 0⟩ := rfl
    rw [e1, e2]
    have hre : ∀ y : ℝ, 1 < (⟨1 + h, y⟩ : ℂ).re := fun y => by simp [hh]
    have A1 := Complex.hasSum_re (summ a ha (hre t)).hasSum
    have B1 := Complex.hasSum_re (summ b hb (hre (2 * t))).hasSum
    have R0 := Complex.hasSum_re (summ _ hRle (hre 0)).hasSum
    have le := hasSum_le (termwise θ a b ha hb hap hbp t h hh)
      ((R0.mul_left (-3)).add (hGsum.hasSum.mul_left (-5))) ((A1.mul_left 4).add B1)
    have eqAux := vonMangoldt.eqOn_LFunctionResidueClassAux (q := 3) (a := 1) isUnit_one
      (show ((1 + h : ℝ) : ℂ) ∈ {s : ℂ | 1 < s.re} by simp [hh])
    have tot : (Nat.totient 3 : ℂ) = 2 := by
      rw [Nat.totient_prime Nat.prime_three]; norm_num
    have hval : (∑' n, LSeries.term (fun n => ((vonMangoldt.residueClass (1 : ZMod 3) n : ℝ) : ℂ))
        (⟨1 + h, 0⟩ : ℂ) n).re =
        (vonMangoldt.LFunctionResidueClassAux (1 : ZMod 3) ((1 + h : ℝ) : ℂ)).re + 1 / (2 * h) := by
      rw [eqAux]
      simp only [tot]
      have e3 : ((2 : ℂ)⁻¹ / (((1 + h : ℝ) : ℂ) - 1)) = ((1 / (2 * h) : ℝ) : ℂ) := by
        push_cast
        field_simp
        ring
      rw [e3, Complex.sub_re, Complex.ofReal_re]
      change (LSeries _ _).re = _
      rw [e0]
      ring
    rw [hval] at le
    have hmul := mul_le_mul_of_nonneg_left le hh.le
    have hne : h ≠ 0 := hh.ne'
    have expand : h * (-3 * ((vonMangoldt.LFunctionResidueClassAux (1 : ZMod 3) ((1 + h : ℝ) : ℂ)).re
        + 1 / (2 * h)) + -5 * ∑' n : ℕ, (if n.Prime then 0 else Λ n) / (n : ℝ)) =
        -(3/2) - 3 * (h * (vonMangoldt.LFunctionResidueClassAux (1 : ZMod 3) ((1 + h : ℝ) : ℂ)).re)
        - 5 * (h * ∑' n : ℕ, (if n.Prime then 0 else Λ n) / (n : ℝ)) := by
      field_simp
      ring
    rw [expand] at hmul
    exact hmul
  have lim : Tendsto (fun h : ℝ =>
      -(3/2) - 3 * (h * (vonMangoldt.LFunctionResidueClassAux (1 : ZMod 3) ((1 + h : ℝ) : ℂ)).re)
        - 5 * (h * ∑' n : ℕ, (if n.Prime then 0 else Λ n) / (n : ℝ))) (𝓝[>] 0) (𝓝 (-(3/2))) := by
    have hcont := vonMangoldt.continuousOn_LFunctionResidueClassAux (1 : ZMod 3)
    have h1mem : (1 : ℂ) ∈ {s : ℂ | 1 ≤ s.re} := by simp
    have hto : Tendsto (fun h : ℝ => ((1 + h : ℝ) : ℂ)) (𝓝[>] 0) (𝓝[{s : ℂ | 1 ≤ s.re}] 1) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · have : Tendsto (fun h : ℝ => ((1 + h : ℝ) : ℂ)) (𝓝 0) (𝓝 (((1 + 0 : ℝ)) : ℂ)) :=
          (Complex.continuous_ofReal.comp (continuous_const.add continuous_id)).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with h hh
        show 1 ≤ ((1 + h : ℝ) : ℂ).re
        rw [Complex.ofReal_re]
        linarith [Set.mem_Ioi.mp hh]
    have haux : Tendsto (fun h : ℝ =>
        (vonMangoldt.LFunctionResidueClassAux (1 : ZMod 3) ((1 + h : ℝ) : ℂ)).re) (𝓝[>] 0)
        (𝓝 (vonMangoldt.LFunctionResidueClassAux (1 : ZMod 3) 1).re) :=
      (Complex.continuous_re.tendsto _).comp ((hcont 1 h1mem).tendsto.comp hto)
    have hid : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    have := ((tendsto_const_nhds (x := -(3/2 : ℝ))).sub ((hid.mul haux).const_mul 3)).sub
      ((hid.mul_const (∑' n : ℕ, (if n.Prime then 0 else Λ n) / (n : ℝ))).const_mul 5)
    simpa using this
  filter_upwards [lim.eventually_const_lt (by norm_num : -(7/4:ℝ) < -(3/2)), self_mem_nhdsWithin]
    with h h1 h2
  exact h1.le.trans (key h h2)

end F2Oeis

theorem OMA.solution : OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1_H1_R1.H2 :=
  F2Oeis.three_four_one
