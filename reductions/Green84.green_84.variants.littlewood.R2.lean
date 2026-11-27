import FormalConjectures.GreensOpenProblems.«84»
import Mathlib

-- Credit: @MrSeizy

/-!
# Reduction of Green's Littlewood problem using piecewise smooth waves

The exterior-frequency analysis follows §5 of OpenAI's October 5, 2026
Ultraflat real Littlewood polynomials. The projection and real rounding
argument adapts @ChadySaba's R1 reduction. The real defect rounding in H1
is the estimate used in @BetAdmin237's merged Golay proof.
-/

namespace OMA.R_Green84_green_84_variants_littlewood_R2

open Filter MeasureTheory Set
open scoped ComplexConjugate ExponentialSum Finset Interval Topology

/-- Defect-sensitive rounding for real coefficients on a consecutive frequency interval. -/
def H1 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ X : ℕ → ℝ, (∀ k < N, |X k| ≤ 1) →
    ∃ ε : ℕ → ℤ, (∀ k < N, ε k = 1 ∨ ε k = -1) ∧
      let μ := (∑ k ∈ Finset.range N, (1 - |X k|)) / 2
      ∀ θ : ℝ, ‖∑ k ∈ Finset.range N, ((ε k : ℂ) - (X k : ℂ)) * e (k * θ)‖ ≤
        C * (1 + √(μ * Real.log (80 * N / μ)))

/-- A wave with a uniform in-band cap and a piecewise smooth, matched leading phase. -/
def H2 : Prop :=
  ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧ ∀ δ ∈ Ioo 0 δ₀,
    ∃ (m : ℕ) (d M : ℝ), 0 < d ∧ 0 ≤ M ∧ ∀ᶠ N : ℕ in atTop,
      ∃ (B : C(UnitAddCircle, ℂ)) (s : ℕ → ℝ) (P : ℝ → ℝ)
        (φ p₁ p₂ : ℕ → ℝ → ℝ) (f f₁ f₂ : ℕ → ℝ → ℂ),
        Monotone s ∧ s 0 = 0 ∧ s m = 1 ∧ P 0 = P 1 ∧
        (∀ t, B (-t) = conj (B t) ∧ 1 ≤ ‖B t‖ ∧ ‖B t‖ ≤ 1 + C * δ) ∧
        (∀ k : ℕ, k < N → √N * ‖fourierCoeff B k‖ ≤ 1 + C * √δ) ∧
        ∀ i < m, let J := Icc (s i) (s (i+1))
          ContinuousOn (p₂ i) J ∧ ContinuousOn (f₂ i) J ∧
          ∀ t ∈ J, HasDerivWithinAt (φ i) (P t) J t ∧
            HasDerivWithinAt P (p₁ i t) J t ∧
            HasDerivWithinAt (p₁ i) (p₂ i t) J t ∧
            HasDerivWithinAt (f i) (f₁ i t) J t ∧
            HasDerivWithinAt (f₁ i) (f₂ i t) J t ∧
            d ≤ P t ∧ P t ≤ 1-d ∧ |p₁ i t| ≤ M ∧ |p₂ i t| ≤ M ∧
            ‖f i t‖ ≤ M ∧ ‖f₁ i t‖ ≤ M ∧ ‖f₂ i t‖ ≤ M ∧
            B (t : UnitAddCircle) =
              f i t * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((N:ℝ) * φ i t : ℝ))

/-- Two integrations by parts, retaining the leading boundary term. -/
lemma oscillatory_piece {a b D : ℝ} (hab : a ≤ b) (hD : 0 < D)
    {f f₁ f₂ v v₁ v₂ E : ℝ → ℂ}
    (hf : ∀ t ∈ Icc a b, HasDerivWithinAt f (f₁ t) (Icc a b) t)
    (hf₁ : ∀ t ∈ Icc a b, HasDerivWithinAt f₁ (f₂ t) (Icc a b) t)
    (hf₂ : ContinuousOn f₂ (Icc a b))
    (hv : ∀ t ∈ Icc a b, HasDerivWithinAt v (v₁ t) (Icc a b) t)
    (hv₁ : ∀ t ∈ Icc a b, HasDerivWithinAt v₁ (v₂ t) (Icc a b) t)
    (hv₂ : ContinuousOn v₂ (Icc a b))
    (hE : ∀ t ∈ Icc a b, HasDerivWithinAt E ((D : ℂ) * v t * E t) (Icc a b) t)
    {M d : ℝ} (hM : 0 ≤ M) (hd : 0 < d)
    (hbound : ∀ t ∈ Icc a b,
      ‖f t‖ ≤ M ∧ ‖f₁ t‖ ≤ M ∧ ‖f₂ t‖ ≤ M ∧
      d ≤ ‖v t‖ ∧ ‖v₁ t‖ ≤ M ∧ ‖v₂ t‖ ≤ M ∧ ‖E t‖ = 1) :
    ‖(∫ t in a..b, f t * E t) -
      ((f b * E b / v b - f a * E a / v a) / (D : ℂ))‖ ≤
      (2 * (M / d^2 + M^2 / d^3) +
        (b-a) * (M / d^2 + 4 * M^2 / d^3 + 3 * M^3 / d^4)) / D^2 := by
  let U (t : ℝ) := f₁ t / (v t)^2 - f t * v₁ t / (v t)^3
  let W (t : ℝ) := f₂ t / (v t)^2 - (3 * f₁ t * v₁ t + f t * v₂ t) / (v t)^3 +
    3 * f t * (v₁ t)^2 / (v t)^4
  have hne (t) (ht : t ∈ Icc a b) : v t ≠ 0 :=
    norm_pos_iff.mp (hd.trans_le (hbound t ht).2.2.2.1)
  have hU (t) (ht : t ∈ Icc a b) : HasDerivWithinAt U (W t) (Icc a b) t := by
    have h := (((hf₁ t ht).div ((hv t ht).pow 2) (pow_ne_zero _ (hne t ht))).sub
      (((hf t ht).mul (hv₁ t ht)).div ((hv t ht).pow 3) (pow_ne_zero _ (hne t ht))))
    refine h.congr_deriv ?_
    dsimp [W]
    field_simp [hne t ht]; ring
  have hc {g : ℝ → ℂ} {g' : ℝ → ℂ}
      (h : ∀ t ∈ Icc a b, HasDerivWithinAt g (g' t) (Icc a b) t) :
      ContinuousOn g (Icc a b) := fun t ht ↦ (h t ht).continuousWithinAt
  have hW : ContinuousOn W (Icc a b) := by
    dsimp [W]
    exact ((hf₂.div ((hc hv).pow 2) (fun t ht ↦ pow_ne_zero _ (hne t ht))).sub
      (((continuousOn_const.mul (hc hf₁)).mul (hc hv₁)).add ((hc hf).mul hv₂) |>.div
        ((hc hv).pow 3) (fun t ht ↦ pow_ne_zero _ (hne t ht)))).add
      ((((continuousOn_const.mul (hc hf)).mul ((hc hv₁).pow 2))).div
        ((hc hv).pow 4) (fun t ht ↦ pow_ne_zero _ (hne t ht)))
  have hfirst (t) (ht : t ∈ Icc a b) :
      HasDerivWithinAt (fun t ↦ f t * E t / v t)
        ((D : ℂ) * (f t * E t) + U t * (v t * E t)) (Icc a b) t := by
    refine (((hf t ht).mul (hE t ht)).div (hv t ht) (hne t ht)).congr_deriv ?_
    dsimp [U]
    field_simp [hne t ht]; ring
  have hsecond (t) (ht : t ∈ Icc a b) :
      HasDerivWithinAt (fun t ↦ U t * E t)
        ((D : ℂ) * (U t * (v t * E t)) + W t * E t) (Icc a b) t := by
    exact ((hU t ht).mul (hE t ht)).congr_deriv (by ring)
  have hintA : IntervalIntegrable (fun t ↦ f t * E t) volume a b :=
    ((hc hf).mul (hc hE)).intervalIntegrable_of_Icc hab
  have hintB : IntervalIntegrable (fun t ↦ U t * (v t * E t)) volume a b :=
    ((hc hU).mul ((hc hv).mul (hc hE))).intervalIntegrable_of_Icc hab
  have hintC : IntervalIntegrable (fun t ↦ W t * E t) volume a b :=
    (hW.mul (hc hE)).intervalIntegrable_of_Icc hab
  have hA := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (hc hfirst) (fun t ht ↦ (hfirst t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)) ((hintA.const_mul (D : ℂ)).add hintB)
  have hB := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (hc hsecond) (fun t ht ↦ (hsecond t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)) ((hintB.const_mul (D : ℂ)).add hintC)
  rw [intervalIntegral.integral_add (hintA.const_mul _) hintB,
    intervalIntegral.integral_const_mul] at hA
  rw [intervalIntegral.integral_add (hintB.const_mul _) hintC,
    intervalIntegral.integral_const_mul] at hB
  have hidentity : (∫ t in a..b, f t * E t) -
      (f b * E b / v b - f a * E a / v a) / (D : ℂ) =
      (-(U b * E b - U a * E a) + ∫ t in a..b, W t * E t) / (D : ℂ)^2 := by
    have hDc : (D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hD.ne'
    field_simp [hDc]
    linear_combination (D : ℂ) * hA - hB
  have hpow {u : ℝ} (hu : 0 ≤ u) {w : ℝ} (hw : d ≤ w) (n : ℕ) :
      u / w^n ≤ u / d^n :=
    div_le_div_of_nonneg_left hu (pow_pos hd _) (pow_le_pow_left₀ hd.le hw _)
  have habsU (t) (ht : t ∈ Icc a b) : ‖U t‖ ≤ M / d^2 + M^2 / d^3 := by
    obtain ⟨h0,h1,_,hv0,hv1,_,_⟩ := hbound t ht
    calc
      _ ≤ ‖f₁ t / (v t)^2‖ + ‖f t * v₁ t / (v t)^3‖ := norm_sub_le _ _
      _ ≤ _ := by
        simp only [norm_div, norm_mul, norm_pow]
        refine add_le_add ((div_le_div_of_nonneg_right h1 (by positivity)).trans (hpow hM hv0 2)) ?_
        refine (div_le_div_of_nonneg_right ?_ (by positivity)).trans (hpow (sq_nonneg M) hv0 3)
        rw [pow_two]
        gcongr
  have habsW (t) (ht : t ∈ Icc a b) :
      ‖W t‖ ≤ M / d^2 + 4 * M^2 / d^3 + 3 * M^3 / d^4 := by
    obtain ⟨h0,h1,h2,hv0,hv1,hv2,hE0⟩ := hbound t ht
    dsimp [W]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · simp only [norm_div, norm_pow]
        exact (div_le_div_of_nonneg_right h2 (by positivity)).trans (hpow hM hv0 2)
      · simp only [norm_div, norm_pow]
        refine (div_le_div_of_nonneg_right ((norm_add_le _ _).trans ?_) (by positivity)).trans
          (hpow (by positivity) hv0 3)
        simp only [norm_mul, Complex.norm_ofNat]
        rw [pow_two]
        calc
          _ ≤ 3 * M * M + M * M := by gcongr
          _ = _ := by ring
    · simp only [norm_div, norm_mul, norm_pow, Complex.norm_ofNat]
      refine (div_le_div_of_nonneg_right ?_ (by positivity)).trans (hpow (by positivity) hv0 4)
      calc
        _ ≤ 3 * M * M^2 := by gcongr
        _ = _ := by ring
  have hC : ‖∫ t in a..b, W t * E t‖ ≤
      (b-a) * (M / d^2 + 4 * M^2 / d^3 + 3 * M^3 / d^4) := by
    rw [mul_comm, ← abs_of_nonneg (sub_nonneg.mpr hab)]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    have ht : t ∈ Icc a b := uIoc_subset_uIcc ht |> (uIcc_of_le hab ▸ ·)
    rw [norm_mul, (hbound t ht).2.2.2.2.2.2, mul_one]
    exact habsW t ht
  rw [hidentity, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD]
  apply div_le_div_of_nonneg_right _ (by positivity)
  refine (norm_add_le _ _).trans (add_le_add ?_ hC)
  rw [norm_neg]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul, (hbound b ⟨hab,le_rfl⟩).2.2.2.2.2.2,
    (hbound a ⟨le_rfl,hab⟩).2.2.2.2.2.2, mul_one, mul_one, two_mul]
  exact add_le_add (habsU b ⟨hab,le_rfl⟩) (habsU a ⟨le_rfl,hab⟩)

lemma unit_fourier_eq_exp (k : ℤ) (t : ℝ) :
    (fourier k (t : UnitAddCircle) : ℂ) =
      Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((k : ℝ) * t : ℝ)) := by
  rw [fourier_coe_apply]
  congr 1
  simp only [Complex.ofReal_one, div_one, Complex.ofReal_mul, Complex.ofReal_intCast]
  ring

lemma exterior_phase_gap {n k p d : ℝ} (hn : 0 < n) (hd : 0 < d)
    (hp : d ≤ p) (hp' : p ≤ 1-d) (hk : k ≤ 0 ∨ n ≤ k) :
    (d / 2) * (n + |k|) ≤ |n*p-k| := by
  have hd1 : d ≤ 1 := by linarith
  rcases hk with hk | hk
  · rw [abs_of_nonpos hk, abs_of_nonneg (by nlinarith)]
    nlinarith [mul_le_mul_of_nonneg_left hp hn.le, mul_nonneg (sub_nonneg.mpr hd1) (neg_nonneg.mpr hk)]
  · rw [abs_of_nonneg (by linarith : 0 ≤ k), abs_of_nonpos (by nlinarith)]
    nlinarith [mul_le_mul_of_nonneg_left hp' hn.le,
      mul_nonneg (sub_nonneg.mpr hk) (show 0 ≤ 1-d/2 by linarith)]

/-- The leading boundary terms cancel at the joins, leaving exterior quadratic decay. -/
lemma piecewise_fourier_decay {m : ℕ} {d M : ℝ} (hd : 0 < d) (hM : 0 ≤ M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {N : ℕ}, 0 < N →
    ∀ {s : ℕ → ℝ}, Monotone s → s 0 = 0 → s m = 1 →
    ∀ {B : C(UnitAddCircle, ℂ)} {P : ℝ → ℝ}, P 0 = P 1 →
    ∀ {φ p₁ p₂ : ℕ → ℝ → ℝ} {f f₁ f₂ : ℕ → ℝ → ℂ},
    (∀ i < m, let J := Icc (s i) (s (i+1))
      ContinuousOn (p₂ i) J ∧ ContinuousOn (f₂ i) J ∧
      ∀ t ∈ J, HasDerivWithinAt (φ i) (P t) J t ∧
        HasDerivWithinAt P (p₁ i t) J t ∧
        HasDerivWithinAt (p₁ i) (p₂ i t) J t ∧
        HasDerivWithinAt (f i) (f₁ i t) J t ∧
        HasDerivWithinAt (f₁ i) (f₂ i t) J t ∧
        d ≤ P t ∧ P t ≤ 1-d ∧
        |p₁ i t| ≤ M ∧ |p₂ i t| ≤ M ∧
        ‖f i t‖ ≤ M ∧ ‖f₁ i t‖ ≤ M ∧ ‖f₂ i t‖ ≤ M ∧
        B (t : UnitAddCircle) =
          f i t * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((N:ℝ) * φ i t : ℝ))) →
    ∀ k : ℤ, (k < 0 ∨ (N : ℤ) ≤ k) →
      ‖fourierCoeff B k‖ ≤ K / ((N:ℝ) + |(k:ℝ)|)^2 := by
  let c : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  have hc : ‖c‖ = 2 * Real.pi := by
    simp [c, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  let A := (1+2*Real.pi)*M
  let r := Real.pi*d
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hAM : M ≤ A := by dsimp [A]; nlinarith [mul_nonneg Real.pi_pos.le hM]
  have hr : 0 < r := mul_pos Real.pi_pos hd
  let U := A / r^2 + A^2 / r^3
  let W := A / r^2 + 4 * A^2 / r^3 + 3*A^3 / r^4
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  refine ⟨(m:ℝ)*(2*U+W), by positivity, ?_⟩
  intro N hN s hs hs₀ hs₁ B P hP φ p₁ p₂ f f₁ f₂ hpiece k hk
  let D : ℝ := (N:ℝ) + |(k:ℝ)|
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hD : 0 < D := by dsimp [D]; positivity
  have hND : (N:ℝ) ≤ D := le_add_of_nonneg_right (abs_nonneg _)
  have hND' : (N:ℝ)/D ≤ 1 := (div_le_one hD).mpr hND
  have hk' : (k:ℝ) ≤ 0 ∨ (N:ℝ) ≤ (k:ℝ) := by
    rcases hk with h | h
    · exact Or.inl (by exact_mod_cast h.le)
    · exact Or.inr (by exact_mod_cast h)
  let v (t : ℝ) := c * (((N:ℝ)*P t-k)/D : ℝ)
  let V (i : ℕ) (p : ℕ → ℝ → ℝ) (t : ℝ) := c * (((N:ℝ)*p i t)/D : ℝ)
  let g (t : ℝ) := B (t : UnitAddCircle) * (fourier (-k) (t : UnitAddCircle) : ℂ)
  let L (t : ℝ) := g t / v t / (D : ℂ)
  have hg : Continuous g := by
    dsimp only [g]
    simp_rw [unit_fourier_eq_exp]
    exact (B.continuous.comp (AddCircle.continuous_mk' (1:ℝ))).mul (by fun_prop)
  have hL : L (s m) = L (s 0) := by
    rw [hs₁,hs₀]
    have hcircle : ((1:ℝ) : UnitAddCircle) = ((0:ℝ) : UnitAddCircle) := by
      rw [AddCircle.coe_period, AddCircle.coe_zero]
    simp only [L,g,v,hcircle,hP]
  have hsum (i) (hi : i < m) :
      ‖(∫ t in s i..s (i+1), g t) - (L (s (i+1)) - L (s i))‖ ≤
        (2*U+W)/D^2 := by
    let J := Icc (s i) (s (i+1))
    have hab : s i ≤ s (i+1) := hs (Nat.le_succ _)
    obtain ⟨hp₂, hf₂, hp⟩ := hpiece i hi
    let E (t : ℝ) := Complex.exp (c * ((N:ℝ)*φ i t-k*t : ℝ))
    have hE (t) (ht : t ∈ J) :
        HasDerivWithinAt E ((D : ℂ)*v t*E t) J t := by
      have hf := (((hp t ht).1.const_mul (N:ℝ)).sub
        ((hasDerivWithinAt_id t J).const_mul (k:ℝ)))
      have he := (hf.ofReal_comp.const_mul c).cexp
      refine he.congr_deriv ?_
      dsimp [v,E]
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr hD.ne']
    have hv (t) (ht : t ∈ J) : HasDerivWithinAt v (V i p₁ t) J t := by
      simpa only [v, V] using
        (((((hp t ht).2.1.const_mul (N:ℝ)).sub_const (k:ℝ)).div_const D).ofReal_comp.const_mul c)
    have hv₁ (t) (ht : t ∈ J) : HasDerivWithinAt (V i p₁) (V i p₂ t) J t := by
      simpa only [V] using
        (((((hp t ht).2.2.1.const_mul (N:ℝ)).div_const D).ofReal_comp.const_mul c))
    have hV₂ : ContinuousOn (V i p₂) J :=
      continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn
        ((continuousOn_const.mul hp₂).div_const D))
    have hVbound {u : ℕ → ℝ → ℝ} {t : ℝ} (hu : |u i t| ≤ M) : ‖V i u t‖ ≤ A := by
      simp only [V, norm_mul, hc, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul,
        abs_of_pos hD, abs_of_pos hNr]
      have hh : ((N:ℝ)*|u i t|)/D ≤ M := by
        rw [show ((N:ℝ)*|u i t|)/D = (N:ℝ)/D*|u i t| by ring]
        exact (mul_le_mul_of_nonneg_left hu (by positivity)).trans
          (by simpa using mul_le_mul_of_nonneg_right hND' hM)
      dsimp [A]
      nlinarith [mul_le_mul_of_nonneg_left hh Real.pi_pos.le]
    have hbound (t) (ht : t ∈ J) :
        ‖f i t‖ ≤ A ∧ ‖f₁ i t‖ ≤ A ∧ ‖f₂ i t‖ ≤ A ∧
        r ≤ ‖v t‖ ∧ ‖V i p₁ t‖ ≤ A ∧ ‖V i p₂ t‖ ≤ A ∧ ‖E t‖ = 1 := by
      obtain ⟨_,_,_,_,_,hp0,hp1,h1,h2,h3,h4,h5,_⟩ := hp t ht
      refine ⟨h3.trans hAM, h4.trans hAM,h5.trans hAM,?_,hVbound h1,hVbound h2,?_⟩
      · simp only [v, norm_mul,hc,Complex.norm_real,Real.norm_eq_abs,abs_div,abs_of_pos hD]
        have hh := (le_div_iff₀ hD).2 (exterior_phase_gap hNr hd hp0 hp1 hk')
        dsimp [r]
        nlinarith [mul_le_mul_of_nonneg_left hh Real.pi_pos.le]
      · dsimp only [E]
        rw [show c * ((N:ℝ)*φ i t-k*t : ℝ) =
          ((2 * Real.pi * ((N:ℝ)*φ i t-k*t) : ℝ) : ℂ) * Complex.I by
          dsimp [c]; push_cast; ring]
        exact Complex.norm_exp_ofReal_mul_I _
    have hEq (t) (ht : t ∈ J) : f i t * E t = g t := by
      rw [show g t = B (t : UnitAddCircle) * (fourier (-k) (t : UnitAddCircle) : ℂ) by rfl,
        (hp t ht).2.2.2.2.2.2.2.2.2.2.2.2, unit_fourier_eq_exp, mul_assoc, ← Complex.exp_add]
      apply congrArg (fun z : ℂ ↦ f i t * z)
      dsimp only [E,c]
      apply congrArg Complex.exp
      push_cast
      ring
    have hh := oscillatory_piece hab hD (fun t ht ↦ (hp t ht).2.2.2.1)
      (fun t ht ↦ (hp t ht).2.2.2.2.1) hf₂ hv hv₁ hV₂ hE hA hr hbound
    rw [intervalIntegral.integral_congr (fun t ht ↦ hEq t (by simpa only [J, uIcc_of_le hab] using ht)),
      hEq _ ⟨hab,le_rfl⟩, hEq _ ⟨le_rfl,hab⟩] at hh
    rw [show L (s (i+1)) - L (s i) =
      (g (s (i+1)) / v (s (i+1)) - g (s i) / v (s i)) / (D : ℂ) by simp [L,sub_div] ]
    refine hh.trans (div_le_div_of_nonneg_right ?_ (by positivity))
    change 2*U+(s (i+1)-s i)*W ≤ 2*U+W
    have hh0 : 0 ≤ s i := by rw [← hs₀]; exact hs (Nat.zero_le i)
    have hh1 : s (i+1) ≤ 1 := by rw [← hs₁]; exact hs (Nat.succ_le_of_lt hi)
    nlinarith [mul_le_mul_of_nonneg_right (show s (i+1)-s i ≤ 1 by linarith) hW]
  have hcoeff : fourierCoeff B k = ∫ t in (0:ℝ)..1, g t := by
    rw [fourierCoeff_eq_intervalIntegral _ _ (0:ℝ)]
    simp only [one_div_one,zero_add,one_smul,smul_eq_mul]
    exact intervalIntegral.integral_congr (fun t _ ↦ mul_comm _ _)
  have htot : (∑ i ∈ Finset.range m,
      ((∫ t in s i..s (i+1), g t) - (L (s (i+1))-L (s i)))) = fourierCoeff B k := by
    have htel : (∑ i ∈ Finset.range m, (L (s (i+1)) - L (s i))) = L (s m) - L (s 0) :=
      Finset.sum_range_sub (L ∘ s) m
    rw [Finset.sum_sub_distrib, htel,
      intervalIntegral.sum_integral_adjacent_intervals (fun i _ ↦ hg.intervalIntegrable _ _),
      hL, sub_self, sub_zero, hs₀, hs₁, hcoeff]
  rw [← htot]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ i ∈ Finset.range m, (2*U+W)/D^2 :=
      Finset.sum_le_sum (fun i hi ↦ hsum i (Finset.mem_range.mp hi))
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul, mul_div_assoc, D]

lemma inverse_square_majorant (N : ℕ) (hN : 0 < N) :
    Summable (fun k : ℤ ↦ 1 / ((N:ℝ) + |(k:ℝ)|)^2) ∧
    (∑' k : ℤ, 1 / ((N:ℝ) + |(k:ℝ)|)^2) ≤ 4 / (N : ℝ) := by
  let u (k : ℕ) : ℝ := 1 / ((N:ℝ) + k)^2
  let v (k : ℕ) : ℝ := 2 / ((N:ℝ) + k)
  have hN' : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hu (k : ℕ) : u k ≤ v k-v (k+1) := by
    let x : ℝ := (N:ℝ) + k
    have hx : 1 ≤ x := le_trans hN' (le_add_of_nonneg_right (Nat.cast_nonneg _))
    have hxx : 0 < x := by linarith
    have hxx' : 0 < x+1 := by linarith
    change 1/x^2 ≤ 2/x-2/((N:ℝ)+((k+1:ℕ):ℝ))
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc]
    have he : 2/x-2/(x+1) = 2/(x*(x+1)) := by field_simp; ring
    change 1/x^2 ≤ 2/x-2/(x+1)
    rw [he]
    apply (div_le_div_iff₀ (sq_pos_of_pos hxx) (mul_pos hxx hxx')).2
    nlinarith [mul_nonneg hxx.le (sub_nonneg.mpr hx)]
  have hsu (n : ℕ) : ∑ k ∈ Finset.range n, u k ≤ 2/N := by
    apply (Finset.sum_le_sum (fun k (_ : k ∈ Finset.range n) ↦ hu k)).trans
    have ht := Finset.sum_range_sub v n
    rw [Finset.sum_sub_distrib] at ht ⊢
    have hv0 : v 0 = 2/(N:ℝ) := by simp [v]
    have hvn : 0 ≤ v n := by dsimp [v]; positivity
    linarith
  have hu0 (k) : 0 ≤ u k := by dsimp [u]; positivity
  have hsu' := summable_of_sum_range_le hu0 hsu
  have htail (n : ℕ) : 1 / ((N:ℝ) + |((-(n+1):ℤ):ℝ)|)^2 ≤ u n := by
    push_cast
    rw [abs_neg, abs_of_nonneg (by positivity : 0 ≤ (n:ℝ)+1)]
    apply div_le_div_of_nonneg_left zero_le_one (by positivity)
    gcongr
    linarith
  let w (k : ℤ) := 1 / ((N:ℝ) + |(k:ℝ)|)^2
  have hpos : (fun n : ℕ ↦ w n) = u := by
    funext n
    simp [w,u,abs_of_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hw₁ : Summable (fun n : ℕ ↦ w n) := hpos.symm ▸ hsu'
  have hw₂ : Summable (fun n : ℕ ↦ w (-(n+1))) :=
    Summable.of_nonneg_of_le (fun _ ↦ by dsimp [w]; positivity) htail hsu'
  refine ⟨hw₁.of_nat_of_neg_add_one hw₂, ?_⟩
  change (∑' k : ℤ, w k) ≤ _
  rw [tsum_of_nat_of_neg_add_one hw₁ hw₂, hpos]
  have hs₁ := Real.tsum_le_of_sum_range_le hu0 hsu
  have hs₂ : (∑' n : ℕ, w (-(n+1))) ≤ (∑' n : ℕ, u n) :=
    hw₂.tsum_le_tsum htail hsu'
  calc
    _ ≤ 2/(N:ℝ) + 2/(N:ℝ) := add_le_add hs₁ (hs₂.trans hs₁)
    _ = _ := by ring

open scoped ComplexConjugate ExponentialSum

lemma unit_fourier_eq_addChar (k : ℤ) (t : ℝ) :
    (fourier k (t : UnitAddCircle) : ℂ) = e (k*t) := by
  rw [unit_fourier_eq_exp]
  change Complex.exp _ = Complex.exp ((2 * Real.pi * ((k:ℝ)*t) : ℝ) * Complex.I)
  congr 1
  push_cast
  ring

lemma real_coeff_of_reflection {B : C(UnitAddCircle, ℂ)}
    (hB : ∀ x, B (-x) = conj (B x)) (k : ℤ) :
    (fourierCoeff B k).im = 0 := by
  let J (x : UnitAddCircle) : ℂ := fourier (-k) x * B x
  have hJ (x) : J (-x) = conj (J x) := by
    simp only [J,hB,map_mul]
    congr 1
    rw [← fourier_neg]
    simp only [fourier_apply, smul_neg, neg_smul, neg_neg]
  have hc : conj (fourierCoeff B k) = fourierCoeff B k := by
    change conj (∫ x, J x ∂AddCircle.haarAddCircle) = ∫ x, J x ∂AddCircle.haarAddCircle
    rw [← integral_conj]
    simp_rw [← hJ]
    exact integral_neg_eq_self J AddCircle.haarAddCircle
  have hei := congrArg Complex.im hc
  simp only [Complex.conj_im] at hei
  linarith

lemma wave_spectral_data (h2 : H2) :
    ∃ C₂ δ₀ : ℝ, 0 < C₂ ∧ 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ N₀ : ℕ, ∃ K : ℝ, 0 ≤ K ∧
        ∀ N : ℕ, N₀ ≤ N → ∃ (B : ℝ → ℂ) (b : ℤ → ℝ),
          (∀ t : ℝ, 1 ≤ ‖B t‖ ∧ ‖B t‖ ≤ 1 + C₂ * δ) ∧
          (∀ k : ℕ, k < N → √N * |b k| ≤ 1 + C₂ * √δ) ∧
          Summable (fun k : ℤ ↦ |b k|) ∧
          (∀ t : ℝ, HasSum (fun k : ℤ ↦ (b k : ℂ) * e (k * t)) (B t)) ∧
          (∑' k : {k : ℤ // k < 0 ∨ (N : ℤ) ≤ k}, |b k.val|) ≤ K / N := by
  classical
  obtain ⟨C, δ₀, hC, hδ₀, h⟩ := h2
  refine ⟨C, δ₀, hC, hδ₀, fun δ hδ hδ' ↦ ?_⟩
  obtain ⟨m, d, M, hd, hM, hdata⟩ := h δ ⟨hδ, hδ'⟩
  obtain ⟨K, hK, hdecay⟩ := piecewise_fourier_decay (m := m) hd hM
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hdata
  refine ⟨max 1 N₀, 4*K, by positivity, fun N hN ↦ ?_⟩
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans hN)
  obtain ⟨B, s, P, φ, p₁, p₂, f, f₁, f₂, hs, hs₀, hs₁, hP, hb, hin, hj⟩ :=
    hN₀ N ((le_max_right _ _).trans hN)
  let b (k : ℤ) := (fourierCoeff B k).re
  have hc (k : ℤ) : (b k : ℂ) = fourierCoeff B k := by
    apply Complex.ext
    · exact Complex.ofReal_re _
    · rw [Complex.ofReal_im, real_coeff_of_reflection (fun t ↦ (hb t).1) k]
  have hc' (k : ℤ) : |b k| = ‖fourierCoeff B k‖ := by
    rw [← hc, Complex.norm_real, Real.norm_eq_abs]
  let w (k : ℤ) := K * (1 / ((N:ℝ) + |(k:ℝ)|)^2)
  have hw₀ (k : ℤ) : 0 ≤ w k := by dsimp [w]; positivity
  obtain ⟨hw, hw'⟩ := inverse_square_majorant N hNpos
  have hwS : Summable w := hw.mul_left K
  have hle (k : ℤ) (hk : k < 0 ∨ (N:ℤ) ≤ k) : |b k| ≤ w k := by
    rw [hc']
    simpa only [w, mul_one_div] using
      hdecay hNpos hs hs₀ hs₁ (B := B) (P := P) hP
        (φ := φ) (p₁ := p₁) (p₂ := p₂) (f := f) (f₁ := f₁) (f₂ := f₂) hj k hk
  let S : Finset ℤ := Finset.image Int.ofNat (Finset.range N)
  have hmem (k : ℤ) : k ∉ S ↔ k < 0 ∨ (N:ℤ) ≤ k := by
    simp only [S, Finset.mem_image, Finset.mem_range, not_exists, not_and]
    constructor
    · intro hk
      by_cases hk₀ : 0 ≤ k
      · right
        by_contra hkn
        have ht := Int.toNat_of_nonneg hk₀
        exact hk k.toNat (by omega) ht
      · exact Or.inl (lt_of_not_ge hk₀)
    · intro hk j hj hjk
      change (j : ℤ) = k at hjk
      omega
  have hscompl : Summable (fun k : {k : ℤ // k ∉ S} ↦ |b k.val|) :=
    Summable.of_nonneg_of_le (fun _ ↦ abs_nonneg _) (fun k ↦ hle k ((hmem _).mp k.property))
      (hwS.subtype _)
  have hbS : Summable (fun k : ℤ ↦ |b k|) := S.summable_compl_iff.mp hscompl
  have hcS : Summable (fourierCoeff B) :=
    Summable.of_norm (by simpa only [← hc'] using hbS)
  refine ⟨fun t ↦ B (t : UnitAddCircle), b, fun t ↦ (hb t).2, ?_, hbS, ?_, ?_⟩
  · intro k hk
    rw [hc']
    exact hin k hk
  · intro t
    simpa only [hc, smul_eq_mul, unit_fourier_eq_addChar] using
      has_pointwise_sum_fourier_series_of_summable hcS (t : UnitAddCircle)
  · let T := {k : ℤ // k < 0 ∨ (N:ℤ) ≤ k}
    have hwt : Summable (fun k : T ↦ w k.val) := hwS.subtype _
    have hbt : Summable (fun k : T ↦ |b k.val|) := hbS.subtype _
    calc
      _ ≤ ∑' k : T, w k.val := hbt.tsum_le_tsum (fun k ↦ hle k k.property) hwt
      _ ≤ ∑' k : ℤ, w k := hwt.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
        (fun k _ ↦ hw₀ k) (fun _ ↦ le_rfl) hwS
      _ ≤ (4*K) / N := by
        rw [(hw.hasSum.mul_left K).tsum_eq, mul_comm (4:ℝ) K, mul_div_assoc]
        exact mul_le_mul_of_nonneg_left hw' hK

lemma norm_additiveChar (x : ℝ) : ‖e x‖ = 1 := by
  change ‖Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)‖ = 1
  exact Complex.norm_exp_ofReal_mul_I _

lemma additiveChar_add (x y : ℝ) : e (x + y) = e x * e y := by
  change Complex.exp ((2 * Real.pi * (x + y) : ℝ) * Complex.I) =
    Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I) *
      Complex.exp ((2 * Real.pi * y : ℝ) * Complex.I)
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma additiveChar_mul_conj (x y : ℝ) :
    e x * starRingEnd ℂ (e y) = e (x - y) := by
  change Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I) *
      starRingEnd ℂ (Complex.exp ((2 * Real.pi * y : ℝ) * Complex.I)) =
    Complex.exp ((2 * Real.pi * (x - y) : ℝ) * Complex.I)
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

lemma intervalIntegral_additiveChar_int (n : ℤ) :
    (∫ t in (0 : ℝ)..1, e (n * t)) = if n = 0 then 1 else 0 := by
  split_ifs with hn
  · subst hn
    simp only [Int.cast_zero, zero_mul]
    have he0 : e (0 : ℝ) = 1 := by
      change Complex.exp (((2 * Real.pi * (0 : ℝ) : ℝ) : ℂ) * Complex.I) = 1
      simp
    simp only [he0, intervalIntegral.integral_const, sub_zero, one_smul]
  · let c : ℂ := 2 * Real.pi * (n : ℂ) * Complex.I
    have hc : c ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) (Int.cast_ne_zero.mpr hn)) Complex.I_ne_zero
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun x : ℝ ↦ Complex.exp (c * (x : ℂ)) / c) (e (n * t)) t := by
      intro t _
      have hl : HasDerivAt (fun x : ℝ ↦ c * (x : ℂ)) c t := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c
      have he : HasDerivAt (fun x : ℝ ↦ Complex.exp (c * (x : ℂ)))
          (Complex.exp (c * (t : ℂ)) * c) t := hl.cexp
      have hd : HasDerivAt (fun x : ℝ ↦ Complex.exp (c * (x : ℂ)) / c)
          (Complex.exp (c * (t : ℂ)) * c / c) t := he.div_const c
      rw [mul_div_cancel_right₀ _ hc] at hd
      have h_eq : Complex.exp (c * (t : ℂ)) = e (n * t) := by
        dsimp [c]
        unfold additiveChar
        congr 1
        push_cast
        ring
      rwa [h_eq] at hd
    have hint : IntervalIntegrable (fun t : ℝ ↦ e (n * t)) MeasureTheory.volume 0 1 := by
      apply Continuous.intervalIntegrable
      unfold additiveChar
      fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    have h1 : Complex.exp (c * ((1 : ℝ) : ℂ)) = 1 := by
      rw [show c * ((1 : ℝ) : ℂ) = (n : ℤ) * (2 * Real.pi * Complex.I) by
        dsimp [c]; ring, Complex.exp_int_mul_two_pi_mul_I]
    have h0 : Complex.exp (c * ((0 : ℝ) : ℂ)) = 1 := by simp
    rw [h1, h0, sub_self]

lemma parseval_fin_range (N : ℕ) (X : ℕ → ℝ) :
    (∫ t in (0 : ℝ)..1, ‖∑ k ∈ Finset.range N, (X k : ℂ) * e (k * t)‖ ^ 2) =
      ∑ k ∈ Finset.range N, (X k) ^ 2 := by
  have hcast : ((∫ t in (0 : ℝ)..1,
      ‖∑ k ∈ Finset.range N, (X k : ℂ) * e (k * t)‖ ^ 2 : ℝ) : ℂ) =
      ∫ t in (0 : ℝ)..1, ((‖∑ k ∈ Finset.range N, (X k : ℂ) * e (k * t)‖ ^ 2 : ℝ) : ℂ) :=
    (intervalIntegral.integral_ofReal).symm
  apply Complex.ofReal_injective
  rw [hcast]
  have hnorm (t : ℝ) :
      ((‖∑ k ∈ Finset.range N, (X k : ℂ) * e (k * t)‖ ^ 2 : ℝ) : ℂ) =
      ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
        ((X j * X k : ℝ) : ℂ) * e ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * t) := by
    let S := ∑ k ∈ Finset.range N, (X k : ℂ) * e (k * t)
    have hsq : ((‖S‖ ^ 2 : ℝ) : ℂ) = S * starRingEnd ℂ S := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    rw [hsq]
    dsimp [S]
    simp only [map_sum, map_mul, Complex.conj_ofReal, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    calc
      (X j : ℂ) * e (j * t) * ((X k : ℂ) * starRingEnd ℂ (e (k * t)))
          = ((X j * X k : ℝ) : ℂ) * (e (j * t) * starRingEnd ℂ (e (k * t))) := by
            push_cast; ring
      _ = ((X j * X k : ℝ) : ℂ) * e ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * t) := by
            rw [additiveChar_mul_conj]
            congr 2
            push_cast
            ring
  simp_rw [hnorm]
  rw [intervalIntegral.integral_finsetSum]
  · have hinner (j : ℕ) :
        (∫ t in (0 : ℝ)..1, ∑ k ∈ Finset.range N,
          ((X j * X k : ℝ) : ℂ) * e ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * t)) =
        ∑ k ∈ Finset.range N,
          ((X j * X k : ℝ) : ℂ) * ∫ t in (0 : ℝ)..1, e ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * t) := by
      rw [intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro k _
        exact intervalIntegral.integral_const_mul _ _
      · intro k _
        apply Continuous.intervalIntegrable
        unfold additiveChar
        fun_prop
    simp_rw [hinner, intervalIntegral_additiveChar_int]
    have hdiag (j : ℕ) (hj : j ∈ Finset.range N) :
        (∑ k ∈ Finset.range N,
          ((X j * X k : ℝ) : ℂ) * if (j : ℤ) - (k : ℤ) = 0 then (1 : ℂ) else 0) =
        ((X j ^ 2 : ℝ) : ℂ) := by
      rw [Finset.sum_eq_single j]
      · rw [if_pos (sub_self _), mul_one, pow_two]
      · intro k _ hkj
        have hne : (j : ℤ) - (k : ℤ) ≠ 0 := by omega
        simp [hne]
      · intro hnj
        exact (hnj hj).elim
    rw [Finset.sum_congr rfl (fun j hj ↦ hdiag j hj)]
    push_cast
    rfl
  · intro j _
    apply Continuous.intervalIntegrable
    apply continuous_finsetSum
    intro k _
    unfold additiveChar
    fun_prop

lemma entropy_monotone_bound {q N μ : ℝ} (hq0 : 0 < q) (hq : q ≤ 1 / 2)
    (hN : 0 < N) (hμ0 : 0 ≤ μ) (hμb : μ ≤ q * N) :
    μ * Real.log (80 * N / μ) ≤ q * N * Real.log (80 / q) := by
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this
    exact this
  have hL : 1 ≤ Real.log (80 / q) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 4)
      (show 4 ≤ 80 / q by apply (le_div_iff₀ hq0).mpr; linarith)
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at hh
    norm_num at hh
    linarith
  by_cases hz : μ = 0
  · rw [hz, zero_mul]
    positivity
  have hμp : 0 < μ := lt_of_le_of_ne hμ0 (Ne.symm hz)
  have hsplit : Real.log (80 * N / μ) = Real.log (80 / q) + Real.log (q * N / μ) := by
    rw [← Real.log_mul (by positivity : 80 / q ≠ 0) (by positivity : q * N / μ ≠ 0)]
    congr 1
    field_simp
  have hs : μ * Real.log (q * N / μ) ≤ q * N - μ := by
    calc
      μ * Real.log (q * N / μ) ≤ μ * (q * N / μ - 1) :=
        mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (by positivity)) hμ0
      _ = q * N - μ := by field_simp
  have hm := mul_le_mul_of_nonneg_right hμb (sub_nonneg.mpr hL)
  rw [hsplit, mul_add]
  nlinarith

lemma small_delta_budget {C_round C₂ δ₀ : ℝ}
    (_hCr : 0 < C_round) (hC₂ : 0 < C₂) (hδ₀ : 0 < δ₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < δ₀ ∧ δ < 1 / 100 ∧
      let S := 1 + C₂ * √δ
      let q := (1 - S⁻¹ ^ 2) / 2 + δ
      let E := C_round * √(q * Real.log (80 / q))
      0 < q ∧ q ≤ 1 / 2 ∧
      (1 + C₂ * δ) / S + E < 1 + ε ∧
      1 - ε < S⁻¹ - E := by
  let S (x : ℝ) : ℝ := 1 + C₂ * √x
  let q (x : ℝ) : ℝ := (1 - (S x)⁻¹ ^ 2) / 2 + x
  let G (x : ℝ) : ℝ := C_round * √(q x * Real.log 80 - q x * Real.log (q x))
  let U (x : ℝ) : ℝ := (1 + C₂ * x) / S x + G x
  let L (x : ℝ) : ℝ := (S x)⁻¹ - G x
  have hS_cont : ContinuousAt S 0 := by
    dsimp [S]
    exact continuousAt_const.add (continuousAt_const.mul Real.continuous_sqrt.continuousAt)
  have hS0 : S 0 = 1 := by simp [S]
  have hq_cont : ContinuousAt q 0 := by
    dsimp [q]
    have hinv : ContinuousAt (fun x ↦ (S x)⁻¹) 0 := hS_cont.inv₀ (by rw [hS0]; norm_num)
    exact ((continuousAt_const.sub (hinv.pow 2)).div_const 2).add continuousAt_id
  have hq0 : q 0 = 0 := by norm_num [q, S]
  have hG_cont : ContinuousAt G 0 := by
    dsimp [G]
    have harg : ContinuousAt (fun y : ℝ ↦ y * Real.log 80 - y * Real.log y) (q 0) := by
      rw [hq0]
      exact (continuousAt_id.mul continuousAt_const).sub Real.continuous_mul_log.continuousAt
    have hcomp : ContinuousAt (fun x : ℝ ↦ q x * Real.log 80 - q x * Real.log (q x)) 0 :=
      ContinuousAt.comp harg hq_cont
    exact continuousAt_const.mul (Real.continuous_sqrt.continuousAt.comp hcomp)
  have hG0 : G 0 = 0 := by simp [G, hq0]
  have hU_cont : ContinuousAt U 0 :=
    ((continuousAt_const.add (continuousAt_const.mul continuousAt_id)).div hS_cont
      (by rw [hS0]; norm_num)).add hG_cont
  have hL_cont : ContinuousAt L 0 :=
    (hS_cont.inv₀ (by rw [hS0]; norm_num)).sub hG_cont
  have hU0 : U 0 = 1 := by simp [U, hS0, hG0]
  have hL0 : L 0 = 1 := by simp [L, hS0, hG0]
  have hev : ∀ᶠ x : ℝ in 𝓝 0, q x < 1 / 2 ∧ U x < 1 + ε ∧ 1 - ε < L x := by
    exact (hq_cont.eventually (gt_mem_nhds (by rw [hq0]; norm_num : q 0 < 1 / 2))).and
      ((hU_cont.eventually (gt_mem_nhds (by rw [hU0]; linarith))).and
        (hL_cont.eventually (lt_mem_nhds (by rw [hL0]; linarith))))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
  let δ := min (r / 2) (min (δ₀ / 2) (1 / 200))
  have hδ : 0 < δ := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hδr : δ < r := (min_le_left _ _).trans_lt (by linarith)
  have hδ_lt_δ₀ : δ < δ₀ := (min_le_right _ _).trans_lt ((min_le_left _ _).trans_lt (by linarith))
  have hδ_100 : δ < 1 / 100 := (min_le_right _ _).trans_lt ((min_le_right _ _).trans_lt (by norm_num))
  have hd : dist δ (0 : ℝ) < r := by
    simpa [Real.dist_eq, abs_of_pos hδ] using hδr
  obtain ⟨hq_half, hU_lt, hL_gt⟩ := hball hd
  have hS1 : 1 < S δ := by
    dsimp [S]
    have : 0 < C₂ * √δ := mul_pos hC₂ (Real.sqrt_pos.mpr hδ)
    linarith
  have hq_pos : 0 < q δ := by
    dsimp [q]
    have hinv1 : (S δ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hS1
    have hinv0 : 0 ≤ (S δ)⁻¹ := (inv_pos.mpr (by linarith)).le
    have hsq : (S δ)⁻¹ ^ 2 < 1 := by nlinarith
    linarith
  have hG_eq : G δ = C_round * √(q δ * Real.log (80 / q δ)) := by
    dsimp [G]
    rw [Real.log_div (by norm_num : (80 : ℝ) ≠ 0) hq_pos.ne', mul_sub]
  refine ⟨δ, hδ, hδ_lt_δ₀, hδ_100, hq_pos, hq_half.le, ?_, ?_⟩
  · simpa only [U, S, q, hG_eq] using hU_lt
  · simpa only [L, S, q, hG_eq] using hL_gt

lemma project_and_round (h1 : H1)
    (hWave : ∃ C₂ δ₀ : ℝ, 0 < C₂ ∧ 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ N₀ : ℕ, ∃ K : ℝ, 0 ≤ K ∧
        ∀ N : ℕ, N₀ ≤ N → ∃ (B : ℝ → ℂ) (b : ℤ → ℝ),
          (∀ t : ℝ, 1 ≤ ‖B t‖ ∧ ‖B t‖ ≤ 1 + C₂ * δ) ∧
          (∀ k : ℕ, k < N → √N * |b k| ≤ 1 + C₂ * √δ) ∧
          Summable (fun k : ℤ ↦ |b k|) ∧
          (∀ t : ℝ, HasSum (fun k : ℤ ↦ (b k : ℂ) * e (k * t)) (B t)) ∧
          (∑' k : {k : ℤ // k < 0 ∨ (N : ℤ) ≤ k}, |b k.val|) ≤ K / N) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∃ f : ℕ → ℤ, Green84.IsSignOn N f ∧
      ∀ t : ℝ, |‖Green84.fourierSum N f t‖ - √N| ≤ ε * √N := by
  intro ε hε
  obtain ⟨C_round, hCr, hround⟩ := h1
  obtain ⟨C₂, δ₀, hC₂, hδ₀, hwave⟩ := hWave
  obtain ⟨δ, hδ, hδ_lt_δ₀, _, hq_pos, hq_half, hU_lt, hL_gt⟩ :=
    small_delta_budget hCr hC₂ hδ₀ hε
  let S : ℝ := 1 + C₂ * √δ
  let q : ℝ := (1 - S⁻¹ ^ 2) / 2 + δ
  let E : ℝ := C_round * √(q * Real.log (80 / q))
  have hS : 1 ≤ S := by
    dsimp [S]
    nlinarith [mul_nonneg hC₂.le (Real.sqrt_nonneg δ)]
  have hS_pos : 0 < S := by linarith
  obtain ⟨N₀, K, hK0, hB⟩ := hwave δ hδ hδ_lt_δ₀
  have hinvN : Tendsto (fun N : ℕ ↦ K / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat K
  have hsqrtN : Tendsto (fun N : ℕ ↦ 1 / √(N : ℝ)) atTop (𝓝 0) := by
    exact (tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)).congr
      (fun N ↦ (one_div _).symm)
  have hrem_tend : Tendsto (fun N : ℕ ↦ (K / (N : ℝ)) / S + C_round * (1 / √(N : ℝ)))
      atTop (𝓝 0) := by
    simpa using (hinvN.div_const S).add (hsqrtN.const_mul C_round)
  have hq_lim : Tendsto (fun N : ℕ ↦ (1 - ((1 - K / (N : ℝ)) / S) ^ 2) / 2)
      atTop (𝓝 ((1 - S⁻¹ ^ 2) / 2)) := by
    have h1N : Tendsto (fun N : ℕ ↦ (1 - K / (N : ℝ)) / S) atTop (𝓝 (S⁻¹)) := by
      have ht := ((tendsto_const_nhds (x := (1 : ℝ))).sub hinvN).div_const S
      simpa only [sub_zero, one_div] using ht
    exact ((tendsto_const_nhds.sub (h1N.pow 2)).div_const 2)
  have hmargin : 0 < min (1 + ε - ((1 + C₂ * δ) / S + E)) (S⁻¹ - E - (1 - ε)) :=
    lt_min (sub_pos.mpr hU_lt) (sub_pos.mpr hL_gt)
  have hq_gap : (1 - S⁻¹ ^ 2) / 2 < q := by dsimp [q]; linarith
  filter_upwards [eventually_ge_atTop (max N₀ 1),
    hinvN.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    hq_lim.eventually (gt_mem_nhds hq_gap),
    hrem_tend.eventually (gt_mem_nhds hmargin)] with N hN_ge hK_half hq_ev hrem_ev
  have hN0 : N₀ ≤ N := (le_max_left _ _).trans hN_ge
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN_ge
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNs : 0 < √(N : ℝ) := Real.sqrt_pos.mpr hNr
  obtain ⟨B, b, hB_mod, hb_coef, hb_sum, hB_has, hb_tail⟩ := hB N hN0
  let P (t : ℝ) : ℂ := ∑ k ∈ Finset.range N, (b (k : ℤ) : ℂ) * e ((k : ℝ) * t)
  have hB_sub_P (t : ℝ) : ‖B t - P t‖ ≤ K / N := by
    let s : Finset ℤ := Finset.image Int.ofNat (Finset.range N)
    have hmem_s (k : ℤ) : k ∉ s ↔ k < 0 ∨ (N : ℤ) ≤ k := by
      simp only [s, Finset.mem_image, Finset.mem_range, not_exists, not_and]
      constructor
      · intro hk
        by_cases hk0 : 0 ≤ k
        · right
          by_contra hlt
          have hkt : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk0
          exact hk k.toNat (by omega) hkt
        · left
          omega
      · intro hk m hm hm_eq
        change (m : ℤ) = k at hm_eq
        omega
    have hsum_t : Summable (fun k : ℤ ↦ (b k : ℂ) * e (k * t)) := by
      apply Summable.of_norm
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_additiveChar, mul_one]
        using hb_sum
    have hsplit := hsum_t.sum_add_tsum_compl (s := s)
    rw [(hB_has t).tsum_eq] at hsplit
    have hs_eq : ∑ k ∈ s, (b k : ℂ) * e (k * t) = P t := by
      dsimp [s, P]
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro k _
        simp
      · intro x _ y _ hxy
        exact Int.ofNat.inj hxy
    rw [hs_eq] at hsplit
    have hdiff : B t - P t = ∑' k : {k : ℤ // k ∉ s}, (b k.val : ℂ) * e (k.val * t) := by
      have h1 : B t - P t = ∑' x : ↑(↑s : Set ℤ)ᶜ, (b x.val : ℂ) * e ((x.val : ℝ) * t) := by
        rw [← hsplit]
        ring
      exact h1
    rw [hdiff]
    have hcompl_sum : Summable (fun k : {k : ℤ // k ∉ s} ↦ |b k.val|) :=
      hb_sum.subtype _
    have hnorm_sum : Summable (fun k : {k : ℤ // k ∉ s} ↦ ‖(b k.val : ℂ) * e (k.val * t)‖) := by
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_additiveChar, mul_one]
        using hcompl_sum
    have hle := norm_tsum_le_tsum_norm hnorm_sum
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_additiveChar, mul_one] at hle
    let heqv : {k : ℤ // k ∉ s} ≃ {k : ℤ // k < 0 ∨ (N : ℤ) ≤ k} :=
      Equiv.subtypeEquivRight hmem_s
    have htsum_eq : (∑' k : {k : ℤ // k ∉ s}, |b k.val|) =
        ∑' k : {k : ℤ // k < 0 ∨ (N : ℤ) ≤ k}, |b k.val| :=
      Equiv.tsum_eq heqv (fun k : {k : ℤ // k < 0 ∨ (N : ℤ) ≤ k} ↦ |b k.val|)
    exact hle.trans (htsum_eq ▸ hb_tail)
  let X (k : ℕ) : ℝ := if k < N then √(N : ℝ) / S * b k else 0
  have hX_le (k : ℕ) (hk : k < N) : |X k| ≤ 1 := by
    simp only [X, hk, ↓reduceIte, abs_mul, abs_div, abs_of_pos hNs, abs_of_pos hS_pos]
    rw [div_mul_eq_mul_div]
    exact (div_le_one hS_pos).mpr (hb_coef k hk)
  let UX (t : ℝ) : ℂ := ∑ k ∈ Finset.range N, (X k : ℂ) * e (k * t)
  have hUX_eq (t : ℝ) : UX t = (√(N : ℝ) / S : ℂ) * P t := by
    dsimp [UX, P]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < N := Finset.mem_range.mp hk
    simp only [X, hk', ↓reduceIte]
    push_cast
    ring
  have hUX_bounds (t : ℝ) :
      √(N : ℝ) * ((1 - K / N) / S) ≤ ‖UX t‖ ∧
        ‖UX t‖ ≤ √(N : ℝ) * ((1 + C₂ * δ + K / N) / S) := by
    rw [hUX_eq, norm_mul, Complex.norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hNs, abs_of_pos hS_pos]
    have hP_lo : 1 - K / N ≤ ‖P t‖ := by
      have := norm_sub_norm_le (B t) (P t)
      have h1 := (hB_mod t).1
      have h2 := hB_sub_P t
      linarith
    have hP_hi : ‖P t‖ ≤ 1 + C₂ * δ + K / N := by
      have := norm_sub_norm_le (P t) (B t)
      rw [norm_sub_rev] at this
      have h1 := (hB_mod t).2
      have h2 := hB_sub_P t
      linarith
    constructor
    · calc
        √(N : ℝ) * ((1 - K / N) / S) = (√(N : ℝ) / S) * (1 - K / N) := by ring
        _ ≤ (√(N : ℝ) / S) * ‖P t‖ :=
          mul_le_mul_of_nonneg_left hP_lo (div_nonneg hNs.le hS_pos.le)
    · calc
        (√(N : ℝ) / S) * ‖P t‖ ≤ (√(N : ℝ) / S) * (1 + C₂ * δ + K / N) :=
          mul_le_mul_of_nonneg_left hP_hi (div_nonneg hNs.le hS_pos.le)
        _ = √(N : ℝ) * ((1 + C₂ * δ + K / N) / S) := by ring
  have hParseval : (N : ℝ) * ((1 - K / N) / S) ^ 2 ≤ ∑ k ∈ Finset.range N, (X k) ^ 2 := by
    rw [← parseval_fin_range N X]
    have hint : IntervalIntegrable (fun t : ℝ ↦ ‖UX t‖ ^ 2) MeasureTheory.volume 0 1 := by
      apply Continuous.intervalIntegrable
      have hcont : Continuous UX := by
        apply continuous_finsetSum
        intro k _
        unfold additiveChar
        fun_prop
      exact hcont.norm.pow 2
    have hconst : (N : ℝ) * ((1 - K / N) / S) ^ 2 =
        ∫ _t in (0 : ℝ)..1, (N : ℝ) * ((1 - K / N) / S) ^ 2 := by
      simp
    rw [hconst]
    apply intervalIntegral.integral_mono_on (by norm_num) intervalIntegrable_const hint
    intro t _
    have hlo := (hUX_bounds t).1
    have hpos_lo : 0 ≤ √(N : ℝ) * ((1 - K / N) / S) :=
      mul_nonneg hNs.le (div_nonneg (by linarith) hS_pos.le)
    have hsq := sq_le_sq₀ hpos_lo (norm_nonneg _) |>.mpr hlo
    rw [mul_pow, Real.sq_sqrt hNr.le] at hsq
    exact hsq
  let μ : ℝ := (∑ k ∈ Finset.range N, (1 - |X k|)) / 2
  have hμ0 : 0 ≤ μ := div_nonneg (Finset.sum_nonneg fun k hk ↦
    sub_nonneg.mpr (hX_le k (Finset.mem_range.mp hk))) (by norm_num)
  have hμ_le : μ ≤ q * N := by
    have hsum_le : (∑ k ∈ Finset.range N, (1 - |X k|)) ≤
        ∑ k ∈ Finset.range N, (1 - (X k) ^ 2) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' := hX_le k (Finset.mem_range.mp hk)
      have hh := mul_nonneg (abs_nonneg (X k)) (sub_nonneg.mpr hk')
      nlinarith only [hh, sq_abs (X k)]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      at hsum_le
    have hμ_eq : μ = ((N : ℝ) - ∑ k ∈ Finset.range N, |X k|) / 2 := by
      dsimp [μ]
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have hμ_energy : μ ≤ (N : ℝ) * ((1 - ((1 - K / N) / S) ^ 2) / 2) := by
      nlinarith only [hμ_eq, hsum_le, hParseval]
    exact hμ_energy.trans (by
      rw [mul_comm (N : ℝ) ((1 - ((1 - K / N) / S) ^ 2) / 2)]
      exact mul_le_mul_of_nonneg_right hq_ev.le hNr.le)
  have hentr := entropy_monotone_bound hq_pos hq_half hNr hμ0 hμ_le
  obtain ⟨ε_seq, hε_seq, hε_round⟩ := hround N hN1 X hX_le
  let f : ℕ → ℤ := fun n ↦ if n = 0 then 1 else ε_seq (n - 1)
  refine ⟨f, ?_, ?_⟩
  · intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : n ≠ 0 := by omega
    have hn1 : n - 1 < N := by omega
    simpa [f, hn0] using hε_seq (n - 1) hn1
  · intro θ
    have hfourier : Green84.fourierSum N f θ =
        e θ * ∑ k ∈ Finset.range N, (ε_seq k : ℂ) * e (k * θ) := by
      dsimp [Green84.fourierSum]
      rw [Finset.mul_sum]
      have hbi : ∑ n ∈ Finset.Icc 1 N, (f n : ℂ) * e ((n : ℝ) * θ) =
          ∑ k ∈ Finset.range N, (f (k + 1) : ℂ) * e (((k + 1 : ℕ) : ℝ) * θ) := by
        refine Finset.sum_bij (fun n _ ↦ n - 1) ?_ ?_ ?_ ?_
        · intro n hn
          rw [Finset.mem_Icc] at hn
          rw [Finset.mem_range]
          omega
        · intro n₁ hn₁ n₂ hn₂ h
          rw [Finset.mem_Icc] at hn₁ hn₂
          omega
        · intro k hk
          rw [Finset.mem_range] at hk
          refine ⟨k + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
        · intro n hn
          rw [Finset.mem_Icc] at hn
          have h1 : n - 1 + 1 = n := by omega
          rw [h1]
      rw [hbi]
      apply Finset.sum_congr rfl
      intro k _
      have hk0 : k + 1 ≠ 0 := Nat.succ_ne_zero k
      simp only [f, hk0, ↓reduceIte, Nat.add_sub_cancel]
      have hadd : e (((k + 1 : ℕ) : ℝ) * θ) = e θ * e ((k : ℝ) * θ) := by
        rw [← additiveChar_add]
        congr 1
        push_cast
        ring
      rw [hadd]
      ring
    have hnorm_eq : ‖Green84.fourierSum N f θ‖ =
        ‖∑ k ∈ Finset.range N, (ε_seq k : ℂ) * e (k * θ)‖ := by
      rw [hfourier, norm_mul, norm_additiveChar, one_mul]
    have hround_err : ‖(∑ k ∈ Finset.range N, (ε_seq k : ℂ) * e (k * θ)) - UX θ‖ ≤
        C_round + E * √(N : ℝ) := by
      have hsub : (∑ k ∈ Finset.range N, (ε_seq k : ℂ) * e (k * θ)) - UX θ =
          ∑ k ∈ Finset.range N, ((ε_seq k : ℂ) - (X k : ℂ)) * e (k * θ) := by
        dsimp [UX]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
      rw [hsub]
      refine (hε_round θ).trans ?_
      have hsqrt_le : √(μ * Real.log (80 * (N : ℝ) / μ)) ≤ √(q * Real.log (80 / q)) * √(N : ℝ) := by
        apply (Real.sqrt_le_left (by positivity)).mpr
        rw [mul_pow, Real.sq_sqrt (mul_nonneg hq_pos.le
          (Real.log_nonneg ((le_div_iff₀ hq_pos).mpr (by linarith)))), Real.sq_sqrt hNr.le]
        nlinarith only [hentr]
      have hstep : C_round * (1 + √(μ * Real.log (80 * (N : ℝ) / μ))) ≤
          C_round + E * √(N : ℝ) := by
        have h1 := mul_le_mul_of_nonneg_left
          (by linarith only [hsqrt_le] :
            1 + √(μ * Real.log (80 * (N : ℝ) / μ)) ≤ 1 + √(q * Real.log (80 / q)) * √(N : ℝ))
          hCr.le
        calc
          C_round * (1 + √(μ * Real.log (80 * (N : ℝ) / μ)))
              ≤ C_round * (1 + √(q * Real.log (80 / q)) * √(N : ℝ)) := h1
          _ = C_round + E * √(N : ℝ) := by dsimp [E]; ring
      exact hstep
    have htri1 : ‖Green84.fourierSum N f θ‖ - ‖UX θ‖ ≤ C_round + E * √(N : ℝ) := by
      rw [hnorm_eq]
      exact (norm_sub_norm_le _ _).trans hround_err
    have htri2 : ‖UX θ‖ - ‖Green84.fourierSum N f θ‖ ≤ C_round + E * √(N : ℝ) := by
      rw [hnorm_eq]
      exact ((norm_sub_norm_le _ _).trans (by rw [norm_sub_rev]; exact hround_err))
    have hUX_b := hUX_bounds θ
    have hup_rem : (K / (N : ℝ)) / S + C_round * (1 / √(N : ℝ)) <
        1 + ε - ((1 + C₂ * δ) / S + E) :=
      lt_of_lt_of_le hrem_ev (min_le_left _ _)
    have hlo_rem : (K / (N : ℝ)) / S + C_round * (1 / √(N : ℝ)) <
        S⁻¹ - E - (1 - ε) :=
      lt_of_lt_of_le hrem_ev (min_le_right _ _)
    have hCeq : C_round = (C_round * (1 / √(N : ℝ))) * √(N : ℝ) := by
      field_simp
    have hup : ‖Green84.fourierSum N f θ‖ - √(N : ℝ) ≤ ε * √(N : ℝ) := by
      have h1' : ‖Green84.fourierSum N f θ‖ ≤
          ((1 + C₂ * δ) / S + E + (K / (N : ℝ)) / S + C_round * (1 / √(N : ℝ))) * √(N : ℝ) := by
        have hstep1 : ‖Green84.fourierSum N f θ‖ ≤ ‖UX θ‖ + (C_round + E * √(N : ℝ)) := by
          linarith only [htri1]
        have hstep2 : ‖UX θ‖ + (C_round + E * √(N : ℝ)) ≤
            √(N : ℝ) * ((1 + C₂ * δ + K / (N : ℝ)) / S) +
              ((C_round * (1 / √(N : ℝ))) * √(N : ℝ) + E * √(N : ℝ)) := by
          rw [← hCeq]
          linarith only [hUX_b.2]
        have hstep3 : √(N : ℝ) * ((1 + C₂ * δ + K / (N : ℝ)) / S) +
              ((C_round * (1 / √(N : ℝ))) * √(N : ℝ) + E * √(N : ℝ)) =
            ((1 + C₂ * δ) / S + E + (K / (N : ℝ)) / S + C_round * (1 / √(N : ℝ))) * √(N : ℝ) := by
          ring
        linarith only [hstep1, hstep2, hstep3]
      have h2' : ((1 + C₂ * δ) / S + E + (K / (N : ℝ)) / S + C_round * (1 / √(N : ℝ))) * √(N : ℝ) ≤
          (1 + ε) * √(N : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith only [hup_rem]) hNs.le
      linarith only [h1', h2']
    have hlo : -(ε * √(N : ℝ)) ≤ ‖Green84.fourierSum N f θ‖ - √(N : ℝ) := by
      have h1' : (S⁻¹ - E - (K / (N : ℝ)) / S - C_round * (1 / √(N : ℝ))) * √(N : ℝ) ≤
          ‖Green84.fourierSum N f θ‖ := by
        have hstep1 : (S⁻¹ - E - (K / (N : ℝ)) / S - C_round * (1 / √(N : ℝ))) * √(N : ℝ) =
            √(N : ℝ) * ((1 - K / (N : ℝ)) / S) -
              ((C_round * (1 / √(N : ℝ))) * √(N : ℝ) + E * √(N : ℝ)) := by
          ring
        have hstep2 : √(N : ℝ) * ((1 - K / (N : ℝ)) / S) -
              ((C_round * (1 / √(N : ℝ))) * √(N : ℝ) + E * √(N : ℝ)) ≤
            ‖UX θ‖ - (C_round + E * √(N : ℝ)) := by
          rw [← hCeq]
          linarith only [hUX_b.1]
        have hstep3 : ‖UX θ‖ - (C_round + E * √(N : ℝ)) ≤ ‖Green84.fourierSum N f θ‖ := by
          linarith only [htri2]
        linarith only [hstep1, hstep2, hstep3]
      have h2' : (1 - ε) * √(N : ℝ) ≤
          (S⁻¹ - E - (K / (N : ℝ)) / S - C_round * (1 / √(N : ℝ))) * √(N : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith only [hlo_rem]) hNs.le
      linarith only [h1', h2']
    exact abs_le.mpr ⟨hlo, hup⟩

theorem main : H1 → H2 → type_of% @Green84.green_84.variants.littlewood := by
  intro h1 h2
  exact project_and_round h1 (wave_spectral_data h2)

end OMA.R_Green84_green_84_variants_littlewood_R2
