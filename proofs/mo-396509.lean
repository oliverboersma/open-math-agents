import OMAStatements.S_mo_396509
import Mathlib

/-!
# Sharp contraction of the mean absolute difference

Ordering the three draws reduces the inequality to a lower bound on the smaller
of the two adjacent gaps. At fixed sample mean, each positive superlevel of the
joint density is convex and invariant under coordinate permutations. In radial
gap coordinates its gauge is compared with the chord joining the two directions
where the signed weight changes sign. Integration gives the sharp bound, and
the one-sided exponential density realizes equality.
-/

/-!
# First absolute moment of a log-concave density (MO 396509 support lemma)

For `f` with `OMA.S_mo_396509.IsLogConcavePDF f` we prove `Integrable f` and
`Integrable (fun x => |x| * f x)`.

Proof: pick `a` with `f a > 0`, then `b > a` with `f b < f a / 2` (else `f` is bounded
below on a half-line). Log-concavity along `a, b, x` gives an exponential majorant for
`x > b`. The left tail is the right tail of the reflection `x ↦ f (-x)`.
-/

namespace MO396509Moment

open MeasureTheory Set Real

/-- The hypotheses actually used; closed under reflection. -/
structure Tail (f : ℝ → ℝ) : Prop where
  meas : Measurable f
  nonneg : ∀ x, 0 ≤ f x
  int : Integrable f
  lc : ∀ x y t : ℝ, 0 < t → t < 1 → (f x) ^ (1 - t) * (f y) ^ t ≤ f ((1 - t) * x + t * y)

theorem Tail.neg {f : ℝ → ℝ} (h : Tail f) : Tail (fun x => f (-x)) where
  meas := h.meas.comp measurable_neg
  nonneg x := h.nonneg _
  int := h.int.comp_neg
  lc x y t ht0 ht1 := by
    have := h.lc (-x) (-y) t ht0 ht1
    have e : (1 - t) * -x + t * -y = -((1 - t) * x + t * y) := by ring
    rw [e] at this
    exact this

theorem integrable_of_pdf {f : ℝ → ℝ} (h : OMA.S_mo_396509.IsLogConcavePDF f) :
    Integrable f := by
  by_contra hni
  have h0 := integral_undef hni
  rw [h.2.2.1] at h0
  exact one_ne_zero h0

theorem tail_of_pdf {f : ℝ → ℝ} (h : OMA.S_mo_396509.IsLogConcavePDF f) : Tail f where
  meas := h.1
  nonneg := h.2.1
  int := integrable_of_pdf h
  lc := h.2.2.2

theorem exists_pos {f : ℝ → ℝ} (h : OMA.S_mo_396509.IsLogConcavePDF f) : ∃ a, 0 < f a := by
  by_contra hne
  push Not at hne
  have hz : f = fun _ => 0 := funext fun x => le_antisymm (hne x) (h.2.1 x)
  have h1 := h.2.2.1
  rw [hz] at h1
  simp at h1

theorem exists_small {f : ℝ → ℝ} (h : Tail f) {a : ℝ} (ha : 0 < f a) :
    ∃ b, a < b ∧ f b < f a / 2 := by
  by_contra hne
  push Not at hne
  have hc : IntegrableOn (fun _ : ℝ => f a / 2) (Ioi a) := by
    refine Integrable.mono' h.int.integrableOn aestronglyMeasurable_const ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (half_pos ha)]
    exact hne x hx
  rw [integrableOn_const_iff, Real.volume_Ioi] at hc
  rcases hc with hc | hc
  · have : f a / 2 = 0 := by simpa using hc
    linarith [half_pos ha]
  · exact lt_irrefl _ hc

theorem tail_bound {f : ℝ → ℝ} (h : Tail f) {a b x : ℝ} (ha : 0 < f a) (hab : a < b)
    (hb : f b ≤ f a / 2) (hx : b < x) :
    f x ≤ f a * exp (-(log 2 / (b - a)) * (x - a)) := by
  rcases (h.nonneg x).eq_or_lt with h0 | hpos
  · rw [← h0]
    exact (mul_pos ha (exp_pos _)).le
  have hxa : 0 < x - a := by linarith
  have hba : 0 < b - a := by linarith
  have ht0 : 0 < (b - a) / (x - a) := div_pos hba hxa
  have ht1 : (b - a) / (x - a) < 1 := (div_lt_one hxa).2 (by linarith)
  have hcomb : (1 - (b - a) / (x - a)) * a + (b - a) / (x - a) * x = b := by
    field_simp
    ring
  have h1 := h.lc a x _ ht0 ht1
  rw [hcomb] at h1
  have h2 := h1.trans hb
  have hp1 := rpow_pos_of_pos ha (1 - (b - a) / (x - a))
  have hp2 := rpow_pos_of_pos hpos ((b - a) / (x - a))
  have h3 := log_le_log (mul_pos hp1 hp2) h2
  rw [log_mul hp1.ne' hp2.ne', log_rpow ha, log_rpow hpos, log_div ha.ne' two_ne_zero] at h3
  have h4 : (b - a) / (x - a) * (log (f x) - log (f a)) ≤ -log 2 := by linarith
  have h4' : (b - a) * (log (f x) - log (f a)) ≤ -log 2 * (x - a) := by
    have := mul_le_mul_of_nonneg_right h4 hxa.le
    have e : (b - a) / (x - a) * (log (f x) - log (f a)) * (x - a)
        = (b - a) * (log (f x) - log (f a)) := by
      field_simp
    rwa [e] at this
  have h5 : log (f x) - log (f a) ≤ -(log 2 / (b - a)) * (x - a) := by
    have e : -(log 2 / (b - a)) * (x - a) = -log 2 * (x - a) / (b - a) := by ring
    rw [e, le_div_iff₀ hba]
    linarith
  calc f x = exp (log (f x)) := (exp_log hpos).symm
    _ ≤ exp (log (f a) + (-(log 2 / (b - a)) * (x - a))) := exp_le_exp.2 (by linarith)
    _ = f a * exp (-(log 2 / (b - a)) * (x - a)) := by rw [exp_add, exp_log ha]

theorem right_moment {f : ℝ → ℝ} (h : Tail f) {a : ℝ} (ha : 0 < f a) :
    IntegrableOn (fun x => |x| * f x) (Ioi a) := by
  obtain ⟨b, hab, hb⟩ := exists_small h ha
  have hba : 0 < b - a := by linarith
  obtain ⟨d, hd⟩ : ∃ d, d = log 2 / (2 * (b - a)) := ⟨_, rfl⟩
  have hd0 : 0 < d := by
    rw [hd]
    exact div_pos (log_pos one_lt_two) (by linarith)
  have hG : IntegrableOn
      (fun x => (|a| + (b - a)) * f x + f a / d * exp (d * a) * exp (-d * x)) (Ioi a) :=
    (h.int.integrableOn.const_mul _).add ((exp_neg_integrableOn_Ioi a hd0).const_mul _)
  refine Integrable.mono' hG
    ((continuous_abs.measurable.mul h.meas).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx' : a < x := hx
  have hfx := h.nonneg x
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hfx)]
  have habs : |x| ≤ |a| + (x - a) := by
    calc |x| = |a + (x - a)| := by congr 1; ring
      _ ≤ |a| + |x - a| := abs_add_le _ _
      _ = |a| + (x - a) := by rw [abs_of_pos (by linarith : 0 < x - a)]
  have hE : 0 ≤ f a / d * exp (d * a) * exp (-d * x) :=
    mul_nonneg (mul_nonneg (div_nonneg ha.le hd0.le) (exp_pos _).le) (exp_pos _).le
  have key : (x - a) * f x ≤ (b - a) * f x + f a / d * exp (d * a) * exp (-d * x) := by
    rcases le_or_gt x b with hxb | hxb
    · have : (x - a) * f x ≤ (b - a) * f x :=
        mul_le_mul_of_nonneg_right (by linarith) hfx
      linarith
    · have hb1 := tail_bound h ha hab hb.le hxb
      have e1 : -(log 2 / (b - a)) * (x - a) = -(2 * d * (x - a)) := by
        rw [hd]
        field_simp
      rw [e1] at hb1
      have h1 : d * (x - a) ≤ exp (d * (x - a)) := by
        linarith [add_one_le_exp (d * (x - a))]
      have h2 : x - a ≤ exp (d * (x - a)) / d := by
        rw [le_div_iff₀ hd0]
        linarith
      have h3 : (x - a) * f x ≤ exp (d * (x - a)) / d * (f a * exp (-(2 * d * (x - a)))) :=
        mul_le_mul h2 hb1 hfx (div_nonneg (exp_pos _).le hd0.le)
      have e3 : exp (d * (x - a)) * exp (-(2 * d * (x - a))) = exp (d * a) * exp (-d * x) := by
        rw [← exp_add, ← exp_add]
        congr 1
        ring
      have e2 : exp (d * (x - a)) / d * (f a * exp (-(2 * d * (x - a))))
          = f a / d * exp (d * a) * exp (-d * x) := by
        calc exp (d * (x - a)) / d * (f a * exp (-(2 * d * (x - a))))
            = f a / d * (exp (d * (x - a)) * exp (-(2 * d * (x - a)))) := by ring
          _ = f a / d * (exp (d * a) * exp (-d * x)) := by rw [e3]
          _ = f a / d * exp (d * a) * exp (-d * x) := by ring
      rw [e2] at h3
      have : 0 ≤ (b - a) * f x := mul_nonneg hba.le hfx
      linarith
  have hm := mul_le_mul_of_nonneg_right habs hfx
  nlinarith [hm, key]

theorem left_moment {f : ℝ → ℝ} (h : Tail f) {a : ℝ} (ha : 0 < f a) :
    IntegrableOn (fun x => |x| * f x) (Iio a) := by
  have hl : IntegrableOn (fun x => |x| * f (-x)) (Ioi (-a)) :=
    right_moment h.neg (a := -a) (by simpa using ha)
  have hi := (integrable_indicator_iff measurableSet_Ioi).2 hl
  have hi' := hi.comp_neg
  rw [← integrable_indicator_iff measurableSet_Iio]
  have e : (fun t => (Ioi (-a)).indicator (fun x => |x| * f (-x)) (-t))
      = (Iio a).indicator (fun x => |x| * f x) := by
    funext x
    by_cases hx : x < a
    · have : -x ∈ Ioi (-a) := by simpa using hx
      simp [indicator, hx, this]
    · have : -x ∉ Ioi (-a) := by simpa using hx
      simp [indicator, hx, this]
  rw [e] at hi'
  exact hi'

theorem Tail.integrable_abs_mul {f : ℝ → ℝ} (h : Tail f) {a : ℝ} (ha : 0 < f a) :
    Integrable (fun x => |x| * f x) := by
  have hl : IntegrableOn (fun x => |x| * f x) (Iic a) := by
    rw [integrableOn_Iic_iff_integrableOn_Iio]
    exact left_moment h ha
  have hu := hl.union (right_moment h ha)
  rwa [Iic_union_Ioi, integrableOn_univ] at hu

/-- A log-concave probability density is integrable. -/
theorem integrable {f : ℝ → ℝ} (h : OMA.S_mo_396509.IsLogConcavePDF f) : Integrable f :=
  integrable_of_pdf h

/-- A log-concave probability density has a finite first absolute moment. -/
theorem integrable_abs_mul {f : ℝ → ℝ} (h : OMA.S_mo_396509.IsLogConcavePDF f) :
    Integrable (fun x => |x| * f x) := by
  obtain ⟨a, ha⟩ := exists_pos h
  exact (tail_of_pdf h).integrable_abs_mul ha

end MO396509Moment

namespace MO396509Exp
open MeasureTheory ProbabilityTheory Set Real OMA.S_mo_396509
private noncomputable abbrev p := exponentialPDFReal

private theorem pdf (r x : ℝ) : p r x = if 0 ≤ x then r * exp (-(r*x)) else 0 := by
  simp [p, exponentialPDFReal, gammaPDFReal]

private noncomputable def E (r : ℝ) (g : ℝ → ℝ) := ∫ x : ℝ, g x * p r x
private theorem eq_on_pos {r : ℝ} {g h : ℝ → ℝ} (he : ∀ x, 0 ≤ x → g x = h x) :
    E r g = E r h := by
  unfold E
  congr 1
  funext x
  by_cases hx : 0 ≤ x
  · rw [he x hx]
  · simp [pdf, hx]

private theorem restr (r : ℝ) (g : ℝ → ℝ) :
    E r g = ∫ x in Ioi (0:ℝ), g x * (r * exp (-(r*x))) := by
  unfold E
  rw [← integral_Ici_eq_integral_Ioi, ← integral_indicator measurableSet_Ici]
  congr 1
  funext x
  by_cases hx : 0 ≤ x <;> simp [pdf, hx, Set.indicator, Set.mem_Ici]

private theorem mean {r : ℝ} (hr : 0 < r) : E r id = 1/r := by
  rw [restr]
  simp only [id_eq, mul_left_comm _ r, integral_const_mul]
  have hm := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (by norm_num) hr
  norm_num [Real.Gamma_add_one, Real.Gamma_one] at hm
  rw [hm]
  field_simp

private theorem laplace {r : ℝ} (hr : 0 < r) {s : ℝ} (hs : 0 ≤ s) :
    E r (fun x => exp (-(s*x))) = r/(r+s) := by
  rw [restr]
  simp_rw [mul_left_comm _ r, ← Real.exp_add, show ∀ x:ℝ, -(s*x) + -(r*x) = (-(r+s))*x by intro; ring]
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith)]
  simp only [mul_zero, Real.exp_zero, div_neg]; ring

private theorem mass {r : ℝ} (hr : 0 < r) : ∫ x, p r x = 1 := by
  simpa [E, hr.ne'] using laplace hr (s := 0) le_rfl

theorem valid {r : ℝ} (hr : 0 < r) : IsLogConcavePDF (p r) := by
  refine ⟨measurable_exponentialPDFReal r, exponentialPDFReal_nonneg hr, mass hr, ?_⟩
  intro x y t ht h1
  have ht' : 0 < 1-t := by linarith
  by_cases hx : 0 ≤ x
  · by_cases hy : 0 ≤ y
    · have hz : 0 ≤ (1-t)*x+t*y := by positivity
      simp only [pdf, if_pos hx, if_pos hy, if_pos hz, Real.mul_rpow hr.le (Real.exp_pos _).le,
        ← Real.exp_mul]
      rw [mul_mul_mul_comm, ← Real.rpow_add hr, sub_add_cancel, Real.rpow_one, ← Real.exp_add]
      exact le_of_eq (by congr 2; ring)
    · rw [pdf r y, if_neg hy, Real.zero_rpow ht.ne', mul_zero]
      exact exponentialPDFReal_nonneg hr _
  · rw [pdf r x, if_neg hx, Real.zero_rpow ht'.ne', zero_mul]
    exact exponentialPDFReal_nonneg hr _

private theorem integrable_ne {g : ℝ → ℝ} (h : (∫ x, g x) ≠ 0) : Integrable g := by
  by_contra hn
  exact h (integral_undef hn)

private theorem moment {r : ℝ} (hr : 0 < r) (a b k s : ℝ) (hs : 0 ≤ s) :
    E r (fun x => a*x+b+k*exp (-(s*x))) = a/r+b+k*(r/(r+s)) := by
  have hi : Integrable (p r) := integrable_ne (by rw [mass hr]; norm_num)
  have hj : Integrable (fun x => x*p r x) :=
    integrable_ne (by change E r id ≠ 0; rw [mean hr]; positivity)
  have hl : Integrable (fun x => exp (-(s*x))*p r x) :=
    integrable_ne (by change E r _ ≠ 0; rw [laplace hr hs]; positivity)
  unfold E
  simp_rw [add_mul, mul_assoc]
  rw [integral_add (f := fun x => a*(x*p r x)+b*p r x) ((hj.const_mul a).add (hi.const_mul b)) (hl.const_mul k),
    integral_add (hj.const_mul a) (hi.const_mul b)]
  simp_rw [integral_const_mul, mass hr]
  change a * E r id + b * 1 + k * E r (fun x => exp (-(s*x))) = _
  rw [mean hr, laplace hr hs]; ring

private theorem abs_mean {r : ℝ} (hr : 0 < r) {d : ℝ} (hd : 0 ≤ d) :
    E r (fun z => |d-z|) = d - 1/r + 2/r*exp (-(r*d)) := by
  have htail : (∫ z : ℝ, (z-d)*p r (z-d)) = 1/r := by
    simpa [sub_eq_add_neg] using (integral_add_right_eq_self (fun z : ℝ => z*p r z) (-d)).trans (mean hr)
  have hi : Integrable (p r) := integrable_ne (by rw [mass hr]; norm_num)
  have hj : Integrable (fun x => x*p r x) :=
    integrable_ne (by change E r id ≠ 0; rw [mean hr]; positivity)
  have hk : Integrable (fun z => (z-d)*p r (z-d)) := integrable_ne (by rw [htail]; positivity)
  have he (z : ℝ) : |d-z| * p r z =
      (d*p r z-z*p r z) + (2*exp (-(r*d)))*((z-d)*p r (z-d)) := by
    by_cases hz : d ≤ z
    · have h1 : 0 ≤ z := hd.trans hz
      have h2 : 0 ≤ z-d := sub_nonneg.mpr hz
      rw [abs_of_nonpos (sub_nonpos.mpr hz), pdf r z, if_pos h1, pdf r (z-d), if_pos h2]
      have e : exp (-(r*d))*exp (-(r*(z-d))) = exp (-(r*z)) := by rw [← Real.exp_add]; congr 1; ring
      linear_combination (norm := ring) (-2*r*(z-d)) * e
    · have h2 : ¬ 0 ≤ z-d := by linarith
      rw [abs_of_nonneg (by linarith), pdf r (z-d), if_neg h2]
      ring
  unfold E
  simp_rw [he]
  rw [integral_add (f := fun x => d*p r x-x*p r x) ((hi.const_mul d).sub hj) (hk.const_mul _),
    integral_sub (hi.const_mul _) hj, integral_const_mul, mass hr, integral_const_mul, htail]
  change d*1-E r id + _ = _
  rw [mean hr]; ring
theorem spread_eval {r : ℝ} (hr : 0 < r) : spread (p r) = 1/r := by
  calc
    _ = E r (fun x => E r (fun y => |x-y|)) := by
      unfold spread E
      congr 1; funext x
      rw [← integral_mul_const]
      congr 1; funext y; ring
    _ = E r (fun x => 1*x+(-(1/r))+ (2/r)*exp (-(r*x))) := by
      apply eq_on_pos; intro x hx; rw [abs_mean hr hx]; ring
    _ = _ := by rw [moment hr _ _ _ _ hr.le]; field_simp; ring

theorem gain_eval {r : ℝ} (hr : 0 < r) :
    gain (p r) = (1/9:ℝ) * spread (p r) := by
  have hh : 0 ≤ r/2 := by linarith
  have hinner {x : ℝ} (hx : 0 ≤ x) :
      E r (fun y => E r (fun z => |(x+y)/2-z|)) =
        (1/2)*x + (-(1/(2*r))) + (4/(3*r))*exp (-((r/2)*x)) := by
    calc
      _ = E r (fun y => (1/2)*y+(x/2-1/r)+(2/r*exp (-((r/2)*x)))*exp (-((r/2)*y))) := by
        apply eq_on_pos; intro y hy
        rw [abs_mean hr (show 0 ≤ (x+y)/2 by positivity)]
        rw [show -(r*((x+y)/2)) = -((r/2)*x)+ -((r/2)*y) by ring, Real.exp_add]
        ring
      _ = _ := by rw [moment hr _ _ _ _ hh]; field_simp; ring
  have hobj : (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
      |(x+y)/2-z| * p r x * p r y * p r z) = 8/(9*r) := by
    calc
      _ = E r (fun x => E r (fun y => E r (fun z => |(x+y)/2-z|))) := by
        unfold E
        congr 1; funext x
        rw [← integral_mul_const]
        congr 1; funext y
        rw [← integral_mul_const, ← integral_mul_const]
        congr 1; funext z; ring
      _ = E r (fun x => (1/2)*x + (-(1/(2*r))) + (4/(3*r))*exp (-((r/2)*x))) :=
        eq_on_pos (fun _ hx => hinner hx)
      _ = _ := by rw [moment hr _ _ _ _ hh]; field_simp; ring
  unfold gain
  rw [hobj, spread_eval hr]
  ring
end MO396509Exp

namespace MO396509
open MeasureTheory Set
private noncomputable def F (u v k l s : ℝ) : ℝ :=
  ((k*v+l*(u-v))*s^2+2*l*v*s)/(2*v^2*(v+(u-v)*s)^2)

private theorem deriv_F {u v k l s : ℝ} (hv : v ≠ 0) (hg : v+(u-v)*s ≠ 0) :
    HasDerivAt (F u v k l) ((k*s+l)/(v+(u-v)*s)^3) s := by
  have hi := hasDerivAt_id s
  have hd := ((hi.const_mul (u-v)).const_add v).pow 2
  have hn := ((hi.pow 2).const_mul (k*v+l*(u-v))).add (hi.const_mul (2*l*v))
  unfold F
  convert hn.div (hd.const_mul (2*v^2)) (by dsimp; positivity) using 1 <;> try dsimp
  all_goals first | rfl | (field_simp [hv,hg] <;> ring)

theorem affine_signed_integral_eq {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    (∫ s in (0:ℝ)..1, (min s (1-s)-2/9)/(v+(u-v)*s)^3) =
      (2*u-v)*(2*v-u)/(18*u^2*v^2*(u+v)) := by
  let f := fun s : ℝ => (min s (1-s)-2/9)/(v+(u-v)*s)^3
  have pos {s : ℝ} (h : s ∈ Icc (0:ℝ) 1) : 0 < v+(u-v)*s := by
    rcases le_total u v with h'|h'
    · nlinarith [mul_nonneg (sub_nonneg.mpr h') (sub_nonneg.mpr h.2)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr h') h.1]
  have hc : ContinuousOn f (Icc 0 1) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    exact fun s hs => pow_ne_zero _ (pos hs).ne'
  have hL : ∀ s ∈ uIcc 0 (1/2 : ℝ), HasDerivAt (F u v 1 (-2/9)) (f s) s := by
    intro s hs
    rw [uIcc_of_le (by norm_num)] at hs
    have h := deriv_F (k:=1) (l:= -2/9) hv.ne' (pos ⟨hs.1,by linarith [hs.2]⟩).ne'
    convert h using 1
    dsimp [f]; rw [min_eq_left (by linarith [hs.2])]; ring
  have hR : ∀ s ∈ uIcc (1/2 : ℝ) 1, HasDerivAt (F u v (-1) (7/9)) (f s) s := by
    intro s hs
    rw [uIcc_of_le (by norm_num)] at hs
    have h := deriv_F (k:= -1) (l:=7/9) hv.ne' (pos ⟨by linarith [hs.1],hs.2⟩).ne'
    convert h using 1
    dsimp [f]; rw [min_eq_right (by linarith [hs.1])]; ring
  have hI {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
      IntervalIntegrable f volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact hc.mono (Icc_subset_Icc ha hb)
  have hl := hI (a:=0) (b:=1/2) (by norm_num) (by norm_num) (by norm_num)
  have hr := hI (a:=1/2) (b:=1) (by norm_num) (by norm_num) (by norm_num)
  change (∫ s in (0:ℝ)..1, f s) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals hl hr,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hL hl, intervalIntegral.integral_eq_sub_of_hasDerivAt hR hr]
  have hm : v+(u-v)*(1/2) = (u+v)/2 := by ring
  simp only [F,hm,mul_zero,add_zero,mul_one,add_sub_cancel]
  field_simp [hu.ne',hv.ne',(add_pos hu hv).ne'] <;> ring

theorem affine_signed_integral_nonneg {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (huv : u ≤ 2*v) (hvu : v ≤ 2*u) :
    0 ≤ ∫ s in (0:ℝ)..1, (min s (1-s)-2/9)/(v+(u-v)*s)^3 := by
  rcases eq_or_lt_of_le hu with h|h
  · have hv0 : v=0 := by linarith
    simp [← h,hv0]
  · rw [affine_signed_integral_eq h (by linarith)]
    exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
end MO396509

namespace MO396509Geometry

open Set

private theorem secant_cross {g : ℝ → ℝ} (hg : ConvexOn ℝ (Icc 0 1) g)
    {x y z : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (hz : z ∈ Icc (0:ℝ) 1)
    (hxy : x < y) (hyz : y < z) :
    (g y - g x) * (z-y) ≤ (g z - g y) * (y-x) :=
  (div_le_div_iff₀ (sub_pos.mpr hxy) (sub_pos.mpr hyz)).mp
    (hg.slope_mono_adjacent hx hz hxy hyz)

theorem chord_comparison {g : ℝ → ℝ} (hg : ConvexOn ℝ (Icc 0 1) g)
    (hpos : ∀ s ∈ Icc (0:ℝ) 1, 0 < g s)
    (hab : 11 * g (2/9) ≤ 16 * g (7/9)) (hba : 11 * g (7/9) ≤ 16 * g (2/9)) :
    ∃ u v : ℝ, 0 < u ∧ 0 < v ∧ u ≤ 2*v ∧ v ≤ 2*u ∧
      ∀ s ∈ Icc (0:ℝ) 1, (min s (1-s) - 2/9) / (u*s + v*(1-s))^3 ≤
        (min s (1-s) - 2/9) / (g s)^3 := by
  let a := g (2/9)
  let b := g (7/9)
  let u := (7*b - 2*a)/5
  let v := (7*a - 2*b)/5
  change 11*a ≤ 16*b at hab
  change 11*b ≤ 16*a at hba
  have h₂ : (2/9:ℝ) ∈ Icc (0:ℝ) 1 := by constructor <;> norm_num
  have h₇ : (7/9:ℝ) ∈ Icc (0:ℝ) 1 := by constructor <;> norm_num
  have ha : 0 < a := hpos _ h₂
  have hb : 0 < b := hpos _ h₇
  have hu : 0 < u := by dsimp [u]; linarith
  have hv : 0 < v := by dsimp [v]; linarith
  refine ⟨u,v,hu,hv,by dsimp [u,v]; linarith,by dsimp [u,v]; linarith,?_⟩
  intro s hs
  have hs' := hs.1
  have hs'' := hs.2
  have hL : 0 < u*s + v*(1-s) := by
    by_cases h : s = 0
    · simpa [h] using hv
    · exact add_pos_of_pos_of_nonneg (mul_pos hu (lt_of_le_of_ne hs' (Ne.symm h)))
        (mul_nonneg hv.le (by linarith))
  have hgs := hpos s hs
  have inside (hW : 0 ≤ min s (1-s) - 2/9) (hgL : g s ≤ u*s + v*(1-s)) :
      (min s (1-s) - 2/9) / (u*s + v*(1-s))^3 ≤ (min s (1-s) - 2/9) / (g s)^3 :=
    div_le_div_of_nonneg_left hW (by positivity) (by gcongr)
  have outside (hW : min s (1-s) - 2/9 ≤ 0) (hLg : u*s + v*(1-s) ≤ g s) :
      (min s (1-s) - 2/9) / (u*s + v*(1-s))^3 ≤ (min s (1-s) - 2/9) / (g s)^3 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    exact mul_le_mul_of_nonpos_left (by gcongr) hW
  rcases lt_trichotomy s (2/9) with h | rfl | h
  · apply outside (by linarith [min_le_left s (1-s)])
    have H := secant_cross hg hs h₇ h (by norm_num : (2/9:ℝ) < 7/9)
    change (a - g s) * _ ≤ (b-a) * _ at H
    dsimp [u,v]
    linarith only [H]
  · norm_num
  rcases lt_trichotomy s (7/9) with h' | rfl | h'
  · apply inside (sub_nonneg.mpr (le_min h.le (by linarith)))
    have H := secant_cross hg h₂ h₇ h h'
    change (g s-a) * _ ≤ (b-g s) * _ at H
    dsimp [u,v]
    linarith only [H]
  · norm_num
  · apply outside (by linarith [min_le_right s (1-s)])
    have H := secant_cross hg h₂ hs (by norm_num : (2/9:ℝ) < 7/9) h'
    change (b-a) * _ ≤ (g s-b) * _ at H
    dsimp [u,v]
    linarith only [H]

def gapDir (s : ℝ) : ℝ × ℝ := (s, 1-s)

private theorem gauge_convex_comb {K : Set (ℝ × ℝ)} (hK : Convex ℝ K)
    (ha : Absorbent ℝ K) {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (x y : ℝ × ℝ) :
    gauge K (c • x + d • y) ≤ c * gauge K x + d * gauge K y := by
  simpa only [gauge_smul_of_nonneg hc, gauge_smul_of_nonneg hd, smul_eq_mul] using
    gauge_add_le hK ha (c • x) (d • y)

private theorem gauge_swap {K : Set (ℝ × ℝ)} (T : ℝ × ℝ → ℝ × ℝ)
    (hT : ∀ c x, T (c • x) = (c : ℝ) • T x) (hi : ∀ x, T x ∈ K ↔ x ∈ K)
    (x : ℝ × ℝ) : gauge K (T x) = gauge K x := by
  simp only [gauge_def', ← hT, hi]

theorem gauge_chord_comparison {K : Set (ℝ × ℝ)} (hK : Convex ℝ K)
    (ha : Absorbent ℝ K) (hb : Bornology.IsVonNBounded ℝ K)
    (h₁ : ∀ a b : ℝ, (-a,a+b) ∈ K ↔ (a,b) ∈ K)
    (h₂ : ∀ a b : ℝ, (a+b,-b) ∈ K ↔ (a,b) ∈ K) :
    ∃ u v : ℝ, 0 < u ∧ 0 < v ∧ u ≤ 2*v ∧ v ≤ 2*u ∧
      ∀ s ∈ Icc (0:ℝ) 1, (min s (1-s) - 2/9) / (u*s + v*(1-s))^3 ≤
        (min s (1-s) - 2/9) / (gauge K (gapDir s))^3 := by
  apply chord_comparison (g := fun s => gauge K (gapDir s))
  · refine ⟨convex_Icc _ _, ?_⟩
    intro x hx y hy a b ha' hb' hab
    have H : gapDir (a • x + b • y) = a • gapDir x + b • gapDir y := by
      ext <;> simp [gapDir]; linarith
    change gauge K (gapDir (a • x + b • y)) ≤ _
    rw [H]
    exact gauge_convex_comb hK ha ha' hb' _ _
  · intro s _
    apply (gauge_pos ha hb).mpr
    intro h
    have := congrArg Prod.fst h
    have := congrArg Prod.snd h
    simp only [gapDir, Prod.fst_zero, Prod.snd_zero] at *
    linarith
  · let q := gapDir (7/9)
    let T := fun x : ℝ × ℝ => (-x.1,x.1+x.2)
    have hT : gauge K (T q) = gauge K q := by
      apply gauge_swap T _ (fun x => h₁ x.1 x.2)
      intro c x
      ext <;> simp [T,mul_add]
    have hdir : (11/16:ℝ) • gapDir (2/9) = (67/112:ℝ) • q + (45/112:ℝ) • T q := by
      ext <;> norm_num [gapDir,q,T]
    have H := gauge_convex_comb hK ha (by norm_num : (0:ℝ) ≤ 67/112)
      (by norm_num : (0:ℝ) ≤ 45/112) q (T q)
    rw [← hdir, gauge_smul_of_nonneg (by norm_num : (0:ℝ) ≤ 11/16), hT] at H
    change (11/16) * _ ≤ _ at H
    dsimp [q] at H
    linarith
  · let p := gapDir (2/9)
    let T := fun x : ℝ × ℝ => (x.1+x.2,-x.2)
    have hT : gauge K (T p) = gauge K p := by
      apply gauge_swap T _ (fun x => h₂ x.1 x.2)
      intro c x
      ext <;> simp [T,mul_add]
    have hdir : (11/16:ℝ) • gapDir (7/9) = (67/112:ℝ) • p + (45/112:ℝ) • T p := by
      ext <;> norm_num [gapDir,p,T]
    have H := gauge_convex_comb hK ha (by norm_num : (0:ℝ) ≤ 67/112)
      (by norm_num : (0:ℝ) ≤ 45/112) p (T p)
    rw [← hdir, gauge_smul_of_nonneg (by norm_num : (0:ℝ) ≤ 11/16), hT] at H
    change (11/16) * _ ≤ _ at H
    dsimp [p] at H
    linarith

end MO396509Geometry

namespace MO396509
open MeasureTheory Set Filter
open scoped ENNReal

private theorem layer_eq {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {W : α → ℝ≥0∞} (hW : Measurable W) {H : α → ℝ} (hH : Measurable H)
    (h0 : ∀ a, 0 ≤ H a) :
    (∫⁻ a, W a * ENNReal.ofReal (H a) ∂μ) =
      ∫⁻ t in Ioi (0:ℝ), ∫⁻ a in {a | t ≤ H a}, W a ∂μ := by
  calc
    _ = ∫⁻ a, ENNReal.ofReal (H a) ∂μ.withDensity W :=
      (lintegral_withDensity_eq_lintegral_mul μ hW (ENNReal.measurable_ofReal.comp hH)).symm
    _ = ∫⁻ t in Ioi (0:ℝ), μ.withDensity W {a | t ≤ H a} :=
      lintegral_eq_lintegral_meas_le _ (Filter.Eventually.of_forall h0) hH.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro t
      exact withDensity_apply W (measurableSet_le measurable_const hH)

theorem weighted_layer_comparison {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {L R : α → ℝ≥0∞} (hL : Measurable L) (hR : Measurable R)
    {H : α → ℝ} (hH : Measurable H) (h0 : ∀ a, 0 ≤ H a)
    (hlevel : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)),
      (∫⁻ a in {a | t ≤ H a}, L a ∂μ) ≤ ∫⁻ a in {a | t ≤ H a}, R a ∂μ) :
    (∫⁻ a, L a * ENNReal.ofReal (H a) ∂μ) ≤ ∫⁻ a, R a * ENNReal.ofReal (H a) ∂μ := by
  rw [layer_eq μ hL hH h0,layer_eq μ hR hH h0]
  exact lintegral_mono_ae hlevel

theorem weighted_layer_comparison_of_forall {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {L R : α → ℝ≥0∞} (hL : Measurable L) (hR : Measurable R)
    {H : α → ℝ} (hH : Measurable H) (h0 : ∀ a, 0 ≤ H a)
    (hlevel : ∀ t > 0, (∫⁻ a in {a | t ≤ H a}, L a ∂μ) ≤
      ∫⁻ a in {a | t ≤ H a}, R a ∂μ) :
    (∫⁻ a, L a * ENNReal.ofReal (H a) ∂μ) ≤ ∫⁻ a, R a * ENNReal.ofReal (H a) ∂μ := by
  apply weighted_layer_comparison μ hL hR hH h0
  exact (ae_restrict_mem measurableSet_Ioi).mono hlevel
end MO396509

namespace MO396509Coordinates
open Set MeasureTheory
open scoped ENNReal

abbrev T := ℝ × ℝ × ℝ
def ordered : Set T := {p | p.1 < p.2.1 ∧ p.2.1 < p.2.2}
noncomputable def point (c s r : ℝ) : T :=
  let x := c - (1+s)*r/3
  (x, x+s*r, x+r)

private theorem affine_integral (a b : ℝ) (hb : 0 < b) (g : ℝ → ℝ≥0∞) :
    ∫⁻ y in Ioo a (a+b), g y =
      ∫⁻ s in Ioo (0:ℝ) 1, ENNReal.ofReal b * g (a+s*b) := by
  let F := fun s : ℝ => a+s*b
  have hi : F '' Ioo (0:ℝ) 1 = Ioo a (a+b) := by
    ext y
    constructor
    · rintro ⟨s, ⟨hs, hs'⟩, rfl⟩
      exact ⟨by dsimp [F]; nlinarith, by dsimp [F]; nlinarith⟩
    · rintro ⟨hy, hy'⟩
      refine ⟨(y-a)/b, ⟨div_pos (by linarith) hb, (div_lt_one hb).mpr (by linarith)⟩, ?_⟩
      dsimp [F]
      field_simp
      <;> ring
  rw [← hi]
  have hd (x : ℝ) : HasDerivAt F b x := by
    simpa [F] using ((hasDerivAt_id' x).mul_const b).const_add a
  have hin : Function.Injective F := fun x y h => by
    dsimp [F] at h
    exact (mul_left_inj' hb.ne').mp (add_left_cancel h)
  simpa only [abs_of_pos hb] using
    lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
      (fun x _ => (hd x).hasDerivWithinAt) hin.injOn g

private theorem shift (a : ℝ) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ y, g y) = ∫⁻ t, g (a+t) := by
  rw [← lintegral_map hg (measurable_const_add a), map_add_left_eq_self]

private theorem inner (g : T → ℝ≥0∞) (hg : Measurable g) (x : ℝ) :
    (∫⁻ p : ℝ × ℝ, ordered.indicator g (x,p)) =
    ∫⁻ r in Ioi (0:ℝ), ∫⁻ s in Ioo (0:ℝ) 1,
      ENNReal.ofReal r * g (x,x+s*r,x+r) := by
  have hOrd : MeasurableSet ordered :=
    (measurableSet_lt (f := fun p : T => p.1) (g := fun p : T => p.2.1) (by fun_prop) (by fun_prop)).inter
      (measurableSet_lt (f := fun p : T => p.2.1) (g := fun p : T => p.2.2) (by fun_prop) (by fun_prop))
  have hm : Measurable (fun p : ℝ × ℝ => ordered.indicator g (x,p)) :=
    (hg.indicator hOrd).comp (by fun_prop)
  rw [Measure.volume_eq_prod, lintegral_prod_symm _ hm.aemeasurable]
  rw [shift x _ hm.lintegral_prod_left']
  rw [← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro r
  by_cases hr : 0 < r
  · rw [Set.indicator_of_mem (show r ∈ Ioi (0:ℝ) from hr), ← affine_integral x r hr (fun y => g (x,y,x+r))]
    rw [← lintegral_indicator measurableSet_Ioo]
    rfl
  · rw [Set.indicator_of_notMem (show r ∉ Ioi (0:ℝ) from hr)]
    have hz (y : ℝ) : (x,y,x+r) ∉ ordered := by
      intro h
      change x < y ∧ y < x+r at h
      exact hr (by linarith [h.1, h.2])
    simp [hz]

private theorem rotate (F : ℝ → ℝ → ℝ → ℝ≥0∞)
    (μ ν ξ : Measure ℝ) [SFinite μ] [SFinite ν] [SFinite ξ]
    (hm : Measurable (fun p : T => F p.1 p.2.1 p.2.2)) :
    (∫⁻ x, ∫⁻ y, ∫⁻ z, F x y z ∂ξ ∂ν ∂μ) =
    ∫⁻ y, ∫⁻ z, ∫⁻ x, F x y z ∂μ ∂ξ ∂ν := by
  calc
    _ = ∫⁻ y, ∫⁻ x, ∫⁻ z, F x y z ∂ξ ∂μ ∂ν := by
      apply lintegral_lintegral_swap
      apply Measurable.aemeasurable
      exact (hm.comp (show Measurable (fun p : (ℝ × ℝ) × ℝ => (p.1.1,p.1.2,p.2)) by fun_prop)).lintegral_prod_right' (ν := ξ)
    _ = _ := by
      apply lintegral_congr
      intro y
      apply lintegral_lintegral_swap
      exact (hm.comp (show Measurable (fun p : ℝ × ℝ => (p.1,y,p.2)) by fun_prop)).aemeasurable

theorem ordered_transform (g : T → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ p in ordered, g p) =
    ∫⁻ c : ℝ, ∫⁻ s in Ioo (0:ℝ) 1, ∫⁻ r in Ioi (0:ℝ),
      ENNReal.ofReal r * g (point c s r) := by
  have hOrd : MeasurableSet ordered := by
    change MeasurableSet {p : T | p.1 < p.2.1 ∧ p.2.1 < p.2.2}
    exact (measurableSet_lt (f := fun p : T => p.1) (g := fun p : T => p.2.1) (by fun_prop) (by fun_prop)).inter
      (measurableSet_lt (f := fun p : T => p.2.1) (g := fun p : T => p.2.2) (by fun_prop) (by fun_prop))
  let μ := (volume : Measure ℝ).restrict (Ioi 0)
  let ν := (volume : Measure ℝ).restrict (Ioo 0 1)
  let H (x r s : ℝ) := ENNReal.ofReal r * g (x,x+s*r,x+r)
  let J (r s c : ℝ) := ENNReal.ofReal r * g (point c s r)
  have hH : Measurable (fun p : T => H p.1 p.2.1 p.2.2) := by dsimp [H]; fun_prop
  have hJ : Measurable (fun p : T => J p.1 p.2.1 p.2.2) := by dsimp [J,point]; fun_prop
  have hfirst : (∫⁻ p in ordered, g p) = ∫⁻ x : ℝ, ∫⁻ r, ∫⁻ s, H x r s ∂ν ∂μ := by
    rw [← lintegral_indicator hOrd, Measure.volume_eq_prod, lintegral_prod _ (hg.indicator hOrd).aemeasurable]
    exact lintegral_congr (inner g hg)
  rw [hfirst, rotate H volume μ ν hH]
  have hshift (r s : ℝ) : (∫⁻ x, H x r s) = ∫⁻ c, J r s c := by
    convert shift (-((1+s)*r/3)) (fun x => H x r s) (by dsimp [H]; fun_prop) using 1
    apply lintegral_congr
    intro c
    dsimp [J,H,point]
    rw [sub_eq_neg_add]
  simp_rw [hshift]
  rw [← rotate (fun c r s => J r s c) volume μ ν (hJ.comp
    (show Measurable (fun p : T => (p.2.1,p.2.2,p.1)) by fun_prop))]
  apply lintegral_congr
  intro c
  apply lintegral_lintegral_swap
  exact (hJ.comp (show Measurable (fun p : ℝ × ℝ => (p.1,p.2,c)) by fun_prop)).aemeasurable

end MO396509Coordinates

namespace MO396509
open Set MeasureTheory Filter MO396509Geometry intervalIntegral
open scoped ENNReal Topology

private theorem dir_pos {K : Set (ℝ × ℝ)} (hn : K ∈ 𝓝 0)
    (hb : Bornology.IsVonNBounded ℝ K) (s : ℝ) : 0 < gauge K (gapDir s) := by
  apply (gauge_pos (absorbent_nhds_zero hn) hb).mpr
  intro h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [gapDir,Prod.fst_zero,Prod.snd_zero] at h1 h2
  linarith

private theorem ray_mass {K : Set (ℝ × ℝ)} (hc : Convex ℝ K) (hn : K ∈ 𝓝 0)
    (hb : Bornology.IsVonNBounded ℝ K) (s w : ℝ) (hw : 0 ≤ w) :
    (∫⁻ r in {r : ℝ | 0 < r ∧ r • gapDir s ∈ K},
      ENNReal.ofReal w * ENNReal.ofReal (r^2)) =
      ENNReal.ofReal (w / (gauge K (gapDir s))^3 / 3) := by
  let g := gauge K (gapDir s)
  have hg : 0 < g := dir_pos hn hb s
  have he : {r : ℝ | 0 < r ∧ r • gapDir s ∈ K} =ᵐ[volume] Ioc 0 (1/g) := by
    filter_upwards [volume.ae_ne (1/g)] with r hr
    apply propext
    change (0 < r ∧ r • gapDir s ∈ K) ↔ 0 < r ∧ r ≤ 1/g
    constructor
    · rintro ⟨hr0,hmem⟩
      refine ⟨hr0,(le_div_iff₀ hg).mpr ?_⟩
      simpa only [gauge_smul_of_nonneg hr0.le, smul_eq_mul] using gauge_le_one_of_mem hmem
    · rintro ⟨hr0,hr1⟩
      refine ⟨hr0,interior_subset ((gauge_lt_one_iff_mem_interior hc hn).mp ?_)⟩
      rw [gauge_smul_of_nonneg hr0.le]
      exact (lt_div_iff₀ hg).mp (lt_of_le_of_ne hr1 hr)
  rw [Measure.restrict_congr_set he,lintegral_const_mul _ (by fun_prop),
    ← ofReal_integral_eq_lintegral_ofReal (intervalIntegrable_pow _).1,
    ← intervalIntegral.integral_of_le (by positivity : 0 ≤ 1/g)]
  · rw [← ENNReal.ofReal_mul hw]
    congr 1
    simp [g,integral_pow]; ring
  · exact Eventually.of_forall (fun r => sq_nonneg r)

theorem radial_section_bound {K : Set (ℝ × ℝ)} (hc : Convex ℝ K) (hn : K ∈ 𝓝 0)
    (hb : Bornology.IsVonNBounded ℝ K)
    (h₁ : ∀ a b : ℝ, (-a,a+b) ∈ K ↔ (a,b) ∈ K)
    (h₂ : ∀ a b : ℝ, (a+b,-b) ∈ K ↔ (a,b) ∈ K) :
    (∫⁻ s in Ioo (0:ℝ) 1, ∫⁻ r in {r : ℝ | 0 < r ∧ r • gapDir s ∈ K},
      ENNReal.ofReal (2/9) * ENNReal.ofReal (r^2)) ≤
    ∫⁻ s in Ioo (0:ℝ) 1, ∫⁻ r in {r : ℝ | 0 < r ∧ r • gapDir s ∈ K},
      ENNReal.ofReal (min s (1-s)) * ENNReal.ofReal (r^2) := by
  let g := fun s => gauge K (gapDir s)
  let m := fun s : ℝ => min s (1-s)
  have hg (s) : 0 < g s := dir_pos hn hb s
  have hgc : Continuous g := (continuous_gauge hc hn).comp (by unfold gapDir; fun_prop)
  have hmc : Continuous m := by dsimp [m]; fun_prop
  obtain ⟨u,v,hu,hv,huv,hvu,hcmp⟩ := gauge_chord_comparison hc (absorbent_nhds_zero hn) hb h₁ h₂
  have hlin {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) : 0 < v+(u-v)*s := by
    rcases le_total u v with h|h
    · nlinarith [mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr hs.2)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr h) hs.1]
  have hf : IntervalIntegrable (fun s => (m s-2/9)/(v+(u-v)*s)^3) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact ContinuousOn.div (by fun_prop) (by fun_prop) fun s hs => pow_ne_zero _ (hlin hs).ne'
  have hcL : Continuous (fun s => (2/9)/(g s)^3) :=
    continuous_const.div (hgc.pow 3) fun s => pow_ne_zero _ (hg s).ne'
  have hcR : Continuous (fun s => m s/(g s)^3) :=
    hmc.div (hgc.pow 3) fun s => pow_ne_zero _ (hg s).ne'
  have hid s : (m s-2/9)/(g s)^3 = m s/(g s)^3-(2/9)/(g s)^3 := sub_div ..
  have hp := affine_signed_integral_nonneg hu.le hv.le huv hvu
  have hle := intervalIntegral.integral_mono_on zero_le_one hf
    ((hcR.sub hcL).intervalIntegrable 0 1) (fun s hs => by
      change (m s-2/9)/(v+(u-v)*s)^3 ≤ m s/(g s)^3-(2/9)/(g s)^3
      rw [← hid,show v+(u-v)*s = u*s+v*(1-s) by ring]
      exact hcmp s hs)
  simp only [Pi.sub_apply] at hle
  rw [intervalIntegral.integral_sub (hcR.intervalIntegrable ..) (hcL.intervalIntegrable ..)] at hle
  have hreal := sub_nonneg.mp (hp.trans hle)
  have transfer (w : ℝ → ℝ) (hw : ∀ s ∈ Ioo (0:ℝ) 1, 0 ≤ w s)
      (hwc : Continuous (fun s => w s/(g s)^3)) :
      (∫⁻ s in Ioo (0:ℝ) 1, ∫⁻ r in {r : ℝ | 0 < r ∧ r • gapDir s ∈ K},
        ENNReal.ofReal (w s) * ENNReal.ofReal (r^2)) =
      ENNReal.ofReal ((∫ s in (0:ℝ)..1, w s/(g s)^3)/3) := by
    calc
      _ = ∫⁻ s in Ioo (0:ℝ) 1, ENNReal.ofReal (w s/(g s)^3/3) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
        exact ray_mass hc hn hb s (w s) (hw s hs)
      _ = _ := by
        rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc,← intervalIntegral.integral_div,
          ← ofReal_integral_eq_lintegral_ofReal ((hwc.div_const 3).intervalIntegrable 0 1).1,
          ← intervalIntegral.integral_of_le zero_le_one]
        filter_upwards [ae_restrict_mem measurableSet_Ioc, (volume.restrict (Ioc (0:ℝ) 1)).ae_ne 1] with s hs hs1
        exact div_nonneg (div_nonneg (hw s ⟨hs.1,lt_of_le_of_ne hs.2 hs1⟩) (pow_nonneg (hg s).le _)) (by norm_num)
  rw [transfer (fun _ => 2/9) (by intros; norm_num) hcL, transfer m (fun s hs => le_min hs.1.le (by linarith [hs.2])) hcR]
  exact ENNReal.ofReal_le_ofReal (by linarith)
end MO396509

namespace MO396509Section
open Set MeasureTheory
open scoped Topology

noncomputable def leftCoord (c : ℝ) (p : ℝ × ℝ) : ℝ := c - (2*p.1+p.2)/3

noncomputable def density (f : ℝ → ℝ) (c : ℝ) (p : ℝ × ℝ) : ℝ :=
  let x := leftCoord c p
  f x * f (x+p.1) * f (x+p.1+p.2)

def sectionSet (f : ℝ → ℝ) (c t R : ℝ) : Set (ℝ × ℝ) :=
  {p | t ≤ density f c p ∧ |p.1| ≤ R ∧ |p.2| ≤ R ∧ |p.1+p.2| ≤ R}

theorem density_measurable {f : ℝ → ℝ} (hf : Measurable f) (c : ℝ) :
    Measurable (density f c) := by unfold density leftCoord; fun_prop

theorem density_nonneg {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) (c : ℝ) (p : ℝ × ℝ) :
    0 ≤ density f c p := mul_nonneg (mul_nonneg (hf _) (hf _)) (hf _)

theorem section_measurable {f : ℝ → ℝ} (hf : Measurable f) (c t R : ℝ) :
    MeasurableSet (sectionSet f c t R) := by
  apply MeasurableSet.inter (measurableSet_le measurable_const (density_measurable hf c))
  exact (measurableSet_le (f := fun p : ℝ × ℝ => |p.1|) (by fun_prop) measurable_const).inter
    ((measurableSet_le (f := fun p : ℝ × ℝ => |p.2|) (by fun_prop) measurable_const).inter
     (measurableSet_le (f := fun p : ℝ × ℝ => |p.1+p.2|) (by fun_prop) measurable_const))

theorem section_bounded (f : ℝ → ℝ) (c t R : ℝ) :
    Bornology.IsVonNBounded ℝ (sectionSet f c t R) := by
  apply NormedSpace.isVonNBounded_of_isBounded
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨R, fun p hp => ?_⟩
  exact max_le hp.2.1 hp.2.2.1

private theorem density_left (f : ℝ → ℝ) (c a b : ℝ) :
    density f c (-a,a+b) = density f c (a,b) := by
  simp only [density, leftCoord]
  ring_nf

private theorem density_right (f : ℝ → ℝ) (c a b : ℝ) :
    density f c (a+b,-b) = density f c (a,b) := by
  simp only [density, leftCoord]
  ring_nf

theorem section_swap₁ (f : ℝ → ℝ) (c t R a b : ℝ) :
    (-a,a+b) ∈ sectionSet f c t R ↔ (a,b) ∈ sectionSet f c t R := by
  simp only [sectionSet, mem_ofPred_eq, density_left, abs_neg, neg_add_cancel_left]
  tauto

theorem section_swap₂ (f : ℝ → ℝ) (c t R a b : ℝ) :
    (a+b,-b) ∈ sectionSet f c t R ↔ (a,b) ∈ sectionSet f c t R := by
  simp only [sectionSet, mem_ofPred_eq, density_right, abs_neg, add_neg_cancel_right]
  tauto

private theorem combo_bound {x y R a b : ℝ} (hx : |x| ≤ R) (hy : |y| ≤ R)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) : |a*x+b*y| ≤ R := by
  calc
    _ ≤ |a*x|+|b*y| := abs_add_le _ _
    _ ≤ a*R+b*R := by rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hb]; gcongr
    _ = R := by linear_combination R*hab

theorem section_convex {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x)
    (hl : ∀ x y : ℝ, ∀ t : ℝ, 0 < t → t < 1 →
      (f x) ^ (1-t) * (f y) ^ t ≤ f ((1-t)*x + t*y))
    (c t R : ℝ) (ht : 0 < t) : Convex ℝ (sectionSet f c t R) := by
  intro p hp q hq a b ha hb hab
  rcases ha.eq_or_lt with rfl | ha'
  · have : b = 1 := by linarith
    simpa [this] using hq
  rcases hb.eq_or_lt with rfl | hb'
  · have : a = 1 := by linarith
    simpa [this] using hp
  have hcomb (x y : ℝ) : f x ^ a * f y ^ b ≤ f (a*x+b*y) := by
    simpa only [show 1-b=a by linarith] using hl x y b hb' (by linarith)
  have hlc : leftCoord c (a • p + b • q) = a * leftCoord c p + b * leftCoord c q := by
    simp [leftCoord]
    linear_combination -c*hab
  have H : density f c p ^ a * density f c q ^ b ≤ density f c (a • p + b • q) := by
    let x := leftCoord c p
    let y := leftCoord c q
    let A := a • p + b • q
    have h₂ : leftCoord c A + A.1 = a*(x+p.1)+b*(y+q.1) := by
      rw [show leftCoord c A = _ from hlc]; dsimp [A,x,y]; ring
    have h₃ : leftCoord c A + A.1 + A.2 = a*(x+p.1+p.2)+b*(y+q.1+q.2) := by
      rw [h₂]; dsimp [A]; ring
    change _ ≤ density f c A
    simp only [density, Real.mul_rpow (mul_nonneg (hf _) (hf _)) (hf _),
      Real.mul_rpow (hf _) (hf _)]
    rw [h₃,h₂,show leftCoord c A = _ from hlc]
    calc
      _ = (f x^a*f y^b)*(f (x+p.1)^a*f (y+q.1)^b)*(f (x+p.1+p.2)^a*f (y+q.1+q.2)^b) := by dsimp [x,y]; ring
      _ ≤ _ := by
        have hn (i j : ℝ) : 0 ≤ f i ^ a * f j ^ b := mul_nonneg
          (Real.rpow_nonneg (hf _) _) (Real.rpow_nonneg (hf _) _)
        exact mul_le_mul (mul_le_mul (hcomb _ _) (hcomb _ _) (hn _ _) (hf _))
          (hcomb _ _) (hn _ _) (mul_nonneg (hf _) (hf _))
  have Ht : t^a*t^b=t := by rw [← Real.rpow_add ht, hab, Real.rpow_one]
  refine ⟨?_,combo_bound hp.2.1 hq.2.1 ha hb hab,combo_bound hp.2.2.1 hq.2.2.1 ha hb hab,?_⟩
  · calc
      t = t^a*t^b := Ht.symm
      _ ≤ _ := (mul_le_mul (Real.rpow_le_rpow ht.le hp.1 ha) (Real.rpow_le_rpow ht.le hq.1 hb)
        (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg (density_nonneg hf _ _) _))
      _ ≤ _ := H
  · change |(a*p.1+b*q.1)+(a*p.2+b*q.2)| ≤ R
    convert combo_bound hp.2.2.2 hq.2.2.2 ha hb hab using 1; ring_nf

private theorem zero_or_nhds {K : Set (ℝ × ℝ)} (hK : Convex ℝ K)
    (rot : ∀ a b : ℝ, (a,b) ∈ K → (b,-a-b) ∈ K) :
    K ⊆ {0} ∨ K ∈ 𝓝 0 := by
  classical
  by_cases h : K ⊆ {0}
  · exact Or.inl h
  right
  obtain ⟨⟨a,b⟩, hp, hne⟩ := Set.not_subset.mp h
  have hr := rot a b hp
  have hs : (-a-b,a) ∈ K := by convert rot _ _ hr using 1; congr 2; ring
  have key (u v : ℝ) :
      (1/3:ℝ) • (u,v) + (2/3:ℝ) • ((1/2:ℝ) • (v,-u-v) + (1/2:ℝ) • (-u-v,u)) = 0 := by
    ext <;> simp <;> ring
  have h0 : (0 : ℝ × ℝ) ∈ K := by
    rw [← key a b]
    exact hK hp (hK hr hs (by norm_num) (by norm_num) (by norm_num))
      (by norm_num) (by norm_num) (by norm_num)
  let S := affineSpan ℝ K
  have h0S : (0 : ℝ × ℝ) ∈ S := subset_affineSpan ℝ K h0
  have hdir {v : ℝ × ℝ} (hv : v ∈ K) : v ∈ S.direction := by
    simpa using AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ K hv) h0S
  let d := a^2+a*b+b^2
  have hd : d ≠ 0 := by
    intro H
    dsimp [d] at H
    have hh : a = 0 := by nlinarith [sq_nonneg (2*b+a),sq_nonneg a]
    have h' : b = 0 := by nlinarith [sq_nonneg b]
    exact hne (by simp [hh,h'])
  have htop : S = ⊤ := by
    apply top_unique
    rintro ⟨x,y⟩ _
    have hh := S.direction.add_mem
      (S.direction.smul_mem (((a+b)*x+b*y)/d) (hdir hp))
      (S.direction.smul_mem ((b*x-a*y)/d) (hdir hr))
    have heq : (((a+b)*x+b*y)/d) • (a,b) + ((b*x-a*y)/d) • (b,-a-b) = (x,y) := by
      ext <;> simp <;> field_simp <;> dsimp [d] <;> ring
    rw [heq] at hh
    simpa using AffineSubspace.vadd_mem_of_mem_direction hh h0S
  obtain ⟨⟨x,y⟩, hxy⟩ := hK.interior_nonempty_iff_affineSpan_eq_top.mpr htop
  have hr' := rot x y (interior_subset hxy)
  have hs' : (-x-y,x) ∈ K := by convert rot _ _ hr' using 1; congr 2; ring
  apply mem_interior_iff_mem_nhds.mp
  rw [← key x y]
  exact hK.combo_interior_self_mem_interior hxy
    (hK hr' hs' (by norm_num) (by norm_num) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num)

theorem section_null_or_nhds {f : ℝ → ℝ} (c t R : ℝ) (hK : Convex ℝ (sectionSet f c t R)) :
    sectionSet f c t R ⊆ {0} ∨ sectionSet f c t R ∈ 𝓝 0 :=
  zero_or_nhds hK fun a b hp => by
    have hh := (section_swap₂ f c t R (-a) (a+b)).mpr ((section_swap₁ f c t R a b).mpr hp)
    convert hh using 1; congr 2 <;> ring

end MO396509Section

namespace MO396509Slices
open MeasureTheory Set MO396509Geometry
open scoped ENNReal

private noncomputable def μ : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioo (0:ℝ) 1)).prod (volume.restrict (Ioi (0:ℝ)))
def ray (p : ℝ × ℝ) : ℝ × ℝ := p.2 • gapDir p.1
private theorem ray_meas : Measurable ray := by unfold ray gapDir; fun_prop

private theorem flatten (K : Set (ℝ × ℝ)) (hK : MeasurableSet K) (w : ℝ → ℝ)
    (hw : Measurable w) :
    (∫⁻ p in ray ⁻¹' K, ENNReal.ofReal (w p.1) * ENNReal.ofReal (p.2^2) ∂μ) =
    ∫⁻ s in Ioo (0:ℝ) 1, ∫⁻ r in {r : ℝ | 0 < r ∧ r • gapDir s ∈ K},
      ENNReal.ofReal (w s) * ENNReal.ofReal (r^2) := by
  rw [← lintegral_indicator (ray_meas hK)]
  unfold μ
  rw [lintegral_prod _ (((by fun_prop : Measurable
    (fun p : ℝ × ℝ => ENNReal.ofReal (w p.1) * ENNReal.ofReal (p.2^2)))).indicator
      (ray_meas hK)).aemeasurable]
  apply lintegral_congr
  intro s
  have hpre : MeasurableSet {r : ℝ | r • gapDir s ∈ K} :=
    (show Measurable (fun r : ℝ => r • gapDir s) by fun_prop) hK
  have he : {r : ℝ | 0 < r ∧ r • gapDir s ∈ K} = {r : ℝ | r • gapDir s ∈ K} ∩ Ioi (0:ℝ) := by
    ext; simp [and_comm]
  rw [he, ← Measure.restrict_restrict hpre, ← lintegral_indicator hpre]
  apply lintegral_congr
  intro r
  by_cases hr : r • gapDir s ∈ K <;> simp [Set.indicator, ray, hr]

theorem from_levels (H : ℝ → ℝ × ℝ → ℝ) (hH : ∀ c, Measurable (H c))
    (hn : ∀ c p, 0 ≤ H c p)
    (K : ℝ → ℝ → ℕ → Set (ℝ × ℝ))
    (hK : ∀ c t n, MeasurableSet (K c t n))
    (hinc : ∀ c t, Monotone (K c t))
    (hcover : ∀ c t, ⋃ n, K c t n = {p | t ≤ H c p})
    (hsec : ∀ c t, 0 < t → ∀ n,
      (∫⁻ s in Ioo (0:ℝ) 1, ∫⁻ r in {r : ℝ | 0 < r ∧ r • gapDir s ∈ K c t n},
        ENNReal.ofReal (2/9) * ENNReal.ofReal (r^2)) ≤
      ∫⁻ s in Ioo (0:ℝ) 1, ∫⁻ r in {r : ℝ | 0 < r ∧ r • gapDir s ∈ K c t n},
        ENNReal.ofReal (min s (1-s)) * ENNReal.ofReal (r^2)) :
    (∫⁻ c : ℝ, ∫⁻ s in Ioo (0:ℝ) 1, ∫⁻ r in Ioi (0:ℝ),
      ENNReal.ofReal (2/9) * ENNReal.ofReal (r^2) * ENNReal.ofReal (H c (r • gapDir s))) ≤
    ∫⁻ c : ℝ, ∫⁻ s in Ioo (0:ℝ) 1, ∫⁻ r in Ioi (0:ℝ),
      ENNReal.ofReal (min s (1-s)) * ENNReal.ofReal (r^2) * ENNReal.ofReal (H c (r • gapDir s)) := by
  apply lintegral_mono
  intro c
  let L (p : ℝ × ℝ) := ENNReal.ofReal (2/9) * ENNReal.ofReal (p.2^2)
  let R (p : ℝ × ℝ) := ENNReal.ofReal (min p.1 (1-p.1)) * ENNReal.ofReal (p.2^2)
  have hl : Measurable L := by unfold L; fun_prop
  have hr : Measurable R := by unfold R; fun_prop
  have hm := (hH c).comp ray_meas
  have hb := MO396509.weighted_layer_comparison_of_forall μ hl hr hm
    (fun p => hn c (ray p)) ?_
  · have fub (W : ℝ × ℝ → ℝ≥0∞) (hw : Measurable W) :
        (∫⁻ p, W p * ENNReal.ofReal ((H c ∘ ray) p) ∂μ) =
        ∫⁻ s in Ioo (0:ℝ) 1, ∫⁻ r in Ioi (0:ℝ),
          W (s,r) * ENNReal.ofReal (H c (r • gapDir s)) :=
      lintegral_prod _ ((hw.mul (ENNReal.measurable_ofReal.comp hm)).aemeasurable)
    rw [fub L hl, fub R hr] at hb
    exact hb
  · intro t ht
    have he : {p : ℝ × ℝ | t ≤ (H c ∘ ray) p} = ⋃ n, ray ⁻¹' K c t n := by
      rw [← preimage_iUnion, hcover]
      rfl
    have hm' : Monotone (fun n => ray ⁻¹' K c t n) := fun _ _ h => preimage_mono (hinc c t h)
    rw [he, setLIntegral_iUnion_of_directed _ hm'.directed_le, setLIntegral_iUnion_of_directed _ hm'.directed_le]
    apply iSup_mono
    intro n
    change (∫⁻ p in ray ⁻¹' K c t n, ENNReal.ofReal ((fun _ : ℝ => 2/9) p.1) * ENNReal.ofReal (p.2^2) ∂μ) ≤ _
    rw [flatten _ (hK c t n) _ measurable_const]
    change _ ≤ ∫⁻ p in ray ⁻¹' K c t n, ENNReal.ofReal ((fun s : ℝ => min s (1-s)) p.1) * ENNReal.ofReal (p.2^2) ∂μ
    rw [flatten _ (hK c t n) (fun s : ℝ => min s (1-s)) (by fun_prop)]
    exact hsec c t ht n
noncomputable def G (f : ℝ → ℝ) (c s r : ℝ) :=
  let x := c - (1+s)*r/3
  f x * f (x+s*r) * f (x+r)

private theorem radial_weight {s r : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r) (d : ℝ) :
    ENNReal.ofReal r * ENNReal.ofReal (s*r*d) =
      ENNReal.ofReal s * ENNReal.ofReal (r^2) * ENNReal.ofReal d := by
  rw [ENNReal.ofReal_mul (mul_nonneg hs hr), ENNReal.ofReal_mul hs, pow_two, ENNReal.ofReal_mul hr]
  ring

private theorem degenerate {K : Set (ℝ × ℝ)} (hz : K ⊆ {0}) (s : ℝ) :
    {r : ℝ | 0 < r ∧ r • gapDir s ∈ K} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro r ⟨hr, h⟩
  have he : r • gapDir s = 0 := hz h
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  simp only [gapDir, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_zero, Prod.snd_zero] at h1 h2
  nlinarith

open MO396509Section OMA.S_mo_396509
private theorem density_ray (f : ℝ → ℝ) (c s r : ℝ) :
    density f c (r • gapDir s) = G f c s r := by
  unfold density leftCoord gapDir G
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring_nf

theorem slices {f : ℝ → ℝ} (hf : IsLogConcavePDF f) :
    (∫⁻ c : ℝ, ∫⁻ s in Ioo (0:ℝ) 1, ∫⁻ r in Ioi (0:ℝ),
      ENNReal.ofReal r * ENNReal.ofReal ((2/9)*r*G f c s r)) ≤
    ∫⁻ c : ℝ, ∫⁻ s in Ioo (0:ℝ) 1, ∫⁻ r in Ioi (0:ℝ),
      ENNReal.ofReal r * ENNReal.ofReal (min (s*r) ((1-s)*r)*G f c s r) := by
  let K (c t : ℝ) (n : ℕ) := sectionSet f c t n
  have hm (c t : ℝ) : Monotone (K c t) := by
    intro i j hij p hp
    have hh : (i:ℝ) ≤ j := by exact_mod_cast hij
    exact ⟨hp.1, hp.2.1.trans hh, hp.2.2.1.trans hh, hp.2.2.2.trans hh⟩
  have hu (c t : ℝ) : ⋃ n, K c t n = {p | t ≤ density f c p} := by
    ext p
    constructor
    · intro h; obtain ⟨n, hn⟩ := mem_iUnion.mp h; exact hn.1
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_ge (max |p.1| (max |p.2| |p.1+p.2|))
      exact mem_iUnion.mpr ⟨n, h, (le_max_left ..).trans hn,
        (le_max_left ..).trans ((le_max_right ..).trans hn),
        (le_max_right ..).trans ((le_max_right ..).trans hn)⟩
  have hb := from_levels (density f) (density_measurable hf.1) (density_nonneg hf.2.1)
    K (fun c t n => section_measurable hf.1 c t n) hm hu (by
      intro c t ht n
      have hc := section_convex hf.2.1 hf.2.2.2 c t n ht
      rcases section_null_or_nhds c t n hc with hz | hr
      · simp [K, degenerate hz]
      · exact MO396509.radial_section_bound hc hr (section_bounded ..) (section_swap₁ f c t n) (section_swap₂ f c t n))
  have convertW (w : ℝ → ℝ) (hw : ∀ s ∈ Ioo (0:ℝ) 1, 0 ≤ w s) :
      (∫⁻ c : ℝ, ∫⁻ s in Ioo (0:ℝ) 1, ∫⁻ r in Ioi (0:ℝ),
        ENNReal.ofReal r * ENNReal.ofReal (w s*r*G f c s r)) =
      ∫⁻ c : ℝ, ∫⁻ s in Ioo (0:ℝ) 1, ∫⁻ r in Ioi (0:ℝ),
        ENNReal.ofReal (w s)*ENNReal.ofReal (r^2)*ENNReal.ofReal (density f c (r • gapDir s)) := by
    apply lintegral_congr; intro c
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [density_ray, radial_weight (hw s hs) (le_of_lt hr)]
  rw [← convertW (fun _ => 2/9) (by intros; norm_num),
    ← convertW (fun s => min s (1-s)) (fun s hs => le_min hs.1.le (by linarith [hs.2]))] at hb
  refine hb.trans_eq ?_
  apply lintegral_congr; intro c
  apply lintegral_congr; intro s
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  rw [min_mul_of_nonneg _ _ (le_of_lt hr)]
end MO396509Slices

namespace MO396509Sort
open MeasureTheory Set OMA.S_mo_396509

abbrev T := ℝ × ℝ × ℝ

/-- The ordered chamber `x < y < z`. -/
def chamber : Set T := {p | p.1 < p.2.1 ∧ p.2.1 < p.2.2}

/-- The chamber integrand. -/
noncomputable def chamberIntegrand (f : ℝ → ℝ) (p : T) : ℝ :=
  (min (p.2.1 - p.1) (p.2.2 - p.2.1) - (2/9) * (p.2.2 - p.1)) * (f p.1 * f p.2.1 * f p.2.2)

/-! ### Fubini on triples -/

theorem integral_triple (H : T → ℝ) (hH : Integrable H) :
    ∫ p, H p = ∫ x, ∫ y, ∫ z, H (x, y, z) := by
  have hH2 : Integrable H ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))) := hH
  rw [show (volume : Measure T) = (volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ)) from rfl,
    integral_prod _ hH2]
  apply integral_congr_ae
  filter_upwards [hH2.prod_right_ae] with x hx
  exact integral_prod _ hx

/-! ### The six coordinate permutations -/

def s1 (p : T) : T := (p.1, p.2.2, p.2.1)
def s2 (p : T) : T := (p.2.1, p.1, p.2.2)
def s3 (p : T) : T := (p.2.1, p.2.2, p.1)
def s4 (p : T) : T := (p.2.2, p.1, p.2.1)
def s5 (p : T) : T := (p.2.2, p.2.1, p.1)

theorem mp1 : MeasurePreserving s1 (volume : Measure T) volume :=
  (MeasurePreserving.id (volume : Measure ℝ)).prod
    (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)))

theorem mp2 : MeasurePreserving s2 (volume : Measure T) volume := by
  have a := (measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure ℝ)
    (volume : Measure ℝ))
  have b := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ))).prod (MeasurePreserving.id (volume : Measure ℝ))
  exact a.comp (b.comp a.symm)

theorem mp3 : MeasurePreserving s3 (volume : Measure T) volume := mp1.comp mp2
theorem mp4 : MeasurePreserving s4 (volume : Measure T) volume := mp2.comp mp1
theorem mp5 : MeasurePreserving s5 (volume : Measure T) volume := mp3.comp mp1

theorem setIntegral_perm {σ : T → T} (hσ : MeasurePreserving σ (volume : Measure T) volume)
    {C D : Set T} (hC : MeasurableSet C) (hD : MeasurableSet D) (h : ∀ p, σ p ∈ D ↔ p ∈ C)
    (F : T → ℝ) (hF : Integrable F) :
    ∫ p in D, F p = ∫ p in C, F (σ p) := by
  rw [← integral_indicator hD, ← integral_indicator hC]
  have := integral_map (μ := (volume : Measure T)) hσ.measurable.aemeasurable
    (f := D.indicator F) (by rw [hσ.map_eq]; exact hF.aestronglyMeasurable.indicator hD)
  rw [hσ.map_eq] at this
  rw [this]
  congr 1
  funext p
  by_cases hp : p ∈ C
  · simp [indicator, hp, (h p).2 hp]
  · simp [indicator, hp, (h p).not.2 hp]

/-! ### Null diagonals -/

theorem null12 : volume {p : T | p.1 = p.2.1} = 0 := by
  change ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))) _ = 0
  rw [Measure.measure_prod_null (measurableSet_eq_fun (by fun_prop) (by fun_prop))]
  refine Filter.Eventually.of_forall fun x => ?_
  have hset : (Prod.mk x ⁻¹' {p : T | p.1 = p.2.1}) = ({x} : Set ℝ) ×ˢ (univ : Set ℝ) := by
    ext q
    simp [eq_comm]
  change (volume : Measure (ℝ × ℝ)) (Prod.mk x ⁻¹' {p : T | p.1 = p.2.1}) = 0
  rw [hset]
  exact (Measure.prod_prod _ _).trans (by simp)

theorem null13 : volume {p : T | p.1 = p.2.2} = 0 := by
  have := mp1.measure_preimage (s := {p : T | p.1 = p.2.1})
    (measurableSet_eq_fun (by fun_prop) (by fun_prop)).nullMeasurableSet
  rw [null12] at this
  exact this

theorem null23 : volume {p : T | p.2.1 = p.2.2} = 0 := by
  have := mp2.measure_preimage (s := {p : T | p.1 = p.2.2})
    (measurableSet_eq_fun (by fun_prop) (by fun_prop)).nullMeasurableSet
  rw [null13] at this
  exact this

/-! ### Sorting -/

theorem ms {a b c : T → ℝ} (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) :
    MeasurableSet {p : T | a p < b p ∧ b p < c p} :=
  (measurableSet_lt ha hb).inter (measurableSet_lt hb hc)

theorem measurableSet_chamber : MeasurableSet chamber :=
  ms (a := fun p => p.1) (b := fun p => p.2.1) (c := fun p => p.2.2)
    (by fun_prop) (by fun_prop) (by fun_prop)

/-- Reduction of a full integral to the ordered chamber. -/
theorem integral_eq_chamber (F : T → ℝ) (hF : Integrable F) :
    ∫ p, F p = ∫ p in chamber,
      (F p + F (s1 p) + F (s2 p) + F (s3 p) + F (s4 p) + F (s5 p)) := by
  -- the six chambers
  let D1 : Set T := {p | p.1 < p.2.2 ∧ p.2.2 < p.2.1}
  let D2 : Set T := {p | p.2.1 < p.1 ∧ p.1 < p.2.2}
  let D3 : Set T := {p | p.2.2 < p.1 ∧ p.1 < p.2.1}
  let D4 : Set T := {p | p.2.1 < p.2.2 ∧ p.2.2 < p.1}
  let D5 : Set T := {p | p.2.2 < p.2.1 ∧ p.2.1 < p.1}
  have m1 : MeasurableSet D1 := ms (a := fun p => p.1) (b := fun p => p.2.2)
    (c := fun p => p.2.1) (by fun_prop) (by fun_prop) (by fun_prop)
  have m2 : MeasurableSet D2 := ms (a := fun p => p.2.1) (b := fun p => p.1)
    (c := fun p => p.2.2) (by fun_prop) (by fun_prop) (by fun_prop)
  have m3 : MeasurableSet D3 := ms (a := fun p => p.2.2) (b := fun p => p.1)
    (c := fun p => p.2.1) (by fun_prop) (by fun_prop) (by fun_prop)
  have m4 : MeasurableSet D4 := ms (a := fun p => p.2.1) (b := fun p => p.2.2)
    (c := fun p => p.1) (by fun_prop) (by fun_prop) (by fun_prop)
  have m5 : MeasurableSet D5 := ms (a := fun p => p.2.2) (b := fun p => p.2.1)
    (c := fun p => p.1) (by fun_prop) (by fun_prop) (by fun_prop)
  have m0 := measurableSet_chamber
  have e1 : ∫ p in D1, F p = ∫ p in chamber, F (s1 p) :=
    setIntegral_perm mp1 m0 m1 (fun p => Iff.rfl) F hF
  have e2 : ∫ p in D2, F p = ∫ p in chamber, F (s2 p) :=
    setIntegral_perm mp2 m0 m2 (fun p => Iff.rfl) F hF
  have e3 : ∫ p in D3, F p = ∫ p in chamber, F (s3 p) :=
    setIntegral_perm mp3 m0 m3 (fun p => by simp [D3, s3, chamber, and_comm]) F hF
  have e4 : ∫ p in D4, F p = ∫ p in chamber, F (s4 p) :=
    setIntegral_perm mp4 m0 m4 (fun p => by simp [D4, s4, chamber]) F hF
  have e5 : ∫ p in D5, F p = ∫ p in chamber, F (s5 p) :=
    setIntegral_perm mp5 m0 m5 (fun p => by simp [D5, s5, chamber, and_comm]) F hF
  have i1 : IntegrableOn (fun p => F (s1 p)) chamber :=
    ((mp1.integrable_comp hF.aestronglyMeasurable).2 hF).integrableOn
  have i2 : IntegrableOn (fun p => F (s2 p)) chamber :=
    ((mp2.integrable_comp hF.aestronglyMeasurable).2 hF).integrableOn
  have i3 : IntegrableOn (fun p => F (s3 p)) chamber :=
    ((mp3.integrable_comp hF.aestronglyMeasurable).2 hF).integrableOn
  have i4 : IntegrableOn (fun p => F (s4 p)) chamber :=
    ((mp4.integrable_comp hF.aestronglyMeasurable).2 hF).integrableOn
  have i5 : IntegrableOn (fun p => F (s5 p)) chamber :=
    ((mp5.integrable_comp hF.aestronglyMeasurable).2 hF).integrableOn
  have i0 : IntegrableOn F chamber := hF.integrableOn
  have hR : ∫ p in chamber, (F p + F (s1 p) + F (s2 p) + F (s3 p) + F (s4 p) + F (s5 p)) =
      ∫ p in chamber, (F + (fun p => F (s1 p)) + (fun p => F (s2 p)) + (fun p => F (s3 p)) +
        (fun p => F (s4 p)) + (fun p => F (s5 p))) p := rfl
  rw [hR, integral_add' (((((i0.add i1).add i2).add i3).add i4)) i5,
    integral_add' ((((i0.add i1).add i2).add i3)) i4,
    integral_add' (((i0.add i1).add i2)) i3, integral_add' ((i0.add i1)) i2,
    integral_add' i0 i1, ← e1, ← e2, ← e3, ← e4, ← e5]
  have j0 := hF.indicator m0
  have j1 := hF.indicator m1
  have j2 := hF.indicator m2
  have j3 := hF.indicator m3
  have j4 := hF.indicator m4
  have j5 := hF.indicator m5
  have hS : ∫ p, (chamber.indicator F + D1.indicator F + D2.indicator F + D3.indicator F +
      D4.indicator F + D5.indicator F) p =
      (∫ p in chamber, F p) + (∫ p in D1, F p) + (∫ p in D2, F p) + (∫ p in D3, F p) +
        (∫ p in D4, F p) + (∫ p in D5, F p) := by
    rw [integral_add' ((((j0.add j1).add j2).add j3).add j4) j5,
      integral_add' (((j0.add j1).add j2).add j3) j4,
      integral_add' ((j0.add j1).add j2) j3, integral_add' (j0.add j1) j2,
      integral_add' j0 j1, integral_indicator m0, integral_indicator m1, integral_indicator m2,
      integral_indicator m3, integral_indicator m4, integral_indicator m5]
  rw [← hS]
  apply integral_congr_ae
  have hn : ∀ᵐ p : T, p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2 := by
    have a : ∀ᵐ p : T, p.1 ≠ p.2.1 := measure_eq_zero_iff_ae_notMem.1 null12
    have b : ∀ᵐ p : T, p.1 ≠ p.2.2 := measure_eq_zero_iff_ae_notMem.1 null13
    have c : ∀ᵐ p : T, p.2.1 ≠ p.2.2 := measure_eq_zero_iff_ae_notMem.1 null23
    filter_upwards [a, b, c] with p ha hb hc using ⟨ha, hb, hc⟩
  filter_upwards [hn] with p hp
  obtain ⟨x, y, z⟩ := p
  obtain ⟨hxy, hxz, hyz⟩ := hp
  simp only [ne_eq] at hxy hxz hyz
  simp only [Pi.add_apply, indicator, chamber, D1, D2, D3, D4, D5, Set.mem_ofPred_eq]
  rcases lt_or_gt_of_ne hxy with a | a <;> rcases lt_or_gt_of_ne hxz with b | b <;>
    rcases lt_or_gt_of_ne hyz with c | c <;>
    simp [a, b, c, a.not_gt, b.not_gt, c.not_gt] <;> linarith

/-! ### The bridge -/

theorem integrable_weighted {f : ℝ → ℝ} (hm : Measurable f) (hi : Integrable f)
    (hx : Integrable (fun x => |x| * f x)) (G : T → ℝ) (hG : Measurable G)
    (hb : ∀ p : T, |G p| ≤ 2 * (|p.1| + |p.2.1| + |p.2.2|)) :
    Integrable (fun p : T => G p * f p.1 * f p.2.1 * f p.2.2) := by
  have A1 : Integrable (fun p : T => (|p.1| * f p.1) * (f p.2.1 * f p.2.2)) :=
    hx.mul_prod (hi.mul_prod hi)
  have A2 : Integrable (fun p : T => f p.1 * ((|p.2.1| * f p.2.1) * f p.2.2)) :=
    hi.mul_prod (hx.mul_prod hi)
  have A3 : Integrable (fun p : T => f p.1 * (f p.2.1 * (|p.2.2| * f p.2.2))) :=
    hi.mul_prod (hi.mul_prod hx)
  refine Integrable.mono' (((A1.norm.add A2.norm).add A3.norm).const_mul 2)
    (by fun_prop) (Filter.Eventually.of_forall fun p => ?_)
  obtain ⟨x, y, z⟩ := p
  have h := hb (x, y, z)
  simp only [Real.norm_eq_abs, abs_mul, abs_abs, Pi.add_apply] at h ⊢
  have hP : 0 ≤ |f x| * |f y| * |f z| := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h hP]

/-- Exact bridge identity: the defect `gain - spread/9` is twice the chamber integral. -/
theorem gain_sub_eq {f : ℝ → ℝ} (hm : Measurable f) (h1 : (∫ x : ℝ, f x) = 1)
    (hi : Integrable f) (hx : Integrable (fun x => |x| * f x)) :
    gain f - (1/9) * spread f = 2 * ∫ p in chamber, chamberIntegrand f p := by
  have hU : Integrable (fun p : T => |p.1 - p.2.1| * f p.1 * f p.2.1 * f p.2.2) := by
    refine integrable_weighted hm hi hx (fun p : T => |p.1 - p.2.1|) (by fun_prop) fun p => ?_
    rw [abs_abs]
    have := abs_sub p.1 p.2.1
    have := abs_nonneg p.2.2
    have := abs_nonneg p.1
    have := abs_nonneg p.2.1
    linarith
  have hV : Integrable (fun p : T => |(p.1 + p.2.1) / 2 - p.2.2| * f p.1 * f p.2.1 * f p.2.2) := by
    refine integrable_weighted hm hi hx (fun p : T => |(p.1 + p.2.1) / 2 - p.2.2|)
      (by fun_prop) fun p => ?_
    rw [abs_abs]
    have h1 := abs_sub ((p.1 + p.2.1) / 2) p.2.2
    have h2 := abs_add_le (p.1 / 2) (p.2.1 / 2)
    rw [abs_div, abs_div, abs_two, ← add_div] at h2
    have := abs_nonneg p.2.2
    have := abs_nonneg p.1
    have := abs_nonneg p.2.1
    linarith
  have eS : spread f = ∫ p : T, |p.1 - p.2.1| * f p.1 * f p.2.1 * f p.2.2 := by
    rw [integral_triple _ hU]
    unfold spread
    simp only [integral_const_mul, h1, mul_one]
  have eG : gain f = spread f -
      ∫ p : T, |(p.1 + p.2.1) / 2 - p.2.2| * f p.1 * f p.2.1 * f p.2.2 := by
    rw [integral_triple _ hV]
    rfl
  set F : T → ℝ := fun p => (8/9) * (|p.1 - p.2.1| * f p.1 * f p.2.1 * f p.2.2) -
    |(p.1 + p.2.1) / 2 - p.2.2| * f p.1 * f p.2.1 * f p.2.2 with hFdef
  have hF : Integrable F := (hU.const_mul (8/9)).sub hV
  have eF : gain f - (1/9) * spread f = ∫ p, F p := by
    rw [hFdef, integral_sub (hU.const_mul (8/9)) hV, integral_const_mul, eG, ← eS]
    ring
  rw [eF, integral_eq_chamber F hF, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_chamber ?_
  rintro ⟨x, y, z⟩ ⟨hxy, hyz⟩
  simp only [] at hxy hyz
  simp only [hFdef, s1, s2, s3, s4, s5, chamberIntegrand]
  have a1 : |x - y| = y - x := by rw [abs_of_neg (by linarith)]; ring
  have a2 : |x - z| = z - x := by rw [abs_of_neg (by linarith)]; ring
  have a3 : |y - x| = y - x := abs_of_pos (by linarith)
  have a4 : |y - z| = z - y := by rw [abs_of_neg (by linarith)]; ring
  have a5 : |z - x| = z - x := abs_of_pos (by linarith)
  have a6 : |z - y| = z - y := abs_of_pos (by linarith)
  have b1 : |(x + y) / 2 - z| = z - (x + y) / 2 := by rw [abs_of_neg (by linarith)]; ring
  have b2 : |(y + x) / 2 - z| = z - (x + y) / 2 := by rw [abs_of_neg (by linarith)]; ring
  have b3 : |(y + z) / 2 - x| = (y + z) / 2 - x := abs_of_pos (by linarith)
  have b4 : |(z + y) / 2 - x| = (y + z) / 2 - x := by rw [abs_of_pos (by linarith)]; ring
  rw [a1, a2, a3, a4, a5, a6, b1, b2, b3, b4]
  rcases le_total (y - x) (z - y) with h | h
  · rw [min_eq_left h, abs_of_nonneg (show 0 ≤ (x + z) / 2 - y by linarith),
      abs_of_nonneg (show 0 ≤ (z + x) / 2 - y by linarith)]
    ring
  · rw [min_eq_right h, abs_of_nonpos (show (x + z) / 2 - y ≤ 0 by linarith),
      abs_of_nonpos (show (z + x) / 2 - y ≤ 0 by linarith)]
    ring

/-- The bridge: nonnegativity of the chamber integral gives `spread/9 ≤ gain`. -/
theorem bridge {f : ℝ → ℝ} (hm : Measurable f) (h1 : (∫ x : ℝ, f x) = 1)
    (hi : Integrable f) (hx : Integrable (fun x => |x| * f x))
    (hC : 0 ≤ ∫ p in {p : ℝ × ℝ × ℝ | p.1 < p.2.1 ∧ p.2.1 < p.2.2},
      (min (p.2.1 - p.1) (p.2.2 - p.2.1) - (2/9) * (p.2.2 - p.1)) *
        (f p.1 * f p.2.1 * f p.2.2)) :
    (1/9 : ℝ) * spread f ≤ gain f := by
  have h := gain_sub_eq hm h1 hi hx
  have hC' : 0 ≤ ∫ p in chamber, chamberIntegrand f p := hC
  linarith

end MO396509Sort

namespace MO396509Bridge
open Set MeasureTheory MO396509Coordinates
open scoped ENNReal
noncomputable def dens (f : ℝ → ℝ) (p : T) := f p.1 * f p.2.1 * f p.2.2
noncomputable def low (f : ℝ → ℝ) (p : T) := (2/9 : ℝ) * (p.2.2 - p.1) * dens f p
noncomputable def high (f : ℝ → ℝ) (p : T) := min (p.2.1-p.1) (p.2.2-p.2.1) * dens f p

private theorem majorant {f : ℝ → ℝ} (hf : Integrable f)
    (hm : Integrable (fun x => |x| * f x)) :
    Integrable (fun p : T => (|p.1| + |p.2.1| + |p.2.2|) * dens f p) := by
  have h₁ : Integrable (fun p : T => (|p.1| * f p.1) * (f p.2.1 * f p.2.2)) :=
    hm.mul_prod (hf.mul_prod hf)
  have h₂ : Integrable (fun p : T => f p.1 * ((|p.2.1| * f p.2.1) * f p.2.2)) :=
    hf.mul_prod (hm.mul_prod hf)
  have h₃ : Integrable (fun p : T => f p.1 * (f p.2.1 * (|p.2.2| * f p.2.2))) :=
    hf.mul_prod (hf.mul_prod hm)
  apply ((h₁.add h₂).add h₃).congr
  filter_upwards with p
  dsimp [dens]
  ring

private theorem int_pair {f : ℝ → ℝ} (hf : OMA.S_mo_396509.IsLogConcavePDF f) :
    IntegrableOn (low f) ordered ∧ IntegrableOn (high f) ordered := by
  have hM := (majorant (MO396509Moment.integrable hf)
    (MO396509Moment.integrable_abs_mul hf)).integrableOn (s := ordered)
  have hmf := hf.1
  have hnn := hf.2.1
  have hD (p : T) : 0 ≤ dens f p := by exact mul_nonneg (mul_nonneg (hnn _) (hnn _)) (hnn _)
  have hOrd : MeasurableSet ordered := by
    exact (measurableSet_lt (f := fun p : T => p.1) (g := fun p : T => p.2.1) (by fun_prop) (by fun_prop)).inter
      (measurableSet_lt (f := fun p : T => p.2.1) (g := fun p : T => p.2.2) (by fun_prop) (by fun_prop))
  constructor <;> apply hM.mono' (by first | unfold low dens; fun_prop | unfold high dens; fun_prop)
  all_goals
    filter_upwards [ae_restrict_mem hOrd] with p hp
    change p.1 < p.2.1 ∧ p.2.1 < p.2.2 at hp
    have ha := abs_nonneg p.2.1
    have hb := abs_le.mp (le_refl |p.1|)
    have hc := abs_le.mp (le_refl |p.2.2|)
    have hd := abs_le.mp (le_refl |p.2.1|)
    rw [Real.norm_eq_abs]
  · rw [abs_of_nonneg (show 0 ≤ low f p by dsimp [low]; exact mul_nonneg (by linarith [hp.1,hp.2]) (hD p))]
    exact mul_le_mul_of_nonneg_right (by linarith [hp.1,hp.2] : (2/9:ℝ)*(p.2.2-p.1) ≤ _) (hD p)
  · rw [abs_of_nonneg (show 0 ≤ high f p by dsimp [high]; exact mul_nonneg (le_min (by linarith [hp.1]) (by linarith [hp.2])) (hD p))]
    exact mul_le_mul_of_nonneg_right ((min_le_left _ _).trans (by linarith [abs_nonneg p.2.2])) (hD p)

theorem ordered_bound {f : ℝ → ℝ} (hf : OMA.S_mo_396509.IsLogConcavePDF f)
    (h : (∫⁻ p in ordered, ENNReal.ofReal (low f p)) ≤ ∫⁻ p in ordered, ENNReal.ofReal (high f p)) :
    0 ≤ ∫ p in ordered, (min (p.2.1-p.1) (p.2.2-p.2.1) - (2/9:ℝ)*(p.2.2-p.1)) * dens f p := by
  obtain ⟨hi,hj⟩ := int_pair hf
  have hO : MeasurableSet ordered :=
    (measurableSet_lt (f := fun p : T => p.1) (g := fun p : T => p.2.1) (by fun_prop) (by fun_prop)).inter
      (measurableSet_lt (f := fun p : T => p.2.1) (g := fun p : T => p.2.2) (by fun_prop) (by fun_prop))
  have hnn := hf.2.1
  have hl : 0 ≤ᵐ[volume.restrict ordered] low f := by
    filter_upwards [ae_restrict_mem hO] with p hp
    change p.1 < p.2.1 ∧ p.2.1 < p.2.2 at hp
    simp only [Pi.zero_apply,low,dens]
    exact mul_nonneg (by linarith [hp.1,hp.2]) (mul_nonneg (mul_nonneg (hnn _) (hnn _)) (hnn _))
  have hh : 0 ≤ᵐ[volume.restrict ordered] high f := by
    filter_upwards [ae_restrict_mem hO] with p hp
    change p.1 < p.2.1 ∧ p.2.1 < p.2.2 at hp
    simp only [Pi.zero_apply,high,dens]
    exact mul_nonneg (le_min (by linarith [hp.1]) (by linarith [hp.2])) (mul_nonneg (mul_nonneg (hnn _) (hnn _)) (hnn _))
  have hreal := ENNReal.toReal_mono ((lintegral_ofReal_ne_top_iff_integrable hj.aestronglyMeasurable hh).mpr hj) h
  rw [← integral_eq_lintegral_of_nonneg_ae hl hi.aestronglyMeasurable,
    ← integral_eq_lintegral_of_nonneg_ae hh hj.aestronglyMeasurable] at hreal
  simp only [sub_mul]
  exact (integral_sub hj hi) ▸ sub_nonneg.mpr hreal
end MO396509Bridge

namespace MO396509Final
open MeasureTheory Set MO396509Bridge MO396509Coordinates OMA.S_mo_396509
open scoped ENNReal

private theorem low_point (f : ℝ → ℝ) (c s r : ℝ) :
    low f (point c s r) = (2/9)*r*MO396509Slices.G f c s r := by
  dsimp [low, dens, point, MO396509Slices.G]
  rw [add_sub_cancel_left]

private theorem high_point (f : ℝ → ℝ) (c s r : ℝ) :
    high f (point c s r) = min (s*r) ((1-s)*r) * MO396509Slices.G f c s r := by
  let x := c-(1+s)*r/3
  change min ((x+s*r)-x) ((x+r)-(x+s*r)) * _ = _
  rw [add_sub_cancel_left, show (x+r)-(x+s*r)=(1-s)*r by ring]
  rfl

theorem universal {f : ℝ → ℝ} (hf : IsLogConcavePDF f) : (1/9:ℝ)*spread f ≤ gain f := by
  apply MO396509Sort.bridge hf.1 hf.2.2.1 (MO396509Moment.integrable hf)
    (MO396509Moment.integrable_abs_mul hf)
  apply ordered_bound hf
  have hm := hf.1
  rw [ordered_transform (fun p => ENNReal.ofReal (low f p)) (by unfold low dens; fun_prop),
      ordered_transform (fun p => ENNReal.ofReal (high f p)) (by unfold high dens; fun_prop)]
  simpa only [low_point, high_point] using (MO396509Slices.slices hf)
end MO396509Final

theorem OMA.solution : type_of% @OMA.S_mo_396509.main := by
  refine ⟨⟨fun f hf => MO396509Final.universal hf, ?_⟩, fun r hr => MO396509Exp.gain_eval hr⟩
  intro c hc
  have h := hc (ProbabilityTheory.exponentialPDFReal 1) (MO396509Exp.valid zero_lt_one)
  rw [MO396509Exp.gain_eval zero_lt_one, MO396509Exp.spread_eval zero_lt_one] at h
  simpa using h
