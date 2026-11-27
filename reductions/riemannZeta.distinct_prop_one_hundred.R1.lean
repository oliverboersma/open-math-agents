import FormalConjectures.Paper.RiemannZetaZeros
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Distinct zeros from positive-spacing pair correlation

Goldston, Lee, Schettler and Suriajaya, arXiv:2503.15449v4, §§5–8,
extend Gallagher and Mueller, *Primes and zeros in short intervals* (1978),
Theorem 1, to ordinates without assuming the Riemann hypothesis. The PCC input
below counts spacings in an interval with a varying upper endpoint.
Only strictly positive spacings enter it. The separate unconditional
short-interval second-moment estimate (6.1) counts *all* pairs, including
different complex zeros at exactly the same height. Subtracting the two
orientations of the positive-spacing sum recovers this entire atom. Riemann–von
Mangoldt then lets us compare the cumulative and dyadic multiplicity defects.
-/

namespace OMA.R_riemannZeta_distinct_prop_one_hundred_R1

open ZetaZeros Filter Classical
open scoped BigOperators Topology

/-- The lower bound in (4.3) and PCC, uniform for thresholds in [1/2, B].
Heights are counted with multiplicity. The normalization by the cumulative
zero count is equivalent to the paper's by (3.7). -/
def H1 : Prop :=
  ∀ B : ℝ, 1 ≤ B → ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop,
    ∀ Z : Finset ℂ, (Z : Set ℂ) = nontrivialZeros riemannZeta 0 T →
    ∀ u ∈ Set.Icc (1 / 2 : ℝ) B,
    let m := fun z => (analyticOrderNatAt riemannZeta z : ℝ)
    let L := Real.log T / (2 * Real.pi)
    ((∫ v in 0..u, 1 - Real.sinc (Real.pi * v) ^ 2) - ε) * N riemannZeta 0 T ≤
      ∑ z ∈ Z, ∑ w ∈ Z, if z.im < w.im ∧ (w.im - z.im) * L ≤ u then m z * m w else 0

/-- The upper-bound consequence of (6.1) from Gallagher–Mueller and Fujii.
The bandwidth is first fixed sufficiently large, then the height tends to infinity. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ B : ℝ in atTop, ∀ᶠ T : ℝ in atTop,
    ∀ Z : Finset ℂ, (Z : Set ℂ) = nontrivialZeros riemannZeta 0 T →
    let m := fun z => (analyticOrderNatAt riemannZeta z : ℝ)
    let K := fun u : ℝ => max 0 (1 - |u| * (Real.log T / (2 * Real.pi)) / B)
    (∑ z ∈ Z, ∑ w ∈ Z, m z * m w * K (w.im - z.im)) ≤ (B + ε) * N riemannZeta 0 T

/-- The leading term of the classical Riemann–von Mangoldt formula. -/
def H3 : Prop :=
  Tendsto (fun T : ℝ => (N riemannZeta 0 T : ℝ) / (T * (Real.log T / (2 * Real.pi))))
    atTop (𝓝 1)

open MeasureTheory Set

/-- Integer cosine frequencies have zero mean on [0,1], except at frequency zero. -/
lemma cos_frequency (k : ℤ) :
    (∫ t in (0 : ℝ)..1, Real.cos (((k : ℝ) * Real.pi) * t)) = if k = 0 then 1 else 0 := by
  by_cases h : k = 0
  · simp [h]
  · rw [if_neg h, intervalIntegral.integral_comp_mul_left Real.cos (mul_ne_zero
        (Int.cast_ne_zero.mpr h) Real.pi_ne_zero), integral_cos]
    simp

lemma cos_half_orthogonal (i j : ℕ) :
    (∫ t in (0 : ℝ)..1, Real.cos ((i + 1 / 2 : ℝ) * Real.pi * t) *
      Real.cos ((j + 1 / 2 : ℝ) * Real.pi * t)) = if i = j then 1 / 2 else 0 := by
  have h := congrArg (fun f : ℝ → ℝ => ∫ t in (0 : ℝ)..1, f t) (funext (fun t =>
    show 2 * (Real.cos ((i + 1 / 2 : ℝ) * Real.pi * t) * Real.cos ((j + 1 / 2 : ℝ) * Real.pi * t)) =
      Real.cos (((i - j : ℤ) : ℝ) * Real.pi * t) + Real.cos (((i + j + 1 : ℤ) : ℝ) * Real.pi * t) by
      push_cast
      rw [← mul_assoc, Real.two_mul_cos_mul_cos]
      congr 2 <;> ring))
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) ..) (Continuous.intervalIntegrable (by fun_prop) ..),
    cos_frequency, cos_frequency, if_neg (by omega : (i + j + 1 : ℤ) ≠ 0)] at h
  by_cases he : i = j
  · simp [he] at h ⊢
    linarith
  · rw [if_neg (by omega : (i - j : ℤ) ≠ 0)] at h
    rw [if_neg he]
    linarith

/-- A finite cosine sum majorizes the squared sinc on every finite interval.
Orthogonality gives its integral exactly, avoiding an improper Fourier integral. -/
lemma sinc_mass {B : ℝ} (hB : 0 < B) :
    (∫ u in 0..B, Real.sinc (Real.pi * u) ^ 2) ≤ 1 / 2 := by
  obtain ⟨n, hn⟩ := exists_nat_gt B
  have hn' : (0 : ℝ) < n := hB.trans hn
  let c := fun (i : ℕ) (t : ℝ) => Real.cos ((i + 1 / 2 : ℝ) * Real.pi * t)
  let D := fun t : ℝ => ∑ i ∈ Finset.range n, c i t
  have hc (i : ℕ) : Continuous (c i) := by dsimp [c]; fun_prop
  have hD : Continuous D := continuous_finsetSum _ (fun i _ => hc i)
  have normD : (∫ t in (0 : ℝ)..1, D t ^ 2) = n / 2 := by
    have point (t : ℝ) : D t ^ 2 = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, c i t * c j t := by
      simp only [D, sq, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm
    simp_rw [point]
    rw [intervalIntegral.integral_finsetSum (s := Finset.range n)
      (f := fun i t => ∑ j ∈ Finset.range n, c i t * c j t) (fun i _ => Continuous.intervalIntegrable
      (continuous_finsetSum _ (fun j _ => (hc i).mul (hc j))) ..)]
    simp_rw [intervalIntegral.integral_finsetSum (s := Finset.range n) (f := fun j t => c _ t * c j t)
      (fun j _ => ((hc _).mul (hc j)).intervalIntegrable ..)]
    simp_rw [c, cos_half_orthogonal]
    simp [div_eq_mul_inv]
    calc
      _ = ∑ _ ∈ Finset.range n, (2 : ℝ)⁻¹ := Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_range.mp hi))
      _ = _ := by simp
  have point (t : ℝ) : Real.sinc (Real.pi * (n * t)) = Real.sinc (Real.pi * t / 2) * (D t / n) := by
    by_cases ht : t = 0
    · simp [ht, D, c, hn'.ne']
    let a := Real.pi * t
    have ha : a ≠ 0 := mul_ne_zero Real.pi_ne_zero ht
    have h := Real.sin_mul_sum_cos n a (a / 2)
    have shape (i : ℕ) : a * i + a / 2 = (i + 1 / 2 : ℝ) * Real.pi * t := by dsimp [a]; ring
    simp_rw [shape] at h
    rw [show ((n : ℝ) - 1) * a / 2 + a / 2 = n * a / 2 by ring] at h
    change Real.sin (a / 2) * D t = _ at h
    have hsin := Real.sin_two_mul (n * a / 2)
    rw [show 2 * (n * a / 2) = n * a by ring] at hsin
    rw [show Real.pi * (n * t) = n * a by dsimp [a]; ring,
      Real.sinc_of_ne_zero (mul_ne_zero hn'.ne' ha), Real.sinc_of_ne_zero (div_ne_zero ha (by norm_num))]
    change Real.sin (n * a) / (n * a) = Real.sin (a / 2) / (a / 2) * (D t / n)
    field_simp
    nlinarith [h, hsin]
  have bound := intervalIntegral.integral_mono_on (μ := volume) (zero_le_one' ℝ)
    (f := fun t : ℝ => Real.sinc (Real.pi * (n * t)) ^ 2) (g := fun t => D t ^ 2 / n ^ 2)
    (Continuous.intervalIntegrable (by fun_prop) ..) ((hD.pow 2).div_const _ |>.intervalIntegrable ..)
    (fun t _ => by
      rw [point, mul_pow, div_pow]
      exact mul_le_of_le_one_left (by positivity)
        ((sq_le_one_iff_abs_le_one _).2 (Real.abs_sinc_le_one _)))
  rw [intervalIntegral.integral_div, normD] at bound
  have scale := intervalIntegral.smul_integral_comp_mul_left (a := (0 : ℝ)) (b := 1)
    (fun u => Real.sinc (Real.pi * u) ^ 2) (n : ℝ)
  simp only [smul_eq_mul, mul_zero, mul_one] at scale
  have enlarge := intervalIntegral.integral_mono_interval (μ := volume) (le_refl (0 : ℝ)) hB.le hn.le
    (f := fun u => Real.sinc (Real.pi * u) ^ 2) (ae_of_all _ (fun _ => sq_nonneg _))
    (Continuous.intervalIntegrable (by fun_prop) ..)
  apply enlarge.trans
  rw [← scale]
  calc
    _ ≤ n * (n / 2 / (n : ℝ) ^ 2) := mul_le_mul_of_nonneg_left bound hn'.le
    _ = _ := by field_simp

lemma step_integrable (d c B : ℝ) :
    IntervalIntegrable (fun u : ℝ => if d ≤ u then c else 0) volume 0 B := by
  change IntervalIntegrable ((Ici d).indicator (fun _ => c)) volume 0 B
  exact intervalIntegrable_iff.mpr (intervalIntegrable_const.def'.indicator measurableSet_Ici)

lemma step_integral {d B : ℝ} (hd : 0 ≤ d) (hB : 0 < B) (c : ℝ) :
    (∫ u in 0..B, if d ≤ u then c else 0) = B * (c * max 0 (1 - d / B)) := by
  change (∫ u in 0..B, (Ici d).indicator (fun _ => c) u) = _
  rw [intervalIntegral.integral_of_le hB.le, setIntegral_indicator measurableSet_Ici]
  rw [setIntegral_congr_set ((ae_eq_refl _).inter Ioi_ae_eq_Ici.symm), Ioc_inter_Ioi,
    sup_eq_right.mpr hd, setIntegral_const, Real.volume_real_Ioc, smul_eq_mul]
  by_cases h : d ≤ B
  · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonneg.mpr ((div_le_one hB).2 h))]
    field_simp
  · rw [max_eq_right (by linarith), max_eq_left (sub_nonpos.mpr ((one_le_div hB).2 (le_of_not_ge h)))]
    simp

/-- Exact decomposition over ordered pairs. Every equal-height pair has weight one. -/
lemma split_pairs (Z : Finset ℂ) (m : ℂ → ℝ) (K : ℝ → ℝ) (h0 : K 0 = 1)
    (hs : ∀ u, K (-u) = K u) :
    (∑ z ∈ Z, ∑ w ∈ Z, m z * m w * K (w.im - z.im)) =
      (∑ z ∈ Z, ∑ w ∈ Z, if z.im = w.im then m z * m w else 0) +
      2 * ∑ z ∈ Z, ∑ w ∈ Z, if z.im < w.im then m z * m w * K (w.im - z.im) else 0 := by
  let P := fun z w : ℂ => if z.im < w.im then m z * m w * K (w.im - z.im) else 0
  have flip : (∑ z ∈ Z, ∑ w ∈ Z, P w z) = ∑ z ∈ Z, ∑ w ∈ Z, P z w := Finset.sum_comm
  change _ = _ + 2 * ∑ z ∈ Z, ∑ w ∈ Z, P z w
  rw [two_mul]
  nth_rw 2 [← flip]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro w hw
  rcases lt_trichotomy z.im w.im with h | h | h
  · simp [P, h, h.ne, h.asymm]
  · simp [P, h, h0]
  · have he := hs (w.im - z.im)
    rw [neg_sub] at he
    simp [P, h, h.ne', h.asymm, he, mul_comm]

lemma finite_window {a b : ℝ} (ha : 0 ≤ a) : (nontrivialZeros riemannZeta a b).Finite := by
  apply ((Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1 + b)).finite_riemannZeta_zeros).subset
  intro z hz
  obtain ⟨hz0, hr0, hr1, hi0, hi1⟩ := hz
  refine ⟨?_, hz0⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have h := Complex.norm_le_abs_re_add_abs_im z
  rw [abs_of_pos hr0, abs_of_pos (ha.trans_lt hi0)] at h
  linarith

lemma count_eq {a b : ℝ} {Z : Finset ℂ} (hZ : (Z : Set ℂ) = nontrivialZeros riemannZeta a b) :
    (N riemannZeta a b : ℝ) = ∑ z ∈ Z, (analyticOrderNatAt riemannZeta z : ℝ) := by
  unfold N Complex.zeroCountOn
  rw [← hZ, finsum_mem_coe_finset, Nat.cast_sum]

/-- Even if several distinct complex zeros share an ordinate, their cross terms
are nonnegative. The self-pairs already pay for all copies beyond the first. -/
lemma defect_le_atom (Z : Finset ℂ) (m : ℂ → ℕ) :
    (∑ z ∈ Z, (m z : ℝ)) + (∑ z ∈ Z, ((m z - 1 : ℕ) : ℝ)) ≤
    ∑ z ∈ Z, ∑ w ∈ Z, if z.im = w.im then (m z : ℝ) * m w else 0 := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro z hz
  have self := Finset.single_le_sum (s := Z)
    (f := fun w : ℂ => if z.im = w.im then (m z : ℝ) * m w else 0)
    (fun w _ => by split <;> positivity) hz
  simp only [if_true] at self
  refine le_trans ?_ self
  cases h : m z with
  | zero => simp
  | succ n =>
    simp only [Nat.succ_sub_one, Nat.cast_succ]
    nlinarith [sq_nonneg (n : ℝ)]

/-- Integrating the positive-spacing counting function produces the triangular
weight. A spacing at the endpoint contributes zero area. -/
lemma positive_triangle (Z : Finset ℂ) (m : ℂ → ℝ) {L B η W : ℝ}
    (hL : 0 < L) (hB : 0 < B)
    (hp : ∀ u ∈ Icc 0 B, (u - 1 / 2 - η) * W ≤ ∑ z ∈ Z, ∑ w ∈ Z,
      if z.im < w.im ∧ (w.im - z.im) * L ≤ u then m z * m w else 0) :
    (B - 1 - 2 * η) * W ≤ 2 * ∑ z ∈ Z, ∑ w ∈ Z, if z.im < w.im then
      m z * m w * max 0 (1 - |w.im - z.im| * L / B) else 0 := by
  let F := fun (z w : ℂ) (u : ℝ) =>
    if z.im < w.im ∧ (w.im - z.im) * L ≤ u then m z * m w else 0
  have hi (z w : ℂ) : IntervalIntegrable (F z w) volume 0 B := by
    by_cases h : z.im < w.im
    · simpa only [F, h, true_and] using step_integrable ((w.im - z.im) * L) (m z * m w) B
    · simpa only [F, h, false_and, if_false] using
        (intervalIntegrable_const (c := (0 : ℝ)) (μ := volume) (a := 0) (b := B))
  have hstep (z w : ℂ) : (∫ u in 0..B, F z w u) = B * (if z.im < w.im then
      m z * m w * max 0 (1 - |w.im - z.im| * L / B) else 0) := by
    by_cases h : z.im < w.im
    · simpa only [F, h, true_and, if_true, abs_of_pos (sub_pos.mpr h)] using
        step_integral (mul_nonneg (sub_nonneg.mpr h.le) hL.le) hB (m z * m w)
    · simp [F, h]
  have hiw (z : ℂ) : IntervalIntegrable (fun u => ∑ w ∈ Z, F z w u) volume 0 B := by
    exact (show (fun u => ∑ w ∈ Z, F z w u) = ∑ w ∈ Z, F z w from
      funext fun u => (Finset.sum_apply ..).symm) ▸ IntervalIntegrable.sum Z (fun w _ => hi z w)
  have H := intervalIntegral.integral_mono_on (μ := volume)
    (f := fun u : ℝ => (u - 1 / 2 - η) * W) (g := fun u => ∑ z ∈ Z, ∑ w ∈ Z, F z w u) hB.le
    (Continuous.intervalIntegrable (by fun_prop) ..)
    (by
      rw [show (fun u => ∑ z ∈ Z, ∑ w ∈ Z, F z w u) = ∑ z ∈ Z, (fun u => ∑ w ∈ Z, F z w u) from
        funext fun u => (Finset.sum_apply u Z (fun z u => ∑ w ∈ Z, F z w u)).symm]
      exact IntervalIntegrable.sum Z (fun z _ => hiw z)) hp
  rw [intervalIntegral.integral_finsetSum (fun z _ => hiw z)] at H
  simp_rw [intervalIntegral.integral_finsetSum (fun w _ => hi _ w), hstep, ← Finset.mul_sum] at H
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_sub
    (f := fun u : ℝ => u - 1 / 2) (g := fun _ => η) (Continuous.intervalIntegrable (by fun_prop) ..) intervalIntegrable_const,
    intervalIntegral.integral_sub (f := fun u : ℝ => u) (g := fun _ => 1 / 2) (continuous_id.intervalIntegrable ..) intervalIntegrable_const,
    integral_id, intervalIntegral.integral_const, intervalIntegral.integral_const] at H
  simp only [sub_zero, smul_eq_mul] at H
  apply le_of_mul_le_mul_left (a := B) _ hB
  linarith

lemma atom_bound (pcc : H1) (moment : H2) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ Z : Finset ℂ, (Z : Set ℂ) = nontrivialZeros riemannZeta 0 T →
      (∑ z ∈ Z, ∑ w ∈ Z, if z.im = w.im then
        (analyticOrderNatAt riemannZeta z : ℝ) * analyticOrderNatAt riemannZeta w else 0) ≤
      (1 + ε) * N riemannZeta 0 T := by
  obtain ⟨B, hB, hm⟩ := ((eventually_ge_atTop (1 : ℝ)).and (moment (ε / 2) (half_pos hε))).exists
  filter_upwards [pcc B hB (ε / 4) (by positivity), hm, eventually_gt_atTop (1 : ℝ)] with T hp ht hT
  intro Z hZ
  let m := fun z => (analyticOrderNatAt riemannZeta z : ℝ)
  let L := Real.log T / (2 * Real.pi)
  let K := fun u : ℝ => max 0 (1 - |u| * L / B)
  have hL : 0 < L := div_pos (Real.log_pos hT) (by positivity)
  have tri := positive_triangle Z m (η := ε / 4) (W := N riemannZeta 0 T) hL
    (show 0 < B by linarith) (by
      intro u hu
      by_cases h : 1 / 2 ≤ u
      · have hc := hp Z hZ u ⟨h, hu.2⟩
        dsimp only at hc
        rw [intervalIntegral.integral_sub intervalIntegrable_const
          (Continuous.intervalIntegrable (by fun_prop) ..), intervalIntegral.integral_const] at hc
        simp only [sub_zero, smul_eq_mul, mul_one] at hc
        exact (mul_le_mul_of_nonneg_right (by linarith [sinc_mass (B := u) (by linarith)] : u - 1 / 2 - ε / 4 ≤ _)
          (Nat.cast_nonneg (α := ℝ) (N riemannZeta 0 T))).trans hc
      · apply le_trans (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg _))
        apply Finset.sum_nonneg
        intro z _
        apply Finset.sum_nonneg
        intro w _
        split <;> positivity)
  have split := split_pairs Z m K (by simp [K]) (by simp [K])
  have hall := ht Z hZ
  dsimp only [K, m, L] at split tri hall
  linarith

lemma cumulative_defect (pcc : H1) (moment : H2) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ Z : Finset ℂ, (Z : Set ℂ) = nontrivialZeros riemannZeta 0 T →
      (∑ z ∈ Z, ((analyticOrderNatAt riemannZeta z - 1 : ℕ) : ℝ)) ≤ ε * N riemannZeta 0 T := by
  filter_upwards [atom_bound pcc moment ε hε] with T h
  intro Z hZ
  have hd := defect_le_atom Z (analyticOrderNatAt riemannZeta)
  rw [← count_eq hZ] at hd
  linarith [h Z hZ]

lemma dyadic_add {T : ℝ} (hT : 0 < T) :
    N riemannZeta 0 (2 * T) = N riemannZeta 0 T + N riemannZeta T (2 * T) := by
  let A := (finite_window (b := T) le_rfl).toFinset
  let D := (finite_window (b := 2 * T) hT.le).toFinset
  have ha : (A : Set ℂ) = nontrivialZeros riemannZeta 0 T := Set.Finite.coe_toFinset _
  have hd : (D : Set ℂ) = nontrivialZeros riemannZeta T (2 * T) := Set.Finite.coe_toFinset _
  have hu : ((A ∪ D : Finset ℂ) : Set ℂ) = nontrivialZeros riemannZeta 0 (2 * T) := by
    rw [Finset.coe_union, ha, hd]
    ext z
    simp only [Set.mem_union, nontrivialZeros, Set.mem_ofPred_eq]
    constructor
    · rintro (⟨hz, h₀, h₁, h₂, h₃⟩ | ⟨hz, h₀, h₁, h₂, h₃⟩)
      · exact ⟨hz, h₀, h₁, h₂, by linarith⟩
      · exact ⟨hz, h₀, h₁, hT.trans h₂, h₃⟩
    · rintro ⟨hz, h₀, h₁, h₂, h₃⟩
      rcases le_or_gt z.im T with h | h
      · exact Or.inl ⟨hz, h₀, h₁, h₂, h⟩
      · exact Or.inr ⟨hz, h₀, h₁, h, h₃⟩
  have hdis : Disjoint A D := by
    apply Finset.disjoint_left.mpr
    intro z za zd
    have h₁ : z ∈ nontrivialZeros riemannZeta 0 T := ha ▸ (show z ∈ (A : Set ℂ) from za)
    have h₂ : z ∈ nontrivialZeros riemannZeta T (2 * T) := hd ▸ (show z ∈ (D : Set ℂ) from zd)
    exact h₂.2.2.2.1.not_ge h₁.2.2.2.2
  unfold N Complex.zeroCountOn
  rw [← hu, ← ha, ← hd, finsum_mem_coe_finset, finsum_mem_coe_finset,
    finsum_mem_coe_finset, Finset.sum_union hdis]

/-- A coarse growth ratio suffices to transfer a vanishing relative defect. -/
lemma dyadic_growth (rvm : H3) :
    ∀ᶠ T : ℝ in atTop, (N riemannZeta 0 (2 * T) : ℝ) ≤ 4 * N riemannZeta T (2 * T) := by
  let M := fun t : ℝ => t * (Real.log t / (2 * Real.pi))
  have limits : ∀ᶠ t : ℝ in atTop, 7 / 8 < (N riemannZeta 0 t : ℝ) / M t ∧
      (N riemannZeta 0 t : ℝ) / M t < 5 / 4 :=
    (rvm.eventually_const_lt (by norm_num)).and (rvm.eventually_lt_const (by norm_num))
  have dbl : Tendsto (fun T : ℝ => 2 * T) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  filter_upwards [limits, dbl.eventually limits, eventually_gt_atTop (1 : ℝ)] with T h₁ h₂ hT
  have ht : 0 < T := by linarith
  have ht₂ : 1 < 2 * T := by linarith
  have pos : 0 < M T := mul_pos ht (div_pos (Real.log_pos hT) (by positivity))
  have pos₂ : 0 < M (2 * T) := mul_pos (by positivity) (div_pos (Real.log_pos ht₂) (by positivity))
  have grow : 2 * M T ≤ M (2 * T) := by
    dsimp [M]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (Real.log_le_log ht (by linarith)) (by positivity)) ht.le)
      (by norm_num)
  have split : (N riemannZeta 0 (2 * T) : ℝ) =
      N riemannZeta 0 T + N riemannZeta T (2 * T) := by exact_mod_cast dyadic_add ht
  linarith [(div_lt_iff₀ pos).mp h₁.2, (lt_div_iff₀ pos₂).mp h₂.1]

lemma dyadic_defect (pcc : H1) (moment : H2) (rvm : H3) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, (N riemannZeta T (2 * T) : ℝ) - Nd riemannZeta T (2 * T) ≤
      ε * N riemannZeta T (2 * T) := by
  have dbl : Tendsto (fun T : ℝ => 2 * T) atTop atTop := tendsto_id.const_mul_atTop (by norm_num)
  filter_upwards [dbl.eventually (cumulative_defect pcc moment (ε / 4) (by positivity)),
    dyadic_growth rvm, eventually_gt_atTop (0 : ℝ)] with T hc hg hT
  let Z := (finite_window (b := 2 * T) (le_refl (0 : ℝ))).toFinset
  let D := (finite_window (b := 2 * T) hT.le).toFinset
  have hZ : (Z : Set ℂ) = nontrivialZeros riemannZeta 0 (2 * T) := Set.Finite.coe_toFinset _
  have hD : (D : Set ℂ) = nontrivialZeros riemannZeta T (2 * T) := Set.Finite.coe_toFinset _
  have sub : D ⊆ Z := by
    intro z hz
    have h : z ∈ nontrivialZeros riemannZeta T (2 * T) := hD ▸ (show z ∈ (D : Set ℂ) from hz)
    change z ∈ (Z : Set ℂ)
    rw [hZ]
    exact ⟨h.1, h.2.1, h.2.2.1, hT.trans h.2.2.2.1, h.2.2.2.2⟩
  let m := analyticOrderNatAt riemannZeta
  have mono := Finset.sum_le_sum_of_subset_of_nonneg (f := fun z => ((m z - 1 : ℕ) : ℝ))
    sub (fun _ _ _ => Nat.cast_nonneg _)
  have hcount : (N riemannZeta T (2 * T) : ℝ) ≤ (D.card : ℝ) + ∑ z ∈ D, ((m z - 1 : ℕ) : ℝ) := by
    rw [count_eq hD]
    calc
      _ ≤ ∑ z ∈ D, ((1 : ℝ) + ((m z - 1 : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum
        intro z _
        change (m z : ℝ) ≤ _
        exact_mod_cast (show m z ≤ 1 + (m z - 1) by omega)
      _ = _ := by simp [Finset.sum_add_distrib]
  have hd : Nd riemannZeta T (2 * T) = D.card := by simp [Nd, ← hD]
  have hcum := hc Z hZ
  have hscale := mul_le_mul_of_nonneg_left hg (show 0 ≤ ε / 4 by positivity)
  dsimp only [m] at mono hcount
  rw [hd]
  linarith

theorem main : H1 → H2 → H3 → type_of% @riemannZeta.distinct_prop_one_hundred := by
  intro pcc moment rvm
  let n := fun T : ℝ => (N riemannZeta T (2 * T) : ℝ)
  let d := fun T : ℝ => (Nd riemannZeta T (2 * T) : ℝ)
  let o := fun T => max 0 (n T - d T) / n T
  have hn (T : ℝ) : 0 ≤ n T := Nat.cast_nonneg _
  have hd (T : ℝ) : 0 ≤ d T := Nat.cast_nonneg _
  refine ⟨o, (Asymptotics.isLittleO_one_iff ℝ).2 ?_, ?_⟩
  · apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [dyadic_defect pcc moment rvm (half_pos hε)] with T ht
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (le_max_left _ _) (hn T))]
    rcases (hn T).eq_or_lt with hz | hz
    · simp [← hz, hε]
    · apply lt_of_le_of_lt ((div_le_iff₀ hz).2 (max_le (by positivity) ht)) (half_lt_self hε)
  · intro T _
    change (1 - o T) * n T ≤ d T
    rcases (hn T).eq_or_lt with hz | hz
    · simp [← hz, hd T]
    · dsimp only [o]
      rw [sub_mul, one_mul, div_mul_cancel₀ _ hz.ne']
      linarith [le_max_right 0 (n T - d T)]

end OMA.R_riemannZeta_distinct_prop_one_hundred_R1
