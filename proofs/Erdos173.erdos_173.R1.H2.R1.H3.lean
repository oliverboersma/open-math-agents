import OMAReductions.R_Erdos173_erdos_173_R1_H2_R1

/-! Measurable circle exclusion for two equilateral scales.
Port of the public proof by Jacob Parish (Plasma AI), plasma-ai/erdos-173 at
4a368a652753, including the project's adaptation of OpenAI's plane-coloring definitions.
Both sources are used under Apache-2.0. -/
-- Credit: @marcusbuffett


-- Copied from openai/math at adc7f124 (same path under lean/) and modified; see OAI/README.md.




namespace OAI

namespace EuclideanFiveColor

def ProperColoring (k : ℕ) (c : ℂ → Fin k) : Prop :=
  ∀ x y : ℂ, ‖x - y‖ = 1 → c x ≠ c y

end EuclideanFiveColor

noncomputable section
open MeasureTheory
namespace EuclideanFiveColor
instance anglePeriodPositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
abbrev Angles := AddCircle (2*Real.pi)
def angularMeasure : Measure Angles := AddCircle.haarAddCircle
def direction (t : Angles) : ℂ := AddCircle.toCircle t
instance : IsProbabilityMeasure angularMeasure := inferInstanceAs (IsProbabilityMeasure (AddCircle.haarAddCircle (T := 2*Real.pi)))
instance : angularMeasure.IsAddHaarMeasure := inferInstanceAs (AddCircle.haarAddCircle (T := 2*Real.pi)).IsAddHaarMeasure
lemma direction_continuous : Continuous direction := continuous_subtype_val.comp AddCircle.continuous_toCircle
@[simp] lemma direction_norm (t : Angles) : ‖direction t‖ = 1 := Circle.norm_coe _
@[simp] lemma direction_real (t : ℝ) : direction (t : Angles) = (Circle.exp t : ℂ) := by
  simp [direction,AddCircle.toCircle_apply_mk,Real.pi_ne_zero]
/-- Exactly the manuscript weak measurable condition, using normalized Haar angular measure.
A function is understood up to a plane-null set; no regularity is imposed on a proper coloring. -/
def WeakColoring (k : ℕ) (c : ℂ → Fin k) : Prop :=
  AEMeasurable c (volume : Measure ℂ) ∧ ∀ᵐ p ∂(volume : Measure ℂ).prod angularMeasure,
    c p.1 ≠ c (p.1+direction p.2)

end EuclideanFiveColor
end

end OAI




/-
# Colorings of the complex plane and copies of triangles

The proof works in `ℂ`. A triangle is given by a template `(0, a, b)` with
`a b : ℂ`, and its orientation-preserving copies are `(p, p + u a, p + u b)` for
`p : ℂ` and `‖u‖ = 1`. A two-coloring `c : ℂ → Fin 2` *avoids* the template when
no copy is monochromatic, and *weakly avoids* it when the monochromatic copies
form a null set for area times normalized arc length, the angular measure of
`OAI.EuclideanFiveColor.WeakColoring`.

The equilateral triangle of side `r` is the template `(0, r, r ζ)`, with
`ζ = e^{iπ/3}`. The numbers `ζ`, `1 - ζ = ζ̄` and `ζ - 1` lie on the unit circle, and
directions add angles: `e^{i(s+t)} = e^{is} e^{it}`.
-/


noncomputable section

namespace Port173

open MeasureTheory OAI.EuclideanFiveColor

/-- The sixth root of unity `ζ = e^{iπ/3} = 1/2 + (√3/2) i`. -/
def ζ : ℂ := ⟨1 / 2, √3 / 2⟩

/-- `ζ` lies on the unit circle. -/
lemma norm_ζ : ‖ζ‖ = 1 := by
  rw [Complex.norm_def, Real.sqrt_eq_one]
  simp [ζ, Complex.normSq]
  ring_nf
  norm_num

/-- `ζ̄ = 1 - ζ` lies on the unit circle. -/
lemma norm_one_sub_ζ : ‖1 - ζ‖ = 1 := by
  rw [Complex.norm_def, Real.sqrt_eq_one]
  simp [ζ, Complex.normSq]
  ring_nf
  norm_num

/-- `-ζ̄ = ζ - 1` lies on the unit circle. -/
lemma norm_ζ_sub_one : ‖ζ - 1‖ = 1 := by
  rw [norm_sub_rev, norm_one_sub_ζ]

/-- Directions add angles: `e^{i(s+t)} = e^{is} e^{it}`. -/
lemma direction_add (s t : Angles) : direction (s + t) = direction s * direction t := by
  simp [direction, AddCircle.toCircle_add]

/-- The copy `(p, p + u a, p + u b)` of the template `(0, a, b)` is monochromatic. -/
def MonoCopy (c : ℂ → Fin 2) (a b p u : ℂ) : Prop :=
  c (p + u * a) = c p ∧ c (p + u * b) = c p

/-- No orientation-preserving copy of the template `(0, a, b)` is monochromatic. -/
def Avoids (c : ℂ → Fin 2) (a b : ℂ) : Prop :=
  ∀ p u : ℂ, ‖u‖ = 1 → ¬ MonoCopy c a b p u

/-- Almost no orientation-preserving copy of the template `(0, a, b)` is
monochromatic, for area times normalized arc length. -/
def WeaklyAvoids (c : ℂ → Fin 2) (a b : ℂ) : Prop :=
  ∀ᵐ q ∂(volume : Measure ℂ).prod angularMeasure, ¬ MonoCopy c a b q.1 (direction q.2)

/-- No equilateral triangle of side `r` is monochromatic. -/
def AvoidsEq (c : ℂ → Fin 2) (r : ℝ) : Prop :=
  Avoids c r (r * ζ)

/-- Almost no equilateral triangle of side `r` is monochromatic. -/
def WeaklyAvoidsEq (c : ℂ → Fin 2) (r : ℝ) : Prop :=
  WeaklyAvoids c r (r * ζ)

end Port173

end






/-
# Density points of a measurable two-coloring

A set `K ⊆ ℂ` has *density zero* at `p` when `|K ∩ B(p, ρ)| = o(ρ²)` as `ρ → 0`.
For a two-coloring `c`, the point `p` is a density point of the class `i` when the
other class has density zero there. The *boundary* of `c` is the set of points at
which neither class has density zero; at such a point both classes have positive
upper density.

The density-zero condition can be tested along the radii `1/(k+1)`, because the
measure of `K ∩ B(p, ρ)` is monotone in `ρ`, so the set of points where `K` has
density zero is measurable. Lebesgue's density theorem makes the boundary null.
A coloring that weakly avoids some triangle has two classes of positive area:
if one class were null, almost every copy of the triangle would lie in the
other.
-/


noncomputable section

namespace Port173

open MeasureTheory Metric Set Filter Topology OAI.EuclideanFiveColor

/-- The set `K` has density zero at `p`: `|K ∩ B(p, ρ)| = o(ρ²)` as `ρ → 0`. -/
def DensityZero (K : Set ℂ) (p : ℂ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ ρ, 0 < ρ → ρ < δ →
    volume (K ∩ closedBall p ρ) ≤ ENNReal.ofReal (ε * ρ ^ 2)

/-- The boundary of a two-coloring: the points at which neither class has density
zero. -/
def boundary (c : ℂ → Fin 2) : Set ℂ :=
  {p | ∀ i, ¬ DensityZero {z | c z = i} p}

/-- The measure of `K ∩ B(p, ρ)` is measurable in `p`. -/
lemma measurable_measure_inter_closedBall {K : Set ℂ} (hK : MeasurableSet K) (ρ : ℝ) :
    Measurable fun p => volume (K ∩ closedBall p ρ) := by
  have hs : MeasurableSet {q : ℂ × ℂ | q.2 ∈ K ∧ dist q.2 q.1 ≤ ρ} :=
    (hK.preimage measurable_snd).inter
      (measurableSet_le (continuous_snd.dist continuous_fst).measurable measurable_const)
  exact measurable_measure_prodMk_left hs

/-- Density zero along the radii `1/(k+1)` implies density zero. -/
lemma densityZero_of_seq {K : Set ℂ} {p : ℂ}
    (h : ∀ n : ℕ, ∃ m : ℕ, ∀ k, m ≤ k →
      volume (K ∩ closedBall p (1 / (k + 1))) ≤
        ENNReal.ofReal (1 / (n + 1) * (1 / (k + 1)) ^ 2)) :
    DensityZero K p := by
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (by positivity : 0 < ε / 4)
  obtain ⟨m, hm⟩ := h n
  refine ⟨1 / (m + 1), by positivity, fun ρ hρ hρδ => ?_⟩
  have hinv : (m + 1 : ℝ) < ρ⁻¹ := by
    rw [lt_inv_comm₀ (by positivity) hρ]; simpa using hρδ
  set j := ⌊ρ⁻¹⌋₊ with hj
  have hj1 : (m + 1 : ℝ) ≤ j := by
    have : m + 1 ≤ j := Nat.le_floor (by push_cast; linarith)
    exact_mod_cast this
  have hjle : (j : ℝ) ≤ ρ⁻¹ := Nat.floor_le (by positivity)
  have hjlt : ρ⁻¹ < j + 1 := Nat.lt_floor_add_one _
  have hjpos : (1 : ℝ) ≤ j := by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hjnat : 1 ≤ j := by exact_mod_cast hjpos
  have hk : m ≤ j - 1 := by
    have : m + 1 ≤ j := by exact_mod_cast hj1
    omega
  have hcast : ((j - 1 : ℕ) : ℝ) + 1 = j := by
    rw [Nat.cast_sub hjnat]; push_cast; ring
  have key := hm (j - 1) hk
  rw [hcast] at key
  have hρj : ρ ≤ 1 / j := by
    rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hjle hρ.le
    rw [mul_inv_cancel₀ hρ.ne'] at this
    linarith [mul_comm ρ (j : ℝ)]
  have hj2 : 1 / (j : ℝ) < 2 * ρ := by
    rw [div_lt_iff₀ (by positivity)]
    have h1 : 1 < ρ * (j + 1) := by
      have := mul_lt_mul_of_pos_left hjlt hρ
      rwa [mul_inv_cancel₀ hρ.ne'] at this
    nlinarith
  calc volume (K ∩ closedBall p ρ)
      ≤ volume (K ∩ closedBall p (1 / j)) := by
        gcongr
    _ ≤ ENNReal.ofReal (1 / (n + 1) * (1 / j) ^ 2) := key
    _ ≤ ENNReal.ofReal (ε * ρ ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        have h0 : 0 ≤ 1 / (j : ℝ) := by positivity
        have hsq : (1 / (j : ℝ)) ^ 2 ≤ 4 * ρ ^ 2 := by nlinarith
        have hn' : (1 : ℝ) / (n + 1) ≤ ε / 4 := hn.le
        calc 1 / ((n : ℝ) + 1) * (1 / j) ^ 2 ≤ ε / 4 * (4 * ρ ^ 2) := by
              gcongr
          _ = ε * ρ ^ 2 := by ring

/-- The points at which a measurable set has density zero form a measurable set. -/
theorem measurableSet_densityZero {K : Set ℂ} (hK : MeasurableSet K) :
    MeasurableSet {p | DensityZero K p} := by
  have heq : {p | DensityZero K p} = ⋂ n : ℕ, ⋃ m : ℕ, ⋂ k : ℕ, ⋂ (_ : m ≤ k),
      {p | volume (K ∩ closedBall p (1 / (k + 1))) ≤
        ENNReal.ofReal (1 / (n + 1) * (1 / (k + 1)) ^ 2)} := by
    ext p
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion]
    constructor
    · intro h n
      obtain ⟨δ, hδ, hp⟩ := h (1 / (n + 1)) (by positivity)
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
      refine ⟨m, fun k hk => hp _ (by positivity) (lt_of_le_of_lt ?_ hm)⟩
      gcongr
    · exact densityZero_of_seq
  rw [heq]
  refine MeasurableSet.iInter fun n => MeasurableSet.iUnion fun m =>
    MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ => ?_
  exact measurableSet_le (measurable_measure_inter_closedBall hK _) measurable_const

/-- Lebesgue's density theorem: a measurable set has density zero at almost every
point outside it. -/
theorem ae_densityZero {K : Set ℂ} (hK : MeasurableSet K) :
    ∀ᵐ p, p ∉ K → DensityZero K p := by
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet volume hK]
    with p hp hpK
  rw [indicator_of_notMem hpK] at hp
  intro ε hε
  have hev := (ENNReal.tendsto_nhds_zero.1 hp) (ENNReal.ofReal (ε / 4)) (by positivity)
  obtain ⟨δ, hδ, hP⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.1 hev
  refine ⟨δ, hδ, fun ρ hρ hρδ => ?_⟩
  have hball : volume (closedBall p ρ) = ENNReal.ofReal (Real.pi * ρ ^ 2) := by
    rw [Complex.volume_closedBall, ENNReal.ofReal_mul Real.pi_pos.le,
      ENNReal.ofReal_pow hρ.le, mul_comm]
    congr 1
    rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]
  have h1 := hP ⟨hρ, hρδ⟩
  rw [ENNReal.div_le_iff
    (by rw [hball]; simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity)
    (by rw [hball]; simp)] at h1
  refine h1.trans ?_
  rw [hball, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have := Real.pi_le_four
  have : 0 ≤ ε * ρ ^ 2 := by positivity
  nlinarith

/-- The boundary of a measurable two-coloring is measurable. -/
theorem measurableSet_boundary {c : ℂ → Fin 2} (hc : Measurable c) :
    MeasurableSet (boundary c) := by
  have : boundary c = ⋂ i, {p | DensityZero {z | c z = i} p}ᶜ := by
    ext p; simp [boundary]
  rw [this]
  exact MeasurableSet.iInter fun i =>
    (measurableSet_densityZero (measurableSet_eq_fun hc measurable_const)).compl

/-- The boundary of a measurable two-coloring is null. -/
theorem volume_boundary {c : ℂ → Fin 2} (hc : Measurable c) : volume (boundary c) = 0 := by
  have h : ∀ᵐ p, ∀ i, p ∉ {z | c z = i} → DensityZero {z | c z = i} p :=
    ae_all_iff.2 fun i => ae_densityZero (measurableSet_eq_fun hc measurable_const)
  refine measure_mono_null (fun p hp => ?_) (ae_iff.1 h)
  intro hall
  refine hp (c p + 1) (hall _ ?_)
  change c p ≠ c p + 1
  generalize c p = a
  fin_cases a <;> decide

/-- Translating a null set along a continuous family of directions gives a null set
of copies. -/
lemma ae_prod_add_notMem {N : Set ℂ} (hN : MeasurableSet N) (hN0 : volume N = 0)
    {w : Angles → ℂ} (hw : Continuous w) :
    ∀ᵐ q ∂(volume : Measure ℂ).prod angularMeasure, q.1 + w q.2 ∉ N := by
  rw [ae_iff]
  simp only [not_not]
  have hm : MeasurableSet {q : ℂ × Angles | q.1 + w q.2 ∈ N} :=
    hN.preimage (by fun_prop)
  rw [Measure.prod_apply_symm hm]
  refine (lintegral_congr fun t => ?_).trans lintegral_zero
  change volume ((· + w t) ⁻¹' N) = 0
  rw [measure_preimage_add_right]
  exact hN0

/-- If a measurable two-coloring weakly avoids a triangle, both classes have
positive area. -/
theorem volume_ne_zero_of_weaklyAvoids {c : ℂ → Fin 2} (hc : Measurable c) {a b : ℂ}
    (h : WeaklyAvoids c a b) (i : Fin 2) : volume {z | c z = i} ≠ 0 := by
  intro h0
  have hN : MeasurableSet {z | c z = i} := measurableSet_eq_fun hc measurable_const
  have h1 := ae_prod_add_notMem hN h0 (w := fun _ => 0) continuous_const
  have h2 := ae_prod_add_notMem hN h0 (w := fun t => direction t * a)
    (direction_continuous.mul continuous_const)
  have h3 := ae_prod_add_notMem hN h0 (w := fun t => direction t * b)
    (direction_continuous.mul continuous_const)
  have hfalse : ∀ᵐ _q ∂(volume : Measure ℂ).prod angularMeasure, False := by
    filter_upwards [h, h1, h2, h3] with q hq hq1 hq2 hq3
    apply hq
    simp only [add_zero] at hq1 hq2 hq3
    constructor
    · generalize c (q.1 + direction q.2 * a) = x at hq2
      generalize c q.1 = y at hq1
      fin_cases i <;> fin_cases x <;> fin_cases y <;> simp_all
    · generalize c (q.1 + direction q.2 * b) = x at hq3
      generalize c q.1 = y at hq1
      fin_cases i <;> fin_cases x <;> fin_cases y <;> simp_all
  rw [ae_iff] at hfalse
  simp only [not_false_eq_true] at hfalse
  have huniv : (volume.prod angularMeasure) (univ : Set (ℂ × Angles)) = 0 := hfalse
  rw [← univ_prod_univ, Measure.prod_prod] at huniv
  simp at huniv

end Port173

end




/-
# The apex lemma

Let a measurable two-coloring `c` weakly avoid the triangle `(0, a, b)`, let the
class `i` have positive upper density at `p`, and let `u₀` be a direction. Then
`p + u₀ a` and `p + u₀ b` are not both density points of the class `i`.

Otherwise take a radius `h` at which `|K ∩ B(p, h)| > ε h²`, where `K` is the
class `i`, and the arc `T` of directions within `h / L` of `u₀`, with
`L = |a| + |b| + 1`. For `q ∈ B(p, h)` and `u ∈ T` the vertex `q + u a` lies in
`B(p + u₀ a, 2h)`, where the other class has measure `o(h²)`; so the copies
`(q, u)` with `q ∈ K ∩ B(p, h)` and `u ∈ T` whose vertex `q + u a` or `q + u b`
leaves `K` have measure `o(h²) |T|`, while all of them have measure at least
`ε h² |T|`. The remaining copies are monochromatic and have positive measure,
contrary to weak avoidance.
-/


noncomputable section

namespace Port173

open MeasureTheory Metric Set Filter OAI.EuclideanFiveColor

/-- The apex lemma: if `c` weakly avoids `(0, a, b)` and the class `i` has
positive upper density at `p`, then for no direction `u₀` are both `p + u₀ a` and
`p + u₀ b` density points of the class `i`. -/
theorem apex_density {c : ℂ → Fin 2} (hc : Measurable c) {a b : ℂ} (h : WeaklyAvoids c a b)
    {i : Fin 2} {p : ℂ} (hp : ¬ DensityZero {z | c z = i} p) (t₀ : Angles)
    (ha : DensityZero {z | c z ≠ i} (p + direction t₀ * a))
    (hb : DensityZero {z | c z ≠ i} (p + direction t₀ * b)) : False := by
  set K : Set ℂ := {z | c z = i} with hK
  set L : ℝ := ‖a‖ + ‖b‖ + 1 with hL
  have hL0 : 0 < L := by rw [hL]; positivity
  unfold DensityZero at hp
  push Not at hp
  obtain ⟨ε, hε, hp⟩ := hp
  obtain ⟨δa, hδa, ha⟩ := ha (ε / 16) (by positivity)
  obtain ⟨δb, hδb, hb⟩ := hb (ε / 16) (by positivity)
  obtain ⟨r, hr, hrδ, hgood⟩ := hp (min δa δb / 2) (by positivity)
  have h2a : 2 * r < δa := by have := min_le_left δa δb; linarith
  have h2b : 2 * r < δb := by have := min_le_right δa δb; linarith
  set T : Set Angles := {t | dist (direction t) (direction t₀) < r / L} with hT
  have hTo : IsOpen T :=
    isOpen_lt (direction_continuous.dist continuous_const) continuous_const
  have hTpos : angularMeasure T ≠ 0 :=
    (hTo.measure_pos _ ⟨t₀, by simp only [hT, mem_ofPred_eq, dist_self]; positivity⟩).ne'
  have hTfin : angularMeasure T ≠ ⊤ := measure_ne_top _ _
  -- the copies whose vertex `q + u w` leaves the class `i`
  have hbad : ∀ w : ℂ, ‖w‖ ≤ L → ∀ C,
      volume ({z | c z ≠ i} ∩ closedBall (p + direction t₀ * w) (2 * r)) ≤ C →
      (volume.prod angularMeasure)
        {q : ℂ × Angles | q.1 ∈ closedBall p r ∧ q.2 ∈ T ∧ c (q.1 + direction q.2 * w) ≠ i}
        ≤ C * angularMeasure T := by
    intro w hw C hC
    have hm : MeasurableSet {q : ℂ × Angles |
        q.1 ∈ closedBall p r ∧ q.2 ∈ T ∧ c (q.1 + direction q.2 * w) ≠ i} := by
      refine (measurableSet_closedBall.preimage measurable_fst).inter
        ((hTo.measurableSet.preimage measurable_snd).inter ?_)
      refine (measurableSet_eq_fun (hc.comp ?_) measurable_const).compl
      exact (continuous_fst.add
        ((direction_continuous.comp continuous_snd).mul continuous_const)).measurable
    rw [Measure.prod_apply_symm hm, ← lintegral_indicator_const hTo.measurableSet]
    refine lintegral_mono fun t => ?_
    by_cases ht : t ∈ T
    · rw [indicator_of_mem ht]
      refine le_trans (measure_mono (t := (· + direction t * w) ⁻¹'
        ({z | c z ≠ i} ∩ closedBall (p + direction t₀ * w) (2 * r))) ?_) ?_
      · rintro x ⟨hx, -, hcx⟩
        refine ⟨hcx, ?_⟩
        rw [mem_closedBall] at hx ⊢
        have htd : dist (direction t) (direction t₀) < r / L := ht
        calc dist (x + direction t * w) (p + direction t₀ * w)
            ≤ dist x p + dist (direction t * w) (direction t₀ * w) := dist_add_add_le _ _ _ _
          _ ≤ r + r := by
            gcongr
            rw [dist_eq_norm, ← sub_mul, norm_mul, ← dist_eq_norm]
            calc dist (direction t) (direction t₀) * ‖w‖ ≤ r / L * L := by
                  gcongr
              _ = r := by field_simp
          _ = 2 * r := by ring
      · rw [measure_preimage_add_right]
        exact hC
    · rw [indicator_of_notMem ht]
      exact le_of_eq (measure_mono_null (fun x hx => (ht hx.2.1).elim) measure_empty)
  have hmono : (volume.prod angularMeasure)
      {q : ℂ × Angles | MonoCopy c a b q.1 (direction q.2)} = 0 := by
    simpa using ae_iff.1 h
  set C := ENNReal.ofReal (ε / 16 * (2 * r) ^ 2) with hC
  have hA := hbad a (by rw [hL]; linarith [norm_nonneg b]) C (ha (2 * r) (by positivity) h2a)
  have hB := hbad b (by rw [hL]; linarith [norm_nonneg a]) C (hb (2 * r) (by positivity) h2b)
  have hsub : (K ∩ closedBall p r) ×ˢ T ⊆
      {q : ℂ × Angles | MonoCopy c a b q.1 (direction q.2)} ∪
        {q : ℂ × Angles | q.1 ∈ closedBall p r ∧ q.2 ∈ T ∧ c (q.1 + direction q.2 * a) ≠ i} ∪
        {q : ℂ × Angles | q.1 ∈ closedBall p r ∧ q.2 ∈ T ∧ c (q.1 + direction q.2 * b) ≠ i} := by
    rintro ⟨x, t⟩ ⟨⟨hxK, hxr⟩, ht⟩
    by_contra hq
    simp only [mem_union, mem_ofPred_eq, not_or, not_and, not_not] at hq
    obtain ⟨⟨hm, hqa⟩, hqb⟩ := hq
    have hxK' : c x = i := hxK
    exact hm ⟨(hqa hxr ht).trans hxK'.symm, (hqb hxr ht).trans hxK'.symm⟩
  have hle : volume (K ∩ closedBall p r) * angularMeasure T ≤ (C + C) * angularMeasure T := by
    rw [← Measure.prod_prod, add_mul]
    calc _ ≤ _ := measure_mono hsub
      _ ≤ _ := measure_union_le _ _
      _ ≤ _ := add_le_add_left (measure_union_le _ _) _
      _ ≤ 0 + C * angularMeasure T + C * angularMeasure T := by
        rw [hmono]
        gcongr
      _ = _ := by rw [zero_add]
  rw [ENNReal.mul_le_mul_iff_left hTpos hTfin] at hle
  have hCC : C + C < ENNReal.ofReal (ε * r ^ 2) := by
    rw [hC, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    nlinarith [sq_nonneg r, mul_pos hε (pow_pos hr 2)]
  exact absurd (hle.trans_lt (hCC.trans hgood)) (lt_irrefl _)

end Port173

end








/-
# A set with density points of both kinds has a boundary point

Let `A ⊆ ℂ` be measurable, with a point `a` at which `Aᶜ` has density zero and a
point `b` at which `A` has density zero. Then at some point `z` neither `A` nor
`Aᶜ` has density zero.

For a small side `s`, the axis-parallel square of side `s` at `a` is mostly in
`A` and the one at `b` mostly in `Aᶜ`. The measure of `A` in a square of fixed
side is continuous in its position, so some square between them is balanced:
half of it lies in `A`. The four half-side quadrants of a balanced square
average one half, so one of them is at least half in `A` and one at least half
in `Aᶜ`; sliding a half-side square between them inside the parent gives a
balanced half-side subsquare. The nested balanced squares shrink to a point
`z`, and each lies in the disk of radius twice its side about `z`, so both `A`
and `Aᶜ` have measure at least `ρ² / 8` in disks `B(z, ρ)` of arbitrarily small
radius.
-/


noncomputable section

namespace Port173

open MeasureTheory Metric Set Filter Topology
open scoped symmDiff

/-- The closed axis-parallel square with lower-left corner `p` and side `s`. -/
def square (p : ℂ) (s : ℝ) : Set ℂ :=
  {z | p.re ≤ z.re ∧ z.re ≤ p.re + s ∧ p.im ≤ z.im ∧ z.im ≤ p.im + s}

/-- A square of nonnegative side contains its corner. -/
lemma mem_square_self (p : ℂ) {s : ℝ} (hs : 0 ≤ s) : p ∈ square p s :=
  ⟨le_rfl, by linarith, le_rfl, by linarith⟩

/-- The square is a product of intervals in the coordinates `(re, im)`. -/
lemma square_eq_preimage (p : ℂ) (s : ℝ) :
    square p s = Complex.measurableEquivRealProd ⁻¹'
      (Icc p.re (p.re + s) ×ˢ Icc p.im (p.im + s)) := by
  ext z
  simp [square, Complex.measurableEquivRealProd]
  tauto

/-- A square of side `s` has area `s²`. -/
lemma volume_square (p : ℂ) {s : ℝ} (hs : 0 ≤ s) :
    volume (square p s) = ENNReal.ofReal (s ^ 2) := by
  rw [square_eq_preimage, Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_mul (by linarith)]
  congr 1
  ring

/-- Squares are closed. -/
lemma isClosed_square (p : ℂ) (s : ℝ) : IsClosed (square p s) :=
  (isClosed_le continuous_const Complex.continuous_re).inter
    ((isClosed_le Complex.continuous_re continuous_const).inter
      ((isClosed_le continuous_const Complex.continuous_im).inter
        (isClosed_le Complex.continuous_im continuous_const)))

/-- Squares are convex. -/
lemma convex_square (p : ℂ) (s : ℝ) : Convex ℝ (square p s) := by
  have : square p s = Complex.reLm ⁻¹' Icc p.re (p.re + s) ∩
      Complex.imLm ⁻¹' Icc p.im (p.im + s) := by
    ext z
    simp [square]
    tauto
  rw [this]
  exact ((convex_Icc _ _).linear_preimage _).inter ((convex_Icc _ _).linear_preimage _)

/-- A square containing `z` lies in the closed disk about `z` of radius twice its
side. -/
lemma square_subset_closedBall {p z : ℂ} {s : ℝ} (hz : z ∈ square p s) :
    square p s ⊆ closedBall z (2 * s) := by
  rintro w ⟨h1, h2, h3, h4⟩
  obtain ⟨g1, g2, g3, g4⟩ := hz
  rw [mem_closedBall, dist_eq_norm]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [Complex.sub_re, Complex.sub_im]
  have hre : |w.re - z.re| ≤ s := abs_le.2 ⟨by linarith, by linarith⟩
  have him : |w.im - z.im| ≤ s := abs_le.2 ⟨by linarith, by linarith⟩
  linarith

/-- Squares are compact. -/
lemma isCompact_square (p : ℂ) (s : ℝ) : IsCompact (square p s) := by
  rcases (square p s).eq_empty_or_nonempty with he | ⟨z, hz⟩
  · rw [he]
    exact isCompact_empty
  · exact Metric.isCompact_of_isClosed_isBounded (isClosed_square p s)
      (isBounded_closedBall.subset (square_subset_closedBall hz))

/-- Squares have finite area. -/
lemma volume_square_ne_top (p : ℂ) (s : ℝ) : volume (square p s) ≠ ⊤ :=
  (isCompact_square p s).measure_lt_top.ne

/-- The part of any set inside a square has finite area. -/
lemma volume_inter_square_ne_top (K : Set ℂ) (p : ℂ) (s : ℝ) :
    volume (K ∩ square p s) ≠ ⊤ :=
  ne_top_of_le_ne_top (volume_square_ne_top p s) (measure_mono inter_subset_right)

/-- The square at `p` is the translate by `p` of the square at `0`. -/
lemma square_eq_preimage_sub (p : ℂ) (s : ℝ) :
    square p s = (fun z => z - p) ⁻¹' square 0 s := by
  ext z
  simp only [square, mem_ofPred_eq, mem_preimage, Complex.sub_re, Complex.sub_im,
    Complex.zero_re, Complex.zero_im, zero_add]
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- Translating a square moves it continuously in measure. -/
lemma tendsto_volume_square_symmDiff (s : ℝ) (p₀ : ℂ) :
    Tendsto (fun p => volume (square p s ∆ square p₀ s)) (𝓝 p₀) (𝓝 0) := by
  let f : ℂ → C(ℂ, ℂ) := fun p => ⟨fun z => z - p, by fun_prop⟩
  have hf : Continuous f :=
    ContinuousMap.continuous_of_continuous_uncurry _ (continuous_snd.sub continuous_fst)
  have h := tendsto_measure_symmDiff_preimage_nhds_zero (μ := volume) (ν := volume)
    (s := square 0 s) (hf.tendsto p₀)
    (Eventually.of_forall fun p => measurePreserving_sub_right volume p)
    (measurePreserving_sub_right volume p₀) (isClosed_square 0 s).measurableSet.nullMeasurableSet
    (volume_square_ne_top 0 s)
  convert h using 3 with p
  rw [square_eq_preimage_sub p, square_eq_preimage_sub p₀]
  rfl

/-- The measure of `A ∩ X` moves by at most the measure of `X ∆ Y` when `X` is
replaced by `Y`. -/
lemma abs_sub_toReal_le {A X Y : Set ℂ} (hX : volume X ≠ ⊤) (hY : volume Y ≠ ⊤) :
    |(volume (A ∩ X)).toReal - (volume (A ∩ Y)).toReal| ≤ (volume (X ∆ Y)).toReal := by
  have hXY : volume (X ∆ Y) ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hX, hY⟩)
    ((measure_mono symmDiff_subset_union).trans (measure_union_le _ _))
  have hAX : volume (A ∩ X) ≠ ⊤ := ne_top_of_le_ne_top hX (measure_mono inter_subset_right)
  have hAY : volume (A ∩ Y) ≠ ⊤ := ne_top_of_le_ne_top hY (measure_mono inter_subset_right)
  have key : ∀ X Y : Set ℂ, volume (A ∩ X) ≤ volume (A ∩ Y) + volume (X ∆ Y) := by
    intro X Y
    calc volume (A ∩ X) ≤ volume ((A ∩ Y) ∪ (X ∆ Y)) := by
          refine measure_mono fun z ⟨hzA, hzX⟩ => ?_
          by_cases hzY : z ∈ Y
          · exact Or.inl ⟨hzA, hzY⟩
          · exact Or.inr (mem_symmDiff.2 (Or.inl ⟨hzX, hzY⟩))
      _ ≤ _ := measure_union_le _ _
  have h1 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hAY, hXY⟩) (key X Y)
  have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hAX, hXY⟩)
    ((key Y X).trans_eq (by rw [symmDiff_comm]))
  rw [ENNReal.toReal_add hAY hXY] at h1
  rw [ENNReal.toReal_add hAX hXY] at h2
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- The measure of a set inside a square of fixed side is continuous in the
square's position. -/
lemma continuous_volume_inter_square (A : Set ℂ) (s : ℝ) :
    Continuous fun p => (volume (A ∩ square p s)).toReal := by
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (g := fun p => (volume (square p s ∆ square p₀ s)).toReal)
    (fun _ => dist_nonneg) (fun p => ?_) ?_
  · rw [Real.dist_eq]
    exact abs_sub_toReal_le (volume_square_ne_top p s) (volume_square_ne_top p₀ s)
  · have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (tendsto_volume_square_symmDiff s p₀)
    exact this

/-- A square of side `s` splits into its parts in `A` and in `Aᶜ`, of total
area `s²`. -/
lemma toReal_inter_add_compl {A : Set ℂ} (hA : MeasurableSet A) (p : ℂ) {s : ℝ}
    (hs : 0 ≤ s) :
    (volume (A ∩ square p s)).toReal + (volume (Aᶜ ∩ square p s)).toReal = s ^ 2 := by
  rw [← ENNReal.toReal_add (volume_inter_square_ne_top _ _ _) (volume_inter_square_ne_top _ _ _),
    inter_comm A, inter_comm Aᶜ, ← sdiff_eq, measure_inter_add_sdiff _ hA, volume_square p hs,
    ENNReal.toReal_ofReal (by positivity)]

/-- Between a square at least half in `A` and one at most half in `A`, some square
on the segment joining their corners is exactly half in `A`. -/
lemma exists_balanced_mem_segment (A : Set ℂ) (s : ℝ) {q₁ q₂ : ℂ}
    (h₁ : (volume (Aᶜ ∩ square q₁ s)).toReal ≤ (volume (A ∩ square q₁ s)).toReal)
    (h₂ : (volume (A ∩ square q₂ s)).toReal ≤ (volume (Aᶜ ∩ square q₂ s)).toReal) :
    ∃ q ∈ segment ℝ q₁ q₂,
      (volume (A ∩ square q s)).toReal = (volume (Aᶜ ∩ square q s)).toReal := by
  set g : ℂ → ℝ := fun q => (volume (A ∩ square q s)).toReal - (volume (Aᶜ ∩ square q s)).toReal
    with hg
  have hgc : Continuous g :=
    (continuous_volume_inter_square A s).sub (continuous_volume_inter_square Aᶜ s)
  obtain ⟨q, hq, hq0⟩ := (convex_segment q₁ q₂).isPreconnected.intermediate_value
    (right_mem_segment ℝ q₁ q₂) (left_mem_segment ℝ q₁ q₂) hgc.continuousOn
    (show (0 : ℝ) ∈ Icc (g q₂) (g q₁) from
      ⟨by simp only [hg]; linarith, by simp only [hg]; linarith⟩)
  exact ⟨q, hq, by simp only [hg] at hq0; linarith⟩

/-- A balanced square has a balanced half-side subsquare. -/
lemma exists_balanced_subsquare {A : Set ℂ} (hA : MeasurableSet A) {p : ℂ} {s : ℝ}
    (hs : 0 ≤ s)
    (h : (volume (A ∩ square p s)).toReal = (volume (Aᶜ ∩ square p s)).toReal) :
    ∃ q, square q (s / 2) ⊆ square p s ∧
      (volume (A ∩ square q (s / 2))).toReal = (volume (Aᶜ ∩ square q (s / 2))).toReal := by
  set t := s / 2 with ht
  have ht0 : 0 ≤ t := by positivity
  set c₁ := p
  set c₂ := p + (t : ℂ)
  set c₃ := p + (t : ℂ) * Complex.I
  set c₄ := p + (t : ℂ) + (t : ℂ) * Complex.I
  have hcorner : ∀ c ∈ ({c₁, c₂, c₃, c₄} : Set ℂ), c ∈ square p t := by
    simp only [mem_insert_iff, mem_singleton_iff]
    rintro c (rfl | rfl | rfl | rfl) <;>
      simp [c₂, c₃, c₄, square, ht0]
  have hcov : square p s ⊆ square c₁ t ∪ square c₂ t ∪ square c₃ t ∪ square c₄ t := by
    rintro z ⟨h1, h2, h3, h4⟩
    simp only [mem_union, square, mem_ofPred_eq, c₁, c₂, c₃, c₄, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    rcases le_total z.re (p.re + t) with hr | hr <;>
      rcases le_total z.im (p.im + t) with hi | hi
    · exact Or.inl (Or.inl (Or.inl ⟨h1, hr, h3, hi⟩))
    · exact Or.inl (Or.inr ⟨h1, hr, by linarith, by linarith⟩)
    · exact Or.inl (Or.inl (Or.inr ⟨hr, by linarith, h3, hi⟩))
    · exact Or.inr ⟨hr, by linarith, hi, by linarith⟩
  have hsub : ∀ K : Set ℂ, (volume (K ∩ square p s)).toReal ≤
      (volume (K ∩ square c₁ t)).toReal + (volume (K ∩ square c₂ t)).toReal +
        (volume (K ∩ square c₃ t)).toReal + (volume (K ∩ square c₄ t)).toReal := by
    intro K
    have hf := fun c => volume_inter_square_ne_top K c t
    have h12 := ENNReal.add_ne_top.2 ⟨hf c₁, hf c₂⟩
    have h123 := ENNReal.add_ne_top.2 ⟨h12, hf c₃⟩
    rw [← ENNReal.toReal_add (hf _) (hf _), ← ENNReal.toReal_add h12 (hf _),
      ← ENNReal.toReal_add h123 (hf _)]
    refine ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨h123, hf c₄⟩) ?_
    calc volume (K ∩ square p s)
        ≤ volume ((K ∩ square c₁ t) ∪ (K ∩ square c₂ t) ∪ (K ∩ square c₃ t) ∪
            (K ∩ square c₄ t)) := by
          refine measure_mono fun z ⟨hzK, hz⟩ => ?_
          rcases hcov hz with ((h | h) | h) | h
          · exact Or.inl (Or.inl (Or.inl ⟨hzK, h⟩))
          · exact Or.inl (Or.inl (Or.inr ⟨hzK, h⟩))
          · exact Or.inl (Or.inr ⟨hzK, h⟩)
          · exact Or.inr ⟨hzK, h⟩
      _ ≤ _ := by
          refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
          refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
          exact measure_union_le _ _
  have hsumA := hsub A
  have hsumB := hsub Aᶜ
  have hbig := toReal_inter_add_compl hA p hs
  have hq := fun c => toReal_inter_add_compl hA c ht0
  have hts : s ^ 2 = 4 * t ^ 2 := by rw [ht]; ring
  -- one quadrant is at least half in `A`, one at least half in `Aᶜ`
  have hex₁ : ∃ c ∈ ({c₁, c₂, c₃, c₄} : Set ℂ),
      (volume (Aᶜ ∩ square c t)).toReal ≤ (volume (A ∩ square c t)).toReal := by
    by_contra hno
    push Not at hno
    have e1 := hno c₁ (by simp)
    have e2 := hno c₂ (by simp)
    have e3 := hno c₃ (by simp)
    have e4 := hno c₄ (by simp)
    linarith [hq c₁, hq c₂, hq c₃, hq c₄]
  have hex₂ : ∃ c ∈ ({c₁, c₂, c₃, c₄} : Set ℂ),
      (volume (A ∩ square c t)).toReal ≤ (volume (Aᶜ ∩ square c t)).toReal := by
    by_contra hno
    push Not at hno
    have e1 := hno c₁ (by simp)
    have e2 := hno c₂ (by simp)
    have e3 := hno c₃ (by simp)
    have e4 := hno c₄ (by simp)
    linarith [hq c₁, hq c₂, hq c₃, hq c₄]
  obtain ⟨d₁, hd₁, hle₁⟩ := hex₁
  obtain ⟨d₂, hd₂, hle₂⟩ := hex₂
  obtain ⟨q, hqseg, hqbal⟩ := exists_balanced_mem_segment A t hle₁ hle₂
  have hqmem : q ∈ square p t :=
    (convex_square p t).segment_subset (hcorner d₁ hd₁) (hcorner d₂ hd₂) hqseg
  refine ⟨q, ?_, hqbal⟩
  obtain ⟨g1, g2, g3, g4⟩ := hqmem
  rintro z ⟨h1, h2, h3, h4⟩
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- If the complement of a measurable set `A` has density zero at some point and
`A` has density zero at another, then at some point neither has density zero. -/
theorem exists_not_densityZero {A : Set ℂ} (hA : MeasurableSet A) {a b : ℂ}
    (ha : DensityZero Aᶜ a) (hb : DensityZero A b) :
    ∃ z, ¬ DensityZero A z ∧ ¬ DensityZero Aᶜ z := by
  -- a square containing a point where `K` has density zero has little of `K`
  have hsmall : ∀ (K : Set ℂ) (x : ℂ) (δ : ℝ),
      (∀ ρ, 0 < ρ → ρ < δ → volume (K ∩ closedBall x ρ) ≤ ENNReal.ofReal (1 / 16 * ρ ^ 2)) →
      ∀ (q : ℂ) (t : ℝ), 0 < t → 2 * t < δ → x ∈ square q t →
        (volume (K ∩ square q t)).toReal ≤ t ^ 2 / 4 := by
    intro K x δ hK q t ht htδ hx
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    calc volume (K ∩ square q t) ≤ volume (K ∩ closedBall x (2 * t)) :=
          measure_mono (inter_subset_inter_right _ (square_subset_closedBall hx))
      _ ≤ ENNReal.ofReal (1 / 16 * (2 * t) ^ 2) := hK _ (by positivity) htδ
      _ = ENNReal.ofReal (t ^ 2 / 4) := by congr 1; ring
  -- a first balanced square
  obtain ⟨δa, hδa, ha'⟩ := ha (1 / 16) (by norm_num)
  obtain ⟨δb, hδb, hb'⟩ := hb (1 / 16) (by norm_num)
  set s := min δa δb / 4 with hsdef
  have hs : 0 < s := by positivity
  have h2sa : 2 * s < δa := by have := min_le_left δa δb; linarith
  have h2sb : 2 * s < δb := by have := min_le_right δa δb; linarith
  have hla := hsmall Aᶜ a δa ha' a s hs h2sa (mem_square_self a hs.le)
  have hlb := hsmall A b δb hb' b s hs h2sb (mem_square_self b hs.le)
  have hsa := toReal_inter_add_compl hA a hs.le
  have hsb := toReal_inter_add_compl hA b hs.le
  obtain ⟨p₀, -, hp₀⟩ := exists_balanced_mem_segment A s (q₁ := a) (q₂ := b)
    (by nlinarith) (by nlinarith)
  -- nested balanced squares
  have step : ∀ (n : ℕ) (p : ℂ),
      (volume (A ∩ square p (s / 2 ^ n))).toReal = (volume (Aᶜ ∩ square p (s / 2 ^ n))).toReal →
      ∃ q, square q (s / 2 ^ (n + 1)) ⊆ square p (s / 2 ^ n) ∧
        (volume (A ∩ square q (s / 2 ^ (n + 1)))).toReal =
          (volume (Aᶜ ∩ square q (s / 2 ^ (n + 1)))).toReal := by
    intro n p hp
    have := exists_balanced_subsquare hA (by positivity) hp
    rwa [show s / 2 ^ n / 2 = s / 2 ^ (n + 1) by rw [pow_succ]; ring] at this
  choose! next hnext_sub hnext_bal using step
  let seq : ℕ → ℂ := fun n => Nat.rec p₀ (fun n q => next n q) n
  have hseq : ∀ n, (volume (A ∩ square (seq n) (s / 2 ^ n))).toReal =
      (volume (Aᶜ ∩ square (seq n) (s / 2 ^ n))).toReal := by
    intro n
    induction n with
    | zero => simpa [seq] using hp₀
    | succ n ih => exact hnext_bal n _ ih
  have hnest : ∀ n, square (seq (n + 1)) (s / 2 ^ (n + 1)) ⊆ square (seq n) (s / 2 ^ n) :=
    fun n => hnext_sub n _ (hseq n)
  obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => square (seq n) (s / 2 ^ n)) hnest
    (fun n => ⟨seq n, mem_square_self _ (by positivity)⟩) (isCompact_square _ _)
    (fun n => isClosed_square _ _)
  rw [mem_iInter] at hz
  -- both `A` and `Aᶜ` fill half of every square, so neither has density zero at `z`
  have hnot : ∀ K : Set ℂ, (∀ n, (volume (K ∩ square (seq n) (s / 2 ^ n))).toReal =
      (s / 2 ^ n) ^ 2 / 2) → ¬ DensityZero K z := by
    intro K hK hz0
    obtain ⟨δ, hδ, hzδ⟩ := hz0 (1 / 16) (by norm_num)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < δ / (2 * s) by positivity)
      (show (1 / 2 : ℝ) < 1 by norm_num)
    have hsn : s / 2 ^ n = s * (1 / 2) ^ n := by rw [one_div_pow]; ring
    have hn' : 2 * (s / 2 ^ n) < δ := by
      rw [hsn]
      rw [lt_div_iff₀ (by positivity)] at hn
      linarith
    have hpos : 0 < s / 2 ^ n := by positivity
    have := hsmall K z δ hzδ (seq n) (s / 2 ^ n) hpos hn' (hz n)
    rw [hK n] at this
    nlinarith
  refine ⟨z, hnot A fun n => ?_, hnot Aᶜ fun n => ?_⟩
  · have := toReal_inter_add_compl hA (seq n) (show 0 ≤ s / 2 ^ n by positivity)
    linarith [hseq n]
  · have := toReal_inter_add_compl hA (seq n) (show 0 ≤ s / 2 ^ n by positivity)
    linarith [hseq n]

end Port173

end






/-
# Alternation on a circle

Let `R` be a measurable subset of the circle `𝕋 = ℝ / 2πℤ` with normalized arc
length `|·|`, and write `R - s = {t | t + s ∈ R}`. Suppose that
`R ∩ (R - π/3)`, `Rᶜ ∩ (Rᶜ - π/3)` and `R ∩ (R - γ)` are null. Then `γ / π` is
rational.

The first condition gives `R - π/3 ⊆ Rᶜ` up to a null set, so `|R| ≤ |Rᶜ|`, and
the second gives the reverse inequality. Inclusions between sets of equal
finite measure are equalities up to null sets, so `R - π/3 = Rᶜ` and, by the
third condition, `R - γ = Rᶜ`, again up to null sets. Hence `R` is invariant
up to a null set under the rotation by `γ - π/3`. If `γ / π` is irrational this
rotation is ergodic, so `R` is null or conull, contradicting `|R| = |Rᶜ|`.
-/


noncomputable section

namespace Port173

open MeasureTheory Set Real OAI.EuclideanFiveColor

/-- If `R ∩ (R - s)` is null, then `R - s ⊆ Rᶜ` up to a null set. -/
lemma preimage_add_ae_le_compl {R : Set Angles} {s : Angles}
    (h : angularMeasure (R ∩ (· + s) ⁻¹' R) = 0) :
    (· + s) ⁻¹' R ≤ᵐ[angularMeasure] Rᶜ := by
  exact (ae_le_set (s := (· + s) ⁻¹' R) (t := Rᶜ)).2 (by simpa only [sdiff_compl, inter_comm] using h)

/-- Alternation on a circle: the three null intersections force `γ / π` to be
rational. -/
theorem circle_alternation {R : Set Angles} (hR : MeasurableSet R) {γ : ℝ}
    (hγ : Irrational (γ / π))
    (h₁ : angularMeasure (R ∩ (· + ((π / 3 : ℝ) : Angles)) ⁻¹' R) = 0)
    (h₂ : angularMeasure (Rᶜ ∩ (· + ((π / 3 : ℝ) : Angles)) ⁻¹' Rᶜ) = 0)
    (h₃ : angularMeasure (R ∩ (· + (γ : Angles)) ⁻¹' R) = 0) : False := by
  set s : Angles := ((π / 3 : ℝ) : Angles) with hs
  set g : Angles := (γ : Angles) with hg
  have hmp : ∀ x : Angles, MeasurePreserving (· + x) angularMeasure angularMeasure :=
    fun x => measurePreserving_add_right angularMeasure x
  have hmeas : ∀ x : Angles, angularMeasure ((· + x) ⁻¹' R) = angularMeasure R :=
    fun x => (hmp x).measure_preimage hR.nullMeasurableSet
  have hmeas' : ∀ x : Angles, angularMeasure ((· + x) ⁻¹' Rᶜ) = angularMeasure Rᶜ :=
    fun x => (hmp x).measure_preimage hR.compl.nullMeasurableSet
  have hle₁ := preimage_add_ae_le_compl h₁
  have hle₂ : (· + s) ⁻¹' Rᶜ ≤ᵐ[angularMeasure] R := by
    filter_upwards [preimage_add_ae_le_compl h₂] with q hq
    exact fun hq' => Classical.byContradiction (hq hq')
  have hRc : angularMeasure R ≤ angularMeasure Rᶜ := (hmeas s).symm.le.trans (measure_mono_ae hle₁)
  have hcR : angularMeasure Rᶜ ≤ angularMeasure R := (hmeas' s).symm.le.trans (measure_mono_ae hle₂)
  have hnull : ∀ x : Angles, NullMeasurableSet ((· + x) ⁻¹' R) angularMeasure :=
    fun x => (hR.preimage (measurable_add_const x)).nullMeasurableSet
  have heq_s : (· + s) ⁻¹' R =ᵐ[angularMeasure] Rᶜ :=
    ae_eq_of_ae_subset_of_measure_ge hle₁ ((hmeas s).symm ▸ hcR) (hnull s) (measure_ne_top _ _)
  have heq_g : (· + g) ⁻¹' R =ᵐ[angularMeasure] Rᶜ :=
    ae_eq_of_ae_subset_of_measure_ge (preimage_add_ae_le_compl h₃) ((hmeas g).symm ▸ hcR)
      (hnull g) (measure_ne_top _ _)
  -- `R` is invariant up to a null set under the rotation by `γ - π/3`
  have hinv : (fun x => (g - s) + x) ⁻¹' R =ᵐ[angularMeasure] R := by
    have h := (hmp (-s)).quasiMeasurePreserving.preimage_ae_eq (heq_g.trans heq_s.symm)
    have e1 : (· + -s) ⁻¹' ((· + g) ⁻¹' R) = (fun x => (g - s) + x) ⁻¹' R := by
      ext t; simp only [mem_preimage]; congr! 1; abel
    have e2 : (· + -s) ⁻¹' ((· + s) ⁻¹' R) = R := by
      ext t; simp
    rwa [e1, e2] at h
  have hdense : DenseRange (fun n : ℤ => n • (g - s)) := by
    rw [hg, hs, ← AddCircle.coe_sub, AddCircle.denseRange_zsmul_coe_iff]
    have h' : Irrational (γ / π * ((1 / 2 : ℚ) : ℝ) - ((1 / 6 : ℚ) : ℝ)) :=
      (hγ.mul_ratCast (by norm_num)).sub_ratCast _
    convert h' using 1
    field_simp
    ring
  have herg := ergodic_add_left_of_denseRange_zsmul hdense angularMeasure
  have hsum : angularMeasure R + angularMeasure Rᶜ = 1 := by
    rw [measure_add_measure_compl hR, measure_univ]
  have hRR : angularMeasure Rᶜ = angularMeasure R := le_antisymm hcR hRc
  rw [hRR] at hsum
  rcases herg.ae_empty_or_univ_of_preimage_ae_le hR.nullMeasurableSet hinv.le with h0 | h1
  · rw [measure_congr h0, measure_empty] at hsum
    simp at hsum
  · rw [measure_congr h1, measure_univ] at hsum
    norm_num at hsum

end Port173

end








/-
# Two rational chord angles

Let `2/3 < x < 3/2` with `x ≠ 1`, and put `A = arcsin (x / 2)` and
`B = arcsin (1 / (2x))`, the half apex angles of the isosceles triangles with
sides `1, 1, x` and `x, x, 1`. Then `A / π` and `B / π` are not both rational.

Since `sin A sin B = 1/4`, the angles `u = A - B` and `v = A + B` satisfy
`2 cos u - 2 cos v = 1`. If both are rational multiples of `π`, write
`u = 2πa/m` and `v = 2πb/m` modulo `2π`. Then `ω = e^{2πi/m}` is a root of
`X^a + X^{(m-1)a} - X^b - X^{(m-1)b} - 1`, so every primitive `m`-th root of
unity `ω^k` is one too, since the minimal polynomial of `ω` over `ℚ` is the
cyclotomic polynomial: `2 cos (ku) - 2 cos (kv) = 1` for every `k` coprime to
`m`. In the window `cos u > cos (π/5)`, and `cos u ≠ 1` as `x ≠ 1`, so the
reduced denominator `m₁` of `u / 2π` is at least `11`. Every such `m₁` has a
unit `j` with `m₁ < 3j < 2m₁`, and a `k` coprime to `m` carries `u` to
`2πj/m₁`, where `cos < -1/2`, so `2 cos (ku) - 2 cos (kv) < 1`.
-/


noncomputable section

namespace Port173

open Real Polynomial

/-- For `ω = e^{2πi/m}`, `ω^{jn} + ω^{j(m-1)n} = 2 cos (2π jn / m)`. -/
lemma pow_add_pow_eq_two_cos {m : ℕ} (hm : 0 < m) (j n : ℕ) :
    (Complex.exp (2 * π * Complex.I / m) ^ j) ^ n +
        (Complex.exp (2 * π * Complex.I / m) ^ j) ^ ((m - 1) * n) =
      ((2 * cos (2 * π * (j * n) / m) : ℝ) : ℂ) := by
  set ω := Complex.exp (2 * π * Complex.I / m) with hω
  have hprim : IsPrimitiveRoot ω m := Complex.isPrimitiveRoot_exp m hm.ne'
  have hz : (ω ^ j) ^ n = Complex.exp (↑(2 * π * (j * n) / m) * Complex.I) := by
    rw [← pow_mul, hω, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hinv : (ω ^ j) ^ ((m - 1) * n) = ((ω ^ j) ^ n)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_add, ← add_one_mul, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hm.ne'), ← pow_mul,
      show j * (m * n) = m * (j * n) by ring, pow_mul, hprim.pow_eq_one, one_pow]
  rw [hinv, hz, ← Complex.exp_neg]
  push_cast
  rw [Complex.two_cos, neg_mul]

/-- The Galois step: if `2 cos (2πa/m) - 2 cos (2πb/m) = 1`, the same holds after
multiplying both angles by any `k` coprime to `m`. -/
lemma two_cos_sub_two_cos_of_coprime {m a b : ℕ} (hm : 0 < m)
    (h : 2 * cos (2 * π * a / m) - 2 * cos (2 * π * b / m) = 1) {k : ℕ} (hk : k.Coprime m) :
    2 * cos (2 * π * (k * a) / m) - 2 * cos (2 * π * (k * b) / m) = 1 := by
  set ω := Complex.exp (2 * π * Complex.I / m) with hω
  have hprim : IsPrimitiveRoot ω m := Complex.isPrimitiveRoot_exp m hm.ne'
  have hprimk : IsPrimitiveRoot (ω ^ k) m := hprim.pow_of_coprime k hk
  have hmin : minpoly ℚ (ω ^ k) = minpoly ℚ ω := by
    rw [← cyclotomic_eq_minpoly_rat hprim hm, ← cyclotomic_eq_minpoly_rat hprimk hm]
  set P : ℚ[X] := X ^ a + X ^ ((m - 1) * a) - X ^ b - X ^ ((m - 1) * b) - 1 with hP
  have hev : ∀ j : ℕ, aeval (ω ^ j) P =
      ((2 * cos (2 * π * (j * a) / m) - 2 * cos (2 * π * (j * b) / m) - 1 : ℝ) : ℂ) := by
    intro j
    have ha := pow_add_pow_eq_two_cos hm j a
    have hb := pow_add_pow_eq_two_cos hm j b
    simp only [hP, map_sub, map_add, map_pow, aeval_X, map_one]
    push_cast at ha hb ⊢
    rw [← ha, ← hb]
    ring
  have h1 : aeval ω P = 0 := by
    have := hev 1
    rw [pow_one] at this
    rw [this]
    simp only [Nat.cast_one, one_mul, h, sub_self, Complex.ofReal_zero]
  obtain ⟨Q, hQ⟩ := minpoly.dvd ℚ ω h1
  have hk0 : aeval (ω ^ k) P = 0 := by
    rw [hQ, map_mul, ← hmin, minpoly.aeval, zero_mul]
  rw [hev k] at hk0
  have := Complex.ofReal_eq_zero.1 hk0
  linarith

/-- Every `m ≥ 11` has a unit `j` modulo `m` with `m < 3j < 2m`. -/
lemma exists_coprime_middle_third {m : ℕ} (hm : 11 ≤ m) :
    ∃ j : ℕ, j.Coprime m ∧ m < 3 * j ∧ 3 * j < 2 * m := by
  obtain ⟨l, rfl | rfl | rfl | rfl⟩ : ∃ l, m = 4 * l ∨ m = 4 * l + 1 ∨ m = 4 * l + 2 ∨
      m = 4 * l + 3 := ⟨m / 4, by omega⟩
  · refine ⟨2 * l + 1, ?_, by omega, by omega⟩
    rw [show 4 * l = 2 * (2 * l) by ring]
    refine Nat.Coprime.mul_right ?_ ?_
    · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]; omega
    · exact Nat.coprime_self_add_left.2 (Nat.coprime_one_left _)
  · refine ⟨2 * l, ?_, by omega, by omega⟩
    rw [show 4 * l + 1 = 2 * (2 * l) + 1 by ring, Nat.coprime_mul_right_add_right]
    exact Nat.coprime_one_right _
  · refine ⟨2 * l + 3, ?_, by omega, by omega⟩
    rw [show 4 * l + 2 = 2 * (2 * l + 1) by ring]
    refine Nat.Coprime.mul_right ?_ ?_
    · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]; omega
    · rw [show 2 * l + 3 = (2 * l + 1) + 2 by ring, Nat.coprime_self_add_left,
        Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      omega
  · refine ⟨2 * l + 1, ?_, by omega, by omega⟩
    rw [show 4 * l + 3 = 2 * (2 * l + 1) + 1 by ring, Nat.coprime_mul_right_add_right]
    exact Nat.coprime_one_right _

/-- `cos θ < -1/2` for `2π/3 < θ < 4π/3`. -/
lemma cos_lt_neg_half {θ : ℝ} (h₁ : 2 * π / 3 < θ) (h₂ : θ < 4 * π / 3) :
    cos θ < -1 / 2 := by
  have hc : cos θ = -cos (θ - π) := by rw [cos_sub_pi]; ring
  rw [hc]
  have : 1 / 2 < cos (θ - π) := by
    rw [← cos_pi_div_three]
    rcases le_total 0 (θ - π) with h | h
    · exact cos_lt_cos_of_nonneg_of_le_pi h (by linarith [pi_pos]) (by linarith)
    · rw [← cos_neg (θ - π)]
      exact cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith [pi_pos]) (by linarith)
  linarith

/-- Angles `2πx/m` and `2πy/m` with `x ≡ y` modulo `m` have the same cosine. -/
lemma cos_eq_of_dvd_sub {m : ℕ} (hm : 0 < m) {x y : ℤ} (h : (m : ℤ) ∣ y - x) :
    cos (2 * π * x / m) = cos (2 * π * y / m) := by
  obtain ⟨t, ht⟩ := h
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hy : (y : ℝ) = x + m * t := by
    have : ((y - x : ℤ) : ℝ) = ((m * t : ℤ) : ℝ) := by rw [ht]
    push_cast at this
    linarith
  rw [hy, show 2 * π * (x + m * t) / m = 2 * π * x / m + t * (2 * π) by field_simp,
    cos_add_int_mul_two_pi]

/-- `cos (2π a / m) ≤ cos (2π / m)` unless `m ∣ a`. -/
lemma cos_two_pi_div_le {m a : ℕ} (hm : 0 < m) (ha : ¬ m ∣ a) :
    cos (2 * π * a / m) ≤ cos (2 * π / m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set r := a % m with hr
  set q := a / m with hq
  have hr1 : 1 ≤ r := Nat.pos_of_ne_zero fun h => ha (Nat.dvd_of_mod_eq_zero h)
  have hr2 : r + 1 ≤ m := Nat.mod_lt _ hm
  have hadd : (a : ℝ) = r + m * q := by exact_mod_cast (Nat.mod_add_div a m).symm
  rw [hadd, show 2 * π * (r + m * q) / m = 2 * π * r / m + q * (2 * π) by field_simp,
    cos_add_nat_mul_two_pi]
  have hr1' : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hr2' : (r : ℝ) + 1 ≤ m := by exact_mod_cast hr2
  have h1 : 2 * π / m ≤ 2 * π * r / m := by
    apply div_le_div_of_nonneg_right _ hmR.le
    nlinarith [pi_pos]
  have h2 : 2 * π * r / m ≤ 2 * π - 2 * π / m := by
    rw [div_le_iff₀ hmR, sub_mul, div_mul_cancel₀ _ hmR.ne']
    nlinarith [pi_pos]
  rcases le_total (2 * π * r / m) π with h | h
  · exact cos_le_cos_of_nonneg_of_le_pi (by positivity) h h1
  · rw [← cos_two_pi_sub (2 * π * r / m)]
    exact cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by linarith)

/-- The arithmetic step: if `cos (2πa/m) > cos (π/5)` and `cos (2πa/m) ≠ 1`, some
`k` coprime to `m` gives `cos (2πka/m) < -1/2`. -/
lemma exists_coprime_cos_lt {m a : ℕ} (hm : 0 < m)
    (h₁ : (1 + √5) / 4 < cos (2 * π * a / m)) (h₂ : cos (2 * π * a / m) ≠ 1) :
    ∃ k : ℕ, k.Coprime m ∧ cos (2 * π * (k * a) / m) < -1 / 2 := by
  obtain ⟨a₁, m₁, hcop, ha, hmm⟩ := Nat.exists_coprime a m
  set g := a.gcd m with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right a hm
  have hm₁ : 0 < m₁ := by
    rcases Nat.eq_zero_or_pos m₁ with h | h
    · rw [h, zero_mul] at hmm; omega
    · exact h
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg0.ne'
  have hm₁R : (0 : ℝ) < m₁ := by exact_mod_cast hm₁
  -- the angle in lowest terms
  have hangle : ∀ k : ℕ, 2 * π * (k * a) / m = 2 * π * (k * a₁) / m₁ := by
    intro k
    rw [ha, hmm]
    push_cast
    field_simp
  have h1' := hangle 1
  simp only [Nat.cast_one, one_mul] at h1'
  rw [h1'] at h₁ h₂
  -- the reduced denominator is at least `11`
  have h11 : 11 ≤ m₁ := by
    by_contra hlt
    push Not at hlt
    by_cases hdvd : m₁ ∣ a₁
    · have h1 : m₁ = 1 := Nat.Coprime.eq_one_of_dvd hcop.symm hdvd
      apply h₂
      rw [h1, Nat.cast_one, div_one]
      obtain ⟨t, rfl⟩ := hdvd
      rw [h1, one_mul, mul_comm]
      exact_mod_cast cos_nat_mul_two_pi t
    · have hm₁2 : 2 ≤ m₁ := by
        rcases Nat.lt_or_ge m₁ 2 with h | h
        · exact absurd (by interval_cases m₁; exact one_dvd a₁) hdvd
        · exact h
      have hle := cos_two_pi_div_le hm₁ hdvd
      have hm₁le : (m₁ : ℝ) ≤ 10 := by exact_mod_cast (Nat.lt_succ_iff.1 hlt)
      have hm₁2' : (2 : ℝ) ≤ m₁ := by exact_mod_cast hm₁2
      have : cos (2 * π / m₁) ≤ cos (π / 5) := by
        apply cos_le_cos_of_nonneg_of_le_pi (by positivity)
        · rw [div_le_iff₀ hm₁R]; nlinarith [pi_pos]
        · rw [div_le_div_iff₀ (by norm_num) hm₁R]; nlinarith [pi_pos]
      rw [cos_pi_div_five] at this
      linarith
  obtain ⟨j, hj, hj₁, hj₂⟩ := exists_coprime_middle_third h11
  -- lift the unit `j / a₁` modulo `m₁` to a unit modulo `m`
  have : NeZero m := ⟨hm.ne'⟩
  have : NeZero m₁ := ⟨hm₁.ne'⟩
  have hdvd : m₁ ∣ m := ⟨g, by rw [hmm]⟩
  obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective hdvd
    (ZMod.unitOfCoprime j hj * (ZMod.unitOfCoprime a₁ hcop)⁻¹)
  refine ⟨(v : ZMod m).val, ZMod.val_coe_unit_coprime v, ?_⟩
  have hcong : ((((v : ZMod m).val * a₁ : ℕ)) : ZMod m₁) = (j : ZMod m₁) := by
    have hv' : ((ZMod.unitsMap hdvd v : (ZMod m₁)ˣ) : ZMod m₁) = ZMod.cast (v : ZMod m) := rfl
    rw [Nat.cast_mul, ZMod.natCast_val, ← hv', hv, ← ZMod.coe_unitOfCoprime a₁ hcop,
      ← Units.val_mul, inv_mul_cancel_right, ZMod.coe_unitOfCoprime]
  have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).1 hcong
  rw [hangle]
  have hcos := cos_eq_of_dvd_sub hm₁ (x := ((v : ZMod m).val * a₁ : ℕ)) (y := (j : ℕ))
    ((Nat.modEq_iff_dvd).1 hmod)
  push_cast at hcos
  rw [hcos]
  have hj₁' : (m₁ : ℝ) < 3 * j := by exact_mod_cast hj₁
  have hj₂' : 3 * (j : ℝ) < 2 * m₁ := by exact_mod_cast hj₂
  apply cos_lt_neg_half
  · rw [lt_div_iff₀ hm₁R]; nlinarith [pi_pos]
  · rw [div_lt_div_iff₀ hm₁R (by norm_num)]; nlinarith [pi_pos]

/-- An integer multiple of `2π / m` is, modulo `2π`, a natural multiple. -/
lemma exists_nat_cos_eq_int {m : ℕ} (hm : 0 < m) (N : ℤ) :
    ∃ a : ℕ, cos (2 * π * N / m) = cos (2 * π * a / m) := by
  have hm' : (0 : ℤ) ≤ N % m := Int.emod_nonneg _ (by exact_mod_cast hm.ne')
  refine ⟨(N % m).toNat, ?_⟩
  have hcast : (((N % m).toNat : ℕ) : ℝ) = ((N % m : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hm']
  rw [hcast]
  exact cos_eq_of_dvd_sub hm (Int.mod_modEq N m).dvd |>.symm

/-- Two rational multiples of `2π` are, modulo `2π`, `2πa/m` and `2πb/m` for a
common denominator `m`. -/
lemma exists_nat_cos_eq (s t : ℚ) :
    ∃ m : ℕ, 0 < m ∧ ∃ a b : ℕ, cos (2 * π * s) = cos (2 * π * a / m) ∧
      cos (2 * π * t) = cos (2 * π * b / m) := by
  have hm : 0 < s.den * t.den := Nat.mul_pos s.den_pos t.den_pos
  refine ⟨s.den * t.den, hm, ?_⟩
  have hsd : (s.den : ℝ) ≠ 0 := by exact_mod_cast s.den_pos.ne'
  have htd : (t.den : ℝ) ≠ 0 := by exact_mod_cast t.den_pos.ne'
  obtain ⟨a, ha⟩ := exists_nat_cos_eq_int hm (s.num * t.den)
  obtain ⟨b, hb⟩ := exists_nat_cos_eq_int hm (t.num * s.den)
  refine ⟨a, b, ?_, ?_⟩
  · rw [← ha, Rat.cast_def]
    congr 1
    push_cast
    field_simp
  · rw [← hb, Rat.cast_def]
    congr 1
    push_cast
    field_simp

/-- For `2/3 < x < 3/2` with `x ≠ 1`, one of the apex angles of the isosceles
triangles with sides `1, 1, x` and `x, x, 1` is an irrational multiple of `π`. -/
theorem irrational_apex_angle {x : ℝ} (hx₁ : 2 / 3 < x) (hx₂ : x < 3 / 2) (hx : x ≠ 1) :
    Irrational (2 * arcsin (x / 2) / π) ∨ Irrational (2 * arcsin (1 / (2 * x)) / π) := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  unfold Irrational at h1 h2
  rw [not_not] at h1 h2
  obtain ⟨q₁, hq₁⟩ := h1
  obtain ⟨q₂, hq₂⟩ := h2
  have hx0 : 0 < x := by linarith
  set A := arcsin (x / 2) with hA
  set B := arcsin (1 / (2 * x)) with hB
  set y := 1 / (2 * x) with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y < 1 := by rw [hy, div_lt_one (by positivity)]; linarith
  have hsA : sin A = x / 2 := sin_arcsin (by linarith) (by linarith)
  have hsB : sin B = y := sin_arcsin (by linarith) hy1.le
  have hcA : cos A = √(1 - (x / 2) ^ 2) := cos_arcsin _
  have hcB : cos B = √(1 - y ^ 2) := cos_arcsin _
  have hA' : A = 2 * π * ((q₁ / 4 : ℚ) : ℝ) := by
    push_cast; rw [hq₁]; field_simp; ring
  have hB' : B = 2 * π * ((q₂ / 4 : ℚ) : ℝ) := by
    push_cast; rw [hq₂]; field_simp; ring
  have hu : A - B = 2 * π * (((q₁ - q₂) / 4 : ℚ) : ℝ) := by
    rw [hA', hB']; push_cast; ring
  have hv : A + B = 2 * π * (((q₁ + q₂) / 4 : ℚ) : ℝ) := by
    rw [hA', hB']; push_cast; ring
  obtain ⟨m, hm, a, b, ha, hb⟩ := exists_nat_cos_eq ((q₁ - q₂) / 4) ((q₁ + q₂) / 4)
  have hxy : x * y = 1 / 2 := by rw [hy]; field_simp
  have hkey : 2 * cos (2 * π * a / m) - 2 * cos (2 * π * b / m) = 1 := by
    rw [← ha, ← hb, ← hu, ← hv, cos_sub, cos_add, hsA, hsB]
    linear_combination 2 * hxy
  have hbig : (1 + √5) / 4 < cos (2 * π * a / m) := by
    rw [← ha, ← hu, cos_sub, hsA, hsB, hcA, hcB]
    have hP : 0 ≤ √(1 - (x / 2) ^ 2) * √(1 - y ^ 2) := by positivity
    have hsq : (√(1 - (x / 2) ^ 2) * √(1 - y ^ 2)) ^ 2 = (1 - (x / 2) ^ 2) * (1 - y ^ 2) := by
      rw [mul_pow, sq_sqrt (by nlinarith), sq_sqrt (by nlinarith)]
    have h5 : (√5 / 4) ^ 2 < (√(1 - (x / 2) ^ 2) * √(1 - y ^ 2)) ^ 2 := by
      rw [hsq, div_pow, sq_sqrt (by norm_num)]
      have hy₁ : 1 / 3 < y := by rw [hy, lt_div_iff₀ (by positivity)]; linarith
      have hy₂ : y < 3 / 4 := by rw [hy, div_lt_iff₀ (by positivity)]; linarith
      nlinarith [mul_pos (sub_pos.2 hx₁) (sub_pos.2 hx₂), mul_pos (sub_pos.2 hy₁) (sub_pos.2 hy₂)]
    have := lt_of_pow_lt_pow_left₀ 2 hP h5
    have hxy' : x / 2 * y = 1 / 4 := by linear_combination hxy / 2
    linarith
  have hne : cos (2 * π * a / m) ≠ 1 := by
    rw [← ha, ← hu]
    intro h1
    have hAb := neg_pi_div_two_le_arcsin (x / 2)
    have hAt := arcsin_le_pi_div_two (x / 2)
    have hBb := neg_pi_div_two_le_arcsin y
    have hBt := arcsin_le_pi_div_two y
    have h0 := (cos_eq_one_iff_of_lt_of_lt (by linarith [pi_pos]) (by linarith [pi_pos])).1 h1
    have hAB : A = B := by linarith
    have : x / 2 = y := by rw [← hsA, ← hsB, hAB]
    have hx2 : x * x = 1 := by
      have h' : x / 2 * (2 * x) = y * (2 * x) := by rw [this]
      rw [hy, div_mul_cancel₀ _ (by positivity)] at h'
      linarith
    have hfac : (x - 1) * (x + 1) = 0 := by linear_combination hx2
    rcases mul_eq_zero.1 hfac with h | h
    · exact hx (by linarith)
    · linarith
  obtain ⟨k, hk, hlt⟩ := exists_coprime_cos_lt hm hbig hne
  have := two_cos_sub_two_cos_of_coprime hm hkey hk
  have := neg_one_le_cos (2 * π * (k * b) / m)
  linarith

end Port173

end








/-
# No null set supports itself on circles

Let `S ⊆ ℂ` be measurable and null and `r > 0`. If every point `p ∈ S` sees `S`
in positive arc length on the circle of radius `r` about it, then `S` is empty.

For `p ∈ S` the pairs of directions `(t, u)` with `p + r e^{it} ∈ S` and
`p + r e^{it} + r e^{iu} ∈ S` have positive measure, by Fubini. But the map
`(t, u) ↦ e^{it} + e^{iu}` pulls null sets back to null sets. After the shear
`u ↦ t + u` it is `(t, u) ↦ e^{it} (1 + e^{iu})`, a point of modulus
`|1 + e^{iu}| = 2 cos (u/2)` turned by `t`. By polar coordinates, almost every
circle about the origin meets a null set in a null set of angles, and the radius
`2 cos (u/2)` lies in a given null set of radii only for a null set of `u`,
since `u = ± 2 arccos (ρ/2)` and `arccos` is differentiable on `(-1, 1)`.
-/


noncomputable section

namespace Port173

open MeasureTheory Set Real OAI.EuclideanFiveColor

/-- A measurable set of angles is null if its lift to `(-π, π]` is null. -/
lemma angularMeasure_eq_zero_of_volume_preimage {Y : Set Angles} (hY : MeasurableSet Y)
    (h : volume ((QuotientAddGroup.mk : ℝ → Angles) ⁻¹' Y ∩ Ioc (-π) π) = 0) :
    angularMeasure Y = 0 := by
  have hmp := AddCircle.measurePreserving_mk (2 * π) (-π)
  have hvol : (volume : Measure Angles) Y = 0 := by
    rw [← hmp.measure_preimage hY.nullMeasurableSet,
      Measure.restrict_apply (hY.preimage hmp.measurable),
      show -π + 2 * π = π by ring]
    exact h
  simp only [AddCircle.volume_eq_smul_haarAddCircle, Measure.smul_apply, smul_eq_mul,
    mul_eq_zero, ENNReal.ofReal_eq_zero] at hvol
  exact hvol.resolve_left (not_le.2 (by positivity))

/-- Rotating a circle: the directions `t` with `e^{it} w ∈ N` have the measure
of those with `|w| e^{it} ∈ N`. -/
lemma angularMeasure_mul_mem (N : Set ℂ) (w : ℂ) :
    angularMeasure {t | direction t * w ∈ N} =
      angularMeasure {t | (‖w‖ : ℂ) * direction t ∈ N} := by
  have hw : w = (‖w‖ : ℂ) * direction (Complex.arg w : Angles) := by
    rw [direction_real, Circle.coe_exp, Complex.norm_mul_exp_arg_mul_I]
  have : {t | direction t * w ∈ N} =
      (· + (Complex.arg w : Angles)) ⁻¹' {t | (‖w‖ : ℂ) * direction t ∈ N} := by
    ext t
    simp only [mem_ofPred_eq, mem_preimage, direction_add]
    conv_lhs => rw [hw]
    ring_nf
  rw [this, measure_preimage_add_right]

/-- `|1 + e^{iα}| = 2 cos (α/2)` for `|α| ≤ π`. -/
lemma norm_one_add_exp {α : ℝ} (h₁ : -π ≤ α) (h₂ : α ≤ π) :
    ‖1 + Complex.exp (α * Complex.I)‖ = 2 * cos (α / 2) := by
  have hc : 0 ≤ cos (α / 2) := cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  rw [Complex.norm_def, Complex.normSq_apply]
  have hre : (1 + Complex.exp (α * Complex.I)).re = 1 + cos α := by
    rw [Complex.add_re, Complex.exp_ofReal_mul_I_re, Complex.one_re]
  have him : (1 + Complex.exp (α * Complex.I)).im = sin α := by
    rw [Complex.add_im, Complex.exp_ofReal_mul_I_im, Complex.one_im, zero_add]
  have hα : α = 2 * (α / 2) := by ring
  rw [hre, him, hα, cos_two_mul, sin_two_mul, show 2 * (α / 2) / 2 = α / 2 by ring]
  rw [show (1 + (2 * cos (α / 2) ^ 2 - 1)) * (1 + (2 * cos (α / 2) ^ 2 - 1)) +
      2 * sin (α / 2) * cos (α / 2) * (2 * sin (α / 2) * cos (α / 2)) =
        (2 * cos (α / 2)) ^ 2 by nlinarith [sin_sq_add_cos_sq (α / 2)]]
  exact sqrt_sq (by positivity)

/-- The directions `u` for which `|1 + e^{iu}|` lies in a null set of radii form a
null set. -/
lemma angularMeasure_norm_one_add_mem {Z : Set ℝ} (hZ : MeasurableSet Z)
    (h0 : volume Z = 0) : angularMeasure {u | ‖1 + direction u‖ ∈ Z} = 0 := by
  have hmeas : MeasurableSet {u : Angles | ‖1 + direction u‖ ∈ Z} :=
    hZ.preimage (continuous_const.add direction_continuous).norm.measurable
  refine angularMeasure_eq_zero_of_volume_preimage hmeas ?_
  set Z₀ := Z ∩ Ioo (-2) 2 with hZ₀
  set g : ℝ → ℝ := fun ρ => 2 * arccos (ρ / 2) with hg
  have hdiff : DifferentiableOn ℝ g Z₀ := by
    intro ρ hρ
    have hρ' : ρ / 2 ≠ -1 ∧ ρ / 2 ≠ 1 := ⟨by linarith [hρ.2.1], by linarith [hρ.2.2]⟩
    have h1 : DifferentiableAt ℝ arccos (ρ / 2) := Real.differentiableAt_arccos.2 hρ'
    have h2 : DifferentiableAt ℝ (fun ρ : ℝ => ρ / 2) ρ := differentiableAt_id.div_const 2
    exact ((h1.comp ρ h2).const_mul 2).differentiableWithinAt
  have hZ₀0 : volume Z₀ = 0 := measure_mono_null inter_subset_left h0
  have h₁ : volume (g '' Z₀) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hdiff hZ₀0
  have h₂ : volume ((fun ρ => -g ρ) '' Z₀) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hdiff.neg hZ₀0
  refine measure_mono_null (t := g '' Z₀ ∪ (fun ρ => -g ρ) '' Z₀ ∪ {0}) ?_
    (measure_union_null (measure_union_null h₁ h₂) (measure_singleton 0))
  rintro α ⟨hαZ, hα₁, hα₂⟩
  simp only [mem_preimage, mem_ofPred_eq, direction_real, Circle.coe_exp] at hαZ
  rw [norm_one_add_exp hα₁.le hα₂] at hαZ
  rcases lt_trichotomy α 0 with hneg | rfl | hpos
  · have hc : cos (α / 2) = cos (-α / 2) := by rw [← cos_neg]; ring_nf
    have hcos1 : cos (-α / 2) < 1 := by
      rw [← cos_zero]
      exact cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith) (by linarith)
    have hcos0 : 0 ≤ cos (-α / 2) := cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
    refine Or.inl (Or.inr ⟨2 * cos (α / 2), ⟨hαZ, by rw [hc]; linarith, by rw [hc]; linarith⟩, ?_⟩)
    simp only [hg]
    rw [show 2 * cos (α / 2) / 2 = cos (-α / 2) by rw [hc]; ring,
      arccos_cos (by linarith) (by linarith)]
    ring
  · exact Or.inr rfl
  · have hcos1 : cos (α / 2) < 1 := by
      rw [← cos_zero]
      exact cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith) (by linarith)
    have hcos0 : 0 ≤ cos (α / 2) := cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
    refine Or.inl (Or.inl ⟨2 * cos (α / 2), ⟨hαZ, by linarith, by linarith⟩, ?_⟩)
    simp only [hg]
    rw [show 2 * cos (α / 2) / 2 = cos (α / 2) by ring, arccos_cos (by linarith) (by linarith)]
    ring

/-- Polar coordinates: almost every circle about the origin meets a null set in a
null set of directions. -/
lemma ae_angularMeasure_mul_mem {N : Set ℂ} (hN : MeasurableSet N) (h0 : volume N = 0) :
    ∀ᵐ ρ : ℝ, 0 < ρ → angularMeasure {t | (ρ : ℂ) * direction t ∈ N} = 0 := by
  set F : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * Complex.I) with hF
  have hFm : Measurable F := by fun_prop
  have hint := Complex.lintegral_comp_polarCoord_symm (N.indicator 1)
  rw [lintegral_indicator_one hN, h0] at hint
  simp_rw [Complex.polarCoord_symm_apply] at hint
  have hfm : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal p.1 • N.indicator (1 : ℂ → ENNReal) (F p) := by
    have h1 : Measurable fun p : ℝ × ℝ => ENNReal.ofReal p.1 :=
      ENNReal.measurable_ofReal.comp measurable_fst
    have h2 : Measurable fun p : ℝ × ℝ => N.indicator (1 : ℂ → ENNReal) (F p) :=
      (measurable_one.indicator hN).comp hFm
    exact h1.smul h2
  rw [lintegral_eq_zero_iff' hfm.aemeasurable, Filter.EventuallyEq,
    ae_restrict_iff' (by rw [polarCoord_target]; exact measurableSet_Ioi.prod measurableSet_Ioo)]
    at hint
  set W : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.2 ∈ Ioo (-π) π ∧ F p ∈ N} with hW
  have hWm : MeasurableSet W :=
    (measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_Ioo.preimage measurable_snd).inter (hN.preimage hFm))
  have hW0 : (volume : Measure (ℝ × ℝ)) W = 0 := by
    refine measure_mono_null (fun p hp => ?_) (ae_iff.1 hint)
    obtain ⟨hp1, hp2, hp3⟩ := hp
    simp only [mem_ofPred_eq, polarCoord_target, Pi.zero_apply, _root_.not_imp]
    refine ⟨⟨hp1, hp2⟩, ?_⟩
    simp only [Set.indicator_of_mem hp3, Pi.one_apply, smul_eq_mul, mul_one]
    exact (ENNReal.ofReal_pos.2 hp1).ne'
  rw [Measure.volume_eq_prod, Measure.measure_prod_null hWm] at hW0
  filter_upwards [hW0] with ρ hρ hρpos
  have hY : MeasurableSet {t : Angles | (ρ : ℂ) * direction t ∈ N} :=
    hN.preimage (continuous_const.mul direction_continuous).measurable
  refine angularMeasure_eq_zero_of_volume_preimage hY ?_
  refine measure_mono_null (t := Prod.mk ρ ⁻¹' W ∪ {π}) ?_
    (measure_union_null hρ (measure_singleton π))
  rintro α ⟨hα, hα₁, hα₂⟩
  rcases hα₂.lt_or_eq with hlt | rfl
  · refine Or.inl ⟨hρpos, ⟨hα₁, hlt⟩, ?_⟩
    simp only [mem_preimage, mem_ofPred_eq, direction_real, Circle.coe_exp] at hα
    simp only [hF]
    convert hα using 2
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  · exact Or.inr rfl

/-- The map `(t, u) ↦ e^{it} + e^{iu}` pulls null sets back to null sets. -/
lemma angularMeasure_prod_add_mem {N : Set ℂ} (hN : MeasurableSet N) (h0 : volume N = 0) :
    (angularMeasure.prod angularMeasure)
      {q : Angles × Angles | direction q.1 + direction q.2 ∈ N} = 0 := by
  have hX : MeasurableSet {q : Angles × Angles | direction q.1 + direction q.2 ∈ N} :=
    hN.preimage ((direction_continuous.comp continuous_fst).add
      (direction_continuous.comp continuous_snd)).measurable
  rw [← (measurePreserving_prod_add angularMeasure angularMeasure).measure_preimage
    hX.nullMeasurableSet]
  have hY : MeasurableSet ((fun z : Angles × Angles => (z.1, z.1 + z.2)) ⁻¹'
      {q : Angles × Angles | direction q.1 + direction q.2 ∈ N}) :=
    hX.preimage (measurable_fst.prodMk (measurable_fst.add measurable_snd))
  rw [Measure.prod_apply_symm hY]
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  -- the radii whose circle meets `N` in positive measure, together with `0`
  obtain ⟨Z, hZsub, hZm, hZ0⟩ := exists_measurable_superset_of_null
    (ae_iff.1 (ae_angularMeasure_mul_mem hN h0))
  have hbad := angularMeasure_norm_one_add_mem (hZm.union (measurableSet_singleton 0))
    (measure_union_null hZ0 (measure_singleton 0))
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun u hu => ?_) hbad
  simp only [mem_ofPred_eq] at hu
  have hsec : (fun t => (t, u)) ⁻¹' ((fun z : Angles × Angles => (z.1, z.1 + z.2)) ⁻¹'
      {q : Angles × Angles | direction q.1 + direction q.2 ∈ N}) =
        {t | direction t * (1 + direction u) ∈ N} := by
    ext t
    simp only [mem_preimage, mem_ofPred_eq, direction_add]
    ring_nf
  rw [hsec, angularMeasure_mul_mem] at hu
  simp only [mem_ofPred_eq, mem_union, mem_singleton_iff]
  by_contra hno
  push Not at hno
  apply hu
  have hpos : 0 < ‖1 + direction u‖ := (norm_nonneg _).lt_of_ne (Ne.symm hno.2)
  by_contra hne
  exact hno.1 (hZsub (by simp only [mem_ofPred_eq, _root_.not_imp]; exact ⟨hpos, hne⟩))

/-- A null measurable set which every one of its points sees in positive arc
length on the circle of radius `r` is empty. -/
theorem eq_empty_of_selfSupporting {S : Set ℂ} (hS : MeasurableSet S) (h0 : volume S = 0)
    {r : ℝ} (hr : 0 < r) (h : ∀ p ∈ S, angularMeasure {t | p + r * direction t ∈ S} ≠ 0) :
    S = ∅ := by
  by_contra hne
  obtain ⟨p, hp⟩ := nonempty_iff_ne_empty.2 hne
  have hcont : Continuous fun t : Angles => p + r * direction t :=
    continuous_const.add (continuous_const.mul direction_continuous)
  set E : Set (Angles × Angles) :=
    {q | p + r * direction q.1 ∈ S ∧ p + r * direction q.1 + r * direction q.2 ∈ S} with hE
  have hEm : MeasurableSet E :=
    (hS.preimage (hcont.comp continuous_fst).measurable).inter
      (hS.preimage ((hcont.comp continuous_fst).add
        (continuous_const.mul (direction_continuous.comp continuous_snd))).measurable)
  -- the pairs of steps from `p` that stay in `S` have positive measure
  have hpos : (angularMeasure.prod angularMeasure) E ≠ 0 := by
    rw [Measure.prod_apply hEm]
    intro hzero
    rw [lintegral_eq_zero_iff (measurable_measure_prodMk_left hEm), Filter.EventuallyEq,
      ae_iff] at hzero
    refine h p hp (measure_mono_null (fun t ht => ?_) hzero)
    simp only [mem_ofPred_eq, Pi.zero_apply]
    have : Prod.mk t ⁻¹' E = {u | (p + r * direction t) + r * direction u ∈ S} := by
      ext u
      simp only [hE, mem_preimage, mem_ofPred_eq, and_iff_right_iff_imp]
      exact fun _ => ht
    rw [this]
    exact h _ ht
  -- their endpoints lie in `S`, which is null
  set N : Set ℂ := (fun w => p + (r : ℂ) * w) ⁻¹' S with hN
  have hNm : MeasurableSet N :=
    hS.preimage (continuous_const.add (continuous_const.mul continuous_id)).measurable
  have hN0 : volume N = 0 := by
    have : N = (fun w : ℂ => r • w) ⁻¹' ((fun w => p + w) ⁻¹' S) := by
      ext w
      simp [hN, Complex.real_smul]
    rw [this, Measure.addHaar_preimage_smul volume hr.ne', measure_preimage_add, h0, mul_zero]
  refine hpos (measure_mono_null (fun q hq => ?_) (angularMeasure_prod_add_mem hNm hN0))
  simp only [hN, mem_ofPred_eq, mem_preimage]
  rw [mul_add, ← add_assoc]
  exact hq.2

end Port173

end




/-
# The eight-point configuration

Lemma 1.3 of Jelínek, Kynčl, Stolař and Valla, which they take from Erdős,
Graham, Montgomery, Rothschild, Spencer and Straus, in coordinates. Put
`A = 0`, `B = a`, `C = a ζ`, `D = z`, `B' = ζ z`, `A' = a + ζ z`,
`C' = a ζ̄ + ζ z` and `D' = a - ζ̄ z`. The triples `ABC`, `A'B'C'` are
equilateral of side `a`, `ADB'`, `A'D'B` of side `|z|` and `BDC'`, `B'D'C` of
side `|z - a|`, and `BAD`, `CAB'`, `CBD'`, `B'A'D'`, `C'A'B`, `C'B'D` are
orientation-preserving copies of the triangle `(a, 0, z)`.

(i) If `A, B, C` have one color, one of the six copies is monochromatic.
(ii) If `B, A, D` have one color, one of the six equilateral triples is
monochromatic. The positive-measure form of (ii) composes the configuration
with a variable motion, which preserves area times arc length.

In the proofs `ζ̄` is written `1 - ζ`, so that every incidence of the
configuration is a ring identity. The copy of `(0, a, b)` with multiplier `m`
and translation `t`, placed by the motion `(p, u)`, is the copy placed by
`(p + u t, u m)`; each listed triple is such a copy of the template or of a
standard equilateral triangle.
-/


noncomputable section

namespace Port173

open MeasureTheory OAI.EuclideanFiveColor

namespace EightPoint

/-- Composing a placement with a fixed rotation and a translation along the placed frame
preserves area times normalized arc length. -/
lemma ae_motion {P : ℂ → ℂ → Prop} (X w : ℂ) (hw : ‖w‖ = 1)
    (h : ∀ᵐ q ∂(volume : Measure ℂ).prod angularMeasure, P q.1 (direction q.2)) :
    ∀ᵐ q ∂(volume : Measure ℂ).prod angularMeasure,
      P (q.1 + direction q.2 * X) (direction q.2 * w) := by
  obtain ⟨t, ht⟩ := Circle.exp_surjective (⟨w, mem_sphere_zero_iff_norm.2 hw⟩ : Circle)
  set φ : Angles := (t : Angles)
  have hφ : direction φ = w := by simp [φ, ht]
  have hS : MeasurePreserving (fun q : Angles × ℂ => (q.1 + φ, q.2 + direction q.1 * X))
      (angularMeasure.prod (volume : Measure ℂ)) (angularMeasure.prod volume) :=
    (measurePreserving_add_right angularMeasure φ).skew_product
      (g := fun θ p => p + direction θ * X)
      (by
        have := direction_continuous
        exact Continuous.measurable (by fun_prop))
      (Filter.Eventually.of_forall fun θ => map_add_right_eq_self volume _)
  have hT : MeasurePreserving
      (fun q : ℂ × Angles => (q.1 + direction q.2 * X, q.2 + φ))
      ((volume : Measure ℂ).prod angularMeasure) ((volume : Measure ℂ).prod angularMeasure) :=
    Measure.measurePreserving_swap.comp (hS.comp Measure.measurePreserving_swap)
  filter_upwards [hT.quasiMeasurePreserving.tendsto_ae.eventually h] with q hq
  simpa [direction, AddCircle.toCircle_add, ← hφ] using hq

/-- The copy of `(0, a, b)` with multiplier `m` and translation `t`, placed by `(p, u)`. -/
lemma monoCopy_iff (c : ℂ → Fin 2) (a b p u t m x y : ℂ) (hx : t + m * a = x)
    (hy : t + m * b = y) :
    MonoCopy c a b (p + u * t) (u * m) ↔
      c (p + u * x) = c (p + u * t) ∧ c (p + u * y) = c (p + u * t) := by
  subst hx hy
  have e₁ : p + u * t + u * m * a = p + u * (t + m * a) := by ring
  have e₂ : p + u * t + u * m * b = p + u * (t + m * b) := by ring
  simp only [MonoCopy, e₁, e₂]

/-- The color bookkeeping of part (i). -/
lemma forcing_i : ∀ A B C D B' A' C' D' : Fin 2, B = A → C = A →
    ¬ (B = A ∧ D = A) → ¬ (C = A ∧ B' = A) → ¬ (C = B ∧ D' = B) →
    ¬ (B' = A' ∧ D' = A') → ¬ (C' = A' ∧ B = A') → ¬ (C' = B' ∧ D = B') → False := by
  intro A B C D B' A' C' D'
  omega

/-- The color bookkeeping of part (ii). -/
lemma forcing_ii : ∀ A B C D B' A' C' D' : Fin 2, B = A → D = A →
    ¬ (D = A ∧ B' = A) → ¬ (B = A ∧ C = A) → ¬ (D = B ∧ C' = B) →
    ¬ (B' = A' ∧ C' = A') → ¬ (D' = A' ∧ B = A') → ¬ (D' = B' ∧ C = B') → False := by
  intro A B C D B' A' C' D'
  omega

end EightPoint

open EightPoint

/-- Part (i): a monochromatic equilateral triangle of side `a` forces a
monochromatic copy of every triangle with a side `a`. -/
theorem not_avoids_of_not_avoidsEq (c : ℂ → Fin 2) {a : ℝ} {z : ℂ}
    (h : ¬ AvoidsEq c a) : ¬ Avoids c a z := by
  intro hav
  simp only [AvoidsEq, Avoids, not_forall, not_not] at h
  obtain ⟨p, u, hu, hABC⟩ := h
  have key : ∀ t m x y : ℂ, ‖m‖ = 1 → t + m * a = x → t + m * z = y →
      ¬ (c (p + u * x) = c (p + u * t) ∧ c (p + u * y) = c (p + u * t)) := by
    intro t m x y hm hx hy
    rw [← monoCopy_iff c a z p u t m x y hx hy]
    exact hav _ _ (by rw [norm_mul, hu, hm, one_mul])
  -- `BAD`, `CAB'`, `CBD'`, `B'A'D'`, `C'A'B`, `C'B'D`
  have h₁ := key 0 1 a z (by simp) (by ring) (by ring)
  have h₂ := key 0 ζ (a * ζ) (ζ * z) norm_ζ (by ring) (by ring)
  have h₃ := key a (ζ - 1) (a * ζ) (a - (1 - ζ) * z) norm_ζ_sub_one (by ring) (by ring)
  have h₄ := key (a + ζ * z) (-1) (ζ * z) (a - (1 - ζ) * z) (by simp) (by ring) (by ring)
  have h₅ := key (a + ζ * z) (-ζ) (a * (1 - ζ) + ζ * z) a (by simp [norm_ζ]) (by ring)
    (by ring)
  have h₆ := key (ζ * z) (1 - ζ) (a * (1 - ζ) + ζ * z) z norm_one_sub_ζ (by ring) (by ring)
  simp only [mul_zero, add_zero] at h₁ h₂
  exact forcing_i _ _ _ _ _ _ _ _ hABC.1 hABC.2 h₁ h₂ h₃ h₄ h₅ h₆

/-- Part (ii), in measure form: if almost no equilateral triangle of side `a`,
`|z|` or `|z - a|` is monochromatic, then almost no copy of `(0, a, z)` is. -/
theorem weaklyAvoids_of_weaklyAvoidsEq (c : ℂ → Fin 2) {a : ℝ} (ha : 0 < a) {z : ℂ}
    (hz0 : z ≠ 0) (hza : z ≠ a) (h₁ : WeaklyAvoidsEq c a) (h₂ : WeaklyAvoidsEq c ‖z‖)
    (h₃ : WeaklyAvoidsEq c ‖z - a‖) : WeaklyAvoids c a z := by
  have key : ∀ {s : ℝ}, 0 < s → WeaklyAvoidsEq c s → ∀ X Y Z : ℂ, ‖Y - X‖ = s →
      Z = X + ζ * (Y - X) → ∀ᵐ q ∂(volume : Measure ℂ).prod angularMeasure,
        ¬ (c (q.1 + direction q.2 * Y) = c (q.1 + direction q.2 * X) ∧
          c (q.1 + direction q.2 * Z) = c (q.1 + direction q.2 * X)) := by
    intro s hs h X Y Z hY hZ
    have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    have hw : ‖(Y - X) / s‖ = 1 := by
      rw [norm_div, hY, Complex.norm_real, Real.norm_of_nonneg hs.le, div_self hs.ne']
    filter_upwards [ae_motion (P := fun p u => ¬ MonoCopy c s (s * ζ) p u) X _ hw h]
      with q hq
    rwa [monoCopy_iff c s (s * ζ) q.1 (direction q.2) X ((Y - X) / s) Y Z
      (by field_simp; ring) (by rw [hZ]; field_simp)] at hq
  have hz : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hza' : 0 < ‖z - a‖ := norm_pos_iff.2 (sub_ne_zero.2 hza)
  -- `ADB'`, `ABC`, `BDC'`, `A'B'C'`, `A'D'B`, `B'D'C`
  have e₁ := key hz h₂ 0 z (ζ * z) (by simp) (by ring)
  have e₂ := key ha h₁ 0 a (a * ζ) (by simp [ha.le]) (by ring)
  have e₃ := key hza' h₃ a z (a * (1 - ζ) + ζ * z) rfl (by ring)
  have e₄ := key ha h₁ (a + ζ * z) (ζ * z) (a * (1 - ζ) + ζ * z)
    (by rw [show ζ * z - (a + ζ * z) = -(a : ℂ) by ring, norm_neg]; simp [ha.le]) (by ring)
  have e₅ := key hz h₂ (a + ζ * z) (a - (1 - ζ) * z) a
    (by rw [show a - (1 - ζ) * z - (a + ζ * z) = -z by ring, norm_neg]) (by ring)
  have e₆ := key hza' h₃ (ζ * z) (a - (1 - ζ) * z) (a * ζ)
    (by rw [show a - (1 - ζ) * z - ζ * z = a - z by ring, norm_sub_rev]) (by ring)
  filter_upwards [e₁, e₂, e₃, e₄, e₅, e₆] with q h₁ h₂ h₃ h₄ h₅ h₆ hBAD
  simp only [mul_zero, add_zero] at h₁ h₂
  exact forcing_ii _ _ _ _ _ _ _ _ hBAD.1 hBAD.2 h₁ h₂ h₃ h₄ h₅ h₆

end Port173

end










/-
# Circle exclusion of two equilateral scales near one

Let `2/3 < x < 3/2` with `x ≠ 1`, and let `c` be a measurable two-coloring that
weakly avoids the equilateral triangles of sides `1` and `x`. One of the apex
angles `γ` of the isosceles triangles with sides `1, 1, x` and `x, x, 1` is an
irrational multiple of `π`; let `r` be its leg.

At a point of the measure-theoretic boundary of the red class, if the circle of
radius `r` met the boundary in a null set, its red density points `R` would
satisfy `R + π/3 = Rᶜ` and `R + γ = Rᶜ` up to null sets, so `R` would be invariant
under the dense group generated by `γ - π/3` and would also satisfy
`R + π/3 = Rᶜ`, which is impossible. So every boundary point sees the boundary
in positive arc length on its circle; the map `(θ, φ) ↦ p + r e^{iθ} + r e^{iφ}`
then gives the null boundary positive area unless it is empty. A nested
sequence of squares of red proportion one half shows the boundary is not empty.
-/


noncomputable section

namespace Port173

open MeasureTheory Set Real OAI.EuclideanFiveColor

/-- The direction `e^{iπ/3}` is `ζ`. -/
lemma direction_pi_div_three : direction ((π / 3 : ℝ) : Angles) = ζ := by
  rw [direction_real, Circle.coe_exp]
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re, cos_pi_div_three]; simp [ζ]
  · rw [Complex.exp_ofReal_mul_I_im, sin_pi_div_three]; simp [ζ]

/-- The chord `|e^{2iA} - 1| = 2 sin A` for `0 ≤ sin A`. -/
lemma norm_direction_two_mul_sub_one {A : ℝ} (hA : 0 ≤ sin A) :
    ‖direction ((2 * A : ℝ) : Angles) - 1‖ = 2 * sin A := by
  rw [direction_real, Circle.coe_exp, Complex.norm_def]
  have hre : (Complex.exp (↑(2 * A) * Complex.I) - 1).re = cos (2 * A) - 1 := by
    rw [Complex.sub_re, Complex.exp_ofReal_mul_I_re, Complex.one_re]
  have him : (Complex.exp (↑(2 * A) * Complex.I) - 1).im = sin (2 * A) := by
    rw [Complex.sub_im, Complex.exp_ofReal_mul_I_im, Complex.one_im, sub_zero]
  rw [Complex.normSq_apply, hre, him, cos_two_mul, sin_two_mul]
  rw [show (2 * cos A ^ 2 - 1 - 1) * (2 * cos A ^ 2 - 1 - 1) +
      2 * sin A * cos A * (2 * sin A * cos A) = (2 * sin A) ^ 2 by
    nlinarith [sin_sq_add_cos_sq A]]
  exact sqrt_sq (by positivity)

/-- The core of circle exclusion: no measurable coloring weakly avoids both the
equilateral triangle of side `r` and the isosceles triangle with legs `r` and
apex angle `γ`, when `γ / π` is irrational. -/
theorem circle_core {c : ℂ → Fin 2} (hc : Measurable c) {r γ : ℝ} (hr : 0 < r)
    (hγ : Irrational (γ / π)) (h₁ : WeaklyAvoids c r (r * direction ((π / 3 : ℝ) : Angles)))
    (h₂ : WeaklyAvoids c r (r * direction (γ : Angles))) : False := by
  set S := boundary c with hSdef
  have hS : MeasurableSet S := measurableSet_boundary hc
  have hS0 : volume S = 0 := volume_boundary hc
  have hcompl0 : {z | c z ≠ 0} = {z | c z = 1} := by
    ext z; simp only [mem_ofPred_eq]; generalize c z = a; fin_cases a <;> decide
  have hcompl1 : {z | c z ≠ 1} = {z | c z = 0} := by
    ext z; simp only [mem_ofPred_eq]; generalize c z = a; fin_cases a <;> decide
  have hmemS : ∀ q, ¬ DensityZero {z | c z ≠ 0} q → ¬ DensityZero {z | c z ≠ 1} q → q ∈ S := by
    intro q h0 h1
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · rw [← hcompl1]; exact h1
    · rw [← hcompl0]; exact h0
  -- the circle of radius `r` about a boundary point meets the boundary in positive length
  have hsupp : ∀ p ∈ S, angularMeasure {t | p + r * direction t ∈ S} ≠ 0 := by
    intro p hp hΘ
    have hcont : Continuous fun t : Angles => p + r * direction t :=
      continuous_const.add (continuous_const.mul direction_continuous)
    set R : Fin 2 → Set Angles := fun i => {t | DensityZero {z | c z ≠ i} (p + r * direction t)}
      with hRdef
    have hRm : ∀ i, MeasurableSet (R i) := fun i =>
      (measurableSet_densityZero (measurableSet_eq_fun hc measurable_const).compl).preimage
        hcont.measurable
    -- no two density points of one class at angular distance `x` on the circle
    have hdisj : ∀ (i : Fin 2) (x : Angles), WeaklyAvoids c r (r * direction x) →
        R i ∩ (· + x) ⁻¹' R i = ∅ := by
      intro i x hx
      refine eq_empty_iff_forall_notMem.2 fun t ⟨ht, htx⟩ => ?_
      refine apex_density hc hx (hp i) t ?_ ?_
      · have ht' : DensityZero {z | c z ≠ i} (p + r * direction t) := ht
        rwa [mul_comm] at ht'
      · have htx' : DensityZero {z | c z ≠ i} (p + r * direction (t + x)) := htx
        have : p + r * direction (t + x) = p + direction t * (↑r * direction x) := by
          rw [direction_add]; ring
        rwa [this] at htx'
    have hΘ' : ∀ x : Angles, angularMeasure ((· + x) ⁻¹' {t | p + r * direction t ∈ S}) = 0 :=
      fun x => ((measurePreserving_add_right angularMeasure x).measure_preimage
        (hS.preimage hcont.measurable).nullMeasurableSet).trans hΘ
    refine circle_alternation (hRm 0) hγ ?_ ?_ ?_
    · rw [hdisj 0 _ h₁, measure_empty]
    · refine measure_mono_null (t := (R 1 ∩ (· + ((π / 3 : ℝ) : Angles)) ⁻¹' R 1) ∪
        {t | p + r * direction t ∈ S} ∪
          (· + ((π / 3 : ℝ) : Angles)) ⁻¹' {t | p + r * direction t ∈ S}) ?_ ?_
      · rintro t ⟨ht, htx⟩
        by_cases h1 : t ∈ R 1
        · by_cases h2 : t + ((π / 3 : ℝ) : Angles) ∈ R 1
          · exact Or.inl (Or.inl ⟨h1, h2⟩)
          · exact Or.inr (hmemS _ htx h2)
        · exact Or.inl (Or.inr (hmemS _ ht h1))
      · rw [hdisj 1 _ h₁]
        simp only [empty_union]
        exact measure_union_null hΘ (hΘ' _)
    · rw [hdisj 0 _ h₂, measure_empty]
  have hempty := eq_empty_of_selfSupporting hS hS0 hr hsupp
  -- both classes have density points
  have hpt : ∀ i : Fin 2, ∃ q, DensityZero {z | c z ≠ i} q := by
    intro i
    have hK : MeasurableSet {z | c z ≠ i} := (measurableSet_eq_fun hc measurable_const).compl
    have hpos := volume_ne_zero_of_weaklyAvoids hc h₁ i
    by_contra hno
    push Not at hno
    refine hpos (measure_mono_null (fun q hq => ?_) (ae_iff.1 (ae_densityZero hK)))
    simp only [mem_ofPred_eq, _root_.not_imp, not_not]
    exact ⟨hq, hno q⟩
  obtain ⟨a, ha⟩ := hpt 0
  obtain ⟨b, hb⟩ := hpt 1
  have hA : MeasurableSet {z | c z = 0} := measurableSet_eq_fun hc measurable_const
  have hAc : {z | c z = 0}ᶜ = {z | c z = 1} := by rw [← hcompl0]; rfl
  rw [hcompl0, ← hAc] at ha
  rw [hcompl1] at hb
  obtain ⟨z, hz0, hz1⟩ := exists_not_densityZero hA ha hb
  rw [hAc, ← hcompl0] at hz1
  have : z ∈ S := hmemS z hz1 (by rwa [hcompl1])
  rw [hempty] at this
  exact this

/-- No measurable two-coloring weakly avoids the equilateral triangles of sides
`1` and `x` when `2/3 < x < 3/2` and `x ≠ 1`. -/
theorem circle_exclusion {x : ℝ} (hx₁ : 2 / 3 < x) (hx₂ : x < 3 / 2) (hx : x ≠ 1)
    (c : ℂ → Fin 2) (hc : Measurable c) (h₁ : WeaklyAvoidsEq c 1)
    (h₂ : WeaklyAvoidsEq c x) : False := by
  have hx0 : 0 < x := by linarith
  rcases irrational_apex_angle hx₁ hx₂ hx with h | h
  · -- the circle of radius `1`, with apex angle `2 arcsin (x / 2)`
    set A := arcsin (x / 2) with hA
    have hsinA : sin A = x / 2 := sin_arcsin (by linarith) (by linarith)
    have hchord : ‖direction ((2 * A : ℝ) : Angles) - 1‖ = x := by
      rw [norm_direction_two_mul_sub_one (by rw [hsinA]; positivity), hsinA]; ring
    have hchord' : ‖direction ((2 * A : ℝ) : Angles) - ((1 : ℝ) : ℂ)‖ = x := by
      rw [Complex.ofReal_one]; exact hchord
    have hiso : WeaklyAvoids c (1 : ℝ) (direction ((2 * A : ℝ) : Angles)) :=
      weaklyAvoids_of_weaklyAvoidsEq c one_pos
        (by intro h0; simpa [h0] using direction_norm ((2 * A : ℝ) : Angles))
        (by intro h1; rw [h1, sub_self, norm_zero] at hchord'; linarith)
        h₁ (by rw [direction_norm]; exact h₁) (by rw [hchord']; exact h₂)
    refine circle_core hc (r := 1) one_pos h ?_ ?_
    · rw [direction_pi_div_three]; exact h₁
    · simpa using hiso
  · -- the circle of radius `x`, with apex angle `2 arcsin (1 / (2 x))`
    set B := arcsin (1 / (2 * x)) with hB
    have hsinB : sin B = 1 / (2 * x) :=
      sin_arcsin
        (by
          have : 0 < 1 / (2 * x) := by positivity
          linarith)
        (by rw [div_le_one (by positivity)]; linarith)
    have hchord : ‖direction ((2 * B : ℝ) : Angles) - 1‖ = 1 / x := by
      rw [norm_direction_two_mul_sub_one (by rw [hsinB]; positivity), hsinB]; field_simp
    set z : ℂ := x * direction ((2 * B : ℝ) : Angles) with hz
    have hzn : ‖z‖ = x := by rw [hz, norm_mul, direction_norm]; simp [abs_of_pos hx0]
    have hzx : ‖z - x‖ = 1 := by
      rw [hz, show (x : ℂ) * direction ((2 * B : ℝ) : Angles) - x =
        x * (direction ((2 * B : ℝ) : Angles) - 1) by ring, norm_mul, hchord]
      simp [abs_of_pos hx0, hx0.ne']
    have hiso : WeaklyAvoids c x z :=
      weaklyAvoids_of_weaklyAvoidsEq c hx0
        (by intro h0; rw [h0, norm_zero] at hzn; linarith)
        (by intro h1; rw [h1, sub_self, norm_zero] at hzx; norm_num at hzx)
        h₂ (by rw [hzn]; exact h₂) (by rw [hzx]; exact h₁)
    exact circle_core hc hx0 h (by rw [direction_pi_div_three]; exact h₂) hiso

end Port173

end

theorem OMA.solution : OMA.R_Erdos173_erdos_173_R1_H2_R1.H3 := by
  intro x hlow hhigh hx c hc h1 h2
  exact Port173.circle_exclusion hlow hhigh hx c hc h1 h2
