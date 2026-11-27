import FormalConjectures.ErdosProblems.«996»

-- Credit: @senamakel
import Mathlib

/- Adapted from github.com/hongjin-he/erdos-lean (commit efede9693a3192e324bc092e5510f16a2aff1804), Copyright 2026 HongJin HE, Apache-2.0 (Licensed under the Apache License, Version 2.0; http://www.apache.org/licenses/LICENSE-2.0). Mathematics: B. S. Ho, arXiv:2604.18535, Cor 1.4. Definitions IsLacunary and fourierPartial derive from google-deepmind/formal-conjectures (Apache-2.0). Modified: merged into one file, abbreviations expanded, namespace renamed, ported to Lean 4.33.1 / Mathlib. -/

/- ### Statement -/

/-!
Section: Erdős Problem 996 (JSP-000829): statement

Source: <https://www.erdosproblems.com/996>, catalogued as JSP-000829 in
<https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000829>.

> Let `n₁ < n₂ < ⋯` be a lacunary sequence of integers, and let `f ∈ L²([0,1])`.
> Let `fₙ` be the `n`th partial sum of the Fourier series of `f`. Is there an absolute
> constant `C > 0` such that, if `‖f - fₙ‖₂ ≪ 1 / (log log log n)^C`, then
> `lim_{N → ∞} (1/N) ∑_{k ≤ N} f({α n_k}) = ∫₀¹ f` for almost every `α`?

The answer is **no** (B. S. Ho, arXiv:2604.18535, Corollary 1.4).

`IsLacunary`, `fourierPartial` and the shape of `OMA.Port23Statement` follow
`google-deepmind/formal-conjectures` (`FormalConjectures/ErdosProblems/996.lean` at commit
`a9fb8e86c0`, and `FormalConjecturesForMathlib/NumberTheory/Lacunary.lean`),
Apache License 2.0, copied here so that this project does not depend on that repository.
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real

namespace OMA.Port23

/-- A sequence is lacunary if there is some `c > 1` with `c * n k < n (k + 1)` for all
sufficiently large `k` (as in formal-conjectures). -/
def IsLacunary (n : ℕ → ℕ) : Prop := ∃ c > (1 : ℝ), ∀ᶠ k in atTop, c * n k < n (k + 1)

/-- The symmetric Fourier partial sum `S_k f = ∑_{|i| ≤ k} f̂(i) e_i`. -/
noncomputable def fourierPartial {T : ℝ} [hT : Fact (0 < T)] (f : Lp ℂ 2 (@haarAddCircle T hT))
    (k : ℕ) : AddCircle T → ℂ :=
  fun x => ∑ i ∈ Icc (-k : ℤ) k, fourierCoeff f i • fourier i x

/-- The Fourier-tail hypothesis `‖f - S_k f‖₂ = O((log log log k)^{-C})`. -/
def FourierTailBound (C : ℝ) (f : Lp ℂ 2 (haarAddCircle (T := 1))) : Prop :=
  (fun k : ℕ => (eLpNorm (⇑f - fourierPartial f k) 2 (haarAddCircle (T := 1))).toReal) =O[atTop]
    (fun k : ℕ => 1 / (log (log (log k))) ^ C)

/-- The lacunary averages `(1/N) ∑_{k < N} f(n_k x)` converge to `∫ f` for almost every `x`. -/
def LacunaryAveragesConverge (f : Lp ℂ 2 (haarAddCircle (T := 1))) (n : ℕ → ℕ) : Prop :=
  ∀ᵐ x ∂(haarAddCircle (T := 1)),
    Tendsto (fun N : ℕ => (∑ k ∈ range N, f (n k • x)) / N) atTop
      (𝓝 (∫ t, f t ∂haarAddCircle))

/-- Erdős's question (#996), literally: is there an absolute `C > 0` such that the Fourier-tail
bound forces a.e. convergence of lacunary averages, for every `f ∈ L²` and every lacunary `n`? -/
def OMA.Port23Statement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (f : Lp ℂ 2 (haarAddCircle (T := 1))) (n : ℕ → ℕ),
    IsLacunary n → FourierTailBound C f → LacunaryAveragesConverge f n

/-- A strong lacunarity condition satisfied by the counterexample (`n_{k+1} ≥ 2 n_k`, `n 0 ≥ 1`). -/
def IsDyadicLacunary (n : ℕ → ℕ) : Prop := 1 ≤ n 0 ∧ ∀ k, 2 * n k ≤ n (k + 1)

lemma IsDyadicLacunary.isLacunary {n : ℕ → ℕ} (hn : IsDyadicLacunary n) : IsLacunary n := by
  refine ⟨3 / 2, by norm_num, Eventually.of_forall fun k => ?_⟩
  have hpos : ∀ k, 1 ≤ n k := by
    intro k
    induction k with
    | zero => exact hn.1
    | succ k ih => have := hn.2 k; omega
  have h1 : (1 : ℝ) ≤ n k := by exact_mod_cast hpos k
  have h2 : (2 : ℝ) * n k ≤ n (k + 1) := by exact_mod_cast hn.2 k
  linarith

end OMA.Port23

/- ### Defs -/

/-! # Erdős 996: shared definitions (spike, digit windows, block). -/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real

namespace OMA.Port23


/-- The dyadic spike `φ_d = (1_{[0,2^{-d})} - 2^{-d}) / √(2^{-d}(1-2^{-d}))` on the circle. -/
noncomputable def spike (d : ℕ) (x : (AddCircle (1 : ℝ))) : ℝ :=
  ((Set.indicator (QuotientAddGroup.mk '' Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d)) 1 x : ℝ) -
      (2 : ℝ)⁻¹ ^ d) / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d))

/-- A set is *determined by the digit window* `[a, b)` if membership of `x` depends only on
binary digits `a+1, …, b` of `x`. -/
def DeterminedByWindow (a b : ℕ) (E : Set (AddCircle (1 : ℝ))) : Prop :=
  ∀ x y : (AddCircle (1 : ℝ)), (∀ j, a ≤ j → j < b →
      Int.fract ((2 : ℝ) ^ j * (AddCircle.equivIco 1 0 x : ℝ)) < 2⁻¹ ↔
      Int.fract ((2 : ℝ) ^ j * (AddCircle.equivIco 1 0 y : ℝ)) < 2⁻¹) → (x ∈ E ↔ y ∈ E)

/-- The block `F(x) = √(λ/L) ∑_{q=1}^{L} φ_d(2^{U+qD} x)`. -/
noncomputable def block (lam : ℝ) (L d D U : ℕ) (x : (AddCircle (1 : ℝ))) : ℝ :=
  Real.sqrt (lam / L) * ∑ q ∈ Finset.Icc 1 L, spike d ((2 ^ (U + q * D) : ℕ) • x)

end OMA.Port23

/- ### SpikeGe -/

/-! # Erdős 996: pointwise lower bound for the spike. -/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real

namespace OMA.Port23


/-- Lower floor of a spike: `φ_d ≥ -g_d` with `g_d = 1/√(2^d - 1)`. -/
lemma spike_ge (d : ℕ) (hd : 1 ≤ d) (x : (AddCircle (1 : ℝ))) :
    -(1 / Real.sqrt (2 ^ d - 1)) ≤ spike d x := by
  have hp : (0 : ℝ) < (2 : ℝ)⁻¹ ^ d := by positivity
  have h2 : (2 : ℝ) ^ d * (2 : ℝ)⁻¹ ^ d = 1 := by rw [← mul_pow]; norm_num
  have h1 : (1 : ℝ) < 2 ^ d := one_lt_pow₀ (by norm_num) (by omega)
  have hq : 0 < Real.sqrt (2 ^ d - 1) := Real.sqrt_pos.2 (by linarith)
  have hs : Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) =
      (2 : ℝ)⁻¹ ^ d * Real.sqrt (2 ^ d - 1) := by
    rw [show (2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d) = ((2 : ℝ)⁻¹ ^ d) ^ 2 * (2 ^ d - 1) by
      linear_combination (-(2 : ℝ)⁻¹ ^ d) * h2]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hp.le]
  have hI : (0 : ℝ) ≤ Set.indicator (QuotientAddGroup.mk '' Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d))
      (1 : (AddCircle (1 : ℝ)) → ℝ) x :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hpq : 0 < (2 : ℝ)⁻¹ ^ d * Real.sqrt (2 ^ d - 1) := mul_pos hp hq
  have he : -(1 / Real.sqrt (2 ^ d - 1)) =
      (0 - (2 : ℝ)⁻¹ ^ d) / ((2 : ℝ)⁻¹ ^ d * Real.sqrt (2 ^ d - 1)) := by
    field_simp
    ring
  unfold spike
  rw [hs, he, div_le_div_iff_of_pos_right hpq]
  linarith

end OMA.Port23

/- ### SpikeFourierSupport -/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real

namespace OMA.Port23


/-- Fourier coefficients of `x ↦ g (n • x)` vanish off the multiples of `n`. -/
lemma fourierCoeff_nsmul_comp_eq_zero (n : ℕ) (hn : 0 < n) (g : (AddCircle (1 : ℝ)) → ℂ) (r : ℤ)
    (h : ¬ (n : ℤ) ∣ r) : fourierCoeff (fun x : (AddCircle (1 : ℝ)) => g (n • x)) r = 0 := by
  obtain ⟨a, ha_def⟩ : ∃ a : (AddCircle (1 : ℝ)), a = (((1 : ℝ) / n : ℝ) : (AddCircle (1 : ℝ))) := ⟨_, rfl⟩
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have ha : n • a = 0 := by
    have e : ((n • ((1 : ℝ) / n) : ℝ) : (AddCircle (1 : ℝ))) = n • (((1 : ℝ) / n : ℝ) : (AddCircle (1 : ℝ))) :=
      AddCircle.coe_nsmul (1 : ℝ)
    rw [ha_def, ← e, nsmul_eq_mul, mul_one_div_cancel hn']
    exact AddCircle.coe_period (1 : ℝ)
  have hI : fourierCoeff (fun x : (AddCircle (1 : ℝ)) => g (n • x)) r =
      fourier (-r) a * fourierCoeff (fun x : (AddCircle (1 : ℝ)) => g (n • x)) r := by
    unfold fourierCoeff
    rw [← integral_const_mul]
    have hshift := integral_add_right_eq_self (μ := (haarAddCircle (T := 1)))
      (fun x : (AddCircle (1 : ℝ)) => fourier (-r) x • g (n • x)) a
    rw [← hshift]
    congr 1
    funext x
    have hf : fourier (-r) (x + a) = fourier (-r) x * fourier (-r) a := by
      rw [fourier_apply, fourier_apply, fourier_apply, smul_add, AddCircle.toCircle_add]
      rfl
    simp only [smul_add, ha, add_zero, smul_eq_mul, hf]
    ring
  have hne : fourier (-r) a ≠ 1 := by
    rw [ha_def, fourier_coe_apply]
    intro he
    rw [Complex.exp_eq_one_iff] at he
    obtain ⟨k, hk⟩ := he
    push_cast at hk
    have hpi : (2 * π * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have h1 : -(r : ℂ) * (1 / (n : ℂ)) = k := by
      apply mul_left_cancel₀ hpi
      linear_combination hk
    have h2 : (r : ℂ) = -(k : ℂ) * n := by
      rw [← h1]; field_simp
    have h3 : r = -k * n := by exact_mod_cast h2
    exact h ⟨-k, by rw [h3]; ring⟩
  have : (1 - fourier (-r) a) * fourierCoeff (fun x : (AddCircle (1 : ℝ)) => g (n • x)) r = 0 := by
    rw [sub_mul, one_mul, ← hI, sub_self]
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd (sub_eq_zero.mp h0).symm hne
  · exact h0

/-- Dilation formula: `\widehat{g(n ·)}(n s) = \hat g(s)`. -/
lemma fourierCoeff_nsmul_comp_mul (n : ℕ) (hn : 0 < n) (g : (AddCircle (1 : ℝ)) → ℂ)
    (hg : AEStronglyMeasurable g (haarAddCircle (T := 1))) (s : ℤ) :
    fourierCoeff (fun x : (AddCircle (1 : ℝ)) => g (n • x)) ((n : ℤ) * s) = fourierCoeff g s := by
  have hmp : MeasurePreserving (fun x : (AddCircle (1 : ℝ)) => (n : ℤ) • x) (haarAddCircle (T := 1)) (haarAddCircle (T := 1)) :=
    Measure.measurePreserving_zsmul (haarAddCircle (T := 1)) (by exact_mod_cast hn.ne')
  have hF : AEStronglyMeasurable (fun y : (AddCircle (1 : ℝ)) => fourier (-s) y • g y) (haarAddCircle (T := 1)) :=
    (map_continuous (fourier (-s))).aestronglyMeasurable.smul hg
  have hpt : ∀ x : (AddCircle (1 : ℝ)), fourier (-((n : ℤ) * s)) x • g (n • x) =
      (fun y : (AddCircle (1 : ℝ)) => fourier (-s) y • g y) ((n : ℤ) • x) := by
    intro x
    show fourier (-((n : ℤ) * s)) x • g (n • x) = fourier (-s) ((n : ℤ) • x) • g ((n : ℤ) • x)
    have e : n • x = (n : ℤ) • x := (natCast_zsmul x n).symm
    rw [e, fourier_apply, fourier_apply, smul_smul, show -((n : ℤ) * s) = -s * (n : ℤ) by ring]
  rw [fourierCoeff, fourierCoeff]
  calc ∫ t, fourier (-((n : ℤ) * s)) t • g (n • t) ∂(haarAddCircle (T := 1))
      = ∫ t, (fun y : (AddCircle (1 : ℝ)) => fourier (-s) y • g y) ((n : ℤ) • t) ∂(haarAddCircle (T := 1)) :=
        integral_congr_ae (ae_of_all _ hpt)
    _ = ∫ y, fourier (-s) y • g y ∂(Measure.map (fun x : (AddCircle (1 : ℝ)) => (n : ℤ) • x) (haarAddCircle (T := 1))) :=
        (integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hF)).symm
    _ = ∫ y, fourier (-s) y • g y ∂(haarAddCircle (T := 1)) := by rw [hmp.map_eq]

lemma measurableSet_spikeSet (d : ℕ) :
    MeasurableSet (QuotientAddGroup.mk '' Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d) : Set (AddCircle (1 : ℝ))) := by
  have hb : (0 : ℝ) < (2 : ℝ)⁻¹ ^ d := by positivity
  rw [← Set.Ioo_insert_left hb, Set.image_insert_eq]
  exact ((QuotientAddGroup.isOpenMap_coe (N := AddSubgroup.zmultiples (1 : ℝ))) _
    isOpen_Ioo).measurableSet.insert _

lemma measurable_spike (d : ℕ) : Measurable (spike d) := by
  unfold spike
  exact ((measurable_one.indicator (measurableSet_spikeSet d)).sub measurable_const).div_const _

lemma mem_spikeSet_iff (d : ℕ) (hd : 1 ≤ d) (x : ℝ)
    (hx : x ∈ Set.Ioc ((2 : ℝ)⁻¹ ^ d - 1) ((2 : ℝ)⁻¹ ^ d)) :
    ((x : (AddCircle (1 : ℝ))) ∈ (QuotientAddGroup.mk '' Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d) : Set (AddCircle (1 : ℝ)))) ↔
      x ∈ Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d) := by
  constructor
  · rintro ⟨u, hu, hux⟩
    have hb : (2 : ℝ)⁻¹ ^ d ≤ 2⁻¹ := pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
    have hux' : ((x : ℝ) : (AddCircle (1 : ℝ))) = ((u : ℝ) : (AddCircle (1 : ℝ))) := hux.symm
    have h0 : ((x - u : ℝ) : (AddCircle (1 : ℝ))) = 0 := by
      rw [AddCircle.coe_sub, hux', sub_self]
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h0
    rw [zsmul_eq_mul, mul_one] at hk
    have hk1 : (k : ℝ) < 1 := by linarith [hx.2, hu.1]
    have hk2 : (-1 : ℝ) < k := by linarith [hx.1, hu.2]
    have hk0 : k = 0 := by
      have : k < 1 := by exact_mod_cast hk1
      have : -1 < k := by exact_mod_cast hk2
      omega
    rw [hk0] at hk
    push_cast at hk
    have : x = u := by linarith
    rw [this]; exact hu
  · intro hx'
    exact ⟨x, hx', rfl⟩

/-- For `d ≥ 1`, the spike `φ_d` has vanishing Fourier coefficients at nonzero multiples of `2^d`. -/
lemma fourierCoeff_spike_eq_zero (d : ℕ) (hd : 1 ≤ d) (m : ℤ) (hm : m ≠ 0) :
    fourierCoeff (fun x : (AddCircle (1 : ℝ)) => (spike d x : ℂ)) ((2 : ℤ) ^ d * m) = 0 := by
  have hb0 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ d := by positivity
  have hb1 : (2 : ℝ)⁻¹ ^ d < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  obtain ⟨C, hC_def⟩ : ∃ C : ℂ, C = 2 * π * Complex.I * (((-((2 : ℤ) ^ d * m)) : ℤ) : ℂ) :=
    ⟨_, rfl⟩
  have hC : C ≠ 0 := by
    rw [hC_def]; simp [Real.pi_ne_zero, Complex.I_ne_zero, hm]
  have h2 : (2 : ℂ) ^ d * ((2 : ℂ)⁻¹) ^ d = 1 := by rw [← mul_pow]; norm_num
  have hCb : Complex.exp (C * (((2 : ℝ)⁻¹ ^ d : ℝ) : ℂ)) = 1 := by
    rw [Complex.exp_eq_one_iff]
    refine ⟨-m, ?_⟩
    rw [hC_def]; push_cast
    linear_combination (-2 * π * Complex.I * m) * h2
  have hCb1 : Complex.exp (C * (((2 : ℝ)⁻¹ ^ d - 1 : ℝ) : ℂ)) = 1 := by
    rw [Complex.exp_eq_one_iff]
    refine ⟨2 ^ d * m - m, ?_⟩
    rw [hC_def]; push_cast
    linear_combination (-2 * π * Complex.I * m) * h2
  have hC0 : Complex.exp (C * ((0 : ℝ) : ℂ)) = 1 := by simp
  have hpt : ∀ x ∈ Set.uIoc ((2 : ℝ)⁻¹ ^ d - 1) ((2 : ℝ)⁻¹ ^ d),
      fourier (-((2 : ℤ) ^ d * m)) (x : (AddCircle (1 : ℝ))) • (spike d (x : (AddCircle (1 : ℝ))) : ℂ) =
        (1 / ((Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) : ℝ) : ℂ)) *
            (Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d)).indicator (fun y : ℝ => Complex.exp (C * y)) x -
          ((((2 : ℝ)⁻¹ ^ d : ℝ) : ℂ) /
              ((Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) : ℝ) : ℂ)) *
            Complex.exp (C * x) := by
    intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    have hmem := mem_spikeSet_iff d hd x hx
    have hf : fourier (-((2 : ℤ) ^ d * m)) (x : (AddCircle (1 : ℝ))) = Complex.exp (C * x) := by
      rw [fourier_coe_apply, hC_def]
      congr 1
      push_cast; ring
    rw [hf]
    unfold spike
    by_cases hxI : x ∈ Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d)
    · rw [Set.indicator_of_mem (hmem.mpr hxI), Set.indicator_of_mem hxI, Pi.one_apply]
      push_cast; ring
    · rw [Set.indicator_of_notMem (fun h => hxI (hmem.mp h)), Set.indicator_of_notMem hxI]
      push_cast; ring
  have hcont : Continuous (fun y : ℝ => Complex.exp (C * y)) := by fun_prop
  have hle : (2 : ℝ)⁻¹ ^ d - 1 ≤ (2 : ℝ)⁻¹ ^ d := by linarith
  have hind : IntervalIntegrable
      ((Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d)).indicator (fun y : ℝ => Complex.exp (C * y))) volume
      ((2 : ℝ)⁻¹ ^ d - 1) ((2 : ℝ)⁻¹ ^ d) :=
    intervalIntegrable_iff.mpr
      ((intervalIntegrable_iff.mp (hcont.intervalIntegrable _ _)).indicator measurableSet_Ico)
  have hsub : Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d) ⊆ Set.Ioc ((2 : ℝ)⁻¹ ^ d - 1) ((2 : ℝ)⁻¹ ^ d) :=
    fun y hy => ⟨by linarith [hy.1, hb1], hy.2.le⟩
  have hI1 : ∫ x in ((2 : ℝ)⁻¹ ^ d - 1)..((2 : ℝ)⁻¹ ^ d),
      (Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d)).indicator (fun y : ℝ => Complex.exp (C * y)) x =
      ∫ x in (0 : ℝ)..((2 : ℝ)⁻¹ ^ d), Complex.exp (C * x) := by
    rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hb0.le,
      setIntegral_indicator measurableSet_Ico, Set.inter_eq_right.mpr hsub,
      integral_Ico_eq_integral_Ioc]
  rw [fourierCoeff_eq_intervalIntegral _ _ ((2 : ℝ)⁻¹ ^ d - 1), sub_add_cancel,
    intervalIntegral.integral_congr_ae (ae_of_all _ hpt),
    intervalIntegral.integral_sub (hind.const_mul _) ((hcont.intervalIntegrable _ _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hI1,
    integral_exp_mul_complex hC, integral_exp_mul_complex hC, hCb, hCb1, hC0]
  simp

/-- Fourier support of a dilated spike: `\widehat{φ_d(2^v ·)}(r) = 0` unless
`v ≤ val₂(r) ≤ v + d - 1`. -/
lemma fourierCoeff_spike_dilate_eq_zero (d v : ℕ) (r : ℤ) (hr : r ≠ 0)
    (h : ¬ (2 ^ v ∣ r ∧ ¬ 2 ^ (v + d) ∣ r)) :
    fourierCoeff (fun x : (AddCircle (1 : ℝ)) => (spike d ((2 ^ v : ℕ) • x) : ℂ)) r = 0 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have : (fun x : (AddCircle (1 : ℝ)) => (spike 0 ((2 ^ v : ℕ) • x) : ℂ)) = fun _ => 0 := by
      funext x; simp [spike]
    rw [this]; simp [fourierCoeff]
  have hn : 0 < 2 ^ v := by positivity
  rw [not_and, not_not] at h
  by_cases hv : (2 : ℤ) ^ v ∣ r
  · obtain ⟨m, rfl⟩ := h hv
    have hm : m ≠ 0 := by rintro rfl; simp at hr
    have hr' : (2 : ℤ) ^ (v + d) * m = ((2 ^ v : ℕ) : ℤ) * ((2 : ℤ) ^ d * m) := by
      push_cast; ring
    have hmeas : AEStronglyMeasurable (fun y : (AddCircle (1 : ℝ)) => (spike d y : ℂ)) (haarAddCircle (T := 1)) :=
      (Complex.measurable_ofReal.comp (measurable_spike d)).aestronglyMeasurable
    rw [hr']
    refine (fourierCoeff_nsmul_comp_mul (2 ^ v) hn (fun y : (AddCircle (1 : ℝ)) => (spike d y : ℂ)) hmeas _).trans ?_
    exact fourierCoeff_spike_eq_zero d hd m hm
  · exact fourierCoeff_nsmul_comp_eq_zero (2 ^ v) hn (fun y : (AddCircle (1 : ℝ)) => (spike d y : ℂ)) r
      (by push_cast; exact hv)

end OMA.Port23

/- ### SpikeTail -/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real

namespace OMA.Port23


namespace SpikeTailAux

lemma mem_spikeSet_iff (d : ℕ) (z : (AddCircle (1 : ℝ))) :
    z ∈ (QuotientAddGroup.mk '' Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d) : Set (AddCircle (1 : ℝ))) ↔
      ((AddCircle.equivIco 1 0 z : ℝ)) < (2 : ℝ)⁻¹ ^ d := by
  have hp1 : (2 : ℝ)⁻¹ ^ d ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ Set.Ico (0:ℝ) (0 + 1) := ⟨hx.1, by linarith [hx.2]⟩
    rw [AddCircle.equivIco_coe_of_mem hx']
    exact hx.2
  · intro h
    refine ⟨(AddCircle.equivIco 1 0 z : ℝ), ⟨(AddCircle.equivIco 1 0 z).2.1, h⟩, ?_⟩
    exact AddCircle.coe_equivIco

lemma measurable_spike (d : ℕ) : Measurable (spike d) := by
  have hA : MeasurableSet (QuotientAddGroup.mk '' Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d) : Set (AddCircle (1 : ℝ))) := by
    have : (QuotientAddGroup.mk '' Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d) : Set (AddCircle (1 : ℝ))) =
        (fun z : (AddCircle (1 : ℝ)) => (AddCircle.equivIco 1 0 z : ℝ)) ⁻¹' Set.Iio ((2 : ℝ)⁻¹ ^ d) := by
      ext z; exact mem_spikeSet_iff d z
    rw [this]
    exact (measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable)
      measurableSet_Iio
  exact ((measurable_one.indicator hA).sub measurable_const).div_const _

lemma fourier_add_arg (n : ℤ) (x y : (AddCircle (1 : ℝ))) : fourier n (x + y) = fourier n x * fourier n y := by
  simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

lemma fc_eq_zero_of_not_dvd (d Q : ℕ) (hQ : 0 < Q) (r : ℤ) (h : ¬ (Q : ℤ) ∣ r) :
    fourierCoeff (fun x : (AddCircle (1 : ℝ)) => (spike d (Q • x) : ℂ)) r = 0 := by
  have hQr : (0:ℝ) < Q := by exact_mod_cast hQ
  have hQne : (Q:ℝ) ≠ 0 := hQr.ne'
  set t : (AddCircle (1 : ℝ)) := ((1 / (Q : ℝ) : ℝ) : (AddCircle (1 : ℝ))) with ht
  have hQt : Q • t = 0 := by
    rw [ht, ← AddCircle.coe_nsmul, nsmul_eq_mul, mul_one_div_cancel hQne]
    exact AddCircle.coe_period (p := (1:ℝ))
  have key : fourierCoeff (fun x : (AddCircle (1 : ℝ)) => (spike d (Q • x) : ℂ)) r =
      fourier (-r) t * fourierCoeff (fun x : (AddCircle (1 : ℝ)) => (spike d (Q • x) : ℂ)) r := by
    unfold fourierCoeff
    have e := integral_add_right_eq_self (μ := (haarAddCircle : Measure (AddCircle (1 : ℝ))))
      (fun x => fourier (-r) x • (spike d (Q • x) : ℂ)) t
    conv_lhs => rw [← e]
    rw [← integral_const_mul]
    congr 1
    funext x
    simp only [smul_eq_mul, nsmul_add, hQt, add_zero, fourier_add_arg]
    ring
  have hne : fourier (-r) t ≠ 1 := by
    intro h1
    have h2 : toCircle ((-r) • t) = 1 := by
      rw [fourier_apply] at h1
      exact Circle.ext (h1.trans Circle.coe_one.symm)
    have h3 : (-r) • t = 0 :=
      AddCircle.injective_toCircle one_ne_zero (h2.trans AddCircle.toCircle_zero.symm)
    rw [ht, ← AddCircle.coe_zsmul, AddCircle.coe_eq_zero_iff] at h3
    obtain ⟨m, hm⟩ := h3
    simp only [zsmul_eq_mul, mul_one, Int.cast_neg, one_div] at hm
    apply h
    refine ⟨-m, ?_⟩
    have hmQ : (m:ℝ) * Q = -r := by
      rw [hm, mul_assoc, inv_mul_cancel₀ hQne, mul_one]
    have : (r:ℝ) = (Q:ℝ) * ((-m : ℤ) : ℝ) := by
      push_cast
      linear_combination hmQ
    exact_mod_cast this
  have h3 : (fourier (-r) t - 1) * fourierCoeff (fun x : (AddCircle (1 : ℝ)) => (spike d (Q • x) : ℂ)) r = 0 := by
    rw [sub_mul, one_mul, ← key, sub_self]
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact absurd (sub_eq_zero.mp h4) hne
  · exact h4

lemma fc_dilate (d Q : ℕ) (hQ : 0 < Q) (s : ℤ) :
    fourierCoeff (fun x : (AddCircle (1 : ℝ)) => (spike d (Q • x) : ℂ)) ((Q : ℤ) * s) =
      fourierCoeff (fun x : (AddCircle (1 : ℝ)) => (spike d x : ℂ)) s := by
  have hQz : (Q : ℤ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hmp : MeasurePreserving (fun x : (AddCircle (1 : ℝ)) => (Q : ℤ) • x) (haarAddCircle : Measure (AddCircle (1 : ℝ)))
      haarAddCircle := Measure.measurePreserving_zsmul _ hQz
  have hg : AEStronglyMeasurable (fun y : (AddCircle (1 : ℝ)) => fourier (-s) y • (spike d y : ℂ))
      haarAddCircle :=
    (map_continuous (fourier (-s))).aestronglyMeasurable.smul
      (Complex.measurable_ofReal.comp (measurable_spike d)).aestronglyMeasurable
  have e := integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hg)
  rw [hmp.map_eq] at e
  unfold fourierCoeff
  rw [e]
  congr 1
  funext x
  have hx : ((Q:ℤ) • x) = Q • x := natCast_zsmul x Q
  show _ = fourier (-s) ((Q:ℤ) • x) • (spike d ((Q:ℤ) • x) : ℂ)
  rw [fourier_apply, fourier_apply, smul_smul, hx, show -((Q:ℤ) * s) = -s * (Q:ℤ) by ring]

lemma fc_spike (d : ℕ) (hd : 1 ≤ d) (s : ℤ) (hs : s ≠ 0) :
    fourierCoeff (fun x : (AddCircle (1 : ℝ)) => (spike d x : ℂ)) s =
      (((Real.sqrt ((2:ℝ)⁻¹ ^ d * (1 - (2:ℝ)⁻¹ ^ d)))⁻¹ : ℝ) : ℂ) *
        ((Complex.exp (-(2 * π * Complex.I * s) * (((2:ℝ)⁻¹ ^ d : ℝ) : ℂ)) - 1) /
          -(2 * π * Complex.I * s)) := by
  have hp0 : (0:ℝ) < (2:ℝ)⁻¹ ^ d := by positivity
  have hp1 : (2:ℝ)⁻¹ ^ d < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hc0 : -(2 * π * Complex.I * s) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero, hs]
  have hE : ∀ x : ℝ, fourier (-s) (x : (AddCircle (1 : ℝ))) = Complex.exp (-(2 * π * Complex.I * s) * x) := by
    intro x; rw [fourier_coe_apply]; congr 1; push_cast; ring
  rw [fourierCoeff_eq_intervalIntegral _ _ 0, zero_add, one_div_one, one_smul,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  have hpt : Set.EqOn (fun x : ℝ => fourier (-s) (x : (AddCircle (1 : ℝ))) • (spike d (x : (AddCircle (1 : ℝ))) : ℂ))
      (fun x : ℝ => (((Real.sqrt ((2:ℝ)⁻¹ ^ d * (1 - (2:ℝ)⁻¹ ^ d)))⁻¹ : ℝ) : ℂ) *
        (Set.indicator (Set.Iio ((2:ℝ)⁻¹ ^ d))
            (fun x : ℝ => Complex.exp (-(2 * π * Complex.I * s) * x)) x
          - (((2:ℝ)⁻¹ ^ d : ℝ) : ℂ) * Complex.exp (-(2 * π * Complex.I * s) * x)))
      (Set.Ioo 0 1) := by
    intro x hx
    have hx' : x ∈ Set.Ico (0:ℝ) (0 + 1) := ⟨hx.1.le, by linarith [hx.2]⟩
    have hmem := mem_spikeSet_iff d (x : (AddCircle (1 : ℝ)))
    rw [AddCircle.equivIco_coe_of_mem hx'] at hmem
    simp only [hE, spike, smul_eq_mul]
    by_cases hxp : x < (2:ℝ)⁻¹ ^ d
    · rw [Set.indicator_of_mem (hmem.mpr hxp),
        Set.indicator_of_mem (show x ∈ Set.Iio ((2:ℝ)⁻¹ ^ d) from hxp)]
      simp only [Pi.one_apply]
      push_cast; ring
    · rw [Set.indicator_of_notMem (fun h => hxp (hmem.mp h)),
        Set.indicator_of_notMem (show x ∉ Set.Iio ((2:ℝ)⁻¹ ^ d) from hxp)]
      push_cast; ring
  rw [setIntegral_congr_fun measurableSet_Ioo hpt, integral_const_mul]
  have hEint : IntegrableOn (fun x : ℝ => Complex.exp (-(2 * π * Complex.I * s) * x))
      (Set.Ioo 0 1) :=
    (Continuous.integrableOn_Icc (by fun_prop)).mono_set Set.Ioo_subset_Icc_self
  rw [integral_sub (Integrable.indicator hEint measurableSet_Iio) (Integrable.const_mul hEint _),
    setIntegral_indicator measurableSet_Iio, integral_const_mul, Set.Ioo_inter_Iio,
    min_eq_right hp1.le]
  have e1 : ∫ x in Set.Ioo (0:ℝ) ((2:ℝ)⁻¹ ^ d), Complex.exp (-(2 * π * Complex.I * s) * x) =
      ∫ x in (0:ℝ)..(2:ℝ)⁻¹ ^ d, Complex.exp (-(2 * π * Complex.I * s) * x) := by
    rw [intervalIntegral.integral_of_le hp0.le, integral_Ioc_eq_integral_Ioo]
  have e2 : ∫ x in Set.Ioo (0:ℝ) 1, Complex.exp (-(2 * π * Complex.I * s) * x) =
      ∫ x in (0:ℝ)..1, Complex.exp (-(2 * π * Complex.I * s) * x) := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  rw [e1, e2, integral_exp_mul_complex hc0, integral_exp_mul_complex hc0]
  have h1 : Complex.exp (-(2 * π * Complex.I * s) * ((1:ℝ) : ℂ)) = 1 :=
    Complex.exp_eq_one_iff.mpr ⟨-s, by push_cast; ring⟩
  rw [h1]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_self, zero_div, sub_zero]

lemma norm_fc_spike_sq_le (d : ℕ) (hd : 1 ≤ d) (s : ℤ) (hs : s ≠ 0) :
    ‖fourierCoeff (fun x : (AddCircle (1 : ℝ)) => (spike d x : ℂ)) s‖ ^ 2 ≤ 2 * (2:ℝ)⁻¹ ^ d ∧
    ‖fourierCoeff (fun x : (AddCircle (1 : ℝ)) => (spike d x : ℂ)) s‖ ^ 2 ≤ 1 / ((2:ℝ)⁻¹ ^ d * (s:ℝ) ^ 2) := by
  rw [fc_spike d hd s hs]
  have hp0 : (0:ℝ) < (2:ℝ)⁻¹ ^ d := by positivity
  have hp2 : (2:ℝ)⁻¹ ^ d ≤ 2⁻¹ := by
    calc (2:ℝ)⁻¹ ^ d ≤ (2:ℝ)⁻¹ ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hd
      _ = 2⁻¹ := pow_one _
  set p : ℝ := (2:ℝ)⁻¹ ^ d with hp
  set σ : ℝ := Real.sqrt (p * (1 - p)) with hσ
  have hσ2 : σ ^ 2 = p * (1 - p) := Real.sq_sqrt (by nlinarith)
  have hσ0 : 0 < σ := Real.sqrt_pos.mpr (by nlinarith)
  have hsR : (s:ℝ) ≠ 0 := by exact_mod_cast hs
  have hsabs : 0 < |(s:ℝ)| := abs_pos.mpr hsR
  have hs2 : 0 < (s:ℝ) ^ 2 := by
    have := pow_pos hsabs 2
    rwa [sq_abs] at this
  set θ : ℝ := -(2 * π * s * p) with hθ
  have hcp : -(2 * π * Complex.I * s) * (p : ℂ) = Complex.I * θ := by
    rw [hθ]; push_cast; ring
  rw [hcp]
  set A : ℂ := Complex.exp (Complex.I * θ) - 1 with hA
  have hden : 0 < 2 * π * |(s:ℝ)| := mul_pos (by positivity) hsabs
  have hcn : ‖-(2 * π * Complex.I * (s:ℂ))‖ = 2 * π * |(s:ℝ)| := by
    simp [abs_of_pos Real.pi_pos]
  have hnorm : ‖((σ⁻¹ : ℝ) : ℂ) * (A / -(2 * π * Complex.I * s))‖ =
      σ⁻¹ * (‖A‖ / (2 * π * |(s:ℝ)|)) := by
    rw [norm_mul, norm_div, hcn, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hσ0.le)]
  rw [hnorm]
  have hA1 : ‖A‖ ≤ |θ| := by
    have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ)
    rwa [Real.norm_eq_abs] at this
  have hA2 : ‖A‖ ≤ 2 := by
    calc ‖A‖ ≤ ‖Complex.exp (Complex.I * θ)‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [mul_comm, Complex.norm_exp_ofReal_mul_I, norm_one]; norm_num
  have hθabs : |θ| = 2 * π * |(s:ℝ)| * p := by
    rw [hθ, abs_neg, show 2 * π * (s:ℝ) * p = (2 * π * p) * s by ring, abs_mul,
      abs_of_pos (by positivity : (0:ℝ) < 2 * π * p)]
    ring
  set B := ‖A‖ / (2 * π * |(s:ℝ)|) with hB
  have hB0 : 0 ≤ B := div_nonneg (norm_nonneg _) hden.le
  have hB1 : B ≤ p := by
    rw [hB, div_le_iff₀ hden]; linarith
  have hB2 : B ≤ 1 / (π * |(s:ℝ)|) := by
    rw [hB, div_le_div_iff₀ hden (by positivity)]; nlinarith [hA2]
  have hq : 0 < p * (1 - p) := by nlinarith
  constructor
  · rw [mul_pow, inv_pow, hσ2, inv_mul_le_iff₀ hq]
    have : B ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ hB0 hB1 2
    nlinarith [mul_nonneg (sq_nonneg p) (by linarith : (0:ℝ) ≤ 1 - 2 * p)]
  · rw [mul_pow, inv_pow, hσ2, inv_mul_le_iff₀ hq]
    have h9 : 9 ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
    have hπ : 1 ≤ π ^ 2 * (1 - p) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h9) (by linarith : (0:ℝ) ≤ 1 - p)]
    calc B ^ 2 ≤ (1 / (π * |(s:ℝ)|)) ^ 2 := pow_le_pow_left₀ hB0 hB2 2
      _ = 1 / (π ^ 2 * (s:ℝ) ^ 2) := by rw [div_pow, one_pow, mul_pow, sq_abs]
      _ ≤ (1 - p) / (s:ℝ) ^ 2 := by
          rw [div_le_div_iff₀ (by positivity) hs2]
          nlinarith [mul_nonneg hs2.le (sub_nonneg.mpr hπ)]
      _ = p * (1 - p) * (1 / (p * (s:ℝ) ^ 2)) := by
          field_simp

lemma tail_nat (K : ℝ) (hK : 0 < K) (L : ℕ) :
    ∑ n ∈ Finset.range L, (if K < (n:ℝ) then 1 / (n:ℝ) ^ 2 else 0) ≤ 2 / K := by
  have e : ∑ n ∈ Finset.range L, (if K < (n:ℝ) then 1 / (n:ℝ) ^ 2 else 0) =
      ∑ n ∈ Finset.Ioo ⌊K⌋₊ L, ((n:ℝ) ^ 2)⁻¹ := by
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioo]
      rw [Nat.floor_lt hK.le]
      tauto
    · intro n _; rw [one_div]
  rw [e]
  calc _ ≤ 2 / ((⌊K⌋₊ : ℝ) + 1) := sum_Ioo_inv_sq_le _ _
    _ ≤ 2 / K := div_le_div_of_nonneg_left (by norm_num) hK (Nat.lt_floor_add_one K).le

lemma tail_int (K : ℝ) (hK : 0 < K) :
    Summable (fun s : ℤ => if K < |(s:ℝ)| then 1 / (s:ℝ) ^ 2 else 0) ∧
    ∑' s : ℤ, (if K < |(s:ℝ)| then 1 / (s:ℝ) ^ 2 else 0) ≤ 4 / K := by
  set f : ℤ → ℝ := fun s => if K < |(s:ℝ)| then 1 / (s:ℝ) ^ 2 else 0 with hf
  set g : ℕ → ℝ := fun n => if K < (n:ℝ) then 1 / (n:ℝ) ^ 2 else 0 with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n => by simp only [hg]; split_ifs <;> positivity
  have hgL : ∀ L, ∑ n ∈ Finset.range L, g n ≤ 2 / K := tail_nat K hK
  have hgL' : ∀ L, ∑ n ∈ Finset.range L, g (n + 1) ≤ 2 / K := by
    intro L
    have := hgL (L + 1)
    rw [Finset.sum_range_succ'] at this
    linarith [hg0 0]
  have hgs : Summable g := summable_of_sum_range_le hg0 hgL
  have hgs' : Summable (fun n => g (n + 1)) := summable_of_sum_range_le (fun n => hg0 _) hgL'
  have h1 : (fun n : ℕ => f n) = fun n => g n := by
    funext n; simp only [hf, hg, Int.cast_natCast, Nat.abs_cast]
  have h2 : (fun n : ℕ => f (-((n : ℤ) + 1))) = fun n => g (n + 1) := by
    funext n
    simp only [hf, hg]
    push_cast
    rw [abs_neg, abs_of_pos (by positivity : (0:ℝ) < (n:ℝ) + 1), neg_sq]
  have hs1 : Summable (fun n : ℕ => f n) := by rw [h1]; exact hgs
  have hs2 : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) := by rw [h2]; exact hgs'
  refine ⟨Summable.of_nat_of_neg_add_one hs1 hs2, ?_⟩
  rw [tsum_of_nat_of_neg_add_one hs1 hs2, h1, h2]
  have t1 := Real.tsum_le_of_sum_range_le hg0 hgL
  have t2 := Real.tsum_le_of_sum_range_le (fun n => hg0 (n + 1)) hgL'
  exact le_trans (add_le_add t1 t2) (le_of_eq (by ring))

end SpikeTailAux

open SpikeTailAux in
/-- Fourier tail of one dilated spike: `‖(I - S_N) φ_d(2^v ·)‖₂² ≤ C₁ min(1, 2^{d+v}/N)`. -/
lemma spike_dilate_tail :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (d v N : ℕ), 1 ≤ d → 1 ≤ N →
      ∑' r : {r : ℤ // (N : ℤ) < |r|},
          ‖fourierCoeff (fun x : (AddCircle (1 : ℝ)) => (spike d ((2 ^ v : ℕ) • x) : ℂ)) r‖ ^ 2
        ≤ C₁ * min 1 ((2 : ℝ) ^ (d + v) / N) := by
  refine ⟨10, by norm_num, ?_⟩
  intro d v N hd hN
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = 2 ^ v := ⟨_, rfl⟩
  rw [← hQ]
  have hQpos : 0 < Q := by rw [hQ]; positivity
  have hQz : (Q : ℤ) ≠ 0 := by exact_mod_cast hQpos.ne'
  have hQr : (Q : ℝ) = 2 ^ v := by rw [hQ]; push_cast; ring
  have hQr0 : (0:ℝ) < Q := by exact_mod_cast hQpos
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have e1 : ∑' r : {r : ℤ // (N : ℤ) < |r|},
        ‖fourierCoeff (fun x : (AddCircle (1 : ℝ)) => (spike d (Q • x) : ℂ)) r‖ ^ 2 =
      ∑' r : ℤ, (if (N:ℤ) < |r| then
        ‖fourierCoeff (fun x : (AddCircle (1 : ℝ)) => (spike d (Q • x) : ℂ)) r‖ ^ 2 else 0) := by
    have := tsum_subtype {r : ℤ | (N:ℤ) < |r|}
      (fun r => ‖fourierCoeff (fun x : (AddCircle (1 : ℝ)) => (spike d (Q • x) : ℂ)) r‖ ^ 2)
    simp only [Set.indicator_apply, Set.mem_setOf_eq] at this
    exact this
  have e2 : ∑' r : ℤ, (if (N:ℤ) < |r| then
        ‖fourierCoeff (fun x : (AddCircle (1 : ℝ)) => (spike d (Q • x) : ℂ)) r‖ ^ 2 else 0) =
      ∑' s : ℤ, (if (N:ℤ) < |(Q:ℤ) * s| then
        ‖fourierCoeff (fun x : (AddCircle (1 : ℝ)) => (spike d x : ℂ)) s‖ ^ 2 else 0) := by
    rw [← (mul_right_injective₀ hQz).tsum_eq]
    · congr 1
      funext s
      simp only [fc_dilate d Q hQpos]
    · intro r hr
      rw [Function.mem_support] at hr
      by_cases hdiv : (Q:ℤ) ∣ r
      · obtain ⟨s, rfl⟩ := hdiv
        exact ⟨s, rfl⟩
      · exfalso
        apply hr
        simp [fc_eq_zero_of_not_dvd d Q hQpos r hdiv]
  rw [e1, e2]
  have hbd : ∀ s : ℤ, (N:ℤ) < |(Q:ℤ) * s| → s ≠ 0 ∧ (N:ℝ) / Q < |(s:ℝ)| := by
    intro s hs
    refine ⟨?_, ?_⟩
    · rintro rfl
      rw [mul_zero, abs_zero] at hs
      omega
    · have h' : (N:ℝ) < |(Q:ℝ) * s| := by exact_mod_cast hs
      rw [abs_mul, abs_of_pos hQr0] at h'
      rw [div_lt_iff₀ hQr0]
      linarith
  set a : ℤ → ℝ := fun s => if (N:ℤ) < |(Q:ℤ) * s| then
        ‖fourierCoeff (fun x : (AddCircle (1 : ℝ)) => (spike d x : ℂ)) s‖ ^ 2 else 0 with ha
  have ha0 : ∀ s, 0 ≤ a s := fun s => by simp only [ha]; split_ifs <;> positivity
  by_cases hX : (2:ℝ) ^ (d + v) ≤ N
  · have hK : 0 < (N:ℝ) / Q := by positivity
    obtain ⟨hsum, htail⟩ := tail_int ((N:ℝ) / Q) hK
    have hab : ∀ s, a s ≤
        (2:ℝ) ^ d * (if (N:ℝ) / Q < |(s:ℝ)| then 1 / (s:ℝ) ^ 2 else 0) := by
      intro s
      simp only [ha]
      by_cases h1 : (N:ℤ) < |(Q:ℤ) * s|
      · obtain ⟨hs0, hK'⟩ := hbd s h1
        rw [if_pos h1, if_pos hK']
        refine (norm_fc_spike_sq_le d hd s hs0).2.trans (le_of_eq ?_)
        rw [inv_pow, one_div, mul_inv, inv_inv, one_div]
      · rw [if_neg h1]
        exact mul_nonneg (by positivity) (by split_ifs <;> positivity)
    have hsb := hsum.mul_left ((2:ℝ) ^ d)
    have hsa : Summable a := Summable.of_nonneg_of_le ha0 hab hsb
    calc ∑' s, a s
        ≤ ∑' s : ℤ, (2:ℝ) ^ d * (if (N:ℝ) / Q < |(s:ℝ)| then 1 / (s:ℝ) ^ 2 else 0) :=
          Summable.tsum_le_tsum hab hsa hsb
      _ = (2:ℝ) ^ d * ∑' s : ℤ, (if (N:ℝ) / Q < |(s:ℝ)| then 1 / (s:ℝ) ^ 2 else 0) :=
          tsum_mul_left
      _ ≤ (2:ℝ) ^ d * (4 / ((N:ℝ) / Q)) := mul_le_mul_of_nonneg_left htail (by positivity)
      _ = 4 * ((2:ℝ) ^ (d + v) / N) := by
          rw [pow_add, hQr, div_div_eq_mul_div]; ring
      _ ≤ 10 * min 1 ((2:ℝ) ^ (d + v) / N) := by
          rw [min_eq_right ((div_le_one hNr).mpr hX)]
          have : 0 ≤ (2:ℝ) ^ (d + v) / N := by positivity
          linarith
  · push_neg at hX
    obtain ⟨M, hM⟩ : ∃ M : ℕ, M = 2 ^ d := ⟨_, rfl⟩
    have hMr : (M:ℝ) = 2 ^ d := by rw [hM]; push_cast; ring
    have hMpos : (0:ℝ) < M := by rw [hMr]; positivity
    obtain ⟨hsum, htail⟩ := tail_int (M:ℝ) hMpos
    set b1 : ℤ → ℝ := fun s => if |s| ≤ (M:ℤ) then 2 * (2:ℝ)⁻¹ ^ d else 0 with hb1
    have hb1fin : ∀ s ∉ Finset.Icc (-(M:ℤ)) M, b1 s = 0 := by
      intro s hs
      rw [Finset.mem_Icc, ← abs_le] at hs
      simp only [hb1, if_neg hs]
    have hab : ∀ s, a s ≤
        b1 s + (2:ℝ) ^ d * (if (M:ℝ) < |(s:ℝ)| then 1 / (s:ℝ) ^ 2 else 0) := by
      intro s
      have hb1n : 0 ≤ b1 s := by simp only [hb1]; split_ifs <;> positivity
      have ht0 : 0 ≤ (2:ℝ) ^ d * (if (M:ℝ) < |(s:ℝ)| then 1 / (s:ℝ) ^ 2 else 0) :=
        mul_nonneg (by positivity) (by split_ifs <;> positivity)
      by_cases h1 : (N:ℤ) < |(Q:ℤ) * s|
      · obtain ⟨hs0, -⟩ := hbd s h1
        have hb := norm_fc_spike_sq_le d hd s hs0
        have has : a s = ‖fourierCoeff (fun x : (AddCircle (1 : ℝ)) => (spike d x : ℂ)) s‖ ^ 2 := by
          simp only [ha, if_pos h1]
        rw [has]
        by_cases h2 : |s| ≤ (M:ℤ)
        · have : b1 s = 2 * (2:ℝ)⁻¹ ^ d := by simp only [hb1, if_pos h2]
          linarith [hb.1]
        · have h3 : (M:ℝ) < |(s:ℝ)| := by
            push_neg at h2
            exact_mod_cast h2
          have : b1 s = 0 := by simp only [hb1, if_neg h2]
          rw [this, zero_add, if_pos h3]
          refine hb.2.trans (le_of_eq ?_)
          rw [inv_pow, one_div, mul_inv, inv_inv, one_div]
      · have has : a s = 0 := by simp only [ha, if_neg h1]
        rw [has]
        linarith
    have hs1 : Summable b1 := summable_of_ne_finset_zero hb1fin
    have hs2 := hsum.mul_left ((2:ℝ) ^ d)
    have hsb := hs1.add hs2
    have hsa : Summable a := Summable.of_nonneg_of_le ha0 hab hsb
    have hb1sum : ∑' s, b1 s ≤ (2 * M + 1) * (2 * (2:ℝ)⁻¹ ^ d) := by
      rw [tsum_eq_sum hb1fin]
      calc ∑ s ∈ Finset.Icc (-(M:ℤ)) M, b1 s
          ≤ ∑ s ∈ Finset.Icc (-(M:ℤ)) M, 2 * (2:ℝ)⁻¹ ^ d := by
            apply Finset.sum_le_sum
            intro s _
            simp only [hb1]
            split_ifs
            · exact le_rfl
            · positivity
        _ = (2 * M + 1) * (2 * (2:ℝ)⁻¹ ^ d) := by
            rw [Finset.sum_const, nsmul_eq_mul, Int.card_Icc]
            congr 1
            have : (M:ℤ) + 1 - -(M:ℤ) = ((2 * M + 1 : ℕ) : ℤ) := by push_cast; ring
            rw [this, Int.toNat_natCast]
            push_cast
            ring
    calc ∑' s, a s
        ≤ ∑' s : ℤ, (b1 s + (2:ℝ) ^ d * (if (M:ℝ) < |(s:ℝ)| then 1 / (s:ℝ) ^ 2 else 0)) :=
          Summable.tsum_le_tsum hab hsa hsb
      _ = ∑' s : ℤ, b1 s +
            (2:ℝ) ^ d * ∑' s : ℤ, (if (M:ℝ) < |(s:ℝ)| then 1 / (s:ℝ) ^ 2 else 0) := by
          rw [Summable.tsum_add hs1 hs2, tsum_mul_left]
      _ ≤ (2 * M + 1) * (2 * (2:ℝ)⁻¹ ^ d) + (2:ℝ) ^ d * (4 / M) :=
          add_le_add hb1sum (mul_le_mul_of_nonneg_left htail (by positivity))
      _ ≤ 10 * min 1 ((2:ℝ) ^ (d + v) / N) := by
          rw [min_eq_left ((one_le_div hNr).mpr hX.le), hMr, inv_pow]
          have hy : (1:ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
          have hy0 : (0:ℝ) < 2 ^ d := by positivity
          have hinv : (2:ℝ) ^ d * ((2:ℝ) ^ d)⁻¹ = 1 := mul_inv_cancel₀ hy0.ne'
          have e3 : (2:ℝ) ^ d * (4 / 2 ^ d) = 4 := by linear_combination 4 * hinv
          have e4 : (2 * (2:ℝ) ^ d + 1) * (2 * ((2:ℝ) ^ d)⁻¹) = 4 + 2 * ((2:ℝ) ^ d)⁻¹ := by
            linear_combination 4 * hinv
          have e5 : ((2:ℝ) ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hy
          rw [e3, e4]
          linarith

end OMA.Port23

/- ### DigitIndependence -/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real

namespace OMA.Port23


namespace DigitIndep

/-- Haar measure on `(AddCircle (1 : ℝ))` computed on `[0,1)` in `ℝ`. -/
lemma haar_eq (U : Set (AddCircle (1 : ℝ))) (hU : MeasurableSet U) :
    (haarAddCircle (T := 1)) U = volume (Set.Ico (0 : ℝ) 1 ∩ (((↑) : ℝ → (AddCircle (1 : ℝ))) ⁻¹' U)) := by
  have h1 : (volume : Measure (AddCircle (1 : ℝ))) = (haarAddCircle (T := 1)) := by
    rw [volume_eq_smul_haarAddCircle]; simp
  have h2 := AddCircle.add_projection_respects_measure (T := 1) 0 hU
  rw [← h1, h2, zero_add, Set.inter_comm]
  exact measure_congr ((Ico_ae_eq_Ioc (μ := (volume : Measure ℝ))).symm.inter (ae_eq_refl _))

lemma digit_mk (j : ℕ) (y : ℝ) :
    Int.fract ((2 : ℝ) ^ j * (AddCircle.equivIco 1 0 (y : (AddCircle (1 : ℝ))) : ℝ)) =
      Int.fract ((2 : ℝ) ^ j * y) := by
  rw [coe_equivIco_mk_apply, div_one, mul_one]
  have hy : Int.fract y = y - ⌊y⌋ := rfl
  have : (2 : ℝ) ^ j * ⌊y⌋ = ((2 ^ j * ⌊y⌋ : ℤ) : ℝ) := by push_cast; ring
  rw [hy, mul_sub, this, Int.fract_sub_intCast]

lemma digit_shift {A j : ℕ} (hj : A ≤ j) (m : ℕ) (y : ℝ) :
    Int.fract ((2 : ℝ) ^ j * (y + (m : ℝ) / 2 ^ A)) = Int.fract ((2 : ℝ) ^ j * y) := by
  have h : (2 : ℝ) ^ j = 2 ^ (j - A) * 2 ^ A := by rw [← pow_add, Nat.sub_add_cancel hj]
  have : (2 : ℝ) ^ j * (y + (m : ℝ) / 2 ^ A) = 2 ^ j * y + ((m * 2 ^ (j - A) : ℕ) : ℝ) := by
    rw [h]; push_cast; field_simp
  rw [this, Int.fract_add_natCast]

lemma fract_lt_half_iff (u : ℝ) : Int.fract u < 2⁻¹ ↔ ⌊2 * u⌋ % 2 = 0 := by
  have h1 := Int.fract_nonneg u
  have h2 := Int.fract_lt_one u
  have h3 : (⌊u⌋ : ℝ) + Int.fract u = u := Int.floor_add_fract u
  by_cases hf : Int.fract u < 2⁻¹
  · have : ⌊2 * u⌋ = 2 * ⌊u⌋ := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    rw [this]; simp [hf]
  · have : ⌊2 * u⌋ = 2 * ⌊u⌋ + 1 := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    rw [this]; simp only [hf, false_iff]; omega

lemma floor_le_of_block {A j : ℕ} (hj : j < A) {m : ℤ} {y y' : ℝ}
    (hy : (m : ℝ) ≤ 2 ^ A * y') (hy' : 2 ^ A * y < m + 1) :
    ⌊2 * (2 ^ j * y)⌋ ≤ ⌊2 * (2 ^ j * y')⌋ := by
  by_contra hlt
  push_neg at hlt
  have e1 : 2 * (2 ^ j * y') < (⌊2 * (2 ^ j * y')⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have e2 : ((⌊2 * (2 ^ j * y')⌋ + 1 : ℤ) : ℝ) ≤ 2 * (2 ^ j * y) :=
    (Int.cast_le.mpr (Int.add_one_le_of_lt hlt)).trans (Int.floor_le _)
  have hA : (2 : ℝ) ^ A = 2 * 2 ^ j * 2 ^ (A - j - 1) := by
    rw [← pow_succ', ← pow_add]; congr 1; omega
  have hpos : (0 : ℝ) < 2 ^ (A - j - 1) := by positivity
  obtain ⟨c, hc⟩ : ∃ c : ℤ, (c : ℝ) = 2 ^ (A - j - 1) * ((⌊2 * (2 ^ j * y')⌋ : ℝ) + 1) :=
    ⟨2 ^ (A - j - 1) * (⌊2 * (2 ^ j * y')⌋ + 1), by push_cast; ring⟩
  have h1 : (m : ℝ) < c :=
    calc (m : ℝ) ≤ 2 ^ A * y' := hy
      _ = 2 ^ (A - j - 1) * (2 * (2 ^ j * y')) := by rw [hA]; ring
      _ < 2 ^ (A - j - 1) * ((⌊2 * (2 ^ j * y')⌋ : ℝ) + 1) := mul_lt_mul_of_pos_left e1 hpos
      _ = c := hc.symm
  have h2 : (c : ℝ) < m + 1 :=
    calc (c : ℝ) = 2 ^ (A - j - 1) * ((⌊2 * (2 ^ j * y')⌋ + 1 : ℤ) : ℝ) := by
          rw [hc]; push_cast; ring
      _ ≤ 2 ^ (A - j - 1) * (2 * (2 ^ j * y)) := mul_le_mul_of_nonneg_left e2 hpos.le
      _ = 2 ^ A * y := by rw [hA]; ring
      _ < m + 1 := hy'
  have h1' : m < c := by exact_mod_cast h1
  have h2' : c < m + 1 := by exact_mod_cast h2
  omega

lemma digit_block {A j : ℕ} (hj : j < A) {m : ℤ} {y y' : ℝ}
    (h1 : (m : ℝ) ≤ 2 ^ A * y) (h2 : 2 ^ A * y < m + 1)
    (h1' : (m : ℝ) ≤ 2 ^ A * y') (h2' : 2 ^ A * y' < m + 1) :
    Int.fract ((2 : ℝ) ^ j * y) < 2⁻¹ ↔ Int.fract ((2 : ℝ) ^ j * y') < 2⁻¹ := by
  rw [fract_lt_half_iff, fract_lt_half_iff,
    le_antisymm (floor_le_of_block hj h1' h2) (floor_le_of_block hj h1 h2')]

/-- Intended reading of `DeterminedByWindow` (with the `↔` inside the window binder). -/
def StrongDet (a b : ℕ) (E : Set (AddCircle (1 : ℝ))) : Prop :=
  ∀ x y : (AddCircle (1 : ℝ)), (∀ j, a ≤ j → j < b →
      (Int.fract ((2 : ℝ) ^ j * (AddCircle.equivIco 1 0 x : ℝ)) < 2⁻¹ ↔
      Int.fract ((2 : ℝ) ^ j * (AddCircle.equivIco 1 0 y : ℝ)) < 2⁻¹)) → (x ∈ E ↔ y ∈ E)

/-- The point keeping the binary digits of `y` in the window `[a,b)` and zeroing the others. -/
noncomputable def proj (a b : ℕ) (y : ℝ) : ℝ :=
  ((⌊(2 : ℝ) ^ b * y⌋ - 2 ^ (b - a) * ⌊(2 : ℝ) ^ a * y⌋ : ℤ) : ℝ) / 2 ^ b

lemma proj_digits {a b : ℕ} (hab : a ≤ b) (y : ℝ) (j : ℕ) :
    (a ≤ j → j < b → (Int.fract ((2 : ℝ) ^ j * y) < 2⁻¹ ↔
      Int.fract ((2 : ℝ) ^ j * proj a b y) < 2⁻¹)) ∧
    (¬(a ≤ j ∧ j < b) → Int.fract ((2 : ℝ) ^ j * proj a b y) < 2⁻¹) := by
  have hK1 : (⌊(2 : ℝ) ^ b * y⌋ : ℝ) ≤ 2 ^ b * y := Int.floor_le _
  have hK2 : (2 : ℝ) ^ b * y < ⌊(2 : ℝ) ^ b * y⌋ + 1 := Int.lt_floor_add_one _
  have hL1 : (⌊(2 : ℝ) ^ a * y⌋ : ℝ) ≤ 2 ^ a * y := Int.floor_le _
  have hL2 : (2 : ℝ) ^ a * y < ⌊(2 : ℝ) ^ a * y⌋ + 1 := Int.lt_floor_add_one _
  have hba : (2 : ℝ) ^ b = 2 ^ (b - a) * 2 ^ a := by rw [← pow_add, Nat.sub_add_cancel hab]
  have hpa : (0 : ℝ) < 2 ^ a := by positivity
  have hpb : (0 : ℝ) < 2 ^ b := by positivity
  have hpba : (0 : ℝ) < 2 ^ (b - a) := by positivity
  have hN0 : 2 ^ (b - a) * ⌊(2 : ℝ) ^ a * y⌋ ≤ ⌊(2 : ℝ) ^ b * y⌋ := by
    rw [Int.le_floor]; push_cast; rw [hba, mul_assoc]
    exact mul_le_mul_of_nonneg_left hL1 hpba.le
  have hN1 : ⌊(2 : ℝ) ^ b * y⌋ < 2 ^ (b - a) * ⌊(2 : ℝ) ^ a * y⌋ + 2 ^ (b - a) := by
    have : (⌊(2 : ℝ) ^ b * y⌋ : ℝ) <
        ((2 ^ (b - a) * ⌊(2 : ℝ) ^ a * y⌋ + 2 ^ (b - a) : ℤ) : ℝ) := by
      push_cast
      calc (⌊(2 : ℝ) ^ b * y⌋ : ℝ) ≤ 2 ^ b * y := hK1
        _ = 2 ^ (b - a) * (2 ^ a * y) := by rw [hba]; ring
        _ < 2 ^ (b - a) * ((⌊(2 : ℝ) ^ a * y⌋ : ℝ) + 1) := mul_lt_mul_of_pos_left hL2 hpba
        _ = _ := by ring
    exact_mod_cast this
  set K := ⌊(2 : ℝ) ^ b * y⌋ with hK
  set L := ⌊(2 : ℝ) ^ a * y⌋ with hL
  set N : ℤ := K - 2 ^ (b - a) * L with hN
  have hN0' : (0 : ℝ) ≤ N := by
    have : (0 : ℤ) ≤ N := by rw [hN]; linarith
    exact_mod_cast this
  have hN1' : (N : ℝ) + 1 ≤ 2 ^ (b - a) := by
    have : N + 1 ≤ 2 ^ (b - a) := by rw [hN]; linarith
    exact_mod_cast this
  have hp : proj a b y = (N : ℝ) / 2 ^ b := rfl
  constructor
  · intro h1 h2
    have hja : (2 : ℝ) ^ j = 2 ^ (j - a) * 2 ^ a := by rw [← pow_add, Nat.sub_add_cancel h1]
    have e : (2 : ℝ) ^ j * proj a b y = 2 ^ j * ((K : ℝ) / 2 ^ b) - ((2 ^ (j - a) * L : ℤ) : ℝ) := by
      rw [hp, hN]; push_cast; rw [hja, hba]; field_simp
    rw [e, Int.fract_sub_intCast]
    have e2 : (2 : ℝ) ^ b * ((K : ℝ) / 2 ^ b) = K := by field_simp
    exact digit_block h2 (m := K) hK1 hK2 (le_of_eq e2.symm) (by rw [e2]; linarith)
  · intro hj
    by_cases hjb : b ≤ j
    · have hjb' : (2 : ℝ) ^ j = 2 ^ (j - b) * 2 ^ b := by rw [← pow_add, Nat.sub_add_cancel hjb]
      have e : (2 : ℝ) ^ j * proj a b y = ((N * 2 ^ (j - b) : ℤ) : ℝ) := by
        rw [hp, hjb']; push_cast; field_simp
      rw [e, Int.fract_intCast]; norm_num
    · have hja : j < a := by omega
      have h2j : (2 : ℝ) * 2 ^ j ≤ 2 ^ a := by
        rw [← pow_succ']; exact pow_le_pow_right₀ (by norm_num) hja
      have hlt : 2 * (2 ^ j * (N : ℝ)) < 2 ^ b :=
        calc 2 * (2 ^ j * (N : ℝ)) = (2 * 2 ^ j) * N := by ring
          _ ≤ 2 ^ a * N := mul_le_mul_of_nonneg_right h2j hN0'
          _ < 2 ^ a * 2 ^ (b - a) := mul_lt_mul_of_pos_left (by linarith) hpa
          _ = 2 ^ b := by rw [hba]; ring
      have h0 : 0 ≤ (2 : ℝ) ^ j * proj a b y := by
        rw [hp]; exact mul_nonneg (by positivity) (div_nonneg hN0' hpb.le)
      have hhalf : (2 : ℝ) ^ j * proj a b y < 2⁻¹ := by
        rw [hp, ← mul_div_assoc, div_lt_iff₀ hpb]; linarith
      rw [Int.fract_eq_self.mpr ⟨h0, by linarith⟩]
      exact hhalf

lemma strong_of_det {a b : ℕ} {E : Set (AddCircle (1 : ℝ))} (hE : DeterminedByWindow a b E) : StrongDet a b E := by
  intro x x' hxx'
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨y', rfl⟩ := QuotientAddGroup.mk_surjective x'
  by_cases hab : a ≤ b
  · have key : ∀ w : ℝ, (∀ j, a ≤ j → j < b →
        (Int.fract ((2 : ℝ) ^ j * y) < 2⁻¹ ↔ Int.fract ((2 : ℝ) ^ j * w) < 2⁻¹)) →
        (((w : ℝ) : (AddCircle (1 : ℝ))) ∈ E ↔ ((proj a b y : ℝ) : (AddCircle (1 : ℝ))) ∈ E) := by
      intro w hw
      apply hE
      intro j
      rw [digit_mk, digit_mk]
      by_cases hj : a ≤ j ∧ j < b
      · have hc := (hw j hj.1 hj.2).symm.trans ((proj_digits hab y j).1 hj.1 hj.2)
        constructor
        · intro h; exact hc.1 (h hj.1 hj.2)
        · intro h _ _; exact hc.2 h
      · have := (proj_digits hab y j).2 hj
        constructor
        · intro _; exact this
        · intro _ h1 h2; exact absurd ⟨h1, h2⟩ hj
    refine (key y (fun j _ _ => Iff.rfl)).trans (key y' (fun j h1 h2 => ?_)).symm
    have := hxx' j h1 h2
    rwa [digit_mk, digit_mk] at this
  · have key : ∀ w : ℝ, (((w : ℝ) : (AddCircle (1 : ℝ))) ∈ E ↔ (((0 : ℝ) : ℝ) : (AddCircle (1 : ℝ))) ∈ E) := by
      intro w
      apply hE
      intro j
      rw [digit_mk, digit_mk, mul_zero, Int.fract_zero]
      constructor
      · intro _; norm_num
      · intro _ h1 h2; omega
    exact (key y).trans (key y').symm

/-- The dyadic interval `[m/2^A, (m+1)/2^A)`. -/
def dyBlock (A m : ℕ) : Set ℝ := {y | (m : ℝ) ≤ 2 ^ A * y ∧ 2 ^ A * y < m + 1}

lemma mem_dyBlock {A m : ℕ} {y : ℝ} :
    y ∈ dyBlock A m ↔ (m : ℝ) ≤ 2 ^ A * y ∧ 2 ^ A * y < m + 1 := Iff.rfl

lemma measurableSet_dyBlock (A m : ℕ) : MeasurableSet (dyBlock A m) :=
  show MeasurableSet ({y : ℝ | (m : ℝ) ≤ 2 ^ A * y} ∩ {y : ℝ | 2 ^ A * y < m + 1}) from
    (measurableSet_le measurable_const (measurable_const.mul measurable_id)).inter
      (measurableSet_lt (measurable_const.mul measurable_id) measurable_const)

lemma Ico_decomp (A : ℕ) (X : Set ℝ) (hX : MeasurableSet X) :
    volume (Set.Ico (0 : ℝ) 1 ∩ X) = ∑ m ∈ range (2 ^ A), volume (dyBlock A m ∩ X) := by
  have hpos : (0 : ℝ) < 2 ^ A := by positivity
  have hset : Set.Ico (0 : ℝ) 1 ∩ X = ⋃ m ∈ range (2 ^ A), (dyBlock A m ∩ X) := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_Ico, Set.mem_iUnion, Finset.mem_range, exists_prop,
      mem_dyBlock]
    constructor
    · rintro ⟨⟨h0, h1⟩, hx⟩
      have hnn : 0 ≤ (2 : ℝ) ^ A * y := mul_nonneg hpos.le h0
      refine ⟨⌊(2 : ℝ) ^ A * y⌋₊, ?_, ⟨Nat.floor_le hnn, Nat.lt_floor_add_one _⟩, hx⟩
      rw [Nat.floor_lt hnn]; push_cast
      calc (2 : ℝ) ^ A * y < 2 ^ A * 1 := mul_lt_mul_of_pos_left h1 hpos
        _ = 2 ^ A := mul_one _
    · rintro ⟨m, hm, ⟨h1, h2⟩, hx⟩
      have hm' : (m : ℝ) + 1 ≤ 2 ^ A := by exact_mod_cast Nat.succ_le_of_lt hm
      refine ⟨⟨?_, ?_⟩, hx⟩
      · by_contra h
        push_neg at h
        have := mul_neg_of_pos_of_neg hpos h
        have := Nat.cast_nonneg (α := ℝ) m
        linarith
      · by_contra h
        push_neg at h
        have := mul_le_mul_of_nonneg_left h hpos.le
        linarith
  rw [hset, measure_biUnion_finset]
  · intro m _ m' _ hne
    refine Set.disjoint_left.mpr ?_
    rintro y ⟨⟨a1, a2⟩, _⟩ ⟨⟨b1, b2⟩, _⟩
    have e1 : (m : ℝ) < m' + 1 := by linarith
    have e2 : (m' : ℝ) < m + 1 := by linarith
    have e1' : m < m' + 1 := by exact_mod_cast e1
    have e2' : m' < m + 1 := by exact_mod_cast e2
    exact hne (by omega)
  · intro m _
    exact (measurableSet_dyBlock A m).inter hX

lemma dyBlock_shift (A m : ℕ) (X : Set ℝ) (hinv : ∀ y : ℝ, y + (m : ℝ) / 2 ^ A ∈ X ↔ y ∈ X) :
    volume (dyBlock A m ∩ X) = volume (dyBlock A 0 ∩ X) := by
  have : dyBlock A 0 ∩ X = (fun y => y + (m : ℝ) / 2 ^ A) ⁻¹' (dyBlock A m ∩ X) := by
    ext y
    have e : (2 : ℝ) ^ A * (y + m / 2 ^ A) = 2 ^ A * y + m := by
      rw [mul_add]; congr 1; field_simp
    simp only [Set.mem_inter_iff, Set.mem_preimage, mem_dyBlock, e, hinv, Nat.cast_zero]
    constructor <;> rintro ⟨⟨h1, h2⟩, h3⟩ <;> exact ⟨⟨by linarith, by linarith⟩, h3⟩
  rw [this, measure_preimage_add_right]

open scoped Classical in
lemma sum_formula (A : ℕ) (G X : Set ℝ) (hG : MeasurableSet G) (hX : MeasurableSet X)
    (hblock : ∀ m : ℕ, (∀ y ∈ dyBlock A m, y ∈ G) ∨ (∀ y ∈ dyBlock A m, y ∉ G))
    (hinv : ∀ (m : ℕ) (y : ℝ), y + (m : ℝ) / 2 ^ A ∈ X ↔ y ∈ X) :
    volume (Set.Ico (0 : ℝ) 1 ∩ (G ∩ X)) =
      ((range (2 ^ A)).filter (fun m => ∀ y ∈ dyBlock A m, y ∈ G)).card *
        volume (dyBlock A 0 ∩ X) := by
  rw [Ico_decomp A _ (hG.inter hX)]
  calc ∑ m ∈ range (2 ^ A), volume (dyBlock A m ∩ (G ∩ X))
      = ∑ m ∈ range (2 ^ A),
          (if (∀ y ∈ dyBlock A m, y ∈ G) then volume (dyBlock A 0 ∩ X) else 0) := by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        by_cases h : ∀ y ∈ dyBlock A m, y ∈ G
        · rw [if_pos h, ← dyBlock_shift A m X (hinv m)]
          congr 1
          ext y
          constructor
          · rintro ⟨hy, _, hx⟩; exact ⟨hy, hx⟩
          · rintro ⟨hy, hx⟩; exact ⟨hy, h y hy, hx⟩
        · rw [if_neg h]
          have h' := (hblock m).resolve_left h
          have : dyBlock A m ∩ (G ∩ X) = ∅ :=
            Set.subset_empty_iff.mp (fun y hy => (h' y hy.1 hy.2.1).elim)
          rw [this, measure_empty]
    _ = _ := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]

lemma ennreal_aux (cG cU u t : ENNReal) (h : cU * u = 1) : cG * t = cG * u * (cU * t) := by
  calc cG * t = cG * t * (cU * u) := by rw [h, mul_one]
    _ = cG * u * (cU * t) := by ring

/-- Two-window independence: a set determined by digits `[0,A)` and a set determined by
digits `[A,B)` are independent. -/
lemma indep_two {A B : ℕ} {F E : Set (AddCircle (1 : ℝ))} (hF : StrongDet 0 A F)
    (hE : StrongDet A B E) (mF : MeasurableSet F) (mE : MeasurableSet E) :
    (haarAddCircle (T := 1)) (F ∩ E) = (haarAddCircle (T := 1)) F * (haarAddCircle (T := 1)) E := by
  have hG : MeasurableSet (((↑) : ℝ → (AddCircle (1 : ℝ))) ⁻¹' F) := AddCircle.measurable_mk' mF
  have hX : MeasurableSet (((↑) : ℝ → (AddCircle (1 : ℝ))) ⁻¹' E) := AddCircle.measurable_mk' mE
  have hblock : ∀ m : ℕ, (∀ y ∈ dyBlock A m, y ∈ ((↑) : ℝ → (AddCircle (1 : ℝ))) ⁻¹' F) ∨
      (∀ y ∈ dyBlock A m, y ∉ ((↑) : ℝ → (AddCircle (1 : ℝ))) ⁻¹' F) := by
    intro m
    by_cases h : ∃ y ∈ dyBlock A m, y ∈ ((↑) : ℝ → (AddCircle (1 : ℝ))) ⁻¹' F
    · left
      obtain ⟨y0, hy0, hy0G⟩ := h
      intro y hy
      rw [mem_dyBlock] at hy0 hy
      exact (hF (y0 : (AddCircle (1 : ℝ))) (y : (AddCircle (1 : ℝ))) (fun j _ hj => by
        rw [digit_mk, digit_mk]
        exact digit_block hj (m := (m : ℤ)) (by exact_mod_cast hy0.1) (by exact_mod_cast hy0.2)
          (by exact_mod_cast hy.1) (by exact_mod_cast hy.2))).1 hy0G
    · right
      push_neg at h
      exact h
  have hinv : ∀ (m : ℕ) (y : ℝ), y + (m : ℝ) / 2 ^ A ∈ ((↑) : ℝ → (AddCircle (1 : ℝ))) ⁻¹' E ↔
      y ∈ ((↑) : ℝ → (AddCircle (1 : ℝ))) ⁻¹' E := by
    intro m y
    apply hE
    intro j hj _
    rw [digit_mk, digit_mk, digit_shift hj]
  have hinvU : ∀ (m : ℕ) (y : ℝ), y + (m : ℝ) / 2 ^ A ∈ (Set.univ : Set ℝ) ↔
      y ∈ (Set.univ : Set ℝ) := fun _ _ => Iff.rfl
  have hblockU : ∀ m : ℕ, (∀ y ∈ dyBlock A m, y ∈ (Set.univ : Set ℝ)) ∨
      (∀ y ∈ dyBlock A m, y ∉ (Set.univ : Set ℝ)) := fun _ => Or.inl fun _ _ => trivial
  have kFE := sum_formula A _ _ hG hX hblock hinv
  have kF := sum_formula A _ _ hG MeasurableSet.univ hblock hinvU
  have kE := sum_formula A _ _ MeasurableSet.univ hX hblockU hinv
  have kU := sum_formula A _ _ MeasurableSet.univ MeasurableSet.univ hblockU hinvU
  rw [haar_eq _ (mF.inter mE), haar_eq _ mF, haar_eq _ mE]
  have e1 : volume (Set.Ico (0 : ℝ) 1 ∩ (((↑) : ℝ → (AddCircle (1 : ℝ))) ⁻¹' (F ∩ E))) =
      volume (Set.Ico (0 : ℝ) 1 ∩ ((((↑) : ℝ → (AddCircle (1 : ℝ))) ⁻¹' F) ∩ (((↑) : ℝ → (AddCircle (1 : ℝ))) ⁻¹' E))) := rfl
  have e2 : volume (Set.Ico (0 : ℝ) 1 ∩ (((↑) : ℝ → (AddCircle (1 : ℝ))) ⁻¹' F)) =
      volume (Set.Ico (0 : ℝ) 1 ∩ ((((↑) : ℝ → (AddCircle (1 : ℝ))) ⁻¹' F) ∩ Set.univ)) := by
    rw [Set.inter_univ]
  have e3 : volume (Set.Ico (0 : ℝ) 1 ∩ (((↑) : ℝ → (AddCircle (1 : ℝ))) ⁻¹' E)) =
      volume (Set.Ico (0 : ℝ) 1 ∩ (Set.univ ∩ (((↑) : ℝ → (AddCircle (1 : ℝ))) ⁻¹' E))) := by
    rw [Set.univ_inter]
  have e4 : volume (Set.Ico (0 : ℝ) 1 ∩ ((Set.univ : Set ℝ) ∩ Set.univ)) = 1 := by simp
  rw [e1, e2, e3, kFE, kF, kE]
  rw [kU] at e4
  exact ennreal_aux _ _ _ _ e4

lemma det_mono {a b a' b' : ℕ} {E : Set (AddCircle (1 : ℝ))} (h : StrongDet a b E)
    (hw : ∀ j, a ≤ j → j < b → a' ≤ j ∧ j < b') : StrongDet a' b' E :=
  fun x y hxy => h x y (fun j h1 h2 => hxy j (hw j h1 h2).1 (hw j h1 h2).2)

lemma det_iInter {ι : Type*} {a b : ℕ} (s : Finset ι) (E : ι → Set (AddCircle (1 : ℝ)))
    (h : ∀ i ∈ s, StrongDet a b (E i)) : StrongDet a b (⋂ i ∈ s, E i) := by
  intro x y hxy
  simp only [Set.mem_iInter]
  exact forall₂_congr fun i hi => h i hi x y hxy

end DigitIndep

open DigitIndep in
/-- Sets determined by pairwise disjoint digit windows are independent under Haar measure. -/
lemma measure_iInter_of_disjoint_windows {ι : Type*} (s : Finset ι) (a b : ι → ℕ)
    (E : ι → Set (AddCircle (1 : ℝ))) (hE : ∀ i ∈ s, DeterminedByWindow (a i) (b i) (E i))
    (hmeas : ∀ i ∈ s, MeasurableSet (E i))
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → b i ≤ a j ∨ b j ≤ a i) :
    (haarAddCircle (T := 1)) (⋂ i ∈ s, E i) = ∏ i ∈ s, (haarAddCircle (T := 1)) (E i) := by
  classical
  have hE' : ∀ i ∈ s, StrongDet (a i) (b i) (E i) := fun i hi => strong_of_det (hE i hi)
  clear hE
  revert hE' hmeas hdisj
  induction s using Finset.induction_on_max_value (f := b) with
  | empty => intro _ _ _; simp
  | insert i s hi hmax ih =>
    intro hmeas hdisj hE
    rw [Finset.prod_insert hi, Finset.set_biInter_insert, Set.inter_comm]
    have hF : StrongDet 0 (a i) (⋂ j ∈ s, E j) := by
      refine det_iInter s E (fun j hj => det_mono (hE j (Finset.mem_insert_of_mem hj)) ?_)
      intro k hk1 hk2
      have hij : i ≠ j := fun h => hi (h ▸ hj)
      have hb := hmax j hj
      rcases hdisj i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj) hij with h | h
      · omega
      · omega
    rw [indep_two hF (hE i (Finset.mem_insert_self i s))
      (Finset.measurableSet_biInter s (fun j hj => hmeas j (Finset.mem_insert_of_mem hj)))
      (hmeas i (Finset.mem_insert_self i s))]
    rw [ih (fun j hj => hmeas j (Finset.mem_insert_of_mem hj))
      (fun j hj k hk => hdisj j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk))
      (fun j hj => hE j (Finset.mem_insert_of_mem hj)),
      mul_comm]

end OMA.Port23

/- ### BlockFloor -/

/-! # Erdős 996: deterministic lower floor of a block (G3). -/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real

namespace OMA.Port23


/-- Crude spike floor: `φ_d ≥ -t/√(t(1-t))` with `t = 2^{-d}` (valid for all `d`). -/
lemma spike_ge_floor_aux (d : ℕ) (x : (AddCircle (1 : ℝ))) :
    -((2 : ℝ)⁻¹ ^ d / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d))) ≤ spike d x := by
  unfold spike
  rw [← neg_div]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  have h : (0 : ℝ) ≤ Set.indicator (QuotientAddGroup.mk '' Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d))
      (1 : (AddCircle (1 : ℝ)) → ℝ) x :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) x
  linarith

/-- The spike floor constant `g` satisfies `g² ≤ 2 · 2^{-d}`. -/
lemma spike_floor_exists (d : ℕ) :
    ∃ g : ℝ, 0 ≤ g ∧ g ^ 2 ≤ 2 * (2 : ℝ)⁻¹ ^ d ∧ ∀ y : (AddCircle (1 : ℝ)), -g ≤ spike d y := by
  have ht0 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ d := by positivity
  have ht1 : (2 : ℝ)⁻¹ ^ d ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  refine ⟨(2 : ℝ)⁻¹ ^ d / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)),
    div_nonneg ht0.le (Real.sqrt_nonneg _), ?_, fun y => spike_ge_floor_aux d y⟩
  rcases Nat.eq_zero_or_pos d with rfl | hd1
  · simp
  · have ht2 : (2 : ℝ)⁻¹ ^ d ≤ 1 / 2 := by
      have := pow_le_pow_of_le_one (a := (2 : ℝ)⁻¹) (by norm_num) (by norm_num) hd1
      simpa using this
    have hs : Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) ^ 2
        = (2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d) := Real.sq_sqrt (by nlinarith)
    rw [div_pow, hs, div_le_iff₀ (by nlinarith)]
    nlinarith [mul_nonneg (sq_nonneg ((2 : ℝ)⁻¹ ^ d)) (sub_nonneg.2 ht2)]

/-- Deterministic lower floor `F ≥ -C₃ λ / B` under the depth choice `64 B² L / λ ≤ 2^d`. -/
lemma block_lower_floor (lam B : ℝ) (L d D U : ℕ) (hlam : 0 < lam) (hB : 1 ≤ B)
    (hL : 1 ≤ L) (hd : 64 * B ^ 2 * L / lam ≤ 2 ^ d) (x : (AddCircle (1 : ℝ))) :
    -(lam / B) ≤ block lam L d D U x := by
  obtain ⟨g, hg0, hg2, hspk⟩ := spike_floor_exists d
  have hLpos : (0 : ℝ) < L := Nat.cast_pos.2 hL
  have hB0 : 0 < B := by linarith
  have ht0 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ d := by positivity
  have hsum : -((L : ℝ) * g) ≤
      ∑ q ∈ Finset.Icc 1 L, spike d ((2 ^ (U + q * D) : ℕ) • x) := by
    have h := Finset.sum_le_sum (s := Finset.Icc 1 L)
      (fun q _ => hspk ((2 ^ (U + q * D) : ℕ) • x))
    rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at h
    linarith
  have htd : (2 : ℝ)⁻¹ ^ d * 2 ^ d = 1 := by rw [← mul_pow]; norm_num
  have h1 : 64 * B ^ 2 * L ≤ 2 ^ d * lam := (div_le_iff₀ hlam).1 hd
  have h2 := mul_le_mul_of_nonneg_right h1 ht0.le
  have e : 2 ^ d * lam * (2 : ℝ)⁻¹ ^ d = lam := by linear_combination lam * htd
  have hkey : (L : ℝ) * g ^ 2 * B ^ 2 ≤ lam := by
    have := mul_le_mul_of_nonneg_left hg2 (by positivity : (0 : ℝ) ≤ L * B ^ 2)
    nlinarith
  have hsq : Real.sqrt (lam / L) ^ 2 = lam / L := Real.sq_sqrt (div_nonneg hlam.le hLpos.le)
  have hAB : Real.sqrt (lam / L) * (L * g) * B ≤ lam := by
    apply (pow_le_pow_iff_left₀ (by positivity) hlam.le two_ne_zero).1
    rw [mul_pow, mul_pow, hsq]
    have e2 : lam / L * ((L : ℝ) ^ 2 * g ^ 2) * B ^ 2 = lam * (L * g ^ 2 * B ^ 2) := by
      field_simp
    rw [mul_pow, e2]
    have := mul_le_mul_of_nonneg_left hkey hlam.le
    nlinarith
  have h3 : Real.sqrt (lam / L) * (L * g) ≤ lam / B := (le_div_iff₀ hB0).2 hAB
  have h4 := mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg (lam / L))
  unfold block
  linarith

end OMA.Port23

/- ### TrialSignal -/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real

namespace OMA.Port23


/-- Pointwise lower bound for the spike. -/
lemma spike_ge_neg (d : ℕ) (y : (AddCircle (1 : ℝ))) :
    -((2 : ℝ)⁻¹ ^ d) / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) ≤ spike d y := by
  unfold spike
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  have : (0 : ℝ) ≤ Set.indicator (QuotientAddGroup.mk '' Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d))
      (1 : (AddCircle (1 : ℝ)) → ℝ) y := Set.indicator_nonneg (fun _ _ => zero_le_one) y
  linarith

/-- Value of the spike on its support interval. -/
lemma spike_eq_of_mem (d : ℕ) (y : (AddCircle (1 : ℝ)))
    (hy : y ∈ QuotientAddGroup.mk '' Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d)) :
    spike d y = (1 - (2 : ℝ)⁻¹ ^ d) / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) := by
  unfold spike
  rw [Set.indicator_of_mem hy]
  simp

/-- Local amplification: on the good event the trial sum is at least `2 B ℓ`
(the probability bound `≥ c₀ λ / B²` is a consequence of G2). -/
lemma trial_signal (lam B : ℝ) (L ℓ d D U M : ℕ) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hB : 100 ≤ B) (hL : 1 ≤ L) (hℓ : 8 * ℓ ≤ L) (hD : d + 2 ≤ D)
    (hd : 64 * B ^ 2 * L / lam ≤ 2 ^ d) (hd' : (2 : ℝ) ^ d < 128 * B ^ 2 * L / lam) (x : (AddCircle (1 : ℝ)))
    (hgood : ∃ h ∈ Finset.Icc (ℓ + 1) (L + 1),
      (2 ^ (U + M + h * D) : ℕ) • x ∈ QuotientAddGroup.mk '' Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d)) :
    2 * B * ℓ ≤ ∑ r ∈ Finset.Icc 1 ℓ, block lam L d D U ((2 ^ (M + r * D) : ℕ) • x) := by
  obtain ⟨h, hh, hx⟩ := hgood
  rw [Finset.mem_Icc] at hh
  have hppos : 0 < (2 : ℝ)⁻¹ ^ d := by positivity
  have hp2 : (2 : ℝ)⁻¹ ^ d * 2 ^ d = 1 := by rw [← mul_pow]; norm_num
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < L := by linarith
  have hkey : 64 * B ^ 2 * L * (2 : ℝ)⁻¹ ^ d ≤ lam := by
    have h0 := (div_le_iff₀ hlam).1 hd
    have h1 := mul_le_mul_of_nonneg_right h0 hppos.le
    calc 64 * B ^ 2 * L * (2 : ℝ)⁻¹ ^ d ≤ 2 ^ d * lam * (2 : ℝ)⁻¹ ^ d := h1
      _ = lam := by linear_combination lam * hp2
  have hB2 : (10000 : ℝ) ≤ B ^ 2 := by nlinarith
  have hLp0 : 0 ≤ (L : ℝ) * (2 : ℝ)⁻¹ ^ d := by positivity
  have hLp : (L : ℝ) * (2 : ℝ)⁻¹ ^ d ≤ 1 / 640000 := by
    nlinarith [mul_le_mul_of_nonneg_right hB2 hLp0]
  have hpL : (2 : ℝ)⁻¹ ^ d ≤ (L : ℝ) * (2 : ℝ)⁻¹ ^ d := by nlinarith
  have hp1 : 0 < 1 - (2 : ℝ)⁻¹ ^ d := by linarith
  have hs : 0 < Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) :=
    Real.sqrt_pos.2 (mul_pos hppos hp1)
  have hs2 : Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) ^ 2
      = (2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d) := Real.sq_sqrt (mul_pos hppos hp1).le
  have ha : 0 ≤ Real.sqrt (lam / L) := Real.sqrt_nonneg _
  have ha2 : Real.sqrt (lam / L) ^ 2 * L = lam := by
    rw [Real.sq_sqrt (div_nonneg hlam.le hLpos.le)]; field_simp
  -- the amplification inequality for one block
  have hmain : 2 * B ≤ Real.sqrt (lam / L) *
      ((1 - L * (2 : ℝ)⁻¹ ^ d) / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d))) := by
    rw [← mul_div_assoc, le_div_iff₀ hs]
    by_contra hcon
    push_neg at hcon
    have h0 : 0 ≤ Real.sqrt (lam / L) * (1 - L * (2 : ℝ)⁻¹ ^ d) :=
      mul_nonneg ha (by linarith)
    have h1 := mul_self_lt_mul_self h0 hcon
    have h2 : Real.sqrt (lam / L) ^ 2 * (1 - L * (2 : ℝ)⁻¹ ^ d) ^ 2
        < 4 * B ^ 2 * ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) := by
      rw [← hs2]; nlinarith [h1]
    have h3 : lam * (1 - L * (2 : ℝ)⁻¹ ^ d) ^ 2
        < 4 * B ^ 2 * ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) * L := by
      rw [← ha2]; nlinarith [mul_lt_mul_of_pos_right h2 hLpos]
    have h4 : 4 * B ^ 2 * ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) * L
        ≤ 4 * B ^ 2 * L * (2 : ℝ)⁻¹ ^ d := by
      have : 0 ≤ B ^ 2 * L * (2 : ℝ)⁻¹ ^ d * (2 : ℝ)⁻¹ ^ d := by positivity
      nlinarith
    have h5 : lam * (L * (2 : ℝ)⁻¹ ^ d) ≤ lam * (1 / 640000) :=
      mul_le_mul_of_nonneg_left hLp hlam.le
    have h6 : 0 ≤ lam * (L * (2 : ℝ)⁻¹ ^ d) ^ 2 := by positivity
    nlinarith
  have hterm : ∀ r ∈ Finset.Icc 1 ℓ,
      2 * B ≤ block lam L d D U ((2 ^ (M + r * D) : ℕ) • x) := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    obtain ⟨q, rfl⟩ : ∃ q, h = q + r := ⟨h - r, by omega⟩
    have hq0 : q ∈ Finset.Icc 1 L := Finset.mem_Icc.2 ⟨by omega, by omega⟩
    have hbig : spike d ((2 ^ (U + q * D) : ℕ) • ((2 ^ (M + r * D) : ℕ) • x))
        = (1 - (2 : ℝ)⁻¹ ^ d) / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) := by
      apply spike_eq_of_mem
      rw [smul_smul, ← pow_add]
      have he : U + q * D + (M + r * D) = U + M + (q + r) * D := by ring
      rw [he]; exact hx
    have hnn : ∀ q' ∈ Finset.Icc 1 L,
        0 ≤ spike d ((2 ^ (U + q' * D) : ℕ) • ((2 ^ (M + r * D) : ℕ) • x))
          + (2 : ℝ)⁻¹ ^ d / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) := by
      intro q' _
      have := spike_ge_neg d ((2 ^ (U + q' * D) : ℕ) • ((2 ^ (M + r * D) : ℕ) • x))
      rw [neg_div] at this
      linarith
    have hsingle := Finset.single_le_sum hnn hq0
    rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, hbig,
      Nat.add_sub_cancel] at hsingle
    have hsum : (1 - L * (2 : ℝ)⁻¹ ^ d) / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d))
        ≤ ∑ q' ∈ Finset.Icc 1 L,
          spike d ((2 ^ (U + q' * D) : ℕ) • ((2 ^ (M + r * D) : ℕ) • x)) := by
      have hid : (1 - L * (2 : ℝ)⁻¹ ^ d) / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d))
          = (1 - (2 : ℝ)⁻¹ ^ d) / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d))
            + (2 : ℝ)⁻¹ ^ d / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d))
            - (L : ℝ) * ((2 : ℝ)⁻¹ ^ d / Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d))) := by
        field_simp; ring
      rw [hid]; linarith
    unfold block
    exact hmain.trans (mul_le_mul_of_nonneg_left hsum ha)
  calc 2 * B * (ℓ : ℝ) = ∑ r ∈ Finset.Icc 1 ℓ, 2 * B := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]; ring
    _ ≤ _ := Finset.sum_le_sum hterm

end OMA.Port23

/- ### Construction -/

/-!
Section: Erdős 996, assembly: the explicit global construction

Everything here is a plain definition (no proofs). See the module docs for the
mathematics. The construction depends on one natural parameter `A` (the decay rate of the
stage costs, `λ_k = 2^{-A(k+1)}`), chosen in the assembly from the target exponent `C`.

Indexing conventions (all `ℕ`, starting at `0`):
* stages `k = 0, 1, 2, …`; stage `k` owns the trials `s ∈ [firstTrial A k, firstTrial A (k+1))`;
* trials `s = 0, 1, 2, …` are numbered globally; trial `s` has length `trialLen s = 20·21^s`
  and occupies the global indices `j ∈ [21^s - 1, 21^(s+1) - 1)`, the `r`-th exponent
  (`1 ≤ r ≤ trialLen s`) sitting at `j = 21^s + r - 2`;
* the selected exponents are `mExp A j = trialStart A s + r * spacing A (stage A s)` and
  `nSeq A j = 2 ^ mExp A j`.
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace OMA.Port23
namespace Asm


/-! ### Stage parameters -/

/-- `a_k = A (k+1)`, so that `λ_k = 2^{-a_k}`. -/
def aExp (A k : ℕ) : ℕ := A * (k + 1)

/-- Stage cost `λ_k = 2^{-A(k+1)}` (squared `L²` norm of the `k`-th block). -/
noncomputable def lam (A k : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ aExp A k

/-- Number of trials in stage `k`: `T_k = 2^{a_k + k + 24}`. -/
def nTrials (A k : ℕ) : ℕ := 2 ^ (aExp A k + k + 24)

/-- Index of the first trial of stage `k`: `S_0 = 0`, `S_{k+1} = S_k + T_k`. -/
def firstTrial (A : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => firstTrial A k + nTrials A k

/-- Number of layers of the `k`-th block: `L_k = 8 · 21^{S_{k+1}}` (≥ 8 × every trial length
of the stage). -/
def blockLen (A k : ℕ) : ℕ := 8 * 21 ^ firstTrial A (k + 1)

/-- Spike depth `d_k = ⌈log₂(64 B₀² L_k / λ_k)⌉` with `B₀ = 100`, i.e. the least `d` with
`640000 · L_k · 2^{a_k} ≤ 2^d`. -/
def depth (A k : ℕ) : ℕ := Nat.clog 2 (640000 * blockLen A k * 2 ^ aExp A k)

/-- Layer spacing `D_k = d_k + 2`. -/
def spacing (A k : ℕ) : ℕ := depth A k + 2

/-- Base shift of the `k`-th block: `U_0 = 0`, `U_{k+1} = U_k + L_k D_k + d_k`
(so the dyadic valuation bands of different blocks are disjoint). -/
def shift (A : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => shift A k + blockLen A k * spacing A k + depth A k

/-- `log₂` of the Fourier threshold of the `k`-th block: `Q_k = 2^{E_k}`, `E_k = U_{k+1} + 2`. -/
def logQ (A k : ℕ) : ℕ := shift A (k + 1) + 2

/-! ### Trials and the exponent sequence -/

/-- The stage containing trial `s`: the largest `k ≤ s` with `S_k ≤ s`. -/
def stage (A s : ℕ) : ℕ := Nat.findGreatest (fun k => firstTrial A k ≤ s) s

/-- Length of trial `s`: `ℓ_s = 20 · 21^s` (so `P_s + 1 = 21^s` exponents precede it). -/
def trialLen (s : ℕ) : ℕ := 20 * 21 ^ s

/-- Start offset of trial `s`: `M_0 = 0`, `M_{s+1} = M_s + (L_k + 2) D_k` with `k = stage s`. -/
def trialStart (A : ℕ) : ℕ → ℕ
  | 0 => 0
  | s + 1 => trialStart A s + (blockLen A (stage A s) + 2) * spacing A (stage A s)

/-- The trial containing global index `j`: `s = ⌊log₂₁ (j+1)⌋`. -/
def trialOf (j : ℕ) : ℕ := Nat.log 21 (j + 1)

/-- The `j`-th selected exponent: `m_j = M_s + r D_{stage s}` with `s = trialOf j`,
`r = j + 2 - 21^s ∈ [1, ℓ_s]`. -/
def mExp (A j : ℕ) : ℕ :=
  trialStart A (trialOf j) + (j + 2 - 21 ^ trialOf j) * spacing A (stage A (trialOf j))

/-- The lacunary sequence `n_j = 2^{m_j}`. -/
def nSeq (A j : ℕ) : ℕ := 2 ^ mExp A j

/-! ### The function -/

/-- The `k`-th block `F_k = √(λ_k/L_k) ∑_{q=1}^{L_k} φ_{d_k}(2^{U_k + q D_k} ·)`. -/
noncomputable def blk (A k : ℕ) (x : (AddCircle (1 : ℝ))) : ℝ :=
  block (lam A k) (blockLen A k) (depth A k) (spacing A k) (shift A k) x

/-- The `(k,q)` atom `φ_{d_k}(2^{U_k + q D_k} x)`; `blk A k = √(λ_k/L_k) ∑_q atom A k q`. -/
noncomputable def atom (A k q : ℕ) (x : (AddCircle (1 : ℝ))) : ℝ :=
  spike (depth A k) ((2 ^ (shift A k + q * spacing A k) : ℕ) • x)

/-- Deterministic floor constant `c_k = λ_k / B₀` (`B₀ = 100`): `F_k ≥ -c_k`. -/
noncomputable def floorC (A k : ℕ) : ℝ := lam A k / 100

/-- The nonnegative series `∑_k (F_k + c_k)` in `[0, ∞]`. -/
noncomputable def gPos (A : ℕ) (x : (AddCircle (1 : ℝ))) : ℝ≥0∞ :=
  ∑' k, ENNReal.ofReal (blk A k x + floorC A k)

/-- The counterexample, pointwise: `g = ∑_k (F_k + c_k) - ∑_k c_k` (where the first series is
finite, which is almost everywhere). -/
noncomputable def gFun (A : ℕ) (x : (AddCircle (1 : ℝ))) : ℝ :=
  (gPos A x).toReal - ∑' k, floorC A k

/-! ### Events -/

/-- The support of the positive part of the spike `φ_d`: the arc `[0, 2^{-d})`. -/
def spikeSet (d : ℕ) : Set (AddCircle (1 : ℝ)) := QuotientAddGroup.mk '' Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d)

/-- `{x | 2^v x ∈ [0, 2^{-d})}`: the event that `φ_d(2^v x)` spikes. -/
def hitSet (d v : ℕ) : Set (AddCircle (1 : ℝ)) := {x | (2 ^ v : ℕ) • x ∈ spikeSet d}

/-- Good event of trial `s` (Ho, Def. 3.6): some central layer `h ∈ [ℓ_s + 1, L_k + 1]` spikes. -/
def goodSet (A s : ℕ) : Set (AddCircle (1 : ℝ)) :=
  ⋃ h ∈ Finset.Icc (trialLen s + 1) (blockLen A (stage A s) + 1),
    hitSet (depth A (stage A s)) (shift A (stage A s) + trialStart A s + h * spacing A (stage A s))

/-- Stage event `S_k`: some trial of stage `k` is good. -/
def stageGood (A k : ℕ) : Set (AddCircle (1 : ℝ)) :=
  ⋃ s ∈ Finset.Ico (firstTrial A k) (firstTrial A (k + 1)), goodSet A s

end Asm
end OMA.Port23

/- ### Params -/

/-!
Section: Assembly sub-lemma 1 (Params): elementary facts about the stage parameters

Ho, arXiv:2604.18535, (3.1)–(3.2), (4.3)–(4.9),
Lemma 4.1 and the upper half of Lemma 5.1 (`scale_bound`).
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace OMA.Port23
namespace Asm


lemma lam_pos (A k : ℕ) : 0 < lam A k := by
  unfold lam; positivity

lemma lam_le_one (A k : ℕ) : lam A k ≤ 1 := by
  unfold lam; exact pow_le_one₀ (by norm_num) (by norm_num)

lemma lam_le (A : ℕ) (hA : 1 ≤ A) (k : ℕ) : lam A k ≤ (2 : ℝ)⁻¹ ^ (k + 1) := by
  unfold lam aExp
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by nlinarith)

lemma geomSucc_summable : Summable (fun k : ℕ => (2 : ℝ)⁻¹ ^ (k + 1)) := by
  have := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)).mul_right (2⁻¹)
  exact this.congr (fun k => (pow_succ _ _).symm)

lemma geomSucc_tsum : ∑' k : ℕ, (2 : ℝ)⁻¹ ^ (k + 1) = 1 := by
  simp_rw [pow_succ]
  rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

lemma summable_lam (A : ℕ) (hA : 1 ≤ A) : Summable (lam A) := by
  exact Summable.of_nonneg_of_le (fun k => (lam_pos A k).le) (lam_le A hA) geomSucc_summable

lemma tsum_lam_le_one (A : ℕ) (hA : 1 ≤ A) : ∑' k, lam A k ≤ 1 := by
  calc ∑' k, lam A k ≤ ∑' k : ℕ, (2 : ℝ)⁻¹ ^ (k + 1) :=
        Summable.tsum_le_tsum (lam_le A hA) (summable_lam A hA) geomSucc_summable
    _ = 1 := geomSucc_tsum

lemma floorC_nonneg (A k : ℕ) : 0 ≤ floorC A k := by
  unfold floorC; exact div_nonneg (lam_pos A k).le (by norm_num)

lemma summable_floorC (A : ℕ) (hA : 1 ≤ A) : Summable (floorC A) := by
  exact (summable_lam A hA).div_const 100

lemma tsum_floorC_le (A : ℕ) (hA : 1 ≤ A) : ∑' k, floorC A k ≤ 1 / 100 := by
  show ∑' k, lam A k / 100 ≤ 1 / 100
  rw [tsum_div_const]
  have := tsum_lam_le_one A hA
  linarith

lemma one_le_blockLen (A k : ℕ) : 1 ≤ blockLen A k := by
  unfold blockLen
  have : 0 < 21 ^ firstTrial A (k + 1) := by positivity
  omega

lemma depth_nat (A k : ℕ) :
    640000 * blockLen A k * 2 ^ aExp A k ≤ 2 ^ depth A k ∧
      2 ^ depth A k < 2 * (640000 * blockLen A k * 2 ^ aExp A k) := by
  have hN1 : 1 < 640000 * blockLen A k * 2 ^ aExp A k := by
    have := one_le_blockLen A k
    have : 0 < 2 ^ aExp A k := by positivity
    nlinarith
  have hd : depth A k = Nat.clog 2 (640000 * blockLen A k * 2 ^ aExp A k) := rfl
  rw [hd]
  refine ⟨Nat.le_pow_clog (by norm_num) _, ?_⟩
  have hpos := Nat.clog_pos (b := 2) (by norm_num) hN1
  have hlt := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hN1
  have e : 2 ^ Nat.clog 2 (640000 * blockLen A k * 2 ^ aExp A k) =
      2 * 2 ^ (Nat.clog 2 (640000 * blockLen A k * 2 ^ aExp A k)).pred := by
    rw [← pow_succ']
    exact congrArg _ (Nat.succ_pred_eq_of_pos hpos).symm
  omega

lemma one_le_depth (A k : ℕ) : 1 ≤ depth A k := by
  obtain ⟨h1, _⟩ := depth_nat A k
  rcases Nat.eq_zero_or_pos (depth A k) with h | h
  · rw [h] at h1
    have := one_le_blockLen A k
    have : 0 < 2 ^ aExp A k := by positivity
    nlinarith
  · exact h

/-- The depth choice (Ho (3.2) / (4.5)) with `B = B₀ = 100`, in the exact form used by
`block_lower_floor` and `trial_signal`. -/
lemma depth_spec (A k : ℕ) :
    64 * (100 : ℝ) ^ 2 * (blockLen A k : ℝ) / lam A k ≤ 2 ^ depth A k ∧
      (2 : ℝ) ^ depth A k < 128 * (100 : ℝ) ^ 2 * (blockLen A k : ℝ) / lam A k := by
  obtain ⟨h1, h2⟩ := depth_nat A k
  have hlam : (lam A k)⁻¹ = (2 : ℝ) ^ aExp A k := by unfold lam; rw [inv_pow, inv_inv]
  have e1 : 64 * (100 : ℝ) ^ 2 * (blockLen A k : ℝ) / lam A k =
      ((640000 * blockLen A k * 2 ^ aExp A k : ℕ) : ℝ) := by
    rw [div_eq_mul_inv, hlam]; push_cast; ring
  have e2 : 128 * (100 : ℝ) ^ 2 * (blockLen A k : ℝ) / lam A k =
      ((2 * (640000 * blockLen A k * 2 ^ aExp A k) : ℕ) : ℝ) := by
    rw [div_eq_mul_inv, hlam]; push_cast; ring
  rw [e1, e2]
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

lemma firstTrial_strictMono (A : ℕ) : StrictMono (firstTrial A) := by
  refine strictMono_nat_of_lt_succ (fun k => ?_)
  show firstTrial A k < firstTrial A k + nTrials A k
  have : 0 < nTrials A k := by unfold nTrials; positivity
  omega

lemma le_firstTrial (A k : ℕ) : k ≤ firstTrial A k := by
  exact (firstTrial_strictMono A).id_le k

lemma stage_spec (A s : ℕ) :
    firstTrial A (stage A s) ≤ s ∧ s < firstTrial A (stage A s + 1) := by
  have h0 : firstTrial A (stage A s) ≤ s :=
    Nat.findGreatest_spec (P := fun k => firstTrial A k ≤ s) (Nat.zero_le s) (by simp [firstTrial])
  refine ⟨h0, ?_⟩
  by_contra h
  rw [not_lt] at h
  have hle : stage A s + 1 ≤ s := le_trans (le_firstTrial A _) h
  exact Nat.findGreatest_is_greatest (P := fun k => firstTrial A k ≤ s)
    (Nat.lt_succ_self _) hle h

lemma stage_eq (A s k : ℕ) (h1 : firstTrial A k ≤ s) (h2 : s < firstTrial A (k + 1)) :
    stage A s = k := by
  obtain ⟨a1, a2⟩ := stage_spec A s
  have hm := (firstTrial_strictMono A).monotone
  rcases lt_trichotomy (stage A s) k with h | h | h
  · have := hm (show stage A s + 1 ≤ k from h); omega
  · exact h
  · have := hm (show k + 1 ≤ stage A s from h); omega

lemma stage_mono (A : ℕ) : Monotone (stage A) := by
  intro s t hst
  by_contra h
  rw [not_le] at h
  obtain ⟨a1, _⟩ := stage_spec A s
  obtain ⟨_, b2⟩ := stage_spec A t
  have := (firstTrial_strictMono A).monotone (show stage A t + 1 ≤ stage A s from h)
  omega

/-- Every trial of stage `k` is at most `L_k / 8` long. -/
lemma trialLen_le (A s : ℕ) : 8 * trialLen s ≤ blockLen A (stage A s) := by
  unfold trialLen blockLen
  have h1 : s + 1 ≤ firstTrial A (stage A s + 1) := Nat.succ_le_of_lt (stage_spec A s).2
  have h2 : 21 ^ (s + 1) ≤ 21 ^ firstTrial A (stage A s + 1) := Nat.pow_le_pow_right (by norm_num) h1
  rw [pow_succ] at h2
  omega

lemma shift_mono (A : ℕ) : Monotone (shift A) := by
  refine monotone_nat_of_le_succ (fun k => ?_)
  show shift A k ≤ shift A k + blockLen A k * spacing A k + depth A k
  omega

lemma trialStart_mono (A : ℕ) : Monotone (trialStart A) := by
  refine monotone_nat_of_le_succ (fun k => ?_)
  show trialStart A k ≤ trialStart A k + (blockLen A (stage A k) + 2) * spacing A (stage A k)
  omega

/-- Deterministic floor of a block (Ho (3.4) with `C₃ = 1`, `B = 100`). -/
lemma blk_floor (A k : ℕ) (x : (AddCircle (1 : ℝ))) : -(floorC A k) ≤ blk A k x := by
  have := block_lower_floor (lam A k) 100 (blockLen A k) (depth A k) (spacing A k) (shift A k)
    (lam_pos A k) (by norm_num) (one_le_blockLen A k) (depth_spec A k).1 x
  unfold blk floorC
  exact this

lemma lt_two_pow_aux (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; omega

lemma firstTrial_le_pow (A k : ℕ) : firstTrial A k ≤ 2 ^ (A * k + k + 24) := by
  induction k with
  | zero => simp [firstTrial]
  | succ k ih =>
    show firstTrial A k + nTrials A k ≤ _
    unfold nTrials aExp
    have h1 : 2 ^ (A * k + k + 24) ≤ 2 ^ (A * (k + 1) + k + 24) :=
      Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    have h2 : 2 ^ (A * (k + 1) + (k + 1) + 24) = 2 * 2 ^ (A * (k + 1) + k + 24) := by ring
    omega

lemma aExp_le_firstTrial (A k : ℕ) : aExp A k ≤ firstTrial A (k + 1) := by
  show aExp A k ≤ firstTrial A k + nTrials A k
  unfold nTrials
  have h1 := lt_two_pow_aux (aExp A k)
  have h2 : 2 ^ aExp A k ≤ 2 ^ (aExp A k + k + 24) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

lemma depth_le (A k : ℕ) : depth A k ≤ 6 * firstTrial A (k + 1) + 23 := by
  obtain ⟨S, hS⟩ : ∃ S, firstTrial A (k + 1) = S := ⟨_, rfl⟩
  have hL : blockLen A k = 8 * 21 ^ S := by rw [← hS]; rfl
  have ha := aExp_le_firstTrial A k
  rw [hS] at ha ⊢
  apply Nat.clog_le_of_le_pow
  rw [hL]
  have h21 : 21 ^ S ≤ 2 ^ (5 * S) := by rw [pow_mul]; exact Nat.pow_le_pow_left (by norm_num) S
  have h2a : 2 ^ aExp A k ≤ 2 ^ S := Nat.pow_le_pow_right (by norm_num) ha
  have e : 2 ^ (6 * S + 23) = 2 ^ 23 * (2 ^ (5 * S) * 2 ^ S) := by ring
  rw [e]
  have h3 : 21 ^ S * 2 ^ aExp A k ≤ 2 ^ (5 * S) * 2 ^ S := Nat.mul_le_mul h21 h2a
  have e2 : 640000 * (8 * 21 ^ S) * 2 ^ aExp A k = 5120000 * (21 ^ S * 2 ^ aExp A k) := by ring
  rw [e2]
  exact Nat.mul_le_mul (by norm_num) h3

lemma shift_le (A k : ℕ) : shift A k ≤ 2 ^ (6 * firstTrial A k + 10) := by
  induction k with
  | zero => simp [shift]
  | succ k ih =>
    show shift A k + blockLen A k * spacing A k + depth A k ≤ 2 ^ (6 * firstTrial A (k + 1) + 10)
    have hmono : firstTrial A k + 1 ≤ firstTrial A (k + 1) :=
      Nat.succ_le_of_lt (firstTrial_strictMono A (Nat.lt_succ_self k))
    have hd := depth_le A k
    obtain ⟨S, hS⟩ : ∃ S, firstTrial A (k + 1) = S := ⟨_, rfl⟩
    have hL : blockLen A k = 8 * 21 ^ S := by rw [← hS]; rfl
    rw [hS] at hd hmono ⊢
    have hL' : blockLen A k ≤ 2 ^ (5 * S + 3) := by
      rw [hL]
      have h21 : 21 ^ S ≤ 2 ^ (5 * S) := by rw [pow_mul]; exact Nat.pow_le_pow_left (by norm_num) S
      have : 2 ^ (5 * S + 3) = 8 * 2 ^ (5 * S) := by ring
      omega
    have hsp : spacing A k = depth A k + 2 := rfl
    have hlin : 12 * S + 48 ≤ 2 ^ (S + 6) := by
      have := lt_two_pow_aux S
      have : 2 ^ (S + 6) = 64 * 2 ^ S := by ring
      omega
    have hb1 := one_le_blockLen A k
    have h1 : blockLen A k * spacing A k + depth A k ≤ blockLen A k * (2 * depth A k + 2) := by
      rw [hsp]; nlinarith
    have h2 : blockLen A k * (2 * depth A k + 2) ≤ 2 ^ (5 * S + 3) * 2 ^ (S + 6) :=
      Nat.mul_le_mul hL' (by omega)
    have h3 : 2 ^ (6 * firstTrial A k + 10) ≤ 2 ^ (6 * S + 4) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have e1 : 2 ^ (6 * S + 10) = 64 * 2 ^ (6 * S + 4) := by ring
    have e2 : 2 ^ (5 * S + 3) * 2 ^ (S + 6) = 32 * 2 ^ (6 * S + 4) := by ring
    omega

lemma twoLogQ_le (A k : ℕ) : 2 * logQ A k ≤ 2 ^ (2 ^ ((A + 1) * (k + 1) + 30)) := by
  have h1 := shift_le A (k + 1)
  have h2 := firstTrial_le_pow A (k + 1)
  have hq : logQ A k = shift A (k + 1) + 2 := rfl
  have hM : A * (k + 1) + (k + 1) + 24 = (A + 1) * (k + 1) + 24 := by ring
  rw [hM] at h2
  have hpM : 2 ^ ((A + 1) * (k + 1) + 30) = 64 * 2 ^ ((A + 1) * (k + 1) + 24) := by ring
  have hpos : 0 < 2 ^ ((A + 1) * (k + 1) + 24) := by positivity
  have h3 : 6 * firstTrial A (k + 1) + 12 ≤ 2 ^ ((A + 1) * (k + 1) + 30) := by omega
  have h4 : 2 ^ (6 * firstTrial A (k + 1) + 12) ≤ 2 ^ (2 ^ ((A + 1) * (k + 1) + 30)) :=
    Nat.pow_le_pow_right (by norm_num) h3
  have h5 : 2 ^ (6 * firstTrial A (k + 1) + 12) = 4 * 2 ^ (6 * firstTrial A (k + 1) + 10) := by
    ring
  have h6 : 4 ≤ 2 ^ (6 * firstTrial A (k + 1) + 10) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- Endpoint scale control, upper half (Ho Lemma 5.1): `log log log (Q_k²) ≤ (A+1)(k+1) + 30`
where `Q_k = 2^{E_k}`. Proof: `S_{k+1} ≤ 2^{a_k+k+25}`, `d_k ≤ 6 S_{k+1} + 23`,
`E_k ≤ 2^{6 S_{k+1} + 11}`, then take three logarithms. -/
lemma scale_bound (A : ℕ) (hA : 1 ≤ A) (k : ℕ) :
    Real.log (Real.log (Real.log ((2 : ℝ) ^ (2 * logQ A k)))) ≤ ((A : ℝ) + 1) * (k + 1) + 30 := by
  have hn := twoLogQ_le A k
  have hq2 : 2 ≤ logQ A k := by show 2 ≤ shift A (k + 1) + 2; omega
  obtain ⟨T, hT⟩ : ∃ T, (A + 1) * (k + 1) + 30 = T := ⟨_, rfl⟩
  rw [hT] at hn
  obtain ⟨E, hE0⟩ : ∃ E, 2 * logQ A k = E := ⟨_, rfl⟩
  rw [hE0] at hn
  have hE4 : 4 ≤ E := by omega
  rw [hE0]
  have hlt := Real.log_two_lt_d9
  have hgt := Real.log_two_gt_d9
  have hx1 : Real.log ((2 : ℝ) ^ E) = (E : ℝ) * Real.log 2 := Real.log_pow _ _
  have hE : (E : ℝ) ≤ (2 : ℝ) ^ (2 ^ T) := by
    have := (Nat.cast_le (α := ℝ)).2 hn
    rw [Nat.cast_pow, Nat.cast_ofNat] at this
    exact this
  have hEge : (4 : ℝ) ≤ (E : ℝ) := by exact_mod_cast hE4
  have hx1pos : 1 < Real.log ((2 : ℝ) ^ E) := by
    rw [hx1]
    have := mul_le_mul_of_nonneg_right hEge (by linarith : (0 : ℝ) ≤ Real.log 2)
    linarith
  have hx1le : Real.log ((2 : ℝ) ^ E) ≤ (2 : ℝ) ^ (2 ^ T) := by
    rw [hx1]
    have : (E : ℝ) * Real.log 2 ≤ (E : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  have hx2pos : 0 < Real.log (Real.log ((2 : ℝ) ^ E)) := Real.log_pos hx1pos
  have hx2le : Real.log (Real.log ((2 : ℝ) ^ E)) ≤ (2 : ℝ) ^ T := by
    have h1 : Real.log (Real.log ((2 : ℝ) ^ E)) ≤ Real.log ((2 : ℝ) ^ (2 ^ T)) :=
      Real.log_le_log (by linarith) hx1le
    have h2 : Real.log ((2 : ℝ) ^ (2 ^ T)) = ((2 ^ T : ℕ) : ℝ) * Real.log 2 := Real.log_pow _ _
    have h3 : ((2 ^ T : ℕ) : ℝ) = (2 : ℝ) ^ T := by push_cast; rfl
    have h4 : (0 : ℝ) ≤ (2 : ℝ) ^ T := by positivity
    have h5 : (2 : ℝ) ^ T * Real.log 2 ≤ (2 : ℝ) ^ T * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) h4
    rw [h2, h3] at h1
    linarith
  have h1 : Real.log (Real.log (Real.log ((2 : ℝ) ^ E))) ≤ Real.log ((2 : ℝ) ^ T) :=
    Real.log_le_log hx2pos hx2le
  have h2 : Real.log ((2 : ℝ) ^ T) = (T : ℝ) * Real.log 2 := Real.log_pow _ _
  have h3 : (T : ℝ) = ((A : ℝ) + 1) * (k + 1) + 30 := by rw [← hT]; push_cast; ring
  have h4 : (T : ℝ) * Real.log 2 ≤ (T : ℝ) * 1 :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  rw [h2] at h1
  linarith

end Asm
end OMA.Port23

/- ### Sequence -/

/-!
Section: Assembly sub-lemma 2 (Sequence): the exponent sequence

Blueprint §3. Ho §4 (4.10)–(4.13) and the lacunarity part of Prop. 4.3.
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace OMA.Port23
namespace Asm


lemma trialOf_trial (s r : ℕ) (hr1 : 1 ≤ r) (hr2 : r ≤ trialLen s) :
    trialOf (21 ^ s + r - 2) = s := by
  unfold trialOf
  have h21 : 1 ≤ 21 ^ s := Nat.one_le_pow _ _ (by norm_num)
  unfold trialLen at hr2
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · omega
  · rw [pow_succ]; omega

/-- Every global index is the `r`-th exponent of some trial. -/
lemma exists_trial (j : ℕ) : ∃ s r, 1 ≤ r ∧ r ≤ trialLen s ∧ j = 21 ^ s + r - 2 := by
  have h1 := Nat.pow_log_le_self 21 (by omega : j + 1 ≠ 0)
  have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 21) (j + 1)
  rw [Nat.pow_succ] at h2
  refine ⟨Nat.log 21 (j + 1), j + 2 - 21 ^ Nat.log 21 (j + 1), ?_, ?_, ?_⟩
  · omega
  · unfold trialLen; omega
  · omega

/-- The `r`-th exponent of trial `s` sits at global index `21^s + r - 2`. -/
lemma mExp_trial (A s r : ℕ) (hr1 : 1 ≤ r) (hr2 : r ≤ trialLen s) :
    mExp A (21 ^ s + r - 2) = trialStart A s + r * spacing A (stage A s) := by
  unfold mExp
  rw [trialOf_trial s r hr1 hr2]
  have h21 : 1 ≤ 21 ^ s := Nat.one_le_pow _ _ (by norm_num)
  have : 21 ^ s + r - 2 + 2 - 21 ^ s = r := by omega
  rw [this]

lemma mExp_strictMono (A : ℕ) : StrictMono (mExp A) := by
  apply strictMono_nat_of_lt_succ
  intro j
  obtain ⟨s, r, h1, h2, rfl⟩ := exists_trial j
  have h21 : 1 ≤ 21 ^ s := Nat.one_le_pow _ _ (by norm_num)
  by_cases hr : r < trialLen s
  · have e : 21 ^ s + r - 2 + 1 = 21 ^ s + (r + 1) - 2 := by omega
    rw [e, mExp_trial A s (r + 1) (by omega) hr, mExp_trial A s r h1 h2, add_mul, one_mul]
    have : 0 < spacing A (stage A s) := by unfold spacing; omega
    omega
  · have hr' : r = trialLen s := by omega
    have e : 21 ^ s + r - 2 + 1 = 21 ^ (s + 1) + 1 - 2 := by
      rw [pow_succ]; unfold trialLen at hr'; omega
    have hlen : 1 ≤ trialLen (s + 1) := by
      unfold trialLen; have := Nat.one_le_pow (s + 1) 21 (by norm_num); omega
    rw [e, mExp_trial A (s + 1) 1 le_rfl hlen, mExp_trial A s r h1 h2, trialStart]
    have hL := trialLen_le A s
    have hm : r * spacing A (stage A s) ≤
        (blockLen A (stage A s) + 2) * spacing A (stage A s) :=
      Nat.mul_le_mul_right _ (by omega)
    have : 0 < spacing A (stage A (s + 1)) := by unfold spacing; omega
    omega

lemma isDyadicLacunary_nSeq (A : ℕ) : IsDyadicLacunary (nSeq A) := by
  refine ⟨Nat.one_le_pow _ _ (by norm_num), fun k => ?_⟩
  unfold nSeq
  have h := mExp_strictMono A (Nat.lt_succ_self k)
  calc 2 * 2 ^ mExp A k = 2 ^ (mExp A k + 1) := by ring
    _ ≤ 2 ^ mExp A (k + 1) := Nat.pow_le_pow_right (by norm_num) h

end Asm
end OMA.Port23

/- ### SpikeMeasure -/

/-!
Section: Assembly sub-lemma 3 (SpikeMeasure): measure-theoretic facts about spikes

Blueprint §4. Ho §2, (2.1) and Lemma 2.1(a): `|[0,2^{-d})| = 2^{-d}`, `∫ φ_d = 0`,
`∫ φ_d² = 1`, and `x ↦ n x` preserves Haar measure.
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace OMA.Port23
namespace Asm


lemma measurableSet_spikeSet (d : ℕ) : MeasurableSet (spikeSet d) := by
  have hb : (0 : ℝ) < (2 : ℝ)⁻¹ ^ d := by positivity
  unfold spikeSet
  rw [← Set.Ioo_insert_left hb, Set.image_insert_eq]
  exact ((QuotientAddGroup.isOpenMap_coe (N := AddSubgroup.zmultiples (1 : ℝ))) _
    isOpen_Ioo).measurableSet.insert _

/-- Haar measure on `(AddCircle (1 : ℝ))` computed on `[0,1)` in `ℝ`. -/
lemma haar_eq_volume_Ico (U : Set (AddCircle (1 : ℝ))) (hU : MeasurableSet U) :
    (haarAddCircle (T := 1)) U = volume (Set.Ico (0 : ℝ) 1 ∩ (((↑) : ℝ → (AddCircle (1 : ℝ))) ⁻¹' U)) := by
  have h1 : (volume : Measure (AddCircle (1 : ℝ))) = (haarAddCircle (T := 1)) := by
    rw [volume_eq_smul_haarAddCircle]; simp
  have h2 := AddCircle.add_projection_respects_measure (T := 1) 0 hU
  rw [← h1, h2, zero_add, Set.inter_comm]
  exact measure_congr ((Ico_ae_eq_Ioc (μ := (volume : Measure ℝ))).symm.inter (ae_eq_refl _))

lemma measure_spikeSet (d : ℕ) : (haarAddCircle (T := 1)) (spikeSet d) = (2⁻¹ : ℝ≥0∞) ^ d := by
  have ht1 : (2 : ℝ)⁻¹ ^ d ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  rw [haar_eq_volume_Ico _ (measurableSet_spikeSet d)]
  have hset : Set.Ico (0 : ℝ) 1 ∩ (((↑) : ℝ → (AddCircle (1 : ℝ))) ⁻¹' spikeSet d) =
      Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d) := by
    ext x
    constructor
    · rintro ⟨hx01, ⟨u, hu, hux⟩⟩
      have hx' : x ∈ Set.Ico (0 : ℝ) (0 + 1) := by rw [zero_add]; exact hx01
      have hu' : u ∈ Set.Ico (0 : ℝ) (0 + 1) := ⟨hu.1, by linarith [hu.2]⟩
      have e1 := AddCircle.equivIco_coe_of_mem hx'
      have e2 := AddCircle.equivIco_coe_of_mem hu'
      have hxu : x = u := by
        have : (AddCircle.equivIco 1 0 (x : (AddCircle (1 : ℝ))) : ℝ) = (AddCircle.equivIco 1 0 (u : (AddCircle (1 : ℝ))) : ℝ) := by
          rw [hux]
        rw [e1, e2] at this
        exact this
      rw [hxu]; exact hu
    · intro hx
      exact ⟨⟨hx.1, lt_of_lt_of_le hx.2 ht1⟩, ⟨x, hx, rfl⟩⟩
  rw [hset, Real.volume_Ico, sub_zero, ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_inv_of_pos (by norm_num)]
  simp

lemma spike_eq (d : ℕ) (x : (AddCircle (1 : ℝ))) :
    spike d x = ((spikeSet d).indicator 1 x - (2 : ℝ)⁻¹ ^ d) /
      Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) := rfl

lemma measurable_spike (d : ℕ) : Measurable (spike d) := by
  have : spike d = fun x => ((spikeSet d).indicator 1 x - (2 : ℝ)⁻¹ ^ d) /
      Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) := rfl
  rw [this]
  exact ((measurable_one.indicator (measurableSet_spikeSet d)).sub measurable_const).div_const _

lemma abs_spike_le (d : ℕ) (x : (AddCircle (1 : ℝ))) : |spike d x| ≤ 2 ^ d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [spike]
  rw [spike_eq]
  set t : ℝ := (2 : ℝ)⁻¹ ^ d with ht
  have ht0 : 0 < t := by positivity
  have hthalf : t ≤ 2⁻¹ := pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
  have hct : t ≤ Real.sqrt (t * (1 - t)) := by
    have := Real.abs_le_sqrt (x := t) (y := t * (1 - t)) (by nlinarith)
    rwa [abs_of_pos ht0] at this
  have hc : 0 < Real.sqrt (t * (1 - t)) := lt_of_lt_of_le ht0 hct
  have hnum : |(spikeSet d).indicator 1 x - t| ≤ 1 := by
    by_cases h : x ∈ spikeSet d
    · rw [Set.indicator_of_mem h]
      simp only [Pi.one_apply]
      rw [abs_le]; constructor <;> linarith
    · rw [Set.indicator_of_notMem h]
      rw [abs_le]; constructor <;> linarith
  rw [abs_div, abs_of_pos hc]
  calc |(spikeSet d).indicator 1 x - t| / Real.sqrt (t * (1 - t))
      ≤ 1 / Real.sqrt (t * (1 - t)) := div_le_div_of_nonneg_right hnum hc.le
    _ ≤ 1 / t := one_div_le_one_div_of_le ht0 hct
    _ = 2 ^ d := by rw [ht, one_div, inv_pow, inv_inv]

lemma measurableSet_hitSet (d v : ℕ) : MeasurableSet (hitSet d v) :=
  (continuous_nsmul (2 ^ v)).measurable (measurableSet_spikeSet d)

lemma measurePreserving_nsmul (n : ℕ) (hn : n ≠ 0) :
    MeasurePreserving (fun x : (AddCircle (1 : ℝ)) => n • x) (haarAddCircle (T := 1)) (haarAddCircle (T := 1)) := by
  have hmp : MeasurePreserving (fun x : (AddCircle (1 : ℝ)) => (n : ℤ) • x) (haarAddCircle (T := 1)) (haarAddCircle (T := 1)) :=
    Measure.measurePreserving_zsmul (haarAddCircle (T := 1)) (by exact_mod_cast hn)
  have e : (fun x : (AddCircle (1 : ℝ)) => n • x) = fun x => (n : ℤ) • x := by
    funext x; exact (natCast_zsmul x n).symm
  rw [e]; exact hmp

lemma measure_hitSet (d v : ℕ) : (haarAddCircle (T := 1)) (hitSet d v) = (2⁻¹ : ℝ≥0∞) ^ d := by
  have hmp := measurePreserving_nsmul (2 ^ v) (by positivity)
  have : hitSet d v = (fun x : (AddCircle (1 : ℝ)) => (2 ^ v : ℕ) • x) ⁻¹' spikeSet d := rfl
  rw [this, hmp.measure_preimage (measurableSet_spikeSet d).nullMeasurableSet]
  exact measure_spikeSet d

lemma integral_nsmul_comp (n : ℕ) (hn : n ≠ 0) (g : (AddCircle (1 : ℝ)) → ℝ) (hg : Measurable g) :
    ∫ x, g (n • x) ∂(haarAddCircle (T := 1)) = ∫ x, g x ∂(haarAddCircle (T := 1)) := by
  have hmp := measurePreserving_nsmul n hn
  rw [← integral_map hmp.measurable.aemeasurable
    (by rw [hmp.map_eq]; exact hg.aestronglyMeasurable), hmp.map_eq]

lemma integral_indicator_spikeSet (d : ℕ) :
    ∫ x, (spikeSet d).indicator (1 : (AddCircle (1 : ℝ)) → ℝ) x ∂(haarAddCircle (T := 1)) = (2 : ℝ)⁻¹ ^ d := by
  rw [integral_indicator_one (measurableSet_spikeSet d), measureReal_def, measure_spikeSet]
  simp

lemma integrable_indicator_spikeSet (d : ℕ) :
    Integrable (fun x => (spikeSet d).indicator (1 : (AddCircle (1 : ℝ)) → ℝ) x) (haarAddCircle (T := 1)) :=
  (integrable_const (1 : ℝ)).indicator (measurableSet_spikeSet d)

lemma integral_spike_nsmul (d n : ℕ) (hn : n ≠ 0) : ∫ x, spike d (n • x) ∂(haarAddCircle (T := 1)) = 0 := by
  rw [integral_nsmul_comp n hn _ (measurable_spike d)]
  simp only [spike_eq]
  rw [integral_div, integral_sub (integrable_indicator_spikeSet d) (integrable_const _),
    integral_indicator_spikeSet, integral_const]
  simp

lemma integral_spike_nsmul_sq (d n : ℕ) (hd : 1 ≤ d) (hn : n ≠ 0) :
    ∫ x, spike d (n • x) ^ 2 ∂(haarAddCircle (T := 1)) = 1 := by
  rw [integral_nsmul_comp n hn (fun y => spike d y ^ 2) ((measurable_spike d).pow_const 2)]
  set t : ℝ := (2 : ℝ)⁻¹ ^ d with ht
  have ht0 : 0 < t := by positivity
  have hthalf : t ≤ 2⁻¹ := pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
  have hpos : 0 < t * (1 - t) := mul_pos ht0 (by linarith)
  have hpt : ∀ x : (AddCircle (1 : ℝ)), spike d x ^ 2 =
      ((spikeSet d).indicator (1 : (AddCircle (1 : ℝ)) → ℝ) x * (1 - 2 * t) + t ^ 2) / (t * (1 - t)) := by
    intro x
    rw [spike_eq, div_pow, Real.sq_sqrt hpos.le]
    congr 1
    by_cases h : x ∈ spikeSet d
    · rw [Set.indicator_of_mem h]; simp only [Pi.one_apply]; ring
    · rw [Set.indicator_of_notMem h]; ring
  simp only [hpt]
  rw [integral_div, integral_add ((integrable_indicator_spikeSet d).mul_const _)
    (integrable_const _), integral_mul_const, integral_indicator_spikeSet, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  rw [div_eq_one_iff_eq hpos.ne']
  ring

end Asm
end OMA.Port23

/- ### HitWindow -/

/-!
Section: Assembly sub-lemma 4 (HitWindow): spike events are digit-window events

Blueprint §4. Ho, proof of Lemma 2.1: `φ_d(2^v x)` depends only on the binary digits
`v+1, …, v+d` of `x` (digit `j` in the convention of `DeterminedByWindow` is
`fract(2^j x) < 1/2`, for `v ≤ j < v + d`).
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace OMA.Port23
namespace Asm


/-- `z ↦ z mod 1` lands in `[0, c)` iff the fractional part of `z` is below `c`. -/
lemma coe_mem_image_Ico_iff (z c : ℝ) (hc : c ≤ 1) :
    ((z : (AddCircle (1 : ℝ))) ∈ (QuotientAddGroup.mk '' Set.Ico (0 : ℝ) c : Set (AddCircle (1 : ℝ)))) ↔ Int.fract z < c := by
  constructor
  · rintro ⟨w, hw, h⟩
    have h1 : ((w : ℝ) : (AddCircle (1 : ℝ))) = ((Int.fract z : ℝ) : (AddCircle (1 : ℝ))) := by
      rw [AddCircle.coe_fract]; exact h
    have hw' : w ∈ Set.Ico (0 : ℝ) (0 + 1) := ⟨hw.1, by linarith [hw.2]⟩
    have hf' : Int.fract z ∈ Set.Ico (0 : ℝ) (0 + 1) :=
      ⟨Int.fract_nonneg z, by simpa using Int.fract_lt_one z⟩
    have := (AddCircle.coe_eq_coe_iff_of_mem_Ico hw' hf').1 h1
    rw [← this]; exact hw.2
  · intro h
    exact ⟨Int.fract z, ⟨Int.fract_nonneg z, h⟩, AddCircle.coe_fract z⟩

lemma fract_lt_two_inv_pow_succ (z : ℝ) (d : ℕ) :
    Int.fract z < (2 : ℝ)⁻¹ ^ (d + 1) ↔
      Int.fract z < 2⁻¹ ∧ Int.fract (2 * z) < (2 : ℝ)⁻¹ ^ d := by
  have hpow : (2 : ℝ)⁻¹ ^ (d + 1) = 2⁻¹ * (2 : ℝ)⁻¹ ^ d := by rw [pow_succ]; ring
  have hle : (2 : ℝ)⁻¹ ^ d ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hpos : (0 : ℝ) < (2 : ℝ)⁻¹ ^ d := by positivity
  by_cases hf : Int.fract z < 2⁻¹
  · have h2 : Int.fract (2 * z) = 2 * Int.fract z := by
      rw [Int.fract_eq_iff]
      refine ⟨by linarith [Int.fract_nonneg z], by linarith, 2 * ⌊z⌋, ?_⟩
      rw [Int.fract]; push_cast; ring
    rw [h2, hpow]
    constructor
    · intro h; exact ⟨hf, by linarith⟩
    · rintro ⟨-, h⟩; linarith
  · constructor
    · intro h; exfalso; apply hf; rw [hpow] at h; nlinarith
    · rintro ⟨h, -⟩; exact absurd h hf

/-- `fract z < 2^{-d}` iff the first `d` binary digits of `z` vanish. -/
lemma fract_lt_two_inv_pow_iff (d : ℕ) : ∀ z : ℝ,
    Int.fract z < (2 : ℝ)⁻¹ ^ d ↔ ∀ i < d, Int.fract ((2 : ℝ) ^ i * z) < 2⁻¹ := by
  induction d with
  | zero =>
    intro z
    simp only [pow_zero, Nat.not_lt_zero, false_imp_iff, implies_true, iff_true]
    exact Int.fract_lt_one z
  | succ d ih =>
    intro z
    rw [fract_lt_two_inv_pow_succ, ih (2 * z)]
    constructor
    · rintro ⟨h0, h⟩ i hi
      rcases i with _ | i
      · simpa using h0
      · have := h i (by omega)
        rw [pow_succ, mul_assoc]; exact this
    · intro h
      refine ⟨by simpa using h 0 (by omega), fun i hi => ?_⟩
      have := h (i + 1) (by omega)
      rw [pow_succ, mul_assoc] at this; exact this

lemma mem_hitSet_iff (d v : ℕ) (x : (AddCircle (1 : ℝ))) :
    x ∈ hitSet d v ↔ ∀ j, v ≤ j → j < v + d →
      Int.fract ((2 : ℝ) ^ j * (AddCircle.equivIco 1 0 x : ℝ)) < 2⁻¹ := by
  set y : ℝ := (AddCircle.equivIco 1 0 x : ℝ)
  have hx : ((y : ℝ) : (AddCircle (1 : ℝ))) = x := AddCircle.coe_equivIco
  have hsmul : (2 ^ v : ℕ) • x = (((2 : ℝ) ^ v * y : ℝ) : (AddCircle (1 : ℝ))) := by
    rw [← hx, ← AddCircle.coe_nsmul, nsmul_eq_mul]; push_cast; rfl
  simp only [hitSet, spikeSet, Set.mem_ofPred_eq]
  rw [hsmul, coe_mem_image_Ico_iff _ _ (pow_le_one₀ (by norm_num) (by norm_num)),
    fract_lt_two_inv_pow_iff]
  constructor
  · intro h j hj1 hj2
    have := h (j - v) (by omega)
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hj1] at this
    exact this
  · intro h i hi
    rw [← mul_assoc, ← pow_add]
    exact h (i + v) (by omega) (by omega)

lemma determinedByWindow_hitSet (d v : ℕ) : DeterminedByWindow v (v + d) (hitSet d v) := by
  intro x y h
  rw [mem_hitSet_iff, mem_hitSet_iff]
  constructor
  · intro hx j hj1 hj2; exact (h j).1 (fun _ _ => hx j hj1 hj2)
  · intro hy j hj1 hj2; exact (h j).2 (hy j hj1 hj2) hj1 hj2

lemma DeterminedByWindow.compl' {a b : ℕ} {E : Set (AddCircle (1 : ℝ))} (h : DeterminedByWindow a b E) :
    DeterminedByWindow a b Eᶜ := by
  intro x y hxy
  exact not_congr (h x y hxy)

end Asm
end OMA.Port23

/- ### StageProb -/

/-!
Section: Assembly sub-lemma 5 (StageProb): each stage succeeds with high probability

Blueprint §5. Ho Lemma 3.7 (probability of a good trial) and Lemma 4.2 (independence, stage
failure `≤ exp(-c₀ T_k λ_k / B²)`), simplified: `(S_k)ᶜ` is the intersection over all pairs
(trial `s` of stage `k`, central layer `h`) of the miss events, all with disjoint digit windows,
so `μ((S_k)ᶜ) = (1 - 2^{-d_k})^{n_k}` with `n_k ≥ 7 T_k L_k / 8`, and `n_k 2^{-d_k} ≥ 2^{k+3}`.
Then a union bound gives `μ(⋂ S_k) ≥ 1 - ∑ 2^{-(k+3)} = 3/4`.
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace OMA.Port23
namespace Asm


/-- Elementary bound `(1 - r)^n ≤ 2^{-m}` from `n r ≥ 2^m` (via `(1-r)^n (1+r)^n ≤ 1` and
Bernoulli). -/
lemma one_sub_pow_le_aux (r : ℝ) (n m : ℕ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hn : (2 : ℝ) ^ m ≤ n * r) : (1 - r) ^ n ≤ (2⁻¹ : ℝ) ^ m := by
  have hb := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ r) n
  have h1 : (2 : ℝ) ^ m ≤ (1 + r) ^ n := by linarith
  have h2 : (1 - r) ^ n * (1 + r) ^ n ≤ 1 := by
    rw [← mul_pow]; exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have h3 : 0 ≤ (1 - r) ^ n := pow_nonneg (by linarith) n
  have h4 : (1 - r) ^ n * 2 ^ m ≤ 1 := le_trans (mul_le_mul_of_nonneg_left h1 h3) h2
  rw [inv_pow, ← one_div, le_div_iff₀ (by positivity)]
  exact h4

lemma ennreal_inv_two_pow (m : ℕ) :
    ((2⁻¹ : ℝ≥0∞)) ^ m = ENNReal.ofReal ((2⁻¹ : ℝ) ^ m) := by
  rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
  simp

/-- The (trial, central layer) pairs of stage `k`. -/
def stagePairs (A k : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.Ico (firstTrial A k) (firstTrial A (k + 1))).sigma
    (fun s => Finset.Icc (trialLen s + 1) (blockLen A k + 1))

/-- Start of the digit window of the pair `i = (s, h)`. -/
def pairStart (A k : ℕ) (i : Σ _ : ℕ, ℕ) : ℕ :=
  shift A k + trialStart A i.1 + i.2 * spacing A k

lemma stage_of_mem_Ico {A k s : ℕ} (hs : s ∈ Finset.Ico (firstTrial A k) (firstTrial A (k + 1))) :
    stage A s = k := by
  rw [Finset.mem_Ico] at hs
  exact stage_eq A s k hs.1 hs.2

lemma compl_stageGood_eq (A k : ℕ) :
    (stageGood A k)ᶜ = ⋂ i ∈ stagePairs A k, (hitSet (depth A k) (pairStart A k i))ᶜ := by
  ext x
  simp only [Set.mem_compl_iff, stageGood, Set.mem_iInter]
  constructor
  · intro h i hi hx
    rw [stagePairs, Finset.mem_sigma] at hi
    apply h
    refine Set.mem_iUnion₂.mpr ⟨i.1, hi.1, ?_⟩
    rw [goodSet, stage_of_mem_Ico hi.1]
    exact Set.mem_iUnion₂.mpr ⟨i.2, hi.2, hx⟩
  · intro h hx
    obtain ⟨s, hs, hx⟩ := Set.mem_iUnion₂.mp hx
    rw [goodSet, stage_of_mem_Ico hs] at hx
    obtain ⟨hh, hhm, hx⟩ := Set.mem_iUnion₂.mp hx
    exact h ⟨s, hh⟩ (by rw [stagePairs, Finset.mem_sigma]; exact ⟨hs, hhm⟩) hx

lemma pairStart_lt_of_lt (A k : ℕ) {s h s' h' : ℕ}
    (hs : s ∈ Finset.Ico (firstTrial A k) (firstTrial A (k + 1)))
    (hh : h ≤ blockLen A k + 1) (hss' : s < s') :
    pairStart A k ⟨s, h⟩ + depth A k ≤ pairStart A k ⟨s', h'⟩ := by
  have hM : trialStart A (s + 1) = trialStart A s + (blockLen A k + 2) * spacing A k := by
    show trialStart A s + (blockLen A (stage A s) + 2) * spacing A (stage A s) = _
    rw [stage_of_mem_Ico hs]
  have hmono : trialStart A (s + 1) ≤ trialStart A s' := trialStart_mono A hss'
  have e1 : h * spacing A k ≤ (blockLen A k + 1) * spacing A k := Nat.mul_le_mul_right _ hh
  have e2 : (blockLen A k + 2) * spacing A k = (blockLen A k + 1) * spacing A k + spacing A k := by
    ring
  have hD : spacing A k = depth A k + 2 := rfl
  simp only [pairStart]
  omega

lemma pairStart_disj (A k : ℕ) :
    ∀ i ∈ stagePairs A k, ∀ j ∈ stagePairs A k, i ≠ j →
      pairStart A k i + depth A k ≤ pairStart A k j ∨
        pairStart A k j + depth A k ≤ pairStart A k i := by
  intro i hi j hj hij
  rcases i with ⟨s, h⟩
  rcases j with ⟨s', h'⟩
  rw [stagePairs, Finset.mem_sigma, Finset.mem_Icc] at hi hj
  rcases lt_trichotomy s s' with hlt | heq | hgt
  · left; exact pairStart_lt_of_lt A k hi.1 hi.2.2 hlt
  · subst heq
    have hne : h ≠ h' := by
      intro e; subst e; exact hij rfl
    have hD : spacing A k = depth A k + 2 := rfl
    simp only [pairStart]
    rcases lt_or_gt_of_ne hne with hl | hl
    · left
      have : (h + 1) * spacing A k ≤ h' * spacing A k := Nat.mul_le_mul_right _ hl
      have e2 : (h + 1) * spacing A k = h * spacing A k + spacing A k := by ring
      omega
    · right
      have : (h' + 1) * spacing A k ≤ h * spacing A k := Nat.mul_le_mul_right _ hl
      have e2 : (h' + 1) * spacing A k = h' * spacing A k + spacing A k := by ring
      omega
  · right; exact pairStart_lt_of_lt A k hj.1 hj.2.2 hgt

lemma card_stagePairs (A k : ℕ) :
    7 * nTrials A k * blockLen A k ≤ 8 * (stagePairs A k).card := by
  have hS : firstTrial A (k + 1) = firstTrial A k + nTrials A k := rfl
  rw [stagePairs, Finset.card_sigma, Finset.mul_sum]
  calc 7 * nTrials A k * blockLen A k
      = ∑ _s ∈ Finset.Ico (firstTrial A k) (firstTrial A (k + 1)), 7 * blockLen A k := by
        rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul, hS, Nat.add_sub_cancel_left]; ring
    _ ≤ _ := by
        apply Finset.sum_le_sum
        intro s hs
        rw [Nat.card_Icc]
        have := trialLen_le A s
        rw [stage_of_mem_Ico hs] at this
        omega

lemma real_count_aux (n L P Λ K : ℝ) (hcard : 7 * (Λ * K * 16777216) * L ≤ 8 * n)
    (hspec : P < 128 * 100 ^ 2 * L * Λ) (hK : 0 < K) (hL : 0 ≤ L) (hΛ : 0 ≤ Λ) :
    K * 2 ^ 3 * P ≤ n := by
  have hk := mul_lt_mul_of_pos_left hspec hK
  have hmono : 0 ≤ K * (L * Λ) := mul_nonneg hK.le (mul_nonneg hL hΛ)
  nlinarith

lemma stage_count_real (A k : ℕ) :
    (2 : ℝ) ^ (k + 3) ≤ ((stagePairs A k).card : ℝ) * (2⁻¹ : ℝ) ^ depth A k := by
  have hspec := (depth_spec A k).2
  have hlam : lam A k = ((2 : ℝ) ^ aExp A k)⁻¹ := by simp [lam, inv_pow]
  rw [hlam, div_inv_eq_mul] at hspec
  have hcardR : 7 * (nTrials A k : ℝ) * (blockLen A k : ℝ) ≤ 8 * ((stagePairs A k).card : ℝ) := by
    exact_mod_cast card_stagePairs A k
  have hT : (nTrials A k : ℝ) = 2 ^ aExp A k * 2 ^ k * 16777216 := by
    simp only [nTrials]; push_cast; rw [pow_add, pow_add]; norm_num
  rw [hT] at hcardR
  rw [inv_pow, le_mul_inv_iff₀ (by positivity), pow_add]
  exact real_count_aux _ _ _ _ _ hcardR hspec (by positivity) (Nat.cast_nonneg _) (by positivity)

lemma measure_compl_stageGood_le (A : ℕ) (hA : 1 ≤ A) (k : ℕ) :
    (haarAddCircle (T := 1)) (stageGood A k)ᶜ ≤ (2⁻¹ : ℝ≥0∞) ^ (k + 3) := by
  classical
  have hmeasI : (haarAddCircle (T := 1)) (⋂ i ∈ stagePairs A k, (hitSet (depth A k) (pairStart A k i))ᶜ) =
      ∏ i ∈ stagePairs A k, (haarAddCircle (T := 1)) (hitSet (depth A k) (pairStart A k i))ᶜ :=
    measure_iInter_of_disjoint_windows (stagePairs A k) (pairStart A k)
      (fun i => pairStart A k i + depth A k) (fun i => (hitSet (depth A k) (pairStart A k i))ᶜ)
      (fun i _ => DeterminedByWindow.compl' (determinedByWindow_hitSet _ _))
      (fun i _ => (measurableSet_hitSet _ _).compl) (pairStart_disj A k)
  have hEi : ∀ i, (haarAddCircle (T := 1)) (hitSet (depth A k) (pairStart A k i))ᶜ = 1 - (2⁻¹ : ℝ≥0∞) ^ depth A k := by
    intro i
    rw [measure_compl (measurableSet_hitSet _ _) (measure_ne_top _ _), measure_univ,
      measure_hitSet]
  have hr1 : (2⁻¹ : ℝ) ^ depth A k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hr0 : (0 : ℝ) ≤ (2⁻¹ : ℝ) ^ depth A k := by positivity
  have hfin := one_sub_pow_le_aux _ (stagePairs A k).card (k + 3) hr0 hr1 (stage_count_real A k)
  rw [compl_stageGood_eq, hmeasI, Finset.prod_congr rfl (fun i _ => hEi i), Finset.prod_const,
    ennreal_inv_two_pow, ennreal_inv_two_pow, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub _ hr0, ← ENNReal.ofReal_pow (by linarith)]
  exact ENNReal.ofReal_le_ofReal hfin

lemma measure_iInter_stageGood_pos (A : ℕ) (hA : 1 ≤ A) :
    0 < (haarAddCircle (T := 1)) (⋂ k, stageGood A k) := by
  set G := ⋂ k, stageGood A k
  have hsum : ∑' k : ℕ, (2⁻¹ : ℝ≥0∞) ^ (k + 3) = (2⁻¹ : ℝ≥0∞) ^ 2 := by
    calc ∑' k : ℕ, (2⁻¹ : ℝ≥0∞) ^ (k + 3) = ∑' k : ℕ, (2⁻¹ : ℝ≥0∞) ^ 3 * (2⁻¹ : ℝ≥0∞) ^ k :=
          tsum_congr fun k => by ring
      _ = (2⁻¹ : ℝ≥0∞) ^ 3 * (1 - 2⁻¹)⁻¹ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      _ = (2⁻¹ : ℝ≥0∞) ^ 2 := by
          rw [ENNReal.one_sub_inv_two, inv_inv, pow_succ, mul_assoc,
            ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
  have hc : (haarAddCircle (T := 1)) Gᶜ ≤ (2⁻¹ : ℝ≥0∞) ^ 2 := by
    rw [Set.compl_iInter]
    calc _ ≤ ∑' k, (haarAddCircle (T := 1)) (stageGood A k)ᶜ := measure_iUnion_le _
      _ ≤ ∑' k : ℕ, (2⁻¹ : ℝ≥0∞) ^ (k + 3) :=
          ENNReal.tsum_le_tsum fun k => measure_compl_stageGood_le A hA k
      _ = _ := hsum
  have h1 : (1 : ℝ≥0∞) ≤ (haarAddCircle (T := 1)) G + (2⁻¹ : ℝ≥0∞) ^ 2 := by
    calc (1 : ℝ≥0∞) = (haarAddCircle (T := 1)) (G ∪ Gᶜ) := by rw [Set.union_compl_self, measure_univ]
      _ ≤ (haarAddCircle (T := 1)) G + (haarAddCircle (T := 1)) Gᶜ := measure_union_le _ _
      _ ≤ _ := by gcongr
  rw [pos_iff_ne_zero]
  intro h0
  rw [h0, zero_add] at h1
  have h2 : (2⁻¹ : ℝ≥0∞) ^ 2 ≤ 2⁻¹ :=
    pow_le_of_le_one (by simp) (ENNReal.inv_le_one.2 ENNReal.one_lt_two.le) (by norm_num)
  have h3 : (2⁻¹ : ℝ≥0∞) < 1 := ENNReal.inv_lt_one.2 ENNReal.one_lt_two
  exact absurd (h1.trans h2) (not_le.mpr h3)

end Asm
end OMA.Port23

/- ### Atoms -/

/-!
Section: Assembly sub-lemma 6 (Atoms): Fourier decomposition of the blocks into atoms

Blueprint §7. Ho Lemma 3.1 proof and (4.8): the atom `φ_{d_k}(2^{U_k+qD_k} ·)` has Fourier
support in the valuation band `[U_k + q D_k, U_k + q D_k + d_k)`; these bands are pairwise
disjoint over all `(k, q)` with `1 ≤ q ≤ L_k`, and every atom has mean zero.
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace OMA.Port23
namespace Asm


/-! ### Auxiliary lemmas (self-contained; they only use fully proved results of
`Parts/SpikeFourierSupport.lean`). -/

lemma alt_shift_mono (A : ℕ) : Monotone (shift A) := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  show shift A n ≤ shift A n + blockLen A n * spacing A n + depth A n
  exact le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)

/-- Bands of different stages are separated. -/
lemma alt_band_sep (A k k' q q' : ℕ) (hk : k < k') (hq : q ≤ blockLen A k) :
    shift A k + q * spacing A k + depth A k ≤ shift A k' + q' * spacing A k' := by
  have h1 : shift A (k + 1) ≤ shift A k' := alt_shift_mono A (by omega)
  have h2 : shift A (k + 1) = shift A k + blockLen A k * spacing A k + depth A k := rfl
  have h3 : q * spacing A k ≤ blockLen A k * spacing A k := Nat.mul_le_mul_right _ hq
  generalize q * spacing A k = a at *
  generalize blockLen A k * spacing A k = b at *
  generalize q' * spacing A k' = c at *
  omega

/-- Bands of the same stage are separated. -/
lemma alt_band_sep_same (A k q q' : ℕ) (hq : q < q') :
    shift A k + q * spacing A k + depth A k ≤ shift A k + q' * spacing A k := by
  have h1 : (q + 1) * spacing A k ≤ q' * spacing A k := Nat.mul_le_mul_right _ hq
  have h2 : (q + 1) * spacing A k = q * spacing A k + (depth A k + 2) := by
    rw [add_mul, one_mul]; rfl
  generalize q * spacing A k = a at *
  generalize q' * spacing A k = c at *
  omega

lemma alt_integrable_spike (d : ℕ) : Integrable (fun y : (AddCircle (1 : ℝ)) => (spike d y : ℂ)) (haarAddCircle (T := 1)) := by
  have h : Integrable (spike d) (haarAddCircle (T := 1)) := by
    unfold spike
    exact (((integrable_const (1 : ℝ)).indicator (OMA.Port23.measurableSet_spikeSet d)).sub
      (integrable_const _)).div_const _
  exact h.ofReal

lemma alt_integrable_atom (A k q : ℕ) : Integrable (fun x : (AddCircle (1 : ℝ)) => (atom A k q x : ℂ)) (haarAddCircle (T := 1)) := by
  have hn : ((2 ^ (shift A k + q * spacing A k) : ℕ) : ℤ) ≠ 0 := by positivity
  have hmp : MeasurePreserving (fun x : (AddCircle (1 : ℝ)) => ((2 ^ (shift A k + q * spacing A k) : ℕ) : ℤ) • x)
      (haarAddCircle (T := 1)) (haarAddCircle (T := 1)) := Measure.measurePreserving_zsmul (haarAddCircle (T := 1)) hn
  have e : (fun x : (AddCircle (1 : ℝ)) => (atom A k q x : ℂ)) = (fun y : (AddCircle (1 : ℝ)) => (spike (depth A k) y : ℂ)) ∘
      (fun x : (AddCircle (1 : ℝ)) => ((2 ^ (shift A k + q * spacing A k) : ℕ) : ℤ) • x) := by
    funext x
    simp only [Function.comp, atom, natCast_zsmul]
  rw [e]
  exact Integrable.comp_measurable (by rw [hmp.map_eq]; exact alt_integrable_spike _)
    hmp.measurable

lemma alt_fourierCoeff_spike_zero (d : ℕ) :
    fourierCoeff (fun x : (AddCircle (1 : ℝ)) => (spike d x : ℂ)) 0 = 0 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have : (fun x : (AddCircle (1 : ℝ)) => (spike 0 x : ℂ)) = fun _ => 0 := by
      funext x; simp [spike]
    rw [this]; simp [fourierCoeff]
  have hb0 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ d := by positivity
  have hb1 : (2 : ℝ)⁻¹ ^ d < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hpt : ∀ x ∈ Set.uIoc ((2 : ℝ)⁻¹ ^ d - 1) ((2 : ℝ)⁻¹ ^ d),
      fourier (-(0 : ℤ)) (x : (AddCircle (1 : ℝ))) • (spike d (x : (AddCircle (1 : ℝ))) : ℂ) =
        (1 / ((Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) : ℝ) : ℂ)) *
            (Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d)).indicator (fun _ : ℝ => (1 : ℂ)) x -
          ((((2 : ℝ)⁻¹ ^ d : ℝ) : ℂ) /
              ((Real.sqrt ((2 : ℝ)⁻¹ ^ d * (1 - (2 : ℝ)⁻¹ ^ d)) : ℝ) : ℂ)) := by
    intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    have hmem := mem_spikeSet_iff d hd x hx
    rw [neg_zero, fourier_zero, one_smul]
    unfold spike
    by_cases hxI : x ∈ Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d)
    · rw [Set.indicator_of_mem (hmem.mpr hxI), Set.indicator_of_mem hxI, Pi.one_apply]
      push_cast; ring
    · rw [Set.indicator_of_notMem (fun h => hxI (hmem.mp h)), Set.indicator_of_notMem hxI]
      push_cast; ring
  have hcont : Continuous (fun _ : ℝ => (1 : ℂ)) := continuous_const
  have hle : (2 : ℝ)⁻¹ ^ d - 1 ≤ (2 : ℝ)⁻¹ ^ d := by linarith
  have hind : IntervalIntegrable
      ((Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d)).indicator (fun _ : ℝ => (1 : ℂ))) volume
      ((2 : ℝ)⁻¹ ^ d - 1) ((2 : ℝ)⁻¹ ^ d) :=
    intervalIntegrable_iff.mpr
      ((intervalIntegrable_iff.mp (hcont.intervalIntegrable _ _)).indicator measurableSet_Ico)
  have hsub : Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d) ⊆ Set.Ioc ((2 : ℝ)⁻¹ ^ d - 1) ((2 : ℝ)⁻¹ ^ d) :=
    fun y hy => ⟨by linarith [hy.1, hb1], hy.2.le⟩
  have hI1 : ∫ x in ((2 : ℝ)⁻¹ ^ d - 1)..((2 : ℝ)⁻¹ ^ d),
      (Set.Ico (0 : ℝ) ((2 : ℝ)⁻¹ ^ d)).indicator (fun _ : ℝ => (1 : ℂ)) x =
      ∫ x in (0 : ℝ)..((2 : ℝ)⁻¹ ^ d), (1 : ℂ) := by
    rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hb0.le,
      setIntegral_indicator measurableSet_Ico, Set.inter_eq_right.mpr hsub,
      integral_Ico_eq_integral_Ioc]
  rw [fourierCoeff_eq_intervalIntegral _ _ ((2 : ℝ)⁻¹ ^ d - 1), sub_add_cancel,
    intervalIntegral.integral_congr_ae (ae_of_all _ hpt),
    intervalIntegral.integral_sub (hind.const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, hI1, intervalIntegral.integral_const,
    intervalIntegral.integral_const]
  simp only [sub_zero, sub_sub_cancel, one_div, one_smul, inv_one]
  rw [Complex.real_smul]
  push_cast
  ring

/-! ### Main statements -/

lemma blk_eq_sum_atom (A k : ℕ) (x : (AddCircle (1 : ℝ))) :
    blk A k x = Real.sqrt (lam A k / blockLen A k) *
      ∑ q ∈ Finset.Icc 1 (blockLen A k), atom A k q x := by
  rfl

lemma fourierCoeff_blk (A k : ℕ) (r : ℤ) :
    fourierCoeff (fun x => (blk A k x : ℂ)) r =
      (Real.sqrt (lam A k / blockLen A k) : ℂ) *
        ∑ q ∈ Finset.Icc 1 (blockLen A k), fourierCoeff (fun x => (atom A k q x : ℂ)) r := by
  have hfun : (fun x => (blk A k x : ℂ)) = fun x => (Real.sqrt (lam A k / blockLen A k) : ℂ) *
      (∑ q ∈ Finset.Icc 1 (blockLen A k), fun x : (AddCircle (1 : ℝ)) => (atom A k q x : ℂ)) x := by
    funext x
    rw [blk_eq_sum_atom, Finset.sum_apply]
    push_cast
    rfl
  rw [hfun, fourierCoeff.const_mul,
    fourierCoeff.sum _ _ (fun q _ => alt_integrable_atom A k q), Finset.sum_apply]

lemma fourierCoeff_atom_zero (A k q : ℕ) : fourierCoeff (fun x => (atom A k q x : ℂ)) 0 = 0 := by
  have hmeas : AEStronglyMeasurable (fun y : (AddCircle (1 : ℝ)) => (spike (depth A k) y : ℂ)) (haarAddCircle (T := 1)) :=
    (Complex.measurable_ofReal.comp (OMA.Port23.measurable_spike _)).aestronglyMeasurable
  have h := fourierCoeff_nsmul_comp_mul (2 ^ (shift A k + q * spacing A k)) (by positivity)
    (fun y : (AddCircle (1 : ℝ)) => (spike (depth A k) y : ℂ)) hmeas 0
  rw [mul_zero] at h
  exact h.trans (alt_fourierCoeff_spike_zero _)

/-- Distinct atoms have disjoint Fourier supports. -/
lemma fourierCoeff_atom_disjoint (A k q k' q' : ℕ) (r : ℤ)
    (hq : q ∈ Finset.Icc 1 (blockLen A k)) (hq' : q' ∈ Finset.Icc 1 (blockLen A k'))
    (hne : (k, q) ≠ (k', q')) :
    fourierCoeff (fun x => (atom A k q x : ℂ)) r = 0 ∨
      fourierCoeff (fun x => (atom A k' q' x : ℂ)) r = 0 := by
  by_cases hr : r = 0
  · subst hr; left; exact fourierCoeff_atom_zero A k q
  by_contra hcon
  obtain ⟨h1, h2⟩ := not_or.mp hcon
  have e1 : (2 : ℤ) ^ (shift A k + q * spacing A k) ∣ r ∧
      ¬ (2 : ℤ) ^ (shift A k + q * spacing A k + depth A k) ∣ r := by
    by_contra h
    exact h1 (fourierCoeff_spike_dilate_eq_zero _ _ r hr h)
  have e2 : (2 : ℤ) ^ (shift A k' + q' * spacing A k') ∣ r ∧
      ¬ (2 : ℤ) ^ (shift A k' + q' * spacing A k' + depth A k') ∣ r := by
    by_contra h
    exact h2 (fourierCoeff_spike_dilate_eq_zero _ _ r hr h)
  rw [Finset.mem_Icc] at hq hq'
  have sep : shift A k + q * spacing A k + depth A k ≤ shift A k' + q' * spacing A k' ∨
      shift A k' + q' * spacing A k' + depth A k' ≤ shift A k + q * spacing A k := by
    rcases lt_trichotomy k k' with hk | rfl | hk
    · exact Or.inl (alt_band_sep A k k' q q' hk hq.2)
    · have hqq : q ≠ q' := fun h => hne (by rw [h])
      rcases lt_or_gt_of_ne hqq with h | h
      · exact Or.inl (alt_band_sep_same A k q q' h)
      · exact Or.inr (alt_band_sep_same A k q' q h)
    · exact Or.inr (alt_band_sep A k' k q' q hk hq'.2)
  rcases sep with h | h
  · exact e1.2 (dvd_trans (pow_dvd_pow 2 h) e2.1)
  · exact e2.2 (dvd_trans (pow_dvd_pow 2 h) e1.1)

end Asm
end OMA.Port23

/- ### PartialSumL2 -/

/-!
Section: Assembly sub-lemma 7 (PartialSumL2): `L²` norm of the partial sums

Blueprint §7. Ho Lemma 3.1 (3.3) and Prop. 4.3 (orthogonality of the blocks):
`‖∑_{k<K} F_k‖₂² = ∑_{k<K} λ_k ≤ 1`, via Parseval (`tsum_sq_fourierCoeff`), the disjoint
Fourier supports of the atoms (`fourierCoeff_atom_disjoint`), and `‖atom‖₂ = 1`
(`integral_spike_nsmul_sq`).
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace OMA.Port23
namespace Asm


private lemma measurable_atom' (A k q : ℕ) : Measurable (atom A k q) :=
  (OMA.Port23.measurable_spike _).comp (continuous_nsmul _).measurable

private lemma memLp_atomC (A k q : ℕ) : MemLp (fun x => (atom A k q x : ℂ)) 2 (haarAddCircle (T := 1)) :=
  MemLp.of_bound ((Complex.measurable_ofReal.comp (measurable_atom' A k q)).aestronglyMeasurable)
    (2 ^ depth A k)
    (Eventually.of_forall fun x => by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_spike_le _ _)

/-- The atom as an element of `L²((AddCircle (1 : ℝ)); ℂ)`. -/
private noncomputable def aLp (A k q : ℕ) : Lp ℂ 2 (haarAddCircle (T := 1)) := (memLp_atomC A k q).toLp _

private lemma coeFn_aLp (A k q : ℕ) : ⇑(aLp A k q) =ᵐ[(haarAddCircle (T := 1))] fun x => (atom A k q x : ℂ) :=
  (memLp_atomC A k q).coeFn_toLp

private lemma fourierCoeff_aLp (A k q : ℕ) (r : ℤ) :
    fourierCoeff (⇑(aLp A k q)) r = fourierCoeff (fun x => (atom A k q x : ℂ)) r := by
  unfold fourierCoeff
  refine integral_congr_ae ?_
  filter_upwards [coeFn_aLp A k q] with x hx
  rw [hx]

private lemma inner_fourierBasis_aLp (A k q : ℕ) (r : ℤ) :
    inner ℂ (fourierBasis r) (aLp A k q) = fourierCoeff (fun x => (atom A k q x : ℂ)) r := by
  rw [← fourierBasis.repr_apply_apply, fourierBasis_repr, fourierCoeff_aLp]

private lemma inner_aLp_eq_zero (A k q k' q' : ℕ)
    (hq : q ∈ Finset.Icc 1 (blockLen A k)) (hq' : q' ∈ Finset.Icc 1 (blockLen A k'))
    (hne : (k, q) ≠ (k', q')) : inner ℂ (aLp A k q) (aLp A k' q') = 0 := by
  rw [← fourierBasis.tsum_inner_mul_inner]
  refine (tsum_congr fun r => ?_).trans tsum_zero
  rw [← inner_conj_symm, inner_fourierBasis_aLp, inner_fourierBasis_aLp]
  rcases fourierCoeff_atom_disjoint A k q k' q' r hq hq' hne with h | h <;> simp [h]

private lemma inner_aLp_self (A k q : ℕ) : inner ℂ (aLp A k q) (aLp A k q) = 1 := by
  rw [MeasureTheory.L2.inner_def]
  have h : ∀ᵐ x ∂(haarAddCircle (T := 1)), inner ℂ ((aLp A k q) x) ((aLp A k q) x) =
      ((spike (depth A k) ((2 ^ (shift A k + q * spacing A k) : ℕ) • x) ^ 2 : ℝ) : ℂ) := by
    filter_upwards [coeFn_aLp A k q] with x hx
    rw [hx, RCLike.inner_apply', atom, Complex.conj_ofReal]
    push_cast; ring
  rw [integral_congr_ae h, integral_complex_ofReal,
    integral_spike_nsmul_sq _ _ (one_le_depth A k) (pow_ne_zero _ two_ne_zero)]
  simp

private lemma coeFn_finset_sum' {ι : Type*} (s : Finset ι) (f : ι → Lp ℂ 2 (haarAddCircle (T := 1))) :
    ⇑(∑ i ∈ s, f i) =ᵐ[(haarAddCircle (T := 1))] fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℂ 2 (haarAddCircle (T := 1))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2, Finset.sum_insert ha]

lemma eLpNorm_partialSum_le (A : ℕ) (hA : 1 ≤ A) (K : ℕ) :
    eLpNorm (fun x => ∑ k ∈ range K, blk A k x) 2 (haarAddCircle (T := 1)) ≤ 1 := by
  set c : ℕ → ℝ := fun k => Real.sqrt (lam A k / blockLen A k) with hc
  obtain ⟨Gc, hGc⟩ : ∃ Gc : Lp ℂ 2 (haarAddCircle (T := 1)),
      Gc = ∑ k ∈ range K, ∑ q ∈ Icc 1 (blockLen A k), ((c k : ℝ) : ℂ) • aLp A k q := ⟨_, rfl⟩
  -- pointwise identification
  have hae : ⇑Gc =ᵐ[(haarAddCircle (T := 1))] fun x => (((∑ k ∈ range K, blk A k x : ℝ)) : ℂ) := by
    have h1 := coeFn_finset_sum' (range K)
      (fun k => ∑ q ∈ Icc 1 (blockLen A k), ((c k : ℝ) : ℂ) • aLp A k q)
    have h2 : ∀ᵐ x ∂(haarAddCircle (T := 1)), ∀ k : ℕ,
        (⇑(∑ q ∈ Icc 1 (blockLen A k), ((c k : ℝ) : ℂ) • aLp A k q)) x =
          ∑ q ∈ Icc 1 (blockLen A k), ((c k : ℝ) : ℂ) * (atom A k q x : ℂ) := by
      refine ae_all_iff.2 fun k => ?_
      filter_upwards [coeFn_finset_sum' (Icc 1 (blockLen A k))
          (fun q => ((c k : ℝ) : ℂ) • aLp A k q),
        ae_all_iff.2 fun q => Lp.coeFn_smul ((c k : ℝ) : ℂ) (aLp A k q),
        ae_all_iff.2 fun q => coeFn_aLp A k q] with x hx hs ha
      rw [hx]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hs q, Pi.smul_apply, smul_eq_mul, ha q]
    filter_upwards [h1, h2] with x hx h2x
    rw [hGc, hx]
    simp only [h2x]
    simp only [blk_eq_sum_atom, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum, hc]
  -- inner product computation
  have key : ∀ k ∈ range K, ∀ q ∈ Icc 1 (blockLen A k),
      inner ℂ (aLp A k q) Gc = ((c k : ℝ) : ℂ) := by
    intro k hk q hq
    rw [hGc, inner_sum, Finset.sum_eq_single k]
    · rw [inner_sum, Finset.sum_eq_single q]
      · rw [inner_smul_right, inner_aLp_self, mul_one]
      · intro q' hq' hne
        rw [inner_smul_right, inner_aLp_eq_zero A k q k q' hq hq'
          (fun h => hne (Prod.ext_iff.1 h).2.symm), mul_zero]
      · intro h; exact absurd hq h
    · intro k' _ hne
      rw [inner_sum]
      refine Finset.sum_eq_zero fun q' hq' => ?_
      rw [inner_smul_right, inner_aLp_eq_zero A k q k' q' hq hq'
        (fun h => hne (Prod.ext_iff.1 h).1.symm), mul_zero]
    · intro h; exact absurd hk h
  have hinner : inner ℂ Gc Gc = (((∑ k ∈ range K, lam A k : ℝ)) : ℂ) := by
    calc inner ℂ Gc Gc
        = inner ℂ (∑ k ∈ range K, ∑ q ∈ Icc 1 (blockLen A k), ((c k : ℝ) : ℂ) • aLp A k q)
            Gc := by rw [← hGc]
      _ = ∑ k ∈ range K, ∑ q ∈ Icc 1 (blockLen A k),
            (starRingEnd ℂ) ((c k : ℝ) : ℂ) * inner ℂ (aLp A k q) Gc := by
          rw [sum_inner]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [sum_inner]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [inner_smul_left]
      _ = (((∑ k ∈ range K, lam A k : ℝ)) : ℂ) := by
          rw [Complex.ofReal_sum]
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Finset.sum_congr rfl fun q hq => by rw [key k hk q hq]]
          have hL : (blockLen A k : ℝ) ≠ 0 := by
            have := one_le_blockLen A k
            exact_mod_cast (show blockLen A k ≠ 0 by omega)
          have h0 : 0 ≤ lam A k / blockLen A k :=
            div_nonneg (lam_pos A k).le (Nat.cast_nonneg _)
          rw [Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul,
            Complex.conj_ofReal, ← Complex.ofReal_mul, hc, Real.mul_self_sqrt h0,
            ← Complex.ofReal_natCast, ← Complex.ofReal_mul, mul_div_cancel₀ _ hL]
  have hnorm_sq : ‖Gc‖ ^ 2 = ∑ k ∈ range K, lam A k := by
    have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) Gc
    rw [hinner] at this
    exact Complex.ofReal_injective (by rw [Complex.ofReal_pow]; exact this.symm)
  have hsum : ∑ k ∈ range K, lam A k ≤ 1 :=
    ((summable_lam A hA).sum_le_tsum (range K) (fun k _ => (lam_pos A k).le)).trans
      (tsum_lam_le_one A hA)
  have hnorm : ‖Gc‖ ≤ 1 := by nlinarith [norm_nonneg Gc]
  have hmeas : AEStronglyMeasurable (fun x => ∑ k ∈ range K, blk A k x) (haarAddCircle (T := 1)) := by
    have hb : ∀ k, Measurable (blk A k) := fun k => by
      have e : blk A k = fun x => Real.sqrt (lam A k / blockLen A k) *
          ∑ q ∈ Icc 1 (blockLen A k), atom A k q x := funext (blk_eq_sum_atom A k)
      rw [e]
      exact (Finset.measurable_sum _ fun q _ => measurable_atom' A k q).const_mul _
    exact (Finset.measurable_sum _ fun k _ => hb k).aestronglyMeasurable
  have e1 : eLpNorm (fun x => ∑ k ∈ range K, blk A k x) 2 (haarAddCircle (T := 1)) ≤
      eLpNorm (fun x => (((∑ k ∈ range K, blk A k x : ℝ)) : ℂ)) 2 (haarAddCircle (T := 1)) :=
    eLpNorm_mono fun x => le_of_eq (Complex.norm_real _).symm
  refine e1.trans ?_
  rw [← eLpNorm_congr_ae hae, ← Lp.enorm_def, ← ofReal_norm]
  exact ENNReal.ofReal_le_one.2 hnorm

end Asm
end OMA.Port23

/- ### GlobalL2 -/

/-!
Section: Assembly sub-lemma 8 (GlobalL2): the global function `g = ∑ F_k`

Blueprint §8. Ho Prop. 4.3, first paragraph, simplified (no Kolmogorov criterion):
* `∑ (F_k + c_k) ≥ 0` termwise and `∫ ∑ (F_k + c_k) = ∑ c_k < ∞` (monotone convergence,
  `∫ F_k = 0`), so `gPos < ∞` a.e.;
* where `gPos x < ∞`, the partial sums `∑_{k<K} F_k x → gFun x`;
* Fatou (`eLpNorm_partialSum_le`) gives `g ∈ L²`;
* `‖g - ∑_{k<K} F_k‖₁ ≤ 2 ∑_{k ≥ K} c_k → 0`, hence `∫ g = 0` and the Fourier coefficients of
  `g` are the sums of those of the blocks (only one block is nonzero at each frequency).
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace OMA.Port23
namespace Asm


/-! ### Auxiliary facts about the blocks -/

lemma measurable_blk (A k : ℕ) : Measurable (blk A k) := by
  unfold blk block
  refine Measurable.const_mul (Finset.measurable_sum _ fun q _ => ?_) _
  exact (measurable_spike _).comp (continuous_nsmul _).measurable

lemma integrable_blk (A k : ℕ) : Integrable (blk A k) (haarAddCircle (T := 1)) := by
  refine Integrable.of_bound (measurable_blk A k).aestronglyMeasurable
    (Real.sqrt (lam A k / blockLen A k) * ∑ q ∈ Finset.Icc 1 (blockLen A k), (2 : ℝ) ^ depth A k)
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs]
  unfold blk block
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  gcongr
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q _ => abs_spike_le _ _)

lemma fourierCoeff_blk_zero (A k : ℕ) : fourierCoeff (fun x => (blk A k x : ℂ)) 0 = 0 := by
  rw [fourierCoeff_blk, Finset.sum_eq_zero (fun q _ => fourierCoeff_atom_zero A k q), mul_zero]

lemma integral_blk (A k : ℕ) : ∫ x, blk A k x ∂(haarAddCircle (T := 1)) = 0 := by
  have h := fourierCoeff_blk_zero A k
  rw [fourierCoeff] at h
  simp only [neg_zero, fourier_zero, one_smul] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

lemma measurable_gPos (A : ℕ) : Measurable (gPos A) := by
  unfold gPos
  exact Measurable.ennreal_tsum fun k => ((measurable_blk A k).add_const _).ennreal_ofReal

lemma measurable_gFun (A : ℕ) : Measurable (gFun A) := by
  unfold gFun
  exact (measurable_gPos A).ennreal_toReal.sub_const _

lemma lintegral_gPos (A : ℕ) :
    ∫⁻ x, gPos A x ∂(haarAddCircle (T := 1)) = ∑' k, ENNReal.ofReal (floorC A k) := by
  unfold gPos
  rw [lintegral_tsum fun k => ((measurable_blk A k).add_const _).ennreal_ofReal.aemeasurable]
  congr 1
  ext k
  have hi : Integrable (fun x => blk A k x + floorC A k) (haarAddCircle (T := 1)) :=
    (integrable_blk A k).add (integrable_const _)
  have hnn : (0 : (AddCircle (1 : ℝ)) → ℝ) ≤ᵐ[(haarAddCircle (T := 1))] fun x => blk A k x + floorC A k :=
    ae_of_all _ fun x => by
      have := blk_floor A k x
      simp only [Pi.zero_apply]
      linarith
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnn,
    integral_add (integrable_blk A k) (integrable_const _), integral_blk, integral_const]
  simp

lemma lintegral_gPos_ne_top (A : ℕ) (hA : 1 ≤ A) : ∫⁻ x, gPos A x ∂(haarAddCircle (T := 1)) ≠ ∞ := by
  rw [lintegral_gPos, ← ENNReal.ofReal_tsum_of_nonneg (floorC_nonneg A) (summable_floorC A hA)]
  exact ENNReal.ofReal_ne_top

lemma gPos_toReal_eq (A : ℕ) (x : (AddCircle (1 : ℝ))) (hx : gPos A x ≠ ∞) :
    Summable (fun k => blk A k x + floorC A k) ∧
      (gPos A x).toReal = ∑' k, (blk A k x + floorC A k) := by
  have hnn : ∀ k, 0 ≤ blk A k x + floorC A k := fun k => by linarith [blk_floor A k x]
  have e : ∀ k, (ENNReal.ofReal (blk A k x + floorC A k)).toReal = blk A k x + floorC A k :=
    fun k => ENNReal.toReal_ofReal (hnn k)
  constructor
  · have := ENNReal.summable_toReal (f := fun k => ENNReal.ofReal (blk A k x + floorC A k)) hx
    simp only [e] at this
    exact this
  · unfold gPos
    rw [ENNReal.tsum_toReal_eq (fun k => ENNReal.ofReal_ne_top)]
    simp only [e]

lemma hasSum_blk (A : ℕ) (hA : 1 ≤ A) (x : (AddCircle (1 : ℝ))) (hx : gPos A x ≠ ∞) :
    HasSum (fun k => blk A k x) (gFun A x) := by
  obtain ⟨hs, htr⟩ := gPos_toReal_eq A x hx
  have h := hs.hasSum.sub (summable_floorC A hA).hasSum
  simp only [add_sub_cancel_right] at h
  unfold gFun
  rw [htr]
  exact h

/-! ### Main statements -/

lemma ae_gPos_ne_top (A : ℕ) (hA : 1 ≤ A) : ∀ᵐ x ∂(haarAddCircle (T := 1)), gPos A x ≠ ∞ :=
  (ae_lt_top' (measurable_gPos A).aemeasurable (lintegral_gPos_ne_top A hA)).mono
    fun _ hx => hx.ne

lemma tendsto_partialSum_gFun (A : ℕ) (hA : 1 ≤ A) (x : (AddCircle (1 : ℝ))) (hx : gPos A x ≠ ∞) :
    Tendsto (fun K => ∑ k ∈ range K, blk A k x) atTop (𝓝 (gFun A x)) :=
  (hasSum_blk A hA x hx).tendsto_sum_nat

lemma memLp_gFun (A : ℕ) (hA : 1 ≤ A) : MemLp (fun x => (gFun A x : ℂ)) 2 (haarAddCircle (T := 1)) := by
  refine MemLp.ofReal (f := gFun A) ⟨(measurable_gFun A).aestronglyMeasurable, ?_⟩
  show eLpNorm (gFun A) 2 (haarAddCircle (T := 1)) < ∞
  have hlim : ∀ᵐ x ∂(haarAddCircle (T := 1)), Tendsto (fun K => ∑ k ∈ range K, blk A k x) atTop (𝓝 (gFun A x)) :=
    (ae_gPos_ne_top A hA).mono fun x hx => tendsto_partialSum_gFun A hA x hx
  have hmeas : ∀ K, AEStronglyMeasurable (fun x => ∑ k ∈ range K, blk A k x) (haarAddCircle (T := 1)) := fun K =>
    (Finset.measurable_sum _ fun k _ => measurable_blk A k).aestronglyMeasurable
  refine lt_of_le_of_lt (Lp.eLpNorm_lim_le_liminf_eLpNorm hmeas _ hlim) ?_
  refine lt_of_le_of_lt (liminf_le_of_frequently_le'
    (Frequently.of_forall fun K => eLpNorm_partialSum_le A hA K)) ?_
  exact ENNReal.one_lt_top

lemma fourierCoeff_blk_eq_zero_of_ne (A k k' : ℕ) (r : ℤ) (hne : k ≠ k')
    (h : fourierCoeff (fun x => (blk A k x : ℂ)) r ≠ 0) :
    fourierCoeff (fun x => (blk A k' x : ℂ)) r = 0 := by
  rw [fourierCoeff_blk] at h ⊢
  obtain ⟨q, hq, hq0⟩ : ∃ q ∈ Finset.Icc 1 (blockLen A k),
      fourierCoeff (fun x => (atom A k q x : ℂ)) r ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h (by rw [Finset.sum_eq_zero hc, mul_zero])
  rw [Finset.sum_eq_zero fun q' hq' => ?_, mul_zero]
  exact (fourierCoeff_atom_disjoint A k q k' q' r hq hq'
    (fun he => hne (congrArg Prod.fst he))).resolve_left hq0

lemma tendsto_fourierCoeff_partialSum (A : ℕ) (hA : 1 ≤ A) (r : ℤ) :
    Tendsto (fun K => ∑ k ∈ range K, fourierCoeff (fun x => (blk A k x : ℂ)) r) atTop
      (𝓝 (fourierCoeff (fun x => (gFun A x : ℂ)) r)) := by
  have hS : ∀ K, Measurable (fun x => ∑ k ∈ range K, blk A k x) := fun K =>
    Finset.measurable_sum _ fun k _ => measurable_blk A k
  have heq : ∀ K, ∑ k ∈ range K, fourierCoeff (fun x => (blk A k x : ℂ)) r =
      ∫ x, fourier (-r) x • (((∑ k ∈ range K, blk A k x : ℝ)) : ℂ) ∂(haarAddCircle (T := 1)) := by
    intro K
    have h := congrFun (fourierCoeff.sum (range K) (fun k x => (blk A k x : ℂ))
      (fun k _ => (integrable_blk A k).ofReal)) r
    rw [Finset.sum_apply] at h
    rw [← h, fourierCoeff]
    congr 1
    ext x
    simp only [Finset.sum_apply, Complex.ofReal_sum]
  refine (tendsto_congr heq).mpr ?_
  rw [fourierCoeff]
  have hG : Integrable (fun x => (gPos A x).toReal + ∑' k, floorC A k) (haarAddCircle (T := 1)) :=
    (integrable_toReal_of_lintegral_ne_top (measurable_gPos A).aemeasurable
      (lintegral_gPos_ne_top A hA)).add (integrable_const _)
  refine tendsto_integral_of_dominated_convergence
    (fun x => (gPos A x).toReal + ∑' k, floorC A k) ?_ hG ?_ ?_
  · intro K
    exact ((map_continuous (fourier (-r))).measurable.smul
      (Complex.measurable_ofReal.comp (hS K))).aestronglyMeasurable
  · intro K
    filter_upwards [ae_gPos_ne_top A hA] with x hx
    obtain ⟨hs, htr⟩ := gPos_toReal_eq A x hx
    rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_eq_abs,
      htr]
    have h1 : |∑ k ∈ range K, blk A k x| ≤
        ∑ k ∈ range K, (blk A k x + floorC A k) + ∑ k ∈ range K, floorC A k := by
      rw [← Finset.sum_add_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      have h1 := blk_floor A k x
      have h2 := floorC_nonneg A k
      rw [abs_le]
      constructor <;> linarith
    have h2 : ∑ k ∈ range K, (blk A k x + floorC A k) ≤ ∑' k, (blk A k x + floorC A k) :=
      hs.sum_le_tsum _ fun k _ => by linarith [blk_floor A k x]
    have h3 : ∑ k ∈ range K, floorC A k ≤ ∑' k, floorC A k :=
      (summable_floorC A hA).sum_le_tsum _ fun k _ => floorC_nonneg A k
    linarith
  · filter_upwards [ae_gPos_ne_top A hA] with x hx
    exact ((Complex.continuous_ofReal.tendsto _).comp
      (tendsto_partialSum_gFun A hA x hx)).const_smul (fourier (-r) x)

lemma hasSum_fourierCoeff_gFun_aux (A : ℕ) (hA : 1 ≤ A) (r : ℤ) :
    HasSum (fun k => fourierCoeff (fun x => (blk A k x : ℂ)) r)
      (fourierCoeff (fun x => (gFun A x : ℂ)) r) := by
  obtain ⟨a, ha⟩ : ∃ a, HasSum (fun k => fourierCoeff (fun x => (blk A k x : ℂ)) r) a := by
    by_cases h : ∃ k0, fourierCoeff (fun x => (blk A k0 x : ℂ)) r ≠ 0
    · obtain ⟨k0, hk0⟩ := h
      exact ⟨_, hasSum_single k0 fun k hk =>
        fourierCoeff_blk_eq_zero_of_ne A k0 k r (Ne.symm hk) hk0⟩
    · push Not at h
      exact ⟨0, by simp [h]⟩
  have := tendsto_nhds_unique ha.tendsto_sum_nat (tendsto_fourierCoeff_partialSum A hA r)
  rwa [← this]

lemma integral_gFun (A : ℕ) (hA : 1 ≤ A) : ∫ x, (gFun A x : ℂ) ∂(haarAddCircle (T := 1)) = 0 := by
  have h := hasSum_fourierCoeff_gFun_aux A hA 0
  simp only [fourierCoeff_blk_zero] at h
  have h0 := h.unique hasSum_zero
  rw [fourierCoeff] at h0
  simp only [neg_zero, fourier_zero, one_smul] at h0
  exact h0

lemma hasSum_fourierCoeff_gFun (A : ℕ) (hA : 1 ≤ A) (r : ℤ) :
    HasSum (fun k => fourierCoeff (fun x => (blk A k x : ℂ)) r)
      (fourierCoeff (fun x => (gFun A x : ℂ)) r) :=
  hasSum_fourierCoeff_gFun_aux A hA r

end Asm
end OMA.Port23

/- ### Master -/

/-!
Section: Assembly sub-lemma 9 (Master): the master estimate at the end of a good trial

Blueprint §9. Ho Prop. 4.3, master estimate (4.16): if trial `s` (of stage `k`) is good and
the series is finite at all `n_j x`, then with `N = 21^{s+1} - 1`, `P = 21^s - 1`, `ℓ = ℓ_s`:
`∑_{j<N} g(n_j x) ≥ ∑_{r=1}^{ℓ} F_k(2^{M_s + r D_k} x) - N/100 ≥ 200 ℓ - N/100 ≥ N`.
Also the pointwise floors of `g` and the pull-back of a.e. statements along `x ↦ n_j x`.
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace OMA.Port23
namespace Asm


lemma gFun_ge (A : ℕ) (hA : 1 ≤ A) (x : (AddCircle (1 : ℝ))) : -(1 / 100 : ℝ) ≤ gFun A x := by
  unfold gFun
  have h1 := tsum_floorC_le A hA
  have h2 : 0 ≤ (gPos A x).toReal := ENNReal.toReal_nonneg
  linarith

lemma blk_sub_le_gFun (A : ℕ) (hA : 1 ≤ A) (x : (AddCircle (1 : ℝ))) (hx : gPos A x ≠ ∞) (k : ℕ) :
    blk A k x - 1 / 100 ≤ gFun A x := by
  unfold gFun
  have h1 := tsum_floorC_le A hA
  have h0 := floorC_nonneg A k
  have hle : ENNReal.ofReal (blk A k x + floorC A k) ≤ gPos A x := by
    unfold gPos
    exact ENNReal.le_tsum (f := fun k => ENNReal.ofReal (blk A k x + floorC A k)) k
  have h3 : (ENNReal.ofReal (blk A k x + floorC A k)).toReal ≤ (gPos A x).toReal :=
    ENNReal.toReal_mono hx hle
  have h4 : blk A k x + floorC A k ≤ (ENNReal.ofReal (blk A k x + floorC A k)).toReal := by
    rw [ENNReal.toReal_ofReal']; exact le_max_left _ _
  linarith

lemma ae_forall_nSeq (A : ℕ) {P : (AddCircle (1 : ℝ)) → Prop} (h : ∀ᵐ y ∂(haarAddCircle (T := 1)), P y) :
    ∀ᵐ x ∂(haarAddCircle (T := 1)), ∀ j, P (nSeq A j • x) := by
  have hv : (volume : Measure (AddCircle (1 : ℝ))) = (haarAddCircle (T := 1)) := by
    rw [volume_eq_smul_haarAddCircle]; simp
  rw [ae_all_iff]
  intro j
  have hmp : MeasurePreserving (fun y : (AddCircle (1 : ℝ)) => nSeq A j • y) (haarAddCircle (T := 1)) (haarAddCircle (T := 1)) := by
    by_cases h1 : 1 < nSeq A j
    · rw [← hv]; exact (ergodic_nsmul h1).toMeasurePreserving
    · have h2 : 1 ≤ nSeq A j := Nat.one_le_two_pow
      have h3 : nSeq A j = 1 := by omega
      simp only [h3, one_smul]
      exact MeasurePreserving.id _
  exact hmp.quasiMeasurePreserving.ae h

lemma master_trial (A : ℕ) (hA : 1 ≤ A) (x : (AddCircle (1 : ℝ))) (s : ℕ)
    (hfin : ∀ j, gPos A (nSeq A j • x) ≠ ∞) (hx : x ∈ goodSet A s) :
    ∃ N : ℕ, s ≤ N ∧ (1 : ℝ) ≤ (∑ j ∈ range N, gFun A (nSeq A j • x)) / N := by
  set k := stage A s with hk
  set ℓ := trialLen s with hℓ
  set P := 21 ^ s - 1 with hP
  have ht : 1 ≤ 21 ^ s := Nat.one_le_pow _ _ (by norm_num)
  have hsl : s < 21 ^ s := Nat.lt_pow_self (by norm_num)
  have hℓP : P + 1 ≤ ℓ := by simp only [hℓ, hP, trialLen]; omega
  have hℓv : ℓ = 20 * 21 ^ s := rfl
  refine ⟨P + ℓ, by omega, ?_⟩
  -- the trial signal
  have hsig : 2 * (100 : ℝ) * ℓ ≤ ∑ r ∈ Finset.Icc 1 ℓ,
      block (lam A k) (blockLen A k) (depth A k) (spacing A k) (shift A k)
        ((2 ^ (trialStart A s + r * spacing A k) : ℕ) • x) := by
    have hd := depth_spec A k
    apply trial_signal (lam A k) 100 (blockLen A k) ℓ (depth A k) (spacing A k) (shift A k)
      (trialStart A s) (lam_pos A k) (lam_le_one A k) le_rfl (one_le_blockLen A k)
      (trialLen_le A s) (by simp [spacing]) hd.1 hd.2 x
    simp only [goodSet, Set.mem_iUnion] at hx
    obtain ⟨h, hh, hx⟩ := hx
    exact ⟨h, hh, by simpa [hitSet, spikeSet, add_assoc] using hx⟩
  -- reindex the trial
  have hre : ∑ r ∈ Finset.Icc 1 ℓ,
      block (lam A k) (blockLen A k) (depth A k) (spacing A k) (shift A k)
        ((2 ^ (trialStart A s + r * spacing A k) : ℕ) • x)
      = ∑ j ∈ Finset.Ico P (P + ℓ), blk A k (nSeq A j • x) := by
    apply Finset.sum_nbij' (fun r => 21 ^ s + r - 2) (fun j => j + 2 - 21 ^ s)
    · intro r hr; simp only [Finset.mem_Icc, Finset.mem_Ico] at hr ⊢
      omega
    · intro j hj; simp only [Finset.mem_Icc, Finset.mem_Ico] at hj ⊢
      omega
    · intro r hr; simp only [Finset.mem_Icc] at hr; omega
    · intro j hj; simp only [Finset.mem_Ico] at hj; omega
    · intro r hr
      simp only [Finset.mem_Icc] at hr
      unfold blk nSeq
      rw [mExp_trial A s r hr.1 hr.2]
  have hsplit := Finset.sum_range_add_sum_Ico (fun j => gFun A (nSeq A j • x))
    (Nat.le_add_right P ℓ)
  have hA1 : -((P : ℝ) * (1 / 100)) ≤ ∑ j ∈ range P, gFun A (nSeq A j • x) := by
    have := Finset.card_nsmul_le_sum (range P) (fun j => gFun A (nSeq A j • x)) (-(1 / 100))
      (fun j _ => gFun_ge A hA _)
    simp only [Finset.card_range, nsmul_eq_mul] at this
    linarith
  have hA2 : ∑ j ∈ Finset.Ico P (P + ℓ), (blk A k (nSeq A j • x) - 1 / 100)
      ≤ ∑ j ∈ Finset.Ico P (P + ℓ), gFun A (nSeq A j • x) :=
    Finset.sum_le_sum (fun j _ => blk_sub_le_gFun A hA _ (hfin j) k)
  rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ico, Nat.add_sub_cancel_left,
    nsmul_eq_mul, ← hre] at hA2
  rw [← hsplit]
  have hNpos : (0 : ℝ) < ((P + ℓ : ℕ) : ℝ) := by
    have : 0 < P + ℓ := by omega
    exact_mod_cast this
  rw [le_div_iff₀ hNpos, one_mul]
  have hℓP' : (P : ℝ) + 1 ≤ ℓ := by exact_mod_cast hℓP
  push_cast
  nlinarith

end Asm
end OMA.Port23

/- ### ParsevalTail -/

/-!
Section: Assembly sub-lemma 10 (ParsevalTail): the Fourier tail via Parseval

Blueprint §10. Generic: for `f ∈ L²((AddCircle (1 : ℝ)))`, `‖f - S_N f‖₂² = ∑_{|r| > N} |f̂(r)|²`
(`tsum_sq_fourierCoeff` applied to `f - S_N f`, whose coefficients are `f̂(r) 1_{|r|>N}`).
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace OMA.Port23
namespace Asm


lemma eLpNorm_sub_fourierPartial_sq (f : Lp ℂ 2 (haarAddCircle (T := 1))) (N : ℕ) :
    (eLpNorm (⇑f - fourierPartial f N) 2 (haarAddCircle (T := 1))).toReal ^ 2 =
      ∑' r : {r : ℤ // (N : ℤ) < |r|}, ‖fourierCoeff f r‖ ^ 2 := by
  classical
  set s : Finset ℤ := Icc (-(N : ℤ)) N with hs
  set g : Lp ℂ 2 (haarAddCircle (T := 1)) := f - ∑ i ∈ s, fourierCoeff f i • fourierLp (T := 1) 2 i with hg
  have hae : (⇑g : (AddCircle (1 : ℝ)) → ℂ) =ᵐ[(haarAddCircle (T := 1))] ⇑f - fourierPartial f N := by
    have h1 := Lp.coeFn_sub f (∑ i ∈ s, fourierCoeff f i • fourierLp (T := 1) 2 i)
    have h2 := Lp.coeFn_finsetSum s (fun i => fourierCoeff f i • fourierLp (T := 1) 2 i)
    have h3 : ∀ i : ℤ, (⇑(fourierCoeff f i • fourierLp (T := 1) 2 i) : (AddCircle (1 : ℝ)) → ℂ) =ᵐ[(haarAddCircle (T := 1))]
        fun x => fourierCoeff f i • fourier i x := by
      intro i
      filter_upwards [Lp.coeFn_smul (fourierCoeff f i) (fourierLp (T := 1) 2 i),
        coeFn_fourierLp (T := 1) 2 i] with x hx1 hx2
      rw [hx1, Pi.smul_apply, hx2]
    have h3' := ae_all_iff.2 h3
    filter_upwards [h1, h2, h3'] with x hx1 hx2 hx3
    rw [hx1, Pi.sub_apply, Pi.sub_apply, hx2, Finset.sum_apply]
    simp only [fourierPartial, hx3, hs]
  have hL : (eLpNorm (⇑f - fourierPartial f N) 2 (haarAddCircle (T := 1))).toReal = ‖g‖ := by
    rw [Lp.norm_def, eLpNorm_congr_ae hae]
  have hnorm : HasSum (fun i => ‖(fourierBasis (T := 1)).repr g i‖ ^ 2) (‖g‖ ^ 2) := by
    have H₁ : HasSum (fun i => ‖(fourierBasis (T := 1)).repr g i‖ ^ 2)
        (‖(fourierBasis (T := 1)).repr g‖ ^ 2) := by
      apply_mod_cast lp.hasSum_norm ?_ ((fourierBasis (T := 1)).repr g)
      simp
    simpa using H₁
  have he : ∀ j : ℤ, fourierLp (T := 1) 2 j = (fourierBasis (T := 1)) j := fun j => by
    rw [coe_fourierBasis]
  have hcoef : ∀ i, (fourierBasis (T := 1)).repr g i = if i ∈ s then 0 else fourierCoeff f i := by
    intro i
    rw [hg, map_sub, map_sum]
    simp only [he, map_smul, HilbertBasis.repr_self, lp.coeFn_sub, lp.coeFn_sum, lp.coeFn_smul,
      Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, lp.single_apply, fourierBasis_repr,
      Pi.single_apply, smul_eq_mul]
    split_ifs with h <;> simp [h]
  have hterm : (fun i => ‖(fourierBasis (T := 1)).repr g i‖ ^ 2) =
      {r : ℤ | (N : ℤ) < |r|}.indicator (fun r => ‖fourierCoeff f r‖ ^ 2) := by
    funext i
    rw [hcoef i, Set.indicator_apply]
    by_cases h : i ∈ s
    · have : ¬ (N : ℤ) < |i| := by
        rw [hs, Finset.mem_Icc] at h; rw [not_lt, abs_le]; exact h
      simp [h, this]
    · have : (N : ℤ) < |i| := by
        rw [hs, Finset.mem_Icc] at h; rw [lt_abs]; omega
      simp [h, this]
  rw [hL, ← hnorm.tsum_eq, hterm]
  exact (tsum_subtype {r : ℤ | (N : ℤ) < |r|} _).symm

end Asm
end OMA.Port23

/- ### TailSum -/

/-!
Section: Assembly sub-lemma 11 (TailSum): the Fourier tail of `g`

Blueprint §10. Ho Lemma 3.1 (3.5)–(3.6) and (5.4)–(5.5): at each frequency at most one atom is
nonzero, so `|ĝ(r)|² = ∑_k (λ_k/L_k) ∑_q |âtom_{k,q}(r)|²`; summing over `|r| > N` and using
`spike_dilate_tail` with `2^{d_k + U_k + q D_k} ≤ 2^{E_k}` gives
`∑_{|r|>N} |ĝ(r)|² ≤ C₁ ∑_k λ_k min(1, 2^{E_k}/N)`.
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace OMA.Port23
namespace Asm


/-- If at most one term of a finite sum is nonzero, `‖∑ f‖² = ∑ ‖f‖²`. -/
lemma alt_norm_sum_sq_of_disj {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i = 0 ∨ f j = 0) :
    ‖∑ i ∈ s, f i‖ ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2 := by
  classical
  by_cases hex : ∃ i ∈ s, f i ≠ 0
  · obtain ⟨i, hi, hfi⟩ := hex
    have hz : ∀ j ∈ s, j ≠ i → f j = 0 := by
      intro j hj hji
      rcases h i hi j hj (Ne.symm hji) with h1 | h1
      · exact absurd h1 hfi
      · exact h1
    rw [Finset.sum_eq_single i hz (fun h' => absurd hi h'),
      Finset.sum_eq_single i (fun j hj hji => by rw [hz j hj hji, norm_zero]; ring)
        (fun h' => absurd hi h')]
  · push Not at hex
    rw [Finset.sum_eq_zero hex, Finset.sum_eq_zero (fun i hi => by rw [hex i hi, norm_zero]; ring)]
    simp

lemma alt_fc_blk_disj (A k k' : ℕ) (r : ℤ) (hne : k ≠ k') :
    fourierCoeff (fun x => (blk A k x : ℂ)) r = 0 ∨
      fourierCoeff (fun x => (blk A k' x : ℂ)) r = 0 := by
  by_contra hc
  rw [not_or] at hc
  obtain ⟨h1, h2⟩ := hc
  simp only [fourierCoeff_blk] at h1 h2
  obtain ⟨q, hq, hq0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul h1)
  obtain ⟨q', hq', hq0'⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul h2)
  rcases fourierCoeff_atom_disjoint A k q k' q' r hq hq'
    (fun h => hne (congrArg Prod.fst h)) with h | h
  · exact hq0 h
  · exact hq0' h

lemma alt_hasSum_norm_sq (A : ℕ) (hA : 1 ≤ A) (r : ℤ) :
    HasSum (fun k => ‖fourierCoeff (fun x => (blk A k x : ℂ)) r‖ ^ 2)
      (‖fourierCoeff (fun x => (gFun A x : ℂ)) r‖ ^ 2) := by
  classical
  have hs := hasSum_fourierCoeff_gFun A hA r
  set b := fun k => fourierCoeff (fun x => (blk A k x : ℂ)) r with hb
  by_cases hex : ∃ k0, b k0 ≠ 0
  · obtain ⟨k0, hk0⟩ := hex
    have hz : ∀ k, k ≠ k0 → b k = 0 := by
      intro k hk
      rcases alt_fc_blk_disj A k k0 r hk with h | h
      · exact h
      · exact absurd h hk0
    have h1 : HasSum b (b k0) := hasSum_single k0 hz
    rw [hs.unique h1]
    exact hasSum_single k0 (fun k hk => by
      show ‖b k‖ ^ 2 = 0
      rw [hz k hk, norm_zero]; ring)
  · push Not at hex
    have hb0 : b = 0 := funext hex
    have h1 : HasSum b 0 := by rw [hb0]; exact hasSum_zero
    rw [hs.unique h1, norm_zero]
    have : (fun k => ‖b k‖ ^ 2) = fun _ => (0 : ℝ) ^ 2 := by
      funext k; rw [hex k, norm_zero]
    rw [show (fun k => ‖fourierCoeff (fun x => (blk A k x : ℂ)) r‖ ^ 2) =
      fun k => ‖b k‖ ^ 2 from rfl, this]
    simp

lemma alt_norm_blk_sq (A k : ℕ) (r : ℤ) :
    ‖fourierCoeff (fun x => (blk A k x : ℂ)) r‖ ^ 2 =
      lam A k / blockLen A k *
        ∑ q ∈ Finset.Icc 1 (blockLen A k), ‖fourierCoeff (fun x => (atom A k q x : ℂ)) r‖ ^ 2 := by
  rw [fourierCoeff_blk, norm_mul, mul_pow, alt_norm_sum_sq_of_disj]
  · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (div_nonneg (lam_pos A k).le (Nat.cast_nonneg _))]
  · intro q hq q' hq' hne
    exact fourierCoeff_atom_disjoint A k q k q' r hq hq' (fun h => hne (congrArg Prod.snd h))

lemma alt_summable_atom (A k q : ℕ) :
    Summable (fun r : ℤ => ‖fourierCoeff (fun x => (atom A k q x : ℂ)) r‖ ^ 2) := by
  have hmeas : Measurable (atom A k q) :=
    (OMA.Port23.measurable_spike _).comp (continuous_nsmul _).measurable
  have hm : MemLp (fun x => (atom A k q x : ℂ)) 2 (haarAddCircle (T := 1)) :=
    MemLp.of_bound ((Complex.measurable_ofReal.comp hmeas).aestronglyMeasurable)
      (2 ^ depth A k)
      (Eventually.of_forall fun x => by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_spike_le _ _)
  have := (hasSum_sq_fourierCoeff (hm.toLp _)).summable
  rwa [fourierCoeff_congr_ae hm.coeFn_toLp] at this

lemma tail_sum_le : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ A : ℕ, 1 ≤ A → ∀ N : ℕ, 1 ≤ N →
    ∑' r : {r : ℤ // (N : ℤ) < |r|}, ‖fourierCoeff (fun x => (gFun A x : ℂ)) r‖ ^ 2 ≤
      C₁ * ∑' k, lam A k * min 1 ((2 : ℝ) ^ logQ A k / N) := by
  obtain ⟨C, hC, hT⟩ := spike_dilate_tail
  refine ⟨C, hC, fun A hA N hN => ?_⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set F : ℕ → ℝ := fun k => C * (lam A k * min 1 ((2 : ℝ) ^ logQ A k / N)) with hFdef
  have hF0 : ∀ k, 0 ≤ F k := fun k =>
    mul_nonneg hC.le (mul_nonneg (lam_pos A k).le (le_min zero_le_one (by positivity)))
  have hFle : ∀ k, F k ≤ C * lam A k := fun k =>
    mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (lam_pos A k).le (min_le_left _ _)) hC.le
  have hFs : Summable F :=
    Summable.of_nonneg_of_le hF0 hFle ((summable_lam A hA).mul_left C)
  rw [← tsum_mul_left]
  refine Real.tsum_le_of_sum_le (fun r => sq_nonneg _) (fun u => ?_)
  have h1 : HasSum (fun k => ∑ r ∈ u, ‖fourierCoeff (fun x => (blk A k x : ℂ)) r.1‖ ^ 2)
      (∑ r ∈ u, ‖fourierCoeff (fun x => (gFun A x : ℂ)) r.1‖ ^ 2) :=
    hasSum_sum (fun r _ => alt_hasSum_norm_sq A hA r.1)
  refine hasSum_le (fun k => ?_) h1 hFs.hasSum
  -- termwise bound for the `k`-th block
  have hL : (1 : ℝ) ≤ blockLen A k := by exact_mod_cast one_le_blockLen A k
  have hq : ∀ q ∈ Finset.Icc 1 (blockLen A k),
      ∑ r ∈ u, ‖fourierCoeff (fun x => (atom A k q x : ℂ)) r.1‖ ^ 2 ≤
        C * min 1 ((2 : ℝ) ^ logQ A k / N) := by
    intro q hqm
    rw [Finset.mem_Icc] at hqm
    have hs : Summable (fun r : {r : ℤ // (N : ℤ) < |r|} =>
        ‖fourierCoeff (fun x => (atom A k q x : ℂ)) r.1‖ ^ 2) :=
      (alt_summable_atom A k q).comp_injective Subtype.val_injective
    have ht := hT (depth A k) (shift A k + q * spacing A k) N (one_le_depth A k) hN
    have hexp : depth A k + (shift A k + q * spacing A k) ≤ logQ A k := by
      have e1 : logQ A k = shift A k + blockLen A k * spacing A k + depth A k + 2 := rfl
      have e2 : q * spacing A k ≤ blockLen A k * spacing A k := Nat.mul_le_mul_right _ hqm.2
      omega
    have hpow : (2 : ℝ) ^ (depth A k + (shift A k + q * spacing A k)) ≤ (2 : ℝ) ^ logQ A k :=
      pow_le_pow_right₀ (by norm_num) hexp
    calc ∑ r ∈ u, ‖fourierCoeff (fun x => (atom A k q x : ℂ)) r.1‖ ^ 2
        ≤ ∑' r : {r : ℤ // (N : ℤ) < |r|},
            ‖fourierCoeff (fun x => (atom A k q x : ℂ)) r.1‖ ^ 2 :=
          hs.sum_le_tsum u (fun _ _ => sq_nonneg _)
      _ ≤ C * min 1 ((2 : ℝ) ^ (depth A k + (shift A k + q * spacing A k)) / N) := ht
      _ ≤ C * min 1 ((2 : ℝ) ^ logQ A k / N) :=
          mul_le_mul_of_nonneg_left
            (min_le_min_left _ (div_le_div_of_nonneg_right hpow hNr.le)) hC.le
  calc ∑ r ∈ u, ‖fourierCoeff (fun x => (blk A k x : ℂ)) r.1‖ ^ 2
      = lam A k / blockLen A k * ∑ q ∈ Finset.Icc 1 (blockLen A k),
          ∑ r ∈ u, ‖fourierCoeff (fun x => (atom A k q x : ℂ)) r.1‖ ^ 2 := by
        simp_rw [alt_norm_blk_sq, ← Finset.mul_sum]
        rw [Finset.sum_comm]
    _ ≤ lam A k / blockLen A k * ∑ q ∈ Finset.Icc 1 (blockLen A k),
          C * min 1 ((2 : ℝ) ^ logQ A k / N) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hq)
          (div_nonneg (lam_pos A k).le (by linarith))
    _ = F k := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel, hFdef]
        field_simp

end Asm
end OMA.Port23

/- ### TailAsymp -/

/-!
Section: Assembly sub-lemma 12 (TailAsymp): the tail sum beats `(log log log N)^{-C}`

Blueprint §11. Replaces Ho Prop. 5.2 for #996 (fixed `C`, no endpoint): split the stages into
`2^{E_k} ≤ √N` (contribution `≤ ∑ λ_k / √N ≤ N^{-1/2}`) and `N < 2^{2E_k}` (then
`log log log N ≤ B_k := (A+1)(k+1)+30`, so `λ_k ≤ λ_k B_k^{2C} / (log log log N)^{2C}`, and
`∑ λ_k B_k^{2C} < ∞` since `λ_k` decays geometrically); finally
`N^{-1/2} ≤ (log log log N)^{-2C}` for large `N`.
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace OMA.Port23
namespace Asm


lemma alt_log_gt_three (N : ℕ) (hN : 32 ≤ N) : 3 < Real.log (N : ℝ) := by
  have h2 := Real.log_two_gt_d9
  have h : Real.log ((2 : ℝ) ^ 5) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ^ 5 ≤ N by norm_num; omega))
  rw [Real.log_pow] at h
  push_cast at h
  linarith

lemma alt_one_lt_loglog (N : ℕ) (hN : 32 ≤ N) : 1 < Real.log (Real.log (N : ℝ)) := by
  have h3 := alt_log_gt_three N hN
  have he : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
  rw [Real.lt_log_iff_exp_lt (by linarith)]
  linarith

lemma alt_lll_pos (N : ℕ) (hN : 32 ≤ N) : 0 < Real.log (Real.log (Real.log (N : ℝ))) :=
  Real.log_pos (alt_one_lt_loglog N hN)

lemma alt_lll_le_log (N : ℕ) (hN : 32 ≤ N) :
    Real.log (Real.log (Real.log (N : ℝ))) ≤ Real.log (N : ℝ) := by
  have h1 := alt_one_lt_loglog N hN
  have h3 := alt_log_gt_three N hN
  calc _ ≤ Real.log (Real.log (N : ℝ)) := Real.log_le_self (by linarith)
    _ ≤ Real.log (N : ℝ) := Real.log_le_self (by linarith)

lemma alt_lll_lt (N e : ℕ) (hN : 32 ≤ N) (h : (N : ℝ) < (2 : ℝ) ^ (2 * e)) :
    Real.log (Real.log (Real.log (N : ℝ))) <
      Real.log (Real.log (Real.log ((2 : ℝ) ^ (2 * e)))) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h1 := alt_one_lt_loglog N hN
  have h3 := alt_log_gt_three N hN
  have g1 : Real.log (N : ℝ) < Real.log ((2 : ℝ) ^ (2 * e)) := Real.log_lt_log hNpos h
  have g2 : Real.log (Real.log (N : ℝ)) < Real.log (Real.log ((2 : ℝ) ^ (2 * e))) :=
    Real.log_lt_log (by linarith) g1
  exact Real.log_lt_log (by linarith) g2

/-- Per-term bound. -/
lemma alt_term_bound (A : ℕ) (C : ℝ) (hC : 0 < C) (e k : ℕ)
    (hE : Real.log (Real.log (Real.log ((2 : ℝ) ^ (2 * e)))) ≤ ((A : ℝ) + 1) * (k + 1) + 30)
    (N : ℕ) (hN : 32 ≤ N) :
    lam A k * min 1 ((2 : ℝ) ^ e / N) ≤
      lam A k / Real.sqrt N + lam A k * ((((A : ℝ) + 1) * (k + 1) + 30) ^ C) ^ 2 /
        (Real.log (Real.log (Real.log (N : ℝ))) ^ C) ^ 2 := by
  have hl := lam_pos A k
  set B : ℝ := ((A : ℝ) + 1) * (k + 1) + 30 with hB
  set L := Real.log (Real.log (Real.log (N : ℝ))) with hL
  have hLpos : 0 < L := alt_lll_pos N hN
  have hu : 0 < L ^ C := Real.rpow_pos_of_pos hLpos C
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hBpos : 0 < B := by rw [hB]; positivity
  have t1 : 0 ≤ lam A k / Real.sqrt N := by positivity
  have t2 : 0 ≤ lam A k * (B ^ C) ^ 2 / (L ^ C) ^ 2 := by positivity
  have hmin0 : 0 ≤ min 1 ((2 : ℝ) ^ e / N) := le_min zero_le_one (by positivity)
  by_cases h : (2 : ℝ) ^ (2 * e) ≤ N
  · have h1 : Real.sqrt (((2 : ℝ) ^ e) ^ 2) ≤ Real.sqrt N :=
      Real.sqrt_le_sqrt (by rw [← pow_mul, mul_comm]; exact h)
    rw [Real.sqrt_sq (by positivity)] at h1
    have e1 : Real.sqrt N / N = 1 / Real.sqrt N := by
      rw [eq_div_iff hs.ne', div_mul_eq_mul_div, div_eq_one_iff_eq hNpos.ne']
      exact Real.mul_self_sqrt hNpos.le
    have h2 : min 1 ((2 : ℝ) ^ e / N) ≤ 1 / Real.sqrt N := by
      rw [← e1]
      exact (min_le_right _ _).trans (div_le_div_of_nonneg_right h1 hNpos.le)
    calc lam A k * min 1 ((2 : ℝ) ^ e / N) ≤ lam A k * (1 / Real.sqrt N) :=
          mul_le_mul_of_nonneg_left h2 hl.le
      _ = lam A k / Real.sqrt N := by rw [mul_one_div]
      _ ≤ _ := le_add_of_nonneg_right t2
  · push Not at h
    have hlt := alt_lll_lt N e hN h
    have hLB : L ≤ B := (le_of_lt hlt).trans hE
    have hLC : L ^ C ≤ B ^ C := Real.rpow_le_rpow hLpos.le hLB hC.le
    have hsq : (L ^ C) ^ 2 ≤ (B ^ C) ^ 2 := pow_le_pow_left₀ hu.le hLC 2
    have hone : 1 ≤ (B ^ C) ^ 2 / (L ^ C) ^ 2 := (one_le_div (by positivity)).2 hsq
    calc lam A k * min 1 ((2 : ℝ) ^ e / N) ≤ lam A k * 1 :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hl.le
      _ ≤ lam A k * ((B ^ C) ^ 2 / (L ^ C) ^ 2) := mul_le_mul_of_nonneg_left hone hl.le
      _ = lam A k * (B ^ C) ^ 2 / (L ^ C) ^ 2 := by rw [mul_div_assoc]
      _ ≤ _ := le_add_of_nonneg_left t1

/-- Summability of the weighted stage costs `λ_k B_k^{2C}`. -/
lemma alt_summable_weight (A : ℕ) (hA : 1 ≤ A) (C : ℝ) (_hC : 0 < C) :
    Summable (fun k : ℕ => lam A k * ((((A : ℝ) + 1) * (k + 1) + 30) ^ C) ^ 2) := by
  set n := ⌈C⌉₊
  set c : ℝ := ((A : ℝ) + 31) ^ (2 * n)
  have hg : Summable (fun m : ℕ => (m : ℝ) ^ (2 * n) * ((2 : ℝ)⁻¹) ^ m) :=
    summable_pow_mul_geometric_of_norm_lt_one (2 * n)
      (by rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]; norm_num)
  have hg1 : Summable (fun k : ℕ => c * (((k : ℝ) + 1) ^ (2 * n) * ((2 : ℝ)⁻¹) ^ (k + 1))) := by
    have := (summable_nat_add_iff 1).2 hg
    refine (this.mul_left c).congr fun k => ?_
    push_cast; ring
  refine Summable.of_nonneg_of_le (fun k => by have := lam_pos A k; positivity) (fun k => ?_) hg1
  have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  set B : ℝ := ((A : ℝ) + 1) * (k + 1) + 30 with hB
  have hB1 : 1 ≤ B := by rw [hB]; nlinarith
  have hBle : B ≤ ((A : ℝ) + 31) * ((k : ℝ) + 1) := by rw [hB]; nlinarith
  have h1 : B ^ C ≤ B ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le hB1 (Nat.le_ceil C)
  rw [Real.rpow_natCast] at h1
  have h2 : B ^ n ≤ (((A : ℝ) + 31) * ((k : ℝ) + 1)) ^ n :=
    pow_le_pow_left₀ (by linarith) hBle n
  have h3 : (B ^ C) ^ 2 ≤ ((((A : ℝ) + 31) * ((k : ℝ) + 1)) ^ n) ^ 2 :=
    pow_le_pow_left₀ (Real.rpow_nonneg (by linarith) C) (h1.trans h2) 2
  have e3 : ((((A : ℝ) + 31) * ((k : ℝ) + 1)) ^ n) ^ 2 = c * ((k : ℝ) + 1) ^ (2 * n) := by
    rw [← pow_mul, mul_pow, mul_comm n 2]
  have hlam := lam_le A hA k
  calc lam A k * (B ^ C) ^ 2 ≤ (2 : ℝ)⁻¹ ^ (k + 1) * (c * ((k : ℝ) + 1) ^ (2 * n)) := by
        rw [← e3]
        exact mul_le_mul hlam h3 (by positivity) (by positivity)
    _ = _ := by ring

/-- Eventually `(log log log N)^{2C} ≤ √N`. -/
lemma alt_eventually_small (C : ℝ) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop, 32 ≤ N ∧
      (Real.log (Real.log (Real.log (N : ℝ))) ^ C) ^ 2 ≤ Real.sqrt N := by
  have ho := (isLittleO_log_rpow_rpow_atTop C (show (0 : ℝ) < 1 / 4 by norm_num)).bound one_pos
  have ho' := tendsto_natCast_atTop_atTop.eventually ho
  filter_upwards [ho', eventually_ge_atTop 32] with N hN h32
  refine ⟨h32, ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLpos := alt_lll_pos N h32
  have hlog := alt_log_gt_three N h32
  have hle := alt_lll_le_log N h32
  simp only [one_mul, Real.norm_eq_abs] at hN
  rw [abs_of_nonneg (Real.rpow_nonneg (by linarith) C),
    abs_of_nonneg (Real.rpow_nonneg hNpos.le _)] at hN
  have h1 : Real.log (Real.log (Real.log (N : ℝ))) ^ C ≤ (N : ℝ) ^ (1 / 4 : ℝ) :=
    (Real.rpow_le_rpow hLpos.le hle hC.le).trans hN
  have h2 := pow_le_pow_left₀ (Real.rpow_nonneg hLpos.le C) h1 2
  refine h2.trans (le_of_eq ?_)
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
  norm_num

lemma tail_asymp (C : ℝ) (hC : 0 < C) : ∃ A₀ : ℕ, ∀ A : ℕ, A₀ ≤ A → ∀ E : ℕ → ℕ,
    (∀ k, Real.log (Real.log (Real.log ((2 : ℝ) ^ (2 * E k)))) ≤ ((A : ℝ) + 1) * (k + 1) + 30) →
    ∀ C₁ : ℝ, 0 ≤ C₁ → ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ N : ℕ in atTop,
      Real.sqrt (C₁ * ∑' k, lam A k * min 1 ((2 : ℝ) ^ E k / N)) ≤
        K * (1 / (Real.log (Real.log (Real.log N))) ^ C) := by
  refine ⟨1, fun A hA E hE C₁ hC₁ => ?_⟩
  set w : ℕ → ℝ := fun k => lam A k * ((((A : ℝ) + 1) * (k + 1) + 30) ^ C) ^ 2 with hw
  have hws : Summable w := alt_summable_weight A hA C hC
  set W := ∑' k, w k
  have hW0 : 0 ≤ W := tsum_nonneg fun k => by
    have := lam_pos A k; simp only [hw]; positivity
  refine ⟨Real.sqrt (C₁ * (1 + W)), Real.sqrt_nonneg _, ?_⟩
  filter_upwards [alt_eventually_small C hC] with N ⟨hN, hsmall⟩
  set L := Real.log (Real.log (Real.log (N : ℝ))) with hL
  have hLpos : 0 < L := alt_lll_pos N hN
  have hu : 0 < L ^ C := Real.rpow_pos_of_pos hLpos C
  have hu2 : 0 < (L ^ C) ^ 2 := by positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hlamS := summable_lam A hA
  have hfS : Summable (fun k => lam A k * min 1 ((2 : ℝ) ^ E k / N)) := by
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hlamS
    · have := lam_pos A k
      have : 0 ≤ min 1 ((2 : ℝ) ^ E k / N) := le_min zero_le_one (by positivity)
      positivity
    · exact mul_le_of_le_one_right (lam_pos A k).le (min_le_left _ _)
  have hS : ∑' k, lam A k * min 1 ((2 : ℝ) ^ E k / N) ≤ (1 + W) / (L ^ C) ^ 2 := by
    have hsum := (hlamS.div_const (Real.sqrt N)).add (hws.div_const ((L ^ C) ^ 2))
    calc ∑' k, lam A k * min 1 ((2 : ℝ) ^ E k / N)
        ≤ ∑' k, (lam A k / Real.sqrt N + w k / (L ^ C) ^ 2) :=
          Summable.tsum_mono hfS hsum fun k => alt_term_bound A C hC (E k) k (hE k) N hN
      _ = (∑' k, lam A k) / Real.sqrt N + W / (L ^ C) ^ 2 := by
          rw [Summable.tsum_add (hlamS.div_const _) (hws.div_const _), tsum_div_const,
            tsum_div_const]
      _ ≤ 1 / Real.sqrt N + W / (L ^ C) ^ 2 := by
          gcongr
          exact tsum_lam_le_one A hA
      _ ≤ 1 / (L ^ C) ^ 2 + W / (L ^ C) ^ 2 := by
          gcongr
      _ = (1 + W) / (L ^ C) ^ 2 := by ring
  calc Real.sqrt (C₁ * ∑' k, lam A k * min 1 ((2 : ℝ) ^ E k / N))
      ≤ Real.sqrt (C₁ * ((1 + W) / (L ^ C) ^ 2)) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hS hC₁)
    _ = Real.sqrt (C₁ * (1 + W)) * (1 / L ^ C) := by
        rw [← mul_div_assoc, Real.sqrt_div' _ hu2.le, Real.sqrt_sq hu.le, mul_one_div]

end Asm
end OMA.Port23

/- ### Assembly -/

/-!
Section: Erdős 996: global assembly (gaps G4, G5, G6)

The counterexample is the explicit construction of `Parts/Asm/Construction.lean` with the
parameter `A` supplied by `tail_asymp`.
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace OMA.Port23


open Asm in
/-- The pointwise counterexample: a mean-zero `g ∈ L²` (given pointwise, as an a.e. limit of
blocks), a dyadic lacunary `n`, the Fourier-tail bound for the `L²` class of `g`, and a set of
positive measure on which the averages are `≥ δ > 0` infinitely often. -/
theorem exists_pointwise_counterexample (C : ℝ) (hC : 0 < C) :
    ∃ (f : Lp ℂ 2 (haarAddCircle (T := 1))) (n : ℕ → ℕ) (δ : ℝ), 0 < δ ∧ IsDyadicLacunary n ∧
      FourierTailBound C f ∧ ∫ t, f t ∂(haarAddCircle (T := 1)) = 0 ∧
      0 < (haarAddCircle (T := 1)) {x | ∃ᶠ N in atTop, δ ≤ ‖(∑ k ∈ range N, f (n k • x)) / (N : ℂ)‖} := by
  obtain ⟨A₀, hA₀⟩ := tail_asymp C hC
  set A : ℕ := max A₀ 1 with hAdef
  have hA : 1 ≤ A := le_max_right _ _
  have hmem := memLp_gFun A hA
  set f : Lp ℂ 2 (haarAddCircle (T := 1)) := hmem.toLp _ with hfdef
  have hfg : (f : (AddCircle (1 : ℝ)) → ℂ) =ᵐ[(haarAddCircle (T := 1))] fun x => (gFun A x : ℂ) := hmem.coeFn_toLp
  refine ⟨f, nSeq A, 1, one_pos, isDyadicLacunary_nSeq A, ?_, ?_, ?_⟩
  · -- G5: the Fourier tail bound
    obtain ⟨C₁, hC₁, htail⟩ := tail_sum_le
    obtain ⟨K, hK, hev⟩ := hA₀ A (le_max_left _ _) (logQ A) (scale_bound A hA) C₁ hC₁.le
    have hcoef : fourierCoeff (⇑f) = fourierCoeff (fun x => (gFun A x : ℂ)) :=
      fourierCoeff_congr_ae hfg
    unfold FourierTailBound
    refine IsBigO.of_bound K ?_
    filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    have hsq := eLpNorm_sub_fourierPartial_sq f N
    rw [hcoef] at hsq
    calc (eLpNorm (⇑f - fourierPartial f N) 2 (haarAddCircle (T := 1))).toReal
        = Real.sqrt ((eLpNorm (⇑f - fourierPartial f N) 2 (haarAddCircle (T := 1))).toReal ^ 2) :=
          (Real.sqrt_sq ENNReal.toReal_nonneg).symm
      _ ≤ Real.sqrt (C₁ * ∑' k, lam A k * min 1 ((2 : ℝ) ^ logQ A k / N)) := by
          rw [hsq]; exact Real.sqrt_le_sqrt (htail A hA N hN1)
      _ ≤ K * (1 / (Real.log (Real.log (Real.log N))) ^ C) := hN
      _ ≤ K * ‖1 / (Real.log (Real.log (Real.log N))) ^ C‖ :=
          mul_le_mul_of_nonneg_left (Real.le_norm_self _) hK
  · -- mean zero
    rw [integral_congr_ae hfg]
    exact integral_gFun A hA
  · -- G6: positive measure
    have hall : ∀ᵐ x ∂(haarAddCircle (T := 1)), ∀ j, gPos A (nSeq A j • x) ≠ ∞ ∧
        f (nSeq A j • x) = (gFun A (nSeq A j • x) : ℂ) :=
      ae_forall_nSeq A (P := fun y => gPos A y ≠ ∞ ∧ f y = (gFun A y : ℂ))
        (by filter_upwards [ae_gPos_ne_top A hA, hfg] with y h1 h2 using ⟨h1, h2⟩)
    set G : Set (AddCircle (1 : ℝ)) := {x | ∀ j, gPos A (nSeq A j • x) ≠ ∞ ∧
        f (nSeq A j • x) = (gFun A (nSeq A j • x) : ℂ)} with hGdef
    have hGc : (haarAddCircle (T := 1)) Gᶜ = 0 := mem_ae_iff.1 hall
    have hsub : (⋂ k, stageGood A k) ∩ G ⊆
        {x | ∃ᶠ N in atTop, (1 : ℝ) ≤ ‖(∑ k ∈ range N, f (nSeq A k • x)) / (N : ℂ)‖} := by
      rintro x ⟨hx, hxG⟩
      simp only [Set.mem_ofPred_eq]
      refine frequently_atTop.2 fun a => ?_
      have hxa : x ∈ stageGood A a := Set.mem_iInter.1 hx a
      simp only [stageGood] at hxa
      obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.1 hxa
      obtain ⟨N, hsN, hN⟩ := master_trial A hA x s (fun j => (hxG j).1) hxs
      refine ⟨N, ?_, ?_⟩
      · have h1 := le_firstTrial A a
        have h2 := (Finset.mem_Ico.1 hs).1
        omega
      · have hsum : (∑ k ∈ range N, f (nSeq A k • x)) / (N : ℂ) =
            (((∑ j ∈ range N, gFun A (nSeq A j • x)) / N : ℝ) : ℂ) := by
          rw [Finset.sum_congr rfl fun j _ => (hxG j).2, Complex.ofReal_div,
            Complex.ofReal_sum, Complex.ofReal_natCast]
        rw [hsum, Complex.norm_real]
        exact hN.trans (Real.le_norm_self _)
    calc (0 : ℝ≥0∞) < (haarAddCircle (T := 1)) (⋂ k, stageGood A k) := measure_iInter_stageGood_pos A hA
      _ = (haarAddCircle (T := 1)) ((⋂ k, stageGood A k) ∩ G) := (measure_inter_conull hGc).symm
      _ ≤ _ := measure_mono hsub

end OMA.Port23

/- ### Main -/

/-!
Section: Erdős Problem 996 (JSP-000829): the answer is **no**

Main result: `OMA.Port23.erdos_996 : ¬ OMA.Port23Statement` (statement in `Statement.lean`).
The proof formalizes the counterexample of B. S. Ho, *Counterexamples for lacunary dilates via
dyadic spike blocks*, arXiv:2604.18535, Corollary 1.4.

The construction follows Ho (§§2–5), simplified for #996:

* only `f ∈ L²` is needed (no `Lᵖ` / Rosenthal);
* the signal height is a fixed constant `B₀` (no `B_k → ∞`), since it suffices that the averages
  exceed `B₀ - μ > 0` infinitely often on a set of positive measure;
* stage failure probabilities are made summable with total `< 1`, so a union bound replaces the
  second Borel–Cantelli lemma and no cross-stage independence is needed;
* for each fixed `C` we build a separate example, so the Fourier tail only has to beat
  `(log log log N)^{-C}` rather than the endpoint `(log log N)^{-1/2}`.

File layout: `Defs` (spikes, digit windows, blocks), `Parts/*` (G1–G3: spike bounds, Fourier support
and tail, independence of disjoint binary-digit windows, block floor, trial signal),
`Parts/Asm/*` (global construction, parameters, L² and Fourier-tail bounds, positive-measure
assembly), and this file (reduction to the literal statement).
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real

namespace OMA.Port23


/-! ### Reduction to the literal statement -/

theorem not_lacunaryAveragesConverge {f : Lp ℂ 2 (haarAddCircle (T := 1))} {n : ℕ → ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hint : ∫ t, f t ∂(haarAddCircle (T := 1)) = 0)
    (hpos : 0 < (haarAddCircle (T := 1)) {x | ∃ᶠ N in atTop, δ ≤ ‖(∑ k ∈ range N, f (n k • x)) / (N : ℂ)‖}) :
    ¬ LacunaryAveragesConverge f n := by
  intro hconv
  have h0 := ae_iff.1 hconv
  refine (ne_of_gt hpos) (measure_mono_null (fun x hx => ?_) h0)
  simp only [Set.mem_setOf_eq] at hx ⊢
  intro hlim
  rw [hint] at hlim
  have hev : ∀ᶠ N in atTop, ‖(∑ k ∈ range N, f (n k • x)) / (N : ℂ)‖ < δ := by
    have := hlim.norm
    simp only [norm_zero] at this
    exact this.eventually (gt_mem_nhds hδ)
  obtain ⟨N, hN1, hN2⟩ := (hx.and_eventually hev).exists
  exact lt_irrefl _ (hN1.trans_lt hN2)

/-- For every `C > 0` there is a counterexample. -/
theorem counterexample (C : ℝ) (hC : 0 < C) :
    ∃ (f : Lp ℂ 2 (haarAddCircle (T := 1))) (n : ℕ → ℕ), IsLacunary n ∧ FourierTailBound C f ∧
      ¬ LacunaryAveragesConverge f n := by
  obtain ⟨f, n, δ, hδ, hn, htail, hint, hpos⟩ := exists_pointwise_counterexample C hC
  exact ⟨f, n, hn.isLacunary, htail, not_lacunaryAveragesConverge hδ hint hpos⟩

/-- **Erdős Problem 996 has a negative answer.** -/
theorem erdos_996 : ¬ OMA.Port23Statement := by
  rintro ⟨C, hC, h⟩
  obtain ⟨f, n, hn, htail, hconv⟩ := counterexample C hC
  exact hconv (h f n hn htail)

end OMA.Port23

open scoped Classical

theorem OMA.disproof : ¬ (type_of% @Erdos996.erdos_996) := by
  rintro ⟨C, hC, h⟩
  refine OMA.Port23.erdos_996 ⟨C, hC, fun f n hn ht => ?_⟩
  have h1 := h f n hn ht
  have hv : (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) =
      MeasureTheory.Measure.map id (AddCircle.haarAddCircle (T := 1)) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; simp
  rw [hv, MeasureTheory.Measure.map_id] at h1
  exact h1
