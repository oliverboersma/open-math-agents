
import FormalConjectures.ErdosProblems.«996»
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Dyadic control of the lacunary Fourier averages -/

open scoped BigOperators
open MeasureTheory

namespace Lacunary996

variable {G : Type*} [NormedAddCommGroup G]

private def blockSum (g : ℕ → G) (a m : ℕ) : G :=
  ∑ k ∈ Finset.range m, g (a + k)

private theorem blockSum_split (g : ℕ → G) (a m h : ℕ) :
    blockSum g a (m+h) = blockSum g a m + blockSum g (a+m) h := by
  simp only [blockSum, Finset.sum_range_add, Nat.add_assoc]

private def dyadicEnergy (g : ℕ → G) : ℕ → ℕ → ℝ
  | 0, a => ‖g a‖^2
  | j+1, a => ‖blockSum g a (2^(j+1))‖^2 +
      dyadicEnergy g j a + dyadicEnergy g j (a + 2^j)

private theorem dyadicEnergy_nonneg (g : ℕ → G) (j a : ℕ) :
    0 ≤ dyadicEnergy g j a := by
  induction j generalizing a with
  | zero => exact sq_nonneg _
  | succ j ih =>
    exact add_nonneg (add_nonneg (sq_nonneg _) (ih a)) (ih (a + 2^j))

private theorem full_le_energy (g : ℕ → G) (j a : ℕ) :
    ‖blockSum g a (2^j)‖^2 ≤ dyadicEnergy g j a := by
  cases j with
  | zero => simp [dyadicEnergy, blockSum]
  | succ j =>
    have := dyadicEnergy_nonneg g j a
    have := dyadicEnergy_nonneg g j (a + 2^j)
    simp only [dyadicEnergy]
    linarith

private theorem sq_add_le_scaled {x y S T d : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hS : 0 ≤ S) (hT : 0 ≤ T) (hd : 0 ≤ d) (h1 : x^2 ≤ S) (h2 : y^2 ≤ d*T) :
    (x+y)^2 ≤ (d+1)*(S+T) := by
  have hx' : x ≤ Real.sqrt S := Real.le_sqrt_of_sq_le h1
  have hy' : y ≤ Real.sqrt d * Real.sqrt T := by
    rw [← Real.sqrt_mul hd]
    exact Real.le_sqrt_of_sq_le h2
  calc
    (x+y)^2 ≤ (Real.sqrt S + Real.sqrt d * Real.sqrt T)^2 :=
      pow_le_pow_left₀ (add_nonneg hx hy) (add_le_add hx' hy') 2
    _ ≤ (Real.sqrt S + Real.sqrt d * Real.sqrt T)^2 +
        (Real.sqrt d * Real.sqrt S - Real.sqrt T)^2 := le_add_of_nonneg_right (sq_nonneg _)
    _ = (1+(Real.sqrt d)^2)*((Real.sqrt S)^2 + (Real.sqrt T)^2) := by ring
    _ = (d+1)*(S+T) := by rw [Real.sq_sqrt hd, Real.sq_sqrt hS, Real.sq_sqrt hT, add_comm 1 d]

/-- At most one block from each dyadic scale is needed for a prefix. -/
theorem prefix_sq_le_energy (g : ℕ → G) (j a m : ℕ) (hm : m ≤ 2^j) :
    ‖blockSum g a m‖^2 ≤ ((j : ℝ) + 1) * dyadicEnergy g j a := by
  induction j generalizing a m with
  | zero =>
    have hm' : m = 0 ∨ m = 1 := by
      have : m ≤ 1 := hm
      omega
    rcases hm' with rfl | rfl <;> simp [blockSum, dyadicEnergy]
  | succ j ih =>
    have hleft := dyadicEnergy_nonneg g j a
    have hright := dyadicEnergy_nonneg g j (a + 2^j)
    by_cases hhalf : m ≤ 2^j
    · calc
        _ ≤ ((j : ℝ) + 1) * dyadicEnergy g j a := ih a m hhalf
        _ ≤ ((j.succ : ℝ) + 1) * dyadicEnergy g j.succ a := by
          apply mul_le_mul
          · simp
          · dsimp [dyadicEnergy]
            linarith [sq_nonneg ‖blockSum g a (2^(j+1))‖]
          · exact hleft
          · positivity
    · let m' := m - 2^j
      have hm' : m' ≤ 2^j := by
        rw [pow_succ] at hm
        dsimp [m']
        omega
      have heq : m = 2^j + m' := by dsimp [m']; omega
      rw [heq, blockSum_split]
      calc
        _ ≤ (‖blockSum g a (2^j)‖ + ‖blockSum g (a+2^j) m'‖)^2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
        _ ≤ (((j : ℝ) + 1) + 1) *
            (dyadicEnergy g j a + dyadicEnergy g j (a+2^j)) :=
          sq_add_le_scaled (norm_nonneg _) (norm_nonneg _) hleft hright (by positivity)
            (full_le_energy g j a) (ih (a+2^j) m' hm')
        _ ≤ ((j.succ : ℝ)+1) * dyadicEnergy g j.succ a := by
          rw [Nat.cast_succ]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          dsimp [dyadicEnergy]
          linarith [sq_nonneg ‖blockSum g a (2^(j+1))‖]

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem dyadic_integrable (g : ℕ → X → G)
    (h : ∀ a m, Integrable (fun x => ‖blockSum (fun k => g k x) a m‖^2) μ)
    (j a : ℕ) : Integrable (fun x => dyadicEnergy (fun k => g k x) j a) μ := by
  induction j generalizing a with
  | zero => simpa [dyadicEnergy, blockSum] using h a 1
  | succ j ih =>
    exact (((h a (2^(j+1))).add (ih a)).add (ih (a+2^j))).congr
      (Filter.Eventually.of_forall fun _ => rfl)

/-- The interval lengths on each dyadic level sum to the length of the original interval. -/
theorem integral_energy_le (g : ℕ → X → G)
    (hint : ∀ a m, Integrable (fun x => ‖blockSum (fun k => g k x) a m‖^2) μ)
    {K : ℝ} (hbound : ∀ a m, (∫ x, ‖blockSum (fun k => g k x) a m‖^2 ∂μ) ≤ K * m)
    (j a : ℕ) :
    (∫ x, dyadicEnergy (fun k => g k x) j a ∂μ) ≤ ((j : ℝ) + 1) * K * (2:ℝ)^j := by
  induction j generalizing a with
  | zero => simpa [dyadicEnergy, blockSum] using hbound a 1
  | succ j ih =>
    let f (x : X) := ‖blockSum (fun k => g k x) a (2^(j+1))‖^2
    let l (x : X) := dyadicEnergy (fun k => g k x) j a
    let r (x : X) := dyadicEnergy (fun k => g k x) j (a+2^j)
    have hf : Integrable f μ := hint a _
    have hl : Integrable l μ := dyadic_integrable g hint j a
    have hr : Integrable r μ := dyadic_integrable g hint j (a+2^j)
    change (∫ x, ((f+l)+r) x ∂μ) ≤ _
    rw [integral_add' (hf.add hl) hr, integral_add' hf hl]
    calc
      _ ≤ K * (↑(2^(j+1) : ℕ) : ℝ) + (((j:ℝ)+1)*K*2^j) + (((j:ℝ)+1)*K*2^j) :=
        add_le_add (add_le_add (hbound a (2^(j+1))) (ih a)) (ih (a+2^j))
      _ = _ := by push_cast; rw [pow_succ]; ring

end Lacunary996


namespace Lacunary996

open scoped BigOperators

private theorem interval_error_sq_le (u v : ℕ → ℂ) {m M : ℕ} (h : m ≤ M) :
    ‖blockSum (fun i => u i - v i) 0 m‖^2 ≤
      (M : ℝ) * ∑ i ∈ Finset.range M, ‖u i - v i‖^2 := by
  let g := fun i => ‖u i - v i‖
  have hnorm : ‖blockSum (fun i => u i - v i) 0 m‖ ≤ ∑ i ∈ Finset.range m, g i := by
    simpa [blockSum, g] using norm_sum_le (Finset.range m) (fun i => u i - v i)
  calc
    _ ≤ (∑ i ∈ Finset.range m, g i)^2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ (m : ℝ) * ∑ i ∈ Finset.range m, g i ^ 2 := by
      simpa using sq_sum_le_card_mul_sum_sq (s := Finset.range m) (f := g)
    _ ≤ _ := by
      apply mul_le_mul (by exact_mod_cast h) _ (by positivity) (by positivity)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) (fun i _ _ => sq_nonneg _)

private theorem norm_sq_add_le (x y : ℂ) : ‖x+y‖^2 ≤ 2 * (‖x‖^2 + ‖y‖^2) := by
  have h := pow_le_pow_left₀ (norm_nonneg (x+y)) (norm_add_le x y) 2
  nlinarith only [h, sq_nonneg (‖x‖-‖y‖)]

/-- The uniform mean-square bound on a dyadic window separates interval covariance and truncation. -/
theorem prefix_mean_sq_bound (u v : ℕ → ℂ) {j m N : ℕ} (hN : 0 < N)
    (hm : m ≤ 2^j) (hn : N ≤ m) :
    ‖blockSum u 0 m / (m : ℂ)‖^2 ≤
      2 * ( ( ((j:ℝ)+1) * dyadicEnergy v j 0 +
          ((2:ℝ)^j) * ∑ i ∈ Finset.range (2^j), ‖u i - v i‖^2 ) / (N:ℝ)^2 ) := by
  have hdecomp : blockSum u 0 m =
      blockSum v 0 m + blockSum (fun i => u i - v i) 0 m := by
    simp only [blockSum, Finset.sum_sub_distrib]
    abel
  rw [norm_div, norm_natCast, div_pow]
  have htotal := norm_sq_add_le (blockSum v 0 m) (blockSum (fun i => u i - v i) 0 m)
  rw [← hdecomp] at htotal
  have hp := prefix_sq_le_energy v j 0 m hm
  have he := interval_error_sq_le u v hm
  push_cast at he
  have hn' : (N:ℝ)^2 ≤ (m:ℝ)^2 :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast hn) 2
  calc
    _ ≤ ‖blockSum u 0 m‖^2 / (N:ℝ)^2 :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hn'
    _ ≤ (2 * (‖blockSum v 0 m‖^2 + ‖blockSum (fun i => u i - v i) 0 m‖^2)) /
        (N:ℝ)^2 := div_le_div_of_nonneg_right htotal (by positivity)
    _ ≤ _ := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add hp he) (by norm_num))
        (by positivity)

end Lacunary996

open Filter MeasureTheory
open scoped ENNReal BigOperators Topology

namespace Lacunary996

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The terms of a nonnegative series tend to zero almost everywhere if the integrals are summable. -/
theorem ae_tendsto_of_summable_integrals (s : ℕ → X → ℝ)
    (hn : ∀ j x, 0 ≤ s j x) (hs : ∀ j, Integrable (s j) μ)
    (h : Summable fun j => ∫ x, s j x ∂μ) :
    ∀ᵐ x ∂μ, Tendsto (fun j => s j x) atTop (𝓝 0) := by
  let S (j : ℕ) (x : X) := ENNReal.ofReal (s j x)
  have hmeas (j : ℕ) : AEMeasurable (S j) μ := (hs j).aemeasurable.ennreal_ofReal
  have hfinite : (∫⁻ x, ∑' j, S j x ∂μ) ≠ ⊤ := by
    rw [lintegral_tsum hmeas]
    have heq (j : ℕ) : (∫⁻ x, S j x ∂μ) = ENNReal.ofReal (∫ x, s j x ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal (hs j) (ae_of_all _ (hn j))).symm
    simp_rw [heq]
    exact h.tsum_ofReal_lt_top.ne
  filter_upwards [ae_lt_top' (AEMeasurable.tsum hmeas) hfinite] with x hx
  have hsum := ENNReal.summable_toReal hx.ne
  have hs' : Summable (fun j => s j x) := by
    simpa only [S, ENNReal.toReal_ofReal (hn _ _)] using hsum
  exact hs'.tendsto_atTop_zero

/-- Convergence of uniform bounds on successive dyadic ranges implies convergence of the sequence. -/
theorem tendsto_zero_of_dyadic_bounds (f : ℕ → ℂ) (b : ℕ → ℝ)
    (hb : Tendsto b atTop (𝓝 0))
    (h : ∀ j m, 2^j ≤ m → m < 2^(j+1) → ‖f m‖^2 ≤ b j) :
    Tendsto f atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨j, hj⟩ := Metric.tendsto_atTop.mp hb (ε^2) (by positivity)
  refine ⟨2^j, fun m hm => ?_⟩
  have hmpos : 0 < m := (Nat.two_pow_pos _).trans_le hm
  let k := Nat.log2 m
  have hk : 2^k ≤ m := Nat.log2_self_le hmpos.ne'
  have hmk : m < 2^(k+1) := Nat.lt_log2_self
  have hjk : j ≤ k := by
    by_contra! hlt
    have hu := Nat.pow_le_pow_right (by decide : 0 < 2) (show k+1 ≤ j by omega)
    omega
  have hnorm : ‖f m‖^2 ≤ b k := h k m hk hmk
  have hlt := hj k hjk
  rw [Real.dist_eq, sub_zero] at hlt
  rw [dist_zero_right]
  by_contra! hbad
  have hs := pow_le_pow_left₀ hε.le hbad 2
  exact (not_lt_of_ge (hs.trans (hnorm.trans (le_abs_self _)))) hlt

end Lacunary996


namespace Lacunary996

open Filter MeasureTheory
open scoped Topology

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

private def height (j : ℕ) := 2*j+2
private def firstLength (j : ℕ) := 2^(2*j)
private def lastLength (j : ℕ) := 2^height j

private theorem length_ratio (j : ℕ) : (lastLength j : ℝ) = 4*(firstLength j : ℝ) := by
  simp only [lastLength, firstLength, height, pow_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  ring

private noncomputable def covBudget (K : ℕ → ℝ) (j : ℕ) : ℝ :=
  (2/(firstLength j : ℝ)^2) * ((height j : ℝ)+1)^2 * K j * (lastLength j : ℝ)

/-- A sequence of Fourier approximants may vary between dyadic windows. -/
theorem ae_block_average_zero (f : ℕ → X → ℂ) (g : ℕ → ℕ → X → ℂ)
    (K e : ℕ → ℝ)
    (hiG : ∀ j a m, Integrable (fun x => ‖blockSum (fun k => g j k x) a m‖^2) μ)
    (hG : ∀ j a m,
      (∫ x, ‖blockSum (fun k => g j k x) a m‖^2 ∂μ) ≤ K j * m)
    (hiE : ∀ j i, Integrable (fun x => ‖f i x - g j i x‖^2) μ)
    (hE : ∀ j i, (∫ x, ‖f i x - g j i x‖^2 ∂μ) ≤ e j)
    (hKs : Summable (covBudget K)) (hEs : Summable e) :
    ∀ᵐ x ∂μ, Tendsto (fun m => blockSum (fun k => f k x) 0 m / (m : ℂ)) atTop (𝓝 0) := by
  let E (j : ℕ) (x : X) := dyadicEnergy (fun k => g j k x) (height j) 0
  let R (j : ℕ) (x : X) := ∑ i ∈ Finset.range (lastLength j), ‖f i x - g j i x‖^2
  let a (j : ℕ) := (2/((firstLength j : ℝ)^2))*((height j : ℝ)+1)
  let b (j : ℕ) := (2/((firstLength j : ℝ)^2))*(lastLength j : ℝ)
  let W (j : ℕ) (x : X) := a j * E j x + b j * R j x
  have ha (j : ℕ) : 0 ≤ a j := by dsimp [a]; positivity
  have hb (j : ℕ) : 0 ≤ b j := by dsimp [b]; positivity
  have hW (j : ℕ) (x : X) : 0 ≤ W j x :=
    add_nonneg (mul_nonneg (ha j) (dyadicEnergy_nonneg _ _ _))
      (mul_nonneg (hb j) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hei (j : ℕ) : Integrable (E j) μ := dyadic_integrable (g j) (hiG j) _ _
  have hri (j : ℕ) : Integrable (R j) μ :=
    integrable_finsetSum (Finset.range (lastLength j)) fun i _ => hiE j i
  have hiW (j : ℕ) : Integrable (W j) μ :=
    (((hei j).const_mul (a j)).add ((hri j).const_mul (b j))).congr
      (Filter.Eventually.of_forall fun _ => rfl)
  have hwi (j : ℕ) : (∫ x, W j x ∂μ) ≤ covBudget K j + 32*e j := by
    have hEint := integral_energy_le (g j) (hiG j) (hG j) (height j) 0
    have hRint : (∫ x, R j x ∂μ) ≤ (lastLength j : ℝ) * e j := by
      dsimp only [R]
      rw [integral_finsetSum _ (fun i _ => hiE j i)]
      calc
        _ ≤ ∑ _i ∈ Finset.range (lastLength j), e j := Finset.sum_le_sum fun i _ => hE j i
        _ = _ := by simp [nsmul_eq_mul]
    have hjpos : 0 < (firstLength j : ℝ) := by dsimp [firstLength]; positivity
    dsimp only [W]
    rw [integral_add ((hei j).const_mul (a j)) ((hri j).const_mul (b j)),
      integral_const_mul, integral_const_mul]
    calc
      _ ≤ a j * (((height j : ℝ)+1) * K j * (2:ℝ)^(height j)) +
          b j * ((lastLength j : ℝ) * e j) :=
        add_le_add (mul_le_mul_of_nonneg_left hEint (ha j)) (mul_le_mul_of_nonneg_left hRint (hb j))
      _ = _ := by
        have hcast : (2:ℝ)^height j = (lastLength j : ℝ) := by simp [lastLength]
        dsimp only [a,b,covBudget]
        rw [hcast]
        rw [length_ratio]
        field_simp
        ring
  have hsum : Summable (fun j => ∫ x, W j x ∂μ) :=
    Summable.of_nonneg_of_le (fun j => integral_nonneg (hW j)) hwi (hKs.add (hEs.mul_left 32))
  filter_upwards [ae_tendsto_of_summable_integrals W hW hiW hsum] with x hx
  let H (i : ℕ) := W (i/2) x
  have ht : Tendsto (fun i : ℕ => i/2) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (2*b)] with i hi
    omega
  refine tendsto_zero_of_dyadic_bounds (fun m => blockSum (fun i => f i x) 0 m / (m : ℂ))
    H (hx.comp ht) ?_
  intro i m hlo hhi
  let j := i/2
  have hjlo : 2*j ≤ i := by dsimp [j]; omega
  have hjhi : i+1 ≤ height j := by dsimp [height,j]; omega
  have hfirst : firstLength j ≤ m := (Nat.pow_le_pow_right (by decide) hjlo).trans hlo
  have hlast : m ≤ lastLength j := hhi.le.trans (Nat.pow_le_pow_right (by decide) hjhi)
  have hscale : 0 < firstLength j := Nat.two_pow_pos _
  have hineq := prefix_mean_sq_bound (fun k => f k x) (fun k => g j k x) hscale hlast hfirst
  change _ ≤ W j x
  convert hineq using 1
  have heq : (2:ℝ)^height j = (lastLength j : ℝ) := by simp [lastLength]
  dsimp only [W,a,b,E,R]
  rw [heq]
  change _ = _
  simp only [lastLength]
  ring

end Lacunary996


/- # Covariance bounds for finite blocks of lacunary averages -/

open scoped BigOperators ComplexConjugate InnerProductSpace
open Finset Filter

namespace Lacunary996

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- A fixed-width covariance band yields a linear bound on every block. -/
theorem block_norm_sq_le_of_gap (u : ℕ → G) {M : ℝ} (hM : 0 ≤ M)
    (hnorm : ∀ i, ‖u i‖ ≤ M) (D : ℕ)
    (hgap : ∀ i j, D ≤ (i-j)+(j-i) → ⟪u i, u j⟫_ℂ = 0)
    (a m : ℕ) :
    ‖∑ i ∈ range m, u (a+i)‖^2 ≤ ((2*D+1 : ℕ) : ℝ) * M^2 * m := by
  let s := range m
  have hinner :
      ‖∑ i ∈ s, u (a+i)‖ ^ 2 =
        ∑ i ∈ s, ∑ j ∈ s, (⟪u (a+i), u (a+j)⟫_ℂ).re := by
    let z := ∑ i ∈ s, u (a+i)
    have h : (⟪z, z⟫_ℂ).re = ‖z‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]
      change (((‖z‖ : ℝ) : ℂ)^2).re = _
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
    change ‖z‖ ^ 2 = _
    rw [← h, show z = ∑ i ∈ s, u (a+i) from rfl, sum_inner]
    simp_rw [inner_sum, Complex.re_sum]
  rw [hinner]
  have himplied (i : ℕ) :
      (∑ j ∈ s, (⟪u (a+i), u (a+j)⟫_ℂ).re) ≤ ((2*D+1 : ℕ) : ℝ) * M^2 := by
    classical
    let T := s.filter fun j => (i-j)+(j-i) < D
    have hin : T ⊆ Icc (i-D) (i+D) := by
      intro j hj
      have hj' := (mem_filter.mp hj).2
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    have hcard : T.card ≤ 2*D+1 := by
      have hle := card_le_card hin
      rw [Nat.card_Icc] at hle
      omega
    calc
      _ ≤ ∑ j ∈ s, if (i-j)+(j-i) < D then M^2 else 0 := by
        apply sum_le_sum
        intro j _
        split_ifs with hij
        · calc
            _ ≤ ‖⟪u (a+i), u (a+j)⟫_ℂ‖ := Complex.re_le_norm _
            _ ≤ ‖u (a+i)‖ * ‖u (a+j)‖ := norm_inner_le_norm _ _
            _ ≤ M^2 := by
              rw [pow_two]
              exact mul_le_mul (hnorm _) (hnorm _) (norm_nonneg _) hM
        · have hzero : ⟪u (a+i), u (a+j)⟫_ℂ = 0 := hgap _ _ (by omega)
          simp [hzero]
      _ = (T.card : ℝ) * M^2 := by rw [← sum_filter]; simp [T, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg _)
  calc
    ∑ i ∈ s, ∑ j ∈ s, (⟪u (a+i), u (a+j)⟫_ℂ).re
        ≤ ∑ _i ∈ s, ((2*D+1:ℕ):ℝ) * M^2 := sum_le_sum fun i _ => himplied i
    _ = _ := by simp [s, nsmul_eq_mul, mul_comm]

end Lacunary996


/- # Scales for the lacunary strong law -/

open Filter Asymptotics
open scoped Topology

namespace Lacunary996

private def cutoff (j : ℕ) : ℕ := 2 ^ (2 ^ j)

private theorem cutoff_tendsto : Tendsto cutoff atTop atTop := by
  apply StrictMono.tendsto_atTop
  intro i j hij
  exact Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.pow_lt_pow_right (by decide : 1 < 2) hij)

private theorem log_log_cutoff (j : ℕ) :
    Real.log (Real.log (cutoff j : ℝ)) = (j : ℝ) * Real.log 2 + Real.log (Real.log 2) := by
  simp only [cutoff, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]

/-- The double logarithm at the double-exponential truncations grows linearly. -/
theorem summable_cutoff_error_sq (e : ℕ → ℝ) (C : ℝ) (hC : 1/2 < C)
    (he : e =O[atTop] fun k => 1 / Real.log (Real.log k) ^ C) :
    Summable (fun j => e (cutoff j)^2) := by
  let c := Real.log 2 / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hdecay : (fun j => 1 / Real.log (Real.log (cutoff j)) ^ C) =O[atTop]
      fun j : ℕ => (j : ℝ)^(-C) := by
    apply IsBigO.of_bound (c ^ (-C))
    obtain ⟨N, hN⟩ := exists_nat_gt ((-Real.log (Real.log 2)) / c)
    filter_upwards [eventually_ge_atTop (max N 1)] with j hj
    have hjpos : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
    have hN' : (-Real.log (Real.log 2)) / c < (j : ℝ) :=
      hN.trans_le (by exact_mod_cast (show N ≤ j by omega))
    have hb := (div_lt_iff₀ hc).mp hN'
    have hscale : c * (j : ℝ) ≤ Real.log (Real.log (cutoff j)) := by
      rw [log_log_cutoff]
      dsimp [c] at *
      nlinarith only [hb]
    have hpos : 0 < Real.log (Real.log (cutoff j)) := (mul_pos hc hjpos).trans_le hscale
    have hpow : (c * (j : ℝ)) ^ C ≤ (Real.log (Real.log (cutoff j))) ^ C :=
      Real.rpow_le_rpow (mul_pos hc hjpos).le hscale (by linarith)
    have hdiv := one_div_le_one_div_of_le (Real.rpow_pos_of_pos (mul_pos hc hjpos) C) hpow
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    calc
      _ ≤ 1 / (c * (j : ℝ)) ^ C := hdiv
      _ = c ^ (-C) * (j : ℝ) ^ (-C) := by
        rw [Real.mul_rpow hc.le hjpos.le, Real.rpow_neg hc.le, Real.rpow_neg hjpos.le]
        simp [one_div, mul_inv_rev, mul_comm]
  have hs := ((he.comp_tendsto cutoff_tendsto).trans hdecay).pow 2
  have hsum : Summable (fun j : ℕ => ((j : ℝ)^(-C))^2) := by
    simp_rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    exact Real.summable_nat_rpow.mpr (by norm_num; linarith : -C * (↑(2:ℕ) : ℝ) < -1)
  exact summable_of_isBigO_nat hsum hs

private theorem iterated_gap (q : ℝ) (n : ℕ → ℕ) (hq : 0 ≤ q)
    (hn : ∀ i, q * (n i : ℝ) ≤ n (i+1)) (i gap : ℕ) :
    q^gap * (n i : ℝ) ≤ n (i+gap) := by
  induction gap with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_comm (q^k) q, mul_assoc, Nat.add_succ]
    exact (mul_le_mul_of_nonneg_left ih hq).trans (hn (i+k))

/-- A gap proportional to the logarithm of the frequency cutoff separates the spectra. -/
theorem cutoff_gap (q : ℝ) (hq : 1 < q) (n : ℕ → ℕ)
    (hpos : ∀ i, 0 < n i) (hn : ∀ i, q * (n i : ℝ) ≤ n (i+1)) :
    ∃ A : ℕ, 0 < A ∧ ∀ j i k, i + A * 2^j ≤ k → cutoff j * n i < n k := by
  obtain ⟨A, hA⟩ := pow_unbounded_of_one_lt (2 : ℝ) hq
  have hApos : 0 < A := by
    by_contra! ha
    have hzero : A = 0 := by omega
    norm_num [hzero] at hA
  refine ⟨A, hApos, fun j i k hik => ?_⟩
  have hp : ((cutoff j : ℕ):ℝ) < q^(A*2^j) := by
    simp only [cutoff, Nat.cast_pow, Nat.cast_ofNat, pow_mul]
    exact pow_lt_pow_left₀ hA (by positivity) (Nat.two_pow_pos _).ne'
  have hpow : q^(A*2^j) ≤ q^(k-i) := pow_le_pow_right₀ hq.le (by omega)
  have hbound := iterated_gap q n (by linarith) hn i (k-i)
  rw [Nat.add_sub_of_le (by omega : i ≤ k)] at hbound
  exact_mod_cast (lt_of_lt_of_le (mul_lt_mul_of_pos_right (hp.trans_le hpow)
    (by exact_mod_cast hpos i)) hbound)

end Lacunary996

/-
# Fourier truncation and dilations on the unit additive circle
-/

open MeasureTheory AddCircle Filter ContinuousMap
open scoped InnerProductSpace ComplexConjugate BigOperators

namespace LacunaryFourier

noncomputable section

abbrev UnitCircle := AddCircle (1 : ℝ)
abbrev haar : Measure UnitCircle := haarAddCircle
abbrev Space := Lp ℂ 2 haar

/-- The nonzero frequencies retained by a symmetric Fourier truncation. -/
def frequencies (K : ℕ) : Finset ℤ :=
  (Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0

/-- The pointwise Fourier truncation with its constant term removed. -/
def centered (f : Space) (K : ℕ) (x : UnitCircle) : ℂ :=
  Erdos996.fourierPartial f K x - fourierCoeff f 0

theorem centered_eq_sum (f : Space) (K : ℕ) (x : UnitCircle) :
    centered f K x = ∑ i ∈ frequencies K, fourierCoeff f i • fourier i x := by
  unfold centered Erdos996.fourierPartial frequencies
  have h0 : (0 : ℤ) ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
    simp only [Finset.mem_Icc]
    omega
  rw [← Finset.sum_erase_add _ _ h0, fourier_zero, smul_eq_mul, mul_one, add_sub_cancel_right]

/-- The dilated Fourier polynomial as a bundled continuous function. -/
def dilatedContinuous (f : Space) (K n : ℕ) : C(UnitCircle, ℂ) :=
  ∑ i ∈ frequencies K, fourierCoeff f i • fourier (i * (n : ℤ))

theorem dilatedContinuous_apply (f : Space) (K n : ℕ) (x : UnitCircle) :
    dilatedContinuous f K n x = centered f K (n • x) := by
  rw [centered_eq_sum, dilatedContinuous]
  simp [mul_zsmul, natCast_zsmul]

/-- The dilated centred Fourier polynomial viewed in L². -/
def dilateLP (f : Space) (K n : ℕ) : Space :=
  ContinuousMap.toLp 2 haar ℂ (dilatedContinuous f K n)

theorem dilateLP_eq_sum (f : Space) (K n : ℕ) :
    dilateLP f K n = ∑ i ∈ frequencies K, fourierCoeff f i • fourierLp 2 (i * (n : ℤ)) := by
  simp [dilateLP, dilatedContinuous]

theorem coe_dilateLP (f : Space) (K n : ℕ) :
    (⇑(dilateLP f K n)) =ᵐ[haar] fun x => centered f K (n • x) := by
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) haar
    (dilatedContinuous f K n)] with x hx
  exact hx.trans (dilatedContinuous_apply f K n x)

theorem measurePreserving_nsmul {n : ℕ} (hn : 0 < n) :
    MeasurePreserving (fun x : UnitCircle => n • x) haar haar := by
  simpa only [natCast_zsmul] using
    (Measure.measurePreserving_zsmul haar (n := (n : ℤ)) (by exact_mod_cast hn.ne'))

/-- Pull back an L² function by positive natural multiplication. -/
def pullback (g : Space) {n : ℕ} (hn : 0 < n) : Space :=
  Lp.compMeasurePreserving _ (measurePreserving_nsmul hn) g

theorem coe_pullback (g : Space) {n : ℕ} (hn : 0 < n) :
    (⇑(pullback g hn)) =ᵐ[haar] fun x => g (n • x) :=
  Lp.coeFn_compMeasurePreserving g (measurePreserving_nsmul hn)

theorem norm_pullback (g : Space) {n : ℕ} (hn : 0 < n) :
    ‖pullback g hn‖ = ‖g‖ :=
  Lp.norm_compMeasurePreserving g (measurePreserving_nsmul hn)

theorem norm_sq_dilateLP (f : Space) (K : ℕ) {n : ℕ} (hn : 0 < n) :
    ‖dilateLP f K n‖ ^ 2 = ∑ i ∈ frequencies K, ‖fourierCoeff f i‖ ^ 2 := by
  have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have horth : Orthonormal ℂ (fun i : ℤ => fourierLp (T := 1) 2 (i * (n : ℤ))) :=
    (orthonormal_fourier (T := 1)).comp _ (mul_left_injective₀ hnz)
  rw [dilateLP_eq_sum, InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), horth.inner_sum]
  change Complex.reCLM (∑ i ∈ frequencies K,
    (starRingEnd ℂ) (fourierCoeff f i) * fourierCoeff f i) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change ((starRingEnd ℂ) (fourierCoeff f i) * fourierCoeff f i).re = _
  rw [mul_comm, Complex.mul_conj']
  norm_cast

theorem norm_dilateLP_le (f : Space) (K : ℕ) {n : ℕ} (hn : 0 < n) :
    ‖dilateLP f K n‖ ≤ ‖f‖ := by
  have h := (orthonormal_fourier (T := 1)).sum_inner_products_le f (s := frequencies K)
  have hcoeff (i : ℤ) : ⟪fourierLp (T := 1) 2 i, f⟫_ℂ = fourierCoeff f i := by
    rw [← fourierBasis_repr, HilbertBasis.repr_apply_apply, coe_fourierBasis]
  simp_rw [hcoeff] at h
  rw [← norm_sq_dilateLP f K hn] at h
  exact le_of_pow_le_pow_left₀ (by decide : 2 ≠ 0) (norm_nonneg _) h

theorem integral_sq_eq_norm_sq (g : Space) :
    (∫ x, ‖g x‖ ^ 2 ∂haar) = ‖g‖ ^ 2 := by
  calc
    _ = ∫ x : UnitCircle, RCLike.re ⟪g x, g x⟫_ℂ ∂haar := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (g x))
    _ = RCLike.re (∫ x : UnitCircle, ⟪g x, g x⟫_ℂ ∂haar) :=
      integral_re (MeasureTheory.L2.integrable_inner g g)
    _ = _ := by
      rw [← MeasureTheory.L2.inner_def, ← InnerProductSpace.norm_sq_eq_re_inner]

private theorem frequencies_abs {K : ℕ} {i : ℤ} (hi : i ∈ frequencies K) : i.natAbs ≤ K := by
  have hrange := Finset.mem_Icc.mp (Finset.mem_erase.mp hi).2
  have hs : (i.natAbs : ℤ) ≤ (K : ℤ) := by
    rw [Int.natCast_natAbs]
    exact abs_le.mpr hrange
  exact_mod_cast hs

private theorem separate_indices {K m n : ℕ} (hmn : K * m < n)
    {i j : ℤ} (hi : i ∈ frequencies K) (hj : j ∈ frequencies K) :
    i * (m : ℤ) ≠ j * (n : ℤ) := by
  intro he
  have ha := congrArg Int.natAbs he
  rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast] at ha
  have hn : 1 ≤ j.natAbs := Int.natAbs_pos.mpr (Finset.ne_of_mem_erase hj)
  have hleft : i.natAbs * m ≤ K * m := Nat.mul_le_mul_right _ (frequencies_abs hi)
  have hright : n ≤ j.natAbs * n := by simpa using Nat.mul_le_mul_right n hn
  omega

/-- Dilated centred truncations with disjoint nonzero frequency supports
are orthogonal in L². -/
theorem inner_dilateLP_eq_zero (f g : Space) (K : ℕ) {m n : ℕ} (hmn : K * m < n) :
    ⟪dilateLP f K m, dilateLP g K n⟫_ℂ = 0 := by
  simp only [dilateLP_eq_sum, sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [(orthonormal_fourier (T := 1)).inner_eq_zero (separate_indices hmn hi hj)]
  simp

theorem fourierCoeff_zero (f : Space) : fourierCoeff f 0 = ∫ x, f x ∂haar := by
  simp [fourierCoeff]

/-- The uncentred Fourier truncation viewed in L². -/
def partialLP (f : Space) (K : ℕ) : Space :=
  ContinuousMap.toLp 2 haar ℂ (∑ i ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), fourierCoeff f i • fourier i)

theorem coe_partialLP (f : Space) (K : ℕ) :
    (⇑(partialLP f K)) =ᵐ[haar] Erdos996.fourierPartial f K := by
  unfold partialLP
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) haar
    (∑ i ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), fourierCoeff f i • fourier i)] with x hx
  simpa [Erdos996.fourierPartial] using hx

theorem norm_error_eq (f : Space) (K : ℕ) :
    ‖f - partialLP f K‖ = (eLpNorm (⇑f - Erdos996.fourierPartial f K) 2 haar).toReal := by
  rw [Lp.norm_def]
  congr 1
  apply eLpNorm_congr_ae
  filter_upwards [Lp.coeFn_sub f (partialLP f K), coe_partialLP f K] with x hx hy
  simpa only [Pi.sub_apply, hy] using hx

end

end LacunaryFourier


namespace Lacunary996

open MeasureTheory Filter LacunaryFourier
open scoped Topology InnerProductSpace BigOperators
noncomputable section

private theorem cov_budget_summable (K : ℕ → ℝ) (B : ℝ) (hK : ∀ j, 0 ≤ K j)
    (hB : ∀ j, K j ≤ B * (2:ℝ)^j) : Summable (covBudget K) := by
  have hr : ‖(1/2:ℝ)‖ < 1 := by norm_num
  have hgeo : Summable (fun j : ℕ => ((height j : ℝ)+1)^2 * (1/2:ℝ)^j) := by
    have h := (((summable_pow_mul_geometric_of_norm_lt_one 2 hr).mul_left 4).add
      ((summable_pow_mul_geometric_of_norm_lt_one 1 hr).mul_left 12)).add
      ((summable_pow_mul_geometric_of_norm_lt_one 0 hr).mul_left 9)
    refine h.congr (fun j => ?_)
    simp [height]
    ring
  refine Summable.of_nonneg_of_le (f := fun j => 8*B*((((height j : ℝ)+1)^2)*(1/2:ℝ)^j))
    (fun j => ?_) (fun j => ?_) (hgeo.mul_left _)
  · unfold covBudget
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (hK j)) (by positivity)
  · have hpos : 0 < (2:ℝ)^j := by positivity
    have hfirst : (firstLength j : ℝ) = ((2:ℝ)^j)^2 := by
      simp only [firstLength, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, Nat.mul_comm 2 j]
    calc
      covBudget K j ≤ (2 / (firstLength j : ℝ)^2) * (((height j : ℝ)+1)^2) *
          (B*(2:ℝ)^j) * (lastLength j : ℝ) := by
        dsimp only [covBudget]
        gcongr
        exact hB j
      _ = _ := by
        rw [length_ratio, hfirst]
        simp only [div_pow, one_pow]
        field_simp
        ring

set_option maxHeartbeats 700000 in
private theorem ae_positive (C : ℝ) (hC : 1/2 < C) (f : Space) (n : ℕ → ℕ)
    (q : ℝ) (hq : 1 < q) (hpos : ∀ i, 0 < n i)
    (hstep : ∀ i, q * (n i : ℝ) ≤ n (i+1))
    (hTail : (fun k => (eLpNorm (⇑f - Erdos996.fourierPartial f k) 2 haar).toReal)
      =O[atTop] fun k => 1 / Real.log (Real.log k) ^ C) :
    ∀ᵐ x ∂haar, Tendsto
      (fun m => blockSum (fun i => f (n i • x) - fourierCoeff f 0) 0 m / (m : ℂ))
      atTop (𝓝 0) := by
  obtain ⟨A, _, hgap⟩ := cutoff_gap q hq n hpos hstep
  let D (j : ℕ) := A*2^j
  let K (j : ℕ) : ℝ := ((2*D j+1:ℕ):ℝ)*‖f‖^2
  let e (j : ℕ) := ((eLpNorm (⇑f - Erdos996.fourierPartial f (cutoff j)) 2 haar).toReal)^2
  let u (i : ℕ) (x : UnitCircle) := f (n i • x) - fourierCoeff f 0
  let g (j i : ℕ) (x : UnitCircle) := centered f (cutoff j) (n i • x)
  let U (j i : ℕ) := dilateLP f (cutoff j) (n i)
  let V (j a m : ℕ) := ∑ i ∈ Finset.range m, U j (a + i)
  have hV (j a m : ℕ) : (⇑(V j a m)) =ᵐ[haar]
      fun x => blockSum (fun i => g j i x) a m := by
    have hG : ∀ᵐ x ∂haar, ∀ i : ℕ, U j i x = g j i x :=
      ae_all_iff.mpr fun i => coe_dilateLP f (cutoff j) (n i)
    filter_upwards [Lp.coeFn_finsetSum (Finset.range m) (fun i => U j (a+i)), hG] with x hx hg
    rw [show V j a m x = ∑ i ∈ Finset.range m, U j (a+i) x by
      simpa only [Finset.sum_apply] using hx]
    apply Finset.sum_congr rfl
    intro i _
    exact hg (a+i)
  have hiG (j a m : ℕ) : Integrable (fun x => ‖blockSum (fun i => g j i x) a m‖^2) haar := by
    refine (Lp.memLp (V j a m)).norm.integrable_sq.congr ?_
    filter_upwards [hV j a m] with x hx
    rw [hx]
  have hG (j a m : ℕ) : (∫ x, ‖blockSum (fun i => g j i x) a m‖^2 ∂haar) ≤ K j * m := by
    have hsq : (∫ x, ‖blockSum (fun i => g j i x) a m‖^2 ∂haar) = ‖V j a m‖^2 := by
      rw [← integral_sq_eq_norm_sq]
      apply integral_congr_ae
      filter_upwards [hV j a m] with x hx
      rw [hx]
    rw [hsq]
    refine block_norm_sq_le_of_gap (U j) (norm_nonneg _) (fun i => norm_dilateLP_le f _ (hpos i))
      (D j) ?_ a m
    intro i k h
    dsimp only [D] at h
    by_cases hik : i ≤ k
    · apply inner_dilateLP_eq_zero
      apply hgap j i k
      omega
    · apply inner_eq_zero_symm.mpr
      apply inner_dilateLP_eq_zero
      apply hgap j k i
      omega
  let W (j i : ℕ) := pullback (f - partialLP f (cutoff j)) (hpos i)
  have hW (j i : ℕ) : (⇑(W j i)) =ᵐ[haar] fun x => u i x - g j i x := by
    let Z := partialLP f (cutoff j)
    have he : (⇑(f-Z)) =ᵐ[haar] fun x => f x - Erdos996.fourierPartial f (cutoff j) x := by
      filter_upwards [Lp.coeFn_sub f Z, coe_partialLP f (cutoff j)] with x hx hz
      change Z x = Erdos996.fourierPartial f (cutoff j) x at hz
      simpa only [Pi.sub_apply, hz] using hx
    have he' := (measurePreserving_nsmul (hpos i)).quasiMeasurePreserving.ae_eq_comp he
    filter_upwards [coe_pullback (f-Z) (hpos i), he'] with x hx hx'
    have hpt : W j i x = (f-Z) (n i • x) := hx
    rw [hpt, show (f-Z) (n i • x) = f (n i • x) - Erdos996.fourierPartial f (cutoff j) (n i • x) from hx']
    simp only [u, g, centered]
    abel
  have hiE (j i : ℕ) : Integrable (fun x => ‖u i x - g j i x‖^2) haar := by
    refine (Lp.memLp (W j i)).norm.integrable_sq.congr ?_
    filter_upwards [hW j i] with x hx
    rw [hx]
  have hE (j i : ℕ) : (∫ x, ‖u i x - g j i x‖^2 ∂haar) ≤ e j := by
    calc
      _ = (∫ x, ‖W j i x‖^2 ∂haar) := by
        apply integral_congr_ae
        filter_upwards [hW j i] with x hx
        rw [hx]
      _ ≤ e j := by
        rw [integral_sq_eq_norm_sq]
        exact le_of_eq (by simp only [W, e, norm_pullback, norm_error_eq])
  have hK (j : ℕ) : K j ≤ (2*(A:ℝ)+1)*‖f‖^2*(2:ℝ)^j := by
    have hpow : 1 ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
    simp only [K, D, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_one]
    nlinarith [mul_nonneg (sub_nonneg.mpr hpow) (sq_nonneg ‖f‖)]
  have hKsum : Summable (covBudget K) :=
    cov_budget_summable K ((2*(A:ℝ)+1)*‖f‖^2) (fun j => by dsimp [K]; positivity) hK
  have heSum : Summable e :=
    summable_cutoff_error_sq (fun k => (eLpNorm (⇑f - Erdos996.fourierPartial f k) 2 haar).toReal)
      C hC hTail
  exact ae_block_average_zero (μ := haar) u g K e hiG hG hiE hE hKsum heSum

end
end Lacunary996


namespace Lacunary996

open Filter MeasureTheory LacunaryFourier
open scoped Topology BigOperators
noncomputable section

private theorem mean_zero_of_shift (u : ℕ → ℂ) (a : ℕ)
    (h : Tendsto (fun m => blockSum (fun i => u (a+i)) 0 m / (m : ℂ)) atTop (𝓝 0)) :
    Tendsto (fun m => blockSum u 0 m / (m : ℂ)) atTop (𝓝 0) := by
  have hsub : Tendsto (fun m : ℕ => m-a) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (b+a)] with m hm
    omega
  have htail : Tendsto (fun m : ℕ => ‖blockSum u a (m-a)‖ / ((m-a:ℕ):ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def, blockSum, norm_div, norm_natCast] using (h.norm.comp hsub)
  have hbase : Tendsto (fun m : ℕ => ‖blockSum u 0 a‖ / (m:ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by simpa using hbase.add htail)
    (Filter.Eventually.of_forall (fun m => norm_nonneg _)) ?_
  filter_upwards [eventually_ge_atTop (a+1)] with m hm
  have hcut : a + (m-a) = m := by omega
  have hpos : 0 < ((m-a:ℕ):ℝ) := by exact_mod_cast (show 0 < m-a by omega)
  have hd : ((m-a:ℕ):ℝ) ≤ (m:ℝ) := by exact_mod_cast (Nat.sub_le m a)
  rw [norm_div, norm_natCast, ← show blockSum u 0 a + blockSum u a (m-a) = blockSum u 0 m by
    simpa only [Nat.zero_add, hcut] using (blockSum_split u 0 a (m-a)).symm]
  calc
    _ ≤ (‖blockSum u 0 a‖ + ‖blockSum u a (m-a)‖) / (m:ℝ) :=
      div_le_div_of_nonneg_right (norm_add_le _ _) (by positivity)
    _ = ‖blockSum u 0 a‖ / (m:ℝ) + ‖blockSum u a (m-a)‖ / (m:ℝ) := add_div _ _ _
    _ ≤ _ := add_le_add le_rfl (div_le_div_of_nonneg_left (norm_nonneg (blockSum u a (m-a))) hpos hd)

end
end Lacunary996

open Lacunary996 LacunaryFourier Filter MeasureTheory

/-- Matsuyama's lacunary strong law with a double-logarithmic Fourier-tail bound.
Tohoku Mathematical Journal 18 (1966), 259–269. -/
theorem OMA.solution : type_of% @Erdos996.erdos_996.variants.log2 := by
  intro C hC f n hn hTail
  obtain ⟨q, hq, hqstep⟩ := hn
  obtain ⟨a, ha⟩ := eventually_atTop.mp hqstep
  let r (i : ℕ) := n ((a+1)+i)
  have hrpos (i : ℕ) : 0 < r i := by
    have h := ha (a+i) (by omega)
    have h0 : (0:ℝ) ≤ q * (n (a+i):ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg _)
    have heq : a+i+1 = (a+1)+i := by omega
    rw [heq] at h
    exact_mod_cast h0.trans_lt h
  have hrstep (i : ℕ) : q * (r i:ℝ) ≤ r (i+1) := by
    simpa only [r, Nat.add_assoc] using (ha ((a+1)+i) (by omega)).le
  have hpos := ae_positive C (by linarith) f r q hq hrpos hrstep hTail
  have hvol : (volume : Measure UnitCircle) = haar := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
  rw [hvol]
  filter_upwards [hpos] with x hx
  let mean := fourierCoeff f 0
  have hcentered := mean_zero_of_shift (fun i => f (n i • x) - mean) (a+1) hx
  have hplus := hcentered.add (tendsto_const_nhds (x := mean))
  simp only [zero_add] at hplus
  rw [← fourierCoeff_zero f]
  apply hplus.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with m hm
  have hne : (m:ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  simp only [blockSum, Nat.zero_add, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  field_simp
  ring