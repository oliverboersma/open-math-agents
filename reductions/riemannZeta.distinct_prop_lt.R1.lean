import FormalConjectures.Paper.RiemannZetaZeros
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Distinct zeta zeros via the Montgomery–Taylor window

The analytic input retains disjoint triples in the simple critical-line block of
the pair energy. For the normalized cosine kernel and the pinching/packing method,
see O. D’Souza, *On the proportions of simple and of distinct zeros of the Riemann
zeta function*, §§2–4, 6. The slope-four clipping is the level-two instance of
K. M. Knausgård, arXiv:2610.08965, (3.3). Here the analytic estimate is required
directly on the dyadic window. The finite packing input contains no zeta data.
-/

namespace OMA.R_riemannZeta_distinct_prop_lt_R1

open ZetaZeros Filter Classical
open scoped BigOperators Topology

/-- Dyadic energy budget with disjoint three-point blocks retained in the simple
critical-line Gram matrix. The square-kernel terms are counted once per unordered
pair and discounted by a factor of four. The diagonal cost is clipped at slope four. -/
def H1 : Prop :=
  let K := fun x : ℝ =>
    (Real.sinc (Real.pi * x - 1 / Real.sqrt 2) + Real.sinc (Real.pi * x + 1 / Real.sqrt 2)) /
      (2 * Real.sinc (1 / Real.sqrt 2))
  ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop,
    ∀ Z : Finset ℂ, (Z : Set ℂ) = nontrivialZeros riemannZeta T (2 * T) →
    let m := analyticOrderNatAt riemannZeta
    let S := Z.filter fun z => z.re = 1 / 2 ∧ m z = 1
    let Y := S.image fun z => z.im * (Real.log T / (2 * Real.pi))
    ∀ (n : ℕ) (x : Fin n → Fin 3 → ℝ),
      (∀ i j, x i j ∈ Y) → Function.Injective (fun p : Fin n × Fin 3 => x p.1 p.2) →
      (∀ i j k, |x i j - x i k| ≤ 100) →
      (∑ z ∈ Z, max (2 * (m z : ℝ)) (4 * m z - 4)) - S.card +
        (∑ i, ((K (x i 0 - x i 1)) ^ 2 + (K (x i 1 - x i 2)) ^ 2 +
          (K (x i 0 - x i 2)) ^ 2)) / 4 ≤
        (montgomeryTaylorConst⁻¹ + ε) * N riemannZeta T (2 * T)

/-- Finite packing problem for the Montgomery–Taylor kernel. The points are
arbitrary real numbers in an interval of length at most four times their count. -/
def H2 : Prop :=
  let K := fun x : ℝ =>
    (Real.sinc (Real.pi * x - 1 / Real.sqrt 2) + Real.sinc (Real.pi * x + 1 / Real.sqrt 2)) /
      (2 * Real.sinc (1 / Real.sqrt 2))
  ∃ b : ℝ, 0 < b ∧ ∃ M : ℕ, ∀ (Y : Finset ℝ) (a : ℝ), M ≤ Y.card →
    (∀ y ∈ Y, a ≤ y ∧ y ≤ a + 4 * Y.card) →
    ∃ (n : ℕ) (x : Fin n → Fin 3 → ℝ),
      (∀ i j, x i j ∈ Y) ∧ Function.Injective (fun p : Fin n × Fin 3 => x p.1 p.2) ∧
      (∀ i j k, |x i j - x i k| ≤ 100) ∧ b * Y.card ≤
        (∑ i, ((K (x i 0 - x i 1)) ^ 2 + (K (x i 1 - x i 2)) ^ 2 +
          (K (x i 0 - x i 2)) ^ 2)) / 4

/-- A coarse dyadic Riemann–von Mangoldt estimate for the available length
in normalized height coordinates. -/
def H3 : Prop :=
  ∀ B : ℝ, ∀ᶠ T : ℝ in atTop, B ≤ N riemannZeta T (2 * T) ∧
    T * (Real.log T / (2 * Real.pi)) ≤ 3 / 2 * N riemannZeta T (2 * T)

lemma finite_window {T : ℝ} (hT : 0 < T) :
    (nontrivialZeros riemannZeta T (2 * T)).Finite := by
  apply ((Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1 + 2 * T)).finite_riemannZeta_zeros).subset
  intro z hz
  obtain ⟨hz0, hr0, hr1, hi0, hi1⟩ := hz
  refine ⟨?_, hz0⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have h := Complex.norm_le_abs_re_add_abs_im z
  rw [abs_of_pos hr0, abs_of_pos (hT.trans hi0)] at h
  linarith

/-- Pointwise, the clipped cost is 3m - 2 + |m - 2|. At each marked
simple zero the absolute-value term cancels the unit simple-zero discount. -/
lemma clipped_counts {α : Type*} (Z : Finset α) (m : α → ℕ) (mark : α → Prop)
    [DecidablePred mark] (hm : ∀ z ∈ Z, mark z → m z = 1) :
    let W := ∑ z ∈ Z, (m z : ℝ)
    let Q := ∑ z ∈ Z, max (2 * (m z : ℝ)) (4 * m z - 4)
    2 * W ≤ Q ∧ 3 * W - 2 * Z.card + (Z.filter mark).card ≤ Q := by
  classical
  dsimp only
  constructor
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun z _ => le_max_left _ _
  · have key := Finset.sum_le_sum (s := Z) (f := fun z => 3 * (m z : ℝ) - 2 +
        (if mark z then (1 : ℝ) else 0))
        (g := fun z => max (2 * (m z : ℝ)) (4 * m z - 4)) (by
          intro z hz
          by_cases h : mark z
          · norm_num [h, hm z hz h]
          · simp only [h, if_false, add_zero]
            linarith [le_max_left (2 * (m z : ℝ)) (4 * m z - 4),
              le_max_right (2 * (m z : ℝ)) (4 * m z - 4)])
    simpa [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_boole, mul_comm (↑Z.card : ℝ) 2] using key

lemma inv_constant_bound : montgomeryTaylorConst⁻¹ ≤ (3 : ℝ) / 2 := by
  have hs : 0 < Real.sqrt 2 := by positivity
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs1 : 1 < Real.sqrt 2 := by nlinarith
  have ht := Real.lt_tan (show 0 < 1 / Real.sqrt 2 by positivity)
    (show 1 / Real.sqrt 2 < Real.pi / 2 by
      have : 1 / Real.sqrt 2 < 1 := (div_lt_one hs).2 hs1
      linarith [Real.pi_gt_three])
  have hp : 0 < Real.tan (1 / Real.sqrt 2) := lt_trans (by positivity) ht
  unfold montgomeryTaylorConst
  rw [inv_div]
  apply (div_le_iff₀ (mul_pos hs hp)).2
  have hmul := (div_lt_iff₀ hs).mp ht
  field_simp
  nlinarith [show Real.sqrt 2 ≤ 2 * Real.tan (1 / Real.sqrt 2) by
    nlinarith [mul_lt_mul_of_pos_right hmul hs,
      mul_eq_zero_of_left (sub_eq_zero.mpr hs2) (Real.tan (1 / Real.sqrt 2))]]

theorem main : H1 → H2 → H3 → type_of% @riemannZeta.distinct_prop_lt := by
  classical
  intro budget packing density
  obtain ⟨b, hb, M, pack⟩ := packing
  let ε := min (1 / 10 : ℝ) (b / 10)
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hsmall : ε ≤ 1 / 10 := min_le_left _ _
  have hgain : ε ≤ b / 10 := min_le_right _ _
  let c := (3 - montgomeryTaylorConst⁻¹) / 2 + b / 10
  have eventual : ∀ᶠ T : ℝ in atTop, c * N riemannZeta T (2 * T) ≤ Nd riemannZeta T (2 * T) := by
    filter_upwards [budget ε hε, density (3 * M), eventually_gt_atTop (1 : ℝ)] with T hE hD hT
    let Z := (finite_window (show 0 < T by linarith)).toFinset
    have hZ : (Z : Set ℂ) = nontrivialZeros riemannZeta T (2 * T) := Set.Finite.coe_toFinset _
    let m := analyticOrderNatAt riemannZeta
    let S := Z.filter fun z => z.re = 1 / 2 ∧ m z = 1
    let L := Real.log T / (2 * Real.pi)
    let Y := S.image fun z => z.im * L
    let W : ℝ := N riemannZeta T (2 * T)
    have hW : (∑ z ∈ Z, (m z : ℝ)) = W := by
      dsimp only [W, N, Complex.zeroCountOn, m]
      rw [← hZ, finsum_mem_coe_finset, Nat.cast_sum]
    have hNd : Nd riemannZeta T (2 * T) = Z.card := by simp [Nd, ← hZ]
    have hL : 0 < L := div_pos (Real.log_pos hT) (by positivity)
    have hYS : Y.card = S.card := by
      apply Finset.card_image_of_injOn
      intro z hz w hw he
      apply Complex.ext
      · exact (Finset.mem_filter.mp hz).2.1.trans (Finset.mem_filter.mp hw).2.1.symm
      · exact mul_right_cancel₀ hL.ne' he
    obtain ⟨hbase, hcount⟩ := clipped_counts Z m (fun z => z.re = 1 / 2 ∧ m z = 1)
      (fun _ _ h => h.2)
    rw [hW] at hbase hcount
    change 3 * W - 2 * Z.card + S.card ≤ _ at hcount
    have src := hE Z hZ
    have empty := src 0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
      (fun p => Fin.elim0 p.1) (fun i => Fin.elim0 i)
    simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_div, add_zero] at empty
    change _ - (S.card : ℝ) ≤ (montgomeryTaylorConst⁻¹ + ε) * W at empty
    have hW0 : 0 ≤ W := Nat.cast_nonneg _
    have hscale := mul_le_mul_of_nonneg_right (add_le_add inv_constant_bound hsmall) hW0
    have hS : 2 / 5 * W ≤ S.card := by linarith
    have hM : (3 : ℝ) * M ≤ W := hD.1
    have hsize : M ≤ Y.card := by
      rw [hYS]
      exact_mod_cast (show (M : ℝ) ≤ S.card by linarith [Nat.cast_nonneg (α := ℝ) M])
    obtain ⟨n, x, hx, hi, hd, hk⟩ := pack Y (T * L) hsize (by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      have hzZ : z ∈ (Z : Set ℂ) := (Finset.mem_filter.mp hz).1
      rw [hZ] at hzZ
      obtain ⟨_, _, _, hlo, hhi⟩ := hzZ
      have hlen : T * L ≤ 3 / 2 * W := hD.2
      rw [hYS]
      constructor
      · exact mul_le_mul_of_nonneg_right hlo.le hL.le
      · linarith [mul_le_mul_of_nonneg_right hhi hL.le])
    have hfull := src n x hx hi hd
    rw [hYS] at hk
    have hbonus := mul_le_mul_of_nonneg_left hS hb.le
    have herr := mul_le_mul_of_nonneg_right hgain hW0
    rw [hNd]
    change c * W ≤ (Z.card : ℝ)
    dsimp only [c]
    change _ - (S.card : ℝ) + _ ≤ (montgomeryTaylorConst⁻¹ + ε) * W at hfull
    linarith
  refine ⟨c, by dsimp [c]; linarith, fun T => if c * N riemannZeta T (2 * T) ≤
    Nd riemannZeta T (2 * T) then 0 else c, ?_, ?_⟩
  · apply (Asymptotics.isLittleO_one_iff ℝ).2
    apply tendsto_const_nhds.congr'
    filter_upwards [eventual] with T h using (if_pos h).symm
  · intro T _
    dsimp only
    split_ifs with h
    · simpa using h
    · simp

end OMA.R_riemannZeta_distinct_prop_lt_R1
