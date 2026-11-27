import OMAReductions.R_Erdos969_erdos_969_variants_evelyn_linfoot_R1_H3_R1

/-!
Lean proof: Hanan Beer.
Reduction and boundary-value formulation: Erik Byrwa (@ebyrwa),
open-math-agents PR 2735.
The proof bounds differences of complex powers by their derivatives, then splits the
little-o bound into a fixed summable part and an arbitrarily small zeta tail.
-/

open Filter Topology Asymptotics

namespace AbelianBoundary

lemma power_difference_bound (s : ℂ) (hs : 0 < s.re) (x : ℝ) (hx : 0 < x) :
    ‖(x : ℂ) ^ (-s) - ((x + 1 : ℝ) : ℂ) ^ (-s)‖ ≤
      ‖s‖ * x ^ (-s.re - 1) := by
  have hs0 : -s ≠ 0 := neg_ne_zero.mpr (fun h => by simp [h] at hs)
  have hd (y : ℝ) (hy : y ∈ Set.Icc x (x + 1)) :
      HasDerivWithinAt (fun v : ℝ => (v : ℂ) ^ (-s))
        ((-s) * (y : ℂ) ^ (-s - 1)) (Set.Icc x (x + 1)) y :=
    (hasDerivAt_ofReal_cpow_const (by linarith [hy.1]) hs0).hasDerivWithinAt
  have hb (y : ℝ) (hy : y ∈ Set.Ico x (x + 1)) :
      ‖(-s) * (y : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * x ^ (-s.re - 1) := by
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith [hy.1])]
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hx hy.1 (by linarith)) (norm_nonneg s)
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hb (x + 1)
    (show x + 1 ∈ Set.Icc x (x + 1) by constructor <;> linarith)
  simpa only [norm_sub_rev, add_sub_cancel_left, mul_one] using h

lemma zeta_mass_limit :
    Tendsto (fun t : ℝ => t * ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-1 - t))
      (𝓝[>] 0) (𝓝 1) := by
  have hshift : Tendsto (fun t : ℝ => 1 + t) (𝓝[>] 0) (𝓝[>] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (tendsto_const_nhds.add (tendsto_id.mono_left nhdsWithin_le_nhds) :
        Tendsto (fun t : ℝ => 1 + t) (𝓝[>] 0) (𝓝 (1 + 0)))
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using ht
  apply (tendsto_sub_mul_tsum_nat_rpow.comp hshift).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htpos : 0 < t := ht
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-1 - t)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have heq : (∑' n : ℕ, 1 / (n : ℝ) ^ (1 + t)) =
      ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-1 - t) := by
    simp_rw [one_div, ← Real.rpow_neg (Nat.cast_nonneg _), neg_add_rev,
      show -t + -(1 : ℝ) = -1 - t by ring_nf]
    rw [hsum.tsum_eq_zero_add]
    simp [Real.zero_rpow (show -1 - t ≠ 0 by linarith)]
  simp only [Function.comp_apply, add_sub_cancel_left, heq]

lemma little_o_offset (u : ℕ → ℝ)
    (hu : (fun n => |u n|) =o[atTop] (fun n => (n : ℝ) ^ (1 / 4 : ℝ)))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |u n| ≤ C + δ * (n : ℝ) ^ (1 / 4 : ℝ) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hu.bound hδ)
  refine ⟨∑ i ∈ Finset.range N, |u i|, Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro n
  by_cases hn : n < N
  · have hle := Finset.single_le_sum (f := fun i => |u i|)
      (fun i _ => abs_nonneg (u i)) (Finset.mem_range.mpr hn)
    exact hle.trans (le_add_of_nonneg_right (by positivity))
  · have h := hN n (by omega)
    simp only [Real.norm_eq_abs, abs_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)] at h
    exact h.trans (le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => abs_nonneg _))

noncomputable def term (u : ℕ → ℝ) (z : ℂ) (t : ℝ) (n : ℕ) : ℂ :=
  (u (n + 1) : ℂ) *
    (((n + 1 : ℕ) : ℂ) ^ (-(z + t)) - ((n + 2 : ℕ) : ℂ) ^ (-(z + t)))

lemma term_bound (u : ℕ → ℝ) (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re)
    (C δ t : ℝ) (hC : 0 ≤ C) (hδ : 0 ≤ δ) (ht : 0 < t) (ht1 : t ≤ 1)
    (hu : ∀ n : ℕ, |u n| ≤ C + δ * (n : ℝ) ^ (1 / 4 : ℝ)) (n : ℕ) :
    ‖term u z t n‖ ≤ (‖z‖ + 1) *
      (C * ((n + 1 : ℕ) : ℝ) ^ (-(5 / 4 : ℝ)) +
       δ * ((n + 1 : ℕ) : ℝ) ^ (-1 - t)) := by
  let x : ℝ := n + 1
  have hx : 1 ≤ x := by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hx0 : 0 < x := by linarith
  have hzr : 0 < (z + (t : ℂ)).re := by simp only [Complex.add_re, Complex.ofReal_re]; linarith
  have hK : ‖z + (t : ℂ)‖ ≤ ‖z‖ + 1 := by
    calc ‖z + (t : ℂ)‖ ≤ ‖z‖ + ‖(t : ℂ)‖ := norm_add_le _ _
      _ ≤ ‖z‖ + 1 := by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht] using add_le_add_left ht1 ‖z‖
  have hd : ‖(x : ℂ) ^ (-(z + t)) - ((x + 1 : ℝ) : ℂ) ^ (-(z + t))‖ ≤
      (‖z‖ + 1) * x ^ (-(5 / 4 : ℝ) - t) := by
    apply (power_difference_bound (z + t) hzr x hx0).trans
    apply mul_le_mul hK ?_ (Real.rpow_nonneg hx0.le _) (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le hx
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hu' : |u (n + 1)| ≤ C + δ * x ^ (1 / 4 : ℝ) := by simpa [x] using hu (n + 1)
  have hbase : x ^ (-(5 / 4 : ℝ) - t) ≤ x ^ (-(5 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hprod : x ^ (1 / 4 : ℝ) * x ^ (-(5 / 4 : ℝ) - t) = x ^ (-1 - t) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring_nf
  have ht' : term u z t n = (u (n + 1) : ℂ) *
      ((x : ℂ) ^ (-(z + t)) - ((x + 1 : ℝ) : ℂ) ^ (-(z + t))) := by
    simp only [term, x, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Complex.ofReal_add,
      Complex.ofReal_natCast, Complex.ofReal_one]
    congr 2
    ring_nf
  rw [ht', norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hbound := mul_le_mul hu' hd (norm_nonneg _) (by positivity : 0 ≤ C + δ * x ^ (1 / 4 : ℝ))
  simp only [Nat.cast_add, Nat.cast_one]
  change |u (n + 1)| * _ ≤ (‖z‖ + 1) * (C * x ^ (-(5 / 4 : ℝ)) + δ * x ^ (-1 - t))
  calc
    _ ≤ (C + δ * x ^ (1 / 4 : ℝ)) * ((‖z‖ + 1) * x ^ (-(5 / 4 : ℝ) - t)) := hbound
    _ = (‖z‖ + 1) * (C * x ^ (-(5 / 4 : ℝ) - t) + δ * x ^ (-1 - t)) := by rw [← hprod]; ring_nf
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left hbase hC) le_rfl) (by positivity)

lemma sum_bound (u : ℕ → ℝ) (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re)
    (C δ t : ℝ) (hC : 0 ≤ C) (hδ : 0 ≤ δ) (ht : 0 < t) (ht1 : t ≤ 1)
    (hu : ∀ n : ℕ, |u n| ≤ C + δ * (n : ℝ) ^ (1 / 4 : ℝ)) :
    ‖∑' n, term u z t n‖ ≤ (‖z‖ + 1) *
      (C * (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-(5 / 4 : ℝ))) +
       δ * (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-1 - t))) := by
  have hB : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-(5 / 4 : ℝ))) :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by norm_num))
  have hR : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-1 - t)) :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith))
  have hm := ((hB.mul_left C).add (hR.mul_left δ)).mul_left (‖z‖ + 1)
  have hb := term_bound u z hz C δ t hC hδ ht ht1 hu
  have hn : Summable (fun n => ‖term u z t n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hm
  apply (norm_tsum_le_tsum_norm hn).trans
  apply (hn.tsum_le_tsum hb hm).trans_eq
  rw [tsum_mul_left, (hB.mul_left C).tsum_add (hR.mul_left δ), tsum_mul_left, tsum_mul_left]

lemma boundary_limit (u : ℕ → ℝ) (z : ℂ) (hz : (1 / 4 : ℝ) ≤ z.re)
    (hu : (fun n => |u n|) =o[atTop] (fun n => (n : ℝ) ^ (1 / 4 : ℝ))) :
    Tendsto (fun t : ℝ => (t : ℂ) * ∑' n, term u z t n) (𝓝[>] 0) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let K : ℝ := ‖z‖ + 1
  have hK : 0 < K := by dsimp [K]; positivity
  let δ : ℝ := ε / (4 * K)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨C, hC, huC⟩ := little_o_offset u hu δ hδ
  let B : ℝ := ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-(5 / 4 : ℝ))
  have hhead : Tendsto (fun t : ℝ => t * (K * C * B)) (𝓝[>] 0) (𝓝 0) := by
    have ht0 : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using ht0.mul_const (K * C * B)
  have hhead_small : ∀ᶠ t : ℝ in 𝓝[>] 0, t * (K * C * B) < ε / 2 :=
    hhead.eventually (gt_mem_nhds (by linarith))
  have hmass : ∀ᶠ t : ℝ in 𝓝[>] 0,
      t * ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-1 - t) < 2 :=
    zeta_mass_limit.eventually (gt_mem_nhds (by norm_num))
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall, hhead_small, hmass] with t ht ht1 hh hm
  have htpos : 0 < t := ht
  have hb := sum_bound u z hz C δ t hC hδ.le htpos ht1.le huC
  rw [dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
  calc
    t * ‖∑' n, term u z t n‖ ≤ t * (K * (C * B + δ *
        (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-1 - t)))) :=
      mul_le_mul_of_nonneg_left hb htpos.le
    _ = t * (K * C * B) + δ * K *
        (t * ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-1 - t)) := by ring_nf
    _ < ε / 2 + δ * K * 2 := add_lt_add hh (mul_lt_mul_of_pos_left hm (mul_pos hδ hK))
    _ = ε := by dsimp [δ]; field_simp; ring_nf

end AbelianBoundary

theorem OMA.solution : OMA.R_Erdos969_erdos_969_variants_evelyn_linfoot_R1_H3_R1.H2 :=
  AbelianBoundary.boundary_limit
