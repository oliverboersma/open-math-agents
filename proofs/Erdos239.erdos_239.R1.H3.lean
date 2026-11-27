import OMAReductions.R_Erdos239_erdos_239_R1

/-! If the prime series of (1 - cos (t log p)) / p converged, the Euler product would give
|zeta (sigma + i t)| at least a constant multiple of zeta sigma for every sigma > 1. The
zeta function is continuous at 1 + i t, while (sigma - 1) zeta sigma tends to one, which is
a contradiction as sigma decreases to 1. -/

open Filter Topology

namespace OMA239

lemma re_log_bound {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    |(-Complex.log (1 - z)).re - z.re| ≤ ‖z‖ ^ 2 := by
  have h1 : ‖-z‖ < 1 := by
    rw [norm_neg]
    linarith
  have h2 := Complex.norm_log_one_add_sub_self_le h1
  rw [norm_neg] at h2
  have h3 : (1 - ‖z‖)⁻¹ ≤ 2 := by
    have h : (1 / 2 : ℝ) ≤ 1 - ‖z‖ := by linarith
    calc (1 - ‖z‖)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h
      _ = 2 := by norm_num
  have h4 : ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 ≤ ‖z‖ ^ 2 := by
    have h := mul_le_mul_of_nonneg_left h3 (sq_nonneg ‖z‖)
    linarith
  have h5 : (-Complex.log (1 - z)).re - z.re = -(Complex.log (1 + -z) - -z).re := by
    rw [← sub_eq_add_neg, sub_neg_eq_add, Complex.add_re, Complex.neg_re]
    ring
  rw [h5, abs_neg]
  exact (Complex.abs_re_le_norm _).trans (h2.trans h4)

lemma term_bound (t σ : ℝ) (hσ : 1 < σ) (p : Nat.Primes) :
    (-Complex.log (1 - ((p : ℕ) : ℂ) ^ (-(σ : ℂ)))).re ≤
      ((1 - Real.cos (t * Real.log (p.val : ℝ))) / (p.val : ℝ) + 2 / (p.val : ℝ) ^ 2) +
      (-Complex.log (1 - ((p : ℕ) : ℂ) ^ (-((σ : ℂ) + t * Complex.I)))).re := by
  have hp2 : (2 : ℝ) ≤ (p.val : ℝ) := by exact_mod_cast p.prop.two_le
  have hp0 : (0 : ℝ) < (p.val : ℝ) := by linarith
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log (p.val : ℝ) := ⟨_, rfl⟩
  have hLpos : 0 < L := by
    rw [hL]
    exact Real.log_pos (by linarith)
  have hexpL : Real.exp L = (p.val : ℝ) := by rw [hL, Real.exp_log hp0]
  obtain ⟨x, hx⟩ : ∃ x, x = Real.exp (-(L * σ)) := ⟨_, rfl⟩
  have hxpos : 0 < x := by
    rw [hx]
    exact Real.exp_pos _
  have hxle : x ≤ 1 / (p.val : ℝ) := by
    have h1 : Real.exp (-(L * σ)) ≤ Real.exp (-L) := Real.exp_le_exp.2 (by nlinarith)
    rwa [Real.exp_neg L, hexpL, ← one_div, ← hx] at h1
  have hxhalf : x ≤ 1 / 2 := hxle.trans (one_div_le_one_div_of_le (by norm_num) hp2)
  have hz : ∀ s : ℂ, ((p : ℕ) : ℂ) ^ (-s) = Complex.exp (-((L : ℂ) * s)) := by
    intro s
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast p.prop.ne_zero), ← Complex.natCast_log,
      ← hL, mul_neg]
  have hzσ : ((p : ℕ) : ℂ) ^ (-(σ : ℂ)) = ((x : ℝ) : ℂ) := by
    rw [hz, hx, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul]
  have hre : (-((L : ℂ) * ((σ : ℂ) + t * Complex.I))).re = -(L * σ) := by simp
  have him : (-((L : ℂ) * ((σ : ℂ) + t * Complex.I))).im = -(L * t) := by simp
  have hzs_norm : ‖((p : ℕ) : ℂ) ^ (-((σ : ℂ) + t * Complex.I))‖ = x := by
    rw [hz, Complex.norm_exp, hre, ← hx]
  have hzs_re : (((p : ℕ) : ℂ) ^ (-((σ : ℂ) + t * Complex.I))).re = x * Real.cos (t * L) := by
    rw [hz, Complex.exp_re, hre, him, Real.cos_neg, mul_comm L t, ← hx]
  have ha := re_log_bound (z := ((p : ℕ) : ℂ) ^ (-((σ : ℂ) + t * Complex.I)))
    (by rw [hzs_norm]; exact hxhalf)
  have hb := re_log_bound (z := ((p : ℕ) : ℂ) ^ (-(σ : ℂ)))
    (by rw [hzσ, Complex.norm_real, Real.norm_of_nonneg hxpos.le]; exact hxhalf)
  rw [hzs_norm, hzs_re] at ha
  rw [hzσ, Complex.norm_real, Real.norm_of_nonneg hxpos.le, Complex.ofReal_re] at hb
  have hcos : 0 ≤ 1 - Real.cos (t * L) := by linarith [Real.cos_le_one (t * L)]
  have h1 : x * (1 - Real.cos (t * L)) ≤ (1 - Real.cos (t * L)) / (p.val : ℝ) := by
    rw [div_eq_mul_one_div, mul_comm]
    exact mul_le_mul_of_nonneg_left hxle hcos
  have h2 : x ^ 2 ≤ 1 / (p.val : ℝ) ^ 2 := by
    rw [← one_div_pow]
    exact pow_le_pow_left₀ hxpos.le hxle 2
  have h3 : 2 / (p.val : ℝ) ^ 2 = 2 * (1 / (p.val : ℝ) ^ 2) := by ring
  have ha' := (abs_le.1 ha).1
  have hb' := (abs_le.1 hb).2
  rw [hzσ, ← hL]
  linarith

theorem main_thm (t : ℝ) (ht : t ≠ 0) :
    ¬ Summable (fun p : Nat.Primes =>
      (1 - Real.cos (t * Real.log (p.val : ℝ))) / (p.val : ℝ)) := by
  intro hsum
  have hsq : Summable (fun p : Nat.Primes => 2 / (p.val : ℝ) ^ 2) := by
    have h := (Nat.Primes.summable_rpow (r := -2)).2 (by norm_num)
    refine (h.mul_left 2).congr (fun p => ?_)
    rw [Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_two, div_eq_mul_inv]
  have hc := hsum.add hsq
  have hlog : ∀ s : ℂ, 1 < s.re →
      Summable (fun p : Nat.Primes => -Complex.log (1 - ((p : ℕ) : ℂ) ^ (-s))) := by
    intro s hs
    have h1 : Summable (fun p : Nat.Primes => -(((p : ℕ) : ℂ) ^ (-s))) := by
      refine (Summable.of_norm ?_).neg
      have h := (Nat.Primes.summable_rpow (r := -s.re)).2 (by linarith)
      refine h.congr (fun p => ?_)
      rw [Complex.norm_natCast_cpow_of_pos p.prop.pos, Complex.neg_re]
    have h2 := (Complex.summable_log_one_add_of_summable h1).neg
    refine h2.congr (fun p => ?_)
    rw [sub_eq_add_neg]
  obtain ⟨C, hC⟩ : ∃ C, C = ∑' p : Nat.Primes,
      ((1 - Real.cos (t * Real.log (p.val : ℝ))) / (p.val : ℝ) + 2 / (p.val : ℝ) ^ 2) :=
    ⟨_, rfl⟩
  have key : ∀ σ : ℝ, 1 < σ →
      ‖riemannZeta (σ : ℂ)‖ ≤ Real.exp C * ‖riemannZeta ((σ : ℂ) + t * Complex.I)‖ := by
    intro σ hσ
    have hs1 : 1 < ((σ : ℂ)).re := by simpa using hσ
    have hs2 : 1 < ((σ : ℂ) + t * Complex.I).re := by simpa using hσ
    have hA := Complex.hasSum_re (hlog _ hs2).hasSum
    have hB := Complex.hasSum_re (hlog _ hs1).hasSum
    have hle := hasSum_le (fun p => term_bound t σ hσ p) hB (hc.hasSum.add hA)
    rw [← riemannZeta_eulerProduct_exp_log hs1, ← riemannZeta_eulerProduct_exp_log hs2,
      Complex.norm_exp, Complex.norm_exp, ← Real.exp_add, Real.exp_le_exp, hC]
    exact hle
  have hs0 : (1 : ℂ) + t * Complex.I ≠ 1 := by
    intro h
    have h1 := congrArg Complex.im h
    simp at h1
    exact ht h1
  have hcont : ContinuousAt riemannZeta (1 + t * Complex.I) :=
    (differentiableAt_riemannZeta hs0).continuousAt
  have h0 : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝 (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    have h := Complex.continuous_ofReal.tendsto 1
    rwa [Complex.ofReal_one] at h
  have hpath : Tendsto (fun σ : ℝ => (σ : ℂ) + t * Complex.I) (𝓝[>] (1 : ℝ))
      (𝓝 (1 + t * Complex.I)) := (h0.add_const _).mono_left nhdsWithin_le_nhds
  have hb : Tendsto (fun σ : ℝ => ‖riemannZeta ((σ : ℂ) + t * Complex.I)‖) (𝓝[>] (1 : ℝ))
      (𝓝 ‖riemannZeta (1 + t * Complex.I)‖) := (hcont.tendsto.comp hpath).norm
  have hto : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨h0.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    intro h
    have h1 : σ = 1 := by exact_mod_cast (Set.mem_singleton_iff.1 h)
    exact (ne_of_gt hσ) h1
  have hres := (riemannZeta_residue_one.comp hto).norm
  have hup : Tendsto (fun σ : ℝ => (σ - 1) *
      (Real.exp C * ‖riemannZeta ((σ : ℂ) + t * Complex.I)‖)) (𝓝[>] (1 : ℝ))
      (𝓝 ((1 - 1) * (Real.exp C * ‖riemannZeta (1 + t * Complex.I)‖))) :=
    (((continuous_sub_right (1 : ℝ)).tendsto 1).mono_left nhdsWithin_le_nhds).mul
      (hb.const_mul _)
  have hfin := le_of_tendsto_of_tendsto hres hup (by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    change ‖((σ : ℂ) - 1) * riemannZeta (σ : ℂ)‖ ≤
      (σ - 1) * (Real.exp C * ‖riemannZeta ((σ : ℂ) + t * Complex.I)‖)
    have hσ1 : (1 : ℝ) < σ := hσ
    have hn : ‖(σ : ℂ) - 1‖ = σ - 1 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_of_nonneg (by linarith)]
    rw [norm_mul, hn]
    exact mul_le_mul_of_nonneg_left (key σ hσ1) (by linarith))
  rw [norm_one, sub_self, zero_mul] at hfin
  linarith

end OMA239

theorem OMA.solution : OMA.R_Erdos239_erdos_239_R1.H3 := fun t ht => OMA239.main_thm t ht
