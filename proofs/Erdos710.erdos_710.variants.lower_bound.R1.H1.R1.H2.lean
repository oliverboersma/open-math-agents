import OMAReductions.R_Erdos710_erdos_710_variants_lower_bound_R1_H1_R1
import Mathlib

open Filter Real
open scoped Topology

/-! In the notation of Erdős and Pomerance, Section 2, round
the smoothness scale down to an integer and retain a strict margin
in both the logarithmic and square-root estimates. -/
namespace WindowScale

private lemma ratio_top : Tendsto (fun n : ℕ => log n/log (log n)) atTop atTop := by
  have h : Tendsto (fun x : ℝ => log x/x) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero, ?_⟩
    filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    exact div_pos (log_pos hx) (by linarith)
  simpa [Function.comp_def,inv_div] using h.inv_tendsto_nhdsGT_zero.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

private lemma scale_limits (a : ℝ) (ha : 0 < a) :
    let Q := fun n : ℕ => log n / log (log n)
    let y := fun n : ℕ => ⌊a*Q n⌋₊
    Tendsto y atTop atTop ∧
    Tendsto (fun n => (y n:ℝ)*log (y n)/log n) atTop (𝓝 a) ∧
    Tendsto (fun n => √(y n:ℝ)/√(Q n)) atTop (𝓝 (√a)) := by
  intro Q y
  have hQ : Tendsto Q atTop atTop := ratio_top
  have hL := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hLL := Real.tendsto_log_atTop.comp hL
  have hy : Tendsto y atTop atTop := tendsto_nat_floor_atTop.comp (hQ.const_mul_atTop ha)
  have rat : Tendsto (fun n => (y n:ℝ)/Q n) atTop (𝓝 a) :=
    (tendsto_nat_floor_mul_div_atTop ha.le).comp hQ
  have hlog := (Real.continuousAt_log ha.ne').tendsto.comp rat
  have err := hlog.div_atTop hLL
  have err₂ := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hLL
  have lim : Tendsto (fun n : ℕ => log (y n)/log (log n)) atTop (𝓝 1) := by
    have H := (err.add (tendsto_const_nhds (x := (1:ℝ)))).sub err₂
    refine (by simpa using H : Tendsto _ _ (𝓝 (1:ℝ))).congr' ?_
    filter_upwards [hy.eventually_gt_atTop 0,hQ.eventually_gt_atTop 0,
      hL.eventually_gt_atTop 1] with n hn hq hl
    change 1 < log n at hl
    have ll := log_pos hl
    have h0 : 0 < (y n:ℝ) := by exact_mod_cast hn
    change log ((y n:ℝ)/Q n)/log (log n)+1-log (log (log n))/log (log n) = _
    rw [Real.log_div h0.ne' hq.ne']
    dsimp [Q]
    rw [Real.log_div (by linarith : log n ≠ 0) ll.ne']
    field_simp
    ring
  refine ⟨hy,?_,?_⟩
  · refine (by simpa using rat.mul lim : Tendsto _ _ (𝓝 a)).congr' ?_
    filter_upwards [hL.eventually_gt_atTop 1] with n hl
    change 1 < log n at hl
    have ll := log_pos hl
    dsimp [Q]
    field_simp
  · refine (Real.continuous_sqrt.continuousAt.tendsto.comp rat).congr' ?_
    filter_upwards with n
    exact Real.sqrt_div (Nat.cast_nonneg _) _

lemma select_scale (η : ℝ) (hp : 0 < η) (hs : η < 1) :
    ∃ ξ h : ℝ, 0 < ξ ∧ ξ < 1 ∧ 0 < h ∧
    ∀ Y : ℕ, ∀ᶠ n : ℕ in atTop, ∃ y : ℕ, Y ≤ y ∧ 2 ≤ y ∧
      ∀ m : ℕ, 0 < m → (1-ξ)*y*log y/4 ≤ log m → log m ≤ (1+ξ)*y*log y/4 →
        (m:ℝ) ≤ η*n ∧ ∃ B : ℕ, m ≤ B ∧ B ≤ m*y ∧
          (1-η)*(2/√(exp 1))*m*√(log n/log (log n)) ≤ B ∧
          (B:ℝ)/m ≤ exp (log y/2-(1/2+h)) := by
  let k := 1-η/2
  let a := (2*k)^2
  let h := η/8
  let ξ := η/4
  let s := (1:ℝ)/2+h
  let C := (1-η)*(2/√(exp 1))
  have hk : 0 < k := by dsimp [k]; linarith
  have hk1 : k < 1 := by dsimp [k]; linarith
  have ha : 0 < a := by dsimp [a]; positivity
  have hroot : √a = 2*k := Real.sqrt_sq (by positivity)
  have hξ : 0 < ξ := by dsimp [ξ]; positivity
  have hh : 0 < h := by dsimp [h]; positivity
  have hmass : (1+ξ)*a/4 < 1 := by
    have hk2 := mul_le_mul_of_nonneg_left hk1.le hk.le
    have H := mul_le_mul_of_nonneg_left hk2 (by linarith : 0 ≤ 1+ξ)
    dsimp [a,k,ξ] at *
    nlinarith only [H,hp, sq_nonneg η]
  have cost : C < exp (-s)*√a := by
    have he : 1-h ≤ exp (-h) := by linarith only [Real.add_one_le_exp (-h)]
    have he' := mul_le_mul_of_nonneg_right he hk.le
    have gap : 1-η < exp (-h)*k := by
      dsimp [k,h] at he' ⊢
      nlinarith only [he',hp,sq_nonneg η]
    have oneexp : exp (-(1:ℝ)/2) = 1/√(exp 1) := by
      rw [neg_div,exp_neg,exp_half,one_div]
    have es : exp (-s) = exp (-h) * (1/√(exp 1)) := by
      rw [← oneexp, ← exp_add]; congr 1; dsimp [s]; ring
    rw [es,hroot]
    have H := mul_lt_mul_of_pos_right gap (by positivity : 0 < 2/√(exp 1))
    dsimp [C]; simp only [div_eq_mul_inv,one_mul] at H ⊢; linarith only [H]
  refine ⟨ξ,h,hξ,by dsimp [ξ]; linarith,hh,?_⟩
  intro Y
  let Q := fun n : ℕ => log n/log (log n)
  let y := fun n : ℕ => ⌊a*Q n⌋₊
  obtain ⟨yt,ylog,ysqrt⟩ := scale_limits a ha
  change Tendsto y atTop atTop at yt
  change Tendsto (fun n : ℕ => (y n:ℝ)*log (y n)/log n) atTop (𝓝 a) at ylog
  change Tendsto (fun n : ℕ => √(y n:ℝ)/√(Q n)) atTop (𝓝 (√a)) at ysqrt
  have hL := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have S : Tendsto (fun n => √(Q n)) atTop atTop := Real.tendsto_sqrt_atTop.comp ratio_top
  have mlim := ((ylog.const_mul (1+ξ)).div_const 4).sub
    (tendsto_const_nhds.div_atTop hL : Tendsto (fun n : ℕ => log η/log n) atTop (𝓝 0))
  have blim := (ysqrt.const_mul (exp (-s))).sub
    (tendsto_const_nhds.div_atTop S : Tendsto (fun n : ℕ => 1/√(Q n)) atTop (𝓝 0))
  filter_upwards [yt.eventually_ge_atTop (max Y 2),hL.eventually_gt_atTop 0,
      S.eventually_gt_atTop 0,mlim.eventually_lt_const (by linarith : (1+ξ)*a/4-0 < 1),
      blim.eventually_const_lt (by linarith : C < exp (-s)*√a-0)] with n hyn hn hS hm' hb'
  change 0 < log n at hn
  change (1+ξ)*((y n:ℝ)*log (y n)/log n)/4-log η/log n < 1 at hm'
  change C < exp (-s)*(√(y n:ℝ)/√(Q n))-1/√(Q n) at hb'
  change 0 < √(Q n) at hS
  have hy2 : 2 ≤ y n := (le_max_right Y 2).trans hyn
  have yr : 1 ≤ (y n:ℝ) := by exact_mod_cast (show 1 ≤ y n by omega)
  have yp : 0 < (y n:ℝ) := by linarith
  have np : 0 < (n:ℝ) := by
    apply Nat.cast_pos.mpr
    apply Nat.pos_of_ne_zero
    rintro rfl
    simp at hn
  let E := exp (log (y n)/2-s)
  have hE : E = exp (-s)*√(y n:ℝ) := by
    dsimp [E]; rw [sub_eq_add_neg, exp_add, exp_half, exp_log yp, mul_comm]
  have room : C*√(Q n)+1 ≤ E := by
    rw [hE]; field_simp at hb'; linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have E1 : 1 ≤ E := by linarith [mul_nonneg hC hS.le]
  have Ey : E ≤ y n := by
    dsimp [E]
    conv_rhs => rw [← Real.exp_log yp]
    apply Real.exp_le_exp.mpr
    have hl := Real.log_nonneg yr
    dsimp [s]; linarith
  refine ⟨y n,(le_max_left Y 2).trans hyn,hy2,?_⟩
  intro m hm _ hi
  have mr : 1 ≤ (m:ℝ) := by exact_mod_cast hm
  have mp : 0 < (m:ℝ) := by linarith
  constructor
  · apply (Real.log_le_log_iff mp (mul_pos hp np)).mp
    rw [Real.log_mul hp.ne' np.ne']
    field_simp at hm'
    linarith
  · let B := ⌊(m:ℝ)*E⌋₊
    have floorle : (B:ℝ) ≤ (m:ℝ)*E := Nat.floor_le (by positivity)
    have floorlt : (m:ℝ)*E < (B:ℝ)+1 := Nat.lt_floor_add_one _
    refine ⟨B,(Nat.le_floor_iff (by positivity)).mpr ?_,?_,?_,?_⟩
    · simpa only [mul_one] using mul_le_mul_of_nonneg_left E1 mp.le
    · have hb := floorle.trans (mul_le_mul_of_nonneg_left Ey mp.le)
      exact_mod_cast hb
    · change C*m*√(Q n) ≤ B
      have hz := mul_le_mul_of_nonneg_left room mp.le
      linarith only [hz,floorlt,mr]
    · exact (div_le_iff₀ mp).mpr (by linarith only [floorle])

end WindowScale

theorem OMA.solution : OMA.R_Erdos710_erdos_710_variants_lower_bound_R1_H1_R1.H2 := WindowScale.select_scale
