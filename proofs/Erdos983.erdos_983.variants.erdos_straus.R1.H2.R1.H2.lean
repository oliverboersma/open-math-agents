import OMAReductions.R_Erdos983_erdos_983_variants_erdos_straus_R1_H2_R1

/-! Taking the maximum of the error on a growing interval preserves arbitrary
logarithmic savings. Above exp A the comparison function x / (log x)^A is
increasing, and any fixed initial segment contributes a bounded error. -/

open Real Filter Asymptotics Finset Set
open scoped Topology

namespace OMA.PrimeErrorEnvelope

private lemma weight_mono (A : ℝ) (hA : 0 < A) :
    MonotoneOn (fun x : ℝ => x / log x ^ A) (Ici (exp A)) := by
  have hd (x : ℝ) (hx : x ∈ Ici (exp A)) :
      HasDerivAt (fun t : ℝ => t / log t ^ A)
        ((log x - A) * (log x ^ (A-1)) / (log x ^ A)^2) x := by
    have pos : 0 < x := (exp_pos A).trans_le hx
    have hlog : A ≤ log x := (le_log_iff_exp_le pos).mpr hx
    have lp := hA.trans_le hlog
    have h := (hasDerivAt_id x).div ((hasDerivAt_log pos.ne').rpow_const
      (p := A) (Or.inl lp.ne')) (rpow_pos_of_pos lp A).ne'
    change HasDerivAt (id / fun t : ℝ => log t ^ A) _ x
    suffices heq : (1 * log x ^ A - id x * (x⁻¹ * A * log x ^ (A-1))) / (log x ^ A)^2 =
        (log x - A) * log x ^ (A-1) / (log x ^ A)^2 by rwa [← heq]
    congr 1
    rw [show log x ^ A = log x ^ (A-1) * log x by
      rw [← Real.rpow_add_one lp.ne']; congr 1; ring]
    simp only [id_eq,one_mul]
    field_simp
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici _)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
  intro x hx
  have hh := interior_subset hx
  have pos : 0 < x := (exp_pos A).trans_le hh
  have lp : A ≤ log x := (le_log_iff_exp_le pos).mpr hh
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr lp) (rpow_nonneg (hA.trans_le lp).le _)) (sq_nonneg _)

private lemma scale_bound (A : ℝ) (hA : 0 < A) (n : ℕ) (hn : 2 ≤ n) :
    (128 * √(n:ℝ)) / log (128 * √(n:ℝ)) ^ A ≤
      (128 * 2^A) * (√(n:ℝ) / log n ^ A) := by
  have pos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have lp : 0 < log n := log_pos (by exact_mod_cast (show 1 < n by omega))
  have hl : log (n:ℝ) / 2 ≤ log (128 * √(n:ℝ)) := by
    rw [log_mul (by norm_num) (sqrt_pos.mpr pos).ne',log_sqrt pos.le]
    linarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 128)]
  have hpart : 0 < log (n:ℝ)/2 := by positivity
  calc
    _ ≤ (128 * √(n:ℝ)) / (log n / 2)^A :=
      div_le_div_of_nonneg_left (by positivity) (rpow_pos_of_pos hpart _) (rpow_le_rpow hpart.le hl hA.le)
    _ = _ := by rw [Real.div_rpow lp.le (by norm_num : (0:ℝ) ≤ 2)]; simp only [div_div_eq_mul_div]; ring

theorem envelope (g : ℕ → ℝ)
    (hg : ∀ A : ℝ, 0 < A → g =o[atTop] (fun k : ℕ => (k:ℝ) / log k ^ A)) :
    ∃ E : ℕ → ℕ, (∀ A : ℝ, 0 < A → (fun n : ℕ => (E n:ℝ)) =o[atTop]
      (fun n : ℕ => √(n:ℝ) / log n ^ A)) ∧
      ∀ᶠ n : ℕ in atTop, 1 ≤ E n ∧ ∀ k ≤ 128*n.sqrt, |g k| ≤ E n := by
  let c (k : ℕ) := ⌈|g k|⌉₊
  let S (n : ℕ) := range (128*n.sqrt + 1)
  let E (n : ℕ) := (S n).sup c + 1
  refine ⟨E,?_,?_⟩
  · intro A hA
    apply isLittleO_iff.mpr
    intro ε he
    let D := (128:ℝ)*2^A
    have hD : 0 < D := by dsimp [D]; positivity
    let δ := ε/(2*D)
    have hd : 0 < δ := by dsimp [δ]; positivity
    obtain ⟨K,hK⟩ := eventually_atTop.mp (((hg A hA).bound hd).and
      ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (exp A)))
    let M := (range K).sup c
    have hM : (0:ℝ) < (M:ℝ)+2 := by positivity
    have small := ((isLittleO_log_rpow_rpow_atTop A (by norm_num : 0 < (1/2:ℝ))).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).bound (div_pos (div_pos he (by norm_num : (0:ℝ)<2)) hM)
    filter_upwards [small,eventually_ge_atTop 2] with n hs hn
    have pos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have lp : 0 < log n := log_pos (by exact_mod_cast (show 1 < n by omega))
    have pl : 0 < log n ^ A := rpow_pos_of_pos lp _
    change ‖log n ^ A‖ ≤ (ε/2/((M:ℝ)+2)) * ‖(n:ℝ)^(1/2:ℝ)‖ at hs
    rw [← sqrt_eq_rpow,Real.norm_eq_abs,abs_of_pos pl,Real.norm_eq_abs,abs_of_nonneg (sqrt_nonneg _)] at hs
    have initial : (M:ℝ)+2 ≤ ε/2*(√(n:ℝ)/log n ^ A) := by
      rw [← mul_div_assoc,le_div_iff₀ pl]
      have hh := (le_div_iff₀ hM).mp (show log n ^ A ≤ (ε/2*√(n:ℝ))/((M:ℝ)+2) by
        simpa only [div_mul_eq_mul_div] using hs)
      simpa only [mul_comm ((M:ℝ)+2)] using hh
    obtain ⟨k,hk,eq⟩ := exists_mem_eq_sup (S n) (by exact ⟨0,mem_range.mpr (by omega)⟩) c
    have form : (E n:ℝ) = (c k:ℝ)+1 := by simp only [E,eq,Nat.cast_add,Nat.cast_one]
    change ‖(E n:ℝ)‖ ≤ ε * ‖√(n:ℝ) / log n ^ A‖
    rw [Real.norm_eq_abs,abs_of_nonneg (show (0:ℝ) ≤ E n by positivity),form,
      Real.norm_eq_abs,abs_of_nonneg (div_nonneg (sqrt_nonneg _) pl.le)]
    by_cases ltK : k < K
    · have h : c k ≤ M := Finset.le_sup (f := c) (mem_range.mpr ltK)
      have h' : (c k:ℝ) ≤ M := by exact_mod_cast h
      have hw : 0 ≤ ε * (√(n:ℝ)/log n ^ A) := by positivity
      linarith
    · obtain ⟨hb,hkexp⟩ := hK k (by omega)
      have kp : 0 < (k:ℝ) := (exp_pos A).trans_le hkexp
      have logk : 0 < log k := hA.trans_le ((le_log_iff_exp_le kp).mpr hkexp)
      change ‖g k‖ ≤ δ * ‖(k:ℝ)/log k ^ A‖ at hb
      rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (div_nonneg kp.le (rpow_pos_of_pos logk A).le)] at hb
      have hkn : k ≤ 128*n.sqrt := by have := mem_range.mp hk; omega
      have root : (n.sqrt:ℝ) ≤ √(n:ℝ) := by
        apply (le_sqrt (by positivity) pos.le).mpr
        exact_mod_cast (by simpa [sq] using Nat.sqrt_le n : n.sqrt^2 ≤ n)
      have hkn' : (k:ℝ) ≤ 128*√(n:ℝ) :=
        (show (k:ℝ) ≤ 128*(n.sqrt:ℝ) by exact_mod_cast hkn).trans (by gcongr)
      have bound := (weight_mono A hA hkexp (hkexp.trans hkn') hkn').trans (scale_bound A hA n hn)
      have smallg := hb.trans (mul_le_mul_of_nonneg_left bound hd.le)
      have hmul : δ*(D*(√(n:ℝ)/log n ^ A)) = ε/2*(√(n:ℝ)/log n ^ A) := by dsimp [δ]; field_simp
      change |g k| ≤ δ*(D*_) at smallg
      rw [hmul] at smallg
      have ceilb : (c k:ℝ) < |g k|+1 := Nat.ceil_lt_add_one (abs_nonneg _)
      have m0 := Nat.cast_nonneg (α := ℝ) M
      linarith
  · filter_upwards with n
    refine ⟨by dsimp [E]; omega,?_⟩
    intro k hk
    have h : c k ≤ (S n).sup c := Finset.le_sup (f := c) (mem_range.mpr (by omega))
    exact (Nat.le_ceil _).trans (by exact_mod_cast (by dsimp [E]; omega : c k ≤ E n))

end OMA.PrimeErrorEnvelope

theorem OMA.solution : OMA.R_Erdos983_erdos_983_variants_erdos_straus_R1_H2_R1.H2 :=
  OMA.PrimeErrorEnvelope.envelope
