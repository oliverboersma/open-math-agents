import OMAReductions.R_Erdos90_erdos_90_variants_sawin_explicit_R1_H2_R1
import Mathlib

/-! Rational certificates for Sawin’s explicit numerical inequality in Erdős 90.
We enclose the fourth and eighth roots by taking integer powers. Lower Taylor
sums and rational bounds on e and π certify the remaining logarithms and
exponentials. The two sides lie on opposite sides of 48.53. -/
open Real Finset
namespace Sawin90
lemma large_exp : (72004800000:ℝ)^11 * 1.05756 ≤ exp 275.056 := by
  have h25 : 72004800000 ≤ exp 25 := calc
    (72004800000:ℝ) ≤ 2.7182818^25 := by norm_num
    _ ≤ (exp 1)^25 := pow_le_pow_left₀ (by norm_num) (by linarith [exp_one_gt_d9]) _
    _ = _ := by rw [←exp_nat_mul]; norm_num
  have hfrac := sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤0.056) 3
  norm_num [sum_range_succ,Nat.factorial] at hfrac
  rw [show (275.056:ℝ) = (11:ℕ)*(25:ℝ)+0.056 by norm_num,exp_add,exp_nat_mul]
  exact mul_le_mul (pow_le_pow_left₀ (by norm_num) h25 _) (by linarith) (by norm_num) (by positivity)

lemma medium_exp : (161757605:ℝ) ≤ exp 18.902 := by
  have hfrac := sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤0.902) 7
  norm_num [sum_range_succ,Nat.factorial] at hfrac
  calc
    _ ≤ (2.7182818:ℝ)^18 * 2.4643 := by norm_num
    _ ≤ (exp 1)^18 * exp 0.902 := mul_le_mul
      (pow_le_pow_left₀ (by norm_num) (by linarith [exp_one_gt_d9]) _) (by linarith) (by norm_num) (by positivity)
    _ = _ := by rw [←exp_nat_mul,←exp_add]; norm_num

lemma small_exp : exp 3.882140384 < 48.53 := by
  have hfrac := sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤0.117859616) 4
  norm_num [sum_range_succ,Nat.factorial] at hfrac
  rw [show (3.882140384:ℝ) = (4:ℕ)*(1:ℝ)-0.117859616 by norm_num,exp_sub,exp_nat_mul]
  apply (div_lt_iff₀ (exp_pos _)).2
  calc
    (exp 1)^4 ≤ 2.7182818286^4 := pow_le_pow_left₀ (exp_pos 1).le exp_one_lt_d9.le _
    _ < 48.53*1.12506 := by norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by norm_num)

lemma rhs : (48.53:ℝ) < (1-1/72)*sqrt (2*π/exp 1)*
    (4028003754363836120804840523694080:ℝ)^(8:ℝ)⁻¹ /
    ((sqrt 26165522663340060)^(1/4:ℝ)*sqrt (log (sqrt 26165522663340060))) := by
  let D : ℝ := 26165522663340060
  let V : ℝ := 4028003754363836120804840523694080
  have hD : 0<D := by norm_num [D]
  have hV : 0<V := by norm_num [V]
  have h1 : 1.52034 ≤ sqrt (2*π/exp 1) := by
    apply Real.le_sqrt_of_sq_le
    apply (le_div_iff₀ (exp_pos _)).mpr
    have h := mul_le_mul_of_nonneg_left exp_one_lt_d9.le (by norm_num : 0 ≤ (1.52034:ℝ)^2)
    linarith [Real.pi_gt_d6]
  have h2 : 15872.16 ≤ V^(8:ℝ)⁻¹ := by
    apply le_of_pow_le_pow_left₀ (n := 8) (by decide) (Real.rpow_nonneg hV.le _)
    rw [show (V^(8:ℝ)⁻¹)^8 = V by simpa only [Nat.cast_ofNat] using Real.rpow_inv_natCast_pow (n:=8) hV.le (by decide)]
    norm_num [V]
  have hs : sqrt D ≤ 161757605 := by
    apply (Real.sqrt_le_iff).2
    norm_num [D]
  have h3 : (sqrt D)^(1/4:ℝ) ≤ 112.776 := by
    apply le_of_pow_le_pow_left₀ (n:=4) (by decide) (by norm_num)
    rw [one_div,show ((sqrt D)^(4:ℝ)⁻¹)^4 = sqrt D by simpa only [Nat.cast_ofNat] using Real.rpow_inv_natCast_pow (n:=4) (sqrt_nonneg D) (by decide)]
    exact hs.trans (by norm_num)
  have hlog : log (sqrt D) ≤ 18.902 := (log_le_iff_le_exp (sqrt_pos.2 hD)).2 (hs.trans medium_exp)
  have h4 : sqrt (log (sqrt D)) ≤ 4.34765 := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by norm_num, hlog.trans (by norm_num)⟩
  have hlogpos : 0 < log (sqrt D) := log_pos ((Real.lt_sqrt (by norm_num)).2 (by norm_num [D]))
  apply (lt_div_iff₀ (mul_pos (Real.rpow_pos_of_pos (sqrt_pos.2 hD) _) (sqrt_pos.2 hlogpos))).2
  calc
    _ ≤ 48.53*(112.776*4.34765) := mul_le_mul_of_nonneg_left (mul_le_mul h3 h4 (sqrt_nonneg _) (by norm_num)) (by norm_num)
    _ < (1-1/72)*1.52034*15872.16 := by norm_num
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2 (by norm_num) (by positivity)

end Sawin90

theorem OMA.solution : OMA.R_Erdos90_erdos_90_variants_sawin_explicit_R1_H2_R1.H2 := by
  let U : ℝ := 15366930839640910407280821544568342760939116621460511799368640691024952414942895895674487917919190453067074013839821044685981817225847752755432866840801104952946378971003813637609053179555854971429716544369570035272611087657978405847032106632812497009078453661958168488757383118555915563176123245641339520488302511643015980605017267388801042321225063767021503823501125249521809325896257913477135701039141274572751456580509666911459268400451518726144000000000000000000000
  let A : ℝ := U ^ (4:ℝ)⁻¹
  have hu : 0<U := by norm_num [U]
  have ha : 0<A := Real.rpow_pos_of_pos hu _
  have hb : A ≤ 1979917000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by
    apply le_of_pow_le_pow_left₀ (n:=4) (by decide) (by norm_num)
    change (U ^ (4:ℝ)⁻¹)^4 ≤ _
    rw [show (U^(4:ℝ)⁻¹)^4 = U by simpa only [Nat.cast_ofNat] using Real.rpow_inv_natCast_pow (n:=4) hu.le (by decide)]
    norm_num [U]
  have hlog : log (144*A+1) ≤ 275.056 := by
    apply (log_le_iff_le_exp (by positivity)).mpr
    apply le_trans _ Sawin90.large_exp
    linarith only [hb]
  apply lt_trans _ Sawin90.rhs
  change (144*A+1) ^ (0.014114:ℝ) < 48.53
  rw [Real.rpow_def_of_pos (by positivity)]
  apply lt_of_le_of_lt _ Sawin90.small_exp
  exact Real.exp_le_exp.mpr (by linarith)
