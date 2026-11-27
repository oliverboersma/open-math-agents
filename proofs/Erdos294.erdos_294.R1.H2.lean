import OMAReductions.R_Erdos294_erdos_294_R1
import Mathlib

/-!
For x = log N, y = log x and z = log y choose L = ceiling(x*y^3*z^5).
Then log L ≤ 2y and log log L ≤ 2z, so the smaller smoothness cutoff
eventually exceeds 20x. Chebyshev's elementary lower bound for the lcm
then puts it above 4N. One further factor z absorbs the separation constant.
-/

open Real Filter Finset

namespace Scale294

lemma log_power (d : ℕ) : ∀ᶠ r : ℝ in atTop, 2*(log r)^d ≤ r := by
  filter_upwards [(Real.isLittleO_pow_log_id_atTop (n := d)).bound (show (0 : ℝ) < 1/2 by norm_num),
    eventually_ge_atTop (1 : ℝ)] with r h hr
  have h' : |(log r)^d| ≤ (1/2 : ℝ)*|r| := h
  rw [abs_of_nonneg (pow_nonneg (log_nonneg hr) _),abs_of_nonneg (by linarith)] at h'
  linarith

lemma lcm_monotone {a b : ℕ} (h : a ≤ b) : Nat.lcmUpto a ∣ Nat.lcmUpto b := by
  unfold Nat.lcmUpto
  apply Finset.lcm_dvd
  intro n hn
  apply Finset.dvd_lcm
  exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,(Finset.mem_Icc.mp hn).2.trans h⟩

lemma lcm_large {N S : ℕ} (hN : 0 < N) (hx : 8 ≤ Real.log (N : ℝ))
    (hS : 20 * Real.log (N : ℝ) ≤ S) : 4*N ≤ Nat.lcmUpto S := by
  have hpos : 0 < (N : ℝ) := by positivity
  have hs : (128 : ℝ) ≤ S := by linarith
  have hh : Real.log ((S : ℝ)+1) ≤ (S : ℝ)/4 := by
    rw [show (S : ℝ)+1 = 8*(((S : ℝ)+1)/8) by ring,Real.log_mul (by norm_num) (by positivity)]
    have h := Real.log_le_self (show 0 ≤ ((S : ℝ)+1)/8 by positivity)
    linarith [Real.log_le_self (by norm_num : (0 : ℝ) ≤ 8)]
  have ht : (1/2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  have hψ := Chebyshev.psi_ge S
  rw [Chebyshev.psi_eq_log_lcmUpto] at hψ
  have hf : Real.log ((4 : ℝ)*N) ≤ Real.log (Nat.lcmUpto S) := by
    rw [Real.log_mul (by norm_num) hpos.ne']
    nlinarith [mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ (S : ℝ)),
      Real.log_le_self (by norm_num : (0 : ℝ) ≤ 4)]
  exact_mod_cast (Real.log_le_log_iff (by positivity) (by exact_mod_cast Nat.lcmUpto_pos S)).mp hf

end Scale294

open Scale294

theorem OMA.solution : OMA.R_Erdos294_erdos_294_R1.H2 := by
  intro c hc N₀
  refine ⟨6,?_⟩
  have tx := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ty := Real.tendsto_log_atTop.comp tx
  have tz := Real.tendsto_log_atTop.comp ty
  filter_upwards [tz.eventually_ge_atTop 64,tz.eventually_ge_atTop (4096/c),
    tx.eventually_ge_atTop (max 128 (N₀ : ℝ)),ty.eventually_ge_atTop 64,
    tx.eventually (log_power 8),tendsto_natCast_atTop_atTop.eventually (log_power 9),
    eventually_ge_atTop (1 : ℕ)] with N hz64 hcz hx' hy64 hp8 hp9 hN
  let x := log (N : ℝ)
  let y := log x
  let z := log y
  change 64 ≤ z at hz64
  change 4096/c ≤ z at hcz
  change max 128 (N₀ : ℝ) ≤ x at hx'
  change 64 ≤ y at hy64
  change 2*y^8 ≤ x at hp8
  change 2*x^9 ≤ (N : ℝ) at hp9
  have hx : 128 ≤ x := (le_max_left ..).trans hx'
  have hxN : (N₀ : ℝ) ≤ x := (le_max_right ..).trans hx'
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hz0 : 0 < z := by linarith
  have hzy : z ≤ y := Real.log_le_self hy0.le
  have hyx : y ≤ x := Real.log_le_self hx0.le
  have hcz' := (div_le_iff₀ hc).mp hcz
  let B := x*y^3*z^5
  let L := ⌈B⌉₊
  have hB : x ≤ B := by
    calc
      x = x*1^3*1^5 := by ring
      _ ≤ x*y^3*z^5 := by gcongr <;> linarith
  have hLlo : B ≤ (L : ℝ) := Nat.le_ceil _
  have hLup : (L : ℝ) ≤ 2*B := by
    have := Nat.ceil_lt_add_one (show 0 ≤ B by linarith)
    change (L : ℝ) < B+1 at this
    linarith
  have hLx : (L : ℝ) ≤ x^2 := calc
    _ ≤ 2*(x*y^3*z^5) := hLup
    _ ≤ 2*(x*y^3*y^5) := by gcongr
    _ = x*(2*y^8) := by ring
    _ ≤ x*x := by gcongr
    _ = _ := by ring
  have hlog : log L ≤ 2*y := calc
    _ ≤ log (x^2) := Real.log_le_log (by linarith) hLx
    _ = _ := by rw [Real.log_pow]; simp [y]
  have hlog0 : y ≤ log L := Real.log_le_log hx0 (by linarith)
  have hloglog0 : z ≤ log (log L) := Real.log_le_log hy0 hlog0
  have hloglog : log (log L) ≤ 2*z := calc
    _ ≤ log (2*y) := Real.log_le_log (by linarith) hlog
    _ = log 2 + z := by rw [Real.log_mul (by norm_num) hy0.ne']
    _ ≤ _ := by linarith [Real.log_le_self (by norm_num : (0 : ℝ) ≤ 2)]
  let DL := (log L)^3*(log (log L))^4
  have hd0 : 0 < DL := mul_pos (pow_pos (by linarith) _) (pow_pos (by linarith) _)
  have hd1 : 1 ≤ DL := by
    change 1 ≤ (log L)^3*(log (log L))^4
    calc
      1 = (1 : ℝ)^3*1^4 := by norm_num
      _ ≤ _ := by gcongr <;> linarith
  have hdhi : DL ≤ 128*y^3*z^4 := calc
    _ ≤ (2*y)^3*(2*z)^4 := by dsimp [DL]; gcongr <;> linarith
    _ = _ := by ring
  let SL := ⌊c*(L:ℝ)/DL⌋₊
  have hbig : 21*x ≤ c*(L:ℝ)/DL := by
    apply (le_div_iff₀ hd0).mpr
    calc
      21*x*DL ≤ 21*x*(128*y^3*z^4) := by gcongr
      _ ≤ (x*y^3*z^4)*(z*c) := by
        have hh : 2688 ≤ z*c := by linarith
        nlinarith only [mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ x*y^3*z^4)]
      _ = c*B := by dsimp [B]; ring
      _ ≤ _ := by gcongr
  have hSL : 20*x ≤ (SL : ℝ) := by
    have hh := Nat.lt_floor_add_one (c*(L:ℝ)/DL)
    change _ < (SL : ℝ)+1 at hh
    linarith
  have hctl : (L : ℝ)*(x^3*y^4) ≤ N := calc
    _ ≤ x^2*(x^3*x^4) := by gcongr
    _ = x^9 := by ring
    _ ≤ _ := by linarith [show 0 ≤ x^9 by positivity]
  have hdiv : SL ≤ ⌊c*(N : ℝ)/(x^3*y^4)⌋₊ := by
    apply Nat.floor_le_floor
    calc
      c*(L:ℝ)/DL ≤ c*(L:ℝ) := div_le_self (by positivity) hd1
      _ ≤ _ := by
        apply (le_div_iff₀ (by positivity)).mpr
        calc
          c*(L:ℝ)*(x^3*y^4) = c*((L:ℝ)*(x^3*y^4)) := by ring
          _ ≤ _ := by gcongr
  refine ⟨L,by exact_mod_cast (show (N₀ : ℝ) ≤ L by linarith),
    by exact_mod_cast (show (32 : ℝ) ≤ L by linarith),
    lcm_large hN (by change 8 ≤ x; linarith) hSL,lcm_monotone hdiv,?_⟩
  change 32*(L : ℝ)*|(N:ℝ)/(x*y^3*z^(6 : ℝ))| ≤ N
  rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num,Real.rpow_natCast,abs_of_nonneg (by positivity)]
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity)).mpr
  have hfin : 32*(L : ℝ) ≤ x*y^3*z^6 := calc
    _ ≤ 32*(2*B) := by gcongr
    _ = 64*B := by ring
    _ ≤ z*B := by gcongr
    _ = _ := by dsimp [B]; ring
  nlinarith only [mul_le_mul_of_nonneg_right hfin (by positivity : 0 ≤ (N : ℝ))]
