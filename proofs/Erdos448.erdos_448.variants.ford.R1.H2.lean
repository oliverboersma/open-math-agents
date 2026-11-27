import OMAReductions.R_Erdos448_erdos_448_variants_ford_R1
import Mathlib

/-! With beta = 1 - alpha in (0,1): Bernoulli gives beta (j+1)^(beta-1) <= (j+1)^beta - j^beta,
so the power sum telescopes to at most n^beta / beta. The upper bound splits the range at
sqrt n (log(j+2) >= log(sqrt n + 1) >= (log n)/2 on the long part); the lower bound keeps the
upper half of the range. Finally n = (Nat.log 2 x)/2 + 1 lies between (log x)/2 and log x. -/

open Finset Filter Asymptotics Real
open scoped Topology

namespace OMA.P2b448

theorem beta_bounds : 0 < (1 + log (log 2)) / log 2 ∧ (1 + log (log 2)) / log 2 < 1 := by
  have h2 := Real.log_two_gt_d9
  have h2' := Real.log_two_lt_d9
  have hl : 0 < log 2 := by linarith
  have he := Real.exp_one_gt_d9
  have he' := Real.exp_one_lt_d9
  constructor
  · apply div_pos _ hl
    have : -1 < log (log 2) := by
      rw [Real.lt_log_iff_exp_lt hl, Real.exp_neg, inv_lt_iff_one_lt_mul₀ (Real.exp_pos 1)]
      nlinarith
    linarith
  · rw [div_lt_one hl]
    have : log (log 2) < log 2 - 1 := by
      rw [Real.log_lt_iff_lt_exp hl, Real.exp_sub, Real.exp_log (by norm_num),
        lt_div_iff₀ (Real.exp_pos 1)]
      nlinarith
    linarith

theorem term_tele {β : ℝ} (h0 : 0 < β) (h1 : β ≤ 1) (j : ℕ) :
    β * ((j:ℝ) + 1) ^ (β - 1) ≤ ((j:ℝ) + 1) ^ β - (j:ℝ) ^ β := by
  set a : ℝ := (j:ℝ) + 1 with ha
  have ha1 : 1 ≤ a := by rw [ha]; have := Nat.cast_nonneg (α := ℝ) j; linarith
  have ha0 : 0 < a := by linarith
  have hj : (j:ℝ) = a * (1 + (-(1 / a))) := by
    rw [ha]; field_simp; ring
  have hs : -1 ≤ -(1 / a) := by
    have : 1 / a ≤ 1 := by rw [div_le_one ha0]; exact ha1
    linarith
  have hb := rpow_one_add_le_one_add_mul_self hs h0.le h1
  have hnn : 0 ≤ 1 + -(1 / a) := by linarith
  rw [hj, Real.mul_rpow ha0.le hnn, Real.rpow_sub_one ha0.ne']
  have hap : 0 < a ^ β := Real.rpow_pos_of_pos ha0 β
  have := mul_le_mul_of_nonneg_left hb hap.le
  have e : a ^ β * (1 + β * -(1 / a)) = a ^ β - β * (a ^ β / a) := by field_simp; ring
  linarith

theorem tele {β : ℝ} (h0 : 0 < β) (h1 : β ≤ 1) (n : ℕ) :
    ∑ j ∈ range n, ((j:ℝ) + 1) ^ (β - 1) ≤ (n:ℝ) ^ β / β := by
  rw [le_div_iff₀ h0]
  have hsum : ∑ j ∈ range n, (((j:ℝ) + 1) ^ β - (j:ℝ) ^ β) = (n:ℝ) ^ β := by
    have := Finset.sum_range_sub (fun j : ℕ => (j:ℝ) ^ β) n
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at this
    rw [this, Real.zero_rpow h0.ne', sub_zero]
  rw [mul_comm, Finset.mul_sum, ← hsum]
  exact Finset.sum_le_sum (fun j _ => term_tele h0 h1 j)

theorem w_pos (β : ℝ) (j : ℕ) : 0 < ((j:ℝ)+1)^(β - 1) / (log ((j:ℝ)+2))^((3:ℝ)/2) := by
  have h1 : (0:ℝ) < (j:ℝ) + 1 := by positivity
  have h2 : 0 < log ((j:ℝ) + 2) := Real.log_pos (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
  positivity

theorem lower {β : ℝ} (h1 : β ≤ 1) (n : ℕ) (hn : 2 ≤ n) :
    (n:ℝ) ^ β / (2 * log ((n:ℝ) + 1) ^ ((3:ℝ)/2)) ≤
      ∑ j ∈ range n, ((j:ℝ)+1)^(β - 1) / (log ((j:ℝ)+2))^((3:ℝ)/2) := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hlogn : 0 < log ((n:ℝ) + 1) := Real.log_pos (by linarith)
  have hL : 0 < log ((n:ℝ) + 1) ^ ((3:ℝ)/2) := Real.rpow_pos_of_pos hlogn _
  have hterm : ∀ j ∈ Ico (n / 2) n, (n:ℝ) ^ (β - 1) / log ((n:ℝ) + 1) ^ ((3:ℝ)/2) ≤
      ((j:ℝ)+1)^(β - 1) / (log ((j:ℝ)+2))^((3:ℝ)/2) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    have hj1 : (j:ℝ) + 1 ≤ n := by
      have : j + 1 ≤ n := hj.2
      exact_mod_cast this
    have hj0 : (0:ℝ) < (j:ℝ) + 1 := by positivity
    have hlj : 0 < log ((j:ℝ) + 2) := Real.log_pos (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
    have hlle : log ((j:ℝ) + 2) ≤ log ((n:ℝ) + 1) := Real.log_le_log (by positivity) (by linarith)
    apply div_le_div₀ (Real.rpow_pos_of_pos hj0 _).le
      (Real.rpow_le_rpow_of_nonpos hj0 hj1 (by linarith [h1]))
      (Real.rpow_pos_of_pos hlj _) (Real.rpow_le_rpow hlj.le hlle (by norm_num))
  have hsub : Ico (n / 2) n ⊆ range n := fun j hj => Finset.mem_range.2 (Finset.mem_Ico.1 hj).2
  have hpos : ∀ j ∈ range n, j ∉ Ico (n / 2) n →
      0 ≤ ((j:ℝ)+1)^(β - 1) / (log ((j:ℝ)+2))^((3:ℝ)/2) := fun j _ _ => (w_pos β j).le
  have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub hpos
  have h2 := Finset.card_nsmul_le_sum (Ico (n / 2) n) _ _ hterm
  rw [Nat.card_Ico, nsmul_eq_mul] at h2
  have hcard : (n:ℝ) / 2 ≤ ((n - n / 2 : ℕ) : ℝ) := by
    have : n ≤ 2 * (n - n / 2) := by omega
    have : (n:ℝ) ≤ 2 * ((n - n / 2 : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have hnpos : (0:ℝ) < n := by linarith
  have hsplit : (n:ℝ) ^ β = (n:ℝ) * (n:ℝ) ^ (β - 1) := by
    rw [Real.rpow_sub_one hnpos.ne']; field_simp
  calc (n:ℝ) ^ β / (2 * log ((n:ℝ) + 1) ^ ((3:ℝ)/2))
      = (n:ℝ) / 2 * ((n:ℝ) ^ (β - 1) / log ((n:ℝ) + 1) ^ ((3:ℝ)/2)) := by
        rw [hsplit]; field_simp
    _ ≤ ((n - n / 2 : ℕ) : ℝ) * ((n:ℝ) ^ (β - 1) / log ((n:ℝ) + 1) ^ ((3:ℝ)/2)) := by
        gcongr
    _ ≤ _ := h2.trans h1

theorem upper {β : ℝ} (h0 : 0 < β) (h1 : β ≤ 1) (n : ℕ) (hn : 4 ≤ n) :
    ∑ j ∈ range n, ((j:ℝ)+1)^(β - 1) / (log ((j:ℝ)+2))^((3:ℝ)/2) ≤
      ((n.sqrt : ℕ) : ℝ) ^ β / β / log 2 ^ ((3:ℝ)/2) +
        (n:ℝ) ^ β / β / log (((n.sqrt : ℕ) : ℝ) + 1) ^ ((3:ℝ)/2) := by
  set m := n.sqrt with hm
  have hm2 : 2 ≤ m := by
    rw [hm, Nat.le_sqrt]; omega
  have hmn : m ≤ n := Nat.sqrt_le_self n
  rw [← Finset.sum_range_add_sum_Ico _ hmn]
  have hl2 : 0 < log (2:ℝ) := Real.log_pos (by norm_num)
  have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm2
  have hlm : 0 < log ((m:ℝ) + 1) := Real.log_pos (by linarith)
  apply add_le_add
  · have hle : ∀ j ∈ range m, ((j:ℝ)+1)^(β - 1) / (log ((j:ℝ)+2))^((3:ℝ)/2) ≤
        ((j:ℝ)+1)^(β - 1) / log 2 ^ ((3:ℝ)/2) := by
      intro j _
      have hj0 : (0:ℝ) < (j:ℝ) + 1 := by positivity
      apply div_le_div_of_nonneg_left (Real.rpow_pos_of_pos hj0 _).le (Real.rpow_pos_of_pos hl2 _)
      exact Real.rpow_le_rpow hl2.le
        (Real.log_le_log (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) j; linarith)) (by norm_num)
    calc _ ≤ ∑ j ∈ range m, ((j:ℝ)+1)^(β - 1) / log 2 ^ ((3:ℝ)/2) := Finset.sum_le_sum hle
      _ = (∑ j ∈ range m, ((j:ℝ)+1)^(β - 1)) / log 2 ^ ((3:ℝ)/2) := by rw [Finset.sum_div]
      _ ≤ (m:ℝ) ^ β / β / log 2 ^ ((3:ℝ)/2) := by
        gcongr
        exact tele h0 h1 m
  · have hle : ∀ j ∈ Ico m n, ((j:ℝ)+1)^(β - 1) / (log ((j:ℝ)+2))^((3:ℝ)/2) ≤
        ((j:ℝ)+1)^(β - 1) / log ((m:ℝ) + 1) ^ ((3:ℝ)/2) := by
      intro j hj
      have hjm : (m:ℝ) ≤ j := by exact_mod_cast (Finset.mem_Ico.1 hj).1
      have hj0 : (0:ℝ) < (j:ℝ) + 1 := by positivity
      apply div_le_div_of_nonneg_left (Real.rpow_pos_of_pos hj0 _).le (Real.rpow_pos_of_pos hlm _)
      exact Real.rpow_le_rpow hlm.le (Real.log_le_log (by linarith) (by linarith)) (by norm_num)
    calc _ ≤ ∑ j ∈ Ico m n, ((j:ℝ)+1)^(β - 1) / log ((m:ℝ) + 1) ^ ((3:ℝ)/2) := Finset.sum_le_sum hle
      _ = (∑ j ∈ Ico m n, ((j:ℝ)+1)^(β - 1)) / log ((m:ℝ) + 1) ^ ((3:ℝ)/2) := by rw [Finset.sum_div]
      _ ≤ (∑ j ∈ range n, ((j:ℝ)+1)^(β - 1)) / log ((m:ℝ) + 1) ^ ((3:ℝ)/2) := by
        gcongr
        exact fun j hj => Finset.mem_range.2 (Finset.mem_Ico.1 hj).2
      _ ≤ (n:ℝ) ^ β / β / log ((m:ℝ) + 1) ^ ((3:ℝ)/2) := by
        gcongr
        exact tele h0 h1 n

theorem four_rpow : (4:ℝ) ^ ((3:ℝ)/2) = 8 := by
  rw [show (4:ℝ) = 2 ^ (2:ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
  rw [show (2:ℝ) * (3 / 2) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  norm_num

theorem two_rpow_le : (2:ℝ) ^ ((3:ℝ)/2) ≤ 3 := by
  rw [show (3:ℝ)/2 = 1 + 1/2 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one,
    ← Real.sqrt_eq_rpow]
  have : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  linarith

theorem key (x : ℕ) (hx : 1 ≤ x) (hL : (16:ℝ) ≤ log (x:ℝ)) :
    4 ≤ Nat.log 2 x / 2 + 1 ∧ ((Nat.log 2 x / 2 + 1 : ℕ) : ℝ) ≤ log (x:ℝ) ∧
      log (x:ℝ) / 2 ≤ ((Nat.log 2 x / 2 + 1 : ℕ) : ℝ) := by
  have hx0 : x ≠ 0 := by omega
  have hK1 := Nat.pow_log_le_self 2 hx0
  have hK2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) x
  set K := Nat.log 2 x with hKdef
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hA : (K:ℝ) * log 2 ≤ log (x:ℝ) := by
    have h : ((2:ℝ))^K ≤ (x:ℝ) := by exact_mod_cast hK1
    have := Real.log_le_log (by positivity) h
    rwa [Real.log_pow] at this
  have hB : log (x:ℝ) < ((K:ℝ) + 1) * log 2 := by
    have h : (x:ℝ) < (2:ℝ)^(K+1) := by exact_mod_cast hK2
    have := Real.log_lt_log (by positivity) h
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hA' : (K:ℝ) * 0.6931471803 ≤ log (x:ℝ) :=
    le_trans (mul_le_mul_of_nonneg_left hl2.le (Nat.cast_nonneg K)) hA
  have hB' : log (x:ℝ) < ((K:ℝ) + 1) * 0.6931471808 :=
    lt_of_lt_of_le hB (mul_le_mul_of_nonneg_left hl2'.le (by positivity))
  have hn1 : 2 * (K / 2 + 1) ≤ K + 2 := by omega
  have hn2 : K + 1 ≤ 2 * (K / 2 + 1) := by omega
  have hn1' : 2 * ((K / 2 + 1 : ℕ) : ℝ) ≤ K + 2 := by exact_mod_cast hn1
  have hn2' : (K:ℝ) + 1 ≤ 2 * ((K / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast hn2
  refine ⟨?_, by linarith, by linarith⟩
  have h6 : (6:ℝ) ≤ K := by linarith
  have h6' : 6 ≤ K := by exact_mod_cast h6
  omega

theorem main_gen {β : ℝ} (h0 : 0 < β) (h1 : β < 1) :
    (fun x : ℕ => ∑ j ∈ range (Nat.log 2 x / 2 + 1),
        ((j:ℝ)+1)^(β - 1) / (log ((j:ℝ)+2))^((3:ℝ)/2)) =Θ[atTop]
      (fun x : ℕ => log (x:ℝ)^β / log (log (x:ℝ))^((3:ℝ)/2)) := by
  have hLt : Tendsto (fun x : ℕ => log (x:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hE1 : ∀ᶠ x : ℕ in atTop, (16:ℝ) ≤ log (x:ℝ) := hLt.eventually (eventually_ge_atTop 16)
  have hE2 : ∀ᶠ x : ℕ in atTop, log (log (x:ℝ)) ^ ((3:ℝ)/2) ≤ log (x:ℝ) ^ (β/2) := by
    have h := (isLittleO_log_rpow_rpow_atTop ((3:ℝ)/2) (show 0 < β/2 by linarith)).bound
      (show (0:ℝ) < 1 by norm_num)
    filter_upwards [hLt.eventually h, hE1] with x hx h16
    have hl0 : 0 ≤ log (log (x:ℝ)) := Real.log_nonneg (by linarith)
    rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg hl0 _),
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hx
    exact hx
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  refine ⟨IsBigO.of_bound (11 / β) ?_, IsBigO.of_bound 12 ?_⟩
  · filter_upwards [hE1, hE2, eventually_ge_atTop 1] with x h16 hE2x hx1
    obtain ⟨hn4, hnL, hLn⟩ := key x hx1 h16
    set n := Nat.log 2 x / 2 + 1 with hn
    set L := log (x:ℝ) with hLdef
    have hL0 : 0 < L := by linarith
    have hlL : 2 ≤ log L := by
      rw [Real.le_log_iff_exp_le hL0]
      have := Real.exp_one_lt_d9
      have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h2]
      have he0 := Real.exp_pos 1
      have : Real.exp 1 ^ 2 < 8 := by nlinarith
      linarith
    have hA0 : 0 < L ^ β := Real.rpow_pos_of_pos hL0 β
    have hB0 : 0 < log L ^ ((3:ℝ)/2) := Real.rpow_pos_of_pos (by linarith) _
    have hup := upper h0 h1.le n hn4
    set m := n.sqrt with hm
    have hn4' : (4:ℝ) ≤ n := by exact_mod_cast hn4
    have hnpos : (0:ℝ) < n := by linarith
    -- second term
    have hm1 : log L / 4 ≤ log ((m:ℝ) + 1) := by
      have hsq : n < (m + 1) * (m + 1) := Nat.lt_succ_sqrt n
      have hsq' : (n:ℝ) ≤ ((m:ℝ) + 1) ^ 2 := by
        have : n ≤ (m + 1) ^ 2 := by nlinarith
        exact_mod_cast this
      have h1' : log (n:ℝ) ≤ 2 * log ((m:ℝ) + 1) := by
        have := Real.log_le_log hnpos hsq'
        rwa [Real.log_pow] at this
      have h2' : log (L / 2) ≤ log (n:ℝ) := Real.log_le_log (by linarith) hLn
      rw [Real.log_div hL0.ne' (by norm_num)] at h2'
      linarith
    have hm1pos : 0 < log L / 4 := by linarith
    have hT2 : (n:ℝ) ^ β / β / log ((m:ℝ) + 1) ^ ((3:ℝ)/2) ≤
        8 / β * (L ^ β / log L ^ ((3:ℝ)/2)) := by
      have hnb : (n:ℝ) ^ β ≤ L ^ β := Real.rpow_le_rpow hnpos.le hnL h0.le
      have hlb : (log L / 4) ^ ((3:ℝ)/2) ≤ log ((m:ℝ) + 1) ^ ((3:ℝ)/2) :=
        Real.rpow_le_rpow hm1pos.le hm1 (by norm_num)
      rw [Real.div_rpow (by linarith) (by norm_num), four_rpow] at hlb
      have hpos1 : 0 < log L ^ ((3:ℝ)/2) / 8 := by positivity
      calc (n:ℝ) ^ β / β / log ((m:ℝ) + 1) ^ ((3:ℝ)/2)
          ≤ L ^ β / β / (log L ^ ((3:ℝ)/2) / 8) := by
            apply div_le_div₀ (by positivity) (div_le_div_of_nonneg_right hnb h0.le) hpos1 hlb
        _ = 8 / β * (L ^ β / log L ^ ((3:ℝ)/2)) := by field_simp
    -- first term
    have hT1 : ((m:ℕ):ℝ) ^ β / β / log 2 ^ ((3:ℝ)/2) ≤ 3 / β * (L ^ β / log L ^ ((3:ℝ)/2)) := by
      have hmsq : (m:ℝ) ≤ Real.sqrt n := by
        rw [Real.le_sqrt (by positivity) hnpos.le]
        have : m * m ≤ n := Nat.sqrt_le n
        have : (m:ℝ) * m ≤ n := by exact_mod_cast this
        nlinarith
      have hmb : (m:ℝ) ^ β ≤ L ^ (β / 2) := by
        calc (m:ℝ) ^ β ≤ (Real.sqrt n) ^ β := Real.rpow_le_rpow (by positivity) hmsq h0.le
          _ = (n:ℝ) ^ (β / 2) := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hnpos.le]; ring_nf
          _ ≤ L ^ (β / 2) := Real.rpow_le_rpow hnpos.le hnL (by linarith)
      have hhalf : L ^ (β / 2) * L ^ (β / 2) = L ^ β := by
        rw [← Real.rpow_add hL0]; ring_nf
      have hLb : L ^ (β / 2) ≤ L ^ β / log L ^ ((3:ℝ)/2) := by
        rw [le_div_iff₀ hB0, ← hhalf]
        exact mul_le_mul_of_nonneg_left hE2x (Real.rpow_nonneg hL0.le _)
      have hl2b : (0.4:ℝ) ≤ log 2 ^ ((3:ℝ)/2) := by
        have h1' : log 2 ^ (2:ℝ) ≤ log 2 ^ ((3:ℝ)/2) :=
          Real.rpow_le_rpow_of_exponent_ge (by linarith) (by linarith) (by norm_num)
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast] at h1'
        nlinarith
      calc ((m:ℕ):ℝ) ^ β / β / log 2 ^ ((3:ℝ)/2)
          ≤ (L ^ β / log L ^ ((3:ℝ)/2)) / β / 0.4 := by
            apply div_le_div₀ (by positivity) (div_le_div_of_nonneg_right (hmb.trans hLb) h0.le)
              (by norm_num) hl2b
        _ ≤ 3 / β * (L ^ β / log L ^ ((3:ℝ)/2)) := by
            rw [div_div, div_le_iff₀ (by positivity)]
            have : 0 < L ^ β / log L ^ ((3:ℝ)/2) := by positivity
            field_simp
            nlinarith
    have hS0 : 0 ≤ ∑ j ∈ range n, ((j:ℝ)+1)^(β - 1) / (log ((j:ℝ)+2))^((3:ℝ)/2) :=
      Finset.sum_nonneg (fun j _ => (w_pos β j).le)
    rw [Real.norm_of_nonneg hS0, Real.norm_of_nonneg (by positivity)]
    have : 0 < L ^ β / log L ^ ((3:ℝ)/2) := by positivity
    calc _ ≤ _ := hup
      _ ≤ 3 / β * (L ^ β / log L ^ ((3:ℝ)/2)) + 8 / β * (L ^ β / log L ^ ((3:ℝ)/2)) :=
          add_le_add hT1 hT2
      _ = 11 / β * (L ^ β / log L ^ ((3:ℝ)/2)) := by ring
  · filter_upwards [hE1, eventually_ge_atTop 1] with x h16 hx1
    obtain ⟨hn4, hnL, hLn⟩ := key x hx1 h16
    set n := Nat.log 2 x / 2 + 1 with hn
    set L := log (x:ℝ) with hLdef
    have hL0 : 0 < L := by linarith
    have hlL : 2 ≤ log L := by
      rw [Real.le_log_iff_exp_le hL0]
      have := Real.exp_one_lt_d9
      have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h2]
      have he0 := Real.exp_pos 1
      have : Real.exp 1 ^ 2 < 8 := by nlinarith
      linarith
    have hn4' : (4:ℝ) ≤ n := by exact_mod_cast hn4
    have hlow := lower h1.le n (by omega)
    have hS0 : 0 ≤ ∑ j ∈ range n, ((j:ℝ)+1)^(β - 1) / (log ((j:ℝ)+2))^((3:ℝ)/2) :=
      Finset.sum_nonneg (fun j _ => (w_pos β j).le)
    have hB0 : 0 < log L ^ ((3:ℝ)/2) := Real.rpow_pos_of_pos (by linarith) _
    rw [Real.norm_of_nonneg hS0, Real.norm_of_nonneg (by positivity)]
    -- n^β ≥ L^β / 2
    have hnb : L ^ β / 2 ≤ (n:ℝ) ^ β := by
      have h1' : (L / 2) ^ β ≤ (n:ℝ) ^ β := Real.rpow_le_rpow (by linarith) hLn h0.le
      rw [Real.div_rpow hL0.le (by norm_num)] at h1'
      have h2b : (2:ℝ) ^ β ≤ 2 := by
        have := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 2 by norm_num) h1.le
        rwa [Real.rpow_one] at this
      have hLb : 0 < L ^ β := Real.rpow_pos_of_pos hL0 β
      calc L ^ β / 2 ≤ L ^ β / 2 ^ β := div_le_div_of_nonneg_left hLb.le (by positivity) h2b
        _ ≤ _ := h1'
    have hlog : log ((n:ℝ) + 1) ^ ((3:ℝ)/2) ≤ 3 * log L ^ ((3:ℝ)/2) := by
      have h1' : log ((n:ℝ) + 1) ≤ 2 * log L := by
        have : (n:ℝ) + 1 ≤ L ^ 2 := by nlinarith
        have := Real.log_le_log (by linarith) this
        rwa [Real.log_pow, Nat.cast_ofNat] at this
      have h2' : 0 ≤ log ((n:ℝ) + 1) := Real.log_nonneg (by linarith)
      calc log ((n:ℝ) + 1) ^ ((3:ℝ)/2) ≤ (2 * log L) ^ ((3:ℝ)/2) :=
            Real.rpow_le_rpow h2' h1' (by norm_num)
        _ = 2 ^ ((3:ℝ)/2) * log L ^ ((3:ℝ)/2) := Real.mul_rpow (by norm_num) (by linarith)
        _ ≤ 3 * log L ^ ((3:ℝ)/2) := by
            gcongr
            exact two_rpow_le
    have hlogpos : 0 < log ((n:ℝ) + 1) ^ ((3:ℝ)/2) :=
      Real.rpow_pos_of_pos (Real.log_pos (by linarith)) _
    calc L ^ β / log L ^ ((3:ℝ)/2) = 12 * ((L ^ β / 2) / (2 * (3 * log L ^ ((3:ℝ)/2)))) := by
          field_simp; ring
      _ ≤ 12 * ((n:ℝ) ^ β / (2 * log ((n:ℝ) + 1) ^ ((3:ℝ)/2))) := by
          gcongr
      _ ≤ _ := by gcongr

theorem sol : OMA.R_Erdos448_erdos_448_variants_ford_R1.H2 := by
  unfold OMA.R_Erdos448_erdos_448_variants_ford_R1.H2
  dsimp only
  have hb := beta_bounds
  have e1 : -(1 - (1 + log (log 2)) / log 2) = (1 + log (log 2)) / log 2 - 1 := by ring
  have e2 : 1 - (1 - (1 + log (log 2)) / log 2) = (1 + log (log 2)) / log 2 := by ring
  rw [e1, e2]
  exact main_gen hb.1 hb.2

end OMA.P2b448

theorem OMA.solution : OMA.R_Erdos448_erdos_448_variants_ford_R1.H2 := OMA.P2b448.sol
