import OMAReductions.R_Erdos930_erdos_930_variants_consecutive_integers_R1_H4_R1_H2_R1
import Mathlib

/-! Partial summation transfers a one-sided estimate for the first Chebyshev function to the desired prime count. Above five million, the derivative of the comparison function dominates the upper bound for the Abel integrand. The two finite inputs can be checked separately. For the initial segment only primes and the left endpoint need testing, since between primes the left side increases by at most one per integer. -/
open Real

namespace OMA.R_Erdos930_erdos_930_variants_consecutive_integers_R1_H4_R1_H2_R1_H1_R1

/-- Finite verification at the jumps of the prime count and the left endpoint. -/
def H1 : Prop := ∀ k : ℕ, 60184 ≤ k → k < 5000000 → k=60184 ∨ k.Prime →
  (k.primeCounting:ℝ)*(log k-11/10) ≤ k

/-- A single finite sum and prime count anchor partial summation at five million. -/
def H2 : Prop := let T : ℝ := 5000000
  (Nat.primeCounting 5000000 : ℝ) - Chebyshev.theta T / log T ≤
    T/(log T-11/10) - T/log T - T/(5*(log T)^3)

/-- The upper half of Dusart 2018, Theorem 4.2, with k = 2 and eta = 0.2.
The published threshold 3594641 is below five million. -/
def H3 : Prop := ∀ t : ℝ, 5000000 ≤ t → Chebyshev.theta t ≤ t + t/(5*(log t)^2)
open Real MeasureTheory Set

private lemma logLarge930 {t : ℝ} (ht : 5000000 ≤ t) : 14 ≤ log t := by
  apply (le_log_iff_exp_le (by linarith)).2
  calc
    exp 14 = exp 1 ^ 14 := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ (3:ℝ)^14 := by gcongr; exact exp_one_lt_three.le
    _ ≤ t := by norm_num; linarith

private lemma slope930 {L : ℝ} (h : 14 ≤ L) :
    1/L^2 + 1/(5*L^4) ≤
    1/(L-11/10) - 1/(L-11/10)^2 - 1/L + 1/L^2 - 1/(5*L^3) + 3/(5*L^4) := by
  generalize he : L - 11/10 = D
  have hD : 0 < D := by linarith
  have hL : 0 < L := by linarith
  field_simp
  rw [← he]
  obtain ⟨u, hu, rfl⟩ := exists_nonneg_add_of_le h
  rw [← sub_nonneg]
  ring_nf
  positivity

private lemma model930 (t : ℝ) (ht : 5000000 ≤ t) :
    HasDerivAt (fun x : ℝ => x/(log x-11/10) - x/log x - x/(5*(log x)^3))
    (1/(log t-11/10) - 1/(log t-11/10)^2 - 1/log t + 1/(log t)^2
      - 1/(5*(log t)^3) + 3/(5*(log t)^4)) t := by
  have hl := logLarge930 ht
  have ht0 : t ≠ 0 := by linarith
  have hl0 : log t ≠ 0 := by linarith
  have hk : log t - 11/10 ≠ 0 := by linarith
  have l := hasDerivAt_log ht0
  have d := hasDerivAt_id t
  have der := ((d.div (l.sub_const (11/10)) hk).sub (d.div l hl0)).sub
    (d.div ((l.pow 3).const_mul 5) (mul_ne_zero (by norm_num) (pow_ne_zero _ hl0)))
  apply der.congr_deriv
  dsimp
  field_simp
  ring

private theorem transfer930
    (anch : let T : ℝ := 5000000
      (Nat.primeCounting 5000000 : ℝ) - Chebyshev.theta T / log T ≤
        T/(log T-11/10) - T/log T - T/(5*(log T)^3))
    (bound : ∀ t : ℝ, 5000000 ≤ t → Chebyshev.theta t ≤ t + t/(5*(log t)^2))
    (k : ℕ) (hk : 5000000 ≤ k) : (k.primeCounting : ℝ)*(log k-11/10) ≤ k := by
  let T : ℝ := 5000000
  have hx : T ≤ (k : ℝ) := by dsimp [T]; exact_mod_cast hk
  let v := fun t : ℝ => Chebyshev.theta t / (t*(log t)^2)
  let G := fun t : ℝ => t/(log t-11/10) - t/log t - t/(5*(log t)^3)
  let g := fun t : ℝ => 1/(log t-11/10) - 1/(log t-11/10)^2 - 1/log t + 1/(log t)^2
      - 1/(5*(log t)^3) + 3/(5*(log t)^4)
  have vi (x : ℝ) (hx2 : 2≤x) : IntervalIntegrable v volume 2 x := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hx2).2
    exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq x).mono_set Ioc_subset_Icc_self
  have ht2 : (2:ℝ) ≤ T := by norm_num [T]
  have hT := vi T ht2
  have hx2 := ht2.trans hx
  have vx := hT.symm.trans (vi k hx2)
  have hgc : ContinuousOn g (uIcc T k) := by
    rw [uIcc_of_le hx]
    intro t ht
    have hlog := logLarge930 ht.1
    have ht0 : t ≠ 0 := by dsimp [T] at ht; linarith [ht.1]
    have hl0 : log t ≠ 0 := by linarith
    have hd0 : log t - 11/10 ≠ 0 := by linarith
    dsimp only [g]
    fun_prop (disch := first | positivity | assumption)
  have gi := hgc.intervalIntegrable (μ := volume)
  have hmono : (∫ t in T..(k:ℝ), v t) ≤ ∫ t in T..(k:ℝ), g t := by
    apply intervalIntegral.integral_mono_on hx vx gi
    intro t ht
    have t0 : 0 < t := by dsimp [T] at ht; linarith [ht.1]
    have hlog := logLarge930 ht.1
    have l0 : 0 < log t := by linarith
    calc
      v t ≤ (t+t/(5*(log t)^2))/(t*(log t)^2) :=
        div_le_div_of_nonneg_right (bound t ht.1) (by positivity)
      _ = 1/(log t)^2 + 1/(5*(log t)^4) := by field_simp <;> ring
      _ ≤ g t := slope930 hlog
  have ftc : (∫ t in T..(k:ℝ), g t) = G k - G T := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ gi
    intro t ht
    rw [uIcc_of_le hx] at ht
    exact model930 t ht.1
  rw [ftc] at hmono
  have hsum := intervalIntegral.integral_add_adjacent_intervals hT vx
  have hbase := Chebyshev.primeCounting_eq_theta_div_log_add_integral ht2
  have htop := Chebyshev.primeCounting_eq_theta_div_log_add_integral hx2
  rw [Nat.floor_natCast] at htop
  have hf : ⌊T⌋₊ = 5000000 := Nat.floor_natCast 5000000
  rw [hf] at hbase
  change (Nat.primeCounting 5000000 : ℝ) = Chebyshev.theta T / log T + ∫ t in (2:ℝ)..T, v t at hbase
  change (k.primeCounting : ℝ) = Chebyshev.theta k / log k + ∫ t in (2:ℝ)..(k:ℝ), v t at htop
  change (Nat.primeCounting 5000000 : ℝ) - Chebyshev.theta T / log T ≤ G T at anch
  have l0 := logLarge930 hx
  have hlog : 0 < log (k:ℝ) := by linarith
  have hd : 0 < log (k:ℝ)-11/10 := by linarith
  have he : Chebyshev.theta k / log k ≤ (k:ℝ)/log k + (k:ℝ)/(5*(log k)^3) := by
    calc
      _ ≤ ((k:ℝ) + (k:ℝ)/(5*(log k)^2)) / log k :=
        div_le_div_of_nonneg_right (bound k hx) hlog.le
      _ = _ := by field_simp <;> ring
  apply (le_div_iff₀ hd).1
  dsimp only [G] at hmono anch
  linarith


open Real

private lemma pc_le_self930 (n : ℕ) : n.primeCounting ≤ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    change Nat.count Nat.Prime ((k+1)+1) ≤ k+1
    change Nat.count Nat.Prime (k+1) ≤ k at ih
    rw [Nat.count_succ]
    split <;> omega

private theorem finite930
    (hp : ∀ k : ℕ, 60184 ≤ k → k < 5000000 → k=60184 ∨ k.Prime →
      (k.primeCounting:ℝ)*(log k-11/10) ≤ k)
    (k : ℕ) (hk : 60184 ≤ k) (hT : k < 5000000) :
    (k.primeCounting:ℝ)*(log k-11/10) ≤ k := by
  induction k with
  | zero => omega
  | succ n ih =>
    by_cases hit : n+1=60184 ∨ (n+1).Prime
    · exact hp _ hk hT hit
    push_neg at hit
    have hl : 60184 ≤ n := by omega
    have hn : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
    have pc : (n+1).primeCounting = n.primeCounting :=
      Nat.count_succ_eq_count_iff.mpr hit.2
    have ih' := ih hl (by omega)
    have hcnt : (n.primeCounting:ℝ) ≤ n := by exact_mod_cast pc_le_self930 n
    have delta : log ((n:ℝ)+1) - log n ≤ 1/(n:ℝ) := by
      rw [← log_div (by positivity) hn.ne']
      calc
        _ ≤ ((n:ℝ)+1)/n - 1 := log_le_sub_one_of_pos (by positivity)
        _ = _ := by field_simp; ring
    have inc := mul_le_mul_of_nonneg_left delta (show (0:ℝ)≤n.primeCounting by positivity)
    have le1 : (n.primeCounting:ℝ) * (1/n) ≤ 1 := by
      simpa only [mul_one_div,one_mul] using (div_le_one hn).mpr hcnt
    rw [pc, Nat.cast_add_one]
    linarith


theorem main : H1 → H2 → H3 → OMA.R_Erdos930_erdos_930_variants_consecutive_integers_R1_H4_R1_H2_R1.H1 := by
  intro finite anchor theta k hk
  by_cases ht : k < 5000000
  · exact finite930 finite k hk ht
  · exact transfer930 anchor theta k (Nat.le_of_not_gt ht)

end OMA.R_Erdos930_erdos_930_variants_consecutive_integers_R1_H4_R1_H2_R1_H1_R1
