import FormalConjectures.ErdosProblems.«233»
import Mathlib

/-! # Squared prime gaps from a weighted tail bound
For each threshold k, count the total length of gaps of length at least k.
Adding over k counts the square of each individual gap. The harmonic sum
costs one logarithm, and replacing the prime cutoff by its index costs another.
The remaining analytic estimate is stated with its Riemann hypothesis input. -/

namespace OMA.R_Erdos233_erdos_233_variants_upper_bound_unconditional_R1
open Filter Real Finset Asymptotics
open scoped BigOperators

def H1 : Prop := RiemannHypothesis

/-- The Selberg weighted tail estimate on dyadic prime intervals, in index coordinates. -/
def H2 : Prop := RiemannHypothesis → ∃ C : ℝ, 0 < C ∧ ∀ r k : ℕ, 0 < k →
  (∑ j ∈ Ico (Nat.primeCounting' (2^r)) (Nat.primeCounting' (2^(r+1))),
    if k ≤ primeGap j then (primeGap j : ℝ) else 0) ≤
      C * (2:ℝ)^r * (log ((2:ℝ)^r))^2 / k

lemma logSquare (x : ℝ) : log (x^2) = 2*log x := by simp [log_pow]
lemma logCube (x : ℝ) : log (x^3) = 3*log x := by simp [log_pow]

lemma endpoint : ∀ᶠ N : ℕ in atTop,
    Nat.nth Nat.Prime N ≤ N^2 ∧
    (Nat.nth Nat.Prime N : ℝ) * log 2 ≤ 6 * N * log N := by
  have two : 0 < log 2 := log_pos (by norm_num)
  have small := (Real.isLittleO_log_id_atTop.comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).bound (show 0 < log 2 / 6 by positivity)
  filter_upwards [eventually_ge_atTop 3,small] with N hN hlog
  have nr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have ln : 0 ≤ log (N : ℝ) := log_nonneg (by linarith)
  change ‖log (N : ℝ)‖ ≤ log 2 / 6 * ‖(N : ℝ)‖ at hlog
  rw [Real.norm_eq_abs,abs_of_nonneg ln,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg N)] at hlog
  let p := Nat.nth Nat.Prime N
  have p2 : 2 ≤ p := (Nat.le_add_left 2 N).trans (Nat.add_two_le_nth_prime N)
  have coarse : p ≤ N^2 := by
    by_contra! big
    have low : Nat.primeCounting (N^2) ≤ N := by
      have h := Nat.monotone_primeCounting' (show N^2+1 ≤ p by omega)
      simpa [p,← Nat.primeCounting_eq_primeCounting'_succ] using h
    have lpos : 0 < log ((N^2 : ℕ) : ℝ) := log_pos (by push_cast; nlinarith)
    have est := (div_le_iff₀ lpos).mp (Chebyshev.pi_ge (N^2))
    have lowR : (Nat.primeCounting (N^2) : ℝ) ≤ N := by exact_mod_cast low
    have upper := mul_le_mul_of_nonneg_right lowR lpos.le
    have hlog3 : log (((N^2 : ℕ) : ℝ)+1) ≤ 3 * log N := by
      rw [← logCube]
      apply log_le_log (by positivity)
      push_cast
      nlinarith [sq_nonneg ((N:ℝ)-1), mul_nonneg (sq_nonneg (N:ℝ)) (show 0 ≤ (N:ℝ)-2 by linarith)]
    push_cast at est upper hlog3
    rw [log_pow] at est upper
    norm_num at est upper
    have large := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2*(N:ℝ)+3 by positivity)
    nlinarith [mul_pos two (show (0:ℝ) < N by positivity),
      mul_nonneg two.le (mul_nonneg (show (0:ℝ) ≤ N by positivity) (show (0:ℝ) ≤ (N:ℝ)-3 by linarith))]
  refine ⟨coarse,?_⟩
  have primeCount : Nat.primeCounting p = N+1 := by
    change Nat.count Nat.Prime (p+1) = _
    rw [Nat.count_succ,if_pos (Nat.prime_nth_prime N)]
    exact congrArg (·+1) (Nat.primeCounting'_nth_eq N)
  have pp : (2:ℝ) ≤ p := by exact_mod_cast p2
  have lp : 0 < log (p:ℝ) := log_pos (by linarith)
  have est := (div_le_iff₀ lp).mp (Chebyshev.pi_ge p)
  rw [primeCount] at est
  push_cast at est
  have hplus : log ((p:ℝ)+1) ≤ 2*log p := by
    rw [← logSquare]
    apply log_le_log (by positivity)
    nlinarith [sq_nonneg ((p:ℝ)-1)]
  have logBound : log (p : ℝ) ≤ 2 * log N := by
    rw [← logSquare]
    apply log_le_log (by positivity)
    exact_mod_cast coarse
  change (p : ℝ) * log 2 ≤ _
  nlinarith [mul_le_mul_of_nonneg_left logBound (show 0 ≤ (N:ℝ)+3 by positivity),
    mul_nonneg ln (show 0 ≤ (N : ℝ)-3 by linarith)]

lemma sumTails {C : ℝ} (pos : 0 ≤ C)
    (blocks : ∀ r k : ℕ, 0 < k →
      (∑ j ∈ Ico (Nat.primeCounting' (2^r)) (Nat.primeCounting' (2^(r+1))),
        if k ≤ primeGap j then (primeGap j : ℝ) else 0) ≤ C*2^r*(log ((2:ℝ)^r))^2/k)
    (X k : ℕ) (hX : 2 ≤ X) (hk : 0 < k) :
    (∑ j ∈ range (Nat.primeCounting' X), if k ≤ primeGap j then (primeGap j : ℝ) else 0) ≤
      8 * C * X * (log X)^2 / k := by
  let w (j : ℕ) : ℝ := if k ≤ primeGap j then primeGap j else 0
  have kr : (0:ℝ) < k := by exact_mod_cast hk
  have powers (r : ℕ) : (∑ j ∈ range (Nat.primeCounting' (2^r)), w j) ≤
      C*(2:ℝ)^r*(log ((2:ℝ)^r))^2/k := by
    induction r with
    | zero => simp [Nat.primeCounting'_eq_zero_iff.mpr (show 1 ≤ 2 by decide)]
    | succ r ih =>
      have step : Nat.primeCounting' (2^r) ≤ Nat.primeCounting' (2^(r+1)) :=
        Nat.monotone_primeCounting' (by rw [pow_succ]; omega)
      rw [← sum_range_add_sum_Ico w step]
      have both := add_le_add ih (blocks r k hk)
      have logs : (log ((2:ℝ)^r))^2 ≤ (log ((2:ℝ)^(r+1)))^2 := by
        simp only [log_pow, Nat.cast_add, Nat.cast_one]
        have zero : 0 ≤ log 2 := log_nonneg (by norm_num)
        nlinarith [mul_nonneg (show 0 ≤ (r:ℝ) by positivity) (sq_nonneg (log 2))]
      have coeff : 0 ≤ C*(2:ℝ)^r := by positivity
      apply both.trans
      rw [pow_succ (2:ℝ) r]
      calc
        _ ≤ C * 2^r * (log ((2:ℝ)^(r+1)))^2/k +
            C * 2^r * (log ((2:ℝ)^(r+1)))^2/k :=
          add_le_add (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left logs coeff) kr.le)
            (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left logs coeff) kr.le)
        _ = _ := by rw [pow_succ (2:ℝ) r]; ring
  let r := Nat.log 2 X + 1
  have left : X ≤ 2^r := (Nat.lt_pow_succ_log_self (by decide : 1 < 2) X).le
  have right : 2^r ≤ 2*X := by
    dsimp [r]
    rw [pow_succ,mul_comm]
    exact Nat.mul_le_mul_left _ (Nat.pow_log_le_self 2 (by omega))
  have rightR : (2:ℝ)^r ≤ 2*X := by exact_mod_cast right
  have xr : (2:ℝ) ≤ X := by exact_mod_cast hX
  have lr : log ((2:ℝ)^r) ≤ 2*log X := by
    rw [← logSquare]
    apply log_le_log (by positivity)
    nlinarith [mul_nonneg (show 0 ≤ (X:ℝ) by positivity) (show 0 ≤ (X:ℝ)-2 by linarith)]
  have l0 : 0 ≤ log ((2:ℝ)^r) := log_nonneg (one_le_pow₀ (by norm_num))
  have mono : (∑ j ∈ range (Nat.primeCounting' X), w j) ≤
      ∑ j ∈ range (Nat.primeCounting' (2^r)), w j := by
    apply sum_le_sum_of_subset_of_nonneg (range_mono (Nat.monotone_primeCounting' left))
    intro j _ _
    dsimp [w]; split <;> positivity
  apply (mono.trans (powers r)).trans
  apply div_le_div_of_nonneg_right _ kr.le
  calc
    _ ≤ (C * (2*X)) * ((2*log X)^2) := by
      gcongr
    _ = _ := by ring

lemma layerCount (N X : ℕ) (bound : ∀ j < N, primeGap j ≤ X) :
    (∑ j ∈ range N, (primeGap j : ℝ)^2) =
    ∑ k ∈ Icc 1 X, ∑ j ∈ range N, if k ≤ primeGap j then (primeGap j : ℝ) else 0 := by
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  have gj := bound j (mem_range.mp hj)
  have eq : (Icc 1 X).filter (fun k => k ≤ primeGap j) = Icc 1 (primeGap j) := by
    ext; simp; omega
  rw [← sum_filter,eq,sum_const,Nat.card_Icc]
  simp [pow_two]


theorem main : H1 → H2 → type_of% @Erdos233.erdos_233.variants.upper_bound_unconditional := by
  intro rh tail
  obtain ⟨C,cpos,blocks⟩ := tail rh
  have two : 0 < log 2 := log_pos (by norm_num)
  apply IsBigO.of_bound (576*C / log 2)
  have large := (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1
  filter_upwards [endpoint,large] with N he hlog
  change 1 ≤ log (N:ℝ) at hlog
  let p := Nat.nth Nat.Prime N
  have p2 : 2 ≤ p := (Nat.le_add_left 2 N).trans (Nat.add_two_le_nth_prime N)
  have coarse : p ≤ N^2 := he.1
  have bound : (p:ℝ) ≤ (6*N*log N)/log 2 := (le_div_iff₀ two).mpr he.2
  have mono := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone
  have gaps (j : ℕ) (hj : j < N) : primeGap j ≤ p :=
    (Nat.sub_le _ _).trans (mono (Nat.succ_le_of_lt hj))
  have first (k : ℕ) (hk : k ∈ Icc 1 p) :
      (∑ j ∈ range N, if k ≤ primeGap j then (primeGap j : ℝ) else 0) ≤
        8*C*p*(log p)^2 * (k:ℝ)⁻¹ := by
    simpa [p,div_eq_mul_inv] using sumTails cpos.le blocks p k p2 (mem_Icc.mp hk).1
  have lp : 0 ≤ log (p:ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
  have ln : 0 ≤ log (N:ℝ) := by linarith
  have lp2 : log (p:ℝ) ≤ 2*log N := by
    rw [← logSquare]
    apply log_le_log (by exact_mod_cast (show 0 < p by omega))
    exact_mod_cast coarse
  have harm : (∑ k ∈ Icc 1 p, (k:ℝ)⁻¹) ≤ 1+log p := by
    simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] using harmonic_le_one_add_log p
  have sqr : 0 ≤ ∑ j ∈ range N, (primeGap j:ℝ)^2 := sum_nonneg (fun _ _ => sq_nonneg _)
  change ‖∑ j ∈ range N, (primeGap j:ℝ)^2‖ ≤ 576*C/log 2 * ‖(N:ℝ)*(log N)^4‖
  rw [Real.norm_of_nonneg sqr, Real.norm_of_nonneg (by positivity : 0 ≤ (N:ℝ)*(log N)^4),
    layerCount N p gaps]
  calc
    _ ≤ ∑ k ∈ Icc 1 p, 8*C*p*(log p)^2 * (k:ℝ)⁻¹ := sum_le_sum first
    _ = 8*C*p*(log p)^2 * ∑ k ∈ Icc 1 p, (k:ℝ)⁻¹ := (mul_sum ..).symm
    _ ≤ 8*C*p*(log p)^2 * (1+log p) := mul_le_mul_of_nonneg_left harm (by positivity)
    _ ≤ 8*C*((6*N*log N)/log 2)*(2*log N)^2*(3*log N) := by
      have last : 1+log (p:ℝ) ≤ 3*log N := by linarith
      gcongr
    _ = _ := by ring

end OMA.R_Erdos233_erdos_233_variants_upper_bound_unconditional_R1
