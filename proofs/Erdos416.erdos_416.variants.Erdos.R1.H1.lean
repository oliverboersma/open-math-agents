import OMAReductions.R_Erdos416_erdos_416_variants_Erdos_R1
import Mathlib

-- Step Erdos416.erdos_416.variants.Erdos.R1.H1: hypothesis H1 of reduction Erdos416.erdos_416.variants.Erdos.R1
-- Credit: @ivillar

/-!
`V(x) ≥ π(⌊x⌋)`, since `p ↦ p - 1 = φ(p)` is injective on primes `p ≤ ⌊x⌋`. Mathlib's Chebyshev
bounds give `π(N) log N ≥ ψ(N) ≥ N log 2 - log (N + 1)`, so `π(N) log x ≥ x / 2` for large `x`,
while `x (log x) ^ (-1 - ε) ≤ (x / 2) / log x` once `(log x) ^ (-ε) ≤ 1 / 2`.
-/

open Filter Real in
theorem OMA.solution : OMA.R_Erdos416_erdos_416_variants_Erdos_R1.H1 := by
  unfold OMA.R_Erdos416_erdos_416_variants_Erdos_R1.H1
  intro ε hε
  have h1 : ∀ᶠ x : ℝ in atTop, Real.log x ^ (-ε) ≤ 1 / 2 :=
    Real.tendsto_log_atTop.eventually
      ((tendsto_rpow_neg_atTop hε).eventually (ge_mem_nhds (by norm_num : (0:ℝ) < 1 / 2)))
  have h2 : ∀ᶠ x : ℝ in atTop, Real.log (x + 1) ≤ 1 / 40 * (x + 1) := by
    have hb := Real.isLittleO_log_id_atTop.bound (show (0:ℝ) < 1 / 40 by norm_num)
    filter_upwards [(tendsto_atTop_add_const_right atTop 1 tendsto_id).eventually hb,
      eventually_ge_atTop (1:ℝ)] with x hx hx1
    simp only [id, Real.norm_eq_abs] at hx
    have h0 : 0 ≤ Real.log (x + 1) := Real.log_nonneg (by linarith)
    rw [abs_of_nonneg h0, abs_of_nonneg (by linarith)] at hx
    exact hx
  filter_upwards [h1, h2, eventually_ge_atTop (100:ℝ)] with x h1 h2 hx
  set N := ⌊x⌋₊ with hN
  have hNx : (N:ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxN : x < (N:ℝ) + 1 := Nat.lt_floor_add_one x
  have hN1 : (1:ℝ) ≤ N := by linarith
  -- V x ≥ π N
  have hV : (Nat.primeCounting N : ℝ) ≤ Erdos416.V x := by
    unfold Erdos416.V
    rw [← hN]
    norm_cast
    rw [← Nat.primesLE_card_eq_primeCounting]
    apply Finset.card_le_card_of_injOn (fun p => p - 1)
    · intro p hp
      obtain ⟨hpN, hpp⟩ := Nat.mem_primesLE.mp hp
      have h2p := hpp.two_le
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, p, Nat.totient_prime hpp⟩
    · intro p hp q hq hpq
      have h2p := (Nat.mem_primesLE.mp hp).2.two_le
      have h2q := (Nat.mem_primesLE.mp hq).2.two_le
      simp only at hpq
      omega
  -- Chebyshev
  have c1 := Chebyshev.psi_le_primeCounting_mul_log N
  have c2 := Chebyshev.psi_ge N
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogN : Real.log N ≤ Real.log x := Real.log_le_log (by linarith) hNx
  have hlogN1 : Real.log ((N:ℝ) + 1) ≤ Real.log (x + 1) := Real.log_le_log (by linarith) (by linarith)
  have hpi0 : (0:ℝ) ≤ (Nat.primeCounting N : ℝ) := Nat.cast_nonneg _
  have hl2 := Real.log_two_gt_d9
  have key : x / 2 ≤ (Nat.primeCounting N : ℝ) * Real.log x := by
    have : (Nat.primeCounting N : ℝ) * Real.log N ≤ (Nat.primeCounting N : ℝ) * Real.log x :=
      mul_le_mul_of_nonneg_left hlogN hpi0
    nlinarith
  have hrp : Real.log x ^ (-1 - ε) = Real.log x ^ (-ε) * (Real.log x)⁻¹ := by
    rw [show (-1 - ε) = -ε + -1 by ring, Real.rpow_add hlogx, Real.rpow_neg_one]
  have hpos : 0 ≤ Real.log x ^ (-ε) := Real.rpow_nonneg hlogx.le _
  calc x * Real.log x ^ (-1 - ε) = x * Real.log x ^ (-ε) / Real.log x := by
        rw [hrp]; field_simp
    _ ≤ (x / 2) / Real.log x := by
        apply div_le_div_of_nonneg_right _ hlogx.le
        nlinarith
    _ ≤ (Nat.primeCounting N : ℝ) := by
        rw [div_le_iff₀ hlogx]; exact key
    _ ≤ Erdos416.V x := hV
