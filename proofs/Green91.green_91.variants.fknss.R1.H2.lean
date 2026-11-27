import OMAReductions.R_Green91_green_91_variants_fknss_R1
import Mathlib

-- Step Green91.green_91.variants.fknss.R1.H2: hypothesis H2 of reduction Green91.green_91.variants.fknss.R1
-- Credit: @ivillar

/-!
Diagonal selection. For each `k` choose `N k` with `P j n ∈ [1 - 1/k, 1 + 1/k]` for all `j ≤ k`
and `n ≥ N k`, make the thresholds monotone (`M k = max_{i ≤ k} N i + k`), and let `k(n)` be the
largest `k ≤ n` with `M k ≤ n`. Then `k(n) → ∞` and `P (k n) n ∈ [1 - 1/k(n), 1 + 1/k(n)]`.
-/

open Filter in
theorem OMA.solution : OMA.R_Green91_green_91_variants_fknss_R1.H2 := by
  unfold OMA.R_Green91_green_91_variants_fknss_R1.H2
  intro P hP
  have hev : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ j ∈ Finset.range (k + 1),
      P j n ∈ Set.Icc (1 - ((k : ENNReal))⁻¹) (1 + ((k : ENNReal))⁻¹) := by
    intro k
    rw [Filter.eventually_all_finset]
    intro j _
    exact (ENNReal.tendsto_nhds ENNReal.one_ne_top).mp (hP j) _
      (ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top k))
  choose N hN using fun k => eventually_atTop.mp (hev k)
  let M : ℕ → ℕ := fun k => (Finset.range (k + 1)).sup N + k
  have hMmono : Monotone M := by
    intro a b hab
    apply Nat.add_le_add _ hab
    apply Finset.sup_mono
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  have hMN : ∀ k, N k ≤ M k := fun k =>
    le_trans (Finset.le_sup (Finset.self_mem_range_succ k)) (Nat.le_add_right _ _)
  have hMk : ∀ k, k ≤ M k := fun k => Nat.le_add_left _ _
  let kk : ℕ → ℕ := fun n => Nat.findGreatest (fun k => M k ≤ n) n
  have hkk_spec : ∀ n, M 0 ≤ n → M (kk n) ≤ n := fun n hn =>
    Nat.findGreatest_spec (P := fun k => M k ≤ n) (Nat.zero_le n) hn
  have hkk_ge : ∀ K n, M K ≤ n → K ≤ kk n := fun K n h =>
    Nat.le_findGreatest (le_trans (hMk K) h) h
  refine ⟨kk, ?_, ?_⟩
  · rw [tendsto_atTop_atTop]
    intro K
    exact ⟨M K, fun n hn => hkk_ge K n hn⟩
  · rw [ENNReal.tendsto_nhds ENNReal.one_ne_top]
    intro ε hε
    obtain ⟨K, hK⟩ := ENNReal.exists_inv_nat_lt hε.ne'
    filter_upwards [eventually_ge_atTop (M K)] with n hn
    have h0 : M 0 ≤ n := le_trans (hMmono (Nat.zero_le K)) hn
    have hk1 := hkk_spec n h0
    have hk2 := hkk_ge K n hn
    have hin := hN (kk n) n (le_trans (hMN _) hk1) (kk n) (Finset.self_mem_range_succ _)
    have hεle : ((kk n : ENNReal))⁻¹ ≤ ε :=
      le_trans (ENNReal.inv_le_inv.mpr (by exact_mod_cast hk2)) hK.le
    exact ⟨le_trans (tsub_le_tsub_left hεle 1) hin.1, le_trans hin.2 (add_le_add_right hεle 1)⟩
