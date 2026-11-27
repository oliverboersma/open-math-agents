import OMAReductions.R_Erdos402_erdos_402_variants_szegedy_zaharescu_weak_R1_H2_R1_H1_R1
import Mathlib

-- Step Erdos402.erdos_402.variants.szegedy_zaharescu_weak.R1.H2.R1.H1.R1.H2: hypothesis H2 of
-- reduction Erdos402.erdos_402.variants.szegedy_zaharescu_weak.R1.H2.R1.H1.R1
-- Credit: @ivillar

/-!
`ψ x - ψ y = (θ x - θ y) + ((ψ - θ) x - (ψ - θ) y)`. Mathlib gives `ψ - θ ≤ C₀ √x` and `θ ≤ ψ`,
and `θ x - θ y` is the sum of `log p ≤ log x` over the primes in `(y, x]`.
-/

open Chebyshev in
theorem OMA.solution :
    OMA.R_Erdos402_erdos_402_variants_szegedy_zaharescu_weak_R1_H2_R1_H1_R1.H2 := by
  unfold OMA.R_Erdos402_erdos_402_variants_szegedy_zaharescu_weak_R1_H2_R1_H1_R1.H2
  obtain ⟨C0, hC0⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨max C0 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro x y hyx
  have h1 := hC0 (x : ℝ)
  have h2 : θ (y : ℝ) ≤ ψ (y : ℝ) := Chebyshev.theta_le_psi _
  have hsub : Nat.primesLE y ⊆ Nat.primesLE x := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨le_trans hp.1 hyx, hp.2⟩
  have hset : Nat.primesLE x \ Nat.primesLE y = (Finset.Ioc y x).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_sdiff, Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨by by_contra h; exact h3 ⟨by omega, h2⟩, h1⟩, h2⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h2, h3⟩, fun h => by omega⟩
  have h3 : θ (x : ℝ) - θ (y : ℝ) ≤
      (((Finset.Ioc y x).filter Nat.Prime).card : ℝ) * Real.log x := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log,
      ← Finset.sum_sdiff hsub, hset, add_sub_cancel_right]
    calc (∑ p ∈ (Finset.Ioc y x).filter Nat.Prime, Real.log p)
        ≤ ∑ _p ∈ (Finset.Ioc y x).filter Nat.Prime, Real.log x := by
          apply Finset.sum_le_sum
          intro p hp
          obtain ⟨hpI, hpp⟩ := Finset.mem_filter.mp hp
          exact Real.log_le_log (by exact_mod_cast hpp.pos)
            (by exact_mod_cast (Finset.mem_Ioc.mp hpI).2)
      _ = (((Finset.Ioc y x).filter Nat.Prime).card : ℝ) * Real.log x := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have h4 : C0 * Real.sqrt x ≤ max C0 1 * Real.sqrt x :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
  linarith
