import OMAReductions.R_ElliottHalberstamConjecture_elliott_halberstam_variants_bombieri_vinogradov_R1
import Mathlib

/-! The three finite Abel summation lemmas below are from Jonas Whidden (@kimihiro64), kimihiro64/bombieri-vinogradov, commit 7a1748306e026825ed6a5555516cc2f28989b2ac. Used under Apache-2.0. The partialBound estimate removes the nonprime prime powers using Chebyshev’s exact remainder. -/
namespace BombieriVinogradov.RealAnalysis

/-- Finite summation by parts, including an empty interval and signed coefficients. -/
theorem sum_Ioc_mul_eq_abel (F g : Nat -> Real) {R Q : Nat} (hRQ : R <= Q) :
    Finset.sum (Finset.Ioc R Q) (fun n => F n * g n) =
      Finset.sum (Finset.Icc 1 Q) F * g Q -
        Finset.sum (Finset.Icc 1 R) F * g R +
          Finset.sum (Finset.Ico R Q)
            (fun k => Finset.sum (Finset.Icc 1 k) F * (g k - g (k + 1))) := by
  induction Q, hRQ using Nat.le_induction with
  | base => simp
  | succ Q hRQ ih =>
    rw [Finset.sum_Ioc_succ_top hRQ, Finset.sum_Ico_succ_top hRQ,
      Finset.sum_Icc_succ_top (Nat.succ_pos Q), ih]
    ring

end BombieriVinogradov.RealAnalysis

namespace BombieriVinogradov.RealAnalysis

/-- Exact partial summation for coefficients vanishing at one. -/
theorem sum_Icc_div_log_eq_abel (F : Nat -> Real) {N : Nat}
    (hN : 2 <= N) (hOne : F 1 = 0) :
    Finset.sum (Finset.Icc 2 N) (fun n => F n / Real.log (n : Real)) =
      Finset.sum (Finset.Icc 1 N) F / Real.log (N : Real) +
        Finset.sum (Finset.Ico 2 N) (fun k =>
          Finset.sum (Finset.Icc 1 k) F *
            (1 / Real.log (k : Real) - 1 / Real.log ((k : Real) + 1))) := by
  have hAbel := sum_Ioc_mul_eq_abel F (fun n => 1 / Real.log (n : Real)) hN
  have hInitial : Finset.sum (Finset.Icc 1 2) F = F 2 := by
    norm_num [Finset.sum_Icc_succ_top, hOne]
  have hIntervals : Finset.Icc 2 N = insert 2 (Finset.Ioc 2 N) :=
    (Finset.Ioc_insert_left hN).symm
  calc
    Finset.sum (Finset.Icc 2 N) (fun n => F n / Real.log (n : Real)) =
        F 2 / Real.log ((2 : Nat) : Real) +
          Finset.sum (Finset.Ioc 2 N) (fun n => F n / Real.log (n : Real)) := by
      rw [hIntervals, Finset.sum_insert]
      simp
    _ = F 2 / Real.log ((2 : Nat) : Real) +
        Finset.sum (Finset.Ioc 2 N) (fun n => F n * (1 / Real.log (n : Real))) := by
      apply congrArg (fun z : Real => F 2 / Real.log ((2 : Nat) : Real) + z)
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = F 2 / Real.log ((2 : Nat) : Real) +
        (Finset.sum (Finset.Icc 1 N) F * (1 / Real.log (N : Real)) -
          Finset.sum (Finset.Icc 1 2) F * (1 / Real.log ((2 : Nat) : Real)) +
            Finset.sum (Finset.Ico 2 N) (fun k =>
              Finset.sum (Finset.Icc 1 k) F *
                (1 / Real.log (k : Real) - 1 / Real.log ((k : Real) + 1)))) := by
      congr 1
      simpa only [Nat.cast_add, Nat.cast_one] using hAbel
    _ = Finset.sum (Finset.Icc 1 N) F / Real.log (N : Real) +
        Finset.sum (Finset.Ico 2 N) (fun k =>
          Finset.sum (Finset.Icc 1 k) F *
            (1 / Real.log (k : Real) - 1 / Real.log ((k : Real) + 1))) := by
      rw [hInitial]
      ring

end BombieriVinogradov.RealAnalysis

namespace BombieriVinogradov.RealAnalysis

/-- Reciprocal logarithms decrease on natural arguments at least two. -/
theorem log_reciprocal_difference_nonneg {k : Nat} (hk : 2 <= k) :
    0 <= 1 / Real.log (k : Real) - 1 / Real.log ((k : Real) + 1) := by
  have hkPos : (0 : Real) < (k : Real) := by positivity
  have hLogPos : 0 < Real.log (k : Real) := Real.log_pos (by
    have hkCast : (2 : Real) <= (k : Real) := Nat.cast_le.mpr hk
    linarith)
  have hLogLe : Real.log (k : Real) <= Real.log ((k : Real) + 1) :=
    Real.log_le_log hkPos (by linarith)
  exact sub_nonneg.mpr (one_div_le_one_div_of_le hLogPos hLogLe)

/-- The positive reciprocal-log differences telescope. -/
theorem sum_log_reciprocal_differences {N : Nat} (hN : 2 <= N) :
    Finset.sum (Finset.Ico 2 N) (fun k =>
      1 / Real.log (k : Real) - 1 / Real.log ((k : Real) + 1)) =
        1 / Real.log (2 : Real) - 1 / Real.log (N : Real) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_Ico_succ_top hN, ih]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

/-- A uniform cumulative bound controls the reciprocal-log weighted sum. -/
theorem abs_sum_Icc_div_log_le (F : Nat -> Real) {N : Nat} {D : Real}
    (hN : 2 <= N) (hOne : F 1 = 0)
    (hBound : forall k : Nat, 1 <= k -> k <= N ->
      abs (Finset.sum (Finset.Icc 1 k) F) <= D) :
    abs (Finset.sum (Finset.Icc 2 N) (fun n => F n / Real.log (n : Real))) <=
      D / Real.log (2 : Real) := by
  have hLogN : 0 < Real.log (N : Real) := Real.log_pos (by
    have hNCast : (2 : Real) <= (N : Real) := Nat.cast_le.mpr hN
    linarith)
  rw [sum_Icc_div_log_eq_abel F hN hOne]
  calc
    abs (Finset.sum (Finset.Icc 1 N) F / Real.log (N : Real) +
        Finset.sum (Finset.Ico 2 N) (fun k =>
          Finset.sum (Finset.Icc 1 k) F *
            (1 / Real.log (k : Real) - 1 / Real.log ((k : Real) + 1)))) <=
      abs (Finset.sum (Finset.Icc 1 N) F / Real.log (N : Real)) +
        abs (Finset.sum (Finset.Ico 2 N) (fun k =>
          Finset.sum (Finset.Icc 1 k) F *
            (1 / Real.log (k : Real) - 1 / Real.log ((k : Real) + 1)))) :=
      abs_add_le _ _
    _ <= D / Real.log (N : Real) +
        Finset.sum (Finset.Ico 2 N) (fun k =>
          D * (1 / Real.log (k : Real) - 1 / Real.log ((k : Real) + 1))) := by
      exact add_le_add (by
        rw [abs_div, abs_of_pos hLogN]
        exact div_le_div_of_nonneg_right
          (hBound N (by linarith) (le_refl N)) hLogN.le) (by
        calc
          abs (Finset.sum (Finset.Ico 2 N) (fun k =>
              Finset.sum (Finset.Icc 1 k) F *
                (1 / Real.log (k : Real) - 1 / Real.log ((k : Real) + 1)))) <=
            Finset.sum (Finset.Ico 2 N) (fun k =>
              abs (Finset.sum (Finset.Icc 1 k) F *
                (1 / Real.log (k : Real) - 1 / Real.log ((k : Real) + 1)))) :=
              Finset.abs_sum_le_sum_abs _ _
          _ <= Finset.sum (Finset.Ico 2 N) (fun k =>
              D * (1 / Real.log (k : Real) - 1 / Real.log ((k : Real) + 1))) := by
            apply Finset.sum_le_sum
            intro k hk
            have hkData := Finset.mem_Ico.mp hk
            have hDiff := log_reciprocal_difference_nonneg hkData.1
            rw [abs_mul, abs_of_nonneg hDiff]
            exact mul_le_mul_of_nonneg_right
              (hBound k (by linarith) hkData.2.le) hDiff)
    _ = D / Real.log (2 : Real) := by
      rw [show Finset.sum (Finset.Ico 2 N) (fun k =>
        D * (1 / Real.log (k : Real) - 1 / Real.log ((k : Real) + 1))) =
          D * Finset.sum (Finset.Ico 2 N) (fun k =>
            1 / Real.log (k : Real) - 1 / Real.log ((k : Real) + 1)) by
              exact (Finset.mul_sum _ _ _).symm,
        sum_log_reciprocal_differences hN]
      ring

end BombieriVinogradov.RealAnalysis

open Finset Real ArithmeticFunction
open scoped ArithmeticFunction

theorem OMA.solution : OMA.R_ElliottHalberstamConjecture_elliott_halberstam_variants_bombieri_vinogradov_R1.H2 := by
  classical
  intro x f M hx hf hM
  let F (n : ℕ) := if n.Prime then f n * (Λ n : ℝ) else 0
  have partialBound (k : ℕ) (_ : 1 ≤ k) (hk : k ≤ x) :
      |∑ n ∈ Icc 1 k, F n| ≤ M + (Chebyshev.psi x - Chebyshev.theta x) := by
    let S := (Icc 1 k).filter (fun n => ¬ n.Prime)
    let G (n : ℕ) := f n * (Λ n : ℝ)
    have split : (∑ n ∈ Icc 1 k, F n) = (∑ n ∈ Icc 1 k, G n) - ∑ n ∈ S, G n := by
      rw [eq_sub_iff_add_eq,← sum_filter (s := Icc 1 k) Nat.Prime G]
      exact sum_filter_add_sum_filter_not ..
    have rem : |∑ n ∈ S,G n| ≤ Chebyshev.psi x - Chebyshev.theta x := calc
      _ ≤ ∑ n ∈ S, |G n| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ S, (Λ n : ℝ) := by
        apply sum_le_sum; intro n hn
        dsimp [G]; rw [abs_mul,abs_of_nonneg vonMangoldt_nonneg]
        exact mul_le_of_le_one_left vonMangoldt_nonneg (hf n ((mem_Icc.mp (mem_filter.mp hn).1).2.trans hk))
      _ ≤ _ := by
        rw [Chebyshev.psi_sub_theta_eq_sum_not_prime,Nat.floor_natCast]
        apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => vonMangoldt_nonneg)
        intro n hn
        obtain ⟨h,hn⟩ := mem_filter.mp hn
        obtain ⟨hn1,hnk⟩ := mem_Icc.mp h
        exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,hnk.trans hk⟩,hn⟩
    rw [split]
    exact (abs_sub ..).trans (add_le_add (hM k hk) rem)
  have transfer := BombieriVinogradov.RealAnalysis.abs_sum_Icc_div_log_le F hx
    (by simp [F]) partialBound
  have eq : (∑ n ∈ Icc 2 x, F n / Real.log n) = ∑ p ∈ Nat.primesLE x, f p := by
    rw [Nat.primesLE_eq_filter_Icc_two,sum_filter]
    apply sum_congr rfl; intro n _
    by_cases hn : n.Prime
    · simp [F,hn,vonMangoldt_apply_prime hn,(log_pos (by exact_mod_cast hn.one_lt : 1 < (n:ℝ))).ne']
    · simp [F,hn]
  rwa [eq] at transfer
