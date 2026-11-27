import OMAReductions.R_Erdos239_erdos_239_R1_H2_R1
import Mathlib

-- Step Erdos239.erdos_239.R1.H2.R1.H1: hypothesis H1 of reduction Erdos239.erdos_239.R1.H2.R1
-- Credit: @ivillar

/-!
# Compactness: pointwise divergence of a nonnegative prime series gives a common finite sum

For each `t` the series `∑_p (1 - f p * cos (t * log p)) / p` has nonnegative terms and is not
summable, so some finite partial sum exceeds `B`. That partial sum is continuous in `t`, hence
exceeds `B` on a neighbourhood of `t`. Finitely many neighbourhoods cover `[-T, T]`, and the union
of the corresponding finite sets of primes works for every `t` in the interval.
-/

namespace Erdos239CompactStep

open Finset Filter Real
open scoped Topology

theorem compact_step : ∀ f : ℕ → ℝ, (∀ n ≥ 1, |f n| ≤ 1) →
    (∀ t : ℝ, ¬ Summable (fun p : Nat.Primes =>
      (1 - f p * cos (t * log p.val)) / p.val)) →
    ∀ T B : ℝ, ∃ S : Finset Nat.Primes, ∀ t ∈ Set.Icc (-T) T,
      B < ∑ p ∈ S, (1 - f p * cos (t * log p.val)) / p.val := by
  intro f hf hdiv T B
  have hnn : ∀ (t : ℝ) (p : Nat.Primes),
      0 ≤ (1 - f p * cos (t * log p.val)) / p.val := by
    intro t p
    have hp : (0 : ℝ) < p.val := by exact_mod_cast p.prop.pos
    have h1 : |f p| ≤ 1 := hf p p.prop.one_le
    have h2 : |cos (t * log p.val)| ≤ 1 := abs_cos_le_one _
    have h3 : f p * cos (t * log p.val) ≤ 1 :=
      calc f p * cos (t * log p.val) ≤ |f p * cos (t * log p.val)| := le_abs_self _
        _ = |f p| * |cos (t * log p.val)| := abs_mul _ _
        _ ≤ 1 * 1 := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    exact div_nonneg (sub_nonneg.mpr h3) hp.le
  have hpt : ∀ t : ℝ, ∃ S : Finset Nat.Primes,
      B < ∑ p ∈ S, (1 - f p * cos (t * log p.val)) / p.val := by
    intro t
    by_contra hcon
    exact hdiv t (summable_of_sum_le (fun p => hnn t p)
      (fun S => not_lt.mp (fun h => hcon ⟨S, h⟩)))
  choose S hS using hpt
  have hopen : ∀ t : ℝ,
      IsOpen {s : ℝ | B < ∑ p ∈ S t, (1 - f p * cos (s * log p.val)) / p.val} := by
    intro t
    exact isOpen_lt continuous_const (continuous_finsetSum _ (fun p _ => by fun_prop))
  obtain ⟨F, hF⟩ := (isCompact_Icc (a := -T) (b := T)).elim_finite_subcover
    (fun t : ℝ => {s : ℝ | B < ∑ p ∈ S t, (1 - f p * cos (s * log p.val)) / p.val}) hopen
    (fun s _ => Set.mem_iUnion.mpr ⟨s, hS s⟩)
  refine ⟨F.biUnion S, fun t ht => ?_⟩
  obtain ⟨u, hu⟩ := Set.mem_iUnion.mp (hF ht)
  obtain ⟨huF, hut⟩ := Set.mem_iUnion.mp hu
  exact lt_of_lt_of_le hut (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_biUnion_of_mem S huF) (fun p _ _ => hnn t p))

end Erdos239CompactStep

theorem OMA.solution : OMA.R_Erdos239_erdos_239_R1_H2_R1.H1 :=
  Erdos239CompactStep.compact_step
