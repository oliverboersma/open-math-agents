import FormalConjectures.ErdosProblems.«100»
import Mathlib

/-! The diameter bound ≫ n / log n for n points in the plane whose distinct distances differ
by at least 1, from the theorem of Guth and Katz, On the Erdős distinct distances problem in
the plane, Ann. of Math. 181 (2015): n points determine ≫ n / log n distinct distances. That
is the catalogue's Erdos89.erdos_89.variants.n_dvd_log_n. The passage to the diameter is
elementary: the distinct distances are nonnegative reals up to the diameter that pairwise
differ by at least 1, so there are at most diam + 1 of them. -/

namespace OMA.R_Erdos100_erdos_100_variants_guth_katz_R1
open Filter Asymptotics

/-- Guth and Katz: n points in the plane determine ≫ n / log n distinct distances. -/
def H1 : Prop := (fun n : ℕ => (n : ℝ) / Real.log (n : ℝ)) =O[atTop]
  (fun n : ℕ => (minimalDistinctDistances (EuclideanSpace ℝ (Fin 2)) n : ℝ))

/-- If any two different distances in A differ by at least 1, then A determines at most
diam A + 1 distinct distances. -/
def H2 : Prop := ∀ A : Finset (EuclideanSpace ℝ (Fin 2)), Erdos100.DistancesSeparated A →
  (distinctDistances A : ℝ) ≤ Metric.diam (A : Set (EuclideanSpace ℝ (Fin 2))) + 1

theorem main : H1 → H2 → type_of% @Erdos100.erdos_100.variants.guth_katz := by
  intro h1 h2
  obtain ⟨c, hc⟩ := h1.bound
  have hc' : (0 : ℝ) < max c 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨1 / (2 * max c 1), by positivity, ?_⟩
  have t0 : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) / 2) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const (by norm_num)
  have t1 : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hc, t0.eventually_ge_atTop (2 * max c 1), t1.eventually_ge_atTop 1]
    with n hn hbig hlog A hA hsep
  have hlpos : 0 < Real.log (n : ℝ) := by linarith
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hs0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hn0
  have hlog2 : Real.log (n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
    have h := Real.log_le_rpow_div hn0 (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h
    calc Real.log (n : ℝ) ≤ Real.sqrt (n : ℝ) / (1 / 2) := h
      _ = 2 * Real.sqrt (n : ℝ) := by ring
  have hq : Real.sqrt (n : ℝ) / 2 ≤ (n : ℝ) / Real.log (n : ℝ) := by
    rw [le_div_iff₀ hlpos]
    nlinarith [mul_le_mul_of_nonneg_left hlog2 hs0]
  have hqbig : 2 * max c 1 ≤ (n : ℝ) / Real.log (n : ℝ) := le_trans hbig hq
  have hq0 : 0 ≤ (n : ℝ) / Real.log (n : ℝ) := by linarith
  have hm : (minimalDistinctDistances (EuclideanSpace ℝ (Fin 2)) n : ℝ) ≤
      (distinctDistances A : ℝ) := by
    have hmem : distinctDistances A ∈ {m : ℕ | ∃ points : Finset (EuclideanSpace ℝ (Fin 2)),
        points.card = n ∧ distinctDistances points = m} := ⟨A, hA, rfl⟩
    have hm' : minimalDistinctDistances (EuclideanSpace ℝ (Fin 2)) n ≤ distinctDistances A :=
      Nat.sInf_le hmem
    exact_mod_cast hm'
  have hd := h2 A hsep
  rw [Real.norm_of_nonneg hq0, Real.norm_of_nonneg (Nat.cast_nonneg _)] at hn
  have hm0 : (0 : ℝ) ≤ (minimalDistinctDistances (EuclideanSpace ℝ (Fin 2)) n : ℝ) :=
    Nat.cast_nonneg _
  have h3 : (n : ℝ) / Real.log (n : ℝ) ≤
      max c 1 * (Metric.diam (A : Set (EuclideanSpace ℝ (Fin 2))) + 1) := by
    calc (n : ℝ) / Real.log (n : ℝ)
        ≤ c * (minimalDistinctDistances (EuclideanSpace ℝ (Fin 2)) n : ℝ) := hn
      _ ≤ max c 1 * (minimalDistinctDistances (EuclideanSpace ℝ (Fin 2)) n : ℝ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hm0
      _ ≤ max c 1 * (Metric.diam (A : Set (EuclideanSpace ℝ (Fin 2))) + 1) :=
          mul_le_mul_of_nonneg_left (le_trans hm hd) hc'.le
  have e : 1 / (2 * max c 1) * (n : ℝ) / Real.log (n : ℝ) =
      ((n : ℝ) / Real.log (n : ℝ)) / (2 * max c 1) := by ring
  show Metric.diam (A : Set (EuclideanSpace ℝ (Fin 2))) ≥
    1 / (2 * max c 1) * (n : ℝ) / Real.log (n : ℝ)
  rw [e, ge_iff_le, div_le_iff₀ (by positivity)]
  nlinarith

end OMA.R_Erdos100_erdos_100_variants_guth_katz_R1
