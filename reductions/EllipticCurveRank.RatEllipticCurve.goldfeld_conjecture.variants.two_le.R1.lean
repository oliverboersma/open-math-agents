import FormalConjectures.Wikipedia.EllipticCurveRank
import Mathlib

/-! Reduction of Goldfeld's conjecture for rank r >= 2 (Smith 2025) to showing that both
positive (real quadratic) twists of rank >= 2 and negative (imaginary quadratic) twists of
rank >= 2 have natural density 0. In `main`, we bound the count of rank-r twists by the sum
of positive and negative twists of rank >= 2, normalize by `ncard_twistIndexLE H = 2 * H`,
and apply the squeeze theorem (`tendsto_of_tendsto_of_tendsto_of_le_of_le'`). -/

namespace OMA.R_EllipticCurveRank_RatEllipticCurve_goldfeld_conjecture_variants_two_le_R1

open EllipticCurveRank Filter Topology

/-- Positive quadratic twists of `E` with Mordell-Weil rank at least 2 have natural density 0. -/
def H1 : Prop :=
  ∀ E : RatEllipticCurve,
    atTop.Tendsto
      (fun H : ℕ ↦ ({d : ℤ | 0 < d ∧ d ≤ (H : ℤ) ∧ 2 ≤ E.twistRank d}.ncard / (H : ℝ)))
      (𝓝 0)

/-- Negative quadratic twists of `E` with Mordell-Weil rank at least 2 have natural density 0. -/
def H2 : Prop :=
  ∀ E : RatEllipticCurve,
    atTop.Tendsto
      (fun H : ℕ ↦ ({d : ℤ | -(H : ℤ) ≤ d ∧ d < 0 ∧ 2 ≤ E.twistRank d}.ncard / (H : ℝ)))
      (𝓝 0)

theorem main : H1 → H2 →
    type_of% @EllipticCurveRank.RatEllipticCurve.goldfeld_conjecture.variants.two_le := by
  intro h1 h2 E r hr
  have hsum : atTop.Tendsto
      (fun H : ℕ ↦
        (({d : ℤ | 0 < d ∧ d ≤ (H : ℤ) ∧ 2 ≤ E.twistRank d}.ncard / (H : ℝ)) +
         ({d : ℤ | -(H : ℤ) ≤ d ∧ d < 0 ∧ 2 ≤ E.twistRank d}.ncard / (H : ℝ))) / 2)
      (𝓝 0) := by
    have h := ((h1 E).add (h2 E)).div_const 2
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum ?_ ?_
  · exact Eventually.of_forall fun H => by positivity
  · filter_upwards [eventually_ge_atTop 1] with H hH
    have hHpos : (0 : ℝ) < (H : ℝ) := Nat.cast_pos.2 (by omega)
    rw [RatEllipticCurve.ncard_twistIndexLE H]
    set P : Set ℤ := {d : ℤ | 0 < d ∧ d ≤ (H : ℤ) ∧ 2 ≤ E.twistRank d}
    set N : Set ℤ := {d : ℤ | -(H : ℤ) ≤ d ∧ d < 0 ∧ 2 ≤ E.twistRank d}
    have hPfin : P.Finite :=
      (Set.finite_Icc (1 : ℤ) (H : ℤ)).subset fun d ⟨hd1, hd2, _⟩ => ⟨by omega, hd2⟩
    have hNfin : N.Finite :=
      (Set.finite_Icc (-(H : ℤ)) (-1 : ℤ)).subset fun d ⟨hd1, hd2, _⟩ => ⟨hd1, by omega⟩
    have hsub : {d ∈ RatEllipticCurve.twistIndexLE H | E.twistRank d = r} ⊆ P ∪ N := by
      intro d ⟨⟨hd0, hdabs⟩, hdr⟩
      have hge : 2 ≤ E.twistRank d := hdr ▸ hr
      have habs := abs_le.1 hdabs
      rcases lt_or_gt_of_ne hd0 with hlt | hgt
      · exact Or.inr ⟨habs.1, hlt, hge⟩
      · exact Or.inl ⟨hgt, habs.2, hge⟩
    have hcard : ({d ∈ RatEllipticCurve.twistIndexLE H | E.twistRank d = r}.ncard : ℝ) ≤
        (P.ncard : ℝ) + (N.ncard : ℝ) := by
      have h1' : {d ∈ RatEllipticCurve.twistIndexLE H | E.twistRank d = r}.ncard ≤
          (P ∪ N).ncard := Set.ncard_le_ncard hsub (hPfin.union hNfin)
      have h2' : (P ∪ N).ncard ≤ P.ncard + N.ncard := Set.ncard_union_le P N
      exact_mod_cast le_trans h1' h2'
    push_cast
    have h2Hpos : (0 : ℝ) < 2 * (H : ℝ) := by positivity
    calc
      ({d ∈ RatEllipticCurve.twistIndexLE H | E.twistRank d = r}.ncard : ℝ) / (2 * (H : ℝ))
          ≤ ((P.ncard : ℝ) + (N.ncard : ℝ)) / (2 * (H : ℝ)) :=
            div_le_div_of_nonneg_right hcard h2Hpos.le
      _ = ((P.ncard : ℝ) / (H : ℝ) + (N.ncard : ℝ) / (H : ℝ)) / 2 := by ring

end OMA.R_EllipticCurveRank_RatEllipticCurve_goldfeld_conjecture_variants_two_le_R1
