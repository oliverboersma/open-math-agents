import FormalConjectures.ErdosProblems.«101»
import Mathlib.Combinatorics.SimpleGraph.Triangle.Tripartite

-- Reduction Erdos101.erdos_101.R2 of Erdős Problem 101
-- Credit: @ubuwaits

/-!
# Triangle ratios on four-point lines

Choose three ordered points x, y, z on each selected line. Write z = a x + b y
with a + b = 1. Store a on the xz pair, b on the yz pair, and d = b/a on the
xy pair. When all three pairs of a triangle occur, possibly on three different
lines, its ratio is a(x,z) d(x,y) / b(y,z). A change of projective chart
introduces vertex factors that cancel around the triangle.

The first step asks whether four-point density forces a dense family of triples
with boundedly many triangle ratios. The second handles arbitrary linear
families of collinear triples with boundedly many ratios. A linear family
has at most one record with any specified pair of entries in fixed positions.
-/

namespace OMA.R_Erdos101_erdos_101_R2

open EuclideanGeometry SimpleGraph.TripartiteFromTriangles Filter Asymptotics
open scoped Classical

/-- Extract a positive density of ordered triples on distinct four-point lines
so that the ratios on triangles formed from their pairs take boundedly many values. -/
def H1 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ k : ℕ, ∃ η : ℝ, 0 < η ∧ ∃ N : ℕ,
    ∀ S : Finset ℝ², N ≤ S.card → NonCollinearFor 5 (S : Set ℝ²) →
    δ*(S.card : ℝ)^2 ≤ (linesWithPointsFor 4 (S : Set ℝ²)).ncard →
    ∃ T : Finset (S × S × S), ExplicitDisjoint T ∧ η*(S.card : ℝ)^2 ≤ T.card ∧
      (T : Set (S × S × S)).InjOn (fun e => line[ℝ,(e.1 : ℝ²),(e.2.1 : ℝ²)]) ∧
      (∀ e ∈ T, e.1 ≠ e.2.1 ∧ e.1 ≠ e.2.2 ∧ e.2.1 ≠ e.2.2 ∧
        line[ℝ,(e.1 : ℝ²),(e.2.1 : ℝ²)] ∈ linesWithPointsFor 4 (S : Set ℝ²)) ∧
    ∃ a b d : S → S → ℝˣ,
      (∀ e ∈ T, (a e.1 e.2.2 : ℝ) + (b e.2.1 e.2.2 : ℝ) = 1 ∧
        (a e.1 e.2.2 : ℝ) • (e.1 : ℝ²) + (b e.2.1 e.2.2 : ℝ) • (e.2.1 : ℝ²) = (e.2.2 : ℝ²) ∧
        d e.1 e.2.1 = b e.2.1 e.2.2 / a e.1 e.2.2) ∧
    ∃ K : Finset ℝˣ, K.card ≤ k ∧ ∀ x y z, (∃ w, (x,y,w) ∈ T) →
      (∃ w, (x,w,z) ∈ T) → (∃ w, (w,y,z) ∈ T) → a x z * d x y / b y z ∈ K

/-- A linear family of collinear triples with boundedly many triangle ratios
has subquadratic size, uniformly in the actual ratio values. -/
def H2 : Prop :=
  ∀ k : ℕ, ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ S : Finset ℝ², N ≤ S.card →
    NonCollinearFor 5 (S : Set ℝ²) →
    ∀ T : Finset (S × S × S), ExplicitDisjoint T → ∀ a b d : S → S → ℝˣ,
      (∀ e ∈ T, (a e.1 e.2.2 : ℝ) + (b e.2.1 e.2.2 : ℝ) = 1 ∧
        (a e.1 e.2.2 : ℝ) • (e.1 : ℝ²) + (b e.2.1 e.2.2 : ℝ) • (e.2.1 : ℝ²) = (e.2.2 : ℝ²) ∧
        d e.1 e.2.1 = b e.2.1 e.2.2 / a e.1 e.2.2) →
    ∀ K : Finset ℝˣ, K.card ≤ k → (∀ x y z, (∃ w, (x,y,w) ∈ T) →
      (∃ w, (x,w,z) ∈ T) → (∃ w, (w,y,z) ∈ T) → a x z * d x y / b y z ∈ K) →
      (T.card : ℝ) < δ*(S.card : ℝ)^2

theorem main : H1 → H2 → type_of% @Erdos101.erdos_101 := by
  intro extract sparse
  apply IsLittleO.of_bound
  intro δ hδ
  obtain ⟨k,η,hη,N,hN⟩ := extract δ hδ
  obtain ⟨M,hM⟩ := sparse k η hη
  filter_upwards [eventually_ge_atTop (max N M)] with n hn
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (sq_nonneg _)]
  have hmax : Erdos101.numLinesWithFourPointMax n ≤ ⌊δ*(n : ℝ)^2⌋₊ := by
    apply csSup_le'
    rintro _ ⟨U,hcard,hfin,hcap,rfl⟩
    let S := hfin.toFinset
    have hU : (S : Set ℝ²) = U := hfin.coe_toFinset
    have hs : S.card = n := (Set.ncard_eq_toFinset_card U hfin).symm.trans hcard
    apply Nat.le_floor
    by_contra! hdense
    obtain ⟨T,hd,hcount,_,_,a,b,d,hw,K,hk,hK⟩ :=
      hN S (hs ▸ (le_max_left ..).trans hn) (hU ▸ hcap) (by simpa only [hU,hs] using hdense.le)
    exact (not_lt_of_ge hcount) (hM S (hs ▸ (le_max_right ..).trans hn) (hU ▸ hcap)
      T hd a b d hw K hk hK)
  exact (Nat.cast_le.mpr hmax).trans (Nat.floor_le (mul_nonneg hδ.le (sq_nonneg _)))

end OMA.R_Erdos101_erdos_101_R2
