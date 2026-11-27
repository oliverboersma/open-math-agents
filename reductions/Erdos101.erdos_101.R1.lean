import FormalConjectures.ErdosProblems.«101»
import Mathlib.Algebra.MvPolynomial.Polynomial

-- Reduction Erdos101.erdos_101.R1 of Erdős Problem 101
-- Credit: @ubuwaits

/-!
# A bounded-degree inverse problem for four-point lines

The first hypothesis asks whether a positive proportion of points incident to many
four-point lines must have a positive proportion on a curve of bounded degree.
We prove the full bounded-degree case through degree three, including reducible cubics.
The second hypothesis is the remaining bounded-degree quadruple-line estimate
(Elekes and Szabó, On Triple Lines and Cubic Curves, Theorem 4.3).

The choice of points matters. On each surviving line we designate one of its
four points and discard points that receive too few designations. A curve through
many of the remaining points captures many designated incidences. Applying this
four times and multiplying the polynomials puts all four points of every
surviving line on one bounded-degree curve.
-/

namespace OMA.R_Erdos101_erdos_101_R1

open EuclideanGeometry MvPolynomial Filter Asymptotics
open scoped Classical Finset Polynomial

/-- A positive-density set of points, each on linearly many four-point lines,
has a positive-density subset on a curve of degree bounded in terms of the density. -/
def H1 : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ d : ℕ, ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ,
    ∀ S T : Finset ℝ², N ≤ S.card → T ⊆ S → NonCollinearFor 5 (S : Set ℝ²) →
      τ * S.card ≤ T.card →
      (∀ p ∈ T, ∃ A : Finset (AffineSubspace ℝ ℝ²), τ * S.card ≤ A.card ∧
        ∀ L ∈ A, p ∈ L ∧ L ∈ linesWithPointsFor 4 (S : Set ℝ²)) →
      ∃ F : MvPolynomial (Fin 2) ℝ, F ≠ 0 ∧ F.totalDegree ≤ d ∧
        c * S.card ≤ (T.filter (fun p => eval (fun i => p i) F = 0)).card

/-- The quadruple-line bound for algebraic curves of degree from four to d,
uniform in their coefficients. The cases of degree at most three are proved below. -/
def H2 : Prop :=
  ∀ d : ℕ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ S : Finset ℝ², S.card ≤ n → NonCollinearFor 5 (S : Set ℝ²) →
      ∀ F : MvPolynomial (Fin 2) ℝ, F ≠ 0 → 4 ≤ F.totalDegree → F.totalDegree ≤ d →
        (∀ p ∈ S, eval (fun i => p i) F = 0) →
        ((linesWithPointsFor 4 (S : Set ℝ²)).ncard : ℝ) ≤ ε * (n : ℝ)^2

lemma four_lines_finite (S : Finset ℝ²) :
    (linesWithPointsFor 4 (S : Set ℝ²)).Finite := by
  apply (S.finite_toSet.image2 (fun p q => line[ℝ, p, q]) S.finite_toSet).subset
  rintro L ⟨⟨p, hp, q, hq, _, he⟩, _⟩
  exact ⟨p, hp, q, hq, he⟩

lemma four_points {S : Finset ℝ²} {L : AffineSubspace ℝ ℝ²}
    (hL : L ∈ linesWithPointsFor 4 (S : Set ℝ²)) :
    (S.filter (fun p => p ∈ L)).card = 4 := by
  have he : ((S.filter (fun p => p ∈ L) : Finset ℝ²) : Set ℝ²) = (L : Set ℝ²) ∩ S := by
    ext p
    simp [and_comm]
  rw [← Set.ncard_coe_finset, he]
  exact hL.2

lemma line_through {S : Finset ℝ²} {L : AffineSubspace ℝ ℝ²}
    (hL : L ∈ linesWithPointsFor 4 (S : Set ℝ²)) {p q : ℝ²}
    (hp : p ∈ L) (hq : q ∈ L) (hne : p ≠ q) : line[ℝ, p, q] = L := by
  obtain ⟨⟨a, _, b, _, _, rfl⟩, _⟩ := hL
  exact affineSpan_pair_eq_of_mem_of_mem_of_ne hp hq hne

/-- Distinct lines through p use disjoint triples among the other points. -/
lemma pencil_bound {S : Finset ℝ²} {A : Finset (AffineSubspace ℝ ℝ²)}
    (hA : ∀ L ∈ A, L ∈ linesWithPointsFor 4 (S : Set ℝ²))
    {p : ℝ²} (hp : p ∈ S) :
    3 * (A.filter (fun L => p ∈ L)).card ≤ S.card - 1 := by
  let pencil := A.filter (fun L => p ∈ L)
  let others := fun L : AffineSubspace ℝ ℝ² => (S.filter (fun q => q ∈ L)).erase p
  have hdisj : (pencil : Set (AffineSubspace ℝ ℝ²)).PairwiseDisjoint others := by
    intro L hL M hM hne
    obtain ⟨hLA, hpL⟩ := Finset.mem_filter.mp hL
    obtain ⟨hMA, hpM⟩ := Finset.mem_filter.mp hM
    apply Finset.disjoint_left.mpr
    intro q hqL hqM
    obtain ⟨hqp, hqL'⟩ := Finset.mem_erase.mp hqL
    have hqM' := (Finset.mem_erase.mp hqM).2
    exact hne ((line_through (hA L hLA) hpL (Finset.mem_filter.mp hqL').2 hqp.symm).symm.trans
      (line_through (hA M hMA) hpM (Finset.mem_filter.mp hqM').2 hqp.symm))
  have hcard (L) (hL : L ∈ pencil) : (others L).card = 3 := by
    obtain ⟨hLA, hpL⟩ := Finset.mem_filter.mp hL
    rw [Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hp, hpL⟩), four_points (hA L hLA)]
  have hsub : pencil.biUnion others ⊆ S.erase p := by
    intro q hq
    obtain ⟨L, _, hq⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hq
    exact Finset.mem_erase.mpr ⟨hne, (Finset.mem_filter.mp hmem).1⟩
  calc
    3 * pencil.card = ∑ L ∈ pencil, (others L).card := by
      simp [Finset.sum_congr rfl hcard, mul_comm]
    _ = (pencil.biUnion others).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (S.erase p).card := Finset.card_le_card hsub
    _ = S.card - 1 := Finset.card_erase_of_mem hp

/-- Pair counting, with the constant for unordered pairs. -/
lemma pair_bound {S : Finset ℝ²} {A : Finset (AffineSubspace ℝ ℝ²)}
    (hA : ∀ L ∈ A, L ∈ linesWithPointsFor 4 (S : Set ℝ²)) :
    12 * A.card ≤ S.card * (S.card - 1) := by
  have hcount : (∑ L ∈ A, (S.filter (fun p => p ∈ L)).card) =
      ∑ p ∈ S, (A.filter (fun L => p ∈ L)).card :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun L p => p ∈ L)
  have hs : (∑ L ∈ A, (S.filter (fun p => p ∈ L)).card) = A.card * 4 := by
    simp [Finset.sum_congr rfl (fun L hL => four_points (hA L hL))]
  calc
    12 * A.card = 3 * (A.card * 4) := by omega
    _ = 3 * ∑ p ∈ S, (A.filter (fun L => p ∈ L)).card := by rw [← hcount, hs]
    _ = ∑ p ∈ S, 3 * (A.filter (fun L => p ∈ L)).card := Finset.mul_sum ..
    _ ≤ ∑ _p ∈ S, (S.card - 1) := Finset.sum_le_sum fun p hp => pencil_bound hA hp
    _ = S.card * (S.card - 1) := by simp

/-- With one designated point on each line, the inverse hypothesis captures a
positive-density subfamily at its designated points. The constants are uniform
over both the line family and the designations. -/
lemma capture_one (h1 : H1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ d : ℕ, ∃ η : ℝ, 0 < η ∧ ∃ N : ℕ,
      ∀ (S : Finset ℝ²) (A : Finset (AffineSubspace ℝ ℝ²))
        (mark : AffineSubspace ℝ ℝ² → ℝ²),
        N ≤ S.card → NonCollinearFor 5 (S : Set ℝ²) →
        (∀ L ∈ A, L ∈ linesWithPointsFor 4 (S : Set ℝ²)) →
        (∀ L ∈ A, mark L ∈ S ∧ mark L ∈ L) →
        δ * (S.card : ℝ)^2 ≤ A.card →
        ∃ F : MvPolynomial (Fin 2) ℝ, F ≠ 0 ∧ F.totalDegree ≤ d ∧
          ∃ B ⊆ A, η * (S.card : ℝ)^2 ≤ B.card ∧
            ∀ L ∈ B, eval (fun i => mark L i) F = 0 := by
  let τ := δ / 2
  have hτ : 0 < τ := half_pos hδ
  obtain ⟨d, c, hc, N, hinv⟩ := h1 τ hτ
  refine ⟨d, c * τ, mul_pos hc hτ, max N 1, ?_⟩
  intro S A mark hN hS hA hmark hdense
  let n : ℝ := S.card
  have hn : 0 < n := by
    have := (le_max_right N 1).trans hN
    dsimp [n]
    exact_mod_cast (show 0 < S.card by omega)
  let fiber := fun p : ℝ² => A.filter (fun L => mark L = p)
  let w := fun p : ℝ² => ((fiber p).card : ℝ)
  let T := S.filter (fun p => τ * n ≤ w p)
  have hTS : T ⊆ S := Finset.filter_subset ..
  have hmaps : Set.MapsTo mark (A : Set (AffineSubspace ℝ ℝ²)) (S : Set ℝ²) :=
    fun L hL => (hmark L hL).1
  have hsum : ∑ p ∈ S, w p = (A.card : ℝ) := by
    dsimp [w, fiber]
    exact_mod_cast (Finset.card_eq_sum_card_fiberwise hmaps).symm
  have hcap (p) (hp : p ∈ S) : w p ≤ n := by
    have hsub : fiber p ⊆ A.filter (fun L => p ∈ L) := by
      intro L hL
      obtain ⟨hLA, hLp⟩ := Finset.mem_filter.mp hL
      exact Finset.mem_filter.mpr ⟨hLA, hLp ▸ (hmark L hLA).2⟩
    have hcard := Finset.card_le_card hsub
    have hpencil := pencil_bound hA hp
    dsimp only [w, n]
    exact_mod_cast (show (fiber p).card ≤ S.card by omega)
  have hhot : τ * n ≤ (T.card : ℝ) := by
    have hTsum : (∑ p ∈ T, w p) ≤ T.card * n := by
      calc
        _ ≤ ∑ _p ∈ T, n := Finset.sum_le_sum fun p hp => hcap p (hTS hp)
        _ = _ := by simp
    have hlight : (∑ p ∈ S \ T, w p) ≤ n * (τ * n) := by
      calc
        _ ≤ ∑ _p ∈ S \ T, τ * n := by
          apply Finset.sum_le_sum
          intro p hp
          have hp' := Finset.mem_sdiff.mp hp
          exact le_of_not_ge fun h => hp'.2 (Finset.mem_filter.mpr ⟨hp'.1, h⟩)
        _ = ((S \ T).card : ℝ) * (τ * n) := by simp
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg hτ.le hn.le)
          dsimp only [n]
          exact_mod_cast Finset.card_le_card (Finset.sdiff_subset (s := S) (t := T))
    have htotal := Finset.sum_sdiff hTS (f := w)
    rw [hsum] at htotal
    change δ * n^2 ≤ (A.card : ℝ) at hdense
    have htwice : δ = τ + τ := by dsimp [τ]; ring
    exact (le_of_mul_le_mul_right (a := n) (by nlinarith only [htotal, hlight, hTsum, hdense, htwice]) hn)
  have hstars (p) (hp : p ∈ T) :
      ∃ C : Finset (AffineSubspace ℝ ℝ²), τ * S.card ≤ C.card ∧
        ∀ L ∈ C, p ∈ L ∧ L ∈ linesWithPointsFor 4 (S : Set ℝ²) := by
    refine ⟨fiber p, (Finset.mem_filter.mp hp).2, ?_⟩
    intro L hL
    obtain ⟨hLA, heq⟩ := Finset.mem_filter.mp hL
    exact ⟨heq ▸ (hmark L hLA).2, hA L hLA⟩
  obtain ⟨F, hF, hdeg, hmany⟩ :=
    hinv S T ((le_max_left N 1).trans hN) hTS hS hhot hstars
  let G := T.filter (fun p => eval (fun i => p i) F = 0)
  let B := A.filter (fun L => mark L ∈ G)
  have hgoodmass : ∑ p ∈ G, w p = (B.card : ℝ) := by
    dsimp only [B, w, fiber]
    exact_mod_cast Finset.sum_card_fiberwise_eq_card_filter A G mark
  refine ⟨F, hF, hdeg, B, Finset.filter_subset .., ?_, ?_⟩
  · change c * n ≤ (G.card : ℝ) at hmany
    calc
      (c * τ) * (S.card : ℝ)^2 = (c * n) * (τ * n) := by dsimp [n]; ring
      _ ≤ (G.card : ℝ) * (τ * n) := mul_le_mul_of_nonneg_right hmany (mul_nonneg hτ.le hn.le)
      _ = ∑ _p ∈ G, τ * n := by simp
      _ ≤ ∑ p ∈ G, w p := Finset.sum_le_sum fun p hp =>
        (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
      _ = _ := hgoodmass
  · intro L hL
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hL).2).2

/-- Repeatedly capture a designated point, retaining the lines captured earlier. -/
lemma capture_many (h1 : H1) (k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ d : ℕ, ∃ η : ℝ, 0 < η ∧ ∃ N : ℕ,
      ∀ (S : Finset ℝ²) (A : Finset (AffineSubspace ℝ ℝ²))
        (mark : Fin k → AffineSubspace ℝ ℝ² → ℝ²),
        N ≤ S.card → NonCollinearFor 5 (S : Set ℝ²) →
        (∀ L ∈ A, L ∈ linesWithPointsFor 4 (S : Set ℝ²)) →
        (∀ i, ∀ L ∈ A, mark i L ∈ S ∧ mark i L ∈ L) →
        δ * (S.card : ℝ)^2 ≤ A.card →
        ∃ F : MvPolynomial (Fin 2) ℝ, F ≠ 0 ∧ F.totalDegree ≤ d ∧
          ∃ B ⊆ A, η * (S.card : ℝ)^2 ≤ B.card ∧
            ∀ L ∈ B, ∀ i, eval (fun j => mark i L j) F = 0 := by
  induction k with
  | zero =>
    refine ⟨0, δ, hδ, 0, ?_⟩
    intro S A mark _ _ _ _ hA
    exact ⟨1, one_ne_zero, (by simp), A, Finset.Subset.rfl, hA, fun _ _ i => i.elim0⟩
  | succ k ih =>
    obtain ⟨d, α, hα, N, hfirst⟩ := ih
    obtain ⟨e, β, hβ, M, hlast⟩ := capture_one h1 α hα
    refine ⟨d + e, β, hβ, max N M, ?_⟩
    intro S A mark hN hS hA hp hdense
    obtain ⟨F, hF, hFd, B, hBA, hB, hroots⟩ :=
      hfirst S A (fun i => mark i.castSucc) ((le_max_left N M).trans hN)
        hS hA (fun i => hp i.castSucc) hdense
    obtain ⟨G, hG, hGe, C, hCB, hC, hlastroot⟩ :=
      hlast S B (mark (Fin.last k)) ((le_max_right N M).trans hN) hS
        (fun L hL => hA L (hBA hL)) (fun L hL => hp _ L (hBA hL)) hB
    refine ⟨F * G, mul_ne_zero hF hG, (totalDegree_mul F G).trans (Nat.add_le_add hFd hGe),
      C, hCB.trans hBA, hC, ?_⟩
    intro L hL i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [hlastroot L hL]
    · simp [hroots L (hCB hL) j]

lemma enumerate_four {S : Finset ℝ²} {A : Finset (AffineSubspace ℝ ℝ²)}
    (hA : ∀ L ∈ A, L ∈ linesWithPointsFor 4 (S : Set ℝ²)) :
    ∃ mark : Fin 4 → AffineSubspace ℝ ℝ² → ℝ²,
      (∀ i, ∀ L ∈ A, mark i L ∈ S ∧ mark i L ∈ L) ∧
      ∀ L ∈ A, ∀ p ∈ S, p ∈ L → ∃ i, mark i L = p := by
  let U (L : AffineSubspace ℝ ℝ²) := S.filter (fun p => p ∈ L)
  let mark (i : Fin 4) (L : AffineSubspace ℝ ℝ²) : ℝ² :=
    if hL : L ∈ A then
      ((Finset.equivFinOfCardEq (s := U L) (four_points (hA L hL))).symm i).val
    else 0
  refine ⟨mark, ?_, ?_⟩
  · intro i L hL
    simp only [mark, dif_pos hL]
    exact Finset.mem_filter.mp (Subtype.property _)
  · intro L hL p hp hpL
    let e : U L ≃ Fin 4 := Finset.equivFinOfCardEq (four_points (hA L hL))
    let a : U L := ⟨p, Finset.mem_filter.mpr ⟨hp, hpL⟩⟩
    refine ⟨e a, ?_⟩
    simpa only [mark, dif_pos hL] using congrArg Subtype.val (e.symm_apply_apply a)

/-- Retaining every point of a four-point line keeps that line in the count. -/
lemma mem_after_restriction {S T : Finset ℝ²} (hTS : T ⊆ S) {L : AffineSubspace ℝ ℝ²}
    (hL : L ∈ linesWithPointsFor 4 (S : Set ℝ²)) (hkeep : ∀ p ∈ S, p ∈ L → p ∈ T) :
    L ∈ linesWithPointsFor 4 (T : Set ℝ²) := by
  obtain ⟨⟨a, ha, b, hb, hab, he⟩, hcard⟩ := hL
  have haL : a ∈ L := he ▸ left_mem_affineSpan_pair ℝ a b
  have hbL : b ∈ L := he ▸ right_mem_affineSpan_pair ℝ a b
  refine ⟨⟨a, hkeep a ha haL, b, hkeep b hb hbL, hab, he⟩, ?_⟩
  have hinter : (L : Set ℝ²) ∩ T = (L : Set ℝ²) ∩ S :=
    Set.ext fun p => ⟨fun h => ⟨h.1, hTS h.2⟩, fun h => ⟨h.1, hkeep p h.2 h.1⟩⟩
  rw [hinter]
  exact hcard

/-- Removing k points destroys at most k times (n−1)/3 four-point lines.
This also controls configurations with a small exceptional set off a curve. -/
lemma delete_points_bound {S T : Finset ℝ²} (hTS : T ⊆ S) :
    3 * (linesWithPointsFor 4 (S : Set ℝ²)).ncard ≤
      3 * (linesWithPointsFor 4 (T : Set ℝ²)).ncard + (S \ T).card * (S.card - 1) := by
  let A := (four_lines_finite S).toFinset
  let B := (four_lines_finite T).toFinset
  let through := fun p : ℝ² => A.filter (fun L => p ∈ L)
  have hA : ∀ L ∈ A, L ∈ linesWithPointsFor 4 (S : Set ℝ²) :=
    fun _ hL => (four_lines_finite S).mem_toFinset.mp hL
  have cover : A ⊆ B ∪ (S \ T).biUnion through := by
    intro L hL
    by_cases hkeep : ∀ p ∈ S, p ∈ L → p ∈ T
    · exact Finset.mem_union_left _ ((four_lines_finite T).mem_toFinset.mpr
        (mem_after_restriction hTS (hA L hL) hkeep))
    · push Not at hkeep
      obtain ⟨p, hp, hpL, hdel⟩ := hkeep
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨p, Finset.mem_sdiff.mpr ⟨hp, hdel⟩, Finset.mem_filter.mpr ⟨hL, hpL⟩⟩)
  have hsum : 3 * (∑ p ∈ S \ T, (through p).card) ≤ (S \ T).card * (S.card - 1) := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ _p ∈ S \ T, (S.card - 1) :=
        Finset.sum_le_sum fun p hp => pencil_bound hA (Finset.mem_sdiff.mp hp).1
      _ = _ := by simp
  have hcount := (Finset.card_le_card cover).trans
    ((Finset.card_union_le ..).trans (Nat.add_le_add_left (Finset.card_biUnion_le ..) B.card))
  rw [Set.ncard_eq_toFinset_card _ (four_lines_finite S),
    Set.ncard_eq_toFinset_card _ (four_lines_finite T)]
  change 3 * A.card ≤ 3 * B.card + (S \ T).card * (S.card - 1)
  omega

/-- The unconditional pair bound on the precise supremum in the problem. -/
lemma max_pair_bound (n : ℕ) : 12 * Erdos101.numLinesWithFourPointMax n ≤ n * (n - 1) := by
  rw [mul_comm 12, ← Nat.le_div_iff_mul_le (by decide : 0 < 12)]
  apply csSup_le'
  rintro b ⟨S, hcard, hfin, _, rfl⟩
  let T := hfin.toFinset
  have he : (T : Set ℝ²) = S := hfin.coe_toFinset
  have hTcard : T.card = n := by simpa [T, ← Set.ncard_eq_toFinset_card] using hcard
  let lineFin := four_lines_finite T
  have h := pair_bound (S := T) (A := lineFin.toFinset)
    (fun _ hL => lineFin.mem_toFinset.mp hL)
  rw [Nat.le_div_iff_mul_le (by decide : 0 < 12), mul_comm]
  rw [← he, Set.ncard_eq_toFinset_card _ lineFin, ← hTcard]
  exact h

/-- Substituting affine univariate polynomials does not increase total degree. -/
lemma degree_substitution {σ : Type*} (F : MvPolynomial σ ℝ) (u : σ → Polynomial ℝ)
    (hu : ∀ i, (u i).natDegree ≤ 1) :
    ((eval₂Hom Polynomial.C u) F).natDegree ≤ F.totalDegree := by
  let φ := eval₂Hom Polynomial.C u
  have he : φ F = ∑ v ∈ F.support, φ (monomial v (coeff v F)) := by
    simpa only [map_sum] using congrArg φ F.as_sum
  change (φ F).natDegree ≤ _
  rw [he]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro v hv
  change ((eval₂Hom Polynomial.C u) (monomial v (coeff v F))).natDegree ≤ _
  rw [eval₂Hom_monomial]
  calc
    _ ≤ (Polynomial.C (coeff v F)).natDegree +
        (v.prod (fun i e => (u i)^e)).natDegree := Polynomial.natDegree_mul_le
    _ = (v.prod (fun i e => (u i)^e)).natDegree := by simp
    _ ≤ ∑ i ∈ v.support, ((u i)^(v i)).natDegree := Polynomial.natDegree_prod_le ..
    _ ≤ ∑ i ∈ v.support, v i := Finset.sum_le_sum fun i _ =>
      (Polynomial.natDegree_pow_le).trans (by simpa using Nat.mul_le_mul_left (v i) (hu i))
    _ ≤ F.totalDegree := le_totalDegree hv

lemma eval_substitution {σ : Type*} (F : MvPolynomial σ ℝ) (u : σ → Polynomial ℝ) (t : ℝ) :
    (((eval₂Hom Polynomial.C u) F).eval t) = eval (fun i => (u i).eval t) F := by
  exact (polynomial_eval_eval₂ Polynomial.C u F).trans (by
    have he : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id ℝ := by ext; simp
    rw [he, eval₂_id])

lemma eq_zero_of_many_roots {U : Finset ℝ²} {i : Fin 2} {g : Polynomial ℝ}
    (hproj : Set.InjOn (fun p : ℝ² => p i) (U : Set ℝ²))
    (hroot : ∀ p ∈ U, g.eval (p i) = 0) (hsize : g.natDegree < U.card) : g = 0 := by
  by_contra hn
  have hsub : (U.image (fun p => p i)).val ⊆ g.roots := by
    intro t ht
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
    exact (Polynomial.mem_roots hn).mpr (hroot p hp)
  have h := Polynomial.card_le_degree_of_subset_roots hsub
  rw [Finset.card_image_of_injOn hproj] at h
  omega

/-- A line determined by two distinct points is a horizontal level
or the graph of x as an affine function of y. -/
lemma charts {S : Finset ℝ²} {L : AffineSubspace ℝ ℝ²}
    (hL : L ∈ linesWithPointsFor 4 (S : Set ℝ²)) :
    (∃ b : ℝ, ∀ p : ℝ², p ∈ L ↔ p 1 = b) ∨
    (∃ m b : ℝ, ∀ p : ℝ², p ∈ L ↔ p 0 = m * p 1 + b) := by
  obtain ⟨⟨a, _, b, _, hne, rfl⟩, _⟩ := hL
  have param (p : ℝ²) : p ∈ line[ℝ, a, b] ↔
      ∃ t : ℝ, ∀ i, p i = a i + t * (b i - a i) := by
    rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨t, fun i => ?_⟩
      simp [AffineMap.lineMap_apply_module]
      ring
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      ext i
      simp [AffineMap.lineMap_apply_module]
      rw [ht i]
      ring
  by_cases hy : b 1 = a 1
  · have hx : b 0 - a 0 ≠ 0 := by
      intro he
      apply hne
      ext i
      fin_cases i
      · exact (sub_eq_zero.mp he).symm
      · exact hy.symm
    left
    refine ⟨a 1, fun p => (param p).trans ?_⟩
    constructor
    · rintro ⟨t, ht⟩
      simpa [hy] using ht 1
    · intro hp
      refine ⟨(p 0 - a 0) / (b 0 - a 0), ?_⟩
      intro i
      fin_cases i
      · dsimp; field_simp; ring
      · simpa [hy] using hp
  · have hd : b 1 - a 1 ≠ 0 := sub_ne_zero.mpr hy
    let m := (b 0 - a 0) / (b 1 - a 1)
    have hm : m * (b 1 - a 1) = b 0 - a 0 := div_mul_cancel₀ _ hd
    right
    refine ⟨m, a 0 - m * a 1, fun p => (param p).trans ?_⟩
    constructor
    · rintro ⟨t, ht⟩
      rw [ht 0, ht 1]
      linear_combination -t * hm
    · intro hp
      let t := (p 1 - a 1) / (b 1 - a 1)
      have ht : t * (b 1 - a 1) = p 1 - a 1 := div_mul_cancel₀ _ hd
      refine ⟨t, ?_⟩
      intro i
      fin_cases i
      · dsimp
        linear_combination hp + m * ht - t * hm
      · dsimp
        linarith

lemma coordinates_eq {a b : ℝ²} (h0 : a 0 = b 0) (h1 : a 1 = b 1) : a = b := by
  ext i
  fin_cases i
  · exact h0
  · exact h1

lemma unique_eval (Q : MvPolynomial (Fin 1) ℝ) (t : ℝ) :
    ((uniqueAlgEquiv ℝ (Fin 1)) Q).eval t = eval (fun _ => t) Q := by
  simpa only [uniqueAlgEquiv_apply, coe_eval₂Hom, Polynomial.eval_X] using
    eval_substitution Q (fun _ => Polynomial.X) t

lemma line_code {S : Finset ℝ²} {L : AffineSubspace ℝ ℝ²}
    (hL : L ∈ linesWithPointsFor 4 (S : Set ℝ²))
    (F : MvPolynomial (Fin 2) ℝ) (hF : F ≠ 0) (hd : F.totalDegree < 4)
    (hS : ∀ p ∈ S, eval (fun i => p i) F = 0) :
    let P := (finSuccEquiv ℝ 1) F
    let g := (uniqueAlgEquiv ℝ (Fin 1)) P.leadingCoeff
    ∃ z ∈ P.roots.toFinset.disjSum g.roots.toFinset, ∀ p : ℝ², p ∈ L ↔ match z with
      | .inl q => p 0 = eval (fun _ => p 1) q
      | .inr b => p 1 = b := by
  let P := (finSuccEquiv ℝ 1) F
  let g := (uniqueAlgEquiv ℝ (Fin 1)) P.leadingCoeff
  change ∃ z ∈ P.roots.toFinset.disjSum g.roots.toFinset, ∀ p : ℝ², p ∈ L ↔ match z with
      | .inl q => p 0 = eval (fun _ => p 1) q
      | .inr b => p 1 = b
  have hP : P ≠ 0 := fun h => hF ((finSuccEquiv ℝ 1).injective
    (h.trans (map_zero (finSuccEquiv ℝ 1)).symm))
  have hg : g ≠ 0 := fun h => (Polynomial.leadingCoeff_ne_zero.mpr hP)
    ((uniqueAlgEquiv ℝ (Fin 1)).injective (h.trans (map_zero (uniqueAlgEquiv ℝ (Fin 1))).symm))
  let U := S.filter (fun p => p ∈ L)
  have hU : U.card = 4 := four_points hL
  obtain ⟨b, hlevel⟩ | ⟨m, b, hgraph⟩ := charts hL
  · let e := eval (fun _ : Fin 1 => b)
    have hx (x : ℝ) : (P.map e).eval x = eval (Fin.cases x (fun _ : Fin 1 => b)) F := by
      calc
        _ = e (P.eval (C x)) := by
          simpa only [e, eval_C] using Polynomial.eval_map_apply (p := P) e (C x)
        _ = _ := by
          simpa only [e, P, eval_C] using
            eval_polynomial_eval_finSuccEquiv (x := fun _ : Fin 1 => b) F (C x)
    have hconst (p : ℝ²) (hp : p ∈ U) : p 1 = b := (hlevel p).mp (Finset.mem_filter.mp hp).2
    have hsmall : (P.map e).natDegree < U.card := by
      rw [hU]
      exact Polynomial.natDegree_map_le.trans_lt
        ((natDegree_finSuccEquiv F ▸ degreeOf_le_totalDegree F 0).trans_lt hd)
    have hzero : P.map e = 0 := by
      apply eq_zero_of_many_roots (U := U) (i := 0) _ _ hsmall
      · intro a ha c hc heq
        exact coordinates_eq heq ((hconst _ ha).trans (hconst _ hc).symm)
      · intro p hp
        rw [hx]
        have heq : (fun i => Fin.cases (p 0) (fun _ : Fin 1 => b) i) = fun i => p i := by
          funext i
          fin_cases i
          · rfl
          · exact (hconst p hp).symm
        rw [heq]
        exact hS p (Finset.mem_filter.mp hp).1
    have hg0 : g.eval b = 0 := by
      rw [show g.eval b = e P.leadingCoeff from unique_eval _ _]
      have hh := congrArg (fun W : Polynomial ℝ => W.coeff P.natDegree) hzero
      simpa only [Polynomial.coeff_map, Polynomial.coeff_zero, Polynomial.leadingCoeff] using hh
    refine ⟨.inr b, ?_, hlevel⟩
    simpa using (Polynomial.mem_roots hg).mpr hg0
  · let q : MvPolynomial (Fin 1) ℝ := C m * X 0 + C b
    let u : Fin 2 → Polynomial ℝ :=
      Fin.cases (Polynomial.C m * Polynomial.X + Polynomial.C b) (fun _ => Polynomial.X)
    let W := (eval₂Hom Polynomial.C u) F
    have hu (i : Fin 2) : (u i).natDegree ≤ 1 := by
      fin_cases i
      · change (Polynomial.C m * Polynomial.X + Polynomial.C b).natDegree ≤ 1
        exact Polynomial.natDegree_add_le_of_degree_le
          (by simpa using (Polynomial.natDegree_mul_le (p := Polynomial.C m) (q := Polynomial.X)))
          (by simp)
      · change (Polynomial.X : Polynomial ℝ).natDegree ≤ 1
        simp
    have hxy (p : ℝ²) (hp : p ∈ U) : p 0 = m * p 1 + b :=
      (hgraph p).mp (Finset.mem_filter.mp hp).2
    have hW : W = 0 := by
      apply eq_zero_of_many_roots (U := U) (i := 1)
      · intro a ha c hc he
        apply coordinates_eq _ he
        exact (hxy _ ha).trans ((congrArg (fun y => m*y+b) he).trans (hxy _ hc).symm)
      · intro p hp
        rw [show W.eval (p 1) = _ from eval_substitution F u (p 1)]
        have he : (fun i => (u i).eval (p 1)) = fun i => p i := by
          funext i
          fin_cases i
          · simpa [u] using (hxy p hp).symm
          · exact Polynomial.eval_X
        rw [he]
        exact hS p (Finset.mem_filter.mp hp).1
      · rw [hU]
        exact (degree_substitution F u hu).trans_lt hd
    have hroot : P.eval q = 0 := by
      apply MvPolynomial.funext
      intro y
      rw [map_zero, eval_polynomial_eval_finSuccEquiv]
      have he : (fun i => Fin.cases (eval y q) y i) = fun i => (u i).eval (y 0) := by
        funext i
        fin_cases i
        · simp [q, u]
        · exact (Polynomial.eval_X (x := y 0)).symm
      rw [he, ← eval_substitution F u (y 0)]
      change W.eval (y 0) = 0
      rw [hW, Polynomial.eval_zero]
    refine ⟨.inl q, ?_, ?_⟩
    · simpa using (Polynomial.mem_roots hP).mpr hroot
    · intro p
      simpa [q] using hgraph p

/-- A real algebraic curve of degree at most three, including a reducible one,
can support no more four-point lines than its total degree. -/
theorem four_lines_on_cubic (S : Finset ℝ²) (F : MvPolynomial (Fin 2) ℝ) (hF : F ≠ 0)
    (hd : F.totalDegree ≤ 3) (hS : ∀ p ∈ S, eval (fun i => p i) F = 0) :
    (linesWithPointsFor 4 (S : Set ℝ²)).ncard ≤ F.totalDegree := by
  let P := (finSuccEquiv ℝ 1) F
  let g := (uniqueAlgEquiv ℝ (Fin 1)) P.leadingCoeff
  let codes := P.roots.toFinset.disjSum g.roots.toFinset
  let A := (four_lines_finite S).toFinset
  have hP : P ≠ 0 := fun h => hF ((finSuccEquiv ℝ 1).injective
    (h.trans (map_zero (finSuccEquiv ℝ 1)).symm))
  let carrier (z : MvPolynomial (Fin 1) ℝ ⊕ ℝ) : Set ℝ² := {p | match z with
    | .inl q => p 0 = eval (fun _ => p 1) q
    | .inr b => p 1 = b}
  have h (L : A) : ∃ z ∈ codes, ∀ p : ℝ², p ∈ L.val ↔ p ∈ carrier z :=
    line_code ((four_lines_finite S).mem_toFinset.mp L.property) F hF (by omega) hS
  choose z hz hdesc using h
  let enc (L : A) : codes := ⟨z L, hz L⟩
  have hinj : Function.Injective enc := by
    intro L M he
    have hcode : z L = z M := congrArg Subtype.val he
    exact Subtype.ext (SetLike.ext fun p =>
      (hdesc L p).trans (hcode ▸ (hdesc M p).symm))
  have hcount : A.card ≤ codes.card := by simpa using Fintype.card_le_of_injective enc hinj
  have hdeg : g.natDegree ≤ P.leadingCoeff.totalDegree := by
    exact degree_substitution P.leadingCoeff (fun _ => Polynomial.X) (by simp)
  have hlead : P.coeff P.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  have hl := totalDegree_coeff_finSuccEquiv_add_le F P.natDegree hlead
  change P.leadingCoeff.totalDegree + P.natDegree ≤ F.totalDegree at hl
  rw [Set.ncard_eq_toFinset_card _ (four_lines_finite S)]
  calc
    A.card ≤ codes.card := hcount
    _ = P.roots.toFinset.card + g.roots.toFinset.card := Finset.card_disjSum ..
    _ ≤ P.natDegree + g.natDegree := Nat.add_le_add
      ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' P))
      ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' g))
    _ ≤ F.totalDegree := by omega

/-- With k points off a cubic, t₄ ≤ deg(F) + k(n−1)/3. -/
theorem four_lines_near_cubic (S : Finset ℝ²) (F : MvPolynomial (Fin 2) ℝ)
    (hF : F ≠ 0) (hd : F.totalDegree ≤ 3) :
    3 * (linesWithPointsFor 4 (S : Set ℝ²)).ncard ≤
      3 * F.totalDegree +
        (S.filter (fun p => eval (fun i => p i) F ≠ 0)).card * (S.card - 1) := by
  let T := S.filter (fun p => eval (fun i => p i) F = 0)
  have ht := four_lines_on_cubic T F hF hd (fun _ hp => (Finset.mem_filter.mp hp).2)
  have hdel := delete_points_bound (show T ⊆ S from Finset.filter_subset ..)
  have he : S \ T = S.filter (fun p => eval (fun i => p i) F ≠ 0) := by
    ext p
    by_cases hp : p ∈ S <;> simp [hp, T]
  rw [he] at hdel
  omega

/-- The desired asymptotic holds when all but o(n) points lie on a cubic.
Both the curve and the exceptional points may vary freely with n. -/
theorem littleO_near_cubics (S : ℕ → Finset ℝ²) (F : ℕ → MvPolynomial (Fin 2) ℝ)
    (hcard : ∀ n, (S n).card ≤ n) (hnonzero : ∀ n, F n ≠ 0)
    (hdeg : ∀ n, (F n).totalDegree ≤ 3)
    (hexceptions : (fun n => (((S n).filter (fun p => eval (fun i => p i) (F n) ≠ 0)).card : ℝ))
      =o[atTop] (fun n => (n : ℝ))) :
    (fun n => ((linesWithPointsFor 4 (↑(S n) : Set ℝ²)).ncard : ℝ))
      =o[atTop] (fun n => (n : ℝ)^2) := by
  apply IsLittleO.of_bound
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt (9 / ε)
  filter_upwards [eventually_ge_atTop (max K 1), hexceptions.bound hε] with n hn hsmall
  let k := ((S n).filter (fun p => eval (fun i => p i) (F n) ≠ 0)).card
  let q := (linesWithPointsFor 4 (↑(S n) : Set ℝ²)).ncard
  change ‖(k : ℝ)‖ ≤ ε * ‖(n : ℝ)‖ at hsmall
  change ‖(q : ℝ)‖ ≤ ε * ‖(n : ℝ)^2‖
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)] at hsmall
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (sq_nonneg _)]
  have hnear : 3 * q ≤ 9 + k * n := by
    have h := four_lines_near_cubic (S n) (F n) (hnonzero n) (hdeg n)
    change 3 * q ≤ 3 * (F n).totalDegree + k * ((S n).card - 1) at h
    exact h.trans (Nat.add_le_add (by have := hdeg n; omega)
      (Nat.mul_le_mul_left k ((Nat.sub_le ..).trans (hcard n))))
  have hr : 3 * (q : ℝ) ≤ 9 + (k : ℝ) * n := by exact_mod_cast hnear
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnK : (K : ℝ) ≤ n := by exact_mod_cast (show K ≤ n by omega)
  have hsq : (n : ℝ) ≤ (n : ℝ)^2 := by nlinarith [mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hn1)]
  have hconst : (9 : ℝ) ≤ ε * (n : ℝ)^2 :=
    (by linarith [(div_lt_iff₀ hε).mp hK] : (9 : ℝ) ≤ ε * K).trans
      (mul_le_mul_of_nonneg_left (hnK.trans hsq) hε.le)
  have hkn := mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg n : 0 ≤ (n : ℝ))
  nlinarith only [hr, hconst, hkn]

/-- Absorb the uniform constant for cubics into the quadratic error term. -/
lemma all_degrees_bound (h2 : H2) (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ S : Finset ℝ², S.card ≤ n → NonCollinearFor 5 (S : Set ℝ²) →
        ∀ F : MvPolynomial (Fin 2) ℝ, F ≠ 0 → F.totalDegree ≤ d →
          (∀ p ∈ S, eval (fun i => p i) F = 0) →
          ((linesWithPointsFor 4 (S : Set ℝ²)).ncard : ℝ) ≤ ε * (n : ℝ)^2 := by
  obtain ⟨N, hhigh⟩ := h2 d ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt (3 / ε)
  refine ⟨max N (max K 1), ?_⟩
  intro n hn S hSn hS F hF hd hzero
  by_cases hsmall : F.totalDegree ≤ 3
  · have hk : (K : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show K ≤ n by omega)
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
    have hsq : (n : ℝ) ≤ (n : ℝ)^2 := by nlinarith [mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hn1)]
    calc
      _ ≤ (3 : ℝ) := by exact_mod_cast (four_lines_on_cubic S F hF hsmall hzero).trans hsmall
      _ ≤ ε * K := by linarith [(div_lt_iff₀ hε).mp hK]
      _ ≤ ε * (n : ℝ)^2 := mul_le_mul_of_nonneg_left (hk.trans hsq) hε.le
  · exact hhigh n (le_trans (le_max_left ..) hn) S hSn hS F hF (by omega) hd hzero

lemma configuration_bound (h1 : H1) (h2 : H2) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ S : Finset ℝ², N ≤ S.card → NonCollinearFor 5 (S : Set ℝ²) →
      ((linesWithPointsFor 4 (S : Set ℝ²)).ncard : ℝ) ≤ ε * (S.card : ℝ)^2 := by
  obtain ⟨d, η, hη, N, hcap⟩ := capture_many h1 4 ε hε
  obtain ⟨M, halg⟩ := all_degrees_bound h2 d (η / 2) (half_pos hη)
  refine ⟨max (max N M) 1, ?_⟩
  intro S hn hS
  have hN := (le_max_left N M).trans ((le_max_left _ 1).trans hn)
  have hM := (le_max_right N M).trans ((le_max_left _ 1).trans hn)
  have hpos : 0 < (S.card : ℝ) := by
    have hh := (le_max_right (max N M) 1).trans hn
    exact_mod_cast (show 0 < S.card by omega)
  let hfin := four_lines_finite S
  let A := hfin.toFinset
  have hA : ∀ L ∈ A, L ∈ linesWithPointsFor 4 (S : Set ℝ²) := fun _ hL => hfin.mem_toFinset.mp hL
  rw [Set.ncard_eq_toFinset_card _ hfin]
  by_contra! hlarge
  obtain ⟨mark, hpoints, hcover⟩ := enumerate_four hA
  obtain ⟨F, hF, hdeg, B, hBA, hB, hzero⟩ := hcap S A mark hN hS hA hpoints hlarge.le
  let T := S.filter (fun p => eval (fun j => p j) F = 0)
  have hTS : T ⊆ S := Finset.filter_subset ..
  have hsub : B ⊆ (four_lines_finite T).toFinset := by
    intro L hL
    apply (four_lines_finite T).mem_toFinset.mpr
    apply mem_after_restriction hTS (hA L (hBA hL))
    intro p hp hpL
    obtain ⟨i, hi⟩ := hcover L (hBA hL) p hp hpL
    exact Finset.mem_filter.mpr ⟨hp, hi ▸ hzero L hL i⟩
  have hub := halg S.card hM T (Finset.card_le_card hTS) (hS.subset hTS) F hF hdeg
    (fun _ hp => (Finset.mem_filter.mp hp).2)
  rw [Set.ncard_eq_toFinset_card _ (four_lines_finite T)] at hub
  have hcard : (B.card : ℝ) ≤ ((four_lines_finite T).toFinset.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have himpossible := hB.trans (hcard.trans hub)
  exact (not_le_of_gt (mul_lt_mul_of_pos_right (half_lt_self hη) (sq_pos_of_pos hpos))) himpossible

theorem main : H1 → H2 → type_of% @Erdos101.erdos_101 := by
  intro h1 h2
  apply IsLittleO.of_bound
  intro ε hε
  obtain ⟨N, hbound⟩ := configuration_bound h1 h2 ε hε
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (sq_nonneg _)]
  have hmax : Erdos101.numLinesWithFourPointMax n ≤ ⌊ε * (n : ℝ)^2⌋₊ := by
    apply csSup_le'
    rintro b ⟨S, hcard, hfin, hS, rfl⟩
    let T := hfin.toFinset
    have he : (T : Set ℝ²) = S := hfin.coe_toFinset
    have hTcard : T.card = n := (Set.ncard_eq_toFinset_card S hfin).symm.trans hcard
    apply Nat.le_floor
    have h := hbound T (hTcard ▸ hn) (he ▸ hS)
    simpa only [he, hTcard] using h
  exact (Nat.cast_le.mpr hmax).trans (Nat.floor_le (mul_nonneg hε.le (sq_nonneg _)))

end OMA.R_Erdos101_erdos_101_R1
