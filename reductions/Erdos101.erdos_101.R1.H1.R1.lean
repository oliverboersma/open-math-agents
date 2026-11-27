import OMAReductions.R_Erdos101_erdos_101_R1

/-!
# Marked points on many four-point lines

An unmarked triple-line inverse theorem can be applied repeatedly to the
points outside a curve already collected. This bounds the number of
four-point lines having at most one point on the resulting curve.
The second hypothesis concerns the remaining secants and retains the
specified set of points required by the parent reduction.
-/

namespace OMA.R_Erdos101_erdos_101_R1_H1_R1

open EuclideanGeometry MvPolynomial
open scoped Classical

/-- Unmarked capture when a subset contains at least three points on each
of a positive-density family of four-point lines of the ambient set. -/
def H1 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ d : ℕ, ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ,
    ∀ S U : Finset ℝ², N ≤ S.card → U ⊆ S → NonCollinearFor 5 (S : Set ℝ²) →
    ∀ A : Finset (AffineSubspace ℝ ℝ²), δ*(S.card : ℝ)^2 ≤ A.card →
      (∀ L ∈ A, L ∈ linesWithPointsFor 4 (S : Set ℝ²) ∧ 3 ≤ (U.filter (fun p => p ∈ L)).card) →
      ∃ F : MvPolynomial (Fin 2) ℝ, F ≠ 0 ∧ F.totalDegree ≤ d ∧
        c*S.card ≤ (U.filter (fun p => eval (fun i => p i) F = 0)).card

/-- Marked capture for points outside one bounded-degree curve, when each
specified point lies on linearly many four-point lines with two points on the curve. -/
def H2 : Prop :=
  ∀ d : ℕ, ∀ τ : ℝ, 0 < τ → ∃ e : ℕ, ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ,
    ∀ S T : Finset ℝ², N ≤ S.card → T ⊆ S → NonCollinearFor 5 (S : Set ℝ²) →
    ∀ F : MvPolynomial (Fin 2) ℝ, F ≠ 0 → F.totalDegree ≤ d →
      (∀ p ∈ T, eval (fun i => p i) F ≠ 0) → τ*S.card ≤ T.card →
      (∀ p ∈ T, ∃ A : Finset (AffineSubspace ℝ ℝ²), τ*S.card ≤ A.card ∧
        ∀ L ∈ A, p ∈ L ∧ L ∈ linesWithPointsFor 4 (S : Set ℝ²) ∧
          2 ≤ (S.filter (fun x => x ∈ L ∧ eval (fun i => x i) F = 0)).card) →
      ∃ G : MvPolynomial (Fin 2) ℝ, G ≠ 0 ∧ G.totalDegree ≤ e ∧
        c*S.card ≤ (T.filter (fun p => eval (fun i => p i) G = 0)).card

lemma product_gain (S : Finset ℝ²) (F G : MvPolynomial (Fin 2) ℝ) :
    (S.filter (fun p => eval (fun i => p i) F = 0)).card +
      ((S.filter (fun p => eval (fun i => p i) F ≠ 0)).filter (fun p => eval (fun i => p i) G = 0)).card =
      (S.filter (fun p => eval (fun i => p i) (F*G) = 0)).card := by
  let C := S.filter (fun p => eval (fun i => p i) F = 0)
  let D := (S.filter (fun p => eval (fun i => p i) F ≠ 0)).filter (fun p => eval (fun i => p i) G = 0)
  have hd : Disjoint C D := Finset.disjoint_left.mpr (fun _ hx hy =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2 (Finset.mem_filter.mp hx).2)
  have he : C ∪ D = S.filter (fun p => eval (fun i => p i) (F*G) = 0) := by
    ext p
    simp only [C,D,Finset.mem_union,Finset.mem_filter,map_mul,mul_eq_zero]
    tauto
  exact (Finset.card_union_of_disjoint hd).symm.trans (congrArg Finset.card he)

/-- After collecting a bounded number of curves, fewer than δn² of the given
four-point lines have three or more points outside their union. -/
theorem two_points_on_curve (hunmarked : H1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ D N : ℕ, ∀ S : Finset ℝ², N ≤ S.card → NonCollinearFor 5 (S : Set ℝ²) →
      ∀ A : Finset (AffineSubspace ℝ ℝ²), (∀ L ∈ A, L ∈ linesWithPointsFor 4 (S : Set ℝ²)) →
        ∃ F : MvPolynomial (Fin 2) ℝ, F ≠ 0 ∧ F.totalDegree ≤ D ∧
          ((A.filter (fun L => 3 ≤ (S.filter (fun p => p ∈ L ∧ eval (fun i => p i) F ≠ 0)).card)).card : ℝ)
            < δ*(S.card : ℝ)^2 := by
  classical
  obtain ⟨d,c,hc,N,hN⟩ := hunmarked δ hδ
  obtain ⟨k,hk⟩ := exists_nat_gt (1/c)
  refine ⟨k*d,max 1 N,?_⟩
  intro S hn hcap A hA
  let n : ℝ := S.card
  have hn₀ : 0 < n := by dsimp [n]; exact_mod_cast (show 0 < S.card by omega)
  let outside (F : MvPolynomial (Fin 2) ℝ) := S.filter (fun p => eval (fun i => p i) F ≠ 0)
  let mass (F : MvPolynomial (Fin 2) ℝ) : ℝ := (S.filter (fun p => eval (fun i => p i) F = 0)).card
  let bad (F : MvPolynomial (Fin 2) ℝ) :=
    A.filter (fun L => 3 ≤ (S.filter (fun p => p ∈ L ∧ eval (fun i => p i) F ≠ 0)).card)
  have iterate (j : ℕ) : ∃ F : MvPolynomial (Fin 2) ℝ, F ≠ 0 ∧ F.totalDegree ≤ j*d ∧
      (((bad F).card : ℝ) < δ*n^2 ∨ (j : ℝ)*(c*n) ≤ mass F) := by
    induction j with
    | zero => exact ⟨1,one_ne_zero,by simp,Or.inr (by simp [mass])⟩
    | succ j ih =>
      obtain ⟨F,hF,hdeg,hstep⟩ := ih
      by_cases doneF : ((bad F).card : ℝ) < δ*n^2
      · exact ⟨F,hF,hdeg.trans (Nat.mul_le_mul_right _ (Nat.le_succ _)),Or.inl doneF⟩
      have hlines (L) (hL : L ∈ bad F) : L ∈ linesWithPointsFor 4 (S : Set ℝ²) ∧
          3 ≤ ((outside F).filter (fun p => p ∈ L)).card := by
        obtain ⟨hLA,hs⟩ := Finset.mem_filter.mp hL
        exact ⟨hA L hLA,by simpa [outside,Finset.filter_filter,and_comm] using hs⟩
      obtain ⟨G,hG,hdG,hgain⟩ := hN S (outside F) ((le_max_right ..).trans hn)
        (Finset.filter_subset ..) hcap (bad F) (le_of_not_gt doneF) hlines
      have he : mass F + (((outside F).filter (fun p => eval (fun i => p i) G = 0)).card : ℝ) =
          mass (F*G) := by dsimp [mass,outside]; exact_mod_cast product_gain S F G
      have hprev := hstep.resolve_left doneF
      refine ⟨F*G,mul_ne_zero hF hG,(totalDegree_mul F G).trans ?_,Or.inr ?_⟩
      · rw [Nat.succ_mul]
        exact Nat.add_le_add hdeg hdG
      · change c*n ≤ _ at hgain
        push_cast
        linarith only [he,hprev,hgain]
  obtain ⟨F,hF,hdeg,hstep⟩ := iterate k
  refine ⟨F,hF,hdeg,hstep.resolve_right ?_⟩
  have hmax : mass F ≤ n := by dsimp [mass,n]; exact_mod_cast Finset.card_filter_le ..
  have hkc : 1 < (k:ℝ)*c := (div_lt_iff₀ hc).mp hk
  have hkn := mul_lt_mul_of_pos_right hkc hn₀
  intro hbad
  exact (not_le_of_gt (by simpa only [one_mul,mul_assoc] using hkn : n < (k:ℝ)*(c*n))) (hbad.trans hmax)

/-- A family of four-point lines contributes at most four marked incidences per line. -/
lemma marked_incidence_bound {S U : Finset ℝ²} (hUS : U ⊆ S)
    {B : Finset (AffineSubspace ℝ ℝ²)} (hB : ∀ L ∈ B, L ∈ linesWithPointsFor 4 (S : Set ℝ²)) :
    (∑ p ∈ U, (B.filter (fun L => p ∈ L)).card) ≤ 4*B.card := by
  have he : ∑ L ∈ B, (U.filter (fun p => p ∈ L)).card =
      ∑ p ∈ U, (B.filter (fun L => p ∈ L)).card :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun L p => p ∈ L)
  rw [← he]
  calc
    _ ≤ ∑ _L ∈ B, 4 := Finset.sum_le_sum (fun L hL =>
      (Finset.card_le_card (Finset.filter_subset_filter _ hUS)).trans_eq
        (OMA.R_Erdos101_erdos_101_R1.four_points (hB L hL)))
    _ = _ := by simp [mul_comm]

/-- If the collected curve captures few marked points, many marked points
outside it have small pencils of exceptional lines. -/
lemma discard_exceptional_points (τ : ℝ) (hτ : 0 < τ) (S T : Finset ℝ²) (hTS : T ⊆ S)
    (hn : 0 < S.card) (hT : τ*S.card ≤ T.card) (F : MvPolynomial (Fin 2) ℝ)
    (hon : ((T.filter (fun p => eval (fun i => p i) F = 0)).card : ℝ) < (τ/4)*S.card)
    (B : Finset (AffineSubspace ℝ ℝ²)) (hB : ∀ L ∈ B, L ∈ linesWithPointsFor 4 (S : Set ℝ²))
    (hfew : (B.card : ℝ) < (τ^2/32)*(S.card : ℝ)^2) :
    ∃ W ⊆ T, (τ/2)*S.card ≤ W.card ∧ ∀ p ∈ W, eval (fun i => p i) F ≠ 0 ∧
      ((B.filter (fun L => p ∈ L)).card : ℝ) < (τ/2)*S.card := by
  classical
  let n : ℝ := S.card
  have hn₀ : 0 < n := by dsimp [n]; exact_mod_cast hn
  let onCurve := T.filter (fun p => eval (fun i => p i) F = 0)
  let many := T.filter (fun p => (τ/2)*n ≤ ((B.filter (fun L => p ∈ L)).card : ℝ))
  let W := T \ (onCurve ∪ many)
  have hbadprod : (many.card : ℝ)*((τ/2)*n) ≤ 4*(B.card : ℝ) := by
    calc
      _ = ∑ _p ∈ many, (τ/2)*n := by simp
      _ ≤ ∑ p ∈ many, ((B.filter (fun L => p ∈ L)).card : ℝ) :=
        Finset.sum_le_sum (fun _ hp => (Finset.mem_filter.mp hp).2)
      _ ≤ _ := by exact_mod_cast marked_incidence_bound ((Finset.filter_subset _ T).trans hTS) hB
  have hbad : (many.card : ℝ) < (τ/4)*n := by
    by_contra! hlarge
    have hl := mul_le_mul_of_nonneg_right hlarge (show 0 ≤ (τ/2)*n by positivity)
    change (B.card : ℝ) < (τ^2/32)*n^2 at hfew
    nlinarith only [hl,hbadprod,hfew]
  have hsub : T ⊆ (onCurve ∪ many) ∪ W := by
    intro p hp
    by_cases hm : p ∈ onCurve ∪ many
    · exact Finset.mem_union_left _ hm
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hp,hm⟩)
  have hcard : T.card ≤ onCurve.card + many.card + W.card := (Finset.card_le_card hsub).trans
    ((Finset.card_union_le ..).trans (Nat.add_le_add_right (Finset.card_union_le ..) _))
  refine ⟨W,Finset.sdiff_subset,?_,?_⟩
  · have hsize : (T.card : ℝ) ≤ onCurve.card + many.card + W.card := by exact_mod_cast hcard
    change (onCurve.card : ℝ) < (τ/4)*n at hon
    change τ*n ≤ T.card at hT
    change (τ/2)*n ≤ W.card
    linarith
  · intro p hp
    obtain ⟨hpT,hout⟩ := Finset.mem_sdiff.mp hp
    constructor
    · exact fun h => hout (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hpT,h⟩))
    · exact lt_of_not_ge (fun h => hout (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hpT,h⟩)))

lemma two_on_of_at_most_two_off {S : Finset ℝ²} {L : AffineSubspace ℝ ℝ²}
    (hL : L ∈ linesWithPointsFor 4 (S : Set ℝ²)) (F : MvPolynomial (Fin 2) ℝ)
    (hoff : ¬ 3 ≤ (S.filter (fun p => p ∈ L ∧ eval (fun i => p i) F ≠ 0)).card) :
    2 ≤ (S.filter (fun p => p ∈ L ∧ eval (fun i => p i) F = 0)).card := by
  have h := Finset.card_filter_add_card_filter_not (s := S.filter (fun p => p ∈ L))
    (fun p => eval (fun i => p i) F = 0)
  rw [OMA.R_Erdos101_erdos_101_R1.four_points hL] at h
  simp only [Finset.filter_filter] at h
  have h' : (S.filter (fun p => p ∈ L ∧ eval (fun i => p i) F = 0)).card +
      (S.filter (fun p => p ∈ L ∧ eval (fun i => p i) F ≠ 0)).card = 4 := h
  omega

theorem main : H1 → H2 → OMA.R_Erdos101_erdos_101_R1.H1 := by
  intro hunmarked hsecant τ hτ
  let δ := τ^2/32
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨D,N,hN⟩ := two_points_on_curve hunmarked δ hδ
  obtain ⟨e,c,hc,M,hM⟩ := hsecant D (τ/2) (half_pos hτ)
  refine ⟨max D e,min (τ/4) c,lt_min (by positivity) hc,max 1 (max N M),?_⟩
  intro S T hn hTS hcap hT hstars
  let A := (OMA.R_Erdos101_erdos_101_R1.four_lines_finite S).toFinset
  have hA (L) : L ∈ A ↔ L ∈ linesWithPointsFor 4 (S : Set ℝ²) :=
    (OMA.R_Erdos101_erdos_101_R1.four_lines_finite S).mem_toFinset
  obtain ⟨F,hF,hD,hfew⟩ := hN S (by omega) hcap A (fun L hL => (hA L).mp hL)
  by_cases hcapture : (τ/4)*S.card ≤ (T.filter (fun p => eval (fun i => p i) F = 0)).card
  · exact ⟨F,hF,hD.trans (le_max_left ..),
      (mul_le_mul_of_nonneg_right (min_le_left ..) (Nat.cast_nonneg _)).trans hcapture⟩
  let B := A.filter (fun L => 3 ≤ (S.filter (fun p => p ∈ L ∧ eval (fun i => p i) F ≠ 0)).card)
  have hB (L) (hL : L ∈ B) := (hA L).mp (Finset.mem_filter.mp hL).1
  obtain ⟨W,hWT,hW,hpW⟩ := discard_exceptional_points τ hτ S T hTS (by omega) hT F
    (lt_of_not_ge hcapture) B hB hfew
  obtain ⟨G,hG,he,hcaptured⟩ := hM S W (by omega) (hWT.trans hTS) hcap F hF hD
    (fun p hp => (hpW p hp).1) hW (by
      intro p hp
      obtain ⟨C,hCnum,hC⟩ := hstars p (hWT hp)
      refine ⟨C \ B,?_,?_⟩
      · have hsub : C ⊆ (C \ B) ∪ (B.filter (fun L => p ∈ L)) := by
          intro L hL
          by_cases hb : L ∈ B
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hb,(hC L hL).1⟩)
          · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hL,hb⟩)
        have hreal : (C.card : ℝ) ≤ (C \ B).card + (B.filter (fun L => p ∈ L)).card := by
          exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le ..)
        linarith only [hreal,(hpW p hp).2,hCnum]
      · intro L hL
        obtain ⟨hcL,hbL⟩ := Finset.mem_sdiff.mp hL
        obtain ⟨hpL,hfour⟩ := hC L hcL
        exact ⟨hpL,hfour,two_on_of_at_most_two_off hfour F
          (fun h => hbL (Finset.mem_filter.mpr ⟨(hA L).mpr hfour,h⟩))⟩)
  refine ⟨G,hG,he.trans (le_max_right ..),?_⟩
  exact ((mul_le_mul_of_nonneg_right (min_le_right ..) (Nat.cast_nonneg _)).trans hcaptured).trans
    (by exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hWT))

/-- A family of four-point lines meeting V is bounded by the sum of the
pencils through V. -/
lemma lines_meeting_points {S V : Finset ℝ²} (hVS : V ⊆ S) {A : Finset (AffineSubspace ℝ ℝ²)}
    (hA : ∀ L ∈ A, L ∈ linesWithPointsFor 4 (S : Set ℝ²))
    (hV : ∀ L ∈ A, ∃ p ∈ V, p ∈ L) : A.card ≤ V.card*S.card := by
  classical
  let pencil (p : ℝ²) := A.filter (fun L => p ∈ L)
  have hsub : A ⊆ V.biUnion pencil := by
    intro L hL
    obtain ⟨p,hp,he⟩ := hV L hL
    exact Finset.mem_biUnion.mpr ⟨p,hp,Finset.mem_filter.mpr ⟨hL,he⟩⟩
  calc
    _ ≤ _ := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ V, S.card := Finset.sum_le_sum (fun p hp => by
      have h := OMA.R_Erdos101_erdos_101_R1.pencil_bound hA (hVS hp)
      change 3*(pencil p).card ≤ _ at h
      omega)
    _ = _ := by simp

/-- Both subproblems also follow from the parent capture statement.
Thus their conjunction is equivalent to that statement. -/
theorem cases_of_marked_capture (capture : OMA.R_Erdos101_erdos_101_R1.H1) : H1 ∧ H2 := by
  classical
  constructor
  · intro δ hδ
    obtain ⟨d,c,hc,N,hN⟩ := OMA.R_Erdos101_erdos_101_R1.capture_one capture δ hδ
    refine ⟨d,c,hc,max 1 N,?_⟩
    intro S U hn hUS hcap A hdense hlines
    have hex (L) (hL : L ∈ A) : ∃ p ∈ U, p ∈ L := by
      have hs := (hlines L hL).2
      obtain ⟨p,hp⟩ := Finset.card_pos.mp (show 0 < (U.filter (fun p => p ∈ L)).card by omega)
      exact ⟨p,Finset.mem_filter.mp hp⟩
    let mark (L : AffineSubspace ℝ ℝ²) := if h : L ∈ A then (hex L h).choose else 0
    have hmark L (hL : L ∈ A) : mark L ∈ U ∧ mark L ∈ L := by
      simpa [mark,hL] using (hex L hL).choose_spec
    obtain ⟨F,hF,hdeg,B,hBA,hnum,hzero⟩ := hN S A mark ((le_max_right ..).trans hn) hcap
      (fun L hL => (hlines L hL).1)
      (fun L hL => ⟨hUS (hmark L hL).1,(hmark L hL).2⟩) hdense
    let V := U.filter (fun p => eval (fun i => p i) F = 0)
    have hv : B.card ≤ V.card*S.card := lines_meeting_points ((Finset.filter_subset ..).trans hUS)
      (fun L hL => (hlines L (hBA hL)).1)
      (fun L hL => ⟨mark L,Finset.mem_filter.mpr ⟨(hmark L (hBA hL)).1,hzero L hL⟩,(hmark L (hBA hL)).2⟩)
    have hR : (B.card : ℝ) ≤ (V.card : ℝ)*S.card := by exact_mod_cast hv
    have hpos : 0 < (S.card : ℝ) := by exact_mod_cast (show 0 < S.card by omega)
    refine ⟨F,hF,hdeg,le_of_mul_le_mul_right (a := (S.card:ℝ)) ?_ hpos⟩
    nlinarith only [hnum,hR]
  · intro _ τ hτ
    obtain ⟨e,c,hc,N,hN⟩ := capture τ hτ
    refine ⟨e,c,hc,N,?_⟩
    intro S T hn hTS hcap _ _ _ _ hT hstars
    apply hN S T hn hTS hcap hT
    intro p hp
    obtain ⟨A,hnum,hA⟩ := hstars p hp
    exact ⟨A,hnum,fun L hL => ⟨(hA L hL).1,(hA L hL).2.1⟩⟩

end OMA.R_Erdos101_erdos_101_R1_H1_R1
