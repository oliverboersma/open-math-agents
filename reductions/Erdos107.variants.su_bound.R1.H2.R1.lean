import OMAReductions.R_Erdos107_variants_su_bound_R1
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Nat.Choose.Bounds

-- Reduction Erdos107.variants.su_bound.R1.H2.R1 of step Erdos107.variants.su_bound.R1.H2
-- Credit: @mucoucah
-- Suk's argument (pockets, chain/antichain analysis, asymmetric cups-caps, joining) is proved
-- below. What remains is the Por-Valtr positive-fraction Erdos-Szekeres theorem, in the form:
-- m disjoint large parts of X such that every transversal triple i < j < l is clockwise.
-- H1 and H2 are this statement for X of even and of odd size.

open Finset Filter

namespace OMA.R_Erdos107_variants_su_bound_R1_H2_R1

namespace SukOdd

variable {orient : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ → ℝ}
  [hO : Fact (∀ a b c : ℝ × ℝ,
    orient a b c = (b.1 - a.1) * (c.2 - b.2) - (b.2 - a.2) * (c.1 - b.1))]


theorem orient_cycle (a b c : (ℝ × ℝ)) : orient a b c = orient b c a := by
  simp only [hO.out]
  ring

theorem orient_flip (a b c : (ℝ × ℝ)) : orient a b c = -orient b a c := by
  simp only [hO.out]
  ring

theorem orient_basis (p q a b r : (ℝ × ℝ)) :
    orient p a b * orient p q r =
      orient p r b * orient p q a + orient p a r * orient p q b := by
  simp only [hO.out]
  ring

/-- A secant with both anchors to its right also has every point in their angular sector to
its right. -/
theorem orient_lt_of_sector {p q a b r : (ℝ × ℝ)}
    (hab : 0 < orient p a b) (har : 0 < orient p a r) (hrb : 0 < orient p r b)
    (hqa : orient p q a < 0) (hqb : orient p q b < 0) :
    orient p q r < 0 := by
  refine lt_of_not_ge fun h => ?_
  have hnonneg := mul_nonneg hab.le h
  rw [(orient_basis (orient := orient))] at hnonneg
  apply (not_lt_of_ge hnonneg)
  exact add_neg (mul_neg_of_pos_of_neg hrb hqa) (mul_neg_of_pos_of_neg har hqb)

/-- A secant with opposite anchor signs is consistently oriented toward a point on the
corresponding side of both anchor rays. -/
theorem orient_lt_of_preceding {p q a b r : (ℝ × ℝ)}
    (hab : 0 < orient p a b) (har : orient p a r < 0) (hrb : 0 < orient p r b)
    (hqa : orient p q a < 0) (hqb : 0 < orient p q b) :
    orient p q r < 0 := by
  refine lt_of_not_ge fun h => ?_
  have hnonneg := mul_nonneg hab.le h
  rw [(orient_basis (orient := orient))] at hnonneg
  apply (not_lt_of_ge hnonneg)
  exact add_neg (mul_neg_of_pos_of_neg hrb hqa) (mul_neg_of_neg_of_pos har hqb)

theorem orient_pos_of_following {p q a b r : (ℝ × ℝ)}
    (hab : 0 < orient p a b) (har : 0 < orient p a r) (hrb : orient p r b < 0)
    (hqa : orient p q a < 0) (hqb : 0 < orient p q b) :
    0 < orient p q r := by
  apply (mul_pos_iff_of_pos_left hab).mp
  rw [(orient_basis (orient := orient))]
  exact add_pos (mul_pos_of_neg_of_neg hrb hqa) (mul_pos har hqb)

theorem convex_subset {X Y : Finset (ℝ × ℝ)} (hYX : Y ⊆ X) (hX : (∀ p_c ∈ X, ∃ u_c v_c : ℝ, ∀ q_c ∈ X, q_c ≠ p_c → u_c * p_c.1 + v_c * p_c.2 < u_c * q_c.1 + v_c * q_c.2)) :
    (∀ p_c ∈ Y, ∃ u_c v_c : ℝ, ∀ q_c ∈ Y, q_c ≠ p_c → u_c * p_c.1 + v_c * p_c.2 < u_c * q_c.1 + v_c * q_c.2) := by
  intro p hp
  obtain ⟨u, v, huv⟩ := hX p (hYX hp)
  exact ⟨u, v, fun q hq hne => huv q (hYX hq) hne⟩

theorem exact_convex_size {X Y : Finset (ℝ × ℝ)} {n : ℕ}
    (hYX : Y ⊆ X) (hY : (∀ p_c ∈ Y, ∃ u_c v_c : ℝ, ∀ q_c ∈ Y, q_c ≠ p_c → u_c * p_c.1 + v_c * p_c.2 < u_c * q_c.1 + v_c * q_c.2)) (hn : n ≤ Y.card) :
    ∃ Z ⊆ X, Z.card = n ∧ (∀ p_c ∈ Z, ∃ u_c v_c : ℝ, ∀ q_c ∈ Z, q_c ≠ p_c → u_c * p_c.1 + v_c * p_c.2 < u_c * q_c.1 + v_c * q_c.2) := by
  obtain ⟨Z, hZY, hZ⟩ := Finset.exists_subset_card_eq hn
  exact ⟨Z, hZY.trans hYX, hZ, convex_subset hZY hY⟩

/-- If no consecutive directed pair attains the target, the first summand must
grow by the full surplus at every step. -/
theorem growth_along_blocks {a b : ℕ → ℕ} {n d k : ℕ}
    (hlarge : ∀ i ≤ k, n + d ≤ a i + b i)
    (hsmall : ∀ i < k, a i + b (i + 1) < n) :
    a 0 + k * (d + 1) ≤ a k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hprev := ih (fun i hi => hlarge i (by omega)) (fun i hi => hsmall i (by omega))
    have hstep := hlarge (k + 1) le_rfl
    have hpair := hsmall k (by omega)
    rw [Nat.succ_mul]
    omega

theorem orient_reverse (a b c : (ℝ × ℝ)) : orient a b c = -orient c b a := by
  simp only [hO.out]
  ring

theorem orient_swap_last (a b c : (ℝ × ℝ)) : orient a b c = -orient a c b := by
  simp only [hO.out]
  ring

theorem orient_of_rotatedKey {ι : Type*} [LinearOrder ι]
    {X : Finset (ℝ × ℝ)} {key : (ℝ × ℝ) → ι}
    (h : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, key a < key b → key b < key c →
      orient a b c < 0)
    {p q r : (ℝ × ℝ)} (hp : p ∈ X) (hq : q ∈ X) (hr : r ∈ X)
    (hpq : key q ≠ key p)
    (hqr : (toLex (decide ((key q) < (key p)), (key q))) < (toLex (decide ((key r) < (key p)), (key r)))) :
    orient p q r < 0 := by
  rw [Prod.Lex.toLex_lt_toLex] at hqr
  by_cases hq' : key q < key p <;> by_cases hr' : key r < key p
  · have he : key q < key r := by simpa [hq', hr'] using hqr
    rw [(orient_cycle (orient := orient))]
    exact h q hq r hr p hp he hr'
  · simp [hq', hr'] at hqr
    exact ((by decide : ¬ (true : Bool) < false) hqr).elim
  · have hpq' := lt_of_le_of_ne (le_of_not_gt hq') hpq.symm
    rw [← (orient_cycle (orient := orient)) r p q]
    exact h r hr p hp q hq hr' hpq'
  · have hpq' := lt_of_le_of_ne (le_of_not_gt hq') hpq.symm
    have he : key q < key r := by simpa [hq', hr'] using hqr
    exact h p hp q hq r hr hpq' he

theorem rotatedKey_injective {ι : Type*} [LinearOrder ι] (origin : ι) :
    Function.Injective (fun u : ι => (toLex (decide (u < origin), u))) := by
  intro u v huv
  exact congrArg (fun z => (ofLex z).2) huv

theorem dot_strict {p r : (ℝ × ℝ)} (hne : p ≠ r) :
    (r.1 - p.1) * p.1 + (r.2 - p.2) * p.2 <
      (r.1 - p.1) * r.1 + (r.2 - p.2) * r.2 := by
  rcases not_and_or.mp (fun h : p.1 = r.1 ∧ p.2 = r.2 => hne (Prod.ext h.1 h.2)) with h | h
  · nlinarith only [sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm h) : r.1 - p.1 ≠ 0),
      sq_nonneg (r.2 - p.2)]
  · nlinarith only [sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm h) : r.2 - p.2 ≠ 0),
      sq_nonneg (r.1 - p.1)]

/-- A cyclic order in which every triple turns clockwise gives strict support at every point. -/
theorem convex_of_clockwise {ι : Type*} [LinearOrder ι]
    {X : Finset (ℝ × ℝ)} {key : (ℝ × ℝ) → ι} (hinj : Set.InjOn key (X : Set (ℝ × ℝ)))
    (h : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, key a < key b → key b < key c →
      orient a b c < 0) : (∀ p_c ∈ X, ∃ u_c v_c : ℝ, ∀ q_c ∈ X, q_c ≠ p_c → u_c * p_c.1 + v_c * p_c.2 < u_c * q_c.1 + v_c * q_c.2) := by
  classical
  intro p hp
  let T := X.erase p
  by_cases hT : T.Nonempty
  · let key' := fun q => (toLex (decide ((key q) < (key p)), (key q)))
    obtain ⟨r, hr, hmin⟩ := Finset.exists_min_image T key' hT
    obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image T key' hT
    have hne (q : (ℝ × ℝ)) (hq : q ∈ T) : key q ≠ key p :=
      fun e => (mem_erase.mp hq).1 (hinj (mem_erase.mp hq).2 hp e)
    have hinj' : Set.InjOn key' (T : Set (ℝ × ℝ)) :=
      fun a ha b hb e => hinj (mem_erase.mp ha).2 (mem_erase.mp hb).2
        (rotatedKey_injective (key p) e)
    have hrot {a b : (ℝ × ℝ)} (ha : a ∈ T) (hb : b ∈ T) (hab : key' a < key' b) :
        orient p a b < 0 :=
      orient_of_rotatedKey h hp (mem_erase.mp ha).2 (mem_erase.mp hb).2
        (hne a ha) hab
    by_cases hrs : r = s
    · refine ⟨r.1 - p.1, r.2 - p.2, fun q hq hqp => ?_⟩
      have hqT : q ∈ T := mem_erase.mpr ⟨hqp, hq⟩
      have hqr : q = r := hinj' hqT hr (le_antisymm (hrs ▸ hmax q hqT) (hmin q hqT))
      subst q
      exact dot_strict (mem_erase.mp hr).1.symm
    · refine ⟨r.2 - s.2, s.1 - r.1, fun q hq hqp => ?_⟩
      have hqT : q ∈ T := mem_erase.mpr ⟨hqp, hq⟩
      have hl : orient p r q ≤ 0 := by
        by_cases hqr : r = q
        · subst q
          simp [hO.out]
        exact (hrot hr hqT ((hmin q hqT).lt_of_ne (fun e => hqr (hinj' hr hqT e)))).le
      have hu : 0 ≤ orient p s q := by
        by_cases hqs : q = s
        · subst q
          simp [hO.out]
        rw [(orient_swap_last (orient := orient))]
        exact neg_nonneg.mpr
          (hrot hqT hs ((hmax q hqT).lt_of_ne (fun e => hqs (hinj' hqT hs e)))).le
      have hstrict : orient p r q < orient p s q := by
        by_cases hqr : r = q
        · rw [(orient_swap_last (orient := orient)) p s q]
          have hpos := hrot hqT hs
            ((hmax q hqT).lt_of_ne (fun e => hrs (hqr.trans (hinj' hqT hs e))))
          subst q
          rw [show orient p r r = 0 by simp [hO.out]]
          exact neg_pos.mpr hpos
        exact (hrot hr hqT ((hmin q hqT).lt_of_ne (fun e => hqr (hinj' hr hqT e)))).trans_le hu
      simp only [hO.out] at hstrict
      linarith only [hstrict]
  · exact ⟨0, 0, fun q hq hqp => (hT ⟨q, mem_erase.mpr ⟨hqp, hq⟩⟩).elim⟩

theorem anchorNorm_pos {a b : (ℝ × ℝ)} (h : a ≠ b) : 0 < ((b.1 - a.1)^2 + (b.2 - a.2)^2) := by
  rcases not_and_or.mp (fun e : a.1 = b.1 ∧ a.2 = b.2 => h (Prod.ext e.1 e.2)) with e | e
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm e))) (sq_nonneg _)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm e)))

theorem projected_fst_lt {a b p q : (ℝ × ℝ)} (hab : a ≠ b)
    (hp : 0 < orient a b p) (hq : 0 < orient a b q) :
    (((((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2)) / orient a b p, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2))) / orient a b p) : ℝ × ℝ)).1 < (((((b.1 - a.1) * (q.1 - a.1) + (b.2 - a.2) * (q.2 - a.2)) / orient a b q, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q.1 - a.1) + (b.2 - a.2) * (q.2 - a.2))) / orient a b q) : ℝ × ℝ)).1 ↔ orient p q a < 0 := by
  change ((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2)) / orient a b p < ((b.1 - a.1) * (q.1 - a.1) + (b.2 - a.2) * (q.2 - a.2)) / orient a b q ↔ _
  rw [div_lt_div_iff₀ hp hq, ← sub_neg]
  have he : ((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2)) * orient a b q - ((b.1 - a.1) * (q.1 - a.1) + (b.2 - a.2) * (q.2 - a.2)) * orient a b p =
      ((b.1 - a.1)^2 + (b.2 - a.2)^2) * orient p q a := by
    simp only [hO.out]
    ring
  rw [he]
  constructor
  · intro hn
    exact lt_of_not_ge fun hn' => (not_lt_of_ge (mul_nonneg (anchorNorm_pos hab).le hn')) hn
  · exact mul_neg_of_pos_of_neg (anchorNorm_pos hab)

theorem projected_snd_lt {a b p q : (ℝ × ℝ)} (hab : a ≠ b)
    (hp : 0 < orient a b p) (hq : 0 < orient a b q) :
    (((((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2)) / orient a b p, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2))) / orient a b p) : ℝ × ℝ)).2 < (((((b.1 - a.1) * (q.1 - a.1) + (b.2 - a.2) * (q.2 - a.2)) / orient a b q, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q.1 - a.1) + (b.2 - a.2) * (q.2 - a.2))) / orient a b q) : ℝ × ℝ)).2 ↔ 0 < orient p q b := by
  change (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2))) / orient a b p <
    (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q.1 - a.1) + (b.2 - a.2) * (q.2 - a.2))) / orient a b q ↔ _
  rw [div_lt_div_iff₀ hp hq, ← sub_pos]
  have he : (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q.1 - a.1) + (b.2 - a.2) * (q.2 - a.2))) * orient a b p -
      (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2))) * orient a b q =
      ((b.1 - a.1)^2 + (b.2 - a.2)^2) * orient p q b := by
    simp only [hO.out]
    ring
  rw [he, mul_pos_iff_of_pos_left (anchorNorm_pos hab)]

theorem projected_orientation {a b p q r : (ℝ × ℝ)}
    (hp : 0 < orient a b p) (hq : 0 < orient a b q) (hr : 0 < orient a b r) :
    (orient a b p * orient a b q * orient a b r) *
        orient (((((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2)) / orient a b p, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2))) / orient a b p) : ℝ × ℝ)) (((((b.1 - a.1) * (q.1 - a.1) + (b.2 - a.2) * (q.2 - a.2)) / orient a b q, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q.1 - a.1) + (b.2 - a.2) * (q.2 - a.2))) / orient a b q) : ℝ × ℝ)) (((((b.1 - a.1) * (r.1 - a.1) + (b.2 - a.2) * (r.2 - a.2)) / orient a b r, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (r.1 - a.1) + (b.2 - a.2) * (r.2 - a.2))) / orient a b r) : ℝ × ℝ)) =
      -(((b.1 - a.1)^2 + (b.2 - a.2)^2))^2 * orient p q r := by
  simp only [hO.out] at *
  field_simp [ne_of_gt hp, ne_of_gt hq, ne_of_gt hr]
  ring

section CupsCaps
open scoped Classical

variable {turns : Bool → List (ℝ × ℝ) → Prop}
  [hT : Fact (∀ (up : Bool) (a b c : (ℝ × ℝ)) (l : List (ℝ × ℝ)),
    turns up (a :: b :: c :: l) = ((if up then 0 < orient a b c else orient a b c < 0) ∧ turns up (b :: c :: l)))]
  [hT2 : Fact (∀ (up : Bool) (l : List (ℝ × ℝ)), l.length < 3 → turns up l)]

theorem isSeq_mono {up : Bool} {X Y : Finset (ℝ × ℝ)} {l : List (ℝ × ℝ)}
    (hl : ((∀ x_s ∈ l, x_s ∈ X) ∧ List.Pairwise (fun x_s y_s : ℝ × ℝ => x_s.1 < y_s.1) l ∧ turns up l)) (hXY : X ⊆ Y) : ((∀ x_s ∈ l, x_s ∈ Y) ∧ List.Pairwise (fun x_s y_s : ℝ × ℝ => x_s.1 < y_s.1) l ∧ turns up l) :=
  ⟨fun p hp => hXY (hl.1 p hp), hl.2⟩

theorem tcons {up : Bool} {a b c : ℝ × ℝ} {l : List (ℝ × ℝ)} :
    turns up (a :: b :: c :: l) ↔
      ((if up then 0 < orient a b c else orient a b c < 0) ∧ turns up (b :: c :: l)) :=
  Iff.of_eq (hT.out up a b c l)

theorem tshort {up : Bool} {l : List (ℝ × ℝ)} (h : l.length < 3) : turns up l :=
  hT2.out up l h

theorem turns_append {up : Bool} {a b c : (ℝ × ℝ)} (l : List (ℝ × ℝ))
    (hl : turns up (l ++ [a, b])) (hc : (if up then 0 < orient a b c else orient a b c < 0)) :
    turns up (l ++ [a, b, c]) := by
  induction l with
  | nil => exact (tcons (orient := orient)).2 ⟨hc, tshort (by simp)⟩
  | cons x l ih =>
    cases l with
    | nil =>
      exact (tcons (orient := orient)).2 ⟨((tcons (orient := orient)).1 hl).1, ih (tshort (by simp))⟩
    | cons y l =>
      cases l with
      | nil => exact (tcons (orient := orient)).2 ⟨((tcons (orient := orient)).1 hl).1, ih ((tcons (orient := orient)).1 hl).2⟩
      | cons z l => exact (tcons (orient := orient)).2 ⟨((tcons (orient := orient)).1 hl).1, ih ((tcons (orient := orient)).1 hl).2⟩

theorem isSeq_append {up : Bool} {X : Finset (ℝ × ℝ)} {a b c : (ℝ × ℝ)} {l : List (ℝ × ℝ)}
    (hl : ((∀ x_s ∈ (l ++ [a, b]), x_s ∈ X) ∧ List.Pairwise (fun x_s y_s : ℝ × ℝ => x_s.1 < y_s.1) (l ++ [a, b]) ∧ turns up (l ++ [a, b]))) (hc : c ∈ X) (hbc : b.1 < c.1) (ht : (if up then 0 < orient a b c else orient a b c < 0)) :
    ((∀ x_s ∈ (l ++ [a, b, c]), x_s ∈ X) ∧ List.Pairwise (fun x_s y_s : ℝ × ℝ => x_s.1 < y_s.1) (l ++ [a, b, c]) ∧ turns up (l ++ [a, b, c])) := by
  rw [show l ++ [a, b, c] = (l ++ [a, b]) ++ [c] by simp]
  refine ⟨?_, List.pairwise_append.2 ⟨hl.2.1, by simp, ?_⟩, ?_⟩
  · intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hl.1 p hp
    · simpa using (List.mem_singleton.1 hp ▸ hc)
  · intro p hp q hq
    have hqc := List.mem_singleton.1 hq
    subst q
    rw [show l ++ [a, b] = (l ++ [a]) ++ [b] by simp] at hp
    rcases List.mem_append.1 hp with hp | hp
    · have hsort := hl.2.1
      rw [show l ++ [a,b] = (l ++ [a]) ++ [b] by simp] at hsort
      exact ((List.pairwise_append.1 hsort).2.2 _ hp _ (by simp)).trans hbc
    · simpa [List.mem_singleton.1 hp] using hbc
  · simpa using turns_append l hl.2.2 ht

theorem exists_suffix_two {l : List (ℝ × ℝ)} (h : 2 ≤ l.length) :
    ∃ pre a b, l = pre ++ [a, b] := by
  have hrevlen : 2 ≤ l.reverse.length := by simpa using h
  cases hr : l.reverse with
  | nil => simp [hr] at hrevlen
  | cons b r =>
    cases r with
    | nil => simp [hr] at hrevlen
    | cons a pre =>
      exact ⟨pre.reverse, a, b, by
        simpa [List.reverse_cons, List.append_assoc] using congrArg List.reverse hr⟩

theorem no_shorter_cup_outside (s : ℕ) (X : Finset (ℝ × ℝ)) :
    ¬ (∃ l_h : List (ℝ × ℝ), ((∀ x_s ∈ l_h, x_s ∈ {p ∈ X | ¬ (∃ (pre_e : List (ℝ × ℝ)) (a_e : ℝ × ℝ), ((∀ x_s ∈ (pre_e ++ [a_e, p]), x_s ∈ X) ∧ List.Pairwise (fun x_s y_s : ℝ × ℝ => x_s.1 < y_s.1) (pre_e ++ [a_e, p]) ∧ turns true (pre_e ++ [a_e, p])) ∧ pre_e.length = s)}) ∧ List.Pairwise (fun x_s y_s : ℝ × ℝ => x_s.1 < y_s.1) l_h ∧ turns true l_h) ∧ l_h.length = (s + 2)) := by
  rintro ⟨l, hl, hlen⟩
  obtain ⟨pre, a, p, rfl⟩ := exists_suffix_two (by omega : 2 ≤ l.length)
  have hp := Finset.mem_filter.1 (hl.1 p (by simp))
  have hpre : pre.length = s := by simpa using hlen
  exact hp.2 ⟨pre, a, isSeq_mono hl (Finset.filter_subset _ _), hpre⟩

theorem no_shorter_cap_in_ends (s t : ℕ) (X : Finset (ℝ × ℝ))
    (hgen : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X,
      a.1 < b.1 → b.1 < c.1 → orient a b c ≠ 0)
    (hc : ¬ (∃ l_h : List (ℝ × ℝ), ((∀ x_s ∈ l_h, x_s ∈ X) ∧ List.Pairwise (fun x_s y_s : ℝ × ℝ => x_s.1 < y_s.1) l_h ∧ turns true l_h) ∧ l_h.length = (s + 3))) (hd : ¬ (∃ l_h : List (ℝ × ℝ), ((∀ x_s ∈ l_h, x_s ∈ X) ∧ List.Pairwise (fun x_s y_s : ℝ × ℝ => x_s.1 < y_s.1) l_h ∧ turns false l_h) ∧ l_h.length = (t + 3))) :
    ¬ (∃ l_h : List (ℝ × ℝ), ((∀ x_s ∈ l_h, x_s ∈ {p ∈ X | (∃ (pre_e : List (ℝ × ℝ)) (a_e : ℝ × ℝ), ((∀ x_s ∈ (pre_e ++ [a_e, p]), x_s ∈ X) ∧ List.Pairwise (fun x_s y_s : ℝ × ℝ => x_s.1 < y_s.1) (pre_e ++ [a_e, p]) ∧ turns true (pre_e ++ [a_e, p])) ∧ pre_e.length = s)}) ∧ List.Pairwise (fun x_s y_s : ℝ × ℝ => x_s.1 < y_s.1) l_h ∧ turns false l_h) ∧ l_h.length = (t + 2)) := by
  rintro ⟨l, hl, hlen⟩
  cases l with
  | nil => simp at hlen
  | cons p l =>
    cases l with
    | nil => simp at hlen
    | cons q tail =>
      obtain ⟨hp, pre, a, hcup, hpre⟩ := Finset.mem_filter.1 (hl.1 p (by simp))
      have hq := (Finset.mem_filter.1 (hl.1 q (by simp))).1
      have ha := hcup.1 a (by simp)
      have hap : a.1 < p.1 :=
        (List.pairwise_cons.1 (List.pairwise_append.1 hcup.2.1).2.1).1 p (by simp)
      have hpq : p.1 < q.1 := (List.pairwise_cons.1 hl.2.1).1 q (by simp)
      by_cases hturn : 0 < orient a p q
      · apply hc
        exact ⟨pre ++ [a, p, q],
          isSeq_append hcup hq hpq (by simpa using hturn), by simp [hpre]⟩
      · apply hd
        have hneg : orient a p q < 0 :=
          lt_of_le_of_ne (le_of_not_gt hturn) (hgen a ha p hp q hq hap hpq)
        have hlX := isSeq_mono hl (Finset.filter_subset _ _)
        refine ⟨a :: p :: q :: tail,
          ⟨?_, List.pairwise_cons.2 ⟨?_, hlX.2.1⟩, ?_⟩, ?_⟩
        · intro b hb
          rcases List.mem_cons.1 hb with rfl | hb
          · exact ha
          · exact hlX.1 b hb
        · intro b hb
          rcases List.mem_cons.1 hb with rfl | hb
          · exact hap
          · exact hap.trans ((List.pairwise_cons.1 hlX.2.1).1 _ hb)
        · refine (tcons (orient := orient)).2 ?_
          exact ⟨by simpa using hneg, hlX.2.2⟩
        · simp only [List.length_cons] at hlen ⊢
          omega

theorem hasSeq_two {X : Finset (ℝ × ℝ)}
    (hx : Set.InjOn Prod.fst (X : Set (ℝ × ℝ))) (hX : 1 < X.card) (up : Bool) :
    (∃ l_h : List (ℝ × ℝ), ((∀ x_s ∈ l_h, x_s ∈ X) ∧ List.Pairwise (fun x_s y_s : ℝ × ℝ => x_s.1 < y_s.1) l_h ∧ turns up l_h) ∧ l_h.length = 2) := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hX
  have hne : a.1 ≠ b.1 := fun he => hab (hx ha hb he)
  have hseq {a b : (ℝ × ℝ)} (ha : a ∈ X) (hb : b ∈ X) (hab : a.1 < b.1) :
      (∃ l_h : List (ℝ × ℝ), ((∀ x_s ∈ l_h, x_s ∈ X) ∧ List.Pairwise (fun x_s y_s : ℝ × ℝ => x_s.1 < y_s.1) l_h ∧ turns up l_h) ∧ l_h.length = 2) := by
    refine ⟨[a, b], ⟨?_, ?_, tshort (by simp)⟩, rfl⟩
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ha
      · exact hb
    · simp [hab]
  rcases lt_or_gt_of_ne hne with h | h
  · exact hseq ha hb h
  · exact hseq hb ha h

theorem card_le_binomial (s t : ℕ) (X : Finset (ℝ × ℝ))
    (hx : Set.InjOn Prod.fst (X : Set (ℝ × ℝ)))
    (hgen : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X,
      a.1 < b.1 → b.1 < c.1 → orient a b c ≠ 0)
    (hc : ¬ (∃ l_h : List (ℝ × ℝ), ((∀ x_s ∈ l_h, x_s ∈ X) ∧ List.Pairwise (fun x_s y_s : ℝ × ℝ => x_s.1 < y_s.1) l_h ∧ turns true l_h) ∧ l_h.length = (s + 2))) (hd : ¬ (∃ l_h : List (ℝ × ℝ), ((∀ x_s ∈ l_h, x_s ∈ X) ∧ List.Pairwise (fun x_s y_s : ℝ × ℝ => x_s.1 < y_s.1) l_h ∧ turns false l_h) ∧ l_h.length = (t + 2))) :
    X.card ≤ (s + t).choose s := by
  induction s generalizing t X with
  | zero =>
    simpa using (le_of_not_gt fun h => hc (hasSeq_two hx h true))
  | succ s ih =>
    induction t generalizing X with
    | zero =>
      simpa using (le_of_not_gt fun h => hd (hasSeq_two hx h false))
    | succ t jt =>
      let T := X.filter (fun p => (∃ (pre_e : List (ℝ × ℝ)) (a_e : ℝ × ℝ), ((∀ x_s ∈ (pre_e ++ [a_e, p]), x_s ∈ X) ∧ List.Pairwise (fun x_s y_s : ℝ × ℝ => x_s.1 < y_s.1) (pre_e ++ [a_e, p]) ∧ turns true (pre_e ++ [a_e, p])) ∧ pre_e.length = s))
      let U := X.filter (fun p => ¬ (∃ (pre_e : List (ℝ × ℝ)) (a_e : ℝ × ℝ), ((∀ x_s ∈ (pre_e ++ [a_e, p]), x_s ∈ X) ∧ List.Pairwise (fun x_s y_s : ℝ × ℝ => x_s.1 < y_s.1) (pre_e ++ [a_e, p]) ∧ turns true (pre_e ++ [a_e, p])) ∧ pre_e.length = s))
      have hTX : T ⊆ X := Finset.filter_subset _ _
      have hUX : U ⊆ X := Finset.filter_subset _ _
      have hT : T.card ≤ (s + 1 + t).choose (s + 1) := by
        apply jt T (hx.mono hTX)
        · exact fun a ha b hb c hc hab hbc => hgen a (hTX ha) b (hTX hb) c (hTX hc) hab hbc
        · rintro ⟨l, hl, hlen⟩
          exact hc ⟨l, isSeq_mono hl hTX, hlen⟩
        · exact no_shorter_cap_in_ends s t X hgen hc hd
      have hU : U.card ≤ (s + (t + 1)).choose s := by
        apply ih (t + 1) U (hx.mono hUX)
        · exact fun a ha b hb c hc hab hbc => hgen a (hUX ha) b (hUX hb) c (hUX hc) hab hbc
        · exact no_shorter_cup_outside s X
        · rintro ⟨l, hl, hlen⟩
          exact hd ⟨l, isSeq_mono hl hUX, hlen⟩
      have hpart : T.card + U.card = X.card :=
        Finset.card_filter_add_card_filter_not (fun p => (∃ (pre_e : List (ℝ × ℝ)) (a_e : ℝ × ℝ), ((∀ x_s ∈ (pre_e ++ [a_e, p]), x_s ∈ X) ∧ List.Pairwise (fun x_s y_s : ℝ × ℝ => x_s.1 < y_s.1) (pre_e ++ [a_e, p]) ∧ turns true (pre_e ++ [a_e, p])) ∧ pre_e.length = s))
      have hchoose :
          ((s + 1) + (t + 1)).choose (s + 1) =
            (s + (t + 1)).choose s + (s + 1 + t).choose (s + 1) := by
        rw [show (s + 1) + (t + 1) = (s + (t + 1)) + 1 by omega,
          Nat.choose_succ_succ', show s + (t + 1) = s + 1 + t by omega]
      rw [hchoose, ← hpart]
      exact (Nat.add_le_add hT hU).trans_eq (Nat.add_comm _ _)

theorem turn_iff_signed (up : Bool) (a b c : (ℝ × ℝ)) :
    (if up then 0 < orient a b c else orient a b c < 0) ↔ 0 < ((if up then (1 : ℝ) else -1) * orient a b c) := by
  cases up <;> simp

theorem turn_quad {up : Bool} {a b c d : (ℝ × ℝ)}
    (hab : a.1 < b.1) (hbc : b.1 < c.1) (hcd : c.1 < d.1)
    (h₁ : (if up then 0 < orient a b c else orient a b c < 0)) (h₂ : (if up then 0 < orient b c d else orient b c d < 0)) :
    (if up then 0 < orient a b d else orient a b d < 0) ∧ (if up then 0 < orient a c d else orient a c d < 0) := by
  rw [turn_iff_signed] at h₁ h₂
  simp only [turn_iff_signed]
  have hleft :
      (c.1 - b.1) * ((if up then (1 : ℝ) else -1) * orient a b d) =
        (d.1 - b.1) * ((if up then (1 : ℝ) else -1) * orient a b c) + (b.1 - a.1) * ((if up then (1 : ℝ) else -1) * orient b c d) := by
    simp only [hO.out]
    ring
  have hright :
      (c.1 - b.1) * ((if up then (1 : ℝ) else -1) * orient a c d) =
        (c.1 - a.1) * ((if up then (1 : ℝ) else -1) * orient b c d) + (d.1 - c.1) * ((if up then (1 : ℝ) else -1) * orient a b c) := by
    simp only [hO.out]
    ring
  constructor
  · apply (mul_pos_iff_of_pos_left (sub_pos.mpr hbc)).mp
    rw [hleft]
    exact add_pos (mul_pos (sub_pos.mpr (hbc.trans hcd)) h₁) (mul_pos (sub_pos.mpr hab) h₂)
  · apply (mul_pos_iff_of_pos_left (sub_pos.mpr hbc)).mp
    rw [hright]
    exact add_pos (mul_pos (sub_pos.mpr (hab.trans hbc)) h₂) (mul_pos (sub_pos.mpr hcd) h₁)

include hT hT2 in
theorem turns_tail {up : Bool} {a : (ℝ × ℝ)} {l : List (ℝ × ℝ)}
    (h : turns up (a :: l)) : turns up l := by
  rcases l with _ | ⟨b, _ | ⟨c, l⟩⟩
  · exact tshort (by simp)
  · exact tshort (by simp)
  · exact ((tcons (orient := orient)).1 h).2

theorem x_lt_next {a b : (ℝ × ℝ)} {l : List (ℝ × ℝ)}
    (h : (a :: b :: l).Pairwise (fun p q => p.1 < q.1)) : a.1 < b.1 :=
  (List.pairwise_cons.1 h).1 b (by simp)

include hT hT2 in
theorem turns_delete {up : Bool} {p : (ℝ × ℝ)} {l : List (ℝ × ℝ)} (pre : List (ℝ × ℝ))
    (hs : (pre ++ p :: l).Pairwise (fun a b => a.1 < b.1))
    (ht : turns up (pre ++ p :: l)) : turns up (pre ++ l) := by
  induction pre with
  | nil => exact turns_tail (orient := orient) ht
  | cons a pre ih =>
    cases pre with
    | nil =>
      rcases l with _ | ⟨b, _ | ⟨c, l⟩⟩
      · exact tshort (by simp)
      · exact tshort (by simp)
      · have hs' : (a :: p :: b :: c :: l).Pairwise (fun u v => u.1 < v.1) := hs
        have ht0 : turns up (a :: p :: b :: c :: l) := ht
        have ht' := (tcons (orient := orient)).1 ht0
        have ht'' := (tcons (orient := orient)).1 ht'.2
        have hp := turn_quad (x_lt_next hs') (x_lt_next hs'.tail)
          (x_lt_next hs'.tail.tail) ht'.1 ht''.1
        exact (tcons (orient := orient)).2 ⟨hp.2, ht''.2⟩
    | cons b pre =>
      cases pre with
      | nil =>
        cases l with
        | nil => exact tshort (by simp)
        | cons c l =>
          have hs' : (a :: b :: p :: c :: l).Pairwise (fun u v => u.1 < v.1) := hs
          have ht0 : turns up (a :: b :: p :: c :: l) := ht
          have ht' := (tcons (orient := orient)).1 ht0
          have ht'' := (tcons (orient := orient)).1 ht'.2
          have hp := turn_quad (x_lt_next hs') (x_lt_next hs'.tail)
            (x_lt_next hs'.tail.tail) ht'.1 ht''.1
          exact (tcons (orient := orient)).2 ⟨hp.1, ih hs'.tail ht'.2⟩
      | cons c pre =>
        have ht0 : turns up (a :: b :: c :: (pre ++ p :: l)) := ht
        have ht' := (tcons (orient := orient)).1 ht0
        exact (tcons (orient := orient)).2 ⟨ht'.1, ih hs.tail ht'.2⟩

include hT hT2 in
theorem turns_sublist_append {up : Bool} {l₁ l₂ : List (ℝ × ℝ)} (h : List.Sublist l₁ l₂)
    (pre : List (ℝ × ℝ)) (hs : (pre ++ l₂).Pairwise (fun a b => a.1 < b.1))
    (ht : turns up (pre ++ l₂)) : turns up (pre ++ l₁) := by
  induction h generalizing pre with
  | slnil => exact ht
  | cons a h ih =>
    apply ih pre
    · apply List.Pairwise.sublist _ hs
      exact (List.Sublist.refl _).append (List.Sublist.cons _ (List.Sublist.refl _))
    · exact turns_delete (orient := orient) pre hs ht
  | cons_cons a h ih =>
    simpa only [List.append_assoc, List.singleton_append] using
      ih (pre ++ [a]) (by simpa only [List.append_assoc, List.singleton_append] using hs)
        (by simpa only [List.append_assoc, List.singleton_append] using ht)

theorem turn_of_mem {up : Bool} {X : Finset (ℝ × ℝ)} {l : List (ℝ × ℝ)}
    (h : ((∀ x_s ∈ l, x_s ∈ X) ∧ List.Pairwise (fun x_s y_s : ℝ × ℝ => x_s.1 < y_s.1) l ∧ turns up l)) {a b c : (ℝ × ℝ)} (ha : a ∈ l) (hb : b ∈ l) (hc : c ∈ l)
    (hab : a.1 < b.1) (hbc : b.1 < c.1) : (if up then 0 < orient a b c else orient a b c < 0) := by
  let r : (ℝ × ℝ) → (ℝ × ℝ) → Prop := fun a b => a.1 < b.1
  let : Std.Antisymm r := ⟨fun _ _ h₁ h₂ => (lt_asymm h₁ h₂).elim⟩
  let : Std.Irrefl r := ⟨fun _ => lt_irrefl _⟩
  have htri : [a, b, c].Pairwise r := by simp [r, hab, hbc, hab.trans hbc]
  have hsub : [a, b, c] ⊆ l := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  have hsublist : List.Sublist [a, b, c] l :=
    List.sublist_of_subperm_of_pairwise (List.subperm_of_subset htri.nodup hsub) htri h.2.1
  have hh := turns_sublist_append (orient := orient) hsublist [] h.2.1 h.2.2
  exact ((tcons (orient := orient)).1 hh).1

include hT hT2 in
theorem cups_caps_core (s t : ℕ) (X : Finset (ℝ × ℝ)) (hX : (Set.InjOn Prod.fst (X : Set (ℝ × ℝ)) ∧ ∀ a_g ∈ X, ∀ b_g ∈ X, ∀ c_g ∈ X, a_g.1 < b_g.1 → b_g.1 < c_g.1 → orient a_g b_g c_g ≠ 0))
    (hcard : (s + t).choose s < X.card) :
    (∃ Y ⊆ X, Y.card = s + 2 ∧ Set.InjOn Prod.fst (Y : Set (ℝ × ℝ)) ∧
        ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, a.1 < b.1 → b.1 < c.1 → 0 < orient a b c) ∨
    (∃ Y ⊆ X, Y.card = t + 2 ∧ Set.InjOn Prod.fst (Y : Set (ℝ × ℝ)) ∧
        ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, a.1 < b.1 → b.1 < c.1 → orient a b c < 0) := by
  have key : ∀ (up : Bool) (k : ℕ), (∃ l_h : List (ℝ × ℝ), ((∀ x_s ∈ l_h, x_s ∈ X) ∧ List.Pairwise (fun x_s y_s : ℝ × ℝ => x_s.1 < y_s.1) l_h ∧ turns up l_h) ∧ l_h.length = k) →
      ∃ Y ⊆ X, Y.card = k ∧ Set.InjOn Prod.fst (Y : Set (ℝ × ℝ)) ∧
        ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, a.1 < b.1 → b.1 < c.1 → (if up then 0 < orient a b c else orient a b c < 0) := by
    rintro up k ⟨l, hl, hlen⟩
    have hnodup : l.Nodup := by
      apply hl.2.1.imp
      intro a b hab he
      subst b
      exact (lt_irrefl _) hab
    have hsub : l.toFinset ⊆ X := fun p hp => hl.1 p (List.mem_toFinset.1 hp)
    refine ⟨l.toFinset, hsub, (List.toFinset_card_of_nodup hnodup).trans hlen,
      hX.1.mono (Finset.coe_subset.mpr hsub), ?_⟩
    intro a ha b hb c hc hab hbc
    exact turn_of_mem hl (List.mem_toFinset.1 ha) (List.mem_toFinset.1 hb)
      (List.mem_toFinset.1 hc) hab hbc
  by_contra hcon
  rw [not_or] at hcon
  have h1 : ¬ (∃ l_h : List (ℝ × ℝ), ((∀ x_s ∈ l_h, x_s ∈ X) ∧ List.Pairwise (fun x_s y_s : ℝ × ℝ => x_s.1 < y_s.1) l_h ∧ turns true l_h) ∧ l_h.length = (s + 2)) := fun h => hcon.1 (by
    obtain ⟨Y, hYX, hYc, hYi, hYt⟩ := key true _ h
    exact ⟨Y, hYX, hYc, hYi, fun a ha b hb c hc hab hbc => by
      simpa using hYt a ha b hb c hc hab hbc⟩)
  have h2 : ¬ (∃ l_h : List (ℝ × ℝ), ((∀ x_s ∈ l_h, x_s ∈ X) ∧ List.Pairwise (fun x_s y_s : ℝ × ℝ => x_s.1 < y_s.1) l_h ∧ turns false l_h) ∧ l_h.length = (t + 2)) := fun h => hcon.2 (by
    obtain ⟨Y, hYX, hYc, hYi, hYt⟩ := key false _ h
    exact ⟨Y, hYX, hYc, hYi, fun a ha b hb c hc hab hbc => by
      simpa using hYt a ha b hb c hc hab hbc⟩)
  exact absurd (card_le_binomial s t X hX.1 hX.2 h1 h2) (not_le.mpr hcard)

end CupsCaps

theorem cups_caps_planar (s t : ℕ) (X : Finset (ℝ × ℝ)) (hX : (Set.InjOn Prod.fst (X : Set (ℝ × ℝ)) ∧ ∀ a_g ∈ X, ∀ b_g ∈ X, ∀ c_g ∈ X, a_g.1 < b_g.1 → b_g.1 < c_g.1 → orient a_g b_g c_g ≠ 0))
    (hcard : (s + t).choose s < X.card) :
    (∃ Y ⊆ X, Y.card = s + 2 ∧ Set.InjOn Prod.fst (Y : Set (ℝ × ℝ)) ∧
        ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, a.1 < b.1 → b.1 < c.1 → 0 < orient a b c) ∨
    (∃ Y ⊆ X, Y.card = t + 2 ∧ Set.InjOn Prod.fst (Y : Set (ℝ × ℝ)) ∧
        ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, a.1 < b.1 → b.1 < c.1 → orient a b c < 0) :=
  cups_caps_core (turns := fun up l => ∀ i (h : i + 2 < l.length), (if up then 0 < orient l[i] l[i + 1] l[i + 2] else orient l[i] l[i + 1] l[i + 2] < 0))
    (hT := ⟨fun up a b c l => propext ⟨fun h => ⟨h 0 (by simp),
      fun i hi => h (i + 1) (by simp at hi ⊢; omega)⟩,
      fun ⟨h0, h⟩ i hi => by
        cases i with
        | zero => exact h0
        | succ i => exact h i (by simp at hi ⊢; omega)⟩⟩)
    (hT2 := ⟨fun up l hl i hi => by omega⟩) s t X hX hcard

theorem orient_ne_of_distinct {X : Finset (ℝ × ℝ)} (hX : (Set.InjOn Prod.fst (X : Set (ℝ × ℝ)) ∧ ∀ a_g ∈ X, ∀ b_g ∈ X, ∀ c_g ∈ X, a_g.1 < b_g.1 → b_g.1 < c_g.1 → orient a_g b_g c_g ≠ 0))
    {a b c : (ℝ × ℝ)} (ha : a ∈ X) (hb : b ∈ X) (hc : c ∈ X)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) : orient a b c ≠ 0 := by
  intro he
  have hcab := ((orient_cycle (orient := orient)) c a b).trans he
  have hbca := ((orient_cycle (orient := orient)) a b c).symm.trans he
  have hbac : orient b a c = 0 := by rw [(orient_flip (orient := orient)) b a c, he, neg_zero]
  have hacb : orient a c b = 0 := by rw [(orient_swap_last (orient := orient)) a c b, he, neg_zero]
  have hcba : orient c b a = 0 := by rw [(orient_reverse (orient := orient)) c b a, he, neg_zero]
  have habx : a.1 ≠ b.1 := fun e => hab (hX.1 ha hb e)
  have hbcx : b.1 ≠ c.1 := fun e => hbc (hX.1 hb hc e)
  have hacx : a.1 ≠ c.1 := fun e => hac (hX.1 ha hc e)
  rcases lt_or_gt_of_ne habx with h₁ | h₁ <;>
    rcases lt_or_gt_of_ne hbcx with h₂ | h₂ <;>
    rcases lt_or_gt_of_ne hacx with h₃ | h₃
  all_goals first
    | exact hX.2 a ha b hb c hc h₁ h₂ he
    | exact hX.2 a ha c hc b hb h₃ h₂ hacb
    | exact hX.2 b hb a ha c hc h₁ h₃ hbac
    | exact hX.2 b hb c hc a ha h₂ h₃ hbca
    | exact hX.2 c hc a ha b hb h₃ h₁ hcab
    | exact hX.2 c hc b hb a ha h₂ h₁ hcba

theorem projected_fst_injOn {a b : (ℝ × ℝ)} {X : Finset (ℝ × ℝ)} (hab : a ≠ b)
    (hpos : ∀ p ∈ X, 0 < orient a b p)
    (ha : ∀ p ∈ X, ∀ q ∈ X, p ≠ q → orient p q a ≠ 0) :
    Set.InjOn (fun p => (((((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2)) / orient a b p, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2))) / orient a b p) : ℝ × ℝ)).1) (X : Set (ℝ × ℝ)) := by
  intro p hp q hq he
  by_contra hne
  rcases lt_or_gt_of_ne (ha p hp q hq hne) with h | h
  · exact (ne_of_lt ((projected_fst_lt hab (hpos p hp) (hpos q hq)).2 h)) he
  · rw [(orient_flip (orient := orient)) p q a] at h
    exact (ne_of_lt ((projected_fst_lt hab (hpos q hq) (hpos p hp)).2 (neg_pos.mp h))) he.symm

theorem projected_snd_ne_of_ne {a b p q : (ℝ × ℝ)} (hab : a ≠ b)
    (hp : 0 < orient a b p) (hq : 0 < orient a b q) (h : orient p q b ≠ 0) :
    (((((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2)) / orient a b p, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2))) / orient a b p) : ℝ × ℝ)).2 ≠ (((((b.1 - a.1) * (q.1 - a.1) + (b.2 - a.2) * (q.2 - a.2)) / orient a b q, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q.1 - a.1) + (b.2 - a.2) * (q.2 - a.2))) / orient a b q) : ℝ × ℝ)).2 := by
  rcases lt_or_gt_of_ne h with h | h
  · rw [(orient_flip (orient := orient)) p q b] at h
    exact (ne_of_lt ((projected_snd_lt hab hq hp).2 (neg_lt_zero.mp h))).symm
  · exact ne_of_lt ((projected_snd_lt hab hp hq).2 h)

theorem projected_image_general {a b : (ℝ × ℝ)} {X : Finset (ℝ × ℝ)}
    (hab : a ≠ b) (hpos : ∀ p ∈ X, 0 < orient a b p)
    (ha : ∀ p ∈ X, ∀ q ∈ X, p ≠ q → orient p q a ≠ 0)
    (hX : ∀ p ∈ X, ∀ q ∈ X, ∀ r ∈ X, p ≠ q → q ≠ r → p ≠ r → orient p q r ≠ 0) :
    (Set.InjOn Prod.fst ((X.image (fun p => ((((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2)) / orient a b p, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2))) / orient a b p) : ℝ × ℝ))) : Set (ℝ × ℝ)) ∧ ∀ a_g ∈ (X.image (fun p => ((((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2)) / orient a b p, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2))) / orient a b p) : ℝ × ℝ))), ∀ b_g ∈ (X.image (fun p => ((((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2)) / orient a b p, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2))) / orient a b p) : ℝ × ℝ))), ∀ c_g ∈ (X.image (fun p => ((((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2)) / orient a b p, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2))) / orient a b p) : ℝ × ℝ))), a_g.1 < b_g.1 → b_g.1 < c_g.1 → orient a_g b_g c_g ≠ 0) := by
  refine ⟨?_, ?_⟩
  · intro p hp q hq he
    obtain ⟨p₀, hp₀, rfl⟩ := mem_image.mp hp
    obtain ⟨q₀, hq₀, rfl⟩ := mem_image.mp hq
    obtain rfl := projected_fst_injOn hab hpos ha hp₀ hq₀ he
    rfl
  · intro p hp q hq r hr hpq hqr he
    obtain ⟨p₀, hp₀, rfl⟩ := mem_image.mp hp
    obtain ⟨q₀, hq₀, rfl⟩ := mem_image.mp hq
    obtain ⟨r₀, hr₀, rfl⟩ := mem_image.mp hr
    have hn := hX p₀ hp₀ q₀ hq₀ r₀ hr₀
      (fun e => hpq.ne (congrArg (fun p => (((((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2)) / orient a b p, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2))) / orient a b p) : ℝ × ℝ)).1) e))
      (fun e => hqr.ne (congrArg (fun p => (((((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2)) / orient a b p, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2))) / orient a b p) : ℝ × ℝ)).1) e))
      (fun e => (hpq.trans hqr).ne (congrArg (fun p => (((((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2)) / orient a b p, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2))) / orient a b p) : ℝ × ℝ)).1) e))
    have he' := projected_orientation (hpos p₀ hp₀) (hpos q₀ hq₀) (hpos r₀ hr₀)
    rw [he, mul_zero] at he'
    exact (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ (anchorNorm_pos hab).ne')) hn) he'.symm

theorem projected_turn {a b p q r : (ℝ × ℝ)} (hab : a ≠ b)
    (hp : 0 < orient a b p) (hq : 0 < orient a b q) (hr : 0 < orient a b r) :
    (0 < orient (((((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2)) / orient a b p, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2))) / orient a b p) : ℝ × ℝ)) (((((b.1 - a.1) * (q.1 - a.1) + (b.2 - a.2) * (q.2 - a.2)) / orient a b q, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q.1 - a.1) + (b.2 - a.2) * (q.2 - a.2))) / orient a b q) : ℝ × ℝ)) (((((b.1 - a.1) * (r.1 - a.1) + (b.2 - a.2) * (r.2 - a.2)) / orient a b r, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (r.1 - a.1) + (b.2 - a.2) * (r.2 - a.2))) / orient a b r) : ℝ × ℝ)) ↔ orient p q r < 0) ∧
    (orient (((((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2)) / orient a b p, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2))) / orient a b p) : ℝ × ℝ)) (((((b.1 - a.1) * (q.1 - a.1) + (b.2 - a.2) * (q.2 - a.2)) / orient a b q, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q.1 - a.1) + (b.2 - a.2) * (q.2 - a.2))) / orient a b q) : ℝ × ℝ)) (((((b.1 - a.1) * (r.1 - a.1) + (b.2 - a.2) * (r.2 - a.2)) / orient a b r, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (r.1 - a.1) + (b.2 - a.2) * (r.2 - a.2))) / orient a b r) : ℝ × ℝ)) < 0 ↔ 0 < orient p q r) := by
  have he := projected_orientation hp hq hr
  have hd : 0 < orient a b p * orient a b q * orient a b r := by positivity
  have hm : 0 < (((b.1 - a.1)^2 + (b.2 - a.2)^2))^2 := pow_pos (anchorNorm_pos hab) _
  constructor
  · rw [← mul_pos_iff_of_pos_left hd, he, neg_mul, neg_pos, mul_comm]
    constructor
    · intro hn
      exact lt_of_not_ge fun hn' => (not_lt_of_ge (mul_nonneg hn' hm.le)) hn
    · exact fun h => mul_neg_of_neg_of_pos h hm
  · have fac (x y : ℝ) (hx : 0 < x) : x * y < 0 ↔ y < 0 := by
      exact ⟨fun h => lt_of_not_ge fun h' => (not_lt_of_ge (mul_nonneg hx.le h')) h,
        mul_neg_of_pos_of_neg hx⟩
    rw [← fac _ _ hd, he, neg_mul, neg_lt_zero, mul_pos_iff_of_pos_left hm]

theorem orient_angular_interval {a p u v r : (ℝ × ℝ)}
    (huv : orient a u v < 0) (hup : orient a u p < 0) (hpv : orient a p v < 0) :
    (orient a u r < 0 → orient a v r < 0 → orient a p r < 0) ∧
    (0 < orient a u r → 0 < orient a v r → 0 < orient a p r) := by
  have he : orient a u v * orient a p r =
      orient a p v * orient a u r + orient a u p * orient a v r := by
    simp only [hO.out]
    ring
  constructor
  · intro hur hvr
    have h := add_pos (mul_pos_of_neg_of_neg hpv hur) (mul_pos_of_neg_of_neg hup hvr)
    rw [← he] at h
    exact lt_of_not_ge fun hh => (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg huv.le hh)) h
  · intro hur hvr
    have h := add_neg (mul_neg_of_neg_of_pos hpv hur) (mul_neg_of_neg_of_pos hup hvr)
    rw [← he] at h
    exact lt_of_not_ge fun hh => (not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos huv.le hh)) h

theorem chain_or_antichain {α : Type*} (S : Finset α) (R : α → α → Prop)
    (hir : ∀ x, ¬ R x x) (ht : ∀ {x y z}, R x y → R y z → R x z)
    {a b : ℕ} (ha : 0 < a) (hsize : a * b < S.card) :
    (∃ C ⊆ S, a ≤ C.card ∧ IsChain R (C : Set α)) ∨
      ∃ A ⊆ S, b < A.card ∧ IsAntichain R (A : Set α) := by
  classical
  by_cases hc : ∃ C ⊆ S, a ≤ C.card ∧ IsChain R (C : Set α)
  · exact Or.inl hc
  right
  let below (p : α) := S.powerset.filter fun (C : Finset α) =>
    IsChain R (C : Set α) ∧ ∀ q ∈ C, R q p
  let rank (p : α) := (below p).sup Finset.card
  have extend {C : Finset α} {p : α} (hC : C ∈ below p) (hp : p ∈ S) :
      insert p C ⊆ S ∧ IsChain R ((insert p C : Finset α) : Set α) ∧
        (insert p C).card = C.card + 1 := by
    obtain ⟨hCS, hchain, hrel⟩ := mem_filter.mp hC
    have hpn : p ∉ C := fun h => hir p (hrel p h)
    refine ⟨insert_subset hp (mem_powerset.mp hCS), ?_, card_insert_of_notMem hpn⟩
    rw [coe_insert]
    exact hchain.insert (fun q hq _ => Or.inr (hrel q hq))
  have hlt p (hp : p ∈ S) : rank p < a := by
    change (below p).sup Finset.card < a
    apply (Finset.sup_lt_iff ha).mpr
    intro C hC
    obtain ⟨hsub, hchain, hcard⟩ := extend hC hp
    have hbound : ¬ a ≤ (insert p C).card := fun hle =>
      hc ⟨insert p C, hsub, hle, hchain⟩
    omega
  have hrank {p q} (hp : p ∈ S) (hpq : R p q) : rank p < rank q := by
    have hne : (below p).Nonempty := ⟨∅, by simp [below]⟩
    obtain ⟨C, hC, he⟩ := Finset.exists_mem_eq_sup (below p) hne Finset.card
    obtain ⟨hsub, hchain, hcard⟩ := extend hC hp
    have hm : insert p C ∈ below q := by
      refine mem_filter.mpr ⟨mem_powerset.mpr hsub, hchain, ?_⟩
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact hpq
      · exact ht ((mem_filter.mp hC).2.2 x hx) hpq
    have hbnd : (insert p C).card ≤ rank q := Finset.le_sup hm
    change rank p = C.card at he
    omega
  obtain ⟨j, -, hj⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := S) (t := Finset.range a) (f := rank)
    (fun p hp => mem_range.mpr (hlt p hp)) (by simpa using hsize)
  refine ⟨S.filter (fun p => rank p = j), filter_subset _ _, hj, ?_⟩
  intro p hp q hq _ hpq
  obtain ⟨hpS, hpj⟩ := mem_filter.mp hp
  obtain ⟨_, hqj⟩ := mem_filter.mp hq
  exact (hrank hpS hpq).ne (hpj.trans hqj.symm)

theorem convex_of_clockwise_blocks {X : Finset (ℝ × ℝ)}
    {tag : (ℝ × ℝ) → ℕ} {key : (ℝ × ℝ) → ℝ}
    (hinj : Set.InjOn (fun p => toLex (tag p, key p)) (X : Set (ℝ × ℝ)))
    (hone : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, tag a = tag b → tag b = tag c →
      key a < key b → key b < key c → orient a b c < 0)
    (htwo : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, tag a = tag b → tag a ≠ tag c →
      key a < key b → orient a b c < 0)
    (hthree : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, tag a < tag b → tag b < tag c →
      orient a b c < 0) :
    (∀ p_c ∈ X, ∃ u_c v_c : ℝ, ∀ q_c ∈ X, q_c ≠ p_c → u_c * p_c.1 + v_c * p_c.2 < u_c * q_c.1 + v_c * q_c.2) := by
  refine convex_of_clockwise (orient := orient) hinj (fun a ha b hb c hc hab hbc => ?_)
  obtain ⟨hab, hkab⟩ := Prod.Lex.toLex_lt_toLex'.mp hab
  obtain ⟨hbc, hkbc⟩ := Prod.Lex.toLex_lt_toLex'.mp hbc
  rcases hab.eq_or_lt with hab | hab <;> rcases hbc.eq_or_lt with hbc | hbc
  · exact hone a ha b hb c hc hab hbc (hkab hab) (hkbc hbc)
  · exact htwo a ha b hb c hc hab ((hab.le.trans_lt hbc).ne) (hkab hab)
  · rw [(orient_cycle (orient := orient))]
    exact htwo b hb c hc a ha hbc hab.ne' (hkbc hbc)
  · exact hthree a ha b hb c hc hab hbc

theorem convex_of_clockwise_union {B C : Finset (ℝ × ℝ)} (hdisj : Disjoint B C)
    {keyB keyC : (ℝ × ℝ) → ℝ}
    (hBi : Set.InjOn keyB (B : Set (ℝ × ℝ))) (hCi : Set.InjOn keyC (C : Set (ℝ × ℝ)))
    (hB : ∀ p ∈ B, ∀ q ∈ B, ∀ r ∈ B, keyB p < keyB q → keyB q < keyB r →
      orient p q r < 0)
    (hC : ∀ p ∈ C, ∀ q ∈ C, ∀ r ∈ C, keyC p < keyC q → keyC q < keyC r →
      orient p q r < 0)
    (hBC : ∀ p ∈ B, ∀ q ∈ B, ∀ r ∈ C, keyB p < keyB q → orient p q r < 0)
    (hCB : ∀ p ∈ C, ∀ q ∈ C, ∀ r ∈ B, keyC p < keyC q → orient p q r < 0) :
    (∀ p_c ∈ (B ∪ C), ∃ u_c v_c : ℝ, ∀ q_c ∈ (B ∪ C), q_c ≠ p_c → u_c * p_c.1 + v_c * p_c.2 < u_c * q_c.1 + v_c * q_c.2) := by
  classical
  let tag (p : (ℝ × ℝ)) : ℕ := if p ∈ B then 0 else 1
  let key (p : (ℝ × ℝ)) : ℝ := if p ∈ B then keyB p else keyC p
  have hzero {p : (ℝ × ℝ)} (hp : p ∈ B) : tag p = 0 ∧ key p = keyB p := by simp [tag, key, hp]
  have hone {p : (ℝ × ℝ)} (hp : p ∈ C) : tag p = 1 ∧ key p = keyC p := by
    have hnot : p ∉ B := fun h => Finset.disjoint_left.mp hdisj h hp
    simp [tag, key, hnot]
  have hcase (p : (ℝ × ℝ)) (hp : p ∈ B ∪ C) :
      (p ∈ B ∧ tag p = 0 ∧ key p = keyB p) ∨
      (p ∈ C ∧ tag p = 1 ∧ key p = keyC p) := by
    rcases mem_union.mp hp with hp | hp
    · exact Or.inl ⟨hp, hzero hp⟩
    · exact Or.inr ⟨hp, hone hp⟩
  refine convex_of_clockwise_blocks (orient := orient) (tag := tag) (key := key) ?_ ?_ ?_ ?_
  · intro p hp q hq he
    have he' := congrArg ofLex he
    have ht : tag p = tag q := congrArg Prod.fst he'
    have hk : key p = key q := congrArg Prod.snd he'
    rcases hcase p hp with ⟨hp, htp, hkp⟩ | ⟨hp, htp, hkp⟩ <;>
      rcases hcase q hq with ⟨hq, htq, hkq⟩ | ⟨hq, htq, hkq⟩ <;>
      rw [htp, htq] at ht <;> try contradiction
    · exact hBi hp hq (by simpa [hkp, hkq] using hk)
    · exact hCi hp hq (by simpa [hkp, hkq] using hk)
  · intro a ha b hb c hc hab hbc hka hkb
    rcases hcase a ha with ⟨ha, hta, hxa⟩ | ⟨ha, hta, hxa⟩ <;>
      rcases hcase b hb with ⟨hb, htb, hxb⟩ | ⟨hb, htb, hxb⟩ <;>
      rcases hcase c hc with ⟨hc, htc, hxc⟩ | ⟨hc, htc, hxc⟩ <;>
      rw [hta, htb] at hab <;> rw [htb, htc] at hbc <;> try contradiction
    · exact hB a ha b hb c hc (by simpa [hxa, hxb] using hka) (by simpa [hxb, hxc] using hkb)
    · exact hC a ha b hb c hc (by simpa [hxa, hxb] using hka) (by simpa [hxb, hxc] using hkb)
  · intro a ha b hb c hc hab hac hk
    rcases hcase a ha with ⟨ha, hta, hxa⟩ | ⟨ha, hta, hxa⟩ <;>
      rcases hcase b hb with ⟨hb, htb, hxb⟩ | ⟨hb, htb, hxb⟩ <;>
      rcases hcase c hc with ⟨hc, htc, hxc⟩ | ⟨hc, htc, hxc⟩ <;>
      rw [hta, htb] at hab <;> rw [hta, htc] at hac <;> try contradiction
    · exact hBC a ha b hb c hc (by simpa [hxa, hxb] using hk)
    · exact hCB a ha b hb c hc (by simpa [hxa, hxb] using hk)
  · intro a ha b hb c hc hab hbc
    rcases hcase a ha with ⟨_, hta, _⟩ | ⟨_, hta, _⟩ <;>
      rcases hcase b hb with ⟨_, htb, _⟩ | ⟨_, htb, _⟩ <;>
      rcases hcase c hc with ⟨_, htc, _⟩ | ⟨_, htc, _⟩ <;>
      rw [hta, htb] at hab <;> rw [htb, htc] at hbc <;> omega

theorem pocket_mono {a b : (ℝ × ℝ)} {B C : Finset (ℝ × ℝ)}
    (hB : (a ≠ b ∧ (∀ p_k ∈ B, 0 < orient a b p_k) ∧ (∀ p_k ∈ B, ∀ q_k ∈ B, p_k ≠ q_k → orient p_k q_k a ≠ 0) ∧ (∀ p_k ∈ B, ∀ q_k ∈ B, p_k ≠ q_k → orient p_k q_k b ≠ 0) ∧ (∀ p_k ∈ B, ∀ q_k ∈ B, ∀ r_k ∈ B, p_k ≠ q_k → q_k ≠ r_k → p_k ≠ r_k → orient p_k q_k r_k ≠ 0))) (hCB : C ⊆ B) : (a ≠ b ∧ (∀ p_k ∈ C, 0 < orient a b p_k) ∧ (∀ p_k ∈ C, ∀ q_k ∈ C, p_k ≠ q_k → orient p_k q_k a ≠ 0) ∧ (∀ p_k ∈ C, ∀ q_k ∈ C, p_k ≠ q_k → orient p_k q_k b ≠ 0) ∧ (∀ p_k ∈ C, ∀ q_k ∈ C, ∀ r_k ∈ C, p_k ≠ q_k → q_k ≠ r_k → p_k ≠ r_k → orient p_k q_k r_k ≠ 0)) :=
  ⟨hB.1, fun p hp => hB.2.1 p (hCB hp),
    fun p hp q hq => hB.2.2.1 p (hCB hp) q (hCB hq),
    fun p hp q hq => hB.2.2.2.1 p (hCB hp) q (hCB hq),
    fun p hp q hq r hr => hB.2.2.2.2 p (hCB hp) q (hCB hq) r (hCB hr)⟩

theorem pocket_of_general {a b : (ℝ × ℝ)} {B X : Finset (ℝ × ℝ)}
    (hX : (Set.InjOn Prod.fst (X : Set (ℝ × ℝ)) ∧ ∀ a_g ∈ X, ∀ b_g ∈ X, ∀ c_g ∈ X, a_g.1 < b_g.1 → b_g.1 < c_g.1 → orient a_g b_g c_g ≠ 0)) (hBX : B ⊆ X) (ha : a ∈ X) (hb : b ∈ X) (hab : a ≠ b)
    (hside : ∀ p ∈ B, 0 < orient a b p) : (a ≠ b ∧ (∀ p_k ∈ B, 0 < orient a b p_k) ∧ (∀ p_k ∈ B, ∀ q_k ∈ B, p_k ≠ q_k → orient p_k q_k a ≠ 0) ∧ (∀ p_k ∈ B, ∀ q_k ∈ B, p_k ≠ q_k → orient p_k q_k b ≠ 0) ∧ (∀ p_k ∈ B, ∀ q_k ∈ B, ∀ r_k ∈ B, p_k ≠ q_k → q_k ≠ r_k → p_k ≠ r_k → orient p_k q_k r_k ≠ 0)) := by
  have hne {p : (ℝ × ℝ)} (hp : p ∈ B) : p ≠ a ∧ p ≠ b := by
    constructor <;> rintro rfl <;> have ht := hside _ hp <;> simp only [hO.out] at ht <;> nlinarith only [ht]
  exact ⟨hab, hside,
    fun p hp q hq hpq => orient_ne_of_distinct hX (hBX hp) (hBX hq) ha hpq
      (hne hq).1 (hne hp).1,
    fun p hp q hq hpq => orient_ne_of_distinct hX (hBX hp) (hBX hq) hb hpq
      (hne hq).2 (hne hp).2,
    fun p hp q hq r hr => orient_ne_of_distinct hX (hBX hp) (hBX hq) (hBX hr)⟩

theorem pocket_inj {a b : (ℝ × ℝ)} {B : Finset (ℝ × ℝ)} (h : (a ≠ b ∧ (∀ p_k ∈ B, 0 < orient a b p_k) ∧ (∀ p_k ∈ B, ∀ q_k ∈ B, p_k ≠ q_k → orient p_k q_k a ≠ 0) ∧ (∀ p_k ∈ B, ∀ q_k ∈ B, p_k ≠ q_k → orient p_k q_k b ≠ 0) ∧ (∀ p_k ∈ B, ∀ q_k ∈ B, ∀ r_k ∈ B, p_k ≠ q_k → q_k ≠ r_k → p_k ≠ r_k → orient p_k q_k r_k ≠ 0))) :
    Set.InjOn (fun p => (((((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2)) / orient a b p, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2))) / orient a b p) : ℝ × ℝ)).1) (B : Set (ℝ × ℝ)) :=
  projected_fst_injOn h.1 h.2.1 h.2.2.1

theorem pocket_chain_or_outward {a b : (ℝ × ℝ)} {B : Finset (ℝ × ℝ)} {h w : ℕ}
    (hB : (a ≠ b ∧ (∀ p_k ∈ B, 0 < orient a b p_k) ∧ (∀ p_k ∈ B, ∀ q_k ∈ B, p_k ≠ q_k → orient p_k q_k a ≠ 0) ∧ (∀ p_k ∈ B, ∀ q_k ∈ B, p_k ≠ q_k → orient p_k q_k b ≠ 0) ∧ (∀ p_k ∈ B, ∀ q_k ∈ B, ∀ r_k ∈ B, p_k ≠ q_k → q_k ≠ r_k → p_k ≠ r_k → orient p_k q_k r_k ≠ 0))) (hh : 0 < h) (hcard : h * w < B.card) :
    (∃ C ⊆ B, h ≤ C.card ∧ (∀ p_m ∈ C, ∀ q_m ∈ C, (((((b.1 - a.1) * (p_m.1 - a.1) + (b.2 - a.2) * (p_m.2 - a.2)) / orient a b p_m, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p_m.1 - a.1) + (b.2 - a.2) * (p_m.2 - a.2))) / orient a b p_m) : ℝ × ℝ)).1 < (((((b.1 - a.1) * (q_m.1 - a.1) + (b.2 - a.2) * (q_m.2 - a.2)) / orient a b q_m, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q_m.1 - a.1) + (b.2 - a.2) * (q_m.2 - a.2))) / orient a b q_m) : ℝ × ℝ)).1 → (((((b.1 - a.1) * (p_m.1 - a.1) + (b.2 - a.2) * (p_m.2 - a.2)) / orient a b p_m, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p_m.1 - a.1) + (b.2 - a.2) * (p_m.2 - a.2))) / orient a b p_m) : ℝ × ℝ)).2 < (((((b.1 - a.1) * (q_m.1 - a.1) + (b.2 - a.2) * (q_m.2 - a.2)) / orient a b q_m, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q_m.1 - a.1) + (b.2 - a.2) * (q_m.2 - a.2))) / orient a b q_m) : ℝ × ℝ)).2)) ∨
      ∃ C ⊆ B, w < C.card ∧ (∀ p_m ∈ C, ∀ q_m ∈ C, (((((b.1 - a.1) * (p_m.1 - a.1) + (b.2 - a.2) * (p_m.2 - a.2)) / orient a b p_m, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p_m.1 - a.1) + (b.2 - a.2) * (p_m.2 - a.2))) / orient a b p_m) : ℝ × ℝ)).1 < (((((b.1 - a.1) * (q_m.1 - a.1) + (b.2 - a.2) * (q_m.2 - a.2)) / orient a b q_m, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q_m.1 - a.1) + (b.2 - a.2) * (q_m.2 - a.2))) / orient a b q_m) : ℝ × ℝ)).1 → (((((b.1 - a.1) * (q_m.1 - a.1) + (b.2 - a.2) * (q_m.2 - a.2)) / orient a b q_m, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q_m.1 - a.1) + (b.2 - a.2) * (q_m.2 - a.2))) / orient a b q_m) : ℝ × ℝ)).2 < (((((b.1 - a.1) * (p_m.1 - a.1) + (b.2 - a.2) * (p_m.2 - a.2)) / orient a b p_m, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p_m.1 - a.1) + (b.2 - a.2) * (p_m.2 - a.2))) / orient a b p_m) : ℝ × ℝ)).2) := by
  let R (p q : (ℝ × ℝ)) := (((((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2)) / orient a b p, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2))) / orient a b p) : ℝ × ℝ)).1 < (((((b.1 - a.1) * (q.1 - a.1) + (b.2 - a.2) * (q.2 - a.2)) / orient a b q, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q.1 - a.1) + (b.2 - a.2) * (q.2 - a.2))) / orient a b q) : ℝ × ℝ)).1 ∧
    (((((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2)) / orient a b p, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2))) / orient a b p) : ℝ × ℝ)).2 < (((((b.1 - a.1) * (q.1 - a.1) + (b.2 - a.2) * (q.2 - a.2)) / orient a b q, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q.1 - a.1) + (b.2 - a.2) * (q.2 - a.2))) / orient a b q) : ℝ × ℝ)).2
  obtain hchain | hanti := chain_or_antichain B R
    (fun p h => (lt_irrefl _) h.1)
    (fun hpq hqr => ⟨hpq.1.trans hqr.1, hpq.2.trans hqr.2⟩) hh hcard
  · obtain ⟨C, hCB, hc, hC⟩ := hchain
    refine Or.inl ⟨C, hCB, hc, fun p hp q hq hpq => ?_⟩
    rcases hC hp hq (fun e => hpq.ne (congrArg (fun p => (((((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2)) / orient a b p, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2))) / orient a b p) : ℝ × ℝ)).1) e)) with hr | hr
    · exact hr.2
    · exact (hpq.not_gt hr.1).elim
  · obtain ⟨C, hCB, hc, hC⟩ := hanti
    refine Or.inr ⟨C, hCB, hc, fun p hp q hq hpq => ?_⟩
    have hne : p ≠ q := fun e => hpq.ne (congrArg (fun p => (((((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2)) / orient a b p, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2))) / orient a b p) : ℝ × ℝ)).1) e)
    have hp' := hCB hp
    have hq' := hCB hq
    rcases lt_or_gt_of_ne (projected_snd_ne_of_ne hB.1 (hB.2.1 p hp')
      (hB.2.1 q hq') (hB.2.2.2.1 p hp' q hq' hne)) with hr | hr
    · exact (hC hp hq hne ⟨hpq, hr⟩).elim
    · exact hr

theorem pocket_convex {a b : (ℝ × ℝ)} {B : Finset (ℝ × ℝ)} {up : Bool}
    (hB : (a ≠ b ∧ (∀ p_k ∈ B, 0 < orient a b p_k) ∧ (∀ p_k ∈ B, ∀ q_k ∈ B, p_k ≠ q_k → orient p_k q_k a ≠ 0) ∧ (∀ p_k ∈ B, ∀ q_k ∈ B, p_k ≠ q_k → orient p_k q_k b ≠ 0) ∧ (∀ p_k ∈ B, ∀ q_k ∈ B, ∀ r_k ∈ B, p_k ≠ q_k → q_k ≠ r_k → p_k ≠ r_k → orient p_k q_k r_k ≠ 0))) (hturn : (∀ p_t ∈ B, ∀ q_t ∈ B, ∀ r_t ∈ B, (((((b.1 - a.1) * (p_t.1 - a.1) + (b.2 - a.2) * (p_t.2 - a.2)) / orient a b p_t, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p_t.1 - a.1) + (b.2 - a.2) * (p_t.2 - a.2))) / orient a b p_t) : ℝ × ℝ)).1 < (((((b.1 - a.1) * (q_t.1 - a.1) + (b.2 - a.2) * (q_t.2 - a.2)) / orient a b q_t, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q_t.1 - a.1) + (b.2 - a.2) * (q_t.2 - a.2))) / orient a b q_t) : ℝ × ℝ)).1 → (((((b.1 - a.1) * (q_t.1 - a.1) + (b.2 - a.2) * (q_t.2 - a.2)) / orient a b q_t, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q_t.1 - a.1) + (b.2 - a.2) * (q_t.2 - a.2))) / orient a b q_t) : ℝ × ℝ)).1 < (((((b.1 - a.1) * (r_t.1 - a.1) + (b.2 - a.2) * (r_t.2 - a.2)) / orient a b r_t, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (r_t.1 - a.1) + (b.2 - a.2) * (r_t.2 - a.2))) / orient a b r_t) : ℝ × ℝ)).1 → (if up then 0 < orient p_t q_t r_t else orient p_t q_t r_t < 0))) : (∀ p_c ∈ B, ∃ u_c v_c : ℝ, ∀ q_c ∈ B, q_c ≠ p_c → u_c * p_c.1 + v_c * p_c.2 < u_c * q_c.1 + v_c * q_c.2) := by
  cases up
  · exact convex_of_clockwise (orient := orient) (pocket_inj hB) hturn
  · refine convex_of_clockwise (orient := orient) (key := fun p => -(((((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2)) / orient a b p, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2))) / orient a b p) : ℝ × ℝ)).1)
      (fun p hp q hq h => (pocket_inj hB) hp hq (neg_injective h)) ?_
    intro p hp q hq r hr hpq hqr
    rw [(orient_reverse (orient := orient)) p q r, neg_lt_zero]
    exact hturn r hr q hq p hp (neg_lt_neg_iff.mp hqr) (neg_lt_neg_iff.mp hpq)

theorem pocket_cups_caps {a b : (ℝ × ℝ)} {B : Finset (ℝ × ℝ)}
    (hB : (a ≠ b ∧ (∀ p_k ∈ B, 0 < orient a b p_k) ∧ (∀ p_k ∈ B, ∀ q_k ∈ B, p_k ≠ q_k → orient p_k q_k a ≠ 0) ∧ (∀ p_k ∈ B, ∀ q_k ∈ B, p_k ≠ q_k → orient p_k q_k b ≠ 0) ∧ (∀ p_k ∈ B, ∀ q_k ∈ B, ∀ r_k ∈ B, p_k ≠ q_k → q_k ≠ r_k → p_k ≠ r_k → orient p_k q_k r_k ≠ 0))) (s t : ℕ) (hcard : (s + t).choose s < B.card) :
    (∃ C ⊆ B, C.card = s + 2 ∧ (∀ p_t ∈ C, ∀ q_t ∈ C, ∀ r_t ∈ C, (((((b.1 - a.1) * (p_t.1 - a.1) + (b.2 - a.2) * (p_t.2 - a.2)) / orient a b p_t, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p_t.1 - a.1) + (b.2 - a.2) * (p_t.2 - a.2))) / orient a b p_t) : ℝ × ℝ)).1 < (((((b.1 - a.1) * (q_t.1 - a.1) + (b.2 - a.2) * (q_t.2 - a.2)) / orient a b q_t, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q_t.1 - a.1) + (b.2 - a.2) * (q_t.2 - a.2))) / orient a b q_t) : ℝ × ℝ)).1 → (((((b.1 - a.1) * (q_t.1 - a.1) + (b.2 - a.2) * (q_t.2 - a.2)) / orient a b q_t, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q_t.1 - a.1) + (b.2 - a.2) * (q_t.2 - a.2))) / orient a b q_t) : ℝ × ℝ)).1 < (((((b.1 - a.1) * (r_t.1 - a.1) + (b.2 - a.2) * (r_t.2 - a.2)) / orient a b r_t, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (r_t.1 - a.1) + (b.2 - a.2) * (r_t.2 - a.2))) / orient a b r_t) : ℝ × ℝ)).1 → (if false then 0 < orient p_t q_t r_t else orient p_t q_t r_t < 0))) ∨
      (∃ C ⊆ B, C.card = t + 2 ∧ (∀ p_t ∈ C, ∀ q_t ∈ C, ∀ r_t ∈ C, (((((b.1 - a.1) * (p_t.1 - a.1) + (b.2 - a.2) * (p_t.2 - a.2)) / orient a b p_t, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p_t.1 - a.1) + (b.2 - a.2) * (p_t.2 - a.2))) / orient a b p_t) : ℝ × ℝ)).1 < (((((b.1 - a.1) * (q_t.1 - a.1) + (b.2 - a.2) * (q_t.2 - a.2)) / orient a b q_t, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q_t.1 - a.1) + (b.2 - a.2) * (q_t.2 - a.2))) / orient a b q_t) : ℝ × ℝ)).1 → (((((b.1 - a.1) * (q_t.1 - a.1) + (b.2 - a.2) * (q_t.2 - a.2)) / orient a b q_t, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q_t.1 - a.1) + (b.2 - a.2) * (q_t.2 - a.2))) / orient a b q_t) : ℝ × ℝ)).1 < (((((b.1 - a.1) * (r_t.1 - a.1) + (b.2 - a.2) * (r_t.2 - a.2)) / orient a b r_t, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (r_t.1 - a.1) + (b.2 - a.2) * (r_t.2 - a.2))) / orient a b r_t) : ℝ × ℝ)).1 → (if true then 0 < orient p_t q_t r_t else orient p_t q_t r_t < 0))) := by
  classical
  let f := fun p => ((((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2)) / orient a b p, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2))) / orient a b p) : ℝ × ℝ)
  have hfi : Set.InjOn f (B : Set (ℝ × ℝ)) :=
    fun _ hp _ hq h => (pocket_inj hB) hp hq (congrArg Prod.fst h)
  have hg : (Set.InjOn Prod.fst ((B.image f) : Set (ℝ × ℝ)) ∧ ∀ a_g ∈ (B.image f), ∀ b_g ∈ (B.image f), ∀ c_g ∈ (B.image f), a_g.1 < b_g.1 → b_g.1 < c_g.1 → orient a_g b_g c_g ≠ 0) :=
    projected_image_general hB.1 hB.2.1 hB.2.2.1 hB.2.2.2.2
  have hcard' : (s + t).choose s < (B.image f).card := by
    rwa [Finset.card_image_of_injOn hfi]
  have liftImage {D : Finset (ℝ × ℝ)} (hD : D ⊆ B.image f) :
      ∃ C ⊆ B, C.card = D.card ∧ ∀ p ∈ C, f p ∈ D := by
    let C := B.filter fun p => f p ∈ D
    have hC : C ⊆ B := filter_subset _ _
    have he : C.image f = D := by
      ext z
      constructor
      · intro hz
        obtain ⟨p, hp, rfl⟩ := mem_image.mp hz
        exact (mem_filter.mp hp).2
      · intro hz
        obtain ⟨p, hp, rfl⟩ := mem_image.mp (hD hz)
        exact mem_image_of_mem f (mem_filter.mpr ⟨hp, hz⟩)
    exact ⟨C, hC, by rw [← he, Finset.card_image_of_injOn (hfi.mono hC)],
      fun p hp => (mem_filter.mp hp).2⟩
  rcases cups_caps_planar s t _ hg hcard' with
    ⟨D, hD, hd, _, hturn⟩ | ⟨D, hD, hd, _, hturn⟩
  · obtain ⟨C, hC, hc, him⟩ := liftImage hD
    refine Or.inl ⟨C, hC, hc.trans hd, fun p hp q hq r hr hpq hqr => ?_⟩
    exact (projected_turn hB.1 (hB.2.1 p (hC hp)) (hB.2.1 q (hC hq))
      (hB.2.1 r (hC hr))).1.mp (hturn _ (him p hp) _ (him q hq) _ (him r hr) hpq hqr)
  · obtain ⟨C, hC, hc, him⟩ := liftImage hD
    refine Or.inr ⟨C, hC, hc.trans hd, fun p hp q hq r hr hpq hqr => ?_⟩
    exact (projected_turn hB.1 (hB.2.1 p (hC hp)) (hB.2.1 q (hC hq))
      (hB.2.1 r (hC hr))).2.mp (hturn _ (him p hp) _ (him q hq) _ (him r hr) hpq hqr)

theorem exists_max_subset {α : Type*} (B : Finset α) (P : Finset α → Prop) (h0 : P ∅) :
    ∃ C ⊆ B, P C ∧ ∀ Y ⊆ B, P Y → Y.card ≤ C.card := by
  classical
  let F := B.powerset.filter P
  have hF : F.Nonempty := ⟨∅, by simp [F, h0]⟩
  obtain ⟨C, hC, hc⟩ := Finset.exists_max_image F Finset.card hF
  exact ⟨C, mem_powerset.mp (mem_filter.mp hC).1, (mem_filter.mp hC).2,
    fun Y hY hy => hc Y (mem_filter.mpr ⟨mem_powerset.mpr hY, hy⟩)⟩

theorem pocket_large_turn_sum {a b : (ℝ × ℝ)} {B : Finset (ℝ × ℝ)} {m : ℕ}
    (hB : (a ≠ b ∧ (∀ p_k ∈ B, 0 < orient a b p_k) ∧ (∀ p_k ∈ B, ∀ q_k ∈ B, p_k ≠ q_k → orient p_k q_k a ≠ 0) ∧ (∀ p_k ∈ B, ∀ q_k ∈ B, p_k ≠ q_k → orient p_k q_k b ≠ 0) ∧ (∀ p_k ∈ B, ∀ q_k ∈ B, ∀ r_k ∈ B, p_k ≠ q_k → q_k ≠ r_k → p_k ≠ r_k → orient p_k q_k r_k ≠ 0))) (hcard : 2 ^ m < B.card) :
    ∃ C ⊆ B, ∃ D ⊆ B, (∀ p_t ∈ C, ∀ q_t ∈ C, ∀ r_t ∈ C, (((((b.1 - a.1) * (p_t.1 - a.1) + (b.2 - a.2) * (p_t.2 - a.2)) / orient a b p_t, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p_t.1 - a.1) + (b.2 - a.2) * (p_t.2 - a.2))) / orient a b p_t) : ℝ × ℝ)).1 < (((((b.1 - a.1) * (q_t.1 - a.1) + (b.2 - a.2) * (q_t.2 - a.2)) / orient a b q_t, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q_t.1 - a.1) + (b.2 - a.2) * (q_t.2 - a.2))) / orient a b q_t) : ℝ × ℝ)).1 → (((((b.1 - a.1) * (q_t.1 - a.1) + (b.2 - a.2) * (q_t.2 - a.2)) / orient a b q_t, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q_t.1 - a.1) + (b.2 - a.2) * (q_t.2 - a.2))) / orient a b q_t) : ℝ × ℝ)).1 < (((((b.1 - a.1) * (r_t.1 - a.1) + (b.2 - a.2) * (r_t.2 - a.2)) / orient a b r_t, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (r_t.1 - a.1) + (b.2 - a.2) * (r_t.2 - a.2))) / orient a b r_t) : ℝ × ℝ)).1 → (if true then 0 < orient p_t q_t r_t else orient p_t q_t r_t < 0)) ∧ (∀ p_t ∈ D, ∀ q_t ∈ D, ∀ r_t ∈ D, (((((b.1 - a.1) * (p_t.1 - a.1) + (b.2 - a.2) * (p_t.2 - a.2)) / orient a b p_t, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p_t.1 - a.1) + (b.2 - a.2) * (p_t.2 - a.2))) / orient a b p_t) : ℝ × ℝ)).1 < (((((b.1 - a.1) * (q_t.1 - a.1) + (b.2 - a.2) * (q_t.2 - a.2)) / orient a b q_t, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q_t.1 - a.1) + (b.2 - a.2) * (q_t.2 - a.2))) / orient a b q_t) : ℝ × ℝ)).1 → (((((b.1 - a.1) * (q_t.1 - a.1) + (b.2 - a.2) * (q_t.2 - a.2)) / orient a b q_t, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q_t.1 - a.1) + (b.2 - a.2) * (q_t.2 - a.2))) / orient a b q_t) : ℝ × ℝ)).1 < (((((b.1 - a.1) * (r_t.1 - a.1) + (b.2 - a.2) * (r_t.2 - a.2)) / orient a b r_t, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (r_t.1 - a.1) + (b.2 - a.2) * (r_t.2 - a.2))) / orient a b r_t) : ℝ × ℝ)).1 → (if false then 0 < orient p_t q_t r_t else orient p_t q_t r_t < 0)) ∧
      m < C.card + D.card := by
  classical
  have largest (up : Bool) :
      ∃ C ⊆ B, (∀ p_t ∈ C, ∀ q_t ∈ C, ∀ r_t ∈ C, (((((b.1 - a.1) * (p_t.1 - a.1) + (b.2 - a.2) * (p_t.2 - a.2)) / orient a b p_t, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p_t.1 - a.1) + (b.2 - a.2) * (p_t.2 - a.2))) / orient a b p_t) : ℝ × ℝ)).1 < (((((b.1 - a.1) * (q_t.1 - a.1) + (b.2 - a.2) * (q_t.2 - a.2)) / orient a b q_t, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q_t.1 - a.1) + (b.2 - a.2) * (q_t.2 - a.2))) / orient a b q_t) : ℝ × ℝ)).1 → (((((b.1 - a.1) * (q_t.1 - a.1) + (b.2 - a.2) * (q_t.2 - a.2)) / orient a b q_t, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q_t.1 - a.1) + (b.2 - a.2) * (q_t.2 - a.2))) / orient a b q_t) : ℝ × ℝ)).1 < (((((b.1 - a.1) * (r_t.1 - a.1) + (b.2 - a.2) * (r_t.2 - a.2)) / orient a b r_t, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (r_t.1 - a.1) + (b.2 - a.2) * (r_t.2 - a.2))) / orient a b r_t) : ℝ × ℝ)).1 → (if up then 0 < orient p_t q_t r_t else orient p_t q_t r_t < 0)) ∧
        ∀ Y ⊆ B, (∀ p_t ∈ Y, ∀ q_t ∈ Y, ∀ r_t ∈ Y, (((((b.1 - a.1) * (p_t.1 - a.1) + (b.2 - a.2) * (p_t.2 - a.2)) / orient a b p_t, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p_t.1 - a.1) + (b.2 - a.2) * (p_t.2 - a.2))) / orient a b p_t) : ℝ × ℝ)).1 < (((((b.1 - a.1) * (q_t.1 - a.1) + (b.2 - a.2) * (q_t.2 - a.2)) / orient a b q_t, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q_t.1 - a.1) + (b.2 - a.2) * (q_t.2 - a.2))) / orient a b q_t) : ℝ × ℝ)).1 → (((((b.1 - a.1) * (q_t.1 - a.1) + (b.2 - a.2) * (q_t.2 - a.2)) / orient a b q_t, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q_t.1 - a.1) + (b.2 - a.2) * (q_t.2 - a.2))) / orient a b q_t) : ℝ × ℝ)).1 < (((((b.1 - a.1) * (r_t.1 - a.1) + (b.2 - a.2) * (r_t.2 - a.2)) / orient a b r_t, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (r_t.1 - a.1) + (b.2 - a.2) * (r_t.2 - a.2))) / orient a b r_t) : ℝ × ℝ)).1 → (if up then 0 < orient p_t q_t r_t else orient p_t q_t r_t < 0)) → Y.card ≤ C.card := by
    exact exists_max_subset B _ (by simp)
  obtain ⟨C, hC, hc, hmaxC⟩ := largest true
  obtain ⟨D, hD, hd, hmaxD⟩ := largest false
  refine ⟨C, hC, D, hD, hc, hd, lt_of_not_ge fun h => ?_⟩
  let s := D.card - 1
  let t := C.card - 1
  have hst : s + t ≤ m := by dsimp [s, t]; omega
  have hchoose := (Nat.choose_le_two_pow (s + t) s).trans
    (Nat.pow_le_pow_right (by decide) hst)
  rcases pocket_cups_caps hB s t (hchoose.trans_lt hcard) with
    ⟨Y, hY, hy, hturn⟩ | ⟨Y, hY, hy, hturn⟩
  · have hbound := hmaxD Y hY hturn
    dsimp [s] at hy
    omega
  · have hbound := hmaxC Y hY hturn
    dsimp [t] at hy
    omega

theorem pocket_anchor_first {a b p q : (ℝ × ℝ)} {B : Finset (ℝ × ℝ)}
    (hB : (a ≠ b ∧ (∀ p_k ∈ B, 0 < orient a b p_k) ∧ (∀ p_k ∈ B, ∀ q_k ∈ B, p_k ≠ q_k → orient p_k q_k a ≠ 0) ∧ (∀ p_k ∈ B, ∀ q_k ∈ B, p_k ≠ q_k → orient p_k q_k b ≠ 0) ∧ (∀ p_k ∈ B, ∀ q_k ∈ B, ∀ r_k ∈ B, p_k ≠ q_k → q_k ≠ r_k → p_k ≠ r_k → orient p_k q_k r_k ≠ 0))) (hp : p ∈ B) (hq : q ∈ B)
    (h : (((((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2)) / orient a b p, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2))) / orient a b p) : ℝ × ℝ)).1 < (((((b.1 - a.1) * (q.1 - a.1) + (b.2 - a.2) * (q.2 - a.2)) / orient a b q, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q.1 - a.1) + (b.2 - a.2) * (q.2 - a.2))) / orient a b q) : ℝ × ℝ)).1) : orient p q a < 0 :=
  (projected_fst_lt hB.1 (hB.2.1 p hp) (hB.2.1 q hq)).mp h

theorem pocket_anchor_forward {a b p q : (ℝ × ℝ)} {B : Finset (ℝ × ℝ)}
    (hB : (a ≠ b ∧ (∀ p_k ∈ B, 0 < orient a b p_k) ∧ (∀ p_k ∈ B, ∀ q_k ∈ B, p_k ≠ q_k → orient p_k q_k a ≠ 0) ∧ (∀ p_k ∈ B, ∀ q_k ∈ B, p_k ≠ q_k → orient p_k q_k b ≠ 0) ∧ (∀ p_k ∈ B, ∀ q_k ∈ B, ∀ r_k ∈ B, p_k ≠ q_k → q_k ≠ r_k → p_k ≠ r_k → orient p_k q_k r_k ≠ 0))) (hmono : (∀ p_m ∈ B, ∀ q_m ∈ B, (((((b.1 - a.1) * (p_m.1 - a.1) + (b.2 - a.2) * (p_m.2 - a.2)) / orient a b p_m, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p_m.1 - a.1) + (b.2 - a.2) * (p_m.2 - a.2))) / orient a b p_m) : ℝ × ℝ)).1 < (((((b.1 - a.1) * (q_m.1 - a.1) + (b.2 - a.2) * (q_m.2 - a.2)) / orient a b q_m, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q_m.1 - a.1) + (b.2 - a.2) * (q_m.2 - a.2))) / orient a b q_m) : ℝ × ℝ)).1 → (((((b.1 - a.1) * (p_m.1 - a.1) + (b.2 - a.2) * (p_m.2 - a.2)) / orient a b p_m, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p_m.1 - a.1) + (b.2 - a.2) * (p_m.2 - a.2))) / orient a b p_m) : ℝ × ℝ)).2 < (((((b.1 - a.1) * (q_m.1 - a.1) + (b.2 - a.2) * (q_m.2 - a.2)) / orient a b q_m, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q_m.1 - a.1) + (b.2 - a.2) * (q_m.2 - a.2))) / orient a b q_m) : ℝ × ℝ)).2)) (hp : p ∈ B) (hq : q ∈ B)
    (h : (((((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2)) / orient a b p, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2))) / orient a b p) : ℝ × ℝ)).1 < (((((b.1 - a.1) * (q.1 - a.1) + (b.2 - a.2) * (q.2 - a.2)) / orient a b q, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q.1 - a.1) + (b.2 - a.2) * (q.2 - a.2))) / orient a b q) : ℝ × ℝ)).1) : 0 < orient p q b :=
  (projected_snd_lt hB.1 (hB.2.1 p hp) (hB.2.1 q hq)).mp (hmono p hp q hq h)

theorem pocket_anchor_outward {a b p q : (ℝ × ℝ)} {B : Finset (ℝ × ℝ)}
    (hB : (a ≠ b ∧ (∀ p_k ∈ B, 0 < orient a b p_k) ∧ (∀ p_k ∈ B, ∀ q_k ∈ B, p_k ≠ q_k → orient p_k q_k a ≠ 0) ∧ (∀ p_k ∈ B, ∀ q_k ∈ B, p_k ≠ q_k → orient p_k q_k b ≠ 0) ∧ (∀ p_k ∈ B, ∀ q_k ∈ B, ∀ r_k ∈ B, p_k ≠ q_k → q_k ≠ r_k → p_k ≠ r_k → orient p_k q_k r_k ≠ 0))) (hanti : (∀ p_m ∈ B, ∀ q_m ∈ B, (((((b.1 - a.1) * (p_m.1 - a.1) + (b.2 - a.2) * (p_m.2 - a.2)) / orient a b p_m, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p_m.1 - a.1) + (b.2 - a.2) * (p_m.2 - a.2))) / orient a b p_m) : ℝ × ℝ)).1 < (((((b.1 - a.1) * (q_m.1 - a.1) + (b.2 - a.2) * (q_m.2 - a.2)) / orient a b q_m, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q_m.1 - a.1) + (b.2 - a.2) * (q_m.2 - a.2))) / orient a b q_m) : ℝ × ℝ)).1 → (((((b.1 - a.1) * (q_m.1 - a.1) + (b.2 - a.2) * (q_m.2 - a.2)) / orient a b q_m, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q_m.1 - a.1) + (b.2 - a.2) * (q_m.2 - a.2))) / orient a b q_m) : ℝ × ℝ)).2 < (((((b.1 - a.1) * (p_m.1 - a.1) + (b.2 - a.2) * (p_m.2 - a.2)) / orient a b p_m, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p_m.1 - a.1) + (b.2 - a.2) * (p_m.2 - a.2))) / orient a b p_m) : ℝ × ℝ)).2)) (hp : p ∈ B) (hq : q ∈ B)
    (h : (((((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2)) / orient a b p, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2))) / orient a b p) : ℝ × ℝ)).1 < (((((b.1 - a.1) * (q.1 - a.1) + (b.2 - a.2) * (q.2 - a.2)) / orient a b q, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q.1 - a.1) + (b.2 - a.2) * (q.2 - a.2))) / orient a b q) : ℝ × ℝ)).1) : orient p q b < 0 := by
  rw [(orient_flip (orient := orient)) p q b, neg_lt_zero]
  exact (projected_snd_lt hB.1 (hB.2.1 q hq) (hB.2.1 p hp)).mp (hanti p hp q hq h)

/-- A positive-turn chain in a pocket and a negative-turn chain in its clockwise successor
join to form a convex set. The anchor pairs span the adjacent pockets. -/
theorem consecutive_pocket_chains {a b c d : (ℝ × ℝ)} {B C : Finset (ℝ × ℝ)}
    (hB : (a ≠ b ∧ (∀ p_k ∈ B, 0 < orient a b p_k) ∧ (∀ p_k ∈ B, ∀ q_k ∈ B, p_k ≠ q_k → orient p_k q_k a ≠ 0) ∧ (∀ p_k ∈ B, ∀ q_k ∈ B, p_k ≠ q_k → orient p_k q_k b ≠ 0) ∧ (∀ p_k ∈ B, ∀ q_k ∈ B, ∀ r_k ∈ B, p_k ≠ q_k → q_k ≠ r_k → p_k ≠ r_k → orient p_k q_k r_k ≠ 0))) (hC : (c ≠ d ∧ (∀ p_k ∈ C, 0 < orient c d p_k) ∧ (∀ p_k ∈ C, ∀ q_k ∈ C, p_k ≠ q_k → orient p_k q_k c ≠ 0) ∧ (∀ p_k ∈ C, ∀ q_k ∈ C, p_k ≠ q_k → orient p_k q_k d ≠ 0) ∧ (∀ p_k ∈ C, ∀ q_k ∈ C, ∀ r_k ∈ C, p_k ≠ q_k → q_k ≠ r_k → p_k ≠ r_k → orient p_k q_k r_k ≠ 0))) (hdisj : Disjoint B C)
    (hmB : (∀ p_m ∈ B, ∀ q_m ∈ B, (((((b.1 - a.1) * (p_m.1 - a.1) + (b.2 - a.2) * (p_m.2 - a.2)) / orient a b p_m, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p_m.1 - a.1) + (b.2 - a.2) * (p_m.2 - a.2))) / orient a b p_m) : ℝ × ℝ)).1 < (((((b.1 - a.1) * (q_m.1 - a.1) + (b.2 - a.2) * (q_m.2 - a.2)) / orient a b q_m, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q_m.1 - a.1) + (b.2 - a.2) * (q_m.2 - a.2))) / orient a b q_m) : ℝ × ℝ)).1 → (((((b.1 - a.1) * (p_m.1 - a.1) + (b.2 - a.2) * (p_m.2 - a.2)) / orient a b p_m, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p_m.1 - a.1) + (b.2 - a.2) * (p_m.2 - a.2))) / orient a b p_m) : ℝ × ℝ)).2 < (((((b.1 - a.1) * (q_m.1 - a.1) + (b.2 - a.2) * (q_m.2 - a.2)) / orient a b q_m, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q_m.1 - a.1) + (b.2 - a.2) * (q_m.2 - a.2))) / orient a b q_m) : ℝ × ℝ)).2)) (hmC : (∀ p_m ∈ C, ∀ q_m ∈ C, (((((d.1 - c.1) * (p_m.1 - c.1) + (d.2 - c.2) * (p_m.2 - c.2)) / orient c d p_m, (((d.1 - c.1)^2 + (d.2 - c.2)^2) - ((d.1 - c.1) * (p_m.1 - c.1) + (d.2 - c.2) * (p_m.2 - c.2))) / orient c d p_m) : ℝ × ℝ)).1 < (((((d.1 - c.1) * (q_m.1 - c.1) + (d.2 - c.2) * (q_m.2 - c.2)) / orient c d q_m, (((d.1 - c.1)^2 + (d.2 - c.2)^2) - ((d.1 - c.1) * (q_m.1 - c.1) + (d.2 - c.2) * (q_m.2 - c.2))) / orient c d q_m) : ℝ × ℝ)).1 → (((((d.1 - c.1) * (p_m.1 - c.1) + (d.2 - c.2) * (p_m.2 - c.2)) / orient c d p_m, (((d.1 - c.1)^2 + (d.2 - c.2)^2) - ((d.1 - c.1) * (p_m.1 - c.1) + (d.2 - c.2) * (p_m.2 - c.2))) / orient c d p_m) : ℝ × ℝ)).2 < (((((d.1 - c.1) * (q_m.1 - c.1) + (d.2 - c.2) * (q_m.2 - c.2)) / orient c d q_m, (((d.1 - c.1)^2 + (d.2 - c.2)^2) - ((d.1 - c.1) * (q_m.1 - c.1) + (d.2 - c.2) * (q_m.2 - c.2))) / orient c d q_m) : ℝ × ℝ)).2))
    (htB : (∀ p_t ∈ B, ∀ q_t ∈ B, ∀ r_t ∈ B, (((((b.1 - a.1) * (p_t.1 - a.1) + (b.2 - a.2) * (p_t.2 - a.2)) / orient a b p_t, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p_t.1 - a.1) + (b.2 - a.2) * (p_t.2 - a.2))) / orient a b p_t) : ℝ × ℝ)).1 < (((((b.1 - a.1) * (q_t.1 - a.1) + (b.2 - a.2) * (q_t.2 - a.2)) / orient a b q_t, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q_t.1 - a.1) + (b.2 - a.2) * (q_t.2 - a.2))) / orient a b q_t) : ℝ × ℝ)).1 → (((((b.1 - a.1) * (q_t.1 - a.1) + (b.2 - a.2) * (q_t.2 - a.2)) / orient a b q_t, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q_t.1 - a.1) + (b.2 - a.2) * (q_t.2 - a.2))) / orient a b q_t) : ℝ × ℝ)).1 < (((((b.1 - a.1) * (r_t.1 - a.1) + (b.2 - a.2) * (r_t.2 - a.2)) / orient a b r_t, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (r_t.1 - a.1) + (b.2 - a.2) * (r_t.2 - a.2))) / orient a b r_t) : ℝ × ℝ)).1 → (if true then 0 < orient p_t q_t r_t else orient p_t q_t r_t < 0))) (htC : (∀ p_t ∈ C, ∀ q_t ∈ C, ∀ r_t ∈ C, (((((d.1 - c.1) * (p_t.1 - c.1) + (d.2 - c.2) * (p_t.2 - c.2)) / orient c d p_t, (((d.1 - c.1)^2 + (d.2 - c.2)^2) - ((d.1 - c.1) * (p_t.1 - c.1) + (d.2 - c.2) * (p_t.2 - c.2))) / orient c d p_t) : ℝ × ℝ)).1 < (((((d.1 - c.1) * (q_t.1 - c.1) + (d.2 - c.2) * (q_t.2 - c.2)) / orient c d q_t, (((d.1 - c.1)^2 + (d.2 - c.2)^2) - ((d.1 - c.1) * (q_t.1 - c.1) + (d.2 - c.2) * (q_t.2 - c.2))) / orient c d q_t) : ℝ × ℝ)).1 → (((((d.1 - c.1) * (q_t.1 - c.1) + (d.2 - c.2) * (q_t.2 - c.2)) / orient c d q_t, (((d.1 - c.1)^2 + (d.2 - c.2)^2) - ((d.1 - c.1) * (q_t.1 - c.1) + (d.2 - c.2) * (q_t.2 - c.2))) / orient c d q_t) : ℝ × ℝ)).1 < (((((d.1 - c.1) * (r_t.1 - c.1) + (d.2 - c.2) * (r_t.2 - c.2)) / orient c d r_t, (((d.1 - c.1)^2 + (d.2 - c.2)^2) - ((d.1 - c.1) * (r_t.1 - c.1) + (d.2 - c.2) * (r_t.2 - c.2))) / orient c d r_t) : ℝ × ℝ)).1 → (if false then 0 < orient p_t q_t r_t else orient p_t q_t r_t < 0)))
    (hBC : ∀ p ∈ B, ∀ r ∈ C, 0 < orient p a r ∧ orient p r b < 0)
    (hCB : ∀ p ∈ C, ∀ r ∈ B, orient p c r < 0 ∧ 0 < orient p r d) :
    (∀ p_c ∈ (B ∪ C), ∃ u_c v_c : ℝ, ∀ q_c ∈ (B ∪ C), q_c ≠ p_c → u_c * p_c.1 + v_c * p_c.2 < u_c * q_c.1 + v_c * q_c.2) := by
  refine convex_of_clockwise_union (orient := orient) (keyB := fun p => -(((((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2)) / orient a b p, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p.1 - a.1) + (b.2 - a.2) * (p.2 - a.2))) / orient a b p) : ℝ × ℝ)).1)
    (keyC := fun p => (((((d.1 - c.1) * (p.1 - c.1) + (d.2 - c.2) * (p.2 - c.2)) / orient c d p, (((d.1 - c.1)^2 + (d.2 - c.2)^2) - ((d.1 - c.1) * (p.1 - c.1) + (d.2 - c.2) * (p.2 - c.2))) / orient c d p) : ℝ × ℝ)).1) hdisj (fun p hp q hq he => (pocket_inj hB) hp hq (neg_injective he))
    (pocket_inj hC) ?_ htC ?_ ?_
  · intro p hp q hq r hr hpq hqr
    rw [(orient_reverse (orient := orient)) p q r, neg_lt_zero]
    exact htB r hr q hq p hp (neg_lt_neg_iff.mp hqr) (neg_lt_neg_iff.mp hpq)
  · intro p hp q hq r hr hpq
    have hqp := neg_lt_neg_iff.mp hpq
    obtain ⟨h₁, h₂⟩ := hBC q hq r hr
    rw [(orient_flip (orient := orient)) p q r, neg_lt_zero]
    apply orient_pos_of_following (a := a) (b := b) (by rw [(orient_cycle (orient := orient)) q a b]; exact hB.2.1 q hq) h₁ h₂
    · exact pocket_anchor_first hB hq hp hqp
    · exact pocket_anchor_forward hB hmB hq hp hqp
  · intro p hp q hq r hr hpq
    obtain ⟨h₁, h₂⟩ := hCB p hp r hr
    apply orient_lt_of_preceding (a := c) (b := d) (by rw [(orient_cycle (orient := orient)) p c d]; exact hC.2.1 p hp) h₁ h₂
    · exact pocket_anchor_first hC hp hq hpq
    · exact pocket_anchor_forward hC hmC hp hq hpq

/-- Outward-facing caps from separated pockets can be joined in their pocket order. -/
theorem convex_of_outward_pockets (s : Finset ℕ) (B : ℕ → Finset (ℝ × ℝ))
    (a b : ℕ → (ℝ × ℝ))
    (hpocket : ∀ i ∈ s, ((a i) ≠ (b i) ∧ (∀ p_k ∈ (B i), 0 < orient (a i) (b i) p_k) ∧ (∀ p_k ∈ (B i), ∀ q_k ∈ (B i), p_k ≠ q_k → orient p_k q_k (a i) ≠ 0) ∧ (∀ p_k ∈ (B i), ∀ q_k ∈ (B i), p_k ≠ q_k → orient p_k q_k (b i) ≠ 0) ∧ (∀ p_k ∈ (B i), ∀ q_k ∈ (B i), ∀ r_k ∈ (B i), p_k ≠ q_k → q_k ≠ r_k → p_k ≠ r_k → orient p_k q_k r_k ≠ 0)))
    (hanti : ∀ i ∈ s, (∀ p_m ∈ (B i), ∀ q_m ∈ (B i), ((((((b i).1 - (a i).1) * (p_m.1 - (a i).1) + ((b i).2 - (a i).2) * (p_m.2 - (a i).2)) / orient (a i) (b i) p_m, ((((b i).1 - (a i).1)^2 + ((b i).2 - (a i).2)^2) - (((b i).1 - (a i).1) * (p_m.1 - (a i).1) + ((b i).2 - (a i).2) * (p_m.2 - (a i).2))) / orient (a i) (b i) p_m) : ℝ × ℝ)).1 < ((((((b i).1 - (a i).1) * (q_m.1 - (a i).1) + ((b i).2 - (a i).2) * (q_m.2 - (a i).2)) / orient (a i) (b i) q_m, ((((b i).1 - (a i).1)^2 + ((b i).2 - (a i).2)^2) - (((b i).1 - (a i).1) * (q_m.1 - (a i).1) + ((b i).2 - (a i).2) * (q_m.2 - (a i).2))) / orient (a i) (b i) q_m) : ℝ × ℝ)).1 → ((((((b i).1 - (a i).1) * (q_m.1 - (a i).1) + ((b i).2 - (a i).2) * (q_m.2 - (a i).2)) / orient (a i) (b i) q_m, ((((b i).1 - (a i).1)^2 + ((b i).2 - (a i).2)^2) - (((b i).1 - (a i).1) * (q_m.1 - (a i).1) + ((b i).2 - (a i).2) * (q_m.2 - (a i).2))) / orient (a i) (b i) q_m) : ℝ × ℝ)).2 < ((((((b i).1 - (a i).1) * (p_m.1 - (a i).1) + ((b i).2 - (a i).2) * (p_m.2 - (a i).2)) / orient (a i) (b i) p_m, ((((b i).1 - (a i).1)^2 + ((b i).2 - (a i).2)^2) - (((b i).1 - (a i).1) * (p_m.1 - (a i).1) + ((b i).2 - (a i).2) * (p_m.2 - (a i).2))) / orient (a i) (b i) p_m) : ℝ × ℝ)).2))
    (hturn : ∀ i ∈ s, (∀ p_t ∈ (B i), ∀ q_t ∈ (B i), ∀ r_t ∈ (B i), ((((((b i).1 - (a i).1) * (p_t.1 - (a i).1) + ((b i).2 - (a i).2) * (p_t.2 - (a i).2)) / orient (a i) (b i) p_t, ((((b i).1 - (a i).1)^2 + ((b i).2 - (a i).2)^2) - (((b i).1 - (a i).1) * (p_t.1 - (a i).1) + ((b i).2 - (a i).2) * (p_t.2 - (a i).2))) / orient (a i) (b i) p_t) : ℝ × ℝ)).1 < ((((((b i).1 - (a i).1) * (q_t.1 - (a i).1) + ((b i).2 - (a i).2) * (q_t.2 - (a i).2)) / orient (a i) (b i) q_t, ((((b i).1 - (a i).1)^2 + ((b i).2 - (a i).2)^2) - (((b i).1 - (a i).1) * (q_t.1 - (a i).1) + ((b i).2 - (a i).2) * (q_t.2 - (a i).2))) / orient (a i) (b i) q_t) : ℝ × ℝ)).1 → ((((((b i).1 - (a i).1) * (q_t.1 - (a i).1) + ((b i).2 - (a i).2) * (q_t.2 - (a i).2)) / orient (a i) (b i) q_t, ((((b i).1 - (a i).1)^2 + ((b i).2 - (a i).2)^2) - (((b i).1 - (a i).1) * (q_t.1 - (a i).1) + ((b i).2 - (a i).2) * (q_t.2 - (a i).2))) / orient (a i) (b i) q_t) : ℝ × ℝ)).1 < ((((((b i).1 - (a i).1) * (r_t.1 - (a i).1) + ((b i).2 - (a i).2) * (r_t.2 - (a i).2)) / orient (a i) (b i) r_t, ((((b i).1 - (a i).1)^2 + ((b i).2 - (a i).2)^2) - (((b i).1 - (a i).1) * (r_t.1 - (a i).1) + ((b i).2 - (a i).2) * (r_t.2 - (a i).2))) / orient (a i) (b i) r_t) : ℝ × ℝ)).1 → (if false then 0 < orient p_t q_t r_t else orient p_t q_t r_t < 0)))
    (hsec : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ∀ p ∈ B i, ∀ r ∈ B j, 0 < orient p (a i) r ∧ 0 < orient p r (b i))
    (hthree : ∀ i ∈ s, ∀ j ∈ s, ∀ k ∈ s, i < j → j < k →
      ∀ p ∈ B i, ∀ q ∈ B j, ∀ r ∈ B k, orient p q r < 0) :
    (∀ p_c ∈ (s.biUnion B), ∃ u_c v_c : ℝ, ∀ q_c ∈ (s.biUnion B), q_c ≠ p_c → u_c * p_c.1 + v_c * p_c.2 < u_c * q_c.1 + v_c * q_c.2) := by
  classical
  have hc (p : (ℝ × ℝ)) (hp : p ∈ s.biUnion B) : ∃ i ∈ s, p ∈ B i := mem_biUnion.mp hp
  let tag (p : (ℝ × ℝ)) := if hp : p ∈ s.biUnion B then (hc p hp).choose else 0
  let key (p : (ℝ × ℝ)) := ((((((b (tag p)).1 - (a (tag p)).1) * (p.1 - (a (tag p)).1) + ((b (tag p)).2 - (a (tag p)).2) * (p.2 - (a (tag p)).2)) / orient (a (tag p)) (b (tag p)) p, ((((b (tag p)).1 - (a (tag p)).1)^2 + ((b (tag p)).2 - (a (tag p)).2)^2) - (((b (tag p)).1 - (a (tag p)).1) * (p.1 - (a (tag p)).1) + ((b (tag p)).2 - (a (tag p)).2) * (p.2 - (a (tag p)).2))) / orient (a (tag p)) (b (tag p)) p) : ℝ × ℝ)).1
  have htag {p : (ℝ × ℝ)} (hp : p ∈ s.biUnion B) : tag p ∈ s ∧ p ∈ B (tag p) := by
    simpa only [tag, dif_pos hp] using (hc p hp).choose_spec
  refine convex_of_clockwise_blocks (orient := orient) (tag := tag) (key := key) ?_ ?_ ?_ ?_
  · intro p hp q hq he
    have ht : tag p = tag q := congrArg (fun w => (ofLex w).1) he
    have hk : key p = key q := congrArg (fun w => (ofLex w).2) he
    exact (pocket_inj (hpocket _ (htag hp).1)) (htag hp).2 (ht ▸ (htag hq).2)
      (by simpa only [key, ← ht] using hk)
  · intro p hp q hq r hr he₁ he₂ hpq hqr
    have her : tag p = tag r := he₁.trans he₂
    apply hturn _ (htag hp).1 p (htag hp).2 q (he₁ ▸ (htag hq).2)
      r (her ▸ (htag hr).2)
    · simpa only [key, ← he₁] using hpq
    · simpa only [key, ← he₁, ← her] using hqr
  · intro p hp q hq r hr he hne hk
    have hh := hpocket _ (htag hp).1
    have hq' : q ∈ B (tag p) := he ▸ (htag hq).2
    have hk' : ((((((b (tag p)).1 - (a (tag p)).1) * (p.1 - (a (tag p)).1) + ((b (tag p)).2 - (a (tag p)).2) * (p.2 - (a (tag p)).2)) / orient (a (tag p)) (b (tag p)) p, ((((b (tag p)).1 - (a (tag p)).1)^2 + ((b (tag p)).2 - (a (tag p)).2)^2) - (((b (tag p)).1 - (a (tag p)).1) * (p.1 - (a (tag p)).1) + ((b (tag p)).2 - (a (tag p)).2) * (p.2 - (a (tag p)).2))) / orient (a (tag p)) (b (tag p)) p) : ℝ × ℝ)).1 < ((((((b (tag p)).1 - (a (tag p)).1) * (q.1 - (a (tag p)).1) + ((b (tag p)).2 - (a (tag p)).2) * (q.2 - (a (tag p)).2)) / orient (a (tag p)) (b (tag p)) q, ((((b (tag p)).1 - (a (tag p)).1)^2 + ((b (tag p)).2 - (a (tag p)).2)^2) - (((b (tag p)).1 - (a (tag p)).1) * (q.1 - (a (tag p)).1) + ((b (tag p)).2 - (a (tag p)).2) * (q.2 - (a (tag p)).2))) / orient (a (tag p)) (b (tag p)) q) : ℝ × ℝ)).1 := by
      simpa only [key, ← he] using hk
    obtain ⟨h₁, h₂⟩ := hsec _ (htag hp).1 _ (htag hr).1 hne p (htag hp).2 r (htag hr).2
    apply orient_lt_of_sector (by rw [(orient_cycle (orient := orient)) p (a (tag p)) (b (tag p))]; exact hh.2.1 p (htag hp).2) h₁ h₂
    · exact pocket_anchor_first hh (htag hp).2 hq' hk'
    · exact pocket_anchor_outward hh (hanti _ (htag hp).1) (htag hp).2 hq' hk'
  · intro p hp q hq r hr hpq hqr
    exact hthree _ (htag hp).1 _ (htag hq).1 _ (htag hr).1 hpq hqr
      p (htag hp).2 q (htag hq).2 r (htag hr).2

theorem convex_from_chain_run {X : Finset (ℝ × ℝ)} {k d n : ℕ}
    (a b : ℕ → (ℝ × ℝ)) (B : ℕ → Finset (ℝ × ℝ))
    (hsub : ∀ i ≤ k, B i ⊆ X)
    (hpocket : ∀ i ≤ k, ((a i) ≠ (b i) ∧ (∀ p_k ∈ (B i), 0 < orient (a i) (b i) p_k) ∧ (∀ p_k ∈ (B i), ∀ q_k ∈ (B i), p_k ≠ q_k → orient p_k q_k (a i) ≠ 0) ∧ (∀ p_k ∈ (B i), ∀ q_k ∈ (B i), p_k ≠ q_k → orient p_k q_k (b i) ≠ 0) ∧ (∀ p_k ∈ (B i), ∀ q_k ∈ (B i), ∀ r_k ∈ (B i), p_k ≠ q_k → q_k ≠ r_k → p_k ≠ r_k → orient p_k q_k r_k ≠ 0)))
    (hmono : ∀ i ≤ k, (∀ p_m ∈ (B i), ∀ q_m ∈ (B i), ((((((b i).1 - (a i).1) * (p_m.1 - (a i).1) + ((b i).2 - (a i).2) * (p_m.2 - (a i).2)) / orient (a i) (b i) p_m, ((((b i).1 - (a i).1)^2 + ((b i).2 - (a i).2)^2) - (((b i).1 - (a i).1) * (p_m.1 - (a i).1) + ((b i).2 - (a i).2) * (p_m.2 - (a i).2))) / orient (a i) (b i) p_m) : ℝ × ℝ)).1 < ((((((b i).1 - (a i).1) * (q_m.1 - (a i).1) + ((b i).2 - (a i).2) * (q_m.2 - (a i).2)) / orient (a i) (b i) q_m, ((((b i).1 - (a i).1)^2 + ((b i).2 - (a i).2)^2) - (((b i).1 - (a i).1) * (q_m.1 - (a i).1) + ((b i).2 - (a i).2) * (q_m.2 - (a i).2))) / orient (a i) (b i) q_m) : ℝ × ℝ)).1 → ((((((b i).1 - (a i).1) * (p_m.1 - (a i).1) + ((b i).2 - (a i).2) * (p_m.2 - (a i).2)) / orient (a i) (b i) p_m, ((((b i).1 - (a i).1)^2 + ((b i).2 - (a i).2)^2) - (((b i).1 - (a i).1) * (p_m.1 - (a i).1) + ((b i).2 - (a i).2) * (p_m.2 - (a i).2))) / orient (a i) (b i) p_m) : ℝ × ℝ)).2 < ((((((b i).1 - (a i).1) * (q_m.1 - (a i).1) + ((b i).2 - (a i).2) * (q_m.2 - (a i).2)) / orient (a i) (b i) q_m, ((((b i).1 - (a i).1)^2 + ((b i).2 - (a i).2)^2) - (((b i).1 - (a i).1) * (q_m.1 - (a i).1) + ((b i).2 - (a i).2) * (q_m.2 - (a i).2))) / orient (a i) (b i) q_m) : ℝ × ℝ)).2))
    (hlarge : ∀ i ≤ k, 2 ^ (n + d) < (B i).card)
    (hdisj : ∀ i < k, Disjoint (B i) (B (i + 1)))
    (hforward : ∀ i < k, ∀ p ∈ B i, ∀ r ∈ B (i + 1),
      0 < orient p (a i) r ∧ orient p r (b i) < 0)
    (hback : ∀ i < k, ∀ p ∈ B (i + 1), ∀ r ∈ B i,
      orient p (a (i + 1)) r < 0 ∧ 0 < orient p r (b (i + 1)))
    (hlen : n ≤ k * (d + 1)) :
    ∃ Y ⊆ X, Y.card = n ∧ (∀ p_c ∈ Y, ∃ u_c v_c : ℝ, ∀ q_c ∈ Y, q_c ≠ p_c → u_c * p_c.1 + v_c * p_c.2 < u_c * q_c.1 + v_c * q_c.2) := by
  classical
  by_contra hn
  have hchoices (i : ℕ) :
      ∃ C D : Finset (ℝ × ℝ), i ≤ k →
        C ⊆ B i ∧ D ⊆ B i ∧ (∀ p_t ∈ C, ∀ q_t ∈ C, ∀ r_t ∈ C, ((((((b i).1 - (a i).1) * (p_t.1 - (a i).1) + ((b i).2 - (a i).2) * (p_t.2 - (a i).2)) / orient (a i) (b i) p_t, ((((b i).1 - (a i).1)^2 + ((b i).2 - (a i).2)^2) - (((b i).1 - (a i).1) * (p_t.1 - (a i).1) + ((b i).2 - (a i).2) * (p_t.2 - (a i).2))) / orient (a i) (b i) p_t) : ℝ × ℝ)).1 < ((((((b i).1 - (a i).1) * (q_t.1 - (a i).1) + ((b i).2 - (a i).2) * (q_t.2 - (a i).2)) / orient (a i) (b i) q_t, ((((b i).1 - (a i).1)^2 + ((b i).2 - (a i).2)^2) - (((b i).1 - (a i).1) * (q_t.1 - (a i).1) + ((b i).2 - (a i).2) * (q_t.2 - (a i).2))) / orient (a i) (b i) q_t) : ℝ × ℝ)).1 → ((((((b i).1 - (a i).1) * (q_t.1 - (a i).1) + ((b i).2 - (a i).2) * (q_t.2 - (a i).2)) / orient (a i) (b i) q_t, ((((b i).1 - (a i).1)^2 + ((b i).2 - (a i).2)^2) - (((b i).1 - (a i).1) * (q_t.1 - (a i).1) + ((b i).2 - (a i).2) * (q_t.2 - (a i).2))) / orient (a i) (b i) q_t) : ℝ × ℝ)).1 < ((((((b i).1 - (a i).1) * (r_t.1 - (a i).1) + ((b i).2 - (a i).2) * (r_t.2 - (a i).2)) / orient (a i) (b i) r_t, ((((b i).1 - (a i).1)^2 + ((b i).2 - (a i).2)^2) - (((b i).1 - (a i).1) * (r_t.1 - (a i).1) + ((b i).2 - (a i).2) * (r_t.2 - (a i).2))) / orient (a i) (b i) r_t) : ℝ × ℝ)).1 → (if true then 0 < orient p_t q_t r_t else orient p_t q_t r_t < 0)) ∧
          (∀ p_t ∈ D, ∀ q_t ∈ D, ∀ r_t ∈ D, ((((((b i).1 - (a i).1) * (p_t.1 - (a i).1) + ((b i).2 - (a i).2) * (p_t.2 - (a i).2)) / orient (a i) (b i) p_t, ((((b i).1 - (a i).1)^2 + ((b i).2 - (a i).2)^2) - (((b i).1 - (a i).1) * (p_t.1 - (a i).1) + ((b i).2 - (a i).2) * (p_t.2 - (a i).2))) / orient (a i) (b i) p_t) : ℝ × ℝ)).1 < ((((((b i).1 - (a i).1) * (q_t.1 - (a i).1) + ((b i).2 - (a i).2) * (q_t.2 - (a i).2)) / orient (a i) (b i) q_t, ((((b i).1 - (a i).1)^2 + ((b i).2 - (a i).2)^2) - (((b i).1 - (a i).1) * (q_t.1 - (a i).1) + ((b i).2 - (a i).2) * (q_t.2 - (a i).2))) / orient (a i) (b i) q_t) : ℝ × ℝ)).1 → ((((((b i).1 - (a i).1) * (q_t.1 - (a i).1) + ((b i).2 - (a i).2) * (q_t.2 - (a i).2)) / orient (a i) (b i) q_t, ((((b i).1 - (a i).1)^2 + ((b i).2 - (a i).2)^2) - (((b i).1 - (a i).1) * (q_t.1 - (a i).1) + ((b i).2 - (a i).2) * (q_t.2 - (a i).2))) / orient (a i) (b i) q_t) : ℝ × ℝ)).1 < ((((((b i).1 - (a i).1) * (r_t.1 - (a i).1) + ((b i).2 - (a i).2) * (r_t.2 - (a i).2)) / orient (a i) (b i) r_t, ((((b i).1 - (a i).1)^2 + ((b i).2 - (a i).2)^2) - (((b i).1 - (a i).1) * (r_t.1 - (a i).1) + ((b i).2 - (a i).2) * (r_t.2 - (a i).2))) / orient (a i) (b i) r_t) : ℝ × ℝ)).1 → (if false then 0 < orient p_t q_t r_t else orient p_t q_t r_t < 0)) ∧ n + d ≤ C.card + D.card := by
    by_cases hi : i ≤ k
    · obtain ⟨C, hC, D, hD, hc, hd, hsum⟩ :=
        pocket_large_turn_sum (hpocket i hi) (hlarge i hi)
      exact ⟨C, D, fun _ => ⟨hC, hD, hc, hd, hsum.le⟩⟩
    · exact ⟨∅, ∅, fun h => (hi h).elim⟩
  choose C D hCD using hchoices
  have hcsmall (i : ℕ) (hi : i ≤ k) : (C i).card < n := by
    obtain ⟨hC, _, hc, _, _⟩ := hCD i hi
    exact lt_of_not_ge fun h => hn
      (exact_convex_size (hC.trans (hsub i hi)) (pocket_convex (orient := orient) (pocket_mono (hpocket i hi) hC) hc) h)
  have hpairs (i : ℕ) (hi : i < k) : (C i).card + (D (i + 1)).card < n := by
    have hi' : i + 1 ≤ k := by omega
    obtain ⟨hC, _, hc, _, _⟩ := hCD i hi.le
    obtain ⟨_, hD, _, hd, _⟩ := hCD (i + 1) hi'
    have hsep : Disjoint (C i) (D (i + 1)) := (hdisj i hi).mono hC hD
    have hconv := consecutive_pocket_chains
      (pocket_mono (hpocket i hi.le) hC) (pocket_mono (hpocket (i + 1) hi') hD) hsep
      (fun p hp q hq => hmono i hi.le p (hC hp) q (hC hq))
      (fun p hp q hq => hmono (i + 1) hi' p (hD hp) q (hD hq)) hc hd
      (fun p hp r hr => hforward i hi p (hC hp) r (hD hr))
      (fun p hp r hr => hback i hi p (hD hp) r (hC hr))
    have hsub' : C i ∪ D (i + 1) ⊆ X := union_subset (hC.trans (hsub i hi.le))
      (hD.trans (hsub (i + 1) hi'))
    refine lt_of_not_ge fun h => hn (exact_convex_size hsub' hconv ?_)
    rwa [Finset.card_union_of_disjoint hsep]
  have hgrow := growth_along_blocks (a := fun i => (C i).card) (b := fun i => (D i).card)
    (fun i hi => (hCD i hi).2.2.2.2) hpairs
  have hsmall := hcsmall k le_rfl
  omega

theorem pocket_outward_or_convex {X B : Finset (ℝ × ℝ)} {a b : (ℝ × ℝ)} {s n : ℕ}
    (hBX : B ⊆ X) (hB : (a ≠ b ∧ (∀ p_k ∈ B, 0 < orient a b p_k) ∧ (∀ p_k ∈ B, ∀ q_k ∈ B, p_k ≠ q_k → orient p_k q_k a ≠ 0) ∧ (∀ p_k ∈ B, ∀ q_k ∈ B, p_k ≠ q_k → orient p_k q_k b ≠ 0) ∧ (∀ p_k ∈ B, ∀ q_k ∈ B, ∀ r_k ∈ B, p_k ≠ q_k → q_k ≠ r_k → p_k ≠ r_k → orient p_k q_k r_k ≠ 0))) (hanti : (∀ p_m ∈ B, ∀ q_m ∈ B, (((((b.1 - a.1) * (p_m.1 - a.1) + (b.2 - a.2) * (p_m.2 - a.2)) / orient a b p_m, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p_m.1 - a.1) + (b.2 - a.2) * (p_m.2 - a.2))) / orient a b p_m) : ℝ × ℝ)).1 < (((((b.1 - a.1) * (q_m.1 - a.1) + (b.2 - a.2) * (q_m.2 - a.2)) / orient a b q_m, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q_m.1 - a.1) + (b.2 - a.2) * (q_m.2 - a.2))) / orient a b q_m) : ℝ × ℝ)).1 → (((((b.1 - a.1) * (q_m.1 - a.1) + (b.2 - a.2) * (q_m.2 - a.2)) / orient a b q_m, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q_m.1 - a.1) + (b.2 - a.2) * (q_m.2 - a.2))) / orient a b q_m) : ℝ × ℝ)).2 < (((((b.1 - a.1) * (p_m.1 - a.1) + (b.2 - a.2) * (p_m.2 - a.2)) / orient a b p_m, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p_m.1 - a.1) + (b.2 - a.2) * (p_m.2 - a.2))) / orient a b p_m) : ℝ × ℝ)).2))
    (hcard : (s + n).choose s < B.card) :
    (∃ C ⊆ B, C.card = s + 2 ∧ (∀ p_t ∈ C, ∀ q_t ∈ C, ∀ r_t ∈ C, (((((b.1 - a.1) * (p_t.1 - a.1) + (b.2 - a.2) * (p_t.2 - a.2)) / orient a b p_t, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p_t.1 - a.1) + (b.2 - a.2) * (p_t.2 - a.2))) / orient a b p_t) : ℝ × ℝ)).1 < (((((b.1 - a.1) * (q_t.1 - a.1) + (b.2 - a.2) * (q_t.2 - a.2)) / orient a b q_t, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q_t.1 - a.1) + (b.2 - a.2) * (q_t.2 - a.2))) / orient a b q_t) : ℝ × ℝ)).1 → (((((b.1 - a.1) * (q_t.1 - a.1) + (b.2 - a.2) * (q_t.2 - a.2)) / orient a b q_t, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q_t.1 - a.1) + (b.2 - a.2) * (q_t.2 - a.2))) / orient a b q_t) : ℝ × ℝ)).1 < (((((b.1 - a.1) * (r_t.1 - a.1) + (b.2 - a.2) * (r_t.2 - a.2)) / orient a b r_t, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (r_t.1 - a.1) + (b.2 - a.2) * (r_t.2 - a.2))) / orient a b r_t) : ℝ × ℝ)).1 → (if false then 0 < orient p_t q_t r_t else orient p_t q_t r_t < 0)) ∧ (∀ p_m ∈ C, ∀ q_m ∈ C, (((((b.1 - a.1) * (p_m.1 - a.1) + (b.2 - a.2) * (p_m.2 - a.2)) / orient a b p_m, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p_m.1 - a.1) + (b.2 - a.2) * (p_m.2 - a.2))) / orient a b p_m) : ℝ × ℝ)).1 < (((((b.1 - a.1) * (q_m.1 - a.1) + (b.2 - a.2) * (q_m.2 - a.2)) / orient a b q_m, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q_m.1 - a.1) + (b.2 - a.2) * (q_m.2 - a.2))) / orient a b q_m) : ℝ × ℝ)).1 → (((((b.1 - a.1) * (q_m.1 - a.1) + (b.2 - a.2) * (q_m.2 - a.2)) / orient a b q_m, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (q_m.1 - a.1) + (b.2 - a.2) * (q_m.2 - a.2))) / orient a b q_m) : ℝ × ℝ)).2 < (((((b.1 - a.1) * (p_m.1 - a.1) + (b.2 - a.2) * (p_m.2 - a.2)) / orient a b p_m, (((b.1 - a.1)^2 + (b.2 - a.2)^2) - ((b.1 - a.1) * (p_m.1 - a.1) + (b.2 - a.2) * (p_m.2 - a.2))) / orient a b p_m) : ℝ × ℝ)).2)) ∨
      ∃ Y ⊆ X, Y.card = n ∧ (∀ p_c ∈ Y, ∃ u_c v_c : ℝ, ∀ q_c ∈ Y, q_c ≠ p_c → u_c * p_c.1 + v_c * p_c.2 < u_c * q_c.1 + v_c * q_c.2) := by
  rcases pocket_cups_caps hB s n hcard with ⟨C, hC, hc, ht⟩ | ⟨C, hC, hc, ht⟩
  · exact Or.inl ⟨C, hC, hc, ht, fun p hp q hq => hanti p (hC hp) q (hC hq)⟩
  · exact Or.inr (exact_convex_size (hC.trans hBX) (pocket_convex (orient := orient) (pocket_mono hB hC) ht) (by omega))

theorem convex_from_outward_covers {X : Finset (ℝ × ℝ)} {n : ℕ}
    (s : Finset ℕ) (B : ℕ → Finset (ℝ × ℝ)) (a b : ℕ → (ℝ × ℝ))
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (B i) (B j))
    (hsub : ∀ i ∈ s, B i ⊆ X)
    (hpocket : ∀ i ∈ s, ((a i) ≠ (b i) ∧ (∀ p_k ∈ (B i), 0 < orient (a i) (b i) p_k) ∧ (∀ p_k ∈ (B i), ∀ q_k ∈ (B i), p_k ≠ q_k → orient p_k q_k (a i) ≠ 0) ∧ (∀ p_k ∈ (B i), ∀ q_k ∈ (B i), p_k ≠ q_k → orient p_k q_k (b i) ≠ 0) ∧ (∀ p_k ∈ (B i), ∀ q_k ∈ (B i), ∀ r_k ∈ (B i), p_k ≠ q_k → q_k ≠ r_k → p_k ≠ r_k → orient p_k q_k r_k ≠ 0)))
    (hanti : ∀ i ∈ s, (∀ p_m ∈ (B i), ∀ q_m ∈ (B i), ((((((b i).1 - (a i).1) * (p_m.1 - (a i).1) + ((b i).2 - (a i).2) * (p_m.2 - (a i).2)) / orient (a i) (b i) p_m, ((((b i).1 - (a i).1)^2 + ((b i).2 - (a i).2)^2) - (((b i).1 - (a i).1) * (p_m.1 - (a i).1) + ((b i).2 - (a i).2) * (p_m.2 - (a i).2))) / orient (a i) (b i) p_m) : ℝ × ℝ)).1 < ((((((b i).1 - (a i).1) * (q_m.1 - (a i).1) + ((b i).2 - (a i).2) * (q_m.2 - (a i).2)) / orient (a i) (b i) q_m, ((((b i).1 - (a i).1)^2 + ((b i).2 - (a i).2)^2) - (((b i).1 - (a i).1) * (q_m.1 - (a i).1) + ((b i).2 - (a i).2) * (q_m.2 - (a i).2))) / orient (a i) (b i) q_m) : ℝ × ℝ)).1 → ((((((b i).1 - (a i).1) * (q_m.1 - (a i).1) + ((b i).2 - (a i).2) * (q_m.2 - (a i).2)) / orient (a i) (b i) q_m, ((((b i).1 - (a i).1)^2 + ((b i).2 - (a i).2)^2) - (((b i).1 - (a i).1) * (q_m.1 - (a i).1) + ((b i).2 - (a i).2) * (q_m.2 - (a i).2))) / orient (a i) (b i) q_m) : ℝ × ℝ)).2 < ((((((b i).1 - (a i).1) * (p_m.1 - (a i).1) + ((b i).2 - (a i).2) * (p_m.2 - (a i).2)) / orient (a i) (b i) p_m, ((((b i).1 - (a i).1)^2 + ((b i).2 - (a i).2)^2) - (((b i).1 - (a i).1) * (p_m.1 - (a i).1) + ((b i).2 - (a i).2) * (p_m.2 - (a i).2))) / orient (a i) (b i) p_m) : ℝ × ℝ)).2))
    (hturn : ∀ i ∈ s, (∀ p_t ∈ (B i), ∀ q_t ∈ (B i), ∀ r_t ∈ (B i), ((((((b i).1 - (a i).1) * (p_t.1 - (a i).1) + ((b i).2 - (a i).2) * (p_t.2 - (a i).2)) / orient (a i) (b i) p_t, ((((b i).1 - (a i).1)^2 + ((b i).2 - (a i).2)^2) - (((b i).1 - (a i).1) * (p_t.1 - (a i).1) + ((b i).2 - (a i).2) * (p_t.2 - (a i).2))) / orient (a i) (b i) p_t) : ℝ × ℝ)).1 < ((((((b i).1 - (a i).1) * (q_t.1 - (a i).1) + ((b i).2 - (a i).2) * (q_t.2 - (a i).2)) / orient (a i) (b i) q_t, ((((b i).1 - (a i).1)^2 + ((b i).2 - (a i).2)^2) - (((b i).1 - (a i).1) * (q_t.1 - (a i).1) + ((b i).2 - (a i).2) * (q_t.2 - (a i).2))) / orient (a i) (b i) q_t) : ℝ × ℝ)).1 → ((((((b i).1 - (a i).1) * (q_t.1 - (a i).1) + ((b i).2 - (a i).2) * (q_t.2 - (a i).2)) / orient (a i) (b i) q_t, ((((b i).1 - (a i).1)^2 + ((b i).2 - (a i).2)^2) - (((b i).1 - (a i).1) * (q_t.1 - (a i).1) + ((b i).2 - (a i).2) * (q_t.2 - (a i).2))) / orient (a i) (b i) q_t) : ℝ × ℝ)).1 < ((((((b i).1 - (a i).1) * (r_t.1 - (a i).1) + ((b i).2 - (a i).2) * (r_t.2 - (a i).2)) / orient (a i) (b i) r_t, ((((b i).1 - (a i).1)^2 + ((b i).2 - (a i).2)^2) - (((b i).1 - (a i).1) * (r_t.1 - (a i).1) + ((b i).2 - (a i).2) * (r_t.2 - (a i).2))) / orient (a i) (b i) r_t) : ℝ × ℝ)).1 → (if false then 0 < orient p_t q_t r_t else orient p_t q_t r_t < 0)))
    (hsec : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ∀ p ∈ B i, ∀ r ∈ B j, 0 < orient p (a i) r ∧ 0 < orient p r (b i))
    (hthree : ∀ i ∈ s, ∀ j ∈ s, ∀ k ∈ s, i < j → j < k →
      ∀ p ∈ B i, ∀ q ∈ B j, ∀ r ∈ B k, orient p q r < 0)
    (hcard : n ≤ ∑ i ∈ s, (B i).card) :
    ∃ Y ⊆ X, Y.card = n ∧ (∀ p_c ∈ Y, ∃ u_c v_c : ℝ, ∀ q_c ∈ Y, q_c ≠ p_c → u_c * p_c.1 + v_c * p_c.2 < u_c * q_c.1 + v_c * q_c.2) := by
  classical
  refine exact_convex_size (Y := s.biUnion B) ?_
    (convex_of_outward_pockets (orient := orient) s B a b hpocket hanti hturn hsec hthree) ?_
  · intro p hp
    obtain ⟨i, hi, hip⟩ := mem_biUnion.mp hp
    exact hsub i hi hip
  · rwa [Finset.card_biUnion (fun i hi j hj h => hdisj i hi j hj h)]

/-- Evaluate the binomial sum at an auxiliary positive weight to bound one coefficient. -/
theorem weighted_choose_le_pow (s n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ((s + n).choose s : ℝ) * x ^ s ≤ (1 + x) ^ (s + n) := by
  rw [add_comm (1 : ℝ) x, add_pow]
  have h := Finset.single_le_sum
    (f := fun j => x ^ j * (1 : ℝ) ^ (s + n - j) * ((s + n).choose j : ℝ))
    (fun j _ => by positivity) (Finset.mem_range.mpr (show s < s + n + 1 by omega))
  simpa [mul_comm] using h

theorem sparse_binomial_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : ℕ, 0 < T ∧ ∀ n : ℕ,
      ((n / T + n).choose (n / T) : ℝ) ≤ (2 : ℝ) ^ (δ * n) := by
  have base : (1 : ℝ) < 2 := by norm_num
  have hbase : (0 : ℝ) < 2 := by norm_num
  let x := min ((2 : ℝ) ^ (δ / 4) - 1) 1
  have hx : 0 < x := lt_min (sub_pos.mpr (Real.one_lt_rpow base (by linarith))) zero_lt_one
  have hupper : 1 + x ≤ (2 : ℝ) ^ (δ / 4) := by
    have h := min_le_left ((2 : ℝ) ^ (δ / 4) - 1) 1
    dsimp [x]
    linarith only [h]
  let y := Real.logb 2 x⁻¹
  obtain ⟨T, hT⟩ := exists_nat_gt (max (y / (δ / 2)) 1)
  have hTpos : 0 < T := by
    have h : (1 : ℝ) < T := (le_max_right _ _).trans_lt hT
    exact_mod_cast (zero_lt_one.trans h)
  have hy : y ≤ (δ / 2) * (T : ℝ) := by
    have h : y / (δ / 2) < (T : ℝ) := (le_max_left _ _).trans_lt hT
    linarith only [(div_lt_iff₀ (show 0 < δ / 2 by linarith)).mp h]
  refine ⟨T, hTpos, fun n => ?_⟩
  let s := n / T
  change ((s + n).choose s : ℝ) ≤ _
  have hs : s ≤ n := Nat.div_le_self _ _
  have hsmul : (s : ℝ) * (T : ℝ) ≤ n := by
    exact_mod_cast (Nat.div_mul_le_self n T)
  have hterm₁ : (1 + x) ^ (s + n) ≤ (2 : ℝ) ^ ((δ / 2) * n) := by
    calc
      (1 + x) ^ (s + n) ≤ ((2 : ℝ) ^ (δ / 4)) ^ (s + n) :=
        pow_le_pow_left₀ (by positivity) hupper _
      _ = (2 : ℝ) ^ ((δ / 4) * (↑(s + n) : ℝ)) :=
        (Real.rpow_mul_natCast hbase.le _ _).symm
      _ ≤ (2 : ℝ) ^ ((δ / 2) * n) := by
        apply Real.rpow_le_rpow_of_exponent_le base.le
        have hs' : (s : ℝ) ≤ n := by exact_mod_cast hs
        push_cast
        nlinarith only [mul_le_mul_of_nonneg_left hs' hδ.le]
  have hterm₂ : (x⁻¹) ^ s ≤ (2 : ℝ) ^ ((δ / 2) * n) := by
    have hxy : (2 : ℝ) ^ y = x⁻¹ :=
      Real.rpow_logb hbase base.ne' (inv_pos.mpr hx)
    rw [← hxy, ← Real.rpow_mul_natCast hbase.le]
    apply Real.rpow_le_rpow_of_exponent_le base.le
    calc
      y * (s : ℝ) ≤ (δ / 2 * (T : ℝ)) * (s : ℝ) :=
        mul_le_mul_of_nonneg_right hy (Nat.cast_nonneg s)
      _ = δ / 2 * ((s : ℝ) * (T : ℝ)) := by ring
      _ ≤ δ / 2 * n := mul_le_mul_of_nonneg_left hsmul (by linarith)
  have hw := weighted_choose_le_pow s n hx.le
  calc
    ((s + n).choose s : ℝ) = (((s + n).choose s : ℝ) * x ^ s) * (x⁻¹) ^ s := by
      rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hx.ne', one_pow, mul_one]
    _ ≤ (1 + x) ^ (s + n) * (x⁻¹) ^ s :=
      mul_le_mul_of_nonneg_right hw (by positivity)
    _ ≤ (2 : ℝ) ^ ((δ / 2) * n) * (2 : ℝ) ^ ((δ / 2) * n) :=
      mul_le_mul hterm₁ hterm₂ (by positivity) (by positivity)
    _ = (2 : ℝ) ^ (δ * n) := by rw [← Real.rpow_add hbase]; congr 1; ring

theorem orient_two_angular_intervals {o l p r l' q r' : (ℝ × ℝ)}
    (hlr : orient o l r < 0) (hlp : orient o l p < 0) (hpr : orient o p r < 0)
    (hlr' : orient o l' r' < 0) (hlq' : orient o l' q < 0) (hqr' : orient o q r' < 0)
    (hll' : orient o l l' < 0) (hlr'' : orient o l r' < 0)
    (hrl' : orient o r l' < 0) (hrr' : orient o r r' < 0) :
    orient o p q < 0 := by
  have hp₁ := (orient_angular_interval hlr hlp hpr).1 hll' hrl'
  have hp₂ := (orient_angular_interval hlr hlp hpr).1 hlr'' hrr'
  rw [(orient_swap_last (orient := orient)) o p l', neg_lt_zero] at hp₁
  rw [(orient_swap_last (orient := orient)) o p r', neg_lt_zero] at hp₂
  have h := (orient_angular_interval hlr' hlq' hqr').2 hp₁ hp₂
  rw [(orient_swap_last (orient := orient)) o q p, neg_pos] at h
  exact h
theorem layout_of_family {X : Finset (ℝ × ℝ)} {L k : ℕ} (hX : (Set.InjOn Prod.fst (X : Set (ℝ × ℝ)) ∧ ∀ a_g ∈ X, ∀ b_g ∈ X, ∀ c_g ∈ X, a_g.1 < b_g.1 → b_g.1 < c_g.1 → orient a_g b_g c_g ≠ 0))
    {S : ℕ → Finset (ℝ × ℝ)}
    (hS : (∀ i < 2 * k + 6, S i ⊆ X ∧ L < (S i).card) ∧
      (∀ i < 2 * k + 6, ∀ j < 2 * k + 6, i ≠ j → Disjoint (S i) (S j)) ∧
      ∀ i j l, i < j → j < l → l < 2 * k + 6 →
        ∀ p ∈ S i, ∀ q ∈ S j, ∀ r ∈ S l, orient p q r < 0) :
    ∃ (left right : ℕ → (ℝ × ℝ)) (part : ℕ → Finset (ℝ × ℝ)),
      (∀ i < k, part i ⊆ X) ∧
      (∀ i < k, ((left i) ≠ (right i) ∧ (∀ p_k ∈ (part i), 0 < orient (left i) (right i) p_k) ∧ (∀ p_k ∈ (part i), ∀ q_k ∈ (part i), p_k ≠ q_k → orient p_k q_k (left i) ≠ 0) ∧ (∀ p_k ∈ (part i), ∀ q_k ∈ (part i), p_k ≠ q_k → orient p_k q_k (right i) ≠ 0) ∧ (∀ p_k ∈ (part i), ∀ q_k ∈ (part i), ∀ r_k ∈ (part i), p_k ≠ q_k → q_k ≠ r_k → p_k ≠ r_k → orient p_k q_k r_k ≠ 0))) ∧
      (∀ i < k, ∀ j < k, i ≠ j → Disjoint (part i) (part j)) ∧
      (∀ i, i + 1 < k → ∀ p ∈ part i, ∀ r ∈ part (i + 1),
        0 < orient p (left i) r ∧ orient p r (right i) < 0) ∧
      (∀ i, i + 1 < k → ∀ p ∈ part (i + 1), ∀ r ∈ part i,
        orient p (left (i + 1)) r < 0 ∧ 0 < orient p r (right (i + 1))) ∧
      (∀ i < k, ∀ j < k, (i + 1 < j ∨ j + 1 < i) →
        ∀ p ∈ part i, ∀ r ∈ part j, 0 < orient p (left i) r ∧ 0 < orient p r (right i)) ∧
      (∀ i j l, i < j → j < l → l < k →
        ∀ p ∈ part i, ∀ q ∈ part j, ∀ r ∈ part l, orient p q r < 0) ∧
      (∀ i < k, L < (part i).card) := by
  obtain ⟨hsub, hdis, hcw⟩ := hS
  have hne : ∀ n, ∃ g : (ℝ × ℝ), n < 2 * k + 6 → g ∈ S n := by
    intro n
    by_cases hn : n < 2 * k + 6
    · obtain ⟨g, hg⟩ := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le L) (hsub n hn).2)
      exact ⟨g, fun _ => hg⟩
    · exact ⟨(0, 0), fun h => (hn h).elim⟩
  choose g hg using hne
  have cw : ∀ {i j l : ℕ} {p q r : (ℝ × ℝ)}, p ∈ S i → q ∈ S j → r ∈ S l →
      i < j → j < l → l < 2 * k + 6 → orient p q r < 0 :=
    fun hp hq hr hij hjl hl => hcw _ _ _ hij hjl hl _ hp _ hq _ hr
  refine ⟨fun i => g (2 * i + 1), fun i => g (2 * i + 7), fun i => S (2 * i + 4),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact (hsub _ (by omega)).1
  · intro i hi
    have hl := hg (2 * i + 1) (by omega)
    have hr := hg (2 * i + 7) (by omega)
    have hside : ∀ p ∈ S (2 * i + 4), 0 < orient (g (2 * i + 1)) (g (2 * i + 7)) p := by
      intro p hp
      have h := cw hl hp hr (by omega) (by omega) (by omega)
      rw [(orient_swap_last (orient := orient))]
      linarith
    have hab : g (2 * i + 1) ≠ g (2 * i + 7) := by
      intro he
      obtain ⟨p, hp⟩ := Finset.card_pos.mp
        (lt_of_le_of_lt (Nat.zero_le L) (hsub (2 * i + 4) (by omega)).2)
      have h := hside p hp
      rw [he, hO.out] at h
      ring_nf at h
      exact lt_irrefl _ h
    exact pocket_of_general hX (hsub _ (by omega)).1 ((hsub _ (by omega)).1 hl)
      ((hsub _ (by omega)).1 hr) hab hside
  · intro i hi j hj hij
    exact hdis _ (by omega) _ (by omega) (by omega)
  · intro i hi p hp r hr
    have hl := hg (2 * i + 1) (by omega)
    have hR := hg (2 * i + 7) (by omega)
    constructor
    · have h := cw hl hp hr (by omega) (by omega) (by omega)
      rw [(orient_flip (orient := orient))]
      linarith
    · exact cw hp hr hR (by omega) (by omega) (by omega)
  · intro i hi p hp r hr
    have hl := hg (2 * (i + 1) + 1) (by omega)
    have hR := hg (2 * (i + 1) + 7) (by omega)
    constructor
    · rw [(orient_cycle (orient := orient))]
      exact cw hl hr hp (by omega) (by omega) (by omega)
    · have h := cw hr hp hR (by omega) (by omega) (by omega)
      rw [(orient_flip (orient := orient))]
      linarith
  · intro i hi j hj hij p hp r hr
    have hl := hg (2 * i + 1) (by omega)
    have hR := hg (2 * i + 7) (by omega)
    rcases hij with hij | hij
    · constructor
      · have h := cw hl hp hr (by omega) (by omega) (by omega)
        rw [(orient_flip (orient := orient))]
        linarith
      · have h := cw hp hR hr (by omega) (by omega) (by omega)
        rw [(orient_swap_last (orient := orient))]
        linarith
    · constructor
      · have h := cw hr hl hp (by omega) (by omega) (by omega)
        rw [(orient_reverse (orient := orient))]
        linarith
      · have h := cw hr hp hR (by omega) (by omega) (by omega)
        rw [(orient_flip (orient := orient))]
        linarith
  · intro i j l hij hjl hl p hp q hq r hr
    exact cw hp hq hr (by omega) (by omega) (by omega)
  · intro i hi
    exact (hsub _ (by omega)).2

/-- A block of consecutive chain pockets forces a join. In the other case, choose an
outward cap from each block, leaving one unused pocket between blocks. -/
theorem convex_of_large_layout {X : Finset (ℝ × ℝ)} {T R s n d : ℕ}
    (left right : ℕ → (ℝ × ℝ)) (part : ℕ → Finset (ℝ × ℝ))
    (Psubset : ∀ i < T * (R + 2), part i ⊆ X)
    (Ppocket : ∀ i < T * (R + 2), ((left i) ≠ (right i) ∧ (∀ p_k ∈ (part i), 0 < orient (left i) (right i) p_k) ∧ (∀ p_k ∈ (part i), ∀ q_k ∈ (part i), p_k ≠ q_k → orient p_k q_k (left i) ≠ 0) ∧ (∀ p_k ∈ (part i), ∀ q_k ∈ (part i), p_k ≠ q_k → orient p_k q_k (right i) ≠ 0) ∧ (∀ p_k ∈ (part i), ∀ q_k ∈ (part i), ∀ r_k ∈ (part i), p_k ≠ q_k → q_k ≠ r_k → p_k ≠ r_k → orient p_k q_k r_k ≠ 0)))
    (Pdisjoint : ∀ i < T * (R + 2), ∀ j < T * (R + 2), i ≠ j → Disjoint (part i) (part j))
    (Pfollowing : ∀ i, i + 1 < T * (R + 2) → ∀ p ∈ part i, ∀ r ∈ part (i + 1),
      0 < orient p (left i) r ∧ orient p r (right i) < 0)
    (Ppreceding : ∀ i, i + 1 < T * (R + 2) → ∀ p ∈ part (i + 1), ∀ r ∈ part i,
      orient p (left (i + 1)) r < 0 ∧ 0 < orient p r (right (i + 1)))
    (Psector : ∀ i < T * (R + 2), ∀ j < T * (R + 2), (i + 1 < j ∨ j + 1 < i) →
      ∀ p ∈ part i, ∀ r ∈ part j, 0 < orient p (left i) r ∧ 0 < orient p r (right i))
    (Pclockwise : ∀ i j l, i < j → j < l → l < T * (R + 2) →
      ∀ p ∈ part i, ∀ q ∈ part j, ∀ r ∈ part l, orient p q r < 0)
    (hr : n ≤ R * (d + 1))
    (ht : n ≤ T * (s + 2))
    (hbig : ∀ i < T * (R + 2), (2 ^ (n + d) + 1) * (s + n).choose s < (part i).card) :
    ∃ Y ⊆ X, Y.card = n ∧ (∀ p_c ∈ Y, ∃ u_c v_c : ℝ, ∀ q_c ∈ Y, q_c ≠ p_c → u_c * p_c.1 + v_c * p_c.2 < u_c * q_c.1 + v_c * q_c.2) := by
  classical
  by_contra hn
  let M (i : ℕ) := ∃ B ⊆ part i, 2 ^ (n + d) < B.card ∧ (∀ p_m ∈ B, ∀ q_m ∈ B, ((((((right i).1 - (left i).1) * (p_m.1 - (left i).1) + ((right i).2 - (left i).2) * (p_m.2 - (left i).2)) / orient (left i) (right i) p_m, ((((right i).1 - (left i).1)^2 + ((right i).2 - (left i).2)^2) - (((right i).1 - (left i).1) * (p_m.1 - (left i).1) + ((right i).2 - (left i).2) * (p_m.2 - (left i).2))) / orient (left i) (right i) p_m) : ℝ × ℝ)).1 < ((((((right i).1 - (left i).1) * (q_m.1 - (left i).1) + ((right i).2 - (left i).2) * (q_m.2 - (left i).2)) / orient (left i) (right i) q_m, ((((right i).1 - (left i).1)^2 + ((right i).2 - (left i).2)^2) - (((right i).1 - (left i).1) * (q_m.1 - (left i).1) + ((right i).2 - (left i).2) * (q_m.2 - (left i).2))) / orient (left i) (right i) q_m) : ℝ × ℝ)).1 → ((((((right i).1 - (left i).1) * (p_m.1 - (left i).1) + ((right i).2 - (left i).2) * (p_m.2 - (left i).2)) / orient (left i) (right i) p_m, ((((right i).1 - (left i).1)^2 + ((right i).2 - (left i).2)^2) - (((right i).1 - (left i).1) * (p_m.1 - (left i).1) + ((right i).2 - (left i).2) * (p_m.2 - (left i).2))) / orient (left i) (right i) p_m) : ℝ × ℝ)).2 < ((((((right i).1 - (left i).1) * (q_m.1 - (left i).1) + ((right i).2 - (left i).2) * (q_m.2 - (left i).2)) / orient (left i) (right i) q_m, ((((right i).1 - (left i).1)^2 + ((right i).2 - (left i).2)^2) - (((right i).1 - (left i).1) * (q_m.1 - (left i).1) + ((right i).2 - (left i).2) * (q_m.2 - (left i).2))) / orient (left i) (right i) q_m) : ℝ × ℝ)).2)
  let A (i : ℕ) := ∃ B ⊆ part i, B.card = s + 2 ∧
    (∀ p_t ∈ B, ∀ q_t ∈ B, ∀ r_t ∈ B, ((((((right i).1 - (left i).1) * (p_t.1 - (left i).1) + ((right i).2 - (left i).2) * (p_t.2 - (left i).2)) / orient (left i) (right i) p_t, ((((right i).1 - (left i).1)^2 + ((right i).2 - (left i).2)^2) - (((right i).1 - (left i).1) * (p_t.1 - (left i).1) + ((right i).2 - (left i).2) * (p_t.2 - (left i).2))) / orient (left i) (right i) p_t) : ℝ × ℝ)).1 < ((((((right i).1 - (left i).1) * (q_t.1 - (left i).1) + ((right i).2 - (left i).2) * (q_t.2 - (left i).2)) / orient (left i) (right i) q_t, ((((right i).1 - (left i).1)^2 + ((right i).2 - (left i).2)^2) - (((right i).1 - (left i).1) * (q_t.1 - (left i).1) + ((right i).2 - (left i).2) * (q_t.2 - (left i).2))) / orient (left i) (right i) q_t) : ℝ × ℝ)).1 → ((((((right i).1 - (left i).1) * (q_t.1 - (left i).1) + ((right i).2 - (left i).2) * (q_t.2 - (left i).2)) / orient (left i) (right i) q_t, ((((right i).1 - (left i).1)^2 + ((right i).2 - (left i).2)^2) - (((right i).1 - (left i).1) * (q_t.1 - (left i).1) + ((right i).2 - (left i).2) * (q_t.2 - (left i).2))) / orient (left i) (right i) q_t) : ℝ × ℝ)).1 < ((((((right i).1 - (left i).1) * (r_t.1 - (left i).1) + ((right i).2 - (left i).2) * (r_t.2 - (left i).2)) / orient (left i) (right i) r_t, ((((right i).1 - (left i).1)^2 + ((right i).2 - (left i).2)^2) - (((right i).1 - (left i).1) * (r_t.1 - (left i).1) + ((right i).2 - (left i).2) * (r_t.2 - (left i).2))) / orient (left i) (right i) r_t) : ℝ × ℝ)).1 → (if false then 0 < orient p_t q_t r_t else orient p_t q_t r_t < 0)) ∧ (∀ p_m ∈ B, ∀ q_m ∈ B, ((((((right i).1 - (left i).1) * (p_m.1 - (left i).1) + ((right i).2 - (left i).2) * (p_m.2 - (left i).2)) / orient (left i) (right i) p_m, ((((right i).1 - (left i).1)^2 + ((right i).2 - (left i).2)^2) - (((right i).1 - (left i).1) * (p_m.1 - (left i).1) + ((right i).2 - (left i).2) * (p_m.2 - (left i).2))) / orient (left i) (right i) p_m) : ℝ × ℝ)).1 < ((((((right i).1 - (left i).1) * (q_m.1 - (left i).1) + ((right i).2 - (left i).2) * (q_m.2 - (left i).2)) / orient (left i) (right i) q_m, ((((right i).1 - (left i).1)^2 + ((right i).2 - (left i).2)^2) - (((right i).1 - (left i).1) * (q_m.1 - (left i).1) + ((right i).2 - (left i).2) * (q_m.2 - (left i).2))) / orient (left i) (right i) q_m) : ℝ × ℝ)).1 → ((((((right i).1 - (left i).1) * (q_m.1 - (left i).1) + ((right i).2 - (left i).2) * (q_m.2 - (left i).2)) / orient (left i) (right i) q_m, ((((right i).1 - (left i).1)^2 + ((right i).2 - (left i).2)^2) - (((right i).1 - (left i).1) * (q_m.1 - (left i).1) + ((right i).2 - (left i).2) * (q_m.2 - (left i).2))) / orient (left i) (right i) q_m) : ℝ × ℝ)).2 < ((((((right i).1 - (left i).1) * (p_m.1 - (left i).1) + ((right i).2 - (left i).2) * (p_m.2 - (left i).2)) / orient (left i) (right i) p_m, ((((right i).1 - (left i).1)^2 + ((right i).2 - (left i).2)^2) - (((right i).1 - (left i).1) * (p_m.1 - (left i).1) + ((right i).2 - (left i).2) * (p_m.2 - (left i).2))) / orient (left i) (right i) p_m) : ℝ × ℝ)).2)
  let base (j : ℕ) := j * (R + 2)
  have hidx {j i : ℕ} (hj : j < T) (hi : i ≤ R) : base j + i < T * (R + 2) := by
    have h := Nat.mul_le_mul_right (R + 2) (show j + 1 ≤ T by omega)
    rw [Nat.add_mul, one_mul] at h
    change j * (R + 2) + i < _
    omega
  have hlocal (i : ℕ) (hi : i < T * (R + 2)) : M i ∨ A i := by
    rcases pocket_chain_or_outward (Ppocket i hi) (Nat.succ_pos (2 ^ (n + d)))
      (hbig i hi) with h | ⟨B, hB, hc, hm⟩
    · obtain ⟨B, hB, hc, hm⟩ := h
      exact Or.inl ⟨B, hB, by omega, hm⟩
    · rcases pocket_outward_or_convex (hB.trans (Psubset i hi)) (pocket_mono (Ppocket i hi) hB) hm hc
        with ⟨C, hC, hcc, hct, hca⟩ | h
      · exact Or.inr ⟨C, hC.trans hB, hcc, hct, hca⟩
      · exact (hn h).elim
  have runImpossible (j : ℕ) (hj : j < T) : ¬ ∀ i ≤ R, M (base j + i) := by
    intro hall
    have hx (i : ℕ) : ∃ B : Finset (ℝ × ℝ), i ≤ R →
        B ⊆ part (base j + i) ∧ 2 ^ (n + d) < B.card ∧
          (∀ p_m ∈ B, ∀ q_m ∈ B, ((((((right (base j + i)).1 - (left (base j + i)).1) * (p_m.1 - (left (base j + i)).1) + ((right (base j + i)).2 - (left (base j + i)).2) * (p_m.2 - (left (base j + i)).2)) / orient (left (base j + i)) (right (base j + i)) p_m, ((((right (base j + i)).1 - (left (base j + i)).1)^2 + ((right (base j + i)).2 - (left (base j + i)).2)^2) - (((right (base j + i)).1 - (left (base j + i)).1) * (p_m.1 - (left (base j + i)).1) + ((right (base j + i)).2 - (left (base j + i)).2) * (p_m.2 - (left (base j + i)).2))) / orient (left (base j + i)) (right (base j + i)) p_m) : ℝ × ℝ)).1 < ((((((right (base j + i)).1 - (left (base j + i)).1) * (q_m.1 - (left (base j + i)).1) + ((right (base j + i)).2 - (left (base j + i)).2) * (q_m.2 - (left (base j + i)).2)) / orient (left (base j + i)) (right (base j + i)) q_m, ((((right (base j + i)).1 - (left (base j + i)).1)^2 + ((right (base j + i)).2 - (left (base j + i)).2)^2) - (((right (base j + i)).1 - (left (base j + i)).1) * (q_m.1 - (left (base j + i)).1) + ((right (base j + i)).2 - (left (base j + i)).2) * (q_m.2 - (left (base j + i)).2))) / orient (left (base j + i)) (right (base j + i)) q_m) : ℝ × ℝ)).1 → ((((((right (base j + i)).1 - (left (base j + i)).1) * (p_m.1 - (left (base j + i)).1) + ((right (base j + i)).2 - (left (base j + i)).2) * (p_m.2 - (left (base j + i)).2)) / orient (left (base j + i)) (right (base j + i)) p_m, ((((right (base j + i)).1 - (left (base j + i)).1)^2 + ((right (base j + i)).2 - (left (base j + i)).2)^2) - (((right (base j + i)).1 - (left (base j + i)).1) * (p_m.1 - (left (base j + i)).1) + ((right (base j + i)).2 - (left (base j + i)).2) * (p_m.2 - (left (base j + i)).2))) / orient (left (base j + i)) (right (base j + i)) p_m) : ℝ × ℝ)).2 < ((((((right (base j + i)).1 - (left (base j + i)).1) * (q_m.1 - (left (base j + i)).1) + ((right (base j + i)).2 - (left (base j + i)).2) * (q_m.2 - (left (base j + i)).2)) / orient (left (base j + i)) (right (base j + i)) q_m, ((((right (base j + i)).1 - (left (base j + i)).1)^2 + ((right (base j + i)).2 - (left (base j + i)).2)^2) - (((right (base j + i)).1 - (left (base j + i)).1) * (q_m.1 - (left (base j + i)).1) + ((right (base j + i)).2 - (left (base j + i)).2) * (q_m.2 - (left (base j + i)).2))) / orient (left (base j + i)) (right (base j + i)) q_m) : ℝ × ℝ)).2) := by
      by_cases hi : i ≤ R
      · obtain ⟨B, hB, hc, hm⟩ := hall i hi
        exact ⟨B, fun _ => ⟨hB, hc, hm⟩⟩
      · exact ⟨∅, fun h => (hi h).elim⟩
    choose B hB using hx
    apply hn
    refine convex_from_chain_run (orient := orient) (fun i => left (base j + i)) (fun i => right (base j + i))
      B (fun i hi => (hB i hi).1.trans (Psubset _ (hidx hj hi)))
      (fun i hi => pocket_mono (Ppocket _ (hidx hj hi)) (hB i hi).1)
      (fun i hi => (hB i hi).2.2) (fun i hi => (hB i hi).2.1) ?_ ?_ ?_ hr
    · intro i hi
      exact (Pdisjoint _ (hidx hj hi.le) _ (hidx hj (show i + 1 ≤ R by omega))
        (by omega)).mono (hB i hi.le).1 (hB (i + 1) (by omega)).1
    · intro i hi p hp r hr'
      exact Pfollowing (base j + i) (by simpa only [Nat.add_assoc] using hidx hj (show i + 1 ≤ R by omega)) p ((hB i hi.le).1 hp)
        r ((hB (i + 1) (by omega)).1 hr')
    · intro i hi p hp r hr'
      exact Ppreceding (base j + i) (by simpa only [Nat.add_assoc] using hidx hj (show i + 1 ≤ R by omega)) p ((hB (i + 1) (by omega)).1 hp)
        r ((hB i hi.le).1 hr')
  have hchoose (j : ℕ) : ∃ i : ℕ, ∃ B : Finset (ℝ × ℝ), j < T →
      i ≤ R ∧ B ⊆ part (base j + i) ∧ B.card = s + 2 ∧
        (∀ p_t ∈ B, ∀ q_t ∈ B, ∀ r_t ∈ B, ((((((right (base j + i)).1 - (left (base j + i)).1) * (p_t.1 - (left (base j + i)).1) + ((right (base j + i)).2 - (left (base j + i)).2) * (p_t.2 - (left (base j + i)).2)) / orient (left (base j + i)) (right (base j + i)) p_t, ((((right (base j + i)).1 - (left (base j + i)).1)^2 + ((right (base j + i)).2 - (left (base j + i)).2)^2) - (((right (base j + i)).1 - (left (base j + i)).1) * (p_t.1 - (left (base j + i)).1) + ((right (base j + i)).2 - (left (base j + i)).2) * (p_t.2 - (left (base j + i)).2))) / orient (left (base j + i)) (right (base j + i)) p_t) : ℝ × ℝ)).1 < ((((((right (base j + i)).1 - (left (base j + i)).1) * (q_t.1 - (left (base j + i)).1) + ((right (base j + i)).2 - (left (base j + i)).2) * (q_t.2 - (left (base j + i)).2)) / orient (left (base j + i)) (right (base j + i)) q_t, ((((right (base j + i)).1 - (left (base j + i)).1)^2 + ((right (base j + i)).2 - (left (base j + i)).2)^2) - (((right (base j + i)).1 - (left (base j + i)).1) * (q_t.1 - (left (base j + i)).1) + ((right (base j + i)).2 - (left (base j + i)).2) * (q_t.2 - (left (base j + i)).2))) / orient (left (base j + i)) (right (base j + i)) q_t) : ℝ × ℝ)).1 → ((((((right (base j + i)).1 - (left (base j + i)).1) * (q_t.1 - (left (base j + i)).1) + ((right (base j + i)).2 - (left (base j + i)).2) * (q_t.2 - (left (base j + i)).2)) / orient (left (base j + i)) (right (base j + i)) q_t, ((((right (base j + i)).1 - (left (base j + i)).1)^2 + ((right (base j + i)).2 - (left (base j + i)).2)^2) - (((right (base j + i)).1 - (left (base j + i)).1) * (q_t.1 - (left (base j + i)).1) + ((right (base j + i)).2 - (left (base j + i)).2) * (q_t.2 - (left (base j + i)).2))) / orient (left (base j + i)) (right (base j + i)) q_t) : ℝ × ℝ)).1 < ((((((right (base j + i)).1 - (left (base j + i)).1) * (r_t.1 - (left (base j + i)).1) + ((right (base j + i)).2 - (left (base j + i)).2) * (r_t.2 - (left (base j + i)).2)) / orient (left (base j + i)) (right (base j + i)) r_t, ((((right (base j + i)).1 - (left (base j + i)).1)^2 + ((right (base j + i)).2 - (left (base j + i)).2)^2) - (((right (base j + i)).1 - (left (base j + i)).1) * (r_t.1 - (left (base j + i)).1) + ((right (base j + i)).2 - (left (base j + i)).2) * (r_t.2 - (left (base j + i)).2))) / orient (left (base j + i)) (right (base j + i)) r_t) : ℝ × ℝ)).1 → (if false then 0 < orient p_t q_t r_t else orient p_t q_t r_t < 0)) ∧
        (∀ p_m ∈ B, ∀ q_m ∈ B, ((((((right (base j + i)).1 - (left (base j + i)).1) * (p_m.1 - (left (base j + i)).1) + ((right (base j + i)).2 - (left (base j + i)).2) * (p_m.2 - (left (base j + i)).2)) / orient (left (base j + i)) (right (base j + i)) p_m, ((((right (base j + i)).1 - (left (base j + i)).1)^2 + ((right (base j + i)).2 - (left (base j + i)).2)^2) - (((right (base j + i)).1 - (left (base j + i)).1) * (p_m.1 - (left (base j + i)).1) + ((right (base j + i)).2 - (left (base j + i)).2) * (p_m.2 - (left (base j + i)).2))) / orient (left (base j + i)) (right (base j + i)) p_m) : ℝ × ℝ)).1 < ((((((right (base j + i)).1 - (left (base j + i)).1) * (q_m.1 - (left (base j + i)).1) + ((right (base j + i)).2 - (left (base j + i)).2) * (q_m.2 - (left (base j + i)).2)) / orient (left (base j + i)) (right (base j + i)) q_m, ((((right (base j + i)).1 - (left (base j + i)).1)^2 + ((right (base j + i)).2 - (left (base j + i)).2)^2) - (((right (base j + i)).1 - (left (base j + i)).1) * (q_m.1 - (left (base j + i)).1) + ((right (base j + i)).2 - (left (base j + i)).2) * (q_m.2 - (left (base j + i)).2))) / orient (left (base j + i)) (right (base j + i)) q_m) : ℝ × ℝ)).1 → ((((((right (base j + i)).1 - (left (base j + i)).1) * (q_m.1 - (left (base j + i)).1) + ((right (base j + i)).2 - (left (base j + i)).2) * (q_m.2 - (left (base j + i)).2)) / orient (left (base j + i)) (right (base j + i)) q_m, ((((right (base j + i)).1 - (left (base j + i)).1)^2 + ((right (base j + i)).2 - (left (base j + i)).2)^2) - (((right (base j + i)).1 - (left (base j + i)).1) * (q_m.1 - (left (base j + i)).1) + ((right (base j + i)).2 - (left (base j + i)).2) * (q_m.2 - (left (base j + i)).2))) / orient (left (base j + i)) (right (base j + i)) q_m) : ℝ × ℝ)).2 < ((((((right (base j + i)).1 - (left (base j + i)).1) * (p_m.1 - (left (base j + i)).1) + ((right (base j + i)).2 - (left (base j + i)).2) * (p_m.2 - (left (base j + i)).2)) / orient (left (base j + i)) (right (base j + i)) p_m, ((((right (base j + i)).1 - (left (base j + i)).1)^2 + ((right (base j + i)).2 - (left (base j + i)).2)^2) - (((right (base j + i)).1 - (left (base j + i)).1) * (p_m.1 - (left (base j + i)).1) + ((right (base j + i)).2 - (left (base j + i)).2) * (p_m.2 - (left (base j + i)).2))) / orient (left (base j + i)) (right (base j + i)) p_m) : ℝ × ℝ)).2) := by
    by_cases hj : j < T
    · obtain ⟨i, hi, hni⟩ := not_forall.mp (runImpossible j hj) |>.imp fun _ h => Classical.not_imp.mp h
      rcases hlocal _ (hidx hj hi) with hm | ⟨B, hB, hc, ht, ha⟩
      · exact (hni hm).elim
      · exact ⟨i, B, fun _ => ⟨hi, hB, hc, ht, ha⟩⟩
    · exact ⟨0, ∅, fun h => (hj h).elim⟩
  choose offset B hB using hchoose
  let f (i : ℕ) := base i + offset i
  have hf {i : ℕ} (hi : i < T) : f i < T * (R + 2) := hidx hi (hB i hi).1
  have hsep {i j : ℕ} (hi : i < T) (hij : i < j) : f i + 1 < f j := by
    have h := Nat.mul_le_mul_right (R + 2) (show i + 1 ≤ j by omega)
    rw [Nat.add_mul, one_mul] at h
    have hi' := (hB i hi).1
    dsimp [f, base]
    omega
  apply hn
  refine convex_from_outward_covers (orient := orient) (range T) B (fun i => left (f i))
    (fun i => right (f i)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i hi j hj hne
    have hi' := mem_range.mp hi
    have hj' := mem_range.mp hj
    have h' : f i ≠ f j := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact (lt_of_le_of_lt (Nat.le_succ _) (hsep hi' h)).ne
      · exact (lt_of_le_of_lt (Nat.le_succ _) (hsep hj' h)).ne'
    exact (Pdisjoint _ (hf hi') _ (hf hj') h').mono (hB i hi').2.1 (hB j hj').2.1
  · intro i hi
    have hi' := mem_range.mp hi
    exact (hB i hi').2.1.trans (Psubset _ (hf hi'))
  · intro i hi
    have hi' := mem_range.mp hi
    exact pocket_mono (Ppocket _ (hf hi')) (hB i hi').2.1
  · exact fun i hi => (hB i (mem_range.mp hi)).2.2.2.2
  · exact fun i hi => (hB i (mem_range.mp hi)).2.2.2.1
  · intro i hi j hj hne p hp r hr'
    have hi' := mem_range.mp hi
    have hj' := mem_range.mp hj
    have h : f i + 1 < f j ∨ f j + 1 < f i :=
      (lt_or_gt_of_ne hne).imp (hsep hi') (hsep hj')
    exact Psector _ (hf hi') _ (hf hj') h p ((hB i hi').2.1 hp) r ((hB j hj').2.1 hr')
  · intro i hi j hj l hl hij hjl p hp q hq r hr'
    have hi' := mem_range.mp hi
    have hj' := mem_range.mp hj
    have hl' := mem_range.mp hl
    exact Pclockwise _ _ _ (lt_of_le_of_lt (Nat.le_succ _) (hsep hi' hij))
      (lt_of_le_of_lt (Nat.le_succ _) (hsep hj' hjl)) (hf hl')
      p ((hB i hi').2.1 hp) q ((hB j hj').2.1 hq) r ((hB l hl').2.1 hr')
  · calc
      n ≤ T * (s + 2) := ht
      _ = ∑ i ∈ range T, (s + 2) := by simp
      _ = ∑ i ∈ range T, (B i).card :=
        Finset.sum_congr rfl fun i hi => (hB i (mem_range.mp hi)).2.2.1.symm

theorem finite_suk_bound
    (hPV : ∀ m : ℕ, ∃ C : ℕ, ∀ (X : Finset (ℝ × ℝ)) (L : ℕ), (Set.InjOn Prod.fst (X : Set (ℝ × ℝ)) ∧ ∀ a_g ∈ X, ∀ b_g ∈ X, ∀ c_g ∈ X, a_g.1 < b_g.1 → b_g.1 < c_g.1 → orient a_g b_g c_g ≠ 0) →
      C * (L + 1) < X.card →
      ∃ S : ℕ → Finset (ℝ × ℝ), (∀ i < m, S i ⊆ X ∧ L < (S i).card) ∧
        (∀ i < m, ∀ j < m, i ≠ j → Disjoint (S i) (S j)) ∧
        ∀ i j l, i < j → j < l → l < m →
          ∀ p ∈ S i, ∀ q ∈ S j, ∀ r ∈ S l, orient p q r < 0)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ X : Finset (ℝ × ℝ), (Set.InjOn Prod.fst (X : Set (ℝ × ℝ)) ∧ ∀ a_g ∈ X, ∀ b_g ∈ X, ∀ c_g ∈ X, a_g.1 < b_g.1 → b_g.1 < c_g.1 → orient a_g b_g c_g ≠ 0) →
      (2 : ℝ) ^ ((1 + δ) * n) < (X.card : ℝ) →
      ∃ Y ⊆ X, Y.card = n ∧ (∀ p_c ∈ Y, ∃ u_c v_c : ℝ, ∀ q_c ∈ Y, q_c ≠ p_c → u_c * p_c.1 + v_c * p_c.2 < u_c * q_c.1 + v_c * q_c.2) := by
  let η := δ / 4
  have hη : 0 < η := by dsimp [η]; linarith
  obtain ⟨T, hT, hbin⟩ := sparse_binomial_bound hη
  obtain ⟨R, hR⟩ := exists_nat_ge (1 / η)
  obtain ⟨C, hC⟩ := hPV (2 * (T * (R + 2)) + 6)
  obtain ⟨K, hK⟩ := exists_nat_ge (((C : ℝ) + 2) / η)
  filter_upwards [eventually_ge_atTop K] with n hn
  intro X hX hx
  let d := ⌊η * (n : ℝ)⌋₊
  let s := n / T
  let L := (2 ^ (n + d) + 1) * (s + n).choose s
  have hηn : 0 ≤ η * (n : ℝ) := by positivity
  have hd : (d : ℝ) ≤ η * n := Nat.floor_le hηn
  have hd' : η * (n : ℝ) < (d : ℝ) + 1 := Nat.lt_floor_add_one _
  have hr : n ≤ R * (d + 1) := by
    have hR' : 1 ≤ (R : ℝ) * η := by linarith only [(div_le_iff₀ hη).mp hR]
    have h₁ := mul_le_mul_of_nonneg_right hR' (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have h₂ := mul_le_mul_of_nonneg_left hd'.le (Nat.cast_nonneg R : (0 : ℝ) ≤ R)
    have h₃ : (n : ℝ) ≤ (R : ℝ) * ((d : ℝ) + 1) := by nlinarith only [h₁, h₂]
    exact_mod_cast h₃
  have ht : n ≤ T * (s + 2) := by
    have hn' := Nat.mod_add_div n T
    have hm := Nat.mod_lt n hT
    rw [Nat.mul_add]
    change n ≤ T * (n / T) + T * 2
    omega
  have hb : (1 : ℝ) ≤ 2 := by norm_num
  have hpow (m : ℕ) : ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ (m : ℝ) := by
    rw [Real.rpow_natCast]
    norm_num
  have hfirst : ((2 ^ (n + d) + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((1 + η) * n + 1) := by
    have h₁ : 2 ^ (n + d) + 1 ≤ (2 : ℕ) ^ (n + d + 1) := by
      rw [pow_succ]
      have hp : 0 < (2 : ℕ) ^ (n + d) := by positivity
      omega
    have hh : ((2 ^ (n + d) + 1 : ℕ) : ℝ) ≤ ((2 ^ (n + d + 1) : ℕ) : ℝ) := by
      exact_mod_cast h₁
    refine hh.trans ?_
    rw [hpow]
    apply Real.rpow_le_rpow_of_exponent_le hb
    push_cast
    nlinarith only [hd]
  have hL : (L : ℝ) ≤ (2 : ℝ) ^ ((1 + 2 * η) * n + 1) := by
    dsimp only [L]
    rw [Nat.cast_mul]
    calc
      _ ≤ (2 : ℝ) ^ ((1 + η) * n + 1) * (2 : ℝ) ^ (η * n) :=
        mul_le_mul hfirst (hbin n) (Nat.cast_nonneg _) (by positivity)
      _ = _ := by rw [← Real.rpow_add (by norm_num)]; congr 1; ring
  let e : ℝ := (1 + 2 * η) * n + 1
  have he : 1 ≤ (2 : ℝ) ^ e := Real.one_le_rpow hb (by dsimp [e]; positivity)
  have hplus : (L : ℝ) + 1 ≤ (2 : ℝ) ^ (e + 1) := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one]
    change (L : ℝ) ≤ 2 ^ e at hL
    linarith only [hL, he]
  have hconst : (C : ℝ) ≤ (2 : ℝ) ^ (C : ℝ) := by
    rw [← hpow]
    exact_mod_cast Nat.lt_two_pow_self.le
  have hlarge : C * (L + 1) < X.card := by
    have hc₁ : (K : ℝ) ≤ n := by exact_mod_cast hn
    have hc₂ : (C : ℝ) + 2 ≤ η * (n : ℝ) := by
      linarith only [(div_le_iff₀ hη).mp (hK.trans hc₁)]
    have hcalc : (C : ℝ) * ((L : ℝ) + 1) < (X.card : ℝ) := by
      calc
        _ ≤ (2 : ℝ) ^ (C : ℝ) * (2 : ℝ) ^ (e + 1) :=
          mul_le_mul hconst hplus (by positivity) (by positivity)
        _ = (2 : ℝ) ^ ((C : ℝ) + (e + 1)) := (Real.rpow_add (by norm_num) _ _).symm
        _ ≤ (2 : ℝ) ^ ((1 + δ) * n) := by
          apply Real.rpow_le_rpow_of_exponent_le hb
          have hδeq : δ = 4 * η := by dsimp [η]; ring
          rw [hδeq]
          dsimp [e]
          nlinarith only [hc₂, hηn]
        _ < _ := hx
    exact_mod_cast hcalc
  obtain ⟨S, hS⟩ := hC X L hX hlarge
  obtain ⟨left, right, part, h1, h2, h3, h4, h5, h6, h7, h8⟩ := layout_of_family hX hS
  exact convex_of_large_layout left right part h1 h2 h3 h4 h5 h6 h7 hr ht h8

end SukOdd

/-- Por-Valtr positive-fraction Erdos-Szekeres (clockwise transversals), X of even size. -/
def H1 : Prop :=
  ∀ m : ℕ, ∃ C : ℕ, ∀ (X : Finset (ℝ × ℝ)) (L : ℕ), Even X.card →
    Set.InjOn Prod.fst (X : Set (ℝ × ℝ)) →
    (∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a.1 < b.1 → b.1 < c.1 →
      (b.1 - a.1) * (c.2 - b.2) - (b.2 - a.2) * (c.1 - b.1) ≠ 0) →
    C * (L + 1) < X.card →
    ∃ S : ℕ → Finset (ℝ × ℝ), (∀ i < m, S i ⊆ X ∧ L < (S i).card) ∧
      (∀ i < m, ∀ j < m, i ≠ j → Disjoint (S i) (S j)) ∧
      ∀ i j l, i < j → j < l → l < m → ∀ p ∈ S i, ∀ q ∈ S j, ∀ r ∈ S l,
        (q.1 - p.1) * (r.2 - q.2) - (q.2 - p.2) * (r.1 - q.1) < 0

/-- Por-Valtr positive-fraction Erdos-Szekeres (clockwise transversals), X of odd size. -/
def H2 : Prop :=
  ∀ m : ℕ, ∃ C : ℕ, ∀ (X : Finset (ℝ × ℝ)) (L : ℕ), Odd X.card →
    Set.InjOn Prod.fst (X : Set (ℝ × ℝ)) →
    (∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a.1 < b.1 → b.1 < c.1 →
      (b.1 - a.1) * (c.2 - b.2) - (b.2 - a.2) * (c.1 - b.1) ≠ 0) →
    C * (L + 1) < X.card →
    ∃ S : ℕ → Finset (ℝ × ℝ), (∀ i < m, S i ⊆ X ∧ L < (S i).card) ∧
      (∀ i < m, ∀ j < m, i ≠ j → Disjoint (S i) (S j)) ∧
      ∀ i j l, i < j → j < l → l < m → ∀ p ∈ S i, ∀ q ∈ S j, ∀ r ∈ S l,
        (q.1 - p.1) * (r.2 - q.2) - (q.2 - p.2) * (r.1 - q.1) < 0

theorem main : H1 → H2 → OMA.R_Erdos107_variants_su_bound_R1.H2 := by
  intro h1 h2
  have hfin := SukOdd.finite_suk_bound
    (orient := fun a b c : ℝ × ℝ => (b.1 - a.1) * (c.2 - b.2) - (b.2 - a.2) * (c.1 - b.1))
    (hO := ⟨fun _ _ _ => rfl⟩) (by
      intro m
      obtain ⟨C1, hC1⟩ := h1 m
      obtain ⟨C2, hC2⟩ := h2 m
      refine ⟨max C1 C2, fun X L hX hc => ?_⟩
      rcases Nat.even_or_odd X.card with he | ho
      · exact hC1 X L he hX.1 hX.2
          (lt_of_le_of_lt (Nat.mul_le_mul_right _ (le_max_left _ _)) hc)
      · exact hC2 X L ho hX.1 hX.2
          (lt_of_le_of_lt (Nat.mul_le_mul_right _ (le_max_right _ _)) hc))
  intro ε hε _
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨K, hK⟩ := exists_nat_ge (1 / δ)
  filter_upwards [hfin δ hδ, eventually_ge_atTop K] with n hfinite hn
  intro _
  let x := (2 : ℝ) ^ ((1 + δ) * n)
  have hx : 1 ≤ x := Real.one_le_rpow (by norm_num) (by positivity)
  have hkn : (K : ℝ) ≤ n := by exact_mod_cast hn
  have hδn : 1 ≤ δ * (n : ℝ) := by
    have h := (div_le_iff₀ hδ).mp (hK.trans hkn)
    linarith
  refine ⟨⌊x⌋₊ + 1, ?_, fun X hX hi hg => ?_⟩
  · rw [Nat.cast_add, Nat.cast_one]
    calc
      (⌊x⌋₊ : ℝ) + 1 ≤ x + 1 :=
        add_le_add_left (Nat.floor_le (zero_le_one.trans hx)) 1
      _ ≤ x * 2 := by linarith
      _ = (2 : ℝ) ^ ((1 + δ) * n + 1) := by
        rw [Real.rpow_add (by norm_num), Real.rpow_one]
      _ ≤ (2 : ℝ) ^ ((1 + ε) * n) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        dsimp [δ] at hδn ⊢
        linarith only [hδn]
  · apply hfinite X ⟨hi, hg⟩
    rw [hX, Nat.cast_add, Nat.cast_one]
    exact Nat.lt_floor_add_one x

end OMA.R_Erdos107_variants_su_bound_R1_H2_R1
