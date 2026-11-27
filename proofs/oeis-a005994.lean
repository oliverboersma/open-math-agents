import OMAStatements.S_oeis_a005994
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

-- Problem: oeis-a005994 (Mathar's identity relating A005994 and zero-sum array counts A203286).
-- Credit: @Need17Bread
--
-- Subtracting total p.1 = total p.2 from weight p.1 = weight p.2 gives
--   p.1.two + 2 * p.1.three = p.2.two + 2 * p.2.three.
-- Splitting Configuration m by d = |p.2.three - p.1.three| shows that the d = 0 slice bijects
-- with nonnegative integer triples summing to at most m (size C(m + 3, 3)), and each d >= 1
-- contributes two symmetric slices bijecting with triples summing to at most m - 2 * d
-- (size C(m + 3 - 2 * d, 3) each). Finally, applying Pascal's identity twice turns
-- alkaneCount n + alkaneCount (n + 1) into a telescoping sum equal to
-- C(n + 4, 3) + 2 * sum_{d=1}^{n+1} C(n + 4 - 2 * d, 3) = arrayCount (n + 1).

namespace OeisA005994Proof

open Finset OMA.S_oeis_a005994

private instance : DecidableEq Counts := fun a b =>
  decidable_of_iff (a.one = b.one ∧ a.two = b.two ∧ a.three = b.three)
    (by cases a; cases b; simp)

private def pairsLe (M : ℕ) : Finset (ℕ × ℕ) :=
  ((range (M + 1)) ×ˢ (range (M + 1))).filter (fun p => p.1 + p.2 ≤ M)

private lemma mem_pairsLe {M : ℕ} {p : ℕ × ℕ} :
    p ∈ pairsLe M ↔ p.1 + p.2 ≤ M := by
  simp only [pairsLe, mem_filter, mem_product, mem_range]
  omega

private lemma card_pairsLe (M : ℕ) : (pairsLe M).card = (M + 2).choose 2 := by
  induction M with
  | zero =>
    have h : pairsLe 0 = {(0, 0)} := by
      ext ⟨a, b⟩
      simp only [mem_pairsLe, mem_singleton, Prod.mk.injEq]
      omega
    rw [h]; decide
  | succ M ih =>
    let diag : Finset (ℕ × ℕ) := (range (M + 2)).image (fun a => (a, M + 1 - a))
    have hsplit : pairsLe (M + 1) = pairsLe M ∪ diag := by
      ext ⟨a, b⟩
      simp only [mem_pairsLe, mem_union, diag, mem_image, mem_range, Prod.mk.injEq]
      constructor
      · intro h
        by_cases hle : a + b ≤ M
        · exact Or.inl hle
        · exact Or.inr ⟨a, by omega, rfl, by omega⟩
      · rintro (h | ⟨x, hx, rfl, rfl⟩) <;> omega
    have hdisj : Disjoint (pairsLe M) diag := by
      rw [disjoint_left]
      intro ⟨a, b⟩ h1 h2
      rw [mem_pairsLe] at h1
      simp only [diag, mem_image, mem_range, Prod.mk.injEq] at h2
      rcases h2 with ⟨x, hx, rfl, rfl⟩
      omega
    have hdiag_card : diag.card = M + 2 := by
      rw [card_image_of_injective]
      · exact card_range (M + 2)
      · intro x y hxy
        exact (Prod.mk.inj hxy).1
    rw [hsplit, card_union_of_disjoint hdisj, ih, hdiag_card]
    have h1 : (M + 2).choose 1 = M + 2 := Nat.choose_one_right (M + 2)
    have h2 : (M + 1 + 2).choose 2 = (M + 2).choose 1 + (M + 2).choose 2 :=
      Nat.choose_succ_succ (M + 2) 1
    omega

private def triplesLe (M : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((range (M + 1)) ×ˢ ((range (M + 1)) ×ˢ (range (M + 1)))).filter
    (fun t => t.1 + t.2.1 + t.2.2 ≤ M)

private lemma mem_triplesLe {M : ℕ} {t : ℕ × ℕ × ℕ} :
    t ∈ triplesLe M ↔ t.1 + t.2.1 + t.2.2 ≤ M := by
  simp only [triplesLe, mem_filter, mem_product, mem_range]
  omega

private lemma card_triplesLe (M : ℕ) : (triplesLe M).card = (M + 3).choose 3 := by
  induction M with
  | zero =>
    have h : triplesLe 0 = {(0, 0, 0)} := by
      ext ⟨a, b, c⟩
      simp only [mem_triplesLe, mem_singleton, Prod.mk.injEq]
      omega
    rw [h]; decide
  | succ M ih =>
    let face : Finset (ℕ × ℕ × ℕ) :=
      (pairsLe (M + 1)).image (fun p => (p.1, p.2, M + 1 - p.1 - p.2))
    have hsplit : triplesLe (M + 1) = triplesLe M ∪ face := by
      ext ⟨a, b, c⟩
      simp only [mem_triplesLe, mem_union, face, mem_image, mem_pairsLe, Prod.mk.injEq]
      constructor
      · intro h
        by_cases hle : a + b + c ≤ M
        · exact Or.inl hle
        · exact Or.inr ⟨(a, b), by omega, rfl, rfl, by omega⟩
      · rintro (h | ⟨⟨x, y⟩, hxy, rfl, rfl, rfl⟩) <;> omega
    have hdisj : Disjoint (triplesLe M) face := by
      rw [disjoint_left]
      intro ⟨a, b, c⟩ h1 h2
      rw [mem_triplesLe] at h1
      simp only [face, mem_image, mem_pairsLe, Prod.mk.injEq] at h2
      rcases h2 with ⟨⟨x, y⟩, hxy, rfl, rfl, rfl⟩
      dsimp only at h1 hxy
      omega
    have hface_card : face.card = (M + 3).choose 2 := by
      rw [card_image_of_injective]
      · exact card_pairsLe (M + 1)
      · intro ⟨x1, y1⟩ ⟨x2, y2⟩ h
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 h.2.1
    rw [hsplit, card_union_of_disjoint hdisj, ih, hface_card]
    have h3 : (M + 1 + 3).choose 3 = (M + 3).choose 2 + (M + 3).choose 3 :=
      Nat.choose_succ_succ (M + 3) 2
    omega

private def sliceZero (m : ℕ) : Finset (Counts × Counts) :=
  (triplesLe m).image (fun t => (⟨t.1, t.2.1, t.2.2⟩, ⟨t.1, t.2.1, t.2.2⟩))

private def slicePos (m d : ℕ) : Finset (Counts × Counts) :=
  (triplesLe (m - 2 * d)).image
    (fun t => (⟨t.1, t.2.1 + 2 * d, t.2.2⟩, ⟨t.1 + d, t.2.1, t.2.2 + d⟩))

private def sliceNeg (m d : ℕ) : Finset (Counts × Counts) :=
  (triplesLe (m - 2 * d)).image
    (fun t => (⟨t.1 + d, t.2.1, t.2.2 + d⟩, ⟨t.1, t.2.1 + 2 * d, t.2.2⟩))

private lemma card_sliceZero (m : ℕ) : (sliceZero m).card = (m + 3).choose 3 := by
  rw [sliceZero, card_image_of_injective, card_triplesLe]
  intro ⟨a1, b1, c1⟩ ⟨a2, b2, c2⟩ h
  simp only [Prod.mk.injEq, Counts.mk.injEq] at h
  exact Prod.ext h.1.1 (Prod.ext h.1.2.1 h.1.2.2)

private lemma card_slicePos (m d : ℕ) : (slicePos m d).card = (m - 2 * d + 3).choose 3 := by
  rw [slicePos, card_image_of_injective, card_triplesLe]
  intro ⟨a1, b1, c1⟩ ⟨a2, b2, c2⟩ h
  simp only [Prod.mk.injEq, Counts.mk.injEq] at h
  exact Prod.ext h.1.1 (Prod.ext (Nat.add_right_cancel h.1.2.1) h.1.2.2)

private lemma card_sliceNeg (m d : ℕ) : (sliceNeg m d).card = (m - 2 * d + 3).choose 3 := by
  rw [sliceNeg, card_image_of_injective, card_triplesLe]
  intro ⟨a1, b1, c1⟩ ⟨a2, b2, c2⟩ h
  simp only [Prod.mk.injEq, Counts.mk.injEq] at h
  exact Prod.ext h.2.1 (Prod.ext (Nat.add_right_cancel h.2.2.1) h.2.2.2)

private def allPos (m : ℕ) : Finset (Counts × Counts) :=
  (Icc 1 (m / 2)).biUnion (slicePos m)

private def allNeg (m : ℕ) : Finset (Counts × Counts) :=
  (Icc 1 (m / 2)).biUnion (sliceNeg m)

private def configFinset (m : ℕ) : Finset (Counts × Counts) :=
  sliceZero m ∪ (allPos m ∪ allNeg m)

private lemma mem_configFinset {m : ℕ} {p : Counts × Counts} :
    p ∈ configFinset m ↔ total p.1 = total p.2 ∧ weight p.1 = weight p.2 ∧ total p.1 ≤ m := by
  rcases p with ⟨⟨a1, b1, c1⟩, ⟨a2, b2, c2⟩⟩
  simp only [configFinset, allPos, allNeg, sliceZero, slicePos, sliceNeg,
    mem_union, mem_biUnion, mem_Icc, mem_image, mem_triplesLe,
    Prod.mk.injEq, Counts.mk.injEq, total, weight]
  constructor
  · rintro (⟨⟨x, y, z⟩, hxyz, h1, h2⟩ |
      ⟨d, ⟨hd1, hd2⟩, ⟨x, y, z⟩, hxyz, h1, h2⟩ |
      ⟨d, ⟨hd1, hd2⟩, ⟨x, y, z⟩, hxyz, h1, h2⟩) <;>
    · dsimp only at hxyz h1 h2
      omega
  · rintro ⟨htot, hwt, hle⟩
    rcases lt_trichotomy c1 c2 with hlt | heq | hgt
    · right; left
      refine ⟨c2 - c1, ⟨by omega, by omega⟩, (a1, b2, c1), ?_, ?_, ?_⟩ <;> dsimp only <;> omega
    · left
      refine ⟨(a1, b1, c1), ?_, ?_, ?_⟩ <;> dsimp only <;> omega
    · right; right
      refine ⟨c1 - c2, ⟨by omega, by omega⟩, (a2, b1, c2), ?_, ?_, ?_⟩ <;> dsimp only <;> omega

private lemma card_allPos (m : ℕ) :
    (allPos m).card = ∑ d ∈ Icc 1 (m / 2), (m + 3 - 2 * d).choose 3 := by
  rw [allPos, card_biUnion]
  · refine sum_congr rfl fun d hd => ?_
    rw [mem_Icc] at hd
    rw [card_slicePos]
    congr 1; omega
  · intro d1 _ d2 _ hne
    dsimp only [Function.onFun]
    rw [disjoint_left]
    intro p h1 h2
    simp only [slicePos, mem_image] at h1 h2
    rcases h1 with ⟨⟨x1, y1, z1⟩, _, rfl⟩
    rcases h2 with ⟨⟨x2, y2, z2⟩, _, h2⟩
    simp only [Prod.mk.injEq, Counts.mk.injEq] at h2
    omega

private lemma card_allNeg (m : ℕ) :
    (allNeg m).card = ∑ d ∈ Icc 1 (m / 2), (m + 3 - 2 * d).choose 3 := by
  rw [allNeg, card_biUnion]
  · refine sum_congr rfl fun d hd => ?_
    rw [mem_Icc] at hd
    rw [card_sliceNeg]
    congr 1; omega
  · intro d1 _ d2 _ hne
    dsimp only [Function.onFun]
    rw [disjoint_left]
    intro p h1 h2
    simp only [sliceNeg, mem_image] at h1 h2
    rcases h1 with ⟨⟨x1, y1, z1⟩, _, rfl⟩
    rcases h2 with ⟨⟨x2, y2, z2⟩, _, h2⟩
    simp only [Prod.mk.injEq, Counts.mk.injEq] at h2
    omega

private lemma card_configFinset (m : ℕ) :
    (configFinset m).card =
      (m + 3).choose 3 + 2 * ∑ d ∈ Icc 1 m, (m + 3 - 2 * d).choose 3 := by
  have hdisj_pn : Disjoint (allPos m) (allNeg m) := by
    rw [disjoint_left]
    intro p h1 h2
    simp only [allPos, allNeg, mem_biUnion, mem_Icc, slicePos, sliceNeg, mem_image] at h1 h2
    rcases h1 with ⟨d1, ⟨hd1, _⟩, ⟨x1, y1, z1⟩, _, rfl⟩
    rcases h2 with ⟨d2, ⟨hd2, _⟩, ⟨x2, y2, z2⟩, _, h2⟩
    simp only [Prod.mk.injEq, Counts.mk.injEq] at h2
    omega
  have hdisj_z : Disjoint (sliceZero m) (allPos m ∪ allNeg m) := by
    rw [disjoint_left]
    intro p h1 h2
    simp only [sliceZero, mem_image] at h1
    rcases h1 with ⟨⟨x, y, z⟩, _, rfl⟩
    simp only [mem_union, allPos, allNeg, mem_biUnion, mem_Icc, slicePos, sliceNeg, mem_image] at h2
    rcases h2 with ⟨d, ⟨hd, _⟩, ⟨x2, y2, z2⟩, _, h2⟩ | ⟨d, ⟨hd, _⟩, ⟨x2, y2, z2⟩, _, h2⟩ <;>
    · simp only [Prod.mk.injEq, Counts.mk.injEq] at h2
      omega
  have hsum_ext :
      ∑ d ∈ Icc 1 (m / 2), (m + 3 - 2 * d).choose 3 =
        ∑ d ∈ Icc 1 m, (m + 3 - 2 * d).choose 3 := by
    refine sum_subset (Icc_subset_Icc_right (Nat.div_le_self m 2)) fun d hd hnot => ?_
    rw [mem_Icc] at hd hnot
    have hlt : m + 3 - 2 * d < 3 := by omega
    exact Nat.choose_eq_zero_of_lt hlt
  rw [configFinset, card_union_of_disjoint hdisj_z, card_union_of_disjoint hdisj_pn,
    card_sliceZero, card_allPos, card_allNeg, hsum_ext]
  omega

private lemma arrayCount_eq (m : ℕ) :
    arrayCount m = (m + 3).choose 3 + 2 * ∑ d ∈ Icc 1 m, (m + 3 - 2 * d).choose 3 := by
  have heq : Configuration m ≃ {p : Counts × Counts // p ∈ configFinset m} :=
    Equiv.subtypeEquivRight fun _ => mem_configFinset.symm
  rw [arrayCount, Nat.card_congr heq, Nat.card_eq_fintype_card, Fintype.card_coe, card_configFinset]

private lemma choose3_step (n d : ℕ) :
    (n + 4 - 2 * d).choose 3 =
      (n + 4 - 2 * (d + 1)).choose 3 + triangle n d + triangle (n + 1) d := by
  unfold triangle
  by_cases h : 2 * d ≤ n + 1
  · have h1 : n + 4 - 2 * d = (n + 2 - 2 * d) + 2 := by omega
    have h2 : n + 4 - 2 * (d + 1) = n + 2 - 2 * d := by omega
    have h3 : n + 1 + 2 - 2 * d = (n + 2 - 2 * d) + 1 := by omega
    rw [h1, h2, h3]
    set x := n + 2 - 2 * d
    have ha : (x + 2).choose 3 = (x + 1).choose 2 + (x + 1).choose 3 :=
      Nat.choose_succ_succ (x + 1) 2
    have hb : (x + 1).choose 3 = x.choose 2 + x.choose 3 :=
      Nat.choose_succ_succ x 2
    omega
  · have h1 : n + 4 - 2 * d < 3 := by omega
    have h2 : n + 4 - 2 * (d + 1) < 3 := by omega
    have h3 : n + 2 - 2 * d < 2 := by omega
    have h4 : n + 1 + 2 - 2 * d < 2 := by omega
    rw [Nat.choose_eq_zero_of_lt h1, Nat.choose_eq_zero_of_lt h2,
      Nat.choose_eq_zero_of_lt h3, Nat.choose_eq_zero_of_lt h4]

private lemma telescope (n k : ℕ) :
    ∑ d ∈ range k, (2 * d + 1) * (triangle n d + triangle (n + 1) d) +
        (2 * k + 1) * (n + 4 - 2 * k).choose 3 =
      (n + 4).choose 3 + 2 * ∑ d ∈ range k, (n + 4 - 2 * (d + 1)).choose 3 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, sum_range_succ]
    have hstep := choose3_step n k
    have hmul :
        (2 * k + 1) * (n + 4 - 2 * k).choose 3 =
          (2 * k + 1) * (n + 4 - 2 * (k + 1)).choose 3 +
            (2 * k + 1) * (triangle n k + triangle (n + 1) k) := by
      rw [hstep]; ring
    linarith

end OeisA005994Proof

open Finset OeisA005994Proof OMA.S_oeis_a005994 in
theorem OMA.solution : type_of% @OMA.S_oeis_a005994.main := by
  intro n
  rw [arrayCount_eq (n + 1)]
  have htel := telescope n (n + 2)
  have hzero : (n + 4 - 2 * (n + 2)).choose 3 = 0 :=
    Nat.choose_eq_zero_of_lt (by omega)
  rw [hzero, mul_zero, add_zero] at htel
  have hlhs :
      ∑ d ∈ range (n + 2), (2 * d + 1) * (triangle n d + triangle (n + 1) d) =
        alkaneCount n + alkaneCount (n + 1) := by
    unfold alkaneCount
    have hsplit :
        ∑ d ∈ range (n + 2), (2 * d + 1) * (triangle n d + triangle (n + 1) d) =
          (∑ d ∈ range (n + 2), (2 * d + 1) * triangle n d) +
            ∑ d ∈ range (n + 2), (2 * d + 1) * triangle (n + 1) d := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun d _ => by ring
    rw [hsplit, sum_range_succ (fun d => (2 * d + 1) * triangle n d) (n + 1)]
    have ht0 : triangle n (n + 1) = 0 := by
      unfold triangle
      exact Nat.choose_eq_zero_of_lt (by omega)
    rw [ht0, mul_zero, add_zero]
  have hrhs :
      ∑ d ∈ range (n + 2), (n + 4 - 2 * (d + 1)).choose 3 =
        ∑ d ∈ Icc 1 (n + 1), (n + 1 + 3 - 2 * d).choose 3 := by
    rw [sum_range_succ]
    have hlast : (n + 4 - 2 * (n + 1 + 1)).choose 3 = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    rw [hlast, add_zero]
    symm
    refine sum_nbij (· - 1) ?_ ?_ ?_ ?_
    · intro d hd
      rw [mem_Icc] at hd
      rw [mem_range]; omega
    · intro d1 hd1 d2 hd2 h
      simp only [mem_coe, mem_Icc] at hd1 hd2
      dsimp only at h
      omega
    · intro j hj
      simp only [mem_coe, mem_range] at hj
      refine ⟨j + 1, ?_, ?_⟩
      · simp only [mem_coe, mem_Icc]; omega
      · dsimp only; omega
    · intro d hd
      rw [mem_Icc] at hd
      congr 1; omega
  rw [← hlhs, ← hrhs]
  have h4 : n + 1 + 3 = n + 4 := by omega
  rw [h4]
  exact htel
