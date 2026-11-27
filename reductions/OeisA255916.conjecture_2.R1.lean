import FormalConjectures.OEIS.«255916»

/-! For values at most 100, side counts above 101 can be clipped to 101. -/

namespace PolygonalCandidates

private theorem sides_le_polygonal {s x : ℕ} (hx : 2 ≤ x) :
    s ≤ Nat.polygonalNumber s x := by
  have hpred : 1 ≤ x - 1 := by omega
  have hsecond : 2 ≤ x * (x - 1) := by
    calc
      2 = 2 * 1 := by decide
      _ ≤ x * (x - 1) := Nat.mul_le_mul hx hpred
  have hdouble : (s - 2) * 2 ≤ (s - 2) * x * (x - 1) := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ hsecond
  have hquot := (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr hdouble
  unfold Nat.polygonalNumber
  omega

private theorem polygonal_clip_eq {s x cap : ℕ} (h : Nat.polygonalNumber s x < cap) :
    Nat.polygonalNumber (min s cap) x = Nat.polygonalNumber s x := by
  by_cases hs : s ≤ cap
  · rw [min_eq_left hs]
  have hx : x < 2 := by
    by_contra hn
    have hlarge := sides_le_polygonal (show 2 ≤ x by omega) (s := s)
    omega
  interval_cases x <;> simp [Nat.polygonalNumber]

theorem clip_of_small {m n j k cap : ℕ} (hn : n < cap)
    (h : OeisA255916.IsSumOfGmPjPk m n j k) :
    OeisA255916.IsSumOfGmPjPk m n (min j cap) (min k cap) := by
  obtain ⟨z, x, y, h⟩ := h
  refine ⟨z, x, y, ?_⟩
  rw [polygonal_clip_eq (show Nat.polygonalNumber j x < cap by omega),
    polygonal_clip_eq (show Nat.polygonalNumber k y < cap by omega)]
  exact h


end PolygonalCandidates

/- A clipped, executable search for a representation at a fixed value. -/

open Nat Finset

namespace PolygonalCandidates

private def generalizedValues (n : ℕ) : List ℕ :=
  ((List.range (2 * n.sqrt + 1)).map fun (i : ℕ) =>
    Nat.generalizedPolygonalNumber 7 ((i : ℤ) - n.sqrt)).filter (fun v => decide (v ≤ n))

private def polygonalLimit (s n : ℕ) : ℕ := if 3 ≤ s then (2 * n).sqrt else n

private def polygonalValues (s n : ℕ) : List ℕ :=
  ((List.range (polygonalLimit s n + 1)).map (Nat.polygonalNumber s)).filter (fun v => decide (v ≤ n))

private def hasRep (n j k : ℕ) : Bool :=
  (generalizedValues n).any fun g =>
    (polygonalValues j n).any fun x =>
      (polygonalValues k n).any fun y => decide (g + x + y = n)

theorem ordinary_index_le_sqrt {s x n : ℕ} (hs : 3 ≤ s)
    (h : Nat.polygonalNumber s x ≤ n) : x ≤ (2 * n).sqrt := by
  by_cases hx : x = 0
  · simp [hx]
  have hprod : x * (x - 1) ≤ (s - 2) * x * (x - 1) := by
    rw [Nat.mul_assoc]
    exact Nat.le_mul_of_pos_left _ (by omega)
  have hsq : x * (x - 1) + x = x * x := by
    calc
      x * (x - 1) + x = x * (x - 1 + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = x * x := by rw [show x - 1 + 1 = x by omega]
  unfold Nat.polygonalNumber at h
  apply Nat.le_sqrt.mpr
  omega

theorem heptagonal_index_le_sqrt {z : ℤ} {n : ℕ}
    (h : Nat.generalizedPolygonalNumber 7 z ≤ n) : z.natAbs ≤ n.sqrt := by
  unfold Nat.generalizedPolygonalNumber at h
  norm_num at h
  have hnum : 5 * z ^ 2 - 3 * z ≤ 2 * (n : ℤ) + 1 := by omega
  have hlower : 2 * z ^ 2 ≤ 5 * z ^ 2 - 3 * z := by
    by_cases hz : z ≤ 0
    · nlinarith [sq_nonneg z]
    · have hz' : 0 ≤ z - 1 := by omega
      nlinarith [mul_nonneg (show 0 ≤ z by omega) hz']
  have hsq : z ^ 2 ≤ (n : ℤ) := by omega
  apply Nat.le_sqrt.mpr
  rw [← pow_two]
  exact_mod_cast ((Int.natAbs_sq z).le.trans hsq)


private theorem ordinary_index_le_limit {s x n : ℕ}
    (h : Nat.polygonalNumber s x ≤ n) : x ≤ polygonalLimit s n := by
  unfold polygonalLimit
  split_ifs with hs
  · exact ordinary_index_le_sqrt hs h
  · unfold Nat.polygonalNumber at h
    omega

theorem noRep_of_hasRep_false {n j k : ℕ} (h : hasRep n j k = false) :
    ¬ OeisA255916.IsSumOfGmPjPk 7 n j k := by
  intro hrep
  rcases hrep with ⟨z, x, y, hsum⟩
  have hzval : Nat.generalizedPolygonalNumber 7 z ≤ n := by omega
  have hxval : Nat.polygonalNumber j x ≤ n := by omega
  have hyval : Nat.polygonalNumber k y ≤ n := by omega
  have habs : |z| ≤ (n.sqrt : ℤ) := by
    have hnat := heptagonal_index_le_sqrt hzval
    rw [← Int.natCast_natAbs]
    exact_mod_cast hnat
  have hlow : -(n.sqrt : ℤ) ≤ z := (Int.neg_le_neg habs).trans (neg_abs_le z)
  have hhigh : z ≤ (n.sqrt : ℤ) := (le_abs_self z).trans habs
  have hx := ordinary_index_le_limit hxval
  have hy := ordinary_index_le_limit hyval
  have hzadd : ((z + n.sqrt).toNat : ℤ) = z + n.sqrt := Int.toNat_of_nonneg (by omega)
  have hindex : (z + n.sqrt).toNat < 2 * n.sqrt + 1 := by
    have hi : ((z + n.sqrt).toNat : ℤ) < (2 * n.sqrt + 1 : ℕ) := by
      rw [hzadd]
      omega
    exact_mod_cast hi
  have hgmem : Nat.generalizedPolygonalNumber 7 z ∈ generalizedValues n := by
    unfold generalizedValues
    apply List.mem_filter.mpr
    constructor
    · apply List.mem_map.mpr
      refine ⟨(z + n.sqrt).toNat, List.mem_range.mpr hindex, ?_⟩
      rw [hzadd]
      congr 1
      omega
    · exact decide_eq_true hzval
  have hxmem : Nat.polygonalNumber j x ∈ polygonalValues j n := by
    unfold polygonalValues
    apply List.mem_filter.mpr
    constructor
    · exact List.mem_map.mpr ⟨x, List.mem_range.mpr (by omega), rfl⟩
    · exact decide_eq_true hxval
  have hymem : Nat.polygonalNumber k y ∈ polygonalValues k n := by
    unfold polygonalValues
    apply List.mem_filter.mpr
    constructor
    · exact List.mem_map.mpr ⟨y, List.mem_range.mpr (by omega), rfl⟩
    · exact decide_eq_true hyval
  have hytrue : (polygonalValues k n).any (fun y' => decide
      (Nat.generalizedPolygonalNumber 7 z + Nat.polygonalNumber j x + y' = n)) = true := by
    apply List.any_eq_true.mpr
    exact ⟨Nat.polygonalNumber k y, hymem, decide_eq_true hsum⟩
  have hxtrue : (polygonalValues j n).any (fun x' => (polygonalValues k n).any
      (fun y' => decide (Nat.generalizedPolygonalNumber 7 z + x' + y' = n))) = true := by
    apply List.any_eq_true.mpr
    exact ⟨Nat.polygonalNumber j x, hxmem, hytrue⟩
  have hgtrue : (generalizedValues n).any (fun g => (polygonalValues j n).any
      (fun x' => (polygonalValues k n).any (fun y' => decide (g + x' + y' = n)))) = true := by
    apply List.any_eq_true.mpr
    exact ⟨Nat.generalizedPolygonalNumber 7 z, hgmem, hxtrue⟩
  change ((generalizedValues n).any fun g => (polygonalValues j n).any fun x =>
    (polygonalValues k n).any fun y => decide (g + x + y = n)) = false at h
  rw [hgtrue] at h
  cases h

end PolygonalCandidates

/-- Rows give side counts 3 through 10, columns give side counts 0 through 101.
Zero marks a pair that the checker does not need to exclude. -/
private def witnessRows : Array (Array ℕ) := #[
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 51, 0, 0, 0, 0, 51, 0, 0, 131, 0, 0, 51, 274, 108,
    0, 0, 0, 0, 0, 51, 0, 129, 51, 0, 108, 131, 1722, 923, 108, 156, 367,
    108, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51,
    51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51,
    51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51, 51],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45, 0, 0, 45, 211,
    0, 42, 0, 0, 42, 61, 0, 45, 58, 0, 42, 58, 73, 42, 61, 73, 45,
    58, 93, 42, 58, 0, 42, 61, 195, 45, 42, 42, 42, 42, 42, 42, 42, 42,
    42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42,
    42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42,
    42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42],
  #[0, 0, 0, 0, 0, 66, 0, 220, 11, 0, 21, 21, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11],
  #[0, 0, 0, 0, 0, 0, 26, 0, 38, 12, 21, 89, 21, 12, 12, 12, 12,
    12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12,
    12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12,
    12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12,
    12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12,
    12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12],
  #[0, 0, 0, 0, 0, 0, 0, 10, 17, 30, 16, 10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10],
  #[0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 30, 17, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 21, 41, 45, 12, 12, 12, 12,
    12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12,
    12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12,
    12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12,
    12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12,
    12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 26, 21, 16, 26, 21, 22,
    16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16,
    16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16,
    16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16,
    16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16,
    16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16]
]

namespace PolygonalCandidates

/-- Omitted pairs without a bounded obstruction in the screen. -/
private def extraHeptagonalPairs : Finset (ℕ × ℕ) :=
  {(3, 34), (3, 35), (3, 36), (3, 37), (3, 38), (3, 40), (3, 43), (4, 38)}

/-- Sun's listed pairs together with the additional candidates. -/
private def heptagonalCandidates : Finset (ℕ × ℕ) :=
  OeisA255916.sunPolygonalPairsSet1 ∪ extraHeptagonalPairs

private def witness (j k : ℕ) : ℕ :=
  (witnessRows[j - 3]!)[k]!

private def passesPair (j k : ℕ) : Bool :=
  if 3 ≤ j ∧ j ≤ k then
    decide ((j, k) ∈ heptagonalCandidates) ||
      (decide (k = 101 → witness j k ≤ 100) && !hasRep (witness j k) j k)
  else true

private def passesRow (j : ℕ) : Bool := (List.range 102).all (passesPair j)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem checkRows : (List.range 11).all passesRow = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem finiteCertificate {j k : ℕ} (hj : 3 ≤ j) (hj' : j < 11)
    (hjk : j ≤ k) (hk' : k < 102) :
    (j, k) ∈ heptagonalCandidates ∨
      ((k = 101 → witness j k ≤ 100) ∧ hasRep (witness j k) j k = false) := by
  have hrow : passesRow j = true := List.all_eq_true.mp checkRows j (List.mem_range.mpr hj')
  have hpass : passesPair j k = true := List.all_eq_true.mp hrow k (List.mem_range.mpr hk')
  simpa [passesPair, hj, hjk, imp_iff_not_or] using hpass

private theorem checkLarge : hasRep 10 11 11 = false := by decide +kernel

set_option maxRecDepth 8000 in
private theorem candidate_lt : ∀ pair ∈ heptagonalCandidates,
    pair.1 < 101 ∧ pair.2 < 101 := by
  decide +kernel

/-- A universal mixed heptagonal triple must use a pair drawn from this finite list. -/
theorem mem_heptagonalCandidates_of_universal {j k : ℕ} (hj : 3 ≤ j) (hjk : j ≤ k)
    (huniv : ∀ n, OeisA255916.IsSumOfGmPjPk 7 n j k) :
    (j, k) ∈ heptagonalCandidates := by
  by_cases hlarge : 11 ≤ j
  · have hclip := clip_of_small (m := 7) (cap := 11) (n := 10) (by decide) (huniv 10)
    rw [min_eq_right hlarge, min_eq_right (hlarge.trans hjk)] at hclip
    exact (noRep_of_hasRep_false checkLarge hclip).elim
  have hj' : j < 11 := by omega
  let k' := min k 101
  obtain good | ⟨hsmall, hfalse⟩ := finiteCertificate (k := k') hj hj'
    (by dsimp [k']; omega) (by dsimp [k']; omega)
  · have hk' := (candidate_lt (j, k') good).2
    have heqk : k' = k := by dsimp [k'] at *; omega
    simpa only [heqk] using good
  · have hrep := huniv (witness j k')
    apply False.elim
    apply noRep_of_hasRep_false hfalse
    by_cases hclip : 101 < k
    · have hval := hsmall (by dsimp [k']; omega)
      have hclipped := clip_of_small (cap := 101) (by omega) hrep
      rwa [min_eq_left (show j ≤ 101 by omega)] at hclipped
    · have hk' : k' = k := by dsimp [k']; omega
      simpa only [hk'] using hrep


end PolygonalCandidates

namespace OMA.R_OeisA255916_conjecture_2_R1

/-- Each pair listed in the conjecture is universal. -/
def H1 : Prop :=
  ∀ pair ∈ OeisA255916.sunPolygonalPairsSet1,
    ∀ n, OeisA255916.IsSumOfGmPjPk 7 n pair.1 pair.2

/-- None of the eight additional candidates is universal. -/
def H2 : Prop :=
  ∀ pair ∈ PolygonalCandidates.extraHeptagonalPairs,
    ∃ n, ¬ OeisA255916.IsSumOfGmPjPk 7 n pair.1 pair.2

theorem main : H1 → H2 → type_of% @OeisA255916.conjecture_2 := by
  intro listed additional j k hjk
  constructor
  · intro universal
    have hmem := PolygonalCandidates.mem_heptagonalCandidates_of_universal hjk.1 hjk.2 universal
    rcases Finset.mem_union.mp hmem with h | h
    · exact h
    · obtain ⟨n, hn⟩ := additional (j, k) h
      exact (hn (universal n)).elim
  · exact listed (j, k)

end OMA.R_OeisA255916_conjecture_2_R1
