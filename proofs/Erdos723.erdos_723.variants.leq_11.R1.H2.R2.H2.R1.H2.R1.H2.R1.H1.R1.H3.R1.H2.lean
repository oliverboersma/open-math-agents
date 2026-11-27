import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H2_R1_H2_R1_H2_R1_H1_R1_H3_R1
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

-- The exact-cover verifier and catalogue checks are adapted from @avivorly's PR #2602.
-- The certificates here cover the first partitions in this interval.

/- Encode a star as a line mask. Certify the four generators that act on the first group's catalogue. -/

namespace FiniteSearchMasks

variable {α : Type}

def bitMask (xs : List α) (chosen : α → Bool) : Nat :=
  (xs.zipIdx.map fun (x, i) => if chosen x then 2^i else 0).foldr Nat.lor 0

lemma foldr_or_testBit (words : List Nat) (i : Nat) :
    (words.foldr Nat.lor 0).testBit i = true ↔ ∃ n ∈ words, n.testBit i = true := by
  induction words with
  | nil => simp
  | cons word words ih =>
      change (word ||| words.foldr Nat.lor 0).testBit i = true ↔ _
      simp only [Nat.testBit_lor, Bool.or_eq_true, ih, List.mem_cons]
      constructor
      · intro h
        rcases h with bit | ⟨n, hn, bit⟩
        · exact ⟨word, Or.inl rfl, bit⟩
        · exact ⟨n, Or.inr hn, bit⟩
      · rintro ⟨n, h, bit⟩
        rcases h with rfl | mem
        · exact Or.inl bit
        · exact Or.inr ⟨n, mem, bit⟩

theorem bitMask_testBit (xs : List α) (chosen : α → Bool) (i : Nat) :
    (bitMask xs chosen).testBit i = true ↔ ∃ x, xs[i]? = some x ∧ chosen x = true := by
  rw [bitMask, foldr_or_testBit]
  constructor
  · rintro ⟨n, member, set⟩
    obtain ⟨⟨x,j⟩, hxj, rfl⟩ := List.mem_map.mp member
    cases hx : chosen x with
    | false => simp [hx] at set
    | true =>
      have ji : j = i := by simpa [hx, Nat.testBit_two_pow] using set
      subst j
      exact ⟨x, List.mk_mem_zipIdx_iff_getElem?.mp hxj, hx⟩
  · rintro ⟨x, hx, chosen_x⟩
    refine ⟨2^i, ?_, Nat.testBit_two_pow_self⟩
    apply List.mem_map.mpr
    exact ⟨(x,i), List.mk_mem_zipIdx_iff_getElem?.mpr hx, by simp [chosen_x]⟩

lemma bitMask_getElem_testBit (xs : List α) (chosen : α → Bool) (i : ℕ) (in_list : i < xs.length) :
    (bitMask xs chosen).testBit i = chosen xs[i] := by
  apply Bool.eq_iff_iff.mpr
  rw [bitMask_testBit]
  simp [List.getElem?_eq_getElem in_list]

end FiniteSearchMasks

namespace WeightFifteenLargeCatalog

def vertexMask (g : Fin 15) : Nat :=
  ([32760, 32711, 32319, 29183, 4095, 28095, 23543, 16239,
      30431, 14334, 24317, 31611, 28635, 32237, 32694] : List Nat)[g.val]'g.isLt

def endpointMask (g : Fin 60) : Nat :=
  ([17, 33, 129, 257, 513, 1025, 4097, 8193,
      10, 34, 66, 130, 1026, 2050, 4098, 16386,
      12, 20, 68, 260, 516, 2052, 8196, 16388,
      136, 264, 520, 2056, 4104, 16392, 80, 272,
      1040, 2064, 4112, 8208, 96, 160, 544, 1056,
      8224, 16416, 1088, 2112, 8256, 16448, 640, 2176,
      4224, 8320, 768, 1280, 4352, 16640, 8704, 16896,
      5120, 17408, 6144, 10240] : List Nat)[g.val]'g.isLt

def eligibleMask (g : Fin 15) : Nat :=
  ([1152921504590069760, 1152917106576915708, 1134911294713099251, 14411560693780431, 3603047246675775, 732542662748126127, 339435142697119327, 962677200052385786,
      271188003732839925, 98892265553878784, 540976176994648183, 933436301946972123, 787844113021058493, 1097681697835385070, 1152855463058668032] : List Nat)[g.val]'g.isLt


end WeightFifteenLargeCatalog

namespace FiniteMaskCoverEnumeration

abbrev Allowed := Nat × Nat

def enumerate (options : List Allowed) : Nat → Nat → List (Finset Nat)
  | 0, remaining => if remaining == 0 then [∅] else []
  | fuel + 1, remaining =>
      if remaining == 0 then [∅]
      else options.flatMap fun pair =>
        if pair.1.testBit remaining.log2 && (pair.1 &&& remaining == pair.1) then
          (enumerate options fuel (remaining ^^^ pair.1)).map (insert pair.2)
        else []

def covers (options : List Allowed) (remaining : Nat) (picked : Finset Allowed) : Prop :=
  (∀ a ∈ picked, a ∈ options) ∧
  (∀ a ∈ picked, ∀ i, a.1.testBit i = true → remaining.testBit i = true) ∧
  (∀ a ∈ picked, ∀ b ∈ picked, a ≠ b → ∀ i, a.1.testBit i = true → b.1.testBit i = false) ∧
  ∀ i, remaining.testBit i = true → ∃ a ∈ picked, a.1.testBit i = true

lemma cover_empty (options : List Allowed) (nonempty : ∀ a ∈ options, a.1 ≠ 0)
    (picked : Finset Allowed) (valid : covers options 0 picked) :
    picked = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have ne := nonempty a (valid.1 a ha)
  have bit := Nat.testBit_log2 ne
  have impossible := valid.2.1 a ha a.1.log2 bit
  simp at impossible

lemma cover_erase (options : List Allowed) (remaining : Nat) (picked : Finset Allowed)
    (valid : covers options remaining picked) (first : Allowed) (selected : first ∈ picked) :
    covers options (remaining ^^^ first.1) (picked.erase first) := by
  obtain ⟨members, inside, separated, covering⟩ := valid
  refine ⟨?_,?_,?_,?_⟩
  · intro a ha
    exact members a (Finset.mem_of_mem_erase ha)
  · intro a ha i bit
    obtain ⟨unequal, member⟩ := Finset.mem_erase.mp ha
    have old := inside a member i bit
    have not_first := separated a member first selected unequal i bit
    simp [Nat.testBit_xor, old, not_first]
  · intro a ha b hb
    exact separated a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)
  · intro i bit
    have avoid : first.1.testBit i = false := by
      cases at_i : first.1.testBit i
      · rfl
      · have old := inside first selected i at_i
        simp [Nat.testBit_xor, at_i, old] at bit
    have old : remaining.testBit i = true := by simpa [Nat.testBit_xor, avoid] using bit
    obtain ⟨a, ha, covers_i⟩ := covering i old
    have other : a ≠ first := by
      intro same
      rw [same, avoid] at covers_i
      contradiction
    exact ⟨a, Finset.mem_erase.mpr ⟨other, ha⟩, covers_i⟩

theorem enumerate_complete (options : List Allowed) (nonempty : ∀ a ∈ options, a.1 ≠ 0)
    (fuel remaining : Nat) (picked : Finset Allowed) (room : picked.card ≤ fuel)
    (valid : covers options remaining picked) :
    picked.image Prod.snd ∈ enumerate options fuel remaining := by
  induction fuel generalizing remaining picked with
  | zero =>
      have empty : picked = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero room)
      have rem : remaining = 0 := by
        by_contra nonzero
        have covered := valid.2.2.2 remaining.log2 (Nat.testBit_log2 nonzero)
        simp [empty] at covered
      simp [enumerate, rem, empty]
  | succ fuel ih =>
      by_cases empty : remaining = 0
      · subst remaining
        simp [enumerate, cover_empty options nonempty picked valid]
      · obtain ⟨first, selected, bit_pivot⟩ :=
          valid.2.2.2 remaining.log2 (Nat.testBit_log2 empty)
        have in_options := valid.1 first selected
        have subset : first.1 &&& remaining = first.1 := by
          apply Nat.eq_of_testBit_eq
          intro i
          cases bit : first.1.testBit i
          · simp [bit]
          · simp [bit, valid.2.1 first selected i bit]
        have mask_ok : (first.1.testBit remaining.log2 && (first.1 &&& remaining == first.1)) = true := by
          simp [bit_pivot, subset]
        have less : (picked.erase first).card ≤ fuel := by
          rw [Finset.card_erase_of_mem selected]
          omega
        have step := ih (remaining ^^^ first.1) (picked.erase first) less
          (cover_erase options remaining picked valid first selected)
        simp only [enumerate, beq_iff_eq, if_neg empty, List.mem_flatMap]
        refine ⟨first, in_options, ?_⟩
        rw [if_pos mask_ok, List.mem_map]
        refine ⟨(picked.erase first).image Prod.snd, step, ?_⟩
        rw [← Finset.image_insert, Finset.insert_erase selected]

end FiniteMaskCoverEnumeration
namespace WeightFifteenIndexedSearch

open Finset FiniteMaskCoverEnumeration FiniteSearchMasks
open WeightFifteenLargeCatalog (vertexMask endpointMask eligibleMask)

def indexOptions (g : Fin 15) : List Allowed :=
  (List.finRange 60).filterMap fun p =>
    if (eligibleMask g).testBit p.val then some (endpointMask p, p.val) else none

def pack (bits : Finset Nat) : Nat := bitMask (List.range 60) fun p => decide (p ∈ bits)

def numericCatalog (g : Fin 15) : List Nat :=
  ((enumerate (indexOptions g) 60 (vertexMask g)).map pack).mergeSort

lemma vertex_bound : ∀ g : Fin 15, vertexMask g < 2^15 := by decide +kernel
lemma endpoint_bound : ∀ p : Fin 60, endpointMask p < 2^15 := by decide +kernel
lemma endpoint_positive : ∀ p : Fin 60, endpointMask p ≠ 0 := by decide +kernel
lemma eligible_bound : ∀ g : Fin 15, eligibleMask g < 2^60 := by decide +kernel

lemma endpoint_subset : ∀ (g : Fin 15) (p : Fin 60),
    (eligibleMask g).testBit p.val = true → (endpointMask p &&& vertexMask g) = endpointMask p :=
  by decide +kernel

lemma read_indexOptions (g : Fin 15) (q : Allowed) (mem : q ∈ indexOptions g) :
    ∃ p : Fin 60, ((eligibleMask g).testBit p.val = true) ∧ (endpointMask p, p.val) = q := by
  obtain ⟨p, hp, value⟩ := List.mem_filterMap.mp mem
  by_cases avail : (eligibleMask g).testBit p.val = true
  · exact ⟨p, avail, by simpa [avail] using value⟩
  · simp [avail] at value

lemma pack_testBit (b : Finset Nat) (i : Nat) :
    (pack b).testBit i = true ↔ i < 60 ∧ i ∈ b := by
  rw [pack, bitMask_testBit]
  by_cases lt : i < 60
  · have inside : i < (List.range 60).length := by simpa using lt
    rw [List.getElem?_eq_getElem inside, List.getElem_range]
    simp [lt]
  · have outside : (List.range 60).length ≤ i := by simpa using Nat.le_of_not_gt lt
    rw [List.getElem?_eq_none outside]
    simp [lt]

theorem indexed_star_in_catalog (g : Fin 15) (star : Finset (Fin 60))
    (uses : ∀ p ∈ star, (eligibleMask g).testBit p.val = true)
    (exactCover : ∀ m : Fin 15, (vertexMask g).testBit m.val = true →
      ∃! p : Fin 60, p ∈ star ∧ (endpointMask p).testBit m.val = true) :
    pack (star.image Fin.val) ∈ numericCatalog g := by
  let selected := star.image fun p => (endpointMask p, p.val)
  have allowed_nonempty : ∀ a ∈ indexOptions g, a.1 ≠ 0 := by
    intro q hq
    obtain ⟨p, _, rfl⟩ := read_indexOptions g q hq
    exact endpoint_positive p
  have room : selected.card ≤ 60 := by
    exact Finset.card_image_le.trans (by simpa using Finset.card_le_univ star)
  have within (p : Fin 60) (hp : p ∈ star) (b : Nat) (bit : (endpointMask p).testBit b = true) :
      (vertexMask g).testBit b = true := by
    have eq := congrArg (fun m => m.testBit b) (endpoint_subset g p (uses p hp))
    simpa only [Nat.testBit_land, bit, Bool.true_and] using eq
  have chosen : covers (indexOptions g) (vertexMask g) selected := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro q hq
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
      exact List.mem_filterMap.mpr ⟨p, List.mem_finRange p, by simp [uses p hp]⟩
    · intro q hq b bit
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
      exact within p hp b bit
    · intro a ha b hb distinct i on_a
      obtain ⟨p, hp, rfl⟩ := mem_image.mp ha
      obtain ⟨q, hq, rfl⟩ := mem_image.mp hb
      have here : i < 15 := by
        by_contra outside
        have less : endpointMask p < 2^i :=
          (endpoint_bound p).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt outside))
        exact Bool.false_ne_true ((Nat.testBit_lt_two_pow less).symm.trans on_a)
      cases there : (endpointMask q).testBit i
      · rfl
      · obtain ⟨_, _, unique⟩ := exactCover ⟨i,here⟩ (within p hp i on_a)
        have same := (unique p ⟨hp, on_a⟩).trans (unique q ⟨hq, there⟩).symm
        exact (distinct (congrArg (fun w : Fin 60 => (endpointMask w, w.val)) same)).elim
    · intro i required
      have here : i < 15 := by
        by_contra outside
        have less : vertexMask g < 2^i :=
          (vertex_bound g).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt outside))
        exact Bool.false_ne_true ((Nat.testBit_lt_two_pow less).symm.trans required)
      obtain ⟨p, ⟨hp, bit⟩, _⟩ := exactCover ⟨i,here⟩ required
      exact ⟨(endpointMask p,p.val), mem_image_of_mem _ hp, bit⟩
  have member := enumerate_complete _ allowed_nonempty 60 _ selected room chosen
  unfold numericCatalog
  rw [List.mem_mergeSort]
  apply List.mem_map.mpr
  refine ⟨_, member, ?_⟩
  rw [show selected.image Prod.snd = star.image Fin.val by
    unfold selected
    rw [Finset.image_image]
    rfl]

end WeightFifteenIndexedSearch

namespace WeightFifteenIndexedSearch

open Finset FiniteMaskCoverEnumeration FiniteSearchMasks
open WeightFifteenLargeCatalog (vertexMask endpointMask eligibleMask)

def enumerateMasks (options : List Allowed) : Nat → Nat → List Nat
  | 0, remaining => if remaining == 0 then [0] else []
  | fuel + 1, remaining =>
      if remaining == 0 then [0]
      else options.flatMap fun pair =>
        if pair.1.testBit remaining.log2 && (pair.1 &&& remaining == pair.1) then
          (enumerateMasks options fuel (remaining ^^^ pair.1)).map (fun m => 2^pair.2 ||| m)
        else []

lemma pack_empty : pack ∅ = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases b : (pack ∅).testBit i with
  | false => simp
  | true => simpa using ((pack_testBit _ _).mp b).2

lemma pack_insert (p : Nat) (lt : p < 60) (b : Finset Nat) :
    pack (insert p b) = 2^p ||| pack b := by
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  by_cases equal : p = i
  · subst i
    simp [pack_testBit, Nat.testBit_two_pow, lt]
  · simp [pack_testBit, Nat.testBit_two_pow, equal, Ne.symm equal]

lemma enumerateMasks_correct (options : List Allowed) (labels : ∀ a ∈ options, a.2 < 60)
    (fuel remaining : Nat) :
    enumerateMasks options fuel remaining = (enumerate options fuel remaining).map pack := by
  induction fuel generalizing remaining with
  | zero =>
    by_cases empty : remaining = 0 <;> simp [enumerateMasks, enumerate, empty, pack_empty]
  | succ fuel ih =>
    by_cases empty : remaining = 0
    · simp [enumerateMasks, enumerate, empty, pack_empty]
    · simp only [enumerateMasks, enumerate, beq_iff_eq, if_neg empty, List.map_flatMap]
      apply List.flatMap_congr
      intro a ha
      by_cases good : (a.1.testBit remaining.log2 && (a.1 &&& remaining == a.1)) = true
      · simp only [if_pos good, ih, List.map_map, Function.comp_def, pack_insert a.2 (labels a ha)]
      · simp [good]


def directCatalog (g : Fin 15) : List Nat :=
  enumerateMasks (indexOptions g) 60 (vertexMask g)

theorem directCatalog_mem (g : Fin 15) (x : Nat) :
    x ∈ directCatalog g ↔ x ∈ numericCatalog g := by
  unfold directCatalog numericCatalog
  rw [List.mem_mergeSort, enumerateMasks_correct]
  intro a ha
  obtain ⟨p, _, rfl⟩ := read_indexOptions g a ha
  exact p.isLt

end WeightFifteenIndexedSearch

namespace WeightFifteenIndexedSearch

open Finset FiniteMaskCoverEnumeration WeightFifteenLargeCatalog

def partitionOptions : List Allowed := (directCatalog 0).zipIdx

def partitionCatalog : List (Finset Nat) := enumerate partitionOptions 6 (eligibleMask 0)

lemma enumerateMasks_nonzero {options : List Allowed} {fuel remaining mask : Nat}
    (required : remaining ≠ 0) (listed : mask ∈ enumerateMasks options fuel remaining) : mask ≠ 0 := by
  cases fuel with
  | zero => simp [enumerateMasks, required] at listed
  | succ fuel =>
    simp only [enumerateMasks, beq_iff_eq, if_neg required, List.mem_flatMap] at listed
    obtain ⟨pair, _, next⟩ := listed
    split at next
    · obtain ⟨tail, _, rfl⟩ := List.mem_map.mp next
      have bit : (2 ^ pair.2 ||| tail).testBit pair.2 = true := by
        simp [Nat.testBit_lor]
      intro empty
      simp [empty] at bit
    · simp at next

lemma partitionOptions_nonzero : ∀ a ∈ partitionOptions, a.1 ≠ 0 := by
  intro a ha
  exact enumerateMasks_nonzero (by decide : vertexMask 0 ≠ 0) (List.fst_mem_of_mem_zipIdx ha)

lemma star_mask_bit (star : Finset (Fin 60)) (b : Nat) :
    (pack (star.image Fin.val)).testBit b = true ↔ ∃ p ∈ star, p.val = b := by
  rw [pack_testBit]
  constructor
  · exact fun h => Finset.mem_image.mp h.2
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.isLt, Finset.mem_image_of_mem _ hp⟩

/-- Any first-group partition in a solution occurs among the enumerated sets of star indices. -/
theorem partitionCatalog_complete (star : Fin 6 → Finset (Fin 60))
    (allowed : ∀ i p, p ∈ star i → (eligibleMask 0).testBit p.val = true)
    (exactCover : ∀ i (m : Fin 15), (vertexMask 0).testBit m.val = true →
      ∃! p : Fin 60, p ∈ star i ∧ (endpointMask p).testBit m.val = true)
    (partition : ∀ p, (eligibleMask 0).testBit p.val = true → ∃! i, p ∈ star i) :
    let index := fun i => (directCatalog 0).idxOf (pack ((star i).image Fin.val))
    (∀ i, (directCatalog 0)[index i]? = some (pack ((star i).image Fin.val))) ∧
    Finset.univ.image index ∈ partitionCatalog := by
  classical
  have individual (i : Fin 6) : pack ((star i).image Fin.val) ∈ directCatalog 0 :=
    (directCatalog_mem 0 _).mpr (indexed_star_in_catalog 0 _ (allowed i) (exactCover i))
  let index := fun i => (directCatalog 0).idxOf (pack ((star i).image Fin.val))
  have at_index (i : Fin 6) : (directCatalog 0)[index i]? = some (pack ((star i).image Fin.val)) :=
    List.getElem?_idxOf (individual i)
  let selected := Finset.univ.image fun i : Fin 6 => (pack ((star i).image Fin.val), index i)
  have room : selected.card ≤ 6 := Finset.card_image_le.trans (by simp)
  have valid : covers partitionOptions (eligibleMask 0) selected := by
    refine ⟨?_,?_,?_,?_⟩
    · intro a ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      exact List.mk_mem_zipIdx_iff_getElem?.mpr (at_index i)
    · intro a ha b bit
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨p, hp, rfl⟩ := (star_mask_bit _ b).mp bit
      exact allowed i p hp
    · intro a ha b hb different bit on_a
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨p, hp, place⟩ := (star_mask_bit _ bit).mp on_a
      cases on_b : (pack ((star j).image Fin.val)).testBit bit with
      | false => rfl
      | true =>
        obtain ⟨q, hq, place'⟩ := (star_mask_bit _ bit).mp on_b
        have eq : p = q := Fin.ext (place.trans place'.symm)
        subst q
        obtain ⟨_, _, unique⟩ := partition p (allowed i p hp)
        have same := (unique i hp).trans (unique j hq).symm
        exact (different (by rw [same])).elim
    · intro b needed
      have inside : b < 60 := by
        by_contra outside
        have bounded : eligibleMask 0 < 2^b :=
          (eligible_bound 0).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt outside))
        exact Bool.false_ne_true ((Nat.testBit_lt_two_pow bounded).symm.trans needed)
      obtain ⟨i, member, _⟩ := partition ⟨b, inside⟩ needed
      exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ i), (star_mask_bit _ b).mpr ⟨_, member, rfl⟩⟩
  have found := enumerate_complete partitionOptions partitionOptions_nonzero 6 _ selected room valid
  refine ⟨at_index, ?_⟩
  simpa only [partitionCatalog, selected, Finset.image_image, Function.comp_def] using found

end WeightFifteenIndexedSearch

namespace WeightFifteenIndexedSymmetry

open Finset WeightFifteenLargeCatalog

def IsCover (s : Fin 15 → Fin 6 → Finset (Fin 60)) : Prop :=
  (∀ g i p, p ∈ s g i → (eligibleMask g).testBit p.val = true) ∧
  (∀ g i (m : Fin 15), (vertexMask g).testBit m.val = true →
    ∃! p : Fin 60, p ∈ s g i ∧ (endpointMask p).testBit m.val = true) ∧
  (∀ g p, (eligibleMask g).testBit p.val = true → ∃! i, p ∈ s g i) ∧
  ∀ g h i j, g ≠ h → (s g i ∩ s h j).card ≤ 1

structure Symmetry where
  group : Equiv.Perm (Fin 15)
  matching : Equiv.Perm (Fin 15)
  line : Equiv.Perm (Fin 60)
  fixed : group 0 = 0
  preserves_eligible : ∀ g p,
    (eligibleMask (group g)).testBit (line p).val = (eligibleMask g).testBit p.val
  preserves_required : ∀ g m,
    (vertexMask (group g)).testBit (matching m).val = (vertexMask g).testBit m.val
  preserves_endpoints : ∀ p m,
    (endpointMask (line p)).testBit (matching m).val = (endpointMask p).testBit m.val

def Symmetry.applyCover (a : Symmetry) (s : Fin 15 → Fin 6 → Finset (Fin 60))
    (g : Fin 15) (i : Fin 6) : Finset (Fin 60) :=
  (s (a.group.symm g) i).map a.line.toEmbedding

lemma Symmetry.applyCover_mem (a : Symmetry) (s : Fin 15 → Fin 6 → Finset (Fin 60))
    (g : Fin 15) (i : Fin 6) (p : Fin 60) :
    a.line p ∈ a.applyCover s (a.group g) i ↔ p ∈ s g i := by
  unfold Symmetry.applyCover
  rw [Equiv.symm_apply_apply]
  exact Finset.mem_map' _

theorem Symmetry.applyCover_correct (a : Symmetry) (s : Fin 15 → Fin 6 → Finset (Fin 60))
    (valid : IsCover s) : IsCover (a.applyCover s) := by
  unfold IsCover
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g i p where_on
    obtain ⟨g', rfl⟩ := a.group.surjective g
    obtain ⟨p', rfl⟩ := a.line.surjective p
    rw [a.preserves_eligible]
    exact valid.1 g' i p' ((a.applyCover_mem s g' i p').mp where_on)
  · intro g i m needed
    obtain ⟨g', rfl⟩ := a.group.surjective g
    obtain ⟨m', rfl⟩ := a.matching.surjective m
    rw [a.preserves_required] at needed
    have both (p : Fin 60) :
        (p ∈ s g' i ∧ (endpointMask p).testBit m'.val = true) ↔
        (a.line p ∈ a.applyCover s (a.group g') i ∧
          (endpointMask (a.line p)).testBit (a.matching m').val = true) := by
      rw [a.preserves_endpoints, a.applyCover_mem]
    exact (a.line.existsUnique_congr both).mp (valid.2.1 g' i m' needed)
  · intro g p good
    obtain ⟨g', rfl⟩ := a.group.surjective g
    obtain ⟨p', rfl⟩ := a.line.surjective p
    rw [a.preserves_eligible] at good
    apply ((Equiv.refl (Fin 6)).existsUnique_congr (fun i =>
      (a.applyCover_mem s g' i p').symm)).mp
    exact valid.2.2.1 g' p' good
  · intro g h i j unequal
    obtain ⟨g', rfl⟩ := a.group.surjective g
    obtain ⟨h', rfl⟩ := a.group.surjective h
    unfold Symmetry.applyCover
    simp only [Equiv.symm_apply_apply, ← Finset.map_inter, Finset.card_map]
    exact valid.2.2.2 g' h' i j (fun eq => unequal (congrArg a.group eq))

theorem Symmetry.first_group_perm (a : Symmetry) (s : Fin 15 → Fin 6 → Finset (Fin 60))
    (i : Fin 6) : a.applyCover s 0 i = (s 0 i).map a.line.toEmbedding := by
  unfold Symmetry.applyCover
  rw [← a.fixed, Equiv.symm_apply_apply, a.fixed]

end WeightFifteenIndexedSymmetry
namespace WeightFifteenIndexedSymmetry

open WeightFifteenLargeCatalog

def involutionPerm {n : Nat} (f : Fin n → Fin n) (order_two : ∀ a, f (f a) = a) : Equiv.Perm (Fin n) :=
  ⟨f, f, order_two, order_two⟩

lemma involutionPerm_apply {n : Nat} (f : Fin n → Fin n) (h) (x) : involutionPerm f h x = f x := rfl

def generator0_group (a : Fin 15) : Fin 15 :=
    ([0, 5, 6, 7, 8, 1, 2, 3, 4, 9, 10, 11, 12, 13, 14] : List (Fin 15))[a.val]

set_option maxRecDepth 10000 in
def generator0_groupPerm : Equiv.Perm (Fin 15) :=
  involutionPerm generator0_group (by decide +kernel)

def generator0_matching (a : Fin 15) : Fin 15 :=
    ([0, 1, 2, 6, 9, 12, 3, 10, 13, 4, 7, 14, 5, 8, 11] : List (Fin 15))[a.val]

set_option maxRecDepth 10000 in
def generator0_matchingPerm : Equiv.Perm (Fin 15) :=
  involutionPerm generator0_matching (by decide +kernel)

def generator0_line (a : Fin 60) : Fin 60 :=
    ([4, 6, 5, 7, 0, 2, 1, 3, 10, 14, 8, 12, 11, 15, 9, 13, 18, 20, 16, 22, 17, 23, 19, 21, 42, 44, 30, 45, 36, 43, 26, 54, 46, 55, 38, 50, 28, 56, 34, 48, 52, 58, 24, 29, 25, 27, 32, 57, 39, 51, 35, 49, 40, 59, 31, 33, 37, 47, 41, 53] : List (Fin 60))[a.val]

set_option maxRecDepth 10000 in
def generator0_linePerm : Equiv.Perm (Fin 60) :=
  involutionPerm generator0_line (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 30000000 in
lemma generator0_eligible (a : Fin 15) : ∀ b : Fin 60,
    (eligibleMask (generator0_group a)).testBit (generator0_line b).val =
      (eligibleMask a).testBit b.val := by
  fin_cases a <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 30000000 in
lemma generator0_required (a : Fin 15) : ∀ b : Fin 15,
    (vertexMask (generator0_group a)).testBit (generator0_matching b).val =
      (vertexMask a).testBit b.val := by
  fin_cases a <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 30000000 in
lemma generator0_endpoints (a : Fin 60) : ∀ b : Fin 15,
    (endpointMask (generator0_line a)).testBit (generator0_matching b).val =
      (endpointMask a).testBit b.val := by
  fin_cases a <;> decide +kernel

def generator0 : Symmetry where
  group := generator0_groupPerm
  matching := generator0_matchingPerm
  line := generator0_linePerm
  fixed := rfl
  preserves_eligible := generator0_eligible
  preserves_required := generator0_required
  preserves_endpoints := generator0_endpoints

def generator1_group (a : Fin 15) : Fin 15 :=
    ([0, 2, 1, 3, 4, 6, 5, 7, 8, 9, 12, 13, 10, 11, 14] : List (Fin 15))[a.val]

set_option maxRecDepth 10000 in
def generator1_groupPerm : Equiv.Perm (Fin 15) :=
  involutionPerm generator1_group (by decide +kernel)

def generator1_matching (a : Fin 15) : Fin 15 :=
    ([0, 2, 1, 6, 7, 8, 3, 4, 5, 10, 9, 11, 13, 12, 14] : List (Fin 15))[a.val]

set_option maxRecDepth 10000 in
def generator1_matchingPerm : Equiv.Perm (Fin 15) :=
  involutionPerm generator1_matching (by decide +kernel)

def generator1_line (a : Fin 60) : Fin 60 :=
    ([2, 3, 0, 1, 5, 4, 7, 6, 18, 19, 16, 17, 20, 21, 22, 23, 10, 11, 8, 9, 12, 13, 14, 15, 30, 36, 42, 43, 44, 45, 24, 37, 46, 47, 49, 48, 25, 31, 51, 50, 52, 53, 26, 27, 28, 29, 32, 33, 35, 34, 39, 38, 40, 41, 56, 57, 54, 55, 59, 58] : List (Fin 60))[a.val]

set_option maxRecDepth 10000 in
def generator1_linePerm : Equiv.Perm (Fin 60) :=
  involutionPerm generator1_line (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 30000000 in
lemma generator1_eligible (a : Fin 15) : ∀ b : Fin 60,
    (eligibleMask (generator1_group a)).testBit (generator1_line b).val =
      (eligibleMask a).testBit b.val := by
  fin_cases a <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 30000000 in
lemma generator1_required (a : Fin 15) : ∀ b : Fin 15,
    (vertexMask (generator1_group a)).testBit (generator1_matching b).val =
      (vertexMask a).testBit b.val := by
  fin_cases a <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 30000000 in
lemma generator1_endpoints (a : Fin 60) : ∀ b : Fin 15,
    (endpointMask (generator1_line a)).testBit (generator1_matching b).val =
      (endpointMask a).testBit b.val := by
  fin_cases a <;> decide +kernel

def generator1 : Symmetry where
  group := generator1_groupPerm
  matching := generator1_matchingPerm
  line := generator1_linePerm
  fixed := rfl
  preserves_eligible := generator1_eligible
  preserves_required := generator1_required
  preserves_endpoints := generator1_endpoints

def generator2_group (a : Fin 15) : Fin 15 :=
    ([0, 1, 3, 2, 4, 5, 7, 6, 8, 10, 9, 11, 12, 14, 13] : List (Fin 15))[a.val]

set_option maxRecDepth 10000 in
def generator2_groupPerm : Equiv.Perm (Fin 15) :=
  involutionPerm generator2_group (by decide +kernel)

def generator2_matching (a : Fin 15) : Fin 15 :=
    ([1, 0, 2, 4, 3, 5, 9, 10, 11, 6, 7, 8, 12, 14, 13] : List (Fin 15))[a.val]

set_option maxRecDepth 10000 in
def generator2_matchingPerm : Equiv.Perm (Fin 15) :=
  involutionPerm generator2_matching (by decide +kernel)

def generator2_line (a : Fin 60) : Fin 60 :=
    ([8, 9, 12, 13, 10, 11, 14, 15, 0, 1, 4, 5, 2, 3, 6, 7, 17, 16, 20, 21, 18, 19, 23, 22, 32, 33, 30, 31, 34, 35, 26, 27, 24, 25, 28, 29, 38, 39, 36, 37, 41, 40, 46, 50, 55, 54, 42, 51, 56, 57, 43, 47, 58, 59, 45, 44, 48, 49, 52, 53] : List (Fin 60))[a.val]

set_option maxRecDepth 10000 in
def generator2_linePerm : Equiv.Perm (Fin 60) :=
  involutionPerm generator2_line (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 30000000 in
lemma generator2_eligible (a : Fin 15) : ∀ b : Fin 60,
    (eligibleMask (generator2_group a)).testBit (generator2_line b).val =
      (eligibleMask a).testBit b.val := by
  fin_cases a <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 30000000 in
lemma generator2_required (a : Fin 15) : ∀ b : Fin 15,
    (vertexMask (generator2_group a)).testBit (generator2_matching b).val =
      (vertexMask a).testBit b.val := by
  fin_cases a <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 30000000 in
lemma generator2_endpoints (a : Fin 60) : ∀ b : Fin 15,
    (endpointMask (generator2_line a)).testBit (generator2_matching b).val =
      (endpointMask a).testBit b.val := by
  fin_cases a <;> decide +kernel

def generator2 : Symmetry where
  group := generator2_groupPerm
  matching := generator2_matchingPerm
  line := generator2_linePerm
  fixed := rfl
  preserves_eligible := generator2_eligible
  preserves_required := generator2_required
  preserves_endpoints := generator2_endpoints

def generator3_group (a : Fin 15) : Fin 15 :=
    ([0, 1, 2, 4, 3, 5, 6, 8, 7, 9, 11, 10, 13, 12, 14] : List (Fin 15))[a.val]

set_option maxRecDepth 10000 in
def generator3_groupPerm : Equiv.Perm (Fin 15) :=
  involutionPerm generator3_group (by decide +kernel)

def generator3_matching (a : Fin 15) : Fin 15 :=
    ([0, 2, 1, 3, 5, 4, 6, 8, 7, 12, 13, 14, 9, 10, 11] : List (Fin 15))[a.val]

set_option maxRecDepth 10000 in
def generator3_matchingPerm : Equiv.Perm (Fin 15) :=
  involutionPerm generator3_matching (by decide +kernel)

def generator3_line (a : Fin 60) : Fin 60 :=
    ([1, 0, 3, 2, 6, 7, 4, 5, 16, 17, 18, 19, 22, 23, 20, 21, 8, 9, 10, 11, 14, 15, 12, 13, 25, 24, 28, 29, 26, 27, 36, 37, 40, 41, 38, 39, 30, 31, 34, 35, 32, 33, 44, 45, 42, 43, 52, 53, 50, 51, 48, 49, 46, 47, 56, 58, 54, 59, 55, 57] : List (Fin 60))[a.val]

set_option maxRecDepth 10000 in
def generator3_linePerm : Equiv.Perm (Fin 60) :=
  involutionPerm generator3_line (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 30000000 in
lemma generator3_eligible (a : Fin 15) : ∀ b : Fin 60,
    (eligibleMask (generator3_group a)).testBit (generator3_line b).val =
      (eligibleMask a).testBit b.val := by
  fin_cases a <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 30000000 in
lemma generator3_required (a : Fin 15) : ∀ b : Fin 15,
    (vertexMask (generator3_group a)).testBit (generator3_matching b).val =
      (vertexMask a).testBit b.val := by
  fin_cases a <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 30000000 in
lemma generator3_endpoints (a : Fin 60) : ∀ b : Fin 15,
    (endpointMask (generator3_line a)).testBit (generator3_matching b).val =
      (endpointMask a).testBit b.val := by
  fin_cases a <;> decide +kernel

def generator3 : Symmetry where
  group := generator3_groupPerm
  matching := generator3_matchingPerm
  line := generator3_linePerm
  fixed := rfl
  preserves_eligible := generator3_eligible
  preserves_required := generator3_required
  preserves_endpoints := generator3_endpoints

end WeightFifteenIndexedSymmetry

namespace WeightFifteenIndexedSearch

open Finset WeightFifteenLargeCatalog WeightFifteenIndexedSymmetry FiniteSearchMasks

def permuteWord (line : Equiv.Perm (Fin 60)) (word : Nat) : Nat :=
  bitMask (List.finRange 60) fun p => word.testBit (line.symm p).val

lemma permuteWord_bit (line : Equiv.Perm (Fin 60)) (word : Nat) (i : Fin 60) :
    (permuteWord line word).testBit i.val = word.testBit (line.symm i).val := by
  have inside : i.val < (List.finRange 60).length := by simpa using i.isLt
  unfold permuteWord
  rw [bitMask_getElem_testBit _ _ _ inside]
  simp [List.getElem_finRange]

lemma permuteWord_outside (line : Equiv.Perm (Fin 60)) (word b : Nat) (outside : 60 ≤ b) :
    (permuteWord line word).testBit b = false := by
  cases eq : (permuteWord line word).testBit b with
  | false => rfl
  | true =>
    obtain ⟨x, found, _⟩ := (bitMask_testBit _ _ _).mp eq
    have beyond : (List.finRange 60).length ≤ b := by simpa using outside
    simp [List.getElem?_eq_none beyond] at found

lemma star_mask_map (line : Equiv.Perm (Fin 60)) (star : Finset (Fin 60)) :
    pack ((star.map line.toEmbedding).image Fin.val) = permuteWord line (pack (star.image Fin.val)) := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases inside : b < 60
  · let i : Fin 60 := ⟨b, inside⟩
    change (pack ((star.map line.toEmbedding).image Fin.val)).testBit i.val = _
    rw [permuteWord_bit line _ i]
    apply Bool.eq_iff_iff.mpr
    simp only [pack_testBit, i.isLt, true_and, (line.symm i).isLt]
    have m (s : Finset (Fin 60)) (p : Fin 60) : p.val ∈ s.image Fin.val ↔ p ∈ s := by
      constructor
      · intro h
        obtain ⟨q, hq, eq⟩ := mem_image.mp h
        exact (Fin.ext eq : q = p) ▸ hq
      · exact mem_image_of_mem _
    rw [m, m]
    constructor
    · intro member
      obtain ⟨p, hp, eq⟩ := Finset.mem_map.mp member
      exact (line.symm_apply_eq.mpr eq.symm).symm ▸ hp
    · intro member
      exact Finset.mem_map.mpr ⟨line.symm i, member, line.apply_symm_apply i⟩
  · rw [permuteWord_outside line _ b (Nat.le_of_not_gt inside)]
    cases bit : (pack ((star.map line.toEmbedding).image Fin.val)).testBit b with
    | false => rfl
    | true => exact (inside ((pack_testBit _ b).mp bit).1).elim

theorem transport_partition (symmetry : Symmetry)
    (s : Fin 15 → Fin 6 → Finset (Fin 60)) (valid : IsCover s) :
    ∃ index : Fin 6 → Nat,
      (∀ i, (directCatalog 0)[index i]? = some (permuteWord symmetry.line (pack ((s 0 i).image Fin.val)))) ∧
      Finset.univ.image index ∈ partitionCatalog := by
  have new := symmetry.applyCover_correct s valid
  obtain ⟨where_at, listed⟩ :=
    partitionCatalog_complete (symmetry.applyCover s 0) (new.1 0) (new.2.1 0) (new.2.2.1 0)
  refine ⟨_, fun i => ?_, listed⟩
  have eq := where_at i
  rwa [Symmetry.first_group_perm, star_mask_map] at eq

end WeightFifteenIndexedSearch

namespace WeightFifteenIndexedSymmetry

open WeightFifteenLargeCatalog

def Symmetry.identity : Symmetry :=
  ⟨Equiv.refl _, Equiv.refl _, Equiv.refl _, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

def Symmetry.compose (first second : Symmetry) : Symmetry where
  group := first.group.trans second.group
  matching := first.matching.trans second.matching
  line := first.line.trans second.line
  fixed := by simp only [Equiv.trans_apply, first.fixed, second.fixed]
  preserves_eligible g p :=
    (second.preserves_eligible (first.group g) (first.line p)).trans (first.preserves_eligible g p)
  preserves_required g m :=
    (second.preserves_required (first.group g) (first.matching m)).trans (first.preserves_required g m)
  preserves_endpoints p m :=
    (second.preserves_endpoints (first.line p) (first.matching m)).trans (first.preserves_endpoints p m)

def symmetryFromGenerators (word : List (Fin 4)) : Symmetry :=
  word.foldl (fun accumulated i =>
    accumulated.compose (([generator0, generator1, generator2, generator3] : List Symmetry)[i.val]))
    Symmetry.identity

end WeightFifteenIndexedSymmetry

namespace WeightFifteenIndexedSearch

open Finset WeightFifteenIndexedSymmetry FiniteSearchMasks

def partitionKey (s : Fin 15 → Fin 6 → Finset (Fin 60)) : Nat :=
  bitMask (List.range 344) fun index =>
    (List.finRange 6).any fun i => (directCatalog 0).idxOf (pack ((s 0 i).image Fin.val)) == index

theorem least_first_partition (s : Fin 15 → Fin 6 → Finset (Fin 60)) (valid : IsCover s) :
    ∃ best : Fin 15 → Fin 6 → Finset (Fin 60), IsCover best ∧
      ∀ a : Symmetry, partitionKey best ≤ partitionKey (a.applyCover best) := by
  classical
  let realization (key : Nat) := ∃ c : Fin 15 → Fin 6 → Finset (Fin 60),
    IsCover c ∧ partitionKey c = key
  have existsRealization : ∃ key, realization key := ⟨partitionKey s, s, valid, rfl⟩
  obtain ⟨best, correct, minimum⟩ := Nat.find_spec existsRealization
  refine ⟨best, correct, fun a => ?_⟩
  rw [minimum]
  exact Nat.find_min' existsRealization ⟨a.applyCover best, a.applyCover_correct best correct, rfl⟩

end WeightFifteenIndexedSearch

namespace WeightFifteenIndexedSearch

open Finset WeightFifteenIndexedSymmetry FiniteSearchMasks

def firstGroupIndices (s : Fin 15 → Fin 6 → Finset (Fin 60)) : Finset Nat :=
  Finset.univ.image fun i => (directCatalog 0).idxOf (pack ((s 0 i).image Fin.val))

def indexCode (indices : Finset Nat) : Nat :=
  bitMask (List.range 344) fun i => decide (i ∈ indices)

lemma partitionKey_eq (s : Fin 15 → Fin 6 → Finset (Fin 60)) :
    partitionKey s = indexCode (firstGroupIndices s) := by
  unfold partitionKey indexCode
  congr 1
  funext i
  apply Bool.eq_iff_iff.mpr
  simp [List.any_eq_true, firstGroupIndices, Finset.mem_image]

lemma firstGroupIndices_complete (s : Fin 15 → Fin 6 → Finset (Fin 60)) (valid : IsCover s) :
    firstGroupIndices s ∈ partitionCatalog :=
  (partitionCatalog_complete (s 0) (valid.1 0) (valid.2.1 0) (valid.2.2.1 0)).2

structure RelabelIndex (a : Symmetry) where
  apply : Nat → Nat
  agrees : ∀ j star, (directCatalog 0)[j]? = some star →
    (directCatalog 0).idxOf (permuteWord a.line star) = apply j

lemma firstGroupIndices_relabel (a : Symmetry) (index : RelabelIndex a)
    (s : Fin 15 → Fin 6 → Finset (Fin 60)) (valid : IsCover s) :
    firstGroupIndices (a.applyCover s) = (firstGroupIndices s).image index.apply := by
  unfold firstGroupIndices
  rw [Finset.image_image]
  apply Finset.image_congr
  intro i _
  simp only [Function.comp_def, Symmetry.first_group_perm, star_mask_map]
  exact index.agrees _ _ ((partitionCatalog_complete (s 0) (valid.1 0)
    (valid.2.1 0) (valid.2.2.1 0)).1 i)

/-- A certificate of a smaller relabeling excludes any partition outside the representatives. -/
theorem has_representative (representatives : Finset (Finset Nat))
    (improves : ∀ p ∈ partitionCatalog, p ∉ representatives →
      ∃ (a : Symmetry) (index : RelabelIndex a), indexCode (p.image index.apply) < indexCode p)
    (s : Fin 15 → Fin 6 → Finset (Fin 60)) (valid : IsCover s) :
    ∃ best : Fin 15 → Fin 6 → Finset (Fin 60), IsCover best ∧ firstGroupIndices best ∈ representatives := by
  obtain ⟨best, good, least⟩ := least_first_partition s valid
  refine ⟨best, good, ?_⟩
  by_contra outside
  obtain ⟨a, index, smaller⟩ := improves _ (firstGroupIndices_complete best good) outside
  have lower := least a
  rw [partitionKey_eq, partitionKey_eq, firstGroupIndices_relabel a index best good] at lower
  exact (Nat.not_lt_of_ge lower) smaller

end WeightFifteenIndexedSearch

namespace WeightFifteenConflictRows

open Finset

def setBitPositions : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, word =>
    if word = 0 then []
    else word.log2 :: setBitPositions fuel (word ^^^ 2^word.log2)

lemma setBitPositions_sound (fuel word position : Nat) (found : position ∈ setBitPositions fuel word) :
    word.testBit position = true := by
  induction fuel generalizing word with
  | zero => simp [setBitPositions] at found
  | succ fuel ih =>
    by_cases empty : word = 0
    · simp [setBitPositions, empty] at found
    simp only [setBitPositions, if_neg empty, List.mem_cons] at found
    rcases found with equal | rest
    · exact equal.symm ▸ Nat.testBit_log2 empty
    · have bit := ih (word ^^^ 2^word.log2) rest
      by_cases equal : position = word.log2
      · exact equal.symm ▸ Nat.testBit_log2 empty
      · simpa only [Nat.testBit_xor, Nat.testBit_two_pow, Ne.symm equal, decide_false, Bool.xor_false] using bit

end WeightFifteenConflictRows

namespace WeightFifteenConflictRows

lemma clearHighest_lt (word : Nat) (nonzero : word ≠ 0) : word ^^^ 2^word.log2 < 2^word.log2 := by
  apply Nat.lt_of_testBit word.log2
  · simp only [Nat.testBit_xor, Nat.testBit_log2 nonzero, Nat.testBit_two_pow_self, Bool.xor_true, Bool.not_true]
  · exact Nat.testBit_two_pow_self
  · intro i higher
    have less : word < 2^i := Nat.lt_log2_self.trans_le
      (Nat.pow_le_pow_right (by decide) higher)
    have power_less : 2^word.log2 < 2^i := Nat.pow_lt_pow_right (by decide) higher
    simp only [Nat.testBit_xor, Nat.testBit_lt_two_pow less, Nat.testBit_lt_two_pow power_less, Bool.xor_false]

theorem setBitPositions_complete (fuel word position : Nat) (bound : word < 2^fuel)
    (bit : word.testBit position = true) : position ∈ setBitPositions fuel word := by
  induction fuel generalizing word with
  | zero =>
    have empty : word = 0 := by simpa using bound
    simp [empty] at bit
  | succ fuel ih =>
    have nonzero : word ≠ 0 := by intro h; simp [h] at bit
    simp only [setBitPositions, if_neg nonzero, List.mem_cons]
    by_cases pivot : position = word.log2
    · exact Or.inl pivot
    · apply Or.inr (ih (word ^^^ 2^word.log2) _ _)
      · have high : word.log2 ≤ fuel := Nat.le_of_lt_succ ((Nat.log2_lt nonzero).mpr bound)
        exact (clearHighest_lt word nonzero).trans_le (Nat.pow_le_pow_right (by decide) high)
      · simpa only [Nat.testBit_xor, Nat.testBit_two_pow, Ne.symm pivot, decide_false, Bool.xor_false] using bit

lemma fold_or (words : List Nat) (i : Nat) :
    (words.foldr Nat.lor 0).testBit i = true ↔ ∃ w ∈ words, w.testBit i = true := by
  induction words with
  | nil => simp
  | cons w rest ih =>
    change (w ||| rest.foldr Nat.lor 0).testBit i = true ↔ _
    simp only [Nat.testBit_lor, Bool.or_eq_true, ih, List.mem_cons]
    constructor
    · rintro (found | ⟨u, member, found⟩)
      · exact ⟨w, Or.inl rfl, found⟩
      · exact ⟨u, Or.inr member, found⟩
    · rintro ⟨u, rfl | member, found⟩
      · exact Or.inl found
      · exact Or.inr ⟨u, member, found⟩


end WeightFifteenConflictRows


namespace WeightFifteenIndexedSearch

open FiniteSearchMasks WeightFifteenConflictRows

def fastPermuteWord (line : Equiv.Perm (Fin 60)) (word : Nat) : Nat :=
  ((setBitPositions 60 word).map fun i => 2^(line (Fin.ofNat 60 i)).val).foldr Nat.lor 0

lemma fastPermuteWord_iff (line : Equiv.Perm (Fin 60)) (word i : Nat) (small : word < 2^60) :
    (fastPermuteWord line word).testBit i = true ↔
      ∃ p : Fin 60, word.testBit p.val = true ∧ (line p).val = i := by
  rw [fastPermuteWord, fold_or]
  constructor
  · rintro ⟨mask, at_row, bit⟩
    obtain ⟨j, present, rfl⟩ := List.mem_map.mp at_row
    have hit := setBitPositions_sound 60 word j present
    have below : j < 60 := by
      by_contra outside
      have less : word < 2^j := small.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt outside))
      exact Bool.false_ne_true ((Nat.testBit_lt_two_pow less).symm.trans hit)
    let p : Fin 60 := ⟨j, below⟩
    have eq : Fin.ofNat 60 j = p := Fin.ext (Nat.mod_eq_of_lt below)
    rw [eq, Nat.testBit_two_pow] at bit
    exact ⟨p, hit, of_decide_eq_true bit⟩
  · rintro ⟨p, hit, rfl⟩
    have present := setBitPositions_complete 60 word p.val small hit
    refine ⟨2^(line p).val, ?_, Nat.testBit_two_pow_self⟩
    exact List.mem_map.mpr ⟨p.val, present, by rw [show Fin.ofNat 60 p.val = p from Fin.ext (Nat.mod_eq_of_lt p.isLt)]⟩

theorem fastPermuteWord_correct (line : Equiv.Perm (Fin 60)) (word : Nat) (small : word < 2^60) :
    fastPermuteWord line word = permuteWord line word := by
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  rw [fastPermuteWord_iff line word i small]
  by_cases inside : i < 60
  · let p : Fin 60 := ⟨i, inside⟩
    change (∃ q : Fin 60, word.testBit q.val = true ∧ (line q).val = p.val) ↔
      (permuteWord line word).testBit p.val = true
    simp only [permuteWord_bit, Fin.val_inj]
    constructor
    · rintro ⟨q, hit, related⟩
      rwa [← related, Equiv.symm_apply_apply]
    · intro hit
      exact ⟨line.symm p, hit, line.apply_symm_apply p⟩
  · rw [permuteWord_outside line word i (Nat.le_of_not_gt inside)]
    constructor
    · rintro ⟨p, _, rfl⟩
      exact (inside (line p).isLt).elim
    · simp

end WeightFifteenIndexedSearch

namespace WeightFifteenRankAgreement

open Finset FiniteSearchMasks WeightFifteenLargeCatalog WeightFifteenConflictRows
open WeightFifteenIndexedSearch

def recurse (endpoint : Fin 60 → Nat) (options : List (Fin 60)) (fuel remaining : Nat) :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun w => if w=0 then [0] else [])
    (fun _ next w => if w=0 then [0] else options.flatMap fun p =>
      let e := endpoint p
      if e.testBit w.log2 && (e &&& w == e) then (next (w ^^^ e)).map (fun u => 2^p.val ||| u) else [])
    fuel remaining

lemma recurse_eq (endpoint : Fin 60 → Nat) (options : List (Fin 60)) (fuel remaining : Nat) :
    recurse endpoint options fuel remaining =
      enumerateMasks (options.map fun p => (endpoint p, p.val)) fuel remaining := by
  induction fuel generalizing remaining with
  | zero => simp [recurse, enumerateMasks]
  | succ fuel ih =>
    by_cases empty : remaining = 0
    · simp [recurse, enumerateMasks, empty]
    · change (if remaining = 0 then [0] else options.flatMap fun p =>
        if (endpoint p).testBit remaining.log2 && (endpoint p &&& remaining == endpoint p) then
          (recurse endpoint options fuel (remaining ^^^ endpoint p)).map (fun u => 2^p.val ||| u) else []) = _
      simp only [if_neg empty, enumerateMasks, beq_iff_eq, List.flatMap_map]
      apply List.flatMap_congr
      intro p _
      rw [ih]

lemma option_rows (options : List (Fin 60)) (eligible : Fin 60 → Bool) (endpoint : Fin 60 → Nat) :
    (options.filter eligible).map (fun p => (endpoint p, p.val)) =
      options.filterMap (fun p => if eligible p then some (endpoint p, p.val) else none) := by
  induction options with
  | nil => rfl
  | cons p rest ih => cases ok : eligible p <;> simp [ok, ih]

lemma word_from_fins (star : Finset (Fin 60)) :
    (((List.finRange 60).map fun p => if p∈star then 2^p.val else 0).foldr Nat.lor 0) =
      pack (star.image Fin.val) := by
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  rw [fold_or, star_mask_bit]
  constructor
  · rintro ⟨mask, member, bit⟩
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp member
    by_cases present : p ∈ star
    · exact ⟨p, present, by simpa [present, Nat.testBit_two_pow] using bit⟩
    · simp [present] at bit
  · rintro ⟨p, present, rfl⟩
    exact ⟨_, List.mem_map_of_mem (List.mem_finRange p), by simp [present]⟩

lemma word_from_range (n : Nat) (uses : Nat → Bool) :
    (((List.range n).map fun i => if uses i then 2^i else 0).foldr Nat.lor 0) =
      bitMask (List.range n) uses := by
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  rw [fold_or, bitMask_testBit]
  constructor
  · rintro ⟨mask, member, bit⟩
    obtain ⟨j, listed, rfl⟩ := List.mem_map.mp member
    cases select : uses j with
    | false => simp [select] at bit
    | true =>
      have eq : j = i := by simpa [select, Nat.testBit_two_pow] using bit
      subst i
      have lt : j < (List.range n).length := by simpa using List.mem_range.mp listed
      exact ⟨j, by rw [List.getElem?_eq_getElem lt, List.getElem_range], select⟩
  · rintro ⟨j, at_i, used⟩
    obtain ⟨hi, eq⟩ := List.getElem?_eq_some_iff.mp at_i
    rw [List.getElem_range] at eq
    subst j
    refine ⟨2^i, List.mem_map.mpr ⟨i, List.mem_range.mpr (by simpa using hi), ?_⟩,
      Nat.testBit_two_pow_self⟩
    simp [used]

end WeightFifteenRankAgreement

namespace WeightFifteenLargeCatalog

lemma row_testBit (packed width base index : Nat) (within : index < width) :
    (((packed >>> (width * base)) &&& (2^width-1)).testBit index) =
      packed.testBit (width * base + index) := by
  simp only [Nat.testBit_land, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
    decide_eq_true within, Bool.and_true, Nat.add_comm]


set_option maxRecDepth 10000 in
lemma row_eligible : ∀ g : Fin 15,
    ((0xfffc3ef80fafa00f3bbfb03bed00eeaeefc0bef00bdbdcf43b5efe00e7db781eef77db7007715f55fdd75f5f003c3740d75d7ddf5d5c1dd01e7d77fa4b5ea76c0beee5fa2a83ababebbbaf00cccf3cf3f3f3f033333cf3cfcfcffc003cf3cf3f3f3ffffc0000fcfcfcfffffffff000000 : Nat) >>> (60 * g.val)) &&& (2^60-1) = eligibleMask g := by decide +kernel

lemma packed_eligible (g : Fin 15) (p : Fin 60) :
    (0xfffc3ef80fafa00f3bbfb03bed00eeaeefc0bef00bdbdcf43b5efe00e7db781eef77db7007715f55fdd75f5f003c3740d75d7ddf5d5c1dd01e7d77fa4b5ea76c0beee5fa2a83ababebbbaf00cccf3cf3f3f3f033333cf3cfcfcffc003cf3cf3f3f3ffffc0000fcfcfcfffffffff000000 : Nat).testBit (60*g.val+p.val) = (eligibleMask g).testBit p.val := by
  rw [← row_testBit _ _ _ _ p.isLt, row_eligible]

set_option maxRecDepth 10000 in
lemma row_vertex : ∀ g : Fin 15,
    ((0x1fedbef6efdbf6f77bf5bff76df7edf6fdf6df8fffe3fff8fffe3fff8 : Nat) >>> (15 * g.val)) &&& (2^15-1) = vertexMask g := by decide +kernel

lemma packed_vertex (g : Fin 15) (m : Fin 15) :
    (0x1fedbef6efdbf6f77bf5bff76df7edf6fdf6df8fffe3fff8fffe3fff8 : Nat).testBit (15*g.val+m.val) = (vertexMask g).testBit m.val := by
  rw [← row_testBit _ _ _ _ m.isLt, row_vertex]

set_option maxRecDepth 10000 in
lemma row_endpoint : ∀ p : Fin 60,
    ((0x5000600220014008400880208011000a000c01040108011000a0202020401080110201020200840088005000604020404040804100220014200410081010082008400888008801040202040208011000a000c80044008401040201040108011000a400240042008201020202040108011 : Nat) >>> (15 * p.val)) &&& (2^15-1) = endpointMask p := by decide +kernel

lemma packed_endpoint (p : Fin 60) (m : Fin 15) :
    (0x5000600220014008400880208011000a000c01040108011000a0202020401080110201020200840088005000604020404040804100220014200410081010082008400888008801040202040208011000a000c80044008401040201040108011000a400240042008201020202040108011 : Nat).testBit (15*p.val+m.val) = (endpointMask p).testBit m.val := by
  rw [← row_testBit _ _ _ _ m.isLt, row_endpoint]

end WeightFifteenLargeCatalog



namespace WeightFifteenRankAgreement

open WeightFifteenLargeCatalog WeightFifteenIndexedSearch WeightFifteenIndexedSymmetry

def sourceAllowed (g : Fin 15) (p : Fin 60) := (0xfffc3ef80fafa00f3bbfb03bed00eeaeefc0bef00bdbdcf43b5efe00e7db781eef77db7007715f55fdd75f5f003c3740d75d7ddf5d5c1dd01e7d77fa4b5ea76c0beee5fa2a83ababebbbaf00cccf3cf3f3f3f033333cf3cfcfcffc003cf3cf3f3f3ffffc0000fcfcfcfffffffff000000:Nat).testBit (60*g.val+p.val)
def sourceRequired (g m : Fin 15) := (0x1fedbef6efdbf6f77bf5bff76df7edf6fdf6df8fffe3fff8fffe3fff8:Nat).testBit (15*g.val+m.val)
def sourceEndpoints (p : Fin 60) := ((0x5000600220014008400880208011000a000c01040108011000a0202020401080110201020200840088005000604020404040804100220014200410081010082008400888008801040202040208011000a000c80044008401040201040108011000a400240042008201020202040108011:Nat) >>> (15*p.val)) &&& 32767

def sourceValid (s : Fin 15 → Fin 6 → Finset (Fin 60)) :=
    (∀ g i p, p∈s g i → sourceAllowed g p = true) ∧
    (∀ g i m, sourceRequired g m = true → ∃! p, p∈s g i ∧ (sourceEndpoints p).testBit m.val = true) ∧
    (∀ g p, sourceAllowed g p = true → ∃! i, p∈s g i) ∧
    ∀ g h i j, g ≠ h → (s g i ∩ s h j).card ≤ 1

def sourceCatalogue : List Nat := recurse sourceEndpoints
  ((List.finRange 60).filter fun p => decide (sourceAllowed 0 p = true)) 60 32760

def sourceRank (s : Fin 15 → Fin 6 → Finset (Fin 60)) : Nat :=
  let word (star : Finset (Fin 60)) := ((List.finRange 60).map fun p => if p∈star then 2^p.val else 0).foldr Nat.lor 0
  ((List.range 344).map fun j =>
    if (List.finRange 6).any (fun i => sourceCatalogue.idxOf (word (s 0 i)) == j) then 2^j else 0).foldr Nat.lor 0

lemma sourceEndpoints_eq (p : Fin 60) : sourceEndpoints p = endpointMask p := row_endpoint p

lemma sourceValid_eq (s : Fin 15 → Fin 6 → Finset (Fin 60)) : sourceValid s ↔ IsCover s := by
  unfold sourceValid IsCover sourceAllowed sourceRequired
  simp only [packed_eligible, packed_vertex, sourceEndpoints_eq]

lemma sourceCatalogue_eq : sourceCatalogue = directCatalog 0 := by
  unfold sourceCatalogue directCatalog indexOptions
  rw [recurse_eq, option_rows]
  unfold sourceAllowed
  simp only [packed_eligible, sourceEndpoints_eq, Bool.decide_eq_true]
  rfl

lemma sourceRank_eq (s : Fin 15 → Fin 6 → Finset (Fin 60)) : sourceRank s = partitionKey s := by
  unfold sourceRank partitionKey
  simp only [sourceCatalogue_eq, word_from_fins, word_from_range]

set_option maxRecDepth 12000 in
theorem middle_case_equivalence : OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H2_R1_H2_R1_H2_R1_H1_R1_H3_R1.H2 ↔
    ¬ ∃ s, IsCover s ∧ (∀ t, IsCover t → partitionKey s ≤ partitionKey t) ∧
      0x1000000080000000000010000000000000000002000000400000000000100000000000000 < partitionKey s ∧ partitionKey s ≤ 0x1000000200000000000004000000000000000080000000800000000000100000000000000 := by
  change (¬ ∃ s, sourceValid s ∧ (∀ t, sourceValid t → sourceRank s ≤ sourceRank t) ∧
      0x1000000080000000000010000000000000000002000000400000000000100000000000000 < sourceRank s ∧ sourceRank s ≤ 0x1000000200000000000004000000000000000080000000800000000000100000000000000) ↔ _
  simp only [sourceValid_eq, sourceRank_eq]

end WeightFifteenRankAgreement

namespace WeightFifteenIndexedSearch

open Finset FiniteSearchMasks WeightFifteenIndexedSymmetry

lemma indexCode_bit (indices : Finset Nat) (i : Nat) :
    (indexCode indices).testBit i = true ↔ i < 344 ∧ i ∈ indices := by
  rw [indexCode, bitMask_testBit]
  by_cases short : i < 344
  · have lt : i < (List.range 344).length := by simpa using short
    rw [List.getElem?_eq_getElem lt, List.getElem_range]
    simp [short]
  · have le : (List.range 344).length ≤ i := by simpa using Nat.le_of_not_gt short
    rw [List.getElem?_eq_none le]
    simp [short]

lemma indexCode_lt_of_bound (indices : Finset Nat) (bound : Nat)
    (small : ∀ i ∈ indices, i < bound) : indexCode indices < 2^bound := by
  by_cases zero : indexCode indices = 0
  · rw [zero]
    exact Nat.two_pow_pos _
  · have member := ((indexCode_bit _ _).mp (Nat.testBit_log2 zero)).2
    exact (Nat.log2_lt zero).mp (small _ member)

lemma maximum_first_choice (s : Fin 15 → Fin 6 → Finset (Fin 60))
    (minimum : Nat) (above : 2^minimum ≤ partitionKey s) :
    ∃ start, minimum ≤ start ∧ start < 344 ∧ start ∈ firstGroupIndices s ∧
      ∀ i ∈ firstGroupIndices s, i < 344 → i ≤ start := by
  rw [partitionKey_eq] at above
  let indices := firstGroupIndices s
  have nonzero : indexCode indices ≠ 0 := by
    intro h
    have hp : 0 < 2^minimum := Nat.two_pow_pos _
    change 2^minimum ≤ indexCode indices at above
    rw [h] at above
    omega
  let top := (indexCode indices).log2
  have top_bit := Nat.testBit_log2 nonzero
  obtain ⟨top_lt, top_in⟩ := (indexCode_bit indices top).mp top_bit
  refine ⟨top, (Nat.le_log2 nonzero).mpr above, top_lt, top_in, ?_⟩
  intro j hj j_lt
  by_contra not_le
  have too_big : top + 1 ≤ j := by omega
  have bit := (indexCode_bit indices j).mpr ⟨j_lt,hj⟩
  have smaller : indexCode indices < 2^j := Nat.lt_log2_self.trans_le
    (Nat.pow_le_pow_right (by decide) too_big)
  exact Bool.false_ne_true ((Nat.testBit_lt_two_pow smaller).symm.trans bit)

/-- A relabeling that sends every possible remaining index below a selected index improves
    every completion of the current partition. -/
theorem prefix_orbit_cut (s : Fin 15 → Fin 6 → Finset (Fin 60)) (valid : IsCover s)
    (minimal : ∀ t, IsCover t → partitionKey s ≤ partitionKey t)
    (a : Symmetry) (index : RelabelIndex a) (potential start : Nat)
    (allowed : ∀ i ∈ firstGroupIndices s, potential.testBit i = true)
    (selected : (partitionKey s).testBit start = true)
    (all_below : ∀ i, potential.testBit i = true → index.apply i < start) : False := by
  have cannot_rise (j : Nat) (hj : j ∈ (firstGroupIndices s).image index.apply) : j < start := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact all_below i (allowed i hi)
  have below := indexCode_lt_of_bound ((firstGroupIndices s).image index.apply) start cannot_rise
  have never_smaller := minimal (a.applyCover s) (a.applyCover_correct s valid)
  rw [partitionKey_eq (a.applyCover s), firstGroupIndices_relabel a index s valid] at never_smaller
  have hidden := Nat.testBit_lt_two_pow (never_smaller.trans_lt below)
  exact Bool.false_ne_true (hidden.symm.trans selected)

end WeightFifteenIndexedSearch

namespace WeightFifteenIndexedSearch

open WeightFifteenIndexedSymmetry

theorem permuteWord_trans (first next : Equiv.Perm (Fin 60)) (word : Nat) :
    permuteWord (first.trans next) word = permuteWord next (permuteWord first word) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases inside : i < 60
  · let p : Fin 60 := ⟨i, inside⟩
    change (permuteWord (first.trans next) word).testBit p.val =
      (permuteWord next (permuteWord first word)).testBit p.val
    rw [permuteWord_bit, permuteWord_bit, permuteWord_bit]
    rfl
  · simp only [permuteWord_outside _ _ i (Nat.le_of_not_gt inside)]

structure CatalogueRelabeling (a : Symmetry) where
  move : Nat → Nat
  agrees : ∀ i star, (directCatalog 0)[i]? = some star →
    (directCatalog 0)[move i]? = some (permuteWord a.line star)

def CatalogueRelabeling.compose {a b : Symmetry} (first : CatalogueRelabeling a)
    (next : CatalogueRelabeling b) : CatalogueRelabeling (a.compose b) where
  move i := next.move (first.move i)
  agrees i star found := by
    change (directCatalog 0)[next.move (first.move i)]? = some (permuteWord (a.line.trans b.line) star)
    rw [permuteWord_trans]
    exact next.agrees _ _ (first.agrees _ _ found)

def CatalogueRelabeling.toRelabelIndex {a : Symmetry} (action : CatalogueRelabeling a)
    (nodup : (directCatalog 0).Nodup) : RelabelIndex a where
  apply := action.move
  agrees i star found := by
    obtain ⟨bound, same⟩ := List.getElem?_eq_some_iff.mp (action.agrees i star found)
    rw [← same]
    exact nodup.idxOf_getElem (action.move i) bound

end WeightFifteenIndexedSearch

namespace WeightFifteenConcreteGenerators

open WeightFifteenIndexedSearch WeightFifteenIndexedSymmetry WeightFifteenLargeCatalog

def options : List (Nat × Nat) := [(136, 24), (264, 25), (520, 26), (2056, 27), (4104, 28), (16392, 29), (80, 30), (272, 31), (1040, 32), (2064, 33), (4112, 34), (8208, 35), (96, 36), (160, 37), (544, 38), (1056, 39), (8224, 40), (16416, 41), (1088, 42), (2112, 43), (8256, 44), (16448, 45), (640, 46), (2176, 47), (4224, 48), (8320, 49), (768, 50), (1280, 51), (4352, 52), (16640, 53), (8704, 54), (16896, 55), (5120, 56), (17408, 57), (6144, 58), (10240, 59)]

def expected : List Nat := [1416755628998656, 2542380657934336, 4583349116993536, 4649044936753152, 73192462373355520, 73324335049211904, 289360846440628224, 290552648325660672,
  2332081879252992, 1272152670076928, 1412881568497664, 1417275320041472, 4579475056492544, 4583868808036352, 72137861071110144, 73325332555366400,
  288306245138382848, 290553645831815168, 1284797053796352, 2410422082732032, 1425525952217088, 2551150981152768, 4592119440211968, 4662209011515392,
  73201232696573952, 72216201274589184, 289374010515390464, 288318889522102272, 1698213425840128, 2823838454775808, 5071231632015360, 5075625383559168,
  73746521744474112, 72629617646632960, 289919299563290624, 289919777378402304, 288798001713905664, 291045402407337984, 20275149571883008, 20407022247739392,
  20547751146160128, 18305222019383296, 22522542749122560, 22526936500666368, 22658809176522752, 22659286991634432, 90080928763740160, 90212801439596544,
  306249312831012864, 308496713524445184, 577591205412470784, 578783007297503232, 577868200738291712, 577868678553403392, 576746902888906752, 578994303582339072,
  581034794226286592, 581035272041398272, 648588786489360384, 649644385297760256, 2333198302314496, 1273269093138432, 1414006447276032, 2544304333520896,
  4580599935270912, 4650968612339712, 72138992291676160, 73194523437563904, 288307376358948864, 289362907504836608, 2341968625532928, 1286433167900672,
  2341977081249792, 2412345758318592, 1427170522038272, 2553074656739328, 4593764010033152, 4664132687101952, 72147756273106944, 72147762614894592,
  73203293760782336, 72218124950175744, 288320540433711104, 289376071579598848, 1695455788400640, 1699849539944448, 1695464244117504, 2825762130362368,
  5073155307601920, 5077549059145728, 73748644129406976, 72631541322219520, 288799925389492224, 291047326082924544, 18161735483523072, 20409136176955392,
  20277210636091392, 18161750281027584, 18302472837660672, 20549873531092992, 18302479179448320, 18306872930992128, 22524603813330944, 22528997564874752,
  90082989827948544, 90214930166317056, 306251373895221248, 308498774588653568, 576537720533286912, 578785121226719232, 576537735330791424, 577593266476679168,
  576748826564493312, 578996227257925632, 648590915216080896, 649646446361968640, 1302406151274496, 2428031180210176, 1443143505412096, 2568768534347776,
  4609736993406976, 4680105670475776, 73218850249768960, 72233825169571840, 288336513417084928, 289392044562972672, 290517532203286528, 290517669591908352,
  2358461299949568, 1302925842317312, 2358469755666432, 2428838432735232, 1443663196454912, 2569567331155968, 4610256684449792, 4680625361518592,
  72164248947523584, 72164255289311232, 73219786435198976, 72234617624592384, 288337033108127744, 289392564254015488, 1724592846536704, 2850217875472384,
  1724601302253568, 2850226331189248, 5102013259972608, 5102292365737984, 72656005523046400, 72656011864834048, 288828789683650560, 288829062447628288,
  20301528992579584, 18190872541659136, 20301537448296448, 18190887339163648, 18331609895796736, 18331616237584384, 22553324377079808, 22553740871467008,
  90107316640153600, 90107322981941248, 306280100800757760, 306280510953357312, 577621978584711168, 576566857591422976, 576566872388927488, 577622403534815232,
  578747891175129088, 578748028563750912, 576777690858651648, 576777963622629376, 580999678103912448, 580999815492534272, 648553670366986240, 648553807755608064,
  9086948475928576, 9152644295688192, 9293381649825792, 9298054507134976, 81135265250279424, 81073761251491840, 81073898640113664, 81205633927348224,
  297242145318764544, 297242282707386368, 9083074415427584, 9087468166971392, 9083082871144448, 9153451548213248, 9294180446633984, 9298574198177792,
  81136262756433920, 81206631433502720, 9095718799147008, 9165808370450432, 9095727254863872, 9166095931932672, 9306545724588032, 9306824830353408,
  81082531574710272, 81082668963332096, 297255309393526784, 297255446782148608, 9574830990950400, 9579224742494208, 9574839446667264, 9579512303976448,
  81628019331956736, 81627820622610432, 297800598441426944, 297801076256538624, 27026142108057600, 27030535859601408, 27162408535457792, 27162886350569472,
  27026150563774464, 27030960809705472, 27303145889595392, 27303623704707072, 99079330449063936, 99079269128339456, 315252046947155968, 315252524762267648,
  585538393585221632, 585538871400333312, 585472504290607104, 585472641679228928, 585749499616428032, 585749977431539712, 657525684175896576, 657525821564518400,
  38289564992798720, 38421437668655104, 38562175022792704, 36319652237803520, 40536966625755136, 40541776871686144, 108095358982160384, 108227231658016768,
  324263743049433088, 326511076080353280, 36175034481377280, 38422435174809600, 38290509633945600, 36175049278881792, 36315771835514880, 38563172528947200,
  36315778177302528, 36320171928846336, 40537902811185152, 40542296562728960, 108096288825802752, 108228229164171264, 324264672893075456, 326512073586507776,
  38298335316017152, 36187678865096704, 38298343771734016, 36187693662601216, 36328416219234304, 36328422561021952, 40550130700517376, 40550547194904576,
  108104122963591168, 108104129305378816, 324276907124195328, 324277317276794880, 38843624363917312, 36601095237140480, 38843632819634176, 36601110034644992,
  41095419748417536, 41095897563529216, 108649412011491328, 108649418353278976, 324822196172095488, 324822673987207168, 612494087223771136, 614741487917203456,
  612494102021275648, 614741435052195840, 612771097347096576, 612771575162208256, 616993221980979200, 616993699796090880, 684547281906565120, 684547214244052992,
  145250056142848000, 145381928818704384, 145522666172841984, 144405768416788480, 148689259660836864, 148627755662049280, 148627893050671104, 148759628337905664,
  432416036084514816, 433471567230402560, 144195454840602624, 145382926324858880, 144195469638107136, 145251000783994880, 145523663678996480, 144406560871809024,
  148690257166991360, 148760625844060160, 432417033590669312, 433472564736557056, 145258826466066432, 144273795044081664, 145258834921783296, 144273809841586176,
  144414532398219264, 144414538740006912, 148636525985267712, 148636663373889536, 432363296067158016, 432363433455779840, 145804115513966592, 144687211416125440,
  145804123969683456, 144687226213629952, 149182013742514176, 149181815033167872, 432908585115058176, 432908790166192128, 162138522533232640, 162270395209089024,
  162138537330737152, 162270410006593536, 162411132563226624, 162411138905014272, 166633324859621376, 166633263538896896, 450360101283299328, 450360033620787200,
  720646380258852864, 721701979067252736, 720646395056357376, 721701926202245120, 720857486290059264, 720857691341193216, 725079678586454016, 725079815975075840]

set_option maxRecDepth 20000 in
lemma options_agree : indexOptions 0 = options := by decide +kernel

set_option maxHeartbeats 300000000 in
set_option maxRecDepth 100000 in
lemma arithmetic : enumerateMasks options 60 32760 = expected := by rfl

lemma actual_catalog : enumerateMasks (indexOptions 0) 60 (vertexMask 0) = expected := by
  rw [options_agree]
  exact arithmetic

set_option maxRecDepth 20000 in
lemma expected_length : expected.length = 344 := by rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 400000000 in
lemma expected_nodup : expected.Nodup := by decide +kernel

inductive Lookup
  | leaf (value : Nat)
  | node (threshold : Nat) (left right : Lookup)

def Lookup.lookup (table : Lookup) (i : Nat) : Nat :=
  match table with
  | .leaf value => value
  | .node threshold left right => if i < threshold then left.lookup i else right.lookup i

def Lookup.block (table : Lookup) (width bits index : Nat) : Nat :=
  ((table.lookup (index / width)) >>> (bits * (index % width))) &&& (2^bits - 1)

def stars : Lookup := (.node 21 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf 0x408401820000000404042820000000104801820000000104082820000000010844820000000010488820000000009084820000000005088820000000) (.leaf 0x1048100600000001004900a0000000010490120000000010450220000000005090120000000005050220000000004850420000000008490420000000)) (.node 3 (.leaf 0x109041200000000105082200000000091042200000000051082200000000089044200000000049084200000004084100600000004004500a0000000) (.node 4 (.leaf 0x1208412000000001204422000000000a0844200000000060884200000004005080a00000004041021200000001009040a0000000104102220000000) (.leaf 0x4880142000000004808242000000040a0040600000004020440a00000004060080600000004060011200000001020840a0000000106001220000000)))) (.node 7 (.node 6 (.leaf 0x1408010a00000001400820a00000000508080600000000508011200000000500821200000000500422200000000410880a0000000049001220000000) (.leaf 0x8090040600000008010440a00000008050080600000008050011200000008084014200000008040424200000004480020600000004400420a0000000)) (.node 8 (.leaf 0x90a08040000000050608080000000048608100000000084a08100000009040020600000009004010a0000000810408060000000810401120000000) (.node 9 (.leaf 0x49201100000000085202100000004040608010000004004608020000001040a08010000001004a0802000000010860804000000010460808000000) (.leaf 0x100520202000000100520088000000010920104000000010520108000000009120204000000005120108000000008920404000000008520408000000))))) (.node 15 (.node 12 (.node 11 (.leaf 0xa0a04040000000060604080000000060a0110000000006060210000000404120101000000400520102000000100920084000000104120201000000) (.leaf 0x4882005000000004086009000000040a0200440000004020600840000001020a00840000001060200480000000120a0104000000012060204000000)) (.node 13 (.leaf 0x500a01010000000500602010000000410a01020000000410602020000000490200480000000410600880000000408604020000000480a0401000000) (.node 14 (.leaf 0x8040604010000008004604020000008084200500000008004600900000004480200410000004400600810000001408200420000001400a0081000000) (.leaf 0x9204808000000005208808000000008a04810000000004a08810000000904020041000000900420042000000809020044000000801060084000000)))) (.node 18 (.node 16 (.leaf 0x408204801000000408202804000000404208801000000400608802000000100a04802000000104202808000000010a08804000000010608808000000) (.node 17 (.leaf 0x10a10104000000010610108000000009210204000000005210108000000008a10404000000008610408000000004a10110000000008610210000000) (.leaf 0xa204210000000006208210000000404210101000000400610102000000100a10084000000104210201000000100610202000000100610088000000))) (.node 19 (.leaf 0x40220808400000040220410200000010220420200000010220408800000001220820400000001220410800000000a204408000000006208408000000) (.node 20 (.leaf 0x50208201000000050202108000000041208202000000041208088000000040a08402000000048202408000000040a08090000000048202210000000) (.leaf 0x804208401000000800608402000000800608090000000804202110000000440208081000000440202102000000140202202000000140202088000000)))))) (.node 32 (.node 26 (.node 23 (.node 22 (.leaf 0x900204081000000900202084000000810204101000000810202104000000801208084000000801204102000000808204401000000808202404000000) (.leaf 0x120801804000000120084801000000120082804000000120401808000000021088804000000021044808000000020844810000000020488810000000)) (.node 24 (.leaf 0x21090104000000021050204000000020850404000000020450408000000020490110000000020450210000000420044801000000420042804000000) (.node 25 (.leaf 0x21108204000000021104108000000020908404000000020508408000000020904110000000020508210000000120810044000000120410048000000) (.leaf 0x22088404000000022044408000000022084110000000022044210000000420104101000000420102104000000120104201000000120102204000000)))) (.node 29 (.node 27 (.leaf 0x60808050000000060801110000000060082110000000060042210000000422008044000000422001104000000122001204000000122004048000000) (.node 28 (.leaf 0x460008041000000460001101000000160001201000000160002048000000061008048000000061001108000000060088401000000060042408000000) (.leaf 0x920004041000000920002044000000821008044000000821001104000000820044401000000820042404000000820408050000000820401110000000))) (.node 30 (.leaf 0x180801802000000180082802000000090088801000000090042808000000081088802000000089001808000000088801810000000088082810000000) (.node 31 (.leaf 0x89010048000000081050088000000080850402000000088090401000000088810050000000080850090000000488001801000000480042802000000) (.leaf 0x488010041000000480050081000000180810042000000180090081000000090090101000000090050201000000081090102000000081050202000000))))) (.node 37 (.node 34 (.node 33 (.leaf 0x90108201000000090102108000000081108202000000081108088000000080908402000000088102408000000080908090000000088102210000000) (.leaf 0x8208840200000008a00140800000008208809000000008a001210000000480108081000000480102102000000180102202000000180102088000000)) (.node 35 (.leaf 0x888002050000000880042090000000482008042000000482001102000000182001202000000182001088000000092008048000000092001108000000) (.node 36 (.leaf 0x980001081000000980002042000000890008041000000890001101000000881008042000000881001102000000888001401000000880042402000000) (.leaf 0x210801804000000210084801000000210082804000000210401808000000201084802000000205001808000000204801810000000204082810000000)))) (.node 40 (.node 38 (.leaf 0x201090084000000205010048000000204090401000000200490402000000204810050000000200490090000000604001801000000600401802000000) (.node 39 (.leaf 0x200904402000000204102408000000200904090000000204102210000000604010041000000600410042000000210810044000000210410048000000) (.leaf 0x202084090000000206001210000000600104081000000600102084000000210104201000000210102204000000201104202000000201104088000000))) (.node 41 (.leaf 0x240801090000000240082090000000602004042000000602001084000000212001204000000212004048000000202084402000000206001408000000) (.node 42 (.leaf 0x640001081000000640002042000000250001201000000250002048000000241001202000000241001088000000240801402000000240082402000000) (.leaf 0xa10004041000000a10002044000000a01004042000000a01001084000000a04001401000000a00401402000000a04002050000000a00401090000000)))))))
def rename : Lookup := (.node 258 (.node 129 (.node 64 (.node 32 (.node 16 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 0xf8783a1c0d86832180b8582a14098482210078381a0c058281208038180a04018080200) (.leaf 0x1f8f87a3c1d8e872381b8d86a34198c86230178b85a2c158a85228138984a24118884220)) (.node 3 (.leaf 0x2f978ba5c2d968b2582b958aa5429948a250279389a4c259289248239188a44219088240) (.leaf 0x3f9f8fa7c3d9e8f2783b9d8ea74399c8e270379b8da6c359a8d26833998ca6431988c260))) (.node 6 (.node 5 (.leaf 0x4fa793a9c4da6932984ba592a9449a49229047a391a8c45a29128843a190a8441a090280) (.leaf 0x5faf97abc5dae972b85bad96ab459ac962b057ab95aac55aa952a853a994aa451a8942a0)) (.node 7 (.leaf 0x6fb79badc6db69b2d86bb59aad469b49a2d067b399acc65b2992c863b198ac461b0982c0) (.leaf 0x7fbf9fafc7dbe9f2f87bbd9eaf479bc9e2f077bb9daec75ba9d2e873b99cae471b89c2e0)))) (.node 12 (.node 10 (.node 9 (.leaf 0x8fc7a3b1c8dc6a33188bc5a2b1489c4a231087c3a1b0c85c2a130883c1a0b0481c0a0300) (.leaf 0x9fcfa7b3c9dcea73389bcda6b3499cca633097cba5b2c95caa532893c9a4b2491c8a4320)) (.node 11 (.leaf 0x2a90e40049682c3800abd5aab54a9d4aa350a7d3a9b4ca5d2a9348a3d1a8b44a1d0a8340) (.leaf 0x9f884ae601f8f04ce8043d03a013290a90ee963e61eeba0c8cb267928ac1afb013b64c1f))) (.node 14 (.node 13 (.leaf 0x944508a530306a668d119f652225ab557ebb67b6566b066ad8b668a30ba5f2a073f0530d) (.leaf 0x83f8370b4ba8e7a24a253cba6b189f822ff129fc0ef12214a9cf08528a648c8a9f28a96)) (.node 15 (.leaf 0x9821a2278a124a49102b1687c4a9b1ea5c84481da81225c329a6df5cb2da4de2e1aa7830) (.leaf 0x59319b4b43113a10a07b222089c9c252951231922049a7ba092277873a8804ca63b20c9e))))) (.node 24 (.node 20 (.node 18 (.node 17 (.leaf 0x8da9aaaaaa946aacac1cc76aead1c470de73a88c876a41aa9ea6346c37178c06db119cd0) (.leaf 0x71399cae171b9dc8e0381b22cae55a946cafaa540751f389b62ea81baa46719371ca311e)) (.node 19 (.leaf 0x7c2260a9d9ca5697132c19a742a063e82d0749a7e761ea1d34a8509a060148a0a23a7c20) (.leaf 0x958241e81091d242056a3217cba63b0998c968b749646802610a800aa3c510c3213e12a1))) (.node 22 (.node 21 (.leaf 0xa38bc925f79a0c267513ba4c2697abf6069b9b9ee92ef209366287169e40617938b07a47) (.leaf 0x4fa790c873c1e52692552ad3a9c42a10ee765eb058ad758b0d6ed62f145e48b80a666a19)) (.node 23 (.leaf 0x50a8114894422cf47b4aa5152a853a99349b4120d229052295309940204ea7447a395aac) (.leaf 0x6b35574bb58ac198cd6130dcae46db697cbf592cd8ec651a891a8c3f9f8fa7c4b25d5eae)))) (.node 28 (.node 26 (.node 25 (.leaf 0x69b4996ca73b99badc6030568b75b2d5a2d064b21c6e26c36578bd6733d88c570b81a8d7) (.leaf 0x98487238150b4582b0603406020f07c2c171b8d86a34140a4140b008002a146fb7972b8)) (.node 27 (.leaf 0x188c022100301c4a2411888341b1d8e85e2e078380a04100843019190cc4e26048203a1c) (.leaf 0x2b15c9049369b0be5e1e8f0a8552311ccc6720104b05926134e2703218cc4651f0fc964a))) (.node 30 (.node 29 (.leaf 0xa5d2a5d2f9148e7338359a88a442e970a652399c8d26821908b45b2813c9c51379b8c260) (.leaf 0xa05066d37a8d428f4695caa43209f4fe6935abd5a9b4c984c649279349687429dceaab54)) (.node 31 (.leaf 0x763b6231083c1a371a7c3ddecf9753ae0b04a753e673294ca28b449ecf2a752a4d225b2c) (.leaf 0x8f47dfafc77bba271284c2233187abd21d0f8140e2f1679bc9d2e88643601018ec71f4fb)))))) (.node 48 (.node 40 (.node 36 (.node 34 (.node 33 (.leaf 0x78bc1deee74ba082401f8f88a4421908783d018080200038180a047fbf9e2f08ac52170a) (.leaf 0x5bad16ab658ac0f2783b9d8fc7f3e9f0f47b3a9d24f2492c9a452394ca24320763b5d4eb)) (.node 35 (.leaf 0x95caa5b2c7dbe9eef97c3d9fefe7ebf1e6f27a3d41a0c05828221007838100959ac970b9) (.leaf 0x178b84e265faf982c05dae97abc43a190a8446a31148945a21008141a0a6330974be6732))) (.node 38 (.node 37 (.leaf 0xa6536974aa753e8f46a4d20ce6631994c862359a8d2682f978c061160b4562a140a46230) (.leaf 0x1b8d06a361d8e866326d36dbcdf6e375acd76ab51b0d94f27d3a9c5128d42a04c265349b)) (.node 39 (.leaf 0x542a54ea6ab55eab54a8d42a7528e476351b8f47e2f168cc60e270399c8da6c379b87039) (.leaf 0x289388c47249202e160a850341b0c064261272395cce770385c4e3562b554ab572bd48a5)))) (.node 44 (.node 42 (.node 41 (.leaf 0x62b12753b9cce2793d9a4d66d378341e0b048542e130880406050326930964a29948a04f) (.leaf 0x864361d0f2c960ba5c2d16caa542b9583e1e128884624100843a1c6331d94cb6432586c2)) (.node 43 (.leaf 0x6934da2d066b319ece4924d2c974aa511e8e48a428742a2d127d3fa050621118a4562712) (.leaf 0x411212277763d9b0625e100ac3e672ca21066d2790c4c421298c9288c11b69c621e12076))) (.node 46 (.node 45 (.leaf 0x470518e93a55324930a04da452ea14e225086e28168c044138f45a682521d02753dd3463) (.leaf 0x68b2219004c0a10046478550a4b7c3e9a864330a9740c2a029981e5f1620b074ea7d8416)) (.node 47 (.leaf 0x87c35d6ed6c8a560020e0019eb3a5d367d349ccee873a89c25baa14493d1450100619295) (.leaf 0x2103886045b0856a5b743d0c0261e0203a012b8fdf2fb6a994ce2b5d834aa0b6687d7e59))))) (.node 56 (.node 52 (.node 50 (.node 49 (.leaf 0x4091d86174393607016ba6d322d3a0498a79a451a592a904b6833f91c9a4b2f773f0d02e) (.leaf 0x77bf4d22f0283cf6195bb05165174bccbe273a84d06497abc8c25e1e82562035e905ac2c)) (.node 51 (.leaf 0x8a429bca2461491a531106996966932a2b0b6fa8cf81b3e88da697a4d1e432b9bcd64f31) (.leaf 0xa753e513294cce8b3da24f1e2ff358c40e113f894fc5d783f8d430220408a065c891705c))) (.node 54 (.node 53 (.leaf 0x541c63116371b0de32718d9c4708d471c038520d154ad722b2371d70a994a39538d5caab) (.leaf 0x6236e089c889e12076a9542a751aad5ea9568f47ce43a398edceaf732ba3317368cd5237)) (.node 55 (.leaf 0x812699cd05931929384950922775a36a254a884928122873a978c07b2210d30424b9ee82) (.leaf 0x8d549cae155a963a39538d636a631138804c2b1687c4a2418db0dc84281d9064f530f536)))) (.node 60 (.node 58 (.node 57 (.leaf 0x565594951190ee2ea88c479c6e7578d95b57548dd5555723823f54a80ea3838a98d23233) (.leaf 0x7d8365a0b7a021f32c67b6566b0868a5da020e0021eeb381b0de73389b4dc727139a2cae)) (.node 59 (.leaf 0x1f8f084655ab568c2e928ae400474099dd485b3367e219307c3a01a0c8d7ebb7e4be540e) (.leaf 0x94889e2078a4a1fc1046ccdfe11464c9a6df85a5d461b3e88e2a7c2d9a0b26721954ae60))) (.node 62 (.node 61 (.leaf 0x2e1a88a532e9ac88525c32a783003068fc3178429454e5cb2e7a243f8952d456937a894f) (.leaf 0x938b242057489ddf495eb05e48b43cc5032b0483de6837abf58ad780a64f22d3a04a069b)) (.node 63 (.leaf 0x83a4d3e16470520a9d28978824d1e91c925f309a562c39a86406173a84cf7375bb5a8e2f) (.leaf 0x84a8598c99d8791e154ace5a2dda1d367c20860a2274b5f2e9f40c450290a807c2258ec2))))))) (.node 96 (.node 80 (.node 72 (.node 68 (.node 66 (.node 65 (.leaf 0x119f48a530306845299682c38002a90e40042c198a85025918c84f64352742a9a0620098) (.leaf 0x481d8b4561f128f536a048a568107824e8121e91e4205450291c142a14268189f082668d)) (.node 67 (.leaf 0x83a7cb0669d0aa874d0f4ec1afb013b4b267928ac3f261aa9ce66fa8a907632a98d25c84) (.leaf 0x1c472aead9821a227820131d906a627a2124a124a62873c8b4824d938b00617063e92616))) (.node 70 (.node 69 (.leaf 0x9a86420fe4b86e16a32e1aa7830a253c493d954bc1cfc868a4b668a30ba7e211cc76acac) (.leaf 0x52aacd8705745aa1541d47d5e36443da089c2718a10a089529293845bca02992897a8e2f)) (.node 71 (.leaf 0x5bb5962c35d2f984c764351a2dd66325a6df5c329a4de5cb2d76bf67ac166d95ab559ab6) (.leaf 0x87bac846577522832370b95cce270391cee3602f188db6e36168da6833964c660af58ad7)))) (.node 76 (.node 74 (.node 73 (.leaf 0x77d24f73744be20a9d2799212a189d2d2b39992322a7c22149e10aa728a2928a2a5a58f9) (.leaf 0x3f0c40ef1129fc10f42b8f07e60740983a015346ce46e8f462a51aaaaa9faf581a6cd261)) (.node 75 (.leaf 0x413dc90638126a1cea489dde6832497dd2273a84d00852312e0098860a11e1508bfcba6b) (.leaf 0x56a34fe7d54a9d008952a210c8c3c1f14c8242a75569c55210ee76369c62ea819c646ea9))) (.node 78 (.node 77 (.leaf 0x3a9ece87941a6d30a15728148ac4f288f47e542691e954724d28974925922904527d5ea3) (.leaf 0x8743e231583bea3f0b7f3f238fb78bb632f48ebfe0af8823da34f9753ae36f74ca2d0287)) (.node 79 (.leaf 0x8006e3580bc9d2ef81bd5e6fd804262d0883429d8f0743ba31028bc7a1913894362114) (.leaf 0x1007848211107c3a1c1288c2c0c1d06c200e1c0340e021982072110a8a0280a1b0a4680b))))) (.node 88 (.node 84 (.node 82 (.node 81 (.leaf 0xaa4e2952f9148eab2e0c8bc2e2c0280c2627090241e2d0c0a8602e0d0ac0c04190987631) (.leaf 0xa8d5a994e9f50e893fa050685459dd367b4f94c9aa72dabccea12a924a2a52c984ca734b)) (.node 83 (.leaf 0x1e108dc48369c896643818894651f0fce2639ad1e43279bd2657319a4ea7946904966d48) (.leaf 0x2f9a4a8582e16caa592b15cb45d28198d4682999c8a4337980e66b2313cd84e261488044))) (.node 86 (.node 85 (.leaf 0x71b65cedf612e9c0bb5a2c188bc70b018ebe72319b4bf592cdcadb289788e4d1e9049261) (.leaf 0x61b5962b762af5aec16435194d55c2d5c4d87337198d1693359ccf6834d92dd65b7972b6)) (.node 87 (.leaf 0x2f17e8f466cb61369a309804e26a4d21bcdf5128cd46b180c69d4f6eb7142a0349a05e2e) (.leaf 0x1d0ee3d1f4f27cce66160b4562aa6d31b4db4ea70ca643118c5228a5d29acd76ab513298)))) (.node 92 (.node 90 (.node 89 (.leaf 0x8d46dc0e152a90d86da85462d177138d4ca854a9cdc6f198caa5538c465cce7572bce473) (.leaf 0x5bad16ab63d9e8844302811deee562b47039ab55e391d7239554ab381c46c371a0d6ab54)) (.node 91 (.leaf 0x1f8f8020091c89d6ea582c4ea741e0f6432074ba170b93e1f8fe7d221140e06944a5e0f1) (.leaf 0x804665337f3fd82c044a2d108a0703dfafc3c9e082400100e4f2492c99daec59ac8ee76))) (.node 94 (.node 93 (.leaf 0x5faf90a840582a5f2e7cbe1ecf75dae90081954ade4f35eaf1068204026592d7abd1188d) (.leaf 0x6934d2c972e17448251108e8b448a455a2d04aa50b65a10882271243a181a0c98cc1f6fa)) (.node 95 (.leaf 0x49a48b2580f87a8742884459acc47a38aa549fcfa1b0c67b3922902b9583a1ca0d021f0e) (.leaf 0x80c018ac42492026129bcda07026532ca4530d86a793d8542d90c9279449c500c8621308)))))) (.node 112 (.node 104 (.node 100 (.node 98 (.node 97 (.leaf 0x96c8086042a82c3800269302e169d4ee0d0763b18964a0a852733882c1186c22311e6b34) (.leaf 0x3009a833f91c9842b60fb343a0197c94b6b52cafd9eb32b8fe592a210381abb012c07808)) (.node 99 (.leaf 0x20af6432b0283c8e81091d07a09773f1f2fb87c35d6ed7a3a29146340b8ca6715b5452d9) (.leaf 0x163585ad74da64be273097a6f350c9ec2ec3099d406b193cc4a2b760a2c9a87629e49283))) (.node 102 (.node 101 (.leaf 0x2621988782420880bca04da452e2d1e89484481d8ac3e77bf6070174bcdeaf2a4d1cd22f) (.leaf 0x753ddececa5531b8a06d279b69c31a68c4d89c509a094632492277672ca4930272d18088)) (.node 103 (.leaf 0x63a4c96852c2f89e890b3088c80062ea7d3428080308a0a238a80a894222106824461d02) (.leaf 0x89c260b0786401f0faa5d35baa14ea7c50983219854d49cced92950aa3c3ccca1ce9a2c8)))) (.node 108 (.node 106 (.node 105 (.leaf 0x722b1caab38aa0e0e2a9540e43a1c38072e153294da33371b2a751398ec68a41aa9cde32) (.leaf 0x29888348d119f48a068fc7a351c8dc7633178c45aab5773abd54ad1baa46ce3aa559ccae)) (.node 107 (.leaf 0x350c28b3d65a584a7f122e6893c69329a6972e9f8b8b8944c8a48c0d9f00e11220425333) (.leaf 0x592cdcae46db698cc742a10ee76552ad3a9c8a42a2b0b78bfde0fea7d39bca26fa8cd631))) (.node 110 (.node 109 (.leaf 0x8006c371a8d052280a851f0f97b3ddd6ea8dc6a0b0497cba4722aad52974a9cce17cbf) (.leaf 0x93c96af56a6d32773aa150d0c873c1e55aac4fa7924931f0fce07132194c46325928140b)) (.node 111 (.leaf 0x26134b0590603406021c8e05a2c150ac2e160f07df4fb76bb23b1c83c1a2310984c64d24) (.leaf 0x89c4980c15b2d16eb573b99badc64b21a0d144a29108b3d9e95eae50a812a9420104cc67))))) (.node 120 (.node 116 (.node 114 (.node 113 (.leaf 0x2110ce473341a49e5027144b65a0703c0a041d0ec5e2e0c86042207e3f5deee8fc7a1308) (.leaf 0x85c2a2b14994ce5129a7d3a7b3ca2d1172b86fb7996ca69b49188d3f9f0fa7e51a892c97)) (.node 115 (.leaf 0x3a9d14aa44ca611e8e22114d46b2914cb85d080440e06180c4361a1209446227f3fde2f0) (.leaf 0x80c021b0c954ae4320a85468f469acd27f3e5d2ed62b070b81aed66a35586c2663350081))) (.node 118 (.node 117 (.leaf 0x6cb6188c56733d048354a994ea84da6922901e0f4d86d2f17c8c472a155e4f374ba22d17) (.leaf 0x402466321389826120e871eaf48cc62070287c3a592da954e93489bcda83405e2f5c6e2)) (.node 119 (.leaf 0x8ac2dbea369a5d8416470520b074ea7d26c7621e1207688c11b69c371bcc26024124ac57) (.leaf 0x6b8b5329b629e560020e0021b0f75bb452d967acdc23952a986aa78dc75caab0d9f0467d)))) (.node 124 (.node 122 (.node 121 (.leaf 0x722b154ad46148448d2986a290a6f289a4ca4b32d0c4c4212a21066d27924c63a04a0303) (.leaf 0x6e281a0944091dac2c4393586175d834aa0b7cbecca676a8acb2bf6687dc0381a292351c)) (.node 123 (.leaf 0x1d1c8e63b8fc79ccae73abd124f10228a01889c25baa168b212ac9602d1104e2d1ea2508) (.leaf 0xa04ba4536a5532853807815faef179a582b745944327b0710886047e3b8d02e2dad442b6))) (.node 126 (.node 125 (.leaf 0x9fd064726a854aa751aa55aab57994a26729a7d3a893ca2cf67d34a5d36873a9ccee6124) (.leaf 0x6a0a8b0be6607978402b0f9ecec313619cb295c868f4998c9e6b37954b25b20a35225f25)) (.node 127 (.leaf 0x5880cd86e378ca2d18383886ce3081108a067f3c0d4302e2e048b95d030a80a7c3e8c866) (.node 128 (.leaf 0x2e9f84a7f4011a1900142610a4b478550448873ddd50231a692277048f5e4f52f1857a41) (.leaf 0x79ba4be2741924ea13040f1e8e830098ae3f0e804da338cc5ce2a81baa422077fbc4d631))))))))) (.node 193 (.node 161 (.node 145 (.node 137 (.node 133 (.node 131 (.node 130 (.leaf 0x2f3ca8e2f0d9394a8836042540ea80ea7b0b57a8cd4fe343f23f4f9e4215ca08b0c28c2e) (.leaf 0xa43ba3d4e4a25c485c9fc34425ba244a710455a706c70313d8532faa52a6b010c945328b)) (.node 132 (.leaf 0xaac6e6f034d9ecc2f5a4bbcd2fd279494c89461f0dc449610aa528394ca130a50a8a30f0) (.leaf 0x9a4d8301a521e8640690012a23b4aa5a830f89c528b159cc15549d323e0caf991bae354b))) (.node 135 (.node 134 (.leaf 0x50f816001a4886b2e0911d0274048f642059583ca05353a291a7d379165a43a9ca4e733) (.leaf 0x303d232f135bfe010254261347e133a22e3147240a8560e1567d4010088465a0a1290876)) (.node 136 (.leaf 0xa92d0a77008fc50ea1b9c4c6f709925067513ba4bef3231210082040f0660736845527f) (.leaf 0x9dc1d5a9f333e8cefb933b6394dabc7675065627854ec15c96ad4c47a443a57864384a5d)))) (.node 141 (.node 139 (.node 138 (.leaf 0x49a483c580f9668710a14442e4d439e406411649c5b310b1310c78061001a021c4907330) (.leaf 0x6bb0584c45d2f176b0702d1c2c064b2dc6b96cad9bade73b7d90ca71351b0b86aad5ccdc)) (.node 140 (.leaf 0x8b2ba10a09e0c28c2e663399acf68b49a0d363b197cb25facdc8da72b6d86c55eac5acb7) (.leaf 0x80a66a1541d47e9512a7d128e2f1b2be70949e8927e219a864d87027188d45c3416ca25e))) (.node 143 (.node 142 (.leaf 0x64b31cce26e36194b86aad590d4443d820fe954bc1cfc7922d4aab82270370b51a5c530d) (.leaf 0x6fb4db2cf582cd8ad76131dc0e46d2d1bcd26b2ddbad173b8d8cd0672c996b966ad986b1)) (.node 144 (.leaf 0x29914aa43238f4a054a8a9076329b1e83406900126818602f176bf60af574be70b9588db) (.leaf 0x7824148a1aa9d2076119f43800091d0288e1a54e8122114a642059f080e66f25168ac3e))))) (.node 153 (.node 149 (.node 147 (.node 146 (.leaf 0xfc982e039d8789840339649a4133162acac835313cec15c96742a97212668d05cb65681) (.leaf 0x982181afb98a1c18fa1cc762278013b45a790b41d3e931c47221241649e9b43abab68492)) (.node 148 (.leaf 0x129fc3a01099d42a8f369c4906335974c0571e0fc925f2312e2ea881268627e133a20098) (.leaf 0x8553944f0a43ba12a17ba0822ff043d1e683402146719873a80ef113ba4510c1baa52277))) (.node 151 (.node 150 (.leaf 0x82a76a51a8a4a292efa5c4eaaaaa2a5a83239b9ee7295391b8a44432908d261279923d18) (.leaf 0xd0ac1a38058d0441f018140c040380802009923258f97ebd512f88da9a2a7c87bae069b)) (.node 152 (.leaf 0x180b83610070e85236120842627090244c32040cc3a1c1683c623b088e46e351288c2e2c) (.leaf 0xab5326530aacba8b4299d5e432790496512491c8a53260c0a82c0c0a8a0280a0f080322f)))) (.node 157 (.node 155 (.node 154 (.leaf 0x9f50e774d9ad1e7946955425f549c52a893f9ed3e6f49a44da5952a0d025b5395cc69d51) (.leaf 0x54a9d028751291589e4621954844b2491aad3a9ece8793f1e8f8783b9d8fe7d9a4ea734b)) (.node 156 (.leaf 0x4c28500894ea151e954724d3e8a4ca2d5ca052a21569c4ba5146af4da0d509a532092290) (.leaf 0x87c39e91979bf62f1e8dbde2b117fc7615067cc6a29107dc71d2ef783a1dcec75ba9e2ed))) (.node 159 (.node 158 (.leaf 0x5c2d560b459ac972b6804260af88644e0efa80bca2d08823da1b1285bf9f91f81bd63102) (.leaf 0x67b39b2e36bb05ccdc70b01cadb69b41bee761b5994d55db817ee463369a4cd65b7962b7)) (.node 160 (.leaf 0x32928aa592999c7a41220f084401f8f88a436a32184ba63af998d164b758abd7136188bc) (.leaf 0x2f144d84e38188b85b351a0926137120ae56301bcbe69369c8e2632e968d67323934a44c)))))) (.node 177 (.node 169 (.node 165 (.node 163 (.node 162 (.leaf 0x62b5e029981a6e3a39538d5cae155a954d1b889e120766236e089c2313c96642a160a066) (.leaf 0x8586d46978a9f1da020e001b2cf59ac0530d87bae0e164fa4c288e63b0a0a9d169e42474)) (.node 164 (.leaf 0x7c2250a8043cc412819583d7ac17922deafd41bcd0d30424b978c07b22104f73e88dbed3) (.leaf 0x84282049a46ccdfc10464c9fe117d8365a0b5faee5f2a7e03a58f97a021f40c052297cba))) (.node 167 (.node 166 (.leaf 0x154ea68186a32212a180261595619292a23b7139a2cae8c4795117833b13d4c9b1e9b0dc) (.leaf 0x2b1287c5a3113890630d01994b8184f214f051538627e15c9640046aad68c2ea43b84ce8)) (.node 168 (.leaf 0x3015c7e3c33160a8503213c9646269048e3d2f144c2692497cde73381b0dc72389b49840) (.leaf 0x8f8eaa51a8c8ce2124a0489b4b4a544a1cea29914d45c29110d65d33964aa433416cca42)))) (.node 173 (.node 171 (.node 170 (.leaf 0x7881e9b439f081bad1a5c4c510c1649e42056b2de8e2fa4bbc4ee98e0e2a63472382a950) (.leaf 0x9b9ec267556d5dc6e71b2bd5555548dd25426731964d09c2512277114a5bcd2a7d122928)) (.node 172 (.leaf 0x65ae67a244b514fe250fc999ab69f88683230e806761e6632672950aa3c2e0361ac66a19) (.leaf 0x63af9cadb329287e3e25990e0623898e34f9753ae0af8823d9ef1b55210ee7642a75569c))) (.node 175 (.node 174 (.leaf 0x52a2104a69148e9739aa4be9538aacb8680b0080050150a02852361b8d5c8bf6d31966b2) (.leaf 0x19821c0bb582d184ba70b0188bc261487840221088c4f36138da72241b90c8c3c1f10089)) (.node 176 (.leaf 0x562913ca23f1e930a157281509a924a2a12a984caa52c1c0340e020b03036101d0382239) (.leaf 0x15060602e188ec4c326ab2970b56a321ccdc713620d0a743b1e0ee804262d088bc7a0518))))) (.node 185 (.node 181 (.node 179 (.node 178 (.leaf 0x80bc9e6fd81bd50e813a9e4e87b4ca2d069b92c827534a34f2ad51a653a9136158680c04) (.leaf 0x1605c0605178645a0f1384c24096b30d62b76bb058abd2691c823d2f144be6924985d2ef)) (.node 180 (.leaf 0x8e3ede2ed83bea16fe8fbf1ff1d8cbd15a8d3f9f53e8a51abd52a793c868f3598cae9337) (.leaf 0x934a69b3ba7cf6af33a9cb5bccb5cad9bac96fb9db2e33394c8a4333140d468359ccc06f))) (.node 183 (.node 182 (.leaf 0x67b38b2552c150b85b2e968ae5688452191386c4a23158743d249647a4d1c954ba512290) (.leaf 0x34a85b8a06e9a05e2ea1cfa893fa151681410f8883c20120844a230e871a4cd66345a6d0)) (.node 184 (.leaf 0x6ba66934ba453a954ca7d368f4632a89b49e6f19c582b6b354c2646c188d466180a9a85e) (.leaf 0x65136124f8413992500c86190514d18cc06b138a04c312fa61369d6da71b2df51a7c522d)))) (.node 189 (.node 187 (.node 186 (.leaf 0x85c1c361609051850162b1e6f399c4da7b3b9acd2793a851498d062612996530b8698647) (.leaf 0x5c9140606588f57041779eddc425a1e96c43028116eb581120261580118924b81c158904)) (.node 188 (.leaf 0x740f07e7e759f0f076769f40400581d1667991ca24922934a6432093c95e044593b0803e) (.leaf 0xf8899a55691659c561207998542e162269568449285a10881a25b751dde27f0081dd275))) (.node 191 (.node 190 (.leaf 0x872443a258623cae5d87c5622900e08e1a8e67b4d2e93a0d1685409fcfa89438a25a2092) (.leaf 0x7da341a0b5da057e877abe178f67f3e8200c0482974f25eaf9fa8960221f88a0703d828b)) (.node 192 (.leaf 0x73c7d5e731d0edccae7ba09e8ff04045e68041a165932984ba5b33954ae5f317ca310c84) (.leaf 0x72aaea555abd4ea151aa55a34aa8e2b4703470291c8ac8c1b9c66f1b0ca2c6c711c23c72))))))) (.node 225 (.node 209 (.node 201 (.node 197 (.node 195 (.node 194 (.leaf 0x1d0edcce7572be3f1e349a05e2e6eb7142a08caa466378b9b550718da9a3aa71c8d5c2a5) (.leaf 0x281168b75aad8f47b77bb89e502714430196432613082d16c402168b412a9489c48e473)) (.node 196 (.leaf 0x1288da4d34b25e2915a2514d46b180c5bcdf5128e9f4e0703d80c144a29108b7ebf08443) (.leaf 0x7f3fe6533221140e065c2e4fc7f3e1f5e2f0944a4a4530d06d94cb8542e793d2e1744424))) (.node 199 (.node 198 (.leaf 0x9cce0e0711a0d86e357239554ab8d46ea95532194c463140a5b4db4ea72974a08045188d) (.leaf 0x502d7cbf42215f0f97b3de5d2f1f0fc0200592ccee76753ae45232512c2a146331e0b04)) (.node 200 (.leaf 0x8341e753b2c1643c1f4924e2111a1d087039562b6391dab55ccc67160a8562d4f27e9b4c) (.leaf 0x13899b0d94d26e9348060350c877d3ee61312010406023c1e5d8ed9249e4b26261342e16)))) (.node 205 (.node 203 (.node 202 (.leaf 0x8140e6d372b15c3a1c6733d22908743e8141371bc66327138d50a95329e3318a954cc260) (.leaf 0x522962d17a8544bc5f6b351aad74c2668f460482178bd4120deaf4964b490490984988c5)) (.node 204 (.leaf 0x1e8f162b03a9d1d2e890c808c4761b0a01019a4d4a855663351e8e864367d3f361b5c0e1) (.leaf 0x64a55a09473abdfaef7e3ba13138444a3f1e348bcd02e6ea85b8a05d2ed0081793ce552b))) (.node 207 (.node 206 (.leaf 0x602d1104e390e81e052181114500c080f45a398ed82b7459456a5b64345ccae3d8656c21) (.leaf 0xab55279449acde4d3fa0c8e7739a14e2af559ed168f49a35229b4ba652a9f4e07109124f)) (.node 208 (.leaf 0x6da71bea3954b26124a854a652895c865b209a4fa6d409748aa75199ca6632792cbe7543) (.leaf 0x3cb159eb349b1dcaab69a5e030376c361eeb83c1623048ec6e17156b8b5329b6c8a53e9d))))) (.node 217 (.node 213 (.node 211 (.node 210 (.leaf 0x33b5456654f369bca25800984163c311c23952a98f81b3a0483800470512076538d4fa23) (.leaf 0x4694c342243934b2bf5639194d26185d9a1f493195aaa65a59f6f983442391a85451ac2c)) (.node 212 (.leaf 0x7bbaa33177fbc4be273009930284d18cd6315d8350c4c700e118524091caa0b421294834) (.leaf 0x881d06492b8fd0a4b541c4fc5d3a84c3a01478552277548dcfe2579ba5e8e880432050e))) (.node 215 (.node 214 (.leaf 0x718d97224793d5f4f8763da2d187f3c0bc613335054646c188d4301e021004641120da33) (.leaf 0x5d0317840361b820441e824a80a2b0f8de32228197a412c2f9c4705c1716203660799cb2)) (.node 216 (.leaf 0x94d4e42052d08e5c35999cea23b9583ca856050f88a6f030c8123d2a87016009690e4004) (.leaf 0x74098103c0a128a0539a4d8301a238491c90421d9148d3ea9cf4a4409d27d401008a4434)))) (.node 221 (.node 219 (.node 218 (.leaf 0x4020a190e750a1e3197489c0e3312975ee373898dfe6b8b8c5e65f089b43a57008fde860) (.leaf 0x9fc34425b978a5f868a30ba540e0a92e0102099248c4847a450a773faa4fca84c2690675)) (.node 220 (.leaf 0x57a8d5ca045a6510a589512a94a8fd3e8e2fa80e8485c7b0d8e0627f1aa2c3079178206c) (.leaf 0x78461ea61221ba830f7cc8dd6657752258429c4127b0b844f26b010c9449c1b4a25d569c))) (.node 223 (.node 222 (.leaf 0x4aa59549d50a88f69b44a30f8a689c52354b77d265152a2c56ab1b8f539fa69991c9f064) (.leaf 0x663397cb25cb8d70e26a3617ab15d2f19acf5facd6cd95ab5576b09cc16130a9bc0c9e52)) (.node 224 (.leaf 0x6331d92cb6432986c561311a2d272369bade5bb5968e06834dcadb73b7dccdc60b5d80e1) (.leaf 0x920e28511abc76ad4c988b660390f161f466760a80641061003e597dc99da67928ac1a02)))))) (.node 241 (.node 233 (.node 229 (.node 227 (.node 226 (.leaf 0x2a82c380096c8086049dc1e75060b9342c4c4924d5a9f562790e79431e287108e5364e2c) (.leaf 0x2b0f8a68d0d088fa2394ccc8a06520d14e35a9d44e63b378c88e81091d2432b0283c123d)) (.node 228 (.leaf 0x199b41abb012c2592a21038103c0a23a693e2822830202a0289484481da6d40914b8f45a) (.leaf 0x924c168c027221784024208a48c3e06e5132220400e111c3814c3970a96a550390e8dc6c))) (.node 231 (.node 230 (.leaf 0xa4d1cd22f309784e5f3399456d56c8a69146340b8c0260b3089e89062e88c80262198878) (.leaf 0x1535130284f369b69ca6529b8a06c189346351379bea3a753cd430358c458d64d8b5ae99)) (.node 232 (.leaf 0x8f47e31168cc5e070177bf5eaf274bcdf6f987bb5d70d773f1e8e84fa769b4b50b74cc64) (.leaf 0x83c1613137d3e2010c83442230484449d8f681439d4f7854522b0b783f9e2ff8e46a3b1b)))) (.node 237 (.node 235 (.node 234 (.leaf 0xab551ccae711c1507126a1d8a7993cc56ec128a2d7a4124a0cb2bf67ace4b2f5a96cae3f) (.leaf 0xa0c9a473f5b0843a0149b1e754364344b0be25a1594d269a5e79445c170fc5d56391caab)) (.node 236 (.leaf 0x489dd9696a2cf572243f8955aaaabd55ceaf718d952370bb0e6f353d86406b1099d43ecd) (.leaf 0xa43ba130a50a8a9d1e8b0c28c2e9e4215ca09dce592950f3302a8f4931a8538682519cb2))) (.node 239 (.node 238 (.leaf 0x900126d340c068f4a4a88edc4b86c3516ad564329ccdc760aa4a2b9d419589eab53230f0) (.leaf 0x7dbb6770756a7eaf1da6c70d4fe343f27b0b57a8e9f1f133a20500541f934988b8c46406)) (.node 240 (.leaf 0x35bfe32f1379165a432814d148d539f66673a9ca5c6b95b36592cb73b7dbade333ea4c67) (.leaf 0x72368c8f891995f2eb9cc15549daac6e971a380d8c4f6978a6710455a72a94a303d1527f))))) (.node 249 (.node 245 (.node 243 (.node 242 (.leaf 0x1f80496153ba14e23731bddd4281f0281600250510876970d64434592f97eb36331dcadb) (.leaf 0x6834da2d22c078b21f4924e8511a1c42830f4aa5a8b1589c50b8249f96c430d4a25e8912)) (.node 244 (.leaf 0x950389c1b44296a03a2b875228f2e8961d0c2b150aa1c48238b423a04f84022673319acf) (.leaf 0x6038568e0200301a02260590c78980e6483837112584227949128c531f26472a94a0d810))) (.node 247 (.node 246 (.leaf 0x3da6cd2fda4bbcbcf29a944330145a668e2f1e020904641200da111981d78ba5dac188c2) (.leaf 0x1e8248e12409d2560f908157ab161b1582d75bb5882032685d0e79988b64e2c30bd66f03)) (.node 248 (.leaf 0x652b20c9e8528a2f51188edcd566e5329d1e8b518602e9e2ba10a02484d06752fbcc4ee9) (.leaf 0x814d934d88c521d12003010fcb85ac94f4ec783ba01344c350302a644ea12a152354342b)))) (.node 253 (.node 251 (.node 250 (.leaf 0x89d2dbb4d6b380442c1c0d1a4e48836a291a6f4728f50178ea89548952a9f1f130c950e2) (.leaf 0x8227216a3138ce1d40a4d4a335374c840e055bc9d69247548a50ef78ca6193e100a1a343)) (.node 252 (.leaf 0x473082c1449b1e0a9d83a7daee1118b4723569b9622db8ac6dbf1d80c3532a50d8a52eab) (.leaf 0x1206442364a4e27aaf090718acf48312070f4da994ed93a2c004003caccf0763e3acfaed))) (.node 255 (.node 254 (.leaf 0x3fae56d2647b303c154ace5933b61b342e1f493192caa65ab44a376850a8b5573d5e6b3f) (.leaf 0x7bcba64fd7fccde52a08039172f443d9fcfc0987522ce9bd0552e33aac406013bac8f723)) (.node 256 (.leaf 0x7a4b500ba060290abe44be114fa40aec1a0b43afd0c84463e51afb79cac220f60cc58130) (.node 257 (.leaf 0x29194a6672f9b4ba712d18cd272359ccbc6c2e144b67027188d4680482106bd412f1eb2c) (.leaf 0x2495c9056309b8c06f1e8f0823f200f888422290c8c542c12c9e64281988e5526964984a)))))))))) (.node 387 (.node 322 (.node 290 (.node 274 (.node 266 (.node 262 (.node 260 (.node 259 (.leaf 0x8f46212a13f0c5d0268baa2049a8026194b86aad5cce26e361a8c89e0c28c2e8b2ba10a0) (.leaf 0x27188bc5115c955956833b13d4c9d0a834069001149511d8c8f5369a06214f051539dd48)) (.node 261 (.leaf 0x238f4a44421194e46e27990d2613597478602b8fcda712418c8c4b2f924d45c3416cd870) (.leaf 0x8586d4697868a54aab822720299339649840331609a4129914aa43399bcb456250f8a850))) (.node 264 (.node 263 (.leaf 0x538d5207647050e8123e4561eeb5346e0a9d81a6dbed3583659eb370b9588db6131daec5) (.leaf 0x602f174be60af5fc10953f01d2f443d9e48b7680a3a393c4460e164fa4cf22d3e88c3800)) (.node 265 (.leaf 0x46cce5a0b424b9140a40cac1e09464ca58f944be1faf57f845e808413dd008579a0d76bf) (.leaf 0x65ae59ab673b8da0ce632c998c961ac67a249f8855e364a4e26a197d8350d307d0310f31)))) (.node 270 (.node 268 (.node 267 (.leaf 0x9307d5b574950a761e0b80d2d45a0c8d55554ace4f7373f8943a01548dd227747854ea13) (.leaf 0x77d25e2078c8ce1cea860a1d2276f349c0e45a369bad16b2de9f44a847c75548952a8e2f)) (.node 269 (.leaf 0x9e518602e8b4215ca08e0e22124a6d0c59279488aa634a048a7c20908162928a946a274b) (.leaf 0x5c2d6ad51a653876318f45dccdc9b52064268c409509a71362753415062130050a61a8c8))) (.node 272 (.node 271 (.leaf 0x309268f3517865e50145a64bc511586a0d0a562913ca2653564b2003011d8f0773a0f47e) (.leaf 0x77ba4f6753c9d162b7208f6632b078b5faf360b5cd25fa4cdc122709849eb0341a6d7ac5)) (.node 273 (.leaf 0x7c4150a9d5f31cc84baa4be95381b0a5ed0455a70e0621605d0e816b30c9a4793c840605) (.leaf 0x6d31894659148c0200753acee76592cc7c3f975546e357bc6dcadb3898e9739050a02a14))))) (.node 282 (.node 278 (.node 276 (.node 275 (.leaf 0x4129978c437120181644a0174c22791aa12a080e81c1b44294d84e1a02e34f9422a9c8bf) (.leaf 0x1c0350c8c702ec9852924a00e023c1f168b020110843c984c8223960384e46da94b06608)) (.node 277 (.leaf 0x8743d22906733cac57a1cf83c2089c312a8f49a3998d12c152893f12086250d4a25cb85b) (.leaf 0x7f47df90b57a8cd4681107e211449259a4cd2c95685451288e23156834cb45da05043a1c))) (.node 280 (.node 279 (.leaf 0x2290eaf337fc75cedf399aea72d8cbd152a771b64de60a6cedf5074527dbac9331429f3d) (.leaf 0x769f48ab921ada4d29038040400018180a048e3ed5a8d6f32cce5394c99e2ed3f9f572b6)) (.node 281 (.leaf 0x3c1d9d8401f2c8f4b492489d275740f0e8b01eac643203f0fcf2b320ae16eb593c95e27f) (.leaf 0x69a5cb05c6896e87442cb483a250e08c3c24100843e22759f1e044779eddc429448dd477)))) (.node 286 (.node 284 (.node 283 (.leaf 0xa0d1628968724622902b338b4d08925285408824a188f47434a8cc9f4fcaacd2b97526cf) (.leaf 0x6b354c06b4fb65bea3331a9ba68a6d3ccede138a04c31168a45430178b8582b87c562695)) (.node 285 (.leaf 0x4da74c264509a6934ba453944654d18db69c6c189b8a0a65293cda4c17dae996a17a8f46) (.leaf 0x9a4d48ec32492d8ac764146753c26b2a0f0b28326773d29b2c26150b048281b0c0642e1a))) (.node 288 (.node 287 (.leaf 0x1c8d464361d8e8703481c16124f9bce614528112189048413a6d388313094c6801198501) (.leaf 0xa8d4148e0541c5caab711c1ccaeab55158e48caa63aa737b8ce6e78fabeaf538e2b46637)) (.node 289 (.leaf 0x453f25b337da341011060241410078381a0b5346e306e8f1caa5558d2aa2e6d70a962c6c) (.leaf 0x413dd78f660222612e43211e6805d3ca572a40aed06855eaf9828b98cbd0ebf7a3fdf4fe)))))) (.node 306 (.node 298 (.node 294 (.node 292 (.node 291 (.leaf 0x58add70b55cada512491c8a4327904964d29038080200018140c047abe1fa89964c9f28c) (.leaf 0x783b1dce878bb4f8783b9d8f6753a1e4f47e3f9f48840210f07c3f1e9048a435a2c164b3)) (.node 293 (.leaf 0x2999caa595db818cbf7236986d66535596de66b481a38058d02e2c0d0ac3e2275ba9dee9) (.leaf 0x180b848217cc6a15067dc72291046219548440a1d48ac512795a8d4b248a44c251948e4d))) (.node 296 (.node 295 (.leaf 0x271b0e06228978d4682e16e55509c4bea94a9ad1e79469ed3e7f440806c1c3a1b0a4322f) (.leaf 0xa82828280c0a83c207b411e50184459fd0b7e47e250d44295569c45a655ca057a8d2897)) (.node 297 (.leaf 0x4aa3d1c9327918966428198a8585d3097cc76435192dd66346734b9a4ea774d9f50c1816) (.leaf 0xa7532af33a2d0822391b8d41e2d1d8c44a237c41613007d41e270c44a010a9d50a61149f)))) (.node 302 (.node 300 (.node 299 (.leaf 0x8ac44e46d3898cd25f399acb45d60385cadb60b5dccdc73b7da0d3994c2ab2e95cc6a356) (.leaf 0x71b659ccf9654a6f499b5225b53a0d001033098242427190983a1c7bc6dfaf38f45dff1d)) (.node 301 (.leaf 0x7ac0e31027a4661f0e41299069b5426952a748a40dc4824984de602b15d78c45eb15c4d8) (.leaf 0x8f1c9ccae453f01e0e7ea25808860a2d92500c862124f84138a2c86e9a05e2e34a85b8a0))) (.node 304 (.node 303 (.leaf 0x6c188bcd4108812b136816929126896d6c4302810f6ef77108f4b45bad5ce7357c7c763a) (.leaf 0x588f5c66f190da306e711c22c6c7f3e8121006029eaf85e3d97abe792e8d466180a8c264)) (.node 305 (.leaf 0x6fb65469f168a5369d6da71ae99120799c562e16198545c914060678111d840590f882b8) (.leaf 0x3e3acf0763cacce8b053c7472355346dcaab70a9617070906c2c1481c15890462b1e02c2))))) (.node 314 (.node 310 (.node 308 (.node 307 (.leaf 0x81120924b80118d660138c44c284d18cbe98118722b0f48445a6cf4ba4d1d0d3ebb40400) (.leaf 0x3fbc40e013bba8fc3f3aba5d03c54c646637541c62e6d7fbd02208413dd068579a002615)) (.node 309 (.leaf 0x6594c2e1a8514a0c4c631289aca6191dbc67160ad44654f369acd512875230e2e95d1f0c) (.leaf 0x1107d2d1449441a459669555b1c1c0d1551a5639148e046bec1a0b463e50c8443afd02bb))) (.node 312 (.node 311 (.leaf 0xa8d42672d994b2612e98cbe572a9ecee6f399b4e2793a9acd29f4da4d3a914ba652a8f46) (.leaf 0x6e8bcd02e34b7142a0a2d068540a250e7f3e94c9a51239248a4f2590c82af53a9556ad54)) (.node 313 (.leaf 0x2806226ef8947ddcfc8f3f613085a0e8840e39301128827939a2b72dad5ccc15722ca2c8) (.leaf 0x362ea8ed6a3354bed74c264bcd410ad9a0e74a9ed28af64864400521810b4731d83cf48a)))) (.node 318 (.node 316 (.node 315 (.leaf 0xa8cad4881471d08f342a0f618e9744362ef3804062cf2a8380792a5dac0dae1402948cc2) (.leaf 0x38b950aab25b1ce0bea58a294da328a4c6db4ea70c8629fb351e759ab0d98b19f484ab20)) (.node 317 (.leaf 0x9c3196436910d01600970d50876250507c0a75469f2eb7bc6e0b047c3daa8e41fcbd7eb3) (.leaf 0x4129890c4372f0aecf5420c92c5712f69227305204cd94d26cc2d891806aa373baaa7215))) (.node 320 (.node 319 (.leaf 0xa087522a99b84d9ce3a054e5a1c4829e6c122b1bc640987465e90f8140e30f5a90ce5808) (.leaf 0x980e50c7826058800ca1c9cb325ab4c55887499e49b3a2c1069a2c338ae982d4f27ccc2a)) (.node 321 (.leaf 0x35d3862df5128cd4309307e8557492b676170f00e211c7dbb6231d8341dd8fa920e01a02) (.leaf 0x2281a28f17fc56150b783fa500799045187c2906c8810a2348bad33f25e78ca2e2e29ede))))))) (.node 354 (.node 338 (.node 330 (.node 326 (.node 324 (.node 323 (.leaf 0xa652a8f49a35229d4f6ea85b8a0348bcd02ea28952c7f9eb2c48b99488a6623469f4a61a) (.leaf 0x6da705ad74ca6c52d96fa8ccc6415350c4d82f184d43014260c69a2f89cc026358c69b4b)) (.node 325 (.leaf 0x873a9e6e97a3a1fef18bc66131384449faef7e3ba3d1f4f36858d63399456d56f2893e9d) (.leaf 0x85452391a83c16230480c0e1b0f76bae2b0b8ec6df4f87b3b1e4f57f3c22d1880431ef02))) (.node 328 (.node 327 (.leaf 0x378ca693e974da812295c865b2099ca6a3532822830202d1e81e0521810e63b83441f6f9) (.leaf 0x252108e8105954a68d0d08868a40a2392076091d03800119f46aa705150ac3e048f48a06)) (.node 329 (.leaf 0x8110d86e232009082040f02207368ce6124954b26528a85489e896013910b407108e43a) (.leaf 0x68250327b10ad9ceaf262181abb2923070e00b3098878012c0367c1cb854aa6062e97840)))) (.node 334 (.node 332 (.node 331 (.leaf 0x122e46ce30aa3d2277099d43a01129fc6ea99dce685389acde7f419348e8b3dabd559295) (.leaf 0x97c967944ab55190d16094516b72dad5ccae632482ec30fb35969656aa83ccc672c806b1)) (.node 333 (.leaf 0x63a4d8a7967acda69772aacb0be5e904b8b838388968524a0cae3f2e9f8e2a89d50e6327) (.leaf 0x8d52ea94a723689615250520b39824e18cc7429dd087655275569c26a1cb2bf6534958e4))) (.node 336 (.node 335 (.leaf 0x380d8c4f65f2c87e0105800caf975c8c532f5facce23731bdc6b2e8dd55cadb143a86922) (.leaf 0x69b4223428743045409f0822913a2449a4d18850d228f482392c954ba5124931f028c8f8)) (.node 337 (.leaf 0x57281589e2b150b82467330b01e2b874aa1c87d061b3f2d8859acf2c87cba251196a2b45) (.leaf 0x18c5ea23ba7479ccdcab53205000d4da6818854267908653220d3a541f93498521e944a1))))) (.node 346 (.node 342 (.node 340 (.node 339 (.leaf 0x46a9cfa8a51abd5a9f1901a30f018459c4b86c35054ec133a24004a43ba8c2e6aad45725) (.leaf 0x33beddb2635bfe66736fb9e3b578cbc6a729a7c7dbcdd8e534a65085cf596c983ced527f)) (.node 341 (.leaf 0x2886586c52685d0675409d1367b4ca2d0e7937914d4fe71ae4ccfa303d25a43343f1b2b6) (.leaf 0x2080cbef39583cd2fd6bb045b3113ba64205a4bbe8e2f6b2dc59272484c8e1281cde0335))) (.node 344 (.node 343 (.leaf 0x702d0712424118a44f0d93988c226059048046298f88952a210c78048f4c2f52f3c97ab1) (.leaf 0x37110d8105e2e8800c040f258429503976b006808da11991c9c2c01ccc06607a94a2a03a)) (.node 345 (.leaf 0x8dc560a9d6ca9dda7d8eb7e16a383a7d8acf3cacdcad355a5d26c762240f07688b6e089c) (.leaf 0x9c25124c63a2c1aee180c3532a561238241c010005a391a88c521b0b052070f4da99d67c)))) (.node 350 (.node 348 (.node 347 (.leaf 0xb87e6f41919eeab459ca55549654b8e4c7f5cadaaee79eabe76c956b2d22ce3baca84d0) (.leaf 0x814d934d8761ea98dc842820c9e3aac66b3f47b3186cd0987406011b8946c240c8843c15)) (.node 349 (.leaf 0x188ec602e15060561aa4461e0eea747a12a18528950e2929f970b5ab39a78ae9d32158ca) (.leaf 0xaa51286d17234a1d40923aa44b4a544a20da744822f51a345a01344c351aaa4130c80c04))) (.node 352 (.node 351 (.leaf 0x138cc0e05178e85020160e06822a4d4a50efa5c4e35148cd4de329a7c7e9add8e37a4eb7) (.leaf 0x2495c823f38974e05c2896cb04b269649056200f8c65a31138984a74c868f50864f9ace0)) (.node 353 (.leaf 0x1e0f4be6d2f1b08c5423954c26e22108d2723213cca52301bc8a43359ccd46833140ce53) (.leaf 0x7ca31e92d7fccdfcfc7d229f68d41af662c197a2d0abe43afd04bc983de5cc07b2210c84)))))) (.node 370 (.node 362 (.node 358 (.node 356 (.node 355 (.leaf 0x9690e40042a870160079cade52a402e902bb04024220f08038180a0682deb2c993f5f089) (.leaf 0x95039f66776c9857250f9641a026cad9aab566b3d7eb35dac1e860740983a57008fc7808)) (.node 357 (.leaf 0x58af48a6f030c8a856050f87a09775221f417c995d72396109f868a30ba1b3f1096c532f) (.leaf 0x121706c707b188d81079179f466153b03c580610006415cb8da8b87136198ce5f2c974bc))) (.node 360 (.node 359 (.leaf 0x47a450a7740208ea8346a28faa7521e91c90421d9027478461f064221b9ea617f1aa2c30) (.leaf 0x3e299367b51abd5ca04ba51569c52a21328b4fab5589e49a490c78439e4fea94c1f9509a)) (.node 361 (.leaf 0x63b1984c461b1601020a92c8c4809924a6509a06831360a1288e12512852c954eaa91889) (.leaf 0x854260b392913e073785cf67908824e0364e80cd4325183cee75060b1302e4d65b2594c8)))) (.node 366 (.node 364 (.node 363 (.leaf 0x69b41cadb70b01aec17f9ae2e31129746e717b98cda117997e6673a88ec465a1acba560f) (.leaf 0x9f08841401a48a4205a747a2b458dd5664727e9a63b57ab53223421ccc05b316fb9dccdc)) (.node 365 (.leaf 0xa38be394da1c4071241649dbcdd69345c8da702d1acb778c66190e143a80e337489e5353) (.leaf 0x8952a8f50178ea3f4f9e2ba10a08b518602e8a44e354b94549df49a7c7e8912aa52aa03a))) (.node 368 (.node 367 (.leaf 0x822721b014ca94521b85a8cb8702d944c44e2f1b0d46897a2dec88794a8200e7f3f28954) (.leaf 0x984b9e72b0883dff337ecc9cd566e5322f51188ee3d4e4a4e27f35120d842199eabd2eab)) (.node 369 (.leaf 0x73d5e8b5569b9622db6bb845a39118d63adf8ac6cba7131968be6d359ccd27260cc5eec0) (.leaf 0x221096f27752d2492274c840e0578ca5df285c1f96b25761e9d12003011e0ee685084a37))))) (.node 378 (.node 374 (.node 372 (.node 371 (.leaf 0x591dd62750080d727f5b49a467b599e4f076581d00400769f5d67c1f904803e1e0f48a43) (.leaf 0x301bcc26e5ea0d788204025e92d7acb21d40138ce3353a4d49c4a8813613536130ca3148)) (.node 373 (.leaf 0x83279aaa41586a14a2672443a1371aa6833767b1588900e049b2a787c0d36a62b9249056) (.leaf 0x3394cca525fa1d0c845da041a0b7da35f28c6939220da6b3805838110d238de8a46994ac))) (.node 376 (.node 375 (.leaf 0x14081bb4d89d2d913a8035131341506212a1632499ac30f85d96ad4b2a8b24d26128aa47) (.leaf 0x63a4d848e0b0520e9f82a74b04b23150cc503213d7c855d200180a7d229f08968d0e193e)) (.node 377 (.leaf 0xa24fc48212e16de50145a668f3517864a25e8b4215ca09e518602e6623c3c1564ced2b39) (.leaf 0x806c1c3a36139ed0455a725f54a54e0523638189fd0b7e47d46afa7cf4d46886c492e94)))) (.node 382 (.node 380 (.node 379 (.leaf 0x33141bac989c31269547a3a873e0f080b05468b32130050a6275341506190d4442965550) (.leaf 0x301170b544a0018162791974c27c4150a9da5ce450150505096645f31df5074fa2a9b3b)) (.node 381 (.leaf 0x76bc4fe7d934a48a435cad9dee93c9ecea7493c840605208f56eb1783b1dce83f1ea4b20) (.leaf 0x562893ca41586994d53e1e251240101c8840210f160b475ba8ee7691c8802001f8f966b2))) (.node 384 (.node 383 (.leaf 0x5fb91b4c67dc715a8d3394dbccb8a4412c920f888b255693350e811605c9a476b30e1506) (.leaf 0x484892615eb1631025426a9136130c9c4d8462181a382913176e07cc695484058d0ca4a)) (.node 385 (.leaf 0x5e311e91954a9e5b53301bdb2e387c392290a0d003a1c2b9599ece7ac0d069ba4cdc4e13) (.node 386 (.leaf 0x2e969a6d07ebce632b1683cd25f60b5e3d17ab53a9951188edccdc5320a5952040ccdc48) (.leaf 0x994c02239391b580e18dbdeab2e1b8d4e26372b6dff1dabcccd6736fb9e2b11a2d084a23))))))))) (.node 451 (.node 419 (.node 403 (.node 395 (.node 391 (.node 389 (.node 388 (.leaf 0x63b15caab86a39607461405ae9970a962b0f3e3ae0b034ea6d4d1b88a40f07662411b69c) (.leaf 0x31a6904f73ebb617076fb65469f8ea9c461c0100036160a048522d1c8d5a6cf4ba4d6679)) (.node 390 (.leaf 0x8820ba571f9f8964938aa10a8347c30787574ba08d002fa60db17403cd230e3bba89102) (.leaf 0x6816929125a1e89d086e28180883fbc4d66054c65fef4128740e010a84c5027188986637))) (.node 393 (.node 392 (.leaf 0xc8605e2e1d0ec1c0f2db456eb528b21ccae60a2d2b13211eddeee27c24d2a13947912fd) (.leaf 0x32184dd187c3d59c56202c87cec3136178f65b10d925034375ce7357c7df88a108800a04)) (.node 394 (.leaf 0x120780606180a86c320803014092e16082b8383897cbd66151623d2f350d9165d3c888f0) (.leaf 0xa2d0651239ccde9749a7522a555994b285409248a7136a5532612e5c914d466719bdfcfa)))) (.node 399 (.node 397 (.node 396 (.leaf 0x934a67b3ba7d36af5399cb6894393c96793aaa55a5f319fcfa43209acd28f46a8546552b) (.leaf 0x5fa1d9a556191dacd57029176814b450a50a32a89551a463e525102631895066d2790c84)) (.node 398 (.leaf 0x551dd087642aad3a9c6594dbc6756c711afb0f8882e1a160ac70340682da45926b29c8ac) (.leaf 0x7cbae72159c318284a6392e0b041b2c8143e5f1c0c8627c3daaa37970d5ca716d98def1b))) (.node 401 (.node 400 (.leaf 0x5e1b922a94829d06a84da6904a6910d2a8e4a58a294da8d3aa4601058025ebf598fc5265) (.leaf 0x6795db260a4099e90f960226e13094d98a4981c0988486738c1256378c97ae230b61eb18)) (.node 402 (.leaf 0x60b98d2dc7ec7980724a9ed28af451e916ae50a811288a054e922787466a433a08765a1c) (.leaf 0x8947c74b410ad886042dad4d02e7e3b81c420cb24a01828b22130827939a0e707968e63b))))) (.node 411 (.node 407 (.node 405 (.node 404 (.leaf 0x2f351e5165d1b257516b97de717709b51e7540a38e8a44ca6100a510015a2b717b7626ef) (.leaf 0x9f4868ed6863a6a0e09fb34ab20a33561ae8952ed603c9ab0c8f3480c018446662c4a83d)) (.node 406 (.leaf 0x2e2e0d4307f3c02044a2896662369975be6ba70c5ff15990452c7f469f52e7e51a89187c) (.leaf 0x43a4cf2ac4fa790c78114a688d2a7b7a28f19401e7acb2986a78ca85c283652122e48a06))) (.node 409 (.node 408 (.leaf 0x680a761726cea0f060b1303c032c104cc2a7d3b01840a155e635616d32231d980e524ad) (.leaf 0x100843a250e08c441f018180a04038040400a1c9e9a2c8847248380fc98b325338adf6ed)) (.node 410 (.leaf 0x178b85027130c4522d160ac1810050241c0f040441a0b1b0c8743b198dc72351c0d03c24) (.leaf 0x73abe32a98ea9e38ada9d5c8ab921ad9e27f769f653260c0642a130b06c28120b8685430)))) (.node 415 (.node 413 (.node 412 (.leaf 0x29b2e773d331a9ba68301adb2df4fa8dbc67a6d3df4fe7e229e8ff7da365b3337b8e3e73) (.leaf 0x984b8acce89169a0948724622908824a8142203b07cb25a1e9d4773c1da4922283260f0b)) (.node 414 (.leaf 0x2742091028231099062531a713631361b8a031a69b69c6d27a954c7b2f180887ba090c84) (.leaf 0x7ca32593237460e51e8da9a34aaa9556269587c562896a0d1488f077909dc7b759f25123))) (.node 417 (.node 416 (.leaf 0x5bad47e7e599e64f2527c260b032942a733732184d2a14ea6ccaa2a5d26914e7c3d5fa89) (.leaf 0x5fa1e5f3138389ccae38aa1caab722b2a9562c171a25b2b9759ed349a5da459a1d1082b8)) (.node 418 (.leaf 0x86a38aacd9f4fc7ab1748f1d075581d2432028b20964963b149aca9d4f17cbd60a2d0a83) (.leaf 0x2f350be986ba65acd5a3d1974f279a017681954acd91636c5dc2a570292a1512a332188f)))))) (.node 435 (.node 427 (.node 423 (.node 421 (.node 420 (.leaf 0xa68b0ce2b330a8bed74c2668ed6a3355a85e34b7142a06e8bcd02e23401850123b0e6935) (.leaf 0x303644d4830b60c6db4ea70514ba5368526532188d6df18d3946a2a7b78d43016d313e9e)) (.node 422 (.leaf 0x2e2e278caab4c526ac439e687272cc94b0419d135ccc15722da2b72dad590514d26c4f49) (.leaf 0x21810a0185420caecf712f492c538b950aabaa3925ebf1facd7c7025b1cbad34b9fa88d2))) (.node 425 (.node 424 (.leaf 0x11ccd1a7d114a48a062986aa32b4729102749f484ab202a0f6684739968760f451e84005) (.leaf 0x4aabd287b10ad9921953a42a7400e4b4de561902425361acb908761a4881600050f8284a)) (.node 426 (.leaf 0xace670c612d152c7f122e67acbabd095a920fc983c039d85d1e759fb3598b19ab0dced0) (.leaf 0x1e2c1746c23308e4c044a2074b4071089e4e54a443b4171b3827371bd55547700c8c6cb2)))) (.node 431 (.node 429 (.node 428 (.leaf 0x243102332461f00f280811036521ccc10c781c4901a02061002c4c36b8500a5a838254bb) (.leaf 0x7d3b20f068bbce18e986ba22cf2804063cfd89c7e24ef7e3ba1308532086752044b0dcbc)) (.node 430 (.leaf 0x8cc39e90f8c3d605038dbde34ea7cbadf0f682c11ff158a3c5fcf085c2a3b118e441f6ed) (.leaf 0x412010c783da6d1699419d50274439e52c954ba51228f48239269255275569c429dd0876))) (.node 433 (.node 432 (.leaf 0x250518ec651abcfea946a28faa756a7d44a157280fca84d260f4a45627918893e29910a5) (.leaf 0x65320a44f2706c90462605988c281cdca3019a8649213238489a1762b0e0b39824e09615)) (.node 434 (.leaf 0x7c995d723978a47e01058017eb385cf4a65083ced96c9854267908814026d340d0627506) (.leaf 0x7409a4004928ad6ad5214b2540e1e0201a025dac21f412dc367e212b874aa1c2c87d9ecd))))) (.node 443 (.node 439 (.node 437 (.node 436 (.leaf 0x2b150b01e67331f064383d8c4361f0297cb27e1a1e86021cb5f66776c996cd9775228c2e) (.leaf 0x784622c30030c9d82a5c389b0d4221b8d8102003178ba7a985e45e1e82482035eac4b824)) (.node 438 (.leaf 0x8a44e891287432813e11082871069346354baa529d428910d1c8da7f1a88a6f7d19972e3) (.leaf 0x8fd3de31994d4e394d6f3765152a80e80e33920e168e077d268e2f7489e4205938b16ed6))) (.node 441 (.node 440 (.leaf 0x60385fa697997e560f988b582d78ad14ba252d08e234269b42375538bdcc637970d5cadb) (.leaf 0x18040400038140c047f9ae66738ed5dbee78f53a2e31a88eead4c733726472368466039)) (.node 442 (.leaf 0x200f9727f5b498faed94bc48a433dc8cf8eb943bde0ee221096275581d242e9903a0783d) (.leaf 0x963d43a130e0486627190981009599e56f275c1f96b25208fd64773c1d96924913a8f4ec)))) (.node 447 (.node 445 (.node 444 (.leaf 0xa043a6d026c26890565e209c6a953b66a719379825af4a0cdd4d0f81a6ea5498c520dc61) (.leaf 0xa851e2d463617a54f2120d842190d8a4742f180b8200e67b15c4a82b9257a83672458890)) (.node 446 (.leaf 0x2d945172f4a4e2089c8952a10a02718910f657cf616a38fd3cd4687f3f27f3552c360299) (.leaf 0x8f538e469993f5c2d7a8c5cda5f95bcc4a371c88c6a2d1d8c4220f4baae8954574f0b870))) (.node 449 (.node 448 (.leaf 0x69b95cd562e9c583316850a22db6e530b463604c25cf773d5e3adf399ae66ffa2d562b1b) (.leaf 0x89d2e12a12799112f86623d848e9f43269006a2608c545d2003c150b05040280c0a8180a)) (.node 450 (.leaf 0x1c088682c0d0ac1a0b49b1da343644e8b04b5f215933b83a7dbb4d2819914fa4ace60a9d) (.leaf 0x4321196ad8e378a66746bed2caa8a46a14a22919518f966b0dc0d652354aa475da043e17))))))) (.node 483 (.node 467 (.node 459 (.node 455 (.node 453 (.node 452 (.leaf 0x9c25122ce3bac98c9288b6e089c62240f0766939194ac2c9357e874931a20da83278984a) (.leaf 0x842826d024d360f4ec8327a60c0973dd10f6412f10c842d18c9c6224158803e2612a84d0)) (.node 454 (.leaf 0x2e16c9257208fc9a5925961cad355a5d8acf3cacd8e93a544a810e922d244ea8836a98dc) (.leaf 0x7234a86d1ab39a78ae54388fcb892ad594ac9d32262c145cbd06bd43afd0abe38974a270))) (.node 457 (.node 456 (.leaf 0x60286e250c8d848210987406010b87c2a1e1c8b46a230d8a4241c010002c14aa5124eb7) (.leaf 0x1d0bc66270281c702c1a08840281d8c4602e190980c040d0ac302a07844200e048201a0b)) (.node 458 (.leaf 0x40aed00ba3697cd85e1e8f08e55231526b3f3aac586cd47b31c2d780a95330d3a2c1848e) (.leaf 0x85a8d4ed93ebb60e9fa851e42e97035a7d0ca8c5e2d46903a148d59a40130d495bcde52a)))) (.node 463 (.node 461 (.node 460 (.leaf 0x46bed14fa399acd468379808a432999ca066abb9e7aaf54b8cfeb9932d996ad9db263adf) (.leaf 0x3dc8d54969ca56371581a99370f3e3ae0a9d8fd3ea71994bc638dea6b7666ff7f3f25af4)) (.node 462 (.leaf 0x8f53a3148783ba14a284a8664fd7acb118f944be0e469371848842291949e64aad166f41) (.leaf 0xa15024922984b8910231a69230e3bba9ee8262411b69c88a40f076a952650ef8d4529713))) (.node 465 (.node 464 (.leaf 0x203b07cb25e3d89d086e280b4d04a448f4b4602209906253193cda494410c849b4e2994a) (.leaf 0x463e5551a9ccde9d4ba4d228b419448e652caad4a0b034ea6e2b0f3e3ae36a631360acce)) (.node 466 (.leaf 0x100072353218488f07c3d4dd1827c24d2a14ac4cf6ef213b9fa8939478a50a511952d14) (.leaf 0xd05c582b1107c1a0b1c0d02a13188a04e26128740e01088206e330b06c2812168a4461c))))) (.node 475 (.node 471 (.node 469 (.node 468 (.leaf 0x6fa7d46d93ebb63aa7150c03c240300c18100502464360c0645e2e100840a0407838763a) (.leaf 0x39b9d5f1f29b2dbc6746bed5b1c9dcf69b4f94c9a672dabd4cd6603fbc5fef454c660f0b)) (.node 470 (.leaf 0x1e3a1e68036c5d85016ba651d0d3a2c1c2a5331a88ab97d3f8dee328325ba6821ad914fc) (.leaf 0x364588ec36b354aacd40aed48e09a4d68f469f4fe432095caaa35023400be9847c30eae9))) (.node 473 (.node 472 (.leaf 0x98cbead5425924ba573f0fd0a8338aa18ec569a4d2ecf3cacdcaab6a178a8cc1eac574f2) (.leaf 0x2c17082b85f2f4e0e264145a25b5bad5828b732b89aca691650ebf56392753ca1d124f25)) (.node 474 (.leaf 0x1e9508a069b048941423cd0a0182986aa7401a48a433e0288045299687016002ac808604) (.leaf 0x5b0843f261acbaa32b39968760f9988d4e90421d948813a238f48a469f4de56190247c0a)))) (.node 479 (.node 477 (.node 476 (.leaf 0x56a49c6ce590d962cc5c890061e09cdd8c159cce1873564865973d0bcec3b4100c8d9b3f) (.leaf 0x303644d48328a5ab46340b8ce2b1bd55ced012d16af4254a4554773aa3cf69557a512c7f)) (.node 478 (.leaf 0x4c26542a05128d3c9f6c184c8626a178d430330a84f496d0a2974a6b51dba2f6f53c594d) (.leaf 0x5bb45a54493d0caecf5f8fd672f5a96cb32531b6cbed76e1a4d6df18d3a982d4d26d3a9c))) (.node 481 (.node 480 (.leaf 0x5420d0aab5722cfc975621cf293712f57c705c170825824b1496c764145953c26ce9c954) (.leaf 0x8cc3a34ea74c31df138fc4a28f18e441e90f7cbadd10d773f1f6ed38b95ccc12eb4ead31)) (.node 482 (.leaf 0x7bc6e2ef38f3f5ff158ec4630f57c3da2cf2783f9d8fa8140e0b048040613088542e0d07) (.leaf 0x2003090c4233089e4e2906c981619d49c1505a0e80f281c490112c5d8f1612a210381a02)))))) (.node 499 (.node 491 (.node 487 (.node 485 (.node 484 (.leaf 0x42aad3a9c551dd087636b84e4c008cc873304129900a544a21187c431e0dcbc5d1b08810) (.leaf 0x44a210eac3ca4d3c9f492b50c783f25d44a34b1fd1a7d461f106a84da6922a94829d4c82)) (.node 486 (.leaf 0x8abfdca716d98eaa37970d636f74ca60ea8f40a90e88e4029516ae50a80f6954a2bcf48a) (.leaf 0x6839cb473078ece4c07ec7a6356a60b68557980e6231d699769cdf358c68a259988e6411))) (.node 489 (.node 488 (.leaf 0xa08765a1c960221ef45fcbd663f328a6460105801f2eb6b97e5751709b5e71760b98d2dc) (.leaf 0x580f1d10d5a96cd02e5b084860421039dcfc92964ce2b9307c1a027dbb59e57a4364c026)) (.node 490 (.leaf 0x9488a50078a3c69227a054ea43387465c954a5b6a9428910d234ea6ad199b3f90155772a) (.leaf 0x6b51e433e70541d30c5bb45ba2f02881683a77c4e251f93d0e9a2c920e2211c69511bd4f)))) (.node 495 (.node 493 (.node 492 (.leaf 0x5c8908a0622041e0fe5eb88c2d86738cac6f048c8dcbc7ac617c703218964361f029f0f6) (.leaf 0x9cb1a7015250520b046a17962cc1e951746c794588258330a8061e20031d8fa5c170d430)) (.node 494 (.leaf 0x84c209b3a9d85c98168341d953c65cf4a61a2906e150b629266e139b049884881c098e4b) (.leaf 0x190983a130e0481208038140c0401804040061cd48f346111a0300641459219280609e4e))) (.node 497 (.node 496 (.leaf 0x180b86c2410864521b08038702c1a088561a0f85c1a0b1408054180f0542c14060286627) (.leaf 0x80261988f6123974802a11a42e9903a16275581d07a3c1d8c46e251c8b46a230883c742f)) (.node 498 (.leaf 0x95bccda5fa851e2d469fcd61b0152a65e52a36179c0d66aa919ac35da04aa479f431a934) (.leaf 0x2612a810e6c4da049a6724588905e208ac48922d244ea761e964773c1d8803ea8c5dc2d7))))) (.node 507 (.node 503 (.node 501 (.node 500 (.leaf 0xa637284d06dc4660c0973dcc65aa544a10a09c252089c7b220c44e6d4420c9e632490c84) (.leaf 0x5fa1cb24da1b4674c863a4d7c852c12dc4a867b157a832b9264eb75c4956a7e599e4823f)) (.node 502 (.leaf 0x783ba467b759f08842ab399cad398b04e25daa51278ae55a5e5e8b38170b6517234994ac) (.leaf 0x7ca30ca52a5c4e12a19ca560a9d7c224c84fa95263148a0cde1f035326deb2c3718650ef))) (.node 505 (.node 504 (.leaf 0x6ca9e5af43798252f15cc996c7f769f48a43a747aab458dc5664fd391a63514852895496) (.leaf 0xa7c7e7aaf85a8dfcfc351a238de65ab5f68d3394e9add9db260e9f7d228cc50a9c65c6a9)) (.node 506 (.leaf 0x7a43df2eb7dbb59b3f5b0843b4100c8e4c1f2ac808604968701600abb9e3adf99bfce66b) (.leaf 0x5fcbd663f2cc95ab46340b9b260135205265338ad772a580f01c42044b01a0286ba1f8ee)))) (.node 511 (.node 509 (.node 508 (.leaf 0x1c4900f2874c323eef89c4a330e8d3aa391078c52433e02882a7401a48a52225a96d9e57) (.leaf 0x421d91a7d5bb45c95493d0da5446b51dba2f13d24514b6d52a9a2c6f53dc1501d2d06752)) (.node 510 (.leaf 0x52a011288532090c78461f0ea8f579ed2a9454a45547756a48fe9640a90e88e451e94e90) (.leaf 0x3983c765a1acba662345ab906a855a150eac3ca4d2e7e4ca6142a04da693a9c4fa7946a2))) (.node 513 (.node 512 (.leaf 0x6f9ac634e709b4e4c01ccc0233279c5dfb1e8dbde3b117fc55ced01bd56af4212d165751) (.leaf 0x634e2761765cf48f342806025360a128a61a60b99ca7198d59a65d6b97cd2dc6d98c5b4c)) (.node 514 (.leaf 0x654f184462793988480b130365280c02130881c0a0b0483c1a170a61cd5921909cdc2b39) (.node 515 (.leaf 0x7d3b1fcf058b31c6ce1b2c8061e5c8907a54378246456050f88a0628b218a496392c9b3a) (.leaf 0x5eb897c7020961705c2f350c2d832188cc2a350c1746c372f0184008111e5167ac61f0f6)))))))))))

def starAt (i : Nat) : Nat := stars.block 8 60 i
def imageAt (g i : Nat) : Nat := rename.block 32 9 (g*344+i)

lemma direct_first_catalogue : directCatalog 0 = expected := actual_catalog

set_option maxRecDepth 20000 in
set_option maxHeartbeats 500000000 in
lemma table_words : (List.range 344).map starAt = expected := by rfl

lemma table_get (i : Nat) (valid : i < 344) : expected[i]? = some (starAt i) := by
  rw [← table_words, List.getElem?_map]
  have hi : i < (List.range 344).length := by simpa using valid
  rw [List.getElem?_eq_getElem hi, List.getElem_range]
  rfl

lemma starAt_bound (i : Nat) : starAt i < 2^60 := by
  unfold starAt Lookup.block
  exact Nat.and_lt_two_pow _ (by decide)

def checkGenerator (a : Symmetry) (g : Nat) : Bool :=
  (List.range 344).all fun i =>
    let j := imageAt g i
    decide (j < 344) && (starAt j == fastPermuteWord a.line (starAt i))

def checkedGenerator_correct (a : Symmetry) (g : Nat) (checked : checkGenerator a g = true) :
    CatalogueRelabeling a := by
  refine ⟨imageAt g, ?_⟩
  intro i word present
  rw [direct_first_catalogue] at present ⊢
  have inside : i < 344 := by
    simpa only [expected_length] using (List.getElem?_eq_some_iff.mp present).1
  have word_eq : starAt i = word := Option.some.inj ((table_get i inside).symm.trans present)
  have row := List.all_eq_true.mp checked i (List.mem_range.mpr inside)
  simp only [Bool.and_eq_true] at row
  obtain ⟨valid, matched⟩ := row
  have next_inside : imageAt g i < 344 := of_decide_eq_true valid
  have agree : starAt (imageAt g i) = fastPermuteWord a.line (starAt i) := beq_iff_eq.mp matched
  rw [table_get _ next_inside, agree, fastPermuteWord_correct a.line _ (starAt_bound i), word_eq]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 750000000 in
lemma raw_generator0 : checkGenerator generator0 1 = true := by rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 750000000 in
lemma raw_generator1 : checkGenerator generator1 2 = true := by rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 750000000 in
lemma raw_generator2 : checkGenerator generator2 3 = true := by rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 750000000 in
lemma raw_generator3 : checkGenerator generator3 4 = true := by rfl

def faithfulGenerator0 : CatalogueRelabeling generator0 := checkedGenerator_correct _ _ raw_generator0
def faithfulGenerator1 : CatalogueRelabeling generator1 := checkedGenerator_correct _ _ raw_generator1
def faithfulGenerator2 : CatalogueRelabeling generator2 := checkedGenerator_correct _ _ raw_generator2
def faithfulGenerator3 : CatalogueRelabeling generator3 := checkedGenerator_correct _ _ raw_generator3

end WeightFifteenConcreteGenerators

/- The exact-cover checker uses thirty stars over five selected groups. Tables encode allowed and compatible star indices. -/

namespace WeightFifteenVerifiedSearch

structure Tables where
  starMask : Nat → Nat
  candidatesAt : Nat → Nat
  compatibleWith : Nat → Nat

structure Cursor where
  chunks : List Nat
  pack : Nat := 0
  left : Nat := 0

def Cursor.read (cursor : Cursor) : Option (Nat × Cursor) :=
  match cursor.left with
  | 0 => match cursor.chunks with
    | [] => none
    | chunk :: rest => some (chunk % 512, ⟨rest, chunk / 512, 31⟩)
  | left + 1 =>
    some (cursor.pack % 512, ⟨cursor.chunks, cursor.pack / 512, left⟩)

def visitChoices (visit : Nat → Cursor → Option Cursor) :
    Nat → Nat → Cursor → Option Cursor
  | 0, choices, cursor => if choices == 0 then some cursor else none
  | fuel + 1, choices, cursor =>
      if choices == 0 then some cursor
      else
        let index := choices.log2
        match visit index cursor with
        | none => none
        | some next => visitChoices visit fuel (choices ^^^ (2 ^ index)) next

def verifyNode (tables : Tables) (cuts : Nat → Option (Nat × Nat)) : Nat → Nat → Nat → Cursor → Option Cursor
  | 0, _, _, _ => none
  | fuel + 1, remaining, available, cursor =>
    match cursor.read with
    | none => none
    | some (pivot, next) =>
      if 300 ≤ pivot then
        if cuts (pivot - 300) == some (remaining, available) then some next else none
      else if remaining.testBit pivot then
        let choices := available &&& tables.candidatesAt pivot
        visitChoices (fun index branchCursor =>
          verifyNode tables cuts fuel (remaining ^^^ tables.starMask index)
            (available &&& tables.compatibleWith index) branchCursor) 344 choices next
      else none

lemma visitChoices_covers (visit : Nat → Cursor → Option Cursor) (fuel choices : Nat)
    (before after : Cursor) (checked : visitChoices visit fuel choices before = some after)
    (index : Nat) (present : choices.testBit index = true) :
    ∃ input output, visit index input = some output := by
  induction fuel generalizing choices before after with
  | zero =>
      by_cases empty : choices = 0
      · simp [empty] at present
      · simp [visitChoices, empty] at checked
  | succ fuel ih =>
      by_cases empty : choices = 0
      · simp [empty] at present
      simp only [visitChoices, beq_iff_eq, if_neg empty] at checked
      cases result : visit choices.log2 before with
      | none => simp [result] at checked
      | some next =>
          by_cases eq : index = choices.log2
          · exact ⟨before, next, eq.symm ▸ result⟩
          · have in_rest : (choices ^^^ 2 ^ choices.log2).testBit index = true := by
              simpa only [Nat.testBit_xor, Nat.testBit_two_pow, Ne.symm eq, decide_false,
                Bool.xor_false] using present
            rw [result] at checked
            exact ih _ _ _ checked in_rest

-- An accepted tree refutes every predicate that can extend through one branch at each pivot.
theorem verifyNode_refutes (tables : Tables) (cuts : Nat → Option (Nat × Nat)) (feasible : Nat → Nat → Prop)
    (cut_sound : ∀ index remaining available, cuts index = some (remaining, available) →
      ¬ feasible remaining available)
    (step : ∀ remaining available pivot, feasible remaining available →
      remaining.testBit pivot = true →
      ∃ index, (available &&& tables.candidatesAt pivot).testBit index = true ∧
        feasible (remaining ^^^ tables.starMask index) (available &&& tables.compatibleWith index))
    (fuel remaining available : Nat) (before after : Cursor)
    (checked : verifyNode tables cuts fuel remaining available before = some after) :
    ¬ feasible remaining available := by
  induction fuel generalizing remaining available before after with
  | zero => simp [verifyNode] at checked
  | succ fuel ih =>
      intro h
      cases read : before.read with
      | none => simp [verifyNode, read] at checked
      | some pair =>
          obtain ⟨pivot, tail⟩ := pair
          by_cases is_cut : 300 ≤ pivot
          · simp only [verifyNode, read, if_pos is_cut] at checked
            by_cases state_eq : cuts (pivot - 300) = some (remaining, available)
            · exact cut_sound _ _ _ state_eq h
            · simp [state_eq] at checked
          · by_cases used : remaining.testBit pivot = true
            · simp only [verifyNode, read, if_neg is_cut, used, if_true] at checked
              obtain ⟨index, present, still⟩ := step remaining available pivot h used
              obtain ⟨input, output, branch⟩ := visitChoices_covers _ _ _ _ _ checked index present
              exact ih _ _ _ _ branch still
            · simp [verifyNode, read, is_cut, used] at checked

def HasCover (tables : Tables) (remaining available : Nat) : Prop :=
  ∃ picked : Finset Nat,
    (∀ i ∈ picked, available.testBit i = true) ∧
    (∀ i ∈ picked, ∀ p, (tables.starMask i).testBit p = true → remaining.testBit p = true) ∧
    (∀ i ∈ picked, ∀ j ∈ picked, i ≠ j →
      (tables.compatibleWith i).testBit j = true ∧
      ∀ p, (tables.starMask i).testBit p = true → (tables.starMask j).testBit p = false) ∧
    ∀ p, remaining.testBit p = true → ∃ i ∈ picked, (tables.starMask i).testBit p = true

lemma hasCover_step (tables : Tables)
    (allowed_at : ∀ p i, (tables.starMask i).testBit p = true → (tables.candidatesAt p).testBit i = true)
    (remaining available pivot : Nat) (feasible : HasCover tables remaining available)
    (used : remaining.testBit pivot = true) :
    ∃ index, (available &&& tables.candidatesAt pivot).testBit index = true ∧
      HasCover tables (remaining ^^^ tables.starMask index)
        (available &&& tables.compatibleWith index) := by
  obtain ⟨picked, available_of, inside, separated, covering⟩ := feasible
  obtain ⟨index, picked_index, takes⟩ := covering pivot used
  refine ⟨index, ?_, picked.erase index, ?_, ?_, ?_, ?_⟩
  · simp [available_of index picked_index, allowed_at pivot index takes]
  · intro i hi
    obtain ⟨neq, picked_i⟩ := Finset.mem_erase.mp hi
    simp [available_of i picked_i,
      (separated index picked_index i picked_i neq.symm).1]
  · intro i hi p bit
    obtain ⟨neq, picked_i⟩ := Finset.mem_erase.mp hi
    have old := inside i picked_i p bit
    have no_bit := (separated i picked_i index picked_index neq).2 p bit
    simp [Nat.testBit_xor, old, no_bit]
  · intro i hi j hj neq
    exact separated i (Finset.mem_of_mem_erase hi) j (Finset.mem_of_mem_erase hj) neq
  · intro p left
    have absent : (tables.starMask index).testBit p = false := by
      cases selected : (tables.starMask index).testBit p with
      | false => rfl
      | true =>
          have old := inside index picked_index p selected
          simp [Nat.testBit_xor, old, selected] at left
    have old : remaining.testBit p = true := by simpa [Nat.testBit_xor, absent] using left
    obtain ⟨i, picked_i, take⟩ := covering p old
    have neq : i ≠ index := by intro same; rw [same, absent] at take; contradiction
    exact ⟨i, Finset.mem_erase.mpr ⟨neq, picked_i⟩, take⟩

theorem verifyNode_excludes_cover (tables : Tables) (cuts : Nat → Option (Nat × Nat))
    (cut_sound : ∀ index remaining available, cuts index = some (remaining, available) →
      ¬ HasCover tables remaining available)
    (allowed_at : ∀ p i, (tables.starMask i).testBit p = true → (tables.candidatesAt p).testBit i = true)
    (fuel remaining available : Nat) (before after : Cursor)
    (checked : verifyNode tables cuts fuel remaining available before = some after) :
    ¬ HasCover tables remaining available :=
  verifyNode_refutes tables cuts (HasCover tables) cut_sound (hasCover_step tables allowed_at)
    fuel remaining available before after checked


inductive Lookup
  | leaf (value : Nat)
  | node (threshold : Nat) (left right : Lookup)

def Lookup.lookup (table : Lookup) (i : Nat) : Nat :=
  match table with
  | .leaf value => value
  | .node threshold left right => if i < threshold then left.lookup i else right.lookup i

def Lookup.block (table : Lookup) (width bits index : Nat) : Nat :=
  ((table.lookup (index / width)) >>> (bits * (index % width))) &&& (2^bits - 1)

set_option maxRecDepth 20000 in
def starTable : Lookup := (.node 107 (.node 53 (.node 26 (.node 13 (.node 6 (.node 3 (.node 1 (.leaf 0x408401820000000404042820000000104801820000000104082820000000010844820000000010488820000000009084820000000005088820000000) (.node 2 (.leaf 0x1048100600000001004900a0000000010490120000000010450220000000005090120000000005050220000000004850420000000008490420000000) (.leaf 0x109041200000000105082200000000091042200000000051082200000000089044200000000049084200000004084100600000004004500a0000000))) (.node 4 (.leaf 0x1208412000000001204422000000000a0844200000000060884200000004005080a00000004041021200000001009040a0000000104102220000000) (.node 5 (.leaf 0x4880142000000004808242000000040a0040600000004020440a00000004060080600000004060011200000001020840a0000000106001220000000) (.leaf 0x1408010a00000001400820a00000000508080600000000508011200000000500821200000000500422200000000410880a0000000049001220000000)))) (.node 9 (.node 7 (.leaf 0x8090040600000008010440a00000008050080600000008050011200000008084014200000008040424200000004480020600000004400420a0000000) (.node 8 (.leaf 0x90a08040000000050608080000000048608100000000084a08100000009040020600000009004010a0000000810408060000000810401120000000) (.leaf 0x49201100000000085202100000004040608010000004004608020000001040a08010000001004a0802000000010860804000000010460808000000))) (.node 11 (.node 10 (.leaf 0x100520202000000100520088000000010920104000000010520108000000009120204000000005120108000000008920404000000008520408000000) (.leaf 0xa0a04040000000060604080000000060a0110000000006060210000000404120101000000400520102000000100920084000000104120201000000)) (.node 12 (.leaf 0x4882005000000004086009000000040a0200440000004020600840000001020a00840000001060200480000000120a0104000000012060204000000) (.leaf 0x500a01010000000500602010000000410a01020000000410602020000000490200480000000410600880000000408604020000000480a0401000000))))) (.node 19 (.node 16 (.node 14 (.leaf 0x8040604010000008004604020000008084200500000008004600900000004480200410000004400600810000001408200420000001400a0081000000) (.node 15 (.leaf 0x9204808000000005208808000000008a04810000000004a08810000000904020041000000900420042000000809020044000000801060084000000) (.leaf 0x408204801000000408202804000000404208801000000400608802000000100a04802000000104202808000000010a08804000000010608808000000))) (.node 17 (.leaf 0x10a10104000000010610108000000009210204000000005210108000000008a10404000000008610408000000004a10110000000008610210000000) (.node 18 (.leaf 0xa204210000000006208210000000404210101000000400610102000000100a10084000000104210201000000100610202000000100610088000000) (.leaf 0x40220808400000040220410200000010220420200000010220408800000001220820400000001220410800000000a204408000000006208408000000)))) (.node 22 (.node 20 (.leaf 0x50208201000000050202108000000041208202000000041208088000000040a08402000000048202408000000040a08090000000048202210000000) (.node 21 (.leaf 0x804208401000000800608402000000800608090000000804202110000000440208081000000440202102000000140202202000000140202088000000) (.leaf 0x900204081000000900202084000000810204101000000810202104000000801208084000000801204102000000808204401000000808202404000000))) (.node 24 (.node 23 (.leaf 0x120801804000000120084801000000120082804000000120401808000000021088804000000021044808000000020844810000000020488810000000) (.leaf 0x21090104000000021050204000000020850404000000020450408000000020490110000000020450210000000420044801000000420042804000000)) (.node 25 (.leaf 0x21108204000000021104108000000020908404000000020508408000000020904110000000020508210000000120810044000000120410048000000) (.leaf 0x22088404000000022044408000000022084110000000022044210000000420104101000000420102104000000120104201000000120102204000000)))))) (.node 39 (.node 32 (.node 29 (.node 27 (.leaf 0x60808050000000060801110000000060082110000000060042210000000422008044000000422001104000000122001204000000122004048000000) (.node 28 (.leaf 0x460008041000000460001101000000160001201000000160002048000000061008048000000061001108000000060088401000000060042408000000) (.leaf 0x920004041000000920002044000000821008044000000821001104000000820044401000000820042404000000820408050000000820401110000000))) (.node 30 (.leaf 0x180801802000000180082802000000090088801000000090042808000000081088802000000089001808000000088801810000000088082810000000) (.node 31 (.leaf 0x89010048000000081050088000000080850402000000088090401000000088810050000000080850090000000488001801000000480042802000000) (.leaf 0x488010041000000480050081000000180810042000000180090081000000090090101000000090050201000000081090102000000081050202000000)))) (.node 35 (.node 33 (.leaf 0x90108201000000090102108000000081108202000000081108088000000080908402000000088102408000000080908090000000088102210000000) (.node 34 (.leaf 0x8208840200000008a00140800000008208809000000008a001210000000480108081000000480102102000000180102202000000180102088000000) (.leaf 0x888002050000000880042090000000482008042000000482001102000000182001202000000182001088000000092008048000000092001108000000))) (.node 37 (.node 36 (.leaf 0x980001081000000980002042000000890008041000000890001101000000881008042000000881001102000000888001401000000880042402000000) (.leaf 0x210801804000000210084801000000210082804000000210401808000000201084802000000205001808000000204801810000000204082810000000)) (.node 38 (.leaf 0x201090084000000205010048000000204090401000000200490402000000204810050000000200490090000000604001801000000600401802000000) (.leaf 0x200904402000000204102408000000200904090000000204102210000000604010041000000600410042000000210810044000000210410048000000))))) (.node 46 (.node 42 (.node 40 (.leaf 0x202084090000000206001210000000600104081000000600102084000000210104201000000210102204000000201104202000000201104088000000) (.node 41 (.leaf 0x240801090000000240082090000000602004042000000602001084000000212001204000000212004048000000202084402000000206001408000000) (.leaf 0x640001081000000640002042000000250001201000000250002048000000241001202000000241001088000000240801402000000240082402000000))) (.node 44 (.node 43 (.leaf 0xa10004041000000a10002044000000a01004042000000a01001084000000a04001401000000a00401402000000a04002050000000a00401090000000) (.leaf 0x8004041404000008002044404000000044081404000000042084404000004008041404000000408042404000004001101404000000401102404000)) (.node 45 (.leaf 0x440090400200000044090400800004008050400800000408090400400004002110400400004001110400800004002050401000000401090401000) (.leaf 0x440402400200000044402400800004008401400400000408402400400004001401401000000401402401000008400050400200008004050400800)))) (.node 49 (.node 47 (.leaf 0x1004042401000001001084401000008401400400100008004401400400008002404400400008001404400800004042400400100004040401400200) (.node 48 (.leaf 0x9004040400100009000044400200001044080400100001040084400200005008040400100001008084400400005001100400100001004102400400) (.leaf 0x10408040400100010008044400800010401100400100010004101400400010002104400400010001104400800010004041401000010002044401000))) (.node 51 (.node 50 (.leaf 0x104002040400100104000041400200100401080400100100400042400200100004081400400100004042400800100002084400400100001084400800) (.leaf 0x8002804044000008001801104000004042800014000000044801084000000042804084000000042802104000004008801044000000408802044000)) (.node 52 (.leaf 0x440810080200000044810080800004008810040800000408810080400004002810041000000401810081000008401800014000008004801044000) (.leaf 0x5001800011000001004802041000001001804081000001001802101000008400810040200008004810040800008002810100400008001810100800))))))) (.node 80 (.node 66 (.node 59 (.node 56 (.node 54 (.leaf 0x5040800010200001044800080100001040804080200001040802100200005008800040100005008800010400001008804080400001008802100400) (.node 55 (.leaf 0x10401800011000010004801041000010002804041000010001801101000009004800040100009004800010400009000804040200009001800100100) (.leaf 0x10440800010200010044800010800010042800100100010040801100200010408800040100010408800010400010008804040800010008801100400))) (.node 57 (.leaf 0x100400802040200100401800080100100004802040800100004801080400100002804080400100001804080800100002802100400100001802100800) (.node 58 (.leaf 0x450002024000000050081104000004010101044000000410102044000104002800040100104002800010400104000801040200104001800010800) (.leaf 0x4010110040800000410110080400000410090041000000410050081000008410040014000008010041104000004050001024000000450080014000)))) (.node 62 (.node 60 (.leaf 0x50404080800000050402100800004010401041000000410402041000008410010020400008010050100800004050010020800000050090100800) (.node 61 (.leaf 0x1010044081000001010042101000008410400040100008410400010400008010404040800008010401100400004050400010800000450400080100) (.leaf 0x5050000020100001050080100100005010100040100005010100010400001010104080400001010102100400005010040011000001010084041000))) (.node 64 (.node 63 (.leaf 0x10410100040100010410100010400010010104040800010010101100400010410040011000010010041101000009010004020400009010040100100) (.leaf 0x100410002020400100410040080100100010084040800100010044080800100010081100400100010042100800010450000020100010050004020800)) (.node 65 (.leaf 0x4102100014000000104101084000000102104084000000102102104000104010001020400104010040010800100410080040100100410080010400) (.leaf 0x4102010021000000102090101000008104001024000008102004024000004108001024000000508080014000000508002024000000108081104000))))) (.node 73 (.node 69 (.node 67 (.leaf 0x102404081000000102402101000008500010020200008104010020800004108010020800000108090100800000500110080200000104110080800) (.node 68 (.leaf 0x8102400100100008100401100200004108400010800000508400080100000108404080800000108402100800004102400011000000104401081000) (.leaf 0x5100100010200001104100080100001100104080200001100102100200001104080011000001104002021000008500400010200008104400010800))) (.node 71 (.node 70 (.leaf 0x10102100100100010100101100200010104001021000010102004021000009104000020100009100004020200005108000020100001108080100100) (.leaf 0x100104080010800100104002020800100102080100100100100081100200010508000020100010108004020800010500100010200010104100010800)) (.node 72 (.leaf 0x6001100014000002004102044000002001104084000002001102104000104102000020100104100001020200100500080010200100500002020200) (.leaf 0xa00404001400000a001004024000002044080014000002044002024000006008040014000002008084044000002008044084000002008042104000)))) (.node 76 (.node 74 (.leaf 0x6008010020400002008090100400006000110040200002004110080400006001010021000002004090041000002004050081000002001090101000) (.node 75 (.leaf 0x600140001100000200440204100000200140408100000200140210100000a00401002040000a000050100200006040010020200002040090100200) (.leaf 0x6040400010200002044400080100002040404080200002040402100200006008400040100006008400010400002008404080400002008402100400))) (.node 78 (.node 77 (.leaf 0x1200010404020001200110010010001200404001100001200100402100000a00440004010000a00440001040000a00040404020000a001400100100) (.leaf 0x102001080100100102000042100200012044000020100012040004020200012008004020400012008040100100012004100040100012004100010400)) (.node 79 (.leaf 0x106001000020100106000040010200102004080040100102004080010400102004002020400102004040080100102000084040200102000044080200) (.leaf 0x48002040014000048001001024000040042080014000040042002024000040008081044000040008041084000040002102044000040001101084000)))))) (.node 93 (.node 86 (.node 83 (.node 81 (.leaf 0x48002010020400048001010020800040008090040800040008050080800040002110080400040001110080800040002090041000040002050081000) (.node 82 (.leaf 0x48000401040200048001400010800040042400080100040040401080200040008402040800040008401080400040002402041000040001401081000) (.leaf 0x41008002020400041008040080100041000102040200041001100080100041001080011000041001002021000048002400040100048002400010400))) (.node 84 (.leaf 0x50002040011000050001001021000049001000020100049000040010200041040080010200041040002020200041008080040100041008080010400) (.node 85 (.leaf 0x50042000020100050040001020200050008001020400050008040010800050002100040100050002100010400050000101040200050001100010800) (.leaf 0x140002080040100140002080010400140000081040200140001080010800140002002020400140001002020800140002040080100140000041080200)))) (.node 89 (.node 87 (.leaf 0x100804080408000104002200408000010804100408000010408200408000009004200408000005008200408000008804400408000004808400408000) (.node 88 (.leaf 0x100804800088000104002800208000010808800108000010408800208000009004800208000005008800208000400408080408000404002100408000) (.leaf 0x10810100108000010410100208000009010200108000005010100208000008810400108000008410400208000408002800108000400408800088000))) (.node 91 (.node 90 (.leaf 0xa004400208000006008400208000408410000028000400410100088000104810000028000100810080108000100410200088000100410080208000) (.leaf 0x40a004000028000406008000028000402008080108000402004100088000102004200088000102004080208000012008200108000012004100208000)) (.node 92 (.leaf 0x140002200088000140002080208000050808000028000050002100208000041008200088000041008080208000040808400088000048002400208000) (.leaf 0x809004000028000805008000028000801008080108000801004100088000808002400108000800408400088000448002000028000440002100088000))))) (.node 100 (.node 96 (.node 94 (.leaf 0x9004800802000005008800802000008804800804000004808800804000904002000028000900002080108000810408000028000810002100108000) (.node 95 (.leaf 0x408400800800200408004800800800404008800800800404002800801000104800800800200104002800802000010804800801000010408800802000) (.leaf 0x10410200801000010410100802000005010200801000005010100802000004810400801000008410400802000004810100804000008410200804000))) (.node 98 (.node 97 (.leaf 0xa00440080200000600840080200000a004200804000006008200804000404010100800800400410080801000104010200800800100410080802000) (.leaf 0x40808080804000048002200804000406000100800200402004080801000106000200800200102004080802000012004200801000012004100802000)) (.node 99 (.leaf 0x50800100800200050008200800800050002200801000050002100802000049000200800200041008080802000048800400800200048002400802000) (.leaf 0x804008400800800804002400801000800408080804000804002100804000440008080800800440002080801000140800080800200140002080802000)))) (.node 103 (.node 101 (.leaf 0x900400080800200900004080800800810400100800200810004100800800805000100800200801004080801000808400400800200808004400800800) (.node 102 (.leaf 0x10420200401000010420100402000005020200401000005020100402000004820400401000008420400402000004820100404000008420200404000) (.leaf 0x5020800201000009020800102000008820800104000008420800204000404020100400800400420080401000104020200400800100420080402000))) (.node 105 (.node 104 (.leaf 0xa020200104000006020100204000408020800100800400420800081000104020800200800100420800082000010820800101000010420800201000) (.leaf 0x40602000002100040202008010100010602000002200010202008010200001202020010100001202010010200000602040020100000a020400102000)) (.node 106 (.leaf 0x41020200081000041020080201000049020000022000041020100082000040820400081000048020400200800048820000024000040820100084000) (.leaf 0x808420000024000800420100084000448020000020800440020100080800140020200080800140020080200800050820000021000050020100200800)))))))) (.node 161 (.node 134 (.node 120 (.node 113 (.node 110 (.node 108 (.leaf 0x904020000020800900020080100800810020100100800810420000021000805020000021000801020080101000808020400100800800420400081000) (.node 109 (.leaf 0x120400200400200120004200400800021004200401000021004100402000020804400401000020408400402000020804100404000020408200404000) (.leaf 0x120004800200800120002800102000021004800201000021008800102000020808800104000020408800204000420400100400200420004100400800))) (.node 111 (.leaf 0x20810400101000020410400201000020810100104000020410100204000420008800100800420002800101000120800800100200120400800200200) (.node 112 (.leaf 0x22008200104000022004100204000420010100100800420410000021000120010200100800120410000022000021010200101000021010100102000) (.leaf 0x60808000024000060002100204000422000100100200422004000021000122000200100200122004000022000022004400201000022008400102000)))) (.node 116 (.node 114 (.leaf 0x460008000020800460002000021000160800000020200160002000022000061000100200200061008000022000060008400200800060002400201000) (.node 115 (.leaf 0x920400000020200920004000020800821000100100200821004000021000820008400100800820002400101000820408000024000820002100104000) (.leaf 0x90002200401000090002100402000089000200400200081008080402000088800400400200088002400402000080808080404000088002200404000))) (.node 118 (.node 117 (.leaf 0x80808800084000088002800204000480008080400800480002080401000180800080400200180002080402000090800100400200090008200400800) (.leaf 0x480008800080800480002800081000180800800080200180002800082000090008800200800090002800201000089000800200200081008800082000)) (.node 119 (.leaf 0x81010200081000081010080201000089010000022000081010100082000080810400081000088010400200800088810000024000080810100084000) (.leaf 0x82008200084000082008080204000488010000020800480010100080800180010200080800180010080200800090810000021000090010100200800))))) (.node 127 (.node 123 (.node 121 (.leaf 0x48a00000002020048200010008020018200020008020018200008020020009200010020020009200800002200008a000400200200082008400082000) (.node 122 (.leaf 0x890008000020800890002000021000889000000020200881000100080200880008400080800880002400081000888002000024000880002100084000) (.leaf 0x210400200400200210004200400800205000200400200201004080402000204800400400200204002400402000200804080404000204002200404000))) (.node 125 (.node 124 (.leaf 0x210004800200800210002800102000205000800200200201004800082000200804800084000204002800204000600400080400200600004080400800) (.leaf 0x204810000024000200810080104000200410200084000200410080204000600400800080200600004800080800210800800100200210400800200200)) (.node 126 (.leaf 0x604010000020800600010080100800210010200100800210410000022000205010000022000201010080102000204010400200800200410400082000) (.leaf 0x606000000020200602000080100200212000200100200212004000022000206000400200200202004400082000202004200084000202004080204000)))) (.node 130 (.node 128 (.leaf 0x250800000020200250002000022000241000200080200241000080200200240800400080200240002400082000240002200084000240002080204000) (.node 129 (.leaf 0xa10400000020200a10004000020800a05000000020200a01000080100200a00400400080200a00004400080800a04002000024000a00002080104000) (.leaf 0x401080012020000401002022020000004081042020000004041082020000002084042020000002044082020000001081102020000002042102020))) (.node 132 (.node 131 (.leaf 0x1104082004000002104042008000001102102004000001101102008000002102042010000001101082010004002040012020004001001022020) (.leaf 0x8081042010000008041082010004000101042002004001100012004000400102042002000401100012008000004102042004000004101042008)) (.node 133 (.leaf 0x4008001042001004008040012004000408002042001000408040012008000008084042004000008044082004000008042102004000008041102008) (.leaf 0x44001082001000044001022008000042004082001000042004022008000040081102002000042002102001000042080012010000042002022010)))))) (.node 147 (.node 140 (.node 137 (.node 135 (.leaf 0x8002040012010008001001022010004042000012001004040001022002000440080012002000440002022002000044080012004000044002022004) (.node 136 (.leaf 0x8401000012001008400040012002008004001042001008004040012004008002004042001008001004022004008001001102001008000041102002) (.leaf 0x4002040200120004000041200220000401080200120000400042200220000004081200420000004042200820000002084200420000001084200820))) (.node 138 (.leaf 0x401002201001000400042201002000004042201004000004041201008000001084201004000002044201008000001081201010000002042201010) (.node 139 (.leaf 0x4102200404000004101200408000002104200408000001104200808000002102200410000001102200810004001001201001004000041201002) (.leaf 0x8084200404000008044200808000008081200410000008042200810004000101200402004001100200104000400102200402000401100200108)))) (.node 143 (.node 141 (.leaf 0x40084200802000040084200204000042080200110000040081200210004008001200401004008040200104000408002200401000408040200108) (.node 142 (.leaf 0x8002040200110008000041200210004042000200101004040001200201000440080200102000440002200201000044080200104000044002200801) (.leaf 0x8401000200101008400040200102008004001200401008004040200104008002004200401008001004200801008000044200802008000044200204))) (.node 145 (.node 144 (.leaf 0x4002008020420004001008020820000400088040220000400048080220000004088040820000004048080820000002088100420000001088100820) (.leaf 0x400048081002000401008021008000004088041004000004048081004000001088101004000002048101008000002088041010000002048081010)) (.node 146 (.leaf 0x2108100408000001108100808000002108080410000001108080810004002008041001004001008021004000400088041002000401008081001) (.leaf 0x8088040810000008048080810004000108040802004000108040204000400108080402000400108040208000004108080404000004108040808))))) (.node 154 (.node 150 (.node 148 (.leaf 0x40088100802000040088100204004008008040801004008008020404000408008080401000408008020408000008088100404000008048100808) (.node 149 (.leaf 0x8002008020410008001008020810004040008020802004040008020204000440008080201000440008020208000044008080801000044008020808) (.leaf 0x8400008040201008400008020402008004008040801008004008020404008002008100401008001008100801008000048100802008000048100204))) (.node 152 (.node 151 (.leaf 0x400202040220000401200080120000004202040820000004201080420000002204080420000001204080820000002202100420000001202100820) (.leaf 0x1202101004000001201101008000002202041010000001201081010004002200040120004002200010420004000201040220004001200010820)) (.node 153 (.leaf 0x4000201041002004001200011004000400202041002000401200011008000004202041004000004201041008000001204081004000002204041008) (.leaf 0x408200040108000408200010408000008204080404000008204040808000008202100404000008201100408000008202040810000008201080410)))) (.node 157 (.node 155 (.leaf 0x40202100802000040202100204000042200100108000040201100208000042200080110000040201080210004008200040104004008200010404) (.node 156 (.leaf 0x4040200010802004040200010204000440200080102000440200010208000044200080104000044200010808000040204080802000040204080204) (.leaf 0x8000204040802008000204040204008000201100402008001200100104008002200040110008002200010410008000201040210008001200010810))) (.node 159 (.node 158 (.leaf 0x84080010820000084002020820000082080100120000080081100220008400200040102008400200010402008004200040104008004200010404) (.leaf 0x80081101002000082002101001000082080011010000082002021010004082000020120004080001020220000480080010220000480002020220)) (.node 160 (.leaf 0x480080011002000480002021002000084080011004000084002021004000084001081001000084001021008000082004081001000082004021008) (.leaf 0x80102100802000080102100204000082100100108000080101100208000082100080110000080101080210004082000011001004080001021002))))))) (.node 188 (.node 174 (.node 167 (.node 164 (.node 162 (.leaf 0x4080100010802004080100010204000480100080102000480100010208000084100080104000084100010808000080104080802000080104080204) (.node 163 (.leaf 0x488000080101000488000020108000088004080801000088004020808000088080100104000088002100801000088080010810000088002020810) (.leaf 0x8080004020802008080004020204008082000100101008080001100201008082000020110008080001020210004088000010801004088000020104))) (.node 165 (.leaf 0x800084040220000800044080220000801080100120000800042100220008480000010201008480000020102008084000010801008084000020104) (.node 166 (.leaf 0x801080011010000801002021010004801000020120004800040010220000804080040120000804080010420000804002020420000804040080120) (.leaf 0x804002041001000804040011008000800084041002000801004081001000800044081002000801004021008000801002101001000800042101002)))) (.node 170 (.node 168 (.leaf 0x800104080402000800104040208000800102100402000801100100108000800102040210000801100080110004801000011001004800040011002) (.node 169 (.leaf 0x808080040110000808080010410000808002020410000808040080110004800100040102004800100010402000804100040108000804100010408) (.leaf 0x840080010210000840002020210004808000040101004808000010401000808004080401000808004020408000808002100401000808040100108))) (.node 172 (.node 171 (.leaf 0x4840000010201004840000020102000844000080101000844000020108000840004080201000840004020208000840080100102000840002100201) (.leaf 0x8804000040101008804000010401008800004040201008800004020402008801000100101008800040100102008801000020110008800040010210)) (.node 173 (.leaf 0x88004084080000088002104080008004008044080008001008104080000044008084080004008008044080008001004204080000044002204080) (.leaf 0x4008010200480004001010201080008004010042080008001010102080000044010082080004008010042080008084000014080004088000014080))))) (.node 181 (.node 177 (.node 175 (.leaf 0x10008004200480010001004201080010044000012080010008004042080008080010100280000084010081080008004010200480004040010200280) (.node 176 (.leaf 0x10088000100180010084000011080010040008100280010008008100480010004008041080010001008101080010044000200180010040004200280) (.leaf 0x104000008040280100004008080480104001000200180100004002200480104001000012080100004002042080100001004082080100001002102080))) (.node 179 (.node 178 (.leaf 0x404001000011080400004002041080400001004081080400001002101080104080000010280100084000080180100080004080280100080002100280) (.leaf 0x404040000010280400044000080180400040004080280400040002100280404008000040180404008000010480400008004080480400008002100480)) (.node 180 (.leaf 0x4008008400440004001008401040008001004402040000044002402040408004000040180408004000010480408000004040280408001000100180) (.leaf 0x44008404008004001008404020008084000400140008080004400240004088000400140000084002401040008004008400440004040008400240)))) (.node 184 (.node 182 (.leaf 0x44010402008004001010402020008080004404002000088004404008000088002404010000084002404020008001008404010004040008404002) (.node 183 (.leaf 0x10040004402002010001004402020008080010400210004080010401002000084010401008004080010400220008001010402010004040010402002) (.leaf 0x10088000400110010080004401002010084000400120010080004400220010040008400210010008008400410010001008401010010004008400420))) (.node 186 (.node 185 (.leaf 0x104080000400102100084000400108100080004400208100080002400210104000008400402100004008400408100001004402008100001002402010) (.leaf 0x400040004400208400040002400210400008004400408400008002400410400001004401008400001002401010404001000400120400004002400420)) (.node 187 (.leaf 0x8010004042040004050000012040000050004082040000050002102040408000004400402408001000400110404040000400102400044000400108) (.leaf 0x8090000100140004090000011040000090004081040000090002101040008010008100440004010008041040008010004200440004050000200140)))))) (.node 201 (.node 194 (.node 191 (.node 189 (.leaf 0x90004084020000090002104020008010008044010000050008104008000050008084010004010008044020000050004204008000050002204010) (.node 190 (.leaf 0x8010010200410004010010200420008010010042010000050010102008000050010082010004010010042020008090000014010004090000014020) (.leaf 0x10010008041010010010008100420010050000200110010010004200420010050000012010010010004042020000090010101008000090010081010))) (.node 192 (.leaf 0x100010008100408100010008080410100010004200408100010002200410100010004042008100010002042010010090000011010010090000100120) (.node 193 (.leaf 0x400010004041008400010002041010404010000040120404010000010420400010004080420400010002100420100090000100108100090000080110) (.leaf 0x8104000012040004108000012040000108004082040000108002102040408010000040110408010000010410400050000100108400050000080110)))) (.node 197 (.node 195 (.leaf 0x108002204010000104002204020008100008100240000104008081040008104000200140008100004200240004108000200140000104002201040) (.node 196 (.leaf 0x108010082010000104010082020008100008104002000108008104008000108008084010000104008084020008100004204002000108004204008) (.leaf 0x10108000012010010104000012020008100010200210004100010201002000104010201008004100010200220008100010102002000108010102008))) (.node 199 (.node 198 (.leaf 0x100100004082002100100002102002010100008101002010100008100220010108000200110010100004201002010104000200120010100004200220) (.leaf 0x100100008100208100100008080210104100000200102100104000200108100100004200208100100002200210104100000012002100104000012008)) (.node 200 (.leaf 0x404100000011002400104000011008400100004081002400100002101002404100000010220400104000080120400100004080220400100002100220) (.leaf 0x40008002200440040001002201040048001000012040040008002042040408100000100102408100000010210400108000100108400108000080110))))) (.node 208 (.node 204 (.node 202 (.leaf 0x48080000010240040088000080140048000008040240040040008080240040008008080440040001008081040048001000200140040040002200240) (.node 203 (.leaf 0x48080000014002040088000014008048000008044002040040008084002040008008044008040001008084020040040002204002040001002204020) (.leaf 0x48000010200402040040010200208040008010200408040001010201008048000010042002040040010082002040008010042008040001010082020))) (.node 206 (.node 205 (.leaf 0x50000008041002050000008040220050040000200102050001000200120050040000012002050001000012020040080010081002040080010080220) (.leaf 0x140000008080402140000008040208140000002200402140001000200108140000002042002140001000012008050080000011002050080000010220)) (.node 207 (.leaf 0x440008000040108440008000010408440000002041002440001000011008440000002040220440001000080120140080000080102140080000010208) (.leaf 0x804001000011040800004002041040800001004081040800001002101040448000000040102448000000010402440040000080102440040000010208)))) (.node 211 (.node 209 (.leaf 0x804040000010240800044000080140800040004080240800040002100240804008000040140804008000010440800008004080440800008002100440) (.node 210 (.leaf 0x804001000014020800004002044020800001004084020800001002104020808004000040140808004000010440808000004040240808001000100140) (.leaf 0x808000004044002808001000014010804040000014002800044000014008800040004084002800040002104002800008004044008800008002044010))) (.node 213 (.node 212 (.leaf 0x800008010100408800008010080410804000010041002800004010041008800001010101008800001010081010804000010040220800004010080420) (.leaf 0x810004000040120810004000010420810000004040220810001000100120808000010100402808000010040210800040010100208800040010080210)) (.node 214 (.leaf 0x900000002040210900001000080110810040000100102810040000010210810008000040110810008000010410810000004041002810001000011010) (.leaf 0x904000000040102904000000010402900004000040108900004000010408900000004080402900000004040208900000002100402900001000100108)))))))))

set_option maxRecDepth 20000 in
def edgeTable : Lookup := (.node 19 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf 0x0) (.leaf 0x0)) (.node 3 (.leaf 0x0) (.leaf 0x1184d0b12084008044291250440000000000000000c8291290090000011504580240000441c2120a014000e25024000f480068a20000a08800e2988900030000000000000000000e2a08a40000000aa220280002800000000000000000000000000000000000000000000000000000000000000000000000000fffffffffffffff0300c0c0300c0300c03003000c030300f0300c0c0300300300c00300303000c03000c03000000000000000001405014140140007415400c014001d014051101400015417015405c0000c044055014000000000000000500018140280a00000000000000074000e85a2e1a85900008808a8420300003b822a028000000000000000244b22028411084d3886282321c8000000000000000446286012001804423200048014000000000000000088a00028082240b2000880dc122088e2000a000240a28880002400a0088dc1000900280000000000000000))) (.node 6 (.node 5 (.leaf 0x2822a8ba000028228a8880b4000908e8ba89400033500000000000000220220818540005a00026aba00048000000000000008800017a480246a6000076800088a000000000000000c00032e2a8000a4251401450002141c0074500015144113005000120511745000000440000000000000008074c40050000501dae9940000396961d500000028611644600000090000000000000000000000000000005189185000000a0000000000003ff000000000003ff000000000003ff000000000000fff000000000003ff0000000000000ff0c030300c030000300c00c0030000c0300c030300003c00c03000c0000c00300c00300000c00c0300c03000028084e100000000812a1050000002012138444000002a128c6210000005001118840000005014170140000000000000000141104400a00001144642c4888003414404430d2000000a0022c34800110180484802800) (.leaf 0x28000a208820000000a202c820000c0002a208200000a00088a0a300202c00222822000b080028c8228050000000515100000000000000003000000151c11006000001345110470000004d1551708000008437184000000000000000000000000000000000000000000fffffffffffffff000000000000000000000000000000000003ff0000000000fff0000000000000ffc000000000000000000000000000fffc0000000000ffc00000001428000b4690000a0001a1069000220a0008869000000000000000001a10aa0000c90004a42b000691700000000000000014000004565100c0110500077060000000000000001d456515000336045041040011648000000000000000000000000000000000000000000000000000000000ffffffffffffff000000000000000000000000ffc0000000000fffc000000000003fc00000000003fff0000000000000000000000000003ff00)) (.node 7 (.leaf 0xffffffffffffff000000000000000000000000000000000000000000000000000000000000ffc0000000000000000000000000fff000000000000fff00000000000fffc00000000003ffc0000000000000000000000000000000000000ffffffffffffff00000000000000000000000000000000000000000000c0300c0c0300f0300300c00c0030000000000000003000c00c00c0030000c00300300303003c00c0c0300c0000000000000002805005809a070000000000000003000502802dc0a22809a0800b40908a01e0202a01820a000140586a07000000000000000000000000000000900001641224588000047904a86834000d15148e7100003fc0000000003ff00000000000000ff0000000000000ffc000000000003ff000000000003ff0000000300c000300c00c0c00003003c00c300c0000c0c00c0c003000003000c3003c00000c00c0f0030000300c03) (.node 8 (.leaf 0xff000000000000ffc00000000000ff000000000000fff000000000000ff000000000000ffc00000000000000c030300c030000300c00c0030000c00c0c000300000c00c03000f0000c00300c00300003003c0c0300c0ffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000c00c03003000c0c03003030300f0c00300300f000c0c03000c03c00c0c00c0030300c030) (.leaf 0x141100004874000000000000000000c500012c1d00043520000ac780012542000005600005440004416400482401810488001809040708d000000000000000000988521c140840041a0504070210000a18051830180021421c20900000435082b0072000071244b24022000000000000000002809002b00880005000500182800082882252200000a4a6494800000008288b40900000024281e02100000840280948000000a0a0aa2200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))))) (.node 14 (.node 11 (.node 10 (.leaf 0x3000050351d05050000622012022000006019830060500008818050005c00006220d41800000000000000a00a02228a220a22028a08402404400000000000000220a0212830a03aa00a6a084c2983000000000000000ce0648400c050883810000a88500d4c3e040038ba08830280000a02800000000000000000000000000000501599094000a0500124848000a88283008b220004850048121200090500c484848002200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ff000000000000fff000000000003ff000000000000ff0000000000003ff000000000000ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c00c03030000003000f00f000000300c03c0c000000c03c03030000000f000f00c00000300c00c0300) (.leaf 0x31892222000462004142008801020312209888000000c022222200088034d544c0000500c0004a40a001208400011500011514000140440021084000440500090a300001150000514000180d400052162400095004d0000000000000004106000410029480814000420066210115000000152481200112800aa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c441111541011030c110c44441100c1544444504400331111113004400000000000000)) (.node 12 (.leaf 0xfffffffffffffff0000000000000000000003ff000000000ffff0000000000003ffc000000000003ff00000000000000000000000003ffc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0030000c030003c000003000f003c0f0000300f000f03c0000c03000000000000000003c0300000c03f0000b080022283280000001452402b001080004450328004100012140000000000000002b00344000d130031090400011844544200004028b0000000000000004540d02c0041c0000000000000000d4c3c8800322cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ff00000000000fff0000000000003fc000000000000ff000000000000ffc000000000003ff00) (.node 13 (.leaf 0xc00c00300030003000f003003000000000000000000300c003c303c000f000f000c03c00003003c0c030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffff00000000000000000000000000000003003c00c300c000c000f00c00f000c03003c0c0f0000000000000000000f000f00300300c00c0030300c000000000000003c232c404816b040c1284d011120400000000000000030404c404441100c12a1904140a0ca8c8003228bb2000000000000000820900082c0d0b00000000000000c0a2020000208ac8209000a000a501401601c41444180805100b00940b0000000000000000000000000000145009100b10640212402640c0503) (.leaf 0x3003c0c0c000000f000c00c000000c03c03030000003003c0c0c0000000f000f03c00000c03c0300c000000000000000c000008c82a8088c0002802208888c0000b20222822f0000008c802822c0000a03282e0a00000000000000fffffffffffffff00000000000000000000000000000000000000000000000000000000000003ffc0000000000000000000000000ffc000000000003ffc000000000000ffff000000000ffc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030a000210220603c2c80031187990c08c800008960130a000209691050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffff0000000000000000000000000000000000000000000)))) (.node 16 (.node 15 (.leaf 0xff000000000000ffc000000000000ff000000000000ffc00000000000fff000000000000ff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffc000000000003ff000000000000ff0000000000003fc000000000000fff00000000000ff0000000000) (.leaf 0x0)) (.node 17 (.leaf 0xfffffffffffffff03030300f00c030300c00300c0030300c0c0300c0300c00300c03003003000c030030030000000000000000044141d00501400050030110454001405050050140000303504415400011505c15405c00000000000000000000000000000440002c844108014411212c420281d02c8ca1384a80444201204a8120000000000000000440000e204814088003d0488210048820028088140e23d0400280a00518840000a0060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000b8b8e8000b22a830fa0000220a28a028280003028000000000000000aa028a28000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (.node 18 (.leaf 0xfffffffffffffff000000000000000000000000003ff00000000003fff000000000003ff00000000000fff0000000000000000000000000003ff0011090211a400001a45440e4000000b424051a400000544024990000000000000000000005505c1545c0011006064424000000000000000002d0029abae58006600005da26000000000000000000528002204aa20000c2e06012c18001d619899f1800000000000000000015899001400000000000000000000158a181201800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e2c09098800000e2842222000000d2f4941400000098a222a0000000000000000000000ac220c02800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (.leaf 0x1111414450031200104440003c120000000000000044044050000500c42f0494050000042044240500028000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))))) (.node 28 (.node 23 (.node 21 (.node 20 (.leaf 0x8805c00089a1120a868180081c050000000000000000a8448050002152642e624001361544001700049952000000000000005000164000a17a0000000000000055000017a00042a090009d800088aa03470000004405470000005454c50551400004400000000000000000005531400000140d0bd1000002414000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffc0000000000ffc000000000000ffc00000000003ff000000000000000fff00000000003fc000c0c0c0300000c0c03000c00000c0c030300c0000c03000c0300000c03c00300c00c00000c0300c00c0003002222202000e1002088800001a10000088a0000e1000880088002a10000684a32a1000000880a0220005c00000000000000114811110002402108606130031220511104400852381090210852000111101110d00120) (.leaf 0x880000c2080a0000020b208a0a00208000a2080a00020b0002200a00028280000a0a300022000c88a0a388000011390280000000000000008200001451068511c000001515c5a220000005c581020400003345121000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffff000000000000000000000000000000000000fff0000000003fff0000000000003ff0000000000000000000000000000fff00000000003ffc0000)) (.node 22 (.leaf 0xffffffffffffff000000000000000000000000000000000000000000000000000000000000ff00000000000000000000000000ffc000000000003fff00000000000fffc00000000003ff00000000000000000000000000000000000000ffffffffffffff00000000000000000000000000000000000000000000c0c0303003c0c0c00c03000c03c0000000000000003003000c0300c03000f00300c0030300300300c03030000000000000002282202602402d0000000000000002a02601a0700503000b40a005c0a08a0180a02e080a2200888a80242d0000000000000000000000000000880000a2488a3a08d000285a3a3c58400040481045450000ff0000000000ffc00000000000003fc0000000000000ffc000000000003ff00000000000ffc00000003030000c003030300000f0030030300c00030030300c00f00000c0300c000c00003000c0f00c0000300c0c) (.leaf 0x1405035044000000501430050000001430d415400000050505c044000000014170140000005011055000000000000000000141084940300003504943284a800011105212043800110244848028001403004e12a0001442000ca12900048000a281c0800ca0a28000a00000422080280280004208800a014000411c0800280000e8a93a000292000a32a400020a400000000000000000ac0a2800090000ac350a00028000aa20a4a0000000ff000000000000ff000000000000ff000000000000ffc00000000000fff000000000000ffc0000000000000000c0c00c030000c03000c0300000c030300c0300003000c0300c00000c00300c00f0000300f030030300ffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300c00300c00c0300c0c03c0c0c00c00300c0300c003000c03000c0c00c00c0f00c0c0))) (.node 25 (.node 24 (.leaf 0x2823786800000c0818680120001252663a1e150004d060180501400050000000000000050001e65a0000600000000000000052400016d00041a58801e0aa0008228000aaae8000a00000000000000218dc000480010d85400515400071042515400000280811c401400003001545000000050000000000000008e72219a1400292529c8282800082a18282a8000084000000000000000d0aa25050000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ff000000000000ff000000000000fff000000000000ff000000000000ff000000000003ff0300c0f00c00c0000c03000c0030000f000c0300300000c000c030030000c030300c030000c00300c00c00) (.leaf 0x2808108418014000a02b0c0a0000002b0c2102105c000a084a319114000000000000000000a004408414a000208a48a008800000000000000aca000292ad2aa0a00020b50a222800000000000000280000a8ab48281254442000046205cd510001551d400000000000000050f514000440c00000000000000004555100000140418090450340940a0202d402a0228505d401405005000000000000000000000000000000d0aa02501402800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffff0000000003ffc00000000003fff00000000000fff000000000000fff000000000003ff0000000000000000)) (.node 26 (.leaf 0xffffffffffffff0000000000000000000000000000300c0c00c03c00c0c0300300030000c003003003000c000000000000000f00c0c0300c030c00300c00c00c0001422028834210000500c05051400000c00a28a0a300000000000000000502128ce114000505220a28410000000000000000140000150c84102200140584521000000000000000205018284312482350c881e1153200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffff000000000000000c03030030030030300c00f000c0303000f00c00c0030f00c300c00c030000000000000003000c03003003) (.node 27 (.leaf 0xfffffffffffffff0000000000000000000000000000000000000000000000000ffc0000000000fffc000000000000000000000000003ff000000000000ffc0000000000003ffc00000280c000208ca0000a0000a0a2b0000000000000000000c280022a2b000af0a0000a2b000a0a088000aa050001100149115000000000000000000000000000000300014000951453c005500175d4518000574002150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (.leaf 0xffffffffffffff00000000000000000000000000000000000000000000000000000000000ffc000000000000000000000000000fffc00000000003fc000000000003ff000000000003fff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ff00000000003ff0000000000000003ff00000000003fc000000000000ff0000000000000ffc00000c030000300c00f0300000c003c00c3000c00000c00303003000300300c30030000c0300c3003c00003003000000000000000002800002a0378200c002800012c0a08800000a8078208a0200028058208a03700004a0d0a0000001616e020000000000000001100000052d1450440000055484184000005168a218640000014b5c2))))) (.node 33 (.node 30 (.node 29 (.leaf 0xff0000000000000ffc00000000000fff000000000000ffc00000000000ffc00000000000ffc0000000000000c0300c030030000300c003000c0000c00300c00f00003030300c00c000300c0c0300c0003000c03003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000c00c03000c0030c003000c03000c0c00c0c0c03c030c00c030300c030c00c00300c00c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (.leaf 0x0)) (.node 31 (.leaf 0xfffffffffffffff00000000000ffff00000000000fff000000000003ff00000000000fff000000000003ff0000000000000000000f00300f000000c0155010500000f0013444440003c015445c40000030031444440000000000000000000dd05444100000000000000000005004408a088800d4156a9aa29000454118e220a0000000000000000003500029812000001d15400724800024099000911000282a80210120001a86600089080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ca220820ac00000e22aaaa8cb20008b022e4122200000000000000000a008840912100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (.node 32 (.leaf 0xfff0000000000000ff0000000000003fc00000000003ff0000000000003fc000000000000003ff0000000000000000000c0c0f0000300003c0c3c000f0000c0c3c0000f0000300c3c0003000000f00303c000003003c000000f030028210000440f0002418001100c00283000074000c00421800044000f0004c444000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005a0448c10004070440a000a0000880000000000000041cf050c0000a08310c050000028407005010828000049027020002b0010941414000b1040bcc112400240000000000000000c0301824001102b00b8021090000a16890000009480a8610300000420b04300a00000a0b2301200000810702c0a00000280948042082000000) (.leaf 0xffffffffffffff0000000000000000000000000000000003030f00303c0003c0f3c03cf00003030c00303000000000000000000003003c3c00303201a88041111100000000000000a118070033020120681421050981000000000000001111101b4081050084001450820622206800305145c0126408000cc1021094001088820200000000000000062264200040888a48aa432834a0848a848c00a28201000000000000008e00c84242404800000000000000a0840840810242400000000000000000000000000000000000000000000000000000000000000000000000000000000000000501540007084848551070c00c08024c80300c00000c4100208030040400000000000000484880840200300)))) (.node 35 (.node 34 (.leaf 0xfff00000000000003ff0000000000003fc00000000003fc0000000000003fc00000000000000ffc00000000000000000000c0c0003c3c0000c030003c300000c0c0003c0c00000c0f0003c3c00000c03c00003c0c0220008a2222200000000000000022088500030420882814008222a8a82250c030102222220201d000820280000005501150282800000301d01104400000c11044140000411010551100000c04101151150000004100000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (.leaf 0xc00c003000f00c00000224848930000088199827000000000000000300084001808800f0000909085c43000c011104c40400000000000000044110248445980000000000000010144210884a61c4044544a262a29000000000000000000000000000000000000000000000000000000000000000000000000000000000000000141100c40b100b01414141105066000000000000000000000000000040e03024242406100b02b0440501200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.node 36 (.leaf 0xffffffffffffff0000000000000000000000000000000000000000000000000000000000003030300c0c0000000000000000003030303c0f00000f0f03c3c3c00000f00c00c03c0003003003c00f0030000284412110000000000000003000028181b0173c0000881818110f0000023210809000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffff00000000000000000000000000000) (.node 37 (.leaf 0xffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ff000000000000003fc0000000000003fc00000000003fc000000000000ffc0000000000000fff0000000000c00c00f000c00000088a0a22c00000022222c8c000000a2208a8c0000002222322f000000000a3232c000002220808c80000000000000008822001400024030000045044542028800154149c08c88a80001c5040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (.leaf 0xfffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffc00000000000fff00000000000ffc00000000000fff00000000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffc000000000000003fc000000000000ffc00000000003fc000000000000ff0000000000000fff00000000)))))))

def setBitPositions : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, word =>
    if word = 0 then []
    else word.log2 :: setBitPositions fuel (word ^^^ 2^word.log2)

lemma setBitPositions_sound (fuel word position : Nat) (found : position ∈ setBitPositions fuel word) :
    word.testBit position = true := by
  induction fuel generalizing word with
  | zero => simp [setBitPositions] at found
  | succ fuel ih =>
    by_cases empty : word = 0
    · simp [setBitPositions, empty] at found
    simp only [setBitPositions, if_neg empty, List.mem_cons] at found
    rcases found with equal | rest
    · exact equal.symm ▸ Nat.testBit_log2 empty
    · have bit := ih (word ^^^ 2^word.log2) rest
      by_cases equal : position = word.log2
      · exact equal.symm ▸ Nat.testBit_log2 empty
      · simpa only [Nat.testBit_xor, Nat.testBit_two_pow, Ne.symm equal, decide_false, Bool.xor_false] using bit


def packedLineSupport : Lookup := (.node 30 (.node 15 (.node 7 (.node 3 (.node 1 (.leaf 0xe8a93a000292000a32a400020a400000000000000000ac0a2800090000ac350a00028000aa20a4a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (.node 2 (.leaf 0xca220820ac00000e22aaaa8cb20008b022e4122200000000000000000a00884091210000000000000000001442000ca12900048000a281c0800ca0a28000a00000422080280280004208800a014000411c0800280000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (.leaf 0x141084940300003504943284a800011105212043800110244848028001403004e12a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))) (.node 5 (.node 4 (.leaf 0x3500029812000001d15400724800024099000911000282a80210120001a866000890800000000000000000001405035044000000501430050000001430d415400000050505c044000000014170140000005011055000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (.leaf 0xdd05444100000000000000000005004408a088800d4156a9aa29000454118e220a0000000000000000000300c0f00c00c0000c03000c0030000f000c0300300000c000c030030000c030300c030000c00300c00c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.node 6 (.leaf 0xf00300f000000c0155010500000f0013444440003c015445c4000003003144444000000000000000000000000000003ff000000000000ff000000000000fff000000000000ff000000000000ff000000000003ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (.leaf 0xffff00000000000fff000000000003ff00000000000fff000000000003ff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))) (.node 11 (.node 9 (.node 8 (.leaf 0xfffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (.leaf 0xa16890000009480a8610300000420b04300a00000a0b2301200000810702c0a000002809480420820000008e72219a1400292529c8282800082a18282a8000084000000000000000d0aa25050000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000082882252200000a4a6494800000008288b40900000024281e02100000840280948000000a0a0aa2200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.node 10 (.leaf 0x49027020002b0010941414000b1040bcc112400240000000000000000c0301824001102b00b8021090000218dc000480010d85400515400071042515400000280811c40140000300154500000005000000000000000b8b8e8000b22a830fa0000220a28a028280003028000000000000000aa028a28000088000000000000000021421c20900000435082b0072000071244b24022000000000000000002809002b00880005000500182800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (.leaf 0x5a0448c10004070440a000a0000880000000000000041cf050c0000a08310c05000002840700501082800050001e65a0000600000000000000052400016d00041a58801e0aa0008228000aaae8000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000482401810488001809040708d000000000000000000988521c140840041a0504070210000a18051830180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))) (.node 13 (.node 12 (.leaf 0x2823786800000c0818680120001252663a1e150004d0601805014000500000000000000440000e204814088003d0488210048820028088140e23d0400280a00518840000a00600000000000000000141100004874000000000000000000c500012c1d00043520000ac78001254200000560000544000441640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (.leaf 0x3003c000000f030028210000440f0002418001100c00283000074000c00421800044000f0004c4440000000000003ffc00000000003fff00000000000fff000000000000fff000000000003ff000000000000000000000000000000440002c844108014411212c420281d02c8ca1384a80444201204a81200000000000000000000c00c03030000003000f00f000000300c03c0c000000c03c03030000000f000f00c00000300c00c030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.node 14 (.leaf 0xc0c0f0000300003c0c3c000f0000c0c3c0000f0000300c3c0003000000f00303c00000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffff0044141d00501400050030110454001405050050140000303504415400011505c15405c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (.leaf 0xfff0000000000000ff0000000000003fc00000000003ff0000000000003fc000000000000003ff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000003030300f00c030300c00300c0030300c0c0300c0300c00300c03003003000c03003003000000000000000000000000000ff000000000000fff000000000003ff000000000000ff0000000000003ff000000000000ff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000))))) (.node 22 (.node 18 (.node 16 (.leaf 0xfffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (.node 17 (.leaf 0x501540007084848551070c00c08024c80300c00000c4100208030040400000000000000484880840200300418090450340940a0202d402a0228505d401405005000000000000000000000000000000d0aa025014028000000000000000000000000000000000000000000000000000000000000000000000000000000000000000501599094000a0500124848000a88283008b220004850048121200090500c484848002200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (.leaf 0x1254442000046205cd510001551d400000000000000050f514000440c00000000000000004555100000140e2c09098800000e2842222000000d2f4941400000098a222a0000000000000000000000ac220c0280000000ce0648400c050883810000a88500d4c3e040038ba08830280000a0280000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))) (.node 20 (.node 19 (.leaf 0xa48aa432834a0848a848c00a28201000000000000008e00c84242404800000000000000a08408408102424a000208a48a008800000000000000aca000292ad2aa0a00020b50a222800000000000000280000a8ab482800000000000000000000000000000000000000000000000000000000000000000000000000000000000000a00a02228a220a22028a08402404400000000000000220a0212830a03aa00a6a084c29830000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (.leaf 0x84001450820622206800305145c0126408000cc1021094001088820200000000000000062264200040888002808108418014000a02b0c0a0000002b0c2102105c000a084a319114000000000000000000a0044084140c2e06012c18001d619899f1800000000000000000015899001400000000000000000000158a181201800003000050351d05050000622012022000006019830060500008818050005c00006220d4180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.node 21 (.leaf 0x3201a88041111100000000000000a118070033020120681421050981000000000000001111101b40810500c03030030030030300c00f000c0303000f00c00c0030f00c300c00c030000000000000003000c0300300311006064424000000000000000002d0029abae58006600005da26000000000000000000528002204aa20000000000000000000c441111541011030c110c44441100c154444450440033111111300440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (.leaf 0x3030f00303c0003c0f3c03cf00003030c00303000000000000000000003003c3c0030000000000000000000000000000000000000000000000000000000000ffffffffffffff000000000000000011090211a400001a45440e4000000b424051a400000544024990000000000000000000005505c1545c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))) (.node 26 (.node 24 (.node 23 (.leaf 0xffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ff00000000003fff000000000003ff00000000000fff0000000000000000000000000003ff000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (.leaf 0xfffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) (.node 25 (.leaf 0x140000150c84102200140584521000000000000000205018284312482350c881e11532000000000000000000000000000000000000000000000000000000000000000000000000000000000000002162400095004d0000000000000004106000410029480814000420066210115000000152481200112800aa88a00028082240b2000880dc122088e2000a000240a28880002400a0088dc1000900280000000000000000) (.leaf 0x280000005501150282800000301d01104400000c11044140000411010551100000c0410115115000000410001422028834210000500c05051400000c00a28a0a300000000000000000502128ce114000505220a2841000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0004a40a001208400011500011514000140440021084000440500090a300001150000514000180d40005244b22028411084d3886282321c80000000000000004462860120018044232000480140000000000000000))) (.node 28 (.node 27 (.leaf 0xc0220008a2222200000000000000022088500030420882814008222a8a82250c030102222220201d00082300c0c00c03c00c0c0300300030000c003003003000c000000000000000f00c0c0300c030c00300c00c00c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000031892222000462004142008801020312209888000000c022222200088034d544c000050500018140280a00000000000000074000e85a2e1a85900008808a8420300003b822a028000000000000000) (.leaf 0xc0c0003c3c0000c030003c300000c0c0003c0c00000c0f0003c3c00000c03c00003c00000000000000000000000000000000000000000000ffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001405014140140007415400c014001d014051101400015417015405c0000c044055014000000000000000)) (.node 29 (.leaf 0xfff00000000000003ff0000000000003fc00000000003fc0000000000003fc00000000000000ffc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ff00000000000fff0000000000003fc000000000000ff000000000000ffc000000000003ff000300c0c0300c0300c03003000c030300f0300c0c0300300300c00300303000c03000c03000000000000000) (.leaf 0xfffffffffffffff)))))) (.node 45 (.node 37 (.node 33 (.node 31 (.leaf 0x50001100149115000000000000000000000000000000300014000951453c005500175d45180005740021500000000000000000000000000000000000000000000000000000000000000000000000000000000000000031090400011844544200004028b0000000000000004540d02c0041c0000000000000000d4c3c8800322cce25024000f480068a20000a08800e2988900030000000000000000000e2a08a40000000aa2202800028000) (.node 32 (.leaf 0x280c000208ca0000a0000a0a2b0000000000000000000c280022a2b000af0a0000a2b000a0a088000aa1111414450031200104440003c120000000000000044044050000500c42f04940500000420442405000280f0000b080022283280000001452402b001080004450328004100012140000000000000002b00344000d1301184d0b12084008044291250440000000000000000c8291290090000011504580240000441c2120a014000) (.leaf 0xffc0000000000fffc000000000000000000000000003ff000000000000ffc0000000000003ffc0000000000000000114811110002402108606130031220511104400852381090210852000111101110d00120000f0030000c030003c000003000f003c0f0000300f000f03c0000c03000000000000000003c0300000c0300000000000000141104400a00001144642c4888003414404430d2000000a0022c34800110180484802800))) (.node 35 (.node 34 (.leaf 0xfffffffffffffff000000000000000000000000000000000000000000002222202000e1002088800001a10000088a0000e1000880088002a10000684a32a1000000880a0220005c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000028084e100000000812a1050000002012138444000002a128c62100000050011188400000050141701400) (.leaf 0xc0c0c0300000c0c03000c00000c0c030300c0000c03000c0300000c03c00300c00c00000c0300c00c000300000003ff000000000ffff0000000000003ffc000000000003ff00000000000000000000000003ffc00000c030300c030000300c00c0030000c0300c030300003c00c03000c0000c00300c00300000c00c0300c0300)) (.node 36 (.leaf 0xffc0000000000ffc000000000000ffc00000000003ff000000000000000fff00000000003fc00000000000000000000000000000000000000000000000000000000000fffffffffffffff00000000000000000000000003ff000000000003ff000000000003ff000000000000fff000000000003ff0000000000000ff) (.leaf 0x141100c40b100b01414141105066000000000000000000000000000040e03024242406100b02b044050120a0000001616e020000000000000001100000052d1450440000055484184000005168a218640000014b5c2000000000000000000000000000000000000000000000000000000000000000000000000000000000000001401601c41444180805100b00940b0000000000000000000000000000145009100b10640212402640c05031dae9940000396961d500000028611644600000090000000000000000000000000000005189185000000a0)))) (.node 41 (.node 39 (.node 38 (.leaf 0x2800002a0378200c002800012c0a08800000a8078208a0200028058208a03700004a0d03470000004405470000005454c50551400004400000000000000000005531400000140d0bd10000024140ca8c8003228bb2000000000000000820900082c0d0b00000000000000c0a2020000208ac8209000a000a504251401450002141c0074500015144113005000120511745000000440000000000000008074c4005000050) (.leaf 0x3000c011104c40400000000000000044110248445980000000000000010144210884a61c4044544a262a29c030000300c00f0300000c003c00c3000c00000c00303003000300300c30030000c0300c3003c00003003044001700049952000000000000005000164000a17a0000000000000055000017a00042a090009d800088aa000000000000003c232c404816b040c1284d011120400000000000000030404c404441100c12a1904140a0a00026aba00048000000000000008800017a480246a6000076800088a000000000000000c00032e2a8000a)) (.node 40 (.leaf 0xc00c003000f00c00000224848930000088199827000000000000000300084001808800f0000909085c400003ff00000000003ff0000000000000003ff00000000003fc000000000000ff0000000000000ffc00000000000000000008805c00089a1120a868180081c050000000000000000a8448050002152642e6240013615003003c00c300c000c000f00c00f000c03003c0c0f0000000000000000000f000f00300300c00c0030300c000000000000002822a8ba000028228a8880b4000908e8ba89400033500000000000000220220818540005) (.leaf 0xffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fff0000000003fff0000000000003ff0000000000000000000000000000fff00000000003ffc00000000000000000000000000000000000000000000000ffffffffffffff00000000000000000000000000000000000000ffc0000000000fffc000000000003fc00000000003fff0000000000000000000000000003ff00))) (.node 43 (.node 42 (.leaf 0xffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffff000000000000000) (.leaf 0x3003003c00f0030000284412110000000000000003000028181b0173c0000881818110f000002321080900ffc000000000000000000000000000fffc00000000003fc000000000003ff000000000003fff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c00c00300030003000f003003000000000000000000300c003c303c000f000f000c03c00003003c0c03000000000000000014000004565100c0110500077060000000000000001d456515000336045041040011648)) (.node 44 (.leaf 0x3030300c0c0000000000000000003030303c0f00000f0f03c3c3c00000f00c00c03c0000000000000000ffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001428000b4690000a0001a1069000220a0008869000000000000000001a10aa0000c90004a42b0006917) (.leaf 0xffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffff00000000000000000000000000000000000000000000000003ff0000000000fff0000000000000ffc000000000000000000000000000fffc0000000000ffc0000))))) (.node 52 (.node 48 (.node 46 (.leaf 0xfffffffffffffff00000000000000000000000000000) (.node 47 (.leaf 0xc00c03000c0030c003000c03000c0c00c0c0c03c030c00c030300c030c00c00300c00c088000011390280000000000000008200001451068511c000001515c5a220000005c58102040000334512100000000000000000000000000000030a000210220603c2c80031187990c08c800008960130a00020969105050000000515100000000000000003000000151c11006000001345110470000004d1551708000008437184) (.leaf 0xfffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000880000c2080a0000020b208a0a00208000a2080a00020b0002200a00028280000a0a300022000c88a0a30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000028000a208820000000a202c820000c0002a208200000a00088a0a300202c00222822000b080028c8228))) (.node 50 (.node 49 (.leaf 0x3030000c003030300000f0030030300c00030030300c00f00000c0300c000c00003000c0f00c0000300c0c00003ffc0000000000000000000000000ffc000000000003ffc000000000000ffff000000000ffc0000000300c000300c00c0c00003003c00c300c0000c0c00c0c003000003000c3003c00000c00c0f0030000300c03) (.leaf 0xff0000000000ffc00000000000003fc0000000000000ffc000000000003ff00000000000ffc000000000000000000000fffffffffffffff00000000000000000000000000000000000000000000000000000000000003fc0000000003ff00000000000000ff0000000000000ffc000000000003ff000000000003ff0000000)) (.node 51 (.leaf 0xc000002220808c80000000000000008822001400024030000045044542028800154149c08c88a80001c50400c0300c030030000300c003000c0000c00300c00f00003030300c00c000300c0c0300c0003000c03003002200888a80242d0000000000000000000000000000880000a2488a3a08d000285a3a3c584000404810454500000000000000c000008c82a8088c0002802208888c0000b20222822f0000008c802822c0000a03282e0a0a000140586a07000000000000000000000000000000900001641224588000047904a86834000d15148e71) (.leaf 0xc00c00f000c00000088a0a22c00000022222c8c000000a2208a8c0000002222322f000000000a3232ff0000000000000ffc00000000000fff000000000000ffc00000000000ffc00000000000ffc00000000000000000000000002282202602402d0000000000000002a02601a0700503000b40a005c0a08a0180a02e080a00003003c0c0c000000f000c00c000000c03c03030000003003c0c0c0000000f000f03c00000c03c0300c00000000000000002805005809a070000000000000003000502802dc0a22809a0800b40908a01e0202a0182)))) (.node 56 (.node 54 (.node 53 (.leaf 0x3ff000000000000003fc0000000000003fc00000000003fc000000000000ffc0000000000000fff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0c0303003c0c0c00c03000c03c0000000000000003003000c0300c03000f00300c0030300300300c0303000ffc000000000003ff000000000000ff0000000000003fc000000000000fff00000000000ff0000000000c0300c0c0300f0300300c00c0030000000000000003000c00c00c0030000c00300300303003c00c0c0300c) (.leaf 0xffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffff00000000000000000000000000000000000000000000)) (.node 55 (.leaf 0xffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ff00000000000000000000000000ffc000000000003fff00000000000fffc00000000003ff0000000000ffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000ffc0000000000000000000000000fff000000000000fff00000000000fffc00000000003ffc000000000) (.leaf 0xffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffff0000000000000000000000000000000000000000000000000000000000))) (.node 58 (.node 57 (.leaf 0xffc000000000000003fc000000000000ffc00000000003fc000000000000ff0000000000000fff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300c00300c00c0300c0c03c0c0c00c00300c0300c003000c03000c0c00c00c0f00c0c0ff000000000000ffc000000000000ff000000000000ffc00000000000fff000000000000ff00000000000000000000000000c00c03003000c0c03003030300f0c00300300f000c0c03000c03c00c0c00c0030300c030) (.leaf 0xffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000)) (.node 59 (.leaf 0xffc00000000000fff00000000000ffc00000000000fff00000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0c00c030000c03000c0300000c030300c0300003000c0300c00000c00300c00f0000300f0300303000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c030300c030000300c00c0030000c00c0c000300000c00c03000f0000c00300c00300003003c0c0300c0) (.leaf 0xfffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ff000000000000ff000000000000ff000000000000ffc00000000000fff000000000000ffc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ff000000000000ffc00000000000ff000000000000fff000000000000ff000000000000ffc000000000000)))))))

def lineSupport (q : Nat) : Nat := packedLineSupport.lookup q

def localStar (i : Nat) : Nat := starTable.block 8 60 i

def groupMask (g : Nat) : Nat := (2^344-1) <<< (344*g)

def overlap : List Nat → Nat × Nat
  | [] => (0, 0)
  | q :: qs =>
    let tail := overlap qs
    let hits := lineSupport q
    (hits ||| tail.1, tail.2 ||| (hits &&& tail.1))

def conflicts (i : Nat) : Nat :=
  let hits := overlap (setBitPositions 6 (localStar i))
  (hits.1 &&& groupMask (i/344)) ||| hits.2


def candidateMask : Nat := 2^1720-1

def boundedConflicts (i : Nat) : Nat := conflicts i &&& candidateMask

def geometryTables : Tables where
  starMask index := if index < 1720 then (starTable.block 8 60 index) <<< (60 * (index / 344)) else 0
  candidatesAt pivot := (edgeTable.block 8 344 pivot) <<< (344 * (pivot / 60))
  compatibleWith index := candidateMask ^^^ boundedConflicts index

def check (cuts : Nat → Option (Nat × Nat)) (remaining available : Nat) (data : List Nat) : Bool :=
  (verifyNode geometryTables cuts 30 remaining available ⟨data, 0, 0⟩).isSome


lemma check_implies_no_cover (cuts : Nat → Option (Nat × Nat))
    (cut_sound : ∀ i r a, cuts i = some (r, a) → ¬ HasCover geometryTables r a)
    (allowed_at : ∀ p i, (geometryTables.starMask i).testBit p = true →
      (geometryTables.candidatesAt p).testBit i = true)
    (remaining available : Nat) (data : List Nat)
    (accepted : check cuts remaining available data = true) :
    ¬ HasCover geometryTables remaining available := by
  unfold check at accepted
  cases result : verifyNode geometryTables cuts 30 remaining available ⟨data, 0, 0⟩ with
  | none => simp [result] at accepted
  | some cursor =>
      exact verifyNode_excludes_cover geometryTables cuts cut_sound allowed_at
        30 remaining available ⟨data, 0, 0⟩ cursor result

lemma check_without_cuts_implies_no_cover
    (allowed_at : ∀ p i, (geometryTables.starMask i).testBit p = true →
      (geometryTables.candidatesAt p).testBit i = true)
    (remaining available : Nat) (data : List Nat)
    (accepted : check (fun _ => none) remaining available data = true) :
    ¬ HasCover geometryTables remaining available :=
  check_implies_no_cover (fun _ => none) (by simp) allowed_at remaining available data accepted


def allSetBits (check : Nat → Bool) : Nat → Nat → Bool
  | 0, word => word == 0
  | fuel + 1, word =>
      if word == 0 then true
      else check word.log2 && allSetBits check fuel (word ^^^ 2^word.log2)

lemma allSetBits_correct (check : Nat → Bool) (fuel word index : Nat)
    (accepted : allSetBits check fuel word = true)
    (present : word.testBit index = true) : check index = true := by
  induction fuel generalizing word with
  | zero =>
      have empty : word = 0 := beq_iff_eq.mp accepted
      simp [empty] at present
  | succ fuel ih =>
      by_cases empty : word = 0
      · simp [empty] at present
      simp only [allSetBits, beq_iff_eq, if_neg empty, Bool.and_eq_true] at accepted
      by_cases same : index = word.log2
      · rw [same]
        exact accepted.1
      · apply ih (word ^^^ 2^word.log2) accepted.2
        simpa only [Nat.testBit_xor, Nat.testBit_two_pow, Ne.symm same,
          decide_false, Bool.xor_false] using present


def checkSupportGroup (g : Nat) : Bool :=
  (List.range 344).all fun i =>
    allSetBits (fun p => (geometryTables.candidatesAt p).testBit (g*344+i)) 6
      (geometryTables.starMask (g*344+i))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma checkSupportGroup_0 : checkSupportGroup 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma checkSupportGroup_1 : checkSupportGroup 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma checkSupportGroup_2 : checkSupportGroup 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma checkSupportGroup_3 : checkSupportGroup 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000000 in
lemma checkSupportGroup_4 : checkSupportGroup 4 = true := by decide +kernel

theorem supportGroup (g : Nat) (small : g < 5) : checkSupportGroup g = true := by
  have cases : g=0 ∨ g=1 ∨ g=2 ∨ g=3 ∨ g=4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl
  · exact checkSupportGroup_0
  · exact checkSupportGroup_1
  · exact checkSupportGroup_2
  · exact checkSupportGroup_3
  · exact checkSupportGroup_4

theorem actualAllowedAt (p i : Nat) (present : (geometryTables.starMask i).testBit p = true) :
    (geometryTables.candidatesAt p).testBit i = true := by
  by_cases valid : i < 1720
  · have q : i / 344 < 5 := by omega
    have r : i % 344 < 344 := by omega
    have identity : i / 344 * 344 + i % 344 = i := by omega
    have hit := List.all_eq_true.mp (supportGroup (i / 344) q) (i % 344) (List.mem_range.mpr r)
    simpa only [identity] using
      (allSetBits_correct (fun n => (geometryTables.candidatesAt n).testBit (i / 344 * 344 + i % 344))
        6 (geometryTables.starMask (i / 344 * 344 + i % 344)) p hit (by simpa only [identity] using present))
  · simp [geometryTables, valid] at present


def initialFor (part : List Nat) : Nat × Nat :=
  part.foldl (fun state i => (state.1 ^^^ geometryTables.starMask i, state.2 &&& geometryTables.compatibleWith i))
    (0xd5c1dd01e7d77fa00cccf3cf3f3f3ffffc3ef80fafa0015f55fdd75f5f00fffffffff000000, 2^1720-1)

end WeightFifteenVerifiedSearch

namespace WeightFifteenVerifiedSearch

def rowSafe (i : Nat) : Bool :=
  geometryTables.compatibleWith i ||| boundedConflicts i == candidateMask

def checkRows (start number : Nat) : Bool :=
  (List.range number).all fun i => rowSafe (start+i)

lemma positions_nodup (fuel word : Nat) : (setBitPositions fuel word).Nodup := by
  induction fuel generalizing word with
  | zero => simp [setBitPositions]
  | succ fuel ih =>
      by_cases empty : word = 0
      · simp [setBitPositions, empty]
      simp only [setBitPositions, if_neg empty, List.nodup_cons]
      refine ⟨?_, ih _⟩
      intro present
      have yes := setBitPositions_sound _ _ _ present
      simpa [Nat.testBit_xor, Nat.testBit_log2 empty, Nat.testBit_two_pow_self] using yes

lemma overlap_sound (qs : List Nat) (distinct : qs.Nodup) (j : Nat) :
    ((overlap qs).1.testBit j = true → ∃ q ∈ qs, (lineSupport q).testBit j = true) ∧
    ((overlap qs).2.testBit j = true →
      ∃ a ∈ qs, ∃ b ∈ qs, a ≠ b ∧ (lineSupport a).testBit j = true ∧ (lineSupport b).testBit j = true) := by
  induction qs with
  | nil => simp [overlap]
  | cons q tail ih =>
    obtain ⟨q_not, tail_distinct⟩ := List.nodup_cons.mp distinct
    obtain ⟨one, two⟩ := ih tail_distinct
    simp only [overlap, Nat.testBit_lor, Nat.testBit_land, Bool.or_eq_true, Bool.and_eq_true]
    constructor
    · rintro (hit | hit)
      · exact ⟨q, List.mem_cons_self, hit⟩
      · obtain ⟨p, listed, yes⟩ := one hit
        exact ⟨p, List.mem_cons_of_mem _ listed, yes⟩
    · rintro (hit | ⟨a_hit, other_hit⟩)
      · obtain ⟨a, ha, b, hb, neq, sa, sb⟩ := two hit
        exact ⟨a, List.mem_cons_of_mem _ ha, b, List.mem_cons_of_mem _ hb, neq, sa, sb⟩
      · obtain ⟨b, hb, s⟩ := one other_hit
        exact ⟨q, List.mem_cons_self, b, List.mem_cons_of_mem _ hb, fun eq => q_not (eq.symm ▸ hb), a_hit, s⟩

lemma localStar_bound (i : Nat) : localStar i < 2^60 := by
  unfold localStar Lookup.block
  exact Nat.and_lt_two_pow _ (by decide)

lemma line_lt_of_bit {i q : Nat} (yes : (localStar i).testBit q = true) : q < 60 := by
  by_contra outside
  have bound := (localStar_bound i).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt outside))
  exact Bool.false_ne_true ((Nat.testBit_lt_two_pow bound).symm.trans yes)

lemma same_group_of_mask {g j : Nat} (bit : (groupMask g).testBit j = true) : j / 344 = g := by
  unfold groupMask at bit
  simp only [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, Bool.and_eq_true, decide_eq_true_eq] at bit
  omega

theorem checked_compatible
    (support_sound : ∀ p j, p < 60 → j < 1720 → (lineSupport p).testBit j = true → (localStar j).testBit p = true)
    (i j : Nat) (small : j < 1720) (_checked : rowSafe i = true)
    (same_group : i/344 = j/344 → ∀ p, (localStar i).testBit p = true → (localStar j).testBit p = false)
    (separate : ∀ p q, p ≠ q → (localStar i).testBit p = true → (localStar i).testBit q = true →
      (localStar j).testBit p = true → (localStar j).testBit q = true → False) :
    (geometryTables.compatibleWith i).testBit j = true := by
  let qs := setBitPositions 6 (localStar i)
  obtain ⟨once, twice⟩ := overlap_sound qs (positions_nodup _ _) j
  have hit (p : Nat) (hp : p ∈ qs) : (localStar i).testBit p = true := setBitPositions_sound _ _ _ hp
  have noConflict : (conflicts i).testBit j = false := by
    cases yes : (conflicts i).testBit j with
    | false => rfl
    | true =>
      exfalso
      change ((overlap qs).1 &&& groupMask (i/344) ||| (overlap qs).2).testBit j = true at yes
      simp only [Nat.testBit_lor, Nat.testBit_land, Bool.or_eq_true, Bool.and_eq_true] at yes
      rcases yes with ⟨a, group⟩ | b
      · obtain ⟨p, hp, pos⟩ := once a
        have first := hit p hp
        have second := support_sound p j (line_lt_of_bit first) small pos
        have no := same_group (same_group_of_mask group).symm p first
        exact Bool.false_ne_true (no.symm.trans second)
      · obtain ⟨p, hp, q, hq, neq, pos, other⟩ := twice b
        exact separate p q neq (hit p hp) (hit q hq)
          (support_sound p j (line_lt_of_bit (hit p hp)) small pos)
          (support_sound q j (line_lt_of_bit (hit q hq)) small other)
  change (candidateMask ^^^ boundedConflicts i).testBit j = true
  simp only [Nat.testBit_xor, boundedConflicts, Nat.testBit_land, candidateMask,
    Nat.testBit_two_pow_sub_one, decide_eq_true small, noConflict, Bool.false_and, Bool.xor_false]

theorem everyRowSafe (i : Nat) (_ : i < 1720) : rowSafe i = true := by
  apply beq_iff_eq.mpr
  apply Nat.eq_of_testBit_eq
  intro j
  change (candidateMask ^^^ boundedConflicts i ||| boundedConflicts i).testBit j = candidateMask.testBit j
  simp only [ Nat.testBit_lor, Nat.testBit_xor, boundedConflicts, Nat.testBit_land]
  cases candidateMask.testBit j <;> cases (conflicts i).testBit j <;> rfl

end WeightFifteenVerifiedSearch

namespace WeightFifteenVerifiedSearch

/-- Every claimed candidate at an obligation actually contains that obligation. -/
def checkReverseSupport (g : Nat) : Bool :=
  (List.range 60).all fun p =>
    allSetBits (fun i => (starTable.block 8 60 (344*g+i)).testBit p) 344
      (edgeTable.block 8 344 (60*g+p))

set_option maxRecDepth 80000 in
set_option maxHeartbeats 600000000 in
lemma reverseSupport0 : checkReverseSupport 0 = true := by rfl

set_option maxRecDepth 80000 in
set_option maxHeartbeats 600000000 in
lemma reverseSupport1 : checkReverseSupport 1 = true := by rfl

set_option maxRecDepth 80000 in
set_option maxHeartbeats 600000000 in
lemma reverseSupport2 : checkReverseSupport 2 = true := by rfl

set_option maxRecDepth 80000 in
set_option maxHeartbeats 600000000 in
lemma reverseSupport3 : checkReverseSupport 3 = true := by rfl

set_option maxRecDepth 80000 in
set_option maxHeartbeats 600000000 in
lemma reverseSupport4 : checkReverseSupport 4 = true := by rfl

lemma reverseSupport (g : Nat) (valid : g<5) : checkReverseSupport g = true := by
  have cases : g=0 ∨ g=1 ∨ g=2 ∨ g=3 ∨ g=4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl
  · exact reverseSupport0
  · exact reverseSupport1
  · exact reverseSupport2
  · exact reverseSupport3
  · exact reverseSupport4

theorem actualContainsObligation (p i : Nat) (small : p<300)
    (found : (geometryTables.candidatesAt p).testBit i = true) :
    (geometryTables.starMask i).testBit p = true := by
  let g := p/60
  let q := p%60
  have group_lt : g<5 := by dsimp [g]; omega
  have line_lt : q<60 := Nat.mod_lt _ (by decide)
  have pivot_eq : 60*g+q = p := by dsimp [g,q]; omega
  have result := List.all_eq_true.mp (reverseSupport g group_lt) q (List.mem_range.mpr line_lt)
  change allSetBits (fun j => (starTable.block 8 60 (344*g+j)).testBit q) 344
    (edgeTable.block 8 344 (60*g+q)) = true at result
  rw [pivot_eq] at result
  change ((edgeTable.block 8 344 p) <<< (344*g)).testBit i = true at found
  simp only [Nat.testBit_shiftLeft, Bool.and_eq_true] at found
  have offset_le : 344*g ≤ i := of_decide_eq_true found.1
  have word_bound : edgeTable.block 8 344 p < 2^344 := by
    unfold Lookup.block
    exact Nat.and_lt_two_pow _ (Nat.sub_lt (Nat.two_pow_pos _) (by decide))
  have idx_lt : i - 344*g < 344 := by
    by_contra too_big
    have little : edgeTable.block 8 344 p < 2^(i-344*g) :=
      word_bound.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt too_big))
    exact Bool.false_ne_true ((Nat.testBit_lt_two_pow little).symm.trans found.2)
  have idx_eq : 344*g+(i-344*g) = i := by omega
  have in_group : i/344 = g := by omega
  have index_lt : i < 1720 := by omega
  have checked := allSetBits_correct _ _ _ _ result found.2
  rw [idx_eq] at checked
  have pivot_valid : 60*g ≤ p := by omega
  have q_eq : p-60*g = q := by omega
  change (if i < 1720 then (starTable.block 8 60 i) <<< (60*(i/344)) else 0).testBit p = true
  simpa only [if_pos index_lt, in_group, Nat.testBit_shiftLeft, decide_eq_true pivot_valid, Bool.true_and, q_eq]
    using checked

lemma included_if_not_conflict (allowed conflicts i width : Nat) (within : i < width)
    (cover_all : (allowed ||| conflicts) &&& (2^width-1) = 2^width-1)
    (disjoint_lines : conflicts.testBit i = false) : allowed.testBit i = true := by
  have eq := congrArg (fun w : Nat => w.testBit i) cover_all
  simp only [Nat.testBit_land, Nat.testBit_lor, Nat.testBit_two_pow_sub_one,
    decide_eq_true within, disjoint_lines, Bool.or_false, Bool.and_true] at eq
  exact eq

end WeightFifteenVerifiedSearch

namespace WeightFifteenVerifiedSearch

def supportSum (q : Nat) : Nat :=
  ((List.range 5).map fun g => geometryTables.candidatesAt (60*g+q)).foldr Nat.lor 0

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma supportSum_agrees : ∀ q : Fin 60, lineSupport q.val = supportSum q.val := by decide +kernel

lemma bit_of_fold (words : List Nat) (i : Nat) (hit : (words.foldr Nat.lor 0).testBit i = true) :
    ∃ a ∈ words, a.testBit i = true := by
  induction words with
  | nil => simp at hit
  | cons head tail ih =>
    change (head ||| tail.foldr Nat.lor 0).testBit i = true at hit
    simp only [Nat.testBit_lor, Bool.or_eq_true] at hit
    rcases hit with here | later
    · exact ⟨head, List.mem_cons_self, here⟩
    · obtain ⟨a, ha, bit⟩ := ih later
      exact ⟨a, List.mem_cons_of_mem _ ha, bit⟩

lemma lineSupport_sound
    (reverse : ∀ p i : Nat, p < 300 → (geometryTables.candidatesAt p).testBit i = true →
      (geometryTables.starMask i).testBit p = true)
    (p j : Nat) (p_in : p<60) (j_in : j<1720) (present : (lineSupport p).testBit j = true) :
    (localStar j).testBit p = true := by
  rw [show lineSupport p = supportSum p from supportSum_agrees ⟨p,p_in⟩] at present
  obtain ⟨a, listed, seen⟩ := bit_of_fold _ j present
  obtain ⟨g, group_listed, rfl⟩ := List.mem_map.mp listed
  have g_in : g < 5 := List.mem_range.mp group_listed
  have shifted := reverse (60*g+p) j (by omega) seen
  unfold geometryTables at shifted
  simp only [if_pos j_in, Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at shifted
  obtain ⟨lower, bit⟩ := shifted
  have upper : 60*g+p-60*(j/344) < 60 := line_lt_of_bit bit
  have equal : 60*g+p-60*(j/344) = p := by omega
  simpa only [equal, localStar] using bit

theorem full_compatibility_sound
    (reverse : ∀ p i : Nat, p < 300 → (geometryTables.candidatesAt p).testBit i = true →
      (geometryTables.starMask i).testBit p = true)
    (rows : ∀ i : Nat, i < 1720 → rowSafe i = true)
    (i j : Nat) (i_in : i < 1720) (j_in : j < 1720)
    (same_group : i/344 = j/344 → ∀ p, (localStar i).testBit p = true → (localStar j).testBit p = false)
    (separate : ∀ p q, p ≠ q → (localStar i).testBit p = true → (localStar i).testBit q = true →
      (localStar j).testBit p = true → (localStar j).testBit q = true → False) :
    (geometryTables.compatibleWith i).testBit j = true :=
  checked_compatible (lineSupport_sound reverse) i j j_in (rows i i_in) same_group separate

end WeightFifteenVerifiedSearch

namespace WeightFifteenConcreteGenerators

open WeightFifteenIndexedSearch WeightFifteenIndexedSymmetry

def actionParents : List (Nat × Fin 4) := [(0, 0), (0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (3, 1), (3, 3), (4, 2), (5, 2), (5, 3), (6, 1), (6, 3), (7, 2), (8, 1), (8, 3), (9, 2), (10, 3), (11, 2), (12, 1), (13, 1), (13, 3), (14, 2), (15, 3), (16, 2), (17, 1), (18, 3), (19, 2), (20, 1), (21, 2), (22, 1), (24, 3), (25, 2), (26, 1), (27, 2), (28, 1), (30, 2), (31, 1), (33, 1), (35, 2), (36, 1), (38, 1), (40, 1), (43, 1)]

def actionParent (a : Nat) : Nat × Fin 4 := actionParents[a]?.getD (0,0)

def checkAction (a : Nat) : Bool :=
  if a = 0 then (List.range 344).all fun i => imageAt a i == i
  else
    let (parent, step) := actionParent a
    decide (parent < a) && (List.range 344).all fun i =>
      imageAt a i == imageAt (step.val+1) (imageAt parent i)

def checkedGenerator (k : Fin 4) : Σ symmetry : Symmetry, CatalogueRelabeling symmetry :=
  ([⟨generator0, faithfulGenerator0⟩, ⟨generator1, faithfulGenerator1⟩,
    ⟨generator2, faithfulGenerator2⟩, ⟨generator3, faithfulGenerator3⟩] :
      List (Σ symmetry : Symmetry, CatalogueRelabeling symmetry))[k.val]

lemma generator_moves (k : Fin 4) : (checkedGenerator k).2.move = imageAt (k.val+1) := by
  fin_cases k <;> rfl

lemma direct_first_bound {i word : Nat} (found : (directCatalog 0)[i]? = some word) : i < 344 := by
  rw [direct_first_catalogue] at found
  simpa only [expected_length] using (List.getElem?_eq_some_iff.mp found).1

lemma permute_identity (word : Nat) (bounded : word < 2^60) :
    permuteWord (Equiv.refl (Fin 60)) word = word := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases ok : i < 60
  · exact permuteWord_bit _ _ (⟨i, ok⟩ : Fin 60)
  · rw [permuteWord_outside _ _ i (Nat.le_of_not_gt ok)]
    exact (Nat.testBit_lt_two_pow (bounded.trans_le
      (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt ok)))).symm

lemma direct_first_word_bound {i word : Nat} (found : (directCatalog 0)[i]? = some word) : word < 2^60 := by
  have bound := direct_first_bound found
  rw [direct_first_catalogue, table_get i bound] at found
  rw [← Option.some.inj found]
  exact starAt_bound i

theorem checkedAction_correct (checks : ∀ a < 48, checkAction a = true) (row : Nat) (in_table : row < 48) :
    ∃ a, ∃ action : CatalogueRelabeling a, action.move = imageAt row := by
  induction row using Nat.strongRecOn with
  | ind row ih =>
    have tested := checks row in_table
    by_cases identity : row = 0
    · subst row
      refine ⟨Symmetry.identity, ⟨imageAt 0, ?_⟩, rfl⟩
      intro i word found
      have equal := List.all_eq_true.mp (show (List.range 344).all (fun x => imageAt 0 x == x) = true from tested)
        i (List.mem_range.mpr (direct_first_bound found))
      rw [beq_iff_eq.mp equal]
      rw [show Symmetry.identity.line = Equiv.refl _ from rfl, permute_identity _ (direct_first_word_bound found)]
      exact found
    · simp only [checkAction, if_neg identity, Bool.and_eq_true, decide_eq_true_eq] at tested
      obtain ⟨earlier, agrees⟩ := tested
      obtain ⟨a, act, repr⟩ := ih (actionParent row).1 earlier (earlier.trans in_table)
      let step := (actionParent row).2
      let next := checkedGenerator step
      let joined := act.compose next.2
      refine ⟨a.compose next.1, ⟨imageAt row, ?_⟩, rfl⟩
      intro i word found
      have h := List.all_eq_true.mp agrees i (List.mem_range.mpr (direct_first_bound found))
      change (imageAt row i == imageAt (step.val+1) (imageAt (actionParent row).1 i)) = true at h
      have key := congrFun repr i
      have backed := congrFun (generator_moves step) (act.move i)
      have same : imageAt row i = joined.move i :=
        (beq_iff_eq.mp h).trans (by change _ = next.2.move (act.move i); rw [backed, key])
      rw [same]
      exact joined.agrees _ _ found

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow0 : checkAction 0 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow1 : checkAction 1 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow2 : checkAction 2 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow3 : checkAction 3 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow4 : checkAction 4 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow5 : checkAction 5 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow6 : checkAction 6 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow7 : checkAction 7 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow8 : checkAction 8 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow9 : checkAction 9 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow10 : checkAction 10 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow11 : checkAction 11 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow12 : checkAction 12 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow13 : checkAction 13 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow14 : checkAction 14 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow15 : checkAction 15 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow16 : checkAction 16 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow17 : checkAction 17 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow18 : checkAction 18 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow19 : checkAction 19 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow20 : checkAction 20 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow21 : checkAction 21 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow22 : checkAction 22 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow23 : checkAction 23 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow24 : checkAction 24 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow25 : checkAction 25 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow26 : checkAction 26 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow27 : checkAction 27 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow28 : checkAction 28 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow29 : checkAction 29 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow30 : checkAction 30 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow31 : checkAction 31 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow32 : checkAction 32 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow33 : checkAction 33 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow34 : checkAction 34 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow35 : checkAction 35 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow36 : checkAction 36 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow37 : checkAction 37 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow38 : checkAction 38 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow39 : checkAction 39 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow40 : checkAction 40 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow41 : checkAction 41 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow42 : checkAction 42 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow43 : checkAction 43 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow44 : checkAction 44 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow45 : checkAction 45 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow46 : checkAction 46 = true := by rfl

set_option maxRecDepth 15000 in
set_option maxHeartbeats 800000000 in
lemma actionRow47 : checkAction 47 = true := by rfl

theorem checkedActions (a : Nat) (in_table : a < 48) : checkAction a = true := by
  interval_cases a
  · exact actionRow0
  · exact actionRow1
  · exact actionRow2
  · exact actionRow3
  · exact actionRow4
  · exact actionRow5
  · exact actionRow6
  · exact actionRow7
  · exact actionRow8
  · exact actionRow9
  · exact actionRow10
  · exact actionRow11
  · exact actionRow12
  · exact actionRow13
  · exact actionRow14
  · exact actionRow15
  · exact actionRow16
  · exact actionRow17
  · exact actionRow18
  · exact actionRow19
  · exact actionRow20
  · exact actionRow21
  · exact actionRow22
  · exact actionRow23
  · exact actionRow24
  · exact actionRow25
  · exact actionRow26
  · exact actionRow27
  · exact actionRow28
  · exact actionRow29
  · exact actionRow30
  · exact actionRow31
  · exact actionRow32
  · exact actionRow33
  · exact actionRow34
  · exact actionRow35
  · exact actionRow36
  · exact actionRow37
  · exact actionRow38
  · exact actionRow39
  · exact actionRow40
  · exact actionRow41
  · exact actionRow42
  · exact actionRow43
  · exact actionRow44
  · exact actionRow45
  · exact actionRow46
  · exact actionRow47

end WeightFifteenConcreteGenerators

/- Send a geometric cover to the indexed exact-cover model and preserve it while fixing stars from its first partition. -/

namespace WeightFifteenVerifiedSearch

open Finset

def CoversWith (tables : Tables) (remaining available : Nat) (picked : Finset Nat) : Prop :=
    (∀ i ∈ picked, available.testBit i = true) ∧
    (∀ i ∈ picked, ∀ p, (tables.starMask i).testBit p = true → remaining.testBit p = true) ∧
    (∀ i ∈ picked, ∀ j ∈ picked, i ≠ j →
      (tables.compatibleWith i).testBit j = true ∧
      ∀ p, (tables.starMask i).testBit p = true → (tables.starMask j).testBit p = false) ∧
    ∀ p, remaining.testBit p = true → ∃ i ∈ picked, (tables.starMask i).testBit p = true

lemma CoversWith.erase (tables : Tables) (remaining available : Nat) (picked : Finset Nat)
    (valid : CoversWith tables remaining available picked) (index : Nat) (select : index ∈ picked) :
    CoversWith tables (remaining ^^^ tables.starMask index) (available &&& tables.compatibleWith index)
      (picked.erase index) := by
  rcases valid with ⟨available_of, inside, separated, covering⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨neq, picked_i⟩ := Finset.mem_erase.mp hi
    simp [available_of i picked_i, (separated index select i picked_i neq.symm).1]
  · intro i hi p bit
    obtain ⟨neq, picked_i⟩ := Finset.mem_erase.mp hi
    have old := inside i picked_i p bit
    have no_bit := (separated i picked_i index select neq).2 p bit
    simp [Nat.testBit_xor, old, no_bit]
  · intro i hi j hj neq
    exact separated i (Finset.mem_of_mem_erase hi) j (Finset.mem_of_mem_erase hj) neq
  · intro p left
    have absent : (tables.starMask index).testBit p = false := by
      cases selected : (tables.starMask index).testBit p with
      | false => rfl
      | true =>
        have old := inside index select p selected
        simp [Nat.testBit_xor, old, selected] at left
    have old : remaining.testBit p = true := by simpa [Nat.testBit_xor, absent] using left
    obtain ⟨i, picked_i, take⟩ := covering p old
    have neq : i ≠ index := by intro same; rw [same, absent] at take; contradiction
    exact ⟨i, Finset.mem_erase.mpr ⟨neq, picked_i⟩, take⟩

def chooseStars (tables : Tables) (partition : List Nat) (initial : Nat × Nat) : Nat × Nat :=
  partition.foldl (fun s i => (s.1 ^^^ tables.starMask i, s.2 &&& tables.compatibleWith i)) initial

theorem chooseStars_preserves_cover (tables : Tables) (partition : List Nat) (distinct : partition.Nodup)
    (remaining available : Nat) (picked : Finset Nat) (valid : CoversWith tables remaining available picked)
    (selected : ∀ i ∈ partition, i ∈ picked) :
    HasCover tables (chooseStars tables partition (remaining,available)).1
      (chooseStars tables partition (remaining,available)).2 := by
  induction partition generalizing remaining available picked with
  | nil => exact ⟨picked, valid⟩
  | cons i rest ih =>
    obtain ⟨missing, tail⟩ := List.nodup_cons.mp distinct
    have hit := selected i (List.mem_cons_self)
    have after := valid.erase tables remaining available picked i hit
    have keep (j : Nat) (hj : j ∈ rest) : j ∈ picked.erase i := by
      have different : j ≠ i := fun eq => missing (eq ▸ hj)
      exact Finset.mem_erase.mpr ⟨different, selected j (List.mem_cons_of_mem _ hj)⟩
    exact ih tail (remaining ^^^ tables.starMask i) (available &&& tables.compatibleWith i)
      (picked.erase i) after keep

end WeightFifteenVerifiedSearch

namespace WeightFifteenVerifiedSearch

open Finset WeightFifteenIndexedSearch WeightFifteenIndexedSymmetry WeightFifteenLargeCatalog

def groupAt (g : Fin 5) : Fin 15 := ([0,9,14,4,7] : List (Fin 15))[g.val]

lemma groupAt_inj : Function.Injective groupAt := by decide +kernel

lemma group_zero : groupAt 0 = 0 := rfl

def allObligations : Nat := 0xd5c1dd01e7d77fa00cccf3cf3f3f3ffffc3ef80fafa0015f55fdd75f5f00fffffffff000000

def allCandidates : Nat := 2^1720-1

lemma obligationRows : ∀ g : Fin 5,
    ((allObligations >>> (60*g.val)) &&& (2^60-1)) = eligibleMask (groupAt g) := by decide +kernel

lemma obligation_bit (g : Fin 5) (p : Fin 60) :
    allObligations.testBit (60*g.val+p.val) = (eligibleMask (groupAt g)).testBit p.val := by
  have word := congrArg (fun n : Nat => n.testBit p.val) (obligationRows g)
  simpa only [Nat.testBit_land, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
    decide_eq_true p.isLt, Bool.and_true] using word

lemma obligation_bound : allObligations < 2^300 := by decide

lemma obligation_of_bit (q : Nat) (on : allObligations.testBit q = true) :
    ∃ (g : Fin 5) (p : Fin 60), q = 60*g.val+p.val ∧ (eligibleMask (groupAt g)).testBit p.val = true := by
  have small : q < 300 := by
    by_contra outside
    have below := obligation_bound.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt outside))
    exact Bool.false_ne_true ((Nat.testBit_lt_two_pow below).symm.trans on)
  let g : Fin 5 := ⟨q/60, by omega⟩
  let p : Fin 60 := ⟨q%60, by omega⟩
  have same : q = 60*g.val+p.val := by dsimp only [g,p]; omega
  refine ⟨g, p, same, ?_⟩
  rwa [← obligation_bit, ← same]

def starWord (s : Fin 15 → Fin 6 → Finset (Fin 60)) (g : Fin 5) (t : Fin 6) : Nat :=
  pack ((s (groupAt g) t).image Fin.val)

def starOrdinal (s : Fin 15 → Fin 6 → Finset (Fin 60)) (g : Fin 5) (t : Fin 6) : Nat :=
  (directCatalog (groupAt g)).idxOf (starWord s g t)

def starKey (s : Fin 15 → Fin 6 → Finset (Fin 60)) (g : Fin 5) (t : Fin 6) : Nat :=
  344*g.val + starOrdinal s g t

lemma starWord_some (s : Fin 15 → Fin 6 → Finset (Fin 60)) (valid : IsCover s) (g : Fin 5) (t : Fin 6) :
    (directCatalog (groupAt g))[starOrdinal s g t]? = some (starWord s g t) := by
  have found := indexed_star_in_catalog (groupAt g) (s (groupAt g) t) (valid.1 (groupAt g) t) (valid.2.1 (groupAt g) t)
  exact List.getElem?_idxOf ((directCatalog_mem (groupAt g) _).mpr found)

lemma starDecoded
    (layout : ∀ g : Fin 5, (List.range 344).map (fun i => starTable.block 8 60 (344*g.val+i)) = directCatalog (groupAt g))
    (s : Fin 15 → Fin 6 → Finset (Fin 60)) (valid : IsCover s) (g : Fin 5) (t : Fin 6) :
    starOrdinal s g t < 344 ∧ starTable.block 8 60 (starKey s g t) = starWord s g t := by
  have hit := starWord_some s valid g t
  rw [← layout g] at hit
  have below := (List.getElem?_eq_some_iff.mp hit).1
  have bound : starOrdinal s g t < 344 := by simpa using below
  refine ⟨bound, Option.some.inj ?_⟩
  simpa only [List.getElem?_map, List.getElem?_eq_getElem (by simpa using bound : starOrdinal s g t < (List.range 344).length),
    List.getElem_range, Option.map_some, starKey] using hit

lemma star_global_bit
    (layout : ∀ g : Fin 5, (List.range 344).map (fun i => starTable.block 8 60 (344*g.val+i)) = directCatalog (groupAt g))
    (s : Fin 15 → Fin 6 → Finset (Fin 60)) (valid : IsCover s) (g : Fin 5) (t : Fin 6) (q : Nat) :
    (geometryTables.starMask (starKey s g t)).testBit q = true ↔
      ∃ p ∈ s (groupAt g) t, q = 60*g.val+p.val := by
  obtain ⟨small, word⟩ := starDecoded layout s valid g t
  have index_lt : starKey s g t < 1720 := by unfold starKey; have := g.isLt; omega
  have group_index : starKey s g t / 344 = g.val := by unfold starKey; omega
  unfold geometryTables
  simp only [if_pos index_lt, word, group_index, Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq, starWord, star_mask_bit]
  constructor
  · rintro ⟨lo, p, hp, index⟩
    exact ⟨p, hp, by omega⟩
  · rintro ⟨p, hp, index⟩
    exact ⟨by omega, p, hp, by omega⟩

lemma distinct_stars_same_group (s : Fin 15 → Fin 6 → Finset (Fin 60)) (valid : IsCover s)
    (g : Fin 5) (i j : Fin 6) (different : i ≠ j) : Disjoint (s (groupAt g) i) (s (groupAt g) j) := by
  rw [Finset.disjoint_left]
  intro p one two
  obtain ⟨_, _, unique⟩ := valid.2.2.1 (groupAt g) p (valid.1 (groupAt g) i p one)
  exact different ((unique i one).trans (unique j two).symm)

theorem indexed_cover_for_tables
    (layout : ∀ g : Fin 5, (List.range 344).map (fun i => starTable.block 8 60 (344*g.val+i)) = directCatalog (groupAt g))
    (compatible : ∀ (i j : Nat), i < 1720 → j < 1720 →
      (i/344 = j/344 → ∀ p, (starTable.block 8 60 i).testBit p = true → (starTable.block 8 60 j).testBit p = false) →
      (∀ p q, p ≠ q → (starTable.block 8 60 i).testBit p = true → (starTable.block 8 60 i).testBit q = true →
        (starTable.block 8 60 j).testBit p = true → (starTable.block 8 60 j).testBit q = true → False) →
      (geometryTables.compatibleWith i).testBit j = true)
    (s : Fin 15 → Fin 6 → Finset (Fin 60)) (valid : IsCover s) :
    ∃ picked, CoversWith geometryTables allObligations allCandidates picked ∧ firstGroupIndices s ⊆ picked := by
  let f : Fin 5 × Fin 6 → Nat := fun a => starKey s a.1 a.2
  let picked : Finset Nat := Finset.univ.image f
  have index_lt (a : Fin 5 × Fin 6) : f a < 1720 := by
    unfold f starKey
    have := (starDecoded layout s valid a.1 a.2).1
    have := a.1.isLt
    omega
  have slot_eq (a : Fin 5 × Fin 6) : f a / 344 = a.1.val := by
    unfold f starKey
    have := (starDecoded layout s valid a.1 a.2).1
    omega
  refine ⟨picked, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro index found
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp found
    simp only [allCandidates, Nat.testBit_two_pow_sub_one, decide_eq_true (index_lt a)]
  · intro index found q yes
    obtain ⟨⟨g,t⟩, _, rfl⟩ := Finset.mem_image.mp found
    obtain ⟨p, hp, rfl⟩ := (star_global_bit layout s valid g t q).mp yes
    rw [obligation_bit]
    exact valid.1 (groupAt g) t p hp
  · intro i hi j hj different
    obtain ⟨⟨g,t⟩, _, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨⟨h,u⟩, _, rfl⟩ := Finset.mem_image.mp hj
    have word (a : Fin 5) (b : Fin 6) (p : Nat) :
        (starTable.block 8 60 (f (a,b))).testBit p = true ↔ ∃ q ∈ s (groupAt a) b, q.val = p := by
      rw [show starTable.block 8 60 (f (a,b)) = starWord s a b from (starDecoded layout s valid a b).2]
      exact star_mask_bit _ _
    have same_slot_disjoint (eq : g = h) : Disjoint (s (groupAt g) t) (s (groupAt h) u) := by
      subst h
      exact distinct_stars_same_group s valid g _ _ (fun eq => different (congrArg (fun v => f (g,v)) eq))
    have commonAt (p q : Nat) (neq : p ≠ q)
        (ip : (starTable.block 8 60 (f (g,t))).testBit p = true)
        (iq : (starTable.block 8 60 (f (g,t))).testBit q = true)
        (jp : (starTable.block 8 60 (f (h,u))).testBit p = true)
        (jq : (starTable.block 8 60 (f (h,u))).testBit q = true) : False := by
      obtain ⟨x, hx, xp⟩ := (word g t p).mp ip
      obtain ⟨y, hy, yq⟩ := (word g t q).mp iq
      obtain ⟨xx, hxx, xxp⟩ := (word h u p).mp jp
      obtain ⟨yy, hyy, yyq⟩ := (word h u q).mp jq
      have xeq : xx = x := Fin.ext (xxp.trans xp.symm)
      have yeq : yy = y := Fin.ext (yyq.trans yq.symm)
      subst xx
      subst yy
      by_cases eq : g=h
      · exact Finset.disjoint_left.mp (same_slot_disjoint eq) hx hxx
      · have card := valid.2.2.2 (groupAt g) (groupAt h) t u (fun e => eq (groupAt_inj e))
        have same := Finset.card_le_one.mp card x (Finset.mem_inter.mpr ⟨hx, hxx⟩)
          y (Finset.mem_inter.mpr ⟨hy, hyy⟩)
        exact neq (xp.symm.trans ((congrArg Fin.val same).trans yq))
    refine ⟨compatible _ _ (index_lt (g,t)) (index_lt (h,u)) ?_ commonAt, ?_⟩
    · intro same p on_i
      have eq : g = h := Fin.ext ((slot_eq (g,t)).symm.trans (same.trans (slot_eq (h,u))))
      cases on_j : (starTable.block 8 60 (f (h,u))).testBit p with
      | false => rfl
      | true =>
        obtain ⟨x, hx, xp⟩ := (word g t p).mp on_i
        obtain ⟨y, hy, yp⟩ := (word h u p).mp on_j
        have xy : y = x := Fin.ext (yp.trans xp.symm)
        subst y
        exact (Finset.disjoint_left.mp (same_slot_disjoint eq) hx hy).elim
    · intro q a
      cases b : (geometryTables.starMask (f (h,u))).testBit q with
      | false => rfl
      | true =>
        obtain ⟨p, hp, at_p⟩ := (star_global_bit layout s valid g t q).mp a
        obtain ⟨r, hr, at_r⟩ := (star_global_bit layout s valid h u q).mp b
        have eq : g = h := Fin.ext (by have := p.isLt; have := r.isLt; omega)
        subst h
        have rp : r = p := Fin.ext (by omega)
        subst r
        exact (Finset.disjoint_left.mp (same_slot_disjoint rfl) hp hr).elim
  · intro q on
    obtain ⟨g, p, rfl, hit⟩ := obligation_of_bit q on
    obtain ⟨t, hp, _⟩ := valid.2.2.1 (groupAt g) p hit
    exact ⟨f (g,t), Finset.mem_image_of_mem _ (Finset.mem_univ _),
      (star_global_bit layout s valid g t _).mpr ⟨p, hp, rfl⟩⟩
  · intro i member
    obtain ⟨t, _, equal⟩ := Finset.mem_image.mp member
    refine Finset.mem_image.mpr ⟨(0,t), Finset.mem_univ _, ?_⟩
    change 344 * (0 : Fin 5).val + (directCatalog (groupAt 0)).idxOf
      (pack ((s (groupAt 0) t).image Fin.val)) = i
    simpa only [group_zero, Fin.val_zero, Nat.mul_zero, Nat.zero_add] using equal

end WeightFifteenVerifiedSearch

namespace WeightFifteenVerifiedSearch.Catalogue0

open WeightFifteenLargeCatalog WeightFifteenIndexedSearch

def options : List (Nat × Nat) := [(136, 24), (264, 25), (520, 26), (2056, 27), (4104, 28), (16392, 29), (80, 30), (272, 31), (1040, 32), (2064, 33), (4112, 34), (8208, 35), (96, 36), (160, 37), (544, 38), (1056, 39), (8224, 40), (16416, 41), (1088, 42), (2112, 43), (8256, 44), (16448, 45), (640, 46), (2176, 47), (4224, 48), (8320, 49), (768, 50), (1280, 51), (4352, 52), (16640, 53), (8704, 54), (16896, 55), (5120, 56), (17408, 57), (6144, 58), (10240, 59)]

def expected : List Nat := [1416755628998656, 2542380657934336, 4583349116993536, 4649044936753152, 73192462373355520, 73324335049211904, 289360846440628224, 290552648325660672,
  2332081879252992, 1272152670076928, 1412881568497664, 1417275320041472, 4579475056492544, 4583868808036352, 72137861071110144, 73325332555366400,
  288306245138382848, 290553645831815168, 1284797053796352, 2410422082732032, 1425525952217088, 2551150981152768, 4592119440211968, 4662209011515392,
  73201232696573952, 72216201274589184, 289374010515390464, 288318889522102272, 1698213425840128, 2823838454775808, 5071231632015360, 5075625383559168,
  73746521744474112, 72629617646632960, 289919299563290624, 289919777378402304, 288798001713905664, 291045402407337984, 20275149571883008, 20407022247739392,
  20547751146160128, 18305222019383296, 22522542749122560, 22526936500666368, 22658809176522752, 22659286991634432, 90080928763740160, 90212801439596544,
  306249312831012864, 308496713524445184, 577591205412470784, 578783007297503232, 577868200738291712, 577868678553403392, 576746902888906752, 578994303582339072,
  581034794226286592, 581035272041398272, 648588786489360384, 649644385297760256, 2333198302314496, 1273269093138432, 1414006447276032, 2544304333520896,
  4580599935270912, 4650968612339712, 72138992291676160, 73194523437563904, 288307376358948864, 289362907504836608, 2341968625532928, 1286433167900672,
  2341977081249792, 2412345758318592, 1427170522038272, 2553074656739328, 4593764010033152, 4664132687101952, 72147756273106944, 72147762614894592,
  73203293760782336, 72218124950175744, 288320540433711104, 289376071579598848, 1695455788400640, 1699849539944448, 1695464244117504, 2825762130362368,
  5073155307601920, 5077549059145728, 73748644129406976, 72631541322219520, 288799925389492224, 291047326082924544, 18161735483523072, 20409136176955392,
  20277210636091392, 18161750281027584, 18302472837660672, 20549873531092992, 18302479179448320, 18306872930992128, 22524603813330944, 22528997564874752,
  90082989827948544, 90214930166317056, 306251373895221248, 308498774588653568, 576537720533286912, 578785121226719232, 576537735330791424, 577593266476679168,
  576748826564493312, 578996227257925632, 648590915216080896, 649646446361968640, 1302406151274496, 2428031180210176, 1443143505412096, 2568768534347776,
  4609736993406976, 4680105670475776, 73218850249768960, 72233825169571840, 288336513417084928, 289392044562972672, 290517532203286528, 290517669591908352,
  2358461299949568, 1302925842317312, 2358469755666432, 2428838432735232, 1443663196454912, 2569567331155968, 4610256684449792, 4680625361518592,
  72164248947523584, 72164255289311232, 73219786435198976, 72234617624592384, 288337033108127744, 289392564254015488, 1724592846536704, 2850217875472384,
  1724601302253568, 2850226331189248, 5102013259972608, 5102292365737984, 72656005523046400, 72656011864834048, 288828789683650560, 288829062447628288,
  20301528992579584, 18190872541659136, 20301537448296448, 18190887339163648, 18331609895796736, 18331616237584384, 22553324377079808, 22553740871467008,
  90107316640153600, 90107322981941248, 306280100800757760, 306280510953357312, 577621978584711168, 576566857591422976, 576566872388927488, 577622403534815232,
  578747891175129088, 578748028563750912, 576777690858651648, 576777963622629376, 580999678103912448, 580999815492534272, 648553670366986240, 648553807755608064,
  9086948475928576, 9152644295688192, 9293381649825792, 9298054507134976, 81135265250279424, 81073761251491840, 81073898640113664, 81205633927348224,
  297242145318764544, 297242282707386368, 9083074415427584, 9087468166971392, 9083082871144448, 9153451548213248, 9294180446633984, 9298574198177792,
  81136262756433920, 81206631433502720, 9095718799147008, 9165808370450432, 9095727254863872, 9166095931932672, 9306545724588032, 9306824830353408,
  81082531574710272, 81082668963332096, 297255309393526784, 297255446782148608, 9574830990950400, 9579224742494208, 9574839446667264, 9579512303976448,
  81628019331956736, 81627820622610432, 297800598441426944, 297801076256538624, 27026142108057600, 27030535859601408, 27162408535457792, 27162886350569472,
  27026150563774464, 27030960809705472, 27303145889595392, 27303623704707072, 99079330449063936, 99079269128339456, 315252046947155968, 315252524762267648,
  585538393585221632, 585538871400333312, 585472504290607104, 585472641679228928, 585749499616428032, 585749977431539712, 657525684175896576, 657525821564518400,
  38289564992798720, 38421437668655104, 38562175022792704, 36319652237803520, 40536966625755136, 40541776871686144, 108095358982160384, 108227231658016768,
  324263743049433088, 326511076080353280, 36175034481377280, 38422435174809600, 38290509633945600, 36175049278881792, 36315771835514880, 38563172528947200,
  36315778177302528, 36320171928846336, 40537902811185152, 40542296562728960, 108096288825802752, 108228229164171264, 324264672893075456, 326512073586507776,
  38298335316017152, 36187678865096704, 38298343771734016, 36187693662601216, 36328416219234304, 36328422561021952, 40550130700517376, 40550547194904576,
  108104122963591168, 108104129305378816, 324276907124195328, 324277317276794880, 38843624363917312, 36601095237140480, 38843632819634176, 36601110034644992,
  41095419748417536, 41095897563529216, 108649412011491328, 108649418353278976, 324822196172095488, 324822673987207168, 612494087223771136, 614741487917203456,
  612494102021275648, 614741435052195840, 612771097347096576, 612771575162208256, 616993221980979200, 616993699796090880, 684547281906565120, 684547214244052992,
  145250056142848000, 145381928818704384, 145522666172841984, 144405768416788480, 148689259660836864, 148627755662049280, 148627893050671104, 148759628337905664,
  432416036084514816, 433471567230402560, 144195454840602624, 145382926324858880, 144195469638107136, 145251000783994880, 145523663678996480, 144406560871809024,
  148690257166991360, 148760625844060160, 432417033590669312, 433472564736557056, 145258826466066432, 144273795044081664, 145258834921783296, 144273809841586176,
  144414532398219264, 144414538740006912, 148636525985267712, 148636663373889536, 432363296067158016, 432363433455779840, 145804115513966592, 144687211416125440,
  145804123969683456, 144687226213629952, 149182013742514176, 149181815033167872, 432908585115058176, 432908790166192128, 162138522533232640, 162270395209089024,
  162138537330737152, 162270410006593536, 162411132563226624, 162411138905014272, 166633324859621376, 166633263538896896, 450360101283299328, 450360033620787200,
  720646380258852864, 721701979067252736, 720646395056357376, 721701926202245120, 720857486290059264, 720857691341193216, 725079678586454016, 725079815975075840]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000000 in
lemma tableAgrees : (List.range 344).map (fun i => starTable.block 8 60 (344*0+i)) = expected := by rfl

lemma complete : (List.range 344).map (fun i => starTable.block 8 60 (344*(0 : Fin 5).val+i)) =
    directCatalog (groupAt 0) := by
  rw [group_zero, WeightFifteenConcreteGenerators.direct_first_catalogue]
  exact tableAgrees

end WeightFifteenVerifiedSearch.Catalogue0

namespace WeightFifteenVerifiedSearch.Catalogue1

open WeightFifteenLargeCatalog WeightFifteenIndexedSearch

def options : List (Nat × Nat) := [(10, 8), (34, 9), (66, 10), (130, 11), (1026, 12), (4098, 14), (12, 16), (20, 17), (68, 18), (260, 19), (516, 20), (8196, 22), (136, 24), (264, 25), (520, 26), (4104, 28), (80, 30), (272, 31), (1040, 32), (4112, 34), (8208, 35), (96, 36), (160, 37), (544, 38), (1056, 39), (8224, 40), (1088, 42), (8256, 44), (640, 46), (4224, 48), (8320, 49), (768, 50), (1280, 51), (4352, 52), (8704, 54), (5120, 56)]

def expected : List Nat := [70441796386816, 1125972942274560, 70919611498496, 1126450757386240, 4537704267776, 4675092889600, 2251938397700096, 2252075786321920,
  70439883771904, 1126038692171776, 1125973193918464, 1126041913394176, 70920920105984, 1126451009030144, 4675344533504, 74769210802688,
  2252076037965824, 2322169904235008, 70454681276416, 1125985827164160, 70935717610496, 1126466863498240, 4690142038016, 74784008307200,
  1130315154194944, 1130452576370944, 2251885784336384, 2251954503812096, 2252091892433920, 2322254461403392, 281545914978304, 281750966112256,
  281754187334656, 1407447902191872, 282026951312384, 1407925717303552, 285875242009088, 286150052806912, 2533275935441408, 2533550746239232,
  4503738211373056, 4503875599994880, 4503672713119744, 4503741432595456, 4503878821217280, 4574041390186752, 4504150528231424, 4574519205298432,
  72057664976193536, 72057733695669248, 72057870027327488, 72057871084291072, 72127963893596672, 72128033653260544, 73183495039484416, 73183632461660416,
  70952893562880, 1126484039450624, 4569879822336, 4569912852480, 4707301474304, 1130469752127488, 2251902910742528, 2251971679764480,
  2252109068386304, 2322271637159936, 70472092356608, 1126071974236160, 70953128690688, 1126484291094528, 4707553118208, 74801419387392,
  2251903162386432, 2251971881862144, 2252109320030208, 2322203186299392, 281578090532864, 281578123563008, 281784248176640, 1407477962838016,
  282059126866944, 282059159897088, 1407958999172096, 1407958999367936, 285907417563648, 285907450593792, 286182261391616, 1411807289868800,
  2533377870659840, 2533309217505792, 2533584028107776, 2533584028303616, 4503702724415488, 4503771493437440, 4503908882059264, 4574071450832896,
  4504183760749568, 4504183810295808, 4574552487166976, 4574552487362816, 4508032051446272, 4508169473622272, 4508306911594496, 4578400777863680,
  72057697151748096, 72057765871223808, 72057697184778240, 72057765904253952, 72057903292875776, 72057903309391872, 72128065861845248, 72127997175661056,
  73183597024053248, 73183528321548800, 73183665743528960, 73183665743724800, 71472584605696, 1127003730493440, 5499723464704, 75866336018432,
  75868449882112, 1131397481906176, 2252900416897024, 2323269143314432, 71469598511104, 71470671990784, 71472819733504, 1127003982137344,
  5499975108608, 1131397733550080, 2252900668540928, 2323268338058240, 71485469495296, 1127016615383040, 5514772613120, 5514805643264,
  75883482710272, 1131414644918272, 2252916523009024, 2252916572555264, 2323285249426432, 2323285249622272, 282575596687360, 282575629717504,
  282576703197184, 1408475468992512, 282578817909760, 282578850939904, 1408478690214912, 1408478690410752, 286974683382016, 1412872441823488,
  2534375376814336, 2534374369264640, 4504700230569984, 4575068956987392, 4504703451792384, 4504703501338624, 4575072178209792, 4575072178405632,
  4509097252751360, 4579465929818368, 72058694657902592, 72058695714866176, 72058694690932736, 72058695764412416, 72129063367999744, 72129062327419904,
  72129064441283584, 72129064441479424, 73184594530207744, 73184593473307648, 17733954584576, 17733987614720, 17871376236544, 1143633826889728,
  18144107184128, 88510719737856, 88512833601536, 1144041865625600, 2269529505939456, 2269666894561280, 17732041969664, 1143629800411136,
  17871627880448, 87965494149632, 18144358828032, 1144042117269504, 2269667146205184, 2339761012474368, 17746839474176, 17746872504320,
  17884261126144, 1143646711779328, 18159156332544, 18159189362688, 88527866429696, 1144059028637696, 2269409197425152, 2269546619601152,
  2269684057573376, 2339777923842560, 299342074351616, 299344188215296, 299071492325888, 299071525356032, 299346336153856, 1424971364631040,
  299619067101440, 1425516825542912, 2550867043680768, 2551141854478592, 4521329319612416, 4521466708234240, 4521196126208512, 4521333548384512,
  4521470986356736, 4591564852625920, 4521741636470784, 4592110313537792, 72075188389282304, 72075325811458304, 72075461135566848, 72075463249430528,
  72145555001836032, 72145557115699712, 73201086147723776, 73201223569899776, 563023002484736, 563023035514880, 563229160128512, 1688922874789888,
  563500817596416, 563500850626560, 563501924106240, 1689400689901568, 567622911541248, 567625025404928, 2814818553839616, 2815025718837248,
  563021089869824, 563226174033920, 563227247513600, 1688918848311296, 563229395256320, 1688854423929344, 563502126203904, 1689399884645376,
  567350416900608, 1693248175342080, 2814751110332928, 2815024913581056, 563035887374336, 563035920404480, 563242045018112, 1688935759679488,
  563516923708416, 563516956738560, 1689416796013568, 1689416796209408, 567365214405120, 567365247435264, 567640058233088, 1693265086710272,
  2814835667501312, 2814767014347264, 2815041824949248, 2815041825145088, 5066618367512576, 5066825532510208, 5066622596284672, 5066553943130624,
  5066828753732608, 5066828753928448, 5067100411396352, 5067099403846656, 5070947694543360, 5071222505341184, 72620545099694592, 72620614859358464,
  72620545132724736, 72620546206204416, 72620819943522560, 72620818902942720, 72620821016806400, 72620821017002240, 73746444971999744, 73746512617799936,
  18014471541243904, 18014540277235712, 18014949356355584, 18014950429835264, 18018934028648448, 18018936142512128, 20266267059568640, 20266336835944448,
  18014537291141120, 18014538364620800, 18014471792887808, 18014540512363520, 18014949607999488, 18014950681479168, 20266267311212544, 20266336030688256,
  18014484426133504, 18014553162125312, 18014965462467584, 18014965478983680, 18018813753164288, 18018951175340288, 20266284222580736, 20266215520076288,
  20266352942056448, 20266352942252288, 18295942239358976, 18295944353222656, 18295946501161216, 18295877814977024, 18296424316272896, 18296423275693056,
  18296425389556736, 18296425389752576, 18300271566389760, 18300273680253440, 20547674373685760, 20547742019485952, 22518066873241600, 22518136649617408,
  22518071151364096, 22518002448859648, 22518139870839808, 22518139871035648, 22518548966475776, 22518547909575680, 22522396200272384, 22522533622448384,
  90071993638453760, 90072131060629760, 90072061300574208, 90072130020049920, 90072063414437888, 90071994711933440, 90072132133913600, 90072132134109440]

set_option maxRecDepth 20000 in
lemma options_agree : indexOptions 9 = options := by decide +kernel

set_option maxHeartbeats 300000000 in
set_option maxRecDepth 100000 in
lemma arithmetic : enumerateMasks options 60 14334 = expected := by rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000000 in
lemma tableAgrees : (List.range 344).map (fun i => starTable.block 8 60 (344*1+i)) = expected := by rfl

lemma complete : (List.range 344).map (fun i => starTable.block 8 60 (344*(1 : Fin 5).val+i)) =
    directCatalog (groupAt 1) := by
  change (List.range 344).map (fun i => starTable.block 8 60 (344*1+i)) =
    enumerateMasks (indexOptions 9) 60 (vertexMask 9)
  rw [options_agree]
  change _ = enumerateMasks options 60 14334
  rw [arithmetic]
  exact tableAgrees

end WeightFifteenVerifiedSearch.Catalogue1

namespace WeightFifteenVerifiedSearch.Catalogue2

open WeightFifteenLargeCatalog WeightFifteenIndexedSearch

def options : List (Nat × Nat) := [(34, 9), (130, 11), (1026, 12), (2050, 13), (4098, 14), (16386, 15), (20, 17), (260, 19), (516, 20), (2052, 21), (8196, 22), (16388, 23), (272, 31), (1040, 32), (2064, 33), (4112, 34), (8208, 35), (160, 37), (544, 38), (1056, 39), (8224, 40), (16416, 41), (640, 46), (2176, 47), (4224, 48), (8320, 49), (768, 50), (1280, 51), (4352, 52), (16640, 53), (8704, 54), (16896, 55), (5120, 56), (17408, 57), (6144, 58), (10240, 59)]

def expected : List Nat := [1267204335108096, 2392829364043776, 1407933233528832, 2533558262464512, 4574526721523712, 4644616292827136, 73183639977885696, 72198608555900928,
  289356417796702208, 288301296803414016, 1407959001235456, 2533584030171136, 4574552489230336, 4644921232359424, 73183665745592320, 72198640764485632,
  288301329011998720, 290482347765170176, 2323285251489792, 2393653994618880, 1408478692278272, 2534382893039616, 4575072180273152, 4645440923402240,
  72129064443346944, 72129070884225024, 72199433186476032, 73325330944917504, 288301848703041536, 290553644221366272, 1689416798076928, 2815041827012608,
  5066828755795968, 5067107927621632, 72620821018869760, 72620827459747840, 288793605278564352, 288793878009511936, 289919775767953408, 291045400796889088,
  20266352944119808, 18155702934077440, 18296425391620096, 18296431832498176, 22518139872903168, 22659285381185536, 90072132135976960, 90072138576855040,
  306244916395671552, 308496711913996288, 576531687983841280, 578712706737012736, 576742506453565440, 576742779184513024, 577868676942954496, 578994301971890176,
  580964493665796096, 581035270430949376, 648518485928869888, 649644383687311360, 1267221519155200, 2392846548090880, 1407959007502336, 2533584036438016,
  4574552495497216, 4644646361763840, 73183665751859200, 73324265801253376, 289356447865638912, 289356860182497280, 290482485211432960, 290552579077702144,
  2323276667830272, 1267741210198016, 2323285257756672, 1267754095087616, 1408478698545152, 1408482993508352, 4575072186540032, 4575076481503232,
  72129064449613824, 73184602054723584, 288301846563393536, 289357379873540096, 1689408214417408, 2815033243353088, 1689416804343808, 2815041833279488,
  5066828762062848, 5066833057026048, 72620821025136640, 73746452496515584, 288793603138916352, 289919230315332096, 20266344360460288, 18155687909539840,
  20266352950386688, 20406952999780864, 18296425397886976, 20547681898201600, 22518139879170048, 22518144174133248, 22518556490991616, 22658739928564224,
  90072132142243840, 90212732191638016, 306244914256023552, 306245326572881920, 577586793952591872, 576531672959303680, 577586806837481472, 577587219154339840,
  578712844183275520, 578782938049544704, 576742504313917440, 577868131490333184, 580964631112058880, 581034724978328064, 648518623375132672, 648588717241401856,
  2324376175263744, 1268840717631488, 2324384765190144, 1268853602521088, 1409578205978624, 1409582500941824, 4576171693973504, 4576175988936704,
  72130163957047296, 73185701562157056, 288302946070827008, 289358479380973568, 2324401942970368, 2394770686099456, 2535508174446592, 1409608268648448,
  4576201756643328, 4646570499772416, 72130196165632000, 73185727329863680, 288302978279411712, 290484409349441536, 1691053180600320, 2816957381361664,
  2816965971288064, 1691066065489920, 5068752900071424, 5068757195034624, 72622745163145216, 73748642921586688, 288795527276924928, 289921425035366400,
  18157339316600832, 20409134834925568, 20268414528391168, 18157352201490432, 18298076804947968, 20549872323272704, 18298074659033088, 18298081099911168,
  22520201457174528, 22660934648598528, 90074193720248320, 90074200161126400, 306246977979942912, 308498773498267648, 576533324366364672, 578785119884689408,
  576533337251254272, 578714768321284096, 576744428451926016, 577870326210367488, 581036919698362368, 580966555250067456, 648520547513141248, 649646445271582720,
  9078126348877824, 9148215920181248, 9078134938804224, 9148228805070848, 9288953408528384, 9288957703491584, 81065076764706816, 81135170630976000,
  297237854583523328, 297307948449792512, 9078152116584448, 9148520859713536, 9289258348060672, 9288983471198208, 81064965092417536, 81065102532413440,
  81135196398682624, 81205565141811712, 297237747206197248, 297238159523055616, 9078671807627264, 9149040550756352, 9078684692516864, 9149053435645952,
  9289778039103488, 9289782334066688, 81136261548613632, 81065901395281920, 297309043662393344, 297238679214098432, 9570428383150080, 9570707554975744,
  9570716144902144, 9570441268039680, 81628018124136448, 81627751837073920, 297800800237916160, 297800529655890432, 27021739500257280, 27162885008539648,
  27021752385146880, 27022164702005248, 27303622496886784, 27303077037998592, 99079329241243648, 99219929290637824, 315252111355023360, 315252523671881728,
  585468093293150208, 585538870058303488, 585468106178039808, 585468518494898176, 585749701412917248, 585749430830891520, 657525820474132480, 657595914340401664,
  38280742865747968, 36170086414827520, 38280751455674368, 38421351505068544, 36310823903174656, 38562080403489280, 40532538384457728, 40532542679420928,
  40532954996279296, 40673138433851904, 108086530647531520, 108227130696925696, 324259312761311232, 324259725078169600, 38280768633454592, 36170118623412224,
  36310856111759360, 38562106171195904, 40532568447127552, 40532980763985920, 108086562856116224, 108227162905510400, 324259344969895936, 324259757286754304,
  36170638314455040, 38422433832779776, 38281713526245376, 36170651199344640, 36311375802802176, 38563171321126912, 36311373656887296, 36311380097765376,
  40533500455028736, 40674233646452736, 108087492718102528, 108087499158980608, 324260276977797120, 326512072496121856, 36592298877796352, 36592305318674432,
  36592313908600832, 38843563968037376, 41095896355708928, 41095350896820736, 108649343159894528, 108649349600772608, 324822127419589120, 327073922937913856,
  612489691056848896, 614741486575173632, 612489703941738496, 612490116258596864, 612771028594590208, 615022824112914944, 616993286388846592, 616993698705704960,
  145241234015797248, 144256202593812480, 145241242605723648, 145381842655117824, 144396940082159616, 145522571553538560, 148619071175264256, 148689165041533440,
  432345841257154560, 432415935123423744, 145241259783503872, 144256234802397184, 144396972290744320, 145522597321245184, 148618959502974976, 148619096942970880,
  148689190809240064, 148759559552369152, 432345873465739264, 432415967332008448, 144186658481258496, 144186664922136576, 144257027224387584, 145382924982829056,
  144186673512062976, 145242204676294656, 144397764712734720, 145523662471176192, 148690255959171072, 148619895805839360, 432346665887729664, 433472563646171136,
  144678415056781312, 144678421497659392, 144678430087585792, 145804055118086656, 149182012534693888, 149181746247631360, 432908516329521664, 434034414087963136,
  162129726173888512, 162129732614766592, 162129741204692992, 162270341254087168, 162411063711629824, 162411070152507904, 166633323651801088, 166773923701195264,
  720576079966781440, 721701977725222912, 720576232437581824, 720646326303851008, 720857417504522752, 721983315262964224, 725079814884689920, 725149908750959104]

set_option maxRecDepth 20000 in
lemma options_agree : indexOptions 14 = options := by decide +kernel

set_option maxHeartbeats 300000000 in
set_option maxRecDepth 100000 in
lemma arithmetic : enumerateMasks options 60 32694 = expected := by rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000000 in
lemma tableAgrees : (List.range 344).map (fun i => starTable.block 8 60 (344*2+i)) = expected := by rfl

lemma complete : (List.range 344).map (fun i => starTable.block 8 60 (344*(2 : Fin 5).val+i)) =
    directCatalog (groupAt 2) := by
  change (List.range 344).map (fun i => starTable.block 8 60 (344*2+i)) =
    enumerateMasks (indexOptions 14) 60 (vertexMask 14)
  rw [options_agree]
  change _ = enumerateMasks options 60 32694
  rw [arithmetic]
  exact tableAgrees

end WeightFifteenVerifiedSearch.Catalogue2

namespace WeightFifteenVerifiedSearch.Catalogue3

open WeightFifteenLargeCatalog WeightFifteenIndexedSearch

def options : List (Nat × Nat) := [(17, 0), (33, 1), (129, 2), (257, 3), (513, 4), (1025, 5), (10, 8), (34, 9), (66, 10), (130, 11), (1026, 12), (2050, 13), (12, 16), (20, 17), (68, 18), (260, 19), (516, 20), (2052, 21), (136, 24), (264, 25), (520, 26), (2056, 27), (80, 30), (272, 31), (1040, 32), (2064, 33), (96, 36), (160, 37), (544, 38), (1056, 39), (1088, 42), (2112, 43), (640, 46), (2176, 47), (768, 50), (1280, 51)]

def expected : List Nat := [138547306528, 70884794400, 138580336672, 139653816352, 275968958496, 277042438176, 70437497348128, 70439611211808,
  1125968643235872, 1126038419611680, 73031753744, 141767745552, 73032278024, 73049055236, 141801299976, 73082085380,
  279189921800, 279206699012, 70441758695432, 70373072969730, 1125972921360388, 1125904218857474, 550846865424, 551920345104,
  550847389704, 550864166916, 550897197060, 551970676740, 70919573807112, 70918533816321, 1126450736472068, 1126449679704065,
  4535519158288, 4537633021968, 4535520075777, 4400211828738, 4535552712712, 4535553105921, 4672941334536, 4672941727745,
  4672958111748, 4675071975428, 74766824382466, 74768938246146, 1130297970270210, 1130435392380929, 2251868550078480, 2251938326454288,
  2251800905261058, 2251868550995969, 2251868600410116, 2251937320017921, 2252075765407748, 2252074708639745, 2322169631678466, 2322237277413377,
  70936168480, 139655644192, 275987302432, 277044266016, 70369853571616, 70439613235488, 1125900999459360, 1126038421635360,
  138548350992, 70885838864, 138581905416, 70936170500, 275970527240, 275987304452, 70369853575170, 70437499310081,
  1125900999462914, 1125968645197825, 73050097680, 141769573392, 73083652104, 141803127816, 279191749640, 279208526852,
  70441760719112, 70373074797570, 1125972923384068, 1125904220685314, 550865209360, 551922172944, 550898763784, 551972504580,
  70919575830792, 70918535644161, 1126450738495748, 1126449681531905, 4400212869648, 4537635045648, 4400263201284, 4400263202818,
  4672960071681, 4675073999108, 74766826340865, 74768940269826, 1130297972228609, 1130435394404609, 2251800906301968, 2251938328477968,
  2251800956633604, 2251800956635138, 2251868602370049, 2251937321845761, 2252075767431428, 2252074710467585, 2322169633702146, 2322237279437057,
  71002228768, 139721704480, 276086392864, 277159872544, 70369952662048, 70371026141728, 1125968760670240, 1126037480145952,
  138647441424, 139720921104, 138647965704, 71002230788, 276086394884, 277159874564, 70437598007304, 70369952665602,
  70437598400513, 70371026145282, 1125968760672260, 1126037480280065, 73149188112, 141868663824, 73149712392, 141869188104,
  279307356168, 279307617284, 70373173625352, 70373173888002, 1125904336290308, 1125904336291842, 550964299792, 552037779472,
  550964824072, 552038564868, 70918634341384, 70918634734593, 1126449797006340, 1126449797138433, 4400329261572, 4400329263106,
  4673058768904, 4673059162113, 74766925038088, 74766925431297, 1130298087703044, 1130298087704578, 2251868667512848, 2251937386988560,
  2251801022693892, 2251801022695426, 2251868668430337, 2251937387906049, 2252074825942020, 2252074826074113, 2322168692212738, 2322168692343297,
  77344016416, 146063492128, 77377046560, 146096522272, 283485144096, 283501660192, 70446054113568, 70377367929376,
  1125977216321568, 1125908513817120, 1126045935797280, 1126045935993120, 77326716944, 146062708752, 77327241224, 77344018436,
  146096263176, 77377048580, 283484885000, 283501662212, 70446053658632, 70377367932930, 1125977216323588, 1125908513820674,
  558363051024, 558379567120, 558363575304, 558380352516, 558413121544, 558413382660, 70927089992712, 70927090188552,
  1126458252657668, 1126458252853508, 4406653747728, 4544075923728, 4406654272008, 4544076448008, 4406671049220, 4406671050754,
  4406704079364, 4406704080898, 4681514420232, 4681514877188, 74775380689416, 74775381147906, 1130306543354372, 1130306543355906,
  2251877123164176, 2251808420659728, 2251945842639888, 2251945842835728, 2251877124145412, 2251808421446658, 2251808470991364, 2251808470992898,
  2252083281593348, 2252083281789188, 2322177147864066, 2322177148059906, 8798258332192, 8935680508192, 9071004616736, 9073118480416,
  79164870885920, 79166984749600, 1134696016773664, 1134833438949664, 8933565665296, 8935679528976, 8933566582785, 8798258335746,
  8933599219720, 8933599612929, 9070987841544, 9070988234753, 9071004618756, 9073118482436, 79164870889474, 79166984753154,
  1134696016777218, 1134833438887937, 8800405291536, 8937827467536, 8800405815816, 8937827991816, 8800422593028, 8800422594562,
  8800455623172, 8800455624706, 9075265964040, 9075266420996, 79169132233224, 79169132691714, 1134700294898180, 1134700294899714,
  9345882523664, 9347996387344, 9345883441153, 9347997368580, 9345916078088, 9345916471297, 79714593145096, 79714593538305,
  1135245755810052, 1135245755746305, 2260595923616272, 2260733345792272, 2260595924533761, 2260733346709761, 2260595973947908, 2260595973949442,
  2260870784745732, 2260870784681985, 2330964651016450, 2330964650951169, 140738596700704, 140808356364576, 140738629730848, 140739703210528,
  141013440528672, 141012399948832, 141014513812512, 141014514008352, 1266638469005856, 1266706114806048, 140806241521680, 140808355385360,
  140738596704258, 140806242439169, 140806275076104, 140738629734402, 140806275469313, 140739703214082, 141013440073736, 141012400082945,
  1266638469009410, 1266706114744321, 140810503323920, 140741817139728, 140810503848200, 140741817926658, 140741850694152, 140741850956802,
  141016661296136, 141016661491976, 1266641690231810, 1266641690427650, 141288318435600, 141287277855760, 141289391719440, 141289391915280,
  141288318959880, 141287278773249, 141287311410184, 141287311803393, 1267187151078401, 1267187151274241, 145135568552464, 145137682416144,
  145135569469953, 145137683398914, 145135602106888, 145135602500097, 145410412904712, 145410413297921, 1271035441840386, 1271035441775105,
  2392538375848464, 2392606021648656, 2392538376831234, 2392606022566145, 2392537369281538, 2392537369412097, 2392812180014081, 2392812180209921]

set_option maxRecDepth 20000 in
lemma options_agree : indexOptions 4 = options := by decide +kernel

set_option maxHeartbeats 300000000 in
set_option maxRecDepth 100000 in
lemma arithmetic : enumerateMasks options 60 4095 = expected := by rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000000 in
lemma tableAgrees : (List.range 344).map (fun i => starTable.block 8 60 (344*3+i)) = expected := by rfl

lemma complete : (List.range 344).map (fun i => starTable.block 8 60 (344*(3 : Fin 5).val+i)) =
    directCatalog (groupAt 3) := by
  change (List.range 344).map (fun i => starTable.block 8 60 (344*3+i)) =
    enumerateMasks (indexOptions 4) 60 (vertexMask 4)
  rw [options_agree]
  change _ = enumerateMasks options 60 4095
  rw [arithmetic]
  exact tableAgrees

end WeightFifteenVerifiedSearch.Catalogue3

namespace WeightFifteenVerifiedSearch.Catalogue4

open WeightFifteenLargeCatalog WeightFifteenIndexedSearch

def options : List (Nat × Nat) := [(33, 1), (257, 3), (513, 4), (1025, 5), (4097, 6), (8193, 7), (10, 8), (34, 9), (66, 10), (1026, 12), (2050, 13), (4098, 14), (12, 16), (68, 18), (260, 19), (516, 20), (2052, 21), (8196, 22), (264, 25), (520, 26), (2056, 27), (4104, 28), (96, 36), (544, 38), (1056, 39), (8224, 40), (1088, 42), (2112, 43), (8256, 44), (768, 50), (1280, 51), (4352, 52), (8704, 54), (5120, 56), (6144, 58), (10240, 59)]

def expected : List Nat := [4672960086144, 2251868602384512, 1126449797152896, 4673059176576, 2251868668444800, 2252074826088576, 9345883455616, 9345916485760,
  1135245755760768, 2260870784696448, 1126449931362432, 4673193386112, 2251868802654336, 2252074960298112, 1125968896856192, 1126449933190272,
  1130298223886976, 2252074962125952, 9071239893120, 2260596176192128, 4504149450563712, 4508272551862400, 4503668416057472, 4504149452391552,
  4507997743088256, 4508272553886080, 4503668482117760, 4503874639761536, 4504149518451840, 4507997809148544, 4512670598369408, 4512945477255552,
  72057662792016000, 72057662825046144, 72057868949659776, 73183562664321152, 72057868951487616, 73183562666344832, 72057869050578048, 73183494079251072,
  72066390165553792, 72066390198583936, 72066665009381760, 73192290037858944, 288230444905795712, 288230444938825856, 288230651063439488, 289356344778100864,
  288230925942129792, 288230925975159936, 289356825814434944, 289356825814630784, 288234774232826496, 288234774265856640, 288235049076654464, 289360674105131648,
  290482244685922688, 290482176032768640, 290482450843370624, 290482450843566464, 4672962175040, 2251868604473408, 1125968764735552, 1126449801069632,
  1130298091766336, 2252074830005312, 9071008682048, 1135245759873344, 2260595978011200, 2260870788809024, 1125968764747808, 4673062846472,
  1130298091782146, 2251868671590416, 9071008694304, 9345886601232, 9345920155656, 2260595978027010, 1125968898957344, 4673197056008,
  1130298225991682, 2251868805799952, 1134696272495136, 9071243563016, 1134696272498690, 2260596179337744, 4503668418158624, 4507997745192962,
  4503874643690528, 4503668485263376, 4504149521597456, 4507997812294160, 4512395791696416, 4512670602494240, 4512395791699970, 4512945480401168,
  72057662795161616, 72057662828716040, 72057869054247944, 73183494083183618, 72066390168699408, 72066390202253832, 72066665013051656, 73192290041987330,
  288230651067368480, 289356344782225696, 288230444908941328, 288230444942495752, 288230925945275408, 288230925978829832, 288234774235972112, 288234774269526536,
  288235049080324360, 289360674109260034, 290482244689068304, 290482176036701186, 5497592750144, 5497625780288, 1131397465055296, 2252899392692288,
  1131397467078976, 2252899394520128, 1126999552954432, 2252899460580416, 9895639257152, 9895672287296, 1135795511562304, 2261695419384128,
  5497593806864, 5497627361288, 1126999552966688, 5497692897296, 5497693421576, 2252899459809296, 9895639269408, 9895672299552,
  1135795511574560, 2261695418417168, 1126999687176224, 5497827106832, 5497827631112, 2252899594018832, 1126999689004064, 2252899595846672,
  9895873613840, 9895874138120, 4504699206377504, 4509097185583120, 4504699208205344, 4509097187606800, 4504699274265632, 4504699273482256,
  4513495233069344, 4513495232090128, 72058693583380496, 72058693616934920, 72058693585208336, 72058693618762760, 72058693684298768, 72058693684823048,
  72067489643102480, 72067489643626760, 288231475697943584, 288231475730973728, 289357375570248736, 289357375570444576, 288231475697160208, 288231475730714632,
  288235873710375184, 288235873710899464, 290483275477091344, 290483275477287184, 18141976469568, 18142009499712, 1144041848774720, 2269666877710400,
  17867099607104, 1144041850798400, 2269392068936256, 2269666879734080, 17867198697536, 2269392134996544, 17867099619360, 18141977526288,
  18142011080712, 2269392068952066, 17867198709792, 18142076616720, 18142077141000, 2269392135012354, 17867332919328, 18142210826256,
  18142211350536, 2269392269221890, 1143492363420192, 17867334488072, 1143492363423746, 2269392270262800, 4521466691395616, 4521741569302544,
  4521191882621472, 4521466693419296, 4521191882625026, 4521741571326224, 4521191948681760, 4521191948685314, 72075186258583554, 72075186291613698,
  72075461101953032, 73201086130888706, 72075186259624464, 72075186293178888, 72075461103976712, 73201086132912386, 72075186358714896, 72075186359239176,
  288247968372359712, 288247968405389856, 288248243216187680, 289373868244664864, 288247968372363266, 288247968405393410, 288248243215732744, 289373868244668418,
  288248518094094608, 288248518094618888, 290499768151507472, 290499768152490242, 18014948299120704, 20266267042717760, 18014467264614464, 18014948300948544,
  18018796591645248, 20266267044741440, 18014467363704896, 18014948400038976, 18018796690735680, 20266198457647680, 18023744358842688, 20274994416255552,
  18014467264626720, 18018796591661058, 18014467363717152, 18014948399792136, 18018796690751490, 20266198457663490, 18023744358400008, 20274994416271362,
  18014467497926688, 18014948534001672, 18018796824961026, 20266198591873026, 18014467499495432, 18014948535829512, 18018796826526216, 20266198593700866,
  18023194871464480, 18023194871468034, 22518066856402976, 22522396183437314, 22518066858426656, 22522396185460994, 22517998271332896, 22517998271336450,
  22526794229940768, 22526794229944322, 90072061266960392, 90071992581234690, 90072061268984072, 90071992583062530, 90071992681890312, 90071992682152962,
  90080788640498184, 90080788640956674, 306244843381195040, 306244774695010848, 306244843380740104, 306244774695014402, 306245324417074184, 306245324417270024,
  306249172707770888, 306249172708229378, 308496574474945538, 308496574475141378, 576460821057507392, 576460821090537536, 576461027215151168, 577586720929812544,
  576461302093841472, 576461302126871616, 577587201966146624, 577587201966342464, 576465150384538176, 576465150417568320, 576465425228366144, 577591050256843328,
  578712620837634368, 578712552184480320, 578712826995082304, 578712826995278144, 576460821057519648, 576460821090549792, 576461027215163424, 577586720929824800,
  576461302093070352, 576461302126624776, 576465150384553986, 576465150417584130, 576465425227923464, 577591050256859138, 578712620836667408, 578712552184496130,
  576461027450291232, 577586652478964256, 576460821291864080, 576460821292388360, 576461027450032136, 577586652478967810, 576461302328198160, 576461302328722440,
  576465150618894864, 576465150619419144, 578712552385806864, 578712552386593794, 580964420651319584, 580964351998165536, 580964626808767520, 580964626808963360,
  580964420650340368, 580964351998169090, 580964901686674448, 580964901686870288, 580968749977371152, 580968749978353922, 648518415061352720, 648518346375168528,
  648518415061877000, 648518346375955458, 648518346408722952, 648518346408985602, 648518621219324936, 648518621219520776, 649644246248260610, 649644246248456450]

set_option maxRecDepth 20000 in
lemma options_agree : indexOptions 7 = options := by decide +kernel

set_option maxHeartbeats 300000000 in
set_option maxRecDepth 100000 in
lemma arithmetic : enumerateMasks options 60 16239 = expected := by rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000000 in
lemma tableAgrees : (List.range 344).map (fun i => starTable.block 8 60 (344*4+i)) = expected := by rfl

lemma complete : (List.range 344).map (fun i => starTable.block 8 60 (344*(4 : Fin 5).val+i)) =
    directCatalog (groupAt 4) := by
  change (List.range 344).map (fun i => starTable.block 8 60 (344*4+i)) =
    enumerateMasks (indexOptions 7) 60 (vertexMask 7)
  rw [options_agree]
  change _ = enumerateMasks options 60 16239
  rw [arithmetic]
  exact tableAgrees

end WeightFifteenVerifiedSearch.Catalogue4

/- A first-group partition can be traversed by covering the highest remaining line and recording its selected indices. -/

namespace WeightFifteenIndexedPartitionTraversal

open Finset FiniteMaskCoverEnumeration FiniteSearchMasks WeightFifteenConflictRows

def paths (maskAt possibleAt : Nat → Nat) : Nat → Nat → List Nat
  | 0, remaining => if remaining == 0 then [0] else []
  | fuel + 1, remaining =>
    if remaining == 0 then [0]
    else
      (setBitPositions 344 (possibleAt remaining.log2)).flatMap fun k =>
        if maskAt k &&& remaining == maskAt k then
          (paths maskAt possibleAt fuel (remaining ^^^ maskAt k)).map (fun rest => 2^k ||| rest)
        else []

def code (indices : Finset Nat) : Nat := bitMask (List.range 344) fun i => decide (i ∈ indices)

lemma code_bit (indices : Finset Nat) (i : Nat) :
    (code indices).testBit i = true ↔ i < 344 ∧ i ∈ indices := by
  rw [code, bitMask_testBit]
  by_cases inside : i < 344
  · have lt : i < (List.range 344).length := by simpa using inside
    rw [List.getElem?_eq_getElem lt, List.getElem_range]
    simp [inside]
  · have le : (List.range 344).length ≤ i := by simpa using Nat.le_of_not_gt inside
    rw [List.getElem?_eq_none le]
    simp [inside]

lemma code_empty : code ∅ = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases bit : (code ∅).testBit i with
  | false => simp
  | true => simpa using ((code_bit _ i).mp bit).2

lemma code_insert (i : Nat) (lt : i < 344) (indices : Finset Nat) :
    code (insert i indices) = 2^i ||| code indices := by
  apply Nat.eq_of_testBit_eq
  intro k
  apply Bool.eq_iff_iff.mpr
  by_cases h : k = i
  · subst k
    simp [code_bit, lt]
  · simp [code_bit, h, Ne.symm h]

theorem paths_complete (options : List Allowed) (maskAt possibleAt : Nat → Nat)
    (nonempty : ∀ a ∈ options, a.1 ≠ 0)
    (labels : ∀ a ∈ options, a.2 < 344 ∧ maskAt a.2 = a.1)
    (small : ∀ p, possibleAt p < 2^344)
    (hasCandidate : ∀ a ∈ options, ∀ p, a.1.testBit p = true → (possibleAt p).testBit a.2 = true)
    (fuel remaining : Nat) (picked : Finset Allowed) (room : picked.card ≤ fuel)
    (valid : covers options remaining picked) :
    code (picked.image Prod.snd) ∈ paths maskAt possibleAt fuel remaining := by
  induction fuel generalizing remaining picked with
  | zero =>
    have empty : picked = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero room)
    have fixed : remaining = 0 := by
      by_contra nonzero
      have hit := valid.2.2.2 remaining.log2 (Nat.testBit_log2 nonzero)
      simp [empty] at hit
    simp [paths, fixed, empty, code_empty]
  | succ fuel ih =>
    by_cases empty : remaining = 0
    · subst remaining
      simp [paths, cover_empty options nonempty picked valid, code_empty]
    · obtain ⟨a, inside, bit⟩ := valid.2.2.2 remaining.log2 (Nat.testBit_log2 empty)
      have inOptions := valid.1 a inside
      obtain ⟨labelRange, maskEq⟩ := labels a inOptions
      have selected := setBitPositions_complete 344 (possibleAt remaining.log2) a.2
        (small remaining.log2) (hasCandidate a inOptions remaining.log2 bit)
      have fits : a.1 &&& remaining = a.1 := by
        apply Nat.eq_of_testBit_eq
        intro p
        cases b : a.1.testBit p
        · simp [b]
        · simp [b, valid.2.1 a inside p b]
      have room' : (picked.erase a).card ≤ fuel := by
        rw [card_erase_of_mem inside]
        omega
      have continuation := ih (remaining ^^^ a.1) (picked.erase a) room'
        (cover_erase options remaining picked valid a inside)
      simp only [paths, beq_iff_eq, if_neg empty, List.mem_flatMap]
      refine ⟨a.2, selected, ?_⟩
      rw [maskEq, if_pos fits]
      refine List.mem_map.mpr ⟨_, continuation, ?_⟩
      rw [← code_insert a.2 labelRange, ← Finset.image_insert, Finset.insert_erase inside]

end WeightFifteenIndexedPartitionTraversal

namespace WeightFifteenIndexedPartitionTraversal

open WeightFifteenConflictRows

def permuteIndices (position : Nat → Nat) (part : Nat) : Nat :=
  (setBitPositions 344 part).foldr (fun ix rest => 2^position ix ||| rest) 0

def applyWord (g : Fin 4 → Nat → Nat) (moves : Nat) (part : Nat) : Nat :=
  ((List.range (moves % 8)).map fun i =>
    let direction := (moves / (8 * 4^i)) % 4
    (⟨direction, Nat.mod_lt _ (by decide)⟩ : Fin 4)).foldl
      (fun part' next => permuteIndices (g next) part') part

def checkNormalForms (g : Fin 4 → Nat → Nat) (representative : Nat → Bool) :
    List Nat → List Nat → Bool
  | [], [] => true
  | part :: parts, moves :: rest =>
    (representative part || applyWord g moves part < part) &&
      checkNormalForms g representative parts rest
  | _, _ => false

theorem checkNormalForms_sound (g : Fin 4 → Nat → Nat) (representative : Nat → Bool)
    (partitions witnesses : List Nat) (checked : checkNormalForms g representative partitions witnesses = true)
    (part : Nat) (listed : part ∈ partitions) :
    representative part = true ∨ ∃ moves, applyWord g moves part < part := by
  induction partitions generalizing witnesses with
  | nil => simp at listed
  | cons head tail ih =>
    cases witnesses with
    | nil => simp [checkNormalForms] at checked
    | cons moves rest =>
      simp only [checkNormalForms, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at checked
      rcases List.mem_cons.mp listed with equal | later
      · subst part
        rcases checked.1 with kept | smaller
        · exact Or.inl kept
        · exact Or.inr ⟨moves, smaller⟩
      · exact ih rest checked.2 later

end WeightFifteenIndexedPartitionTraversal

namespace WeightFifteenIndexedPartitionTraversal

open Finset WeightFifteenConflictRows

lemma code_lt (indices : Finset Nat) : code indices < 2^344 := by
  by_cases empty : code indices = 0
  · rw [empty]
    decide
  · exact (Nat.log2_lt empty).mp ((code_bit _ _).mp (Nat.testBit_log2 empty)).1

lemma permuteIndices_image (position : Nat → Nat) (indices : Finset Nat)
    (known : ∀ i ∈ indices, i < 344) (bounded : ∀ i ∈ indices, position i < 344) :
    permuteIndices position (code indices) = code (indices.image position) := by
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  change ((setBitPositions 344 (code indices)).foldr
      (fun ix rest => 2^position ix ||| rest) 0).testBit i = true ↔ _
  have fold (xs : List Nat) :
      (xs.foldr (fun ix rest => 2^position ix ||| rest) 0).testBit i = true ↔
        ∃ ix ∈ xs, position ix = i := by
    induction xs with
    | nil => simp
    | cons head tail ih =>
      change (2^position head ||| _).testBit i = true ↔ _
      simp only [Nat.testBit_lor, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq, ih, List.mem_cons]
      constructor
      · rintro (same | ⟨ix, member, same⟩)
        · exact ⟨head, Or.inl rfl, same⟩
        · exact ⟨ix, Or.inr member, same⟩
      · rintro ⟨ix, rfl | member, same⟩
        · exact Or.inl same
        · exact Or.inr ⟨ix, member, same⟩
  rw [fold, code_bit]
  constructor
  · rintro ⟨j, member, rfl⟩
    have j_in := ((code_bit indices j).mp (setBitPositions_sound 344 (code indices) j member)).2
    exact ⟨bounded j j_in, mem_image_of_mem _ j_in⟩
  · rintro ⟨_, member⟩
    obtain ⟨j, j_in, rfl⟩ := mem_image.mp member
    have bit := (code_bit indices j).mpr ⟨known j j_in, j_in⟩
    exact ⟨j, setBitPositions_complete 344 _ j (code_lt indices) bit, rfl⟩

end WeightFifteenIndexedPartitionTraversal

namespace WeightFifteenIndexedPartitionTraversal

open Finset FiniteMaskCoverEnumeration WeightFifteenConflictRows

def disjointPaths (maskAt candidatesAt keeps : Nat → Nat) : Nat → Nat → Nat → List (List Nat)
  | 0, remaining, _ => if remaining == 0 then [[]] else []
  | fuel + 1, remaining, available =>
    if remaining == 0 then [[]]
    else (setBitPositions 344 (candidatesAt remaining.log2 &&& available)).flatMap fun i =>
      (disjointPaths maskAt candidatesAt keeps fuel (remaining ^^^ maskAt i)
        (available &&& keeps i)).map (List.cons i)

theorem disjointPaths_complete (options : List Allowed) (maskAt candidatesAt keeps : Nat → Nat)
    (nonempty : ∀ a ∈ options, a.1 ≠ 0)
    (masks : ∀ a ∈ options, maskAt a.2 = a.1)
    (small : ∀ p, candidatesAt p < 2^344)
    (found : ∀ a ∈ options, ∀ p, a.1.testBit p = true → (candidatesAt p).testBit a.2 = true)
    (preserves : ∀ a ∈ options, ∀ b ∈ options, a ≠ b →
      (∀ p, a.1.testBit p = true → b.1.testBit p = false) → (keeps a.2).testBit b.2 = true)
    (fuel remaining available : Nat) (picked : Finset Allowed)
    (room : picked.card ≤ fuel) (valid : covers options remaining picked)
    (fits : ∀ a ∈ picked, available.testBit a.2 = true) :
    ∃ row ∈ disjointPaths maskAt candidatesAt keeps fuel remaining available,
      row.toFinset = picked.image Prod.snd := by
  classical
  induction fuel generalizing remaining available picked with
  | zero =>
    have empty : picked = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero room)
    have fixed : remaining = 0 := by
      by_contra nonzero
      have hit := valid.2.2.2 remaining.log2 (Nat.testBit_log2 nonzero)
      simp [empty] at hit
    exact ⟨[], by simp [disjointPaths, fixed], by simp [empty]⟩
  | succ fuel ih =>
    by_cases empty : remaining = 0
    · subst remaining
      exact ⟨[], by simp [disjointPaths], by simp [cover_empty options nonempty picked valid]⟩
    · obtain ⟨a, selected, bit⟩ := valid.2.2.2 remaining.log2 (Nat.testBit_log2 empty)
      have hA := valid.1 a selected
      have included : (candidatesAt remaining.log2 &&& available).testBit a.2 = true :=
        by simp [Nat.testBit_land, found a hA _ bit, fits a selected]
      have bound : candidatesAt remaining.log2 &&& available < 2^344 := by
        rw [Nat.and_comm]
        exact Nat.and_lt_two_pow _ (small _)
      have moves := setBitPositions_complete 344 _ a.2 bound included
      have nextFits : ∀ b ∈ picked.erase a, (available &&& keeps a.2).testBit b.2 = true := by
        intro b hb
        obtain ⟨different, hb'⟩ := mem_erase.mp hb
        have keep := preserves a hA b (valid.1 b hb') different.symm
          (valid.2.2.1 a selected b hb' different.symm)
        simp [Nat.testBit_land, fits b hb', keep]
      have room' : (picked.erase a).card ≤ fuel := by
        rw [card_erase_of_mem selected]
        omega
      obtain ⟨tail, listed, same⟩ := ih (remaining ^^^ a.1) (available &&& keeps a.2)
        (picked.erase a) room' (cover_erase options remaining picked valid a selected) nextFits
      refine ⟨a.2 :: tail, ?_, ?_⟩
      · simp only [disjointPaths, beq_iff_eq, if_neg empty, List.mem_flatMap]
        exact ⟨a.2, moves, List.mem_map.mpr ⟨tail, (masks a hA).symm ▸ listed, rfl⟩⟩
      · rw [List.toFinset_cons, same, ← Finset.image_insert, Finset.insert_erase selected]

end WeightFifteenIndexedPartitionTraversal


/-! Replay a prefix search that can rule out a partition before the remaining stars are chosen. -/

namespace WeightFifteenPrefixVerifier

structure State where
  remaining : Nat
  available : Nat
  picked : Nat

structure Cursor where
  chunks : List Nat
  word : Nat := 0
  left : Nat := 0

def Cursor.next (cursor : Cursor) : Option (Nat × Cursor) :=
  match cursor.left with
  | 0 => match cursor.chunks with
      | [] => none
      | chunk :: rest => some (chunk % 2048, ⟨rest, chunk / 2048, 31⟩)
  | left+1 => some (cursor.word % 2048, ⟨cursor.chunks, cursor.word / 2048, left⟩)

structure Tables where
  star : Nat → Nat
  candidates : Nat → Nat
  compatible : Nat → Nat

def extend (tables : Tables) (state : State) (selected : Nat) : State :=
  ⟨state.remaining ^^^ tables.star selected,
    state.available &&& tables.compatible selected, state.picked ||| 2^selected⟩

def runChoices (branch : Nat → Cursor → Option Cursor) : Nat → Nat → Cursor → Option Cursor
  | 0, options, cursor => if options == 0 then some cursor else none
  | fuel+1, options, cursor =>
    if options == 0 then some cursor
    else match branch options.log2 cursor with
      | none => none
      | some next => runChoices branch fuel (options ^^^ 2^options.log2) next

def checkPrefix (tables : Tables) (cut : Nat → State → Bool) : Nat → State → Cursor → Option Cursor
  | 0, _, _ => none
  | fuel+1, state, input =>
    match input.next with
    | none => none
    | some (code, rest) =>
      if code == 63 then
        if state.remaining == 0 then none
        else runChoices (fun index => checkPrefix tables cut fuel (extend tables state index))
          344 (tables.candidates state.remaining.log2 &&& state.available) rest
      else if cut code state then some rest else none

lemma runChoices_complete (branch : Nat → Cursor → Option Cursor) (fuel mask index : Nat)
    (a b : Cursor) (ok : runChoices branch fuel mask a = some b) (bit : mask.testBit index = true) :
    ∃ i j, branch index i = some j := by
  induction fuel generalizing mask a b with
  | zero =>
    by_cases empty : mask = 0
    · simp [empty] at bit
    · simp [runChoices, empty] at ok
  | succ fuel ih =>
    by_cases empty : mask = 0
    · simp [empty] at bit
    simp only [runChoices, beq_iff_eq, if_neg empty] at ok
    cases moved : branch mask.log2 a with
    | none => simp [moved] at ok
    | some next =>
      by_cases eq : index = mask.log2
      · exact ⟨a, next, eq.symm ▸ moved⟩
      · have there : (mask ^^^ 2^mask.log2).testBit index = true := by
          simpa only [Nat.testBit_xor, Nat.testBit_two_pow, Ne.symm eq, decide_false, Bool.xor_false] using bit
        rw [moved] at ok
        exact ih _ _ _ ok there

/-- A trace refutes any feasible state for which a chosen pivot has a feasible successor
    and each checked cut is contradictory. -/
theorem checkPrefix_refutes (tables : Tables) (cut : Nat → State → Bool) (feasible : State → Prop)
    (cut_sound : ∀ code state, cut code state = true → ¬ feasible state)
    (branch_sound : ∀ state, feasible state → state.remaining ≠ 0 →
      ∃ i, (tables.candidates state.remaining.log2 &&& state.available).testBit i = true ∧
        feasible (extend tables state i))
    (fuel : Nat) (state : State) (input output : Cursor)
    (ok : checkPrefix tables cut fuel state input = some output) : ¬ feasible state := by
  induction fuel generalizing state input output with
  | zero => simp [checkPrefix] at ok
  | succ fuel ih =>
    intro model
    cases read : input.next with
    | none => simp [checkPrefix, read] at ok
    | some token =>
      obtain ⟨code, rest⟩ := token
      by_cases all_children : code = 63
      · by_cases empty : state.remaining = 0
        · simp [checkPrefix, read, all_children, empty] at ok
        · simp only [checkPrefix, read, beq_iff_eq, if_pos all_children, if_neg empty] at ok
          obtain ⟨i, bit, extension⟩ := branch_sound state model empty
          obtain ⟨a, b, good⟩ := runChoices_complete _ _ _ i _ _ ok bit
          exact ih _ a b good extension
      · by_cases contradiction_data : cut code state = true
        · exact cut_sound _ _ contradiction_data model
        · simp [checkPrefix, read, all_children, contradiction_data] at ok

end WeightFifteenPrefixVerifier

namespace WeightFifteenPrefixVerifier

open Finset FiniteMaskCoverEnumeration WeightFifteenIndexedPartitionTraversal

def Progress (options : List Allowed) (partition : Finset Allowed) (state : State) : Prop :=
  ∃ left : Finset Allowed, left ⊆ partition ∧ covers options state.remaining left ∧
    (∀ a ∈ left, state.available.testBit a.2 = true) ∧
    code ((partition \ left).image Prod.snd) = state.picked

lemma Progress.extend_by (options : List Allowed) (tables : Tables) (partition : Finset Allowed)
    (maskAt : ∀ a ∈ options, tables.star a.2 = a.1)
    (index_bounds : ∀ a ∈ options, a.2 < 344)
    (preserves : ∀ a ∈ options, ∀ b ∈ options, a ≠ b →
      (∀ p, a.1.testBit p = true → b.1.testBit p = false) →
      (tables.compatible a.2).testBit b.2 = true)
    (state : State) (left : Finset Allowed) (inside : left ⊆ partition)
    (old : covers options state.remaining left)
    (available : ∀ b ∈ left, state.available.testBit b.2 = true)
    (picked : code ((partition \ left).image Prod.snd) = state.picked) (a : Allowed) (hit : a ∈ left) :
    Progress options partition (extend tables state a.2) := by
  have legal := old.1 a hit
  refine ⟨left.erase a, fun b hb => inside (mem_of_mem_erase hb), ?_, ?_, ?_⟩
  · change covers options (state.remaining ^^^ tables.star a.2) (left.erase a)
    rw [maskAt a legal]
    exact cover_erase options _ left old a hit
  · intro b hb
    obtain ⟨different, member⟩ := mem_erase.mp hb
    have kept := preserves a legal b (old.1 b member) different.symm
      (old.2.2.1 a hit b member different.symm)
    change (state.available &&& tables.compatible a.2).testBit b.2 = true
    simp [available b member, kept]
  · have selectedMore : partition \ left.erase a = insert a (partition \ left) := by
      ext b
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
      by_cases h : b = a
      · subst b; simp [inside hit]
      · simp [h]
    change code ((partition \ left.erase a).image Prod.snd) = state.picked ||| 2^a.2
    rw [selectedMore, Finset.image_insert, code_insert _ (index_bounds a legal), picked, Nat.or_comm]

theorem Progress.pivot (options : List Allowed) (tables : Tables) (partition : Finset Allowed)
    (maskAt : ∀ a ∈ options, tables.star a.2 = a.1)
    (index_bounds : ∀ a ∈ options, a.2 < 344)
    (supports : ∀ a ∈ options, ∀ p, a.1.testBit p = true → (tables.candidates p).testBit a.2 = true)
    (preserves : ∀ a ∈ options, ∀ b ∈ options, a ≠ b →
      (∀ p, a.1.testBit p = true → b.1.testBit p = false) →
      (tables.compatible a.2).testBit b.2 = true)
    (state : State) (valid : Progress options partition state) (unfinished : state.remaining ≠ 0) :
    ∃ i, (tables.candidates state.remaining.log2 &&& state.available).testBit i = true ∧
      Progress options partition (extend tables state i) := by
  obtain ⟨left, inside, legal, available, fixed⟩ := valid
  obtain ⟨a, hit, bit⟩ := legal.2.2.2 state.remaining.log2 (Nat.testBit_log2 unfinished)
  have validChoice : (tables.candidates state.remaining.log2 &&& state.available).testBit a.2 = true := by
    simp [supports a (legal.1 a hit) _ bit, available a hit]
  have new := Progress.extend_by options tables partition maskAt index_bounds preserves state
    left inside legal available fixed a hit
  exact ⟨a.2, validChoice, new⟩

end WeightFifteenPrefixVerifier

namespace WeightFifteenPrefixVerifier

open Finset FiniteMaskCoverEnumeration WeightFifteenIndexedPartitionTraversal

lemma Progress.potential (options : List Allowed) (partition : Finset Allowed) (state : State)
    (valid : Progress options partition state) (a : Allowed) (belongs : a ∈ partition) (bounded : a.2 < 344) :
    (state.picked ||| state.available).testBit a.2 = true := by
  obtain ⟨left, _, _, avail, code_eq⟩ := valid
  by_cases unchosen : a ∈ left
  · simp [Nat.testBit_lor, avail a unchosen]
  · have chosen : a ∈ partition \ left := mem_sdiff.mpr ⟨belongs, unchosen⟩
    have bit := (code_bit ((partition \ left).image Prod.snd) a.2).mpr
      ⟨bounded, mem_image_of_mem _ chosen⟩
    rw [code_eq] at bit
    simp [Nat.testBit_lor, bit]

lemma progress_after_largest (options : List Allowed) (tables : Tables) (partition : Finset Allowed)
    (maskAt : ∀ a ∈ options, tables.star a.2 = a.1)
    (index_bounds : ∀ a ∈ options, a.2 < 344)
    (preserves : ∀ a ∈ options, ∀ b ∈ options, a ≠ b →
      (∀ p, a.1.testBit p = true → b.1.testBit p = false) →
      (tables.compatible a.2).testBit b.2 = true)
    (remaining : Nat) (valid : covers options remaining partition) (largest : Allowed)
    (selected : largest ∈ partition) (maximal : ∀ b ∈ partition, b.2 ≤ largest.2) :
    Progress options partition
      ⟨remaining ^^^ tables.star largest.2,
        (2^largest.2-1) &&& tables.compatible largest.2, 2^largest.2⟩ := by
  have item := valid.1 largest selected
  refine ⟨partition.erase largest, fun b hit => mem_of_mem_erase hit, ?_, ?_, ?_⟩
  · dsimp only
    rw [maskAt largest item]
    exact cover_erase options remaining partition valid largest selected
  · intro b hit
    obtain ⟨different, member⟩ := mem_erase.mp hit
    have b_item := valid.1 b member
    have lower : b.2 < largest.2 := by
      apply lt_of_le_of_ne (maximal b member)
      intro equal
      apply different
      apply Prod.ext _ equal
      exact (maskAt b b_item).symm.trans ((congrArg tables.star equal).trans (maskAt largest item))
    have keep := preserves largest item b b_item different.symm
      (valid.2.2.1 largest selected b member different.symm)
    simpa only [Nat.testBit_land, Nat.testBit_two_pow_sub_one, decide_eq_true lower, Bool.true_and] using keep
  · have diff : partition \ partition.erase largest = {largest} := by
      ext b
      simp only [mem_sdiff, mem_erase, mem_singleton]
      by_cases eq : b = largest
      · subst b; simp [selected]
      · simp [eq]
    rw [diff, Finset.image_singleton, ← Finset.insert_empty, code_insert _ (index_bounds largest item),
      code_empty, Nat.or_zero]

end WeightFifteenPrefixVerifier

namespace WeightFifteenIndexedPartitionTraversal

open Finset WeightFifteenConflictRows

lemma code_nonzero (s : Finset Nat) (i : Nat) (hi : i∈s) (small : i<344) : code s ≠ 0 := by
  intro h
  have bit := (code_bit s i).mpr ⟨small,hi⟩
  simp [h] at bit

lemma code_erase (s : Finset Nat) (i : Nat) (hi : i∈s) (small : i<344) :
    code (s.erase i) = code s ^^^ 2^i := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases same : j = i
  · subst j
    have a : (code (s.erase i)).testBit i = false := by
      cases eq : (code (s.erase i)).testBit i
      · rfl
      · exact (Finset.notMem_erase i s ((code_bit _ _).mp eq).2).elim
    have b := (code_bit s i).mpr ⟨small,hi⟩
    simp [a,b,Nat.testBit_xor]
  · apply Bool.eq_iff_iff.mpr
    simp only [Nat.testBit_xor, Nat.testBit_two_pow, Ne.symm same, decide_false, Bool.xor_false,
      code_bit, Finset.mem_erase]
    tauto

theorem positions_to_finset (fuel : Nat) (s : Finset Nat) (bounds : ∀ i∈s, i<344) (card : s.card≤fuel) :
    (setBitPositions fuel (code s)).toFinset = s := by
  induction fuel generalizing s with
  | zero =>
    have empty := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero card)
    simp [setBitPositions, empty]
  | succ fuel ih =>
    by_cases empty : s = ∅
    · simp [setBitPositions, empty, code_empty]
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr empty
    have nonzero := code_nonzero s i hi (bounds i hi)
    let j := (code s).log2
    have yes : (code s).testBit j = true := Nat.testBit_log2 nonzero
    obtain ⟨small, hj⟩ := (code_bit _ _).mp yes
    have card' : (s.erase j).card ≤ fuel := by rw [Finset.card_erase_of_mem hj]; omega
    have bound' : ∀ k ∈ s.erase j, k < 344 := fun k hk => bounds k (Finset.mem_of_mem_erase hk)
    have tail := ih (s.erase j) bound' card'
    change (if code s = 0 then [] else j :: setBitPositions fuel (code s ^^^ 2^j)).toFinset = s
    rw [if_neg nonzero, ← code_erase s j hj small, List.toFinset_cons, tail, Finset.insert_erase hj]

def moveBits (position : Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel+1, w => if w == 0 then 0 else
    (1 <<< position w.log2) ||| moveBits position fuel (w ^^^ (1 <<< w.log2))

lemma moveBits_fold (position : Nat → Nat) (fuel w : Nat) : moveBits position fuel w =
    (setBitPositions fuel w).foldr (fun i rest => 2^position i ||| rest) 0 := by
  induction fuel generalizing w with
  | zero => rfl
  | succ fuel ih =>
    by_cases empty : w = 0
    · simp [moveBits, setBitPositions, empty]
    · simp [moveBits, setBitPositions, empty, Nat.shiftLeft_eq, ih]

lemma code_of_list (position : Nat → Nat) (list : List Nat) (bounded : ∀ i∈list, position i<344) :
    list.foldr (fun i rest => 2^position i ||| rest) 0 = code (list.toFinset.image position) := by
  induction list with
  | nil => simp [code_empty]
  | cons i tail ih =>
    have tail_bounded (j : Nat) (hj : j∈tail) := bounded j (List.mem_cons_of_mem _ hj)
    rw [List.foldr_cons, List.toFinset_cons, Finset.image_insert,
      code_insert _ (bounded _ List.mem_cons_self), ih tail_bounded]

lemma moveBits_code (position : Nat → Nat) (fuel : Nat) (s : Finset Nat) (card : s.card≤fuel)
    (bound : ∀ i∈s, i<344) (position_bound : ∀ i∈s, position i<344) :
    moveBits position fuel (code s) = code (s.image position) := by
  have same := positions_to_finset fuel s bound card
  rw [moveBits_fold, code_of_list, same]
  intro i hi
  exact position_bound i (same ▸ List.mem_toFinset.mpr hi)

theorem code_inj_on_indices (a b : Finset Nat) (a_bound : ∀ i∈a, i<344)
    (b_bound : ∀ i∈b, i<344) (same : code a = code b) : a = b := by
  ext i
  constructor
  · intro hi
    exact ((code_bit b i).mp (same ▸ (code_bit a i).mpr ⟨a_bound _ hi,hi⟩)).2
  · intro hi
    exact ((code_bit a i).mp (same.symm ▸ (code_bit b i).mpr ⟨b_bound _ hi,hi⟩)).2

end WeightFifteenIndexedPartitionTraversal

/- The prefix search starts with the largest selected index. A certificate cuts a branch by its key, a symmetry, or a fully specified first partition. -/

namespace WeightFifteenUpperPrefix

open WeightFifteenPrefixVerifier WeightFifteenVerifiedSearch WeightFifteenIndexedPartitionTraversal

def normalForm : Lookup := (.node 2 (.node 1 (.leaf 0x1000000080000000040000000000000000010000000020000000000000000000000001000000000000000010000001000000000400000000000000000000008000400000000000000000000400000000000000000000100000008000000100000000000000000000001000000004000000000000000200000000000000000000001000000080000001000000000000000000000010000000800000000000000000040000000) (.leaf 0x1000000080000000020000000000000000000004000010000000000000000002000000000000000000000010000000800000000200000000000000000040000000200000000000000000000000100000000000000000100000008000000002000000000000000000000400002000000000000000000100000000000000000000001000000080000000040000000000000000000010000020000000000000000000040000000)) (.node 3 (.leaf 0x1000000200000000000000000200000000010000000000800000000000100000000000000000000000000010000002000000000000000002000000000040000000008000000000004000000000000000000000000000100000020000000000000400000000000000000800000080000000000040000000000000000000000000001000000080000000020000000000000000004000000010000000000000000000000020000) (.leaf 0x1000000200000000000000002000000000004000000000400000000000008000000000000000000000000010000001000000000000000020000000000400000000000400000000000080000000000000000000000000100000020000000000000000200000000000200000000040000000000010000000000000000000000000001000000200000000000004000000000000000080000000800000000000100000000000000)))

def normalFormWord (n : Nat) : Nat := normalForm.block 4 344 n

def lowerBound : Nat := 0x1000000080000000000010000000000000000002000000400000000000100000000000000

def upperBound : Nat := 0x1000000200000000000004000000000000000080000000800000000000100000000000000

def firstMask : Nat := 2^344-1

def sameGroup : Lookup := (.node 43 (.node 21 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf 0x1fcd51505cf400cebcff3592900073fe2e8595880049ff35817735000e29292cadcd4000000000000000003aceb173f84800c7dc5705e1ec00dc75575f4a6000c7170572ac3a000b8e1ef45b0e8000000000000000004ff299545f0800f17f0fca64240047f1de0537340050ffca897fc2000cd642555ff0800000000000000000c5f2bc3ca70000d3dd5745e42c00cd71575f0b3400f30745769bcd00047e42f106f3400000000000000000) (.leaf 0xe211468ff2e8006942a3fa3f6400ec1bb1f3eae000fc93fa3d4c92000983f64f7324800000000000000000b52e8e8ba39400be0ff0ba3a9800b32ec3a2ff8800ae60ba3e8bed000623a98a82fb400000000000000000e05166bf05940029e2acf5cfd0002e8b38fcd4dc003f6cf5ce906500037cfd338419400000000000000000b5aebc2ba700003e3358bac5ec003bcccc58fc74002e68bace90ed00037c5ef1043b400000000000000000)) (.node 3 (.leaf 0xc5f2bc3ca00190e3ee5b8f000392ceb19b53340392c36b8fba8000db247e42f102c3530000000000000000c5d3f6b0a001f0f2b7ed4e0002e3c3d2edac3800f1f36d4ed60000db242b81aa8673041000000000000000f1fc7cbf000178fcbf3ff100026df3fc2f2fc40079fc2ff1fc8000d18629a82a04d8449000000000000000f2fcbc7f300286fc7f0ff2000190f0fcdf1fc80386fc1ff2fc40002e590654551b24a26000000000000000) (.node 4 (.leaf 0x15ad5abf0001781751fcf500033d1d4734fcd4030d3f6cf5ce8000d18154f5138419519000000000000000ea7a2d4ed002863fb354ed0003163ccddc5ce803063794ed4fc000e2f2885aa1582ea260000000000000003aceb173f00206cbec5b3f000386ecb99b53a00386cb8b3fb3c000ecfb8e1ef4530a2060000000000000003ac7f3b1e0020fceb4ed1e0002cff0deedac6800e8cf9d1ed30000ecfa0b29acaa06888000000000000000) (.leaf 0x53fc58400dc735fc7f20005f417873fc3e0001cd39583ff0887750354d15f41f30003d4000000000000000f1fc7c80058578d4dd1000dfc355d174373001cf74f40741749361c0873dfc3b0000159000000000000000182fcbcff000ef954da3fa0000f81c2772f3e800eefc93fa3d40000e5181f64b73248a6000000000000000ea3b0f4ed000ef7e8bd2ed0000eff03ee3a3e800e83792ed2fc0000efa02a986a12e888000000000000000)))) (.node 7 (.node 6 (.leaf 0x1fcd51400cf705cbecf000d1d34d66bb1a8001553949eb35814725744ffd1d3cd0003cd0000000000000003ac7f38008ea0fc7d44000f2ffc7dc55656002a3e6c7150452281accab8f2ffce00028e0000000000000004fd3d1000f3fb3f177a0007825f047d3ec800339b150fd4a8139c2371cd7825e60003f2000000000000000c5d3f6800715f0d3d54000f83fd3cd516560033bf2f305445619ccc8247f83fa8000171000000000000000) (.leaf 0xea3b0f400268ef578950002fb8d7dc35737002e0e63712452684ba0caa82fb87f0000ae000000000000000b52e8e800394d8aa0ef00035fcaeaa2a83d00374df8a60ba3a8b2d0ba7735fc980000790000000000000004e7909400d73353fb3d0008f933d37cf3c8000dd0911d4e50970757142e8f923f00031d000000000000000b586b6800795d83e33e000cafe2e3bcecce000ba0f2e681ac610cc93a37caff28000139000000000000000)) (.node 8 (.leaf 0x1fce80105c4b06cbc00b3fe1ef8666b99001b7759049eb3f000f2d745ffe1ec003cb7060000000000000001fc7c0104cff07ce800d1eb29acf73dee0043388b949fd1e00391e745e2b29800e478c900000000000000053fc80141f4b96fc400ff265459073fcd005874590583ff2003fd2375d1654400ff4b36000000000000000f1fc803f270190d4c00741e5cf96d174500f4b4796f40741001be1c8a73e5cc006f8530000000000000000) (.node 9 (.leaf 0x152fc00fa094f8974003451f74d71d25700348fcf6f70345000bed08a151f74002fb479000000000000000e011400fa3946869c003bf35fc79ee1b9003b7746fcb63bf000b2d0ba7735fc002cb4790000000000000004e7a00045f4b963f8004ed85ab1637cdd004b4750011d4ed0030ff7352e85a800c3ff36000000000000000e0514031a7946829c00c5ecafd392e8ba00c78bb0f3f6c5e0010ccd3a37cafc00433139000000000000000) (.leaf 0xe20024bf1dc46968622ff05f4178e200093fc5cf6dfc3000fc7750354d10001f3dd43d4000000000000000b1003c6b2f4b96bc3f08b2654480b3000f1acf4696ac2000fc7fd23b5d1000151ff4b360000000000000001d2fc00450b4b7954003fa1f64f815277001b4fcb958f3fa000fd20751d1f64003f48f60000000000000004e3b00045378b77e8002ed2a98ef733ee001b788b911d2ed0006ff075e22a98001bfcc9000000000000000))))) (.node 15 (.node 12 (.node 11 (.leaf 0x3d003163ac4b068a2c583ae1ee86aa000b52b776968ae000b3cf2db8fff0003453cb7060000000000000003d0033a1acff0e8e34e81ab29a8eb3000da87b88d98ee000d3391eb8fe20002cae478c9000000000000000ce002d4cdf0b9253995645a42b92cd00075f0b379233100066b6cfcc2ce000255db3f32000000000000000c20026b0ef3c616162ad4a782570ce0009ec3b3b63f0f000d539c23f1cd0001e6e70bf2000000000000000) (.leaf 0xe200260e5d706929a284e58f91392e0008fcd4df0d37d0004ff075f1c2e00023fc1d71d000000000000000ac002d4a8f4b963e3350a885aa063b000c58fc760626c0004ff0ffb3f2e000215c3ff360000000000000001d0013f350b70d875c57055353451d00067f40df74c7100072b735c481d00018fdcd7cd000000000000000220022b35cf40949e0ab35d1d149ee0009d395576dcbe000b3c725f4cff0003cd1c97cd000000000000000)) (.node 13 (.leaf 0x5064bf3ac86900222ff27f45780098b93fcac36e000ff2fc6c922e5007f45f3b24aa600000000000000000acbcab2785d8003f38b2ba8aae00eccf2acf88d90008b2fc9be19ba00ba8aa06f84490000000000000001d000bcba0b4de940da0ba1f64a8190002f2fcfcdface0003d4fd20b51d0000b73f48f6000000000000000ac000f4a8378de3e0bd0a82a98aeb30003a2ff88d926c0002fc6ff0bfe200006a1bfcc9000000000000000) (.node 14 (.leaf 0xa3d9545037b3001dafca5c25f000637685343db1000fca897fc2371005c25b7ff0bf2000000000000000007309445f3bb3003bd6cda81ae300f2ee853708b10006cd0976cf77100a81a6adb3cc100000000000000000a3dabca015f0001d57455c37d30061767f083ff2000745769bcdc82005c35b86f3571000000000000000005166bca714600022ab8ff43d71009399d3373763000b8fba8b0ddb200f43f982c3571000000000000000) (.leaf 0xae9aaba095d80011f8ba4f762e004644f8fcfe0f0008bace90ed93a004f753843b5390000000000000000051260eda6869002284ed8fb939008bb8fce8e30e0004ed4fe0bae2f008fba3f82ea2e000000000000000008fd3f3f0a20f001c57055377c70065767f48e3e600070572ac3acca0053758fb0ea8e000000000000000004162b3f8e8090020ab3ff1fd49009b99d3a2636e000b3fb3cc28ecf00f1ffcd30a28e000000000000000)))) (.node 18 (.node 16 (.leaf 0x8ff2a568fd0800f17f0fca6424008bf1d15a1d1400a0ffca75774200000000000000000f05b41d4fc59200c5e3fabca61400f2b8be8bb81800c3e2eeaf2e0800f36e8be89a890000000000000000070af8e2aaca6100f4fd3e3f059000fe3fcff49a9000f0fe0f8fd18000ff4ff4fe13640000000000000000078a4b62a8626100f8fe3d3fca4000fd3f0ff8656000fcfd0f4fe26000fc8ff8fd2c9000000000000000000875b41d47948600) (.node 17 (.leaf 0x755ebc17a700000df3547f01ec00370ddc54fc74001d647fce90ed000000000000000003cb35b048eb1000dab49d7d7a480032c358d7c4cc003ccddc5ce860003b98d78fe0ba000000000000000000f735bc44bc06002fcd63e35c7400cebcff3592900083fe212a55080086ff3573f71500000000000000000cba436f3d3249003acbf2f2b8a800ceb8be2bb21800f0e2eeafaa8000cf9e2be0ec2a000000000000000008b2c3ef373c8800) (.leaf 0xf4fd3e00059178eb2ec000d5d37cecbb0bc001537ccb4bb4ba0324d18000000000000006cb477260035186f8d737000ae2ecfd3780007a61f8fcdf0dc002a3ecfc8d58d528902e400000000000000875fa1e90008a79751fce87a394004c8ff37f228800731ce3a1ff88005d637f3e8bed00000000000000000788fbc2a2e86100da34cdcd72e800b28771d7189800f03ee3a3ea8000fb91d71fccba000000000000000008b0fbc3b3bc8800))) (.node 19 (.leaf 0x8fd3e7800d3f53f177a0007825f08bd3e160011a53a0fd4a5531423d100000000000000f05f81e9001e27cc5e3fa800615e0e3e8b000f43fe3cea29a900227e3c36a8ba88a09da20000000000000060be4f26003518ca3fc64c00d475dfc7f20005f417883fc3130010e55a43ff074775035400000000000000f714e1fc0017c55f2e8f8c00a8aebfc7820007f05e8f0e0fe3002c3eafc1ea2e86c822a100000000000000871fe1fc0008c79) (.node 20 (.leaf 0xda94d5800aeae732c36000c8de373ccfece000a30e3b985687209ae2f000000000000000f73afcb0000a4bea6b2a400a2aeb3fb090008f3b2b3cc2fcb000e30a3794a948e0aae23000000000000000b63decf0000e4b2fcd63c00c770dcbecf000d1d34d8abb115001165582eb3533c705b4c00000000000000cef437b300345d33acbf2c008aa0bcbe8b000f13fcbeca29a900263eacb8a2ba0cc28e83000000000000008e7c3fb30008673) (.leaf 0x751fce800394b849cef00021ecdf661993d00374bf49633f3a8b2d0ba000000000000006c8e7c26000510eda34cdc002e8e7a2c6700014dc37ec3b93d00260eecb81971bcc2806f000000000000008e4e7c37000863bae7927400d735d3fb3d0008f933d0bcf3070001e0526d4e547f055b1c000000000000003be0d6cf0023dc77557f6800795b80df3e00002ed1f370dece000b90f1d645ec610cc53a000000000000003cb3af0a003218e)))))) (.node 32 (.node 26 (.node 23 (.node 22 (.leaf 0xa3fc802b3d4b16fc400ff265459083fcd00a4d0616a43ff20037523d500000000000000f71b4000fd19468f1e8c03e2685e8fc800ea3ba0aebf3e0e00f8e88e9fc2ea3001aa1da200000000000000782fb000ae26086f4fe003f870190eb000bbce5e394ecb90003b37394cb4bbc000b2cdb8000000000000006cba5800a6b1088f4d700318791f8fe000d5cba92ecf0de000c7380f8ff4d5c0019ccdb80000000000000078afac00a8a6186) (.leaf 0xae7a000add4b163f8004ed85ab160bcdd0085c160626d4ed003057b1f000000000000003be358004fe16c815abc03ea095e817400cab4f372b1d42700cacef0b3f6cab0010a9d22000000000000001491fc008e9318e2fce8023fc4b06cbc00b3fe1ef868ab9900215161682eb3f000705bcf00000000000000cef81800b3f86e02fc7c021ec7f0fce800d1eb29acf83dee00859085186fd1e003116bcf00000000000000cbac2c00e0ec9b3)) (.node 24 (.leaf 0x1c001b3f40b37c951d8ff05f41781c0006cfd0d37cfcc000fd3750354000000000000005540017dd517c55ec002f0e4d737c7e3bc6e48a926cf0000f8fd1807837c0006f3674f5c00000000000000bb8002db57229970d2fc00bf0345f954003fa1f64f8092770025c1c57a4f3fa0007520d500000000000000554de0003d47e3dae3b000ad1785f7e8002ed2a98ef833ee0025d085126d2ed0006570df00000000000000bb839c001fca937) (.node 25 (.leaf 0xd001afcb037e39158ae8a5c25e00d0006bf2c2fe3f0f000e87e823a1000000000000005040017dfc5727cce002a4c9e3be372b89689a81ae3c3000eaf2e08e133d00068f68bfa300000000000000b08002db5cea1b4d3001cfd19c675b08739d1988225f3000f2fc58879f830009ce571e5c00000000000000fb0002f8d72689773003c573749964c7f077221459073000f15cf45965c3000fc5bd21f500000000000000f70001d4fd19468) (.leaf 0x37003153f4490649ec533f21ed8666000b51b77596496000b3cb2d5cf00000000000000cec00390b3f86e037003391e4dd0f4cb4e51e2288cf73000da47b88b94d7000d3191e5cf00000000000000cb8002e3e0ec9b3cb001d7c7b0a92a2c65987c40e12ce000b53373792c3a0009bcd0de7300000000000000e0c00394b4f92e8cb0015b06b2ef3b2876946981a23c3000dac3b08f1f3b0009729cee7300000000000000f08002ebe8ee1b4)))) (.node 29 (.node 27 (.leaf 0x15000bc7f094bf054da37a0364d8150002f1fcfcbf5c70003d4bd20f5000000000000005540003d3d47e3d66000f46d358bf4c8bd26d2288cf730003a1ff88b91550002fc2ff0ff00000000000000bb80001b1fca937190019fd50a675124178d54c52351d0004fcd4df0d3bb0008fe075e1c0000000000000015c0014fc713dc766002d46d749960db3546d01a91637000c54fc75061550004fd0ff53f000000000000003bc002c44fe16c8) (.node 28 (.leaf 0x5cfc972785b8003f37732288cf001cef25cf88b9000773fc9be15ba00000000000000002fb228ae2608600b4dcfd3acae7000739d3988a2700fcef2fca80e80009d39cecb2e6f00000000000000002fb2f87b0883300af1b3fc0a2ec001d8ff85f61f8006706cfe0e3ec000ff8fd2c902e400000000000000001de17d7940e79007b2f0eca62ec003bc6ecaa92ec00fe0f8fe280e80006ec6f24b8eec0000000000000000239edb5bc8833) (.leaf 0xfda97a095b80011f47f03651f000574f4fcfd0f00047fce90ed53a000000000000000011fd0e8e9318e00a4d9fd70a2e7000178d74c5637004774fce8e30e0008d78fe0bae2f000000000000000011fd4f4bc0e4b00a3c3e8f03753001dafca5c25f00063707a1c1e53000fca7577423d100000000000000001dc17dfc5727c00732748dd3b53003bd6cda81ae300f2e12a1d08510006cd67f647bd30000000000000000238edb5cea1b4))) (.node 30 (.leaf 0x4fe3d8541e3c00f178ae8a7c240047e2fe85262c00000000000000000cd7c25b3fa0800f05fc0d1d45f200c5e3fabca61400d3d81601fc3c00cd60763f0a2c0000000000000000047fc3fb86a240050bdcf2e28b71005cfd19144df000fd3f8ff05f400074ff0e8591d000000000000000000dc5f41f4dd4000f354e0d1d517c00f4fd3e3f059000d71d4744dfd000dc75074f41d00000000000000000074dfd3b84d90005cb4d72e0237100) (.node 31 (.leaf 0x5bb4595459e40032c378d5ccd00037cf3c8494dc000000000000000003bccd33f81d40033f0f4c1c533d00b5aabaaaa694003e30b8aacf3c003bc2ccb8acec0000000000000000037cf3f3842a4003c833b0e8eb31002fcd63e35c7400c7dc5705d3d0008975317a411c00000000000000000cfd3d047dc5400cdf417725234d003acbf2f2b8a800c7d81601f33c00dc60763f0ae000000000000000000b8f33f8bb0a8008d7c1f727288e00) (.leaf 0x571fc94453dc004d4fa37a236400771df281b7fc00000000000000000552364f72f4800f34fe011154fe00ad2e87cba17c00bc0fa0ba3f64008b2ec1725d1c00000000000000000cd3f64471d4800770b203d2d4fe00751fce87a3940045cd534523ec00551573714bfc000000000000000007723ecb82fb4005c8ddc2e2a87100da34cdcd72e80092c551451cdc00dc3573734ae000000000000000000b81cdcff32e8008d4ddc3e3a88e00))))) (.node 37 (.node 34 (.node 33 (.leaf 0xa3fc64eb10035dfc7f2ff000017883fc313a440255000000000000000c15f4043dd43d4f714e1fcd500055f2e8f8fe3002ebfc782ea20001e8f0e0fe3f8803ea000000000000000907f05b3b20aa2871fe1fc7900079f4fd3e3f000178eb2ecbb400037cecbb0bc390037c00000000000000074d5d3980c91586cb477268600086f8d73731c002ecfd378d580001f8fcdf0dcc6003ec000000000000000987a61e4a242a4875fa1e96840079) (.leaf 0x2fcd63e350030dcbecfb3500034d8abb1152140255000000000000000cfd1d0451c17c5cef437b393000d33acbf2f2b0020bcbe8ba2b0003cbeca29a93a003ea000000000000000b8f13f8930a28a8e7c3fb333c00738fd3e7a0e00353f177ad4a0001f08bd3e168180253000000000000000cd782446c50bd2f05f81e9e84007cc5e3fabca001e0e3e8ba8b0003e3cea29a932403e300000000000000047f43f9828256160be4f26a48008c)) (.node 35 (.leaf 0xae79274a50035d3fb3d4e500033d0bcf30785402050000000000000000e8f9007c157153be0d6cf47000c77557f691a001b80df3e45e00011f370dece478010f0000000000000003702ef284331393cb3af0a888008eda94d5b16002e732c368560002373ccfecec68030e00000000000000038c8df2e826a2e0f73afcb48c004bea6b2a4e9002eb3fb094a900032b3cc2fcbca8030a000000000000000288f3a3b82aa2a0b63decf4bc004b) (.node 36 (.leaf 0x5cd700104ff3b4fd000d587a61f874df000433b1b8000000000000000dc7a6000e743f4f35fa000c05ea75f4d700318791f8d7000544faf3d4dc55000c43b3f400000000000000074faf0006731785cbd8c0028b618a751fce87a000b849cef33f0000df661993d1b400bf0000000000000007721ec982cb4796c8e7c26268000eda34cdcd7000e7a2c67197000037ec3b93d3a000ee000000000000000b814dcdd30a0ae8e4e7c3733c003b) (.leaf 0x2fc7c021ec7f0fc7c00504f2ffc789556008491a56000000000000000cff2fc00c45bc7cdfc0c0060bcbf21fcbc0101cbf03cbc00a2bf13fcb66a29001a665a9000000000000000fff13c0038a7cbc2fc3c00917c7f153e8c0141e8fa3fc400ea27f05e873e0f00586cda9000000000000000d17f0400fa0be2f31fe000d51fc75f1e8c03e2685e8d4c00601ff0fc3d160700f0acfe200000000000000073ff0c006a85695c3dd0002a3708a)))) (.node 40 (.node 38 (.leaf 0xae3b000ad1785f578002452fb8d789357002491c56000000000000000ce2fb800195cd799c1dc001a8bf3a5b34c00453ecb7a2c0019714dc37663b9001b774b9000000000000000bb14dc0034b4bfe2ce7c00154d7355b94c0104beeb732c00856c8de3737cfe00430b9090000000000000003bc8dc00837a3f33f3ac00c072bc54e6b00041e3ba33f8004a98f3b2b37c2f004a4ed090000000000000002e8f3800c2af2b33e3dc004563fc5) (.node 39 (.leaf 0xd3001cfd19c67590c51141dcc215d100073f41cf74000000000000000b30003f395c69ddd00037c5237cd2b10038ea2e8fcabc3828a27f04a8b3000e3a8ececb000000000000000d10001b3fa0be2770001fcad1fc2dec002f0e4d737c571946448f9354dc00074f41d374000000000000000ec00027cd9d3dc99c0025e5223dd2bc0037218ff3dcbc3788187a60a8b8000dc873b2dc000000000000000dc0001e4e743f4770001e9a85ea2d) (.leaf 0x37003391e4dd0f45d4450422edc7550005644bb9b6000000000000000770003ce64794fcdc0036260bcbf23d0032e2acbf0a8a28b82af13e8aaa000a92a666cb000000000000000ff00038938a7cb4e8003b3a3fc7a3cb0015b06b2ef392c54144d81e13cd00056c0b3bf20000000000000008b0003eea73ab3d0c0036a68be3f8ce002a4c9e3be353981601ac3bc3cd00063f0a2fe2000000000000000ce00023bda2fe390c0025e58ab3f8))) (.node 41 (.leaf 0x66000f46d358bf4589524523a8d7550003714bfcb60000000000000006600007f0bfc7f99c0001e1a8bf3a99000dc923ecd6a206709214dc26aa0003d2b774df000000000000000bb0000dd34b4bf6e80003727cd72f990015a12beed632036812c8de263b000ce878ba0f0000000000000003b00032e837a3f3f8003cb88f2b8fac002a4a8e3bca3e3090a88f3a2a3b000cb8acee0b0000000000000002e00023bc2af2b3b8002cf0fe3f8f) (.node 42 (.leaf 0x5cfc972785b8001d174123cdd7001477354bcdb60000000000000000023cfb06f8579003dd32c2a3708a00b4dcfd3acae700051141dcce170074773f4ac3e600000000000000000dccff3b2caae003dd37c7a08c7a007b2f0eca62ec00194644afb3d40075074f42e3e400000000000000000afb27c92e2ac0021de5e5a88e7a00ae3e2b8791d8002ec8b8f5f2ac00aa0bc2b372dc00000000000000000f5f3982cb178000a3b26a6b518e) (.leaf 0x732748dd3b5300195645ac3bd30071717a091e5200000000000000000ac3847d91fd30021ce5e58ab3f800b0d9545b2eb300067987d41e3300b39a813735b100000000000000000d41fdd3436b3003e4c91947d3f4005cd85417cdb7003f27722345d8001cfe0587cdb9000000000000000002345f36f4976001fe0d0d51fc7500aca4eb2d4f5e003f28b27f44a800ecc13a4d0e57000000000000000007f4443dd4bd6000b21fcad1fc2d))))))) (.node 64 (.node 53 (.node 48 (.node 45 (.node 44 (.leaf 0x5b09445759b70033d46d03a91f000dfc84b4fd090000000000000000003aa3f43fd3f0023dcc14563fc5002a274a8d7b5e0033d0a88fba2e00cec0785c1e07000000000000000008fb807c15f1700031acf0fe3f8f004fd15054dd07002cf33f21edcf00199a81b775b90000000000000000021efcd2cb54f003c3c91917c7f1008ea3e3ac7f0e002cf83af1fe8e00aa815215165700000000000000000f1fc451c17c700083bb3a3fc7a3) (.leaf 0x8ff2a568fd0800d3dd5745e42c0000000000000000a2174576b747000cfe42c45dd1c00d0f94b5478b92004fe3d8541e3c00f2b8be8bb818000000000000000051fe8b887e8b000c2b81aaafa2c00f0af8cd1d46e1005cfd19144df000fe3fcff49a90000000000000000059cff4893774000e09a92e8ddd000f3a4b4d1d526900f8fe3d3fca4000d71d4744e5e00000000000000000f70744762cb8000b8e5e354b2e0008d795b547a88600)) (.node 46 (.leaf 0xa25166ab5d740029e2acf5cfd0000000000000000026fcf547f0550000fcfd007c154002e70e78fc733d00575e99545748000df3547f01ec000000000000000019747f8950ff0003701ef1543fc0033f358c0c571600adaea56bad48003e3358bac5ec000000000000000026e8ba47f0570000fc5ec05c15c003f831bc48ff1600e24162bebaa80029e0acabcf3c00000000000000003f9cabc8e0aa00038cf3f3b82a8000e72e78f4bc0e00) (.node 47 (.leaf 0xf8fe3d3fc00284eb2e4bbc00039400000000000000cb8bbcbb0000eecb8e5e35430a2248e7a5b9433c0068f8d73731c002ecfe37cd5c0002ec00000000000000ff8d5cd70000eeca0ba92e8a260888b2faeeb68c0033571fc94453dc004c8ff37f2288000000000000000059737f094bff000622288ea2ffc00f38fbc11154e900ad2e87cba17c00be0ff0ba3a980000000000000000a6e0ba37c757000c23a98421d5c007b8b383b2fce900) (.leaf 0x8ff2a568f00312e3ee5b8f0003920000000000000082eb8f33c000bd3cfe42c451c1712e0fa4b94b4c00e88fd3e7a0e00353f2b7ed4e0002e300000000000000a2fd4e570000bd3c2b81842c518c1f0af8eebe8c00b4a3fc64eb10035dfcbf3ff100026d00000000000000a43ff174c000b5cc29a8042dd44c1fb24b2f8d700097f2e8f8fe3002ebfcb83ea30002eb00000000000000fc1ea3e8c000ea3a0ba0aa2b288888b2fb2f87b00033)))) (.node 50 (.node 49 (.leaf 0x5cfd19000df334eb2ec000d5d37c0000000000000049cbb4890724754fcd5d3dc0003dce2f4749100355d5f8d737000ae2ecd7154000faf3d400000000000000f70544562898cc8b8faf3ec0002ac8d7d8f6a0008a7a0dad43eb50035d1751fcf500033d0000000000000026fcf547c000b1c0d4f5007c1571515d0f54fc7000c718abdafeb002eb1750bcab00032b000000000000003f9cabc8c000e23184f353b82aa2a0551fd4f4bc004b) (.leaf 0x8fd3e7800d3f53d3d54000f83fd300000000000000a215445631468c2cff83c460003d3d0fd8f6a003e3f84fe3d8400e3fa3e3e8b000f43fe30000000000000041ea8b884e09721cff43f990003e3e0fe4c91003d3f4a3fc64c00d475dd4dd1000dfc35500000000000000a4174174b751848c3dfc0430003d5dd34d37c0037cd2f2e8f8c00a8aebd4d81000ff0fc300000000000000f4160160aca2c82b0ff0fb30002aa8d3dd37c0008c7a)) (.node 51 (.leaf 0x571fc94003dcb749cef00021ecdf0000000000000049633f094b2d0757721ecdd00007fe2ce7c11000d735ad2e87c0017c5eaa0ef00035fcae0000000000000082e0ba33c70509fcf35fc450000d76e8a3837000d72f5757d10007ddb70df3e00002ed1f0000000000000019745e8110de5353702ef2e00013f33f3acc10032bc5ad86a7800d7f5e3e33e000cafe2e0000000000000026e81a473056b1f0fcafc060003173f832bcb0032b8f) (.node 52 (.leaf 0xa3fc802b3d4b16d4c00741e5cf9600000000000000a417410037538cac3e5cc00dd4f16dd3950007a394e853e8c0141e8fa3fc800ea3ba0aeb00000000000000583ea3003ea3721e2ba0800fa8cc9f32fb000d52e8b55cfe00144f4394eb000bbce5e3940000000000000049cbbc000f2c774fce5e0003cb334e2fa580095796e05cd700104ff3b4fe000d5cba92ec0000000000000059cd5c0039dc774e0ba9000e770c8f3afac00c06e9b5) (.leaf 0xd2fc00bf0345f974003451f74d700000000000000a613450007570ca0d1f74001d5cd755cddc003a87f3aa211400bf17c4969c003bf35fc790000000000000082e3bf0007050dfcf35fc001c14d7ae46640037cd71fa2514021ed7c4929c00c5ecafd390000000000000026fc5e003056b1f0fcafc00c15b172e72a400c8f2b4f1dabc01410b7a317400cab4f372b0000000000000019fcab0030ab7211d4f3400c2af2b11d1fc00c553fc5))))) (.node 58 (.node 55 (.node 54 (.leaf 0x1c001b3f40b37c971d47445f535400000000000000f70000763774c481c0001bcddd3dc55c0017e5217dd2e000263f4df06869228bb4d5d17800000000000000cbc000bb0724f5cfc0003dc1c93dcae4003a79735557bc003d2b8f4394aa2e48b8e5e284000000000000008ac000bb0f2cbbcfc0003543cb3346e800394a7f96a8bc0037218ff3dcbe37c818ba92ac00000000000000aec000d739dcbbce00002e8e770c87b8002eba8ee9a7) (.leaf 0xd001afcb037e3935816015c37c300000000000000f3100060be8bc820d0001bbfa2fe350c0017e78973f8c20022bcbe3c6161e0aa8bf43d6100000000000000c3e000a8ce09fa3cf0003993827e3a04003a7b4fd35c73003c5737499644dd174121cd9600000000000000541000749bf34ca730003516fcd36dd0003547a394e8b10038ea2e8fcabc3838a2ba0aaa00000000000000ac2000e8fea3ba3e20002a2fa8cc97b0002f8af2e8a7)) (.node 56 (.leaf 0x15000bc7f094bf054d53450364d700000000000000551000368bff0ca150000bf2ffc7f55c0003e3a87f3a62000687f3dc2949c2a33f21ec59000000000000004960003bcb2d0ff770000dd2cb47fae40002737cd71f62002691e7dc2909e2a45e02ed19000000000000001d7000c710de53f3700032e43793f2e40038bc8f2b4f1d001aeaa0b7ca1610b8aa4f362a000000000000002ee000c8f0abb231d00013bc2af2b1580014f8fd3f8f) (.node 57 (.leaf 0x5cd85417cdb7003f37732288cf00000000000000000773885bf357500228ae26fcc49002fb0d0d52e8b500aca4eb2d4f5e003f38b2ba8aae000000000000000008b274f753b9f00ba8842dd4cc1000b32f8af2e8a700af1b3fc0a2ec001d47445f73d400000000000000000744762cb8cc8005f71bcb2e2ac001ddd7e7a80e7a0051263fcae06800228bbcf5f17800000000000000000bbcbb0c28eec00f5f3dc30a2ac003667a733c865b) (.leaf 0xfd9545095b70011f47f03651f0000000000000000047f8950ff5350003653f43fd3f0011fc41c553fc500ae83eba0375e0011f8ba4f762e000000000000000008ba47f057b1f004f7407c15f170001394f8fd3f8f00a3c3e8f03753001d57455c37d30000000000000000074576b7478c2005c3407dd1fd3001dcd7e78973f8005166a8fd3c410022ab8ff43d7100000000000000000b8f33c705bd300f43c451c17d3003647a7b4fd35c)))) (.node 61 (.node 59 (.leaf 0xcbb09d7c7b080000000000000000cd71575f0b3400f3114516adcf0008bc40f55b73c00d0f94b5478b9200c24162bcbe3c0000000000000000ce82b8bf2e2c00f0fe8ae87e82000cd7c25b3fa0800a056c1adfc5f200e051263f4df00000000000000000ec9b09cfd1d000fccff0fd3750000dc5f41f4dd4000a654e1add517c00bcae3d2b8f400000000000000000b8ec0f4af37000acc8b8fd3fd0000dc656154ff4000770b01d4ad59600) (.node 60 (.leaf 0xc21044bd59e400000000000000002e8b38fcd4dc003bb8d58fe0750003bccd33f81d4002e70e78fc733d0099a49d692b4800000000000000003bcccc58fc74002aa8928fe0ff0003bc4cf1583fc003f831bc48ff1600374eb153f4480000000000000000551557554b7400451705729b3f0007721ef456cfc00cdf81b5072b86003d8ab2e2acbc0000000000000000b3e2ceaaae88008ee82ae0fe2b000e2b21a8af8ac004b883af3a3ec900) (.leaf 0x1cad1b3f40037c000000000000001c6706cfd0037cfccff0fd00003541c5f41b4dd43d45554e17dd500055ec792f0e40037c00000000000000f0fe0f8fd0007837c6e46f0000f5ce08a9268d9d0c8bba096db570009762114687f3dc00000000000000006619b1f1fffc005c737a3d4bd2000552364f72f4800a646e02d3d4fe0099248dc923ec0000000000000000b32ec3a2ff8800aaa0921fcdff000a21898ea37fc007b8b383b2fce900))) (.node 62 (.leaf 0xda3dafcb003e3000000000000000d6276bf2c03e3f0fe8ae840003a10d5c25b3fa0be2505dc17dfc4007cce632a4c9003e300000000000000c3e2eeaf2c00e133d68968c000fa3c2a81a2ada2cc1b0a38edb5cc00b4d3b45cfd10027500000000000000f3fc2f2fc40079f839d19cc000e5ca29882e295c489fb24b2f8d700097735cbc5730019600000000000000731cdf15cc01965c3772fc40001f5512145516f4936f71b41d4fd00068) (.node 63 (.leaf 0x374eb153f001060000000000000066199b51b4019649633fb3c0005cf7721ef452cb506cef81b90b3c00e03747f391e0010f00000000000000731ceda47800b94d751ed300005cf62228aca647849cbac2ee3e0c00b3cbb09d7c70029200000000000000ceb19b53340392c3a9879bc000e738bc40f55343632e0fa4b94b4c00e8cb90d5b06002f300000000000000c3d2edac3800f1f3b946970000e7382981aeaa73881f0af8eebe8c00b4) (.leaf 0x150fcbc7f000bf00000000000000150572f1fc00bf5c737a3d40000f5150364b72f4876554de03d3d4003d661b0f46d000bf00000000000000731ce3a1fc00b915526d2fc0000ff6222886a0bfc49bb839c1b1fc003719a459fd500275000000000000001d4734fcd4030d3bb8d58fc000e1c194c513f81d61d15d0f54fc7000c7665a2d46d0019600000000000000370ddc54fc010615546d4fc00053f2601aa1543fd363be35ac44fc00c8)))))) (.node 75 (.node 69 (.node 66 (.node 65 (.leaf 0xd3b45cc009c67500000000000000d174373001cf74f0114114a571c48b3dcc3f300029ddd34d37c0037cd2b1a8b8c00e8fca00000000000000b3e0ce3002cecbac28a2e87e823a1d17f05b30003e2770b21fc001fc2dec792f000d737c00000000000000dc75074001d374370644663674c48ec8f927c0003dc99e0d65e0023dd2bc8637000ff3dc00000000000000b8ce0dc003b2dcacc818d539d03b4dc7a61e40003f4770b21e9001ea2d) (.leaf 0x3747f38004dd0f000000000000005515656003b9b645150452191e4ca7722efce00014fcdfc0f62003cbf23d8ab2c00cbf0a00000000000000aaa28a900266cb8ae82aa0ce29b83fff13f890003cb4e883bb3003c7a3cb90d5800b2ef300000000000000cd516560033bf2f311441629cec428bd81fee0002b3d0fd8f6a003e3f8ce632a400e3be300000000000000cd607630022fe233160160b68bc82ceac3a3b0003e390e1ce5e002b3f8)) (.node 67 (.leaf 0x661b0f400358bf000000000000005515737003fcb61512452682ff0ca6623a87f00007f99c1dc1e000bf3a99248dc003ecd600000000000000aa2a83d00374df8aa0921bcd2d03fbb14dcdd0000bf6e8a3837000d72f998495800beed6000000000000003bcecce000ba0f2aa8128720dea3f3bc8df2e00023f3f832bcb0032b8fac2a2a400e3bca000000000000003bc2ccb000ee0b26c0a848f0abb232e8f3a3b00032b3b831acf0023f8f) (.node 68 (.leaf 0xd3b4803d3b4a9600000000000000d174500f4b4796f01141002df3c4ab3c4cc00b7ce36dd3950007a394e8e240403e3e8c6900000000000000e280b00f8ecf6bfc3ea2003e823a1d17f0400fa0be2a616e000fd1fc5dec7a000ecf439400000000000000dc75000f4373943706440036fccc8eca5a000dbf33499e158005aa96e8e0510031cff06800000000000000ec9b000c73b36cfccd580039d03f4dc7a6000e743f4a656a000e85ea5d) (.leaf 0xc21040316bec61000000000000002e8ba00c78bb0f3bb8560020dee3f3bc8dc00837a3f2e72a400c8f2b4fe241000e9e3869000000000000002e82b00cacef0b37d4a90030abf232e8f3800c2af2b2a62c4004fe3f4f1d8bc032b0b70b000000000000001d60700f08efe2c71601003e2bc821d533400f8afcb45dc1c007294ff222414032bcbc0900000000000000ee829003a6676bcbea2b000e29f83fff13c0038a7cb8e742400b3fc753)))) (.node 72 (.node 70 (.leaf 0xae1b2b80b3dc00000000000000006606caf0f2dc0008b8fd3fd03b4005f61b4ff43f40009217dad57e2d002a2f0a8f73dc0000000000000000ee0f8af380d80000a86f36fcbbc00aa9268dbf0c800031adb0fea9a71924c00d70a4f7000000000000001d25700348fcf6f31145000dff04a191c540037fcbf55cddc003a87f3ac210400d73ec6100000000000000ee1b9003b7746fcba197000d2d07fbb14dc0034b4bfae46640037cd71f) (.node 71 (.leaf 0xa0d9fc7026f3000000000000000061767f083ff200014516adcfc42005c15bfb73eb3001dcd7e78973f8001044bc7b2c6100000000000000009399d33737630009879bcd0de7300d41fdd3436b3003647a7b4fd35c0050649737cc29000000000000000018b935cfcd2f000772fc5bd21f5002345f36f49760016e1acfd1fc5d00a49ce92bced60000000000000000eccf2acf88d90008929cedf3a3f00988ae2b7cc89000b32f8af2e8a7) (.leaf 0x512606d75829000000000000000009b8f4fcfd0f00046d4fd0ff53f0003aa3f43fd3f0022c68f4fe3f4f00a499e920a6d600000000000000004644f8fcfe0f0008928fe0ffa3f004c553f83fe3f0001394f8fd3f8f000fd3d3f0950f000000000000000005767548fdb6000705729b3f4ca0003658f6cfd4f001c1d727294ff200416293f4dc0900000000000000001999d1b7752f00033fb3cb2d5cf0021efcd2cb54f003427a3b3fc753))) (.node 73 (.leaf 0xb2c759c7c40c0047f1de0537340051b9c7896dcf0008bc40f55b73c00f0fb48d0d4792000000000000000061e0ae8bfc3c00ce82b8bf2e2c00f36e8be89a8900047fc3fb86a24002036c72eacb71000000000000000069228ff4dfd000ec9b09cfd1d000ff4ff4fe136400074dfd3b84d90002c34e72e863710000000000000000be3f48b8e5e000b8ec0f4af37000ae48b8fe1bec00074e5e3106fb0007c8b1b04aeb1000) (.node 74 (.leaf 0x49e0af35d3d0008a9b317a551c0086ff3573f715000cfd3d047dc54008e7427a3d334d00000000000000004dfc573f21ec00771dde05b7740049773f815b3f0007721ef456cfc00c3f818d0d178600000000000000008e3c583ae1ec008becc15a5d140086e83a73f717000cfe1ec45dc5c004f881bd0a3f86000000000000000049e0ae2bf33c00ec82b8bfaae000cf9e2be0ec2a000b8f33f8bb0a8008e7427a373c8e00) (.leaf 0x971dcff400037c1c6706cfd0037cff4ff4fe0000d18145f51b84d91585494f52e8600086000000000000007f3b46ec000394fcfd0f4fe003843786ec6f0000eeca8a5a25492e2248b635ad45bc00680000000000000049c2a37f23ec006619b1f1fffc005d637f3e8bed0007723ecb82fb4002c06e42e2e871000000000000000020c221d71cdc00ec1bb1f3eae000fb91d71fccba000b81cdcff32e8008e46e42f3bc8e00))))) (.node 80 (.node 77 (.node 76 (.leaf 0x73bb56cd0003928bf1d15a1c021222d6cd67c000bd3cea42845d91f12b0e34ad45cc00e8000000000000009358be8b0003e30d6276bf2c03e3f36e8be88000da2055c35b86a2561509dcd2eac8008c000000000000004cff1773000196731cdf15cc01965c2773fc80005ba7321cf106f85307c3b5304ae0008800000000000000b0c719d3000216f0fcdf1fc80386f819d39cc000e6fb0c4cf51b2ca268f3b53d47b00068) (.leaf 0x54df37f0000df150572f1fc00bf5d637f3e80000ba150364b82fb479548dfc2e2e8000e00000000000000924571d70000371c2772f3e800eefb91d71fc00006f181c54bf32e8ae054dfc3f3bc003b00000000000000875cff3500034d0967307a54025586ff3573c000b4c0d535007dc57c545d43573d3000d3000000000000008758be2b0003cb1c6276bfa803eacf9e2be0c000e831853358bb0aa8a055c3d7373c0073)) (.node 78 (.leaf 0xb0c73000dcc23573fc3e0001cd395839d1886571654b3dcc3f300029df334f0d00037cd500000000000000bc383000ff0eaab3e0ce3002cecbac28a2e89aa19a273ff0fb00001697c0b332c003708e000000000000007f3bc0008f937c74ff0e8001d13811c6e4093674754ec8f927c0003dcb3e0d4d10023dd500000000000000be37c000faf2acb8ce0dc003b2dcae4818d619cc9b874faf3a80001787c8b2b2a003618e) (.node 79 (.leaf 0x4df4e00022edcf771dec8003b9b949751e81191e5457722efce00014fc3fc2cc1003cbf1000000000000008e34e000f2fe8e8bcec160011a5786e81a533116b8fcff2fc460003c74f882be3003cba300000000000000b2c76000d81e3347d3ec800339b151b9468129ce6718bd81fee0002b3f0ff8cc1003e3f40000000000000073b89000ac3be347e2fe80022da111d68908768b721ceac3a3b0003e3b0e3ccd1002b3f4) (.leaf 0x7f0006eca5a39474fd0005b3719011c6ec0036fc774eca5a000dbf334b3e3580055696e00000000000000069000d5cfaf178ec9b000c73b36cff4d5c0019ccdb874faf0006731782c36a400a8b610e000000000000004d8bd00023a8df771df28003fcb911526d0942ff0756623a87f00007fb3c3dc11000bf35000000000000003e0bd0002fb8ae8b2ec170011c5726c0a827c65709fce2fb8470000d73b83181f000bf2f)))) (.node 83 (.node 81 (.leaf 0x49c00d1ef2fd498a9ba008591a4786fd1e003116bcfcff2fc00c45bc78e742400e0fcb530000000000000087400e2b5337cb15627005a4eda949fe2b003e2b7011d533400f8afcb41dc3c00d154ff100000000000000b0c009d3c4ce1673fcd0058745905839d3002df3675b3c4cc00b7ce36f33b5000d5394e00000000000000068c00ea3ff0d69e280b00f8ecf6bfc2ea3001aa1da273ff0c006a85692c36e000ae3700e) (.node 82 (.leaf 0x692286e48f9178ec0009cfd1d36c37c0006f3674f5cec00027cd9d3dcaa40028f5723d57000000000000003e3b40a8a5a284b8000f4af3729426c0006f36fcbbcec000254dbf3343b8002d40fe96a800000000000000924001d71c543715277001b4fcb959b1d7000dff075191c540037fcbf51cdfc001547f3500000000000000698002ed2fb8798a1bb0025d1c4726d2ed0006570dfce2fb800195cd7aa42c4001fcbf1f) (.leaf 0x20c22946d81c31ce0009ec3b3b63f3b0009729cee738b0003eea73ab3a04003abe8fe35c0000000000000061a08689ac3961ce0008bf2e2f6333d00068f68bfa3ce00023bda2fe3a040028f5ceb35c0000000000000020c229d1dcc031e200093fc5cf6df830009ce571e5cb30003f395c69dae0003acd737c5700000000000000b0071892c4ce06b3000f1acf4696a820009cedf3a3fb3000351b7ce367f0003d4af394a8))) (.node 84 (.leaf 0x4982826d23a859660001f1fffc2f1550002fc2ff0ff6600007f0bfc7faa40000f1fcbf1f00000000000000920570921c5426190002f2fcfcdfaaa0001fcdff03f190000bf37fcbf5580003f2fc7f2f0000000000000049e0a51e22ed49660009e47bb92f4d7000d3191e5cf770003ce64794f8e4003a3e0fcb53000000000000008618b82a53368a190006baaceecb8ee000e0fe2bb831d00018bf8afcb45800173a3d4fa3) (.node 85 (.leaf 0x22277323cd590018b935cfcd2f000773fc9be15ba0023cfb06f85790036e32cae3700e00000000000000000229d3dccc310098b93fcac36e0009d39cecb2e6f00dccff3b2caae0036e3ac7b08c5b00000000000000001dc8b85f72ac006606caf0f2dc0008b8fe1bec9b8005f71b86fb1780009392eae9718e00000000000000002286ecafb178009b09cfe2e36c0006ec6f24b8eec00afb27c92e2ac0022c68f5bc8e5b) (.leaf 0x1cf73f0365cf00057685b4fdb900073f815b3f5450003658f6cfd4f001c3c51d154ff100000000000000001cf83a53768e0066407a5c1e5700083a73f717b8f00537407dc5fc700083973a3d4fa300000000000000000579c75c163300637685343db10009c7896dcf671005c15bfb73eb3001dcc51d4573f400000000000000002286cdac39710093b17a1d1e430006cd67f647bd300ac3847d91fd30022c68f5ceb35c))))))))

def checkSameGroup : Bool :=
  (List.range 344).all fun i =>
    sameGroup.block 4 344 i == (geometryTables.compatibleWith i &&& firstMask)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000000 in
lemma checkedSameGroup : checkSameGroup = true := by rfl

lemma sameGroup_eq (i : Nat) (valid : i < 344) :
    sameGroup.block 4 344 i = (geometryTables.compatibleWith i &&& firstMask) :=
  beq_iff_eq.mp (List.all_eq_true.mp checkedSameGroup i (List.mem_range.mpr valid))


def tables : WeightFifteenPrefixVerifier.Tables :=
  ⟨starTable.block 8 60, geometryTables.candidatesAt,
    sameGroup.block 4 344⟩

def relabeled (a i : Nat) : Nat := WeightFifteenConcreteGenerators.imageAt a i

def cut (topIndex op : Nat) (state : State) : Bool :=
  if op = 0 then decide ((state.picked ||| state.available) ≤ lowerBound)
  else if op ≤ 48 then allSetBits (fun i => decide (relabeled (op-1) i < topIndex))
    344 (state.picked ||| state.available)
  else if op < 112 then state.remaining == 0 &&
    decide (moveBits (relabeled (op-64)) 6 state.picked < state.picked)
  else if op = 112 then decide (upperBound < state.picked)
  else decide (op-128 < 16) &&
    state.remaining == 0 && state.picked == normalFormWord (op-128)

def initial (topIndex : Nat) : State := ⟨1152921504590069760 ^^^ tables.star topIndex,
  (2^topIndex-1) &&& tables.compatible topIndex, 2^topIndex⟩

def seedList (n : Nat) : List Nat :=
  (WeightFifteenConflictRows.setBitPositions 6 (normalFormWord n)).reverse

end WeightFifteenUpperPrefix

namespace WeightFifteenConflictRows

lemma positions_nodup (fuel word : Nat) : (setBitPositions fuel word).Nodup := by
  induction fuel generalizing word with
  | zero => simp [setBitPositions]
  | succ fuel ih =>
      by_cases empty : word = 0
      · simp [setBitPositions, empty]
      simp only [setBitPositions, if_neg empty, List.nodup_cons]
      refine ⟨?_, ih _⟩
      intro present
      have yes := setBitPositions_sound _ _ _ present
      simpa [Nat.testBit_xor, Nat.testBit_log2 empty, Nat.testBit_two_pow_self] using yes

end WeightFifteenConflictRows

namespace WeightFifteenUpperPrefix

open Finset FiniteMaskCoverEnumeration WeightFifteenIndexedSearch WeightFifteenIndexedSymmetry
  WeightFifteenLargeCatalog WeightFifteenVerifiedSearch WeightFifteenPrefixVerifier
  WeightFifteenIndexedPartitionTraversal WeightFifteenConcreteGenerators

lemma first_partition_model (s : Fin 15 → Fin 6 → Finset (Fin 60)) (isCover : IsCover s) :
    ∃ selected, covers partitionOptions (eligibleMask 0) selected ∧
      selected.image Prod.snd = firstGroupIndices s := by
  let star := s 0
  have allowed := isCover.1 0
  have exactCover := isCover.2.1 0
  have partition := isCover.2.2.1 0
  classical
  have individual (i : Fin 6) : pack ((star i).image Fin.val) ∈ directCatalog 0 :=
    (directCatalog_mem 0 _).mpr (indexed_star_in_catalog 0 _ (allowed i) (exactCover i))
  let index := fun i => (directCatalog 0).idxOf (pack ((star i).image Fin.val))
  have at_index (i : Fin 6) : (directCatalog 0)[index i]? = some (pack ((star i).image Fin.val)) :=
    List.getElem?_idxOf (individual i)
  let selected := Finset.univ.image fun i : Fin 6 => (pack ((star i).image Fin.val), index i)
  have valid : covers partitionOptions (eligibleMask 0) selected := by
    refine ⟨?_,?_,?_,?_⟩
    · intro a ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      exact List.mk_mem_zipIdx_iff_getElem?.mpr (at_index i)
    · intro a ha b bit
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨p, hp, rfl⟩ := (star_mask_bit _ b).mp bit
      exact allowed i p hp
    · intro a ha b hb different bit on_a
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨p, hp, place⟩ := (star_mask_bit _ bit).mp on_a
      cases on_b : (pack ((star j).image Fin.val)).testBit bit with
      | false => rfl
      | true =>
        obtain ⟨q, hq, place'⟩ := (star_mask_bit _ bit).mp on_b
        have eq : p = q := Fin.ext (place.trans place'.symm)
        subst q
        obtain ⟨_, _, unique⟩ := partition p (allowed i p hp)
        have same := (unique i hp).trans (unique j hq).symm
        exact (different (by rw [same])).elim
    · intro b needed
      have inside : b < 60 := by
        by_contra outside
        have bounded : eligibleMask 0 < 2^b :=
          (eligible_bound 0).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt outside))
        exact Bool.false_ne_true ((Nat.testBit_lt_two_pow bounded).symm.trans needed)
      obtain ⟨i, member, _⟩ := partition ⟨b, inside⟩ needed
      exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ i), (star_mask_bit _ b).mpr ⟨_, member, rfl⟩⟩

  refine ⟨selected, valid, ?_⟩
  simp only [selected, firstGroupIndices, Finset.image_image, Function.comp_def, index, star]

lemma first_catalogue_at {a : Allowed} (ha : a ∈ partitionOptions) :
    (directCatalog 0)[a.2]? = some a.1 := by
  rcases a with ⟨word, i⟩
  exact List.mk_mem_zipIdx_iff_getElem?.mp ha

lemma index_bounds (a : Allowed) (ha : a ∈ partitionOptions) : a.2 < 344 :=
  direct_first_bound (first_catalogue_at ha)

lemma layout_first (layout : ∀ g : Fin 5,
    (List.range 344).map (fun i => starTable.block 8 60 (344*g.val+i)) = directCatalog (groupAt g))
    (a : Allowed) (ha : a ∈ partitionOptions) : tables.star a.2 = a.1 := by
  have hit := first_catalogue_at ha
  rw [← group_zero, ← layout 0] at hit
  apply Option.some.inj
  have below : a.2 < (List.range 344).length := by simpa using index_bounds a ha
  simpa only [List.getElem?_map, List.getElem?_eq_getElem below, List.getElem_range,
    Option.map_some, Fin.val_zero, Nat.mul_zero, Nat.zero_add, tables] using hit

lemma supports_first (layout : ∀ g : Fin 5,
    (List.range 344).map (fun i => starTable.block 8 60 (344*g.val+i)) = directCatalog (groupAt g))
    (a : Allowed) (ha : a ∈ partitionOptions) (p : Nat) (hp : a.1.testBit p = true) :
    (tables.candidates p).testBit a.2 = true := by
  have small := index_bounds a ha
  have quotient : a.2 / 344 = 0 := Nat.div_eq_of_lt small
  apply actualAllowedAt
  simpa only [geometryTables, if_pos (show a.2 < 1720 by omega), quotient, Nat.mul_zero,
    Nat.shiftLeft_zero, show starTable.block 8 60 a.2 = a.1 from layout_first layout a ha] using hp

lemma preserves_first (layout : ∀ g : Fin 5,
    (List.range 344).map (fun i => starTable.block 8 60 (344*g.val+i)) = directCatalog (groupAt g))
    (reverse : ∀ p i, p < 300 → (geometryTables.candidatesAt p).testBit i = true →
      (geometryTables.starMask i).testBit p = true)
    (rows : ∀ i < 1720, rowSafe i = true)
    (a : Allowed) (ha : a ∈ partitionOptions) (b : Allowed) (hb : b ∈ partitionOptions)
    (_ : a ≠ b) (separated : ∀ p, a.1.testBit p = true → b.1.testBit p = false) :
    (tables.compatible a.2).testBit b.2 = true := by
  have small_a := index_bounds a ha
  have small_b := index_bounds b hb
  have same_mask_a : starTable.block 8 60 a.2 = a.1 := layout_first layout a ha
  have same_mask_b : starTable.block 8 60 b.2 = b.1 := layout_first layout b hb
  have compatible := full_compatibility_sound reverse rows a.2 b.2
    (show a.2 < 1720 by omega) (show b.2 < 1720 by omega)
    (by simpa only [localStar,same_mask_a,same_mask_b] using fun (_ : a.2/344 = b.2/344) => separated)
    (by
      simp only [localStar,same_mask_a,same_mask_b]
      intro p q _ ap _ bp _
      exact Bool.false_ne_true ((separated p ap).symm.trans bp))
  change (sameGroup.block 4 344 a.2).testBit b.2 = true
  rw [sameGroup_eq a.2 small_a]
  simp only [Nat.testBit_land, compatible, firstMask, Nat.testBit_two_pow_sub_one,
    decide_eq_true small_b, Bool.and_self]

lemma first_indices_bounded (s : Fin 15 → Fin 6 → Finset (Fin 60)) (valid : IsCover s)
    (i : Nat) (in_first : i ∈ firstGroupIndices s) : i < 344 := by
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp in_first
  have located := starWord_some s valid 0 t
  exact direct_first_bound (by simpa only [starOrdinal, starWord, group_zero] using located)

lemma first_indices_card (s : Fin 15 → Fin 6 → Finset (Fin 60)) : (firstGroupIndices s).card ≤ 6 :=
  Finset.card_image_le.trans (by simp)

lemma state_picked (s : Fin 15 → Fin 6 → Finset (Fin 60)) (part : Finset Allowed)
    (same : part.image Prod.snd = firstGroupIndices s) (state : State)
    (model : Progress partitionOptions part state) (finished : state.remaining = 0) :
    state.picked = code (firstGroupIndices s) := by
  obtain ⟨left, _, remains, _, selected⟩ := model
  rw [finished] at remains
  have empty : left = ∅ := cover_empty partitionOptions partitionOptions_nonzero left remains
  simpa only [empty, Finset.sdiff_empty, same] using selected.symm

lemma geometryInitial (n : Nat) :
    initialFor (seedList n) = chooseStars geometryTables (seedList n) (allObligations, allCandidates) := rfl

def RootResults : Prop :=
  ∀ n : Nat, n < 16 →
    ¬ HasCover geometryTables (initialFor (seedList n)).1 (initialFor (seedList n)).2

def PrefixResults : Prop :=
  ∀ start : Nat, 288 ≤ start → start ≤ 289 →
    ∃ transcript : List Nat, (checkPrefix tables (cut start) 6 (initial start) ⟨transcript, 0, 0⟩).isSome

set_option maxHeartbeats 5000000 in
theorem middle_from_checks
    (layout : ∀ g : Fin 5,
      (List.range 344).map (fun i => starTable.block 8 60 (344*g.val+i)) = directCatalog (groupAt g))
    (reverse : ∀ p i, p < 300 → (geometryTables.candidatesAt p).testBit i = true →
      (geometryTables.starMask i).testBit p = true)
    (rows : ∀ i < 1720, rowSafe i = true)
    (actions : ∀ a < 48, checkAction a = true)
    (roots : RootResults) (prefixes : PrefixResults) :
    ¬ ∃ s, IsCover s ∧ (∀ t, IsCover t → partitionKey s ≤ partitionKey t) ∧
      lowerBound < partitionKey s ∧ partitionKey s ≤ upperBound := by
  rintro ⟨s, valid, minimal, above, within⟩
  have key_above : lowerBound < partitionKey s := above
  have above_start : 2^288 ≤ partitionKey s :=
    (show 2^288 ≤ lowerBound by decide).trans (Nat.le_of_lt key_above)
  obtain ⟨start, low, high, in_first, largest⟩ := maximum_first_choice s 288 above_start
  obtain ⟨part, cover, same⟩ := first_partition_model s valid
  obtain ⟨a, a_mem, a_index⟩ := Finset.mem_image.mp (same.symm ▸ in_first)
  have initialModel : Progress partitionOptions part (initial start) := by
    have maximal (b : Allowed) (hb : b ∈ part) : b.2 ≤ a.2 := by
      rw [a_index]
      exact largest b.2 (same ▸ Finset.mem_image_of_mem _ hb) (index_bounds b (cover.1 b hb))
    have h := progress_after_largest partitionOptions tables part (layout_first layout) index_bounds
      (preserves_first layout reverse rows) _ cover a a_mem maximal
    rw [a_index] at h
    exact h
  have nodup : (directCatalog 0).Nodup := by
    rw [direct_first_catalogue]
    exact expected_nodup
  have selectedBit : (partitionKey s).testBit start = true := by
    rw [partitionKey_eq]
    exact (indexCode_bit _ _).mpr ⟨high, in_first⟩
  have boundedStart : start ≤ 289 := by
    by_contra outside
    have smaller : partitionKey s < 2^start := within.trans_lt
      ((show upperBound < 2^290 by decide).trans_le
        (Nat.pow_le_pow_right (by decide) (by omega)))
    exact Bool.false_ne_true ((Nat.testBit_lt_two_pow smaller).symm.trans selectedBit)
  have cuts_good (op : Nat) (state : State) (accepted : cut start op state = true)
      (model : Progress partitionOptions part state) : False := by
    have potential (i : Nat) (member : i ∈ firstGroupIndices s) :
        (state.picked ||| state.available).testBit i = true := by
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (same.symm ▸ member)
      exact model.potential _ _ _ b hb (index_bounds b (cover.1 b hb))
    by_cases zero : op = 0
    · have limit := of_decide_eq_true (show decide ((state.picked ||| state.available) ≤ lowerBound) = true from
        by simpa only [cut, if_pos zero] using accepted)
      have below : partitionKey s ≤ state.picked ||| state.available := by
        rw [partitionKey_eq]
        apply Nat.le_of_testBit
        intro i bit
        exact potential i ((indexCode_bit _ _).mp bit).2
      exact Nat.not_lt_of_ge (below.trans limit) key_above
    by_cases orbit : op ≤ 48
    · have allBelow := show allSetBits (fun i => decide (relabeled (op-1) i < start))
          344 (state.picked ||| state.available) = true from
        by simpa only [cut, if_neg zero, if_pos orbit] using accepted
      obtain ⟨symmetry, action, repr⟩ := checkedAction_correct actions (op-1) (by omega)
      refine prefix_orbit_cut s valid minimal symmetry (action.toRelabelIndex nodup) _
        start potential selectedBit ?_
      intro i yes
      change action.move i < start
      rw [repr]
      exact of_decide_eq_true (allSetBits_correct _ _ _ _ allBelow yes)
    by_cases terminal : op < 112
    · simp only [cut, if_neg zero, if_neg orbit, if_pos terminal, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at accepted
      obtain ⟨finished, shrunk⟩ := accepted
      obtain ⟨symmetry, action, repr⟩ := checkedAction_correct actions (op-64) (by omega)
      have repr' : relabeled (op-64) = action.move := repr.symm
      have moveBound (i : Nat) (hi : i ∈ firstGroupIndices s) : action.move i < 344 := by
        obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hi
        have h := starWord_some s valid 0 t
        have before : ∃ word, (directCatalog 0)[(directCatalog 0).idxOf (pack ((s 0 t).image Fin.val))]? = some word :=
          ⟨_, by simpa only [starOrdinal, starWord, group_zero] using h⟩
        obtain ⟨word, hit⟩ := before
        exact direct_first_bound (action.agrees _ word hit)
      have least := minimal (symmetry.applyCover s) (symmetry.applyCover_correct s valid)
      rw [partitionKey_eq s, partitionKey_eq (symmetry.applyCover s),
        firstGroupIndices_relabel symmetry (action.toRelabelIndex nodup) s valid] at least
      rw [state_picked s part same state model finished, repr',
        moveBits_code action.move 6 _ (first_indices_card s) (first_indices_bounded s valid) moveBound] at shrunk
      exact Nat.not_lt_of_ge least shrunk
    by_cases outside : op = 112
    · have excluded : upperBound < state.picked := of_decide_eq_true
        (show decide (upperBound < state.picked) = true from
          by simpa only [cut, if_neg zero, if_neg orbit, if_neg terminal, if_pos outside] using accepted)
      have selectedBelow : state.picked ≤ partitionKey s := by
        obtain ⟨left, _, _, _, chosen⟩ := model
        rw [← chosen, partitionKey_eq]
        apply Nat.le_of_testBit
        intro i member
        have ⟨small, in_part⟩ := (code_bit _ _).mp member
        obtain ⟨a, ha, ha_index⟩ := Finset.mem_image.mp in_part
        exact (indexCode_bit _ _).mpr ⟨small, same ▸
          (Finset.mem_image.mpr ⟨a, (Finset.mem_sdiff.mp ha).1, ha_index⟩)⟩
      exact Nat.not_lt_of_ge (selectedBelow.trans within) excluded
    simp only [cut, if_neg zero, if_neg orbit, if_neg terminal, if_neg outside, Bool.and_eq_true,
      beq_iff_eq, decide_eq_true_eq] at accepted
    have bound := accepted.1.1
    have finished := accepted.1.2
    have root := accepted.2
    let n := op-128
    have key : normalFormWord n = code (firstGroupIndices s) :=
      root.symm.trans (state_picked s part same state model finished)
    have sameSeed : (seedList n).toFinset = firstGroupIndices s := by
      unfold seedList
      rw [key, List.toFinset_reverse]
      exact positions_to_finset 6 _ (first_indices_bounded s valid) (first_indices_card s)
    have distinct : (seedList n).Nodup := by
      simpa only [seedList, List.nodup_reverse] using
        WeightFifteenConflictRows.positions_nodup 6 (normalFormWord n)
    obtain ⟨picked, model, contains⟩ :=
      indexed_cover_for_tables layout (full_compatibility_sound reverse rows) s valid
    have yes := chooseStars_preserves_cover geometryTables (seedList n) distinct _ _ picked model
      (fun i hi => contains (sameSeed ▸ List.mem_toFinset.mpr hi))
    apply roots n bound
    rw [geometryInitial]
    exact yes
  obtain ⟨transcript, yes⟩ := prefixes start low boundedStart
  obtain ⟨output, replay⟩ := Option.isSome_iff_exists.mp yes
  exact checkPrefix_refutes tables (cut start) (Progress partitionOptions part) cuts_good
    (Progress.pivot partitionOptions tables part (layout_first layout) index_bounds
      (supports_first layout) (preserves_first layout reverse rows))
    6 (initial start) ⟨transcript, 0, 0⟩ output replay initialModel

end WeightFifteenUpperPrefix


namespace WeightFifteenUpperPrefix

open WeightFifteenPrefixVerifier WeightFifteenVerifiedSearch

def transcript288 : List Nat := [0xe01c03803f0000003807007e0003803f0cc0fc1f87007e1081f83f0e00fc0007007e1c0380700e01c03803f,
  0x7e0fc0003f000000000700e00fc010000000003803f0e01c01f8000e00fc3803f0001c01f8000001c01f804,
  0x7e1c01f80007e0000007007e0000003f0000004083f0e00fc0003f0e00fc0000007e0004003f07e00000066,
  0xe00fc0007007e1c01f87007e1c01f87007e1981f83f07e1c01f87007e1c01f8000e01c01f87007e0001f866,
  0xe01c01f8000001981f83f0cc0fc1f83f0000000006607e0fc3803f0001c03803f0e00fc3807007e1c01f800,
  0xe01c01f87007e1c01f8000001c01f8000cc0fc1f80007e0003303f07e0fc0007007e1981f83f0041c01f800,
  0x7e0003803f0000000003f0e00fc3803f0001c01f8000001c01f87007e1981f83f0e00fc0006607e1981f83f,
  0x7e0000003f0e00fc0003f0001c01f80007e0003803f0000fc0007007e0000007007e1c01f8000001c01f870,
  0x7e0000007007e1981f83f0000fc000000001981f83f0000fc000700e00fc0007007e0fc000000001c01f870,
  0xe00fc0000007e1c01f8000e00fc0007007e000000000000fc3803f0001c01f87007e1c01f8000001c01f870,
  0xfc000700e00fc3803f0001c03803f0001c01f8000000083803f0002081f83f07e0003803f00000000000,
  0x7e0fc1f8000e00fc000000e00fc0007007e0001f87007e000000000e01c01f8001080fc1f80000020c1f83f,
  0x1c01f87007e0000003f0e01c01f8000e00fc000700e00fc0007007e2181f83f0e00fc000000e00fc00085,
  0x7e0003803f0001c01f88807e0fc3803f00021c1f83f07e1c03803f0e00fc3803f07e1c01f80007e1c03803f,
  0x7e0fc1f8000e00fc0000007e0003803f0e00fc3803f0000fc000000e00fc3803f0000fc3803f0e00fc00070,
  0x20e00fc000000002281f88907e0fc1f8000001c01f8000000003803f0000000007007e1c01f842,
  0x7e0003583f07e0fc00000000000000000e01c01f8000000003803f0001c01f8700e00fc000000001c01f800,
  0xcc0fc1f8000000fc000700e00fc0000007e0001f80011a0fc1f8000e00fc0003f1180fc1f8000000004583f,
  0x7e0fc1f87007e1981f83f0e00fc000000001c01f8000e00fc0007007e0000006607e1c01f80007e00000000,
  0x1c01f8000000fc0007007e1c01f80007e1c03803f0e01c01f87007e0003807007e000000000e00fc00066,
  0xe00fc0003f000000000700e00fc3803f0001c01f83f0001981f83f07e1c01f86607e0fc3803f0001c01f83f,
  0x1f80011e0fc1f87007e0001f80011c0fc3803f07e00000000]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 1000000000 in
lemma checked288 : (checkPrefix tables (cut 288) 6 (initial 288) ⟨transcript288, 0, 0⟩).isSome = true := by rfl

def transcript289 : List Nat := [0x70]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 1000000000 in
lemma checked289 : (checkPrefix tables (cut 289) 6 (initial 289) ⟨transcript289, 0, 0⟩).isSome = true := by rfl

theorem allPrefixes : PrefixResults := by
  intro start low high
  interval_cases start
  · exact ⟨transcript288, checked288⟩
  · exact ⟨transcript289, checked289⟩

inductive TraceTable where
  | leaf (trace : List Nat)
  | node (pivot : Nat) (low high : TraceTable)

def TraceTable.atRank (rank : Nat) : TraceTable → List Nat
  | .leaf trace => trace
  | .node pivot left right => if rank < pivot then left.atRank rank else right.atRank rank

def rootData : TraceTable := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf [0x2213d584a31ac08c442511098454ba0c944522148dc452b13c944559114886a231549e58,
  0x232ac94462817d064c2d941344a241109ca922128885b231d0a0522913cda4c2316c945b, 0x152663a134e850]) (.leaf [0x25190b66a2f171129725170d44d432a48a9743a111a5543a15344822934aa9a24118d4b1,
  0x229b0a44d43a053264251c0aa5b5698cc4834213cc48343aad525a2511c8862311288e4f,
  0x4e2a9208a6223114c45c422155c4a32150b055291288a66231b08a48])) (.node 3 (.leaf [0x42a1d328e4ca0d52ae56a190e8543a199c4f22939088f3a1c9bc45272110e743925d5e9a,
  0x4b928b0474d958b67037120c64a6d1208c4a23a1d0c8557158bc9d4daa51a8e569509a47,
  0x229189ca6229589e502f1b5425a2398d0e9f502b95285422619c86429210a46221289a87,
  0x239b4bc8c44c90be4a3196cbc8340a1d0858269bc9e9943a0d1a86291290e8e2511cbcb2,
  0x59114be632b1b50c814bab8bc854ea2508894c2cc9448222608a5f22920da4a2520d0c4a,
  0x23180da55599609a684c114be632b1b49455251289447369788c603695564522c1609a68]) (.leaf [0x24148bc64449b4b662222150681432350aa64f134c48d46191128c502b1608441a25609a,
  0x40934a45043211028357a25028340a2cd0ac2391c904a4611c8a45]))) (.node 6 (.node 5 (.leaf [0x239492e47231609e483691cc0505325c908640abd4cb044a113e85239488a4a37aad609a,
  0x47954e88140a1906af30990a4442421d3086542bd0c832911d2e4c27a5c8848]) (.leaf [0x2fa253e6a502c540502320d08b34d2b1348f559789a614c274e46143ab88cae22978d481, 0x9c6245911328b221148c83])) (.node 7 (.leaf [0x46a35028b31150d4a6352650244229414c4723120c44d2911c8c4d27958c48947a35069a, 0x9e311a93c81]) (.leaf [0x561b48c6f4620566482c1109a5b2313cc24642a110e50369608a6a589bcda45221bcd48f, 0x45aa4be4d569a90aa937a30886f])))) (.node 12 (.node 10 (.node 9 (.leaf [0x40a6116442211cb6a042a0c9445221148e472a22c8854351289e462393cd08555260aa64,
  0xe4664d281305b2d13cb85022934b65c279c13645221349e464b9a8b074]) (.leaf [0x2e280b861432053aaf5520c9e4540a0c8c4f43205168340a0d0287422153c722e27530a1,
  0x281549e5b381288c482f958c06d239b0da834292890453117c9a5b36a0ca49f231208e6d,
  0x41a350cab41a15529844980c4864c2110a4a291210a832a96d0a8b419b918472293d52a0,
  0x224c2892a148e055269791e9f46a113ca9])) (.node 11 (.leaf [0x2b148e0a924134b85536a5d5c5235154e05554a0c90472211094b1549289047221d0b05b,
  0x22120a46a221208e8b2511090642391c8ab024110944c4c91c8c4839130bc4f53110944d,
  0x231209e442e1109c8e24110d072251395e45251208c4e23abd124522118a09f241148e61,
  0x4d4d2609045221848a612317c9a47]) (.leaf [0x309615c5237998a45e4c9208845251a8c8442d114e087241108e4d572788e462293cb65c,
  0x2d968904c301888a5b271488e452911ca444321888a4d56118888c439208e442b2bc8e44,
  0x8923918da50261209e84429208e4423928b48522120be6a]))) (.node 14 (.node 13 (.leaf [0x4620d0c48229188a473321d088924114a05226abcc2442516c9e5b559188a442416c8e5c,
  0x4c1295e442913d58482311ccc46241313c4722910985a44918885e311149a4426130bc58,
  0x421109e8b279312e47262749a4f]) (.leaf [0x231108e562913898612f1148c9d2511490462d93c8c4447a249046231108a9d331208e5c,
  0x221289c5227ab08e502313c94452f1888a4622110988345aa4b64728134d86d5791d088d, 0x160c45531178cc8f])) (.node 15 (.leaf [0x43a69068626954a04822a15088741a2c884f31215128543ab5068f41a3cd054391b55281,
  0x24114c85b2a9308a9a23188a06a24171568b5891c8a564320d3a8450960b0742f20d0e89,
  0x43a0d1ab347215329e4d21d349755a65089941a2d2e8339180885e3525d06722f9a93444, 0x1168e2e17c9445]) (.leaf [0x282c4b68630a110aac45a6d0e4542a3d06ab30914c85c4b970b8472f20d306d54a3160af,
  0x391151e4a229188e64472253a5c22168884c2f914b646279388e5054940c847269b542b3,
  0xa6419108c70229bcc2b22f22d06a935179525b342251c64])))))

def rootTrace (n : Nat) : List Nat := rootData.atRank n

def checkRoot (n : Nat) : Bool :=
  check (fun _ => none) (initialFor (seedList n)).1 (initialFor (seedList n)).2 (rootTrace n)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000000 in
lemma replay0 : checkRoot 0 = true := by rfl
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000000 in
lemma replay1 : checkRoot 1 = true := by rfl
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000000 in
lemma replay2 : checkRoot 2 = true := by rfl
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000000 in
lemma replay3 : checkRoot 3 = true := by rfl
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000000 in
lemma replay4 : checkRoot 4 = true := by rfl
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000000 in
lemma replay5 : checkRoot 5 = true := by rfl
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000000 in
lemma replay6 : checkRoot 6 = true := by rfl
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000000 in
lemma replay7 : checkRoot 7 = true := by rfl
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000000 in
lemma replay8 : checkRoot 8 = true := by rfl
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000000 in
lemma replay9 : checkRoot 9 = true := by rfl
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000000 in
lemma replay10 : checkRoot 10 = true := by rfl
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000000 in
lemma replay11 : checkRoot 11 = true := by rfl
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000000 in
lemma replay12 : checkRoot 12 = true := by rfl
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000000 in
lemma replay13 : checkRoot 13 = true := by rfl
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000000 in
lemma replay14 : checkRoot 14 = true := by rfl
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000000 in
lemma replay15 : checkRoot 15 = true := by rfl

set_option maxRecDepth 25000 in
set_option maxHeartbeats 60000000 in
theorem allRootChecks (n : Nat) (hi : n < 16) : checkRoot n = true := by
  interval_cases n
  · exact replay0
  · exact replay1
  · exact replay2
  · exact replay3
  · exact replay4
  · exact replay5
  · exact replay6
  · exact replay7
  · exact replay8
  · exact replay9
  · exact replay10
  · exact replay11
  · exact replay12
  · exact replay13
  · exact replay14
  · exact replay15

theorem allRoots : RootResults := by
  intro n hi
  exact check_without_cuts_implies_no_cover actualAllowedAt _ _ _ (allRootChecks n hi)

end WeightFifteenUpperPrefix

namespace WeightFifteenUpperPrefix

theorem available_layout : ∀ g : Fin 5,
    (List.range 344).map (fun i => WeightFifteenVerifiedSearch.starTable.block 8 60 (344*g.val+i)) =
      WeightFifteenIndexedSearch.directCatalog (WeightFifteenVerifiedSearch.groupAt g) := by
  intro g
  fin_cases g
  · exact WeightFifteenVerifiedSearch.Catalogue0.complete
  · exact WeightFifteenVerifiedSearch.Catalogue1.complete
  · exact WeightFifteenVerifiedSearch.Catalogue2.complete
  · exact WeightFifteenVerifiedSearch.Catalogue3.complete
  · exact WeightFifteenVerifiedSearch.Catalogue4.complete

end WeightFifteenUpperPrefix

theorem OMA.solution : OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H2_R1_H2_R1_H2_R1_H1_R1_H3_R1.H2 := by
  apply WeightFifteenRankAgreement.middle_case_equivalence.mpr
  exact WeightFifteenUpperPrefix.middle_from_checks WeightFifteenUpperPrefix.available_layout
    WeightFifteenVerifiedSearch.actualContainsObligation WeightFifteenVerifiedSearch.everyRowSafe
    WeightFifteenConcreteGenerators.checkedActions WeightFifteenUpperPrefix.allRoots WeightFifteenUpperPrefix.allPrefixes
