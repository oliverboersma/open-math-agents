import OMAReductions.R_Erdos131_erdos_131_variants_elrss_R1
import Mathlib.Combinatorics.Additive.SubsetSum
import Mathlib.Tactic

/-!
# Olson's quadratic subset-sum bound for zero-sum-free sets in cyclic groups

We establish `Erdos131.erdos_131.variants.elrss.R1.H1` following J. E. Olson
(Acta Arithmetica 28, 1975): for any zero-sum-free subset `R` of `ZMod n` (`n > 0`),
`R.card ^ 2 ≤ 9 * ((R.powerset.image fun T => ∑ x ∈ T, x).card - 1)`.
-/

namespace Erdos131ElrssH1Proof

open Finset
open scoped Classical

/- ### 1. Packing translates in levels of the translation boundary -/

private abbrev level {G : Type*} (H : Finset G) (d : G → ℕ) (t : ℕ) :=
  H.filter (fun g => d g ≤ t)

private theorem level_mono {G : Type*} (H : Finset G) (d : G → ℕ) {s t : ℕ} (hst : s ≤ t) :
    level H d s ⊆ level H d t := fun _ h =>
  mem_filter.mpr ⟨(mem_filter.mp h).1, (mem_filter.mp h).2.trans hst⟩

private theorem interpolate {G : Type*} [AddCommGroup G] (d : G → ℕ) (a : ℕ)
    (_hzero : d 0 = 0) (htriangle : ∀ x y, d (x + y) ≤ d x + d y)
    (hneg : ∀ x, d (-x) = d x) (R : Finset G) (hR : ∀ r ∈ R, d r ≤ a)
    {t : ℕ} {g : G} (hg : g ∈ AddSubgroup.closure (R : Set G)) (ht : t < d g) :
    ∃ u ∈ AddSubgroup.closure (R : Set G), t < d u ∧ d u ≤ t + a := by
  classical
  by_contra! hgap
  have hlow : ∀ v, v ∈ AddSubgroup.closure (R : Set G) → d v ≤ t := by
    intro v hv
    induction hv using AddSubgroup.closure_induction_left with
    | zero => omega
    | add_left x hx y hy _ =>
      have hmem := (AddSubgroup.closure (R : Set G)).add_mem (AddSubgroup.subset_closure hx) hy
      have hdx := hR x hx
      have htr := htriangle x y
      specialize hgap (x + y) hmem
      omega
    | neg_add_cancel x hx y hy _ =>
      have hmem := (AddSubgroup.closure (R : Set G)).add_mem
        ((AddSubgroup.closure (R : Set G)).neg_mem (AddSubgroup.subset_closure hx)) hy
      have hdx := hR x hx
      have htr := htriangle (-x) y
      rw [hneg] at htr
      specialize hgap (-x + y) hmem
      omega
  exact (hlow g hg).not_gt ht

private theorem pack_at_steps {G : Type*} [AddCommGroup G] [DecidableEq G]
    (H C : Finset G) (d : G → ℕ) (a t : ℕ)
    (hCH : C ⊆ H) (hclosed : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H)
    (hC : ∀ g ∈ C, d g ≤ a) (htriangle : ∀ x y, d (x + y) ≤ d x + d y)
    (hneg : ∀ x, d (-x) = d x)
    (hgap : ∀ v ≤ t, ∃ u ∈ H, v < d u ∧ d u ≤ v + a) :
    ∀ j : ℕ, (3 * j + 1) * a ≤ t →
      (j + 1) * C.card ≤ (level H d ((3 * j + 1) * a)).card := by
  classical
  intro j
  induction j with
  | zero =>
    intro _
    simp only [Nat.mul_zero, Nat.zero_add, one_mul]
    exact card_le_card (fun g hg => mem_filter.mpr ⟨hCH hg, hC g hg⟩)
  | succ j ih =>
    intro ht
    have hc1 : (3 * (j + 1) + 1) * a = (3 * j + 1) * a + 3 * a := by ring
    rw [hc1] at ht ⊢
    specialize ih (by omega)
    obtain ⟨u, hu, hlo, hhi⟩ := hgap ((3 * j + 1) * a + a) (by omega)
    let U := C.image (fun z => u + z)
    have hsub : U ⊆ level H d ((3 * j + 1) * a + 3 * a) := by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
      have := hC z hz
      have := htriangle u z
      exact mem_filter.mpr ⟨hclosed u hu z (hCH hz), by omega⟩
    have hd : Disjoint (level H d ((3 * j + 1) * a)) U := by
      apply disjoint_left.mpr
      intro x hx hxU
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hxU
      have hb := (mem_filter.mp hx).2
      have hc := hC z hz
      have hrev := htriangle (u + z) (-z)
      rw [add_neg_cancel_right, hneg] at hrev
      omega
    have hlevels := level_mono H d (Nat.le_add_right ((3 * j + 1) * a) (3 * a))
    have htotal := card_le_card (union_subset hlevels hsub)
    rw [card_union_of_disjoint hd] at htotal
    have hcard : U.card = C.card := card_image_of_injective _ (add_right_injective _)
    rw [hcard] at htotal
    nlinarith

private theorem packing_contradiction {G : Type*} [AddCommGroup G] [DecidableEq G]
    (H C : Finset G) (d : G → ℕ) (a k : ℕ)
    (hk : 0 < k) (hsize : 2 * k ≤ H.card) (ha : 2 * a ≤ k) (hbig : 8 * a < C.card)
    (hCH : C ⊆ H) (hclosed : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H)
    (hC : ∀ g ∈ C, d g ≤ a) (hz : 0 ∈ H) (hd0 : d 0 = 0)
    (htriangle : ∀ x y, d (x + y) ≤ d x + d y) (hneg : ∀ x, d (-x) = d x)
    (hinter : ∀ t : ℕ, (∃ g ∈ H, t < d g) → ∃ u ∈ H, t < d u ∧ d u ≤ t + a)
    (hsum : ∑ j ∈ range k, (level H d j).card = k ^ 2) : False := by
  classical
  have all_low (t : ℕ) (h : ¬∃ g ∈ H, t < d g) : level H d t = H := by
    apply filter_true_of_mem
    intro g hg
    exact le_of_not_gt (fun hgt => h ⟨g, hg, hgt⟩)
  by_cases haz : a = 0
  · subst a
    have h0 : ¬∃ g ∈ H, 0 < d g := by
      intro hi
      obtain ⟨u, _, hu, hb⟩ := hinter 0 hi
      omega
    have hforall (t : ℕ) : level H d t = H :=
      all_low t (fun ⟨v, hv, hvt⟩ => h0 ⟨v, hv, by omega⟩)
    simp only [hforall, sum_const, card_range, nsmul_eq_mul] at hsum
    nlinarith [Nat.mul_le_mul_left k hsize]
  have haPos : 0 < a := by omega
  have hone (t : ℕ) : 1 ≤ (level H d t).card :=
    card_pos.mpr ⟨0, mem_filter.mpr ⟨hz, by omega⟩⟩
  have hwide (t : ℕ) (hat : a ≤ t) : 4 * a ≤ (level H d t).card := by
    have h : C ⊆ level H d t := fun g hg => mem_filter.mpr ⟨hCH hg, (hC g hg).trans hat⟩
    have := card_le_card h
    omega
  have hlevel (t : ℕ) (hat : a ≤ t) (htk : t < k) : 2 * t + 1 ≤ (level H d t).card := by
    by_cases hhigh : ∃ g ∈ H, t < d g
    · let j := (t - a) / (3 * a)
      have hdiv := Nat.div_add_mod (t - a) (3 * a)
      have hrem := Nat.mod_lt (t - a) (show 0 < 3 * a by omega)
      have hjn : (3 * j + 1) * a ≤ t ∧ t < (3 * j + 1) * a + 3 * a := by
        dsimp [j]
        ring_nf at *
        omega
      have hgap : ∀ v ≤ t, ∃ u ∈ H, v < d u ∧ d u ≤ v + a := by
        intro v hv
        obtain ⟨g, hg, hgt⟩ := hhigh
        exact hinter v ⟨g, hg, by omega⟩
      have hpack := pack_at_steps H C d a t hCH hclosed hC htriangle hneg hgap j hjn.1
      have hm := card_le_card (level_mono H d hjn.1)
      have hw := Nat.mul_le_mul_left (j + 1) hbig.le
      nlinarith [Nat.zero_le (j * a)]
    · rw [all_low t hhigh]
      omega
  have hfirst : (2 * a) ^ 2 < ∑ j ∈ range (2 * a), (level H d j).card := by
    rw [two_mul, sum_range_add]
    have h1 := sum_le_sum (s := range a) (g := fun i => (level H d i).card)
      (fun i _ => hone i)
    have h2 := sum_le_sum (s := range a) (g := fun i => (level H d (a + i)).card)
      (fun i _ => hwide (a + i) (by omega))
    simp only [sum_const, card_range, nsmul_eq_mul, mul_one] at h1 h2
    nlinarith
  have hstrong (n : ℕ) (hn : 2 * a ≤ n) (hnk : n ≤ k) :
      n ^ 2 < ∑ j ∈ range n, (level H d j).card := by
    induction n, hn using Nat.le_induction with
    | base => exact hfirst
    | succ n hn ih =>
      rw [sum_range_succ]
      have := ih (by omega)
      have := hlevel n (by omega) (by omega)
      nlinarith
  exact (hstrong k ha le_rfl).ne hsum.symm

/- ### 2. Translation boundaries in a finite cyclic group -/

private abbrev shift {G : Type*} [AddCommGroup G] [DecidableEq G] (x : G) (B : Finset G) :=
  B.image (fun y => x + y)

private abbrev delta {G : Type*} [AddCommGroup G] [DecidableEq G] (B : Finset G) (x : G) :=
  (shift x B \ B).card

private theorem shift_card {G : Type*} [AddCommGroup G] [DecidableEq G] (x : G) (B : Finset G) :
    (shift x B).card = B.card :=
  card_image_of_injective _ (add_right_injective _)

private theorem shift_mem {G : Type*} [AddCommGroup G] [DecidableEq G] {x z : G} {B : Finset G} :
    z ∈ shift x B ↔ z - x ∈ B := by
  constructor
  · rintro hz
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hz
    simpa using hb
  · exact fun h => mem_image.mpr ⟨z - x, h, by abel⟩

private theorem shift_shift {G : Type*} [AddCommGroup G] [DecidableEq G]
    (x y : G) (B : Finset G) :
    shift x (shift y B) = shift (x + y) B := by
  simp only [shift, image_image, Function.comp_def, add_assoc]

private theorem shift_sdiff {G : Type*} [AddCommGroup G] [DecidableEq G]
    (x : G) (A B : Finset G) :
    shift x (A \ B) = shift x A \ shift x B :=
  image_sdiff _ _ (add_right_injective _)

private theorem delta_zero {G : Type*} [AddCommGroup G] [DecidableEq G] (B : Finset G) :
    delta B 0 = 0 := by
  simp [delta, shift]

private theorem delta_neg {G : Type*} [AddCommGroup G] [DecidableEq G] (B : Finset G) (x : G) :
    delta B (-x) = delta B x := by
  rw [delta, ← shift_card x, shift_sdiff, shift_shift]
  simp only [add_neg_cancel, shift, zero_add, image_id']
  exact card_sdiff_comm (shift_card x B).symm

private theorem delta_add {G : Type*} [AddCommGroup G] [DecidableEq G]
    (B : Finset G) (x y : G) :
    delta B (x + y) ≤ delta B x + delta B y := by
  have hsub : shift (x + y) B \ B ⊆ (shift x B \ B) ∪ shift x (shift y B \ B) := by
    rw [shift_sdiff, shift_shift]
    intro g hg
    obtain ⟨hm, hn⟩ := mem_sdiff.mp hg
    by_cases h : g ∈ shift x B
    · exact mem_union_left _ (mem_sdiff.mpr ⟨h, hn⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hm, h⟩)
  exact (card_le_card hsub).trans <| (card_union_le _ _).trans_eq (by rw [shift_card])

private theorem delta_union {G : Type*} [AddCommGroup G] [DecidableEq G] (B : Finset G) (x : G) :
    (B ∪ shift x B).card = B.card + delta B x := by
  rw [union_comm, ← card_sdiff_add_card, add_comm]

private theorem shift_group {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    (H : AddSubgroup G) {x : G} (hx : x ∈ H) :
    shift x (H : Set G).toFinset = (H : Set G).toFinset := by
  ext g
  simp only [shift_mem, Set.mem_toFinset, SetLike.mem_coe]
  exact ⟨fun h => by simpa using H.add_mem h hx, fun h => H.sub_mem h hx⟩

private theorem delta_compl {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    (H : AddSubgroup G) (B : Finset G) (hB : (B : Set G) ⊆ H)
    {x : G} (hx : x ∈ H) :
    delta ((H : Set G).toFinset \ B) x = delta B x := by
  let K := (H : Set G).toFinset
  have hs : B ⊆ K := fun _ h => Set.mem_toFinset.mpr (hB h)
  have hsets : (K \ shift x B) \ (K \ B) = B \ shift x B := by
    ext g
    simp only [mem_sdiff]
    constructor
    · rintro ⟨⟨hk, hn⟩, h⟩
      exact ⟨by by_contra hm; exact h ⟨hk, hm⟩, hn⟩
    · rintro ⟨hb, hn⟩
      exact ⟨⟨hs hb, hn⟩, fun h => h.2 hb⟩
  rw [delta, shift_sdiff, shift_group H hx]
  exact (congrArg card hsets).trans (card_sdiff_comm (shift_card x B).symm)

private theorem level_sum {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    (H : AddSubgroup G) (B : Finset G) (hB : (B : Set G) ⊆ H) :
    ∑ j ∈ range B.card, (((H : Set G).toFinset).filter (fun g => delta B g ≤ j)).card =
      B.card ^ 2 := by
  classical
  let K := (H : Set G).toFinset
  have hsize (g : G) :
      B.card - delta B g = (B.filter (fun y => y - g ∈ B)).card := by
    have hdiff := card_sdiff_add_card_inter (shift g B) B
    rw [shift_card] at hdiff
    have he : B ∩ shift g B = B.filter (fun y => y - g ∈ B) := by
      ext y; simp only [mem_inter, mem_filter, shift_mem]
    change B.card - (shift g B \ B).card = _
    rw [← he, inter_comm]
    omega
  have hswap (y : G) (hy : y ∈ B) : (K.filter (fun g => y - g ∈ B)).card = B.card := by
    have he : K.filter (fun g => y - g ∈ B) = B.image (fun z => y - z) := by
      ext g
      constructor
      · intro hg
        exact mem_image.mpr ⟨y - g, (mem_filter.mp hg).2, by abel⟩
      · intro hg
        obtain ⟨z, hz, rfl⟩ := mem_image.mp hg
        exact mem_filter.mpr
          ⟨Set.mem_toFinset.mpr (H.sub_mem (hB hy) (hB hz)), by simpa using hz⟩
    rw [he, card_image_of_injective _ sub_right_injective]
  have htime (g : G) : ((range B.card).filter (fun j => delta B g ≤ j)).card =
      B.card - delta B g := by
    have he : (range B.card).filter (fun j => delta B g ≤ j) = Ico (delta B g) B.card := by
      ext j; simp [and_comm]
    rw [he, Nat.card_Ico]
  calc
    _ = ∑ g ∈ K, (B.card - delta B g) := by
      simp only [Finset.card_filter]
      rw [sum_comm]
      apply sum_congr rfl
      intro g _
      simpa only [Finset.card_filter] using htime g
    _ = ∑ y ∈ B, B.card := by
      simp_rw [hsize, Finset.card_filter]
      rw [sum_comm]
      apply sum_congr rfl
      intro y hy
      simpa only [Finset.card_filter] using hswap y hy
    _ = _ := by simp [pow_two]

private theorem antisym_union {m : ℕ} [NeZero m] (R : Finset (ZMod m))
    (hn : (0 : ZMod m) ∉ R) (ha : ∀ x ∈ R, ∀ y ∈ R, x + y = 0 → x = y) :
    2 * R.card ≤ (insert 0 (R ∪ R.image Neg.neg)).card := by
  classical
  have hfix {x : ZMod m} (hx : x ∈ R ∩ R.image Neg.neg) : 2 * x.val = m := by
    obtain ⟨hxR, hxn⟩ := mem_inter.mp hx
    obtain ⟨y, hy, hxy⟩ := mem_image.mp hxn
    have h := ha x hxR y hy (by rw [← hxy]; abel)
    have hf : -x = x := h ▸ hxy
    exact (x.neg_eq_self_iff.mp hf).resolve_left (fun he => hn (he ▸ hxR))
  have hone : (R ∩ R.image Neg.neg).card ≤ 1 := by
    apply card_le_one.mpr
    intro x hx y hy
    have hxv := hfix hx
    have hyv := hfix hy
    exact ZMod.val_injective m (by omega)
  have hzero : (0 : ZMod m) ∉ R ∪ R.image Neg.neg := by simpa using hn
  have hc := card_union_add_card_inter R (R.image Neg.neg)
  rw [card_image_of_injective _ neg_injective] at hc
  rw [card_insert_of_notMem hzero]
  omega

private theorem cyclic_boundary (m : ℕ) (hm : 0 < m) (B R : Finset (ZMod m))
    (hr : R.Nonempty) (hz : 0 ∈ B)
    (hb : (B : Set (ZMod m)) ⊆ AddSubgroup.closure (R : Set (ZMod m)))
    (havoid : ∀ r ∈ R, -r ∉ B) (hanti : ∀ x ∈ R, ∀ y ∈ R, x + y = 0 → x = y) :
    ∃ x ∈ R, 4 * B.card + min (2 * (B.card + 1)) R.card ≤
      4 * (B ∪ B.image (fun y => x + y)).card := by
  classical
  have : NeZero m := ⟨hm.ne'⟩
  let H := AddSubgroup.closure (R : Set (ZMod m))
  let K := (H : Set (ZMod m)).toFinset
  let a := R.sup (delta B)
  have hBK : B ⊆ K := fun _ h => Set.mem_toFinset.mpr (hb h)
  have hR (r : ZMod m) (h : r ∈ R) : r ∈ H := AddSubgroup.subset_closure h
  have hdmax (r : ZMod m) (h : r ∈ R) : delta B r ≤ a := le_sup h
  obtain ⟨r, hr', heq⟩ := exists_mem_eq_sup R hr (delta B)
  refine ⟨r, hr', ?_⟩
  change 4 * B.card + min (2 * (B.card + 1)) R.card ≤ 4 * (B ∪ shift r B).card
  rw [delta_union, ← heq]
  change 4 * B.card + min (2 * (B.card + 1)) R.card ≤ 4 * (B.card + a)
  by_contra! hbad
  have hnegK : R.image Neg.neg ⊆ K \ B := by
    intro z hz'
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hz'
    exact mem_sdiff.mpr ⟨Set.mem_toFinset.mpr (H.neg_mem (hR y hy)), havoid y hy⟩
  have hkc := card_le_card hnegK
  rw [card_image_of_injective _ neg_injective, card_sdiff_of_subset hBK] at hkc
  let X := if 2 * B.card ≤ K.card then B else K \ B
  have hX : X ⊆ K := by dsimp [X]; split <;> first | exact hBK | exact sdiff_subset
  have hXB : ∀ x ∈ H, delta X x = delta B x := by
    intro x hx
    dsimp [X]; split
    · rfl
    · exact delta_compl H B hb hx
  have hbpos := card_pos.mpr (show B.Nonempty from ⟨0, hz⟩)
  have hrpos := card_pos.mpr hr
  have hXsize : 0 < X.card ∧ 2 * a ≤ X.card ∧ 2 * X.card ≤ K.card := by
    dsimp [X]; split
    · omega
    · rw [card_sdiff_of_subset hBK]; omega
  let C := insert 0 (R ∪ R.image Neg.neg)
  have hnR : (0 : ZMod m) ∉ R := fun h => havoid 0 h (by simpa using hz)
  have hCsize := antisym_union R hnR hanti
  have hC : ∀ z ∈ C, delta X z ≤ a ∧ z ∈ K := by
    intro z h
    rcases mem_insert.mp h with rfl | h
    · exact ⟨by simp [delta_zero], Set.mem_toFinset.mpr H.zero_mem⟩
    · rcases mem_union.mp h with hrz | hneg
      · exact ⟨(hXB z (hR z hrz)).le.trans (hdmax z hrz), Set.mem_toFinset.mpr (hR z hrz)⟩
      · obtain ⟨y, hy, rfl⟩ := mem_image.mp hneg
        rw [delta_neg, hXB y (hR y hy)]
        exact ⟨hdmax y hy, Set.mem_toFinset.mpr (H.neg_mem (hR y hy))⟩
  have hD (y : ZMod m) (hy : y ∈ R) : delta X y ≤ a := (hXB y (hR y hy)).le.trans (hdmax y hy)
  apply packing_contradiction K C (delta X) a X.card
    hXsize.1 hXsize.2.2 hXsize.2.1
    (by change 8 * a < (insert 0 (R ∪ R.image Neg.neg)).card; omega)
    (fun z h => (hC z h).2)
    (fun x hx y hy =>
      Set.mem_toFinset.mpr (H.add_mem (Set.mem_toFinset.mp hx) (Set.mem_toFinset.mp hy)))
    (fun z h => (hC z h).1) (Set.mem_toFinset.mpr H.zero_mem) (delta_zero X)
    (delta_add X) (delta_neg X)
  · intro t ⟨g, hg, hgt⟩
    obtain ⟨u, hu, hlo, hhi⟩ := interpolate (delta X) a (delta_zero X)
      (delta_add X) (delta_neg X) R hD (Set.mem_toFinset.mp hg) hgt
    exact ⟨u, Set.mem_toFinset.mpr hu, hlo, hhi⟩
  · exact level_sum H X (fun z h => Set.mem_toFinset.mp (hX h))

/- ### 3. Pure algebraic analysis of Olson's scalar recurrence -/

private def b (s : ℕ) : ℕ → ℕ
  | 0 => 1
  | i + 1 => b s i + (min (2 * (b s i + 1)) (s - i) + 3) / 4

private def g : ℕ → ℕ
  | 0 => 1
  | i + 1 => g i + (2 * g i + 5) / 4

private def F : ℕ → ℕ
  | 0 => 0
  | m + 1 => F m + (m + 4) / 4

private theorem b_mono (s : ℕ) : Monotone (b s) := by
  apply monotone_nat_of_le_succ
  intro i
  rw [b]
  omega

private theorem two_mul_g_succ (i : ℕ) : 3 * g i + 1 ≤ 2 * g (i + 1) := by
  rw [g]
  omega

private theorem ten_mul_le_g {i : ℕ} (hi : 9 ≤ i) : 10 * i ≤ g i := by
  induction i, hi using Nat.le_induction with
  | base => simp [g]
  | succ i hi ih =>
    have h := two_mul_g_succ i
    omega

private theorem g_ge_three_half (i : ℕ) : 3 * (i + 1) ≤ 2 * g i + 2 := by
  by_cases hi : i < 9
  · interval_cases i <;> simp [g]
  · have h := ten_mul_le_g (by omega : 9 ≤ i)
    omega

private theorem g_ge_four (i : ℕ) : 4 * i ≤ g i + 6 := by
  by_cases hi : i < 9
  · interval_cases i <;> simp [g]
  · have h := ten_mul_le_g (by omega : 9 ≤ i)
    omega

private theorem val_u0_nonneg (i : ℕ) :
    0 ≤ (2 * (g i : ℤ) + 2) ^ 2 + (36 - 16 * ((i : ℤ) + 1)) * (2 * (g i : ℤ) + 2) +
      72 * (g (i + 1) : ℤ) - 8 * ((i : ℤ) + 1) ^ 2 - 185 := by
  by_cases hi : i < 9
  · interval_cases i <;> simp [g]
  · have h10 : 10 * (i : ℤ) ≤ (g i : ℤ) := by exact_mod_cast ten_mul_le_g (by omega)
    have hsucc : 3 * (g i : ℤ) + 1 ≤ 2 * (g (i + 1) : ℤ) := by
      exact_mod_cast two_mul_g_succ i
    have hi9 : (9 : ℤ) ≤ i := by omega
    nlinarith

private theorem F_bounds (m : ℕ) : m * (m + 4) ≤ 8 * F m ∧ 8 * F m ≤ m * (m + 4) + 4 := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm : m < 4
    · interval_cases m <;> simp [F]
    · let m' := m - 4
      have hrec := ih m' (by omega)
      have heq : m = m' + 4 := by omega
      have hstep : F (m' + 4) = F m' + m' + 4 := by
        simp only [F]
        omega
      rw [heq, hstep]
      constructor <;> nlinarith

private theorem b_eq_g {s i : ℕ} (h : ∀ t < i, 2 * (g t + 1) < s - t) : b s i = g i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hi := ih (fun t ht => h t (by omega))
    have hlt := h i (by omega)
    rw [b, g, hi, min_eq_left (by omega)]
    omega

private theorem b_add_F_eq {s j p : ℕ} (hj : s - j ≤ 2 * (b s j + 1))
    (hjp : j ≤ p) (hps : p ≤ s) :
    b s p + F (s - p) = b s j + F (s - j) := by
  induction p, hjp using Nat.le_induction with
  | base => rfl
  | succ p hp ih =>
    specialize ih (by omega)
    have hm := b_mono s hp
    rw [b, min_eq_right (by omega)]
    have hsub : s - p = (s - (p + 1)) + 1 := by omega
    rw [hsub, F] at ih
    omega

private theorem numerical (s p : ℕ) (hp : p < s) :
    s ^ 2 ≤ 9 * b s p + 2 * (s - p - 1) ^ 2 := by
  classical
  have hex : ∃ j, s - j ≤ 2 * (g j + 1) := ⟨s, by simp⟩
  let j := Nat.find hex
  have hj_le : j ≤ s := Nat.find_min' hex (by simp)
  have hj_spec : s - j ≤ 2 * (g j + 1) := Nat.find_spec hex
  have hj_min : ∀ t < j, 2 * (g t + 1) < s - t :=
    fun t ht => Nat.lt_of_not_ge (Nat.find_min hex ht)
  have hbj : b s j = g j := b_eq_g hj_min
  rcases eq_or_ne j 0 with hj0 | hj_pos
  · have hs4 : s ≤ 4 := by
      have h0 : s - 0 ≤ 2 * (g 0 + 1) := hj0 ▸ hj_spec
      simp only [g] at h0
      omega
    clear hbj hj_min hj_spec hj_le hj0 j hex
    interval_cases s <;> interval_cases p <;> simp [b]
  · obtain ⟨i, hi_eq⟩ := Nat.exists_eq_succ_of_ne_zero hj_pos
    have hu_ge : 2 * g i + 2 ≤ s - j := by
      have h := hj_min i (by omega)
      omega
    by_cases hjp : j ≤ p
    · have hF := b_add_F_eq (hbj.symm ▸ hj_spec) hjp hp.le
      have hgj : g j = g (i + 1) := congrArg g hi_eq
      rw [hbj, hgj] at hF
      have hFu := (F_bounds (s - j)).1
      have hFq := (F_bounds (s - p)).2
      let U : ℤ := ↑(s - j)
      let Q : ℤ := ↑(s - p)
      let R : ℤ := ↑(s - p - 1)
      let J : ℤ := (i : ℤ) + 1
      let U0 : ℤ := 2 * (g i : ℤ) + 2
      have hQR : Q = R + 1 := by
        dsimp [Q, R]
        omega
      have hsUJ : (s : ℤ) = U + J := by
        dsimp [U, J]
        omega
      have hF_int : (b s p : ℤ) + (F (s - p) : ℤ) =
          (g (i + 1) : ℤ) + (F (s - j) : ℤ) := by
        exact_mod_cast hF
      have hFu_int : U * (U + 4) ≤ 8 * (F (s - j) : ℤ) := by
        dsimp [U]
        exact_mod_cast hFu
      have hFq_int : 8 * (F (s - p) : ℤ) ≤ Q * (Q + 4) + 4 := by
        dsimp [Q]
        exact_mod_cast hFq
      have hb_lb : 8 * (g (i + 1) : ℤ) + U * (U + 4) - Q * (Q + 4) - 4 ≤
          8 * (b s p : ℤ) := by linarith
      have hq_quad : -149 ≤ 7 * Q ^ 2 - 68 * Q + 16 := by
        have h7 : -1044 ≤ 7 * (7 * Q ^ 2 - 68 * Q + 16) := by
          nlinarith [sq_nonneg (7 * Q - 34)]
        omega
      have hU_ge : U0 ≤ U := by
        dsimp [U0, U]
        exact_mod_cast hu_ge
      have hU0_slope : 8 * J ≤ U0 + 18 := by
        have hg4 : 4 * (i : ℤ) ≤ (g i : ℤ) + 6 := by exact_mod_cast g_ge_four i
        dsimp [J, U0]
        linarith
      have hU_mono : U0 ^ 2 + (36 - 16 * J) * U0 ≤ U ^ 2 + (36 - 16 * J) * U := by
        have hprod : 0 ≤ (U - U0) * (U + U0 + 36 - 16 * J) :=
          mul_nonneg (by linarith) (by linarith)
        linarith
      have hval0 := val_u0_nonneg i
      have hmain8 : 8 * (s : ℤ) ^ 2 ≤ 72 * (b s p : ℤ) + 16 * R ^ 2 := by
        rw [hsUJ, hQR] at *
        dsimp [J, U0] at hU_mono
        linarith
      have hmain : (s : ℤ) ^ 2 ≤ 9 * (b s p : ℤ) + 2 * R ^ 2 := by omega
      dsimp [R] at hmain
      exact_mod_cast hmain
    · have hb_pos : 1 ≤ b s p := by
        have hm := b_mono s (Nat.zero_le p)
        simpa [b] using hm
      have hu3 : 3 * j ≤ s - j := by
        have h3 := g_ge_three_half i
        omega
      have hr_ge : s - j ≤ s - p - 1 := by omega
      have hs_eq : (s - j) + j = s := Nat.sub_add_cancel hj_le
      nlinarith [Nat.mul_le_mul hr_ge hr_ge]

/- ### 4. Greedy subgroup decomposition for zero-sum-free sets -/

private theorem add_card_subsetSum {G : Type*} [AddCommGroup G] [DecidableEq G]
    {P Q : Finset G} (hd : Disjoint P Q)
    (hz : ∀ T ⊆ P ∪ Q, T.Nonempty → ∑ t ∈ T, t ≠ 0) :
    P.subsetSum.card + Q.subsetSum.card ≤ (P ∪ Q).subsetSum.card + 1 := by
  classical
  let a := ∑ x ∈ P, x
  let U := P.subsetSum.erase a
  let V := Q.subsetSum.image (fun y => a + y)
  have hU : U ⊆ (P ∪ Q).subsetSum :=
    (erase_subset _ _).trans (subsetSum_mono subset_union_left)
  have hV : V ⊆ (P ∪ Q).subsetSum := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    obtain ⟨T, hT, rfl⟩ := mem_subsetSum_iff.mp hy
    exact mem_subsetSum_iff.mpr ⟨P ∪ T, union_subset_union_right hT,
      sum_union (hd.mono_right hT)⟩
  have hdis : Disjoint U V := by
    apply Finset.disjoint_left.mpr
    intro z hzU hzV
    obtain ⟨hne, hzP⟩ := mem_erase.mp hzU
    obtain ⟨W, hW, hsumW⟩ := mem_subsetSum_iff.mp hzP
    obtain ⟨y, hy, hsum⟩ := mem_image.mp hzV
    obtain ⟨T, hT, rfl⟩ := mem_subsetSum_iff.mp hy
    have hrem : (P \ W).Nonempty := by
      by_contra! hempty
      have heq := subset_antisymm hW (sdiff_eq_empty_iff_subset.mp hempty)
      exact hne (hsumW.symm.trans (by rw [heq]))
    apply hz ((P \ W) ∪ T) (union_subset_union sdiff_subset hT) (hrem.mono subset_union_left)
    rw [sum_union (hd.mono sdiff_subset hT)]
    change (∑ x ∈ P, x) + ∑ x ∈ T, x = z at hsum
    have heq := sum_sdiff hW (f := id)
    change (∑ x ∈ P \ W, x) + ∑ x ∈ W, x = ∑ x ∈ P, x at heq
    rw [← heq, add_right_comm, hsumW] at hsum
    exact add_right_cancel (hsum.trans (zero_add z).symm)
  have hUV := card_le_card (union_subset hU hV)
  have ha : a ∈ P.subsetSum := mem_subsetSum_iff.mpr ⟨P, Subset.rfl, rfl⟩
  have hc := card_erase_add_one ha
  have hvc : V.card = Q.subsetSum.card := card_image_of_injective _ (add_right_injective a)
  rw [card_union_of_disjoint hdis, hvc] at hUV
  change U.card + 1 = P.subsetSum.card at hc
  omega

private theorem double_card_subsetSum {G : Type*} [AddCommGroup G] [DecidableEq G]
    (R : Finset G) (x : G) (hx : x ∉ AddSubgroup.closure (R : Set G)) :
    2 * R.subsetSum.card ≤ (insert x R).subsetSum.card := by
  classical
  let H := AddSubgroup.closure (R : Set G)
  have hsub {y} (hy : y ∈ R.subsetSum) : y ∈ H := by
    obtain ⟨T, hT, rfl⟩ := mem_subsetSum_iff.mp hy
    exact H.sum_mem fun t ht => AddSubgroup.subset_closure (hT ht)
  have hnot : x ∉ R := fun h => hx (AddSubgroup.subset_closure h)
  let B := R.subsetSum.image (fun y => x + y)
  have hB : B ⊆ (insert x R).subsetSum := by
    rintro y hy
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hy
    obtain ⟨T, hT, rfl⟩ := mem_subsetSum_iff.mp hz
    exact mem_subsetSum_iff.mpr ⟨insert x T, insert_subset_insert _ hT,
      sum_insert (fun h => hnot (hT h))⟩
  have hd : Disjoint R.subsetSum B := by
    apply Finset.disjoint_left.mpr
    intro y hy hyB
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hyB
    simpa using hx (show x ∈ H by simpa using H.sub_mem (hsub hy) (hsub hz))
  have hbound := card_le_card (union_subset (subsetSum_mono (subset_insert x R)) hB)
  have hc : B.card = R.subsetSum.card := card_image_of_injective _ (add_right_injective x)
  rwa [card_union_of_disjoint hd, hc, ← two_mul] at hbound

private theorem subsetSum_insert_eq {G : Type*} [AddCommGroup G] [DecidableEq G]
    {P : Finset G} {x : G} (hx : x ∉ P) :
    (insert x P).subsetSum = P.subsetSum ∪ P.subsetSum.image (fun y => x + y) := by
  classical
  ext a
  constructor
  · intro ha
    obtain ⟨T, hT, rfl⟩ := mem_subsetSum_iff.mp ha
    by_cases hm : x ∈ T
    · apply mem_union_right
      refine mem_image.mpr ⟨∑ y ∈ T.erase x, y, mem_subsetSum_iff.mpr ⟨_, ?_, rfl⟩, ?_⟩
      · intro y hy
        exact (mem_insert.mp (hT (mem_of_mem_erase hy))).resolve_left (ne_of_mem_erase hy)
      · simpa [add_comm] using sum_erase_add T (fun a => a) hm
    · apply mem_union_left
      exact mem_subsetSum_iff.mpr ⟨T, fun y hy =>
        (mem_insert.mp (hT hy)).resolve_left (fun h => hm (h ▸ hy)), rfl⟩
  · intro ha
    rcases mem_union.mp ha with hp | hi
    · exact subsetSum_mono (subset_insert _ _) hp
    · obtain ⟨z, hz, rfl⟩ := mem_image.mp hi
      obtain ⟨T, hT, rfl⟩ := mem_subsetSum_iff.mp hz
      exact mem_subsetSum_iff.mpr ⟨insert x T, insert_subset_insert _ hT,
        sum_insert (fun h => hx (hT h))⟩

private abbrev growth131 (s p : ℕ) : ℕ := b s p

private theorem olson_subsetSum {m : ℕ} (hm : 0 < m) (S : Finset (ZMod m))
    (hzero : ∀ T ⊆ S, T.Nonempty → ∑ t ∈ T, t ≠ 0) :
    S.card ^ 2 ≤ 9 * (S.subsetSum.card - 1) := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases he : S = ∅
    · simp [he]
    have search : ∀ R : Finset (ZMod m), ∀ P : Finset (ZMod m),
        Disjoint P R → P ∪ R = S → R.Nonempty →
        (P : Set (ZMod m)) ⊆ AddSubgroup.closure (R : Set (ZMod m)) →
        growth131 S.card P.card ≤ P.subsetSum.card →
        S.card ^ 2 ≤ 9 * (S.subsetSum.card - 1) := by
      intro R
      induction R using Finset.strongInductionOn with
      | _ R shrinks =>
        intro P hd hpart hr hgen hbudget
        have hsumgen : (P.subsetSum : Set (ZMod m)) ⊆ AddSubgroup.closure (R : Set (ZMod m)) := by
          intro a ha
          obtain ⟨T, hT, rfl⟩ := mem_subsetSum_iff.mp ha
          exact AddSubgroup.sum_mem _ (fun t ht => hgen (hT ht))
        have hav : ∀ r ∈ R, -r ∉ P.subsetSum := by
          intro r hr' hrmem
          obtain ⟨T, hT, hsum⟩ := mem_subsetSum_iff.mp hrmem
          have hrT : r ∉ T := fun h => (Finset.disjoint_left.mp hd) (hT h) hr'
          apply hzero (insert r T) (hpart ▸ insert_subset
            (mem_union_right P hr') (hT.trans subset_union_left)) (insert_nonempty _ _)
          rw [sum_insert hrT, hsum, add_neg_cancel]
        have hanti : ∀ x ∈ R, ∀ y ∈ R, x + y = 0 → x = y := by
          intro x hx y hy hsum
          by_contra hxy
          apply hzero {x, y} (hpart ▸ insert_subset (mem_union_right P hx)
            (singleton_subset_iff.mpr (mem_union_right P hy))) (insert_nonempty _ _)
          simpa [hxy] using hsum
        obtain ⟨x, hx, hinc⟩ :=
          cyclic_boundary m hm P.subsetSum R hr (by simp) hsumgen hav hanti
        let V := R.erase x
        have hV : V ⊂ R := erase_ssubset hx
        have hxP : x ∉ P := fun h => Finset.disjoint_left.mp hd h hx
        have hins : insert x V = R := insert_erase hx
        have hsum : P.card + R.card = S.card := by rw [← hpart, card_union_of_disjoint hd]
        have hVcard : V.card + 1 = R.card := card_erase_add_one hx
        by_cases hdrop : x ∈ AddSubgroup.closure (V : Set (ZMod m))
        · have hgenV : AddSubgroup.closure (R : Set (ZMod m)) ≤
                AddSubgroup.closure (V : Set (ZMod m)) := by
            apply (AddSubgroup.closure_le _).mpr
            intro a ha
            by_cases h : a = x
            · simpa [h] using hdrop
            · exact AddSubgroup.subset_closure (mem_erase.mpr ⟨h, ha⟩ : a ∈ V)
          have hnewpart : insert x P ∪ V = S := by
            rw [← hpart, ← hins, insert_union, union_insert]
          have hdnew : Disjoint (insert x P) V := by
            rw [disjoint_insert_left]
            exact ⟨notMem_erase x R, hd.mono_right (erase_subset _ _)⟩
          have hrg : (↑(insert x P) : Set (ZMod m)) ⊆
              AddSubgroup.closure (V : Set (ZMod m)) := by
            intro a ha
            rcases mem_insert.mp ha with rfl | ha
            · exact hdrop
            · exact hgenV (hgen ha)
          have hnonempty : V.Nonempty := by
            by_contra! hv
            rw [hv] at hdrop
            have hx0 : x = 0 := by simpa using hdrop
            exact hav x hx (by simp [hx0])
          apply shrinks V hV (insert x P) hdnew hnewpart hnonempty hrg
          rw [card_insert_of_notMem hxP, growth131, b]
          change growth131 S.card P.card + (min (2 * (growth131 S.card P.card + 1))
            (S.card - P.card) + 3) / 4 ≤ (insert x P).subsetSum.card
          rw [← subsetSum_insert_eq hxP] at hinc
          have hmin : min (2 * (growth131 S.card P.card + 1)) (S.card - P.card) ≤
              min (2 * (P.subsetSum.card + 1)) R.card := by
            apply min_le_min <;> omega
          omega
        · have hvS : V ⊂ S := hV.trans_le (hpart ▸ subset_union_right)
          have hsmall := ih V hvS (fun T hT => hzero T (hT.trans hvS.le))
          have hdbl := double_card_subsetSum V x hdrop
          have hadd := add_card_subsetSum hd (hpart ▸ hzero)
          rw [hins] at hdbl
          rw [hpart] at hadd
          have hpos := card_pos.mpr V.subsetSum_nonempty
          have hposS := card_pos.mpr S.subsetSum_nonempty
          have hnum' : S.card ^ 2 ≤ 9 * growth131 S.card P.card + 2 * (S.card - P.card - 1) ^ 2 :=
            numerical S.card P.card (by have := card_pos.mpr hr; omega)
          have hrnum : S.card - P.card - 1 = V.card := by omega
          rw [hrnum] at hnum'
          omega
    exact search S ∅ (by simp) (by simp) (Finset.nonempty_iff_ne_empty.mpr he)
      (by simp) (by simp [growth131, b, subsetSum])

theorem prove_h1 : OMA.R_Erdos131_erdos_131_variants_elrss_R1.H1 := by
  intro n hn R hzero
  have himg : (R.powerset.image fun T => ∑ x ∈ T, x) = R.subsetSum := by
    ext z
    simp [Finset.subsetSum]
  rw [himg]
  exact olson_subsetSum hn R hzero

end Erdos131ElrssH1Proof

theorem OMA.solution : OMA.R_Erdos131_erdos_131_variants_elrss_R1.H1 :=
  Erdos131ElrssH1Proof.prove_h1
