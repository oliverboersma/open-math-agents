import OMAReductions.R_Erdos733_erdos_733_variants_limit_exists_R1
import Mathlib

/-! Adding a point outside every old line preserves the sequence up to new 2-point lines. -/

open Erdos733 EuclideanGeometry Finset MeasureTheory

namespace Erdos733GenericPoint

private noncomputable def through (u v : ℝ²) (hne : u ≠ v) : Line :=
  ⟨affineSpan ℝ {u,v}, ⟨u, left_mem_affineSpan_pair _ _ _⟩, by
    rw [IsLine, direction_affineSpan, vectorSpan_pair]
    exact finrank_span_singleton (vsub_ne_zero.mpr hne)⟩

private theorem through_left (u v : ℝ²) (hne : u ≠ v) : u ∈ (through u v hne).val :=
  left_mem_affineSpan_pair _ _ _

private theorem through_right (u v : ℝ²) (hne : u ≠ v) : v ∈ (through u v hne).val :=
  right_mem_affineSpan_pair _ _ _

private theorem eq_through {ℓ : Line} {u v : ℝ²} (hu : u ∈ ℓ.val) (hv : v ∈ ℓ.val) (hne : u ≠ v) :
    ℓ = through u v hne := by
  have hc : Collinear ℝ (ℓ.val : Set ℝ²) := by
    rw [collinear_iff_finrank_le_one, ← direction_affineSpan, AffineSubspace.affineSpan_coe]
    exact ℓ.property.2.le
  apply Subtype.ext
  simp only [through]
  rw [hc.affineSpan_eq_of_ne hu hv hne, AffineSubspace.affineSpan_coe]

open scoped Classical in
private noncomputable def lines (P : Finset ℝ²) : Finset Line :=
  P.offDiag.attach.image (fun uv => through uv.val.1 uv.val.2 (mem_offDiag.mp uv.property).2.2)

private theorem mem_lines {P : Finset ℝ²} {ℓ : Line} : ℓ ∈ lines P ↔ 2 ≤ lineCount P ℓ := by
  classical
  constructor
  · intro h
    obtain ⟨uv, -, rfl⟩ := mem_image.mp h
    obtain ⟨hu,hv,hn⟩ := mem_offDiag.mp uv.property
    unfold lineCount
    exact Nat.succ_le_of_lt (Finset.one_lt_card.mpr
      ⟨uv.val.1, mem_filter.mpr ⟨hu, through_left _ _ _⟩,
        uv.val.2, mem_filter.mpr ⟨hv, through_right _ _ _⟩, hn⟩)
  · intro h
    unfold lineCount at h
    obtain ⟨u,hu,v,hv,hn⟩ := Finset.one_lt_card.mp (show 1 < _ from h)
    obtain ⟨huP,huL⟩ := mem_filter.mp hu
    obtain ⟨hvP,hvL⟩ := mem_filter.mp hv
    exact mem_image.mpr ⟨⟨(u,v), mem_offDiag.mpr ⟨huP,hvP,hn⟩⟩,
      mem_attach _ _, (eq_through huL hvL hn).symm⟩

private theorem card_lines (P : Finset ℝ²) : (lines P).card ≤ P.card*P.card := by
  classical
  calc
    (lines P).card ≤ P.offDiag.card := by unfold lines; exact card_image_le.trans_eq card_attach
    _ ≤ P.card*P.card := by
      rw [← card_product]
      exact card_le_card fun _ h => mem_product.mpr ⟨(mem_offDiag.mp h).1, (mem_offDiag.mp h).2.1⟩

private theorem exists_outside (P : Finset ℝ²) :
    ∃ x : ℝ², x ∉ P ∧ ∀ ℓ ∈ lines P, x ∉ ℓ.val := by
  classical
  let V : Set ℝ² := (P : Set ℝ²) ∪ ⋃ ℓ : lines P, (ℓ.val.val : Set ℝ²)
  have hzero : volume V = 0 := by
    apply measure_union_null (P.finite_toSet.measure_zero volume)
    apply measure_iUnion_null
    intro ℓ
    apply Measure.addHaar_affineSubspace
    intro he
    have hl := ℓ.val.property.2
    rw [IsLine, he, AffineSubspace.direction_top, finrank_top, finrank_euclideanSpace_fin] at hl
    omega
  have hb : V ≠ Set.univ := fun he => by
    rw [he] at hzero
    exact (isOpen_univ.measure_pos volume Set.univ_nonempty).ne' hzero
  obtain ⟨x,hx⟩ := Set.nonempty_compl.mpr hb
  refine ⟨x, fun hp => hx (Or.inl hp), fun ℓ hℓ hxℓ => hx (Or.inr ?_)⟩
  exact Set.mem_iUnion.mpr ⟨⟨ℓ,hℓ⟩, hxℓ⟩

open scoped Classical in
private theorem count_insert {P : Finset ℝ²} {x : ℝ²} (hx : x ∉ P) (ℓ : Line) :
    lineCount (insert x P) ℓ = if x ∈ ℓ.val then lineCount P ℓ + 1 else lineCount P ℓ := by
  classical
  unfold lineCount
  rw [filter_insert]
  split
  · exact card_insert_of_notMem (fun h => hx (mem_filter.mp h).1)
  · rfl

private theorem add_point (P : Finset ℝ²) :
    ∃ (x : ℝ²), x ∉ P ∧
      lineSizeMultiset (insert x P) (lines (insert x P)) =
        lineSizeMultiset P (lines P) + Multiset.replicate P.card 2 := by
  classical
  obtain ⟨x, hxP, hxL⟩ := exists_outside P
  let f (u : P) : Line := through x u.val (fun e => hxP (e ▸ u.property))
  let M := P.attach.image f
  have fx (u : P) : x ∈ (f u).val := through_left _ _ _
  have fu (u : P) : u.val ∈ (f u).val := through_right _ _ _
  have honly (u : P) (v : ℝ²) (hv : v ∈ P) (hline : v ∈ (f u).val) : v = u.val := by
    by_contra hn
    have he := eq_through hline (fu u) hn
    have hmem : through v u.val hn ∈ lines P :=
      mem_image.mpr ⟨⟨(v,u.val),mem_offDiag.mpr ⟨hv,u.property,hn⟩⟩,mem_attach _ _,rfl⟩
    exact hxL _ hmem (he ▸ fx u)
  have hnew_count (ℓ : Line) (hℓ : ℓ ∈ M) : lineCount (insert x P) ℓ = 2 := by
    obtain ⟨u, -, rfl⟩ := mem_image.mp hℓ
    have hfil : P.filter (fun v => v ∈ (f u).val) = {u.val} := by
      ext v
      simp only [mem_filter, mem_singleton]
      exact ⟨fun h => honly u v h.1 h.2, fun e => e.symm ▸ ⟨u.property,fu u⟩⟩
    rw [count_insert hxP, if_pos (fx u)]
    unfold lineCount
    rw [hfil, card_singleton]
  have hMcard : M.card = P.card := by
    unfold M
    rw [Finset.card_image_of_injOn, card_attach]
    intro u _ v _ he
    exact Subtype.ext (honly v u.val u.property (he ▸ fu u))
  have hdis : Disjoint (lines P) M := by
    apply Finset.disjoint_left.mpr
    rintro ℓ hℓ hm
    obtain ⟨u, -, rfl⟩ := mem_image.mp hm
    exact hxL _ hℓ (fx u)
  have hlines : lines (insert x P) = (lines P).disjUnion M hdis := by
    ext ℓ
    rw [mem_disjUnion, mem_lines]
    constructor
    · intro h
      by_cases hxℓ : x ∈ ℓ.val
      · right
        rw [count_insert hxP, if_pos hxℓ] at h
        have hh : 0 < lineCount P ℓ := by omega
        unfold lineCount at hh
        obtain ⟨u, hu⟩ := card_pos.mp hh
        obtain ⟨huP, huℓ⟩ := mem_filter.mp hu
        let v : P := ⟨u,huP⟩
        refine mem_image.mpr ⟨v,mem_attach _ _,?_⟩
        exact (eq_through hxℓ huℓ (fun e => hxP (e ▸ huP))).symm
      · left
        rwa [count_insert hxP, if_neg hxℓ, ← mem_lines] at h
    · rintro (h | h)
      · rw [count_insert hxP, if_neg (hxL ℓ h)]
        exact mem_lines.mp h
      · exact (hnew_count ℓ h).ge
  have hmapold : (lines P).val.map (lineCount (insert x P)) = (lines P).val.map (lineCount P) := by
    apply Multiset.map_congr rfl
    intro ℓ hℓ
    rw [count_insert hxP, if_neg (hxL ℓ hℓ)]
  have hmapnew : M.val.map (lineCount (insert x P)) = Multiset.replicate P.card 2 := by
    calc
      _ = M.val.map (fun _ => 2) := Multiset.map_congr rfl hnew_count
      _ = _ := by simp [hMcard]
  refine ⟨x, hxP, ?_⟩
  unfold lineSizeMultiset
  rw [hlines]
  change ((lines P).val + M.val).map _ = _
  rw [Multiset.map_add, hmapold, hmapnew]

private theorem finite_sequences (n : ℕ) : (allLinesSequences n).Finite := by
  classical
  let W := ⋃ m : Fin (n*n+1), Set.range (fun F : Fin m.val → Fin (n+1) =>
    List.ofFn fun i => (F i).val)
  have hW : W.Finite := by
    unfold W
    exact Set.finite_iUnion fun _ => Set.finite_range _
  apply hW.subset
  intro X hX
  obtain ⟨P,hP,L,hL,rfl⟩ := hX
  have hLe : L = lines P := Finset.ext fun ℓ => (hL ℓ).trans mem_lines.symm
  subst L
  let Y := lineSizeSequence P (lines P)
  have hlen : Y.length ≤ n*n := by
    simpa [Y, lineSizeSequence, lineSizeMultiset, hP] using card_lines P
  let m : Fin (n*n+1) := ⟨Y.length, by omega⟩
  have hvals (a : ℕ) (ha : a ∈ Y) : a ≤ n := by
    simp only [Y, lineSizeSequence, lineSizeMultiset, Multiset.mem_sort, Multiset.mem_map] at ha
    obtain ⟨ℓ,hℓ,rfl⟩ := ha
    rw [← hP]
    exact Finset.card_le_card (filter_subset _ _)
  let F (i : Fin m.val) : Fin (n+1) :=
    ⟨Y[i.val], Nat.lt_succ_of_le (hvals _ (List.getElem_mem _))⟩
  change Y ∈ W
  exact Set.mem_iUnion.mpr ⟨m, ⟨F, List.ofFn_getElem⟩⟩

private theorem monotone_step (n : ℕ) :
    (allLinesSequences n).ncard ≤ (allLinesSequences (n+1)).ncard := by
  let f (X : List ℕ) :=
    ((X : Multiset ℕ) + Multiset.replicate n 2).sort (· ≤ ·)
  have hrep {X : List ℕ} (hX : X ∈ allLinesSequences n) :
      ∃ P : Finset ℝ², P.card = n ∧ X = lineSizeSequence P (lines P) := by
    obtain ⟨P,hP,L,hL,rfl⟩ := hX
    have hLe : L = lines P := Finset.ext fun ℓ => (hL ℓ).trans mem_lines.symm
    exact ⟨P,hP,congrArg _ hLe⟩
  apply Set.ncard_le_ncard_of_injOn f _ _ (finite_sequences (n+1))
  · intro X hX
    obtain ⟨P,hP,rfl⟩ := hrep hX
    obtain ⟨x,hx,hms⟩ := add_point P
    refine ⟨insert x P, by rw [card_insert_of_notMem hx, hP], lines (insert x P),
      fun _ => mem_lines, ?_⟩
    simp [f, lineSizeSequence, hms, hP]
  · intro X hX Y hY he
    obtain ⟨P,_,rfl⟩ := hrep hX
    obtain ⟨Q,_,rfl⟩ := hrep hY
    have h := congrArg (fun s : List ℕ => (s : Multiset ℕ)) he
    simp only [f, lineSizeSequence, Multiset.sort_eq, add_right_cancel_iff] at h
    simp only [lineSizeSequence, h]

theorem main : Monotone (fun n => (allLinesSequences n).ncard) ∧
    ∀ n, 0 < (allLinesSequences n).ncard := by
  refine ⟨monotone_nat_of_le_succ monotone_step, ?_⟩
  have h0 : 0 < (allLinesSequences 0).ncard := by
    apply (Set.ncard_pos (finite_sequences 0)).mpr
    exact ⟨lineSizeSequence ∅ (lines ∅), ∅, rfl, lines ∅, fun _ => mem_lines, rfl⟩
  exact fun n => h0.trans_le ((monotone_nat_of_le_succ monotone_step) (Nat.zero_le n))

end Erdos733GenericPoint

theorem OMA.solution : OMA.R_Erdos733_erdos_733_variants_limit_exists_R1.H1 :=
  Erdos733GenericPoint.main