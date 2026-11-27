import OMAReductions.R_Erdos19_erdos_19_variants_large_n_R1
import Mathlib.Data.Fintype.EquivFin

-- Reduction Erdos19.erdos_19.variants.large_n.R1.H1.R1 of step Erdos19.erdos_19.variants.large_n.R1.H1
-- Credit: @mucoucah
-- Proved here: pass to an inclusion-minimal (vertex-critical) uncolourable subfamily L of the
-- design K; rank-two families are coloured by endpoint sums; the uniform r-by-r case (affine
-- planes, n = r^2) is coloured by parallel classes; pair-budget counting gives every rank-two
-- block of L four rank-two neighbours. What remains: no such critical L exists for large n,
-- split by the maximum block rank in L (Kahn / KKKMO style).
-- H1: for each fixed bound R, eventually no critical L with all block ranks at most R.
-- H2: for some R, eventually no critical L having a block of rank above R.

namespace OMA.R_Erdos19_erdos_19_variants_large_n_R1_H1_R1

open Filter Finset
open scoped BigOperators

theorem block_eq_of_pair {n : ℕ} {K : Finset (Finset (Fin n))}
    (hpair : ∀ i j : Fin n, i ≠ j → ∃! A, A ∈ K ∧ i ∈ A ∧ j ∈ A)
    {A B : Finset (Fin n)} (hA : A ∈ K) (hB : B ∈ K)
    {i j : Fin n} (hij : i ≠ j) (hiA : i ∈ A) (hjA : j ∈ A)
    (hiB : i ∈ B) (hjB : j ∈ B) : A = B :=
  (hpair i j hij).unique ⟨hA, hiA, hjA⟩ ⟨hB, hiB, hjB⟩

theorem links_disjoint {n : ℕ} {K L : Finset (Finset (Fin n))}
    (hpair : ∀ i j : Fin n, i ≠ j → ∃! A, A ∈ K ∧ i ∈ A ∧ j ∈ A)
    (hLK : L ⊆ K) (i : Fin n) :
    ((L.filter fun A => i ∈ A) : Set (Finset (Fin n))).PairwiseDisjoint
      (fun A => A.erase i) := by
  intro A hA B hB hAB
  obtain ⟨hA, hiA⟩ := mem_filter.mp (mem_coe.mp hA)
  obtain ⟨hB, hiB⟩ := mem_filter.mp (mem_coe.mp hB)
  refine disjoint_left.mpr fun j hjA hjB => hAB ?_
  exact block_eq_of_pair hpair (hLK hA) (hLK hB) (mem_erase.mp hjA).1.symm
    hiA (mem_of_mem_erase hjA) hiB (mem_of_mem_erase hjB)

theorem link_weight_eq {n : ℕ} {K : Finset (Finset (Fin n))}
    (hpair : ∀ i j : Fin n, i ≠ j → ∃! A, A ∈ K ∧ i ∈ A ∧ j ∈ A)
    (i : Fin n) :
    ∑ A ∈ K.filter (fun A => i ∈ A), (A.card - 1) = n - 1 := by
  classical
  let H := K.filter fun A => i ∈ A
  have hcover : H.biUnion (fun A => A.erase i) = univ.erase i := by
    ext j
    constructor
    · intro hj
      obtain ⟨A, _, hjA⟩ := mem_biUnion.mp hj
      exact mem_erase.mpr ⟨(mem_erase.mp hjA).1, mem_univ j⟩
    · intro hj
      obtain ⟨A, ⟨hA, hiA, hjA⟩, _⟩ := hpair i j (mem_erase.mp hj).1.symm
      exact mem_biUnion.mpr ⟨A, mem_filter.mpr ⟨hA, hiA⟩,
        mem_erase.mpr ⟨(mem_erase.mp hj).1, hjA⟩⟩
  calc
    ∑ A ∈ H, (A.card - 1) = ∑ A ∈ H, (A.erase i).card := by
      exact sum_congr rfl fun A hA => (card_erase_of_mem (mem_filter.mp hA).2).symm
    _ = (H.biUnion fun A => A.erase i).card :=
      (card_biUnion (links_disjoint hpair Subset.rfl i)).symm
    _ = n - 1 := by rw [hcover, card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]

theorem meeting_weight_eq {n : ℕ} {K : Finset (Finset (Fin n))}
    (hpair : ∀ i j : Fin n, i ≠ j → ∃! B, B ∈ K ∧ i ∈ B ∧ j ∈ B)
    {A : Finset (Fin n)} (hA : A ∈ K) :
    ∑ B ∈ (K.erase A).filter (fun B => (A ∩ B).Nonempty), (B.card - 1) =
      A.card * (n - A.card) := by
  classical
  let H (i : Fin n) := (K.erase A).filter fun B => i ∈ B
  have hdisj : (A : Set (Fin n)).PairwiseDisjoint H := by
    intro i hi j hj hij
    refine disjoint_left.mpr fun B hiB hjB => ?_
    obtain ⟨⟨hBA, hB⟩, hiB⟩ := (mem_erase.mp (mem_filter.mp hiB).1), (mem_filter.mp hiB).2
    exact hBA (block_eq_of_pair hpair hB hA hij hiB (mem_filter.mp hjB).2 hi hj)
  have hunion : A.biUnion H = (K.erase A).filter (fun B => (A ∩ B).Nonempty) := by
    ext B
    constructor
    · intro hB
      obtain ⟨i, hi, hB⟩ := mem_biUnion.mp hB
      exact mem_filter.mpr ⟨(mem_filter.mp hB).1, ⟨i, mem_inter.mpr ⟨hi, (mem_filter.mp hB).2⟩⟩⟩
    · intro hB
      obtain ⟨hB, i, hi⟩ := mem_filter.mp hB
      exact mem_biUnion.mpr ⟨i, (mem_inter.mp hi).1,
        mem_filter.mpr ⟨hB, (mem_inter.mp hi).2⟩⟩
  have hweight (i : Fin n) (hi : i ∈ A) : ∑ B ∈ H i, (B.card - 1) = n - A.card := by
    have hfilter : H i = (K.filter fun B => i ∈ B).erase A := by
      ext B
      simp only [H, mem_filter, mem_erase]
      tauto
    have hsum := sum_erase_add (s := K.filter fun B => i ∈ B) (f := fun B => B.card - 1)
      (mem_filter.mpr ⟨hA, hi⟩)
    have hpositive := card_pos.mpr ⟨i, hi⟩
    have hbound : A.card ≤ n := by simpa using card_le_univ A
    have htotal := link_weight_eq hpair i
    rw [hfilter]
    omega
  rw [← hunion, sum_biUnion hdisj]
  calc
    ∑ i ∈ A, ∑ B ∈ H i, (B.card - 1) = ∑ _i ∈ A, (n - A.card) := sum_congr rfl hweight
    _ = _ := by simp

theorem pair_of_mem_of_card_two {n : ℕ} {A : Finset (Fin n)} {i : Fin n}
    (hi : i ∈ A) (hA : A.card = 2) : ∃ j ≠ i, A = {i, j} := by
  have herase : (A.erase i).card = 1 := by rw [card_erase_of_mem hi, hA]
  obtain ⟨j, hj⟩ := card_eq_one.mp herase
  have hj' : j ∈ A.erase i := by simp [hj]
  exact ⟨j, (mem_erase.mp hj').1, by rw [← insert_erase hi, hj]⟩

theorem color_two_blocks {n : ℕ} [NeZero n] {K : Finset (Finset (Fin n))}
    (hsize : ∀ A ∈ K, A.card = 2) : ∃ c : Finset (Fin n) → Fin n, (∀ X ∈ K, ∀ Y ∈ K, X ≠ Y → (X ∩ Y).Nonempty → c X ≠ c Y) := by
  refine ⟨fun A => ∑ i ∈ A, i, ?_⟩
  intro A hA B hB hAB hmeet heq
  obtain ⟨i, hi⟩ := hmeet
  obtain ⟨j, hj, rfl⟩ := pair_of_mem_of_card_two (mem_inter.mp hi).1 (hsize A hA)
  obtain ⟨k, hk, rfl⟩ := pair_of_mem_of_card_two (mem_inter.mp hi).2 (hsize B hB)
  have heq' : i + j = i + k := by simpa only [sum_pair hj.symm, sum_pair hk.symm] using heq
  exact hAB (congrArg (fun v => ({i, v} : Finset (Fin n))) (add_left_cancel heq'))

theorem extend_coloring_of_unused {n : ℕ} {K : Finset (Finset (Fin n))} {A : Finset (Fin n)}
    {c : Finset (Fin n) → Fin n} (hc : (∀ X ∈ (K.erase A), ∀ Y ∈ (K.erase A), X ≠ Y → (X ∩ Y).Nonempty → c X ≠ c Y))
    {v : Fin n} (hv : v ∉ ((K.erase A).filter (fun B => (A ∩ B).Nonempty)).image c) :
    ∃ d : Finset (Fin n) → Fin n, (∀ X ∈ K, ∀ Y ∈ K, X ≠ Y → (X ∩ Y).Nonempty → d X ≠ d Y) := by
  classical
  have hnew (B : Finset (Fin n)) (hB : B ∈ K.erase A) (hAB : (A ∩ B).Nonempty) : v ≠ c B := by
    intro heq
    exact hv (heq ▸ mem_image_of_mem c (mem_filter.mpr ⟨hB, hAB⟩))
  refine ⟨Function.update c A v, ?_⟩
  intro B hB D hD hBD hmeet
  by_cases hBA : B = A
  · subst B
    simpa only [Function.update_self, Function.update_of_ne hBD.symm] using
      hnew D (mem_erase.mpr ⟨hBD.symm, hD⟩) hmeet
  by_cases hDA : D = A
  · subst D
    simpa only [Function.update_self, Function.update_of_ne hBA] using
      (hnew B (mem_erase.mpr ⟨hBA, hB⟩) (by rwa [inter_comm])).symm
  simpa only [Function.update_of_ne hBA, Function.update_of_ne hDA] using
    hc B (mem_erase.mpr ⟨hBA, hB⟩) D (mem_erase.mpr ⟨hDA, hD⟩) hBD hmeet

theorem extend_coloring {n : ℕ} {K : Finset (Finset (Fin n))} {A : Finset (Fin n)}
    {c : Finset (Fin n) → Fin n} (hc : (∀ X ∈ (K.erase A), ∀ Y ∈ (K.erase A), X ≠ Y → (X ∩ Y).Nonempty → c X ≠ c Y))
    (hfree : ((K.erase A).filter (fun B => (A ∩ B).Nonempty)).card < n) :
    ∃ d : Finset (Fin n) → Fin n, (∀ X ∈ K, ∀ Y ∈ K, X ≠ Y → (X ∩ Y).Nonempty → d X ≠ d Y) := by
  classical
  let used := ((K.erase A).filter (fun B => (A ∩ B).Nonempty)).image c
  have hused : used.card < n := card_image_le.trans_lt hfree
  have hsome : ((univ : Finset (Fin n)) \ used).Nonempty := by
    apply card_pos.mp
    rwa [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin, Nat.sub_pos_iff_lt]
  obtain ⟨v, hv⟩ := hsome
  exact extend_coloring_of_unused hc (mem_sdiff.mp hv).2

theorem all_colors_blocked {n : ℕ} {K : Finset (Finset (Fin n))} {A : Finset (Fin n)}
    (hbad : ¬ ∃ d : Finset (Fin n) → Fin n, (∀ X ∈ K, ∀ Y ∈ K, X ≠ Y → (X ∩ Y).Nonempty → d X ≠ d Y)) {c : Finset (Fin n) → Fin n} (hc : (∀ X ∈ (K.erase A), ∀ Y ∈ (K.erase A), X ≠ Y → (X ∩ Y).Nonempty → c X ≠ c Y)) :
    ((K.erase A).filter (fun B => (A ∩ B).Nonempty)).image c = univ := by
  apply eq_univ_of_forall
  intro v
  by_contra hv
  exact hbad (extend_coloring_of_unused hc hv)

theorem exists_critical_subfamily {n : ℕ} [NeZero n] {K : Finset (Finset (Fin n))}
    (hbad : ¬ ∃ c : Finset (Fin n) → Fin n, (∀ X ∈ K, ∀ Y ∈ K, X ≠ Y → (X ∩ Y).Nonempty → c X ≠ c Y)) :
    ∃ L ⊆ K, L.Nonempty ∧ (¬ ∃ c : Finset (Fin n) → Fin n, (∀ X ∈ L, ∀ Y ∈ L, X ≠ Y → (X ∩ Y).Nonempty → c X ≠ c Y)) ∧ ∀ A ∈ L,
      (∃ c : Finset (Fin n) → Fin n, (∀ X ∈ (L.erase A), ∀ Y ∈ (L.erase A), X ≠ Y → (X ∩ Y).Nonempty → c X ≠ c Y)) ∧
        n ≤ ((L.erase A).filter fun B => (A ∩ B).Nonempty).card := by
  classical
  induction K using Finset.strongInductionOn with
  | _ K ih =>
    by_cases hall : ∀ A ∈ K, ∃ c : Finset (Fin n) → Fin n, (∀ X ∈ (K.erase A), ∀ Y ∈ (K.erase A), X ≠ Y → (X ∩ Y).Nonempty → c X ≠ c Y)
    · have hK : K.Nonempty := by
        by_contra hempty
        exact hbad ⟨fun _ => 0, fun A hA => (hempty ⟨A, hA⟩).elim⟩
      refine ⟨K, Subset.rfl, hK, hbad, fun A hA => ⟨hall A hA, ?_⟩⟩
      obtain ⟨c, hc⟩ := hall A hA
      exact le_of_not_gt fun hfree => hbad (extend_coloring hc hfree)
    · rw [not_forall] at hall
      obtain ⟨A, hA⟩ := hall
      rw [Classical.not_imp] at hA
      obtain ⟨hA, hA_bad⟩ := hA
      obtain ⟨L, hL, hrest⟩ := ih (K.erase A) (erase_ssubset hA) hA_bad
      exact ⟨L, hL.trans (erase_subset A K), hrest⟩

theorem meeting_card_mul_le_sum {n r : ℕ} {L : Finset (Finset (Fin n))} {A : Finset (Fin n)}
    (hrank : ∀ B ∈ L, r ≤ B.card) :
    ((L.erase A).filter fun B => (A ∩ B).Nonempty).card * (r - 1) ≤
      ∑ B ∈ (L.erase A).filter (fun B => (A ∩ B).Nonempty), (B.card - 1) := by
  let S := (L.erase A).filter fun B => (A ∩ B).Nonempty
  calc
    S.card * (r - 1) = ∑ _B ∈ S, (r - 1) := by simp
    _ ≤ ∑ B ∈ S, (B.card - 1) := sum_le_sum fun B hB =>
      Nat.sub_le_sub_right (hrank B (mem_of_mem_erase (mem_filter.mp hB).1)) 1

theorem meeting_card_mul_le {n r : ℕ} {K L : Finset (Finset (Fin n))}
    (hpair : ∀ i j : Fin n, i ≠ j → ∃! B, B ∈ K ∧ i ∈ B ∧ j ∈ B)
    (hLK : L ⊆ K) {A : Finset (Fin n)} (hA : A ∈ K)
    (hrank : ∀ B ∈ L, r ≤ B.card) :
    ((L.erase A).filter fun B => (A ∩ B).Nonempty).card * (r - 1) ≤
      A.card * (n - A.card) := by
  let S := (L.erase A).filter fun B => (A ∩ B).Nonempty
  calc
    S.card * (r - 1) ≤ ∑ B ∈ S, (B.card - 1) := meeting_card_mul_le_sum hrank
    _ ≤ ∑ B ∈ (K.erase A).filter (fun B => (A ∩ B).Nonempty), (B.card - 1) := by
      apply sum_le_sum_of_subset
      intro B hB
      obtain ⟨hBA, hi⟩ := mem_filter.mp hB
      obtain ⟨hne, hBL⟩ := mem_erase.mp hBA
      exact mem_filter.mpr ⟨mem_erase.mpr ⟨hne, hLK hBL⟩, hi⟩
    _ = _ := meeting_weight_eq hpair hA

theorem uniform_square_saturation {n r : ℕ} {K L : Finset (Finset (Fin n))}
    (hpair : ∀ i j : Fin n, i ≠ j → ∃! B, B ∈ K ∧ i ∈ B ∧ j ∈ B)
    (hLK : L ⊆ K) (hL : L.Nonempty) (hn : n = r * r)
    (hsize : ∀ B ∈ K, 2 ≤ B.card) (hrank : ∀ B ∈ L, B.card = r)
    (hdegree : ∀ A ∈ L, n ≤ ((L.erase A).filter fun B => (A ∩ B).Nonempty).card) :
    L = K := by
  classical
  have hclosed {A B : Finset (Fin n)} (hA : A ∈ L) (hB : B ∈ K) (hAB : (A ∩ B).Nonempty) : B ∈ L := by
    by_contra he
    let S := (L.erase A).filter fun D => (A ∩ D).Nonempty
    let T := (K.erase A).filter fun D => (A ∩ D).Nonempty
    have hBS : B ∉ S := fun h => he (mem_of_mem_erase (mem_filter.mp h).1)
    have hBT : B ∈ T := mem_filter.mpr ⟨mem_erase.mpr ⟨fun h => he (h.symm ▸ hA), hB⟩, hAB⟩
    have hsub : insert B S ⊆ T := by
      apply insert_subset hBT
      intro D hD
      obtain ⟨hD, hi⟩ := mem_filter.mp hD
      obtain ⟨hne, hDL⟩ := mem_erase.mp hD
      exact mem_filter.mpr ⟨mem_erase.mpr ⟨hne, hLK hDL⟩, hi⟩
    have htotal : ∑ D ∈ T, (D.card - 1) = n * (r - 1) := by
      rw [meeting_weight_eq hpair (hLK hA), hrank A hA]
      rw [show n - r = r * (r - 1) by rw [hn, Nat.mul_sub, Nat.mul_one], ← Nat.mul_assoc, ← hn]
    have hlower : n * (r - 1) ≤ ∑ D ∈ S, (D.card - 1) :=
      (Nat.mul_le_mul_right _ (hdegree A hA)).trans
        (meeting_card_mul_le_sum (A := A) fun D hD => (hrank D hD).ge)
    have hupper := sum_le_sum_of_subset (f := fun D : Finset (Fin n) => D.card - 1) hsub
    rw [sum_insert hBS, htotal] at hupper
    have hBsize := hsize B hB
    omega
  apply Subset.antisymm hLK
  intro B hB
  obtain ⟨A, hA⟩ := hL
  obtain ⟨i, hi⟩ := card_pos.mp ((by decide : 0 < 2).trans_le (hsize A (hLK hA)))
  obtain ⟨j, hj⟩ := card_pos.mp ((by decide : 0 < 2).trans_le (hsize B hB))
  by_cases hij : i = j
  · exact hclosed hA hB ⟨i, mem_inter.mpr ⟨hi, hij.symm ▸ hj⟩⟩
  · obtain ⟨D, ⟨hD, hiD, hjD⟩, _⟩ := hpair i j hij
    have hDL := hclosed hA hD ⟨i, mem_inter.mpr ⟨hi, hiD⟩⟩
    exact hclosed hDL hB ⟨j, mem_inter.mpr ⟨hjD, hj⟩⟩

theorem critical_pair_neighbor_card {n : ℕ} {K L : Finset (Finset (Fin n))}
    (hpair : ∀ i j : Fin n, i ≠ j → ∃! B, B ∈ K ∧ i ∈ B ∧ j ∈ B)
    (hLK : L ⊆ K) (hsize : ∀ B ∈ K, 2 ≤ B.card)
    {A : Finset (Fin n)} (hA : A ∈ L) (hAcard : A.card = 2)
    (hdegree : n ≤ ((L.erase A).filter fun B => (A ∩ B).Nonempty).card) :
    4 ≤ ((L.erase A).filter fun B => (A ∩ B).Nonempty ∧ B.card = 2).card := by
  classical
  let S := (K.erase A).filter fun B => (A ∩ B).Nonempty
  let T := (L.erase A).filter fun B => (A ∩ B).Nonempty
  have hsub : T ⊆ S := by
    intro B hB
    obtain ⟨hB, hi⟩ := mem_filter.mp hB
    obtain ⟨hne, hBL⟩ := mem_erase.mp hB
    exact mem_filter.mpr ⟨mem_erase.mpr ⟨hne, hLK hBL⟩, hi⟩
  have hupper : ∑ B ∈ T, (B.card - 1) ≤ 2 * (n - 2) :=
    (sum_le_sum_of_subset hsub).trans (by rw [meeting_weight_eq hpair (hLK hA), hAcard])
  have hcount : ∑ B ∈ T, (if B.card = 2 then 1 else 0) = (T.filter fun B => B.card = 2).card := by
    rw [← sum_filter]
    simp
  have hlower : T.card * 2 ≤ ∑ B ∈ T, (B.card - 1) + (T.filter fun B => B.card = 2).card := by
    rw [← hcount, ← sum_add_distrib]
    calc
      T.card * 2 = ∑ _B ∈ T, 2 := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro B hB
        have hB' := hsize B (hLK (mem_of_mem_erase (mem_filter.mp hB).1))
        split <;> omega
  have hn : 2 ≤ n := hAcard ▸ (by simpa using card_le_univ A : A.card ≤ n)
  have ht : n ≤ T.card := hdegree
  have hfour : 4 ≤ (T.filter fun B => B.card = 2).card := by omega
  simpa only [T, filter_filter] using hfour

theorem through_meeting_card {n : ℕ} {K : Finset (Finset (Fin n))}
    (hpair : ∀ i j : Fin n, i ≠ j → ∃! B, B ∈ K ∧ i ∈ B ∧ j ∈ B)
    {A : Finset (Fin n)} (hA : A ∈ K) {x : Fin n} (hx : x ∉ A) :
    ((K.filter fun B => x ∈ B).filter fun B => (A ∩ B).Nonempty).card = A.card := by
  classical
  have hex (i : Fin n) (hi : i ∈ A) : ∃ B, B ∈ K ∧ x ∈ B ∧ i ∈ B :=
    (hpair x i (fun h => hx (h.symm ▸ hi))).exists
  symm
  refine card_bij (fun i hi => (hex i hi).choose) ?_ ?_ ?_
  · intro i hi
    have hB := (hex i hi).choose_spec
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨hB.1, hB.2.1⟩, ⟨i, mem_inter.mpr ⟨hi, hB.2.2⟩⟩⟩
  · intro i hi j hj heq
    by_contra hij
    have hB := (hex i hi).choose_spec
    have hjB := (hex j hj).choose_spec.2.2
    rw [← heq] at hjB
    have hBA := block_eq_of_pair hpair hB.1 hA hij hB.2.2 hjB hi hj
    exact hx (hBA ▸ hB.2.1)
  · intro B hB
    obtain ⟨hBx, i, hi⟩ := mem_filter.mp hB
    obtain ⟨hB, hxB⟩ := mem_filter.mp hBx
    obtain ⟨hiA, hiB⟩ := mem_inter.mp hi
    have hD := (hex i hiA).choose_spec
    exact ⟨i, hiA, block_eq_of_pair hpair hD.1 hB (fun (h : x = i) => hx (h.symm ▸ hiA))
      hD.2.1 hD.2.2 hxB hiB⟩

theorem uniform_through_card {n r : ℕ} {K : Finset (Finset (Fin n))}
    (hpair : ∀ i j : Fin n, i ≠ j → ∃! B, B ∈ K ∧ i ∈ B ∧ j ∈ B)
    (hsize : ∀ A ∈ K, A.card = r) (hr : 2 ≤ r) (hn : n = r * r) (x : Fin n) :
    (K.filter fun A => x ∈ A).card = r + 1 := by
  have hweight := link_weight_eq hpair x
  rw [show (∑ A ∈ K.filter (fun A => x ∈ A), (A.card - 1)) =
      ∑ _A ∈ K.filter (fun A => x ∈ A), (r - 1) from
      sum_congr rfl (fun A hA => by rw [hsize A (mem_filter.mp hA).1])] at hweight
  simp only [sum_const, nsmul_eq_mul] at hweight
  have hprod : (r + 1) * (r - 1) = n - 1 := by
    have hstep : r - 1 + 1 = r := by omega
    have hsum : (r + 1) * (r - 1) + 1 = r * r := by nlinarith
    omega
  exact Nat.eq_of_mul_eq_mul_right (by omega) (hweight.trans hprod.symm)

theorem existsUnique_parallel_through {n r : ℕ} {K : Finset (Finset (Fin n))}
    (hpair : ∀ i j : Fin n, i ≠ j → ∃! B, B ∈ K ∧ i ∈ B ∧ j ∈ B)
    (hsize : ∀ A ∈ K, A.card = r) (hr : 2 ≤ r) (hn : n = r * r)
    {A : Finset (Fin n)} (hA : A ∈ K) (x : Fin n) :
    ∃! B, B ∈ K ∧ x ∈ B ∧ (B = A ∨ Disjoint A B) := by
  classical
  by_cases hx : x ∈ A
  · refine ⟨A, ⟨hA, hx, Or.inl rfl⟩, ?_⟩
    rintro B ⟨_, hxB, hBA | hd⟩
    · exact hBA
    · exact (disjoint_left.mp hd hx hxB).elim
  · let S := K.filter fun B => x ∈ B
    have hcount := card_filter_add_card_filter_not (s := S) (fun B => (A ∩ B).Nonempty)
    have hm : (S.filter fun B => (A ∩ B).Nonempty).card = r :=
      (through_meeting_card hpair hA hx).trans (hsize A hA)
    have hs : S.card = r + 1 := uniform_through_card hpair hsize hr hn x
    have hone : (S.filter fun B => ¬ (A ∩ B).Nonempty).card = 1 := by omega
    refine (existsUnique_congr ?_).mp (card_eq_one_iff_existsUnique.mp hone)
    intro B
    simp only [S, mem_filter, ← not_disjoint_iff_nonempty_inter, not_not, and_assoc]
    constructor
    · rintro ⟨hB, hxB, hd⟩
      exact ⟨hB, hxB, Or.inr hd⟩
    · rintro ⟨hB, hxB, hBA | hd⟩
      · exact (hx (hBA ▸ hxB)).elim
      · exact ⟨hB, hxB, hd⟩

theorem color_uniform_square {n r : ℕ} [NeZero n] {K : Finset (Finset (Fin n))}
    (hpair : ∀ i j : Fin n, i ≠ j → ∃! B, B ∈ K ∧ i ∈ B ∧ j ∈ B)
    (hsize : ∀ A ∈ K, A.card = r) (hr : 2 ≤ r) (hn : n = r * r) :
    ∃ c : Finset (Fin n) → Fin n, (∀ X ∈ K, ∀ Y ∈ K, X ≠ Y → (X ∩ Y).Nonempty → c X ≠ c Y) := by
  classical
  let x : Fin n := 0
  let S := K.filter fun A => x ∈ A
  have hS : Fintype.card S ≤ Fintype.card (Fin n) := by
    rw [Fintype.card_coe, Fintype.card_fin, uniform_through_card hpair hsize hr hn x]
    have hle := Nat.mul_le_mul_right r hr
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hS
  have hparallel {A : Finset (Fin n)} (hA : A ∈ K) (y : Fin n) :=
    existsUnique_parallel_through hpair hsize hr hn hA y
  let rep (A : Finset (Fin n)) (hA : A ∈ K) : S :=
    let h := (hparallel hA x).exists
    ⟨h.choose, mem_filter.mpr ⟨h.choose_spec.1, h.choose_spec.2.1⟩⟩
  have hrep (A : Finset (Fin n)) (hA : A ∈ K) : A = (rep A hA).val ∨ Disjoint (rep A hA).val A :=
    (hparallel hA x).exists.choose_spec.2.2.imp Eq.symm (fun hd => hd.symm)
  refine ⟨fun A => if hA : A ∈ K then e (rep A hA) else 0, ?_⟩
  intro A hA B hB hAB hmeet heq
  simp only [dif_pos hA, dif_pos hB] at heq
  have hsame : rep B hB = rep A hA := (e.injective heq).symm
  have hBR := hrep B hB
  rw [hsame] at hBR
  obtain ⟨y, hy⟩ := hmeet
  have hR : (rep A hA).val ∈ K := (mem_filter.mp (rep A hA).property).1
  exact hAB ((hparallel hR y).unique ⟨hA, (mem_inter.mp hy).1, hrep A hA⟩
    ⟨hB, (mem_inter.mp hy).2, hBR⟩)

def H1 : Prop :=
  ∀ R : ℕ, ∀ᶠ n in Filter.atTop, ∀ K L : Finset (Finset (Fin n)),
    (∀ A ∈ K, 2 ≤ A.card ∧ A.card * A.card ≤ n) →
    (∀ i j : Fin n, i ≠ j → ∃! B, B ∈ K ∧ i ∈ B ∧ j ∈ B) →
    L ⊆ K → (∀ A ∈ L, A.card ≤ R) →
    (¬ ∃ c : Finset (Fin n) → Fin n, (∀ X ∈ L, ∀ Y ∈ L, X ≠ Y → (X ∩ Y).Nonempty → c X ≠ c Y)) →
    (∀ A ∈ L, (∃ c : Finset (Fin n) → Fin n, (∀ X ∈ (L.erase A), ∀ Y ∈ (L.erase A), X ≠ Y → (X ∩ Y).Nonempty → c X ≠ c Y)) ∧
      n ≤ ((L.erase A).filter fun B => (A ∩ B).Nonempty).card) →
    (∀ A ∈ L, ∀ c : Finset (Fin n) → Fin n, (∀ X ∈ (L.erase A), ∀ Y ∈ (L.erase A), X ≠ Y → (X ∩ Y).Nonempty → c X ≠ c Y) →
      ((L.erase A).filter (fun B => (A ∩ B).Nonempty)).image c = Finset.univ) →
    (∃ A ∈ L, 3 ≤ A.card) →
    (∃ A ∈ L, A.card * A.card < n) →
    (∀ A ∈ L, A.card = 2 →
      4 ≤ ((L.erase A).filter fun B => (A ∩ B).Nonempty ∧ B.card = 2).card) →
    False

def H2 : Prop :=
  ∃ R : ℕ, ∀ᶠ n in Filter.atTop, ∀ K L : Finset (Finset (Fin n)),
    (∀ A ∈ K, 2 ≤ A.card ∧ A.card * A.card ≤ n) →
    (∀ i j : Fin n, i ≠ j → ∃! B, B ∈ K ∧ i ∈ B ∧ j ∈ B) →
    L ⊆ K → (∃ A ∈ L, R < A.card) →
    (¬ ∃ c : Finset (Fin n) → Fin n, (∀ X ∈ L, ∀ Y ∈ L, X ≠ Y → (X ∩ Y).Nonempty → c X ≠ c Y)) →
    (∀ A ∈ L, (∃ c : Finset (Fin n) → Fin n, (∀ X ∈ (L.erase A), ∀ Y ∈ (L.erase A), X ≠ Y → (X ∩ Y).Nonempty → c X ≠ c Y)) ∧
      n ≤ ((L.erase A).filter fun B => (A ∩ B).Nonempty).card) →
    (∀ A ∈ L, ∀ c : Finset (Fin n) → Fin n, (∀ X ∈ (L.erase A), ∀ Y ∈ (L.erase A), X ≠ Y → (X ∩ Y).Nonempty → c X ≠ c Y) →
      ((L.erase A).filter (fun B => (A ∩ B).Nonempty)).image c = Finset.univ) →
    (∃ A ∈ L, 3 ≤ A.card) →
    (∃ A ∈ L, A.card * A.card < n) →
    (∀ A ∈ L, A.card = 2 →
      4 ≤ ((L.erase A).filter fun B => (A ∩ B).Nonempty ∧ B.card = 2).card) →
    False

theorem main : H1 → H2 → OMA.R_Erdos19_erdos_19_variants_large_n_R1.H1 := by
  classical
  intro hA hB
  obtain ⟨R, hR⟩ := hB
  unfold OMA.R_Erdos19_erdos_19_variants_large_n_R1.H1
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ), hA R, hR] with n hn hsmall hlarge
  intro K hsize hpair
  let : NeZero n := ⟨by omega⟩
  suffices h : ∃ c : Finset (Fin n) → Fin n, (∀ X ∈ K, ∀ Y ∈ K, X ≠ Y → (X ∩ Y).Nonempty → c X ≠ c Y) by
    obtain ⟨c, hc⟩ := h
    exact ⟨fun A => c A.val, fun A B hAB =>
      hc A.val A.property B.val B.property (fun heq => hAB (Subtype.ext heq))⟩
  by_contra hbad
  obtain ⟨L, hLK, hL, hLbad, hcritical⟩ := exists_critical_subfamily hbad
  have hLthree : ∃ A ∈ L, 3 ≤ A.card := by
    by_contra hnone
    push Not at hnone
    apply hLbad (color_two_blocks ?_)
    intro A hA
    have hlow := (hsize A (hLK hA)).1
    have hhigh := hnone A hA
    omega
  have hLstrict : ∃ A ∈ L, A.card * A.card < n := by
    by_contra hnone
    push Not at hnone
    have hsq (A : Finset (Fin n)) (hA : A ∈ L) : n = A.card * A.card :=
      le_antisymm (hnone A hA) (hsize A (hLK hA)).2
    obtain ⟨A, hA⟩ := hL
    have huni (B : Finset (Fin n)) (hB : B ∈ L) : B.card = A.card := by
      have heq := (hsq B hB).symm.trans (hsq A hA)
      rcases lt_trichotomy B.card A.card with hlt | he | hgt
      · exact (Nat.ne_of_lt (Nat.mul_self_lt_mul_self hlt) heq).elim
      · exact he
      · exact (Nat.ne_of_lt (Nat.mul_self_lt_mul_self hgt) heq.symm).elim
    have heq := uniform_square_saturation hpair hLK ⟨A, hA⟩ (hsq A hA)
      (fun B hB => (hsize B hB).1) huni (fun B hB => (hcritical B hB).2)
    rw [heq] at hLbad
    exact hLbad (color_uniform_square hpair (fun B hB => huni B (heq.symm ▸ hB))
      (hsize A (hLK hA)).1 (hsq A hA))
  have hLpairs (A : Finset (Fin n)) (hA : A ∈ L) (hAcard : A.card = 2) :
      4 ≤ ((L.erase A).filter fun B => (A ∩ B).Nonempty ∧ B.card = 2).card :=
    critical_pair_neighbor_card hpair hLK (fun B hB => (hsize B hB).1) hA hAcard (hcritical A hA).2
  by_cases hbound : ∀ A ∈ L, A.card ≤ R
  · exact hsmall K L hsize hpair hLK hbound hLbad hcritical
      (fun _ _ _ => all_colors_blocked hLbad) hLthree hLstrict hLpairs
  · push Not at hbound
    exact hlarge K L hsize hpair hLK hbound hLbad hcritical
      (fun _ _ _ => all_colors_blocked hLbad) hLthree hLstrict hLpairs

end OMA.R_Erdos19_erdos_19_variants_large_n_R1_H1_R1
