import OMAReductions.R_Erdos643_erdos_643_parts_ii_R1

/-!
# Erdős 643 in rank at least four

A missing-face count gives a finite upper bound after finding a star with
sufficiently small quadratic deficit. The swap and deficit method is adapted
from Huang, Ma, and Yang, arXiv:2609.37744, Section 3.
-/

open Finset
open Filter (atTop eventually_ge_atTop)

namespace OMA.R_Erdos643_erdos_643_parts_ii_R1_H2_R1

variable {α : Type*} [DecidableEq α]

private def missing (V : Finset α) (F : Finset (Finset α)) (c : α) (r : ℕ) :
    Finset (Finset α) :=
  (V.powersetCard (r - 1)).filter fun W => insert c W ∉ F

private def offStar (F : Finset (Finset α)) (c : α) : Finset (Finset α) :=
  F.filter fun E => c ∉ E

private def misses (M : Finset (Finset α)) (T : Finset α) : Finset (Finset α) :=
  M.filter fun W => T ⊆ W

private theorem swap {F : Finset (Finset α)} {c : α} {E G K : Finset α}
    (hfree : ¬ F.HasRepeatedDisjointUnion) (hE : E ∈ F) (hG : G ∈ F)
    (hEG : E ≠ G) (hEc : c ∉ E) (hGc : c ∉ G) (hKc : c ∈ K)
    (hK : Disjoint K (E ∪ G)) (hT : K ∪ (E \ G) ∈ F)
    (hU : K ∪ (G \ E) ∈ F) : False := by
  have hcT : c ∈ K ∪ (E \ G) := mem_union_left _ hKc
  have hcU : c ∈ K ∪ (G \ E) := mem_union_left _ hKc
  have hcross {A B : Finset α} (ha : c ∈ A) (hb : c ∉ B) : A ≠ B :=
    fun h => hb (h ▸ ha)
  have hd₁ : Disjoint E (K ∪ (G \ E)) := by
    rw [Finset.disjoint_union_right]
    exact ⟨(Finset.disjoint_union_right.mp hK).1.symm, Finset.disjoint_left.mpr fun _ hx => fun hy => (mem_sdiff.mp hy).2 hx⟩
  have hd₂ : Disjoint G (K ∪ (E \ G)) := by
    rw [Finset.disjoint_union_right]
    exact ⟨(Finset.disjoint_union_right.mp hK).2.symm, Finset.disjoint_left.mpr fun _ hx => fun hy => (mem_sdiff.mp hy).2 hx⟩
  have hu : E ∪ (K ∪ (G \ E)) = G ∪ (K ∪ (E \ G)) := by
    ext x
    simp only [mem_union, mem_sdiff]
    tauto
  have hTU : K ∪ (G \ E) ≠ K ∪ (E \ G) := by
    intro hh
    apply hEG
    ext x
    have hdis : x ∈ K → x ∉ E ∪ G := fun hx => Finset.disjoint_left.mp hK hx
    have heq : x ∈ K ∪ (G \ E) ↔ x ∈ K ∪ (E \ G) := by rw [hh]
    simp only [mem_union, mem_sdiff] at hdis heq
    tauto
  exact hfree ⟨E, hE, K ∪ (G \ E), hU, G, hG, K ∪ (E \ G), hT,
    hd₁, hd₂, hu, (hcross hcU hEc).symm, (hcross hcT hGc).symm,
    hEG, (hcross hcT hEc).symm, hcross hcU hGc, hTU⟩

/-- Each completion of the two residual sets outside the two edges yields a
missing star edge on at least one side. -/
private theorem sub_card_of_swap {V : Finset α} {F : Finset (Finset α)}
    {c : α} {r : ℕ} {E G : Finset α} (hfree : ¬ F.HasRepeatedDisjointUnion)
    (hcV : c ∉ V) (hE : E ∈ F) (hG : G ∈ F) (hEv : E ⊆ V) (hGv : G ⊆ V)
    (he : E.card = r) (hg : G.card = r) (hEG : E ≠ G)
    (hi : (E ∩ G).Nonempty) :
    (V.card - 2 * r).choose ((E ∩ G).card - 1) ≤
      (misses (missing V F c r) (E \ G)).card +
      (misses (missing V F c r) (G \ E)).card := by
  let T := E \ G
  let U := G \ E
  let M := missing V F c r
  let D := (V \ (E ∪ G)).powersetCard ((E ∩ G).card - 1)
  have hT : T.card + (E ∩ G).card = r := by
    change (E \ G).card + (E ∩ G).card = r
    rw [Finset.card_sdiff_add_card_inter, he]
  have hU : U.card + (E ∩ G).card = r := by
    change (G \ E).card + (E ∩ G).card = r
    rw [inter_comm E G, Finset.card_sdiff_add_card_inter, hg]
  have hcT : 0 < (E ∩ G).card := Finset.card_pos.mpr hi
  have hp {W : Finset α} (hW : W ∈ D) (A : Finset α) (hA : A ⊆ E ∪ G)
      (ha : A.card + (E ∩ G).card = r) (hm : insert c (W ∪ A) ∉ F) :
      W ∪ A ∈ misses M A := by
    obtain ⟨hWs, hWc⟩ := mem_powersetCard.mp hW
    have hWA : Disjoint W A := by
      apply Finset.disjoint_left.mpr
      exact fun x hx hy => (mem_sdiff.mp (hWs hx)).2 (hA hy)
    have hs : W ∪ A ⊆ V :=
      union_subset (hWs.trans sdiff_subset) (hA.trans (union_subset hEv hGv))
    have hca : (W ∪ A).card = r - 1 := by
      rw [card_union_of_disjoint hWA, hWc]
      omega
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hs, hca⟩, hm⟩,
      subset_union_right⟩
  have hsubT : T ⊆ E ∪ G := sdiff_subset.trans subset_union_left
  have hsubU : U ⊆ E ∪ G := sdiff_subset.trans subset_union_right
  let f (W : Finset α) : Finset α ⊕ Finset α :=
    if insert c (W ∪ T) ∈ F then Sum.inr (W ∪ U) else Sum.inl (W ∪ T)
  have hmaps : Set.MapsTo f D ((misses M T).disjSum (misses M U)) := by
    intro W hW
    have hw : W ⊆ V \ (E ∪ G) := (mem_powersetCard.mp (show W ∈ D from hW)).1
    have hK : Disjoint (insert c W) (E ∪ G) := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      rcases mem_insert.mp hx with rfl | hx
      · exact hcV (union_subset hEv hGv hy)
      · exact (mem_sdiff.mp (hw hx)).2 hy
    by_cases ht : insert c (W ∪ T) ∈ F
    · have hu : insert c (W ∪ U) ∉ F := by
        intro hu
        have hct : c ∉ E := fun h => hcV (hEv h)
        have hcu : c ∉ G := fun h => hcV (hGv h)
        exact swap hfree hE hG hEG hct hcu (mem_insert_self _ _) hK
          (by simpa only [insert_union, T] using ht)
          (by simpa only [insert_union, U] using hu)
      simpa [f, ht] using hp hW U hsubU hU hu
    · simpa [f, ht] using hp hW T hsubT hT ht
  have hinj : (D : Set (Finset α)).InjOn f := by
    intro A hA B hB hab
    have recover {Y Z Q : Finset α} (hy : Y ∈ D) (hz : Z ∈ D)
        (hq : Q ⊆ E ∪ G) (heq : Y ∪ Q = Z ∪ Q) : Y = Z := by
      have hy' := (mem_powersetCard.mp hy).1
      have hz' := (mem_powersetCard.mp hz).1
      ext a
      have h1 : a ∈ Y → a ∉ Q := fun h hq' => (mem_sdiff.mp (hy' h)).2 (hq hq')
      have h2 : a ∈ Z → a ∉ Q := fun h hq' => (mem_sdiff.mp (hz' h)).2 (hq hq')
      have heq' := Finset.ext_iff.mp heq a
      simp only [mem_union] at heq'
      tauto
    by_cases h1 : insert c (A ∪ T) ∈ F <;>
      by_cases h2 : insert c (B ∪ T) ∈ F <;>
      simp [f, h1, h2] at hab
    · exact recover hA hB hsubU hab
    · exact recover hA hB hsubT hab
  have hcnt := card_le_card_of_injOn f hmaps hinj
  rw [card_disjSum] at hcnt
  have hbase : V.card - 2 * r ≤ (V \ (E ∪ G)).card := by
    rw [card_sdiff_of_subset (union_subset hEv hGv)]
    have hu := card_union_le E G
    omega
  have hD : (V.card - 2 * r).choose ((E ∩ G).card - 1) ≤ D.card := by
    rw [show D.card = (V \ (E ∪ G)).card.choose ((E ∩ G).card - 1) from card_powersetCard _ _]
    exact Nat.choose_le_choose _ hbase
  exact hD.trans hcnt

private theorem choose_mono_small {n k l : ℕ} (hkl : k ≤ l) (hl : l ≤ n / 2) :
    n.choose k ≤ n.choose l := by
  induction hkl with
  | refl => exact le_rfl
  | step hj ih =>
      exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

private def bad (V : Finset α) (M : Finset (Finset α)) (r t : ℕ) :
    Finset (Finset α) :=
  (V.powersetCard t).filter fun T =>
    (V.card - 2 * r).choose (r - 1 - t) ≤ 2 * (misses M T).card

private theorem sum_misses_le {V : Finset α} {M B : Finset (Finset α)} {r t : ℕ}
    (hM : M ⊆ V.powersetCard (r - 1)) (hB : B ⊆ V.powersetCard t) :
    (∑ T ∈ B, (misses M T).card) ≤ M.card * (r - 1).choose t := by
  classical
  calc
    _ = ∑ T ∈ B, ∑ W ∈ M, if T ⊆ W then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro T _
      rw [misses, Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ W ∈ M, ∑ T ∈ B, if T ⊆ W then 1 else 0 := Finset.sum_comm
    _ ≤ ∑ _W ∈ M, (r - 1).choose t := by
      apply Finset.sum_le_sum
      intro W hW
      rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones,
        ← (mem_powersetCard.mp (hM hW)).2, ← card_powersetCard]
      exact card_le_card fun T hT =>
        mem_powersetCard.mpr ⟨(mem_filter.mp hT).2, (mem_powersetCard.mp (hB (mem_filter.mp hT).1)).2⟩
    _ = _ := by simp

/-- Count the incidences of low-degree residual sets with missing star faces. -/
private theorem bad_bound {V : Finset α} {M : Finset (Finset α)} {r t : ℕ}
    (hM : M ⊆ V.powersetCard (r - 1)) :
    (bad V M r t).card * (V.card - 2 * r).choose (r - 1 - t) ≤
      2 * (M.card * (r - 1).choose t) := by
  calc
    _ = ∑ _T ∈ bad V M r t, (V.card - 2 * r).choose (r - 1 - t) := by simp
    _ ≤ ∑ T ∈ bad V M r t, 2 * (misses M T).card :=
      Finset.sum_le_sum fun T hT => (mem_filter.mp hT).2
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact Nat.mul_le_mul_left 2 (sum_misses_le hM fun _ hT => (mem_filter.mp hT).1)

private theorem count_star {V : Finset α} {F : Finset (Finset α)} {c : α} {r : ℕ}
    (hc : c ∉ V) (hF : ∀ E ∈ F, E ⊆ insert c V ∧ E.card = r) :
    F.card + (missing V F c r).card = V.card.choose (r - 1) + (offStar F c).card := by
  classical
  let S := (V.powersetCard (r - 1)).filter fun W => insert c W ∈ F
  have hpart := Finset.card_filter_add_card_filter_not (s := V.powersetCard (r - 1))
    (p := fun W => insert c W ∈ F)
  have hpartF := Finset.card_filter_add_card_filter_not (s := F) (p := fun E => c ∈ E)
  have hb : S.card = (F.filter fun E => c ∈ E).card := by
    apply Finset.card_bij (fun W _ => insert c W)
    · intro W hW
      exact mem_filter.mpr ⟨(mem_filter.mp hW).2, mem_insert_self _ _⟩
    · intro W hW Z hZ h
      have hw : c ∉ W := fun hw => hc ((mem_powersetCard.mp (mem_filter.mp hW).1).1 hw)
      have hz : c ∉ Z := fun hz => hc ((mem_powersetCard.mp (mem_filter.mp hZ).1).1 hz)
      simpa [erase_insert hw, erase_insert hz] using congrArg (fun T : Finset α => T.erase c) h
    · intro E hE
      obtain ⟨he, hce⟩ := mem_filter.mp hE
      have hsub : E.erase c ⊆ V := by
        intro x hx
        obtain ⟨hne, hxe⟩ := mem_erase.mp hx
        exact (mem_insert.mp ((hF E he).1 hxe)).resolve_left hne
      have hceq : (E.erase c).card = r - 1 := by rw [card_erase_of_mem hce, (hF E he).2]
      have hrec : insert c (E.erase c) = E := insert_erase hce
      exact ⟨E.erase c, mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hsub, hceq⟩, hrec.symm ▸ he⟩, hrec⟩
  change S.card + (missing V F c r).card = _ at hpart
  change (F.filter fun E => c ∈ E).card + (offStar F c).card = _ at hpartF
  rw [card_powersetCard, hb] at hpart
  omega

private theorem card_of_disjoint_residuals {V T : Finset α} {J : Finset (Finset α)}
    (hne : ∀ E ∈ J, (E \ T).Nonempty) (hV : ∀ E ∈ J, E ⊆ V)
    (hd : ∀ E ∈ J, ∀ G ∈ J, E ≠ G → Disjoint (E \ T) (G \ T)) :
    J.card ≤ V.card := by
  classical
  let f (E : J) : α := Classical.choose (hne E.1 E.2)
  have hf (E : J) : f E ∈ E.1 \ T := Classical.choose_spec (hne E.1 E.2)
  let g (E : J) : V := ⟨f E, hV E.1 E.2 (mem_sdiff.mp (hf E)).1⟩
  apply Finset.card_le_card_of_injective (f := g)
  intro E G heq
  apply Subtype.ext
  by_contra h
  have hfg : f E = f G := congrArg Subtype.val heq
  exact Finset.disjoint_left.mp (hd E.1 E.2 G.1 G.2 h) (hf E) (hfg.symm ▸ hf G)

/-- Bound the family using a quadratic bound on the deficit of a fixed star. -/
private theorem finite_near_star {V : Finset α} {F : Finset (Finset α)} {c : α} {r : ℕ}
    (hr : 4 ≤ r) (hn : 4 * r ≤ V.card) (hc : c ∉ V)
    (hF : ∀ E ∈ F, E ⊆ insert c V ∧ E.card = r)
    (hfree : ¬ F.HasRepeatedDisjointUnion)
    (hm : 2 * (missing V F c r).card < (V.card - 2 * r).choose 2) :
    F.card ≤ V.card.choose (r - 1) + V.card + 4 * (r - 1) * (missing V F c r).card := by
  classical
  let M := missing V F c r
  let H := offStar F c
  let B := bad V M r (r - 2)
  have hoff {E : Finset α} (hE : E ∈ H) : E ∈ F ∧ E ⊆ V ∧ E.card = r := by
    obtain ⟨he, hec⟩ := mem_filter.mp hE
    refine ⟨he, fun x hx => (mem_insert.mp ((hF E he).1 hx)).resolve_left ?_, (hF E he).2⟩
    rintro rfl
    exact hec hx
  have hswap {E G : Finset α} (hE : E ∈ H) (hG : G ∈ H) (hne : E ≠ G)
      (hi : (E ∩ G).Nonempty) :
      (V.card - 2 * r).choose ((E ∩ G).card - 1) ≤
        (misses M (E \ G)).card + (misses M (G \ E)).card :=
    sub_card_of_swap hfree hc (hoff hE).1 (hoff hG).1 (hoff hE).2.1 (hoff hG).2.1
      (hoff hE).2.2 (hoff hG).2.2 hne hi
  have hsmall {E G : Finset α} (hE : E ∈ H) (hG : G ∈ H) (hne : E ≠ G) :
      (E ∩ G).card ≤ 2 := by
    by_contra! h
    have hle := card_le_card (inter_subset_left (s₁ := E) (s₂ := G))
    have hEr := (hoff hE).2.2
    have hchoose : (V.card - 2 * r).choose 2 ≤
        (V.card - 2 * r).choose ((E ∩ G).card - 1) :=
      choose_mono_small (by omega) (by omega)
    have hbound := hchoose.trans (hswap hE hG hne (card_pos.mp (by omega)))
    have hT : (misses M (E \ G)).card ≤ M.card := card_le_card (filter_subset _ _)
    have hU : (misses M (G \ E)).card ≤ M.card := card_le_card (filter_subset _ _)
    change 2 * M.card < _ at hm
    omega
  -- A missing face is in at most one off-star edge. A low-degree residual set
  -- can occur in several off-star edges, but their complements are disjoint.
  let cover (T : Finset α) := H.filter fun E => T ⊆ E
  have hcoverM : ∀ T ∈ M, (cover T).card ≤ 1 := by
    intro T hT
    have hTc := (mem_powersetCard.mp (mem_filter.mp hT).1).2
    apply Finset.card_le_one.mpr
    intro E hE G hG
    by_contra hne
    have := hsmall (mem_filter.mp hE).1 (mem_filter.mp hG).1 hne
    have := card_le_card (subset_inter (mem_filter.mp hE).2 (mem_filter.mp hG).2)
    omega
  have hcoverB : ∀ T ∈ B, (cover T).card ≤ V.card := by
    intro T hT
    have hTc := (mem_powersetCard.mp (mem_filter.mp hT).1).2
    apply card_of_disjoint_residuals (T := T)
    · intro E hE
      have hEt := (mem_filter.mp hE).2
      have hEr := (hoff (mem_filter.mp hE).1).2.2
      apply card_pos.mp
      rw [card_sdiff_of_subset hEt]
      omega
    · exact fun E hE => (hoff (mem_filter.mp hE).1).2.1
    · intro E hE G hG hne
      apply Finset.disjoint_left.mpr
      intro x hx hy
      obtain ⟨hxE, hxT⟩ := mem_sdiff.mp hx
      have hxG := (mem_sdiff.mp hy).1
      have hsub : insert x T ⊆ E ∩ G :=
        insert_subset_iff.mpr ⟨mem_inter.mpr ⟨hxE, hxG⟩,
          subset_inter (mem_filter.mp hE).2 (mem_filter.mp hG).2⟩
      have hh := card_le_card hsub
      rw [card_insert_of_notMem hxT] at hh
      have := hsmall (mem_filter.mp hE).1 (mem_filter.mp hG).1 hne
      omega
  -- Off-star edges avoiding both types of residual set form a matching.
  let J := H \ ((M.biUnion cover) ∪ (B.biUnion cover))
  have hJ : J.card ≤ V.card := by
    apply card_of_disjoint_residuals (T := ∅)
    · intro E hE
      have hEr := (hoff (mem_sdiff.mp hE).1).2.2
      simpa using (card_pos.mp (show 0 < E.card by omega))
    · exact fun E hE => (hoff (mem_sdiff.mp hE).1).2.1
    · intro E hE G hG hne
      simp only [sdiff_empty]
      by_contra hdis
      have hi : (E ∩ G).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr fun h => hdis (Finset.disjoint_iff_inter_eq_empty.mpr h)
      obtain ⟨heH, heNo⟩ := mem_sdiff.mp hE
      obtain ⟨hgH, hgNo⟩ := mem_sdiff.mp hG
      have hi₁ := card_pos.mpr hi
      have hi₂ := hsmall heH hgH hne
      have ht := hswap heH hgH hne hi
      have hTc := card_sdiff_add_card_inter E G
      have hUc := card_sdiff_add_card_inter G E
      rw [inter_comm G E, (hoff hgH).2.2] at hUc
      rw [(hoff heH).2.2] at hTc
      have htm : E \ G ∉ M := fun h =>
        heNo (mem_union_left _ (mem_biUnion.mpr ⟨_, h, mem_filter.mpr ⟨heH, sdiff_subset⟩⟩))
      have hum : G \ E ∉ M := fun h =>
        hgNo (mem_union_left _ (mem_biUnion.mpr ⟨_, h, mem_filter.mpr ⟨hgH, sdiff_subset⟩⟩))
      have htb : E \ G ∉ B := fun h =>
        heNo (mem_union_right _ (mem_biUnion.mpr ⟨_, h, mem_filter.mpr ⟨heH, sdiff_subset⟩⟩))
      have hub : G \ E ∉ B := fun h =>
        hgNo (mem_union_right _ (mem_biUnion.mpr ⟨_, h, mem_filter.mpr ⟨hgH, sdiff_subset⟩⟩))
      rcases (show (E ∩ G).card = 1 ∨ (E ∩ G).card = 2 by omega) with h | h
      · have hzero {S : Finset α} (hS : S.card = r - 1) (hS' : S ∉ M) :
            (misses M S).card = 0 := by
          apply card_eq_zero.mpr
          apply eq_empty_iff_forall_notMem.mpr
          intro W hW
          obtain ⟨hw, hsub⟩ := mem_filter.mp hW
          have hwc := (mem_powersetCard.mp (mem_filter.mp hw).1).2
          exact hS' (Finset.eq_of_subset_of_card_le hsub (by omega) ▸ hw)
        rw [h, Nat.sub_self, Nat.choose_zero_right,
          hzero (by omega) htm, hzero (by omega) hum] at ht
        omega
      · have hlt {S : Finset α} (hS : S ⊆ V) (hSc : S.card = r - 2) (hSb : S ∉ B) :
            2 * (misses M S).card < V.card - 2 * r := by
          by_contra! hh
          have heq : r - 1 - (r - 2) = 1 := by omega
          apply hSb
          refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hS, hSc⟩, ?_⟩
          rwa [heq, Nat.choose_one_right]
        have htlt := hlt (sdiff_subset.trans (hoff heH).2.1) (by omega) htb
        have hult := hlt (sdiff_subset.trans (hoff hgH).2.1) (by omega) hub
        rw [h, show 2 - 1 = 1 by decide, Nat.choose_one_right] at ht
        omega
  have hcovM : (M.biUnion cover).card ≤ M.card := by
    calc
      _ ≤ ∑ T ∈ M, (cover T).card := card_biUnion_le
      _ ≤ ∑ _T ∈ M, 1 := Finset.sum_le_sum hcoverM
      _ = _ := by simp
  have hcovB : (B.biUnion cover).card ≤ B.card * V.card := by
    calc
      _ ≤ ∑ T ∈ B, (cover T).card := card_biUnion_le
      _ ≤ ∑ _T ∈ B, V.card := Finset.sum_le_sum hcoverB
      _ = _ := by simp
  have hboundH : H.card ≤ M.card + B.card * V.card + V.card := by
    have hsub : H ⊆ ((M.biUnion cover) ∪ (B.biUnion cover)) ∪ J := by
      intro E hE
      by_cases h : E ∈ (M.biUnion cover) ∪ (B.biUnion cover)
      · exact mem_union_left _ h
      · exact mem_union_right _ (mem_sdiff.mpr ⟨hE, h⟩)
    have h₁ := card_le_card hsub
    have h₂ := card_union_le ((M.biUnion cover) ∪ (B.biUnion cover)) J
    have h₃ := card_union_le (M.biUnion cover) (B.biUnion cover)
    omega
  have hboundB : B.card * (V.card - 2 * r) ≤ 2 * (M.card * (r - 1)) := by
    have h := bad_bound (V := V) (M := M) (r := r) (t := r - 2) (filter_subset _ _)
    have heq : r - 1 - (r - 2) = 1 := by omega
    have hs := Nat.choose_symm (n := r - 1) (k := r - 2) (by omega)
    rw [heq, Nat.choose_one_right] at hs
    rwa [heq, Nat.choose_one_right, ← hs] at h
  have hBV : B.card * V.card ≤ 4 * (r - 1) * M.card := by
    calc
      _ ≤ B.card * (2 * (V.card - 2 * r)) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (B.card * (V.card - 2 * r)) := by ring
      _ ≤ 2 * (2 * (M.card * (r - 1))) := Nat.mul_le_mul_left _ hboundB
      _ = _ := by ring
  have hcard := count_star hc hF
  change F.card + M.card = V.card.choose (r - 1) + H.card at hcard
  change F.card ≤ _ + _ + _ * M.card
  omega

/-- Qualitative stability for families at least as large as a full star.
    Huang, Ma, and Yang, Theorem 1.3. -/
def H1 : Prop :=
  ∀ r : ℕ, 4 ≤ r → ∀ a : ℕ, 0 < a → ∀ᶠ n : ℕ in atTop,
    ∀ F : Finset (Finset (Fin n)), F.IsUniform r → ¬ F.HasRepeatedDisjointUnion →
      (n - 1).choose (r - 1) ≤ F.card →
      ∃ c : Fin n,
        let m := (((Finset.univ.erase c).powersetCard (r - 1)).filter
          fun W => insert c W ∉ F).card
        a * m ≤ (n - 1).choose (r - 1)

/-- A quadratic deficit threshold for a nearly full star.
    Huang, Ma, and Yang, Claim 3.8 gives the stronger bound `n log n`. -/
def H2 : Prop :=
  ∀ r : ℕ, 4 ≤ r → ∃ a : ℕ, 0 < a ∧ ∀ᶠ n : ℕ in atTop,
    ∀ (F : Finset (Finset (Fin n))) (c : Fin n),
      F.IsUniform r → ¬ F.HasRepeatedDisjointUnion →
      (n - 1).choose (r - 1) ≤ F.card →
      let m := (((Finset.univ.erase c).powersetCard (r - 1)).filter
        fun W => insert c W ∉ F).card
      a * m ≤ (n - 1).choose (r - 1) →
      4 * r * m < (n - 1 - 2 * r).choose 2

theorem main : H1 → H2 → OMA.R_Erdos643_erdos_643_parts_ii_R1.H2 := by
  intro hstab himprove r hr
  classical
  obtain ⟨a, ha, happly⟩ := himprove r hr
  filter_upwards [hstab r hr a ha, happly, eventually_ge_atTop (4 * r + 1)] with
    n hstabn himproven hn
  unfold Hypergraph.extremalNumber
  refine Finset.sup_le fun F hF => ?_
  obtain ⟨hSub, hfree⟩ :=
    (@Finset.mem_filter _ (fun F : Finset (Finset (Fin n)) => ¬ F.HasRepeatedDisjointUnion)
      (fun _ => Classical.propDecidable _) _ _).mp hF
  have hu : F.IsUniform r := fun E hE =>
    (mem_powersetCard.mp (mem_powerset.mp hSub hE)).2
  by_cases hcard : (n - 1).choose (r - 1) ≤ F.card
  · obtain ⟨c, hnear⟩ := hstabn F hu hfree hcard
    have hm := himproven F c hu hfree hcard hnear
    let V := (Finset.univ : Finset (Fin n)).erase c
    have hc : c ∉ V := notMem_erase _ _
    have hV : V.card = n - 1 := by simp [V]
    have hG (E : Finset (Fin n)) (he : E ∈ F) : E ⊆ insert c V ∧ E.card = r := by
      refine ⟨?_, hu E he⟩
      simp [V, insert_erase (Finset.mem_univ c)]
    change 4 * r * (missing V F c r).card < (n - 1 - 2 * r).choose 2 at hm
    have hmass : 2 * (missing V F c r).card < (V.card - 2 * r).choose 2 := by
      rw [hV]
      exact (Nat.mul_le_mul_right _ (show 2 ≤ 4 * r by omega)).trans_lt hm
    have hb := finite_near_star hr (by omega : 4 * r ≤ V.card) hc hG hfree hmass
    rw [hV] at hb
    have he : 4 * (r - 1) * (missing V F c r).card ≤ (n - 1).choose (r - 2) := by
      calc
        _ ≤ 4 * r * (missing V F c r).card :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
        _ ≤ (n - 1 - 2 * r).choose 2 := hm.le
        _ ≤ (n - 1).choose 2 := Nat.choose_le_choose _ (by omega)
        _ ≤ _ := choose_mono_small (by omega) (by omega)
    have hp : n.choose (r - 1) = (n - 1).choose (r - 1) + (n - 1).choose (r - 2) := by
      have h := Nat.choose_succ_succ' (n - 1) (r - 2)
      rwa [show n - 1 + 1 = n by omega, show r - 2 + 1 = r - 1 by omega, add_comm] at h
    omega
  · have hle := Nat.choose_le_choose (r - 1) (show n - 1 ≤ n by omega)
    omega

end OMA.R_Erdos643_erdos_643_parts_ii_R1_H2_R1
