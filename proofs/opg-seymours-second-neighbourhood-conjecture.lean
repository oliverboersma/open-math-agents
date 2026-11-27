import OMAStatements.S_opg_seymours_second_neighbourhood_conjecture
import Mathlib
namespace SNCProof

open Finset
open scoped BigOperators Classical

private abbrev Rows (V : Type) := V → Finset V

variable {V : Type}

private def Oriented (H : Rows V) : Prop :=
  (∀ v, v ∈ H v) ∧ (∀ ⦃u v⦄, v ∈ H u → u ∈ H v → u = v)

private noncomputable def close (H : Rows V) (X : Finset V) : Finset V := X.biUnion H

private noncomputable def bd (H : Rows V) (X : Finset V) : Finset V := close H X \ X

private noncomputable def b (H : Rows V) (X : Finset V) : ℕ := (bd H X).card

private def bad (H : Rows V) : Prop := ∀ v, b H (H v) < (H v).card - 1

private theorem minimize {α : Type} (f : α → ℕ) (p : α → Prop) (h : ∃ x, p x) :
    ∃ x, p x ∧ ∀ y, p y → f x ≤ f y := by
  have e : ∃ n, ∃ x, p x ∧ f x = n := by
    obtain ⟨x, hx⟩ := h
    exact ⟨f x, x, hx, rfl⟩
  obtain ⟨x, hx, he⟩ := Nat.find_spec e
  exact ⟨x, hx, fun y hy => he ▸ Nat.find_min' e ⟨y, hy, rfl⟩⟩

@[local simp] private theorem mem_close {H : Rows V} {X : Finset V} {w : V} :
    w ∈ close H X ↔ ∃ u ∈ X, w ∈ H u := mem_biUnion

private theorem close_mono {H K : Rows V} {X Y : Finset V} (h : H ≤ K) (hXY : X ⊆ Y) :
    close H X ⊆ close K Y :=
  (biUnion_mono fun u _ => h u).trans (biUnion_subset_biUnion_of_subset_left K hXY)

private theorem close_extensive {H : Rows V} (hH : Oriented H) (X : Finset V) :
    X ⊆ close H X := fun w hw => mem_close.mpr ⟨w, hw, hH.1 w⟩

private theorem close_union (H : Rows V) (X Y : Finset V) :
    close H (X ∪ Y) = close H X ∪ close H Y := union_biUnion

private theorem close_card {G : Rows V} (hg : Oriented G) (X : Finset V) :
    b G X + X.card = (close G X).card := card_sdiff_add_card_eq_card (close_extensive hg X)

private theorem submodular {G : Rows V} (hg : Oriented G) (X Y : Finset V) :
    b G (X ∩ Y) + b G (X ∪ Y) ≤ b G X + b G Y := by
  have hi : close G (X ∩ Y) ⊆ close G X ∩ close G Y := fun _ hw =>
    mem_inter.mpr ⟨close_mono le_rfl inter_subset_left hw,
      close_mono le_rfl inter_subset_right hw⟩
  have hc := card_le_card hi
  have hu := card_union_add_card_inter X Y
  have hv := card_union_add_card_inter (close G X) (close G Y)
  rw [← close_union, ← close_card hg (X ∪ Y), ← close_card hg X, ← close_card hg Y] at hv
  rw [← close_card hg (X ∩ Y)] at hc
  omega

private theorem sdiff_bound (P Q B C : Finset V) (h₁ : P \ Q ⊆ B) (h₂ : C ⊆ Q \ P) :
    P.card + C.card ≤ Q.card + B.card := by
  have hp := card_le_card h₁
  have hq := card_le_card h₂
  rw [card_sdiff, inter_comm Q P] at hp
  rw [card_sdiff] at hq
  have h : (P ∩ Q).card ≤ P.card := card_le_card inter_subset_left
  have h' : (P ∩ Q).card ≤ Q.card := card_le_card inter_subset_right
  omega

private noncomputable def size [Fintype V] (H : Rows V) : ℕ := ∑ v, (H v).card

private theorem contracts [Fintype V] {G : Rows V} (hg : Oriented G) (hb : bad G)
    (hm : ∀ (K : Rows V), Oriented K → bad K → size G ≤ size K)
    (X : Finset V) (hx : (bd G X).Nonempty) : b G (close G X) < b G X := by
  let E := bd G X
  let outside (T : Finset V) := close G T \ (X ∪ T)
  have hcover : close G X = X ∪ E := (union_sdiff_of_subset (close_extensive hg X)).symm
  obtain ⟨T, ⟨hTE, hT⟩, hmin⟩ :=
    minimize (fun S : Finset V => (E \ S).card)
      (fun S => S ⊆ E ∧ (S = ∅ ∨ (outside S).card < S.card))
      ⟨∅, empty_subset _, Or.inl rfl⟩
  have hfull : T = E := by
    by_contra hne
    let D := E \ T
    have hDT : ∀ {w}, w ∈ D → w ∈ E ∧ w ∉ T := fun hw => mem_sdiff.mp hw
    have hDX : ∀ {w}, w ∈ D → w ∉ X := fun hw => (mem_sdiff.mp (hDT hw).1).2
    have hD : D.Nonempty := sdiff_nonempty.mpr fun h => hne (Subset.antisymm hTE h)
    let K : Rows V := fun u => if u ∈ X then G u \ D else G u
    have hK : K ≤ G := by
      intro u w hw
      by_cases hu : u ∈ X <;> simp [K, hu] at hw
      · exact hw.1
      · exact hw
    have hKo : Oriented K := by
      refine ⟨fun u => ?_, fun {_ _} huv hvu => hg.2 (hK _ huv) (hK _ hvu)⟩
      by_cases hu : u ∈ X
      · simpa [K, hu] using mem_sdiff.mpr ⟨hg.1 u, fun hd => hDX hd hu⟩
      · simpa [K, hu] using hg.1 u
    have hsmall : size K < size G := by
      obtain ⟨w, hw⟩ := hD
      obtain ⟨u, hu, huw⟩ := mem_close.mp (mem_sdiff.mp (hDT hw).1).1
      apply sum_lt_sum (fun u _ => card_le_card (hK u))
      exact ⟨u, mem_univ _, card_lt_card ((ssubset_iff_of_subset (hK u)).mpr
        ⟨w, huw, by simp [K, hu, hw]⟩)⟩
    have hn : ¬ bad K := fun h => (not_le_of_gt hsmall) (hm K hKo h)
    obtain ⟨v, hv⟩ := not_forall.mp hn
    have hv' : (K v).card - 1 ≤ b K (K v) := Nat.le_of_not_lt hv
    have hvne : K v ≠ G v := by
      intro he
      rw [he] at hv'
      have hle : b K (G v) ≤ b G (G v) := card_le_card (fun _ hw =>
        mem_sdiff.mpr ⟨close_mono hK (Subset.refl _) (mem_sdiff.mp hw).1, (mem_sdiff.mp hw).2⟩)
      exact not_lt_of_ge (hv'.trans hle) (hb v)
    have hvX : v ∈ X := by
      by_contra h
      exact hvne (if_neg h)
    have hrow : ∀ {u}, u ∈ X → K u ⊆ X ∪ T := by
      intro u hu w hw
      have hs : w ∈ X ∪ E := hcover ▸ mem_close.mpr ⟨u, hu, hK u hw⟩
      simp only [K, hu, if_true, D, mem_sdiff] at hw
      simp only [mem_union] at hs ⊢
      clear * - hw hs
      tauto
    let L := G v ∩ D
    let J := L ∩ bd K (K v)
    let C := close G L \ (X ∪ T ∪ (close G T ∪ L))
    have hKL : K v = G v \ L := by
      ext w
      simp only [K, hvX, if_true, L, mem_sdiff, mem_inter]
      tauto
    have hL : L.Nonempty := nonempty_iff_ne_empty.mpr fun he => hvne (by simp [hKL, he])
    have hLE : L ⊆ E := fun _ hw => (hDT (mem_inter.mp hw).2).1
    have hTL : Disjoint T L := disjoint_left.mpr fun _ hw hl =>
      (hDT (mem_inter.mp hl).2).2 hw
    have hJ : J ⊆ outside T := by
      intro w hw
      obtain ⟨hl, hs⟩ := mem_inter.mp hw
      have hd := (mem_inter.mp hl).2
      have hnXT : w ∉ X ∪ T := fun h => (mem_union.mp h).elim (hDX hd) (hDT hd).2
      obtain ⟨u, hu, huw⟩ := mem_close.mp (mem_sdiff.mp hs).1
      have huT := (mem_union.mp (hrow hvX hu)).resolve_left (fun h => hnXT (hrow h huw))
      exact mem_sdiff.mpr ⟨mem_close.mpr ⟨u, huT, hK u huw⟩, hnXT⟩
    have hnew : bd K (K v) \ bd G (G v) ⊆ J := by
      intro w hw
      obtain ⟨hp, hq⟩ := mem_sdiff.mp hw
      have hc := close_mono hK (hK v) (mem_sdiff.mp hp).1
      have hG : w ∈ G v := by
        by_contra hn
        exact hq (mem_sdiff.mpr ⟨hc, hn⟩)
      have hN := (mem_sdiff.mp hp).2
      rw [hKL] at hN
      exact mem_inter.mpr ⟨by by_contra hl; exact hN (mem_sdiff.mpr ⟨hG, hl⟩), hp⟩
    have ho : G v ⊆ X ∪ T ∪ L := by
      intro w hw
      have h : w ∈ X ∪ E := hcover ▸ mem_close.mpr ⟨v, hvX, hw⟩
      simp only [L, D, mem_union, mem_inter, mem_sdiff] at h ⊢
      clear * - h hw
      tauto
    have hlost : C ⊆ bd G (G v) \ bd K (K v) := by
      intro w hw
      obtain ⟨hc, hn⟩ := mem_sdiff.mp hw
      obtain ⟨u, hu, huw⟩ := mem_close.mp hc
      refine mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨mem_close.mpr
        ⟨u, (mem_inter.mp hu).1, huw⟩, fun h => ?_⟩, fun h => ?_⟩
      · apply hn
        rcases mem_union.mp (ho h) with h | h
        · exact mem_union_left _ h
        · exact mem_union_right _ (mem_union_right _ h)
      · obtain ⟨a, ha, haw⟩ := mem_close.mp (mem_sdiff.mp h).1
        rcases mem_union.mp (hrow hvX ha) with haX | haT
        · exact hn (mem_union_left _ (hrow haX haw))
        · exact hn (mem_union_right _ (mem_union_left _
            (mem_close.mpr ⟨a, haT, hK a haw⟩)))
    have hdrop := card_sdiff_add_card_eq_card (show L ⊆ G v from inter_subset_left)
    rw [← hKL] at hdrop
    have hgain := sdiff_bound _ _ _ _ hnew hlost
    change b K (K v) + C.card ≤ b G (G v) + J.card at hgain
    have hcontr := hb v
    have hCL : C.card < L.card + J.card := by omega
    have hbound : (outside (T ∪ L)).card + J.card ≤ (outside T).card + C.card := by
      have hs : outside (T ∪ L) ⊆ (outside T \ J) ∪ C := by
        intro w hw
        have hj : w ∈ J → w ∈ L := fun hj => (mem_inter.mp hj).1
        simp only [outside, C, close_union, mem_sdiff, mem_union] at hw ⊢
        clear * - hw hj
        tauto
      have ha := card_le_card hs
      have hb := card_union_le (s := outside T \ J) (t := C)
      have hc := card_sdiff_add_card_eq_card hJ
      omega
    have hTle : (outside T).card ≤ T.card := by
      rcases hT with rfl | h
      · simp [outside, close]
      · exact Nat.le_of_lt h
    have htcard := card_union_of_disjoint hTL
    have hbetter : (outside (T ∪ L)).card < (T ∪ L).card := by omega
    have hsub : T ∪ L ⊆ E := union_subset hTE hLE
    have hm' := hmin (T ∪ L) ⟨hsub, Or.inr hbetter⟩
    have h₁ := card_sdiff_add_card_eq_card hTE
    have h₂ := card_sdiff_add_card_eq_card hsub
    have h₃ := card_pos.mpr hL
    omega
  have he : bd G (close G X) = outside E := by
    rw [bd, hcover, close_union, union_sdiff_distrib,
      sdiff_eq_empty_iff_subset.mpr hcover.le, empty_union]
  change (bd G (close G X)).card < E.card
  rw [he, ← hfull]
  exact hT.resolve_left (fun he => hx.ne_empty (hfull.symm.trans he))

private noncomputable def residual [Fintype V] (G H : Rows V) (v : V) : Finset V :=
  univ.filter fun w => ∀ u, v ∈ G u → w ∈ H u

@[local simp] private theorem mem_residual [Fintype V] {G H : Rows V} {v w : V} :
    w ∈ residual G H v ↔ ∀ u, v ∈ G u → w ∈ H u := by simp [residual]

private theorem residual_le [Fintype V] {G H : Rows V} (hg : Oriented G) :
    residual G H ≤ H := fun v _ hw => mem_residual.mp hw v (hg.1 v)

private theorem residual_mono [Fintype V] {G H K : Rows V} (h : H ≤ K) :
    residual G H ≤ residual G K :=
  fun _ _ hw => mem_residual.mpr fun u hu => h u (mem_residual.mp hw u hu)

private theorem residual_self [Fintype V] {G H : Rows V} (h : G ≤ H) (v : V) :
    v ∈ residual G H v := mem_residual.mpr fun u hu => h u hu

private theorem residual_close [Fintype V] {G H : Rows V}
    (hg : Oriented G) (hh : Oriented H) (h : G ≤ H) :
    Oriented (fun v => close G (residual G H v)) ∧ G ≤ (fun v => close G (residual G H v)) := by
  refine ⟨⟨fun v => close_extensive hg _ (residual_self h v), ?_⟩, ?_⟩
  · intro u v huv hvu
    obtain ⟨x, hxu, hxv⟩ := mem_close.mp huv
    obtain ⟨y, hyv, hyu⟩ := mem_close.mp hvu
    have he : x = y := hh.2 (mem_residual.mp hyv x hxv) (mem_residual.mp hxu y hyu)
    subst y
    have h₁ : u = x := hh.2 (residual_le hg u hxu) (h x hyu)
    have h₂ : v = x := hh.2 (residual_le hg v hyv) (h x hxv)
    exact h₁.trans h₂.symm
  · exact fun u w hw => mem_close.mpr ⟨u, residual_self h u, hw⟩

private noncomputable def total [Fintype V] (G H : Rows V) : ℕ := ∑ v, b G (H v)

private def saturated [Fintype V] (G H : Rows V) : Prop :=
  ∀ (K : Rows V), Oriented K → H ≤ K → total G H ≤ total G K

private theorem orient_between {H K L : Rows V} (hh : Oriented H) (hk : Oriented K)
    (hl : H ≤ L) (hu : L ≤ K) : Oriented L :=
  ⟨fun v => hl v (hh.1 v), fun {_ _} h₁ h₂ => hk.2 (hu _ h₁) (hu _ h₂)⟩

private theorem row_cmp [Fintype V] (G H K : Rows V) (v : V) (h : ∀ w, w ≠ v → H w = K w)
    (ht : total G H ≤ total G K) : b G (H v) ≤ b G (K v) := by
  have he : ∑ i ∈ univ.erase v, b G (H i) = ∑ i ∈ univ.erase v, b G (K i) :=
    sum_congr rfl fun w hw => congrArg (b G) (h w (mem_erase.mp hw).1)
  unfold total at ht
  rw [← sum_erase_add _ _ (mem_univ v), ← sum_erase_add _ _ (mem_univ v), he] at ht
  omega

private theorem sat_row [Fintype V] {G H : Rows V} (hh : Oriented H) (hs : saturated G H)
    (v : V) (W : Finset V) (hw : H v ⊆ W) (ha : ∀ w ∈ W, v ∈ H w → w = v) :
    b G (H v) ≤ b G W := by
  let K := Function.update H v W
  have hk : H ≤ K := le_update_self_iff.mpr hw
  have ho : Oriented K := by
    refine ⟨fun u => hk u (hh.1 u), ?_⟩
    have hm (x y : V) (h : y ∈ K x) : y ∈ H x ∨ x = v ∧ y ∈ W := by
      by_cases hx : x = v
      · exact Or.inr ⟨hx, by simpa [K, hx] using h⟩
      · exact Or.inl (by simpa [K, hx] using h)
    intro x y hxy hyx
    rcases hm x y hxy with h | ⟨rfl, h⟩ <;> rcases hm y x hyx with h' | ⟨rfl, h'⟩
    · exact hh.2 h h'
    · exact ha x h' h
    · exact (ha y h h').symm
    · rfl
  have hc := row_cmp G H K v (fun w hn => by simp [K, hn]) (hs K ho hk)
  simpa [K] using hc

private theorem sat_superrow [Fintype V] {G H K : Rows V} (hh : Oriented H)
    (hk : Oriented K) (hs : saturated G H) (h : H ≤ K) (v : V)
    (W : Finset V) (h₁ : H v ⊆ W) (h₂ : W ⊆ K v) : b G (H v) ≤ b G W :=
  sat_row hh hs v W h₁ fun w hw hv => (hk.2 (h₂ hw) (h w hv)).symm

private theorem tournament [Fintype V] {G H : Rows V} (hg : Oriented G) (hh : Oriented H)
    (h : G ≤ H) (ht : ∀ v w, w ∈ H v ∨ v ∈ H w) :
    total G (residual G H) ≤ total G H := by
  let P := univ.sigma (fun v => bd G (residual G H v))
  let Q := univ.sigma (fun v => bd G (H v))
  rw [total, total, ← show P.card = ∑ v, b G (residual G H v) from card_sigma _ _,
    ← show Q.card = ∑ v, b G (H v) from card_sigma _ _]
  change P.card ≤ Q.card
  let swap (p : Σ _ : V, V) : Σ _ : V, V := ⟨p.2, p.1⟩
  let f (p : Σ _ : V, V) := if p.1 ∈ H p.2 then p else swap p
  have hP : ∀ {p : Σ _ : V, V}, p ∈ P → p.2 ∈ bd G (residual G H p.1) :=
    fun hp => (mem_sigma.mp hp).2
  have hi : ∀ {p : Σ _ : V, V}, p ∈ P → p.2 ≠ p.1 := by
    intro p hp he
    apply (mem_sdiff.mp (hP hp)).2
    rw [he]
    exact residual_self h p.1
  refine card_le_card_of_injOn f ?_ ?_
  · rintro ⟨v, w⟩ hp
    have hp' : (⟨v,w⟩ : Σ _ : V, V) ∈ P := hp
    obtain ⟨hc, hn⟩ := mem_sdiff.mp (hP hp')
    have hwv : w ≠ v := hi hp'
    change f ⟨v,w⟩ ∈ Q
    by_cases ha : v ∈ H w
    · rw [show f ⟨v,w⟩ = ⟨v,w⟩ from if_pos ha]
      exact mem_sigma.mpr ⟨mem_univ _, mem_sdiff.mpr
        ⟨close_mono le_rfl (residual_le hg v) hc, fun hw => hwv (hh.2 hw ha).symm⟩⟩
    · rw [mem_residual] at hn
      obtain ⟨u, hu⟩ := not_forall.mp hn
      obtain ⟨hu, huw⟩ := Classical.not_imp.mp hu
      have hwu := (ht w u).resolve_right huw
      rw [show f ⟨v,w⟩ = ⟨w,v⟩ from if_neg ha]
      exact mem_sigma.mpr ⟨mem_univ _, mem_sdiff.mpr ⟨mem_close.mpr ⟨u, hwu, hu⟩, ha⟩⟩
  · intro p hp q hq he
    have hp' : p ∈ P := hp
    have hq' : q ∈ P := hq
    have cross : ∀ {a d : Σ _ : V, V}, a ∈ P → d ∈ P → a = swap d → False := by
      intro a d ha hd e
      subst a
      have h₁ := (mem_sdiff.mp (hP ha)).1
      have h₂ := (mem_sdiff.mp (hP hd)).1
      exact hi hd ((residual_close hg hh h).1.2 h₂ h₁).symm
    change f p = f q at he
    by_cases ha : p.1 ∈ H p.2 <;> by_cases hd : q.1 ∈ H q.2
    · simpa [f, ha, hd] using he
    · exact (cross hp' hq' (by simpa [f, ha, hd] using he)).elim
    · exact (cross hq' hp' (by simpa [f, ha, hd] using he.symm)).elim
    · have he' : swap p = swap q := by simpa [f, ha, hd] using he
      have invol : ∀ a, swap (swap a) = a := by rintro ⟨a, d⟩; rfl
      simpa only [invol] using congrArg swap he'

private noncomputable def missing [Fintype V] (H : Rows V) : Finset (V × V) :=
  univ.filter fun p => p.2 ∉ H p.1 ∧ p.1 ∉ H p.2

private theorem interval [Fintype V] {G H K : Rows V} (hg : Oriented G) (hh : Oriented H)
    (hk : Oriented K) (hs : saturated G H) (h : H ≤ K) (v : V) (T : Finset V)
    (h₁ : residual G H v ⊆ T) (h₂ : T ⊆ residual G K v) : b G (residual G H v) ≤ b G T := by
  obtain ⟨S, ⟨hs₁, hs₂, hs₃⟩, hm⟩ :=
    minimize card (fun S => residual G H v ⊆ S ∧ S ⊆ residual G K v ∧ b G S ≤ b G T)
      ⟨T, h₁, h₂, le_rfl⟩
  have he : S ⊆ residual G H v := by
    intro w hw
    apply mem_residual.mpr
    intro u hu
    have hi : residual G H v ⊆ S ∩ H u := fun _ ha =>
      mem_inter.mpr ⟨hs₁ ha, mem_residual.mp ha u hu⟩
    have hj : S ∪ H u ⊆ K u := union_subset
      (fun _ ha => mem_residual.mp (hs₂ ha) u hu) (h u)
    have hc := sat_superrow hh hk hs h u _ subset_union_right hj
    have hb := submodular hg S (H u)
    have ha : b G (S ∩ H u) ≤ b G T := by omega
    have hd := hm _ ⟨hi, Subset.trans inter_subset_left hs₂, ha⟩
    have eq : S ∩ H u = S := eq_of_subset_of_card_le inter_subset_left hd
    exact (mem_inter.mp (eq.symm ▸ hw)).2
  rwa [Subset.antisymm he hs₁] at hs₃

private theorem hall [Fintype V] {G H : Rows V} (hg : Oriented G) (hh : Oriented H)
    (hs : saturated G H) (z : V) (U : Finset V)
    (hU : ∀ u ∈ U, u ∉ H z ∧ z ∉ H u) :
    ∃ x : U → V, Function.Injective x ∧ ∀ u : U, x u ∈ G u \ close G (H z) := by
  let F : U → Finset V := fun u => G u \ close G (H z)
  apply (all_card_le_biUnion_card_iff_exists_injective F).mp
  intro s
  let S := s.image (fun u : U => (u : V))
  have hsU : S ⊆ U := fun _ hw => by
    obtain ⟨u, _, rfl⟩ := mem_image.mp hw
    exact u.property
  have hd : Disjoint (H z) S := disjoint_left.mpr fun _ hw ht => (hU _ (hsU ht)).1 hw
  have hc := sat_row hh hs z (H z ∪ S) subset_union_left
    (fun w hw hz => (mem_union.mp hw).elim
      (fun h => (hh.2 h hz).symm) (fun h => ((hU w (hsU h)).2 hz).elim))
  have hh₁ := close_card hg (H z)
  have hh₂ := close_card hg (H z ∪ S)
  have hd' := card_union_of_disjoint hd
  have hsub : close G (H z) ⊆ close G (H z ∪ S) := close_mono le_rfl subset_union_left
  have hcard := card_sdiff_add_card_eq_card hsub
  have he : close G (H z ∪ S) \ close G (H z) = s.biUnion F := by
    rw [close_union, union_sdiff_left]
    unfold close
    rw [image_biUnion]
    ext w
    simp only [mem_sdiff, mem_biUnion, F, mem_close]
    constructor
    · rintro ⟨⟨u, hu, hw⟩, hn⟩
      exact ⟨u, hu, hw, hn⟩
    · rintro ⟨u, hu, hw, hn⟩
      exact ⟨⟨u, hu, hw⟩, hn⟩
  have hm : S.card = s.card := card_image_of_injective _ Subtype.val_injective
  rw [he] at hcard
  omega

private theorem residual_bound [Fintype V] {G : Rows V} (hg : Oriented G)
    (H : Rows V) (hh : Oriented H) (h : G ≤ H) (hs : saturated G H) :
    total G (residual G H) ≤ total G H := by
  suffices main : ∀ (n : ℕ) (K : Rows V), (missing K).card = n → Oriented K → G ≤ K →
      saturated G K → total G (residual G K) ≤ total G K by
    exact main _ H rfl hh h hs
  clear H hh h hs
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro H hn hh h hs
    by_cases ht : ∀ v w, w ∈ H v ∨ v ∈ H w
    · exact tournament hg hh h ht
    obtain ⟨z, u₀, hz₀, hu₀⟩ : ∃ v w, w ∉ H v ∧ v ∉ H w := by
      simpa only [not_forall, not_or] using ht
    let U := univ.filter fun u => u ∉ H z ∧ z ∉ H u
    have hU : ∀ u, u ∈ U ↔ u ∉ H z ∧ z ∉ H u := by intro u; simp [U]
    have hU₀ : u₀ ∈ U := (hU _).mpr ⟨hz₀, hu₀⟩
    have hzU : z ∉ U := fun hz => ((hU _).mp hz).1 (hh.1 z)
    let family (K : Rows V) : Prop :=
      Oriented K ∧ H ≤ K ∧ (∀ u, u ∉ U → K u = H u) ∧ (∀ u ∈ U, z ∈ K u)
    have hex : ∃ K, family K := by
      let K : Rows V := fun v => if v ∈ U then insert z (H v) else H v
      have hm : ∀ v w, w ∈ K v ↔ w ∈ H v ∨ v ∈ U ∧ w = z := by
        intro v w
        by_cases hv : v ∈ U <;> simp [K, hv, or_comm]
      refine ⟨K, ⟨fun v => (hm _ _).mpr (Or.inl (hh.1 v)), ?_⟩,
        fun v _ hw => (hm _ _).mpr (Or.inl hw), fun v hv => if_neg hv,
        fun v hv => (hm _ _).mpr (Or.inr ⟨hv, rfl⟩)⟩
      intro v w hv hw
      rcases (hm _ _).mp hv with hv | ⟨hv, rfl⟩
      · rcases (hm _ _).mp hw with hw | ⟨hw, hvz⟩
        · exact hh.2 hv hw
        · exact (((hU _).mp hw).1 (hvz ▸ hv)).elim
      · rcases (hm _ _).mp hw with hw | ⟨hw, _⟩
        · exact (((hU _).mp hv).1 hw).elim
        · exact (hzU hw).elim
    obtain ⟨K, ⟨hk, hHK, hfixed, hnew⟩, hm⟩ := minimize (total G) family hex
    have hless : (missing K).card < n := by
      rw [← hn]
      apply card_lt_card
      refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
      · intro p hp
        simp only [missing, mem_filter, mem_univ, true_and] at hp ⊢
        exact ⟨fun ha => hp.1 (hHK _ ha), fun ha => hp.2 (hHK _ ha)⟩
      · intro he
        have hp : (z, u₀) ∈ missing H := by simp [missing, hz₀, hu₀]
        have hp' : (z, u₀) ∈ missing K := he.symm ▸ hp
        simp [missing, hnew u₀ hU₀] at hp'
    have hsatK : saturated G K := by
      intro L hl hKL
      have hHL : H ≤ L := le_trans hHK hKL
      let M : Rows V := fun v => if v ∈ U then L v else H v
      have ha : H ≤ M := by
        intro v
        by_cases hv : v ∈ U <;> simp [M, hv, hHL v]
      have hb : M ≤ L := by
        intro v
        by_cases hv : v ∈ U <;> simp [M, hv, hHL v]
      apply le_trans (hm M ⟨orient_between hh hl ha hb, ha, fun _ hv => if_neg hv,
        fun v hv => by simpa [M, hv] using hKL v (hnew v hv)⟩)
      apply sum_le_sum
      intro v _
      by_cases hv : v ∈ U
      · simp [M, hv]
      · simp only [M, if_neg hv]
        exact sat_superrow hh hl hs hHL v _ (hHL v) (Subset.refl _)
    have hrec := ih _ hless K rfl hk (le_trans h hHK) hsatK
    obtain ⟨x, hxi, hx⟩ := hall hg hh hs z U (fun u hu => (hU u).mp hu)
    let R := residual G H
    let R' := residual G K
    have hRR : R ≤ R' := residual_mono hHK
    have hI : ∀ v (W : Finset V), R v ⊆ W → W ⊆ R' v → b G (R v) ≤ b G W :=
      interval hg hh hk hs hHK
    have hcmp : ∀ u : U, b G (R (x u)) + b G (K u) ≤ b G (R' (x u)) + b G (H u) := by
      intro u
      obtain ⟨hxu, hxn⟩ := mem_sdiff.mp (hx u)
      have hzR : z ∈ R' (x u) := by
        apply mem_residual.mpr
        intro y hy
        have hyz : y ∉ H z := fun hyz => hxn (mem_close.mpr ⟨y, hyz, hy⟩)
        by_cases hz : z ∈ H y
        · exact hHK y hz
        · exact hnew y ((hU y).mpr ⟨hyz, hz⟩)
      have hr : R (x u) ⊆ H u := fun _ hw => mem_residual.mp hw u hxu
      have hr' : R' (x u) ⊆ K u := fun _ hw => mem_residual.mp hw u hxu
      have hb₁ := hI (x u) (R' (x u) ∩ H u)
        (fun _ hw => mem_inter.mpr ⟨hRR _ hw, hr hw⟩) inter_subset_left
      let L := Function.update K (u : V) (R' (x u) ∪ H u)
      have hle : H ≤ L := le_update_iff.mpr ⟨subset_union_right, fun v _ => hHK v⟩
      have hge : L ≤ K := by
        intro v
        by_cases hv : v = (u : V)
        · subst v
          simpa [L] using union_subset hr' (hHK u)
        · simp [L, hv]
      have hf : family L := by
        refine ⟨orient_between hh hk hle hge, hle, ?_, ?_⟩
        · intro v hv
          have hv' : v ≠ (u : V) := fun e => hv (e.symm ▸ u.property)
          simp [L, hv', hfixed v hv]
        · intro v hv
          by_cases hv' : v = (u : V)
          · subst v
            simpa [L] using mem_union_left (H u) hzR
          · simpa [L, hv'] using hnew v hv
      have hb₂ := row_cmp G K L u (fun v hv => by simp [L, hv]) (hm L hf)
      have hb₃ := submodular hg (R' (x u)) (H u)
      simp only [L, Function.update_self] at hb₂
      omega
    let dH (v : V) := b G (K v) - b G (H v)
    let dR (v : V) := b G (R' v) - b G (R v)
    have hH : ∀ v, b G (H v) + dH v = b G (K v) := by
      intro v
      have := sat_superrow hh hk hs hHK v (K v) (hHK v) (Subset.refl _)
      dsimp [dH]
      omega
    have hR : ∀ v, b G (R v) + dR v = b G (R' v) := by
      intro v
      have := hI v (R' v) (hRR v) (Subset.refl _)
      dsimp [dR]
      omega
    have htH : total G H + ∑ v, dH v = total G K := by
      unfold total
      rw [← sum_add_distrib]
      exact sum_congr rfl fun v _ => hH v
    have htR : total G R + ∑ v, dR v = total G R' := by
      unfold total
      rw [← sum_add_distrib]
      exact sum_congr rfl fun v _ => hR v
    have hsumH : ∑ v, dH v = ∑ u : U, dH u := by
      rw [← sum_subtype U (fun _ => Iff.rfl) dH]
      exact (sum_subset (subset_univ _) (fun v _ hv => by simp [dH, hfixed v hv])).symm
    have hsumR : ∑ u : U, dR (x u) ≤ ∑ v, dR v := by
      rw [← sum_image hxi.injOn]
      exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
    have hsum : ∑ u : U, dH u ≤ ∑ u : U, dR (x u) := by
      apply sum_le_sum
      intro u _
      have := hcmp u
      have := hH (u : V)
      have := hR (x u)
      omega
    change total G R' ≤ total G K at hrec
    change total G R ≤ total G H
    omega

private theorem restrict_bad {G : Rows V} (hg : Oriented G) (hb : bad G)
    (X : Finset V) (hs : close G X ⊆ X) :
    ∃ K : Rows X, Oriented K ∧ bad K := by
  let K : Rows X := fun v => (G v).subtype (· ∈ X)
  have hm (v w : X) : w ∈ K v ↔ (w : V) ∈ G v := mem_subtype
  have hrow (v : X) : G v ⊆ X := fun w hw => hs (mem_close.mpr ⟨v, v.property, hw⟩)
  have hcard (S : Finset V) (hS : S ⊆ X) : (S.subtype (· ∈ X)).card = S.card := by
    rw [← card_map (Function.Embedding.subtype (· ∈ X)), subtype_map, filter_eq_self.mpr hS]
  refine ⟨K, ⟨fun v => (hm v v).mpr (hg.1 v),
    fun {v w} hvw hwv => Subtype.ext (hg.2 ((hm v w).mp hvw) ((hm w v).mp hwv))⟩, ?_⟩
  intro v
  have hr : (K v).card = (G v).card := hcard (G v) (hrow v)
  have he : bd K (K v) = (bd G (G v)).subtype (· ∈ X) := by
    ext w
    simp only [bd, mem_subtype, mem_sdiff, mem_close, hm]
    constructor
    · rintro ⟨⟨u, hu, huw⟩, hn⟩
      exact ⟨⟨u, hu, huw⟩, hn⟩
    · rintro ⟨⟨u, hu, huw⟩, hn⟩
      exact ⟨⟨⟨u, hrow v hu⟩, hu, huw⟩, hn⟩
  have hs' : bd G (G v) ⊆ X :=
    fun _ hw => hs (close_mono le_rfl (hrow v) (mem_sdiff.mp hw).1)
  simpa only [b, he, hcard _ hs', hr] using hb (v : V)

private def counterexample (n : ℕ) : Prop :=
  ∃ (W : Type) (f : Fintype W) (_ : Nonempty W) (H : Rows W),
    @Fintype.card W f = n ∧ Oriented H ∧ bad H

private theorem no_bad [Fintype V] [Nonempty V] (A : Rows V) (ha : Oriented A) : ¬ bad A := by
  intro hb
  obtain ⟨n, ⟨W, f, c, A', hn, ha', hb'⟩, hnmin⟩ :=
    minimize id counterexample ⟨Fintype.card V, V, inferInstance, inferInstance, A, rfl, ha, hb⟩
  let _ : Fintype W := f
  let _ : Nonempty W := c
  obtain ⟨G, ⟨hg, hbG⟩, hm⟩ := minimize size
    (fun (G : Rows W) => Oriented G ∧ bad G) ⟨A', ha', hb'⟩
  have hcut (X : Finset W) (hx : X.Nonempty) (hx' : X ≠ univ) : (bd G X).Nonempty := by
    apply sdiff_nonempty.mpr
    intro hs
    obtain ⟨K, hk, hbK⟩ := restrict_bad hg hbG X hs
    have _ : Nonempty X := by
      obtain ⟨v, hv⟩ := hx
      exact ⟨⟨v, hv⟩⟩
    have hv := hnmin (Fintype.card X) ⟨X, inferInstance, inferInstance, K, rfl, hk, hbK⟩
    have hc : X.card < Fintype.card W := by
      rw [← card_univ]
      exact card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _, hx'⟩)
    have hn' : Fintype.card W = n := hn
    simp [Fintype.card_coe, ← hn', not_le_of_gt hc] at hv
  have hin (v : W) : ∃ u, u ≠ v ∧ v ∈ G u := by
    have hlt : ({v} : Finset W).card < (G v).card := by
      have := hbG v
      simp only [card_singleton]
      omega
    obtain ⟨w, _, hw⟩ := exists_mem_notMem_of_card_lt_card hlt
    let X := univ.erase v
    have hne : X ≠ univ := by
      intro he
      have hv : v ∈ X := he.symm ▸ mem_univ _
      simp [X] at hv
    obtain ⟨x, hx⟩ := hcut X ⟨w, by simpa [X] using hw⟩ hne
    obtain ⟨hc, hn⟩ := mem_sdiff.mp hx
    have hxv : x = v := by simpa [X] using hn
    obtain ⟨u, hu, hv⟩ := mem_close.mp hc
    exact ⟨u, (mem_erase.mp hu).1, hxv ▸ hv⟩
  obtain ⟨H, ⟨hh, hGH⟩, hmin⟩ := minimize (total G)
    (fun H => Oriented H ∧ G ≤ H) ⟨G, hg, le_rfl⟩
  have hs : saturated G H := fun K hk hHK => hmin K ⟨hk, le_trans hGH hHK⟩
  let R := residual G H
  let K := fun v => close G (R v)
  have hr : total G R ≤ total G H := residual_bound hg H hh hGH hs
  obtain ⟨hc, hle⟩ := residual_close hg hh hGH
  have hstrict (v : W) : b G (K v) < b G (R v) := by
    apply contracts hg hbG (fun K hk hbK => hm K ⟨hk, hbK⟩)
    apply hcut _ ⟨v, residual_self hGH v⟩
    obtain ⟨u, hu, huv⟩ := hin v
    intro he
    have huR : u ∈ residual G H v := he.symm ▸ mem_univ _
    exact hu (hh.2 (hGH _ huv) (residual_le hg v huR))
  have hsum : total G K < total G R := by
    apply sum_lt_sum (fun v _ => (hstrict v).le)
    obtain ⟨v⟩ := c
    exact ⟨v, mem_univ _, hstrict v⟩
  exact (not_lt_of_ge (hmin _ ⟨hc, hle⟩)) (hsum.trans_le hr)

open OMA.S_opg_seymours_second_neighbourhood_conjecture

theorem prove_snc (V : Type) [Fintype V] [DecidableEq V] [Nonempty V]
    (G : Digraph V) [DecidableRel G.Adj] (hg : IsOriented G) :
    ∃ v, outdegree G v ≤ secondOutdegree G v := by
  let H : Rows V := fun v => insert v (univ.filter fun w => G.Adj v w)
  have hmem (u v : V) : v ∈ H u ↔ v = u ∨ G.Adj u v := by simp [H]
  have ho : Oriented H := by
    refine ⟨fun v => (hmem v v).mpr (Or.inl rfl), ?_⟩
    intro u v huv hvu
    rcases (hmem u v).mp huv with h | h
    · exact h.symm
    · exact ((hmem v u).mp hvu).resolve_right (hg _ _ h)
  have h₁ (v : V) : outdegree G v = (H v).card - 1 := by
    have hn : v ∉ univ.filter (fun w => G.Adj v w) := by
      simpa using (fun h : G.Adj v v => hg v v h h)
    simp [H, outdegree, card_insert_of_notMem hn]
  have h₂ (v : V) : secondOutdegree G v = b H (H v) := by
    unfold secondOutdegree b
    apply congrArg Finset.card
    ext w
    simp only [bd, mem_sdiff, mem_close, hmem, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hn, hd, u, hu, huw⟩
      exact ⟨⟨u, Or.inr hu, Or.inr huw⟩, fun h => h.elim hn hd⟩
    · rintro ⟨⟨u, hu, huw⟩, hn⟩
      obtain ⟨hne, hnd⟩ := not_or.mp hn
      exact ⟨hne, hnd, u, hu.resolve_left (fun e => hn (e ▸ huw)),
        huw.resolve_left (fun e => hn (e.symm ▸ hu))⟩
  obtain ⟨v, hv⟩ := not_forall.mp (no_bad H ho)
  exact ⟨v, by rw [h₁, h₂]; exact Nat.le_of_not_lt hv⟩

end SNCProof

theorem OMA.solution : type_of% @OMA.S_opg_seymours_second_neighbourhood_conjecture.main := by
  exact SNCProof.prove_snc