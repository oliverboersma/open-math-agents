import FormalConjectures.Wikipedia.OhbaConjecture

section OhbaProof
open Finset Classical

namespace OhbaBP
variable {V : Type*} [DecidableEq V]

def Acc (q : V → ℕ) (A : Finset V) (L : V → Finset ℕ) (g : V → ℕ) : Prop :=
  (∀ v ∈ A, g v ∈ L v) ∧ ∀ u ∈ A, ∀ v ∈ A, q u ≠ q v → g u ≠ g v
def Colourable (q : V → ℕ) (W : Finset V) (L : V → Finset ℕ) : Prop := ∃ g, Acc q W L g
def nParts (q : V → ℕ) (W : Finset V) : ℕ := (W.image q).card
def partOf (q : V → ℕ) (W : Finset V) (v : V) : Finset V := W.filter fun u => q u = q v
def singletons (q : V → ℕ) (W : Finset V) : Finset V := W.filter fun v => (partOf q W v).card = 1
def colours (W : Finset V) (L : V → Finset ℕ) : Finset ℕ := W.biUnion L
def avail (W : Finset V) (L : V → Finset ℕ) (c : ℕ) : Finset V := W.filter fun v => c ∈ L v
def gam (W : Finset V) (L : V → Finset ℕ) : ℕ := W.card - (colours W L).card
def Frequent (q : V → ℕ) (W : Finset V) (k : ℕ) (L : V → Finset ℕ) (c : ℕ) : Prop :=
  k + 1 ≤ (avail W L c).card ∨ gam W L ≤ ((singletons q W).filter fun v => c ∈ L v).card
def NearAcc (q : V → ℕ) (W : Finset V) (k : ℕ) (L : V → Finset ℕ) (f : V → ℕ) : Prop :=
  (∀ v ∈ W, f v ∈ colours W L) ∧ (∀ u ∈ W, ∀ v ∈ W, q u ≠ q v → f u ≠ f v) ∧
  ∀ v ∈ W, f v ∈ L v ∨ (Frequent q W k L (f v) ∧ ∀ u ∈ W, f u = f v → u = v)
def Bad (q : V → ℕ) (W : Finset V) (k : ℕ) (L : V → Finset ℕ) : Prop :=
  (∀ v ∈ W, k ≤ (L v).card) ∧ ¬ Colourable q W L
def MaxBad (q : V → ℕ) (W : Finset V) (k : ℕ) (L : V → Finset ℕ) : Prop :=
  Bad q W k L ∧ ∀ v ∈ W, ∀ c ∈ colours W L, c ∉ L v →
    Colourable q W (Function.update L v (insert c (L v)))
def IH (q : V → ℕ) (n : ℕ) : Prop := ∀ (W : Finset V) (k : ℕ) (L : V → Finset ℕ),
  W.card < n → nParts q W ≤ k → W.card ≤ 2 * k + 1 → (∀ v ∈ W, k ≤ (L v).card) → Colourable q W L




theorem A_nParts_mono (q : V → ℕ) {W W' : Finset V} (h : W ⊆ W') : nParts q W ≤ nParts q W' :=
  card_le_card (image_subset_image h)

theorem A_greedy_aux (L : V → Finset ℕ) : ∀ W : Finset V, (∀ v ∈ W, W.card ≤ (L v).card) →
    ∃ g : V → ℕ, (∀ v ∈ W, g v ∈ L v) ∧ Set.InjOn g W := by
  intro W
  induction W using Finset.induction_on with
  | empty => intro _; exact ⟨fun _ => 0, by simp, by simp⟩
  | insert a W ha ih =>
    intro h
    have hcard : (insert a W).card = W.card + 1 := card_insert_of_notMem ha
    obtain ⟨g, hg1, hg2⟩ := ih (fun v hv => by have := h v (mem_insert_of_mem hv); omega)
    have hlt : (W.image g).card < (L a).card := by
      have := h a (mem_insert_self a W)
      exact lt_of_le_of_lt card_image_le (by omega)
    obtain ⟨c, hcL, hcn⟩ : ∃ c ∈ L a, c ∉ W.image g := by
      by_contra hno
      push_neg at hno
      exact absurd (card_le_card (show L a ⊆ W.image g from hno)) (by omega)
    refine ⟨Function.update g a c, ?_, ?_⟩
    · intro v hv
      rcases mem_insert.1 hv with rfl | hv
      · simpa using hcL
      · have : v ≠ a := fun e => ha (e ▸ hv)
        simpa [Function.update_of_ne this] using hg1 v hv
    · intro x hx y hy hxy
      simp only [Finset.coe_insert, Set.mem_insert_iff, mem_coe] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · rfl
      · have hya : y ≠ x := fun e => ha (e ▸ hy)
        simp [Function.update_of_ne hya] at hxy
        exact absurd (hxy ▸ mem_image_of_mem g hy) hcn
      · have hxa : x ≠ y := fun e => ha (e ▸ hx)
        simp [Function.update_of_ne hxa] at hxy
        exact absurd (hxy ▸ mem_image_of_mem g hx) hcn
      · have hxa : x ≠ a := fun e => ha (e ▸ hx)
        have hya : y ≠ a := fun e => ha (e ▸ hy)
        simp [Function.update_of_ne hxa, Function.update_of_ne hya] at hxy
        exact hg2 hx hy hxy

theorem P3_greedy {q : V → ℕ} {W : Finset V} {k : ℕ} {L : V → Finset ℕ} (hW : W.card ≤ k)
    (hL : ∀ v ∈ W, k ≤ (L v).card) : Colourable q W L := by
  obtain ⟨g, hg1, hg2⟩ := A_greedy_aux L W (fun v hv => le_trans hW (hL v hv))
  exact ⟨g, hg1, fun u hu v hv h => fun e => h (congrArg q (hg2 hu hv e))⟩

theorem A_refine_step (q : V → ℕ) (W : Finset V) (h : nParts q W < W.card) :
    ∃ q' : V → ℕ, nParts q' W = nParts q W + 1 ∧
      ∀ u ∈ W, ∀ v ∈ W, q u ≠ q v → q' u ≠ q' v := by
  have hn : (W.image q).card < W.card := h
  obtain ⟨u, hu, v, hv, huv, hq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hn
    (f := q) (fun x hx => mem_image_of_mem q hx)
  set N : ℕ := W.sum q + 1 with hN
  have hlt : ∀ x ∈ W, q x < N := fun x hx =>
    Nat.lt_succ_of_le (single_le_sum (f := q) (fun _ _ => Nat.zero_le _) hx)
  refine ⟨fun x => if x = u then N else q x, ?_, ?_⟩
  · have hv' : v ∈ W.erase u := mem_erase.2 ⟨huv.symm, hv⟩
    have himg : W.image (fun x => if x = u then N else q x) = insert N ((W.erase u).image q) := by
      ext n
      simp only [mem_image, mem_insert]
      constructor
      · rintro ⟨x, hx, rfl⟩
        by_cases hxu : x = u
        · left; simp [hxu]
        · right; exact ⟨x, mem_erase.2 ⟨hxu, hx⟩, by simp [hxu]⟩
      · rintro (rfl | ⟨x, hx, rfl⟩)
        · exact ⟨u, hu, by simp⟩
        · have := mem_erase.1 hx
          exact ⟨x, this.2, by simp [this.1]⟩
    have himg2 : W.image q = (W.erase u).image q := by
      ext n
      simp only [mem_image]
      constructor
      · rintro ⟨x, hx, rfl⟩
        by_cases hxu : x = u
        · exact ⟨v, hv', by rw [hxu]; exact hq.symm⟩
        · exact ⟨x, mem_erase.2 ⟨hxu, hx⟩, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, (mem_erase.1 hx).2, rfl⟩
    have hNn : N ∉ (W.erase u).image q := by
      intro hm
      obtain ⟨x, hx, hxe⟩ := mem_image.1 hm
      have := hlt x (mem_erase.1 hx).2
      omega
    unfold nParts
    rw [himg, card_insert_of_notMem hNn, himg2]
  · intro x hx y hy hxy
    by_cases hxu : x = u <;> by_cases hyu : y = u
    · exact absurd (hxu.trans hyu.symm) (fun e => hxy (by rw [e]))
    · have := hlt y hy
      simp [hxu, hyu]; omega
    · have := hlt x hx
      simp [hxu, hyu]; omega
    · simpa [hxu, hyu] using hxy

theorem P4_refine (W : Finset V) (k : ℕ) : ∀ (d : ℕ) (q : V → ℕ), nParts q W + d = k →
    k ≤ W.card → ∃ q' : V → ℕ, nParts q' W = k ∧
      ∀ u ∈ W, ∀ v ∈ W, q u ≠ q v → q' u ≠ q' v := by
  intro d
  induction d with
  | zero => intro q h _; exact ⟨q, by simpa using h, fun u _ v _ h => h⟩
  | succ d ih =>
    intro q h hk
    obtain ⟨q1, h1, h2⟩ := A_refine_step q W (by omega)
    obtain ⟨q', h3, h4⟩ := ih q1 (by omega) hk
    exact ⟨q', h3, fun u hu v hv huv => h4 u hu v hv (h2 u hu v hv huv)⟩

theorem P4_colourable {q q' : V → ℕ} {W : Finset V} {L : V → Finset ℕ}
    (h : ∀ u ∈ W, ∀ v ∈ W, q u ≠ q v → q' u ≠ q' v) (hc : Colourable q' W L) :
    Colourable q W L := by
  obtain ⟨g, hg1, hg2⟩ := hc
  exact ⟨g, hg1, fun u hu v hv huv => hg2 u hu v hv (h u hu v hv huv)⟩

section core
variable {q : V → ℕ} {W : Finset V} {k : ℕ} {L : V → Finset ℕ}


theorem ext_principle (hIH : IH q W.card) {A : Finset V} (hA : A.Nonempty) (hAW : A ⊆ W)
    {g : V → ℕ} (hg : Acc q A L g) {ℓ : ℕ} (hℓ : ℓ ≤ k)
    (h1 : (W \ A).card ≤ 2 * (k - ℓ) + 1) (h2 : nParts q (W \ A) ≤ k - ℓ)
    (h3 : ∀ v ∈ W \ A, k - ℓ ≤ (L v \ A.image g).card) : Colourable q W L := by
  have hlt : (W \ A).card < W.card := by
    obtain ⟨a, ha⟩ := hA
    exact card_lt_card ⟨sdiff_subset, fun h => (mem_sdiff.1 (h (hAW ha))).2 ha⟩
  obtain ⟨g', hg1, hg2⟩ := hIH (W \ A) (k - ℓ) (fun v => L v \ A.image g) hlt h2 h1 h3
  refine ⟨fun v => if v ∈ A then g v else g' v, ?_, ?_⟩
  · intro v hv
    by_cases hvA : v ∈ A
    · simpa [hvA] using hg.1 v hvA
    · have := hg1 v (mem_sdiff.2 ⟨hv, hvA⟩)
      simpa [hvA] using (mem_sdiff.1 this).1
  · intro u hu v hv huv
    by_cases huA : u ∈ A <;> by_cases hvA : v ∈ A
    · simpa [huA, hvA] using hg.2 u huA v hvA huv
    · have := (mem_sdiff.1 (hg1 v (mem_sdiff.2 ⟨hv, hvA⟩))).2
      simp only [huA, hvA, if_true, if_false]
      intro e
      exact this (by rw [← e]; exact mem_image_of_mem g huA)
    · have := (mem_sdiff.1 (hg1 u (mem_sdiff.2 ⟨hu, huA⟩))).2
      simp only [huA, hvA, if_true, if_false]
      intro e
      exact this (by rw [e]; exact mem_image_of_mem g hvA)
    · simpa [huA, hvA] using hg2 u (mem_sdiff.2 ⟨hu, huA⟩) v (mem_sdiff.2 ⟨hv, hvA⟩) huv

theorem A_ext_const (hIH : IH q W.card) (hLk : ∀ v ∈ W, k ≤ (L v).card)
    {A : Finset V} (hA : A.Nonempty) (hAW : A ⊆ W) {c : ℕ} (hcA : ∀ u ∈ A, c ∈ L u)
    (hAq : ∀ u ∈ A, ∀ w ∈ A, q u = q w) (hAc : ∀ w ∈ W \ A, ∀ a ∈ A, q w ≠ q a)
    (hk1 : 1 ≤ k) (hpk : nParts q W = k) (h1 : (W \ A).card ≤ 2 * (k - 1) + 1) :
    Colourable q W L := by
  obtain ⟨a, ha⟩ := hA
  refine ext_principle hIH ⟨a, ha⟩ hAW (g := fun _ => c) ⟨hcA, fun u hu w hw h => absurd (hAq u hu w hw) h⟩
    (ℓ := 1) hk1 h1 ?_ ?_
  · have hsub : (W \ A).image q ⊆ (W.image q).erase (q a) := by
      intro x hx
      obtain ⟨w, hw, rfl⟩ := mem_image.1 hx
      exact mem_erase.2 ⟨hAc w hw a ha, mem_image_of_mem q (mem_sdiff.1 hw).1⟩
    have := card_le_card hsub
    rw [card_erase_of_mem (mem_image_of_mem q (hAW ha))] at this
    unfold nParts
    unfold nParts at hpk
    omega
  · intro w hw
    rw [image_const ⟨a, ha⟩]
    have h := hLk w (mem_sdiff.1 hw).1
    have := pred_card_le_card_erase (s := L w) (a := c)
    rw [sdiff_singleton_eq_erase]
    omega

theorem part_inter_empty (hIH : IH q W.card) (hp : nParts q W = k) (hc : W.card ≤ 2 * k + 1)
    (hb : Bad q W k L) {v : V} (hv : v ∈ W) (h2 : 2 ≤ (partOf q W v).card) (c : ℕ) :
    ∃ u ∈ partOf q W v, c ∉ L u := by
  by_contra hcon
  push_neg at hcon
  have hvP : v ∈ partOf q W v := mem_filter.2 ⟨hv, rfl⟩
  have hPW : partOf q W v ⊆ W := filter_subset _ _
  have hk1 : 1 ≤ k := by
    rw [← hp]; exact card_pos.2 ⟨q v, mem_image_of_mem q hv⟩
  apply hb.2
  refine A_ext_const hIH hb.1 ⟨v, hvP⟩ hPW hcon ?_ ?_ hk1 hp ?_
  · intro u hu w hw
    exact ((mem_filter.1 hu).2).trans ((mem_filter.1 hw).2).symm
  · intro w hw a ha h
    have hw' := mem_sdiff.1 hw
    exact hw'.2 (mem_filter.2 ⟨hw'.1, h.trans (mem_filter.1 ha).2⟩)
  · rw [card_sdiff_of_subset hPW]
    omega

theorem A_hall_set (S : Finset ℕ) (t : ℕ → Finset V) (d : V)
    (hS : ∀ S' ⊆ S, S'.card ≤ (S'.biUnion t).card) :
    ∃ f : ℕ → V, Set.InjOn f S ∧ ∀ c ∈ S, f c ∈ t c := by
  have key := (Finset.all_card_le_biUnion_card_iff_exists_injective (fun c : S => t c)).1 (by
    intro s
    have h := hS (s.image Subtype.val) (by
      intro x hx
      obtain ⟨y, _, rfl⟩ := mem_image.1 hx
      exact y.2)
    rw [card_image_of_injective _ Subtype.val_injective] at h
    refine h.trans (card_le_card ?_)
    intro x hx
    simp only [mem_biUnion, mem_image] at hx ⊢
    obtain ⟨c, ⟨y, hy, rfl⟩, hx⟩ := hx
    exact ⟨y, hy, hx⟩)
  obtain ⟨f, hf1, hf2⟩ := key
  refine ⟨fun c => if h : c ∈ S then f ⟨c, h⟩ else d, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [mem_coe] at hx hy
    simp only [hx, hy, dif_pos] at hxy
    exact congrArg Subtype.val (hf1 hxy)
  · intro c hc
    simpa [hc] using hf2 ⟨c, hc⟩

theorem A_nonempty_of_bad (hb : Bad q W k L) : W.Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  apply hb.2
  subst h
  exact ⟨fun _ => 0, by simp, by simp⟩

theorem hall_saturates_colours (hIH : IH q W.card) (hp : nParts q W = k) (hc : W.card ≤ 2 * k + 1)
    (hb : Bad q W k L) :
    ∃ h : ℕ → V, (∀ c ∈ colours W L, h c ∈ W ∧ c ∈ L (h c)) ∧ Set.InjOn h (colours W L) := by
  obtain ⟨d, hd⟩ := A_nonempty_of_bad hb
  have hav : ∀ c, avail W L c ⊆ W := fun c => filter_subset _ _
  have hall : ∀ T ⊆ colours W L, T.card ≤ (T.biUnion (avail W L)).card := by
    by_contra hno
    push_neg at hno
    obtain ⟨T0, hT0, hT0c⟩ := hno
    have hne : ((colours W L).powerset.filter
        fun T => (T.biUnion (avail W L)).card < T.card).Nonempty :=
      ⟨T0, mem_filter.2 ⟨mem_powerset.2 hT0, hT0c⟩⟩
    obtain ⟨T, hTm, hTmin⟩ := exists_min_image _ card hne
    obtain ⟨hTsub, hTlt⟩ := mem_filter.1 hTm
    have hTC := mem_powerset.1 hTsub
    have hTne : T.Nonempty := by
      rw [← card_pos]; omega
    obtain ⟨c0, hc0⟩ := hTne
    have hc0C := hTC hc0
    obtain ⟨v0, hv0, hc0v⟩ := mem_biUnion.1 hc0C
    have hv0N : v0 ∈ T.biUnion (avail W L) :=
      mem_biUnion.2 ⟨c0, hc0, mem_filter.2 ⟨hv0, hc0v⟩⟩
    set S := T.erase c0 with hS
    have hScard : S.card + 1 = T.card := card_erase_add_one hc0
    have hSne : S.Nonempty := by
      rw [← card_pos]
      have := card_pos.2 ⟨v0, hv0N⟩
      omega
    have hSsubT : S ⊆ T := erase_subset _ _
    have hHallS : ∀ S' ⊆ S, S'.card ≤ (S'.biUnion (avail W L)).card := by
      intro S' hS'
      by_contra hlt
      push_neg at hlt
      have hmem : S' ∈ (colours W L).powerset.filter
          fun T => (T.biUnion (avail W L)).card < T.card :=
        mem_filter.2 ⟨mem_powerset.2 ((hS'.trans hSsubT).trans hTC), hlt⟩
      have := hTmin S' hmem
      have := card_le_card hS'
      omega
    obtain ⟨f, hf1, hf2⟩ := A_hall_set S (avail W L) d hHallS
    set A := S.image f with hA
    have hAcard : A.card = S.card := card_image_of_injOn hf1
    have hNS : S.biUnion (avail W L) ⊆ T.biUnion (avail W L) := biUnion_subset_biUnion_of_subset_left _ hSsubT
    have hAN : A ⊆ S.biUnion (avail W L) := by
      intro x hx
      obtain ⟨c, hc, rfl⟩ := mem_image.1 hx
      exact mem_biUnion.2 ⟨c, hc, hf2 c hc⟩
    have hNScard : (S.biUnion (avail W L)).card ≤ A.card := by
      have := card_le_card hNS
      omega
    have hAeq : A = S.biUnion (avail W L) := eq_of_subset_of_card_le hAN hNScard
    have hAW : A ⊆ W := fun x hx => by
      obtain ⟨c, _, hcx⟩ := mem_biUnion.1 (hAN hx)
      exact hav c hcx
    -- inverse colouring
    set g : V → ℕ := Function.invFunOn f (S : Set ℕ) with hg
    have hgex : ∀ x ∈ A, ∃ c ∈ (S : Set ℕ), f c = x := by
      intro x hx
      obtain ⟨c, hc, rfl⟩ := mem_image.1 hx
      exact ⟨c, hc, rfl⟩
    have hgS : ∀ x ∈ A, g x ∈ S := fun x hx => Function.invFunOn_mem (hgex x hx)
    have hgf : ∀ x ∈ A, f (g x) = x := fun x hx => Function.invFunOn_eq (hgex x hx)
    have hacc : Acc q A L g := by
      refine ⟨?_, ?_⟩
      · intro x hx
        have h1 := hf2 (g x) (hgS x hx)
        rw [hgf x hx] at h1
        exact (mem_filter.1 h1).2
      · intro x hx y hy hxy e
        apply hxy
        rw [← hgf x hx, ← hgf y hy, e]
    apply hb.2
    refine ext_principle hIH (hSne.image f) hAW hacc (k := k) (ℓ := 0) (Nat.zero_le _) ?_ ?_ ?_
    · simp only [Nat.sub_zero]
      exact (card_le_card sdiff_subset).trans hc
    · simp only [Nat.sub_zero]
      rw [← hp]
      exact A_nParts_mono q sdiff_subset
    · intro w hw
      simp only [Nat.sub_zero]
      have hwW := (mem_sdiff.1 hw).1
      have hwA := (mem_sdiff.1 hw).2
      have hdis : Disjoint (L w) (A.image g) := by
        rw [disjoint_left]
        intro c hcw hcg
        obtain ⟨x, hx, rfl⟩ := mem_image.1 hcg
        apply hwA
        have hh : w ∈ S.biUnion (avail W L) :=
          mem_biUnion.2 ⟨g x, hgS x hx, mem_filter.2 ⟨hwW, hcw⟩⟩
        rw [← hAeq] at hh
        exact hh
      rw [sdiff_eq_self_of_disjoint hdis]
      exact hb.1 w hwW
  obtain ⟨f, hf1, hf2⟩ := A_hall_set (colours W L) (avail W L) d hall
  exact ⟨f, fun c hc => ⟨hav c (hf2 c hc) , (mem_filter.1 (hf2 c hc)).2⟩, hf1⟩

theorem colours_lt_card (hIH : IH q W.card) (hp : nParts q W = k) (hc : W.card ≤ 2 * k + 1)
    (hb : Bad q W k L) : (colours W L).card < W.card := by
  obtain ⟨h, hh1, hh2⟩ := hall_saturates_colours hIH hp hc hb
  have hsub : (colours W L).image h ⊆ W := image_subset_iff.2 fun c hc' => (hh1 c hc').1
  have himg := card_image_of_injOn hh2
  have hle : (colours W L).card ≤ W.card := by
    rw [← himg]; exact card_le_card hsub
  by_contra hlt
  have heq : (colours W L).image h = W :=
    eq_of_subset_of_card_le hsub (by rw [himg]; omega)
  apply hb.2
  have hex : ∀ v ∈ W, ∃ c ∈ (colours W L : Set ℕ), h c = v := by
    intro v hv
    rw [← heq] at hv
    obtain ⟨c, hc', rfl⟩ := mem_image.1 hv
    exact ⟨c, hc', rfl⟩
  refine ⟨Function.invFunOn h (colours W L : Set ℕ), ?_, ?_⟩
  · intro v hv
    have h1 := (hh1 _ (Function.invFunOn_mem (hex v hv))).2
    rwa [Function.invFunOn_eq (hex v hv)] at h1
  · intro u hu v hv huv e
    have := congrArg h e
    rw [Function.invFunOn_eq (hex u hu), Function.invFunOn_eq (hex v hv)] at this
    exact huv (by rw [this])

theorem A_disjoint_lists (hIH : IH q W.card) (hp : nParts q W = k) (hc : W.card ≤ 2 * k + 1)
    (hb : Bad q W k L) {u v : V} (hu : u ∈ W) (hv : v ∈ W) (hd : Disjoint (L u) (L v)) :
    L u ∪ L v = colours W L ∧ (colours W L).card = 2 * k := by
  have hlt := colours_lt_card hIH hp hc hb
  have hsub : L u ∪ L v ⊆ colours W L := union_subset
    (fun x hx => mem_biUnion.2 ⟨u, hu, hx⟩) (fun x hx => mem_biUnion.2 ⟨v, hv, hx⟩)
  have hcard : (L u ∪ L v).card = (L u).card + (L v).card := card_union_of_disjoint hd
  have h1 := hb.1 u hu
  have h2 := hb.1 v hv
  have hle := card_le_card hsub
  exact ⟨eq_of_subset_of_card_le hsub (by omega), by omega⟩

theorem A_three_mul_le (hP : ∀ v ∈ W, 3 ≤ (partOf q W v).card) : 3 * nParts q W ≤ W.card := by
  rw [card_eq_sum_card_image q W]
  have : (W.image q).card • 3 ≤ ∑ b ∈ W.image q, (W.filter fun a => q a = b).card := by
    apply card_nsmul_le_sum
    intro b hb
    obtain ⟨v, hv, rfl⟩ := mem_image.1 hb
    exact hP v hv
  unfold nParts
  simp only [smul_eq_mul] at this
  omega

theorem card_eq_two_mul_add_one (hIH : IH q W.card) (hp : nParts q W = k) (hc : W.card ≤ 2 * k + 1)
    (hb : Bad q W k L) : W.card = 2 * k + 1 := by
  by_contra hne
  have hle : W.card ≤ 2 * k := by omega
  obtain ⟨v0, hv0⟩ := A_nonempty_of_bad hb
  have hk1 : 1 ≤ k := by
    rw [← hp]; exact card_pos.2 ⟨q v0, mem_image_of_mem q hv0⟩
  by_cases hex : ∃ v ∈ W, (partOf q W v).card = 1 ∨ (partOf q W v).card = 2
  · obtain ⟨v, hv, hcase⟩ := hex
    have hvP : v ∈ partOf q W v := mem_filter.2 ⟨hv, rfl⟩
    rcases hcase with h1 | h2
    · obtain ⟨a, ha⟩ := card_eq_one.1 h1
      have hva : v = a := by rw [ha] at hvP; exact mem_singleton.1 hvP
      subst hva
      obtain ⟨c, hcv⟩ : (L v).Nonempty := card_pos.1 (by have := hb.1 v hv; omega)
      apply hb.2
      have hvW : ({v} : Finset V) ⊆ W := singleton_subset_iff.2 hv
      refine A_ext_const hIH hb.1 (A := {v}) ⟨v, mem_singleton_self v⟩ hvW (c := c) ?_ ?_ ?_ hk1 hp ?_
      · intro u hu; rw [mem_singleton.1 hu]; exact hcv
      · intro u hu w hw; rw [mem_singleton.1 hu, mem_singleton.1 hw]
      · intro w hw a ha' hq
        have hw' := mem_sdiff.1 hw
        rw [mem_singleton.1 ha'] at hq
        have : w ∈ partOf q W v := mem_filter.2 ⟨hw'.1, hq⟩
        rw [ha] at this
        exact hw'.2 (mem_singleton.1 this ▸ mem_singleton_self _)
      · rw [card_sdiff_of_subset hvW, card_singleton]
        omega
    · obtain ⟨x, y, hxy, hxyP⟩ := card_eq_two.1 h2
      have hx : x ∈ partOf q W v := by rw [hxyP]; simp
      have hy : y ∈ partOf q W v := by rw [hxyP]; simp
      have hxW : x ∈ W := (mem_filter.1 hx).1
      have hyW : y ∈ W := (mem_filter.1 hy).1
      have hd : Disjoint (L x) (L y) := by
        rw [disjoint_left]
        intro c hcx hcy
        obtain ⟨u, hu, hcu⟩ := part_inter_empty hIH hp hc hb hv (by omega) c
        rw [hxyP] at hu
        rcases mem_insert.1 hu with rfl | hu
        · exact hcu hcx
        · rw [mem_singleton.1 hu] at hcu; exact hcu hcy
      have := (A_disjoint_lists hIH hp hc hb hxW hyW hd).2
      have := colours_lt_card hIH hp hc hb
      omega
  · push_neg at hex
    have h3 : ∀ v ∈ W, 3 ≤ (partOf q W v).card := by
      intro v hv
      have hvP : v ∈ partOf q W v := mem_filter.2 ⟨hv, rfl⟩
      have := card_pos.2 ⟨v, hvP⟩
      have h1 := (hex v hv).1
      have h2 := (hex v hv).2
      omega
    have := A_three_mul_le h3
    omega

theorem exists_maxBad (hIH : IH q W.card) (hp : nParts q W = k) (hc : W.card ≤ 2 * k + 1)
    (hb : Bad q W k L) : ∃ L' : V → Finset ℕ, (∀ v ∈ W, L v ⊆ L' v) ∧ MaxBad q W k L' := by
  let T : Set ℕ := {n | ∃ L' : V → Finset ℕ, (∀ v ∈ W, L v ⊆ L' v) ∧ Bad q W k L' ∧
    ∑ v ∈ W, (L' v).card = n}
  have hTne : T.Nonempty := ⟨_, L, fun v _ => subset_rfl, hb, rfl⟩
  have hTbdd : BddAbove T := by
    refine ⟨W.card * W.card, ?_⟩
    rintro n ⟨L', _, hb', rfl⟩
    have hlt := colours_lt_card hIH hp hc hb'
    have : ∀ v ∈ W, (L' v).card ≤ W.card := by
      intro v hv
      exact (card_le_card (fun x hx => mem_biUnion.2 ⟨v, hv, hx⟩ : L' v ⊆ colours W L')).trans hlt.le
    calc ∑ v ∈ W, (L' v).card ≤ ∑ v ∈ W, W.card := sum_le_sum this
      _ = W.card * W.card := by simp
  obtain ⟨L', hL1, hL2, hL3⟩ := Nat.sSup_mem hTne hTbdd
  refine ⟨L', hL1, hL2, ?_⟩
  intro v hv c hcC hcv
  by_contra hnc
  have hbad : Bad q W k (Function.update L' v (insert c (L' v))) := by
    refine ⟨?_, hnc⟩
    intro w hw
    by_cases hwv : w = v
    · subst hwv
      simp only [Function.update_self]
      exact (hL2.1 w hw).trans (card_le_card (subset_insert _ _))
    · simp only [Function.update_of_ne hwv]
      exact hL2.1 w hw
  have hmem : ∑ w ∈ W, ((Function.update L' v (insert c (L' v))) w).card ∈ T := by
    refine ⟨_, ?_, hbad, rfl⟩
    intro w hw
    by_cases hwv : w = v
    · subst hwv
      simp only [Function.update_self]
      exact (hL1 w hw).trans (subset_insert _ _)
    · simp only [Function.update_of_ne hwv]
      exact hL1 w hw
  have hle := le_csSup hTbdd hmem
  have hlt : ∑ w ∈ W, (L' w).card < ∑ w ∈ W, ((Function.update L' v (insert c (L' v))) w).card := by
    apply sum_lt_sum
    · intro w hw
      by_cases hwv : w = v
      · subst hwv
        simp only [Function.update_self]
        exact card_le_card (subset_insert _ _)
      · simp only [Function.update_of_ne hwv]
        exact le_rfl
    · refine ⟨v, hv, ?_⟩
      simp only [Function.update_self]
      exact card_lt_card (ssubset_insert hcv)
  omega

theorem B_hall_def {ι : Type*} [DecidableEq ι] (I : Finset ι) (t : ι → Finset ℕ) :
    ∃ S ⊆ I, ∀ T ⊆ I, ((T.card : ℤ) - (T.biUnion t).card) ≤ (S.card : ℤ) - (S.biUnion t).card := by
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image I.powerset
    (fun T => ((T.card : ℤ) - (T.biUnion t).card)) ⟨∅, by simp⟩
  exact ⟨S, mem_powerset.1 hS, fun T hT => hmax T (mem_powerset.2 hT)⟩

theorem B_hall_match {ι : Type*} [DecidableEq ι] (I S : Finset ι) (t : ι → Finset ℕ) (hSI : S ⊆ I)
    (hmax : ∀ T ⊆ I, ((T.card : ℤ) - (T.biUnion t).card) ≤ (S.card : ℤ) - (S.biUnion t).card) :
    ∃ f : ι → ℕ, Set.InjOn f ↑(I \ S) ∧ ∀ i ∈ I \ S, f i ∈ t i ∧ f i ∉ S.biUnion t := by
  let t' : (I \ S : Finset ι) → Finset ℕ := fun i => t i \ S.biUnion t
  have key : ∀ s : Finset (I \ S : Finset ι), s.card ≤ (s.biUnion t').card := by
    intro s
    set T : Finset ι := s.map (Function.Embedding.subtype _) with hT
    have hTsub : T ⊆ I \ S := by
      intro x hx
      simp only [hT, mem_map, Function.Embedding.coe_subtype] at hx
      obtain ⟨y, _, rfl⟩ := hx
      exact y.2
    have hTI : T ⊆ I := hTsub.trans sdiff_subset
    have hdisj : Disjoint S T := by
      rw [disjoint_left]
      intro x hxS hxT
      exact (mem_sdiff.1 (hTsub hxT)).2 hxS
    have h1 := hmax (S ∪ T) (union_subset hSI hTI)
    have hc1 : (S ∪ T).card = S.card + T.card := card_union_of_disjoint hdisj
    have hbu : (S ∪ T).biUnion t = S.biUnion t ∪ T.biUnion t := union_biUnion
    have hc2 : ((S ∪ T).biUnion t).card = (S.biUnion t).card + (T.biUnion t \ S.biUnion t).card := by
      rw [hbu, ← union_sdiff_self_eq_union, card_union_of_disjoint disjoint_sdiff]
    have hb : s.biUnion t' = T.biUnion t \ S.biUnion t := by
      ext c
      simp only [hT, t', mem_biUnion, mem_sdiff, mem_map, Function.Embedding.coe_subtype]
      constructor
      · rintro ⟨a, ha, hc, hn⟩
        exact ⟨⟨a.1, ⟨a, ha, rfl⟩, hc⟩, hn⟩
      · rintro ⟨⟨x, ⟨a, ha, rfl⟩, hc⟩, hn⟩
        exact ⟨a, ha, hc, hn⟩
    have hsT : s.card = T.card := by simp [hT]
    rw [hb, hsT]
    have : (T.card : ℤ) ≤ (T.biUnion t \ S.biUnion t).card := by
      rw [hc1, hc2] at h1; push_cast at h1; linarith
    exact_mod_cast this
  obtain ⟨f', hinj, hf'⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t').1 key
  refine ⟨fun i => if h : i ∈ I \ S then f' ⟨i, h⟩ else 0, ?_, ?_⟩
  · intro x hx y hy hxy
    have hx' : x ∈ I \ S := hx
    have hy' : y ∈ I \ S := hy
    simp only [hx', hy', dite_true] at hxy
    exact congrArg Subtype.val (hinj hxy)
  · intro i hi
    simp only [hi, dite_true]
    have := mem_sdiff.1 (hf' ⟨i, hi⟩)
    exact this

theorem B_singleton_eq {v u : V} (hv : v ∈ singletons q W) (hu : u ∈ W) (hq : q u = q v) : u = v := by
  have h1 := mem_filter.1 hv
  obtain ⟨a, ha⟩ := card_eq_one.1 h1.2
  have hv' : v ∈ partOf q W v := mem_filter.2 ⟨h1.1, rfl⟩
  have hu' : u ∈ partOf q W v := mem_filter.2 ⟨hu, hq⟩
  rw [ha, mem_singleton] at hv' hu'
  rw [hu', hv']

theorem surj_modif (hIH : IH q W.card) (hp : nParts q W = k) (hc : W.card ≤ 2 * k + 1)
    (hb : Bad q W k L) (f : V → ℕ) (hf : ∀ v ∈ W, f v ∈ colours W L)
    (hfp : ∀ u ∈ W, ∀ v ∈ W, q u ≠ q v → f u ≠ f v) :
    ∃ g : V → ℕ, (∀ v ∈ W, g v ∈ colours W L) ∧ (∀ u ∈ W, ∀ v ∈ W, q u ≠ q v → g u ≠ g v) ∧
      colours W L ⊆ W.image g ∧
      ∀ v ∈ W, g v ∈ L v ∨ (g v = f v ∧ ∀ u ∈ W, g u = g v → f u = f v) := by
  obtain ⟨h, hh1, hh2⟩ := hall_saturates_colours hIH hp hc hb
  obtain ⟨P, hP⟩ : ∃ P : (V → ℕ) → Prop, ∀ g, P g ↔ ((∀ v ∈ W, g v ∈ colours W L) ∧
      (∀ u ∈ W, ∀ v ∈ W, q u ≠ q v → g u ≠ g v) ∧
      ∀ v ∈ W, g v ∈ L v ∨ (g v = f v ∧ ∀ u ∈ W, g u = g v → f u = f v)) :=
    ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨agr, hagr⟩ : ∃ agr : (V → ℕ) → ℕ, ∀ g, agr g = ((colours W L).filter fun c => g (h c) = c).card :=
    ⟨_, fun _ => rfl⟩
  have hPf : P f := by
    rw [hP]
    exact ⟨hf, hfp, fun v hv => Or.inr ⟨rfl, fun u _ hu => by rw [hu]⟩⟩
  have key : ∀ n : ℕ, ∀ g : V → ℕ, P g → (colours W L).card - agr g = n →
      ∃ g, P g ∧ colours W L ⊆ W.image g := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro g hg hn
      by_cases hsub : colours W L ⊆ W.image g
      · exact ⟨g, hg, hsub⟩
      · obtain ⟨c', hc'C, hc'n⟩ := not_subset.1 hsub
        have hc'n' : ∀ v ∈ W, g v ≠ c' := fun v hv e => hc'n (mem_image.2 ⟨v, hv, e⟩)
        obtain ⟨hg1, hg2, hg3⟩ := (hP g).1 hg
        have hw0 : h c' ∈ W := (hh1 c' hc'C).1
        have hw0L : c' ∈ L (h c') := (hh1 c' hc'C).2
        set g' := Function.update g (h c') c' with hg'
        have hg'w : ∀ v, v ≠ h c' → g' v = g v := fun v hv => Function.update_of_ne hv _ _
        have hg'0 : g' (h c') = c' := Function.update_self _ _ _
        have hPg' : P g' := by
          rw [hP]
          refine ⟨?_, ?_, ?_⟩
          · intro v hv
            by_cases hv0 : v = h c'
            · rw [hv0, hg'0]; exact hc'C
            · rw [hg'w v hv0]; exact hg1 v hv
          · intro u hu v hv huv
            by_cases hu0 : u = h c'
            · have hv0 : v ≠ h c' := fun e => huv (by rw [hu0, e])
              rw [hu0, hg'0, hg'w v hv0]; exact fun e => hc'n' v hv e.symm
            · by_cases hv0 : v = h c'
              · rw [hv0, hg'0, hg'w u hu0]; exact hc'n' u hu
              · rw [hg'w u hu0, hg'w v hv0]; exact hg2 u hu v hv huv
          · intro v hv
            by_cases hv0 : v = h c'
            · left; rw [hv0, hg'0]; exact hw0L
            · rw [hg'w v hv0]
              rcases hg3 v hv with h1 | ⟨h1, h2⟩
              · left; exact h1
              · right
                refine ⟨h1, fun u hu hgu => ?_⟩
                by_cases hu0 : u = h c'
                · rw [hu0, hg'0] at hgu
                  exact absurd hgu.symm (hc'n' v hv)
                · rw [hg'w u hu0] at hgu
                  exact h2 u hu hgu
        have hlt : agr g < agr g' := by
          rw [hagr, hagr]
          apply card_lt_card
          rw [ssubset_iff_of_subset]
          · refine ⟨c', ?_, ?_⟩
            · exact mem_filter.2 ⟨hc'C, by rw [hg'0]⟩
            · intro hmem
              exact hc'n' (h c') hw0 (mem_filter.1 hmem).2
          · intro c hcm
            obtain ⟨hcC, hcg⟩ := mem_filter.1 hcm
            refine mem_filter.2 ⟨hcC, ?_⟩
            have hne : h c ≠ h c' := by
              intro e
              have : c = c' := hh2 hcC hc'C e
              exact hc'n' (h c) (hh1 c hcC).1 (hcg.trans this)
            rw [hg'w _ hne]; exact hcg
        have hle : agr g' ≤ (colours W L).card := by
          rw [hagr]; exact card_le_card (filter_subset _ _)
        exact ih ((colours W L).card - agr g') (by omega) g' hPg' rfl
  obtain ⟨g, hg, hsub⟩ := key _ f hPf rfl
  obtain ⟨h1, h2, h3⟩ := (hP g).1 hg
  exact ⟨g, h1, h2, hsub, h3⟩

def B_t (W : Finset V) (L : V → Finset ℕ) (g : V → ℕ) (e : ℕ) : Finset ℕ :=
  (colours W L).filter fun x => ∀ v ∈ W, g v = e → x ∈ L v

theorem B_claim24 (hIH : IH q W.card) (hp : nParts q W = k) (hc : W.card ≤ 2 * k + 1)
    (hb : Bad q W k L) {g : V → ℕ}
    (hg1 : ∀ v ∈ W, g v ∈ colours W L)
    (hg2 : ∀ u ∈ W, ∀ v ∈ W, q u ≠ q v → g u ≠ g v)
    (hg3 : colours W L ⊆ W.image g)
    (hP : ∀ v ∈ W, g v ∈ L v ∨ ∀ u ∈ W, g u = g v → u = v)
    {S : Finset ℕ} (hS : S ⊆ colours W L) {m : ℕ → ℕ}
    (hm1 : Set.InjOn m ↑(colours W L \ S))
    (hm2 : ∀ d ∈ colours W L \ S, (∀ v ∈ W, g v = d → m d ∈ L v) ∧
      m d ∉ S.biUnion (B_t W L g))
    (hs : gam W L ≤ ((singletons q W).filter fun x => g x ∉ S).card) :
    Colourable q W L := by
  have hW := card_eq_two_mul_add_one hIH hp hc hb
  have hlt := colours_lt_card hIH hp hc hb
  have hγ : 1 ≤ gam W L := by unfold gam; omega
  have hLC : ∀ v ∈ W, L v ⊆ colours W L := fun v hv => subset_biUnion_of_mem L hv
  obtain ⟨big, hbig⟩ : ∃ big : V → Prop, ∀ v, big v ↔ ∃ u ∈ W, u ≠ v ∧ g u = g v := ⟨_, fun _ => Iff.rfl⟩
  have hbigL : ∀ v ∈ W, big v → g v ∈ L v := by
    intro v hv hbv
    rcases hP v hv with h | h
    · exact h
    · obtain ⟨u, hu, hne, hgu⟩ := (hbig v).1 hbv
      exact absurd (h u hu hgu) hne
  have hbigt : ∀ v ∈ W, big v → g v ∈ B_t W L g (g v) := by
    intro v hv hbv
    refine mem_filter.2 ⟨hg1 v hv, fun w hw hgw => ?_⟩
    have : big w := by
      rw [hbig]
      by_cases hwv : w = v
      · rw [hwv]; exact (hbig v).1 hbv
      · exact ⟨v, hv, fun e => hwv e.symm, hgw.symm⟩
    rw [← hgw]; exact hbigL w hw this
  set A := W.filter (fun v => g v ∉ S ∨ big v) with hA
  set Bg := W.filter big with hBg
  set ℓ := (Bg.image g).card with hℓ
  set X := (singletons q W).filter (fun x => g x ∉ S) with hX
  set gn : V → ℕ := fun v => if g v ∈ S then g v else m (g v) with hgn
  have hAW : A ⊆ W := filter_subset _ _
  have hXA : X ⊆ A := by
    intro x hx
    have := mem_filter.1 hx
    exact mem_filter.2 ⟨(mem_filter.1 this.1).1, Or.inl this.2⟩
  have hBgA : Bg ⊆ A := by
    intro x hx
    have := mem_filter.1 hx
    exact mem_filter.2 ⟨this.1, Or.inr this.2⟩
  have hXk : X.card ≤ k := by
    rw [← hp]
    apply card_le_card_of_injOn q
    · intro x hx
      exact mem_image_of_mem q (mem_filter.1 (mem_filter.1 hx).1).1
    · intro x hx y hy hxy
      exact (B_singleton_eq (mem_filter.1 hx).1 (mem_filter.1 (mem_filter.1 hy).1).1 hxy.symm).symm
  -- ℓ ≤ γ
  have hD : Bg.image g ⊆ colours W L := by
    intro d hd
    obtain ⟨v, hv, rfl⟩ := mem_image.1 hd
    exact hg1 v (mem_filter.1 hv).1
  have hcls1 : ∀ d ∈ colours W L, 1 ≤ (W.filter fun v => g v = d).card := by
    intro d hd
    obtain ⟨v, hv, hgv⟩ := mem_image.1 (hg3 hd)
    exact card_pos.2 ⟨v, mem_filter.2 ⟨hv, hgv⟩⟩
  have hcls2 : ∀ d ∈ Bg.image g, 2 ≤ (W.filter fun v => g v = d).card := by
    intro d hd
    obtain ⟨v, hv, rfl⟩ := mem_image.1 hd
    obtain ⟨hvW, hvb⟩ := mem_filter.1 hv
    obtain ⟨u, hu, hne, hgu⟩ := (hbig v).1 hvb
    have : 1 < (W.filter fun w => g w = g v).card :=
      one_lt_card.2 ⟨u, mem_filter.2 ⟨hu, hgu⟩, v, mem_filter.2 ⟨hvW, rfl⟩, hne⟩
    omega
  have hℓγ : ℓ ≤ gam W L := by
    have hsum := card_eq_sum_card_fiberwise (f := g) (s := W) (t := colours W L)
      (fun v hv => hg1 v hv)
    have h2 : ∑ d ∈ colours W L, (1 + if d ∈ Bg.image g then 1 else 0) ≤
        ∑ d ∈ colours W L, (W.filter fun v => g v = d).card := by
      apply sum_le_sum
      intro d hd
      by_cases hdm : d ∈ Bg.image g
      · have := hcls2 d hdm; rw [if_pos hdm]; omega
      · have := hcls1 d hd; rw [if_neg hdm]; omega
    rw [sum_add_distrib, sum_const, sum_boole] at h2
    have h3 : (colours W L).filter (fun d => d ∈ Bg.image g) = Bg.image g := by
      ext d; simp only [mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hD h, h⟩⟩
    rw [h3] at h2
    simp only [smul_eq_mul, mul_one, Nat.cast_id] at h2
    unfold gam
    omega
  have hBg2 : 2 * ℓ ≤ Bg.card := by
    have hsum := card_eq_sum_card_fiberwise (f := g) (s := Bg) (t := Bg.image g)
      (fun v hv => mem_image_of_mem g hv)
    have : ∑ d ∈ Bg.image g, 2 ≤ ∑ d ∈ Bg.image g, (Bg.filter fun v => g v = d).card := by
      apply sum_le_sum
      intro d hd
      have h2 := hcls2 d hd
      have : (W.filter fun v => g v = d) ⊆ Bg.filter fun v => g v = d := by
        intro w hw
        obtain ⟨hwW, hwg⟩ := mem_filter.1 hw
        obtain ⟨v, hv, rfl⟩ := mem_image.1 hd
        refine mem_filter.2 ⟨mem_filter.2 ⟨hwW, ?_⟩, hwg⟩
        rw [hbig]
        by_cases hwv : w = v
        · obtain ⟨u, hu, hne, hgu⟩ := (hbig v).1 (mem_filter.1 hv).2
          exact ⟨u, hu, by rw [hwv]; exact hne, by rw [hwv]; exact hgu⟩
        · exact ⟨v, (mem_filter.1 hv).1, fun e => hwv e.symm, hwg.symm⟩
      exact h2.trans (card_le_card this)
    rw [sum_const, smul_eq_mul] at this
    omega
  have hℓk : ℓ ≤ k := by omega
  -- the colouring
  have hnonempty : A.Nonempty := by
    have : X.Nonempty := by rw [← card_pos]; omega
    obtain ⟨x, hx⟩ := this
    exact ⟨x, hXA hx⟩
  have hacc : Acc q A L gn := by
    refine ⟨fun v hv => ?_, fun u hu v hv huv => ?_⟩
    · obtain ⟨hvW, hvc⟩ := mem_filter.1 hv
      by_cases hvS : g v ∈ S
      · have : big v := by tauto
        simp only [hgn, hvS, if_true]; exact hbigL v hvW this
      · simp only [hgn, hvS, if_false]
        exact (hm2 (g v) (mem_sdiff.2 ⟨hg1 v hvW, hvS⟩)).1 v hvW rfl
    · obtain ⟨huW, huc⟩ := mem_filter.1 hu
      obtain ⟨hvW, hvc⟩ := mem_filter.1 hv
      have hne := hg2 u huW v hvW huv
      by_cases huS : g u ∈ S <;> by_cases hvS : g v ∈ S
      · simp only [hgn, huS, hvS, if_true]; exact hne
      · simp only [hgn, huS, hvS, if_true, if_false]
        have hbu : big u := by tauto
        intro e
        have hmem : g u ∈ S.biUnion (B_t W L g) := mem_biUnion.2 ⟨g u, huS, hbigt u huW hbu⟩
        exact (hm2 (g v) (mem_sdiff.2 ⟨hg1 v hvW, hvS⟩)).2 (by rw [← e]; exact hmem)
      · simp only [hgn, huS, hvS, if_true, if_false]
        have hbv : big v := by tauto
        intro e
        have hmem : g v ∈ S.biUnion (B_t W L g) := mem_biUnion.2 ⟨g v, hvS, hbigt v hvW hbv⟩
        exact (hm2 (g u) (mem_sdiff.2 ⟨hg1 u huW, huS⟩)).2 (by rw [e]; exact hmem)
      · simp only [hgn, huS, hvS, if_false]
        intro e
        exact hne (hm1 (mem_sdiff.2 ⟨hg1 u huW, huS⟩ : g u ∈ ((colours W L \ S : Finset ℕ) : Set ℕ))
          (mem_sdiff.2 ⟨hg1 v hvW, hvS⟩ : g v ∈ ((colours W L \ S : Finset ℕ) : Set ℕ)) e)
  refine ext_principle hIH hnonempty hAW hacc hℓk ?_ ?_ ?_
  · have h1 := card_sdiff_add_card_eq_card hAW
    have h2 : Bg.card ≤ A.card := card_le_card hBgA
    omega
  · have hsub : (W \ A).image q ⊆ W.image q \ X.image q := by
      intro a ha
      obtain ⟨v, hv, rfl⟩ := mem_image.1 ha
      obtain ⟨hvW, hvA⟩ := mem_sdiff.1 hv
      refine mem_sdiff.2 ⟨mem_image_of_mem q hvW, fun hx => ?_⟩
      obtain ⟨x, hxX, hxq⟩ := mem_image.1 hx
      have hxs : x ∈ singletons q W := (mem_filter.1 hxX).1
      have := B_singleton_eq hxs hvW hxq.symm
      exact hvA (this ▸ hXA hxX)
    have hXi : (X.image q).card = X.card := by
      apply card_image_of_injOn
      intro x hx y hy hxy
      exact (B_singleton_eq (mem_filter.1 hx).1 (mem_filter.1 (mem_filter.1 hy).1).1 hxy.symm).symm
    have hXsub : X.image q ⊆ W.image q := by
      intro a ha
      obtain ⟨x, hx, rfl⟩ := mem_image.1 ha
      exact mem_image_of_mem q (mem_filter.1 (mem_filter.1 hx).1).1
    have h1 := card_sdiff_add_card_eq_card hXsub
    have h2 := card_le_card hsub
    unfold nParts at hp ⊢
    omega
  · intro v hv
    obtain ⟨hvW, hvA⟩ := mem_sdiff.1 hv
    have hvS : g v ∈ S := by
      by_contra h; exact hvA (mem_filter.2 ⟨hvW, Or.inl h⟩)
    have hvb : ¬ big v := fun h => hvA (mem_filter.2 ⟨hvW, Or.inr h⟩)
    have hLvS : L v ⊆ S.biUnion (B_t W L g) := by
      intro x hx
      refine mem_biUnion.2 ⟨g v, hvS, mem_filter.2 ⟨hLC v hvW hx, fun w hw hgw => ?_⟩⟩
      have : w = v := by
        by_contra hne
        exact hvb ((hbig v).2 ⟨w, hw, hne, hgw⟩)
      rw [this]; exact hx
    have hsub : L v \ Bg.image g ⊆ L v \ A.image gn := by
      intro x hx
      obtain ⟨hxL, hxB⟩ := mem_sdiff.1 hx
      refine mem_sdiff.2 ⟨hxL, fun hxA => ?_⟩
      obtain ⟨a, haA, rfl⟩ := mem_image.1 hxA
      obtain ⟨haW, haor⟩ := mem_filter.1 haA
      by_cases haS : g a ∈ S
      · have hba : big a := by tauto
        simp only [hgn, haS, if_true] at hxB
        exact hxB (mem_image_of_mem g (mem_filter.2 ⟨haW, hba⟩))
      · simp only [hgn, haS, if_false] at hxL
        exact (hm2 (g a) (mem_sdiff.2 ⟨hg1 a haW, haS⟩)).2 (hLvS hxL)
    have h1 := le_card_sdiff (Bg.image g) (L v)
    have h2 := card_le_card hsub
    have h3 := (hb.1 v hvW)
    omega

theorem near_acc_imp_colourable (hIH : IH q W.card) (hp : nParts q W = k) (hc : W.card ≤ 2 * k + 1)
    (hb : Bad q W k L) : ¬ ∃ f, NearAcc q W k L f := by
  rintro ⟨f, hf1, hf2, hf3⟩
  have hW := card_eq_two_mul_add_one hIH hp hc hb
  obtain ⟨g, hg1, hg2, hg3, hg4⟩ := surj_modif hIH hp hc hb f hf1 hf2
  have hgn : ∀ v ∈ W, g v ∈ L v ∨ (Frequent q W k L (g v) ∧ ∀ u ∈ W, g u = g v → u = v) := by
    intro v hv
    rcases hg4 v hv with h | ⟨h1, h2⟩
    · left; exact h
    · rcases hf3 v hv with h' | ⟨hfq, hfs⟩
      · left; rw [h1]; exact h'
      · right
        rw [h1]
        exact ⟨hfq, fun u hu hgu => hfs u hu (h2 u hu (hgu.trans h1.symm))⟩
  have hP : ∀ v ∈ W, g v ∈ L v ∨ ∀ u ∈ W, g u = g v → u = v := fun v hv =>
    (hgn v hv).imp id (fun h => h.2)
  have hLC : ∀ v ∈ W, L v ⊆ colours W L := fun v hv => subset_biUnion_of_mem L hv
  obtain ⟨S, hSC, hmax⟩ := B_hall_def (colours W L) (B_t W L g)
  by_cases hcase : (S.card : ℤ) - (S.biUnion (B_t W L g)).card ≤ 0
  · -- full matching
    have hmax' : ∀ T ⊆ colours W L, ((T.card : ℤ) - (T.biUnion (B_t W L g)).card) ≤
        ((∅ : Finset ℕ).card : ℤ) - ((∅ : Finset ℕ).biUnion (B_t W L g)).card := by
      intro T hT
      have := hmax T hT
      simp only [card_empty, biUnion_empty]; push_cast; linarith
    obtain ⟨m, hm1, hm2⟩ := B_hall_match (colours W L) ∅ (B_t W L g) (empty_subset _) hmax'
    apply hb.2
    refine ⟨fun v => m (g v), fun v hv => ?_, fun u hu v hv huv => ?_⟩
    · have := (hm2 (g v) (mem_sdiff.2 ⟨hg1 v hv, notMem_empty _⟩)).1
      exact (mem_filter.1 this).2 v hv rfl
    · intro e
      have hmem : ∀ w ∈ W, g w ∈ ((colours W L \ ∅ : Finset ℕ) : Set ℕ) := fun w hw =>
        mem_coe.2 (mem_sdiff.2 ⟨hg1 w hw, notMem_empty _⟩)
      exact hg2 u hu v hv huv (hm1 (hmem u hu) (hmem v hv) e)
  · push_neg at hcase
    have hlt : (S.biUnion (B_t W L g)).card < S.card := by omega
    obtain ⟨m, hm1, hm2⟩ := B_hall_match (colours W L) S (B_t W L g) hSC hmax
    have hex : ∃ c ∈ S, c ∉ S.biUnion (B_t W L g) := by
      by_contra hcon
      push_neg at hcon
      exact absurd (card_le_card hcon) (by omega)
    obtain ⟨cs, hcsS, hcsN⟩ := hex
    have hcsC : cs ∈ colours W L := hSC hcsS
    have hnot : ∀ d ∈ S, ∃ u ∈ W, g u = d ∧ cs ∉ L u := by
      intro d hd
      by_contra hcon
      push_neg at hcon
      apply hcsN
      refine mem_biUnion.2 ⟨d, hd, mem_filter.2 ⟨hcsC, fun v hv hgv => ?_⟩⟩
      by_contra hn
      exact hn (hcon v hv hgv)
    obtain ⟨w, hwW, hgw, hcsw⟩ := hnot cs hcsS
    rcases hgn w hwW with h | ⟨hfreq, hcls⟩
    · rw [hgw] at h; exact hcsw h
    · rw [hgw] at hfreq hcls
      rcases hfreq with hglob | hsing
      · -- case 1
        have h1 : k ≤ (S.biUnion (B_t W L g)).card := by
          have hsub : L w ⊆ S.biUnion (B_t W L g) := by
            intro x hx
            refine mem_biUnion.2 ⟨cs, hcsS, mem_filter.2 ⟨hLC w hwW hx, fun v hv hgv => ?_⟩⟩
            have := hcls v hv hgv
            rw [this]; exact hx
          exact (hb.1 w hwW).trans (card_le_card hsub)
        have hinh : Nonempty V := ⟨w⟩
        have hch : ∀ d, ∃ x : V, d ∈ S → (x ∈ W ∧ g x = d ∧ cs ∉ L x) := by
          intro d
          by_cases hd : d ∈ S
          · obtain ⟨u, hu, h2, h3⟩ := hnot d hd
            exact ⟨u, fun _ => ⟨hu, h2, h3⟩⟩
          · exact ⟨w, fun h => absurd h hd⟩
        choose u hu using hch
        have h2 : S.card ≤ (W \ avail W L cs).card := by
          apply card_le_card_of_injOn u
          · intro d hd
            obtain ⟨h1, h2, h3⟩ := hu d hd
            exact mem_sdiff.2 ⟨h1, fun hm => h3 (mem_filter.1 hm).2⟩
          · intro d hd d' hd' e
            have := (hu d hd).2.1
            have := (hu d' hd').2.1
            rw [← (hu d hd).2.1, ← (hu d' hd').2.1, e]
        have h3 := card_sdiff_add_card_eq_card (filter_subset (fun v => cs ∈ L v) W)
        change (W \ avail W L cs).card + (avail W L cs).card = W.card at h3
        omega
      · -- case 2
        apply hb.2
        apply B_claim24 hIH hp hc hb hg1 hg2 hg3 hP hSC hm1 _ _
        · intro d hd
          have := hm2 d hd
          exact ⟨fun v hv hgv => (mem_filter.1 this.1).2 v hv hgv, this.2⟩
        · refine hsing.trans (card_le_card ?_)
          intro x hx
          obtain ⟨hxs, hcx⟩ := mem_filter.1 hx
          refine mem_filter.2 ⟨hxs, fun hxS => hcsN ?_⟩
          have hxW : x ∈ W := (mem_filter.1 hxs).1
          refine mem_biUnion.2 ⟨g x, hxS, mem_filter.2 ⟨hcsC, fun v hv hgv => ?_⟩⟩
          have : v = x := by
            by_contra hne
            have hq : q v ≠ q x := fun e => hne (B_singleton_eq hxs hv e)
            exact hg2 v hv x hxW hq hgv
          rw [this]; exact hcx

theorem frequent_mem_singleton (hIH : IH q W.card) (hp : nParts q W = k) (hc : W.card ≤ 2 * k + 1)
    (hm : MaxBad q W k L) {c : ℕ} (hcf : Frequent q W k L c) {v : V} (hv : v ∈ singletons q W) :
    c ∈ L v := by
  by_contra hcv
  have hv' : v ∈ W := (mem_filter.1 hv).1
  have hlt := colours_lt_card hIH hp hc hm.1
  have hgam : 1 ≤ gam W L := by unfold gam; omega
  have hcC : c ∈ colours W L := by
    rcases hcf with h | h
    · have : (avail W L c).Nonempty := by rw [← card_pos]; omega
      obtain ⟨u, hu⟩ := this
      exact mem_biUnion.2 ⟨u, (mem_filter.1 hu).1, (mem_filter.1 hu).2⟩
    · have : (((singletons q W).filter fun v => c ∈ L v)).Nonempty := by
        rw [← card_pos]; omega
      obtain ⟨u, hu⟩ := this
      have hu' := mem_filter.1 hu
      exact mem_biUnion.2 ⟨u, (mem_filter.1 hu'.1).1, hu'.2⟩
  obtain ⟨g, hg1, hg2⟩ := hm.2 v hv' c hcC hcv
  have hgv : g v = c := by
    by_contra hne
    apply hm.1.2
    refine ⟨g, ?_, hg2⟩
    intro w hw
    by_cases hwv : w = v
    · rw [hwv]
      have := hg1 v hv'
      simp only [Function.update_self, mem_insert] at this
      rcases this with h | h
      · exact absurd h hne
      · exact h
    · have := hg1 w hw
      simpa [Function.update_of_ne hwv] using this
  apply near_acc_imp_colourable hIH hp hc hm.1
  refine ⟨g, ?_, hg2, ?_⟩
  · intro w hw
    by_cases hwv : w = v
    · rw [hwv, hgv]; exact hcC
    · have := hg1 w hw
      rw [Function.update_of_ne hwv] at this
      exact mem_biUnion.2 ⟨w, hw, this⟩
  · intro w hw
    by_cases hwv : w = v
    · right
      rw [hwv, hgv]
      refine ⟨hcf, ?_⟩
      intro u hu hgu
      by_contra hne
      have hq : q u ≠ q v := fun h => hne (B_singleton_eq hv hu h)
      exact hg2 u hu v hv' hq (by rw [hgu, hgv])
    · left
      have := hg1 w hw
      rwa [Function.update_of_ne hwv] at this

theorem prop_4_9 (hIH : IH q W.card) (hp : nParts q W = k) (hc : W.card ≤ 2 * k + 1)
    (hm : MaxBad q W k L) {c : ℕ} (hcC : c ∈ colours W L) (hnf : ¬ Frequent q W k L c) :
    ∃ X ⊆ singletons q W, (singletons q W).card + 1 - gam W L ≤ X.card ∧
      (X.biUnion L).card + (avail W L c).card ≤ 2 * k := by
  have hW := card_eq_two_mul_add_one hIH hp hc hm.1
  have hLC : ∀ v ∈ W, L v ⊆ colours W L := fun v hv => subset_biUnion_of_mem L hv
  rw [Frequent, not_or, not_le, not_le] at hnf
  by_cases hex : ∃ x ∈ singletons q W, c ∉ L x
  swap
  · push_neg at hex
    have hfil : ((singletons q W).filter fun v => c ∈ L v) = singletons q W :=
      filter_true_of_mem hex
    rw [hfil] at hnf
    refine ⟨∅, empty_subset _, ?_, ?_⟩
    · simp only [card_empty]; omega
    · simp only [biUnion_empty, card_empty]; omega
  obtain ⟨x, hxs, hcx⟩ := hex
  have hxW : x ∈ W := (mem_filter.1 hxs).1
  obtain ⟨f, hf1, hf2⟩ := hm.2 x hxW c hcC hcx
  have hfx : f x = c := by
    by_contra hne
    apply hm.1.2
    refine ⟨f, fun w hw => ?_, hf2⟩
    by_cases hwx : w = x
    · rw [hwx]
      have := hf1 x hxW
      simp only [Function.update_self, mem_insert] at this
      rcases this with h | h
      · exact absurd h hne
      · exact h
    · have := hf1 w hw
      rwa [Function.update_of_ne hwx] at this
  have hfL : ∀ w ∈ W, w ≠ x → f w ∈ L w := by
    intro w hw hwx
    have := hf1 w hw
    rwa [Function.update_of_ne hwx] at this
  have hfC : ∀ w ∈ W, f w ∈ colours W L := by
    intro w hw
    by_cases hwx : w = x
    · rw [hwx, hfx]; exact hcC
    · exact hLC w hw (hfL w hw hwx)
  obtain ⟨g, hg1, hg2, hg3, hg4⟩ := surj_modif hIH hp hc hm.1 f hfC hf2
  -- vertices whose colour is not in their list
  have hbad : ∀ v ∈ W, g v ∉ L v → v = x ∧ g v = c := by
    intro v hv hn
    rcases hg4 v hv with h | ⟨h1, _⟩
    · exact absurd h hn
    · have hfv : f v ∉ L v := by rw [← h1]; exact hn
      have hvx : v = x := by
        by_contra hne; exact hfv (hfL v hv hne)
      refine ⟨hvx, ?_⟩
      rw [h1, hvx, hfx]
  have hP : ∀ v ∈ W, g v ∈ L v ∨ ∀ u ∈ W, g u = g v → u = v := by
    intro v hv
    by_cases hl : g v ∈ L v
    · exact Or.inl hl
    · right
      obtain ⟨hvx, hgv⟩ := hbad v hv hl
      intro u hu hgu
      by_contra hne
      have hq : q u ≠ q v := by
        intro e
        rw [hvx] at e hne
        exact hne (B_singleton_eq hxs hu e)
      -- g u = c = g v, but f u = f v by hg4
      rcases hg4 v hv with h | ⟨_, h2⟩
      · exact hl h
      · have := h2 u hu hgu
        rw [hvx] at this
        exact hf2 u hu x hxW (by rw [hvx] at hq; exact hq) this
  have hCt : ∀ d ∈ colours W L, d ≠ c → d ∈ B_t W L g d := by
    intro d hd hdc
    refine mem_filter.2 ⟨hd, fun v hv hgv => ?_⟩
    by_cases hl : g v ∈ L v
    · rw [← hgv]; exact hl
    · exact absurd (by rw [← hgv]; exact (hbad v hv hl).2) hdc
  obtain ⟨S, hSC, hmax⟩ := B_hall_def (colours W L) (B_t W L g)
  by_cases hcase : (S.card : ℤ) - (S.biUnion (B_t W L g)).card ≤ 0
  · exfalso
    have hmax' : ∀ T ⊆ colours W L, ((T.card : ℤ) - (T.biUnion (B_t W L g)).card) ≤
        ((∅ : Finset ℕ).card : ℤ) - ((∅ : Finset ℕ).biUnion (B_t W L g)).card := by
      intro T hT
      have := hmax T hT
      simp only [card_empty, biUnion_empty]; push_cast; linarith
    obtain ⟨m, hm1, hm2⟩ := B_hall_match (colours W L) ∅ (B_t W L g) (empty_subset _) hmax'
    apply hm.1.2
    refine ⟨fun v => m (g v), fun v hv => ?_, fun u hu v hv huv => ?_⟩
    · have := (hm2 (g v) (mem_sdiff.2 ⟨hg1 v hv, notMem_empty _⟩)).1
      exact (mem_filter.1 this).2 v hv rfl
    · intro e
      have hmem : ∀ w ∈ W, g w ∈ ((colours W L \ ∅ : Finset ℕ) : Set ℕ) := fun w hw =>
        mem_coe.2 (mem_sdiff.2 ⟨hg1 w hw, notMem_empty _⟩)
      exact hg2 u hu v hv huv (hm1 (hmem u hu) (hmem v hv) e)
  push_neg at hcase
  have hlt : (S.biUnion (B_t W L g)).card < S.card := by omega
  obtain ⟨m, hm1, hm2⟩ := B_hall_match (colours W L) S (B_t W L g) hSC hmax
  have hex2 : ∃ d ∈ S, d ∉ S.biUnion (B_t W L g) := by
    by_contra hcon
    push_neg at hcon
    exact absurd (card_le_card hcon) (by omega)
  obtain ⟨d0, hd0S, hd0N⟩ := hex2
  have hd0c : d0 = c := by
    by_contra hne
    exact hd0N (mem_biUnion.2 ⟨d0, hd0S, hCt d0 (hSC hd0S) hne⟩)
  rw [hd0c] at hd0S hd0N
  have hnot : ∀ d ∈ S, ∃ u ∈ W, g u = d ∧ c ∉ L u := by
    intro d hd
    by_contra hcon
    push_neg at hcon
    apply hd0N
    refine mem_biUnion.2 ⟨d, hd, mem_filter.2 ⟨hcC, fun v hv hgv => ?_⟩⟩
    by_contra hn
    exact hn (hcon v hv hgv)
  have hinh : Nonempty V := ⟨x⟩
  have hch : ∀ d, ∃ y : V, d ∈ S → (y ∈ W ∧ g y = d ∧ c ∉ L y) := by
    intro d
    by_cases hd : d ∈ S
    · obtain ⟨u, hu, h2, h3⟩ := hnot d hd
      exact ⟨u, fun _ => ⟨hu, h2, h3⟩⟩
    · exact ⟨x, fun h => absurd h hd⟩
  choose u hu using hch
  have hSle : S.card ≤ (W \ avail W L c).card := by
    apply card_le_card_of_injOn u
    · intro d hd
      obtain ⟨h1, h2, h3⟩ := hu d hd
      exact mem_sdiff.2 ⟨h1, fun hm => h3 (mem_filter.1 hm).2⟩
    · intro d hd d' hd' e
      rw [← (hu d hd).2.1, ← (hu d' hd').2.1, e]
  have h3 := card_sdiff_add_card_eq_card (filter_subset (fun v => c ∈ L v) W)
  change (W \ avail W L c).card + (avail W L c).card = W.card at h3
  have hcl : ∀ y ∈ singletons q W, ∀ v ∈ W, g v = g y → v = y := by
    intro y hy v hv hgv
    by_contra hne
    have hq : q v ≠ q y := fun e => hne (B_singleton_eq hy hv e)
    exact hg2 v hv y (mem_filter.1 hy).1 hq hgv
  refine ⟨(singletons q W).filter (fun y => g y ∈ S), filter_subset _ _, ?_, ?_⟩
  · by_contra hcon
    push_neg at hcon
    have hsplit := card_filter_add_card_filter_not (s := singletons q W) (fun y => g y ∈ S)
    have hs : gam W L ≤ ((singletons q W).filter fun y => g y ∉ S).card := by
      change _ ≤ ((singletons q W).filter fun y => ¬ g y ∈ S).card
      omega
    exact hm.1.2 (B_claim24 hIH hp hc hm.1 hg1 hg2 hg3 hP hSC hm1
      (fun d hd => ⟨fun v hv hgv => (mem_filter.1 (hm2 d hd).1).2 v hv hgv, (hm2 d hd).2⟩) hs)
  · have hsub : ((singletons q W).filter (fun y => g y ∈ S)).biUnion L ⊆ S.biUnion (B_t W L g) := by
      intro z hz
      obtain ⟨y, hy, hzy⟩ := mem_biUnion.1 hz
      obtain ⟨hys, hyS⟩ := mem_filter.1 hy
      refine mem_biUnion.2 ⟨g y, hyS, mem_filter.2 ⟨hLC y (mem_filter.1 hys).1 hzy, fun v hv hgv => ?_⟩⟩
      rw [hcl y hys v hv hgv]; exact hzy
    have := card_le_card hsub
    omega

end core


theorem C_best (q : V → ℕ) (W : Finset V) (P : Finset V → Prop) (h0 : P ∅) :
    ∃ V1 ⊆ W, P V1 ∧ ∀ V2 ⊆ W, P V2 →
      V2.card < V1.card ∨ (V2.card = V1.card ∧ (V2.image q).card ≤ (V1.image q).card) := by
  obtain ⟨A, hA, hA1⟩ := Finset.exists_max_image (W.powerset.filter P) Finset.card
    ⟨∅, by simp [h0]⟩
  obtain ⟨B, hB, hB1⟩ := Finset.exists_max_image
    ((W.powerset.filter P).filter (fun s => s.card = A.card)) (fun s => (s.image q).card)
    ⟨A, mem_filter.2 ⟨hA, rfl⟩⟩
  simp only [mem_filter, mem_powerset] at hA hB hA1 hB1
  refine ⟨B, hB.1.1, hB.1.2, fun V2 h2 hP2 => ?_⟩
  have h3 := hA1 V2 ⟨h2, hP2⟩
  rcases lt_or_eq_of_le h3 with h | h
  · left; omega
  · right; exact ⟨by omega, hB1 V2 ⟨⟨h2, hP2⟩, h⟩⟩

theorem C_assemble {q : V → ℕ} {W : Finset V} {k : ℕ} {L : V → Finset ℕ} {F : Finset ℕ}
    (hFC : F ⊆ colours W L) (hFq : ∀ c ∈ F, Frequent q W k L c)
    {V1 : Finset V} {f1 : V → ℕ} (hacc : Acc q V1 L f1) (hV1 : V1 ⊆ W)
    (hF1 : ∀ v ∈ V1, f1 v ∉ F)
    {T : Finset ℕ} {φ : ℕ → ℕ} (hφF : ∀ p ∈ T, φ p ∈ F)
    (hφL : ∀ p ∈ T, ∀ v ∈ W \ V1, q v = p → φ p ∈ L v) (hφinj : Set.InjOn φ T)
    {ψ : V → ℕ} (hψF : ∀ v ∈ W \ V1, q v ∉ T → ψ v ∈ F ∧ ψ v ∉ T.image φ)
    (hψinj : ∀ u ∈ W \ V1, ∀ v ∈ W \ V1, q u ∉ T → q v ∉ T → ψ u = ψ v →
      u = v ∨ (q u = q v ∧ ψ v ∈ L u ∧ ψ v ∈ L v)) :
    ∃ f, NearAcc q W k L f := by
  refine ⟨fun v => if v ∈ V1 then f1 v else if q v ∈ T then φ (q v) else ψ v, ?_, ?_, ?_⟩
  · intro v hv
    by_cases h1 : v ∈ V1
    · simp only [h1, if_true]
      exact Finset.mem_biUnion.2 ⟨v, hv, hacc.1 v h1⟩
    · by_cases h2 : q v ∈ T
      · simp only [h1, h2, if_false, if_true]; exact hFC (hφF _ h2)
      · simp only [h1, h2, if_false]; exact hFC (hψF v (mem_sdiff.2 ⟨hv, h1⟩) h2).1
  · intro u hu v hv huv
    by_cases h1 : u ∈ V1 <;> by_cases h2 : v ∈ V1
    · simp only [h1, h2, if_true]; exact hacc.2 u h1 v h2 huv
    · by_cases h3 : q v ∈ T
      · simp only [h1, h2, h3, if_true, if_false]
        exact fun h => hF1 u h1 (h ▸ hφF _ h3)
      · simp only [h1, h2, h3, if_true, if_false]
        exact fun h => hF1 u h1 (h ▸ (hψF v (mem_sdiff.2 ⟨hv, h2⟩) h3).1)
    · by_cases h3 : q u ∈ T
      · simp only [h1, h2, h3, if_true, if_false]
        exact fun h => hF1 v h2 (h ▸ hφF _ h3)
      · simp only [h1, h2, h3, if_true, if_false]
        exact fun h => hF1 v h2 (h ▸ (hψF u (mem_sdiff.2 ⟨hu, h1⟩) h3).1)
    · by_cases h3 : q u ∈ T <;> by_cases h4 : q v ∈ T
      · simp only [h1, h2, h3, h4, if_true, if_false]
        exact fun h => huv (hφinj h3 h4 h)
      · simp only [h1, h2, h3, h4, if_true, if_false]
        exact fun h => (hψF v (mem_sdiff.2 ⟨hv, h2⟩) h4).2 (mem_image.2 ⟨_, h3, h⟩)
      · simp only [h1, h2, h3, h4, if_true, if_false]
        exact fun h => (hψF u (mem_sdiff.2 ⟨hu, h1⟩) h3).2 (mem_image.2 ⟨_, h4, h.symm⟩)
      · simp only [h1, h2, h3, h4, if_true, if_false]
        intro h
        rcases hψinj u (mem_sdiff.2 ⟨hu, h1⟩) v (mem_sdiff.2 ⟨hv, h2⟩) h3 h4 h with h5 | h5
        · exact huv (by rw [h5])
        · exact huv h5.1
  · intro v hv
    by_cases h1 : v ∈ V1
    · left; simp only [h1, if_true]; exact hacc.1 v h1
    · by_cases h2 : q v ∈ T
      · left; simp only [h1, h2, if_false, if_true]
        exact hφL _ h2 v (mem_sdiff.2 ⟨hv, h1⟩) rfl
      · simp only [h1, h2, if_false]
        have hv' : v ∈ W \ V1 := mem_sdiff.2 ⟨hv, h1⟩
        by_cases h3 : ψ v ∈ L v
        · left; exact h3
        · right
          refine ⟨hFq _ (hψF v hv' h2).1, ?_⟩
          intro u hu hu2
          by_cases h4 : u ∈ V1
          · simp only [h4, if_true] at hu2
            exact absurd (hu2 ▸ (hψF v hv' h2).1) (hF1 u h4)
          · by_cases h5 : q u ∈ T
            · simp only [h4, h5, if_false, if_true] at hu2
              exact absurd (mem_image.2 ⟨_, h5, hu2⟩) (hψF v hv' h2).2
            · simp only [h4, h5, if_false] at hu2
              rcases hψinj u (mem_sdiff.2 ⟨hu, h4⟩) v hv' h5 h2 hu2 with h6 | h6
              · exact h6
              · exact absurd h6.2.2 h3

theorem C_mod {q : V → ℕ} {L : V → Finset ℕ} {F : Finset ℕ} {V1 D S : Finset V} {f1 : V → ℕ}
    {c : ℕ} (hacc : Acc q V1 L f1) (hF1 : ∀ v ∈ V1, f1 v ∉ F) (hD : D ⊆ V1) (hc : c ∉ F)
    (hS : ∀ s ∈ S, c ∈ L s) (hSq : ∀ s ∈ S, ∀ s' ∈ S, q s = q s') (hSV : ∀ s ∈ S, s ∉ V1)
    (hrest : ∀ x ∈ V1 \ D, ∀ s ∈ S, q x ≠ q s → f1 x ≠ c) :
    (∃ f2, Acc q (V1 \ D ∪ S) L f2 ∧ ∀ v ∈ V1 \ D ∪ S, f2 v ∉ F) ∧
      (V1 \ D ∪ S).card + D.card = V1.card + S.card := by
  have hdisj : Disjoint (V1 \ D) S := by
    rw [Finset.disjoint_left]
    intro x hx hxS; exact hSV x hxS (mem_sdiff.1 hx).1
  have key : ∀ v ∈ V1 \ D ∪ S, v ∉ S → v ∈ V1 \ D := by
    intro v hv h
    rcases mem_union.1 hv with h' | h'
    · exact h'
    · exact absurd h' h
  refine ⟨⟨fun v => if v ∈ S then c else f1 v, ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro v hv
    by_cases h : v ∈ S
    · simp only [h, if_true]; exact hS v h
    · simp only [h, if_false]
      exact hacc.1 v (mem_sdiff.1 (key v hv h)).1
  · intro u hu v hv huv
    by_cases h1 : u ∈ S <;> by_cases h2 : v ∈ S
    · exact absurd (hSq u h1 v h2) huv
    · simp only [h1, h2, if_true, if_false]
      exact fun h => hrest v (key v hv h2) u h1 (Ne.symm huv) h.symm
    · simp only [h1, h2, if_true, if_false]
      exact hrest u (key u hu h1) v h2 huv
    · simp only [h1, h2, if_false]
      exact hacc.2 u (mem_sdiff.1 (key u hu h1)).1 v (mem_sdiff.1 (key v hv h2)).1 huv
  · intro v hv
    by_cases h : v ∈ S
    · simp only [h, if_true]; exact hc
    · simp only [h, if_false]; exact hF1 v (mem_sdiff.1 (key v hv h)).1
  · rw [Finset.card_union_of_disjoint hdisj]
    have := Finset.card_sdiff_add_card_eq_card hD
    omega

theorem C_inj {s : Finset V} {t : Finset ℕ} (h : s.card ≤ t.card) :
    ∃ ψ : V → ℕ, (∀ v ∈ s, ψ v ∈ t) ∧ Set.InjOn ψ s := by
  obtain ⟨t', ht', hc⟩ := Finset.exists_subset_card_eq h
  let e := Finset.equivOfCardEq (hc.symm : s.card = t'.card)
  refine ⟨fun v => if hv : v ∈ s then (e ⟨v, hv⟩ : ℕ) else 0, ?_, ?_⟩
  · intro v hv
    simp only [hv, dif_pos]
    exact ht' (e ⟨v, hv⟩).2
  · intro a ha b hb hab
    have ha' : a ∈ s := ha
    have hb' : b ∈ s := hb
    simp only [dif_pos ha', dif_pos hb'] at hab
    have := e.injective (Subtype.ext hab)
    simpa using congrArg Subtype.val this

theorem C_L5 {q : V → ℕ} {W : Finset V} {k : ℕ} {L : V → Finset ℕ}
    (hW : W.card = 2 * k + 1) (hLk : ∀ v ∈ W, k ≤ (L v).card)
    (hlt : (colours W L).card < W.card)
    (hinter : ∀ v ∈ W, 2 ≤ (partOf q W v).card → ∀ c, ∃ u ∈ partOf q W v, c ∉ L u)
    {v : V} (hv : v ∈ W) (h2 : (partOf q W v).card = 2) :
    ∃ u ∈ W, u ≠ v ∧ q u = q v ∧ (∀ c, c ∈ L u → c ∉ L v) ∧ colours W L = L u ∪ L v ∧
      (colours W L).card = 2 * k := by
  obtain ⟨x, y, hxy, hxy2⟩ := Finset.card_eq_two.1 h2
  have hvp : v ∈ partOf q W v := by simp [partOf, hv]
  have hmem : ∀ z, z ∈ partOf q W v ↔ z = x ∨ z = y := by
    intro z; rw [hxy2]; simp
  obtain ⟨u, hu, hne⟩ : ∃ u, u ∈ partOf q W v ∧ u ≠ v := by
    rcases (hmem v).1 hvp with h | h
    · exact ⟨y, (hmem y).2 (Or.inr rfl), by rw [h]; exact Ne.symm hxy⟩
    · exact ⟨x, (hmem x).2 (Or.inl rfl), by rw [h]; exact hxy⟩
  have huW : u ∈ W := (mem_filter.1 hu).1
  have huq : q u = q v := (mem_filter.1 hu).2
  have hall : ∀ z, z ∈ partOf q W v → z = u ∨ z = v := by
    intro z hz
    rcases (hmem z).1 hz with h | h <;> rcases (hmem u).1 hu with h' | h' <;>
      rcases (hmem v).1 hvp with h'' | h'' <;> subst_vars <;> simp_all
  have hdis : ∀ c, c ∈ L u → c ∉ L v := by
    intro c hcu hcv
    obtain ⟨w, hw, hcw⟩ := hinter v hv (by omega) c
    rcases hall w hw with h | h <;> subst h <;> simp_all
  have hsub : L u ∪ L v ⊆ colours W L := by
    intro c hc
    rcases mem_union.1 hc with h | h
    · exact mem_biUnion.2 ⟨u, huW, h⟩
    · exact mem_biUnion.2 ⟨v, hv, h⟩
  have hdj : Disjoint (L u) (L v) := Finset.disjoint_left.2 hdis
  have hcard : (L u ∪ L v).card = (L u).card + (L v).card := Finset.card_union_of_disjoint hdj
  have h1 := hLk u huW
  have h3 := hLk v hv
  have h4 := Finset.card_le_card hsub
  have heq : L u ∪ L v = colours W L :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  exact ⟨u, huW, hne, huq, hdis, heq.symm, by omega⟩

theorem C_claim32 {q : V → ℕ} {W : Finset V} {k : ℕ} {L : V → Finset ℕ} {F : Finset ℕ}
    (hW : W.card = 2 * k + 1) (hnp : (W.image q).card = k) (hLk : ∀ v ∈ W, k ≤ (L v).card)
    (hlt : (colours W L).card < W.card)
    (hinter : ∀ v ∈ W, 2 ≤ (partOf q W v).card → ∀ c, ∃ u ∈ partOf q W v, c ∉ L u)
    (hFk : F.card = k) (hFC : F ⊆ colours W L) (hFq : ∀ c ∈ F, Frequent q W k L c)
    (hno : ¬ ∃ f, NearAcc q W k L f)
    {V1 : Finset V} {f1 : V → ℕ} (hacc : Acc q V1 L f1) (hV1 : V1 ⊆ W)
    (hF1 : ∀ v ∈ V1, f1 v ∉ F)
    (hmax : ∀ V2 ⊆ W, ∀ f2, Acc q V2 L f2 → (∀ v ∈ V2, f2 v ∉ F) →
      V2.card < V1.card ∨ (V2.card = V1.card ∧ (V2.image q).card ≤ (V1.image q).card))
    {v : V} (hv : v ∈ W) (h2 : (partOf q W v).card = 2) : ∃ x ∈ V1, q x = q v := by
  by_contra hnone
  push_neg at hnone
  obtain ⟨u, huW, hne, hq, hdis, hunion, hC2⟩ := C_L5 hW hLk hlt hinter hv h2
  have huV : u ∉ V1 := fun h => hnone u h hq
  have hvV : v ∉ V1 := fun h => hnone v h rfl
  -- extension impossible
  have hext : ∀ w ∈ W, (w = u ∨ w = v) → ∀ c ∈ L w, c ∉ F → c ∉ V1.image f1 → False := by
    intro w hw hwuv c hc hcF hcn
    have hwV : w ∉ V1 := by rcases hwuv with h | h <;> subst h <;> assumption
    obtain ⟨⟨f2, hf2⟩, hcard⟩ := C_mod (D := ∅) (S := {w}) hacc hF1 (empty_subset _) hcF
      (by simpa using hc) (by simp) (by simpa using hwV)
      (by
        intro x hx s hs hxs
        rw [mem_singleton] at hs; subst hs
        intro h
        exact hcn (mem_image.2 ⟨x, by simpa using hx, h⟩))
    have hsub : V1 \ ∅ ∪ {w} ⊆ W := by
      intro z hz
      simp only [sdiff_empty, mem_union, mem_singleton] at hz
      rcases hz with h | h
      · exact hV1 h
      · exact h ▸ hw
    have := hmax _ hsub f2 hf2.1 hf2.2
    simp only [card_empty, card_singleton, add_zero] at hcard
    omega
  have hCF : colours W L \ F ⊆ V1.image f1 := by
    intro c hc
    rw [mem_sdiff] at hc
    by_contra hcn
    have : c ∈ L u ∪ L v := hunion ▸ hc.1
    rcases mem_union.1 this with h | h
    · exact hext u huW (Or.inl rfl) c h hc.2 hcn
    · exact hext v hv (Or.inr rfl) c h hc.2 hcn
  have hk : k ≤ (V1.image f1).card := by
    have := Finset.card_le_card hCF
    rw [Finset.card_sdiff_of_subset hFC] at this
    omega
  have hkV : k ≤ V1.card := le_trans hk Finset.card_image_le
  by_cases hbig : k + 1 ≤ V1.card
  · apply hno
    obtain ⟨ψ, hψ1, hψ2⟩ := C_inj (s := W \ V1) (t := F) (by
      rw [Finset.card_sdiff_of_subset hV1]; omega)
    exact C_assemble hFC hFq hacc hV1 hF1 (T := ∅) (φ := fun _ => 0) (by simp) (by simp)
      (by simp) (ψ := ψ) (fun x hx _ => ⟨hψ1 x hx, by simp⟩)
      (fun a ha b hb _ _ h => Or.inl (hψ2 ha hb h))
  · have hVk : V1.card = k := by omega
    have hinj : Set.InjOn f1 V1 := by
      rw [← Finset.card_image_iff]
      have := Finset.card_image_le (s := V1) (f := f1)
      omega
    have hkpos : 0 < k := by
      rw [← hnp]; exact Finset.card_pos.2 ⟨q v, mem_image.2 ⟨v, hv, rfl⟩⟩
    have hmaps : ∀ a ∈ V1, q a ∈ (W.image q).erase (q v) := by
      intro a ha
      exact mem_erase.2 ⟨hnone a ha, mem_image.2 ⟨a, hV1 ha, rfl⟩⟩
    obtain ⟨x, hx, y, hy, hxy, hqxy⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (by rw [Finset.card_erase_of_mem (mem_image.2 ⟨v, hv, rfl⟩), hnp]; omega) hmaps
    have hcx : f1 x ∈ colours W L \ F := by
      rw [mem_sdiff]
      exact ⟨mem_biUnion.2 ⟨x, hV1 hx, hacc.1 x hx⟩, hF1 x hx⟩
    have : f1 x ∈ L u ∪ L v := hunion ▸ (mem_sdiff.1 hcx).1
    obtain ⟨w, hwW, hwuv, hcw⟩ : ∃ w ∈ W, (w = u ∨ w = v) ∧ f1 x ∈ L w := by
      rcases mem_union.1 this with h | h
      · exact ⟨u, huW, Or.inl rfl, h⟩
      · exact ⟨v, hv, Or.inr rfl, h⟩
    have hwV : w ∉ V1 := by rcases hwuv with h | h <;> subst h <;> assumption
    have hqw : q w = q v := by rcases hwuv with h | h <;> subst h <;> simp [hq]
    obtain ⟨⟨f2, hf2⟩, hcard⟩ := C_mod (D := {x}) (S := {w}) hacc hF1
      (by simpa using hx) ((mem_sdiff.1 hcx).2) (by simpa using hcw) (by simp) (by simpa using hwV)
      (by
        intro z hz s hs _
        rw [mem_sdiff, mem_singleton] at hz
        intro h
        exact hz.2 (hinj hz.1 hx h))
    have hsub : V1 \ {x} ∪ {w} ⊆ W := by
      intro z hz
      simp only [mem_union, mem_sdiff, mem_singleton] at hz
      rcases hz with h | h
      · exact hV1 h.1
      · exact h ▸ hwW
    have hm := hmax _ hsub f2 hf2.1 hf2.2
    simp only [card_singleton] at hcard
    have hq1 : insert (q w) (V1.image q) ⊆ (V1 \ {x} ∪ {w}).image q := by
      intro r hr
      rw [mem_insert] at hr
      rcases hr with h | h
      · exact mem_image.2 ⟨w, by simp, h.symm⟩
      · obtain ⟨z, hz, hzr⟩ := mem_image.1 h
        by_cases hzx : z = x
        · subst hzx
          exact mem_image.2 ⟨y, by simp [mem_union, mem_sdiff, hy, Ne.symm hxy], by rw [← hzr]; exact hqxy.symm⟩
        · exact mem_image.2 ⟨z, by simp [mem_union, mem_sdiff, hz, hzx], hzr⟩
    have hnotin : q w ∉ V1.image q := by
      intro h
      obtain ⟨z, hz, hzq⟩ := mem_image.1 h
      exact hnone z hz (hzq.trans hqw)
    have := Finset.card_le_card hq1
    rw [Finset.card_insert_of_notMem hnotin] at this
    omega

def C_R (q : V → ℕ) (W V1 : Finset V) (p : ℕ) : Finset V := (W \ V1).filter (fun v => q v = p)

theorem C_keyK {q : V → ℕ} {W : Finset V} {L : V → Finset ℕ} {F : Finset ℕ}
    {V1 : Finset V} {f1 : V → ℕ} (hacc : Acc q V1 L f1) (hV1 : V1 ⊆ W)
    (hF1 : ∀ v ∈ V1, f1 v ∉ F)
    (hmax : ∀ V2 ⊆ W, ∀ f2, Acc q V2 L f2 → (∀ v ∈ V2, f2 v ∉ F) →
      V2.card < V1.card ∨ (V2.card = V1.card ∧ (V2.image q).card ≤ (V1.image q).card))
    (p : ℕ) {c : ℕ} (hc : c ∉ F) :
    ((C_R q W V1 p).filter (fun v => c ∈ L v)).card ≤
      (V1.filter (fun x => f1 x = c ∧ q x ≠ p)).card := by
  set S := (C_R q W V1 p).filter (fun v => c ∈ L v) with hSdef
  have hSp : ∀ s ∈ S, c ∈ L s ∧ q s = p ∧ s ∈ W ∧ s ∉ V1 := by
    intro s hs
    simp only [hSdef, C_R, mem_filter, mem_sdiff] at hs
    exact ⟨hs.2, hs.1.2, hs.1.1.1, hs.1.1.2⟩
  have hSW : ∀ D : Finset V, V1 \ D ∪ S ⊆ W := by
    intro D z hz
    rcases mem_union.1 hz with h | h
    · exact hV1 (mem_sdiff.1 h).1
    · exact (hSp z h).2.2.1
  by_cases hS0 : S = ∅
  · rw [hS0]; simp
  have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.2 hS0
  have hSpos : 0 < S.card := Finset.card_pos.2 hSne
  have hi : ∀ x ∈ V1, f1 x = c → q x ≠ p := by
    intro x hx hxc hqx
    obtain ⟨⟨f2, hf2⟩, hcard⟩ := C_mod (D := ∅) (S := S) hacc hF1 (empty_subset _) hc
      (fun s hs => (hSp s hs).1) (fun s hs s' hs' => by rw [(hSp s hs).2.1, (hSp s' hs').2.1])
      (fun s hs => (hSp s hs).2.2.2)
      (by
        intro y hy s hs hne
        rw [sdiff_empty] at hy
        intro h
        apply hacc.2 y hy x hx (by rw [(hSp s hs).2.1] at hne; rw [hqx]; exact hne)
        rw [h, hxc])
    have := hmax _ (hSW ∅) f2 hf2.1 hf2.2
    simp only [card_empty, add_zero] at hcard
    omega
  have hD : V1.filter (fun x => f1 x = c ∧ q x ≠ p) = V1.filter (fun x => f1 x = c) := by
    apply Finset.filter_congr
    intro x hx
    exact ⟨fun h => h.1, fun h => ⟨h, hi x hx h⟩⟩
  rw [hD]
  obtain ⟨⟨f2, hf2⟩, hcard⟩ := C_mod (D := V1.filter (fun x => f1 x = c)) (S := S) hacc hF1
    (filter_subset _ _) hc (fun s hs => (hSp s hs).1)
    (fun s hs s' hs' => by rw [(hSp s hs).2.1, (hSp s' hs').2.1])
    (fun s hs => (hSp s hs).2.2.2)
    (by
      intro y hy s hs _ h
      rw [mem_sdiff, mem_filter] at hy
      exact hy.2 ⟨hy.1, h⟩)
  have := hmax _ (hSW _) f2 hf2.1 hf2.2
  omega

theorem C_phase2 {q : V → ℕ} {W : Finset V} {L : V → Finset ℕ} {F : Finset ℕ} (V1 : Finset V) :
    ∃ T ⊆ W.image q, ∃ φ : ℕ → ℕ,
      (∀ p ∈ T, φ p ∈ F ∧ ∀ v ∈ C_R q W V1 p, φ p ∈ L v) ∧ Set.InjOn φ T ∧
      (∀ p ∈ T, ∀ p' ∈ W.image q \ T, (C_R q W V1 p').card ≤ (C_R q W V1 p).card) ∧
      (T = W.image q ∨ ∃ Q ∈ W.image q \ T,
        (∀ p' ∈ W.image q \ T, (C_R q W V1 p').card ≤ (C_R q W V1 Q).card) ∧
        ∀ c ∈ F \ T.image φ, ∃ v ∈ C_R q W V1 Q, c ∉ L v) := by
  set Qs := W.image q with hQs
  obtain ⟨T, hT, hTmax⟩ := Finset.exists_max_image
    (Qs.powerset.filter (fun T : Finset ℕ => ∃ φ : ℕ → ℕ,
      (∀ p ∈ T, φ p ∈ F ∧ ∀ v ∈ C_R q W V1 p, φ p ∈ L v) ∧ Set.InjOn φ T ∧
      (∀ p ∈ T, ∀ p' ∈ Qs \ T, (C_R q W V1 p').card ≤ (C_R q W V1 p).card)))
    Finset.card ⟨∅, by simp⟩
  have hT' := hT
  rw [mem_filter, mem_powerset] at hT'
  obtain ⟨hTQ, φ, hφ1, hφ2, hφ3⟩ := hT'
  refine ⟨T, hTQ, φ, hφ1, hφ2, hφ3, ?_⟩
  by_cases hTe : T = Qs
  · left; exact hTe
  · right
    have hne : (Qs \ T).Nonempty := by
      rw [Finset.sdiff_nonempty]; intro h; exact hTe (Finset.Subset.antisymm hTQ h)
    obtain ⟨Q, hQ, hQmax⟩ := Finset.exists_max_image (Qs \ T) (fun p => (C_R q W V1 p).card) hne
    refine ⟨Q, hQ, hQmax, ?_⟩
    by_contra hcon
    push_neg at hcon
    obtain ⟨c, hc, hcall⟩ := hcon
    have hc' := mem_sdiff.1 hc
    have hQ' := mem_sdiff.1 hQ
    have hmem : insert Q T ∈ Qs.powerset.filter (fun T : Finset ℕ => ∃ φ : ℕ → ℕ,
      (∀ p ∈ T, φ p ∈ F ∧ ∀ v ∈ C_R q W V1 p, φ p ∈ L v) ∧ Set.InjOn φ T ∧
      (∀ p ∈ T, ∀ p' ∈ Qs \ T, (C_R q W V1 p').card ≤ (C_R q W V1 p).card)) := by
      rw [mem_filter, mem_powerset]
      refine ⟨insert_subset hQ'.1 hTQ, Function.update φ Q c, ?_, ?_, ?_⟩
      · intro p hp
        by_cases hpQ : p = Q
        · subst hpQ
          simp only [Function.update_self]
          exact ⟨hc'.1, hcall⟩
        · rw [Function.update_of_ne hpQ]
          exact hφ1 p ((mem_insert.1 hp).resolve_left hpQ)
      · intro a ha b hb hab
        simp only [coe_insert, Set.mem_insert_iff, mem_coe] at ha hb
        by_cases haQ : a = Q <;> by_cases hbQ : b = Q
        · rw [haQ, hbQ]
        · exfalso
          rw [haQ, Function.update_self, Function.update_of_ne hbQ] at hab
          exact hc'.2 (mem_image.2 ⟨b, hb.resolve_left hbQ, hab.symm⟩)
        · exfalso
          rw [hbQ, Function.update_self, Function.update_of_ne haQ] at hab
          exact hc'.2 (mem_image.2 ⟨a, ha.resolve_left haQ, hab⟩)
        · rw [Function.update_of_ne haQ, Function.update_of_ne hbQ] at hab
          exact hφ2 (ha.resolve_left haQ) (hb.resolve_left hbQ) hab
      · intro p hp p' hp'
        rw [mem_sdiff, mem_insert, not_or] at hp'
        by_cases hpQ : p = Q
        · subst hpQ
          exact hQmax p' (mem_sdiff.2 ⟨hp'.1, hp'.2.2⟩)
        · exact hφ3 p ((mem_insert.1 hp).resolve_left hpQ) p' (mem_sdiff.2 ⟨hp'.1, hp'.2.2⟩)
    have h1 := hTmax _ hmem
    rw [Finset.card_insert_of_notMem hQ'.2] at h1
    omega

theorem C_dc (s : Finset V) (t : Finset ℕ) (P : V → ℕ → Prop) [∀ v c, Decidable (P v c)] :
    ∑ v ∈ s, (t.filter (fun c => P v c)).card = ∑ c ∈ t, (s.filter (fun v => P v c)).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

theorem C_main {q : V → ℕ} {W : Finset V} {k : ℕ} {L : V → Finset ℕ} {F : Finset ℕ}
    (hW : W.card = 2 * k + 1) (hnp : (W.image q).card = k) (hLk : ∀ v ∈ W, k ≤ (L v).card)
    (hlt : (colours W L).card < W.card)
    (hinter : ∀ v ∈ W, 2 ≤ (partOf q W v).card → ∀ c, ∃ u ∈ partOf q W v, c ∉ L u)
    (hFk : F.card = k) (hFC : F ⊆ colours W L) (hFq : ∀ c ∈ F, Frequent q W k L c)
    (hno : ¬ ∃ f, NearAcc q W k L f)
    {V1 : Finset V} {f1 : V → ℕ} (hacc : Acc q V1 L f1) (hV1 : V1 ⊆ W)
    (hF1 : ∀ v ∈ V1, f1 v ∉ F)
    (hmax : ∀ V2 ⊆ W, ∀ f2, Acc q V2 L f2 → (∀ v ∈ V2, f2 v ∉ F) →
      V2.card < V1.card ∨ (V2.card = V1.card ∧ (V2.image q).card ≤ (V1.image q).card)) :
    False := by
  have h32 : ∀ {v : V}, v ∈ W → (partOf q W v).card = 2 → ∃ x ∈ V1, q x = q v :=
    fun {v} hv h2 => C_claim32 hW hnp hLk hlt hinter hFk hFC hFq hno hacc hV1 hF1 hmax hv h2
  obtain ⟨T, hTQ, φ, hφ1, hφ2, hφ3, hcase⟩ := C_phase2 (q := q) (W := W) (L := L) (F := F) V1
  have hφF : ∀ p ∈ T, φ p ∈ F := fun p hp => (hφ1 p hp).1
  have hφL : ∀ p ∈ T, ∀ v ∈ W \ V1, q v = p → φ p ∈ L v := fun p hp v hv h =>
    (hφ1 p hp).2 v (mem_filter.2 ⟨hv, h⟩)
  rcases hcase with hTe | ⟨Q, hQ, hQmax, hstuck⟩
  · apply hno
    refine C_assemble hFC hFq hacc hV1 hF1 hφF hφL hφ2 (ψ := fun _ => 0) ?_ ?_
    · intro v hv h
      exact absurd (by rw [hTe]; exact mem_image.2 ⟨v, (mem_sdiff.1 hv).1, rfl⟩) h
    · intro u hu v hv h
      exact absurd (by rw [hTe]; exact mem_image.2 ⟨u, (mem_sdiff.1 hu).1, rfl⟩) h
  have hQ' := mem_sdiff.1 hQ
  obtain ⟨r, hr⟩ : ∃ r, (C_R q W V1 Q).card = r := ⟨_, rfl⟩
  have hΩc : (W \ V1).card + V1.card = 2 * k + 1 := by
    rw [← hW]; exact Finset.card_sdiff_add_card_eq_card hV1
  have hik : T.card < k := by
    have h1 := Finset.card_le_card (insert_subset hQ'.1 hTQ)
    rw [Finset.card_insert_of_notMem hQ'.2, hnp] at h1; omega
  have himg : (T.image φ).card = T.card := Finset.card_image_of_injOn hφ2
  have himgF : T.image φ ⊆ F := by
    intro c hc; obtain ⟨p, hp, rfl⟩ := mem_image.1 hc; exact hφF p hp
  have hUc : (F \ T.image φ).card = k - T.card := by
    rw [Finset.card_sdiff_of_subset himgF, himg, hFk]
  have hQTc : (W.image q \ T).card = k - T.card := by
    rw [Finset.card_sdiff_of_subset hTQ, hnp]
  have hfib : (W \ V1).card = ∑ p ∈ W.image q, (C_R q W V1 p).card :=
    Finset.card_eq_sum_card_fiberwise (f := q)
      (fun x hx => mem_image.2 ⟨x, (mem_sdiff.1 hx).1, rfl⟩)
  have hsplit := Finset.sum_sdiff (f := fun p => (C_R q W V1 p).card) hTQ
  have hS2 : T.card * r ≤ ∑ p ∈ T, (C_R q W V1 p).card := by
    have := Finset.card_nsmul_le_sum T (fun p => (C_R q W V1 p).card) r
      (fun p hp => by rw [← hr]; exact hφ3 p hp Q hQ)
    simpa using this
  have hmaps : ∀ x ∈ (W \ V1).filter (fun v => q v ∉ T), q x ∈ W.image q \ T := by
    intro x hx
    rw [mem_filter] at hx
    exact mem_sdiff.2 ⟨mem_image.2 ⟨x, (mem_sdiff.1 hx.1).1, rfl⟩, hx.2⟩
  have hV3 : ((W \ V1).filter (fun v => q v ∉ T)).card =
      ∑ p ∈ W.image q \ T, (C_R q W V1 p).card := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    apply Finset.sum_congr rfl
    intro p hp
    have hpT := (mem_sdiff.1 hp).2
    congr 1
    ext x
    simp only [C_R, mem_filter]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by rw [h2]; exact hpT⟩, h2⟩
  by_cases hsmall : ((W \ V1).filter (fun v => q v ∉ T)).card ≤ k - T.card
  · apply hno
    obtain ⟨ψ, hψ1, hψ2⟩ := C_inj (s := (W \ V1).filter (fun v => q v ∉ T))
      (t := F \ T.image φ) (by rw [hUc]; exact hsmall)
    refine C_assemble hFC hFq hacc hV1 hF1 hφF hφL hφ2 (ψ := ψ) ?_ ?_
    · intro v hv h
      have := hψ1 v (mem_filter.2 ⟨hv, h⟩)
      exact ⟨(mem_sdiff.1 this).1, (mem_sdiff.1 this).2⟩
    · intro u hu v hv hu' hv' h
      exact Or.inl (hψ2 (mem_coe.2 (mem_filter.2 ⟨hu, hu'⟩))
        (mem_coe.2 (mem_filter.2 ⟨hv, hv'⟩)) h)
  push_neg at hsmall
  have hS3le : ∑ p ∈ W.image q \ T, (C_R q W V1 p).card ≤ (k - T.card) * r := by
    have := Finset.sum_le_card_nsmul (W.image q \ T) (fun p => (C_R q W V1 p).card) r
      (fun p hp => by rw [← hr]; exact hQmax p hp)
    rw [hQTc, smul_eq_mul] at this; exact this
  have hr2 : 2 ≤ r := by
    by_contra h2
    push_neg at h2
    have : (k - T.card) * r ≤ (k - T.card) * 1 := Nat.mul_le_mul_left _ (by omega)
    omega
  have hV1le : V1.card + T.card * r ≤ k + T.card := by omega
  have hcol : ∀ v ∈ W, L v ⊆ colours W L := fun v hv c hc => mem_biUnion.2 ⟨v, hv, hc⟩
  have hRQ : C_R q W V1 Q ⊆ W := fun z hz => (mem_sdiff.1 (mem_filter.1 hz).1).1
  have hm1 : ∀ x ∈ V1.filter (fun x => q x ≠ Q), f1 x ∈ colours W L \ F := by
    intro x hx
    have hx1 := (mem_filter.1 hx).1
    exact mem_sdiff.2 ⟨mem_biUnion.2 ⟨x, hV1 hx1, hacc.1 x hx1⟩, hF1 x hx1⟩
  have hstar : ∑ v ∈ C_R q W V1 Q, (L v \ F).card ≤ (V1.filter (fun x => q x ≠ Q)).card := by
    have e1 : ∀ v ∈ C_R q W V1 Q,
        (L v \ F).card = ((colours W L \ F).filter (fun c => c ∈ L v)).card := by
      intro v hv
      congr 1
      ext c
      simp only [mem_sdiff, mem_filter]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨hcol v (hRQ hv) h1, h2⟩, h1⟩
      · rintro ⟨⟨_, h2⟩, h1⟩; exact ⟨h1, h2⟩
    rw [Finset.sum_congr rfl e1]
    calc ∑ v ∈ C_R q W V1 Q, ((colours W L \ F).filter (fun c => c ∈ L v)).card
        = ∑ c ∈ colours W L \ F, ((C_R q W V1 Q).filter (fun v => c ∈ L v)).card :=
          C_dc (C_R q W V1 Q) (colours W L \ F) (fun v c => c ∈ L v)
      _ ≤ ∑ c ∈ colours W L \ F, (V1.filter (fun x => f1 x = c ∧ q x ≠ Q)).card :=
          Finset.sum_le_sum (fun c hc => C_keyK hacc hV1 hF1 hmax Q (mem_sdiff.1 hc).2)
      _ = (V1.filter (fun x => q x ≠ Q)).card := by
          refine Eq.trans ?_ (Finset.card_eq_sum_card_fiberwise hm1).symm
          apply Finset.sum_congr rfl
          intro c _
          congr 1
          ext x
          simp only [mem_filter]
          tauto
  have hss : (F \ T.image φ).card ≤ ∑ v ∈ C_R q W V1 Q, (L v \ F).card := by
    calc (F \ T.image φ).card = ∑ c ∈ F \ T.image φ, 1 := by simp
      _ ≤ ∑ c ∈ F \ T.image φ, ((C_R q W V1 Q).filter (fun v => c ∉ L v)).card := by
          apply Finset.sum_le_sum
          intro c hc
          obtain ⟨v, hv, hcv⟩ := hstuck c hc
          exact Finset.card_pos.2 ⟨v, mem_filter.2 ⟨hv, hcv⟩⟩
      _ ≤ ∑ c ∈ F, ((C_R q W V1 Q).filter (fun v => c ∉ L v)).card :=
          Finset.sum_le_sum_of_subset Finset.sdiff_subset
      _ = ∑ v ∈ C_R q W V1 Q, (F.filter (fun c => c ∉ L v)).card :=
          (C_dc (C_R q W V1 Q) F (fun v c => c ∉ L v)).symm
      _ ≤ ∑ v ∈ C_R q W V1 Q, (L v \ F).card := by
          apply Finset.sum_le_sum
          intro v hv
          have h1 := Finset.card_sdiff_add_card_inter (L v) F
          have h2 := Finset.card_sdiff_add_card_inter F (L v)
          have h3 : F.filter (fun c => c ∉ L v) = F \ L v := by ext c; simp [mem_sdiff]
          have h4 : F ∩ L v = L v ∩ F := Finset.inter_comm _ _
          rw [h3]
          rw [h4] at h2
          have := hLk v (hRQ hv)
          omega
  have hN1le : (V1.filter (fun x => q x ≠ Q)).card ≤ V1.card := Finset.card_le_card (filter_subset _ _)
  have hi2 : T.card * 2 ≤ T.card * r := Nat.mul_le_mul_left _ hr2
  have hV1k : V1.card = k - T.card := by omega
  have hN1eq : (V1.filter (fun x => q x ≠ Q)).card = V1.card := by omega
  have hfe : V1.filter (fun x => q x ≠ Q) = V1 :=
    Finset.eq_of_subset_of_card_le (filter_subset _ _) (by omega)
  have hnoQ : ∀ x ∈ V1, q x ≠ Q := by
    intro x hx; rw [← hfe] at hx; exact (mem_filter.1 hx).2
  obtain ⟨w, hw, hwQ⟩ := mem_image.1 hQ'.1
  have hpart : partOf q W w = C_R q W V1 Q := by
    ext z
    simp only [partOf, C_R, mem_filter, mem_sdiff]
    constructor
    · rintro ⟨hzW, hzq⟩
      exact ⟨⟨hzW, fun hzV => hnoQ z hzV (hzq.trans hwQ)⟩, hzq.trans hwQ⟩
    · rintro ⟨⟨hzW, _⟩, hzq⟩
      exact ⟨hzW, hzq.trans hwQ.symm⟩
  have hr3 : 3 ≤ r := by
    by_contra h3
    have hr2' : r = 2 := by omega
    obtain ⟨x, hx, hxq⟩ := h32 hw (by rw [hpart, hr, hr2'])
    exact hnoQ x hx (hxq.trans hwQ)
  have hi3 : T.card * 3 ≤ T.card * r := Nat.mul_le_mul_left _ hr3
  have hi0 : T.card = 0 := by omega
  have hT0 : T = ∅ := Finset.card_eq_zero.1 hi0
  subst hT0
  have hk0 : 0 < k := by omega
  simp only [card_empty, Nat.sub_zero] at hV1k hUc
  -- sum bound
  have hsum1 : r * k ≤ ∑ v ∈ C_R q W V1 Q, ((L v \ F).card + (L v ∩ F).card) := by
    have := Finset.card_nsmul_le_sum (C_R q W V1 Q) (fun v => (L v \ F).card + (L v ∩ F).card) k
      (fun v hv => by rw [Finset.card_sdiff_add_card_inter]; exact hLk v (hRQ hv))
    rw [hr, smul_eq_mul] at this; exact this
  rw [Finset.sum_add_distrib] at hsum1
  have hk3 : 3 * k ≤ r * k := Nat.mul_le_mul_right k hr3
  have hinterSum : 2 * k ≤ ∑ c ∈ F, ((C_R q W V1 Q).filter (fun v => c ∈ L v)).card := by
    have e2 : ∀ v ∈ C_R q W V1 Q, (L v ∩ F).card = (F.filter (fun c => c ∈ L v)).card := by
      intro v _
      rw [Finset.inter_comm, Finset.filter_mem_eq_inter]
    rw [← C_dc (C_R q W V1 Q) F (fun v c => c ∈ L v), ← Finset.sum_congr rfl e2]
    omega
  have hpig : ∃ c ∈ F, 1 < ((C_R q W V1 Q).filter (fun v => c ∈ L v)).card := by
    by_contra hcon
    push_neg at hcon
    have := Finset.sum_le_card_nsmul F (fun c => ((C_R q W V1 Q).filter (fun v => c ∈ L v)).card) 1
      hcon
    rw [hFk, smul_eq_mul] at this
    omega
  obtain ⟨c, hcF, hc1⟩ := hpig
  obtain ⟨u, hu, v', hv', huv⟩ := Finset.one_lt_card.1 hc1
  rw [mem_filter] at hu hv'
  have hΩk : (W \ V1).card = k + 1 := by omega
  have hsub2 : ({u, v'} : Finset V) ⊆ W \ V1 := by
    intro z hz
    rw [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact (mem_filter.1 hu.1).1
    · exact (mem_filter.1 hv'.1).1
  have hcard2 : (({u, v'} : Finset V)).card = 2 := Finset.card_pair huv
  obtain ⟨ψ0, hψ01, hψ02⟩ := C_inj (s := (W \ V1) \ {u, v'}) (t := F.erase c) (by
    rw [Finset.card_sdiff_of_subset hsub2, Finset.card_erase_of_mem hcF]; omega)
  apply hno
  refine C_assemble hFC hFq hacc hV1 hF1 hφF hφL hφ2
    (ψ := fun x => if x = u ∨ x = v' then c else ψ0 x) ?_ ?_
  · intro x hx _
    by_cases h : x = u ∨ x = v'
    · simp only [h, if_true]; simpa using hcF
    · simp only [h, if_false]
      have := hψ01 x (mem_sdiff.2 ⟨hx, by simpa using h⟩)
      simp only [Finset.image_empty, notMem_empty, not_false_eq_true, and_true]
      exact (mem_erase.1 this).2
  · intro x hx y hy _ _ hxy
    by_cases h1 : x = u ∨ x = v' <;> by_cases h2 : y = u ∨ y = v'
    · by_cases hxy' : x = y
      · exact Or.inl hxy'
      · right
        have hqx : q x = Q := by rcases h1 with rfl | rfl; exact (mem_filter.1 hu.1).2; exact (mem_filter.1 hv'.1).2
        have hqy : q y = Q := by rcases h2 with rfl | rfl; exact (mem_filter.1 hu.1).2; exact (mem_filter.1 hv'.1).2
        have hcx : c ∈ L x := by rcases h1 with rfl | rfl; exact hu.2; exact hv'.2
        have hcy : c ∈ L y := by rcases h2 with rfl | rfl; exact hu.2; exact hv'.2
        simp only [h2, if_true]
        exact ⟨hqx.trans hqy.symm, hcx, hcy⟩
    · simp only [h1, h2, if_true, if_false] at hxy
      have := hψ01 y (mem_sdiff.2 ⟨hy, by simpa using h2⟩)
      exact absurd hxy.symm (mem_erase.1 this).1
    · simp only [h1, h2, if_true, if_false] at hxy
      have := hψ01 x (mem_sdiff.2 ⟨hx, by simpa using h1⟩)
      exact absurd hxy (mem_erase.1 this).1
    · simp only [h1, h2, if_false] at hxy
      exact Or.inl (hψ02 (mem_coe.2 (mem_sdiff.2 ⟨hx, by simpa using h1⟩))
        (mem_coe.2 (mem_sdiff.2 ⟨hy, by simpa using h2⟩)) hxy)

section core
variable {q : V → ℕ} {W : Finset V} {k : ℕ} {L : V → Finset ℕ}


theorem exists_near_acc (hIH : IH q W.card) (hp : nParts q W = k) (hc : W.card ≤ 2 * k + 1)
    (hb : Bad q W k L) (F : Finset ℕ) (hF : F.card = k) (hFC : F ⊆ colours W L)
    (hFq : ∀ c ∈ F, Frequent q W k L c) : ∃ f, NearAcc q W k L f := by
  by_contra hno
  have hW := card_eq_two_mul_add_one hIH hp hc hb
  have hlt := colours_lt_card hIH hp hc hb
  obtain ⟨V1, hV1, ⟨f1, hacc, hF1⟩, hbest⟩ := C_best q W
    (fun V1 => ∃ f1 : V → ℕ, Acc q V1 L f1 ∧ ∀ v ∈ V1, f1 v ∉ F)
    ⟨fun _ => 0, ⟨by simp, by simp⟩, by simp⟩
  exact C_main hW hp hb.1 hlt (fun v hv h2 c => part_inter_empty hIH hp hc hb hv h2 c) hF hFC hFq
    hno hacc hV1 hF1 (fun V2 h2 f2 hf2 hF2 => hbest V2 h2 ⟨f2, hf2, hF2⟩)

theorem few_frequent (hIH : IH q W.card) (hp : nParts q W = k) (hc : W.card ≤ 2 * k + 1)
    (hb : Bad q W k L) : ((colours W L).filter (Frequent q W k L)).card < k := by
  by_contra h
  push_neg at h
  obtain ⟨F, hFs, hFk⟩ := Finset.exists_subset_card_eq h
  exact near_acc_imp_colourable hIH hp hc hb
    (exists_near_acc hIH hp hc hb F hFk (fun c hc => (mem_filter.1 (hFs hc)).1)
      (fun c hc => (mem_filter.1 (hFs hc)).2))

theorem C3_singleton_eq {v u : V} (hv : v ∈ singletons q W) (hu : u ∈ W) (hq : q u = q v) : u = v := by
  have h1 := mem_filter.1 hv
  obtain ⟨a, ha⟩ := card_eq_one.1 h1.2
  have hv' : v ∈ partOf q W v := mem_filter.2 ⟨h1.1, rfl⟩
  have hu' : u ∈ partOf q W v := mem_filter.2 ⟨hu, hq⟩
  rw [ha, mem_singleton] at hv' hu'
  rw [hu', hv']

theorem C3_greedy (S : Finset V) (M : V → Finset ℕ) (h : ∀ v ∈ S, S.card ≤ (M v).card) :
    ∃ c : V → ℕ, Set.InjOn c ↑S ∧ ∀ v ∈ S, c v ∈ M v := by
  have key : ∀ s : Finset (S : Finset V), s.card ≤ (s.biUnion (fun v => M v.1)).card := by
    intro s
    rcases s.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
    · simp
    · have h1 : s.card ≤ S.card := by
        have := card_le_univ s
        simpa using this
      have h2 : (M v.1).card ≤ (s.biUnion fun v => M v.1).card :=
        card_le_card (subset_biUnion_of_mem (fun v : (S : Finset V) => M v.1) hv)
      exact h1.trans ((h v.1 v.2).trans h2)
  obtain ⟨f, hinj, hf⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective (fun v : (S : Finset V) => M v.1)).1 key
  refine ⟨fun v => if hv : v ∈ S then f ⟨v, hv⟩ else 0, ?_, ?_⟩
  · intro x hx y hy hxy
    have hx' : x ∈ S := hx
    have hy' : y ∈ S := hy
    simp only [hx', hy', dite_true] at hxy
    exact congrArg Subtype.val (hinj hxy)
  · intro v hv
    simp only [hv, dite_true]
    exact hf ⟨v, hv⟩

theorem C3_card_sing_le (hp : nParts q W = k) : (singletons q W).card ≤ k := by
  rw [← hp]
  apply card_le_card_of_injOn q
  · intro x hx
    exact mem_image_of_mem q (mem_filter.1 hx).1
  · intro x hx y hy hxy
    exact (C3_singleton_eq hx (mem_filter.1 hy).1 hxy.symm).symm

theorem C3_avail_le (hIH : IH q W.card) (hp : nParts q W = k) (hc : W.card ≤ 2 * k + 1)
    (hb : Bad q W k L) (c : ℕ) :
    (avail W L c).card + (k - (singletons q W).card) ≤ W.card := by
  have hsub : singletons q W ⊆ W := filter_subset _ _
  have hdisj : Disjoint ((singletons q W).image q) ((W \ singletons q W).image q) := by
    rw [disjoint_left]
    intro p hp1 hp2
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hp1
    obtain ⟨v, hv, hvq⟩ := mem_image.1 hp2
    obtain ⟨hvW, hvs⟩ := mem_sdiff.1 hv
    exact hvs (C3_singleton_eq hx hvW hvq ▸ hx)
  have hunion : W.image q = (singletons q W).image q ∪ (W \ singletons q W).image q := by
    rw [← image_union, union_sdiff_of_subset hsub]
  have hcard1 : ((singletons q W).image q).card = (singletons q W).card := by
    apply card_image_of_injOn
    intro x hx y hy hxy
    exact (C3_singleton_eq hx (mem_filter.1 hy).1 hxy.symm).symm
  have hP1 : k - (singletons q W).card ≤ ((W \ singletons q W).image q).card := by
    have h1 : (W.image q).card = k := hp
    rw [hunion, card_union_of_disjoint hdisj, hcard1] at h1
    omega
  have h3 := card_sdiff_add_card_eq_card (filter_subset (fun v => c ∈ L v) W)
  change (W \ avail W L c).card + (avail W L c).card = W.card at h3
  suffices hs : k - (singletons q W).card ≤ (W \ avail W L c).card by omega
  refine hP1.trans ?_
  rcases ((W \ singletons q W).image q).eq_empty_or_nonempty with he | ⟨p0, hp0⟩
  · rw [he]; simp
  · obtain ⟨v0, _, _⟩ := mem_image.1 hp0
    haveI : Nonempty V := ⟨v0⟩
    have hch : ∀ p, ∃ u : V, p ∈ (W \ singletons q W).image q → (u ∈ W ∧ q u = p ∧ c ∉ L u) := by
      intro p
      by_cases hpm : p ∈ (W \ singletons q W).image q
      · obtain ⟨v, hv, rfl⟩ := mem_image.1 hpm
        obtain ⟨hvW, hvs⟩ := mem_sdiff.1 hv
        have h2 : 2 ≤ (partOf q W v).card := by
          have hpos : 0 < (partOf q W v).card :=
            card_pos.2 ⟨v, mem_filter.2 ⟨hvW, rfl⟩⟩
          have hne : (partOf q W v).card ≠ 1 := fun e => hvs (mem_filter.2 ⟨hvW, e⟩)
          omega
        obtain ⟨u, hu, hcu⟩ := part_inter_empty hIH hp hc hb hvW h2 c
        obtain ⟨huW, huq⟩ := mem_filter.1 hu
        exact ⟨u, fun _ => ⟨huW, huq, hcu⟩⟩
      · exact ⟨v0, fun h => absurd h hpm⟩
    choose u hu using hch
    apply card_le_card_of_injOn u
    · intro p hpm
      obtain ⟨h1, h2, h3⟩ := hu p hpm
      exact mem_sdiff.2 ⟨h1, fun hm => h3 (mem_filter.1 hm).2⟩
    · intro p hpm p' hpm' e
      rw [← (hu p hpm).2.1, ← (hu p' hpm').2.1, e]

theorem many_singletons (hIH : IH q W.card) (hp : nParts q W = k) (hc : W.card ≤ 2 * k + 1)
    (hb : Bad q W k L) : gam W L ≤ (singletons q W).card := by
  by_contra hlt'
  rw [not_le] at hlt'
  have hW := card_eq_two_mul_add_one hIH hp hc hb
  have hF := few_frequent hIH hp hc hb
  have hlt := colours_lt_card hIH hp hc hb
  have hsk := C3_card_sing_le (q := q) (W := W) hp
  have hLC : ∀ v ∈ W, L v ⊆ colours W L := fun v hv => subset_biUnion_of_mem L hv
  set s := (singletons q W).card with hs
  set F' := (colours W L).filter (fun c => k + 1 ≤ (avail W L c).card) with hF'
  have hdc : ∑ v ∈ W, (L v).card = ∑ c ∈ colours W L, (avail W L c).card := by
    have := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := W) (t := colours W L)
      (fun v c => c ∈ L v)
    refine Eq.trans ?_ this
    apply sum_congr rfl
    intro v hv
    congr 1
    ext c
    simp only [Finset.bipartiteAbove, mem_filter]
    exact ⟨fun h => ⟨hLC v hv h, h⟩, fun h => h.2⟩
  have h1 : W.card * k ≤ ∑ v ∈ W, (L v).card := by
    have : ∑ v ∈ W, k ≤ ∑ v ∈ W, (L v).card := sum_le_sum (fun v hv => hb.1 v hv)
    rw [sum_const, smul_eq_mul] at this
    exact this
  have h2 : ∑ c ∈ colours W L, (avail W L c).card ≤
      ∑ c ∈ colours W L, (k + if c ∈ F' then s + 1 else 0) := by
    apply sum_le_sum
    intro c hcC
    have hav := C3_avail_le hIH hp hc hb c
    by_cases hcF : c ∈ F'
    · rw [if_pos hcF]; omega
    · rw [if_neg hcF]
      have : ¬ (k + 1 ≤ (avail W L c).card) := fun h => hcF (mem_filter.2 ⟨hcC, h⟩)
      omega
  rw [sum_add_distrib, sum_const, smul_eq_mul] at h2
  have h3 : ∑ c ∈ colours W L, (if c ∈ F' then s + 1 else 0) = F'.card * (s + 1) := by
    rw [← sum_filter]
    have : (colours W L).filter (fun c => c ∈ F') = F' := by
      ext c; simp only [mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨(mem_filter.1 h).1, h⟩⟩
    rw [this, sum_const, smul_eq_mul]
  rw [h3] at h2
  have hF'F : F'.card ≤ ((colours W L).filter (Frequent q W k L)).card := by
    apply card_le_card
    intro c hcm
    obtain ⟨h1, h2⟩ := mem_filter.1 hcm
    exact mem_filter.2 ⟨h1, Or.inl h2⟩
  have hgam : gam W L = W.card - (colours W L).card := rfl
  have e1 : k * gam W L ≤ (s + 1) * F'.card := by
    have : W.card = (colours W L).card + gam W L := by omega
    have h4 : W.card * k ≤ (colours W L).card * k + F'.card * (s + 1) := by omega
    rw [this] at h4
    nlinarith
  have e2 : (s + 1) * k ≤ (s + 1) * F'.card := by
    have : (s + 1) * k ≤ k * gam W L := by nlinarith
    omega
  have e3 : k ≤ F'.card := Nat.le_of_mul_le_mul_left e2 (by omega)
  omega

theorem C3_recolour (S : Finset V) (Ab R : Finset ℕ) (c : V → ℕ) (Lx : V → Finset ℕ)
    (hc1 : Set.InjOn c ↑S) (hc3 : ∀ x ∈ S, c x ∉ Ab)
    (hc2 : ∀ x ∈ S, c x ∈ Lx x) (hAb : ∀ x ∈ S, Ab ⊆ Lx x)
    (hR : R ⊆ Ab ∪ S.image c) (hRc : R.card = S.card) :
    ∃ ρ : V → ℕ, Set.InjOn ρ ↑S ∧ ∀ x ∈ S, ρ x ∈ Lx x ∧ ρ x ∈ R := by
  set S1 := S.filter (fun x => c x ∈ R) with hS1
  set S2 := S.filter (fun x => c x ∉ R) with hS2
  set R2 := R ∩ Ab with hR2
  have h12 : S1.card + S2.card = S.card := card_filter_add_card_filter_not _
  have hRs : (R \ Ab).card + R2.card = R.card := card_sdiff_add_card_inter R Ab
  have hRAb : (R \ Ab).card ≤ S1.card := by
    refine le_trans (card_le_card (t := S1.image c) ?_) card_image_le
    intro r hr
    obtain ⟨hrR, hrA⟩ := mem_sdiff.1 hr
    rcases mem_union.1 (hR hrR) with h | h
    · exact absurd h hrA
    · obtain ⟨x, hx, rfl⟩ := mem_image.1 h
      exact mem_image_of_mem c (mem_filter.2 ⟨hx, hrR⟩)
  have hle : S2.card ≤ R2.card := by omega
  obtain ⟨φ, hφ1, hφ2⟩ := C3_greedy S2 (fun _ => R2) (fun v _ => hle)
  refine ⟨fun x => if c x ∈ R then c x else φ x, ?_, ?_⟩
  · intro x hx y hy hxy
    have hx' : x ∈ S := hx
    have hy' : y ∈ S := hy
    by_cases hcx : c x ∈ R <;> by_cases hcy : c y ∈ R
    · simp only [hcx, hcy, if_true] at hxy
      exact hc1 hx hy hxy
    · simp only [hcx, hcy, if_true, if_false] at hxy
      have hy2 : y ∈ S2 := mem_filter.2 ⟨hy', hcy⟩
      have := (mem_inter.1 (hφ2 y hy2)).2
      exact absurd (hxy ▸ this) (hc3 x hx')
    · simp only [hcx, hcy, if_true, if_false] at hxy
      have hx2 : x ∈ S2 := mem_filter.2 ⟨hx', hcx⟩
      have := (mem_inter.1 (hφ2 x hx2)).2
      exact absurd (hxy ▸ this) (hc3 y hy')
    · simp only [hcx, hcy, if_false] at hxy
      exact hφ1 (mem_coe.2 (mem_filter.2 ⟨hx', hcx⟩)) (mem_coe.2 (mem_filter.2 ⟨hy', hcy⟩)) hxy
  · intro x hx
    beta_reduce
    by_cases hcx : c x ∈ R
    · rw [if_pos hcx]; exact ⟨hc2 x hx, hcx⟩
    · rw [if_neg hcx]
      have := mem_inter.1 (hφ2 x (mem_filter.2 ⟨hx, hcx⟩))
      exact ⟨hAb x hx this.2, this.1⟩

theorem frequent_lt_b (hIH : IH q W.card) (hp : nParts q W = k) (hc : W.card ≤ 2 * k + 1)
    (hm : MaxBad q W k L) :
    ((colours W L).filter (Frequent q W k L)).card < k - (singletons q W).card := by
  by_contra hcon
  rw [not_lt] at hcon
  have hb := hm.1
  have hlt := colours_lt_card hIH hp hc hb
  have hms := many_singletons hIH hp hc hb
  have hsk := C3_card_sing_le (q := q) (W := W) hp
  have hgam1 : 1 ≤ gam W L := by unfold gam; omega
  have hSW : singletons q W ⊆ W := filter_subset _ _
  obtain ⟨Ab, hAbs, hAbc⟩ := exists_subset_card_eq hcon
  have hAbL : ∀ x ∈ singletons q W, Ab ⊆ L x := fun x hx c hc' =>
    frequent_mem_singleton hIH hp hc hm (mem_filter.1 (hAbs hc')).2 hx
  obtain ⟨cc, hcc1, hcc2⟩ := C3_greedy (singletons q W) (fun x => L x \ Ab) (fun x hx => by
    have h1 := le_card_sdiff Ab (L x)
    have h2 := hb.1 x (hSW hx)
    omega)
  have hcc3 : ∀ x ∈ singletons q W, cc x ∉ Ab := fun x hx h => (mem_sdiff.1 (hcc2 x hx)).2 h
  have hcc4 : ∀ x ∈ singletons q W, cc x ∈ L x := fun x hx => (mem_sdiff.1 (hcc2 x hx)).1
  set A := Ab ∪ (singletons q W).image cc with hA
  have hAcard : A.card = k := by
    have hd : Disjoint Ab ((singletons q W).image cc) := by
      rw [disjoint_right]
      intro a ha
      obtain ⟨x, hx, rfl⟩ := mem_image.1 ha
      exact hcc3 x hx
    rw [hA, card_union_of_disjoint hd, card_image_of_injOn hcc1]
    omega
  obtain ⟨L', hL'⟩ : ∃ L' : V → Finset ℕ, ∀ v, L' v = if v ∈ singletons q W then A else L v :=
    ⟨_, fun _ => rfl⟩
  have hL's : ∀ v ∈ singletons q W, L' v = A := fun v hv => by rw [hL', if_pos hv]
  have hL'n : ∀ v, v ∉ singletons q W → L' v = L v := fun v hv => by rw [hL', if_neg hv]
  have hL'1 : ∀ v ∈ W, k ≤ (L' v).card := by
    intro v hv
    by_cases hvs : v ∈ singletons q W
    · rw [hL's v hvs, hAcard]
    · rw [hL'n v hvs]; exact hb.1 v hv
  have hcol : Colourable q W L' := by
    by_contra hnc
    have hb' : Bad q W k L' := ⟨hL'1, hnc⟩
    have hms' := many_singletons hIH hp hc hb'
    have hne : (singletons q W).Nonempty := card_pos.1 (by omega)
    obtain ⟨x0, hx0⟩ := hne
    have hAC : A ⊆ colours W L' := fun c hcA =>
      mem_biUnion.2 ⟨x0, hSW hx0, by rw [hL's x0 hx0]; exact hcA⟩
    refine near_acc_imp_colourable hIH hp hc hb' (exists_near_acc hIH hp hc hb' A hAcard hAC
      (fun c hcA => Or.inr ?_))
    have : ((singletons q W).filter fun v => c ∈ L' v) = singletons q W :=
      filter_true_of_mem (fun x hx => by rw [hL's x hx]; exact hcA)
    rw [this]; exact hms'
  obtain ⟨f', hf1, hf2⟩ := hcol
  have hnonS : ∀ v ∈ W, v ∉ singletons q W → ∀ x ∈ singletons q W, f' v ≠ f' x := by
    intro v hv hvn x hx
    apply hf2 v hv x (hSW hx)
    intro e
    exact hvn (C3_singleton_eq hx hv e ▸ hx)
  have hinj : Set.InjOn f' ↑(singletons q W) := by
    intro x hx y hy e
    by_contra hne
    exact hf2 x (hSW hx) y (hSW hy) (fun e' => hne (C3_singleton_eq hy (hSW hx) e')) e
  have hRc : ((singletons q W).image f').card = (singletons q W).card := card_image_of_injOn hinj
  have hRA : (singletons q W).image f' ⊆ Ab ∪ (singletons q W).image cc := by
    intro r hr
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hr
    have := hf1 x (hSW hx)
    rw [hL's x hx] at this
    exact this
  obtain ⟨ρ, hρ1, hρ2⟩ := C3_recolour (singletons q W) Ab ((singletons q W).image f') cc L hcc1
    hcc3 hcc4 hAbL hRA hRc
  apply hb.2
  refine ⟨fun v => if v ∈ singletons q W then ρ v else f' v, fun v hv => ?_, fun u hu v hv huv => ?_⟩
  · by_cases hvs : v ∈ singletons q W
    · simp only [hvs, if_true]; exact (hρ2 v hvs).1
    · simp only [hvs, if_false]
      have := hf1 v hv
      rwa [hL'n v hvs] at this
  · by_cases hus : u ∈ singletons q W <;> by_cases hvs : v ∈ singletons q W
    · simp only [hus, hvs, if_true]
      intro e
      exact huv (by rw [hρ1 (mem_coe.2 hus) (mem_coe.2 hvs) e])
    · simp only [hus, hvs, if_true, if_false]
      intro e
      obtain ⟨x, hx, hxe⟩ := mem_image.1 (hρ2 u hus).2
      exact hnonS v hv hvs x hx (by rw [hxe, ← e])
    · simp only [hus, hvs, if_true, if_false]
      intro e
      obtain ⟨x, hx, hxe⟩ := mem_image.1 (hρ2 v hvs).2
      exact hnonS u hu hus x hx (by rw [hxe, e])
    · simp only [hus, hvs, if_false]
      exact hf2 u hu v hv huv



theorem C2_ar1 (k b g f : ℤ) (h0 : 0 ≤ f) (hf : f + 1 ≤ b) (h48 : 2 * b ≤ k + 1) (hg : 0 ≤ g)
    (hineq : k * (2 * k + 1) ≤ (2 * k + 1 - g - f) * k + f * (2 * k + 1 - b)) :
    2 * g < k + 1 - b := by
  by_contra h
  push_neg at h
  have hk : 1 ≤ k := by linarith
  have h1 : g * k ≤ f * (k + 1 - b) := by nlinarith
  have h2 : (k + 1 - b) * k ≤ 2 * g * k := by nlinarith
  have h3 : 2 * f ≤ k - 1 := by linarith
  have h4 : 0 < k + 1 - b := by linarith
  nlinarith [mul_le_mul_of_nonneg_left h3 h4.le]

theorem C2_ar2 (k b g f m : ℤ) (h0 : 0 ≤ f) (hf : f + 1 ≤ b) (hm0 : 0 ≤ m) (hmk : m ≤ k)
    (hgb : g + b ≤ k) (h48 : 2 * b ≤ k + 1) (hg : 0 ≤ g) (h42 : 2 * g < k + 1 - b)
    (hineq : k * (2 * k + 1) ≤ (2 * k + 1 - g - f) * m + f * (2 * k + 1 - b)) :
    2 * (k - m) < k + 1 - b - 2 * g := by
  have hE : (2 * k + 1 - g - f) * m + f * (2 * k + 1 - b) ≤
      (2 * k + 2 - g - b) * m + (b - 1) * (2 * k + 1 - b) := by
    nlinarith [mul_nonneg (show (0:ℤ) ≤ b - 1 - f by linarith) (show (0:ℤ) ≤ 2 * k + 1 - b - m by linarith)]
  by_contra h
  push_neg at h
  have hD : 0 < 2 * k + 2 - g - b := by linarith
  have h1 : (2 * k + 2 - g - b) * (2 * (k - m)) ≤ 2 * ((b - 1) * (k + 1 - b) - k * g) := by
    nlinarith
  have h2 : (2 * k + 2 - g - b) * (k + 1 - b - 2 * g) ≤ (2 * k + 2 - g - b) * (2 * (k - m)) :=
    mul_le_mul_of_nonneg_left h hD.le
  have h3 : 2 * (b - 1) * (k + 1 - b) ≤ (k - 1) * (k + 1 - b) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h5 : 0 < k + 1 - b - 2 * g := by linarith
  nlinarith [mul_pos h5 (show (0:ℤ) < 2 * k + 2 - g - b - k by linarith)]

theorem C2_ar3 (k b g x N d m : ℤ) (h42 : 2 * g < k + 1 - b)
    (h413 : 2 * (k - m) < k + 1 - b - 2 * g) (hg1 : 1 ≤ g) (hx : k + 1 - b - g ≤ x)
    (hN : N + m ≤ 2 * k) (hd : d ≤ b - 1) (hmk : m ≤ k)
    (hineq : x * (k - d) ≤ (N - d) * (g - 1)) : False := by
  have ht : 0 < k + 1 - b - 2 * g := by linarith
  have hxg : 0 < x - g + 1 := by linarith
  have h1 : d * (x - g + 1) ≤ (b - 1) * (x - g + 1) :=
    mul_le_mul_of_nonneg_right hd hxg.le
  have h2 : (N - k + (k + 1 - b)) * (g - 1) ≤ (k - m + (k + 1 - b)) * (g - 1) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h3 : x * (k + 1 - b) ≤ (k - m + (k + 1 - b)) * (g - 1) := by nlinarith
  have h4 : (k + 1 - b - g) * (k + 1 - b) ≤ x * (k + 1 - b) :=
    mul_le_mul_of_nonneg_right hx (by linarith)
  nlinarith [mul_pos (show (0:ℤ) < g by linarith) ht, mul_nonneg (show (0:ℤ) ≤ k - m by linarith) (show (0:ℤ) ≤ g - 1 by linarith)]

theorem C2_double (W : Finset V) (L : V → Finset ℕ) :
    ∑ v ∈ W, (L v).card = ∑ c ∈ colours W L, (avail W L c).card := by
  have := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := W) (t := colours W L)
    (fun v c => c ∈ L v)
  refine (sum_congr rfl ?_).trans (this.trans (sum_congr rfl ?_))
  · intro v hv
    congr 1
    ext c
    simp only [Finset.bipartiteAbove, mem_filter, colours, mem_biUnion]
    constructor
    · intro h; exact ⟨⟨v, hv, h⟩, h⟩
    · intro h; exact h.2
  · intro c _
    rfl

theorem C2_count {W : Finset V} {k : ℕ} {L : V → Finset ℕ} (F : Finset ℕ)
    (hF : F ⊆ colours W L) (M T : ℕ)
    (hM : ∀ c ∈ colours W L \ F, (avail W L c).card ≤ M)
    (hT : ∀ c ∈ F, (avail W L c).card ≤ T)
    (hL : ∀ v ∈ W, k ≤ (L v).card) :
    k * W.card ≤ ((colours W L).card - F.card) * M + F.card * T := by
  have h1 : k * W.card ≤ ∑ v ∈ W, (L v).card := by
    calc k * W.card = ∑ v ∈ W, k := by simp [mul_comm]
      _ ≤ _ := sum_le_sum hL
  rw [C2_double, ← sum_sdiff hF] at h1
  have a1 : ∑ c ∈ colours W L \ F, (avail W L c).card ≤ ∑ c ∈ colours W L \ F, M :=
    sum_le_sum hM
  have a2 : ∑ c ∈ F, (avail W L c).card ≤ ∑ c ∈ F, T := sum_le_sum hT
  simp only [sum_const, smul_eq_mul, card_sdiff_of_subset hF] at a1 a2
  linarith

theorem C2_split (q : V → ℕ) (W : Finset V) :
    ((W \ singletons q W).image q).card + (singletons q W).card = nParts q W := by
  have hdis : Disjoint ((W \ singletons q W).image q) ((singletons q W).image q) := by
    rw [disjoint_left]
    intro p hp1 hp2
    obtain ⟨u, hu, rfl⟩ := mem_image.1 hp1
    obtain ⟨w, hw, hwq⟩ := mem_image.1 hp2
    have hu' := mem_sdiff.1 hu
    have hwS := mem_filter.1 hw
    obtain ⟨a, ha⟩ := card_eq_one.1 hwS.2
    have h1 : u ∈ partOf q W w := mem_filter.2 ⟨hu'.1, hwq.symm⟩
    have h2 : w ∈ partOf q W w := mem_filter.2 ⟨hwS.1, rfl⟩
    rw [ha] at h1 h2
    have : u = w := (mem_singleton.1 h1).trans (mem_singleton.1 h2).symm
    exact hu'.2 (this ▸ hw)
  have hunion : (W \ singletons q W).image q ∪ (singletons q W).image q = W.image q := by
    rw [← image_union, sdiff_union_of_subset (show singletons q W ⊆ W from filter_subset _ _)]
  have hinj : Set.InjOn q (singletons q W) := by
    intro u hu w hw huw
    have hu' := mem_filter.1 (mem_coe.1 hu)
    have hw' := mem_filter.1 (mem_coe.1 hw)
    obtain ⟨a, ha⟩ := card_eq_one.1 hu'.2
    have h1 : w ∈ partOf q W u := mem_filter.2 ⟨hw'.1, huw.symm⟩
    have h2 : u ∈ partOf q W u := mem_filter.2 ⟨hu'.1, rfl⟩
    rw [ha] at h1 h2
    exact (mem_singleton.1 h2).trans (mem_singleton.1 h1).symm
  unfold nParts
  rw [← hunion, card_union_of_disjoint hdis, card_image_of_injOn hinj]

theorem C2_avail_le {q : V → ℕ} {W : Finset V} {L : V → Finset ℕ}
    (hpart : ∀ v ∈ W, 2 ≤ (partOf q W v).card → ∀ c, ∃ u ∈ partOf q W v, c ∉ L u) (c : ℕ) :
    (avail W L c).card + ((W \ singletons q W).image q).card ≤ W.card := by
  have hsub : (W \ singletons q W).image q ⊆ (W \ avail W L c).image q := by
    intro p hp
    obtain ⟨v, hv, rfl⟩ := mem_image.1 hp
    have hv' := mem_sdiff.1 hv
    have hpos : 0 < (partOf q W v).card := card_pos.2 ⟨v, mem_filter.2 ⟨hv'.1, rfl⟩⟩
    have h2 : 2 ≤ (partOf q W v).card := by
      by_contra h
      apply hv'.2
      exact mem_filter.2 ⟨hv'.1, by omega⟩
    obtain ⟨u, hu, hcu⟩ := hpart v hv'.1 h2 c
    have hu' := mem_filter.1 hu
    exact mem_image.2 ⟨u, mem_sdiff.2 ⟨hu'.1, fun h => hcu (mem_filter.1 h).2⟩, hu'.2⟩
  have h1 := card_le_card hsub
  have h2 := card_image_le (s := W \ avail W L c) (f := q)
  have h3 : (W \ avail W L c).card = W.card - (avail W L c).card :=
    card_sdiff_of_subset (filter_subset _ _)
  have h4 : (avail W L c).card ≤ W.card := card_le_card (filter_subset _ _)
  omega

theorem C2_three_mul_le (q : V → ℕ) (W : Finset V) (hP : ∀ v ∈ W, 3 ≤ (partOf q W v).card) :
    3 * nParts q W ≤ W.card := by
  rw [card_eq_sum_card_image q W]
  have : (W.image q).card • 3 ≤ ∑ b ∈ W.image q, (W.filter fun a => q a = b).card := by
    apply card_nsmul_le_sum
    intro b hb
    obtain ⟨v, hv, rfl⟩ := mem_image.1 hb
    exact hP v hv
  unfold nParts
  simp only [smul_eq_mul] at this
  omega

theorem C2_three {q : V → ℕ} {W : Finset V} (hno2 : ∀ v ∈ W, (partOf q W v).card ≠ 2) :
    3 * ((W \ singletons q W).image q).card + (singletons q W).card ≤ W.card := by
  have h3 : ∀ v ∈ W \ singletons q W, 3 ≤ (partOf q (W \ singletons q W) v).card := by
    intro v hv
    have hv' := mem_sdiff.1 hv
    have hpos : 0 < (partOf q W v).card := card_pos.2 ⟨v, mem_filter.2 ⟨hv'.1, rfl⟩⟩
    have hn1 : (partOf q W v).card ≠ 1 := fun h => hv'.2 (mem_filter.2 ⟨hv'.1, h⟩)
    have hn2 := hno2 v hv'.1
    have hsub : partOf q W v ⊆ partOf q (W \ singletons q W) v := by
      intro u hu
      have hu' := mem_filter.1 hu
      have hset : partOf q W u = partOf q W v := by
        ext x
        simp only [partOf, mem_filter, hu'.2]
      refine mem_filter.2 ⟨mem_sdiff.2 ⟨hu'.1, fun hs => ?_⟩, hu'.2⟩
      have := (mem_filter.1 hs).2
      rw [hset] at this
      exact hn1 this
    have := card_le_card hsub
    omega
  have := C2_three_mul_le q (W \ singletons q W) h3
  have h4 : (W \ singletons q W).card + (singletons q W).card = W.card := by
    have hsS : singletons q W ⊆ W := filter_subset _ _
    rw [card_sdiff_of_subset hsS]
    have := card_le_card hsS
    omega
  unfold nParts at this
  omega

theorem C2_no_two (hIH : IH q W.card) (hp : nParts q W = k) (hc : W.card ≤ 2 * k + 1)
    (hm : MaxBad q W k L) : ∀ v ∈ W, (partOf q W v).card ≠ 2 := by
  intro v hv h2
  have hb := hm.1
  obtain ⟨x, y, hxy, hxyP⟩ := card_eq_two.1 h2
  have hx : x ∈ partOf q W v := by rw [hxyP]; simp
  have hy : y ∈ partOf q W v := by rw [hxyP]; simp
  have hxW : x ∈ W := (mem_filter.1 hx).1
  have hyW : y ∈ W := (mem_filter.1 hy).1
  have hd : Disjoint (L x) (L y) := by
    rw [disjoint_left]
    intro c hcx hcy
    obtain ⟨u, hu, hcu⟩ := part_inter_empty hIH hp hc hb hv (by omega) c
    rw [hxyP] at hu
    rcases mem_insert.1 hu with rfl | hu
    · exact hcu hcx
    · rw [mem_singleton.1 hu] at hcu; exact hcu hcy
  have hCk := (A_disjoint_lists hIH hp hc hb hxW hyW hd).2
  have hW := card_eq_two_mul_add_one hIH hp hc hb
  have hgam : gam W L = 1 := by unfold gam; omega
  have hms := many_singletons hIH hp hc hb
  obtain ⟨v0, hv0⟩ : (singletons q W).Nonempty := card_pos.1 (by omega)
  have hfl := frequent_lt_b hIH hp hc hm
  have hsub : L v0 ⊆ (colours W L).filter (Frequent q W k L) := by
    intro c hcv
    refine mem_filter.2 ⟨mem_biUnion.2 ⟨v0, (mem_filter.1 hv0).1, hcv⟩, Or.inr ?_⟩
    rw [hgam]
    exact card_pos.2 ⟨v0, mem_filter.2 ⟨hv0, hcv⟩⟩
  have h1 := card_le_card hsub
  have h2 := hb.1 v0 (mem_filter.1 hv0).1
  omega

theorem C2_main (hIH : IH q W.card) (hp : nParts q W = k) (hc : W.card ≤ 2 * k + 1)
    (hm : MaxBad q W k L) : False := by
  have hb := hm.1
  have hW := card_eq_two_mul_add_one hIH hp hc hb
  have hlt := colours_lt_card hIH hp hc hb
  have hms := many_singletons hIH hp hc hb
  have hfl := frequent_lt_b hIH hp hc hm
  have hFC : (colours W L).filter (Frequent q W k L) ⊆ colours W L := filter_subset _ _
  have hgdef : gam W L + (colours W L).card = 2 * k + 1 := by unfold gam; omega
  have hno2 := C2_no_two hIH hp hc hm
  have hpart : ∀ v ∈ W, 2 ≤ (partOf q W v).card → ∀ c, ∃ u ∈ partOf q W v, c ∉ L u :=
    fun v hv h2 c => part_inter_empty hIH hp hc hb hv h2 c
  have hsplit := C2_split q W
  have h3 := C2_three hno2
  have hav := C2_avail_le hpart
  set S := singletons q W with hSdef
  set F := (colours W L).filter (Frequent q W k L) with hFdef
  set g := gam W L with hgdef'
  have hsk : S.card ≤ k := by omega
  obtain ⟨b, hkb⟩ : ∃ b, k = S.card + b := ⟨k - S.card, by omega⟩
  have hnb : ((W \ S).image q).card = b := by omega
  have hb48 : 2 * b ≤ k + 1 := by omega
  have hg1 : 1 ≤ g := by omega
  have hgS : g ≤ S.card := hms
  have hFb : F.card + 1 ≤ b := by omega
  have hFnonfreq : ∀ c ∈ colours W L \ F, (avail W L c).card ≤ k := by
    intro c hc'
    have := mem_sdiff.1 hc'
    by_contra hgt
    push_neg at hgt
    exact this.2 (mem_filter.2 ⟨this.1, Or.inl hgt⟩)
  have hFavail : ∀ c ∈ F, (avail W L c).card ≤ k + 1 + S.card := fun c _ => by
    have := hav c
    omega
  obtain ⟨n, hn⟩ : ∃ n, (colours W L).card = F.card + n :=
    ⟨_, (Nat.add_sub_of_le (card_le_card hFC)).symm⟩
  have hn' : (colours W L).card - F.card = n := by omega
  have hc1 := C2_count (k := k) F hFC k (k + 1 + S.card) hFnonfreq hFavail hb.1
  rw [hn', hW] at hc1
  have hz1 : (k:ℤ) * (2 * k + 1) ≤ (2 * k + 1 - g - F.card) * k + F.card * (2 * k + 1 - b) := by
    have h' : ((k * (2 * k + 1) : ℕ) : ℤ) ≤ ((n * k + F.card * (k + 1 + S.card) : ℕ) : ℤ) := by
      exact_mod_cast hc1
    push_cast at h'
    have e1 : (n:ℤ) = 2 * k + 1 - g - F.card := by omega
    have e2 : ((k:ℤ) + 1 + S.card) = 2 * k + 1 - b := by omega
    rw [e1, e2] at h'
    exact h'
  have h42 := C2_ar1 (k:ℤ) b g F.card (Nat.cast_nonneg _) (by exact_mod_cast hFb)
    (by exact_mod_cast hb48) (Nat.cast_nonneg _) hz1
  have hne : (colours W L \ F).Nonempty := by
    rw [← card_pos, card_sdiff_of_subset hFC]
    omega
  obtain ⟨cs, hcs, hcsmax⟩ := exists_max_image (colours W L \ F) (fun c => (avail W L c).card) hne
  have hcsC := (mem_sdiff.1 hcs).1
  have hcsF : cs ∉ F := (mem_sdiff.1 hcs).2
  have hnf : ¬ Frequent q W k L cs := fun h => hcsF (mem_filter.2 ⟨hcsC, h⟩)
  have hmk : (avail W L cs).card ≤ k := hFnonfreq cs hcs
  have hc2 := C2_count (k := k) F hFC (avail W L cs).card (k + 1 + S.card)
    (fun c hc' => hcsmax c hc') hFavail hb.1
  rw [hn', hW] at hc2
  have hz2 : (k:ℤ) * (2 * k + 1) ≤
      (2 * k + 1 - g - F.card) * (avail W L cs).card + F.card * (2 * k + 1 - b) := by
    have h' : ((k * (2 * k + 1) : ℕ) : ℤ) ≤
        ((n * (avail W L cs).card + F.card * (k + 1 + S.card) : ℕ) : ℤ) := by
      exact_mod_cast hc2
    push_cast at h'
    have e1 : (n:ℤ) = 2 * k + 1 - g - F.card := by omega
    have e2 : ((k:ℤ) + 1 + S.card) = 2 * k + 1 - b := by omega
    rw [e1, e2] at h'
    exact h'
  have h413 := C2_ar2 (k:ℤ) b g F.card (avail W L cs).card (Nat.cast_nonneg _)
    (by exact_mod_cast hFb) (Nat.cast_nonneg _) (by exact_mod_cast hmk) (by omega)
    (by exact_mod_cast hb48) (Nat.cast_nonneg _) h42 hz2
  obtain ⟨X, hXS, hXcard, hXN⟩ := prop_4_9 hIH hp hc hm hcsC hnf
  have hXcard' : S.card + 1 - g ≤ X.card := hXcard
  have hXW : ∀ v ∈ X, v ∈ W := fun v hv => (mem_filter.1 (hXS hv)).1
  set U := X.biUnion L with hU
  have hXN' : U.card + (avail W L cs).card ≤ 2 * k := hXN
  set Dset := U.filter (fun c => g ≤ (X.filter (fun v => c ∈ L v)).card) with hDdef
  set Y := U \ Dset with hY
  have hUC : U ⊆ colours W L :=
    biUnion_subset.2 (fun v hv => subset_biUnion_of_mem L (hXW v hv))
  have hDF : Dset ⊆ F := by
    intro c hcD
    have hcD' := mem_filter.1 hcD
    refine mem_filter.2 ⟨hUC hcD'.1, Or.inr ?_⟩
    exact hcD'.2.trans (card_le_card (filter_subset_filter _ hXS))
  have hDU : Dset ⊆ U := filter_subset _ _
  have hYcard : Y.card = U.card - Dset.card := card_sdiff_of_subset hDU
  have hcomm := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := X) (t := Y)
    (fun v c => c ∈ L v)
  have hlow : X.card * (k - Dset.card) ≤
      ∑ v ∈ X, (Y.bipartiteAbove (fun v c => c ∈ L v) v).card := by
    calc X.card * (k - Dset.card) = ∑ v ∈ X, (k - Dset.card) := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro v hv
        have hLU : L v ⊆ U := subset_biUnion_of_mem L hv
        have heq : Y.bipartiteAbove (fun v c => c ∈ L v) v = L v \ Dset := by
          ext c
          simp only [Finset.bipartiteAbove, mem_filter, hY, mem_sdiff]
          constructor
          · rintro ⟨⟨h1, h2⟩, h3⟩
            exact ⟨h3, h2⟩
          · rintro ⟨h3, h2⟩
            exact ⟨⟨hLU h3, h2⟩, h3⟩
        rw [heq]
        have h1 := le_card_sdiff Dset (L v)
        have h2 := hb.1 v (hXW v hv)
        omega
  have hup : ∑ c ∈ Y, (X.bipartiteBelow (fun v c => c ∈ L v) c).card ≤ Y.card * (g - 1) := by
    calc _ ≤ ∑ c ∈ Y, (g - 1) := by
          apply sum_le_sum
          intro c hcY
          have hcY' := mem_sdiff.1 hcY
          have hnot : ¬ g ≤ (X.filter (fun v => c ∈ L v)).card :=
            fun h => hcY'.2 (mem_filter.2 ⟨hcY'.1, h⟩)
          have e : (X.bipartiteBelow (fun v c => c ∈ L v) c).card =
              (X.filter (fun v => c ∈ L v)).card := rfl
          rw [e]
          omega
      _ = Y.card * (g - 1) := by simp [mul_comm]
  have hineqN : X.card * (k - Dset.card) ≤ (U.card - Dset.card) * (g - 1) := by
    rw [← hYcard]
    exact hlow.trans (hcomm.le.trans hup)
  have hdF : Dset.card ≤ F.card := card_le_card hDF
  have hdk : Dset.card ≤ k := by omega
  have hdN : Dset.card ≤ U.card := card_le_card hDU
  zify [hdk, hdN, hg1] at hineqN
  exact C2_ar3 (k:ℤ) b g X.card U.card Dset.card (avail W L cs).card h42 h413
    (by exact_mod_cast hg1) (by omega) (by exact_mod_cast hXN') (by omega)
    (by exact_mod_cast hmk) hineqN

theorem ohba_core {q : V → ℕ} {W : Finset V} {k : ℕ} {L : V → Finset ℕ}
    (hIH : IH q W.card) (hp : nParts q W = k) (hc : W.card ≤ 2 * k + 1)
    (hL : ∀ v ∈ W, k ≤ (L v).card) : Colourable q W L := by
  by_contra hnc
  obtain ⟨L', _, hm⟩ := exists_maxBad hIH hp hc (show Bad q W k L from ⟨hL, hnc⟩)
  exact C2_main hIH hp hc hm



end core


theorem ohba_W_all : ∀ n : ℕ, ∀ q : V → ℕ, IH q n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro q W k L hW hpk hck hLk
    by_cases hk : W.card ≤ k
    · exact P3_greedy hk hLk
    · have hk' : k < W.card := by omega
      obtain ⟨q', hq1, hq2⟩ := P4_refine W k (k - nParts q W) q (by omega) hk'.le
      have hIH' : IH q' W.card := ihn W.card hW q'
      exact P4_colourable hq2 (ohba_core hIH' hq1 hck hLk)

theorem ohba_W (q : V → ℕ) : ∀ n, IH q n := fun n => ohba_W_all n q

theorem A_card_bound_V {V : Type} [Fintype V] (G : SimpleGraph V) :
    G.chromaticNumber ≠ ⊤ := by
  have := G.chromaticNumber_le_card
  exact ne_top_of_le_ne_top (ENat.coe_ne_top _) this

theorem P1_choosable_iff {G : SimpleGraph V} {k : ℕ} :
    OhbaConjecture.Choosable G k ↔ ∀ L : V → Finset ℕ, (∀ v, k ≤ (L v).card) →
      ∃ c : V → ℕ, (∀ v, c v ∈ L v) ∧ ∀ u v, G.Adj u v → c u ≠ c v := by
  constructor
  · intro h L hL
    have : ∀ v, ∃ t ⊆ L v, t.card = k := fun v => exists_subset_card_eq (hL v)
    choose t ht1 ht2 using this
    obtain ⟨c, hc1, hc2⟩ := h t ht2
    exact ⟨c, fun v => ht1 v (hc1 v), hc2⟩
  · intro h L hL
    exact h L (fun v => (hL v).ge)

theorem P2_mono {G : SimpleGraph V} [Fintype V] {q : V → ℕ} {L : V → Finset ℕ}
    (hq : ∀ u v, G.Adj u v → q u ≠ q v) (hc : Colourable q Finset.univ L) :
    ∃ c : V → ℕ, (∀ v, c v ∈ L v) ∧ ∀ u v, G.Adj u v → c u ≠ c v := by
  obtain ⟨g, hg1, hg2⟩ := hc
  exact ⟨g, fun v => hg1 v (mem_univ v), fun u v h =>
    hg2 u (mem_univ u) v (mem_univ v) (hq u v h)⟩

theorem ohba_final :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (Fintype.card V : ℕ∞) ≤ 2 * G.chromaticNumber + 1 →
      OhbaConjecture.Choosable G G.chromaticNumber.toNat := by
  intro V _ _ G _ hcard
  have hne := A_card_bound_V G
  set k : ℕ := G.chromaticNumber.toNat with hk
  have hχ : G.chromaticNumber = (k : ℕ∞) := (ENat.coe_toNat hne).symm
  rw [hχ] at hcard
  have hcard' : Fintype.card V ≤ 2 * k + 1 := by exact_mod_cast hcard
  have hcol : G.Colorable k := by
    have := G.colorable_chromaticNumber_of_fintype
    exact this
  obtain ⟨C⟩ := hcol
  let q : V → ℕ := fun v => (C v : ℕ)
  have hq : ∀ u v, G.Adj u v → q u ≠ q v := by
    intro u v h e
    exact C.valid h (Fin.ext e)
  have hparts : nParts q (Finset.univ : Finset V) ≤ k := by
    unfold nParts
    calc (Finset.univ.image q).card ≤ (Finset.range k).card :=
          card_le_card (by
            intro x hx
            obtain ⟨v, _, rfl⟩ := mem_image.1 hx
            exact mem_range.2 (C v).isLt)
      _ = k := card_range k
  rw [P1_choosable_iff]
  intro L hL
  have hIH := ohba_W q (Fintype.card V + 1)
  have hcol := hIH Finset.univ k L (by simp) hparts (by simpa using hcard') (fun v _ => hL v)
  exact P2_mono hq hcol

end OhbaBP
end OhbaProof


theorem OMA.solution : type_of% @OhbaConjecture.ohba_conjecture :=
  fun {V} _ _ G _ h => OhbaBP.ohba_final G h

