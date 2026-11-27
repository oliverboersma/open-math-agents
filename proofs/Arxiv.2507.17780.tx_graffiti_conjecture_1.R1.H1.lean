import OMAReductions.R_Arxiv_2507_17780_tx_graffiti_conjecture_1_R1

-- Credit: @Mart1neZ

/-!
Proof of `G.residue ≤ G.indepNum` (Favaron–Mahéo–Saclé / Triesch).
-/

namespace OMA.ResidueBound

open SimpleGraph Finset

abbrev hh := SimpleGraph.havelHakimiStep

def hhIter (t : ℕ) (l : List ℕ) : List ℕ := hh^[t] l

def SortedDesc (l : List ℕ) : Prop := l.Pairwise (· ≥ ·)

lemma sortedDesc_sort (m : Multiset ℕ) : SortedDesc (m.sort (· ≥ ·)) :=
  m.pairwise_sort (· ≥ ·)

lemma sortedDesc_mergeSort (l : List ℕ) : SortedDesc (l.mergeSort (· ≥ ·)) := by
  have h := List.pairwise_mergeSort (l := l) (le := fun a b => decide (a ≥ b))
    (fun a b c h1 h2 => by simp at h1 h2 ⊢; omega)
    (fun a b => by by_cases hab : a ≥ b <;> simp [hab]; omega)
  simpa [SortedDesc] using h

lemma sortedDesc_hh {l : List ℕ} (hl : SortedDesc l) : SortedDesc (hh l) := by
  cases l with
  | nil => exact List.Pairwise.nil
  | cons _ _ => exact sortedDesc_mergeSort _

lemma sortedDesc_hhIter {l : List ℕ} (hl : SortedDesc l) (t : ℕ) : SortedDesc (hhIter t l) := by
  induction t generalizing l with
  | zero => exact hl
  | succ t ih => simpa [hhIter, Function.iterate_succ_apply] using ih (sortedDesc_hh hl)

lemma sortedDesc_tail {d : ℕ} {r : List ℕ} (h : SortedDesc (d :: r)) : SortedDesc r :=
  (List.pairwise_cons.mp h).2

lemma sortedDesc_head_ge {d : ℕ} {r : List ℕ} (h : SortedDesc (d :: r)) :
    ∀ x ∈ r, x ≤ d :=
  fun _ hx => (List.pairwise_cons.mp h).1 _ hx

lemma sortedDesc_eq_of_perm {a b : List ℕ} (ha : SortedDesc a) (hb : SortedDesc b)
    (h : a.Perm b) : a = b :=
  List.Perm.eq_of_pairwise (fun _ _ _ _ h1 h2 => Nat.le_antisymm h2 h1) ha hb h

lemma sortedDesc_eq_of_coe {a b : List ℕ} (ha : SortedDesc a) (hb : SortedDesc b)
    (h : (a : Multiset ℕ) = (b : Multiset ℕ)) : a = b :=
  sortedDesc_eq_of_perm ha hb (Multiset.coe_eq_coe.mp h)

lemma sortedDesc_zero_sum {s : List ℕ} (h : SortedDesc (0 :: s)) : (0 :: s).sum = 0 := by
  have hz : ∀ x ∈ s, x = 0 := fun x hx => Nat.eq_zero_of_le_zero (sortedDesc_head_ge h x hx)
  simp [List.sum_eq_zero hz]

lemma length_hh : ∀ l : List ℕ, (hh l).length = l.length - 1
  | [] => rfl
  | _ :: _ => by simp [hh, havelHakimiStep_length_cons]

lemma length_hhIter (l : List ℕ) (t : ℕ) : (hhIter t l).length = l.length - t := by
  induction t generalizing l with
  | zero => simp [hhIter]
  | succ t ih =>
    simp only [hhIter, Function.iterate_succ_apply]
    change (hhIter t (hh l)).length = l.length - (t + 1)
    rw [ih (hh l), length_hh]
    omega

lemma residueAux_eq_length_of_sum_zero {l : List ℕ} (hl : SortedDesc l) (hs : l.sum = 0) :
    residueAux l = l.length := by
  cases l with
  | nil => simp [residueAux]
  | cons d s =>
    cases d with
    | zero => simp [residueAux]; omega
    | succ d => simp at hs

lemma residueAux_succ_cons (d : ℕ) (s : List ℕ) :
    residueAux ((d + 1) :: s) = residueAux (hh ((d + 1) :: s)) := by
  conv_lhs => unfold residueAux
  rfl

lemma hhIter_sum_zero_exists {l : List ℕ} (hl : SortedDesc l) :
    ∃ t ≤ l.length, (hhIter t l).sum = 0 ∧ l.length - t = residueAux l := by
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
    cases l with
    | nil =>
      subst hn
      exact ⟨0, by simp, by simp [hhIter], by simp [residueAux]⟩
    | cons d s =>
      cases d with
      | zero =>
        subst hn
        refine ⟨0, by simp, sortedDesc_zero_sum hl, ?_⟩
        simp [residueAux]; omega
      | succ d =>
        have hlen : (hh ((d + 1) :: s)).length < n := by
          rw [length_hh, ← hn]; simp
        obtain ⟨t, ht, hsum, hres⟩ := ih _ hlen (sortedDesc_hh hl) rfl
        refine ⟨t + 1, ?_, ?_, ?_⟩
        · rw [length_hh] at ht; rw [← hn]; simp only [List.length_cons] at *; omega
        · simpa [hhIter, Function.iterate_succ_apply] using hsum
        · rw [length_hh] at hres
          rw [residueAux_succ_cons, ← hn]
          simp only [List.length_cons] at hres ⊢
          omega

lemma le_residueAux_of_hhIter_sum_zero {l : List ℕ} (hl : SortedDesc l) :
    ∀ t, (hhIter t l).sum = 0 → l.length - t ≤ residueAux l := by
  intro t
  induction t generalizing l with
  | zero =>
    intro hs
    rw [residueAux_eq_length_of_sum_zero hl hs]
    simp
  | succ t ih =>
    intro hs
    cases l with
    | nil => simp [residueAux]
    | cons d s =>
      cases d with
      | zero => simp [residueAux]; omega
      | succ d =>
        have h1 : (hhIter t (hh ((d + 1) :: s))).sum = 0 := by
          simpa [hhIter, Function.iterate_succ_apply] using hs
        have h2 := ih (sortedDesc_hh hl) h1
        rw [length_hh] at h2
        rw [residueAux_succ_cons]
        simp only [List.length_cons] at h2 ⊢
        omega

lemma residueAux_le_of_hhIter_sum_le {a b : List ℕ} (ha : SortedDesc a) (hb : SortedDesc b)
    (hlen : a.length = b.length) (hsum : ∀ t, (hhIter t b).sum ≤ (hhIter t a).sum) :
    residueAux a ≤ residueAux b := by
  obtain ⟨t, _, hza, hra⟩ := hhIter_sum_zero_exists ha
  have hzb : (hhIter t b).sum = 0 := Nat.eq_zero_of_le_zero ((hsum t).trans hza.le)
  have hrb := le_residueAux_of_hhIter_sum_zero hb t hzb
  omega

/- Graph realization and degree-sequence transformations -/

section GraphOps

open scoped Classical

def IsGraphical (l : List ℕ) : Prop :=
  SortedDesc l ∧ ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
    Multiset.ofList l = Finset.univ.val.map (fun v => G.degree v)

lemma isGraphical_length_eq {l : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)}
    (h : Multiset.ofList l = Finset.univ.val.map (fun v => G.degree v)) : l.length = n := by
  have := congrArg Multiset.card h
  simpa using this

def swapEdge {V : Type*} [DecidableEq V] (G : SimpleGraph V) (u w z : V) (hwz : w ≠ z) :
    SimpleGraph V where
  Adj a b := if s(a, b) = s(u, z) then False else if s(a, b) = s(w, z) then True else G.Adj a b
  symm := ⟨fun a b h => by
    rw [Sym2.eq_swap]
    split_ifs at h ⊢ <;> (first | exact h | exact (G.adj_comm _ _).1 h)⟩
  loopless := ⟨fun a h => by
    by_cases h1 : s(a, a) = s(u, z)
    · simp only [h1, ↓reduceIte] at h
    · by_cases h2 : s(a, a) = s(w, z)
      · rw [Sym2.eq_iff] at h2
        rcases h2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩
        · exact hwz (h2a.symm.trans h2b)
        · exact hwz (h2b.symm.trans h2a)
      · simp only [h1, h2, ↓reduceIte] at h
        exact G.loopless.irrefl a h⟩

lemma swapEdge_neighborFinset_u {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {u w z : V}
    (huw : u ≠ w) (huz : u ≠ z) (hwz : w ≠ z) :
    (swapEdge G u w z hwz).neighborFinset u = (G.neighborFinset u).erase z := by
  ext a
  rw [mem_erase, mem_neighborFinset, mem_neighborFinset]
  dsimp only [swapEdge]
  by_cases ha : a = z
  · rw [ha]; simp
  · have h1 : s(u, a) ≠ s(u, z) := by
      rw [ne_eq, Sym2.eq_iff]
      rintro (⟨_, h⟩ | ⟨h, _⟩) <;> [exact ha h; exact huz h]
    have h2 : s(u, a) ≠ s(w, z) := by
      rw [ne_eq, Sym2.eq_iff]
      rintro (⟨h, _⟩ | ⟨h, _⟩) <;> [exact huw h; exact huz h]
    simp [ha, h1, h2]

lemma swapEdge_neighborFinset_w {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {u w z : V}
    (huw : u ≠ w) (huz : u ≠ z) (hwz : w ≠ z) :
    (swapEdge G u w z hwz).neighborFinset w = insert z (G.neighborFinset w) := by
  ext a
  rw [mem_insert, mem_neighborFinset, mem_neighborFinset]
  dsimp only [swapEdge]
  by_cases ha : a = z
  · rw [ha]
    have h1 : s(w, z) ≠ s(u, z) := by
      rw [ne_eq, Sym2.eq_iff]
      rintro (⟨h, _⟩ | ⟨h, _⟩) <;> [exact huw h.symm; exact hwz h]
    simp [h1]
  · have h1 : s(w, a) ≠ s(u, z) := by
      rw [ne_eq, Sym2.eq_iff]
      rintro (⟨h, _⟩ | ⟨h, _⟩) <;> [exact huw h.symm; exact hwz h]
    have h2 : s(w, a) ≠ s(w, z) := by
      rw [ne_eq, Sym2.eq_iff]
      rintro (⟨_, h⟩ | ⟨h, _⟩) <;> [exact ha h; exact hwz h]
    simp [ha, h1, h2]

lemma swapEdge_neighborFinset_z {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {u w z : V}
    (huw : u ≠ w) (huz : u ≠ z) (hwz : w ≠ z) :
    (swapEdge G u w z hwz).neighborFinset z = insert w ((G.neighborFinset z).erase u) := by
  ext a
  rw [mem_insert, mem_erase, mem_neighborFinset, mem_neighborFinset]
  dsimp only [swapEdge]
  by_cases haw : a = w
  · rw [haw]
    have h1 : s(z, w) ≠ s(u, z) := by
      rw [ne_eq, Sym2.eq_iff]
      rintro (⟨h, _⟩ | ⟨_, h⟩) <;> [exact huz h.symm; exact huw h.symm]
    have h2 : s(z, w) = s(w, z) := Sym2.eq_swap
    simp [h1, h2, huw.symm, hwz]
  · by_cases hau : a = u
    · rw [hau]; simp [haw, huw]
    · have h1 : s(z, a) ≠ s(u, z) := by
        rw [ne_eq, Sym2.eq_iff]
        rintro (⟨h, _⟩ | ⟨_, h⟩) <;> [exact huz h.symm; exact hau h]
      have h2 : s(z, a) ≠ s(w, z) := by
        rw [ne_eq, Sym2.eq_iff]
        rintro (⟨h, _⟩ | ⟨_, h⟩) <;> [exact hwz h.symm; exact haw h]
      simp [haw, hau, h1, h2]

lemma swapEdge_neighborFinset_other {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {u w z a : V}
    (hwz : w ≠ z) (hau : a ≠ u) (haw : a ≠ w) (haz : a ≠ z) :
    (swapEdge G u w z hwz).neighborFinset a = G.neighborFinset a := by
  ext b
  rw [mem_neighborFinset, mem_neighborFinset]
  dsimp only [swapEdge]
  have h1 : s(a, b) ≠ s(u, z) := by
    rw [ne_eq, Sym2.eq_iff]
    rintro (⟨h, _⟩ | ⟨h, _⟩) <;> [exact hau h; exact haz h]
  have h2 : s(a, b) ≠ s(w, z) := by
    rw [ne_eq, Sym2.eq_iff]
    rintro (⟨h, _⟩ | ⟨h, _⟩) <;> [exact haw h; exact haz h]
  simp [h1, h2]

lemma isGraphical_robinHood {b b' : List ℕ} (hb : IsGraphical b) (hb' : SortedDesc b')
    {x y : ℕ} (hxy : x ≥ y + 2) (hx : x ∈ b) (hy : y ∈ b)
    (hperm : (b' : Multiset ℕ) + {x, y} = (b : Multiset ℕ) + {x - 1, y + 1}) :
    IsGraphical b' := by
  refine ⟨hb', ?_⟩
  rcases hb with ⟨_, n, G, hG⟩
  have hxm : x ∈ Finset.univ.val.map (fun v => G.degree v) := by
    rw [← hG]; exact hx
  have hym : y ∈ Finset.univ.val.map (fun v => G.degree v) := by
    rw [← hG]; exact hy
  obtain ⟨u, _, hu⟩ := Multiset.mem_map.mp hxm
  obtain ⟨w, _, hw⟩ := Multiset.mem_map.mp hym
  have huw : u ≠ w := by intro h; subst h; omega
  have hcard : (G.neighborFinset w).card < ((G.neighborFinset u).erase w).card := by
    rw [card_neighborFinset_eq_degree, hw]
    have hle : G.degree u - 1 ≤ ((G.neighborFinset u).erase w).card := by
      rw [← card_neighborFinset_eq_degree]
      exact Nat.le_trans (Nat.sub_le_sub_right (le_refl _) 1) pred_card_le_card_erase
    omega
  obtain ⟨z, hz1, hz2⟩ := exists_mem_notMem_of_card_lt_card hcard
  rw [mem_erase, mem_neighborFinset] at hz1
  rw [mem_neighborFinset] at hz2
  rcases hz1 with ⟨hzw, huz⟩
  have hzu : u ≠ z := fun h => G.loopless.irrefl u (h ▸ huz)
  have hwz : w ≠ z := hzw.symm
  let G' := swapEdge G u w z hwz
  refine ⟨n, G', ?_⟩
  have hdeg_u : G'.degree u = x - 1 := by
    rw [← card_neighborFinset_eq_degree, swapEdge_neighborFinset_u G huw hzu hwz,
      card_erase_of_mem (by rw [mem_neighborFinset]; exact huz), card_neighborFinset_eq_degree, hu]
  have hdeg_w : G'.degree w = y + 1 := by
    rw [← card_neighborFinset_eq_degree, swapEdge_neighborFinset_w G huw hzu hwz,
      card_insert_of_notMem (by rw [mem_neighborFinset]; exact hz2), card_neighborFinset_eq_degree, hw]
  have hdeg_z : G'.degree z = G.degree z := by
    rw [← card_neighborFinset_eq_degree, swapEdge_neighborFinset_z G huw hzu hwz,
      card_insert_of_notMem (by simp [mem_neighborFinset, G.adj_comm, hz2]),
      card_erase_of_mem (by rw [mem_neighborFinset]; exact (G.adj_comm _ _).1 huz),
      card_neighborFinset_eq_degree, Nat.sub_add_cancel]
    exact card_pos.mpr ⟨u, by rw [mem_neighborFinset]; exact (G.adj_comm _ _).1 huz⟩
  have hdeg_other : ∀ a, a ≠ u → a ≠ w → G'.degree a = G.degree a := by
    intro a hau haw
    by_cases haz : a = z
    · subst haz; exact hdeg_z
    · rw [← card_neighborFinset_eq_degree, swapEdge_neighborFinset_other G hwz hau haw haz,
        card_neighborFinset_eq_degree]
  have hmap : Finset.univ.val.map (fun v => G'.degree v) + {x, y} =
      Finset.univ.val.map (fun v => G.degree v) + {x - 1, y + 1} := by
    have hpart : (Finset.univ : Finset (Fin n)) =
        insert u (insert w ((Finset.univ.erase u).erase w)) := by
      ext a; simp only [mem_insert, mem_erase, mem_univ, and_true]; tauto
    have hu_nmem : u ∉ insert w ((Finset.univ.erase u).erase w) := by simp [huw]
    have hw_nmem : w ∉ (Finset.univ.erase u).erase w := by simp
    have hsub : Finset.univ.val = u ::ₘ w ::ₘ ((Finset.univ.erase u).erase w).val := by
      conv_lhs => rw [hpart]
      rw [insert_val_of_notMem hu_nmem, insert_val_of_notMem hw_nmem]
    have hrest : ((Finset.univ.erase u).erase w).val.map (fun v => G'.degree v) =
        ((Finset.univ.erase u).erase w).val.map (fun v => G.degree v) := by
      apply Multiset.map_congr rfl
      intro a ha
      rw [← mem_def, mem_erase, mem_erase] at ha
      exact hdeg_other a ha.2.1 ha.1
    rw [hsub, Multiset.map_cons, Multiset.map_cons, Multiset.map_cons, Multiset.map_cons,
      hdeg_u, hdeg_w, hu, hw, hrest]
    simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]
    abel
  have hfin : (b' : Multiset ℕ) + {x, y} =
      Finset.univ.val.map (fun v => G'.degree v) + {x, y} := by
    rw [hperm, hG, ← hmap]
  exact add_right_cancel hfin

def twoSwitch {V : Type*} [DecidableEq V] (G : SimpleGraph V) (v x y z : V)
    (hvy : v ≠ y) (hxz : x ≠ z) : SimpleGraph V where
  Adj a b :=
    if s(a, b) = s(v, x) then False
    else if s(a, b) = s(y, z) then False
    else if s(a, b) = s(v, y) then True
    else if s(a, b) = s(x, z) then True
    else G.Adj a b
  symm := ⟨fun a b h => by
    rw [Sym2.eq_swap]
    split_ifs at h ⊢ <;> (first | exact h | exact (G.adj_comm _ _).1 h)⟩
  loopless := ⟨fun a h => by
    by_cases h1 : s(a, a) = s(v, x)
    · simp only [h1, ↓reduceIte] at h
    · by_cases h2 : s(a, a) = s(y, z)
      · split_ifs at h
      · by_cases h3 : s(a, a) = s(v, y)
        · rw [Sym2.eq_iff] at h3
          rcases h3 with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩
          · exact hvy (ha1.symm.trans ha2)
          · exact hvy (ha2.symm.trans ha1)
        · by_cases h4 : s(a, a) = s(x, z)
          · rw [Sym2.eq_iff] at h4
            rcases h4 with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩
            · exact hxz (ha1.symm.trans ha2)
            · exact hxz (ha2.symm.trans ha1)
          · simp only [h1, h2, h3, h4, ↓reduceIte] at h
            exact G.loopless.irrefl a h⟩

lemma twoSwitch_neighborFinset_v {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {v x y z : V}
    (hvx : v ≠ x) (hvy : v ≠ y) (hvz : v ≠ z) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (twoSwitch G v x y z hvy hxz).neighborFinset v = insert y ((G.neighborFinset v).erase x) := by
  ext a
  rw [mem_insert, mem_erase, mem_neighborFinset, mem_neighborFinset]
  dsimp only [twoSwitch]
  by_cases hay : a = y
  · rw [hay]
    have h1 : s(v, y) ≠ s(v, x) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
    have h2 : s(v, y) ≠ s(y, z) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
    simp [h1, h2, hxy.symm]
  · by_cases hax : a = x
    · rw [hax] at hay ⊢
      have h1 : s(v, x) = s(v, x) := rfl
      rw [if_pos h1]
      simp [hay]
    · have h1 : s(v, a) ≠ s(v, x) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
      have h2 : s(v, a) ≠ s(y, z) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
      have h3 : s(v, a) ≠ s(v, y) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
      have h4 : s(v, a) ≠ s(x, z) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
      simp [hay, hax, h1, h2, h3, h4]

lemma twoSwitch_neighborFinset_x {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {v x y z : V}
    (hvx : v ≠ x) (hvy : v ≠ y) (hvz : v ≠ z) (hxy : x ≠ y) (_hxz : x ≠ z) (_hyz : y ≠ z) :
    (twoSwitch G v x y z hvy _hxz).neighborFinset x = insert z ((G.neighborFinset x).erase v) := by
  ext a
  rw [mem_insert, mem_erase, mem_neighborFinset, mem_neighborFinset]
  dsimp only [twoSwitch]
  by_cases haz : a = z
  · rw [haz]
    have h1 : s(x, z) ≠ s(v, x) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
    have h2 : s(x, z) ≠ s(y, z) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
    have h3 : s(x, z) ≠ s(v, y) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
    simp [h1, h2, h3, hvz.symm]
  · by_cases hav : a = v
    · rw [hav] at haz ⊢
      have h1 : s(x, v) = s(v, x) := Sym2.eq_swap
      rw [if_pos h1]
      simp [haz]
    · have h1 : s(x, a) ≠ s(v, x) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
      have h2 : s(x, a) ≠ s(y, z) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
      have h3 : s(x, a) ≠ s(v, y) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
      have h4 : s(x, a) ≠ s(x, z) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
      simp [haz, hav, h1, h2, h3, h4]

lemma twoSwitch_neighborFinset_y {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {v x y z : V}
    (hvx : v ≠ x) (hvy : v ≠ y) (hvz : v ≠ z) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (twoSwitch G v x y z hvy hxz).neighborFinset y = insert v ((G.neighborFinset y).erase z) := by
  ext a
  rw [mem_insert, mem_erase, mem_neighborFinset, mem_neighborFinset]
  dsimp only [twoSwitch]
  by_cases hav : a = v
  · rw [hav]
    have h1 : s(y, v) ≠ s(v, x) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
    have h2 : s(y, v) ≠ s(y, z) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
    have h3 : s(y, v) = s(v, y) := Sym2.eq_swap
    rw [if_neg h1, if_neg h2, if_pos h3]
    simp
  · by_cases haz : a = z
    · rw [haz] at hav ⊢
      have h1 : s(y, z) ≠ s(v, x) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
      rw [if_neg h1, if_pos rfl]
      simp [hav]
    · have h1 : s(y, a) ≠ s(v, x) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
      have h2 : s(y, a) ≠ s(y, z) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
      have h3 : s(y, a) ≠ s(v, y) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
      have h4 : s(y, a) ≠ s(x, z) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
      simp [hav, haz, h1, h2, h3, h4]

lemma twoSwitch_neighborFinset_z {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {v x y z : V}
    (hvx : v ≠ x) (hvy : v ≠ y) (hvz : v ≠ z) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (twoSwitch G v x y z hvy hxz).neighborFinset z = insert x ((G.neighborFinset z).erase y) := by
  ext a
  rw [mem_insert, mem_erase, mem_neighborFinset, mem_neighborFinset]
  dsimp only [twoSwitch]
  by_cases hax : a = x
  · rw [hax]
    have h1 : s(z, x) ≠ s(v, x) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
    have h2 : s(z, x) ≠ s(y, z) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
    have h3 : s(z, x) ≠ s(v, y) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
    have h4 : s(z, x) = s(x, z) := Sym2.eq_swap
    rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
    simp
  · by_cases hay : a = y
    · rw [hay] at hax ⊢
      have h1 : s(z, y) ≠ s(v, x) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
      have h2 : s(z, y) = s(y, z) := Sym2.eq_swap
      rw [if_neg h1, if_pos h2]
      simp [hax]
    · have h1 : s(z, a) ≠ s(v, x) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
      have h2 : s(z, a) ≠ s(y, z) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
      have h3 : s(z, a) ≠ s(v, y) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
      have h4 : s(z, a) ≠ s(x, z) := by rw [ne_eq, Sym2.eq_iff]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
      simp [hax, hay, h1, h2, h3, h4]

lemma twoSwitch_neighborFinset_other {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {v x y z a : V}
    (hvy : v ≠ y) (hxz : x ≠ z) (hav : a ≠ v) (hax : a ≠ x) (hay : a ≠ y) (haz : a ≠ z) :
    (twoSwitch G v x y z hvy hxz).neighborFinset a = G.neighborFinset a := by
  ext b
  rw [mem_neighborFinset, mem_neighborFinset]
  dsimp only [twoSwitch]
  have h1 : s(a, b) ≠ s(v, x) := by
    rw [ne_eq, Sym2.eq_iff]; rintro (⟨h, _⟩ | ⟨h, _⟩) <;> [exact hav h; exact hax h]
  have h2 : s(a, b) ≠ s(y, z) := by
    rw [ne_eq, Sym2.eq_iff]; rintro (⟨h, _⟩ | ⟨h, _⟩) <;> [exact hay h; exact haz h]
  have h3 : s(a, b) ≠ s(v, y) := by
    rw [ne_eq, Sym2.eq_iff]; rintro (⟨h, _⟩ | ⟨h, _⟩) <;> [exact hav h; exact hay h]
  have h4 : s(a, b) ≠ s(x, z) := by
    rw [ne_eq, Sym2.eq_iff]; rintro (⟨h, _⟩ | ⟨h, _⟩) <;> [exact hax h; exact haz h]
  simp [h1, h2, h3, h4]

lemma twoSwitch_degree_eq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {v x y z : V}
    (hvx : v ≠ x) (hvy : v ≠ y) (hvz : v ≠ z) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h1 : G.Adj v x) (h2 : G.Adj y z) (h3 : ¬ G.Adj v y) (h4 : ¬ G.Adj x z) :
    ∀ a, (twoSwitch G v x y z hvy hxz).degree a = G.degree a := by
  intro a
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  by_cases hav : a = v
  · subst hav; rw [twoSwitch_neighborFinset_v G hvx hvy hvz hxy hxz hyz,
      card_insert_of_notMem (by simp [mem_neighborFinset, h3, hxy.symm]),
      card_erase_add_one (by rw [mem_neighborFinset]; exact h1)]
  · by_cases hax : a = x
    · subst hax; rw [twoSwitch_neighborFinset_x G hvx hvy hvz hxy hxz hyz,
        card_insert_of_notMem (by simp [mem_neighborFinset, h4, hvz.symm]),
        card_erase_add_one (by rw [mem_neighborFinset]; exact (G.adj_comm _ _).1 h1)]
    · by_cases hay : a = y
      · subst hay; rw [twoSwitch_neighborFinset_y G hvx hvy hvz hxy hxz hyz,
          card_insert_of_notMem (by simp [mem_neighborFinset, G.adj_comm, h3, hvz]),
          card_erase_add_one (by rw [mem_neighborFinset]; exact h2)]
      · by_cases haz : a = z
        · subst haz; rw [twoSwitch_neighborFinset_z G hvx hvy hvz hxy hxz hyz,
            card_insert_of_notMem (by simp [mem_neighborFinset, G.adj_comm, h4, hxy]),
            card_erase_add_one (by rw [mem_neighborFinset]; exact (G.adj_comm _ _).1 h2)]
        · rw [twoSwitch_neighborFinset_other G hvy hxz hav hax hay haz]

lemma prefix_of_downward_closed {α : Type*} (l : List α) (P : α → Bool)
    (hdown : ∀ i j (hi : i < j) (hj : j < l.length), P l[j] = true → P l[i] = true) :
    l.countP (fun a => P a) ≤ l.length ∧
      ∀ i (hi : i < l.length), P l[i] = true ↔ i < l.countP (fun a => P a) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ht : ∀ i j (hi : i < j) (hj : j < t.length), P t[j] = true → P t[i] = true := by
      intro i j hi hj hp
      exact hdown (i + 1) (j + 1) (by omega) (by simp; omega) hp
    obtain ⟨hlen, hiff⟩ := ih ht
    by_cases ha : P a = true
    · simp only [List.countP_cons, ha, ↓reduceIte, List.length_cons]
      refine ⟨by omega, fun i hi => ?_⟩
      cases i with
      | zero => simp [ha]
      | succ j =>
        simp only [List.getElem_cons_succ]
        rw [hiff j (by simp at hi; omega)]
        omega
    · have ha' : P a = false := Bool.eq_false_iff.mpr ha
      have hnone : ∀ x ∈ t, P x = false := by
        intro x hx
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
        by_contra hpx
        have hpt : P t[j] = true := Bool.eq_true_of_not_eq_false hpx
        have := hdown 0 (j + 1) (by omega) (by simp; omega) hpt
        simp [ha'] at this
      have hcnt : t.countP (fun a => P a) = 0 := List.countP_eq_zero.mpr (by simpa using hnone)
      simp only [List.countP_cons, ha', Bool.false_eq_true, ↓reduceIte, hcnt, List.length_cons]
      refine ⟨by omega, fun i hi => ?_⟩
      cases i with
      | zero => simp [ha']
      | succ j =>
        have : t[j] ∈ t := List.getElem_mem (by simp at hi; omega)
        simp [hnone _ this]

lemma isGraphical_hh {d : ℕ} {r : List ℕ} (h : IsGraphical ((d + 1) :: r)) :
    IsGraphical (hh ((d + 1) :: r)) ∧ d + 1 ≤ r.length ∧ ∀ x ∈ r.take (d + 1), 1 ≤ x := by
  rcases h with ⟨hsort, n, G, hG⟩
  have hn : n = r.length + 1 := (isGraphical_length_eq hG).symm
  have hdv : (d + 1) ∈ Finset.univ.val.map (fun v => G.degree v) := by
    rw [← hG]; simp
  obtain ⟨v, _, hvdeg⟩ := Multiset.mem_map.mp hdv
  let S : Finset (SimpleGraph (Fin n)) := Finset.univ.filter (fun H => ∀ a, H.degree a = G.degree a)
  have hGS : G ∈ S := mem_filter.mpr ⟨mem_univ _, fun _ => rfl⟩
  obtain ⟨H, hHS, hHmax⟩ := S.exists_max_image (fun H => ∑ a ∈ H.neighborFinset v, H.degree a) ⟨G, hGS⟩
  have Hdeg : ∀ a, H.degree a = G.degree a := (mem_filter.mp hHS).2
  have hHdeg_map : Finset.univ.val.map (fun a => H.degree a) = Multiset.ofList ((d + 1) :: r) := by
    rw [hG]; apply Multiset.map_congr rfl; intro a _; exact Hdeg a
  have hH_opt : ∀ x y, x ≠ v → y ≠ v → H.Adj v x → ¬ H.Adj v y → H.degree y ≤ H.degree x := by
    intro x y hxv hyv hvx hvy_n
    by_contra! hlt
    have hxy : x ≠ y := by rintro rfl; exact hvy_n hvx
    have hcard : (((H.neighborFinset x).erase v).erase y).card < ((H.neighborFinset y).erase x).card := by
      have h1 : ((H.neighborFinset x).erase v).card = H.degree x - 1 := by
        rw [card_erase_of_mem (by rw [mem_neighborFinset]; exact (H.adj_comm _ _).1 hvx),
          card_neighborFinset_eq_degree]
      have hxpos : 1 ≤ H.degree x := by
        rw [← card_neighborFinset_eq_degree]
        exact card_pos.mpr ⟨v, by rw [mem_neighborFinset]; exact (H.adj_comm _ _).1 hvx⟩
      by_cases haxy : H.Adj x y
      · have hyin : y ∈ (H.neighborFinset x).erase v :=
          mem_erase.mpr ⟨hyv, by rw [mem_neighborFinset]; exact haxy⟩
        have hxin : x ∈ H.neighborFinset y := by rw [mem_neighborFinset]; exact (H.adj_comm _ _).1 haxy
        rw [card_erase_of_mem hyin, h1, card_erase_of_mem hxin, card_neighborFinset_eq_degree]
        omega
      · have hynot : y ∉ (H.neighborFinset x).erase v := by simp [mem_erase, mem_neighborFinset, haxy]
        have hxnot : x ∉ H.neighborFinset y := by
          rw [mem_neighborFinset]; exact fun h => haxy ((H.adj_comm _ _).1 h)
        rw [erase_eq_of_notMem hynot, h1, erase_eq_of_notMem hxnot, card_neighborFinset_eq_degree]
        omega
    obtain ⟨z, hz1, hz2⟩ := exists_mem_notMem_of_card_lt_card hcard
    rw [mem_erase, mem_neighborFinset] at hz1
    rcases hz1 with ⟨hzx, hyz⟩
    have hzv : z ≠ v := by rintro rfl; exact hvy_n ((H.adj_comm _ _).1 hyz)
    have hzy : z ≠ y := fun h => H.loopless.irrefl y (h ▸ hyz)
    have hxz_n : ¬ H.Adj x z := by
      intro h
      apply hz2
      exact mem_erase.mpr ⟨hzy, mem_erase.mpr ⟨hzv, by rw [mem_neighborFinset]; exact h⟩⟩
    let H' := twoSwitch H v x y z hyv.symm hzx.symm
    have H'deg : ∀ a, H'.degree a = H.degree a :=
      twoSwitch_degree_eq H hxv.symm hyv.symm hzv.symm hxy hzx.symm hzy.symm hvx hyz hvy_n hxz_n
    have H'mem : H' ∈ S := mem_filter.mpr ⟨mem_univ _, fun a => (H'deg a).trans (Hdeg a)⟩
    have H'max := hHmax H' H'mem
    have hsum_eq : ∑ a ∈ H'.neighborFinset v, H'.degree a =
        (∑ a ∈ H.neighborFinset v, H.degree a) - H.degree x + H.degree y := by
      have hsum_deg : ∑ a ∈ H'.neighborFinset v, H'.degree a =
          ∑ a ∈ H'.neighborFinset v, H.degree a :=
        Finset.sum_congr rfl fun a _ => H'deg a
      rw [hsum_deg, twoSwitch_neighborFinset_v H hxv.symm hyv.symm hzv.symm hxy hzx.symm hzy.symm,
        sum_insert (by simp [mem_neighborFinset, hvy_n, hxy.symm])]
      have hxin : x ∈ H.neighborFinset v := by rw [mem_neighborFinset]; exact hvx
      have hxsum := Finset.add_sum_erase (H.neighborFinset v) (fun a => H.degree a) hxin
      rw [← hxsum]
      have hxle : H.degree x ≤ ∑ a ∈ H.neighborFinset v, H.degree a :=
        Finset.single_le_sum (f := fun a => H.degree a) (fun _ _ => Nat.zero_le _) hxin
      omega
    omega
  let leV : Fin n → Fin n → Bool := fun a b =>
    decide (H.degree b < H.degree a ∨ (H.degree a = H.degree b ∧ (H.Adj v a ∨ ¬ H.Adj v b)))
  have leV_trans : ∀ a b c, leV a b = true → leV b c = true → leV a c = true := by
    intro a b c hab hbc
    simp only [leV, decide_eq_true_eq] at hab hbc ⊢
    rcases hab with hab | ⟨hab1, hab2⟩ <;> rcases hbc with hbc | ⟨hbc1, hbc2⟩
    · left; omega
    · left; omega
    · left; omega
    · right; exact ⟨hab1.trans hbc1, by tauto⟩
  have leV_total : ∀ a b, (leV a b || leV b a) = true := by
    intro a b
    simp only [leV, Bool.or_eq_true, decide_eq_true_eq]
    by_cases hlt : H.degree b < H.degree a
    · left; left; exact hlt
    · by_cases hgt : H.degree a < H.degree b
      · right; left; exact hgt
      · have heq : H.degree a = H.degree b := by omega
        by_cases ha : H.Adj v a
        · left; right; exact ⟨heq, Or.inl ha⟩
        · right; right; exact ⟨heq.symm, Or.inr ha⟩
  let vs : List (Fin n) := (Finset.univ.erase v).toList.mergeSort leV
  have hvs_pair : vs.Pairwise (fun a b => leV a b = true) :=
    List.pairwise_mergeSort leV_trans leV_total _
  have hvs_perm : vs.Perm (Finset.univ.erase v).toList := List.mergeSort_perm _ _
  have hvs_coe : (vs : Multiset (Fin n)) = (Finset.univ.erase v).val := by
    rw [Multiset.coe_eq_coe.mpr hvs_perm, Finset.coe_toList]
  have hvs_deg_sort : SortedDesc (vs.map (fun a => H.degree a)) := by
    refine List.Pairwise.map _ (fun {a b} hab => ?_) hvs_pair
    simp only [leV, decide_eq_true_eq] at hab
    rcases hab with h | ⟨h, _⟩ <;> omega
  have hvs_deg_coe : Multiset.ofList (vs.map (fun a => H.degree a)) = Multiset.ofList r := by
    have h1 : Multiset.ofList (vs.map (fun a => H.degree a)) =
        (Finset.univ.erase v).val.map (fun a => H.degree a) :=
      (Multiset.map_coe _ _).trans (congrArg (Multiset.map _) hvs_coe)
    have h2 : H.degree v ::ₘ (Finset.univ.erase v).val.map (fun a => H.degree a) =
        Finset.univ.val.map (fun a => H.degree a) := by
      rw [← Multiset.map_cons (fun a => H.degree a) v (Finset.univ.erase v).val,
        ← insert_val_of_notMem (notMem_erase v _), Finset.insert_erase (mem_univ v)]
    have h3 : H.degree v = d + 1 := (Hdeg v).trans hvdeg
    rw [hHdeg_map, h3, ← Multiset.cons_coe] at h2
    rw [h1]
    simp only [← Multiset.singleton_add] at h2
    exact add_left_cancel h2
  have hvs_deg_eq : vs.map (fun a => H.degree a) = r :=
    sortedDesc_eq_of_coe hvs_deg_sort (sortedDesc_tail hsort) hvs_deg_coe
  have hvs_len : vs.length = r.length := by rw [← hvs_deg_eq, List.length_map]
  have hvs_mem : ∀ x ∈ vs, x ≠ v := fun x hx => by
    have : x ∈ Finset.univ.erase v := by
      have := hvs_perm.mem_iff.mp hx
      simpa using this
    exact (mem_erase.mp this).1
  have hdown : ∀ i j (hi : i < j) (hj : j < vs.length),
      decide (H.Adj v vs[j]) = true → decide (H.Adj v vs[i]) = true := by
    intro i j hi hj hbj
    simp only [decide_eq_true_eq] at hbj ⊢
    by_contra hbi
    have hp : leV vs[i] vs[j] = true := (List.pairwise_iff_getElem.mp hvs_pair) i j (by omega) hj hi
    simp only [leV, decide_eq_true_eq] at hp
    have hopt := hH_opt vs[j] vs[i] (hvs_mem _ (List.getElem_mem hj)) (hvs_mem _ (List.getElem_mem (by omega))) hbj hbi
    rcases hp with hlt | ⟨heq, hdisj⟩
    · omega
    · rcases hdisj with ha | hb
      · exact hbi ha
      · exact hb hbj
  have hcnt : vs.countP (fun a => decide (H.Adj v a)) = d + 1 := by
    have h1 : (vs.filter (fun a => decide (H.Adj v a))).length = vs.countP (fun a => decide (H.Adj v a)) :=
      List.countP_eq_length_filter.symm
    have h2 : (Multiset.ofList vs).filter (fun a => H.Adj v a) = (H.neighborFinset v).val := by
      rw [hvs_coe]
      refine (Multiset.Nodup.ext ?_ ?_).mpr ?_
      · exact Multiset.Nodup.filter _ (Finset.univ.erase v).nodup
      · exact (H.neighborFinset v).nodup
      intro a
      simp only [Multiset.mem_filter, Finset.mem_val, mem_erase, mem_univ, and_true, mem_neighborFinset]
      constructor
      · rintro ⟨_, ha⟩; exact ha
      · intro ha; exact ⟨fun h => H.loopless.irrefl v (h ▸ ha), ha⟩
    have h3 : (vs.filter (fun a => decide (H.Adj v a))).length =
        ((Multiset.ofList vs).filter (fun a => H.Adj v a)).card := by
      simp [Multiset.filter_coe]
    rw [← h1, h3, h2, card_val, card_neighborFinset_eq_degree, Hdeg v, hvdeg]
  obtain ⟨hcnt_le, hcnt_iff⟩ := prefix_of_downward_closed vs (fun a => decide (H.Adj v a)) hdown
  rw [hcnt, hvs_len] at hcnt_le
  have htake_pos : ∀ x ∈ r.take (d + 1), 1 ≤ x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    have hi' : i < d + 1 := by
      rw [List.length_take, Nat.min_eq_left hcnt_le] at hi
      exact hi
    have hi_r : i < r.length := by omega
    have hi_map : i < (vs.map (fun a => H.degree a)).length := by rw [hvs_deg_eq]; exact hi_r
    rw [List.getElem_take]
    have hi_vs : i < vs.length := by omega
    have hdeg_i : r[i]'hi_r = H.degree vs[i] := by
      have : r[i]'hi_r = (vs.map (fun a => H.degree a))[i]'hi_map := by
        simp only [hvs_deg_eq]
      rw [this, List.getElem_map]
    rw [hdeg_i]
    have hadj : H.Adj v vs[i] := by
      have := (hcnt_iff i hi_vs).mpr (by rw [hcnt]; exact hi')
      simpa [decide_eq_true_eq] using this
    rw [← card_neighborFinset_eq_degree]
    exact card_pos.mpr ⟨v, by rw [mem_neighborFinset]; exact (H.adj_comm _ _).1 hadj⟩
  refine ⟨⟨sortedDesc_hh hsort, ?_⟩, hcnt_le, htake_pos⟩
  let V' := {a : Fin n // a ≠ v}
  have hcardV' : Fintype.card V' = r.length := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin, hn]; simp
  let e : V' ≃ Fin r.length := Fintype.equivFinOfCardEq hcardV'
  let Hsub : SimpleGraph V' := H.induce {a : Fin n | a ≠ v}
  let Hfin : SimpleGraph (Fin r.length) := Hsub.map e.toEmbedding
  refine ⟨r.length, Hfin, ?_⟩
  have hdeg_sub : ∀ (a : V'), Hsub.degree a = H.degree a.1 - (if H.Adj v a.1 then 1 else 0) := by
    intro ⟨a, ha⟩
    rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
    by_cases hadj : H.Adj v a
    · rw [if_pos hadj]
      have heq : (Hsub.neighborFinset ⟨a, ha⟩).map (Function.Embedding.subtype _) =
          (H.neighborFinset a).erase v := by
        ext b
        simp only [mem_map, mem_neighborFinset, Function.Embedding.subtype_apply, mem_erase,
          Subtype.exists, Hsub, SimpleGraph.induce_adj]
        constructor
        · rintro ⟨c, hc, hca, rfl⟩; exact ⟨hc, hca⟩
        · rintro ⟨hbv, hba⟩; exact ⟨b, hbv, hba, rfl⟩
      have hcm : (Hsub.neighborFinset ⟨a, ha⟩).card =
          ((Hsub.neighborFinset ⟨a, ha⟩).map (Function.Embedding.subtype _)).card :=
        (Finset.card_map (Function.Embedding.subtype _)).symm
      rw [hcm, heq, card_erase_of_mem (by rw [mem_neighborFinset]; exact (H.adj_comm _ _).1 hadj)]
    · rw [if_neg hadj, Nat.sub_zero]
      have heq : (Hsub.neighborFinset ⟨a, ha⟩).map (Function.Embedding.subtype _) =
          H.neighborFinset a := by
        ext b
        simp only [mem_map, mem_neighborFinset, Function.Embedding.subtype_apply,
          Subtype.exists, Hsub, SimpleGraph.induce_adj]
        constructor
        · rintro ⟨c, _, hca, rfl⟩; exact hca
        · intro hba; exact ⟨b, fun h => hadj (h ▸ (H.adj_comm _ _).1 hba), hba, rfl⟩
      have hcm : (Hsub.neighborFinset ⟨a, ha⟩).card =
          ((Hsub.neighborFinset ⟨a, ha⟩).map (Function.Embedding.subtype _)).card :=
        (Finset.card_map (Function.Embedding.subtype _)).symm
      rw [hcm, heq]
  have hdeg_fin : ∀ i : Fin r.length, Hfin.degree i =
      H.degree (e.symm i).1 - (if H.Adj v (e.symm i).1 then 1 else 0) := by
    intro i
    rw [← card_neighborFinset_eq_degree]
    have hmap_nf : Hfin.neighborFinset i = (Hsub.neighborFinset (e.symm i)).map e.toEmbedding := by
      ext j
      simp only [mem_neighborFinset, mem_map, Equiv.toEmbedding_apply, Hfin, SimpleGraph.map_adj]
      constructor
      · rintro ⟨x, y, hxy, hxi, rfl⟩
        have hxe : x = e.symm i := e.eq_symm_apply.mpr hxi
        subst hxe; exact ⟨y, hxy, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨e.symm i, y, hy, e.apply_symm_apply i, rfl⟩
    rw [hmap_nf, card_map, card_neighborFinset_eq_degree, hdeg_sub]
  have hfin_mult : Finset.univ.val.map (fun i => Hfin.degree i) =
      (Finset.univ.erase v).val.map (fun a => H.degree a - (if H.Adj v a then 1 else 0)) := by
    have he1 : (Finset.univ : Finset (Fin r.length)).val =
        (Finset.univ : Finset V').val.map e := by
      have := congrArg Finset.val (Finset.map_univ_equiv e)
      simpa using this.symm
    have he2 : (Finset.univ : Finset V').val.map Subtype.val = (Finset.univ.erase v).val := by
      refine (Multiset.Nodup.ext ?_ ?_).mpr ?_
      · exact Multiset.Nodup.map Subtype.val_injective (Finset.univ : Finset V').nodup
      · exact (Finset.univ.erase v).nodup
      intro a
      simp only [Multiset.mem_map, mem_val, mem_univ, true_and, Subtype.exists, mem_erase, and_true]
      constructor
      · rintro ⟨b, hb, rfl⟩; exact hb
      · intro h; exact ⟨a, h, rfl⟩
    rw [he1, Multiset.map_map]
    have hmap_eq : ((Finset.univ : Finset V').val.map (fun a => Hfin.degree (e a))) =
        (Finset.univ : Finset V').val.map (fun a => H.degree a.1 - (if H.Adj v a.1 then 1 else 0)) := by
      apply Multiset.map_congr rfl
      intro a _
      rw [hdeg_fin (e a), e.symm_apply_apply a]
    rw [← he2, Multiset.map_map]
    exact hmap_eq
  have hfin_mult' : Finset.univ.val.map (fun a => Hfin.degree a) =
      Multiset.ofList (vs.map (fun a => H.degree a - (if H.Adj v a then 1 else 0))) := by
    rw [hfin_mult, ← hvs_coe, Multiset.map_coe]
  have hraw : (vs.map (fun a => H.degree a - (if H.Adj v a then 1 else 0))) =
      (r.take (d + 1)).map (· - 1) ++ r.drop (d + 1) := by
    apply List.ext_getElem
    · simp [hvs_len, Nat.min_eq_left hcnt_le]; omega
    · intro i hi1 hi2
      have hi_vs : i < vs.length := by simpa using hi1
      have hi_r : i < r.length := by omega
      have hi_map : i < (vs.map (fun a => H.degree a)).length := by rw [hvs_deg_eq]; exact hi_r
      simp only [List.getElem_map, List.getElem_append]
      by_cases hid : i < d + 1
      · have hadj : H.Adj v vs[i] := by
          have := (hcnt_iff i hi_vs).mpr (by rw [hcnt]; exact hid)
          simpa [decide_eq_true_eq] using this
        have hlt_take : i < ((r.take (d + 1)).map (· - 1)).length := by
          simp [Nat.min_eq_left hcnt_le, hid]
        have hdeg_i : r[i]'hi_r = H.degree vs[i] := by
          have : r[i]'hi_r = (vs.map (fun a => H.degree a))[i]'hi_map := by simp only [hvs_deg_eq]
          rw [this, List.getElem_map]
        rw [if_pos hadj, dif_pos hlt_take]
        simp only [List.getElem_take, hdeg_i]
      · have hnadj : ¬ H.Adj v vs[i] := by
          intro h
          have := (hcnt_iff i hi_vs).mp (by simp [h])
          rw [hcnt] at this
          omega
        have hge_take : ¬ i < ((r.take (d + 1)).map (· - 1)).length := by
          simp [Nat.min_eq_left hcnt_le, hid]
        have hlen_t : ((r.take (d + 1)).map (· - 1)).length = d + 1 := by
          simp [Nat.min_eq_left hcnt_le]
        rw [if_neg hnadj, Nat.sub_zero, dif_neg hge_take, List.getElem_drop]
        simp only [hlen_t]
        have hidx : d + 1 + (i - (d + 1)) = i := by omega
        have hdrop_idx : d + 1 + (i - (d + 1)) < r.length := by omega
        have hdeg_idx : r[d + 1 + (i - (d + 1))]'hdrop_idx = H.degree vs[i] := by
          have h1 : r[d + 1 + (i - (d + 1))]'hdrop_idx = r[i]'hi_r := by congr 1
          have h2 : r[i]'hi_r = (vs.map (fun a => H.degree a))[i]'hi_map := by simp only [hvs_deg_eq]
          rw [h1, h2, List.getElem_map]
        exact hdeg_idx.symm
  have hhh_perm : Multiset.ofList (hh ((d + 1) :: r)) =
      Multiset.ofList (vs.map (fun a => H.degree a - (if H.Adj v a then 1 else 0))) := by
    rw [hraw]
    simp only [hh, havelHakimiStep, List.splitAt_eq]
    exact Multiset.coe_eq_coe.mpr (List.mergeSort_perm _ _)
  convert hhh_perm.trans hfin_mult'.symm

end GraphOps

/- Majorization and Muirhead decomposition -/

section Majorization

open scoped Classical

def Maj (a b : List ℕ) : Prop :=
  SortedDesc a ∧ SortedDesc b ∧ a.length = b.length ∧ a.sum = b.sum ∧
    ∀ k, (b.take k).sum ≤ (a.take k).sum

lemma maj_refl {a : List ℕ} (ha : SortedDesc a) : Maj a a :=
  ⟨ha, ha, rfl, rfl, fun _ => le_rfl⟩

lemma maj_trans {a b c : List ℕ} (hab : Maj a b) (hbc : Maj b c) : Maj a c :=
  ⟨hab.1, hbc.2.1, hab.2.2.1.trans hbc.2.2.1, hab.2.2.2.1.trans hbc.2.2.2.1,
    fun k => (hbc.2.2.2.2 k).trans (hab.2.2.2.2 k)⟩

lemma sortedDesc_ge_of_le {l : List ℕ} (hl : SortedDesc l) {i j : ℕ}
    (hij : i ≤ j) (hj : j < l.length) : l[j] ≤ l[i] := by
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · exact (List.pairwise_iff_getElem.mp hl) i j (by omega) hj hlt

lemma isGraphical_head_le_len {d : ℕ} {r : List ℕ} (hg : IsGraphical (d :: r)) :
    d ≤ r.length := by
  rcases hg with ⟨_, n, G, hG⟩
  have hd : d ∈ Finset.univ.val.map (fun v => G.degree v) := by rw [← hG]; simp
  obtain ⟨v, _, hv⟩ := Multiset.mem_map.mp hd
  have hlt : G.degree v < n := by
    have := G.degree_lt_card_verts v
    simpa using this
  have hlen : (d :: r).length = n := isGraphical_length_eq hG
  simp only [List.length_cons] at hlen
  omega

lemma countP_le_take_plus_drop {α : Type*} (p : α → Bool) (l : List α) (k : ℕ) :
    l.countP p = (l.take k).countP p + (l.drop k).countP p := by
  conv_lhs => rw [← List.take_append_drop k l, List.countP_append]

lemma countP_lt_of_mem_false {α : Type*} (p : α → Bool) (l : List α) {x : α}
    (hx : x ∈ l) (hpx : p x = false) : l.countP p < l.length := by
  induction l with
  | nil => simp at hx
  | cons a t ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | ht
    · simp only [List.countP_cons, hpx, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      have hle : t.countP p ≤ t.length := List.countP_le_length
      omega
    · have := ih ht
      simp only [List.countP_cons, List.length_cons]
      split_ifs <;> omega

lemma sortedDesc_take_pos {d : ℕ} {r : List ℕ} (hr : SortedDesc r)
    (hcnt : d ≤ r.countP (fun x => decide (1 ≤ x))) : ∀ x ∈ r.take d, 1 ≤ x := by
  intro x hx
  by_contra hlt
  have hx0 : x = 0 := by omega
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  have hlen_take : (r.take d).length = min d r.length := List.length_take
  have hid : i < d := by rw [hlen_take] at hi; exact Nat.lt_of_lt_of_le hi (Nat.min_le_left _ _)
  have hi_r : i < r.length := by rw [hlen_take] at hi; exact Nat.lt_of_lt_of_le hi (Nat.min_le_right _ _)
  rw [List.getElem_take] at hx0
  have hdrop0 : (r.drop d).countP (fun y => decide (1 ≤ y)) = 0 := by
    rw [List.countP_eq_zero]
    intro y hy
    simp only [decide_eq_true_eq, not_le]
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hy
    have hj_r : d + j < r.length := by rw [List.length_drop] at hj; omega
    rw [List.getElem_drop]
    have hle := sortedDesc_ge_of_le hr (by omega : i ≤ d + j) hj_r
    omega
  have htake_le : (r.take d).countP (fun y => decide (1 ≤ y)) ≤ d := by
    have h1 : (r.take d).countP (fun y => decide (1 ≤ y)) ≤ (r.take d).length := List.countP_le_length
    rw [hlen_take] at h1
    exact h1.trans (Nat.min_le_left _ _)
  have hi_false : (r.take d)[i]'hi = 0 := by
    simpa [List.getElem_take] using hx0
  have htake_strict : (r.take d).countP (fun y => decide (1 ≤ y)) < d := by
    have hlt_len : (r.take d).countP (fun y => decide (1 ≤ y)) < (r.take d).length :=
      countP_lt_of_mem_false _ _ (List.getElem_mem hi) (by simp [hi_false])
    rw [hlen_take] at hlt_len
    exact Nat.lt_of_lt_of_le hlt_len (Nat.min_le_left _ _)
  have htot := countP_le_take_plus_drop (fun y => decide (1 ≤ y)) r d
  omega

lemma isGraphical_take_pos {d : ℕ} {r : List ℕ} (hg : IsGraphical (d :: r)) :
    d ≤ r.length ∧ ∀ x ∈ r.take d, 1 ≤ x := by
  have hd_le := isGraphical_head_le_len hg
  refine ⟨hd_le, ?_⟩
  rcases hg with ⟨hs, n, G, hG⟩
  have hr : SortedDesc r := sortedDesc_tail hs
  have hd_mem : d ∈ Finset.univ.val.map (fun v => G.degree v) := by rw [← hG]; simp
  obtain ⟨v, _, hv⟩ := Multiset.mem_map.mp hd_mem
  have hmult : Multiset.ofList r = (Finset.univ.erase v).val.map (fun w => G.degree w) := by
    have hpart : (Finset.univ : Finset (Fin n)) = insert v (Finset.univ.erase v) :=
      (Finset.insert_erase (Finset.mem_univ v)).symm
    have hsub : Finset.univ.val = v ::ₘ (Finset.univ.erase v).val := by
      conv_lhs => rw [hpart]
      exact Finset.insert_val_of_notMem (Finset.notMem_erase v _)
    have hcons : Multiset.ofList (d :: r) = d ::ₘ Multiset.ofList r := rfl
    rw [hcons, hsub, Multiset.map_cons, hv] at hG
    simp only [← Multiset.singleton_add] at hG
    exact add_left_cancel hG
  have hcnt_mult : r.countP (fun x => decide (1 ≤ x)) =
      ((Finset.univ.erase v).val.filter (fun w => 1 ≤ G.degree w)).card := by
    rw [← Multiset.coe_countP, hmult, Multiset.countP_map]
  have hsub_nf : G.neighborFinset v ⊆ (Finset.univ.erase v).filter (fun w => 1 ≤ G.degree w) := by
    intro w hw
    rw [Finset.mem_filter, Finset.mem_erase]
    rw [SimpleGraph.mem_neighborFinset] at hw
    refine ⟨⟨fun h => G.loopless.irrefl v (h ▸ hw), Finset.mem_univ w⟩, ?_⟩
    exact Finset.card_pos.mpr ⟨v, by rw [SimpleGraph.mem_neighborFinset]; exact (G.adj_comm _ _).1 hw⟩
  have hcard_le : d ≤ r.countP (fun x => decide (1 ≤ x)) := by
    rw [hcnt_mult, ← Finset.filter_val]
    have hc := Finset.card_le_card hsub_nf
    rw [SimpleGraph.card_neighborFinset_eq_degree, hv] at hc
    exact hc
  exact sortedDesc_take_pos hr hcard_le

lemma map_sub_one_sum {l : List ℕ} (hpos : ∀ x ∈ l, 1 ≤ x) :
    (l.map (· - 1)).sum + l.length = l.sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha : 1 ≤ a := hpos a (by simp)
    have ht := ih (fun x hx => hpos x (by simp [hx]))
    simp only [List.map_cons, List.sum_cons, List.length_cons] at *
    omega

lemma hh_sum_cons {d : ℕ} {r : List ℕ} (hd : d ≤ r.length) (hpos : ∀ x ∈ r.take d, 1 ≤ x) :
    (hh (d :: r)).sum + 2 * d = (d :: r).sum := by
  have hperm : (hh (d :: r)).Perm ((r.take d).map (· - 1) ++ r.drop d) := by
    simp only [hh, SimpleGraph.havelHakimiStep, List.splitAt_eq]
    exact List.mergeSort_perm _ _
  have hsum := hperm.sum_eq
  rw [List.sum_append] at hsum
  have hmap := map_sub_one_sum hpos
  rw [List.length_take, Nat.min_eq_left hd] at hmap
  have hrsum : (r.take d).sum + (r.drop d).sum = r.sum := by
    rw [← List.sum_append, List.take_append_drop]
  rw [List.sum_cons]
  omega

lemma multiset_set {l : List ℕ} {i : ℕ} (hi : i < l.length) (v : ℕ) :
    (l.set i v : Multiset ℕ) + {l[i]} = (l : Multiset ℕ) + {v} := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a t ih =>
    cases i with
    | zero =>
      simp only [List.set_cons_zero, List.getElem_cons_zero, ← Multiset.cons_coe,
        ← Multiset.singleton_add]
      abel
    | succ i =>
      simp only [List.set_cons_succ, List.getElem_cons_succ, ← Multiset.cons_coe]
      have hi' : i < t.length := by simpa using hi
      have h := ih hi'
      calc (a ::ₘ (t.set i v : Multiset ℕ)) + {t[i]}
          = a ::ₘ ((t.set i v : Multiset ℕ) + {t[i]}) := by
              rw [← Multiset.singleton_add, ← Multiset.singleton_add, add_assoc]
        _ = a ::ₘ ((t : Multiset ℕ) + {v}) := by rw [h]
        _ = (a ::ₘ (t : Multiset ℕ)) + {v} := by
              rw [← Multiset.singleton_add, ← Multiset.singleton_add, add_assoc]

lemma sum_take_set {l : List ℕ} {i : ℕ} (hi : i < l.length) (v k : ℕ) :
    ((l.set i v).take k).sum + (if i < k then l[i] else 0) =
      (l.take k).sum + (if i < k then v else 0) := by
  induction l generalizing i k with
  | nil => simp at hi
  | cons a t ih =>
    cases k with
    | zero => simp
    | succ k =>
      cases i with
      | zero =>
        simp only [List.set_cons_zero, List.take_succ_cons, List.sum_cons,
          List.getElem_cons_zero, Nat.zero_lt_succ, ↓reduceIte]
        omega
      | succ i =>
        have hi' : i < t.length := by simpa using hi
        simp only [List.set_cons_succ, List.take_succ_cons, List.sum_cons,
          List.getElem_cons_succ, Nat.succ_lt_succ_iff]
        have h := ih hi' k
        omega

lemma sortedDesc_ext_of_perm {a b : List ℕ} (ha : SortedDesc a) (hb : SortedDesc b)
    (hperm : (a : Multiset ℕ) = (b : Multiset ℕ)) : a = b :=
  (Multiset.coe_eq_coe.mp hperm).eq_of_pairwise (fun _ _ _ _ h1 h2 => Nat.le_antisymm h2 h1) ha hb

lemma sortedDesc_set_of_bounds {l : List ℕ} (hl : SortedDesc l) {i : ℕ} (hi : i < l.length)
    (v : ℕ) (hprev : ∀ hi0 : 0 < i, v ≤ l[i - 1])
    (hnext : ∀ hi1 : i + 1 < l.length, l[i + 1] ≤ v) :
    SortedDesc (l.set i v) := by
  unfold SortedDesc
  rw [List.pairwise_iff_getElem]
  intro p q hp hq hpq
  simp only [List.length_set] at hp hq
  rw [List.getElem_set, List.getElem_set]
  split_ifs with hpi hqi
  · omega
  · have hiq_lt : i < q := by omega
    have hle : l[q] ≤ l[i + 1] := sortedDesc_ge_of_le hl (by omega : i + 1 ≤ q) hq
    exact hle.trans (hnext (by omega))
  · have hpi_lt : p < i := by omega
    have hle : l[i - 1] ≤ l[p] := sortedDesc_ge_of_le hl (by omega : p ≤ i - 1) (by omega)
    exact (hprev (by omega)).trans hle
  · exact sortedDesc_ge_of_le hl (by omega : p ≤ q) hq

lemma sortedDesc_take_eq_filter {l : List ℕ} (hl : SortedDesc l) (z : ℕ) :
    l.take (l.countP (fun w => decide (z ≤ w))) = l.filter (fun w => decide (z ≤ w)) := by
  induction l with
  | nil => simp
  | cons a r ih =>
    by_cases ha : z ≤ a
    · simp only [List.countP_cons, ha, decide_true, List.take_succ_cons, List.filter_cons, ↓reduceIte]
      congr 1
      exact ih (sortedDesc_tail hl)
    · have hr0 : r.countP (fun w => decide (z ≤ w)) = 0 := by
        rw [List.countP_eq_zero]
        intro y hy
        simp only [decide_eq_true_eq, not_le]
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hy
        have hj_le : r[j] ≤ a := sortedDesc_ge_of_le hl (Nat.zero_le (j + 1)) (by simpa using hj)
        omega
      have hfil0 : r.filter (fun w => decide (z ≤ w)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro y hy
        simp only [decide_eq_true_eq, not_le]
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hy
        have hj_le : r[j] ≤ a := sortedDesc_ge_of_le hl (Nat.zero_le (j + 1)) (by simpa using hj)
        omega
      simp [List.filter_cons, ha, hr0, hfil0]

lemma sortedDesc_lt_countP_iff {l : List ℕ} (hl : SortedDesc l) (z : ℕ) {t : ℕ}
    (ht : t < l.length) :
    t < l.countP (fun w => decide (z ≤ w)) ↔ z ≤ l[t] := by
  set px := l.countP (fun w => decide (z ≤ w))
  have hprefix := sortedDesc_take_eq_filter hl z
  constructor
  · intro htpx
    have hmem : l[t] ∈ l.take px := by
      have hi : t < (l.take px).length := by rw [List.length_take, Nat.lt_min]; exact ⟨htpx, ht⟩
      have heq : (l.take px)[t]'hi = l[t] := List.getElem_take
      rw [← heq]
      exact List.getElem_mem hi
    rw [hprefix, List.mem_filter] at hmem
    simpa using hmem.2
  · intro hzt
    by_contra hge
    have hpxt : px ≤ t := by omega
    have hdrop : (l.drop (t + 1)).countP (fun w => decide (z ≤ w)) +
        (l.take (t + 1)).countP (fun w => decide (z ≤ w)) = px := by
      rw [add_comm, ← countP_le_take_plus_drop]
    have htake_all : ∀ y ∈ l.take (t + 1), decide (z ≤ y) = true := by
      intro y hy
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hy
      have hlen_t : (l.take (t + 1)).length = min (t + 1) l.length := List.length_take
      have hjt : j ≤ t := by
        rw [hlen_t] at hj
        have := Nat.lt_of_lt_of_le hj (Nat.min_le_left _ _)
        omega
      rw [List.getElem_take]
      have hle' := sortedDesc_ge_of_le hl hjt ht
      simp; omega
    have hcnt_t1 : (l.take (t + 1)).countP (fun w => decide (z ≤ w)) = t + 1 := by
      rw [List.countP_eq_length.mpr htake_all, List.length_take, Nat.min_eq_left (by omega)]
    omega

lemma sortedDesc_countP_pos_last {l : List ℕ} (hl : SortedDesc l) {x : ℕ} (hx : x ∈ l) :
    ∃ h : 1 ≤ l.countP (fun w => decide (x ≤ w)) ∧
        l.countP (fun w => decide (x ≤ w)) ≤ l.length,
      l[l.countP (fun w => decide (x ≤ w)) - 1]'(by omega) = x ∧
        ∀ t, l.countP (fun w => decide (x ≤ w)) ≤ t → ∀ (ht : t < l.length), l[t] < x := by
  set px := l.countP (fun w => decide (x ≤ w))
  have hpos : 1 ≤ px := List.countP_pos_iff.mpr ⟨x, hx, by simp⟩
  have hle : px ≤ l.length := List.countP_le_length
  refine ⟨⟨hpos, hle⟩, ?_, ?_⟩
  · obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hx
    have hipx : i < px := (sortedDesc_lt_countP_iff hl x hi).mpr (by rw [hix])
    have hpx_lt : px - 1 < l.length := by omega
    have hl_px : x ≤ l[px - 1]'hpx_lt := (sortedDesc_lt_countP_iff hl x hpx_lt).mp (by omega)
    have hpx_le : l[px - 1]'hpx_lt ≤ l[i]'hi := sortedDesc_ge_of_le hl (by omega : i ≤ px - 1) hpx_lt
    rw [hix] at hpx_le
    change l[px - 1]'hpx_lt = x
    omega
  · intro t hpt ht
    by_contra hge
    have := (sortedDesc_lt_countP_iff hl x ht).mpr (by omega)
    omega

lemma sortedDesc_countP_first {l : List ℕ} (hl : SortedDesc l) {y : ℕ} (hy : y ∈ l) :
    ∃ h : l.countP (fun w => decide (y + 1 ≤ w)) < l.length,
      l[l.countP (fun w => decide (y + 1 ≤ w))]'h = y ∧
        ∀ t (ht : t < l.countP (fun w => decide (y + 1 ≤ w))),
          y + 1 ≤ l[t]'(Nat.lt_trans ht h) := by
  set q := l.countP (fun w => decide (y + 1 ≤ w))
  obtain ⟨i, hi, hiy⟩ := List.mem_iff_getElem.mp hy
  have hnot : ¬ (i < q) := by
    intro hlt
    have := (sortedDesc_lt_countP_iff hl (y + 1) hi).mp hlt
    omega
  have hq_le : q ≤ i := by omega
  have hq_lt : q < l.length := Nat.lt_of_le_of_lt hq_le hi
  refine ⟨hq_lt, ?_, ?_⟩
  · have hle1 : l[i] ≤ l[q] := sortedDesc_ge_of_le hl hq_le hi
    rw [hiy] at hle1
    have hlt1 : l[q] < y + 1 := by
      by_contra hge
      have := (sortedDesc_lt_countP_iff hl (y + 1) hq_lt).mpr (by omega)
      omega
    omega
  · intro t htq
    exact (sortedDesc_lt_countP_iff hl (y + 1) (Nat.lt_trans htq hq_lt)).mp htq

lemma maj_of_elementaryTransfer {a b : List ℕ} (ha : SortedDesc a) (hb : SortedDesc b)
    {x y : ℕ} (hxy : x ≥ y + 2) (hx : x ∈ a) (hy : y ∈ a)
    (hperm : (b : Multiset ℕ) + {x, y} = (a : Multiset ℕ) + {x - 1, y + 1}) :
    Maj a b := by
  have hlen : a.length = b.length := by
    have := congrArg Multiset.card hperm
    simpa using this.symm
  have hsum : a.sum = b.sum := by
    have := congrArg Multiset.sum hperm
    simp only [Multiset.sum_add, Multiset.sum_coe, Multiset.sum_pair] at this
    omega
  refine ⟨ha, hb, hlen, hsum, ?_⟩
  obtain ⟨⟨hpx_pos, hpx_le⟩, hax, ha_after_x⟩ := sortedDesc_countP_pos_last ha hx
  set px := a.countP (fun w => decide (x ≤ w))
  have hi_lt : px - 1 < a.length := by omega
  let a1 := a.set (px - 1) (x - 1)
  have ha1_sorted : SortedDesc a1 := by
    apply sortedDesc_set_of_bounds ha hi_lt (x - 1)
    · intro _
      have := sortedDesc_ge_of_le ha (by omega : px - 1 - 1 ≤ px - 1) hi_lt
      rw [hax] at this; omega
    · intro h1
      have := ha_after_x (px - 1 + 1) (by omega) h1
      omega
  have ha1_mult : (a1 : Multiset ℕ) + {x} = (a : Multiset ℕ) + {x - 1} := by
    have h := multiset_set hi_lt (x - 1)
    rwa [hax] at h
  have hy_a1 : y ∈ a1 := by
    have hmem : y ∈ (a1 : Multiset ℕ) + {x} := by
      rw [ha1_mult]
      exact Multiset.mem_add.mpr (Or.inl hy)
    rcases Multiset.mem_add.mp hmem with h | h
    · exact h
    · simp only [Multiset.mem_singleton] at h; omega
  obtain ⟨hq_lt, ha1q, ha1_before_q⟩ := sortedDesc_countP_first ha1_sorted hy_a1
  set q := a1.countP (fun w => decide (y + 1 ≤ w))
  have hi_lt_q : px - 1 < q := by
    rw [sortedDesc_lt_countP_iff ha1_sorted (y + 1) (by simpa [a1] using hi_lt)]
    simp only [a1, List.getElem_set_self]
    omega
  let b' := a1.set q (y + 1)
  have hb'_sorted : SortedDesc b' := by
    apply sortedDesc_set_of_bounds ha1_sorted hq_lt (y + 1)
    · intro _
      exact ha1_before_q (q - 1) (by omega)
    · intro h1
      have := sortedDesc_ge_of_le ha1_sorted (by omega : q ≤ q + 1) h1
      rw [ha1q] at this; omega
  have hb'_mult : (b' : Multiset ℕ) + {y} = (a1 : Multiset ℕ) + {y + 1} := by
    have h := multiset_set hq_lt (y + 1)
    rwa [ha1q] at h
  have hb'_perm : (b' : Multiset ℕ) = (b : Multiset ℕ) := by
    have h1 : (b' : Multiset ℕ) + ({x} + {y}) = (b : Multiset ℕ) + ({x} + {y}) := by
      have hp' : ({x, y} : Multiset ℕ) = {x} + {y} := by
        rw [Multiset.insert_eq_cons, Multiset.singleton_add]
      have hp'' : ({x - 1, y + 1} : Multiset ℕ) = {x - 1} + {y + 1} := by
        rw [Multiset.insert_eq_cons, Multiset.singleton_add]
      calc (b' : Multiset ℕ) + ({x} + {y})
          = ((b' : Multiset ℕ) + {y}) + {x} := by ac_rfl
        _ = ((a1 : Multiset ℕ) + {y + 1}) + {x} := by rw [hb'_mult]
        _ = ((a1 : Multiset ℕ) + {x}) + {y + 1} := by ac_rfl
        _ = ((a : Multiset ℕ) + {x - 1}) + {y + 1} := by rw [ha1_mult]
        _ = (a : Multiset ℕ) + ({x - 1} + {y + 1}) := by ac_rfl
        _ = (a : Multiset ℕ) + {x - 1, y + 1} := by rw [← hp'']
        _ = (b : Multiset ℕ) + {x, y} := hperm.symm
        _ = (b : Multiset ℕ) + ({x} + {y}) := by rw [hp']
    exact add_right_cancel h1
  have hbb' : b = b' := sortedDesc_ext_of_perm hb hb'_sorted hb'_perm.symm
  intro k
  rw [hbb']
  have hs1 := sum_take_set hi_lt (x - 1) k
  have hs2 := sum_take_set hq_lt (y + 1) k
  rw [hax] at hs1
  rw [ha1q] at hs2
  dsimp only [a1, b'] at hs2 ⊢
  by_cases hk1 : px - 1 < k <;> by_cases hk2 : q < k <;> simp only [hk1, hk2, ↓reduceIte] at hs1 hs2 <;> omega

def sumSq (l : List ℕ) : ℕ := (l.map (fun x => x * x)).sum

lemma sumSq_set {l : List ℕ} {i : ℕ} (hi : i < l.length) (v : ℕ) :
    sumSq (l.set i v) + l[i] * l[i] = sumSq l + v * v := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a t ih =>
    cases i with
    | zero =>
      simp only [sumSq, List.set_cons_zero, List.map_cons, List.sum_cons, List.getElem_cons_zero]
      omega
    | succ i =>
      have hi' : i < t.length := by simpa using hi
      have h := ih hi'
      simp only [sumSq, List.set_cons_succ, List.map_cons, List.sum_cons, List.getElem_cons_succ] at h ⊢
      omega

lemma sum_take_add_ge {a b : List ℕ} {k : ℕ} (hk : k < a.length) (hkb : k < b.length) :
    (a.take (k + 1)).sum = (a.take k).sum + a[k] ∧
      (b.take (k + 1)).sum = (b.take k).sum + b[k] := by
  constructor <;> rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
    List.sum_append, List.sum_singleton]

lemma sum_take_le_of_forall {a b : List ℕ} {n : ℕ} (hna : n ≤ a.length) (hnb : n ≤ b.length)
    (h : ∀ k (hk : k < n), a[k]'(Nat.lt_of_lt_of_le hk hna) ≤ b[k]'(Nat.lt_of_lt_of_le hk hnb)) :
    (a.take n).sum ≤ (b.take n).sum := by
  induction n with
  | zero => simp
  | succ m ih =>
    have h1 := ih (by omega) (by omega) (fun k hk => h k (by omega))
    have ⟨ha1, hb1⟩ := sum_take_add_ge (by omega : m < a.length) (by omega : m < b.length)
    have hm := h m (by omega)
    omega

lemma sum_eq_of_forall_le {a b : List ℕ} (hlen : a.length = b.length) (hsum : a.sum = b.sum)
    (h : ∀ k (hk : k < a.length), b[k]'(hlen ▸ hk) ≤ a[k]'hk) : a = b := by
  induction a generalizing b with
  | nil => cases b with | nil => rfl | cons => simp at hlen
  | cons x xs ih =>
    cases b with
    | nil => simp at hlen
    | cons y ys =>
      have hxy : y ≤ x := h 0 (by simp)
      have hxs : xs.length = ys.length := by simpa using hlen
      have htail : ∀ k (hk : k < xs.length), ys[k]'(hxs ▸ hk) ≤ xs[k]'hk :=
        fun k hk => h (k + 1) (by simp; omega)
      have htail_sum : ys.sum ≤ xs.sum := by
        have ht := sum_take_le_of_forall (a := ys) (b := xs) (n := xs.length) (by omega) le_rfl (fun k hk => htail k hk)
        rwa [List.take_of_length_le (by omega), List.take_length] at ht
      simp only [List.sum_cons] at hsum
      have heq1 : x = y := by omega
      have heq2 : xs.sum = ys.sum := by omega
      subst heq1
      rw [ih hxs heq2 htail]

lemma maj_induction (P : List ℕ → Prop)
    (hstep : ∀ a a', IsGraphical a → SortedDesc a' →
      (∃ x y, x ≥ y + 2 ∧ x ∈ a ∧ y ∈ a ∧
        (a' : Multiset ℕ) + {x, y} = (a : Multiset ℕ) + {x - 1, y + 1}) →
      P a' → P a)
    {a b : List ℕ} (ha : IsGraphical a) (hab : Maj a b) :
    P b → P a := by
  intro hPb
  induction hsq : sumSq a using Nat.strong_induction_on generalizing a with
  | _ m ih =>
    rcases hab with ⟨ha_sort, hb_sort, hlen, hsum, htake⟩
    by_cases heq : a = b
    · rwa [heq]
    · have hex_lt : ∃ j, ∃ (hj : j < a.length), a[j] < b[j]'(by omega) := by
        by_contra hnone
        push Not at hnone
        exact heq (sum_eq_of_forall_le hlen hsum (fun k hk => hnone k hk))
      let J : Finset (Fin a.length) :=
        Finset.univ.filter (fun k => a[k.1] < b[k.1]'(by omega))
      have hJ : J.Nonempty := by
        obtain ⟨j, hj, hlt⟩ := hex_lt
        exact ⟨⟨j, hj⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩⟩
      let jFin := J.min' hJ
      let j := jFin.1
      have hj_mem := Finset.min'_mem J hJ
      have hj_lt : j < a.length := jFin.2
      have hj_ltb : j < b.length := by omega
      have haj_lt : a[j] < b[j] := (Finset.mem_filter.mp hj_mem).2
      have hbefore_j : ∀ t (ht : t < j), b[t]'(by omega) ≤ a[t]'(by omega) := by
        intro t ht
        have ht_lt : t < a.length := Nat.lt_trans ht hj_lt
        have ht_ltb : t < b.length := by omega
        by_contra hlt
        have ht_mem : ⟨t, ht_lt⟩ ∈ J := by
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, Nat.lt_of_not_le hlt⟩
        have hmin := Finset.min'_le J ⟨t, ht_lt⟩ ht_mem
        exact Nat.not_le_of_lt ht hmin
      have hex_gt : ∃ i, ∃ (hi : i < j), b[i]'(Nat.lt_trans hi hj_ltb) < a[i]'(Nat.lt_trans hi hj_lt) := by
        by_contra hnone
        push Not at hnone
        have hle_j : (a.take j).sum ≤ (b.take j).sum :=
          sum_take_le_of_forall (by omega) (by omega) (fun k hk => hnone k hk)
        have ⟨ha1, hb1⟩ := sum_take_add_ge hj_lt hj_ltb
        have htake_j1 := htake (j + 1)
        omega
      let I : Finset (Fin a.length) :=
        Finset.univ.filter (fun k => k.1 < j ∧ b[k.1]'(by omega) < a[k.1]'(by omega))
      have hI : I.Nonempty := by
        obtain ⟨i, hij, hgt⟩ := hex_gt
        exact ⟨⟨i, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij, hgt⟩⟩
      let iFin := I.max' hI
      let i := iFin.1
      have hi_mem := Finset.max'_mem I hI
      have hi_ltj : i < j := (Finset.mem_filter.mp hi_mem).2.1
      have hi_lt : i < a.length := by omega
      have hi_ltb : i < b.length := by omega
      have hbi_lt : b[i] < a[i] := (Finset.mem_filter.mp hi_mem).2.2
      have hmid_eq : ∀ t (ht1 : i < t) (ht2 : t < j), a[t]'(by omega) = b[t]'(by omega) := by
        intro t ht1 ht2
        have h1 : b[t]'(by omega) ≤ a[t]'(by omega) := hbefore_j t ht2
        have h2 : ¬ (t < j ∧ b[t]'(by omega) < a[t]'(by omega)) := by
          intro hmem
          have hmax := Finset.le_max' I ⟨t, by omega⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩)
          exact Nat.not_le_of_lt ht1 hmax
        omega
      have hgap : a[i] ≥ a[j] + 2 := by
        have hb_mono : b[j] ≤ b[i] := sortedDesc_ge_of_le hb_sort (by omega) hj_ltb
        omega
      let a' := (a.set i (a[i] - 1)).set j (a[j] + 1)
      have ha'_sorted : SortedDesc a' := by
        have ha1_sorted : SortedDesc (a.set i (a[i] - 1)) := by
          apply sortedDesc_set_of_bounds ha_sort hi_lt (a[i] - 1)
          · intro _
            have := sortedDesc_ge_of_le ha_sort (by omega : i - 1 ≤ i) hi_lt
            omega
          · intro h1
            by_cases hltj : i + 1 < j
            · have hm := hmid_eq (i + 1) (by omega) hltj
              have hbm := sortedDesc_ge_of_le hb_sort (by omega : i ≤ i + 1) (by omega)
              omega
            · have heqj : i + 1 = j := by omega
              have ha_eq : a[i + 1]'h1 = a[j]'hj_lt := by congr 1
              omega
        have hi_lt' : j < (a.set i (a[i] - 1)).length := by simpa using hj_lt
        apply sortedDesc_set_of_bounds ha1_sorted hi_lt' (a[j] + 1)
        · intro _
          rw [List.getElem_set]
          split_ifs with hj1
          · omega
          · have hm := hmid_eq (j - 1) (by omega) (by omega)
            have hbm := sortedDesc_ge_of_le hb_sort (by omega : j - 1 ≤ j) hj_ltb
            omega
        · intro h1
          have h1' : j + 1 < a.length := by simpa using h1
          rw [List.getElem_set]
          split_ifs with hj1
          · omega
          · have := sortedDesc_ge_of_le ha_sort (by omega : j ≤ j + 1) h1'
            omega
      have ha'_mult : (a' : Multiset ℕ) + {a[i], a[j]} = (a : Multiset ℕ) + {a[i] - 1, a[j] + 1} := by
        have hm1 := multiset_set hi_lt (a[i] - 1)
        have hi_lt' : j < (a.set i (a[i] - 1)).length := by simpa using hj_lt
        have hm2 := multiset_set hi_lt' (a[j] + 1)
        have hget : (a.set i (a[i] - 1))[j]'hi_lt' = a[j] := by
          rw [List.getElem_set]; split_ifs with h; exact absurd h.symm (by omega); rfl
        rw [hget] at hm2
        have hp1 : ({a[i], a[j]} : Multiset ℕ) = {a[i]} + {a[j]} := by
          rw [Multiset.insert_eq_cons, Multiset.singleton_add]
        have hp2 : ({a[i] - 1, a[j] + 1} : Multiset ℕ) = {a[i] - 1} + {a[j] + 1} := by
          rw [Multiset.insert_eq_cons, Multiset.singleton_add]
        rw [hp1, hp2]
        calc (a' : Multiset ℕ) + ({a[i]} + {a[j]})
            = ((a' : Multiset ℕ) + {a[j]}) + {a[i]} := by ac_rfl
          _ = (((a.set i (a[i] - 1) : List ℕ) : Multiset ℕ) + {a[j] + 1}) + {a[i]} := by rw [hm2]
          _ = (((a.set i (a[i] - 1) : List ℕ) : Multiset ℕ) + {a[i]}) + {a[j] + 1} := by ac_rfl
          _ = ((a : Multiset ℕ) + {a[i] - 1}) + {a[j] + 1} := by rw [hm1]
          _ = (a : Multiset ℕ) + ({a[i] - 1} + {a[j] + 1}) := by ac_rfl
      have ha'_graph : IsGraphical a' :=
        isGraphical_robinHood ha ha'_sorted hgap (List.getElem_mem hi_lt) (List.getElem_mem hj_lt) ha'_mult
      have ha'_len : a'.length = b.length := by simp [a', hlen]
      have ha'_sum : a'.sum = b.sum := by
        have := congrArg Multiset.sum ha'_mult
        simp only [Multiset.sum_add, Multiset.sum_coe, Multiset.sum_pair] at this
        omega
      have ha'_take : ∀ k, (b.take k).sum ≤ (a'.take k).sum := by
        intro k
        have hs1 := sum_take_set hi_lt (a[i] - 1) k
        have hi_lt' : j < (a.set i (a[i] - 1)).length := by simpa using hj_lt
        have hs2 := sum_take_set hi_lt' (a[j] + 1) k
        have hget : (a.set i (a[i] - 1))[j]'hi_lt' = a[j] := by
          rw [List.getElem_set]; split_ifs with h; exact absurd h.symm (by omega); rfl
        rw [hget] at hs2
        dsimp only [a'] at hs2 ⊢
        by_cases hki : i < k
        · by_cases hkj : j < k
          · simp only [hki, hkj, ↓reduceIte] at hs1 hs2
            have := htake k
            omega
          · simp only [hki, hkj, ↓reduceIte] at hs1 hs2
            have hdiff_i : (b.take (i + 1)).sum < (a.take (i + 1)).sum := by
              have ⟨hai, hbi⟩ := sum_take_add_ge hi_lt hi_ltb
              have hi0 := htake i
              omega
            have hdiff_k : ∀ d, i + 1 + d ≤ j →
                (a.take (i + 1 + d)).sum + (b.take (i + 1)).sum =
                  (b.take (i + 1 + d)).sum + (a.take (i + 1)).sum := by
              intro d hd
              induction d with
              | zero => simp [add_comm]
              | succ d ihd =>
                have ⟨ha1, hb1⟩ := sum_take_add_ge (by omega : i + 1 + d < a.length) (by omega : i + 1 + d < b.length)
                have hmeq := hmid_eq (i + 1 + d) (by omega) (by omega)
                have ha1' : (a.take (i + 1 + (d + 1))).sum = (a.take (i + 1 + d)).sum + b[i + 1 + d]'(by omega) := by
                  have hassoc : i + 1 + (d + 1) = i + 1 + d + 1 := by omega
                  rw [hassoc, ha1, hmeq]
                have hb1' : (b.take (i + 1 + (d + 1))).sum = (b.take (i + 1 + d)).sum + b[i + 1 + d]'(by omega) := by
                  have hassoc : i + 1 + (d + 1) = i + 1 + d + 1 := by omega
                  rw [hassoc, hb1]
                have := ihd (by omega)
                omega
            have hk_ge : i + 1 ≤ k := by omega
            have hd_eq : k = i + 1 + (k - (i + 1)) := by omega
            have hdk := hdiff_k (k - (i + 1)) (by omega)
            rw [← hd_eq] at hdk
            omega
        · have hnkj : ¬ j < k := by omega
          simp only [hki, hnkj, ↓reduceIte] at hs1 hs2
          have := htake k
          omega
      have ha'_maj : Maj a' b := ⟨ha'_sorted, hb_sort, ha'_len, ha'_sum, ha'_take⟩
      have ha'_sq : sumSq a' < sumSq a := by
        have hs1 := sumSq_set hi_lt (a[i] - 1)
        have hi_lt' : j < (a.set i (a[i] - 1)).length := by simpa using hj_lt
        have hs2 := sumSq_set hi_lt' (a[j] + 1)
        have hget : (a.set i (a[i] - 1))[j]'hi_lt' = a[j] := by
          rw [List.getElem_set]; split_ifs with h; exact absurd h.symm (by omega); rfl
        rw [hget] at hs2
        dsimp only [a'] at hs2 ⊢
        have hsub : (a[i] - 1) * (a[i] - 1) + (a[j] + 1) * (a[j] + 1) < a[i] * a[i] + a[j] * a[j] := by
          have hstep1 : (a[i] - 1 + 1) * (a[i] - 1 + 1) = a[i] * a[i] := by
            have : a[i] - 1 + 1 = a[i] := by omega
            rw [this]
          have h1 : (a[i] - 1 + 1) * (a[i] - 1 + 1) = (a[i] - 1) * (a[i] - 1) + 2 * (a[i] - 1) + 1 := by ring
          have h2 : (a[j] + 1) * (a[j] + 1) = a[j] * a[j] + 2 * a[j] + 1 := by ring
          omega
        omega
      have hPa' : P a' := ih (sumSq a') (hsq ▸ ha'_sq) ha'_graph ha'_maj rfl
      exact hstep a a' ha ha'_sorted ⟨a[i], a[j], hgap, List.getElem_mem hi_lt, List.getElem_mem hj_lt, ha'_mult⟩ hPa'

end Majorization

/- Triesch invariant for hhIter sum comparison -/

section Triesch

open scoped Classical

noncomputable def decTop (M : ℕ) (r : List ℕ) : Multiset ℕ :=
  Multiset.map (· - 1) (r.take M : Multiset ℕ) + (r.drop M : Multiset ℕ)

lemma hh_coe_eq_decTop (M : ℕ) (r : List ℕ) :
    (hh (M :: r) : Multiset ℕ) = decTop M r := by
  simp only [hh, SimpleGraph.havelHakimiStep, List.splitAt_eq, decTop]
  have hp := Multiset.coe_eq_coe.mpr (List.mergeSort_perm ((r.take M).map (· - 1) ++ r.drop M) (· ≥ ·))
  rw [hp, ← Multiset.coe_add, Multiset.map_coe]

lemma drop_eq_getElem_cons {α : Type*} {l : List α} {M : ℕ} (hM : M < l.length) :
    l.drop M = l[M] :: l.drop (M + 1) := by
  induction l generalizing M with
  | nil => simp at hM
  | cons a t ih =>
    cases M with
    | zero => simp
    | succ M =>
      simp only [List.drop_succ_cons, List.getElem_cons_succ]
      exact ih (by simpa using hM)

lemma take_set_of_lt {α : Type*} (l : List α) (q M : ℕ) (v : α) (hq : q < M) :
    (l.set q v).take M = (l.take M).set q v := by
  induction l generalizing q M with
  | nil => simp
  | cons a t ih =>
    cases M with
    | zero => omega
    | succ M =>
      cases q with
      | zero => simp
      | succ q =>
        simp only [List.set_cons_succ, List.take_succ_cons, ih q M (by omega)]

lemma take_set_of_le {α : Type*} (l : List α) (q M : ℕ) (v : α) (hq : M ≤ q) :
    (l.set q v).take M = l.take M := by
  induction l generalizing q M with
  | nil => simp
  | cons a t ih =>
    cases M with
    | zero => simp
    | succ M =>
      cases q with
      | zero => omega
      | succ q =>
        simp only [List.set_cons_succ, List.take_succ_cons, ih q M (by omega)]

lemma drop_set_of_lt {α : Type*} (l : List α) (q M : ℕ) (v : α) (hq : q < M) :
    (l.set q v).drop M = l.drop M := by
  induction l generalizing q M with
  | nil => simp
  | cons a t ih =>
    cases M with
    | zero => omega
    | succ M =>
      cases q with
      | zero => simp
      | succ q =>
        simp only [List.set_cons_succ, List.drop_succ_cons, ih q M (by omega)]

lemma drop_set_of_le {α : Type*} (l : List α) (q M : ℕ) (v : α) (hq : M ≤ q) :
    (l.set q v).drop M = (l.drop M).set (q - M) v := by
  induction l generalizing q M with
  | nil => simp
  | cons a t ih =>
    cases M with
    | zero => simp
    | succ M =>
      cases q with
      | zero => omega
      | succ q =>
        simp only [List.set_cons_succ, List.drop_succ_cons, Nat.succ_sub_succ_eq_sub, ih q M (by omega)]

lemma decTop_succ {M : ℕ} {r : List ℕ} (hM : M < r.length) :
    decTop M r + {r[M] - 1} = decTop (M + 1) r + {r[M]} := by
  simp only [decTop]
  have htake : r.take (M + 1) = r.take M ++ [r[M]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hM, Option.toList_some]
  have hdrop : r.drop M = r[M] :: r.drop (M + 1) := drop_eq_getElem_cons hM
  rw [htake, hdrop, ← Multiset.coe_add, Multiset.map_add, ← Multiset.cons_coe,
    ← Multiset.singleton_add]
  simp only [Multiset.coe_singleton, Multiset.map_singleton]
  abel

lemma decTop_card {M : ℕ} {r : List ℕ} : (decTop M r).card = r.length := by
  simp only [decTop, Multiset.card_add, Multiset.card_map, Multiset.coe_card,
    List.length_take, List.length_drop]
  omega

lemma countP_mono {α : Type*} (p q : α → Bool) (h : ∀ a, p a = true → q a = true) (l : List α) :
    l.countP p ≤ l.countP q := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.countP_cons]
    by_cases hp : p a = true
    · have hq := h a hp
      simp [hp, hq]; exact ih
    · have hp' : p a = false := Bool.eq_false_iff.mpr hp
      simp only [hp', Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      split_ifs <;> omega

lemma filter_card_coe {l : List ℕ} {t : ℕ} :
    ((l : Multiset ℕ).filter (fun w => t ≤ w)).card = l.countP (fun w => decide (t ≤ w)) := by
  induction l with
  | nil => simp
  | cons a r ih =>
    rw [← Multiset.cons_coe, Multiset.filter_cons]
    by_cases h : t ≤ a
    · simp only [h, ↓reduceIte, Multiset.card_add, Multiset.card_singleton, List.countP_cons,
        decide_true, ih]; omega
    · simp only [h, ↓reduceIte, Multiset.card_add, Multiset.card_zero, zero_add, List.countP_cons,
        decide_false, Bool.false_eq_true, ih, Nat.add_zero]

lemma countP_succ_le_decTop (M : ℕ) (r : List ℕ) (t : ℕ) :
    r.countP (fun w => decide (t + 1 ≤ w)) ≤
      ((decTop M r).filter (fun w => t ≤ w)).card := by
  simp only [decTop, Multiset.filter_add, Multiset.card_add]
  have h1 : (r.take M).countP (fun w => decide (t + 1 ≤ w)) ≤
      ((Multiset.map (· - 1) (r.take M : Multiset ℕ)).filter (fun w => t ≤ w)).card := by
    have hmap : Multiset.map (· - 1) (r.take M : Multiset ℕ) =
        (((r.take M).map (· - 1) : List ℕ) : Multiset ℕ) := (Multiset.map_coe _ _).symm
    rw [hmap, filter_card_coe, List.countP_map]
    apply countP_mono
    intro a ha
    simp only [Function.comp_def, decide_eq_true_eq] at ha ⊢
    omega
  have h2 : (r.drop M).countP (fun w => decide (t + 1 ≤ w)) ≤
      ((r.drop M : Multiset ℕ).filter (fun w => t ≤ w)).card := by
    rw [filter_card_coe]
    apply countP_mono
    intro a ha
    simp only [decide_eq_true_eq] at ha ⊢
    omega
  have h3 := countP_le_take_plus_drop (fun w => decide (t + 1 ≤ w)) r M
  omega

lemma countP_ge_zero {l : List ℕ} : l.countP (fun w => decide (0 ≤ w)) = l.length := by
  rw [List.countP_eq_length]
  intro w _; simp

lemma countP_le_of_add_eq {l1 l2 : List ℕ} {a b t : ℕ}
    (h : (l1 : Multiset ℕ) + {a} = (l2 : Multiset ℕ) + {b}) :
    l1.countP (fun w => decide (t ≤ w)) + (if t ≤ a then 1 else 0) =
      l2.countP (fun w => decide (t ≤ w)) + (if t ≤ b then 1 else 0) := by
  have hc := congrArg (fun m : Multiset ℕ => (m.filter (fun w => t ≤ w)).card) h
  simp only [Multiset.filter_add, Multiset.card_add, filter_card_coe] at hc
  have ha : (({a} : Multiset ℕ).filter (fun w => t ≤ w)).card = if t ≤ a then 1 else 0 := by
    rw [Multiset.filter_singleton]; split_ifs <;> simp
  have hb : (({b} : Multiset ℕ).filter (fun w => t ≤ w)).card = if t ≤ b then 1 else 0 := by
    rw [Multiset.filter_singleton]; split_ifs <;> simp
  omega

def bump1 (r : List ℕ) (y : ℕ) : List ℕ :=
  r.set (r.countP (fun w => decide (y + 1 ≤ w))) (y + 1)

lemma bump1_spec {r : List ℕ} (hr : SortedDesc r) {y : ℕ} (hy : y ∈ r) :
    let q := r.countP (fun w => decide (y + 1 ≤ w))
    ∃ hq : q < r.length, r[q]'hq = y ∧ SortedDesc (bump1 r y) ∧
      (bump1 r y : Multiset ℕ) + {y} = (r : Multiset ℕ) + {y + 1} := by
  obtain ⟨hq, hrq, hbef⟩ := sortedDesc_countP_first hr hy
  refine ⟨hq, hrq, ?_, ?_⟩
  · apply sortedDesc_set_of_bounds hr hq (y + 1)
    · intro _
      exact hbef _ (by omega)
    · intro h1
      have := sortedDesc_ge_of_le hr (by omega : r.countP (fun w => decide (y + 1 ≤ w)) ≤
        r.countP (fun w => decide (y + 1 ≤ w)) + 1) h1
      omega
  · have h := multiset_set hq (y + 1)
    rwa [hrq] at h

lemma bump1_length {r : List ℕ} {y : ℕ} : (bump1 r y).length = r.length :=
  List.length_set

lemma bump1_getElem_self {r : List ℕ} {y : ℕ}
    (h : r.countP (fun w => decide (y + 1 ≤ w)) < (bump1 r y).length) :
    (bump1 r y)[r.countP (fun w => decide (y + 1 ≤ w))]'h = y + 1 :=
  List.getElem_set_self h

lemma decTop_bump1_lt {r : List ℕ} (hr : SortedDesc r) {y M : ℕ} (hy : y ∈ r)
    (h1y : 1 ≤ y) (hqM : r.countP (fun w => decide (y + 1 ≤ w)) < M) :
    decTop M (bump1 r y) + {y - 1} = decTop M r + {y} := by
  obtain ⟨hq, hrq, _, _⟩ := bump1_spec hr hy
  set q := r.countP (fun w => decide (y + 1 ≤ w))
  simp only [decTop, bump1]
  rw [take_set_of_lt r q M (y + 1) hqM, drop_set_of_lt r q M (y + 1) hqM]
  have hq_take : q < (r.take M).length := by rw [List.length_take, Nat.lt_min]; exact ⟨hqM, hq⟩
  have hm := multiset_set hq_take (y + 1)
  have hrq_take : (r.take M)[q]'hq_take = y := by rw [List.getElem_take]; exact hrq
  rw [hrq_take] at hm
  have hmap := congrArg (Multiset.map (· - 1)) hm
  simp only [Multiset.map_add, Multiset.map_singleton, Nat.add_sub_cancel] at hmap
  calc (Multiset.map (· - 1) ↑((r.take M).set q (y + 1)) + ↑(r.drop M)) + {y - 1}
      = (Multiset.map (· - 1) ↑((r.take M).set q (y + 1)) + {y - 1}) + ↑(r.drop M) := by ac_rfl
    _ = (Multiset.map (· - 1) ↑(r.take M) + {y}) + ↑(r.drop M) := by rw [hmap]
    _ = (Multiset.map (· - 1) ↑(r.take M) + ↑(r.drop M)) + {y} := by ac_rfl

lemma decTop_bump1_ge {r : List ℕ} (hr : SortedDesc r) {y M : ℕ} (hy : y ∈ r)
    (hqM : M ≤ r.countP (fun w => decide (y + 1 ≤ w))) :
    decTop M (bump1 r y) + {y} = decTop M r + {y + 1} := by
  obtain ⟨hq, hrq, _, _⟩ := bump1_spec hr hy
  set q := r.countP (fun w => decide (y + 1 ≤ w))
  simp only [decTop, bump1]
  rw [take_set_of_le r q M (y + 1) hqM, drop_set_of_le r q M (y + 1) hqM]
  have hq_drop : q - M < (r.drop M).length := by rw [List.length_drop]; omega
  have hm := multiset_set hq_drop (y + 1)
  have hrq_drop : (r.drop M)[q - M]'hq_drop = y := by
    rw [List.getElem_drop]
    have hidx : M + (q - M) = q := by omega
    convert hrq
  rw [hrq_drop] at hm
  calc (Multiset.map (· - 1) ↑(r.take M) + ↑((r.drop M).set (q - M) (y + 1))) + {y}
      = Multiset.map (· - 1) ↑(r.take M) + (↑((r.drop M).set (q - M) (y + 1)) + {y}) := by ac_rfl
    _ = Multiset.map (· - 1) ↑(r.take M) + (↑(r.drop M) + {y + 1}) := by rw [hm]
    _ = (Multiset.map (· - 1) ↑(r.take M) + ↑(r.drop M)) + {y + 1} := by ac_rfl

def P1 (v u : List ℕ) : Prop :=
  ∃ x y, 1 ≤ y ∧ y ≤ x ∧ ({x - 1, y - 1} : Multiset ℕ) ≤ (v : Multiset ℕ) ∧
    (u : Multiset ℕ) + {x - 1, y - 1} = (v : Multiset ℕ) + {x, y} ∧
    x + 1 ≤ v.countP (fun w => decide (y - 1 ≤ w))

def P2 (v u : List ℕ) : Prop :=
  ∃ z, 2 ≤ z ∧ z ≤ v.headI + 1 ∧ (z - 2) ∈ v ∧
    (u : Multiset ℕ) + {z - 2} = (v : Multiset ℕ) + {z} ∧
    z + 1 ≤ v.countP (fun w => decide (z - 2 ≤ w)) ∧
    ((z - 1) ∈ v ∨ z ≤ v.countP (fun w => decide (z - 1 ≤ w)))

def Inv (v u : List ℕ) : Prop :=
  IsGraphical v ∧ IsGraphical u ∧ (P1 v u ∨ P2 v u)

lemma inv_pair_coe {a b : ℕ} : ({a, b} : Multiset ℕ) = {a} + {b} := by
  rw [Multiset.insert_eq_cons, Multiset.singleton_add]

lemma multiset_le_iff_exists_add {m1 m2 : Multiset ℕ} :
    m1 ≤ m2 ↔ ∃ s, m2 = m1 + s :=
  ⟨fun h => ⟨m2 - m1, (add_tsub_cancel_of_le h).symm⟩, fun ⟨s, hs⟩ => hs ▸ le_self_add⟩

lemma sortedDesc_pair_le_tail {d x y : ℕ} {r : List ℕ}
    (h1 : ({x, y} : Multiset ℕ) ≤ ((d :: r : List ℕ) : Multiset ℕ))
    (hx : x < d) (hy : y < d) :
    ({x, y} : Multiset ℕ) ≤ (r : Multiset ℕ) := by
  have hcons : ((d :: r : List ℕ) : Multiset ℕ) = d ::ₘ (r : Multiset ℕ) := rfl
  rw [hcons, ← Multiset.singleton_add] at h1
  rw [inv_pair_coe] at h1 ⊢
  obtain ⟨s, hs⟩ := multiset_le_iff_exists_add.mp h1
  have hxd : x ≠ d := by omega
  have hyd : y ≠ d := by omega
  have hds : d ∈ s := by
    have hmem : d ∈ {x} + {y} + s := by rw [← hs]; exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton_self d))
    rcases Multiset.mem_add.mp hmem with h | h
    · rcases Multiset.mem_add.mp h with h | h <;> simp at h <;> omega
    · exact h
  obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem hds
  rw [ht, ← Multiset.singleton_add] at hs
  have hs' : {d} + (r : Multiset ℕ) = {d} + ({x} + {y} + t) := by
    rw [hs]; ac_rfl
  exact multiset_le_iff_exists_add.mpr ⟨t, add_left_cancel hs'⟩

lemma sortedDesc_head_ge_of_mem {d x : ℕ} {r : List ℕ} (hs : SortedDesc (d :: r)) (hx : x ∈ d :: r) :
    x ≤ d := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  exact sortedDesc_ge_of_le hs (Nat.zero_le i) hi

lemma mem_of_pair_le {x y : ℕ} {m : Multiset ℕ} (h : ({x, y} : Multiset ℕ) ≤ m) :
    x ∈ m ∧ y ∈ m := by
  rw [inv_pair_coe] at h
  obtain ⟨s, rfl⟩ := multiset_le_iff_exists_add.mp h
  exact ⟨by simp, by simp⟩

lemma erase_sortedDesc {l : List ℕ} (hl : SortedDesc l) (a : ℕ) :
    SortedDesc (l.erase a) := by
  induction l with
  | nil => simp [SortedDesc]
  | cons x t ih =>
    by_cases hxa : x = a
    · subst hxa
      simp only [List.erase_cons_head]
      exact sortedDesc_tail hl
    · have hne : ¬ (x == a) = true := by simp [hxa]
      rw [List.erase_cons_tail hne]
      exact List.Pairwise.cons
        (fun y hy => (List.pairwise_cons.mp hl).1 y (List.mem_of_mem_erase hy))
        (ih (sortedDesc_tail hl))

lemma multiset_erase_add {l : List ℕ} {a : ℕ} (ha : a ∈ l) :
    ((l.erase a : List ℕ) : Multiset ℕ) + {a} = (l : Multiset ℕ) := by
  induction l with
  | nil => simp at ha
  | cons x t ih =>
    by_cases hxa : x = a
    · subst hxa
      simp [List.erase_cons_head, ← Multiset.cons_coe, ← Multiset.singleton_add, add_comm]
    · have ha' : a ∈ t := by simpa [Ne.symm hxa] using ha
      have hne : ¬ (x == a) = true := by simp [hxa]
      rw [List.erase_cons_tail hne, ← Multiset.cons_coe, ← Multiset.singleton_add,
        ← Multiset.cons_coe, ← Multiset.singleton_add, add_assoc, ih ha']

lemma erase_append_of_mem {l1 l2 : List ℕ} {a : ℕ} (h : a ∈ l1) :
    (l1 ++ l2).erase a = l1.erase a ++ l2 := by
  induction l1 with
  | nil => simp at h
  | cons x t ih =>
    by_cases hxa : x = a
    · subst hxa; simp [List.erase_cons_head]
    · have h' : a ∈ t := by simpa [Ne.symm hxa] using h
      have hne : ¬ (x == a) = true := by simp [hxa]
      simp [List.erase_cons_tail hne, ih h']

lemma erase_append_of_notMem {l1 l2 : List ℕ} {a : ℕ} (h : a ∉ l1) :
    (l1 ++ l2).erase a = l1 ++ l2.erase a := by
  induction l1 with
  | nil => simp
  | cons x t ih =>
    have hxa : x ≠ a := fun heq => h (by simp [heq])
    have ht : a ∉ t := fun hm => h (by simp [hm])
    have hne : ¬ (x == a) = true := by simp [hxa]
    simp [List.erase_cons_tail hne, ih ht]

lemma decTop_erase_head {r : List ℕ} (hr : SortedDesc r) {M : ℕ} (h1M : 1 ≤ M)
    (hM : M < r.length) (hle : M - 1 ≤ r[M]) (ha : M - 1 ∈ r)
    (hhead : ∀ x ∈ r, x ≤ M) :
    decTop M r = decTop (M + 1) (M :: r.erase (M - 1)) := by
  have htakeM : (M :: r.erase (M - 1)).take (M + 1) = M :: (r.erase (M - 1)).take M := by simp
  have hdropM : (M :: r.erase (M - 1)).drop (M + 1) = (r.erase (M - 1)).drop M := by simp
  by_cases hmem : M - 1 ∈ r.take M
  · have hsplit : r = r.take M ++ r[M] :: r.drop (M + 1) := by
      conv_lhs => rw [← List.take_append_drop M r, drop_eq_getElem_cons hM]
    have her : r.erase (M - 1) = (r.take M).erase (M - 1) ++ r[M] :: r.drop (M + 1) := by
      conv_lhs => rw [hsplit]
      exact erase_append_of_mem hmem
    have hlen_er : ((r.take M).erase (M - 1)).length = M - 1 := by
      rw [List.length_erase_of_mem hmem, List.length_take, Nat.min_eq_left (by omega)]
    have htake_er : (r.erase (M - 1)).take M = (r.take M).erase (M - 1) ++ [r[M]] := by
      rw [her, List.take_append, List.take_of_length_le (by omega), hlen_er]
      have : M - (M - 1) = 1 := by omega
      rw [this, List.take_succ_cons, List.take_zero]
    have hdrop_er : (r.erase (M - 1)).drop M = r.drop (M + 1) := by
      rw [her, List.drop_append, hlen_er, List.drop_of_length_le (by omega)]
      have : M - (M - 1) = 1 := by omega
      simp [this]
    have hrm_eq : r[M] = M - 1 := by
      obtain ⟨i, hi, hri⟩ := List.mem_iff_getElem.mp hmem
      have hi_M : i < M := by rw [List.length_take] at hi; exact Nat.lt_of_lt_of_le hi (Nat.min_le_left _ _)
      have hge := sortedDesc_ge_of_le hr (by omega : i ≤ M) hM
      rw [List.getElem_take] at hri
      omega
    have hm_take := multiset_erase_add hmem
    simp only [decTop, htakeM, hdropM, htake_er, hdrop_er]
    rw [drop_eq_getElem_cons hM, hrm_eq]
    have hm_list : ((M :: ((r.take M).erase (M - 1) ++ [M - 1]) : List ℕ) : Multiset ℕ) =
        {M} + (r.take M : Multiset ℕ) := by
      have h1 : (((r.take M).erase (M - 1) ++ [M - 1] : List ℕ) : Multiset ℕ) = (r.take M : Multiset ℕ) := by
        exact (Multiset.coe_add _ _).symm.trans hm_take
      rw [← Multiset.cons_coe, ← Multiset.singleton_add, h1]
    rw [hm_list, Multiset.map_add, Multiset.map_singleton, ← Multiset.cons_coe, ← Multiset.singleton_add]
    abel
  · have hsplit : r = r.take M ++ r.drop M := (List.take_append_drop M r).symm
    have her : r.erase (M - 1) = r.take M ++ (r.drop M).erase (M - 1) := by
      conv_lhs => rw [hsplit]
      exact erase_append_of_notMem hmem
    have hlen_t : (r.take M).length = M := List.length_take_of_le (by omega)
    have htake_er : (r.erase (M - 1)).take M = r.take M := by
      rw [her, List.take_append, hlen_t, Nat.sub_self, List.take_zero, List.append_nil,
        List.take_of_length_le (by omega)]
    have hdrop_er : (r.erase (M - 1)).drop M = (r.drop M).erase (M - 1) := by
      rw [her, List.drop_append, hlen_t, Nat.sub_self, List.drop_zero,
        List.drop_of_length_le (by omega), List.nil_append]
    have ha_drop : M - 1 ∈ r.drop M := by
      have ha' : M - 1 ∈ r.take M ++ r.drop M := by rw [← hsplit]; exact ha
      rcases List.mem_append.mp ha' with h1 | h2
      · exact absurd h1 hmem
      · exact h2
    have hm_drop := multiset_erase_add ha_drop
    simp only [decTop, htakeM, hdropM, htake_er, hdrop_er]
    rw [← Multiset.cons_coe, ← Multiset.singleton_add, Multiset.map_add, Multiset.map_singleton]
    have hgoal : (Multiset.map (· - 1) (r.take M : Multiset ℕ) + (r.drop M : Multiset ℕ)) =
        Multiset.map (· - 1) (r.take M : Multiset ℕ) + ({M - 1} + ((r.drop M).erase (M - 1) : Multiset ℕ)) := by
      rw [add_comm ({M - 1} : Multiset ℕ) ((r.drop M).erase (M - 1) : Multiset ℕ), hm_drop]
    rw [hgoal]; abel

lemma headI_ge_of_mem {l : List ℕ} (hl : SortedDesc l) {a : ℕ} (ha : a ∈ l) : a ≤ l.headI := by
  cases l with
  | nil => simp at ha
  | cons d r => exact sortedDesc_head_ge_of_mem hl ha

lemma pair_le_of_distinct_take {r : List ℕ} {i j M : ℕ} (hi : i < M) (hj : j < M)
    (hM : M ≤ r.length) (hij : i ≠ j) :
    ({r[i]'(by omega), r[j]'(by omega)} : Multiset ℕ) ≤ (r.take M : Multiset ℕ) := by
  have hi_t : i < (r.take M).length := by rw [List.length_take, Nat.min_eq_left hM]; exact hi
  have hj_t : j < (r.take M).length := by rw [List.length_take, Nat.min_eq_left hM]; exact hj
  have h1 : r[i]'(by omega) = (r.take M)[i]'hi_t := (List.getElem_take).symm
  have h2 : r[j]'(by omega) = (r.take M)[j]'hj_t := (List.getElem_take).symm
  rw [h1, h2]
  clear h1 h2
  generalize hs : r.take M = l at hi_t hj_t
  clear hs r M hM hi hj
  induction l generalizing i j with
  | nil => simp at hi_t
  | cons a t ih =>
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl hij
      | succ j =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ, inv_pair_coe, ← Multiset.cons_coe,
          ← Multiset.singleton_add]
        have hm : t[j]'(by simpa using hj_t) ∈ (t : Multiset ℕ) := List.getElem_mem _
        obtain ⟨s, hs⟩ := Multiset.exists_cons_of_mem hm
        rw [hs, ← Multiset.singleton_add]
        exact multiset_le_iff_exists_add.mpr ⟨s, by ac_rfl⟩
    | succ i =>
      cases j with
      | zero =>
        simp only [List.getElem_cons_succ, List.getElem_cons_zero, inv_pair_coe, ← Multiset.cons_coe,
          ← Multiset.singleton_add]
        have hm : t[i]'(by simpa using hi_t) ∈ (t : Multiset ℕ) := List.getElem_mem _
        obtain ⟨s, hs⟩ := Multiset.exists_cons_of_mem hm
        rw [hs, ← Multiset.singleton_add]
        exact multiset_le_iff_exists_add.mpr ⟨s, by ac_rfl⟩
      | succ j =>
        have ih' := ih (i := i) (j := j) (hij := by omega) (hi_t := by simpa using hi_t) (hj_t := by simpa using hj_t)
        simp only [List.getElem_cons_succ, inv_pair_coe, ← Multiset.cons_coe, ← Multiset.singleton_add] at ih' ⊢
        exact ih'.trans le_add_self

lemma countP_decTop_add_drop {M : ℕ} {r : List ℕ} (hM : M ≤ r.length) {t q : ℕ}
    (htake : ∀ x ∈ r.take M, t + 1 ≤ x) (hq : M ≤ q) (hqr : q < r.length)
    (hrq : t ≤ r[q]'hqr) :
    M + 1 ≤ ((decTop M r).filter (fun w => t ≤ w)).card := by
  simp only [decTop, Multiset.filter_add, Multiset.card_add]
  have h1 : M ≤ ((Multiset.map (· - 1) (r.take M : Multiset ℕ)).filter (fun w => t ≤ w)).card := by
    have hmap : Multiset.map (· - 1) (r.take M : Multiset ℕ) =
        (((r.take M).map (· - 1) : List ℕ) : Multiset ℕ) := (Multiset.map_coe _ _).symm
    rw [hmap, filter_card_coe, List.countP_map]
    have hall : ∀ w ∈ r.take M, ((fun x => decide (t ≤ x)) ∘ (· - 1)) w = true := by
      intro w hw; simp; have := htake w hw; omega
    rw [List.countP_eq_length.mpr hall, List.length_take, Nat.min_eq_left hM]
  have h2 : 1 ≤ ((r.drop M : Multiset ℕ).filter (fun w => t ≤ w)).card := by
    rw [filter_card_coe]
    refine List.countP_pos_iff.mpr ⟨r[q]'hqr, ?_, by simp [hrq]⟩
    have hq_d : q - M < (r.drop M).length := by rw [List.length_drop]; omega
    have heq : (r.drop M)[q - M]'hq_d = r[q]'hqr := by rw [List.getElem_drop]; congr 1; omega
    rw [← heq]
    exact List.getElem_mem hq_d
  omega

lemma inv_of_transfer_head {a b : List ℕ} (ha : IsGraphical a) (hb : IsGraphical b)
    {x y : ℕ} (hxy : x ≥ y + 2) (hx : x ∈ a) (hy : y ∈ a)
    (hperm : (b : Multiset ℕ) + {x, y} = (a : Multiset ℕ) + {x - 1, y + 1})
    (hhead : ∀ ha_ne : a ≠ [], ∀ hb_ne : b ≠ [], b.head hb_ne < a.head ha_ne) :
    Inv (hh a) (hh b) := by
  have ha_ne : a ≠ [] := List.ne_nil_of_mem hx
  have hb_ne : b ≠ [] := by
    intro hb0
    have := congrArg Multiset.card hperm
    rw [hb0] at this; simp at this; subst this; simp at ha_ne
  obtain ⟨x0, r, rfl⟩ := List.exists_cons_of_ne_nil ha_ne
  obtain ⟨y0, rb, rfl⟩ := List.exists_cons_of_ne_nil hb_ne
  have hx0_eq : x0 = x := by
    have hlt := hhead (by simp) (by simp)
    simp only [List.head_cons] at hlt
    have hx_le := sortedDesc_head_ge_of_mem ha.1 hx
    by_contra hne
    have hxm : x0 ∈ ((x0 :: r : List ℕ) : Multiset ℕ) + {x - 1, y + 1} := by simp
    rw [← hperm] at hxm
    rcases Multiset.mem_add.mp hxm with h1 | h2
    · have := sortedDesc_head_ge_of_mem hb.1 h1; omega
    · simp only [inv_pair_coe, Multiset.mem_add, Multiset.mem_singleton] at h2
      rcases h2 with rfl | rfl <;> omega
  subst x0
  have hy0_eq : y0 = x - 1 := by
    have hlt := hhead (by simp) (by simp)
    simp only [List.head_cons] at hlt
    have hmem : x - 1 ∈ ((y0 :: rb : List ℕ) : Multiset ℕ) := by
      have h1 : x - 1 ∈ ((x :: r : List ℕ) : Multiset ℕ) + {x - 1, y + 1} := by simp
      rw [← hperm] at h1
      rcases Multiset.mem_add.mp h1 with h1 | h1
      · exact h1
      · simp at h1; omega
    have hle := sortedDesc_head_ge_of_mem hb.1 hmem
    omega
  subst y0
  have hrb_perm : (rb : Multiset ℕ) + {y} = (r : Multiset ℕ) + {y + 1} := by
    have h1 := hperm
    simp only [← Multiset.cons_coe, ← Multiset.singleton_add, inv_pair_coe] at h1
    have hx_eq : ({x - 1} : Multiset ℕ) + (rb : Multiset ℕ) + ({x} + {y}) =
        (({x - 1} : Multiset ℕ) + {x}) + ((rb : Multiset ℕ) + {y}) := by ac_rfl
    have hx_eq2 : ({x} : Multiset ℕ) + (r : Multiset ℕ) + ({x - 1} + {y + 1}) =
        (({x - 1} : Multiset ℕ) + {x}) + ((r : Multiset ℕ) + {y + 1}) := by ac_rfl
    rw [hx_eq, hx_eq2] at h1
    exact add_left_cancel h1
  have hy_r : y ∈ r := by
    have h1 : y ∈ (x :: r) := hy
    simp only [List.mem_cons] at h1
    rcases h1 with rfl | hr
    · omega
    · exact hr
  have hr_sort : SortedDesc r := sortedDesc_tail ha.1
  have hrb_sort : SortedDesc rb := sortedDesc_tail hb.1
  obtain ⟨hq, hrq, hb_sort, hb_perm⟩ := bump1_spec hr_sort hy_r
  have hrb_eq : rb = bump1 r y := sortedDesc_ext_of_perm hrb_sort hb_sort (by
    have h1 : (rb : Multiset ℕ) + {y} = (bump1 r y : Multiset ℕ) + {y} := hrb_perm.trans hb_perm.symm
    exact add_right_cancel h1)
  subst hrb_eq
  have hpos_a := isGraphical_take_pos ha
  have hpos_b := isGraphical_take_pos hb
  have hgr_a : IsGraphical (hh (x :: r)) := by
    cases hx' : x with
    | zero => omega
    | succ x' =>
      have ha' : IsGraphical ((x' + 1) :: r) := by rwa [← hx']
      exact (isGraphical_hh ha').1
  have hgr_b : IsGraphical (hh ((x - 1) :: bump1 r y)) := by
    cases hx1 : x - 1 with
    | zero => omega
    | succ d' =>
      have hb' : IsGraphical ((d' + 1) :: bump1 r y) := by rwa [← hx1]
      exact (isGraphical_hh hb').1
  have hr_len : x ≤ r.length := hpos_a.1
  have hx_dec : decTop (x - 1) r + {r[x - 1]'(by omega) - 1} = decTop x r + {r[x - 1]'(by omega)} := by
    have h := decTop_succ (M := x - 1) (r := r) (by omega)
    have hsub : x - 1 + 1 = x := by omega
    rw [hsub] at h; exact h
  set q := r.countP (fun w => decide (y + 1 ≤ w))
  have ha_hh : (hh (x :: r) : Multiset ℕ) = decTop x r := hh_coe_eq_decTop x r
  have hb_hh : (hh ((x - 1) :: bump1 r y) : Multiset ℕ) = decTop (x - 1) (bump1 r y) :=
    hh_coe_eq_decTop (x - 1) (bump1 r y)
  refine ⟨hgr_a, hgr_b, ?_⟩
  have hzr_pos : 1 ≤ r[x - 1]'(by omega) := by
    apply hpos_a.2
    have hi : x - 1 < (r.take x).length := by rw [List.length_take, Nat.min_eq_left hr_len]; omega
    have htake_el : (r.take x)[x - 1]'hi = r[x - 1]'(by omega) := List.getElem_take
    rw [← htake_el]
    exact List.getElem_mem hi
  set z := r[x - 1]'(by omega)
  by_cases hqm : q < x - 1
  · left
    have h1y : 1 ≤ y := by
      apply hpos_a.2
      rw [← hrq]
      have hi : q < (r.take x).length := by rw [List.length_take, Nat.min_eq_left hr_len]; omega
      have htake_el : (r.take x)[q]'hi = r[q]'hq := List.getElem_take
      rw [← htake_el]
      exact List.getElem_mem hi
    have hzy : z ≤ y := by
      rw [← hrq]
      exact sortedDesc_ge_of_le hr_sort (by omega : q ≤ x - 1) (by omega)
    have hdec := decTop_bump1_lt hr_sort hy_r h1y hqm
    have hmult : (hh ((x - 1) :: bump1 r y) : Multiset ℕ) + {y - 1, z - 1} =
        (hh (x :: r) : Multiset ℕ) + {y, z} := by
      rw [hb_hh, ha_hh, inv_pair_coe, inv_pair_coe]
      have hsum : decTop (x - 1) (bump1 r y) + ({y - 1} + {z - 1}) + {z} =
          decTop x r + ({y} + {z}) + {z} := by
        calc decTop (x - 1) (bump1 r y) + ({y - 1} + {z - 1}) + {z}
            = (decTop (x - 1) (bump1 r y) + {y - 1}) + {z - 1} + {z} := by ac_rfl
          _ = (decTop (x - 1) r + {y}) + {z - 1} + {z} := by rw [hdec]
          _ = (decTop (x - 1) r + {z - 1}) + {y} + {z} := by ac_rfl
          _ = (decTop x r + {z}) + {y} + {z} := by rw [hx_dec]
          _ = decTop x r + ({y} + {z}) + {z} := by ac_rfl
      exact add_right_cancel hsum
    have hle_pair : ({y - 1, z - 1} : Multiset ℕ) ≤ (hh (x :: r) : Multiset ℕ) := by
      rw [ha_hh]
      have hpair := pair_le_of_distinct_take (r := r) (i := q) (j := x - 1) (M := x)
        (by omega) (by omega) hr_len (by omega)
      have hmap := Multiset.map_le_map (f := (· - 1)) hpair
      simp only [Multiset.map_coe, inv_pair_coe, Multiset.map_add, Multiset.map_singleton] at hmap
      have hq_val : r[q]'(by omega) = y := hrq
      rw [hq_val] at hmap
      rw [← Multiset.map_coe] at hmap
      rw [inv_pair_coe, decTop]
      exact hmap.trans le_self_add
    have hcnt_z : y + 1 ≤ (hh (x :: r)).countP (fun w => decide (z - 1 ≤ w)) := by
      rw [← filter_card_coe, ha_hh]
      have h1 := countP_succ_le_decTop x r (z - 1)
      have hsub : z - 1 + 1 = z := by omega
      rw [hsub] at h1
      have hr_cnt : x ≤ r.countP (fun w => decide (z ≤ w)) := by
        by_contra hlt
        have hlt1 : r.countP (fun w => decide (z ≤ w)) ≤ x - 1 := by omega
        have hge := (sortedDesc_lt_countP_iff hr_sort z (by omega : x - 1 < r.length)).mpr le_rfl
        omega
      omega
    exact ⟨y, z, hzr_pos, hzy, hle_pair, hmult, hcnt_z⟩
  · by_cases hqeq : q = x - 1
    · right
      have hzy : z = y := by
        dsimp only [z]
        have : r[x - 1]'(by omega) = r[q]'hq := by congr 1; exact hqeq.symm
        rw [this, hrq]
      have h1y : 1 ≤ y := by omega
      have hdec := decTop_bump1_ge hr_sort hy_r (by omega : x - 1 ≤ q)
      have hmult : (hh ((x - 1) :: bump1 r y) : Multiset ℕ) + {y + 1 - 2} =
          (hh (x :: r) : Multiset ℕ) + {y + 1} := by
        rw [hb_hh, ha_hh]
        have hsub : y + 1 - 2 = y - 1 := by omega
        rw [hsub]
        have hsum : decTop (x - 1) (bump1 r y) + {y - 1} + {y} =
            decTop x r + {y + 1} + {y} := by
          dsimp only [z] at hzy
          calc decTop (x - 1) (bump1 r y) + {y - 1} + {y}
              = (decTop (x - 1) (bump1 r y) + {y}) + {y - 1} := by ac_rfl
            _ = (decTop (x - 1) r + {y + 1}) + {y - 1} := by rw [hdec]
            _ = (decTop (x - 1) r + {y - 1}) + {y + 1} := by ac_rfl
            _ = (decTop (x - 1) r + {r[x - 1]'(by omega) - 1}) + {y + 1} := by rw [hzy]
            _ = (decTop x r + {r[x - 1]'(by omega)}) + {y + 1} := by rw [hx_dec]
            _ = decTop x r + {y + 1} + {y} := by rw [hzy]; ac_rfl
        exact add_right_cancel hsum
      have hmem_v : (y - 1) ∈ hh (x :: r) := by
        have hmem_m : y - 1 ∈ (hh (x :: r) : Multiset ℕ) := by
          rw [ha_hh, decTop, Multiset.mem_add]
          left; rw [Multiset.mem_map]
          refine ⟨y, ?_, rfl⟩
          have hi : x - 1 < (r.take x).length := by rw [List.length_take, Nat.min_eq_left hr_len]; omega
          have heq : (r.take x)[x - 1]'hi = y := by rw [List.getElem_take]; exact hzy
          rw [← heq]; exact List.getElem_mem hi
        exact hmem_m
      have hhead_le : y + 1 ≤ (hh (x :: r)).headI + 1 := by
        have hr0_lt : 0 < r.length := by omega
        have hr0_ge : y + 1 ≤ r[0]'hr0_lt := by
          exact (sortedDesc_lt_countP_iff hr_sort (y + 1) hr0_lt).mp (by omega)
        have hmem_m : r[0]'hr0_lt - 1 ∈ decTop x r := by
          simp only [decTop, Multiset.mem_add, Multiset.mem_map, Multiset.mem_coe]
          left
          refine ⟨r[0]'hr0_lt, ?_, rfl⟩
          have h0_t : 0 < (r.take x).length := by rw [List.length_take, Nat.min_eq_left hr_len]; omega
          have heq : (r.take x)[0]'h0_t = r[0]'hr0_lt := List.getElem_take
          rw [← heq]
          exact List.getElem_mem h0_t
        rw [← ha_hh] at hmem_m
        have hle := headI_ge_of_mem hgr_a.1 hmem_m
        omega
      have hcnt1 : y + 1 + 1 ≤ (hh (x :: r)).countP (fun w => decide (y + 1 - 2 ≤ w)) := by
        have hsub1 : y + 1 - 2 = y - 1 := by omega
        rw [hsub1, ← filter_card_coe, ha_hh]
        have h1 := countP_succ_le_decTop x r (y - 1)
        have hsub2 : y - 1 + 1 = y := by omega
        rw [hsub2] at h1
        have hr_cnt : x ≤ r.countP (fun w => decide (y ≤ w)) := by
          by_contra hlt
          have := (sortedDesc_lt_countP_iff hr_sort y (by omega : x - 1 < r.length)).mpr (by omega)
          omega
        omega
      have hcnt2 : y + 1 ≤ (hh (x :: r)).countP (fun w => decide (y + 1 - 1 ≤ w)) := by
        have hsub1 : y + 1 - 1 = y := by omega
        rw [hsub1, ← filter_card_coe, ha_hh]
        have h1 := countP_succ_le_decTop x r y
        omega
      have hmem_v' : y + 1 - 2 ∈ hh (x :: r) := by
        have hsub : y + 1 - 2 = y - 1 := by omega
        rw [hsub]; exact hmem_v
      exact ⟨y + 1, by omega, hhead_le, hmem_v', hmult, hcnt1, Or.inr hcnt2⟩
    · left
      have hqgt : x ≤ q := by omega
      have hyz : y + 1 ≤ z :=
        (sortedDesc_lt_countP_iff hr_sort (y + 1) (by omega : x - 1 < r.length)).mp (by omega)
      have hdec := decTop_bump1_ge hr_sort hy_r (by omega : x - 1 ≤ q)
      have hmult : (hh ((x - 1) :: bump1 r y) : Multiset ℕ) + {z - 1, y + 1 - 1} =
          (hh (x :: r) : Multiset ℕ) + {z, y + 1} := by
        rw [hb_hh, ha_hh, inv_pair_coe, inv_pair_coe, Nat.add_sub_cancel]
        have hsum : decTop (x - 1) (bump1 r y) + ({z - 1} + {y}) + {z} =
            decTop x r + ({z} + {y + 1}) + {z} := by
          calc decTop (x - 1) (bump1 r y) + ({z - 1} + {y}) + {z}
              = (decTop (x - 1) (bump1 r y) + {y}) + {z - 1} + {z} := by ac_rfl
            _ = (decTop (x - 1) r + {y + 1}) + {z - 1} + {z} := by rw [hdec]
            _ = (decTop (x - 1) r + {z - 1}) + {y + 1} + {z} := by ac_rfl
            _ = (decTop x r + {z}) + {y + 1} + {z} := by rw [hx_dec]
            _ = decTop x r + ({z} + {y + 1}) + {z} := by ac_rfl
        exact add_right_cancel hsum
      have hle_pair : ({z - 1, y + 1 - 1} : Multiset ℕ) ≤ (hh (x :: r) : Multiset ℕ) := by
        rw [ha_hh, decTop, inv_pair_coe, Nat.add_sub_cancel]
        have hz_in : z - 1 ∈ Multiset.map (· - 1) (r.take x : Multiset ℕ) := by
          rw [Multiset.mem_map]
          refine ⟨z, ?_, rfl⟩
          have hi : x - 1 < (r.take x).length := by rw [List.length_take, Nat.min_eq_left hr_len]; omega
          have heq : (r.take x)[x - 1]'hi = z := List.getElem_take
          rw [← heq]; exact List.getElem_mem hi
        have hy_in : y ∈ (r.drop x : Multiset ℕ) := by
          have hi : q - x < (r.drop x).length := by rw [List.length_drop]; omega
          have heq : (r.drop x)[q - x]'hi = y := by
            rw [List.getElem_drop]; convert hrq; omega
          rw [← heq]; exact List.getElem_mem hi
        obtain ⟨s1, hs1⟩ := Multiset.exists_cons_of_mem hz_in
        obtain ⟨s2, hs2⟩ := Multiset.exists_cons_of_mem hy_in
        rw [hs1, hs2, ← Multiset.singleton_add, ← Multiset.singleton_add]
        exact multiset_le_iff_exists_add.mpr ⟨s1 + s2, by ac_rfl⟩
      have hcnt_y : z + 1 ≤ (hh (x :: r)).countP (fun w => decide (y + 1 - 1 ≤ w)) := by
        rw [Nat.add_sub_cancel, ← filter_card_coe, ha_hh]
        have htake_all : ∀ w ∈ r.take x, y + 1 ≤ w := by
          intro w hw
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hw
          have hi_x : i < x := by rw [List.length_take] at hi; exact Nat.lt_of_lt_of_le hi (Nat.min_le_left _ _)
          rw [List.getElem_take]
          exact (sortedDesc_lt_countP_iff hr_sort (y + 1) (by omega)).mp (by omega)
        have h1 := countP_decTop_add_drop (M := x) (r := r) hr_len htake_all hqgt hq (by rw [hrq])
        have hzx : z ≤ x := sortedDesc_head_ge_of_mem ha.1 (by simp [z])
        omega
      exact ⟨z, y + 1, by omega, hyz, hle_pair, hmult, hcnt_y⟩

lemma inv_length_eq {v u : List ℕ} (hInv : Inv v u) : v.length = u.length := by
  rcases hInv with ⟨_, _, hP⟩
  rcases hP with ⟨x, y, _, _, _, heq, _⟩ | ⟨z, _, _, _, heq, _, _⟩
  · have hc := congrArg Multiset.card heq; simpa using hc.symm
  · have hc := congrArg Multiset.card heq; simpa using hc.symm

lemma inv_head_le {v u : List ℕ} (hInv : Inv v u) (hv_ne : v ≠ []) (hu_ne : u ≠ []) :
    v.head hv_ne ≤ u.head hu_ne := by
  rcases hInv with ⟨hgv, hgu, hP⟩
  obtain ⟨M, r_v, rfl⟩ := List.exists_cons_of_ne_nil hv_ne
  obtain ⟨Mu, r_u, rfl⟩ := List.exists_cons_of_ne_nil hu_ne
  simp only [List.head_cons]
  rcases hP with ⟨x, y, h1y, hyx, _, heq, _⟩ | ⟨z, h2z, _, _, heq, _, _⟩
  · have h1 : M ∈ ((M :: r_v : List ℕ) : Multiset ℕ) + {x, y} := by simp
    rw [← heq] at h1
    rcases Multiset.mem_add.mp h1 with h | h
    · exact sortedDesc_head_ge_of_mem hgu.1 h
    · simp only [inv_pair_coe, Multiset.mem_add, Multiset.mem_singleton] at h
      have hxu : x ∈ (Mu :: r_u) := by
        have h2 : x ∈ ((M :: r_v : List ℕ) : Multiset ℕ) + {x, y} := by simp
        rw [← heq] at h2
        rcases Multiset.mem_add.mp h2 with h2 | h2
        · exact h2
        · simp only [inv_pair_coe, Multiset.mem_add, Multiset.mem_singleton] at h2
          rcases h2 with h2 | h2 <;> omega
      have := sortedDesc_head_ge_of_mem hgu.1 hxu
      rcases h with rfl | rfl <;> omega
  · have h1 : M ∈ ((M :: r_v : List ℕ) : Multiset ℕ) + {z} := by simp
    rw [← heq] at h1
    rcases Multiset.mem_add.mp h1 with h | h
    · exact sortedDesc_head_ge_of_mem hgu.1 h
    · simp only [Multiset.mem_singleton] at h
      have hzu : z ∈ (Mu :: r_u) := by
        have h2 : z ∈ ((M :: r_v : List ℕ) : Multiset ℕ) + {z} := by simp
        rw [← heq] at h2
        rcases Multiset.mem_add.mp h2 with h2 | h2
        · exact h2
        · simp only [Multiset.mem_singleton] at h2; omega
      have := sortedDesc_head_ge_of_mem hgu.1 hzu
      omega

lemma isGraphical_cons_succ_head {M : ℕ} {r : List ℕ} (hg : IsGraphical (M :: r)) (hpos : 1 ≤ M) :
    IsGraphical (hh (M :: r)) := by
  obtain ⟨M', hM'⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : M ≠ 0)
  rw [hM'] at hg ⊢
  exact (isGraphical_hh hg).1

lemma inv_step_head_eq {v u : List ℕ} (hInv : Inv v u)
    (hv_ne : v ≠ []) (hu_ne : u ≠ [])
    (h0 : v.head hv_ne = u.head hu_ne) (hpos : 1 ≤ v.head hv_ne) :
    Maj (hh v) (hh u) ∨ Inv (hh v) (hh u) := by
  right
  rcases hInv with ⟨hgv, hgu, hP⟩
  obtain ⟨M, r_v, rfl⟩ := List.exists_cons_of_ne_nil hv_ne
  obtain ⟨Mu, r_u, rfl⟩ := List.exists_cons_of_ne_nil hu_ne
  simp only [List.head_cons] at h0 hpos
  subst h0
  have hr_v_sort : SortedDesc r_v := sortedDesc_tail hgv.1
  have hr_u_sort : SortedDesc r_u := sortedDesc_tail hgu.1
  have hgv_hh : IsGraphical (hh (M :: r_v)) := isGraphical_cons_succ_head hgv hpos
  have hgu_hh : IsGraphical (hh (M :: r_u)) := isGraphical_cons_succ_head hgu hpos
  have hpos_v := isGraphical_take_pos hgv
  have hpos_u := isGraphical_take_pos hgu
  have hM_len : M ≤ r_v.length := hpos_v.1
  have hv_hh : (hh (M :: r_v) : Multiset ℕ) = decTop M r_v := hh_coe_eq_decTop M r_v
  have hu_hh : (hh (M :: r_u) : Multiset ℕ) = decTop M r_u := hh_coe_eq_decTop M r_u
  refine ⟨hgv_hh, hgu_hh, ?_⟩
  rcases hP with ⟨x, y, h1y, hyx, hpair_le, heq, hcnt⟩ | ⟨z, h2z, hzM, hzm_mem, heq, hcnt1, hcnt2⟩
  · have hx_u : x ∈ M :: r_u := by
      have h1 : x ∈ ((M :: r_v : List ℕ) : Multiset ℕ) + {x, y} := by simp
      rw [← heq] at h1
      rcases Multiset.mem_add.mp h1 with h1 | h1
      · exact h1
      · simp at h1; rcases h1 with h1 | h1 <;> omega
    have hxM : x ≤ M := sortedDesc_head_ge_of_mem hgu.1 hx_u
    have hpair_tail : ({x - 1, y - 1} : Multiset ℕ) ≤ (r_v : Multiset ℕ) :=
      sortedDesc_pair_le_tail hpair_le (by omega) (by omega)
    have hru_eq : (r_u : Multiset ℕ) + {x - 1, y - 1} = (r_v : Multiset ℕ) + {x, y} := by
      have h1 := heq
      simp only [← Multiset.cons_coe, ← Multiset.singleton_add] at h1
      have h2 : ({M} : Multiset ℕ) + ((r_u : Multiset ℕ) + {x - 1, y - 1}) =
          ({M} : Multiset ℕ) + ((r_v : Multiset ℕ) + {x, y}) := by
        calc ({M} : Multiset ℕ) + ((r_u : Multiset ℕ) + {x - 1, y - 1})
            = {M} + (r_u : Multiset ℕ) + {x - 1, y - 1} := by ac_rfl
          _ = {M} + (r_v : Multiset ℕ) + {x, y} := h1
          _ = {M} + ((r_v : Multiset ℕ) + {x, y}) := by ac_rfl
      exact add_left_cancel h2
    have ⟨hx1_v, hy1_v⟩ := mem_of_pair_le hpair_tail
    have hx1_rv : x - 1 ∈ r_v := hx1_v
    obtain ⟨hq1, hrq1, hr1_sort, hr1_perm⟩ := bump1_spec hr_v_sort hx1_rv
    set r1 := bump1 r_v (x - 1)
    set q1 := r_v.countP (fun w => decide (x - 1 + 1 ≤ w))
    have hq1_eq : q1 = r_v.countP (fun w => decide (x ≤ w)) :=
      congrArg (fun p => r_v.countP p) (funext (fun w => by simp [Nat.sub_add_cancel (by omega : 1 ≤ x)]))
    have hy1_r1 : y - 1 ∈ r1 := by
      rw [inv_pair_coe] at hpair_tail
      obtain ⟨s, hs⟩ := multiset_le_iff_exists_add.mp hpair_tail
      have hp1 : x - 1 + 1 = x := Nat.sub_add_cancel (by omega)
      have hr1_perm' : (r1 : Multiset ℕ) + {x - 1} = (r_v : Multiset ℕ) + {x} := by
        dsimp only [r1]; rw [hr1_perm, hp1]
      have hm1 : (r1 : Multiset ℕ) + {x - 1} = ({x - 1} + {y - 1} + s) + {x} := by
        rw [hr1_perm', hs]
      have hm2 : (r1 : Multiset ℕ) + {x - 1} = ({y - 1} + s + {x}) + {x - 1} := by
        rw [hm1]; ac_rfl
      have hm3 := add_right_cancel hm2
      have hmem : y - 1 ∈ (r1 : Multiset ℕ) := by rw [hm3]; simp
      exact hmem
    obtain ⟨hq2, hrq2, hr2_sort, hr2_perm⟩ := bump1_spec hr1_sort hy1_r1
    set q2 := r1.countP (fun w => decide (y - 1 + 1 ≤ w))
    have hq2_eq : q2 = r1.countP (fun w => decide (y ≤ w)) :=
      congrArg (fun p => r1.countP p) (funext (fun w => by simp [Nat.sub_add_cancel h1y]))
    have hru_bump : r_u = bump1 r1 (y - 1) := by
      apply sortedDesc_ext_of_perm hr_u_sort hr2_sort
      have hp1 : (x - 1 + 1) = x := Nat.sub_add_cancel (by omega)
      have hp2 : (y - 1 + 1) = y := Nat.sub_add_cancel h1y
      have hr1_perm' : (r1 : Multiset ℕ) + {x - 1} = (r_v : Multiset ℕ) + {x} := by
        dsimp only [r1]; rw [hr1_perm, hp1]
      have hr2_perm' : (bump1 r1 (y - 1) : Multiset ℕ) + {y - 1} = (r1 : Multiset ℕ) + {y} := by
        rw [hr2_perm, hp2]
      have hsum1 : (r_u : Multiset ℕ) + ({x - 1} + {y - 1}) =
          (bump1 r1 (y - 1) : Multiset ℕ) + ({x - 1} + {y - 1}) := by
        calc (r_u : Multiset ℕ) + ({x - 1} + {y - 1})
            = (r_u : Multiset ℕ) + {x - 1, y - 1} := by rw [← inv_pair_coe]
          _ = (r_v : Multiset ℕ) + {x, y} := hru_eq
          _ = ((r_v : Multiset ℕ) + {x}) + {y} := by rw [inv_pair_coe]; ac_rfl
          _ = ((r1 : Multiset ℕ) + {x - 1}) + {y} := by rw [← hr1_perm']
          _ = ((r1 : Multiset ℕ) + {y}) + {x - 1} := by ac_rfl
          _ = ((bump1 r1 (y - 1) : Multiset ℕ) + {y - 1}) + {x - 1} := by rw [← hr2_perm']
          _ = (bump1 r1 (y - 1) : Multiset ℕ) + ({x - 1} + {y - 1}) := by ac_rfl
      exact add_right_cancel hsum1
    rw [hru_bump] at hgu_hh ⊢
    by_cases hq1M : M ≤ q1
    · left
      have hq2M : M ≤ q2 := by
        rw [hq2_eq]
        by_contra hlt
        have hr1_lt : r1[q2]'hq2 = y - 1 := hrq2
        have htake_eq : r1.take M = r_v.take M := by
          dsimp only [r1, bump1, q1]
          exact take_set_of_le r_v q1 M (x - 1 + 1) hq1M
        have hq2_t : q2 < r_v.length := by rw [← bump1_length (r := r_v) (y := x - 1)]; exact hq2
        have hmem_t : y - 1 ∈ r1.take M := by
          have hi : q2 < (r1.take M).length := by rw [List.length_take, Nat.lt_min]; exact ⟨by omega, hq2⟩
          have heq' : (r1.take M)[q2]'hi = y - 1 := by rw [List.getElem_take]; exact hrq2
          rw [← heq']; exact List.getElem_mem hi
        rw [htake_eq] at hmem_t
        obtain ⟨i, hi, hri⟩ := List.mem_iff_getElem.mp hmem_t
        have hiM : i < M := by rw [List.length_take] at hi; exact Nat.lt_of_lt_of_le hi (Nat.min_le_left _ _)
        rw [List.getElem_take] at hri
        have hge := (sortedDesc_lt_countP_iff hr_v_sort x (by omega : i < r_v.length)).mp (by rw [← hq1_eq]; omega)
        omega
      have hdec1 := decTop_bump1_ge hr_v_sort hx1_rv hq1M
      have hdec2 := decTop_bump1_ge hr1_sort hy1_r1 hq2M
      have hp1 : x - 1 + 1 = x := Nat.sub_add_cancel (by omega)
      have hp2 : y - 1 + 1 = y := Nat.sub_add_cancel h1y
      have hdec1' : decTop M r1 + {x - 1} = decTop M r_v + {x} := by
        dsimp only [r1]; rw [hdec1, hp1]
      have hdec2' : decTop M (bump1 r1 (y - 1)) + {y - 1} = decTop M r1 + {y} := by
        rw [hdec2, hp2]
      have hmult : (hh (M :: bump1 r1 (y - 1)) : Multiset ℕ) + {x - 1, y - 1} =
          (hh (M :: r_v) : Multiset ℕ) + {x, y} := by
        rw [hh_coe_eq_decTop, hv_hh, inv_pair_coe, inv_pair_coe]
        calc decTop M (bump1 r1 (y - 1)) + ({x - 1} + {y - 1})
            = (decTop M (bump1 r1 (y - 1)) + {y - 1}) + {x - 1} := by ac_rfl
          _ = (decTop M r1 + {y}) + {x - 1} := by rw [hdec2']
          _ = (decTop M r1 + {x - 1}) + {y} := by ac_rfl
          _ = (decTop M r_v + {x}) + {y} := by rw [hdec1']
          _ = decTop M r_v + ({x} + {y}) := by ac_rfl
      have hle_pair : ({x - 1, y - 1} : Multiset ℕ) ≤ (hh (M :: r_v) : Multiset ℕ) := by
        rw [hv_hh, decTop]
        have hdisj : ∀ a ∈ ({x - 1, y - 1} : Multiset ℕ), a ∉ (r_v.take M : Multiset ℕ) := by
          intro a ha hm
          rw [inv_pair_coe] at ha
          simp only [Multiset.mem_add, Multiset.mem_singleton] at ha
          rw [Multiset.mem_coe] at hm
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hm
          have hiM : i < M := by rw [List.length_take] at hi; exact Nat.lt_of_lt_of_le hi (Nat.min_le_left _ _)
          rw [List.getElem_take] at ha
          have hwx := (sortedDesc_lt_countP_iff hr_v_sort x (by omega : i < r_v.length)).mp (by rw [← hq1_eq]; omega)
          rcases ha with h1 | h1 <;> omega
        have hspl : (r_v : Multiset ℕ) = (r_v.take M : Multiset ℕ) + (r_v.drop M : Multiset ℕ) := by
          conv_lhs => rw [← List.take_append_drop M r_v]
          exact Multiset.coe_add _ _
        rw [hspl] at hpair_tail
        have hdrop_le : ({x - 1, y - 1} : Multiset ℕ) ≤ (r_v.drop M : Multiset ℕ) := by
          rw [Multiset.le_iff_count]
          intro a
          by_cases ha : a ∈ ({x - 1, y - 1} : Multiset ℕ)
          · have h1 := Multiset.le_iff_count.mp hpair_tail a
            have h0 : (r_v.take M : Multiset ℕ).count a = 0 := Multiset.count_eq_zero.mpr (hdisj a ha)
            rw [Multiset.count_add, h0, zero_add] at h1
            exact h1
          · rw [Multiset.count_eq_zero.mpr ha]; exact Nat.zero_le _
        exact hdrop_le.trans le_add_self
      have hcnt_new : x + 1 ≤ (hh (M :: r_v)).countP (fun w => decide (y - 1 ≤ w)) := by
        rw [← filter_card_coe, hv_hh]
        have htake_all : ∀ w ∈ r_v.take M, y - 1 + 1 ≤ w := by
          intro w hw
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hw
          have hiM : i < M := by rw [List.length_take] at hi; exact Nat.lt_of_lt_of_le hi (Nat.min_le_left _ _)
          rw [List.getElem_take]
          have hwx := (sortedDesc_lt_countP_iff hr_v_sort x (by omega : i < r_v.length)).mp (by rw [← hq1_eq]; omega)
          omega
        have h1 := countP_decTop_add_drop (M := M) (r := r_v) hM_len htake_all hq1M hq1 (by rw [hrq1]; omega)
        omega
      exact ⟨x, y, h1y, hyx, hle_pair, hmult, hcnt_new⟩
    · have hq1_lt : q1 < M := by omega
      have h1x1 : 1 ≤ x - 1 := by
        apply hpos_v.2
        rw [← hrq1]
        have hi : q1 < (r_v.take M).length := by rw [List.length_take, Nat.min_eq_left hM_len]; exact hq1_lt
        have htake_el : (r_v.take M)[q1]'hi = r_v[q1]'hq1 := List.getElem_take
        rw [← htake_el]
        exact List.getElem_mem hi
      have hlen_r1 : r1.length = r_v.length := bump1_length
      by_cases hq2M : M ≤ q2
      · have hdec1 := decTop_bump1_lt hr_v_sort hx1_rv h1x1 hq1_lt
        have hdec2 := decTop_bump1_ge hr1_sort hy1_r1 hq2M
        have hp1 : x - 1 + 1 = x := Nat.sub_add_cancel (by omega)
        have hp2 : y - 1 + 1 = y := Nat.sub_add_cancel h1y
        have hdec1' : decTop M r1 + {x - 2} = decTop M r_v + {x - 1} := by
          dsimp only [r1]; rw [show x - 2 = x - 1 - 1 by omega]; exact hdec1
        have hdec2' : decTop M (bump1 r1 (y - 1)) + {y - 1} = decTop M r1 + {y} := by
          rw [hdec2, hp2]
        have hmult_raw : decTop M (bump1 r1 (y - 1)) + {x - 2, y - 1} =
            decTop M r_v + {x - 1, y} := by
          rw [inv_pair_coe, inv_pair_coe]
          calc decTop M (bump1 r1 (y - 1)) + ({x - 2} + {y - 1})
              = (decTop M (bump1 r1 (y - 1)) + {y - 1}) + {x - 2} := by ac_rfl
            _ = (decTop M r1 + {y}) + {x - 2} := by rw [hdec2']
            _ = (decTop M r1 + {x - 2}) + {y} := by ac_rfl
            _ = (decTop M r_v + {x - 1}) + {y} := by rw [hdec1']
            _ = decTop M r_v + ({x - 1} + {y}) := by ac_rfl
        have hy_drop : y - 1 ∈ (r_v.drop M : Multiset ℕ) := by
          have h1 : y - 1 ∈ (r1.drop M : Multiset ℕ) := by
            have hi : q2 - M < (r1.drop M).length := by rw [List.length_drop]; omega
            have heq' : (r1.drop M)[q2 - M]'hi = y - 1 := by rw [List.getElem_drop]; convert hrq2; omega
            rw [← heq']; exact List.getElem_mem hi
          have heq_drop : r1.drop M = r_v.drop M := drop_set_of_lt r_v q1 M (x - 1 + 1) hq1_lt
          rwa [heq_drop] at h1
        have hx_take : x - 2 ∈ Multiset.map (· - 1) (r_v.take M : Multiset ℕ) := by
          rw [Multiset.mem_map]
          refine ⟨x - 1, ?_, by omega⟩
          have hi : q1 < (r_v.take M).length := by rw [List.length_take, Nat.min_eq_left hM_len]; exact hq1_lt
          have heq' : (r_v.take M)[q1]'hi = x - 1 := by rw [List.getElem_take]; exact hrq1
          rw [← heq']; exact List.getElem_mem hi
        have hpair_raw : ({x - 2, y - 1} : Multiset ℕ) ≤ decTop M r_v := by
          obtain ⟨s1, hs1⟩ := Multiset.exists_cons_of_mem hx_take
          obtain ⟨s2, hs2⟩ := Multiset.exists_cons_of_mem hy_drop
          rw [decTop, hs1, hs2, inv_pair_coe, ← Multiset.singleton_add, ← Multiset.singleton_add]
          exact multiset_le_iff_exists_add.mpr ⟨s1 + s2, by ac_rfl⟩
        by_cases hxy_eq : x = y
        · right
          subst hxy_eq
          have htake_xm1 : ∀ w ∈ r_v.take M, (x - 2) + 1 ≤ w := by
            intro w hw
            obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hw
            have hiM : i < M := by rw [List.length_take] at hi; exact Nat.lt_of_lt_of_le hi (Nat.min_le_left _ _)
            rw [List.getElem_take]
            by_cases heqi : i = q1
            · have hri_q : r_v[i]'(by omega) = r_v[q1]'hq1 := by congr 1
              rw [hri_q, hrq1]; omega
            · have hr1_i : r1[i]'(by omega) = r_v[i]'(by omega) := by
                simp only [r1, bump1]; rw [List.getElem_set_ne (by omega)]
              have hge := (sortedDesc_lt_countP_iff hr1_sort x (by omega : i < r1.length)).mp (by rw [← hq2_eq]; omega)
              rw [← hr1_i]; omega
          have hcnt_x2 : M + 1 ≤ ((decTop M r_v).filter (fun w => x - 2 ≤ w)).card := by
            have heq_drop : r1.drop M = r_v.drop M := drop_set_of_lt r_v q1 M (x - 1 + 1) hq1_lt
            have hq_dr : q2 - M < (r_v.drop M).length := by rw [← heq_drop, List.length_drop]; omega
            have hr_q2 : r_v[q2]'(by omega) = x - 1 := by
              have h1 : (r1.drop M)[q2 - M]'(by rw [List.length_drop]; omega) = x - 1 := by
                rw [List.getElem_drop]; convert hrq2; omega
              have h2 : (r_v.drop M)[q2 - M]'hq_dr = x - 1 := by convert h1 using 1; congr 1; exact heq_drop.symm
              rw [List.getElem_drop] at h2
              convert h2 using 2; omega
            exact countP_decTop_add_drop (M := M) (r := r_v) (t := x - 2) (q := q2) hM_len htake_xm1 hq2M (by omega)
              (by rw [hr_q2]; omega)
          refine ⟨x, by omega, ?_, ?_, ?_, ?_, Or.inl ?_⟩
          · have hmem_m : x - 1 ∈ decTop M r_v := by
              rw [decTop, Multiset.mem_add]
              exact Or.inr hy_drop
            rw [← hv_hh] at hmem_m
            have := headI_ge_of_mem hgv_hh.1 hmem_m
            omega
          · change x - 2 ∈ (hh (M :: r_v) : Multiset ℕ)
            rw [hv_hh, decTop, Multiset.mem_add]
            exact Or.inl hx_take
          · rw [hh_coe_eq_decTop, hv_hh]
            have hsum1 : decTop M (bump1 r1 (x - 1)) + {x - 2} + {x - 1} =
                decTop M r_v + {x} + {x - 1} := by
              calc decTop M (bump1 r1 (x - 1)) + {x - 2} + {x - 1}
                  = decTop M (bump1 r1 (x - 1)) + ({x - 2} + {x - 1}) := by ac_rfl
                _ = decTop M (bump1 r1 (x - 1)) + {x - 2, x - 1} := by rw [← inv_pair_coe]
                _ = decTop M r_v + {x - 1, x} := hmult_raw
                _ = decTop M r_v + {x} + {x - 1} := by rw [inv_pair_coe]; ac_rfl
            exact add_right_cancel hsum1
          · rw [← filter_card_coe, hv_hh]
            omega
          · change x - 1 ∈ (hh (M :: r_v) : Multiset ℕ)
            rw [hv_hh, decTop, Multiset.mem_add]
            exact Or.inr hy_drop
        · left
          have htake_y : ∀ w ∈ r_v.take M, y ≤ w := by
            intro w hw
            obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hw
            have hiM : i < M := by rw [List.length_take] at hi; exact Nat.lt_of_lt_of_le hi (Nat.min_le_left _ _)
            rw [List.getElem_take]
            by_cases heqi : i = q1
            · have hri_q : r_v[i]'(by omega) = r_v[q1]'hq1 := by congr 1
              rw [hri_q, hrq1]; omega
            · have hr1_i : r1[i]'(by omega) = r_v[i]'(by omega) := by
                simp only [r1, bump1]; rw [List.getElem_set_ne (by omega)]
              have hge := (sortedDesc_lt_countP_iff hr1_sort y (by omega : i < r1.length)).mp (by rw [← hq2_eq]; omega)
              rw [← hr1_i]; exact hge
          have hcnt_y1 : M + 1 ≤ ((decTop M r_v).filter (fun w => y - 1 ≤ w)).card := by
            have htake_y' : ∀ w ∈ r_v.take M, (y - 1) + 1 ≤ w := fun w hw => by rw [hp2]; exact htake_y w hw
            have heq_drop : r1.drop M = r_v.drop M := drop_set_of_lt r_v q1 M (x - 1 + 1) hq1_lt
            have hq_dr : q2 - M < (r_v.drop M).length := by rw [← heq_drop, List.length_drop]; omega
            have hr_q2 : r_v[q2]'(by omega) = y - 1 := by
              have h1 : (r1.drop M)[q2 - M]'(by rw [List.length_drop]; omega) = y - 1 := by
                rw [List.getElem_drop]; convert hrq2; omega
              have h2 : (r_v.drop M)[q2 - M]'hq_dr = y - 1 := by convert h1 using 1; congr 1; exact heq_drop.symm
              rw [List.getElem_drop] at h2
              convert h2 using 2; omega
            exact countP_decTop_add_drop (M := M) (r := r_v) (t := y - 1) (q := q2) hM_len htake_y' hq2M (by omega)
              (by rw [hr_q2])
          by_cases hx1y : x - 1 = y
          · have hxy1 : x = y + 1 := by omega
            subst hxy1
            refine ⟨y, y, h1y, le_rfl, ?_, ?_, ?_⟩
            · rw [show y + 1 - 2 = y - 1 by omega] at hpair_raw; rw [hv_hh]; exact hpair_raw
            · rw [hh_coe_eq_decTop, hv_hh]; rw [show y + 1 - 2 = y - 1 by omega, show y + 1 - 1 = y by omega] at hmult_raw; exact hmult_raw
            · rw [← filter_card_coe, hv_hh]; omega
          · have hyx1 : y ≤ x - 1 := by omega
            have hsub_x : x - 1 - 1 = x - 2 := by omega
            refine ⟨x - 1, y, h1y, hyx1, ?_, ?_, ?_⟩
            · rw [hv_hh, hsub_x]; exact hpair_raw
            · rw [hh_coe_eq_decTop, hv_hh, hsub_x]; exact hmult_raw
            · rw [← filter_card_coe, hv_hh]; omega
      · have hq2_lt : q2 < M := by omega
        have h1y1 : 1 ≤ y - 1 := by
          have hmem : y - 1 ∈ r1.take M := by
            have hi : q2 < (r1.take M).length := by rw [List.length_take, Nat.min_eq_left (by omega : M ≤ r1.length)]; exact hq2_lt
            have heq' : (r1.take M)[q2]'hi = y - 1 := by rw [List.getElem_take]; exact hrq2
            rw [← heq']; exact List.getElem_mem hi
          have htake_eq : r1.take M = (r_v.take M).set q1 x := by
            simp only [r1, bump1]; rw [take_set_of_lt r_v q1 M (x - 1 + 1) hq1_lt, Nat.sub_add_cancel (by omega)]
          rw [htake_eq] at hmem
          obtain ⟨i, hi, hri⟩ := List.mem_iff_getElem.mp hmem
          by_cases hiq : i = q1
          · have hset_q : ((r_v.take M).set q1 x)[q1]'(by omega) = x := List.getElem_set_self _
            have hri' : ((r_v.take M).set q1 x)[i]'hi = ((r_v.take M).set q1 x)[q1]'(by omega) := by congr 1
            rw [hri', hset_q] at hri; omega
          · rw [List.getElem_set_ne (Ne.symm hiq)] at hri
            rw [← hri]; exact hpos_v.2 _ (List.getElem_mem (by simpa using hi))
        have hq1_lt_q2 : q1 < q2 := by
          by_contra hle
          have hq2_le : q2 ≤ q1 := by omega
          by_cases heq12 : q2 = q1
          · have hr1_q1 : r1[q1]'(by omega) = x := by
              have h := bump1_getElem_self (r := r_v) (y := x - 1) (by rw [bump1_length]; exact hq1)
              have h' : r1[q1]'(by omega) = x - 1 + 1 := h
              omega
            have hr1_q2 : r1[q2]'hq2 = x := by
              exact (getElem_congr_idx heq12).trans hr1_q1
            rw [hrq2] at hr1_q2; omega
          · have hlt12 : q2 < q1 := by omega
            have hr1_q2 : r1[q2]'hq2 = r_v[q2]'(by omega) := by
              simp only [r1, bump1]; rw [List.getElem_set_ne (by omega)]
            have hge := (sortedDesc_lt_countP_iff hr_v_sort x (by omega : q2 < r_v.length)).mp (by rw [← hq1_eq]; omega)
            rw [hrq2] at hr1_q2
            omega
        have hdec1 := decTop_bump1_lt hr_v_sort hx1_rv h1x1 hq1_lt
        have hdec2 := decTop_bump1_lt hr1_sort hy1_r1 h1y1 hq2_lt
        have hp1 : x - 1 + 1 = x := Nat.sub_add_cancel (by omega)
        have hp2 : y - 1 + 1 = y := Nat.sub_add_cancel h1y
        have hdec1' : decTop M r1 + {x - 1 - 1} = decTop M r_v + {x - 1} := hdec1
        have hmult : (hh (M :: bump1 r1 (y - 1)) : Multiset ℕ) + {x - 1 - 1, y - 1 - 1} =
            (hh (M :: r_v) : Multiset ℕ) + {x - 1, y - 1} := by
          rw [hh_coe_eq_decTop, hv_hh, inv_pair_coe, inv_pair_coe]
          calc decTop M (bump1 r1 (y - 1)) + ({x - 1 - 1} + {y - 1 - 1})
              = (decTop M (bump1 r1 (y - 1)) + {y - 1 - 1}) + {x - 1 - 1} := by ac_rfl
            _ = (decTop M r1 + {y - 1}) + {x - 1 - 1} := by rw [hdec2]
            _ = (decTop M r1 + {x - 1 - 1}) + {y - 1} := by ac_rfl
            _ = (decTop M r_v + {x - 1}) + {y - 1} := by rw [hdec1']
            _ = decTop M r_v + ({x - 1} + {y - 1}) := by ac_rfl
        have hle_pair : ({x - 1 - 1, y - 1 - 1} : Multiset ℕ) ≤ (hh (M :: r_v) : Multiset ℕ) := by
          rw [hv_hh]
          have hpair := pair_le_of_distinct_take (r := r_v) (i := q1) (j := q2) (M := M)
            hq1_lt hq2_lt hM_len (by omega)
          have hr_q2 : r_v[q2]'(by omega) = y - 1 := by
            have : r1[q2]'hq2 = r_v[q2]'(by omega) := by
              simp only [r1, bump1]; rw [List.getElem_set_ne (by omega)]
            rw [← this, hrq2]
          have hq1_val : r_v[q1]'(by omega) = x - 1 := hrq1
          have hmap := Multiset.map_le_map (f := (· - 1)) hpair
          simp only [Multiset.map_coe, inv_pair_coe, Multiset.map_add, Multiset.map_singleton] at hmap
          rw [hq1_val, hr_q2, ← Multiset.map_coe] at hmap
          rw [inv_pair_coe, decTop]
          exact hmap.trans le_self_add
        have hcnt_new : (x - 1) + 1 ≤ (hh (M :: r_v)).countP (fun w => decide (y - 1 - 1 ≤ w)) := by
          rw [← filter_card_coe, hv_hh]
          have h1 := countP_succ_le_decTop M r_v (y - 1 - 1)
          have hsub : y - 1 - 1 + 1 = y - 1 := by omega
          rw [hsub] at h1
          have hrv_cnt : x ≤ r_v.countP (fun w => decide (y - 1 ≤ w)) := by
            simp only [List.countP_cons] at hcnt
            have hMy : decide (y - 1 ≤ M) = true := by simp; omega
            simp only [hMy, ↓reduceIte] at hcnt
            omega
          omega
        exact Or.inl ⟨x - 1, y - 1, h1y1, by omega, hle_pair, hmult, hcnt_new⟩
  · -- P2 case
    simp only [List.headI_cons] at hzM
    have hz_mem_ru : z - 2 ∈ r_v := by
      simp only [List.mem_cons] at hzm_mem
      rcases hzm_mem with h1 | h2
      · omega
      · exact h2
    have hru_eq : (r_u : Multiset ℕ) + {z - 2} = (r_v : Multiset ℕ) + {z} := by
      have h1 := heq
      simp only [← Multiset.cons_coe, ← Multiset.singleton_add] at h1
      have h2 : ({M} : Multiset ℕ) + ((r_u : Multiset ℕ) + {z - 2}) =
          ({M} : Multiset ℕ) + ((r_v : Multiset ℕ) + {z}) := by
        calc ({M} : Multiset ℕ) + ((r_u : Multiset ℕ) + {z - 2})
            = {M} + (r_u : Multiset ℕ) + {z - 2} := by ac_rfl
          _ = {M} + (r_v : Multiset ℕ) + {z} := h1
          _ = {M} + ((r_v : Multiset ℕ) + {z}) := by ac_rfl
      exact add_left_cancel h2
    have hz_u : z ∈ M :: r_u := by
      have h1 : z ∈ ((M :: r_v : List ℕ) : Multiset ℕ) + {z} := by simp
      rw [← heq] at h1
      rcases Multiset.mem_add.mp h1 with h1 | h1
      · exact h1
      · simp at h1; omega
    have hzM' : z ≤ M := sortedDesc_head_ge_of_mem hgu.1 hz_u
    obtain ⟨hq1, hrq1, hr1_sort, hr1_perm⟩ := bump1_spec hr_v_sort hz_mem_ru
    set r1 := bump1 r_v (z - 2)
    set q1 := r_v.countP (fun w => decide (z - 2 + 1 ≤ w))
    have hq1_eq : q1 = r_v.countP (fun w => decide (z - 1 ≤ w)) :=
      congrArg (fun p => r_v.countP p) (funext (fun w => by simp [show z - 2 + 1 = z - 1 by omega]))
    have hz1_r1 : z - 1 ∈ r1 := by
      have hmem : z - 1 ∈ (r1 : Multiset ℕ) + {z - 2} := by
        rw [hr1_perm]; simp [show z - 2 + 1 = z - 1 by omega]
      rcases Multiset.mem_add.mp hmem with h | h
      · exact h
      · simp at h; omega
    obtain ⟨hq2, hrq2, hr2_sort, hr2_perm⟩ := bump1_spec hr1_sort hz1_r1
    set q2 := r1.countP (fun w => decide (z - 1 + 1 ≤ w))
    have hq2_eq : q2 = r1.countP (fun w => decide (z ≤ w)) :=
      congrArg (fun p => r1.countP p) (funext (fun w => by simp [show z - 1 + 1 = z by omega]))
    have hru_bump : r_u = bump1 r1 (z - 1) := by
      apply sortedDesc_ext_of_perm hr_u_sort hr2_sort
      have hp1 : z - 2 + 1 = z - 1 := by omega
      have hp2 : z - 1 + 1 = z := by omega
      have hr1_perm' : (r1 : Multiset ℕ) + {z - 2} = (r_v : Multiset ℕ) + {z - 1} := by
        dsimp only [r1]; rw [hr1_perm, hp1]
      have hr2_perm' : (bump1 r1 (z - 1) : Multiset ℕ) + {z - 1} = (r1 : Multiset ℕ) + {z} := by
        rw [hr2_perm, hp2]
      have hsum : (r_u : Multiset ℕ) + ({z - 2} + {z - 1}) =
          (bump1 r1 (z - 1) : Multiset ℕ) + ({z - 2} + {z - 1}) := by
        calc (r_u : Multiset ℕ) + ({z - 2} + {z - 1})
            = ((r_u : Multiset ℕ) + {z - 2}) + {z - 1} := by ac_rfl
          _ = ((r_v : Multiset ℕ) + {z}) + {z - 1} := by rw [hru_eq]
          _ = ((r_v : Multiset ℕ) + {z - 1}) + {z} := by ac_rfl
          _ = ((r1 : Multiset ℕ) + {z - 2}) + {z} := by rw [← hr1_perm']
          _ = ((r1 : Multiset ℕ) + {z}) + {z - 2} := by ac_rfl
          _ = ((bump1 r1 (z - 1) : Multiset ℕ) + {z - 1}) + {z - 2} := by rw [← hr2_perm']
          _ = (bump1 r1 (z - 1) : Multiset ℕ) + ({z - 2} + {z - 1}) := by ac_rfl
      exact add_right_cancel hsum
    rw [hru_bump] at hgu_hh ⊢
    have hq2_le_q1 : q2 ≤ q1 := by
      by_contra hlt
      have hq1_lt : q1 < q2 := by omega
      have hlt_len : q1 < r1.length := by rw [bump1_length]; exact hq1
      have hge := (sortedDesc_lt_countP_iff hr1_sort (z - 1 + 1) hlt_len).mp hq1_lt
      have hr1_q1 : r1[q1]'hlt_len = z - 1 := by
        have h := bump1_getElem_self (r := r_v) (y := z - 2) (by rw [bump1_length]; exact hq1)
        have h' : r1[q1]'hlt_len = z - 2 + 1 := h
        omega
      rw [hr1_q1] at hge
      omega
    by_cases hq2M : M ≤ q2
    · right
      have hq1M : M ≤ q1 := by omega
      have hdec1 := decTop_bump1_ge hr_v_sort hz_mem_ru hq1M
      have hdec2 := decTop_bump1_ge hr1_sort hz1_r1 hq2M
      have hp1 : z - 2 + 1 = z - 1 := by omega
      have hp2 : z - 1 + 1 = z := by omega
      have hdec1' : decTop M r1 + {z - 2} = decTop M r_v + {z - 1} := by
        dsimp only [r1]; rw [hdec1, hp1]
      have hdec2' : decTop M (bump1 r1 (z - 1)) + {z - 1} = decTop M r1 + {z} := by
        rw [hdec2, hp2]
      have hmult : (hh (M :: bump1 r1 (z - 1)) : Multiset ℕ) + {z - 2} =
          (hh (M :: r_v) : Multiset ℕ) + {z} := by
        rw [hh_coe_eq_decTop, hv_hh]
        have hsum : decTop M (bump1 r1 (z - 1)) + {z - 2} + {z - 1} =
            decTop M r_v + {z} + {z - 1} := by
          calc decTop M (bump1 r1 (z - 1)) + {z - 2} + {z - 1}
              = (decTop M (bump1 r1 (z - 1)) + {z - 1}) + {z - 2} := by ac_rfl
            _ = (decTop M r1 + {z}) + {z - 2} := by rw [hdec2']
            _ = (decTop M r1 + {z - 2}) + {z} := by ac_rfl
            _ = (decTop M r_v + {z - 1}) + {z} := by rw [hdec1']
            _ = decTop M r_v + {z} + {z - 1} := by ac_rfl
        exact add_right_cancel hsum
      have htake_all : ∀ w ∈ r_v.take M, z ≤ w := by
        intro w hw
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hw
        have hiM : i < M := by rw [List.length_take] at hi; exact Nat.lt_of_lt_of_le hi (Nat.min_le_left _ _)
        rw [List.getElem_take]
        have hr1_i : r1[i]'(by rw [bump1_length]; omega) = r_v[i]'(by omega) := by
          simp only [r1, bump1]; rw [List.getElem_set_ne (by omega)]
        rw [← hr1_i]
        have hi_q2 : i < q2 := by omega
        have hge := (sortedDesc_lt_countP_iff hr1_sort (z - 1 + 1) (by rw [bump1_length]; omega)).mp hi_q2
        omega
      have hmem_v : z - 2 ∈ hh (M :: r_v) := by
        have h1 : z - 2 ∈ (r_v.drop M : Multiset ℕ) := by
          have hi : q1 - M < (r_v.drop M).length := by rw [List.length_drop]; omega
          have heq' : (r_v.drop M)[q1 - M]'hi = z - 2 := by rw [List.getElem_drop]; convert hrq1; omega
          rw [← heq']; exact List.getElem_mem hi
        change z - 2 ∈ (hh (M :: r_v) : Multiset ℕ)
        rw [hv_hh, decTop, Multiset.mem_add]
        exact Or.inr h1
      have hhead_le : z ≤ (hh (M :: r_v)).headI + 1 := by
        have hr0_lt : 0 < r_v.length := by omega
        have hr0_ge : z ≤ r_v[0]'hr0_lt := htake_all (r_v[0]'hr0_lt) (by
          have h0 : 0 < (r_v.take M).length := by rw [List.length_take, Nat.min_eq_left hM_len]; omega
          have heq' : (r_v.take M)[0]'h0 = r_v[0]'hr0_lt := List.getElem_take
          rw [← heq']; exact List.getElem_mem h0)
        have hmem_m : r_v[0]'hr0_lt - 1 ∈ decTop M r_v := by
          simp only [decTop, Multiset.mem_add, Multiset.mem_map, Multiset.mem_coe]
          left; refine ⟨r_v[0]'hr0_lt, ?_, rfl⟩
          have h0 : 0 < (r_v.take M).length := by rw [List.length_take, Nat.min_eq_left hM_len]; omega
          have heq' : (r_v.take M)[0]'h0 = r_v[0]'hr0_lt := List.getElem_take
          rw [← heq']; exact List.getElem_mem h0
        rw [← hv_hh] at hmem_m
        have := headI_ge_of_mem hgv_hh.1 hmem_m
        omega
      have hcnt1' : z + 1 ≤ (hh (M :: r_v)).countP (fun w => decide (z - 2 ≤ w)) := by
        rw [← filter_card_coe, hv_hh]
        have h1 := countP_decTop_add_drop (M := M) (r := r_v) (t := z - 2) (q := q1) hM_len
          (fun w hw => by have := htake_all w hw; omega) hq1M hq1 (by rw [hrq1])
        omega
      have hcnt2' : z ≤ (hh (M :: r_v)).countP (fun w => decide (z - 1 ≤ w)) := by
        rw [← filter_card_coe, hv_hh]
        have h1 : M ≤ ((decTop M r_v).filter (fun w => z - 1 ≤ w)).card := by
          simp only [decTop, Multiset.filter_add, Multiset.card_add]
          have hm : Multiset.map (· - 1) (r_v.take M : Multiset ℕ) =
              (((r_v.take M).map (· - 1) : List ℕ) : Multiset ℕ) := (Multiset.map_coe _ _).symm
          rw [hm, filter_card_coe, List.countP_map]
          have hall : ∀ w ∈ r_v.take M, ((fun x => decide (z - 1 ≤ x)) ∘ (· - 1)) w = true := by
            intro w hw; simp; have := htake_all w hw; omega
          rw [List.countP_eq_length.mpr hall, List.length_take, Nat.min_eq_left hM_len]
          omega
        omega
      exact ⟨z, h2z, hhead_le, hmem_v, hmult, hcnt1', Or.inr hcnt2'⟩
    · have hq2_lt : q2 < M := by omega
      by_cases hq1M : M ≤ q1
      · left
        have h1z1 : 1 ≤ z - 1 := by omega
        have hdec1 := decTop_bump1_ge hr_v_sort hz_mem_ru hq1M
        have hdec2 := decTop_bump1_lt hr1_sort hz1_r1 h1z1 hq2_lt
        have hp1 : z - 2 + 1 = z - 1 := by omega
        have hdec1' : decTop M r1 + {z - 2} = decTop M r_v + {z - 1} := by
          dsimp only [r1]; rw [hdec1, hp1]
        have hmult : (hh (M :: bump1 r1 (z - 1)) : Multiset ℕ) + {z - 1 - 1, z - 1 - 1} =
            (hh (M :: r_v) : Multiset ℕ) + {z - 1, z - 1} := by
          rw [hh_coe_eq_decTop, hv_hh, inv_pair_coe, inv_pair_coe]
          have hsub : z - 1 - 1 = z - 2 := by omega
          have hdec2' : decTop M (bump1 r1 (z - 1)) + {z - 2} = decTop M r1 + {z - 1} := by
            rw [← hsub]; exact hdec2
          rw [hsub]
          calc decTop M (bump1 r1 (z - 1)) + ({z - 2} + {z - 2})
              = (decTop M (bump1 r1 (z - 1)) + {z - 2}) + {z - 2} := by ac_rfl
            _ = (decTop M r1 + {z - 1}) + {z - 2} := by rw [hdec2']
            _ = (decTop M r1 + {z - 2}) + {z - 1} := by ac_rfl
            _ = (decTop M r_v + {z - 1}) + {z - 1} := by rw [hdec1']
            _ = decTop M r_v + ({z - 1} + {z - 1}) := by ac_rfl
        have htake_all : ∀ w ∈ r_v.take M, z - 2 + 1 ≤ w := by
          intro w hw
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hw
          have hiM : i < M := by rw [List.length_take] at hi; exact Nat.lt_of_lt_of_le hi (Nat.min_le_left _ _)
          rw [List.getElem_take]
          have hi_q1 : i < r_v.countP (fun w => decide (z - 1 ≤ w)) := by rw [← hq1_eq]; omega
          have hge := (sortedDesc_lt_countP_iff hr_v_sort (z - 1) (ht := by omega)).mp hi_q1
          omega
        have hpair : ({z - 2, z - 2} : Multiset ℕ) ≤ decTop M r_v := by
          have hz_in1 : z - 2 ∈ Multiset.map (· - 1) (r_v.take M : Multiset ℕ) := by
            rw [Multiset.mem_map]
            have hr1_q2 : r1[q2]'hq2 = z - 1 := hrq2
            have hr_q2 : r_v[q2]'(by omega) = z - 1 := by
              have : r1[q2]'hq2 = r_v[q2]'(by omega) := by
                simp only [r1, bump1]; rw [List.getElem_set_ne (by omega)]
              rw [← this, hr1_q2]
            refine ⟨z - 1, ?_, by omega⟩
            have hi : q2 < (r_v.take M).length := by rw [List.length_take, Nat.min_eq_left hM_len]; exact hq2_lt
            have heq' : (r_v.take M)[q2]'hi = z - 1 := by rw [List.getElem_take]; exact hr_q2
            rw [← heq']; exact List.getElem_mem hi
          have hz_in2 : z - 2 ∈ (r_v.drop M : Multiset ℕ) := by
            have hi : q1 - M < (r_v.drop M).length := by rw [List.length_drop]; omega
            have heq' : (r_v.drop M)[q1 - M]'hi = z - 2 := by rw [List.getElem_drop]; convert hrq1; omega
            rw [← heq']; exact List.getElem_mem hi
          obtain ⟨s1, hs1⟩ := Multiset.exists_cons_of_mem hz_in1
          obtain ⟨s2, hs2⟩ := Multiset.exists_cons_of_mem hz_in2
          rw [decTop, hs1, hs2, inv_pair_coe, ← Multiset.singleton_add, ← Multiset.singleton_add]
          exact multiset_le_iff_exists_add.mpr ⟨s1 + s2, by ac_rfl⟩
        have hcnt_new : (z - 1) + 1 ≤ (hh (M :: r_v)).countP (fun w => decide (z - 1 - 1 ≤ w)) := by
          have hsub : z - 1 - 1 = z - 2 := by omega
          rw [hsub, ← filter_card_coe, hv_hh]
          have h1 := countP_decTop_add_drop (M := M) (r := r_v) (t := z - 2) (q := q1) hM_len
            htake_all hq1M hq1 (by rw [hrq1])
          omega
        refine ⟨z - 1, z - 1, h1z1, le_rfl, ?_, hmult, hcnt_new⟩
        have hsub : z - 1 - 1 = z - 2 := by omega
        rw [hsub, hv_hh]; exact hpair
      · right
        have hq1_lt : q1 < M := by omega
        have h1z2 : 1 ≤ z - 2 := by
          apply hpos_v.2
          rw [← hrq1]
          have hi : q1 < (r_v.take M).length := by rw [List.length_take, Nat.min_eq_left hM_len]; exact hq1_lt
          have htake_el : (r_v.take M)[q1]'hi = r_v[q1]'hq1 := List.getElem_take
          rw [← htake_el]
          exact List.getElem_mem hi
        have h1z1 : 1 ≤ z - 1 := by omega
        have hdec1 := decTop_bump1_lt hr_v_sort hz_mem_ru h1z2 hq1_lt
        have hdec2 := decTop_bump1_lt hr1_sort hz1_r1 h1z1 hq2_lt
        have hdec1' : decTop M r1 + {z - 3} = decTop M r_v + {z - 2} := by
          dsimp only [r1]; rw [show z - 3 = z - 2 - 1 by omega]; exact hdec1
        have hdec2' : decTop M (bump1 r1 (z - 1)) + {z - 2} = decTop M r1 + {z - 1} := by
          rw [show z - 2 = z - 1 - 1 by omega]; exact hdec2
        have hmult : (hh (M :: bump1 r1 (z - 1)) : Multiset ℕ) + {z - 1 - 2} =
            (hh (M :: r_v) : Multiset ℕ) + {z - 1} := by
          rw [hh_coe_eq_decTop, hv_hh]
          have hsub : z - 1 - 2 = z - 3 := by omega
          have hsum : decTop M (bump1 r1 (z - 1)) + {z - 3} + {z - 2} =
              decTop M r_v + {z - 1} + {z - 2} := by
            calc decTop M (bump1 r1 (z - 1)) + {z - 3} + {z - 2}
                = (decTop M (bump1 r1 (z - 1)) + {z - 2}) + {z - 3} := by ac_rfl
              _ = (decTop M r1 + {z - 1}) + {z - 3} := by rw [hdec2']
              _ = (decTop M r1 + {z - 3}) + {z - 1} := by ac_rfl
              _ = (decTop M r_v + {z - 2}) + {z - 1} := by rw [hdec1']
              _ = decTop M r_v + {z - 1} + {z - 2} := by ac_rfl
          rw [hsub]; exact add_right_cancel hsum
        have hmem_v : z - 1 - 2 ∈ hh (M :: r_v) := by
          have h1 : z - 2 - 1 ∈ Multiset.map (· - 1) (r_v.take M : Multiset ℕ) := by
            rw [Multiset.mem_map]; refine ⟨z - 2, ?_, rfl⟩
            have hi : q1 < (r_v.take M).length := by rw [List.length_take, Nat.min_eq_left hM_len]; exact hq1_lt
            have heq' : (r_v.take M)[q1]'hi = z - 2 := by rw [List.getElem_take]; exact hrq1
            rw [← heq']; exact List.getElem_mem hi
          have hsub : z - 1 - 2 = z - 2 - 1 := by omega
          change z - 1 - 2 ∈ (hh (M :: r_v) : Multiset ℕ)
          rw [hsub, hv_hh, decTop, Multiset.mem_add]
          exact Or.inl h1
        have hr0_lt : 0 < r_v.length := by omega
        have hq1_pos : 1 ≤ q1 := by
          rcases hcnt2 with hzm1 | hcnt_z1
          · simp only [List.mem_cons] at hzm1
            have hz1_rv : z - 1 ∈ r_v := by rcases hzm1 with h | h; omega; exact h
            obtain ⟨i, hi, hir⟩ := List.mem_iff_getElem.mp hz1_rv
            have hiq := (sortedDesc_lt_countP_iff hr_v_sort (z - 1) hi).mpr (by rw [hir])
            rw [hq1_eq]; omega
          · simp only [List.countP_cons] at hcnt_z1
            have hM_ge : decide (z - 1 ≤ M) = true := by simp; omega
            simp only [hM_ge, ↓reduceIte] at hcnt_z1
            rw [hq1_eq]; omega
        have hhead_le : z - 1 ≤ (hh (M :: r_v)).headI + 1 := by
          have hr0_ge : z - 1 ≤ r_v[0]'hr0_lt :=
            (sortedDesc_lt_countP_iff hr_v_sort (z - 1) hr0_lt).mp (by rw [← hq1_eq]; omega)
          have hmem_m : r_v[0]'hr0_lt - 1 ∈ decTop M r_v := by
            simp only [decTop, Multiset.mem_add, Multiset.mem_map, Multiset.mem_coe]
            left; refine ⟨r_v[0]'hr0_lt, ?_, rfl⟩
            have h0 : 0 < (r_v.take M).length := by rw [List.length_take, Nat.min_eq_left hM_len]; omega
            have heq' : (r_v.take M)[0]'h0 = r_v[0]'hr0_lt := List.getElem_take
            rw [← heq']; exact List.getElem_mem h0
          rw [← hv_hh] at hmem_m
          have := headI_ge_of_mem hgv_hh.1 hmem_m
          omega
        have hcnt1' : z - 1 + 1 ≤ (hh (M :: r_v)).countP (fun w => decide (z - 1 - 2 ≤ w)) := by
          have hsub : z - 1 - 2 = z - 3 := by omega
          rw [hsub, ← filter_card_coe, hv_hh]
          have h1 := countP_succ_le_decTop M r_v (z - 3)
          have hsub2 : z - 3 + 1 = z - 2 := by omega
          rw [hsub2] at h1
          have hrv_cnt : z ≤ r_v.countP (fun w => decide (z - 2 ≤ w)) := by
            simp only [List.countP_cons] at hcnt1
            have hM_ge : decide (z - 2 ≤ M) = true := by simp; omega
            simp only [hM_ge, ↓reduceIte] at hcnt1
            omega
          omega
        have hdisj' : z - 1 - 1 ∈ hh (M :: r_v) ∨ z - 1 ≤ (hh (M :: r_v)).countP (fun w => decide (z - 1 - 1 ≤ w)) := by
          rcases hcnt2 with hzm1 | hcnt_z1
          · left
            simp only [List.mem_cons] at hzm1
            have hz1_rv : z - 1 ∈ r_v := by rcases hzm1 with h | h; omega; exact h
            obtain ⟨i, hi, hir⟩ := List.mem_iff_getElem.mp hz1_rv
            have hiq : i < q1 := by
              rw [hq1_eq]
              exact (sortedDesc_lt_countP_iff hr_v_sort (z - 1) hi).mpr (by rw [hir])
            have hiM : i < (r_v.take M).length := by rw [List.length_take, Nat.min_eq_left hM_len]; omega
            have hmem_t : z - 1 ∈ r_v.take M := by
              have heq' : (r_v.take M)[i]'hiM = z - 1 := by rw [List.getElem_take]; exact hir
              rw [← heq']; exact List.getElem_mem hiM
            change z - 1 - 1 ∈ (hh (M :: r_v) : Multiset ℕ)
            rw [hv_hh, decTop, Multiset.mem_add]
            left; rw [Multiset.mem_map]
            exact ⟨z - 1, hmem_t, by omega⟩
          · right
            have hsub : z - 1 - 1 = z - 2 := by omega
            rw [hsub, ← filter_card_coe, hv_hh]
            have h1 := countP_succ_le_decTop M r_v (z - 2)
            have hsub2 : z - 2 + 1 = z - 1 := by omega
            rw [hsub2] at h1
            simp only [List.countP_cons] at hcnt_z1
            have hM_ge : decide (z - 1 ≤ M) = true := by simp; omega
            simp only [hM_ge, ↓reduceIte] at hcnt_z1
            omega
        exact ⟨z - 1, by omega, hhead_le, hmem_v, hmult, hcnt1', hdisj'⟩

lemma inv_drop {v u : List ℕ} (hInv : Inv v u)
    (hv_ne : v ≠ []) (hu_ne : u ≠ []) (hpos : 1 ≤ v.head hv_ne)
    (h0 : v.head hv_ne < u.head hu_ne) :
    Maj (hh v) (hh u) := by
  rcases hInv with ⟨hgv, hgu, hP⟩
  obtain ⟨M, r_v, rfl⟩ := List.exists_cons_of_ne_nil hv_ne
  obtain ⟨Mu, r_u, rfl⟩ := List.exists_cons_of_ne_nil hu_ne
  simp only [List.head_cons] at hpos h0
  have hr_v_sort : SortedDesc r_v := sortedDesc_tail hgv.1
  have hr_u_sort : SortedDesc r_u := sortedDesc_tail hgu.1
  have hpos_v := isGraphical_take_pos hgv
  have hpos_u := isGraphical_take_pos hgu
  have hMu_eq : Mu = M + 1 := by
    rcases hP with ⟨x, y, h1y, hyx, hpair_le, heq, hcnt⟩ | ⟨z, h2z, hzM, hzm_mem, heq, hcnt1, hcnt2⟩
    · have hmu_mem : Mu ∈ ((M :: r_v : List ℕ) : Multiset ℕ) + {x, y} := by rw [← heq]; simp
      have hxm : x - 1 ∈ (M :: r_v) := (mem_of_pair_le hpair_le).1
      have hxm_le := sortedDesc_head_ge_of_mem hgv.1 hxm
      rcases Multiset.mem_add.mp hmu_mem with h1 | h2
      · have := sortedDesc_head_ge_of_mem hgv.1 h1; omega
      · simp only [inv_pair_coe, Multiset.mem_add, Multiset.mem_singleton] at h2
        rcases h2 with rfl | rfl <;> omega
    · have hmu_mem : Mu ∈ ((M :: r_v : List ℕ) : Multiset ℕ) + {z} := by rw [← heq]; simp
      simp only [List.headI_cons] at hzM
      rcases Multiset.mem_add.mp hmu_mem with h1 | h2
      · have := sortedDesc_head_ge_of_mem hgv.1 h1; omega
      · simp at h2; omega
  subst hMu_eq
  have hM_len : M ≤ r_v.length := hpos_v.1
  have hM1_len : M + 1 ≤ r_u.length := hpos_u.1
  have hgv_hh : IsGraphical (hh (M :: r_v)) := isGraphical_cons_succ_head hgv hpos
  have hgu_hh : IsGraphical (hh ((M + 1) :: r_u)) := (isGraphical_hh hgu).1
  have hv_hh : (hh (M :: r_v) : Multiset ℕ) = decTop M r_v := hh_coe_eq_decTop M r_v
  have hu_hh : (hh ((M + 1) :: r_u) : Multiset ℕ) = decTop (M + 1) r_u := hh_coe_eq_decTop (M + 1) r_u
  rcases hP with ⟨x, y, h1y, hyx, hpair_le, heq, hcnt⟩ | ⟨z, h2z, hzM, hzm_mem, heq, hcnt1, hcnt2⟩
  · have hx_eq : x = M + 1 := by
      have hmem : M + 1 ∈ ((M :: r_v : List ℕ) : Multiset ℕ) + {x, y} := by rw [← heq]; simp
      have hxm : x - 1 ∈ (M :: r_v) := (mem_of_pair_le hpair_le).1
      have hxm_le := sortedDesc_head_ge_of_mem hgv.1 hxm
      rcases Multiset.mem_add.mp hmem with h1 | h2
      · have := sortedDesc_head_ge_of_mem hgv.1 h1; omega
      · simp only [inv_pair_coe, Multiset.mem_add, Multiset.mem_singleton] at h2
        rcases h2 with h2 | h2 <;> omega
    subst hx_eq
    have hru_eq : (r_u : Multiset ℕ) + {y - 1} = (r_v : Multiset ℕ) + {y} := by
      have h1 := heq
      simp only [← Multiset.cons_coe, ← Multiset.singleton_add, inv_pair_coe, Nat.add_sub_cancel] at h1
      have ha : ({M + 1} : Multiset ℕ) + (r_u : Multiset ℕ) + ({M} + {y - 1}) =
          ({M + 1} + {M}) + ((r_u : Multiset ℕ) + {y - 1}) := by ac_rfl
      have hb : ({M} : Multiset ℕ) + (r_v : Multiset ℕ) + ({M + 1} + {y}) =
          ({M + 1} + {M}) + ((r_v : Multiset ℕ) + {y}) := by ac_rfl
      rw [ha, hb] at h1
      exact add_left_cancel h1
    have hy1_rv : y - 1 ∈ r_v := by
      have hm1 : ({M, y - 1} : Multiset ℕ) ≤ ((M :: r_v : List ℕ) : Multiset ℕ) := by
        simpa [Nat.add_sub_cancel] using hpair_le
      have hcons : ((M :: r_v : List ℕ) : Multiset ℕ) = {M} + (r_v : Multiset ℕ) := by
        rw [← Multiset.cons_coe, ← Multiset.singleton_add]
      rw [hcons, inv_pair_coe] at hm1
      obtain ⟨s, hs⟩ := multiset_le_iff_exists_add.mp hm1
      have hs' : {M} + (r_v : Multiset ℕ) = {M} + ({y - 1} + s) := by rw [hs]; ac_rfl
      have h1 := add_left_cancel hs'
      have : y - 1 ∈ (r_v : Multiset ℕ) := by rw [h1]; simp
      exact this
    obtain ⟨hq, hrq, hbu_sort, hbu_perm⟩ := bump1_spec hr_v_sort hy1_rv
    have hru_bump : r_u = bump1 r_v (y - 1) := by
      apply sortedDesc_ext_of_perm hr_u_sort hbu_sort
      have hp : y - 1 + 1 = y := Nat.sub_add_cancel h1y
      have hbu_perm' : (bump1 r_v (y - 1) : Multiset ℕ) + {y - 1} = (r_v : Multiset ℕ) + {y} := by
        rw [hbu_perm, hp]
      have h1 : (r_u : Multiset ℕ) + {y - 1} = (bump1 r_v (y - 1) : Multiset ℕ) + {y - 1} := by
        rw [hru_eq, ← hbu_perm']
      exact add_right_cancel h1
    have hrv_len_eq : r_u.length = r_v.length := by rw [hru_bump, bump1_length]
    have hrv_M1 : M + 1 ≤ r_v.length := by omega
    have hrv_cnt : M + 1 ≤ r_v.countP (fun w => decide (y - 1 ≤ w)) := by
      simp only [List.countP_cons] at hcnt
      have hM_ge : decide (y - 1 ≤ M) = true := by simp; omega
      simp only [hM_ge, ↓reduceIte] at hcnt
      omega
    have hrm_ge : y - 1 ≤ r_v[M]'(by omega) :=
      (sortedDesc_lt_countP_iff hr_v_sort (y - 1) (by omega : M < r_v.length)).mp (by omega)
    set q := r_v.countP (fun w => decide (y - 1 + 1 ≤ w))
    have hq_eq : q = r_v.countP (fun w => decide (y ≤ w)) :=
      congrArg (fun p => r_v.countP p) (funext (fun w => by simp [Nat.sub_add_cancel h1y]))
    have hp : y - 1 + 1 = y := Nat.sub_add_cancel h1y
    have hru_hh_eq : hh ((M + 1) :: r_u) = hh (M :: r_v) → Maj (hh (M :: r_v)) (hh ((M + 1) :: r_u)) := by
      intro h; rw [h]; exact maj_refl hgv_hh.1
    by_cases hqm : q < M
    · have hrm_eq : r_v[M]'(by omega) = y - 1 := by
        have h1 := sortedDesc_ge_of_le hr_v_sort (by omega : q ≤ M) (by omega)
        have h2 : r_v[q]'hq = y - 1 := hrq
        omega
      have h1y1 : 1 ≤ y - 1 := by
        apply hpos_v.2
        rw [← hrq]
        have hi : q < (r_v.take M).length := by rw [List.length_take, Nat.min_eq_left hM_len]; exact hqm
        have htake_el : (r_v.take M)[q]'hi = r_v[q]'hq := List.getElem_take
        rw [← htake_el]
        exact List.getElem_mem hi
      have hdec := decTop_bump1_lt hr_v_sort hy1_rv h1y1 (by omega : q < M + 1)
      have hdec_M := decTop_succ (M := M) (r := r_v) (by omega)
      have hcoe_eq : (hh (M :: r_v) : Multiset ℕ) = (hh ((M + 1) :: r_u) : Multiset ℕ) := by
        rw [hv_hh, hu_hh, hru_bump]
        have hsum : decTop (M + 1) (bump1 r_v (y - 1)) + {y - 1 - 1} =
            decTop M r_v + {y - 1 - 1} := by
          calc decTop (M + 1) (bump1 r_v (y - 1)) + {y - 1 - 1}
              = decTop (M + 1) r_v + {y - 1} := hdec
            _ = decTop (M + 1) r_v + {r_v[M]'(by omega)} := by rw [hrm_eq]
            _ = decTop M r_v + {r_v[M]'(by omega) - 1} := hdec_M.symm
            _ = decTop M r_v + {y - 1 - 1} := by rw [hrm_eq]
        exact (add_right_cancel hsum).symm
      rw [sortedDesc_ext_of_perm hgv_hh.1 hgu_hh.1 hcoe_eq]
      exact maj_refl hgu_hh.1
    · by_cases hqeq : q = M
      · have hrm_eq : r_v[M]'(by omega) = y - 1 := by
          have h1 : r_v[q]'hq = y - 1 := hrq
          have h2 : r_v[M]'(by omega) = r_v[q]'hq := by congr 1; exact hqeq.symm
          rw [h2, h1]
        have hdec_M := decTop_succ (M := M) (r := r_v) (by omega)
        have hlt_M1 : q < M + 1 := by omega
        have hcoe_eq : (hh (M :: r_v) : Multiset ℕ) = (hh ((M + 1) :: r_u) : Multiset ℕ) := by
          rw [hv_hh, hu_hh, hru_bump]
          rcases Nat.eq_zero_or_pos (y - 1) with hy0 | h1y1
          · simp only [decTop, bump1]
            rw [take_set_of_lt r_v q (M + 1) (y - 1 + 1) hlt_M1, drop_set_of_lt r_v q (M + 1) (y - 1 + 1) hlt_M1]
            have hq_t : q < (r_v.take (M + 1)).length := by rw [List.length_take, Nat.min_eq_left hrv_M1]; exact hlt_M1
            have hm := multiset_set hq_t (y - 1 + 1)
            have hrq_t : (r_v.take (M + 1))[q]'hq_t = y - 1 := by rw [List.getElem_take]; exact hrq
            rw [hrq_t] at hm
            have hmap := congrArg (Multiset.map (· - 1)) hm
            simp only [Multiset.map_add, Multiset.map_singleton, Nat.add_sub_cancel, hy0, Nat.zero_sub] at hmap
            have hd_eq : decTop (M + 1) r_v + {r_v[M]'(by omega)} = decTop M r_v + {r_v[M]'(by omega) - 1} := hdec_M.symm
            rw [hrm_eq, hy0] at hd_eq
            have h1_set : y - 1 + 1 = 1 := by omega
            have hsum : (Multiset.map (· - 1) ↑((r_v.take (M + 1)).set q (y - 1 + 1)) +
                (r_v.drop (M + 1) : Multiset ℕ)) + {0} = decTop M r_v + {0} := by
              rw [h1_set]
              calc (Multiset.map (· - 1) ↑((r_v.take (M + 1)).set q 1) + (r_v.drop (M + 1) : Multiset ℕ)) + {0}
                  = Multiset.map (· - 1) ↑((r_v.take (M + 1)).set q (0 + 1)) + {0} + (r_v.drop (M + 1) : Multiset ℕ) := by ac_rfl
                _ = Multiset.map (· - 1) ↑(r_v.take (M + 1)) + {0} + (r_v.drop (M + 1) : Multiset ℕ) := by rw [hmap]
                _ = (Multiset.map (· - 1) ↑(r_v.take (M + 1)) + (r_v.drop (M + 1) : Multiset ℕ)) + {0} := by ac_rfl
                _ = decTop (M + 1) r_v + {0} := rfl
                _ = decTop M r_v + {0} := hd_eq
            exact (add_right_cancel hsum).symm
          · have hdec := decTop_bump1_lt hr_v_sort hy1_rv h1y1 hlt_M1
            have hsum : decTop (M + 1) (bump1 r_v (y - 1)) + {y - 1 - 1} =
                decTop M r_v + {y - 1 - 1} := by
              calc decTop (M + 1) (bump1 r_v (y - 1)) + {y - 1 - 1}
                  = decTop (M + 1) r_v + {y - 1} := hdec
                _ = decTop (M + 1) r_v + {r_v[M]'(by omega)} := by rw [hrm_eq]
                _ = decTop M r_v + {r_v[M]'(by omega) - 1} := hdec_M.symm
                _ = decTop M r_v + {y - 1 - 1} := by rw [hrm_eq]
            exact (add_right_cancel hsum).symm
        rw [sortedDesc_ext_of_perm hgv_hh.1 hgu_hh.1 hcoe_eq]
        exact maj_refl hgu_hh.1
      · have hM1_le : M + 1 ≤ q := by omega
        set z := r_v[M]'(by omega)
        have hyz : y ≤ z :=
          (sortedDesc_lt_countP_iff hr_v_sort y (by omega : M < r_v.length)).mp (by rw [← hq_eq]; omega)
        have hdec := decTop_bump1_ge hr_v_sort hy1_rv hM1_le
        have hdec_M := decTop_succ (M := M) (r := r_v) (by omega)
        have hdec' : decTop (M + 1) (bump1 r_v (y - 1)) + {y - 1} = decTop (M + 1) r_v + {y} := by
          rw [hdec, hp]
        have hmult : (hh ((M + 1) :: bump1 r_v (y - 1)) : Multiset ℕ) + {z, y - 1} =
            (hh (M :: r_v) : Multiset ℕ) + {z - 1, y} := by
          rw [hh_coe_eq_decTop, hv_hh, inv_pair_coe, inv_pair_coe]
          have hsum : decTop (M + 1) (bump1 r_v (y - 1)) + ({z} + {y - 1}) + {z} =
              decTop M r_v + ({z - 1} + {y}) + {z} := by
            calc decTop (M + 1) (bump1 r_v (y - 1)) + ({z} + {y - 1}) + {z}
                = (decTop (M + 1) (bump1 r_v (y - 1)) + {y - 1}) + {z} + {z} := by ac_rfl
              _ = (decTop (M + 1) r_v + {y}) + {z} + {z} := by rw [hdec']
              _ = (decTop (M + 1) r_v + {z}) + {y} + {z} := by ac_rfl
              _ = (decTop M r_v + {z - 1}) + {y} + {z} := by rw [← hdec_M]
              _ = decTop M r_v + ({z - 1} + {y}) + {z} := by ac_rfl
          exact add_right_cancel hsum
        rw [← hru_bump] at hmult
        by_cases hzy : z = y
        · have hcoe_eq : (hh (M :: r_v) : Multiset ℕ) = (hh ((M + 1) :: r_u) : Multiset ℕ) := by
            rw [hzy] at hmult
            have hm' : ({y, y - 1} : Multiset ℕ) = {y - 1, y} := by rw [inv_pair_coe, inv_pair_coe]; ac_rfl
            rw [hm'] at hmult
            exact (add_right_cancel hmult).symm
          rw [sortedDesc_ext_of_perm hgv_hh.1 hgu_hh.1 hcoe_eq]
          exact maj_refl hgu_hh.1
        · have hgap : z ≥ (y - 1) + 2 := by omega
          have hz_mem : z ∈ hh (M :: r_v) := by
            have h1 : z ∈ (r_v.drop M : Multiset ℕ) := by
              have h0 : 0 < (r_v.drop M).length := by rw [List.length_drop]; omega
              have heq' : (r_v.drop M)[0]'h0 = z := by rw [List.getElem_drop]; congr 1
              rw [← heq']; exact List.getElem_mem h0
            change z ∈ (hh (M :: r_v) : Multiset ℕ)
            rw [hv_hh, decTop, Multiset.mem_add]
            exact Or.inr h1
          have hy1_mem : y - 1 ∈ hh (M :: r_v) := by
            have h1 : y - 1 ∈ (r_v.drop (M + 1) : Multiset ℕ) := by
              have hq_d : q - (M + 1) < (r_v.drop (M + 1)).length := by rw [List.length_drop]; omega
              have heq' : (r_v.drop (M + 1))[q - (M + 1)]'hq_d = y - 1 := by
                rw [List.getElem_drop]; convert hrq; omega
              rw [← heq']; exact List.getElem_mem hq_d
            have hspl : r_v.drop M = z :: r_v.drop (M + 1) := drop_eq_getElem_cons (by omega)
            have h1' : y - 1 ∈ (r_v.drop M : Multiset ℕ) := by
              rw [hspl, ← Multiset.cons_coe]; exact Multiset.mem_cons_of_mem h1
            change y - 1 ∈ (hh (M :: r_v) : Multiset ℕ)
            rw [hv_hh, decTop, Multiset.mem_add]
            exact Or.inr h1'
          have hmult' : (hh ((M + 1) :: r_u) : Multiset ℕ) + {z, y - 1} =
              (hh (M :: r_v) : Multiset ℕ) + {z - 1, y - 1 + 1} := by rwa [hp]
          exact maj_of_elementaryTransfer hgv_hh.1 hgu_hh.1 hgap hz_mem hy1_mem hmult'
  · have hz_eq : z = M + 1 := by
      have hmem : M + 1 ∈ ((M :: r_v : List ℕ) : Multiset ℕ) + {z} := by rw [← heq]; simp
      rcases Multiset.mem_add.mp hmem with h1 | h2
      · have := sortedDesc_head_ge_of_mem hgv.1 h1; omega
      · simp at h2; exact h2.symm
    subst hz_eq
    have h1M : 1 ≤ M := by omega
    have hrv_cnt : M + 1 ≤ r_v.countP (fun w => decide (M - 1 ≤ w)) := by
      simp only [List.countP_cons] at hcnt1
      have hsub : M + 1 - 2 = M - 1 := by omega
      rw [hsub] at hcnt1
      have hM_ge : decide (M - 1 ≤ M) = true := by simp
      simp only [hM_ge, ↓reduceIte] at hcnt1
      omega
    have hrv_M : M < r_v.length := by
      have := List.countP_le_length (p := fun w => decide (M - 1 ≤ w)) (l := r_v)
      omega
    have hle : M - 1 ≤ r_v[M]'hrv_M :=
      (sortedDesc_lt_countP_iff hr_v_sort (M - 1) hrv_M).mp (by omega)
    have hm1_rv : M - 1 ∈ r_v := by
      simp only [List.mem_cons] at hzm_mem
      rcases hzm_mem with h1 | h2
      · omega
      · exact h2
    have hru_eq_er : r_u = M :: r_v.erase (M - 1) := by
      apply sortedDesc_ext_of_perm hr_u_sort
      · refine List.Pairwise.cons (fun w hw => ?_) (erase_sortedDesc hr_v_sort (M - 1))
        exact sortedDesc_head_ge_of_mem hgv.1 (by simp [List.mem_of_mem_erase hw])
      · have h1 := heq
        simp only [← Multiset.cons_coe, ← Multiset.singleton_add] at h1
        have hsub : M + 1 - 2 = M - 1 := by omega
        rw [hsub] at h1
        have ha : ({M + 1} : Multiset ℕ) + (r_u : Multiset ℕ) + {M - 1} =
            ({M + 1} : Multiset ℕ) + ((r_u : Multiset ℕ) + {M - 1}) := by ac_rfl
        have hb : ({M} : Multiset ℕ) + (r_v : Multiset ℕ) + {M + 1} =
            ({M + 1} : Multiset ℕ) + ({M} + (r_v : Multiset ℕ)) := by ac_rfl
        rw [ha, hb] at h1
        have hc := add_left_cancel h1
        have hd := multiset_erase_add hm1_rv
        rw [← hd] at hc
        have hd2 : ((r_u : Multiset ℕ) + {M - 1}) = ({M} + (r_v.erase (M - 1) : Multiset ℕ)) + {M - 1} := by
          rw [hc]; ac_rfl
        rw [← Multiset.cons_coe, ← Multiset.singleton_add]
        exact add_right_cancel hd2
    have hhead_rv : ∀ w ∈ r_v, w ≤ M := fun w hw => sortedDesc_head_ge_of_mem hgv.1 (by simp [hw])
    have hcoe_eq : (hh (M :: r_v) : Multiset ℕ) = (hh ((M + 1) :: r_u) : Multiset ℕ) := by
      rw [hv_hh, hu_hh, hru_eq_er]
      exact decTop_erase_head hr_v_sort h1M hrv_M hle hm1_rv hhead_rv
    rw [sortedDesc_ext_of_perm hgv_hh.1 hgu_hh.1 hcoe_eq]
    exact maj_refl hgu_hh.1

lemma hhIter_sum_zero_of_all_zero {l : List ℕ} (hl : ∀ x ∈ l, x = 0) :
    ∀ t, (hhIter t l).sum = 0 := by
  intro t
  induction t generalizing l with
  | zero =>
    simp only [hhIter, Function.iterate_zero, id_eq, List.sum_eq_zero_iff]
    exact hl
  | succ t ih =>
    cases l with
    | nil =>
      have : hh [] = [] := rfl
      simp only [hhIter, Function.iterate_succ_apply, this]
      exact ih (fun _ h => by simp at h)
    | cons d s =>
      have hd : d = 0 := hl d (by simp)
      subst hd
      have hs0 : ∀ x ∈ s, x = 0 := fun x hx => hl x (by simp [hx])
      have hhh0 : hh (0 :: s) = s := by
        simp only [hh, havelHakimiStep, List.splitAt_eq, List.take_zero, List.map_nil,
          List.nil_append, List.drop_zero]
        exact List.mergeSort_of_pairwise (List.pairwise_iff_getElem.mpr (fun i j hi hj _ => by
          have h1 := hs0 s[i] (List.getElem_mem hi)
          have h2 := hs0 s[j] (List.getElem_mem hj)
          simp [h1, h2]))
      simpa [hhIter, Function.iterate_succ_apply, hhh0] using ih hs0

lemma inv_sum_le_aux (n : ℕ)
    (ih_n : ∀ {a b : List ℕ}, a.length < n → IsGraphical a → IsGraphical b → Maj a b →
      ∀ t, (hhIter t a).sum ≤ (hhIter t b).sum) :
    ∀ {v u : List ℕ}, v.length = n → Inv v u → ∀ t, (hhIter t v).sum ≤ (hhIter t u).sum := by
  intro v u hvlen hInv t
  induction t generalizing v u n with
  | zero =>
    rcases hInv with ⟨_, _, hP⟩
    rcases hP with ⟨x, y, h1y, hyx, _, heq, _⟩ | ⟨z, h2z, _, _, heq, _, _⟩
    · have hs := congrArg Multiset.sum heq
      simp only [Multiset.sum_add, Multiset.sum_coe, Multiset.sum_pair, hhIter,
        Function.iterate_zero, id_eq] at hs ⊢
      omega
    · have hs := congrArg Multiset.sum heq
      simp only [Multiset.sum_add, Multiset.sum_coe, Multiset.sum_singleton, hhIter,
        Function.iterate_zero, id_eq] at hs ⊢
      omega
  | succ t ih =>
    cases v with
    | nil =>
      simp only [hhIter, Function.iterate_succ_apply]
      have : hh [] = [] := rfl
      rw [this, show (hh^[t] []).sum = 0 from hhIter_sum_zero_of_all_zero (fun _ h => by simp at h) t]
      exact Nat.zero_le _
    | cons d r_v =>
      cases d with
      | zero =>
        have hr0 : ∀ w ∈ (0 :: r_v), w = 0 := fun w hw => by
          have := sortedDesc_head_ge_of_mem hInv.1.1 hw
          omega
        rw [hhIter_sum_zero_of_all_zero hr0]
        exact Nat.zero_le _
      | succ d =>
        have hulen : (0 < u.length) := by
          have hlen := inv_length_eq hInv
          rw [← hlen]; simp
        have hu_ne : u ≠ [] := List.ne_nil_of_length_pos hulen
        have hhead_le := inv_head_le hInv (by simp) hu_ne
        simp only [hhIter, Function.iterate_succ_apply]
        have hlen_hh : (hh ((d + 1) :: r_v)).length < n := by
          rw [length_hh, ← hvlen]; simp
        obtain ⟨Mu, r_u, rfl⟩ := List.exists_cons_of_ne_nil hu_ne
        by_cases heq_head : ((d + 1) :: r_v).head (by simp) = (Mu :: r_u).head (by simp)
        · rcases inv_step_head_eq hInv (by simp) (by simp) heq_head (by simp) with hmaj | hInv'
          · have hMu : Mu = d + 1 := by simpa using heq_head.symm
            subst hMu
            exact ih_n hlen_hh (isGraphical_hh hInv.1).1 (isGraphical_hh hInv.2.1).1 hmaj t
          · exact ih (hh ((d + 1) :: r_v)).length
              (fun {c d'} hc => ih_n (Nat.lt_trans hc hlen_hh))
              rfl hInv'
        · have hlt_head : ((d + 1) :: r_v).head (by simp) < (Mu :: r_u).head (by simp) := by omega
          have hmaj := inv_drop hInv (by simp) (by simp) (by simp) hlt_head
          have hpos_Mu : 1 ≤ Mu := by simp only [List.head_cons] at hlt_head; omega
          exact ih_n hlen_hh (isGraphical_hh hInv.1).1 (isGraphical_cons_succ_head hInv.2.1 hpos_Mu) hmaj t

lemma triesch_sum_le :
    ∀ {a b : List ℕ}, IsGraphical a → IsGraphical b → Maj a b →
      ∀ t, (hhIter t a).sum ≤ (hhIter t b).sum := by
  intro a b ha hb hab t
  induction hn : a.length using Nat.strong_induction_on generalizing a b t with
  | _ n ih =>
    refine (maj_induction (fun a' => a'.length = n → ∀ t', (hhIter t' a').sum ≤ (hhIter t' b).sum)
      (fun a1 a2 ha1 ha2_sort ⟨x, y, hxy, hx, hy, hperm⟩ hPa2 ha1_len t' => ?_)
      ha hab (fun _ _ => le_rfl)) hn t
    have ha2_gr : IsGraphical a2 := isGraphical_robinHood ha1 ha2_sort hxy hx hy hperm
    have ha2_len : a2.length = n := by
      have hc := congrArg Multiset.card hperm
      have hlen : a2.length = a1.length := by simpa [inv_pair_coe] using hc
      exact hlen.trans ha1_len
    have hPa2' := hPa2 ha2_len
    cases t' with
    | zero =>
      have hs := congrArg Multiset.sum hperm
      simp only [Multiset.sum_add, Multiset.sum_coe, Multiset.sum_pair, hhIter,
        Function.iterate_zero, id_eq] at hs ⊢
      have := hPa2' 0
      simp only [hhIter, Function.iterate_zero, id_eq] at this
      omega
    | succ t' =>
      by_cases ha1_nil : a1 = []
      · subst ha1_nil; simp at hx
      · have ha2_nil : a2 ≠ [] := by
          intro h2; have := congrArg Multiset.card hperm; rw [h2] at this; simp at this; subst this; exact ha1_nil rfl
        have hhead_le : a2.head ha2_nil ≤ a1.head ha1_nil := by
          obtain ⟨x0, r1, rfl⟩ := List.exists_cons_of_ne_nil ha1_nil
          obtain ⟨y0, r2, rfl⟩ := List.exists_cons_of_ne_nil ha2_nil
          simp only [List.head_cons]
          have hmem : y0 ∈ ((x0 :: r1 : List ℕ) : Multiset ℕ) + {x - 1, y + 1} := by rw [← hperm]; simp
          rcases Multiset.mem_add.mp hmem with h1 | h2
          · exact sortedDesc_head_ge_of_mem ha1.1 h1
          · simp at h2
            have hx_le := sortedDesc_head_ge_of_mem ha1.1 hx
            rcases h2 with rfl | rfl <;> omega
        by_cases hlt_head : a2.head ha2_nil < a1.head ha1_nil
        · have hInv := inv_of_transfer_head ha1 ha2_gr hxy hx hy hperm (fun _ _ => by simpa using hlt_head)
          have hlen_hh : (hh a1).length < n := by
            obtain ⟨x0, r1, rfl⟩ := List.exists_cons_of_ne_nil ha1_nil
            rw [length_hh, ← ha1_len]; simp
          have h1 := inv_sum_le_aux (hh a1).length
            (fun {c d'} hc hcG hd'G hmaj t => ih _ (Nat.lt_trans hc hlen_hh) hcG hd'G hmaj t rfl)
            rfl hInv t'
          have h2 := hPa2' (t' + 1)
          simp only [hhIter, Function.iterate_succ_apply] at h1 h2 ⊢
          exact h1.trans h2
        · have heq_head : a2.head ha2_nil = a1.head ha1_nil := by omega
          obtain ⟨M, r1, rfl⟩ := List.exists_cons_of_ne_nil ha1_nil
          obtain ⟨Mu, r2, rfl⟩ := List.exists_cons_of_ne_nil ha2_nil
          simp only [List.head_cons] at heq_head
          subst Mu
          rcases Nat.eq_zero_or_pos M with rfl | hpos
          · have h0 : ∀ w ∈ (0 :: r1), w = 0 := fun w hw => by
              have := sortedDesc_head_ge_of_mem ha1.1 hw; omega
            rw [hhIter_sum_zero_of_all_zero h0]; exact Nat.zero_le _
          · have hgr1 : IsGraphical (hh (M :: r1)) := isGraphical_cons_succ_head ha1 hpos
            have hgr2 : IsGraphical (hh (M :: r2)) := isGraphical_cons_succ_head ha2_gr hpos
            have hr2_perm : (r2 : Multiset ℕ) + {x, y} = (r1 : Multiset ℕ) + {x - 1, y + 1} := by
              have h1 := hperm
              simp only [← Multiset.cons_coe, ← Multiset.singleton_add] at h1
              have ha' : ({M} : Multiset ℕ) + ((r2 : Multiset ℕ) + {x, y}) =
                  ({M} : Multiset ℕ) + ((r1 : Multiset ℕ) + {x - 1, y + 1}) := by
                calc ({M} : Multiset ℕ) + ((r2 : Multiset ℕ) + {x, y})
                    = {M} + (r2 : Multiset ℕ) + {x, y} := by ac_rfl
                  _ = {M} + (r1 : Multiset ℕ) + {x - 1, y + 1} := h1
                  _ = {M} + ((r1 : Multiset ℕ) + {x - 1, y + 1}) := by ac_rfl
              exact add_left_cancel ha'
            -- Wait: if x = M (and M is still at Mu = M), then M in r1 is x, so (M :: r1) had TWO copies of M (x in r1)!
            -- If x < M, then x, y in r1 directly!
            -- So in ALL cases, x ∈ r1 and y ∈ r1! Wait: what if x = M and x NOT in r1 (only 1 copy of M in M :: r1)?
            -- Then M was removed from M :: r1, so x - 1 = M - 1 and y + 1 <= M - 1 -> M :: r2 couldn't have M!! Contradiction!
            have hx_r1 : x ∈ r1 := by
              by_contra hnx
              have hxM : x = M := by
                have := hx; simp only [List.mem_cons] at this; rcases this with rfl | h; rfl; exact absurd h hnx
              subst hxM
              have hc := congrArg (Multiset.count x) hr2_perm
              have hxr1 : r1.count x = 0 := List.count_eq_zero.mpr hnx
              have hxy1 : y + 1 < x := by omega
              have hx1 : x - 1 ≠ x := by omega
              have hyx : y ≠ x := by omega
              have hy1x : y + 1 ≠ x := by omega
              simp [inv_pair_coe, Multiset.count_add, hxr1, Ne.symm hx1,
                Ne.symm hyx, Ne.symm hy1x, hx1, hyx, hy1x] at hc
            have hy_r1 : y ∈ r1 := by
              have hx_le : x ≤ M := sortedDesc_head_ge_of_mem ha1.1 hx
              rcases List.mem_cons.mp hy with heq | h
              · omega
              · exact h
            have hmaj : Maj (hh (M :: r1)) (hh (M :: r2)) := by
              have hr1_sort : SortedDesc r1 := sortedDesc_tail ha1.1
              have hr2_sort : SortedDesc r2 := sortedDesc_tail ha2_gr.1
              have hpos1 := isGraphical_take_pos ha1
              have hM_len : M ≤ r1.length := hpos1.1
              have hx1_r2 : x - 1 ∈ r2 := by
                have hmem : x - 1 ∈ (r2 : Multiset ℕ) + {x, y} := by rw [hr2_perm]; simp
                rcases Multiset.mem_add.mp hmem with h1 | h2
                · exact h1
                · simp at h2; rcases h2 with h2 | h2 <;> omega
              obtain ⟨hqy_lt, hr1_qy, hrmid_sort, hrmid_perm1⟩ := bump1_spec hr1_sort hy_r1
              obtain ⟨hpx_lt, hr2_px, hrmid2_sort, hrmid_perm2⟩ := bump1_spec hr2_sort hx1_r2
              set r_mid := bump1 r1 y
              set qy_i := r1.countP (fun w => decide (y + 1 ≤ w))
              set px_i := r2.countP (fun w => decide (x - 1 + 1 ≤ w))
              have hpx_value : (bump1 r2 (x - 1))[px_i]'(by rw [bump1_length]; exact hpx_lt) = x := by
                have hvalue : (bump1 r2 (x - 1))[px_i]'(by rw [bump1_length]; exact hpx_lt) = x - 1 + 1 :=
                  bump1_getElem_self (by rw [bump1_length]; exact hpx_lt)
                exact hvalue.trans (Nat.sub_add_cancel (by omega))
              have hmid_eq : bump1 r2 (x - 1) = r_mid := by
                apply sortedDesc_ext_of_perm hrmid2_sort hrmid_sort
                have hp1 : x - 1 + 1 = x := Nat.sub_add_cancel (by omega)
                have hrmid_perm1' : (r_mid : Multiset ℕ) + {y} = (r1 : Multiset ℕ) + {y + 1} := hrmid_perm1
                have hrmid_perm2' : (bump1 r2 (x - 1) : Multiset ℕ) + {x - 1} = (r2 : Multiset ℕ) + {x} := by
                  rw [hrmid_perm2, hp1]
                have h1 : (bump1 r2 (x - 1) : Multiset ℕ) + ({x - 1} + {y}) =
                    (r_mid : Multiset ℕ) + ({x - 1} + {y}) := by
                  calc (bump1 r2 (x - 1) : Multiset ℕ) + ({x - 1} + {y})
                      = ((bump1 r2 (x - 1) : Multiset ℕ) + {x - 1}) + {y} := by ac_rfl
                    _ = ((r2 : Multiset ℕ) + {x}) + {y} := by rw [hrmid_perm2']
                    _ = (r2 : Multiset ℕ) + {x, y} := by rw [inv_pair_coe]; ac_rfl
                    _ = (r1 : Multiset ℕ) + {x - 1, y + 1} := hr2_perm
                    _ = ((r1 : Multiset ℕ) + {y + 1}) + {x - 1} := by rw [inv_pair_coe]; ac_rfl
                    _ = ((r_mid : Multiset ℕ) + {y}) + {x - 1} := by rw [← hrmid_perm1']
                    _ = (r_mid : Multiset ℕ) + ({x - 1} + {y}) := by ac_rfl
                exact add_right_cancel h1
              have hr2_len : r2.length = r1.length := by
                have hc := congrArg Multiset.card hr2_perm; simpa using hc
              have hM_len2 : M ≤ r2.length := by omega
              have hpx_lt_qy : px_i < qy_i := by
                by_contra hle
                have hqy_le : qy_i ≤ px_i := by omega
                have hlt1 : qy_i < r_mid.length := by rw [bump1_length]; exact hqy_lt
                have hlt2 : px_i < r_mid.length := by rw [← hmid_eq, bump1_length]; exact hpx_lt
                have hrm_qy : r_mid[qy_i]'hlt1 = y + 1 := by
                  exact bump1_getElem_self hlt1
                have hrm_px : r_mid[px_i]'hlt2 = x := by
                  have h1 : (bump1 r2 (x - 1))[px_i]'(by rw [bump1_length]; exact hpx_lt) = x - 1 + 1 :=
                    bump1_getElem_self (by rw [bump1_length]; exact hpx_lt)
                  have h2 : r_mid[px_i]'hlt2 = (bump1 r2 (x - 1))[px_i]'(by rw [bump1_length]; exact hpx_lt) := by
                    congr 1; exact hmid_eq.symm
                  omega
                have hge := sortedDesc_ge_of_le hrmid_sort hqy_le hlt2
                omega
              have hhh1 : (hh (M :: r1) : Multiset ℕ) = decTop M r1 := hh_coe_eq_decTop M r1
              have hhh2 : (hh (M :: r2) : Multiset ℕ) = decTop M r2 := hh_coe_eq_decTop M r2
              by_cases hM_px : M ≤ px_i
              · have hM_qy : M ≤ qy_i := by omega
                have hdec1 := decTop_bump1_ge hr1_sort hy_r1 hM_qy
                have hdec2 := decTop_bump1_ge hr2_sort hx1_r2 hM_px
                have hp1 : x - 1 + 1 = x := Nat.sub_add_cancel (by omega)
                have hdec2' : decTop M r_mid + {x - 1} = decTop M r2 + {x} := by
                  rw [← hmid_eq, hdec2, hp1]
                have hmult : (hh (M :: r2) : Multiset ℕ) + {x, y} =
                    (hh (M :: r1) : Multiset ℕ) + {x - 1, y + 1} := by
                  rw [hhh1, hhh2, inv_pair_coe, inv_pair_coe]
                  calc decTop M r2 + ({x} + {y})
                      = (decTop M r2 + {x}) + {y} := by ac_rfl
                    _ = (decTop M r_mid + {x - 1}) + {y} := by rw [← hdec2']
                    _ = (decTop M r_mid + {y}) + {x - 1} := by ac_rfl
                    _ = (decTop M r1 + {y + 1}) + {x - 1} := by rw [hdec1]
                    _ = decTop M r1 + ({x - 1} + {y + 1}) := by ac_rfl
                have hx_mem : x ∈ hh (M :: r1) := by
                  have hxm : x ∈ (r_mid.drop M : Multiset ℕ) := by
                    have hi : px_i - M < (r_mid.drop M).length := by
                      rw [List.length_drop, ← hmid_eq, bump1_length]; omega
                    have heq' : (r_mid.drop M)[px_i - M]'hi = x := by
                      rw [List.getElem_drop]
                      have h1 : (bump1 r2 (x - 1))[px_i]'(by rw [bump1_length]; exact hpx_lt) = x := hpx_value
                      have h2 : r_mid[M + (px_i - M)]'(by rw [← hmid_eq, bump1_length]; omega) =
                          (bump1 r2 (x - 1))[px_i]'(by rw [bump1_length]; exact hpx_lt) := by
                        congr 1; exact hmid_eq.symm; omega
                      rw [h2, h1]
                    rw [← heq']; exact List.getElem_mem hi
                  have h1 : x ∈ (r1.drop M : Multiset ℕ) + {y + 1} := by
                    have heq_drop : r_mid.drop M = (r1.drop M).set (qy_i - M) (y + 1) :=
                      drop_set_of_le r1 qy_i M (y + 1) hM_qy
                    have hm : (r_mid.drop M : Multiset ℕ) + {y} = (r1.drop M : Multiset ℕ) + {y + 1} := by
                      rw [heq_drop]
                      have hi : qy_i - M < (r1.drop M).length := by rw [List.length_drop]; omega
                      have heq' : (r1.drop M)[qy_i - M]'hi = y := by rw [List.getElem_drop]; convert hr1_qy; omega
                      have hset := multiset_set hi (y + 1)
                      rwa [heq'] at hset
                    rw [← hm]; exact Multiset.mem_add.mpr (Or.inl hxm)
                  rcases Multiset.mem_add.mp h1 with h | h
                  · change x ∈ (hh (M :: r1) : Multiset ℕ)
                    rw [hhh1, decTop, Multiset.mem_add]; exact Or.inr h
                  · simp at h; omega
                have hy_mem : y ∈ hh (M :: r1) := by
                  have h1 : y ∈ (r1.drop M : Multiset ℕ) := by
                    have hi : qy_i - M < (r1.drop M).length := by rw [List.length_drop]; omega
                    have heq' : (r1.drop M)[qy_i - M]'hi = y := by rw [List.getElem_drop]; convert hr1_qy; omega
                    rw [← heq']; exact List.getElem_mem hi
                  change y ∈ (hh (M :: r1) : Multiset ℕ)
                  rw [hhh1, decTop, Multiset.mem_add]; exact Or.inr h1
                exact maj_of_elementaryTransfer hgr1.1 hgr2.1 hxy hx_mem hy_mem hmult
              · have hpx_lt_M : px_i < M := by omega
                have h1x1 : 1 ≤ x - 1 := by omega
                have hdec2 := decTop_bump1_lt hr2_sort hx1_r2 h1x1 hpx_lt_M
                have hp1 : x - 1 + 1 = x := Nat.sub_add_cancel (by omega)
                have hdec2' : decTop M r_mid + {x - 2} = decTop M r2 + {x - 1} := by
                  rw [← hmid_eq, show x - 2 = x - 1 - 1 by omega]; exact hdec2
                by_cases hM_qy : M ≤ qy_i
                · have hdec1 := decTop_bump1_ge hr1_sort hy_r1 hM_qy
                  have hmult : (hh (M :: r2) : Multiset ℕ) + {x - 1, y} =
                      (hh (M :: r1) : Multiset ℕ) + {x - 2, y + 1} := by
                    rw [hhh1, hhh2, inv_pair_coe, inv_pair_coe]
                    calc decTop M r2 + ({x - 1} + {y})
                        = (decTop M r2 + {x - 1}) + {y} := by ac_rfl
                      _ = (decTop M r_mid + {x - 2}) + {y} := by rw [← hdec2']
                      _ = (decTop M r_mid + {y}) + {x - 2} := by ac_rfl
                      _ = (decTop M r1 + {y + 1}) + {x - 2} := by rw [hdec1]
                      _ = decTop M r1 + ({x - 2} + {y + 1}) := by ac_rfl
                  by_cases hx1y : x - 1 = y + 1
                  · have hcoe : (hh (M :: r1) : Multiset ℕ) = (hh (M :: r2) : Multiset ℕ) := by
                      rw [hx1y] at hmult
                      have hsub : y + 1 - 1 = y := by omega
                      have hm' : ({y + 1, y} : Multiset ℕ) = {y, y + 1} := by rw [inv_pair_coe, inv_pair_coe]; ac_rfl
                      have hx2y : x - 2 = y := by omega
                      rw [hx2y, hm'] at hmult
                      exact (add_right_cancel hmult).symm
                    rw [sortedDesc_ext_of_perm hgr1.1 hgr2.1 hcoe]
                    exact maj_refl hgr2.1
                  · have hgap : x - 1 ≥ y + 2 := by omega
                    have hx1_mem : x - 1 ∈ hh (M :: r1) := by
                      have htake_eq : r_mid.take M = r1.take M := take_set_of_le r1 qy_i M (y + 1) hM_qy
                      have hxm : x ∈ r1.take M := by
                        rw [← htake_eq]
                        have hi : px_i < (r_mid.take M).length := by
                          rw [List.length_take, Nat.min_eq_left (by rw [← hmid_eq, bump1_length]; exact hM_len2)]; exact hpx_lt_M
                        have heq' : (r_mid.take M)[px_i]'hi = x := by
                          rw [List.getElem_take]
                          have h1 : (bump1 r2 (x - 1))[px_i]'(by rw [bump1_length]; exact hpx_lt) = x := hpx_value
                          have h2 : r_mid[px_i]'(by rw [← hmid_eq, bump1_length]; exact hpx_lt) =
                              (bump1 r2 (x - 1))[px_i]'(by rw [bump1_length]; exact hpx_lt) := by
                            congr 1; exact hmid_eq.symm
                          rw [h2, h1]
                        rw [← heq']; exact List.getElem_mem hi
                      change x - 1 ∈ (hh (M :: r1) : Multiset ℕ)
                      rw [hhh1, decTop, Multiset.mem_add]
                      left; rw [Multiset.mem_map]; exact ⟨x, hxm, rfl⟩
                    have hy_mem : y ∈ hh (M :: r1) := by
                      have h1 : y ∈ (r1.drop M : Multiset ℕ) := by
                        have hi : qy_i - M < (r1.drop M).length := by rw [List.length_drop]; omega
                        have heq' : (r1.drop M)[qy_i - M]'hi = y := by rw [List.getElem_drop]; convert hr1_qy; omega
                        rw [← heq']; exact List.getElem_mem hi
                      change y ∈ (hh (M :: r1) : Multiset ℕ)
                      rw [hhh1, decTop, Multiset.mem_add]; exact Or.inr h1
                    exact maj_of_elementaryTransfer hgr1.1 hgr2.1 hgap hx1_mem hy_mem hmult
                · have hqy_lt_M : qy_i < M := by omega
                  have h1y : 1 ≤ y := by
                    apply hpos1.2
                    rw [← hr1_qy]
                    have hi : qy_i < (r1.take M).length := by rw [List.length_take, Nat.min_eq_left hM_len]; exact hqy_lt_M
                    have htake_el : (r1.take M)[qy_i]'hi = r1[qy_i]'hqy_lt := List.getElem_take
                    rw [← htake_el]
                    exact List.getElem_mem hi
                  have hdec1 := decTop_bump1_lt hr1_sort hy_r1 h1y hqy_lt_M
                  have hmult : (hh (M :: r2) : Multiset ℕ) + {x - 1, y - 1} =
                      (hh (M :: r1) : Multiset ℕ) + {x - 2, y} := by
                    rw [hhh1, hhh2, inv_pair_coe, inv_pair_coe]
                    calc decTop M r2 + ({x - 1} + {y - 1})
                        = (decTop M r2 + {x - 1}) + {y - 1} := by ac_rfl
                      _ = (decTop M r_mid + {x - 2}) + {y - 1} := by rw [← hdec2']
                      _ = (decTop M r_mid + {y - 1}) + {x - 2} := by ac_rfl
                      _ = (decTop M r1 + {y}) + {x - 2} := by rw [hdec1]
                      _ = decTop M r1 + ({x - 2} + {y}) := by ac_rfl
                  have hgap : x - 1 ≥ (y - 1) + 2 := by omega
                  have hr1_px : r1[px_i]'(by omega) = x := by
                    have hrm_px : r_mid[px_i]'(by rw [bump1_length]; omega) = x := by
                      have h1 : (bump1 r2 (x - 1))[px_i]'(by rw [bump1_length]; exact hpx_lt) = x := hpx_value
                      have h2 : r_mid[px_i]'(by rw [bump1_length]; omega) =
                          (bump1 r2 (x - 1))[px_i]'(by rw [bump1_length]; exact hpx_lt) := by
                        congr 1; exact hmid_eq.symm
                      rw [h2, h1]
                    have hset : px_i < (r1.set qy_i (y + 1)).length := by
                      rw [List.length_set]
                      omega
                    have hentry := List.getElem_set_ne (i := qy_i) (a := y + 1)
                      (ne_of_gt hpx_lt_qy) hset
                    exact hentry.symm.trans hrm_px
                  have hpair : ({x - 1, y - 1} : Multiset ℕ) ≤ (hh (M :: r1) : Multiset ℕ) := by
                    rw [hhh1, decTop]
                    have hp := pair_le_of_distinct_take (r := r1) (i := px_i) (j := qy_i) (M := M)
                      hpx_lt_M hqy_lt_M hM_len (by omega)
                    have h1 : r1[px_i]'(by omega) = x := hr1_px
                    have h2 : r1[qy_i]'(by omega) = y := hr1_qy
                    have hmap := Multiset.map_le_map (f := (· - 1)) hp
                    simp only [Multiset.map_coe, inv_pair_coe, Multiset.map_add, Multiset.map_singleton] at hmap
                    rw [h1, h2, ← Multiset.map_coe] at hmap
                    rw [inv_pair_coe]
                    exact hmap.trans le_self_add
                  have ⟨hx1_mem, hy1_mem⟩ := mem_of_pair_le hpair
                  have hmult' : (hh (M :: r2) : Multiset ℕ) + {x - 1, y - 1} =
                      (hh (M :: r1) : Multiset ℕ) + {x - 1 - 1, y - 1 + 1} := by
                    have hsub1 : x - 1 - 1 = x - 2 := by omega
                    have hsub2 : y - 1 + 1 = y := by omega
                    rw [hsub1, hsub2]; exact hmult
                  exact maj_of_elementaryTransfer hgr1.1 hgr2.1 hgap hx1_mem hy1_mem hmult'
            have hlen_hh : (hh (M :: r1)).length < n := by
              rw [length_hh, ← ha1_len]; simp
            have h1 := ih (hh (M :: r1)).length hlen_hh hgr1 hgr2 hmaj t' rfl
            have h2 := hPa2' (t' + 1)
            simp only [hhIter, Function.iterate_succ_apply] at h1 h2 ⊢
            exact h1.trans h2

end Triesch

open scoped Classical

private def excess (t : ℕ) (l : List ℕ) : ℕ := (l.map (· - t)).sum

private lemma take_sum_le_add_excess (l : List ℕ) (t k : ℕ) :
    (l.take k).sum ≤ k * t + excess t l := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih =>
    cases k with
    | zero => simp
    | succ k =>
      have h := ih k
      simp only [List.take_succ_cons, List.sum_cons, excess, List.map_cons, Nat.succ_mul] at *
      omega

private lemma excess_add_take_mul (l : List ℕ) (t k : ℕ)
    (h₁ : ∀ a ∈ l.take k, t ≤ a) (h₂ : ∀ a ∈ l.drop k, a ≤ t) :
    excess t l + (l.take k).length * t = (l.take k).sum := by
  induction l generalizing k with
  | nil => simp [excess]
  | cons a l ih =>
    cases k with
    | zero =>
      have ha := h₂ a (by simp)
      have h := ih 0 (by simp) (fun b hb => h₂ b (by simpa using Or.inr hb : b ∈ a :: l))
      simp [excess, Nat.sub_eq_zero_of_le ha] at h ⊢
      exact h
    | succ k =>
      have ha : t ≤ a := h₁ a (by simp)
      have h := ih k (fun b hb => h₁ b (by simpa using Or.inr hb : b ∈ a :: l.take k)) h₂
      simp only [List.take_succ_cons, List.length_cons, List.sum_cons, excess, List.map_cons,
        Nat.succ_mul] at h ⊢
      omega

private lemma degree_induce_ne {V : Type} [Fintype V] (G : SimpleGraph V) (v : V)
    (a : {a : V // a ≠ v}) :
    (G.induce {a | a ≠ v}).degree a = G.degree a.1 - (if G.Adj v a.1 then 1 else 0) := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  have heq :
      ((G.induce {a | a ≠ v}).neighborFinset a).map (Function.Embedding.subtype _) =
        (G.neighborFinset a.1).erase v := by
    ext b
    simp only [mem_map, mem_neighborFinset, Function.Embedding.subtype_apply, mem_erase,
      Subtype.exists, SimpleGraph.induce_adj, Set.mem_setOf_eq]
    constructor
    · rintro ⟨c, hc, hca, rfl⟩; exact ⟨hc, hca⟩
    · rintro ⟨hbv, hba⟩; exact ⟨b, hbv, hba, rfl⟩
  rw [← Finset.card_map (Function.Embedding.subtype _), heq]
  by_cases hadj : G.Adj v a.1
  · rw [if_pos hadj, card_erase_of_mem (by rw [mem_neighborFinset]; exact hadj.symm)]
  · rw [if_neg hadj, Nat.sub_zero, erase_eq_of_notMem (by simpa [mem_neighborFinset, adj_comm] using hadj)]

private lemma indepNum_induce_ne {V : Type} [Fintype V] (G : SimpleGraph V) (v : V) :
    (G.induce {a | a ≠ v}).indepNum ≤ G.indepNum := by
  obtain ⟨s, hs⟩ := (G.induce {a | a ≠ v}).exists_isNIndepSet_indepNum
  have h : G.IsIndepSet ((s.map (Function.Embedding.subtype _)) : Set V) := by
    intro x hx y hy hxy hadj
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hx)
    obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hy)
    exact hs.1 (by assumption) (by assumption) (fun hab => hxy (congrArg Subtype.val hab)) hadj
  simpa [hs.2] using h.card_le_indepNum


private lemma excess_map_decrement {α : Type*} (l : List α) (deg : α → ℕ) (sel : α → Bool) (t : ℕ) :
    excess t (l.map (fun a => deg a - if sel a then 1 else 0)) +
      l.countP (fun a => sel a && decide (t < deg a)) = excess t (l.map deg) := by
  induction l with
  | nil => simp [excess]
  | cons a l ih =>
    cases h : sel a <;> by_cases ht : t < deg a <;>
      simp [excess, h, ht, List.countP_cons] at ih ⊢ <;> omega

private lemma excess_append (t : ℕ) (l r : List ℕ) :
    excess t (l ++ r) = excess t l + excess t r := by
  simp [excess]

private lemma excess_perm {t : ℕ} {l r : List ℕ} (h : l.Perm r) :
    excess t l = excess t r :=
  (h.map _).sum_eq

private lemma excess_hh (d t : ℕ) (r : List ℕ) :
    excess t (havelHakimiStep (d :: r)) + (r.take d).countP (fun a => decide (t < a)) =
      excess t r := by
  have hs := excess_map_decrement (r.take d) id (fun _ => true) t
  simp only [id_eq, ite_true, Bool.true_and, List.map_id_fun', List.map_id] at hs
  have hperm : (havelHakimiStep (d :: r)).Perm ((r.take d).map (· - 1) ++ r.drop d) := by
    simp only [havelHakimiStep, List.splitAt_eq]
    exact List.mergeSort_perm _ _
  rw [excess_perm hperm, excess_append, Nat.add_right_comm, hs, ← excess_append, List.take_append_drop]

private lemma countP_take_of_sorted (l : List ℕ) (p : ℕ → Bool) (d : ℕ)
    (h : l.Pairwise (fun x y => p y = true → p x = true)) :
    (l.take d).countP p = min d (l.countP p) := by
  induction l generalizing d with
  | nil => simp
  | cons a l ih =>
    cases d with
    | zero => simp
    | succ d =>
      obtain ⟨ha, hl⟩ := List.pairwise_cons.mp h
      cases hpa : p a with
      | true => simp [List.countP_cons, hpa, ih d hl, Nat.succ_min_succ, Nat.succ_eq_add_one, Nat.add_comm]
      | false =>
        have hall : ∀ x ∈ l, p x = false := by
          intro x hx
          cases hp : p x
          · rfl
          · exact Bool.noConfusion (hpa.symm.trans (ha x hx hp))
        have hzero : l.countP p = 0 := List.countP_eq_zero.mpr (fun x hx => by simp [hall x hx])
        simp [List.countP_cons, hpa, ih d hl, hzero]


section Completion

open scoped Classical

private lemma maj_of_excess {a b : List ℕ} (ha : SortedDesc a) (hb : SortedDesc b)
    (hlen : a.length = b.length) (hsum : a.sum = b.sum)
    (h : ∀ t, excess t b ≤ excess t a) : Maj a b := by
  refine ⟨ha, hb, hlen, hsum, fun k => ?_⟩
  by_cases hk : a.length ≤ k
  · rw [List.take_of_length_le hk, List.take_of_length_le (hlen ▸ hk), hsum]
  cases k with
  | zero => simp
  | succ k =>
    have hka : k < a.length := by omega
    let t := a[k]
    have hpre : ∀ x ∈ a.take (k + 1), t ≤ x := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
      rw [List.getElem_take]
      have hi' := hi
      rw [List.length_take] at hi'
      exact sortedDesc_ge_of_le ha (by omega) hka
    have hpost : ∀ x ∈ a.drop (k + 1), x ≤ t := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
      rw [List.getElem_drop]
      have hi' := hi
      rw [List.length_drop] at hi'
      exact sortedDesc_ge_of_le ha (by omega) (by omega)
    have hEq := excess_add_take_mul a t (k + 1) hpre hpost
    rw [List.length_take, Nat.min_eq_left (by omega)] at hEq
    have hb' := take_sum_le_add_excess b t (k + 1)
    have hh := h t
    omega

private noncomputable def descDegrees {V : Type} [Fintype V] (G : SimpleGraph V) : List ℕ :=
  (Finset.univ.val.map (fun a => G.degree a)).sort (· ≥ ·)

private lemma degree_fintype_irrel {V : Type} (G : SimpleGraph V) (v : V)
    {f₁ f₂ : Fintype (G.neighborSet v)} :
    @SimpleGraph.degree V G v f₁ = @SimpleGraph.degree V G v f₂ := by
  rw [Subsingleton.elim f₁ f₂]

private lemma isGraphical_descDegrees {V : Type} [Fintype V] (G : SimpleGraph V) :
    IsGraphical (descDegrees G) := by
  let e := Fintype.equivFin V
  let H := G.map e.toEmbedding
  refine ⟨sortedDesc_sort _, Fintype.card V, H, ?_⟩
  have hmap : (Finset.univ : Finset (Fin (Fintype.card V))).val =
      (Finset.univ : Finset V).val.map e := by
    simpa using (congrArg Finset.val (Finset.map_univ_equiv e)).symm
  unfold descDegrees
  rw [Multiset.sort_eq, hmap, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro a _
  simp only [Function.comp_apply]
  have h := ((SimpleGraph.Iso.map e G).degree_eq a).symm
  exact h.trans (degree_fintype_irrel H (e a))

private lemma descDegrees_cons_delete {V : Type} [Fintype V] (G : SimpleGraph V)
    (v : V) (d : ℕ) (r : List ℕ) (hv : G.degree v = d)
    (hseq : descDegrees G = d :: r) (hd : d ≤ r.length) :
    Maj (descDegrees (G.induce {a | a ≠ v})) (hh (d :: r)) := by
  let W := {a : V // a ≠ v}
  let H : SimpleGraph W := G.induce {a | a ≠ v}
  let sel : V → Bool := fun a => decide (G.Adj v a)
  let leV : V → V → Bool := fun a b => decide (G.degree b ≤ G.degree a)
  let vs := (Finset.univ.erase v).toList.mergeSort leV
  have hvs_perm : vs.Perm (Finset.univ.erase v).toList := List.mergeSort_perm _ _
  have hvs_coe : (vs : Multiset V) = (Finset.univ.erase v).val := by
    rw [Multiset.coe_eq_coe.mpr hvs_perm, Finset.coe_toList]
  have hvs_pair : vs.Pairwise (fun a b => leV a b = true) := by
    apply List.pairwise_mergeSort
    · intro a b c hab hbc
      simp only [leV, decide_eq_true_eq] at *
      exact hbc.trans hab
    · intro a b
      simp only [leV, Bool.or_eq_true, decide_eq_true_eq]
      exact le_total _ _
  have hseq_sorted : SortedDesc (d :: r) := by
    rw [← hseq]
    exact sortedDesc_sort _
  have hr_eq : vs.map (fun a => G.degree a) = r := by
    apply sortedDesc_eq_of_coe
    · exact List.Pairwise.map _ (fun {_ _} hab => by simpa [leV] using hab) hvs_pair
    · exact sortedDesc_tail hseq_sorted
    · have hc := congrArg (fun l : List ℕ => (l : Multiset ℕ)) hseq
      simp only [descDegrees, Multiset.sort_eq, ← Multiset.cons_coe] at hc
      rw [← Multiset.map_coe, hvs_coe]
      apply (Multiset.cons_inj_right d).mp
      rw [← hv, ← Multiset.map_cons (fun a => G.degree a) v (Finset.univ.erase v).val,
        ← insert_val_of_notMem (notMem_erase v _), insert_erase (mem_univ v), hc, hv]
  have hsub : (Finset.univ : Finset W).val.map Subtype.val = (Finset.univ.erase v).val := by
    refine (Multiset.Nodup.ext ?_ ?_).mpr ?_
    · exact Multiset.Nodup.map Subtype.val_injective (Finset.univ : Finset W).nodup
    · exact (Finset.univ.erase v).nodup
    intro a
    simp only [Multiset.mem_map, mem_val, mem_univ, true_and, Subtype.exists, mem_erase, and_true]
    constructor
    · rintro ⟨b, hb, rfl⟩; exact hb
    · intro h; exact ⟨a, h, rfl⟩
  have hraw : (descDegrees H : Multiset ℕ) = (vs.map (fun a => G.degree a - if sel a then 1 else 0) : Multiset ℕ) := by
    rw [descDegrees, Multiset.sort_eq, ← Multiset.map_coe, hvs_coe, ← hsub, Multiset.map_map]
    apply Multiset.map_congr rfl
    intro a _
    simp only [Function.comp_apply, sel, decide_eq_true_eq]
    exact (degree_fintype_irrel H a).trans (degree_induce_ne G v a)
  have hcnt : vs.countP sel = d := by
    have hset : (vs : Multiset V).filter (fun a => G.Adj v a) = (G.neighborFinset v).val := by
      rw [hvs_coe]
      refine (Multiset.Nodup.ext ?_ (G.neighborFinset v).nodup).mpr ?_
      · exact Multiset.Nodup.filter _ (Finset.univ.erase v).nodup
      intro a
      simp only [Multiset.mem_filter, mem_val, mem_erase, mem_univ, and_true, mem_neighborFinset]
      exact ⟨And.right, fun h => ⟨h.ne.symm, h⟩⟩
    have hc : (vs.filter sel).length = ((vs : Multiset V).filter (fun a => G.Adj v a)).card := by
      simp [sel, Multiset.filter_coe]
    rw [List.countP_eq_length_filter, hc, hset, card_val, card_neighborFinset_eq_degree, hv]
  have hperm := Multiset.coe_eq_coe.mp hraw
  have hex (t : ℕ) := excess_map_decrement vs (fun a => G.degree a) sel t
  have hex' (t : ℕ) : excess t (descDegrees H) + vs.countP (fun a => sel a && decide (t < G.degree a)) =
      excess t r := by
    rw [excess_perm hperm, ← hr_eq]
    exact hex t
  have hgr (t : ℕ) : excess t (hh (d :: r)) + min d (r.countP (fun a => decide (t < a))) =
      excess t r := by
    have hsort : SortedDesc r := sortedDesc_tail hseq_sorted
    have hp : r.Pairwise (fun x y => decide (t < y) = true → decide (t < x) = true) :=
      hsort.imp (fun {_ _} hxy hy =>
        decide_eq_true_eq.mpr ((decide_eq_true_eq.mp hy).trans_le hxy))
    rw [← countP_take_of_sorted r _ d hp]
    exact excess_hh d t r
  have hlen : (descDegrees H).length = (hh (d :: r)).length := by
    have hlen_r : vs.length = r.length := by rw [← hr_eq, List.length_map]
    simpa [length_hh, hlen_r] using hperm.length_eq
  have hsum : (descDegrees H).sum = (hh (d :: r)).sum := by
    have hpos : ∀ a ∈ vs, (sel a && decide (0 < G.degree a)) = sel a := by
      intro a _
      by_cases ha : G.Adj v a
      · have hp : 0 < G.degree a := by
          rw [← card_neighborFinset_eq_degree]
          exact Finset.card_pos.mpr ⟨v, by rw [mem_neighborFinset]; exact ha.symm⟩
        simp [sel, ha, hp]
      · simp [sel, ha]
    have hcong : vs.countP (fun a => sel a && decide (0 < G.degree a)) = vs.countP sel :=
      List.countP_congr (fun a ha => by rw [hpos a ha])
    have htake : ∀ x ∈ r.take d, 1 ≤ x := (isGraphical_take_pos (hseq ▸ isGraphical_descDegrees G)).2
    have hs := hh_sum_cons hd htake
    have h0 := hex' 0
    rw [hcong, hcnt] at h0
    simp [excess] at h0
    simp only [List.sum_cons] at hs
    omega
  refine maj_of_excess (sortedDesc_sort _) (sortedDesc_hh hseq_sorted) hlen hsum (fun t => ?_)
  have hsel := countP_mono (fun a => sel a && decide (t < G.degree a)) sel (fun _ ha => (Bool.and_eq_true_iff.mp ha).1) vs
  have hdeg := countP_mono (fun a => sel a && decide (t < G.degree a)) (fun a => decide (t < G.degree a)) (fun _ ha => (Bool.and_eq_true_iff.mp ha).2) vs
  rw [hcnt] at hsel
  have hdeg' : vs.countP (fun a => decide (t < G.degree a)) =
      r.countP (fun a => decide (t < a)) := by simp [← hr_eq, Function.comp_def]
  rw [hdeg'] at hdeg
  have hmin := le_min hsel hdeg
  have h1 := hgr t
  have h2 := hex' t
  have hle : excess t (hh (d :: r)) ≤ excess t (descDegrees H) := by omega
  exact hle

private lemma residueAux_descDegrees_le_indepNum :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      residueAux (descDegrees G) ≤ G.indepNum := by
  intro V inst G
  induction hn : Fintype.card V using Nat.strong_induction_on generalizing V with
  | _ n ih =>
    cases hs : descDegrees G with
    | nil => simp [residueAux]
    | cons d r =>
      have hsort : SortedDesc (d :: r) := hs ▸ sortedDesc_sort _
      have hG := hs ▸ isGraphical_descDegrees G
      have hdegrees : ((d :: r : List ℕ) : Multiset ℕ) = Finset.univ.val.map (fun a => G.degree a) := by
        rw [← hs, descDegrees, Multiset.sort_eq]
      have hdmem : d ∈ Finset.univ.val.map (fun a => G.degree a) := by rw [← hdegrees]; simp
      obtain ⟨v, _, hv⟩ := Multiset.mem_map.mp hdmem
      cases d with
      | zero =>
        have hz (a : V) : G.degree a = 0 := by
          have hm : G.degree a ∈ (0 :: r : List ℕ) := by
            change G.degree a ∈ (↑(0 :: r) : Multiset ℕ)
            rw [hdegrees]
            exact Multiset.mem_map.mpr ⟨a, by simp, rfl⟩
          exact Nat.eq_zero_of_le_zero (sortedDesc_head_ge_of_mem hsort hm)
        have hI : G.IsIndepSet (Finset.univ : Finset V) := by
          intro a _ b _ _ hab
          exact (SimpleGraph.IsIsolated.of_degree_eq_zero G a (hz a)) b hab
        have hc := congrArg Multiset.card hdegrees
        have hi := hI.card_le_indepNum
        have hcard : r.length + 1 = Fintype.card V := by simpa using hc
        simpa [residueAux, Nat.add_comm] using hcard.le.trans hi
      | succ d =>
        let W := {a : V // a ≠ v}
        let H : SimpleGraph W := G.induce {a | a ≠ v}
        have hcardW : Fintype.card W < n := by
          rw [← hn, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
          have hp : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
          omega
        have hhh := (isGraphical_hh hG).1
        have hH := isGraphical_descDegrees H
        have hmaj := descDegrees_cons_delete G v (d + 1) r hv hs (isGraphical_head_le_len hG)
        have hres := residueAux_le_of_hhIter_sum_le hhh.1 hH.1 hmaj.2.2.1.symm
          (triesch_sum_le hH hhh hmaj)
        rw [residueAux_succ_cons]
        exact hres.trans ((ih _ hcardW W H rfl).trans (indepNum_induce_ne G v))

end Completion
end OMA.ResidueBound

theorem OMA.solution : OMA.R_Arxiv_2507_17780_tx_graffiti_conjecture_1_R1.H1 := by
  intro V _ G hAdj
  have h : hAdj = (fun a b => Classical.propDecidable (G.Adj a b)) := Subsingleton.elim _ _
  cases h
  exact OMA.ResidueBound.residueAux_descDegrees_le_indepNum V G
