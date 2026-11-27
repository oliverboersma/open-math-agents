import OMAReductions.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H3_R1

/-!
# Proof of `tree.R1.H3.R1.H4`

Tree reconstruction for even-diameter (`2 * r`, `r >= 2`) non-path hypomorphic trees having no leaf
adjacent to the center and at least one center component of cardinality strictly greater than `r`
(Kelly 1957 center-branch case).
-/

-- Credit: @green-notes

open SimpleGraph

section TreeR1H3R1H4

open Classical
open Finset (coe_insert coe_union mem_filter mem_univ mem_erase mem_map mem_insert mem_union mem_coe univ card_map card_insert_of_notMem card_pos mem_singleton card_le_card mem_insert_of_mem mem_insert_self mem_union_left card_bij mem_union_right card_pair add_sum_erase mem_sigma mem_product sum_congr card_le_univ card_erase_of_mem card_singleton mem_attach card_sigma card_univ eq_of_subset_of_card_le single_le_sum mem_sdiff card_sdiff_of_subset card_attach card_product union_assoc sum_bij mem_image)
open SimpleGraph.ConnectedComponent (mem_supp_iff sound)
open SimpleGraph.Walk (length_map length_append not_nil_of_ne isPath_copy length_copy support_tail_of_not_nil cons_isPath_iff getVert_eq_support_getElem length_cons getVert_mem_support support_copy length_reverse length_tail isPath_def)
open Subtype (val_injective coe_eta)
open Fintype (card card_coe card_congr card_fin card_sum card_option)
open Set (mem_insert_iff mem_compl_singleton_iff)
open Function (LeftInverse RightInverse Injective)

/-! ### Part 1: Basic tree, distance, center, and component helpers -/

private def pathG (n : ℕ) : SimpleGraph (Fin n) where
  Adj i j := i.val + 1 = j.val ∨ j.val + 1 = i.val
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by omega⟩

private lemma isTree_dist_eq_length_of_isPath {U : Type} (T : SimpleGraph U) (hT : T.IsTree)
    {x y : U} (p : T.Walk x y) (hp : p.IsPath) :
    p.length = T.dist x y := by
  obtain ⟨q, hq, hqlen⟩ := hT.connected.exists_path_of_dist x y
  have hsub : (⟨p, hp⟩ : T.Path x y) = ⟨q, hq⟩ := (hT.isAcyclic.subsingleton_path x y).elim _ _
  have hpq : p = q := congrArg Subtype.val hsub
  rw [hpq, hqlen]
private lemma isTree_path_eq {U : Type} (T : SimpleGraph U) (hT : T.IsTree)
    {x y : U} {p q : T.Walk x y} (hp : p.IsPath) (hq : q.IsPath) :
    p = q :=
  congrArg Subtype.val ((hT.isAcyclic.subsingleton_path x y).elim ⟨p, hp⟩ ⟨q, hq⟩)
private lemma ncard_neighborSet_eq_degree {U : Type} [Fintype U] (T : SimpleGraph U) (u : U) :
    (T.neighborSet u).ncard = T.degree u := by
  rw [← T.card_neighborSet_eq_degree, Set.ncard_eq_toFinset_card' (T.neighborSet u)]
  simp [Set.toFinset_card]
private lemma split_walk_first_mem {U : Type} (T : SimpleGraph U) (P : Set U)
    [DecidablePred (· ∈ P)] {y c : U} (q : T.Walk y c) (hc : c ∈ P) :
    ∃ (z : U) (q₁ : T.Walk y z) (q₂ : T.Walk z c),
      z ∈ P ∧ q = q₁.append q₂ ∧ (∀ u ∈ q₁.support, u ∈ P → u = z) := by
  induction q with
  | nil =>
    exact ⟨_, Walk.nil, Walk.nil, hc, rfl, fun u hu _ => by
      simp only [Walk.support_nil, List.mem_singleton] at hu; exact hu⟩
  | @cons a b c h q' ih =>
    by_cases ha : a ∈ P
    · exact ⟨a, Walk.nil, Walk.cons h q', ha, rfl, fun u hu _ => by
        simp only [Walk.support_nil, List.mem_singleton] at hu; exact hu⟩
    · obtain ⟨z, q₁, q₂, hz, hq', huniq⟩ := ih hc
      refine ⟨z, Walk.cons h q₁, q₂, hz, by rw [hq']; rfl, fun u hu huP => ?_⟩
      simp only [Walk.support_cons, List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact False.elim (ha huP)
      · exact huniq u hu huP
private lemma start_notMem_tail_support_of_isPath {U : Type} {T : SimpleGraph U} {a b : U}
    {w : T.Walk a b} (hw : w.IsPath) : a ∉ w.support.tail := by
  cases w <;> simp_all [isPath_def]
private lemma isPath_append_of_first_meet {U : Type} {T : SimpleGraph U}
    {y z x : U} {q₁ : T.Walk y z} {s : T.Walk z x}
    (hq₁ : q₁.IsPath) (hs : s.IsPath)
    (hmeet : ∀ u ∈ q₁.support, u ∈ s.support.tail → u = z) :
    (q₁.append s).IsPath := by
  rw [isPath_def, Walk.support_append, List.nodup_append']
  refine ⟨hq₁.support_nodup, hs.support_nodup.tail, fun u huq hus => ?_⟩
  have huz : u = z := hmeet u huq hus
  subst huz
  exact start_notMem_tail_support_of_isPath hs hus
private lemma mem_support_tail_of_ne {U : Type} {T : SimpleGraph U}
    {a b x : U} (w : T.Walk a b) (hx : x ∈ w.support) (hne : x ≠ a) : x ∈ w.support.tail := by
  cases w with
  | nil =>
    simp only [Walk.support_nil, List.mem_singleton] at hx
    exact absurd hx hne
  | cons _ _ =>
    simpa [Walk.support_cons] using Or.resolve_left (List.mem_cons.mp hx) hne
private lemma length_walk_induce {U : Type*} (T : SimpleGraph U) (S : Set U) {a b : U}
    (p : T.Walk a b) (hp : ∀ x ∈ p.support, x ∈ S) :
    (p.induce S hp).length = p.length := by
  have h := congrArg Walk.length (Walk.map_induce p hp)
  rwa [length_map] at h
private lemma dist_induce_eq_of_isTree {U : Type} (T : SimpleGraph U) (hT : T.IsTree)
    (S : Set U) (hS : (T.induce S).IsTree) (a b : S) :
    (T.induce S).dist a b = T.dist a.1 b.1 := by
  obtain ⟨p, hp, hplen⟩ := hS.connected.exists_path_of_dist a b
  let g : T.induce S →g T := (Embedding.induce S).toHom
  have hdist := isTree_dist_eq_length_of_isPath T hT (p.map g) (hp.map val_injective)
  rw [length_map, hplen] at hdist
  exact hdist
private lemma iso_edist_eq {A B : Type*} (GA : SimpleGraph A) (GB : SimpleGraph B)
    (φ : GA ≃g GB) (a₁ a₂ : A) : GB.edist (φ a₁) (φ a₂) = GA.edist a₁ a₂ := by
  apply le_antisymm
  · dsimp only [SimpleGraph.edist]
    rw [le_iInf_iff]
    intro w
    exact (SimpleGraph.edist_le (w.map φ.toHom)).trans (by simp)
  · dsimp only [SimpleGraph.edist]
    rw [le_iInf_iff]
    intro w
    exact (SimpleGraph.edist_le ((w.map φ.symm.toHom).copy (φ.symm_apply_apply a₁)
      (φ.symm_apply_apply a₂))).trans (by rw [Nat.cast_le, length_copy, length_map])
private lemma iso_dist_eq {A B : Type*} (GA : SimpleGraph A) (GB : SimpleGraph B)
    (φ : GA ≃g GB) (a₁ a₂ : A) : GB.dist (φ a₁) (φ a₂) = GA.dist a₁ a₂ := by
  by_cases h : GA.Reachable a₁ a₂
  · have h' : GB.Reachable (φ a₁) (φ a₂) := h.map φ.toHom
    have he := iso_edist_eq GA GB φ a₁ a₂
    rw [← h.coe_dist_eq_edist, ← h'.coe_dist_eq_edist] at he
    exact Nat.cast_injective he
  · have h' : ¬ GB.Reachable (φ a₁) (φ a₂) := fun hr => h (by
      simpa using hr.map φ.symm.toHom)
    rw [dist_eq_zero_of_not_reachable h, dist_eq_zero_of_not_reachable h']
private lemma iso_eccent_eq {A B : Type*} (GA : SimpleGraph A) (GB : SimpleGraph B)
    (φ : GA ≃g GB) (a : A) : GB.eccent (φ a) = GA.eccent a := by
  simp only [SimpleGraph.eccent_def]
  apply le_antisymm
  · rw [iSup_le_iff]
    intro b
    rw [← φ.apply_symm_apply b, iso_edist_eq GA GB φ a (φ.symm b)]
    exact le_iSup (GA.edist a) (φ.symm b)
  · rw [iSup_le_iff]
    intro a'
    rw [← iso_edist_eq GA GB φ a a']
    exact le_iSup (GB.edist (φ a)) (φ a')
private lemma iso_diam_eq {A B : Type*} (GA : SimpleGraph A) (GB : SimpleGraph B)
    (φ : GA ≃g GB) : GA.diam = GB.diam := by
  simp only [SimpleGraph.diam, SimpleGraph.ediam]
  congr 1
  apply le_antisymm
  · rw [iSup_le_iff]
    intro a
    rw [← iso_eccent_eq GA GB φ a]
    exact le_iSup GB.eccent (φ a)
  · rw [iSup_le_iff]
    intro b
    rw [← φ.apply_symm_apply b, iso_eccent_eq GA GB φ (φ.symm b)]
    exact le_iSup GA.eccent (φ.symm b)
private lemma dist_le_of_eccent {U : Type} (T : SimpleGraph U) (hT : T.IsTree)
    {c u : U} {r : ℕ} (hecc : T.eccent c = r) : T.dist c u ≤ r := by
  have h1 : (T.dist c u : ℕ∞) ≤ r := by
    rw [(hT.connected c u).coe_dist_eq_edist, ← hecc]
    exact edist_le_eccent
  exact Nat.cast_le.mp h1
private lemma degree_induce_compl_singleton_of_adj {U : Type} [Fintype U]
    (T : SimpleGraph U) {a v : U} (hav : a ∈ ({v}ᶜ : Set U)) (hadj : T.Adj a v) :
    (T.induce {v}ᶜ).degree ⟨a, hav⟩ + 1 = T.degree a := by
  let f : ({v}ᶜ : Set U) ↪ U := ⟨Subtype.val, val_injective⟩
  have hmap_not : v ∉ ((T.induce {v}ᶜ).neighborFinset ⟨a, hav⟩).map f := by
    intro h
    rw [mem_map] at h
    obtain ⟨x, _, hxv⟩ := h
    exact x.2 hxv
  have heq : insert v (((T.induce {v}ᶜ).neighborFinset ⟨a, hav⟩).map f) = T.neighborFinset a := by
    ext y
    rw [mem_insert, mem_map, mem_neighborFinset]
    constructor
    · rintro (rfl | ⟨x, hx, rfl⟩)
      · exact hadj
      · rw [mem_neighborFinset] at hx
        exact hx
    · intro hay
      by_cases hyv : y = v
      · exact Or.inl hyv
      · refine Or.inr ⟨⟨y, hyv⟩, ?_, rfl⟩
        rw [mem_neighborFinset]
        exact hay
  have hcard := congrArg Finset.card heq
  rw [card_insert_of_notMem hmap_not, card_map,
    (T.induce {v}ᶜ).card_neighborFinset_eq_degree, T.card_neighborFinset_eq_degree] at hcard
  omega
private lemma degree_induce_compl_singleton_of_not_adj {U : Type} [Fintype U]
    (T : SimpleGraph U) {a v : U} (hav : a ∈ ({v}ᶜ : Set U)) (hnadj : ¬ T.Adj a v) :
    (T.induce {v}ᶜ).degree ⟨a, hav⟩ = T.degree a := by
  let f : ({v}ᶜ : Set U) ↪ U := ⟨Subtype.val, val_injective⟩
  have heq : ((T.induce {v}ᶜ).neighborFinset ⟨a, hav⟩).map f = T.neighborFinset a := by
    ext y
    rw [mem_map, mem_neighborFinset]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [mem_neighborFinset] at hx
      exact hx
    · intro hay
      have hyv : y ≠ v := fun h => hnadj (h ▸ hay)
      refine ⟨⟨y, hyv⟩, ?_, rfl⟩
      rw [mem_neighborFinset]
      exact hay
  have hcard := congrArg Finset.card heq
  rw [card_map, (T.induce {v}ᶜ).card_neighborFinset_eq_degree,
    T.card_neighborFinset_eq_degree] at hcard
  exact hcard
private lemma degree_induce_compl_le {U : Type} [Fintype U]
    (T : SimpleGraph U) {a v : U} (hav : a ∈ ({v}ᶜ : Set U)) :
    (T.induce {v}ᶜ).degree ⟨a, hav⟩ ≤ T.degree a := by
  by_cases hadj : T.Adj a v
  · have := degree_induce_compl_singleton_of_adj T hav hadj
    omega
  · rw [degree_induce_compl_singleton_of_not_adj T hav hadj]
private lemma induce_compl_singleton_isTree_of_deg_one {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {v : U} (hdeg1 : T.degree v = 1) :
    (T.induce {v}ᶜ).IsTree :=
  ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hdeg1, hT.isAcyclic.induce {v}ᶜ⟩
private lemma induce_compl_singleton_diam_le {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {v : U} (hdeg1 : T.degree v = 1) :
    (T.induce {v}ᶜ).diam ≤ T.diam := by
  have : Nonempty U := hT.connected.nonempty
  have hT' : (T.induce {v}ᶜ).IsTree := induce_compl_singleton_isTree_of_deg_one T hT hdeg1
  have : Nonempty ({v}ᶜ : Set U) := hT'.connected.nonempty
  obtain ⟨a, b, hab⟩ := (T.induce {v}ᶜ).exists_dist_eq_diam
  rw [← hab, dist_induce_eq_of_isTree T hT {v}ᶜ hT']
  exact dist_le_diam (connected_iff_ediam_ne_top.mp hT.connected)
private lemma exists_unique_center_of_diam_eq_two_mul {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {r : ℕ} (hr : 1 ≤ r) (hdiam : T.diam = 2 * r) :
    ∃ c : U, T.eccent c = r ∧ ∀ v : U, v ≠ c → (r : ℕ∞) < T.eccent v := by
  have : Nonempty U := hT.connected.nonempty
  obtain ⟨x0, xd, hxd⟩ := T.exists_dist_eq_diam
  obtain ⟨p, hp, hplen⟩ := hT.connected.exists_path_of_dist x0 xd
  have hplen_r : p.length = 2 * r := hplen.trans (hxd.trans hdiam)
  let c : U := p.getVert r
  let p₁ : T.Walk x0 c := p.take r
  let p₂ : T.Walk c xd := p.drop r
  have hp1 : p₁.IsPath := hp.take r
  have hp2 : p₂.IsPath := hp.drop r
  have hp1_len : p₁.length = r := by rw [Walk.take_length]; omega
  have hp2_len : p₂.length = r := by rw [Walk.drop_length]; omega
  have hp_app : p₁.append p₂ = p := p.append_take_drop_eq r
  have hkey : ∀ y : U, (T.dist y xd = T.dist y c + r ∨ T.dist y x0 = T.dist y c + r) := by
    intro y
    obtain ⟨q, hq, hqlen⟩ := hT.connected.exists_path_of_dist y c
    obtain ⟨z, q₁, q₂, hz_mem, hq_eq, hq_first⟩ :=
      split_walk_first_mem T {u | u ∈ p.support} q (p.getVert_mem_support r)
    have hq_app : (q₁.append q₂).IsPath := hq_eq ▸ hq
    have hq1 : q₁.IsPath := hq_app.of_append_left
    have hq2 : q₂.IsPath := hq_app.of_append_right
    have hz12 : z ∈ p₁.support ∨ z ∈ p₂.support :=
      (Walk.mem_support_append_iff p₁ p₂).mp (hp_app.symm ▸ hz_mem)
    rcases hz12 with hz1 | hz2
    · obtain ⟨a, b, ha, hb, hp1_eq⟩ := hp1.mem_support_iff_exists_append.mp hz1
      let pR : T.Walk z xd := b.append p₂
      have hp_decomp : p = a.append pR := by rw [← hp_app, hp1_eq, Walk.append_assoc]
      have hpR : pR.IsPath := (hp_decomp ▸ hp).of_append_right
      have hmeet_pR : ∀ u ∈ q₁.support, u ∈ pR.support.tail → u = z := by
        intro u huq hup
        exact hq_first u huq
          (hp_decomp ▸ Walk.support_subset_support_append_right a pR (List.mem_of_mem_tail hup))
      have hqp_path : (q₁.append pR).IsPath := isPath_append_of_first_meet hq1 hpR hmeet_pR
      have hdz : T.dist y xd = q₁.length + b.length + r := by
        rw [← isTree_dist_eq_length_of_isPath T hT (q₁.append pR) hqp_path,
          length_append, length_append, hp2_len, add_assoc]
      have hq2_eq : q₂ = b := isTree_path_eq T hT hq2 hb
      have hdc : T.dist y c = q₁.length + b.length := by
        rw [← hqlen, hq_eq, length_append, hq2_eq]
      exact Or.inl (by omega)
    · obtain ⟨a, b, ha, hb, hp2_eq⟩ := hp2.mem_support_iff_exists_append.mp hz2
      let pL : T.Walk z x0 := a.reverse.append p₁.reverse
      let pL_pre : T.Walk x0 z := p₁.append a
      have hp_decomp : p = pL_pre.append b := by rw [← hp_app, hp2_eq, ← Walk.append_assoc]
      have hpL_pre : pL_pre.IsPath := (hp_decomp ▸ hp).of_append_left
      have hpL_eq : pL = pL_pre.reverse := by simp only [pL, pL_pre, Walk.reverse_append]
      have hpL : pL.IsPath := hpL_eq ▸ hpL_pre.reverse
      have hmeet_pL : ∀ u ∈ q₁.support, u ∈ pL.support.tail → u = z := by
        intro u huq hup
        have hu1 : u ∈ pL_pre.reverse.support := hpL_eq ▸ List.mem_of_mem_tail hup
        rw [Walk.support_reverse, List.mem_reverse] at hu1
        exact hq_first u huq (hp_decomp ▸ Walk.support_subset_support_append_left pL_pre b hu1)
      have hqp_path : (q₁.append pL).IsPath := isPath_append_of_first_meet hq1 hpL hmeet_pL
      have hdz : T.dist y x0 = q₁.length + a.length + r := by
        rw [← isTree_dist_eq_length_of_isPath T hT (q₁.append pL) hqp_path,
          length_append, length_append, length_reverse, length_reverse,
          hp1_len, add_assoc]
      have hq2_eq : q₂ = a.reverse := isTree_path_eq T hT hq2 ha.reverse
      have hdc : T.dist y c = q₁.length + a.length := by
        rw [← hqlen, hq_eq, length_append, hq2_eq, length_reverse]
      exact Or.inr (by omega)
  have hle_c : ∀ y : U, T.dist y c ≤ r := by
    intro y
    have hediam : T.ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hT.connected
    have h1 : T.dist y xd ≤ 2 * r := hdiam ▸ dist_le_diam hediam
    have h2 : T.dist y x0 ≤ 2 * r := hdiam ▸ dist_le_diam hediam
    rcases hkey y with h | h <;> omega
  have hecc_le : T.eccent c ≤ r := by
    rw [eccent_le_iff]
    intro y
    rw [← (hT.connected c y).coe_dist_eq_edist, dist_comm]
    exact Nat.cast_le.mpr (hle_c y)
  have hdist_cx : T.dist c xd = r := by
    rw [← isTree_dist_eq_length_of_isPath T hT p₂ hp2, hp2_len]
  have hecc_ge : (r : ℕ∞) ≤ T.eccent c := by
    rw [← hdist_cx, (hT.connected c xd).coe_dist_eq_edist]
    exact edist_le_eccent
  refine ⟨c, le_antisymm hecc_le hecc_ge, fun v hvc => ?_⟩
  have hpos : 0 < T.dist v c := hT.connected.pos_dist_of_ne hvc
  rcases hkey v with h | h
  · have hlt : (r : ℕ∞) < T.edist v xd := by
      rw [← (hT.connected v xd).coe_dist_eq_edist, h]
      exact_mod_cast (by omega : r < T.dist v c + r)
    exact lt_of_lt_of_le hlt edist_le_eccent
  · have hlt : (r : ℕ∞) < T.edist v x0 := by
      rw [← (hT.connected v x0).coe_dist_eq_edist, h]
      exact_mod_cast (by omega : r < T.dist v c + r)
    exact lt_of_lt_of_le hlt edist_le_eccent
private lemma ne_center_of_deg_one {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {r : ℕ} (_hr : 1 ≤ r) (c : U)
    (hecc : T.eccent c = r) (huniq_c : ∀ z : U, z ≠ c → (r : ℕ∞) < T.eccent z)
    {v : U} (hdeg1 : T.degree v = 1) : v ≠ c := by
  rintro rfl
  obtain ⟨u, huv, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hdeg1
  have huc : u ≠ v := huv.ne.symm
  have hle : T.eccent u ≤ r := by
    rw [eccent_le_iff]
    intro y
    rw [← (hT.connected u y).coe_dist_eq_edist]
    norm_cast
    by_cases hyv : y = v
    · subst hyv
      have hd : T.dist u y = 1 := dist_eq_one_iff_adj.mpr huv.symm
      omega
    · obtain ⟨p, hp, hplen⟩ := hT.connected.exists_path_of_dist v y
      have hnp : ¬ p.Nil := not_nil_of_ne (Ne.symm hyv)
      have hsnd : p.snd = u := huniq p.snd (p.adj_snd hnp)
      let p' : T.Walk u y := p.tail.copy hsnd rfl
      have hp' : p'.IsPath := (isPath_copy _ _ _).mpr hp.tail
      have hdist_u : T.dist u y = p'.length :=
        (isTree_dist_eq_length_of_isPath T hT p' hp').symm
      have hvy_le := dist_le_of_eccent T hT (u := y) hecc
      rw [hdist_u, length_copy, length_tail, hplen]
      omega
  exact absurd (lt_of_lt_of_le (huniq_c u huc) hle) (lt_irrefl _)
private lemma center_induce_compl_of_good_leaf {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {r : ℕ} (hr : 1 ≤ r)
    (c : U) (hecc : T.eccent c = r) (huniq_c : ∀ z : U, z ≠ c → (r : ℕ∞) < T.eccent z)
    {v : U} (hdeg1 : T.degree v = 1) (hdiam' : (T.induce {v}ᶜ).diam = 2 * r) :
    ∃ hc : c ∈ ({v}ᶜ : Set U),
      (T.induce {v}ᶜ).eccent ⟨c, hc⟩ = r ∧
      ∀ z' : ({v}ᶜ : Set U), z' ≠ ⟨c, hc⟩ → (r : ℕ∞) < (T.induce {v}ᶜ).eccent z' := by
  have hc : c ∈ ({v}ᶜ : Set U) :=
    mem_compl_singleton_iff.mpr (ne_center_of_deg_one T hT hr c hecc huniq_c hdeg1).symm
  refine ⟨hc, ?_⟩
  let T' := T.induce ({v}ᶜ : Set U)
  have hT' : T'.IsTree := induce_compl_singleton_isTree_of_deg_one T hT hdeg1
  let c' : ({v}ᶜ : Set U) := ⟨c, hc⟩
  have hle_r : ∀ y' : ({v}ᶜ : Set U), T'.dist c' y' ≤ r := fun y' => by
    rw [dist_induce_eq_of_isTree T hT {v}ᶜ hT']
    exact dist_le_of_eccent T hT hecc
  have hecc_le : T'.eccent c' ≤ r := by
    rw [eccent_le_iff]
    intro y'
    rw [← (hT'.connected c' y').coe_dist_eq_edist]
    exact Nat.cast_le.mpr (hle_r y')
  have : Nonempty ({v}ᶜ : Set U) := hT'.connected.nonempty
  obtain ⟨a, b, hab⟩ := T'.exists_dist_eq_diam
  rw [hdiam'] at hab
  have hda : T'.dist c' a = r := by
    have htri := hT'.connected.dist_triangle (u := a) (v := c') (w := b)
    rw [dist_comm (u := a) (v := c')] at htri
    have ha := hle_r a
    have hb := hle_r b
    omega
  have hecc_ge : (r : ℕ∞) ≤ T'.eccent c' := by
    rw [← hda, (hT'.connected c' a).coe_dist_eq_edist]
    exact edist_le_eccent
  have hecc_eq : T'.eccent c' = r := le_antisymm hecc_le hecc_ge
  obtain ⟨c₀, _, huniq₀⟩ := exists_unique_center_of_diam_eq_two_mul T' hT' hr hdiam'
  have hc₀ : c' = c₀ := by
    by_contra hne
    have hlt := huniq₀ c' hne
    rw [hecc_eq] at hlt
    exact absurd hlt (lt_irrefl _)
  subst hc₀
  exact ⟨hecc_eq, huniq₀⟩
private lemma iso_map_center_of_good_leaf {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (hTG : G.IsTree) (hTH : H.IsTree)
    {r : ℕ} (hr : 1 ≤ r) (cG : V) (cH : W)
    (heccG : G.eccent cG = r) (huG : ∀ v : V, v ≠ cG → (r : ℕ∞) < G.eccent v)
    (heccH : H.eccent cH = r) (huH : ∀ w : W, w ≠ cH → (r : ℕ∞) < H.eccent w)
    {v : V} {w : W} (hv1 : G.degree v = 1) (hw1 : H.degree w = 1)
    (hdiamG' : (G.induce {v}ᶜ).diam = 2 * r)
    (φ : G.induce {v}ᶜ ≃g H.induce {w}ᶜ) :
    ∃ (hcG : cG ∈ ({v}ᶜ : Set V)) (hcH : cH ∈ ({w}ᶜ : Set W)), φ ⟨cG, hcG⟩ = ⟨cH, hcH⟩ := by
  have hdiamH' : (H.induce {w}ᶜ).diam = 2 * r := (iso_diam_eq _ _ φ).symm.trans hdiamG'
  obtain ⟨hcG, heccG', _⟩ := center_induce_compl_of_good_leaf G hTG hr cG heccG huG hv1 hdiamG'
  obtain ⟨hcH, _, huH'⟩ := center_induce_compl_of_good_leaf H hTH hr cH heccH huH hw1 hdiamH'
  refine ⟨hcG, hcH, ?_⟩
  by_contra hne
  have hlt := huH' (φ ⟨cG, hcG⟩) hne
  rw [iso_eccent_eq _ _ φ ⟨cG, hcG⟩, heccG'] at hlt
  exact absurd hlt (lt_irrefl _)
private lemma good_leaf_of_ne_diam_ends {U : Type} [Fintype U] (T : SimpleGraph U) (hT : T.IsTree)
    {r : ℕ} (_hr : 2 ≤ r) (hdiam : T.diam = 2 * r) {x0 xd : U} (hxd : T.dist x0 xd = 2 * r)
    {v : U} (hv1 : T.degree v = 1) (hx0 : v ≠ x0) (hxd_ne : v ≠ xd) :
    (T.induce {v}ᶜ).diam = 2 * r := by
  obtain ⟨p, hp, hplen⟩ := hT.connected.exists_path_of_dist x0 xd
  have hnot : v ∉ p.support := by
    intro hv_mem
    obtain ⟨q, s, hq, hs, hp_eq⟩ := hp.mem_support_iff_exists_append.mp hv_mem
    have hq_nn : ¬ q.Nil := not_nil_of_ne hx0.symm
    have hs_nn : ¬ s.Nil := not_nil_of_ne hxd_ne
    have hadj1 : T.Adj v q.penultimate := (q.adj_penultimate hq_nn).symm
    have hadj2 : T.Adj v s.snd := s.adj_snd hs_nn
    have hne12 : q.penultimate ≠ s.snd := by
      have hdisj : q.support.Disjoint s.tail.support := by
        have h1 := (hp_eq ▸ hp).support_nodup
        rw [Walk.support_append, List.nodup_append', ← support_tail_of_not_nil s hs_nn] at h1
        exact h1.2.2
      have hm1 : q.penultimate ∈ q.support := getVert_mem_support q (q.length - 1)
      have hm2 : s.snd ∈ s.tail.support := by
        rw [support_tail_of_not_nil s hs_nn]
        exact s.snd_mem_tail_support hs_nn
      intro heq
      rw [heq] at hm1
      exact hdisj hm1 hm2
    have h2 : 2 ≤ T.degree v := by
      rw [← T.card_neighborFinset_eq_degree]
      have hsub : {q.penultimate, s.snd} ⊆ T.neighborFinset v := by
        intro z hz
        simp only [mem_insert, mem_singleton] at hz
        rw [mem_neighborFinset]
        rcases hz with rfl | rfl <;> assumption
      calc
        2 = ({q.penultimate, s.snd} : Finset U).card := (card_pair hne12).symm
        _ ≤ (T.neighborFinset v).card := card_le_card hsub
    omega
  have hw_supp : ∀ x ∈ p.support, x ∈ ({v}ᶜ : Set U) := fun x hx =>
    mem_compl_singleton_iff.mpr fun heq => hnot (heq ▸ hx)
  let p' := p.induce ({v}ᶜ : Set U) hw_supp
  have hp' : p'.IsPath := by
    refine Walk.IsPath.of_map (f := (Embedding.induce ({v}ᶜ : Set U)).toHom) ?_
    rw [Walk.map_induce]
    exact hp
  have hT' : (T.induce {v}ᶜ).IsTree := induce_compl_singleton_isTree_of_deg_one T hT hv1
  have : Nonempty ({v}ᶜ : Set U) := hT'.connected.nonempty
  have hdist : (T.induce {v}ᶜ).dist ⟨x0, hw_supp x0 p.start_mem_support⟩
      ⟨xd, hw_supp xd p.end_mem_support⟩ = 2 * r := by
    have h1 := isTree_dist_eq_length_of_isPath (T.induce {v}ᶜ) hT' p' hp'
    rw [← h1, length_walk_induce, hplen, hxd]
  have hediam' : (T.induce {v}ᶜ).ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hT'.connected
  have hge : 2 * r ≤ (T.induce {v}ᶜ).diam := hdist ▸ dist_le_diam hediam'
  have hle : (T.induce {v}ᶜ).diam ≤ 2 * r := hdiam ▸ induce_compl_singleton_diam_le T hT hv1
  omega
private lemma diam_path_contains_center {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {r : ℕ} (c : U) (hecc : T.eccent c = r)
    {x0 xd : U} (p : T.Walk x0 xd) (hp : p.IsPath) (hplen : p.length = 2 * r) :
    c ∈ p.support ∧ T.dist c x0 = r ∧ T.dist c xd = r := by
  obtain ⟨q1, hq1, hq1len⟩ := hT.connected.exists_path_of_dist x0 c
  obtain ⟨q2, hq2, hq2len⟩ := hT.connected.exists_path_of_dist c xd
  have h1 : T.dist x0 c ≤ r := by
    rw [dist_comm]
    exact dist_le_of_eccent T hT hecc
  have h2 : T.dist c xd ≤ r := dist_le_of_eccent T hT hecc
  have hpdist : p.length = T.dist x0 xd := isTree_dist_eq_length_of_isPath T hT p hp
  have htri := hT.connected.dist_triangle (u := x0) (v := c) (w := xd)
  have h1eq : T.dist x0 c = r := by omega
  have h2eq : T.dist c xd = r := by omega
  have hq12_len : (q1.append q2).length = T.dist x0 xd := by
    rw [length_append, hq1len, hq2len, h1eq, h2eq, ← hpdist, hplen]
    omega
  have hq12_path : (q1.append q2).IsPath :=
    (q1.append q2).isPath_of_length_eq_dist hq12_len
  have heq : q1.append q2 = p := isTree_path_eq T hT hq12_path hp
  have hc_mem : c ∈ p.support := by
    rw [← heq, Walk.mem_support_append_iff]
    exact Or.inl q1.end_mem_support
  rw [dist_comm] at h1eq
  exact ⟨hc_mem, h1eq, h2eq⟩
private lemma existsUnique_root_of_component {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) (c : U)
    (C : (T.induce {c}ᶜ).ConnectedComponent) :
    ∃! u : ({c}ᶜ : Set U), u ∈ C.supp ∧ T.Adj c u.1 := by
  obtain ⟨z, hz⟩ := C.nonempty_supp
  have hzc : z.1 ≠ c := z.2
  obtain ⟨p, hp, _⟩ := hT.connected.exists_path_of_dist c z.1
  have hnp : ¬ p.Nil := not_nil_of_ne hzc.symm
  let uVal : U := p.snd
  have hadj : T.Adj c uVal := p.adj_snd hnp
  have huc : uVal ∈ ({c}ᶜ : Set U) := mem_compl_singleton_iff.mpr hadj.ne.symm
  let u : ({c}ᶜ : Set U) := ⟨uVal, huc⟩
  have hsupp_tail : ∀ x ∈ p.tail.support, x ∈ ({c}ᶜ : Set U) := by
    intro x hx
    rw [support_tail_of_not_nil p hnp] at hx
    exact mem_compl_singleton_iff.mpr fun hxc =>
      start_notMem_tail_support_of_isPath hp (hxc ▸ hx)
  let p' : (T.induce {c}ᶜ).Walk u z :=
    (p.tail.induce ({c}ᶜ : Set U) hsupp_tail).copy rfl (Subtype.ext rfl)
  have hu_mem : u ∈ C.supp := by
    rw [mem_supp_iff] at hz ⊢
    exact (sound ⟨p'⟩).trans hz
  refine ⟨u, ⟨hu_mem, hadj⟩, fun u' ⟨hu'_mem, hadj'⟩ => ?_⟩
  by_contra hne
  have hne_val : uVal ≠ u'.1 := fun h => hne (Subtype.ext h).symm
  obtain ⟨q⟩ := C.reachable_of_mem_supp hu_mem hu'_mem
  let q_path := q.toPath
  let g : T.induce {c}ᶜ →g T := (Embedding.induce ({c}ᶜ : Set U)).toHom
  have hqG : (q_path.val.map g).IsPath := q_path.isPath.map val_injective
  have hc_not_q : c ∉ (q_path.val.map g).support := by
    rw [Walk.support_map, List.mem_map]
    rintro ⟨x, _, hxc⟩
    exact x.2 hxc
  let two_step : T.Walk uVal u'.1 := Walk.cons hadj.symm (Walk.cons hadj' Walk.nil)
  have htwo_path : two_step.IsPath := by
    simp [two_step, cons_isPath_iff, hne_val, hadj.ne.symm, hadj'.ne]
  have heq := isTree_path_eq T hT hqG htwo_path
  have hc_in : c ∈ two_step.support := by simp [two_step]
  rw [← heq] at hc_in
  exact hc_not_q hc_in
private lemma component_toSimpleGraph_degree {U : Type} [Fintype U]
    (T : SimpleGraph U) (c : U) (C : (T.induce {c}ᶜ).ConnectedComponent) (x : C.supp) :
    C.toSimpleGraph.degree x = (T.induce {c}ᶜ).degree x.1 := by
  let f : C.supp ↪ ({c}ᶜ : Set U) := ⟨Subtype.val, val_injective⟩
  have heq : (C.toSimpleGraph.neighborFinset x).map f = (T.induce {c}ᶜ).neighborFinset x.1 := by
    ext y
    rw [mem_map, mem_neighborFinset]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [mem_neighborFinset] at hz
      exact hz
    · intro hxy
      have hy : y ∈ C.supp := C.mem_supp_of_adj_mem_supp x.2 hxy
      refine ⟨⟨y, hy⟩, ?_, rfl⟩
      rw [mem_neighborFinset]
      exact hxy
  have hcard := congrArg Finset.card heq
  rw [card_map, C.toSimpleGraph.card_neighborFinset_eq_degree,
    (T.induce {c}ᶜ).card_neighborFinset_eq_degree] at hcard
  exact hcard
private lemma component_degree_sum {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) (c : U)
    (C : (T.induce {c}ᶜ).ConnectedComponent) :
    ∑ x : C.supp, T.degree x.1.1 = 2 * card C.supp - 1 := by
  obtain ⟨u, ⟨hu_mem, hu_adj⟩, hu_uniq⟩ := existsUnique_root_of_component T hT c C
  let uC : C.supp := ⟨u, hu_mem⟩
  have hdeg_eq : ∀ x : C.supp,
      T.degree x.1.1 = C.toSimpleGraph.degree x + (if x = uC then 1 else 0) := by
    intro x
    rw [component_toSimpleGraph_degree T c C x]
    split_ifs with hxu
    · subst hxu
      exact (degree_induce_compl_singleton_of_adj T u.2 hu_adj.symm).symm
    · have hnadj : ¬ T.Adj x.1.1 c := by
        intro hadj
        have hxeq : x.1 = u := hu_uniq x.1 ⟨x.2, hadj.symm⟩
        exact hxu (Subtype.ext hxeq)
      exact (degree_induce_compl_singleton_of_not_adj T x.1.2 hnadj).symm
  have hsum : ∑ x : C.supp, T.degree x.1.1 =
      (∑ x : C.supp, C.toSimpleGraph.degree x) + ∑ x : C.supp, (if x = uC then 1 else 0) := by
    rw [← Finset.sum_add_distrib]
    exact sum_congr rfl fun x _ => hdeg_eq x
  have hC_tree : C.toSimpleGraph.IsTree :=
    (hT.isAcyclic.induce {c}ᶜ).isTree_connectedComponent C
  have hdeg_sum : (∑ x : C.supp, C.toSimpleGraph.degree x) = 2 * C.toSimpleGraph.edgeFinset.card := by
    convert C.toSimpleGraph.sum_degrees_eq_twice_card_edges
    all_goals exact Iff.rfl
  rw [hdeg_sum] at hsum
  simp only [Finset.sum_ite_eq', mem_univ, ↓reduceIte] at hsum
  have hC_edges : C.toSimpleGraph.edgeFinset.card + 1 = card C.supp := by
    convert hC_tree.card_edgeFinset
    all_goals exact Iff.rfl
  have hC_pos : 1 ≤ card C.supp := Fintype.card_pos_iff.mpr ⟨uC⟩
  omega
private lemma component_leaves_formula {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) (c : U)
    (C : (T.induce {c}ᶜ).ConnectedComponent) :
    let LC := univ.filter fun x : C.supp => T.degree x.1.1 = 1
    LC.card = 1 + ∑ x ∈ LCᶜ, (T.degree x.1.1 - 2) ∧
      ∀ x ∈ LCᶜ, 2 ≤ T.degree x.1.1 := by
  have hT_pos : ∀ v : U, 1 ≤ T.degree v := by
    intro v
    obtain ⟨w, _⟩ := C.nonempty_supp
    have : Nontrivial U := ⟨⟨c, w.1, fun h => w.2 h.symm⟩⟩
    exact hT.preconnected.degree_pos_of_nontrivial v
  let LC : Finset C.supp := univ.filter fun x : C.supp => T.degree x.1.1 = 1
  have hge2 : ∀ x ∈ LCᶜ, 2 ≤ T.degree x.1.1 := by
    intro x hx
    simp only [LC, Finset.mem_compl, mem_filter, mem_univ, true_and] at hx
    have := hT_pos x.1.1
    omega
  have hsum := component_degree_sum T hT c C
  have hsplit : (∑ x ∈ LC, T.degree x.1.1) + ∑ x ∈ LCᶜ, T.degree x.1.1 = ∑ x : C.supp, T.degree x.1.1 :=
    Finset.sum_add_sum_compl LC (fun x => T.degree x.1.1)
  have hsum_L : ∑ x ∈ LC, T.degree x.1.1 = LC.card := by
    calc
      ∑ x ∈ LC, T.degree x.1.1 = ∑ _x ∈ LC, 1 := sum_congr rfl fun x hx => (mem_filter.mp hx).2
      _ = LC.card := by simp
  have hsum_Lc : ∑ x ∈ LCᶜ, T.degree x.1.1 = 2 * LCᶜ.card + ∑ x ∈ LCᶜ, (T.degree x.1.1 - 2) := by
    calc
      ∑ x ∈ LCᶜ, T.degree x.1.1 = ∑ x ∈ LCᶜ, (2 + (T.degree x.1.1 - 2)) :=
        sum_congr rfl fun x hx => by have := hge2 x hx; omega
      _ = (∑ _x ∈ LCᶜ, 2) + ∑ x ∈ LCᶜ, (T.degree x.1.1 - 2) := Finset.sum_add_distrib
      _ = 2 * LCᶜ.card + ∑ x ∈ LCᶜ, (T.degree x.1.1 - 2) := by simp [mul_comm]
  have hcard_compl : LC.card + LCᶜ.card = card C.supp := by
    rw [Finset.card_compl]
    have : LC.card ≤ card C.supp := card_le_univ LC
    omega
  have hC_pos : 1 ≤ card C.supp := by
    obtain ⟨w, hw⟩ := C.nonempty_supp
    exact Fintype.card_pos_iff.mpr ⟨⟨w, hw⟩⟩
  refine ⟨?_, hge2⟩
  change LC.card = 1 + ∑ x ∈ LCᶜ, (T.degree x.1.1 - 2)
  omega
private lemma card_connectedComponent_eq_degree {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) (c : U) :
    card (T.induce {c}ᶜ).ConnectedComponent = T.degree c := by
  let f : (T.induce {c}ᶜ).ConnectedComponent → T.neighborFinset c := fun C =>
    let u := (existsUnique_root_of_component T hT c C).choose
    ⟨u.1, (T.mem_neighborFinset c u.1).mpr (existsUnique_root_of_component T hT c C).choose_spec.1.2⟩
  let g : T.neighborFinset c → (T.induce {c}ᶜ).ConnectedComponent := fun u =>
    (T.induce {c}ᶜ).connectedComponentMk ⟨u.1, mem_compl_singleton_iff.mpr ((T.mem_neighborFinset c u.1).mp u.2).ne.symm⟩
  have hleft : LeftInverse g f := by
    intro C
    dsimp only [f, g]
    exact (mem_supp_iff C _).mp
      (existsUnique_root_of_component T hT c C).choose_spec.1.1
  have hright : RightInverse g f := by
    intro u
    dsimp only [f, g]
    apply Subtype.ext
    have hadj : T.Adj c u.1 := (T.mem_neighborFinset c u.1).mp u.2
    have huc : u.1 ∈ ({c}ᶜ : Set U) := mem_compl_singleton_iff.mpr hadj.ne.symm
    let u_sub : ({c}ᶜ : Set U) := ⟨u.1, huc⟩
    let C := (T.induce {c}ᶜ).connectedComponentMk u_sub
    have h_eq := ((existsUnique_root_of_component T hT c C).choose_spec.2 u_sub ⟨rfl, hadj⟩).symm
    exact congrArg (fun z : ({c}ᶜ : Set U) => z.1) h_eq
  rw [card_congr ⟨f, g, hleft, hright⟩, card_coe, T.card_neighborFinset_eq_degree]
private lemma sum_card_connectedComponent_eq {U : Type} [Fintype U]
    (T : SimpleGraph U) (c : U) :
    (∑ C : (T.induce {c}ᶜ).ConnectedComponent, card C.supp) + 1 = card U := by
  have h1 : (∑ C : (T.induce {c}ᶜ).ConnectedComponent, card C.supp) =
      card ({c}ᶜ : Set U) := by
    rw [← Fintype.card_sigma]
    refine card_congr
      ⟨fun ⟨_, ⟨x, _⟩⟩ => x, fun (x : ({c}ᶜ : Set U)) => ⟨(T.induce {c}ᶜ).connectedComponentMk x, ⟨x, rfl⟩⟩, ?_, ?_⟩
    · rintro ⟨C, ⟨x, hx⟩⟩
      have hCx : (T.induce {c}ᶜ).connectedComponentMk x = C := (mem_supp_iff C x).mp hx
      subst hCx
      rfl
    · intro x
      rfl
  have h2 : card ({c}ᶜ : Set U) + 1 = card U := by
    have e : ({c}ᶜ : Set U) ≃ ↥(univ.erase c) :=
      ⟨fun x => ⟨x.1, mem_erase.mpr ⟨x.2, mem_univ _⟩⟩,
       fun x => ⟨x.1, (mem_erase.mp x.2).1⟩,
       fun _ => rfl, fun _ => rfl⟩
    rw [card_congr e, card_coe, card_erase_of_mem (mem_univ c),
      card_univ]
    have : 1 ≤ card U := Fintype.card_pos_iff.mpr ⟨c⟩
    omega
  omega
private lemma induce_support_iso_pathG {U : Type} [Fintype U] (T : SimpleGraph U) (hT : T.IsTree)
    {a b : U} (p : T.Walk a b) (hp : p.IsPath) :
    Nonempty (T.induce (p.support.toFinset : Set U) ≃g pathG (p.length + 1)) := by
  let f : Fin (p.length + 1) → U := fun i => p.getVert i.val
  have hf_inj : Injective f := by
    intro i j hij
    have hi : i.val ≤ p.length := by omega
    have hj : j.val ≤ p.length := by omega
    change p.getVert i.val = p.getVert j.val at hij
    rw [getVert_eq_support_getElem p hi, getVert_eq_support_getElem p hj] at hij
    exact Fin.ext ((List.Nodup.getElem_inj_iff hp.support_nodup).mp hij)
  let toFun : Fin (p.length + 1) → (p.support.toFinset : Set U) := fun i =>
    ⟨f i, mem_coe.mpr (List.mem_toFinset.mpr (p.getVert_mem_support i.val))⟩
  have hbij : Function.Bijective toFun := by
    constructor
    · intro i j hij
      exact hf_inj (congrArg Subtype.val hij)
    · rintro ⟨x, hx⟩
      rw [mem_coe, List.mem_toFinset] at hx
      let k := p.support.idxOf x
      have hk_lt : k < p.support.length := List.idxOf_lt_length_of_mem hx
      have hk_le : k ≤ p.length := by rw [p.length_support] at hk_lt; omega
      refine ⟨⟨k, by omega⟩, Subtype.ext ?_⟩
      change p.getVert k = x
      rw [getVert_eq_support_getElem p hk_le]
      exact List.getElem_idxOf hk_lt
  let eqv : Fin (p.length + 1) ≃ (p.support.toFinset : Set U) := Equiv.ofBijective toFun hbij
  have hrel : ∀ i j : Fin (p.length + 1), (pathG (p.length + 1)).Adj i j ↔ T.Adj (f i) (f j) := by
    intro i j
    constructor
    · rintro (h | h)
      · have hi : i.val < p.length := by omega
        simpa [f, h] using p.adj_getVert_succ hi
      · have hj : j.val < p.length := by omega
        exact (by simpa [f, h] using p.adj_getVert_succ hj : T.Adj (f j) (f i)).symm
    · intro hadj
      by_contra hnot
      have hne : i.val ≠ j.val := fun he => T.ne_of_adj hadj (congrArg f (Fin.ext he))
      have hlt_or : i.val + 1 < j.val ∨ j.val + 1 < i.val := by
        have h1 : i.val + 1 ≠ j.val := fun h => hnot (Or.inl h)
        have h2 : j.val + 1 ≠ i.val := fun h => hnot (Or.inr h)
        omega
      have shortcut : ∀ u v : Fin (p.length + 1), u.val + 1 < v.val → T.Adj (f u) (f v) → False := by
        intro u v huv hadjUV
        have hu_le : u.val ≤ p.length := by omega
        have hv_le : v.val ≤ p.length := by omega
        have hu_lt : u.val < p.support.length := by rw [p.length_support]; omega
        have hv_lt : v.val < p.support.length := by rw [p.length_support]; omega
        let p1 := p.takeUntil (p.getVert u.val) (p.getVert_mem_support u.val)
        let p2 := p.dropUntil (p.getVert v.val) (p.getVert_mem_support v.val)
        have hidx_u : p.support.idxOf (p.getVert u.val) = u.val := by
          rw [getVert_eq_support_getElem p hu_le]
          exact hp.support_nodup.idxOf_getElem u.val hu_lt
        have hidx_v : p.support.idxOf (p.getVert v.val) = v.val := by
          rw [getVert_eq_support_getElem p hv_le]
          exact hp.support_nodup.idxOf_getElem v.val hv_lt
        have hp1_len : p1.length = u.val := by rw [Walk.length_takeUntil, hidx_u]
        have hp2_len : p2.length = p.length - v.val := by
          have hspec := p.take_spec (p.getVert_mem_support v.val)
          have hsum := congrArg Walk.length hspec
          rw [length_append, Walk.length_takeUntil, hidx_v] at hsum
          change v.val + p2.length = p.length at hsum
          omega
        let q : T.Walk a b := p1.append (Walk.cons hadjUV p2)
        have hqlen : q.length < p.length := by
          simp only [q, length_append, length_cons]; omega
        have hdist_p := isTree_dist_eq_length_of_isPath T hT p hp
        have hdist_q := T.dist_le q
        omega
      rcases hlt_or with h | h
      · exact shortcut i j h hadj
      · exact shortcut j i h hadj.symm
  exact ⟨(RelIso.mk eqv (fun {i j} => (hrel i j).symm)).symm⟩
private lemma induce_support_iso_pathG_rooted {U : Type} [Fintype U] (T : SimpleGraph U) (hT : T.IsTree)
    {a b : U} (p : T.Walk a b) (hp : p.IsPath) :
    ∃ (φ : T.induce (p.support.toFinset : Set U) ≃g pathG (p.length + 1)),
      φ ⟨a, mem_coe.mpr (List.mem_toFinset.mpr p.start_mem_support)⟩ = ⟨0, Nat.zero_lt_succ _⟩ ∧
      φ ⟨b, mem_coe.mpr (List.mem_toFinset.mpr p.end_mem_support)⟩ = ⟨p.length, Nat.lt_succ_self _⟩ := by
  let f : Fin (p.length + 1) → U := fun i => p.getVert i.val
  have hf_inj : Injective f := by
    intro i j hij
    have hi : i.val ≤ p.length := by omega
    have hj : j.val ≤ p.length := by omega
    change p.getVert i.val = p.getVert j.val at hij
    rw [getVert_eq_support_getElem p hi, getVert_eq_support_getElem p hj] at hij
    exact Fin.ext ((List.Nodup.getElem_inj_iff hp.support_nodup).mp hij)
  let toFun : Fin (p.length + 1) → (p.support.toFinset : Set U) := fun i =>
    ⟨f i, mem_coe.mpr (List.mem_toFinset.mpr (p.getVert_mem_support i.val))⟩
  have hbij : Function.Bijective toFun := by
    constructor
    · intro i j hij
      exact hf_inj (congrArg Subtype.val hij)
    · rintro ⟨x, hx⟩
      rw [mem_coe, List.mem_toFinset] at hx
      let k := p.support.idxOf x
      have hk_lt : k < p.support.length := List.idxOf_lt_length_of_mem hx
      have hk_le : k ≤ p.length := by rw [p.length_support] at hk_lt; omega
      refine ⟨⟨k, by omega⟩, Subtype.ext ?_⟩
      change p.getVert k = x
      rw [getVert_eq_support_getElem p hk_le]
      exact List.getElem_idxOf hk_lt
  let eqv : Fin (p.length + 1) ≃ (p.support.toFinset : Set U) := Equiv.ofBijective toFun hbij
  have hrel : ∀ i j : Fin (p.length + 1), (pathG (p.length + 1)).Adj i j ↔ T.Adj (f i) (f j) := by
    intro i j
    constructor
    · rintro (h | h)
      · have hi : i.val < p.length := by omega
        simpa [f, h] using p.adj_getVert_succ hi
      · have hj : j.val < p.length := by omega
        exact (by simpa [f, h] using p.adj_getVert_succ hj : T.Adj (f j) (f i)).symm
    · intro hadj
      by_contra hnot
      have hne : i.val ≠ j.val := fun he => T.ne_of_adj hadj (congrArg f (Fin.ext he))
      have hlt_or : i.val + 1 < j.val ∨ j.val + 1 < i.val := by
        have h1 : i.val + 1 ≠ j.val := fun h => hnot (Or.inl h)
        have h2 : j.val + 1 ≠ i.val := fun h => hnot (Or.inr h)
        omega
      have shortcut : ∀ u v : Fin (p.length + 1), u.val + 1 < v.val → T.Adj (f u) (f v) → False := by
        intro u v huv hadjUV
        have hu_le : u.val ≤ p.length := by omega
        have hv_le : v.val ≤ p.length := by omega
        have hu_lt : u.val < p.support.length := by rw [p.length_support]; omega
        have hv_lt : v.val < p.support.length := by rw [p.length_support]; omega
        let p1 := p.takeUntil (p.getVert u.val) (p.getVert_mem_support u.val)
        let p2 := p.dropUntil (p.getVert v.val) (p.getVert_mem_support v.val)
        have hidx_u : p.support.idxOf (p.getVert u.val) = u.val := by
          rw [getVert_eq_support_getElem p hu_le]
          exact hp.support_nodup.idxOf_getElem u.val hu_lt
        have hidx_v : p.support.idxOf (p.getVert v.val) = v.val := by
          rw [getVert_eq_support_getElem p hv_le]
          exact hp.support_nodup.idxOf_getElem v.val hv_lt
        have hp1_len : p1.length = u.val := by rw [Walk.length_takeUntil, hidx_u]
        have hp2_len : p2.length = p.length - v.val := by
          have hspec := p.take_spec (p.getVert_mem_support v.val)
          have hsum := congrArg Walk.length hspec
          rw [length_append, Walk.length_takeUntil, hidx_v] at hsum
          change v.val + p2.length = p.length at hsum
          omega
        let q : T.Walk a b := p1.append (Walk.cons hadjUV p2)
        have hqlen : q.length < p.length := by
          simp only [q, length_append, length_cons]; omega
        have hdist_p := isTree_dist_eq_length_of_isPath T hT p hp
        have hdist_q := T.dist_le q
        omega
      rcases hlt_or with h | h
      · exact shortcut i j h hadj
      · exact shortcut j i h hadj.symm
  let φ : T.induce (p.support.toFinset : Set U) ≃g pathG (p.length + 1) :=
    (RelIso.mk eqv (fun {i j} => (hrel i j).symm)).symm
  refine ⟨φ, ?_, ?_⟩
  · apply φ.symm.injective
    rw [φ.symm_apply_apply]
    apply Subtype.ext
    change a = p.getVert 0
    simp
  · apply φ.symm.injective
    rw [φ.symm_apply_apply]
    apply Subtype.ext
    change b = p.getVert p.length
    simp
/-! ### Part 2: Component sets, RootedIso, patching, and component structure -/
private noncomputable def compSet {U : Type} [Fintype U] (T : SimpleGraph U) (c : U)
    (C : (T.induce {c}ᶜ).ConnectedComponent) : Finset U :=
  univ.filter fun x => ∃ h : x ≠ c, (⟨x, h⟩ : ({c}ᶜ : Set U)) ∈ C.supp
private lemma mem_compSet_iff {U : Type} [Fintype U] (T : SimpleGraph U) (c : U)
    (C : (T.induce {c}ᶜ).ConnectedComponent) (x : U) :
    x ∈ compSet T c C ↔ ∃ h : x ≠ c, (⟨x, h⟩ : ({c}ᶜ : Set U)) ∈ C.supp := by
  simp [compSet]
private lemma c_notMem_compSet {U : Type} [Fintype U] (T : SimpleGraph U) (c : U)
    (C : (T.induce {c}ᶜ).ConnectedComponent) : c ∉ compSet T c C := by
  intro h
  obtain ⟨hne, _⟩ := (mem_compSet_iff T c C c).mp h
  exact hne rfl
private lemma compSet_card_eq {U : Type} [Fintype U] (T : SimpleGraph U) (c : U)
    (C : (T.induce {c}ᶜ).ConnectedComponent) :
    (compSet T c C).card = card C.supp := by
  rw [← card_coe (compSet T c C)]
  refine card_congr
    ⟨fun x => ⟨⟨x.1, ((mem_compSet_iff T c C x.1).mp x.2).choose⟩,
       ((mem_compSet_iff T c C x.1).mp x.2).choose_spec⟩,
     fun y => ⟨y.1.1, (mem_compSet_iff T c C y.1.1).mpr ⟨y.1.2, y.2⟩⟩, ?_, ?_⟩
  · intro x; ext; rfl
  · intro y; ext; rfl
private lemma compSet_disjoint {U : Type} [Fintype U] (T : SimpleGraph U) (c : U)
    {C₁ C₂ : (T.induce {c}ᶜ).ConnectedComponent} (hne : C₁ ≠ C₂) :
    Disjoint (compSet T c C₁) (compSet T c C₂) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  obtain ⟨h1, hm1⟩ := (mem_compSet_iff T c C₁ x).mp hx1
  obtain ⟨h2, hm2⟩ := (mem_compSet_iff T c C₂ x).mp hx2
  have hc1 := (mem_supp_iff C₁ ⟨x, h1⟩).mp hm1
  have hc2 := (mem_supp_iff C₂ ⟨x, h2⟩).mp hm2
  exact hne (hc1.symm.trans hc2)
private lemma adj_compSet_eq {U : Type} [Fintype U] (T : SimpleGraph U) (c : U)
    {C₁ C₂ : (T.induce {c}ᶜ).ConnectedComponent} {x₁ x₂ : U}
    (hx1 : x₁ ∈ compSet T c C₁) (hx2 : x₂ ∈ compSet T c C₂) (hadj : T.Adj x₁ x₂) :
    C₁ = C₂ := by
  obtain ⟨h1, hm1⟩ := (mem_compSet_iff T c C₁ x₁).mp hx1
  obtain ⟨h2, hm2⟩ := (mem_compSet_iff T c C₂ x₂).mp hx2
  have hreach : (T.induce {c}ᶜ).Reachable ⟨x₁, h1⟩ ⟨x₂, h2⟩ := Adj.reachable hadj
  have hc1 := (mem_supp_iff C₁ ⟨x₁, h1⟩).mp hm1
  have hc2 := (mem_supp_iff C₂ ⟨x₂, h2⟩).mp hm2
  exact hc1.symm.trans ((sound hreach).trans hc2)
private def RootedIso {U₁ U₂ : Type} (T₁ : SimpleGraph U₁) (c₁ : U₁) (S₁ : Set U₁)
    (T₂ : SimpleGraph U₂) (c₂ : U₂) (S₂ : Set U₂) : Prop :=
  ∃ (h₁ : c₁ ∈ S₁) (h₂ : c₂ ∈ S₂) (φ : T₁.induce S₁ ≃g T₂.induce S₂),
    φ ⟨c₁, h₁⟩ = ⟨c₂, h₂⟩
private lemma RootedIso.refl {U : Type} (T : SimpleGraph U) (c : U) {S : Set U} (hc : c ∈ S) :
    RootedIso T c S T c S :=
  ⟨hc, hc, RelIso.refl _, rfl⟩
private lemma RootedIso.symm {U₁ U₂ : Type} {T₁ : SimpleGraph U₁} {c₁ : U₁} {S₁ : Set U₁}
    {T₂ : SimpleGraph U₂} {c₂ : U₂} {S₂ : Set U₂}
    (h : RootedIso T₁ c₁ S₁ T₂ c₂ S₂) : RootedIso T₂ c₂ S₂ T₁ c₁ S₁ := by
  obtain ⟨h₁, h₂, φ, hφ⟩ := h
  refine ⟨h₂, h₁, φ.symm, ?_⟩
  rw [← hφ, φ.symm_apply_apply]
private lemma RootedIso.trans {U₁ U₂ U₃ : Type} {T₁ : SimpleGraph U₁} {c₁ : U₁} {S₁ : Set U₁}
    {T₂ : SimpleGraph U₂} {c₂ : U₂} {S₂ : Set U₂} {T₃ : SimpleGraph U₃} {c₃ : U₃} {S₃ : Set U₃}
    (h12 : RootedIso T₁ c₁ S₁ T₂ c₂ S₂) (h23 : RootedIso T₂ c₂ S₂ T₃ c₃ S₃) :
    RootedIso T₁ c₁ S₁ T₃ c₃ S₃ := by
  obtain ⟨h1, h2a, φ12, hφ12⟩ := h12
  obtain ⟨h2b, h3, φ23, hφ23⟩ := h23
  refine ⟨h1, h3, φ12.trans φ23, ?_⟩
  rw [RelIso.trans_apply, hφ12, hφ23]
private lemma RootedIso.card_eq {U₁ U₂ : Type} [Fintype U₁] [Fintype U₂]
    {T₁ : SimpleGraph U₁} {c₁ : U₁} {S₁ : Finset U₁}
    {T₂ : SimpleGraph U₂} {c₂ : U₂} {S₂ : Finset U₂}
    (h : RootedIso T₁ c₁ (S₁ : Set U₁) T₂ c₂ (S₂ : Set U₂)) :
    S₁.card = S₂.card := by
  obtain ⟨_, _, φ, _⟩ := h
  rw [← card_coe S₁, ← card_coe S₂]
  exact card_congr φ.toEquiv
private def RootedCompIso {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (cG : V) (C : (G.induce {cG}ᶜ).ConnectedComponent)
    (H : SimpleGraph W) (cH : W) (D : (H.induce {cH}ᶜ).ConnectedComponent) : Prop :=
  RootedIso G cG (insert cG (compSet G cG C : Set V)) H cH (insert cH (compSet H cH D : Set W))
private lemma RootedCompIso.symm {V W : Type} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {cG : V} {C : (G.induce {cG}ᶜ).ConnectedComponent}
    {H : SimpleGraph W} {cH : W} {D : (H.induce {cH}ᶜ).ConnectedComponent}
    (h : RootedCompIso G cG C H cH D) : RootedCompIso H cH D G cG C :=
  RootedIso.symm h
private lemma RootedCompIso.trans {U₁ U₂ U₃ : Type} [Fintype U₁] [Fintype U₂] [Fintype U₃]
    {T₁ : SimpleGraph U₁} {c₁ : U₁} {C₁ : (T₁.induce {c₁}ᶜ).ConnectedComponent}
    {T₂ : SimpleGraph U₂} {c₂ : U₂} {C₂ : (T₂.induce {c₂}ᶜ).ConnectedComponent}
    {T₃ : SimpleGraph U₃} {c₃ : U₃} {C₃ : (T₃.induce {c₃}ᶜ).ConnectedComponent}
    (h12 : RootedCompIso T₁ c₁ C₁ T₂ c₂ C₂) (h23 : RootedCompIso T₂ c₂ C₂ T₃ c₃ C₃) :
    RootedCompIso T₁ c₁ C₁ T₃ c₃ C₃ :=
  RootedIso.trans h12 h23
private lemma iso_of_rootedCompIso_bij {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (cG : V) (cH : W)
    (e : (G.induce {cG}ᶜ).ConnectedComponent ≃ (H.induce {cH}ᶜ).ConnectedComponent)
    (he : ∀ C, RootedCompIso G cG C H cH (e C)) :
    Nonempty (G ≃g H) := by
  let compG (v : V) (hv : v ≠ cG) := (G.induce {cG}ᶜ).connectedComponentMk ⟨v, hv⟩
  let compH (w : W) (hw : w ≠ cH) := (H.induce {cH}ᶜ).connectedComponentMk ⟨w, hw⟩
  let φC (C : (G.induce {cG}ᶜ).ConnectedComponent) :
      G.induce (insert cG (compSet G cG C : Set V)) ≃g
      H.induce (insert cH (compSet H cH (e C) : Set W)) :=
    (he C).choose_spec.choose_spec.choose
  have hφC_root (C : (G.induce {cG}ᶜ).ConnectedComponent) :
      (φC C ⟨cG, Set.mem_insert _ _⟩).1 = cH := by
    have h1 := (he C).choose_spec.choose_spec.choose_spec
    exact congrArg Subtype.val h1
  have hφC_mem (C : (G.induce {cG}ᶜ).ConnectedComponent) (x : V) (hx : x ∈ compSet G cG C) :
      (φC C ⟨x, Or.inr hx⟩).1 ∈ compSet H cH (e C) := by
    have hmem := (φC C ⟨x, Or.inr hx⟩).2
    rcases mem_insert_iff.mp hmem with h | h
    · have hne : (⟨x, Or.inr hx⟩ : ↥(insert cG (compSet G cG C : Set V))) ≠ ⟨cG, Set.mem_insert _ _⟩ := by
        intro heq
        have heqv : x = cG := congrArg (fun z : ↥(insert cG (compSet G cG C : Set V)) => z.1) heq
        exact c_notMem_compSet G cG C (heqv ▸ hx)
      have h' : φC C ⟨x, Or.inr hx⟩ = φC C ⟨cG, Set.mem_insert _ _⟩ := by
        apply Subtype.ext
        rw [h, hφC_root C]
      exact False.elim (hne ((φC C).injective h'))
    · exact h
  have hφC_symm_root (C : (G.induce {cG}ᶜ).ConnectedComponent) :
      ((φC C).symm ⟨cH, Set.mem_insert _ _⟩).1 = cG := by
    have h1 : φC C ⟨cG, Set.mem_insert _ _⟩ = ⟨cH, Set.mem_insert _ _⟩ :=
      Subtype.ext (hφC_root C)
    exact congrArg Subtype.val ((φC C).symm_apply_apply ⟨cG, Set.mem_insert _ _⟩ ▸
      congrArg (φC C).symm h1.symm)
  have hφC_symm_mem (C : (G.induce {cG}ᶜ).ConnectedComponent) (y : W) (hy : y ∈ compSet H cH (e C)) :
      ((φC C).symm ⟨y, Or.inr hy⟩).1 ∈ compSet G cG C := by
    have hmem := ((φC C).symm ⟨y, Or.inr hy⟩).2
    rcases mem_insert_iff.mp hmem with h | h
    · have hne : (⟨y, Or.inr hy⟩ : ↥(insert cH (compSet H cH (e C) : Set W))) ≠ ⟨cH, Set.mem_insert _ _⟩ := by
        intro heq
        have heqv : y = cH := congrArg (fun z : ↥(insert cH (compSet H cH (e C) : Set W)) => z.1) heq
        exact c_notMem_compSet H cH (e C) (heqv ▸ hy)
      have h' : (φC C).symm ⟨y, Or.inr hy⟩ = (φC C).symm ⟨cH, Set.mem_insert _ _⟩ := by
        apply Subtype.ext
        rw [h, hφC_symm_root C]
      exact False.elim (hne ((φC C).symm.injective h'))
    · exact h
  let f : V → W := fun v =>
    if hv : v = cG then cH
    else
      let C := compG v hv
      have hx : v ∈ compSet G cG C := (mem_compSet_iff G cG C v).mpr ⟨hv, rfl⟩
      (φC C ⟨v, Or.inr hx⟩).1
  let g : W → V := fun w =>
    if hw : w = cH then cG
    else
      let D := compH w hw
      let C := e.symm D
      have hy : w ∈ compSet H cH (e C) := by
        rw [e.apply_symm_apply]
        exact (mem_compSet_iff H cH D w).mpr ⟨hw, rfl⟩
      ((φC C).symm ⟨w, Or.inr hy⟩).1
  have hcomp_f : ∀ v (hv : v ≠ cG), f v ≠ cH ∧ compH (f v) (by
      dsimp only [f]; rw [dif_neg hv]
      have hx := (mem_compSet_iff G cG (compG v hv) v).mpr ⟨hv, rfl⟩
      have hx' := hφC_mem (compG v hv) v hx
      exact fun h => c_notMem_compSet H cH (e (compG v hv)) (by rwa [h] at hx')) = e (compG v hv) := by
    intro v hv
    have hx : v ∈ compSet G cG (compG v hv) := (mem_compSet_iff G cG (compG v hv) v).mpr ⟨hv, rfl⟩
    have hm := hφC_mem (compG v hv) v hx
    have hfv : f v = (φC (compG v hv) ⟨v, Or.inr hx⟩).1 := dif_neg hv
    rw [← hfv] at hm
    obtain ⟨hne, hsupp⟩ := (mem_compSet_iff H cH (e (compG v hv)) (f v)).mp hm
    exact ⟨hne, (mem_supp_iff (e (compG v hv)) _).mp hsupp⟩
  have hleft : LeftInverse g f := by
    intro v
    by_cases hv : v = cG
    · subst hv; simp [f, g]
    · have hf := hcomp_f v hv
      have hx : v ∈ compSet G cG (compG v hv) := (mem_compSet_iff G cG (compG v hv) v).mpr ⟨hv, rfl⟩
      have hfv : f v = (φC (compG v hv) ⟨v, Or.inr hx⟩).1 := dif_neg hv
      dsimp only [g]
      rw [dif_neg hf.1]
      have hceq : e.symm (compH (f v) hf.1) = compG v hv := by rw [hf.2, e.symm_apply_apply]
      have hD : ∀ (C : (G.induce {cG}ᶜ).ConnectedComponent)
          (_hC : C = compG v hv) (w : W) (_hw : w = (φC (compG v hv) ⟨v, Or.inr hx⟩).1)
          (hy : w ∈ compSet H cH (e C)),
          ((φC C).symm ⟨w, Or.inr hy⟩).1 = v := by
        rintro C rfl w rfl hy
        exact congrArg Subtype.val ((φC (compG v hv)).left_inv ⟨v, Or.inr hx⟩)
      exact hD (e.symm (compH (f v) hf.1)) hceq (f v) hfv
        (by rw [e.apply_symm_apply]; exact (mem_compSet_iff H cH (compH (f v) hf.1) (f v)).mpr ⟨hf.1, rfl⟩)
  have hright : RightInverse g f := by
    intro w
    by_cases hw : w = cH
    · subst hw; simp [f, g]
    · dsimp only [g]
      rw [dif_neg hw]
      let D := compH w hw
      let C := e.symm D
      have hy : w ∈ compSet H cH (e C) := by
        rw [e.apply_symm_apply]
        exact (mem_compSet_iff H cH D w).mpr ⟨hw, rfl⟩
      have hmg := hφC_symm_mem C w hy
      obtain ⟨hne, hsupp⟩ := (mem_compSet_iff G cG C _).mp hmg
      have hc_eq : compG ((φC C).symm ⟨w, Or.inr hy⟩).1 hne = C :=
        (mem_supp_iff C _).mp hsupp
      dsimp only [f]
      rw [dif_neg hne]
      have hD : ∀ (C' : (G.induce {cG}ᶜ).ConnectedComponent)
          (hC' : C' = C) (hx' : _ ∈ compSet G cG C'),
          (φC C' ⟨((φC C).symm ⟨w, Or.inr hy⟩).1, Or.inr hx'⟩).1 = w := by
        rintro C' rfl hx'
        exact congrArg Subtype.val ((φC C).right_inv ⟨w, Or.inr hy⟩)
      exact hD (compG ((φC C).symm ⟨w, Or.inr hy⟩).1 hne) hc_eq (by rw [hc_eq]; exact hmg)
  refine ⟨⟨⟨f, g, hleft, hright⟩, ?_⟩⟩
  intro a b
  by_cases ha : a = cG <;> by_cases hb : b = cG
  · rw [ha, hb]; simp [f]
  · rw [ha]
    have hf_b := hcomp_f b hb
    have hfb_mem : f b ∈ compSet H cH (e (compG b hb)) :=
      (mem_compSet_iff H cH _ _).mpr ⟨hf_b.1, (mem_supp_iff _ _).mpr hf_b.2⟩
    have hc_f : f cG = cH := by simp [f]
    change H.Adj (f cG) (f b) ↔ G.Adj cG b
    rw [hc_f]
    have h1 : G.Adj cG b ↔ (G.induce (insert cG (compSet G cG (compG b hb) : Set V))).Adj
        ⟨cG, Set.mem_insert _ _⟩ ⟨b, Or.inr ((mem_compSet_iff G cG _ b).mpr ⟨hb, rfl⟩)⟩ := Iff.rfl
    have h2 := (φC (compG b hb)).map_rel_iff
      (a := ⟨cG, Set.mem_insert _ _⟩)
      (b := ⟨b, Or.inr ((mem_compSet_iff G cG _ b).mpr ⟨hb, rfl⟩)⟩)
    have hr1 : φC (compG b hb) ⟨cG, Set.mem_insert _ _⟩ = ⟨cH, Set.mem_insert _ _⟩ :=
      Subtype.ext (hφC_root (compG b hb))
    have hr2 : φC (compG b hb) ⟨b, Or.inr ((mem_compSet_iff G cG _ b).mpr ⟨hb, rfl⟩)⟩ =
        ⟨f b, Or.inr hfb_mem⟩ := by
      apply Subtype.ext
      dsimp only [f]
      rw [dif_neg hb]
    rw [hr1, hr2] at h2
    exact h2.trans h1.symm
  · rw [hb]
    have hf_a := hcomp_f a ha
    have hfa_mem : f a ∈ compSet H cH (e (compG a ha)) :=
      (mem_compSet_iff H cH _ _).mpr ⟨hf_a.1, (mem_supp_iff _ _).mpr hf_a.2⟩
    have hc_f : f cG = cH := by simp [f]
    change H.Adj (f a) (f cG) ↔ G.Adj a cG
    rw [hc_f]
    have h1 : G.Adj a cG ↔ (G.induce (insert cG (compSet G cG (compG a ha) : Set V))).Adj
        ⟨a, Or.inr ((mem_compSet_iff G cG _ a).mpr ⟨ha, rfl⟩)⟩ ⟨cG, Set.mem_insert _ _⟩ := Iff.rfl
    have h2 := (φC (compG a ha)).map_rel_iff
      (a := ⟨a, Or.inr ((mem_compSet_iff G cG _ a).mpr ⟨ha, rfl⟩)⟩)
      (b := ⟨cG, Set.mem_insert _ _⟩)
    have hr1 : φC (compG a ha) ⟨cG, Set.mem_insert _ _⟩ = ⟨cH, Set.mem_insert _ _⟩ :=
      Subtype.ext (hφC_root (compG a ha))
    have hr2 : φC (compG a ha) ⟨a, Or.inr ((mem_compSet_iff G cG _ a).mpr ⟨ha, rfl⟩)⟩ =
        ⟨f a, Or.inr hfa_mem⟩ := by
      apply Subtype.ext
      dsimp only [f]
      rw [dif_neg ha]
    rw [hr1, hr2] at h2
    exact h2.trans h1.symm
  · have ha_mem : a ∈ compSet G cG (compG a ha) := (mem_compSet_iff G cG _ a).mpr ⟨ha, rfl⟩
    have hb_mem : b ∈ compSet G cG (compG b hb) := (mem_compSet_iff G cG _ b).mpr ⟨hb, rfl⟩
    have hfa := hcomp_f a ha
    have hfb := hcomp_f b hb
    by_cases hCeq : compG a ha = compG b hb
    · have hb_mem' : b ∈ compSet G cG (compG a ha) := hCeq ▸ hb_mem
      have h1 : G.Adj a b ↔ (G.induce (insert cG (compSet G cG (compG a ha) : Set V))).Adj
          ⟨a, Or.inr ha_mem⟩ ⟨b, Or.inr hb_mem'⟩ := Iff.rfl
      have h2 := (φC (compG a ha)).map_rel_iff
        (a := ⟨a, Or.inr ha_mem⟩) (b := ⟨b, Or.inr hb_mem'⟩)
      have hfa_v : (φC (compG a ha) ⟨a, Or.inr ha_mem⟩).1 = f a := by
        dsimp only [f]; rw [dif_neg ha]
      have hfb_v : (φC (compG a ha) ⟨b, Or.inr hb_mem'⟩).1 = f b := by
        dsimp only [f]; rw [dif_neg hb]
        have hC_fun : ∀ (C : (G.induce {cG}ᶜ).ConnectedComponent) (hC : compG b hb = C)
            (hmem : b ∈ compSet G cG C),
            (φC C ⟨b, Or.inr hmem⟩).1 = (φC (compG b hb) ⟨b, Or.inr hb_mem⟩).1 := by
          rintro C rfl hmem; rfl
        exact hC_fun (compG a ha) hCeq.symm hb_mem'
      change H.Adj (φC (compG a ha) ⟨a, Or.inr ha_mem⟩).1 (φC (compG a ha) ⟨b, Or.inr hb_mem'⟩).1 ↔
        (G.induce (insert cG (compSet G cG (compG a ha) : Set V))).Adj ⟨a, Or.inr ha_mem⟩ ⟨b, Or.inr hb_mem'⟩ at h2
      rw [hfa_v, hfb_v] at h2
      exact h2.trans h1.symm
    · constructor
      · intro hadjH
        have hfa_mem' : f a ∈ compSet H cH (e (compG a ha)) :=
          (mem_compSet_iff H cH _ _).mpr ⟨hfa.1, (mem_supp_iff _ _).mpr hfa.2⟩
        have hfb_mem' : f b ∈ compSet H cH (e (compG b hb)) :=
          (mem_compSet_iff H cH _ _).mpr ⟨hfb.1, (mem_supp_iff _ _).mpr hfb.2⟩
        exact False.elim (hCeq (e.injective (adj_compSet_eq H cH hfa_mem' hfb_mem' hadjH)))
      · intro hadj
        exact False.elim (hCeq (adj_compSet_eq G cG ha_mem hb_mem hadj))
private lemma comp_noLeaf_card_ge_two {U : Type} [Fintype U] (T : SimpleGraph U) (hT : T.IsTree)
    (c : U) (hnoLeaf : ∀ u : U, T.Adj c u → 2 ≤ T.degree u)
    (C : (T.induce {c}ᶜ).ConnectedComponent) : 2 ≤ card C.supp := by
  obtain ⟨u, ⟨hu_mem, hu_adj⟩, _⟩ := existsUnique_root_of_component T hT c C
  let uC : C.supp := ⟨u, hu_mem⟩
  have h1 := degree_induce_compl_singleton_of_adj T u.2 hu_adj.symm
  rw [coe_eta] at h1
  have hu2 : 2 ≤ T.degree u.1 := hnoLeaf u.1 hu_adj
  have hdegC : 1 ≤ C.toSimpleGraph.degree uC := by
    rw [component_toSimpleGraph_degree T c C uC]
    dsimp only [uC]
    omega
  rw [← C.toSimpleGraph.card_neighborFinset_eq_degree] at hdegC
  obtain ⟨y, hy⟩ := card_pos.mp hdegC
  rw [mem_neighborFinset] at hy
  have hne : uC ≠ y := hy.ne
  exact Fintype.one_lt_card_iff.mpr ⟨uC, y, hne⟩
private lemma comp_dist_ge_of_mem {U : Type} [Fintype U] (T : SimpleGraph U) (hT : T.IsTree)
    (c : U) (C : (T.induce {c}ᶜ).ConnectedComponent) {x : ({c}ᶜ : Set U)} (hx : x ∈ C.supp) :
    T.dist c x.1 ≤ card C.supp := by
  obtain ⟨p, hp, hplen⟩ := hT.connected.exists_path_of_dist c x.1
  have hnp : ¬ p.Nil := not_nil_of_ne (Ne.symm x.2)
  have p_tail_supp : ∀ y ∈ p.tail.support, y ∈ ({c}ᶜ : Set U) := by
    intro y hy
    rw [support_tail_of_not_nil p hnp] at hy
    exact mem_compl_singleton_iff.mpr fun hyc =>
      start_notMem_tail_support_of_isPath hp (hyc ▸ hy)
  have hall_C : ∀ y ∈ p.tail.support, ∃ h : y ∈ ({c}ᶜ : Set U), ⟨y, h⟩ ∈ C.supp := by
    intro y hy
    refine ⟨p_tail_supp y hy, ?_⟩
    have hy_map : y ∈ ((p.tail.induce ({c}ᶜ : Set U) p_tail_supp).map
        (Embedding.induce ({c}ᶜ : Set U)).toHom).support := by
      rw [Walk.map_induce]; exact hy
    rw [Walk.support_map, List.mem_map] at hy_map
    obtain ⟨y', hy', hy'_eq⟩ := hy_map
    obtain ⟨_, q2, _⟩ := Walk.mem_support_iff_exists_append.mp hy'
    have hreach : (T.induce {c}ᶜ).Reachable ⟨y, p_tail_supp y hy⟩ x :=
      ⟨q2.copy (Subtype.ext hy'_eq) (Subtype.ext rfl)⟩
    rw [mem_supp_iff] at hx ⊢
    exact (sound hreach).trans hx
  let S : Finset C.supp := p.tail.support.toFinset.attach.map
    ⟨fun ⟨y, hy⟩ => ⟨⟨y, (hall_C y (List.mem_toFinset.mp hy)).choose⟩,
      (hall_C y (List.mem_toFinset.mp hy)).choose_spec⟩, by
      intro ⟨a, _⟩ ⟨b, _⟩ hab
      exact Subtype.ext (congrArg (fun z : C.supp => z.1.1) hab)⟩
  have hScard : S.card ≤ card C.supp := card_le_univ S
  have hnodup : p.tail.support.Nodup := hp.tail.support_nodup
  have hS_eq : S.card = p.tail.support.length := by
    rw [card_map, card_attach, List.toFinset_card_of_nodup hnodup]
  rw [Walk.length_support, length_tail, hplen] at hS_eq
  omega
private lemma comp_path_of_card_eq_dist {U : Type} [Fintype U] (T : SimpleGraph U) (hT : T.IsTree)
    (c : U) (C : (T.induce {c}ᶜ).ConnectedComponent) {x : ({c}ᶜ : Set U)} (hx : x ∈ C.supp)
    {r : ℕ} (hdist : T.dist c x.1 = r) (hcard : card C.supp = r) :
    ∃ (p : T.Walk c x.1), p.IsPath ∧ p.length = r ∧ p.support.toFinset = insert c (compSet T c C) := by
  obtain ⟨p, hp, hplen⟩ := hT.connected.exists_path_of_dist c x.1
  have hp_len : p.length = r := hplen.trans hdist
  have hnp : ¬ p.Nil := not_nil_of_ne (Ne.symm x.2)
  have p_tail_supp : ∀ y ∈ p.tail.support, y ∈ ({c}ᶜ : Set U) := by
    intro y hy
    rw [support_tail_of_not_nil p hnp] at hy
    exact mem_compl_singleton_iff.mpr fun hyc =>
      start_notMem_tail_support_of_isPath hp (hyc ▸ hy)
  have hsub : p.support.toFinset ⊆ insert c (compSet T c C) := by
    intro y hy
    rw [List.mem_toFinset] at hy
    by_cases hyc : y = c
    · rw [hyc]; exact mem_insert_self c _
    · refine mem_insert_of_mem ((mem_compSet_iff T c C y).mpr ⟨hyc, ?_⟩)
      have hyt : y ∈ p.tail.support := by
        rw [support_tail_of_not_nil p hnp]
        exact mem_support_tail_of_ne p hy hyc
      have hyt' : y ∈ ((p.tail.induce ({c}ᶜ : Set U) p_tail_supp).map
          (Embedding.induce ({c}ᶜ : Set U)).toHom).support := by
        rw [Walk.map_induce]; exact hyt
      rw [Walk.support_map, List.mem_map] at hyt'
      obtain ⟨y', hy', hy'_eq⟩ := hyt'
      obtain ⟨_, q2, _⟩ := Walk.mem_support_iff_exists_append.mp hy'
      have hreach : (T.induce {c}ᶜ).Reachable ⟨y, p_tail_supp y hyt⟩ x :=
        ⟨q2.copy (Subtype.ext hy'_eq) (Subtype.ext rfl)⟩
      rw [mem_supp_iff] at hx ⊢
      exact (sound hreach).trans hx
  have hcard_p : p.support.toFinset.card = r + 1 := by
    rw [List.toFinset_card_of_nodup hp.support_nodup, p.length_support, hp_len]
  have hcard_ins : (insert c (compSet T c C)).card = r + 1 := by
    rw [card_insert_of_notMem (c_notMem_compSet T c C), compSet_card_eq, hcard]
  exact ⟨p, hp, hp_len, eq_of_subset_of_card_le hsub (by omega)⟩
private lemma comp_unique_dist_r_of_card_eq_r {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) (c : U) (C : (T.induce {c}ᶜ).ConnectedComponent)
    {r : ℕ} (hr : 1 ≤ r) (hecc : T.eccent c = r) (hcard : card C.supp = r) :
    ∀ x ∈ C.supp, T.dist c x.1 = r → ∃! z : C.supp, T.dist c z.1.1 = r := by
  intro x hx hxd
  obtain ⟨p, hp, hplen, hfin⟩ := comp_path_of_card_eq_dist T hT c C hx hxd hcard
  refine ⟨⟨x, hx⟩, hxd, fun z hz => ?_⟩
  have hz_mem : z.1.1 ∈ p.support := by
    rw [← List.mem_toFinset, hfin, mem_insert]
    exact Or.inr ((mem_compSet_iff T c C z.1.1).mpr ⟨z.1.2, z.2⟩)
  obtain ⟨q₁, q₂, hq1, _, hpeq⟩ := hp.mem_support_iff_exists_append.mp hz_mem
  have hq1_len : q₁.length = r := by
    rw [isTree_dist_eq_length_of_isPath T hT q₁ hq1, hz]
  have hsum := congrArg Walk.length hpeq
  rw [length_append, hplen, hq1_len] at hsum
  have hq2_len : q₂.length = 0 := by omega
  have heq : z.1.1 = x.1 := by
    have h0 : ∀ {a b : U} (w : T.Walk a b), w.length = 0 → a = b := fun w hw => by
      cases w
      · rfl
      · simp at hw
    exact h0 q₂ hq2_len
  exact Subtype.ext (Subtype.ext heq)
private lemma dist_comp_le_card {U : Type} [Fintype U] (T : SimpleGraph U) (hT : T.IsTree)
    (c : U) (C : (T.induce {c}ᶜ).ConnectedComponent) (x : U) :
    ∀ y ∈ compSet T c C, T.dist c y ≤ card C.supp := by
  intro y hy
  obtain ⟨hne, hsupp⟩ := (mem_compSet_iff T c C y).mp hy
  exact comp_dist_ge_of_mem T hT c C hsupp
private lemma component_two_leaves_of_radius_lt_card {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {r : ℕ} (hr : 2 ≤ r) (c : U)
    (hecc : T.eccent c = r) (C : (T.induce {c}ᶜ).ConnectedComponent)
    (hcard : r + 1 ≤ card C.supp) :
    2 ≤ (univ.filter fun x : C.supp => T.degree x.1.1 = 1).card := by
  obtain ⟨hLC_eq, hge2⟩ := component_leaves_formula T hT c C
  let LC : Finset C.supp := univ.filter fun x : C.supp => T.degree x.1.1 = 1
  by_contra hlt
  have hLC1 : LC.card = 1 := by dsimp only [LC] at hLC_eq ⊢; omega
  obtain ⟨x_end, hx_eq⟩ := Finset.card_eq_one.mp hLC1
  have h_all_le2 : ∀ x : C.supp, T.degree x.1.1 ≤ 2 := by
    intro x
    by_cases hx : x ∈ LC
    · simp only [LC, mem_filter, mem_univ, true_and] at hx; omega
    · have := hLC_eq
      change LC.card = 1 + ∑ y ∈ LCᶜ, (T.degree y.1.1 - 2) at this
      have hzero : ∑ y ∈ LCᶜ, (T.degree y.1.1 - 2) = 0 := by omega
      have hx_c : x ∈ LCᶜ := Finset.mem_compl.mpr hx
      have hle0 : T.degree x.1.1 - 2 = 0 :=
        (Finset.sum_eq_zero_iff.mp hzero) x hx_c
      omega
  have hx_end_mem : x_end ∈ LC := by rw [hx_eq]; exact Finset.mem_singleton_self _
  have hx_deg1 : T.degree x_end.1.1 = 1 := (mem_filter.mp hx_end_mem).2
  have hx_dist : T.dist c x_end.1.1 ≤ r := dist_le_of_eccent T hT hecc
  obtain ⟨u, ⟨hu_mem, hu_adj⟩, _⟩ := existsUnique_root_of_component T hT c C
  let uC : C.supp := ⟨u, hu_mem⟩
  have hC_tree : C.toSimpleGraph.IsTree := (hT.isAcyclic.induce {c}ᶜ).isTree_connectedComponent C
  have hnt : Nontrivial C.supp := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hC_deg_u : 1 ≤ C.toSimpleGraph.degree uC := hC_tree.preconnected.degree_pos_of_nontrivial uC
  have hux_ne : uC ≠ x_end := by
    intro h
    rw [component_toSimpleGraph_degree T c C uC] at hC_deg_u
    dsimp only [uC] at hC_deg_u
    have h1 := degree_induce_compl_singleton_of_adj T u.2 hu_adj.symm
    rw [coe_eta] at h1
    have hu_deg2 : T.degree u.1 ≥ 2 := by omega
    have hval : u.1 = x_end.1.1 := congrArg (fun y : C.supp => y.1.1) h
    rw [hval] at hu_deg2
    omega
  obtain ⟨p, hp, hplen⟩ := hT.connected.exists_path_of_dist c x_end.1.1
  have hnp : ¬ p.Nil := not_nil_of_ne (Ne.symm x_end.1.2)
  have p_tail_supp : ∀ y ∈ p.tail.support, y ∈ ({c}ᶜ : Set U) := by
    intro y hy
    rw [support_tail_of_not_nil p hnp] at hy
    exact mem_compl_singleton_iff.mpr fun hyc => start_notMem_tail_support_of_isPath hp (hyc ▸ hy)
  obtain ⟨pC, hpC, hpClen⟩ := hC_tree.connected.exists_path_of_dist uC x_end
  have hdist_u_x : C.toSimpleGraph.dist uC x_end ≤ T.dist c x_end.1.1 - 1 := by
    let p_tail := p.tail.induce ({c}ᶜ : Set U) p_tail_supp
    have hp_tail_path : p_tail.IsPath := by
      refine Walk.IsPath.of_map (f := (Embedding.induce ({c}ᶜ : Set U)).toHom) ?_
      rw [Walk.map_induce]; exact hp.tail
    have hmem_C : ∀ z ∈ p_tail.support, z ∈ C.supp := by
      intro z hz
      obtain ⟨_, q2, _⟩ := Walk.mem_support_iff_exists_append.mp hz
      have hreach : (T.induce {c}ᶜ).Reachable z x_end.1 := ⟨q2.copy rfl (Subtype.ext rfl)⟩
      rw [mem_supp_iff]
      exact (sound hreach).trans ((mem_supp_iff C x_end.1).mp x_end.2)
    have hu_eq_snd : (⟨p.snd, p_tail_supp p.snd (Walk.start_mem_support _)⟩ : ({c}ᶜ : Set U)) = u := by
      have hu_mem' : (⟨p.snd, p_tail_supp p.snd (Walk.start_mem_support _)⟩ : ({c}ᶜ : Set U)) ∈ C.supp :=
        hmem_C _ (Walk.start_mem_support _)
      exact (existsUnique_root_of_component T hT c C).choose_spec.2 _ ⟨hu_mem', p.adj_snd hnp⟩ |>.trans
        ((existsUnique_root_of_component T hT c C).choose_spec.2 u ⟨hu_mem, hu_adj⟩).symm
    let pC_raw : ((T.induce {c}ᶜ).induce C.supp).Walk ⟨u, hu_mem⟩ x_end :=
      (p_tail.induce C.supp hmem_C).copy (Subtype.ext hu_eq_snd) (Subtype.ext rfl)
    have hlen_raw : pC_raw.length = T.dist c x_end.1.1 - 1 := by
      dsimp only [pC_raw, p_tail]
      rw [length_copy, length_walk_induce, length_walk_induce, length_tail, hplen]
    have h1 : C.toSimpleGraph.dist uC x_end ≤ pC_raw.length := C.toSimpleGraph.dist_le pC_raw
    omega
  have hdeg_uC : C.toSimpleGraph.degree uC = 1 := by
    rw [component_toSimpleGraph_degree T c C uC]
    rw [component_toSimpleGraph_degree T c C uC] at hC_deg_u
    dsimp only [uC]
    dsimp only [uC] at hC_deg_u
    have h1 := degree_induce_compl_singleton_of_adj T u.2 hu_adj.symm
    rw [coe_eta] at h1
    have h2 := h_all_le2 uC
    dsimp only [uC] at h2
    omega
  have hdeg_xC : C.toSimpleGraph.degree x_end = 1 := by
    rw [component_toSimpleGraph_degree T c C x_end]
    have h2 := degree_induce_compl_le T x_end.1.2
    rw [coe_eta] at h2
    have hpos := hC_tree.preconnected.degree_pos_of_nontrivial x_end
    rw [component_toSimpleGraph_degree T c C x_end] at hpos
    omega
  have hsupp_all : ∀ y : C.supp, y ∈ pC.support := by
    intro y
    by_contra hy
    obtain ⟨q, _, _⟩ := hC_tree.connected.exists_path_of_dist y uC
    obtain ⟨z, q₁, _, hz_mem, _, hq_first⟩ :=
      split_walk_first_mem C.toSimpleGraph {w | w ∈ pC.support} q pC.start_mem_support
    have hq1_nn : ¬ q₁.Nil := not_nil_of_ne (fun h => hy (h ▸ hz_mem))
    have hadj_z : C.toSimpleGraph.Adj z q₁.penultimate := (q₁.adj_penultimate hq1_nn).symm
    have hpen_not : q₁.penultimate ∉ pC.support := fun hm =>
      C.toSimpleGraph.ne_of_adj hadj_z (hq_first q₁.penultimate (getVert_mem_support q₁ _) hm).symm
    by_cases hzu : z = uC
    · have hadj_q : C.toSimpleGraph.Adj uC q₁.penultimate := hzu ▸ hadj_z
      have hpC_nn : ¬ pC.Nil := not_nil_of_ne hux_ne
      have hadj_p := pC.adj_snd hpC_nn
      have hne : pC.snd ≠ q₁.penultimate := fun h =>
        hpen_not (h ▸ List.mem_of_mem_tail (pC.snd_mem_tail_support hpC_nn))
      have h2 : 2 ≤ C.toSimpleGraph.degree uC := by
        rw [← C.toSimpleGraph.card_neighborFinset_eq_degree]
        have hsub : {pC.snd, q₁.penultimate} ⊆ C.toSimpleGraph.neighborFinset uC := fun a ha => by
          simp only [mem_insert, mem_singleton] at ha
          rw [mem_neighborFinset]
          rcases ha with rfl | rfl <;> assumption
        exact (card_pair hne).symm ▸ card_le_card hsub
      omega
    · by_cases hzx : z = x_end
      · have hadj_q : C.toSimpleGraph.Adj x_end q₁.penultimate := hzx ▸ hadj_z
        have hpC_nn : ¬ pC.Nil := not_nil_of_ne hux_ne
        have hadj_p := (pC.adj_penultimate hpC_nn).symm
        have hne : pC.penultimate ≠ q₁.penultimate := fun h =>
          hpen_not (h ▸ getVert_mem_support pC _)
        have h2 : 2 ≤ C.toSimpleGraph.degree x_end := by
          rw [← C.toSimpleGraph.card_neighborFinset_eq_degree]
          have hsub : {pC.penultimate, q₁.penultimate} ⊆ C.toSimpleGraph.neighborFinset x_end := fun a ha => by
            simp only [mem_insert, mem_singleton] at ha
            rw [mem_neighborFinset]
            rcases ha with rfl | rfl <;> assumption
          exact (card_pair hne).symm ▸ card_le_card hsub
        omega
      · obtain ⟨a, b, _, _, hpC_eq⟩ := hpC.mem_support_iff_exists_append.mp hz_mem
        have ha_nn : ¬ a.Nil := not_nil_of_ne (fun h => hzu h.symm)
        have hb_nn : ¬ b.Nil := not_nil_of_ne hzx
        have hadj1 : C.toSimpleGraph.Adj z a.penultimate := (a.adj_penultimate ha_nn).symm
        have hadj2 : C.toSimpleGraph.Adj z b.snd := b.adj_snd hb_nn
        have hm1 : a.penultimate ∈ pC.support :=
          hpC_eq ▸ Walk.support_subset_support_append_left a b (getVert_mem_support a _)
        have hm2 : b.snd ∈ pC.support :=
          hpC_eq ▸ Walk.support_subset_support_append_right a b
            (List.mem_of_mem_tail (b.snd_mem_tail_support hb_nn))
        have hne12 : a.penultimate ≠ b.snd := by
          have hdisj : a.support.Disjoint b.tail.support := by
            have h1 := (hpC_eq ▸ hpC).support_nodup
            rw [Walk.support_append, List.nodup_append', ← support_tail_of_not_nil b hb_nn] at h1
            exact h1.2.2
          have ha_pen : a.penultimate ∈ a.support := getVert_mem_support a (a.length - 1)
          intro heq
          rw [heq] at ha_pen
          exact hdisj ha_pen
            (by rw [support_tail_of_not_nil b hb_nn]; exact b.snd_mem_tail_support hb_nn)
        have hne13 : a.penultimate ≠ q₁.penultimate := fun h => hpen_not (h ▸ hm1)
        have hne23 : b.snd ≠ q₁.penultimate := fun h => hpen_not (h ▸ hm2)
        have h3 : 3 ≤ C.toSimpleGraph.degree z := by
          rw [← C.toSimpleGraph.card_neighborFinset_eq_degree]
          have hsub : {a.penultimate, b.snd, q₁.penultimate} ⊆ C.toSimpleGraph.neighborFinset z := fun w hw => by
            simp only [mem_insert, mem_singleton] at hw
            rw [mem_neighborFinset]
            rcases hw with rfl | rfl | rfl <;> assumption
          have hc3 : ({a.penultimate, b.snd, q₁.penultimate} : Finset C.supp).card = 3 := by
            rw [card_insert_of_notMem, card_pair hne23]
            simp [hne12, hne13]
          exact hc3 ▸ card_le_card hsub
        have h4 := (component_toSimpleGraph_degree T c C z).symm ▸
          (degree_induce_compl_le T z.1.2).trans (h_all_le2 z)
        omega
  have hcard_le : card C.supp ≤ pC.length + 1 := by
    have h1 : card C.supp = pC.support.length := by
      calc card C.supp
          = card {x // x ∈ pC.support.toFinset} :=
              card_congr ⟨fun x => ⟨x, List.mem_toFinset.mpr (hsupp_all x)⟩,
                fun x => x.1, fun _ => rfl, fun _ => Subtype.ext rfl⟩
        _ = pC.support.toFinset.card := card_coe _
        _ = pC.support.length := List.toFinset_card_of_nodup hpC.support_nodup
    rw [pC.length_support] at h1
    omega
  omega
private lemma comp_exists_good_leaf_of_radius_lt_card {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {r : ℕ} (hr : 2 ≤ r) (hdiam : T.diam = 2 * r)
    (c : U) (hecc : T.eccent c = r) (C : (T.induce {c}ᶜ).ConnectedComponent)
    (hcard : r + 1 ≤ card C.supp) :
    ∃ v : U, v ∈ compSet T c C ∧ T.degree v = 1 ∧ (T.induce {v}ᶜ).diam = 2 * r := by
  have : Nonempty U := hT.connected.nonempty
  obtain ⟨x0, xd, hxd⟩ := T.exists_dist_eq_diam
  obtain ⟨p, hp, hplen⟩ := hT.connected.exists_path_of_dist x0 xd
  have hxd_r : T.dist x0 xd = 2 * r := hxd.trans hdiam
  obtain ⟨hc_mem, hcx0, hcxd⟩ := diam_path_contains_center T hT c hecc p hp (hplen.trans hxd_r)
  have hx0_ne : x0 ≠ c := fun h => by rw [← h, dist_self] at hcx0; omega
  have hxd_ne : xd ≠ c := fun h => by rw [← h, dist_self] at hcxd; omega
  let x0' : ({c}ᶜ : Set U) := ⟨x0, hx0_ne⟩
  let xd' : ({c}ᶜ : Set U) := ⟨xd, hxd_ne⟩
  have hne_comp : (T.induce {c}ᶜ).connectedComponentMk x0' ≠
      (T.induce {c}ᶜ).connectedComponentMk xd' := by
    intro heq
    obtain ⟨q⟩ := ConnectedComponent.exact heq
    let q_path := q.toPath
    let g : T.induce {c}ᶜ →g T := (Embedding.induce ({c}ᶜ : Set U)).toHom
    have hqG : (q_path.val.map g).IsPath := q_path.isPath.map val_injective
    have hqp := isTree_path_eq T hT hqG hp
    have hc_not : c ∉ (q_path.val.map g).support := by
      rw [Walk.support_map, List.mem_map]
      rintro ⟨y, _, hyc⟩; exact y.2 hyc
    rw [hqp] at hc_not
    exact hc_not hc_mem
  have hLC := component_two_leaves_of_radius_lt_card T hT hr c hecc C hcard
  let LC := univ.filter fun x : C.supp => T.degree x.1.1 = 1
  have hLC_card : 2 ≤ LC.card := hLC
  have hdiff : ∃ v : C.supp, v ∈ LC ∧ v.1.1 ≠ x0 ∧ v.1.1 ≠ xd := by
    by_cases hx0_C : x0' ∈ C.supp
    · have hxd_not : xd' ∉ C.supp := fun h => hne_comp
        (((mem_supp_iff C x0').mp hx0_C).trans
          ((mem_supp_iff C xd').mp h).symm)
      have hsub : LC ⊆ (LC.erase ⟨x0', hx0_C⟩) ∪ {⟨x0', hx0_C⟩} := fun z hz =>
        if hz0 : z = ⟨x0', hx0_C⟩ then mem_union_right _ (mem_singleton.mpr hz0)
        else mem_union_left _ (mem_erase.mpr ⟨hz0, hz⟩)
      have hcard_er : 0 < (LC.erase ⟨x0', hx0_C⟩).card := by
        have h1 := (card_le_card hsub).trans (Finset.card_union_le _ _)
        simp only [card_singleton] at h1
        omega
      obtain ⟨v, hv⟩ := card_pos.mp hcard_er
      obtain ⟨hvne, hvLC⟩ := mem_erase.mp hv
      refine ⟨v, hvLC, fun h => hvne (Subtype.ext (Subtype.ext h)), fun h => hxd_not ?_⟩
      exact (Subtype.ext h.symm : xd' = v.1) ▸ v.2
    · by_cases hxd_C : xd' ∈ C.supp
      · have hsub : LC ⊆ (LC.erase ⟨xd', hxd_C⟩) ∪ {⟨xd', hxd_C⟩} := fun z hz =>
          if hzd : z = ⟨xd', hxd_C⟩ then mem_union_right _ (mem_singleton.mpr hzd)
          else mem_union_left _ (mem_erase.mpr ⟨hzd, hz⟩)
        have hcard_er : 0 < (LC.erase ⟨xd', hxd_C⟩).card := by
          have h1 := (card_le_card hsub).trans (Finset.card_union_le _ _)
          simp only [card_singleton] at h1
          omega
        obtain ⟨v, hv⟩ := card_pos.mp hcard_er
        obtain ⟨hvne, hvLC⟩ := mem_erase.mp hv
        refine ⟨v, hvLC, fun h => hx0_C ?_, fun h => hvne (Subtype.ext (Subtype.ext h))⟩
        exact (Subtype.ext h.symm : x0' = v.1) ▸ v.2
      · obtain ⟨v, hvLC⟩ := card_pos.mp (by omega : 0 < LC.card)
        refine ⟨v, hvLC, fun h => hx0_C ?_, fun h => hxd_C ?_⟩
        · exact (Subtype.ext h.symm : x0' = v.1) ▸ v.2
        · exact (Subtype.ext h.symm : xd' = v.1) ▸ v.2
  obtain ⟨v, hvLC, hvx0, hvxd⟩ := hdiff
  have hvdeg : T.degree v.1.1 = 1 := (mem_filter.mp hvLC).2
  exact ⟨v.1.1, (mem_compSet_iff T c C v.1.1).mpr ⟨v.1.2, v.2⟩, hvdeg,
    good_leaf_of_ne_diam_ends T hT hr hdiam hxd_r hvdeg hvx0 hvxd⟩
private lemma exists_other_diam_comp {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {r : ℕ} (hr : 2 ≤ r) (hdiam : T.diam = 2 * r)
    (c : U) (hecc : T.eccent c = r) (C₀ : (T.induce {c}ᶜ).ConnectedComponent) :
    ∃ C₁ : (T.induce {c}ᶜ).ConnectedComponent,
      C₁ ≠ C₀ ∧ ∃ x ∈ compSet T c C₁, T.dist c x = r := by
  have : Nonempty U := hT.connected.nonempty
  obtain ⟨x0, xd, hxd⟩ := T.exists_dist_eq_diam
  obtain ⟨p, hp, hplen⟩ := hT.connected.exists_path_of_dist x0 xd
  obtain ⟨hc_mem, hcx0, hcxd⟩ := diam_path_contains_center T hT c hecc p hp (hplen.trans (hxd.trans hdiam))
  have hx0_ne : x0 ≠ c := fun h => by rw [← h, dist_self] at hcx0; omega
  have hxd_ne : xd ≠ c := fun h => by rw [← h, dist_self] at hcxd; omega
  let C_x0 := (T.induce {c}ᶜ).connectedComponentMk ⟨x0, hx0_ne⟩
  let C_xd := (T.induce {c}ᶜ).connectedComponentMk ⟨xd, hxd_ne⟩
  have hne : C_x0 ≠ C_xd := by
    intro heq
    obtain ⟨q⟩ := ConnectedComponent.exact heq
    let q_path := q.toPath
    let g : T.induce {c}ᶜ →g T := (Embedding.induce ({c}ᶜ : Set U)).toHom
    have hqG : (q_path.val.map g).IsPath := q_path.isPath.map val_injective
    have hqp := isTree_path_eq T hT hqG hp
    have hc_not : c ∉ (q_path.val.map g).support := by
      rw [Walk.support_map, List.mem_map]; rintro ⟨y, _, hyc⟩; exact y.2 hyc
    rw [hqp] at hc_not
    exact hc_not hc_mem
  by_cases h1 : C_x0 = C₀
  · exact ⟨C_xd, fun h => hne (h1.trans h.symm), xd,
      (mem_compSet_iff T c C_xd xd).mpr ⟨hxd_ne, rfl⟩, hcxd⟩
  · exact ⟨C_x0, h1, x0, (mem_compSet_iff T c C_x0 x0).mpr ⟨hx0_ne, rfl⟩, hcx0⟩
private lemma maxComp_add_one_add_r_le_card {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {r : ℕ} (hr : 2 ≤ r) (hdiam : T.diam = 2 * r)
    (c : U) (hecc : T.eccent c = r) (C₀ : (T.induce {c}ᶜ).ConnectedComponent) :
    card C₀.supp + 1 + r ≤ card U := by
  obtain ⟨C₁, hne, x, hx_mem, hx_dist⟩ := exists_other_diam_comp T hT hr hdiam c hecc C₀
  obtain ⟨hxne, hxsupp⟩ := (mem_compSet_iff T c C₁ x).mp hx_mem
  have hr_le : r ≤ card C₁.supp := hx_dist ▸ comp_dist_ge_of_mem T hT c C₁ hxsupp
  have hsum := sum_card_connectedComponent_eq T c
  have hsub : card C₀.supp + card C₁.supp ≤
      ∑ C : (T.induce {c}ᶜ).ConnectedComponent, card C.supp := by
    have h1 := add_sum_erase univ (fun C : (T.induce {c}ᶜ).ConnectedComponent => card C.supp)
      (mem_univ C₀)
    have h2 : card C₁.supp ≤
        ∑ C ∈ univ.erase C₀, card C.supp :=
      single_le_sum (f := fun C : (T.induce {c}ᶜ).ConnectedComponent => card C.supp)
        (fun _ _ => Nat.zero_le _) (mem_erase.mpr ⟨hne, mem_univ _⟩)
    omega
  omega
/-! ### Part 3: Component matching under deleting a vertex not adjacent to center, plus boundary case -/
private def compl_compl_comm_iso {U : Type} (T : SimpleGraph U) (a b : U) (hab : a ≠ b) :
    (T.induce {a}ᶜ).induce ({⟨b, hab.symm⟩}ᶜ : Set ({a}ᶜ : Set U)) ≃g
    (T.induce {b}ᶜ).induce ({⟨a, hab⟩}ᶜ : Set ({b}ᶜ : Set U)) where
  toFun x := ⟨⟨x.1.1, fun h => x.2 (Subtype.ext h)⟩, fun h => x.1.2 (congrArg Subtype.val h)⟩
  invFun y := ⟨⟨y.1.1, fun h => y.2 (Subtype.ext h)⟩, fun h => y.1.2 (congrArg Subtype.val h)⟩
  left_inv x := rfl
  right_inv y := rfl
  map_rel_iff' := Iff.rfl
private lemma comp_erase_leaf_structure {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) (c : U)
    (hnoLeaf : ∀ u : U, T.Adj c u → 2 ≤ T.degree u)
    {v : U} (hv1 : T.degree v = 1) (hvc : v ≠ c)
    (C₀ : (T.induce {c}ᶜ).ConnectedComponent)
    (hvC0 : v ∈ compSet T c C₀) :
    let hc' : c ∈ ({v}ᶜ : Set U) := hvc.symm
    let T' := T.induce ({v}ᶜ : Set U)
    let c' : ({v}ᶜ : Set U) := ⟨c, hc'⟩
    let v' : ({c}ᶜ : Set U) := ⟨v, hvc⟩
    ∃ (C₀' : (T'.induce {c'}ᶜ).ConnectedComponent),
      (compSet T' c' C₀').map ⟨Subtype.val, val_injective⟩ = (compSet T c C₀).erase v ∧
      RootedIso T c (insert c ((compSet T c C₀).erase v : Set U))
        T' c' (insert c' (compSet T' c' C₀' : Set ({v}ᶜ : Set U))) ∧
      (∀ C : (T.induce {c}ᶜ).ConnectedComponent, C ≠ C₀ →
        ∃ C' : (T'.induce {c'}ᶜ).ConnectedComponent, C' ≠ C₀' ∧
          (compSet T' c' C').map ⟨Subtype.val, val_injective⟩ = compSet T c C ∧
          RootedCompIso T c C T' c' C') ∧
      (∀ D' : (T'.induce {c'}ᶜ).ConnectedComponent, D' ≠ C₀' →
        ∃ C : (T.induce {c}ᶜ).ConnectedComponent, C ≠ C₀ ∧
          (compSet T' c' D').map ⟨Subtype.val, val_injective⟩ = compSet T c C ∧
          RootedCompIso T c C T' c' D') := by
  intro hc' T' c' v'
  have hv_nadj : ¬ T.Adj c v := fun h => by have := hnoLeaf v h; omega
  have hC0_card2 : 2 ≤ card C₀.supp := comp_noLeaf_card_ge_two T hT c hnoLeaf C₀
  have hvC0' : v' ∈ C₀.supp := by
    obtain ⟨h1, h2⟩ := (mem_compSet_iff T c C₀ v).mp hvC0
    exact (mem_supp_iff C₀ v').mpr ((mem_supp_iff C₀ ⟨v, h1⟩).mp h2)
  have hC0_tree : C₀.toSimpleGraph.IsTree := (hT.isAcyclic.induce {c}ᶜ).isTree_connectedComponent C₀
  let vC0 : C₀.supp := ⟨v', hvC0'⟩
  have hdeg_vC0 : C₀.toSimpleGraph.degree vC0 = 1 := by
    rw [component_toSimpleGraph_degree T c C₀ vC0]
    dsimp only [vC0, v']
    exact (degree_induce_compl_singleton_of_not_adj T hvc (fun h => hv_nadj h.symm)).trans hv1
  have hC0_del_tree : (C₀.toSimpleGraph.induce ({vC0}ᶜ : Set C₀.supp)).IsTree :=
    induce_compl_singleton_isTree_of_deg_one C₀.toSimpleGraph hC0_tree hdeg_vC0
  obtain ⟨u₀, hu₀⟩ := hC0_del_tree.connected.nonempty
  have hu₀_ne_v : u₀.1.1 ≠ v := fun h => hu₀ (Subtype.ext (Subtype.ext h))
  let u₀' : ({c'}ᶜ : Set ({v}ᶜ : Set U)) := ⟨⟨u₀.1.1, hu₀_ne_v⟩, fun h => u₀.1.2 (congrArg Subtype.val h)⟩
  let C₀' := (T'.induce {c'}ᶜ).connectedComponentMk u₀'
  have hc_set_eq : ∀ x : ({c'}ᶜ : Set ({v}ᶜ : Set U)),
      x ∈ C₀'.supp ↔ x.1.1 ∈ (compSet T c C₀).erase v := by
    intro x
    have hx_ne_c : x.1.1 ≠ c := fun h => x.2 (Subtype.ext h)
    have hx_ne_v : x.1.1 ≠ v := x.1.2
    constructor
    · intro hxC0'
      rw [mem_erase]
      refine ⟨hx_ne_v, (mem_compSet_iff T c C₀ x.1.1).mpr ⟨hx_ne_c, ?_⟩⟩
      obtain ⟨q⟩ := C₀'.reachable_of_mem_supp rfl hxC0'
      let g : T'.induce {c'}ᶜ →g T.induce {c}ᶜ :=
        ⟨fun z => ⟨z.1.1, fun h => z.2 (Subtype.ext h)⟩, @fun _ _ h => h⟩
      have hreach : (T.induce {c}ᶜ).Reachable ⟨u₀.1.1, u₀.1.2⟩ ⟨x.1.1, hx_ne_c⟩ := ⟨q.map g⟩
      exact (mem_supp_iff C₀ _).mpr ((sound hreach).symm.trans
        ((mem_supp_iff C₀ _).mp u₀.2))
    · intro hx_er
      rw [mem_erase] at hx_er
      have hxC0 : ⟨x.1.1, hx_ne_c⟩ ∈ C₀.supp := by
        obtain ⟨h1, h2⟩ := (mem_compSet_iff T c C₀ x.1.1).mp hx_er.2
        convert h2
      let x_del : ({vC0}ᶜ : Set C₀.supp) := ⟨⟨⟨x.1.1, hx_ne_c⟩, hxC0⟩,
        fun h => hx_ne_v (congrArg (fun z : C₀.supp => z.1.1) h)⟩
      obtain ⟨q⟩ := hC0_del_tree.connected ⟨u₀, hu₀⟩ x_del
      let g : C₀.toSimpleGraph.induce ({vC0}ᶜ : Set C₀.supp) →g T'.induce {c'}ᶜ :=
        ⟨fun z => ⟨⟨z.1.1.1, fun h => z.2 (Subtype.ext (Subtype.ext h))⟩,
          fun h => z.1.1.2 (congrArg Subtype.val h)⟩, @fun _ _ h => h⟩
      have hreach : (T'.induce {c'}ᶜ).Reachable u₀' x := ⟨q.map g⟩
      exact (mem_supp_iff C₀' x).mpr (sound hreach).symm
  refine ⟨C₀', ?_, ?_, ?_, ?_⟩
  · ext y
    simp only [mem_map, mem_compSet_iff, Function.Embedding.coeFn_mk, mem_erase]
    constructor
    · rintro ⟨⟨y', hy'⟩, ⟨hne, hsupp⟩, rfl⟩
      have h1 := (hc_set_eq ⟨⟨y', hy'⟩, hne⟩).mp hsupp
      rw [mem_erase] at h1
      exact ⟨h1.1, (mem_compSet_iff T c C₀ y').mp h1.2⟩
    · rintro ⟨hyv, hyC0⟩
      have hyC0' : y ∈ compSet T c C₀ := (mem_compSet_iff T c C₀ y).mpr hyC0
      have hyc : y ≠ c := fun h => c_notMem_compSet T c C₀ (h ▸ hyC0')
      have hy'_ne : (⟨y, hyv⟩ : ({v}ᶜ : Set U)) ≠ c' := fun h => hyc (congrArg Subtype.val h)
      refine ⟨⟨y, hyv⟩, ⟨hy'_ne, (hc_set_eq ⟨⟨y, hyv⟩, hy'_ne⟩).mpr (mem_erase.mpr ⟨hyv, hyC0'⟩)⟩, rfl⟩
  · refine ⟨Set.mem_insert _ _, Set.mem_insert _ _,
      ⟨⟨fun x => ⟨⟨x.1, by
        rcases mem_insert_iff.mp x.2 with hxc | hx
        · rw [hxc]; exact hvc.symm
        · exact (mem_erase.mp hx).1⟩, by
        rcases mem_insert_iff.mp x.2 with hxc | hx
        · exact mem_insert_iff.mpr (Or.inl (Subtype.ext hxc))
        · refine Set.mem_insert_of_mem c' ((mem_compSet_iff T' c' C₀' _).mpr ⟨fun h => ?_, ?_⟩)
          · have hx2 := (mem_erase.mp hx).2
            rw [show (x.1 : U) = c from congrArg Subtype.val h] at hx2
            exact c_notMem_compSet T c C₀ hx2
          · exact (hc_set_eq _).mpr hx⟩,
      fun y => ⟨y.1.1, by
        rcases mem_insert_iff.mp y.2 with hyc | hy
        · rw [hyc]; exact Set.mem_insert _ _
        · obtain ⟨hne, hsupp⟩ := (mem_compSet_iff T' c' C₀' y.1).mp hy
          exact Or.inr ((hc_set_eq ⟨y.1, hne⟩).mp hsupp)⟩,
      fun x => Subtype.ext rfl, fun y => Subtype.ext (Subtype.ext rfl)⟩, @fun a b => Iff.rfl⟩, rfl⟩
  · intro C hC
    obtain ⟨z, hz⟩ := C.nonempty_supp
    have hz_ne_v : z.1 ≠ v := fun h => hC (((mem_supp_iff C v').mp
      ((Subtype.ext h.symm : v' = z) ▸ hz)).symm.trans ((mem_supp_iff C₀ v').mp hvC0'))
    let z' : ({c'}ᶜ : Set ({v}ᶜ : Set U)) := ⟨⟨z.1, hz_ne_v⟩, fun h => z.2 (congrArg Subtype.val h)⟩
    let C' := (T'.induce {c'}ᶜ).connectedComponentMk z'
    have hall_C : ∀ x : ({c'}ᶜ : Set ({v}ᶜ : Set U)), x ∈ C'.supp ↔ x.1.1 ∈ compSet T c C := by
      intro x
      have hx_ne_c : x.1.1 ≠ c := fun h => x.2 (Subtype.ext h)
      constructor
      · intro hxC'
        obtain ⟨q⟩ := C'.reachable_of_mem_supp rfl hxC'
        let g : T'.induce {c'}ᶜ →g T.induce {c}ᶜ :=
          ⟨fun w => ⟨w.1.1, fun h => w.2 (Subtype.ext h)⟩, @fun _ _ h => h⟩
        have hreach : (T.induce {c}ᶜ).Reachable z ⟨x.1.1, hx_ne_c⟩ := ⟨q.map g⟩
        exact (mem_compSet_iff T c C x.1.1).mpr ⟨hx_ne_c,
          (mem_supp_iff C _).mpr ((sound hreach).symm.trans
            ((mem_supp_iff C z).mp hz))⟩
      · intro hxC
        obtain ⟨hx1, hx2⟩ := (mem_compSet_iff T c C x.1.1).mp hxC
        obtain ⟨q⟩ := C.reachable_of_mem_supp hz ((mem_supp_iff C _).mpr
          ((mem_supp_iff C ⟨x.1.1, hx1⟩).mp hx2))
        let q_path := q.toPath
        have hv_not : v' ∉ q_path.val.support := by
          intro hm
          obtain ⟨q1, _, _, _, _⟩ := q_path.isPath.mem_support_iff_exists_append.mp hm
          exact hC (((mem_supp_iff C v').mp
            ((mem_supp_iff C _).mpr
              ((sound ⟨q1⟩).symm.trans ((mem_supp_iff C z).mp hz)))).symm.trans
            ((mem_supp_iff C₀ v').mp hvC0'))
        let hsupp : ∀ w ∈ q_path.val.support, w ∈ ({v'}ᶜ : Set ({c}ᶜ : Set U)) := fun w hw =>
          mem_compl_singleton_iff.mpr fun h => hv_not (h ▸ hw)
        let q' := q_path.val.induce ({v'}ᶜ : Set ({c}ᶜ : Set U)) hsupp
        let g : (T.induce {c}ᶜ).induce ({v'}ᶜ : Set ({c}ᶜ : Set U)) →g T'.induce {c'}ᶜ :=
          (compl_compl_comm_iso T c v hvc.symm).toHom
        have hreach : (T'.induce {c'}ᶜ).Reachable z' x := ⟨(q'.map g).copy rfl (Subtype.ext (Subtype.ext rfl))⟩
        exact (mem_supp_iff C' x).mpr (sound hreach).symm
    have hC'_ne : C' ≠ C₀' := by
      intro heq
      have h1 : z' ∈ C₀'.supp := (mem_supp_iff C₀' z').mpr (show _ = C₀' from heq)
      have h2 := (hc_set_eq z').mp h1
      rw [mem_erase] at h2
      exact hC (((mem_supp_iff C z).mp hz).symm.trans
        ((mem_supp_iff C₀ _).mp ((mem_compSet_iff T c C₀ z.1).mp h2.2).choose_spec))
    refine ⟨C', hC'_ne, ?_, Set.mem_insert _ _, Set.mem_insert _ _,
      ⟨⟨fun x => ⟨⟨x.1, by
          rcases mem_insert_iff.mp x.2 with hxc | hx
          · rw [hxc]; exact hvc.symm
          · intro heqv
            exact hC (by
              obtain ⟨h1, h2⟩ := (mem_compSet_iff T c C x.1).mp hx
              have : v' = ⟨x.1, h1⟩ := Subtype.ext heqv.symm
              exact ((mem_supp_iff C v').mp (this ▸ h2)).symm.trans
                ((mem_supp_iff C₀ v').mp hvC0'))⟩, by
          rcases mem_insert_iff.mp x.2 with hxc | hx
          · exact mem_insert_iff.mpr (Or.inl (Subtype.ext hxc))
          · refine Set.mem_insert_of_mem c' ((mem_compSet_iff T' c' C' _).mpr ⟨fun h => ?_, ?_⟩)
            · rw [show (x.1 : U) = c from congrArg Subtype.val h] at hx
              exact c_notMem_compSet T c C hx
            · exact (hall_C _).mpr hx⟩,
        fun y => ⟨y.1.1, by
          rcases mem_insert_iff.mp y.2 with hyc | hy
          · rw [hyc]; exact Set.mem_insert _ _
          · obtain ⟨hne, hsupp⟩ := (mem_compSet_iff T' c' C' y.1).mp hy
            exact Or.inr ((hall_C ⟨y.1, hne⟩).mp hsupp)⟩,
        fun _ => Subtype.ext rfl, fun _ => Subtype.ext (Subtype.ext rfl)⟩, @fun a b => Iff.rfl⟩, rfl⟩
    · ext y
      simp only [mem_map, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨⟨y', hy'⟩, hy_mem, rfl⟩
        obtain ⟨hne, hsupp⟩ := (mem_compSet_iff T' c' C' _).mp hy_mem
        exact (hall_C ⟨⟨y', hy'⟩, hne⟩).mp hsupp
      · intro hyC
        have hy_ne_c : y ≠ c := fun h => c_notMem_compSet T c C (by rwa [h] at hyC)
        have hy_ne_v : y ≠ v := fun h => hC (by
          obtain ⟨h1, h2⟩ := (mem_compSet_iff T c C y).mp hyC
          have : v' = ⟨y, h1⟩ := Subtype.ext h.symm
          exact ((mem_supp_iff C v').mp (this ▸ h2)).symm.trans
            ((mem_supp_iff C₀ v').mp hvC0'))
        have hy'_ne : (⟨y, hy_ne_v⟩ : ({v}ᶜ : Set U)) ≠ c' := fun h => hy_ne_c (congrArg Subtype.val h)
        exact ⟨⟨y, hy_ne_v⟩, (mem_compSet_iff T' c' C' _).mpr ⟨hy'_ne, (hall_C ⟨⟨y, hy_ne_v⟩, hy'_ne⟩).mpr hyC⟩, rfl⟩
  · intro D' hD'
    obtain ⟨w, hw⟩ := D'.nonempty_supp
    have hw_ne_c : w.1.1 ≠ c := fun h => w.2 (Subtype.ext h)
    let C := (T.induce {c}ᶜ).connectedComponentMk ⟨w.1.1, hw_ne_c⟩
    have hC : C ≠ C₀ := by
      intro heq
      have h1 : ⟨w.1.1, hw_ne_c⟩ ∈ C₀.supp :=
        (mem_supp_iff C₀ _).mpr (show _ = C₀ from heq)
      have h2 : w.1.1 ∈ (compSet T c C₀).erase v :=
        mem_erase.mpr ⟨w.1.2, (mem_compSet_iff T c C₀ w.1.1).mpr ⟨hw_ne_c, h1⟩⟩
      exact hD' (((mem_supp_iff D' w).mp hw).symm.trans
        ((mem_supp_iff C₀' w).mp ((hc_set_eq w).mpr h2)))
    have hall_C : ∀ x : ({c'}ᶜ : Set ({v}ᶜ : Set U)), x ∈ D'.supp ↔ x.1.1 ∈ compSet T c C := by
      intro x
      have hx_ne_c : x.1.1 ≠ c := fun h => x.2 (Subtype.ext h)
      constructor
      · intro hxD'
        obtain ⟨q⟩ := D'.reachable_of_mem_supp hw hxD'
        let g : T'.induce {c'}ᶜ →g T.induce {c}ᶜ :=
          ⟨fun z => ⟨z.1.1, fun h => z.2 (Subtype.ext h)⟩, @fun _ _ h => h⟩
        have hreach : (T.induce {c}ᶜ).Reachable ⟨w.1.1, hw_ne_c⟩ ⟨x.1.1, hx_ne_c⟩ := ⟨q.map g⟩
        exact (mem_compSet_iff T c C x.1.1).mpr ⟨hx_ne_c,
          (mem_supp_iff C _).mpr (sound hreach).symm⟩
      · intro hxC
        obtain ⟨hx1, hx2⟩ := (mem_compSet_iff T c C x.1.1).mp hxC
        obtain ⟨q⟩ := C.reachable_of_mem_supp rfl ((mem_supp_iff C _).mpr
          ((mem_supp_iff C ⟨x.1.1, hx1⟩).mp hx2))
        let q_path := q.toPath
        have hv_not : v' ∉ q_path.val.support := by
          intro hm
          obtain ⟨q1, _, _, _, _⟩ := q_path.isPath.mem_support_iff_exists_append.mp hm
          exact hC (((mem_supp_iff C v').mp
            ((mem_supp_iff C _).mpr (sound ⟨q1⟩).symm)).symm.trans
            ((mem_supp_iff C₀ v').mp hvC0'))
        let hsupp : ∀ z ∈ q_path.val.support, z ∈ ({v'}ᶜ : Set ({c}ᶜ : Set U)) := fun z hz =>
          mem_compl_singleton_iff.mpr fun h => hv_not (h ▸ hz)
        let q' := q_path.val.induce ({v'}ᶜ : Set ({c}ᶜ : Set U)) hsupp
        let g : (T.induce {c}ᶜ).induce ({v'}ᶜ : Set ({c}ᶜ : Set U)) →g T'.induce {c'}ᶜ :=
          (compl_compl_comm_iso T c v hvc.symm).toHom
        have hreach : (T'.induce {c'}ᶜ).Reachable w x :=
          ⟨(q'.map g).copy (Subtype.ext (Subtype.ext rfl)) (Subtype.ext (Subtype.ext rfl))⟩
        exact (mem_supp_iff D' x).mpr ((sound hreach).symm.trans
          ((mem_supp_iff D' w).mp hw))
    refine ⟨C, hC, ?_, Set.mem_insert _ _, Set.mem_insert _ _,
      ⟨⟨fun x => ⟨⟨x.1, by
          rcases mem_insert_iff.mp x.2 with hxc | hx
          · rw [hxc]; exact hvc.symm
          · intro heqv
            exact hC (by
              obtain ⟨h1, h2⟩ := (mem_compSet_iff T c C x.1).mp hx
              have : v' = ⟨x.1, h1⟩ := Subtype.ext heqv.symm
              exact ((mem_supp_iff C v').mp (this ▸ h2)).symm.trans
                ((mem_supp_iff C₀ v').mp hvC0'))⟩, by
          rcases mem_insert_iff.mp x.2 with hxc | hx
          · exact mem_insert_iff.mpr (Or.inl (Subtype.ext hxc))
          · refine Set.mem_insert_of_mem c' ((mem_compSet_iff T' c' D' _).mpr ⟨fun h => ?_, ?_⟩)
            · rw [show (x.1 : U) = c from congrArg Subtype.val h] at hx
              exact c_notMem_compSet T c C hx
            · exact (hall_C _).mpr hx⟩,
        fun y => ⟨y.1.1, by
          rcases mem_insert_iff.mp y.2 with hyc | hy
          · rw [hyc]; exact Set.mem_insert _ _
          · obtain ⟨hne, hsupp⟩ := (mem_compSet_iff T' c' D' y.1).mp hy
            exact Or.inr ((hall_C ⟨y.1, hne⟩).mp hsupp)⟩,
        fun _ => Subtype.ext rfl, fun _ => Subtype.ext (Subtype.ext rfl)⟩, @fun a b => Iff.rfl⟩, rfl⟩
    · ext y
      simp only [mem_map, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨⟨y', hy'⟩, hy_mem, rfl⟩
        obtain ⟨hne, hsupp⟩ := (mem_compSet_iff T' c' D' _).mp hy_mem
        exact (hall_C ⟨⟨y', hy'⟩, hne⟩).mp hsupp
      · intro hyC
        have hy_ne_c : y ≠ c := fun h => c_notMem_compSet T c C (by rwa [h] at hyC)
        have hy_ne_v : y ≠ v := fun h => hC (by
          obtain ⟨h1, h2⟩ := (mem_compSet_iff T c C y).mp hyC
          have : v' = ⟨y, h1⟩ := Subtype.ext h.symm
          exact ((mem_supp_iff C v').mp (this ▸ h2)).symm.trans
            ((mem_supp_iff C₀ v').mp hvC0'))
        have hy'_ne : (⟨y, hy_ne_v⟩ : ({v}ᶜ : Set U)) ≠ c' := fun h => hy_ne_c (congrArg Subtype.val h)
        exact ⟨⟨y, hy_ne_v⟩, (mem_compSet_iff T' c' D' _).mpr ⟨hy'_ne, (hall_C ⟨⟨y, hy_ne_v⟩, hy'_ne⟩).mpr hyC⟩, rfl⟩
private lemma iso_transport_comp {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (cG : V) (cH : W)
    (φ : G ≃g H) (hφc : φ cG = cH) :
    ∃ e : (G.induce {cG}ᶜ).ConnectedComponent ≃ (H.induce {cH}ᶜ).ConnectedComponent,
      ∀ C, card (e C).supp = card C.supp ∧ RootedCompIso G cG C H cH (e C) := by
  let φ_sub : G.induce {cG}ᶜ ≃g H.induce {cH}ᶜ :=
    ⟨⟨fun x => ⟨φ x.1, fun h => x.2 (φ.injective (h.trans hφc.symm))⟩,
      fun y => ⟨φ.symm y.1, fun h => y.2 (φ.symm.injective (h.trans (φ.symm_apply_eq.mpr hφc.symm).symm))⟩,
      fun _ => Subtype.ext (φ.symm_apply_apply _),
      fun _ => Subtype.ext (φ.apply_symm_apply _)⟩,
     @fun _ _ => φ.map_rel_iff⟩
  let e : (G.induce {cG}ᶜ).ConnectedComponent ≃ (H.induce {cH}ᶜ).ConnectedComponent :=
    ⟨ConnectedComponent.map φ_sub.toHom, ConnectedComponent.map φ_sub.symm.toHom,
      fun C => by
        obtain ⟨x, hx⟩ := C.nonempty_supp
        have h1 : (G.induce {cG}ᶜ).connectedComponentMk x = C := (mem_supp_iff C x).mp hx
        rw [← h1]
        simp only [ConnectedComponent.map_mk]
        congr 1; exact φ_sub.left_inv x,
      fun D => by
        obtain ⟨y, hy⟩ := D.nonempty_supp
        have h1 : (H.induce {cH}ᶜ).connectedComponentMk y = D := (mem_supp_iff D y).mp hy
        rw [← h1]
        simp only [ConnectedComponent.map_mk]
        congr 1; exact φ_sub.right_inv y⟩
  refine ⟨e, fun C => ?_⟩
  have hsupp_iff : ∀ y : ({cH}ᶜ : Set W), y ∈ (e C).supp ↔ φ_sub.symm y ∈ C.supp := by
    intro y
    obtain ⟨x, hx⟩ := C.nonempty_supp
    have hCx : (G.induce {cG}ᶜ).connectedComponentMk x = C := (mem_supp_iff C x).mp hx
    rw [mem_supp_iff, ← hCx, eq_comm]
    change ConnectedComponent.map φ_sub.toHom ((G.induce {cG}ᶜ).connectedComponentMk x) =
        (H.induce {cH}ᶜ).connectedComponentMk y ↔
      (G.induce {cG}ᶜ).connectedComponentMk (φ_sub.symm y) =
        (G.induce {cG}ᶜ).connectedComponentMk x
    rw [ConnectedComponent.map_mk, ConnectedComponent.eq, ConnectedComponent.eq]
    constructor
    · intro hr
      have h1 := hr.map φ_sub.symm.toHom
      change (G.induce {cG}ᶜ).Reachable (φ_sub.symm (φ_sub x)) (φ_sub.symm y) at h1
      rw [φ_sub.symm_apply_apply] at h1
      exact h1.symm
    · intro hr
      have h1 := hr.symm.map φ_sub.toHom
      change (H.induce {cH}ᶜ).Reachable (φ_sub x) (φ_sub (φ_sub.symm y)) at h1
      rw [φ_sub.apply_symm_apply] at h1
      exact h1
  have hcard : card (e C).supp = card C.supp := by
    refine card_congr
      ⟨fun y => ⟨φ_sub.symm y.1, (hsupp_iff y.1).mp y.2⟩,
       fun x => ⟨φ_sub x.1, (hsupp_iff (φ_sub x.1)).mpr (by simpa using x.2)⟩,
       fun _ => Subtype.ext (φ_sub.apply_symm_apply _),
       fun _ => Subtype.ext (φ_sub.symm_apply_apply _)⟩
  refine ⟨hcard, Set.mem_insert _ _, Set.mem_insert _ _, ?_, ?_⟩
  · refine ⟨⟨fun x => ⟨φ x.1, by
        rcases mem_insert_iff.mp x.2 with hxc | hx
        · rw [hxc, hφc]; exact Set.mem_insert _ _
        · obtain ⟨hne, hsupp⟩ := (mem_compSet_iff G cG C x.1).mp hx
          refine Set.mem_insert_of_mem cH ((mem_compSet_iff H cH (e C) (φ x.1)).mpr ⟨?_, ?_⟩)
          · exact fun h => hne (φ.injective (h.trans hφc.symm))
          · exact (hsupp_iff _).mpr (by convert hsupp; exact Subtype.ext (φ.symm_apply_apply _))⟩,
      fun y => ⟨φ.symm y.1, by
        rcases mem_insert_iff.mp y.2 with hyc | hy
        · rw [hyc, φ.symm_apply_eq.mpr hφc.symm]; exact Set.mem_insert _ _
        · obtain ⟨hne, hsupp⟩ := (mem_compSet_iff H cH (e C) y.1).mp hy
          have hm := (hsupp_iff ⟨y.1, hne⟩).mp hsupp
          exact Or.inr ((mem_compSet_iff G cG C _).mpr ⟨_, hm⟩)⟩,
      fun _ => Subtype.ext (φ.symm_apply_apply _),
      fun _ => Subtype.ext (φ.apply_symm_apply _)⟩, ?_⟩
    intro a b; exact φ.map_rel_iff
  · exact Subtype.ext hφc
/-! ### Part 3b: Bicenter helpers for diameter `2 * r - 1` and Boundary Case (`M + 1 + r = n`) -/
private lemma bicenter_eccent_gt_of_ne {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {r : ℕ} (hr : 2 ≤ r) (hdiam : T.diam = 2 * r - 1)
    {a b : U} (hadj : T.Adj a b) (ha : T.eccent a = r) (hb : T.eccent b = r)
    (z : U) (hza : z ≠ a) (hzb : z ≠ b) : (r : ℕ∞) < T.eccent z := by
  have : Nonempty U := hT.connected.nonempty
  obtain ⟨x0, xd, hxd⟩ := T.exists_dist_eq_diam
  obtain ⟨p, hp, hplen⟩ := hT.connected.exists_path_of_dist x0 xd
  have hplen_r : p.length = 2 * r - 1 := hplen.trans (hxd.trans hdiam)
  have hda_x0 : T.dist a x0 ≤ r := dist_le_of_eccent T hT ha
  have hda_xd : T.dist a xd ≤ r := dist_le_of_eccent T hT ha
  have hdb_x0 : T.dist b x0 ≤ r := dist_le_of_eccent T hT hb
  have hdb_xd : T.dist b xd ≤ r := dist_le_of_eccent T hT hb
  have hab_len : T.dist a b = 1 := dist_eq_one_iff_adj.mpr hadj
  have ha_sum : T.dist x0 a + T.dist a xd ≥ 2 * r - 1 := by
    have := hT.connected.dist_triangle (u := x0) (v := a) (w := xd)
    rw [← hplen, hplen_r] at this
    rw [dist_comm] at hda_x0
    omega
  have hb_sum : T.dist x0 b + T.dist b xd ≥ 2 * r - 1 := by
    have := hT.connected.dist_triangle (u := x0) (v := b) (w := xd)
    rw [← hplen, hplen_r] at this
    rw [dist_comm] at hdb_x0
    omega
  have htree_edge_parity : ∀ u : U, T.dist u a = T.dist u b + 1 ∨ T.dist u b = T.dist u a + 1 := by
    intro u
    obtain ⟨qa, hqa, hqalen⟩ := hT.connected.exists_path_of_dist u a
    obtain ⟨qb, hqb, hqblen⟩ := hT.connected.exists_path_of_dist u b
    by_cases hba : b ∈ qa.support
    · obtain ⟨q1, q2, hq1, hq2, hqeq⟩ := hqa.mem_support_iff_exists_append.mp hba
      have hq1_eq : q1 = qb := isTree_path_eq T hT hq1 hqb
      have hq2_len : q2.length = 1 := by
        rw [isTree_dist_eq_length_of_isPath T hT q2 hq2, dist_comm, hab_len]
      have hsum := congrArg Walk.length hqeq
      rw [length_append, hq1_eq, hqblen, hqalen, hq2_len] at hsum
      exact Or.inl hsum
    · let q' : T.Walk u b := qa.concat hadj
      have hq'_path : q'.IsPath := by
        rw [isPath_def, Walk.support_concat, List.nodup_append]
        refine ⟨hqa.support_nodup, List.nodup_singleton _, fun w hw y hy heq => ?_⟩
        simp only [List.mem_singleton] at hy
        rw [heq, hy] at hw
        exact hba hw
      have hq'_dist := isTree_dist_eq_length_of_isPath T hT q' hq'_path
      rw [Walk.length_concat, hqalen] at hq'_dist
      exact Or.inr hq'_dist.symm
  rw [dist_comm] at hda_x0 hdb_x0 hda_xd hdb_xd
  rw [dist_comm (u := a) (v := xd)] at ha_sum
  rw [dist_comm (u := b) (v := xd)] at hb_sum
  have hex_ya : ∃ ya : U, T.dist ya a = r ∧ T.dist ya b = r - 1 := by
    rcases htree_edge_parity x0 with h0 | h0 <;> rcases htree_edge_parity xd with hd | hd
    · exact False.elim (by omega)
    · exact ⟨x0, by omega, by omega⟩
    · exact ⟨xd, by omega, by omega⟩
    · exact False.elim (by omega)
  have hex_yb : ∃ yb : U, T.dist yb b = r ∧ T.dist yb a = r - 1 := by
    rcases htree_edge_parity x0 with h0 | h0 <;> rcases htree_edge_parity xd with hd | hd
    · exact False.elim (by omega)
    · exact ⟨xd, by omega, by omega⟩
    · exact ⟨x0, by omega, by omega⟩
    · exact False.elim (by omega)
  obtain ⟨ya, hya_a, hya_b⟩ := hex_ya
  obtain ⟨yb, hyb_b, hyb_a⟩ := hex_yb
  rcases htree_edge_parity z with hz_ab | hz_ba
  · obtain ⟨qz, hqz, hqzlen⟩ := hT.connected.exists_path_of_dist z b
    obtain ⟨qy, hqy, hqylen⟩ := hT.connected.exists_path_of_dist b yb
    have ha_not_qz : a ∉ qz.support := by
      intro hm
      obtain ⟨q1, _, hq1, _, hqeq⟩ := hqz.mem_support_iff_exists_append.mp hm
      have hlen1 : q1.length = T.dist z a := isTree_dist_eq_length_of_isPath T hT q1 hq1
      have hle : q1.length ≤ qz.length := by rw [hqeq, length_append]; omega
      omega
    have hz_meet : ∀ u ∈ qz.support, u ∈ qy.support.tail → u = b := by
      intro u huz huy
      by_contra hub
      have hqy_nn : ¬ qy.Nil := not_nil_of_ne (fun h => by rw [h, dist_self] at hyb_b; omega)
      have ha_eq_snd : qy.snd = a := by
        obtain ⟨qya, hqya, hqyalen⟩ := hT.connected.exists_path_of_dist a yb
        have hb_not_qya : b ∉ qya.support := by
          intro hm
          obtain ⟨_, q2, _, hq2, hqeq2⟩ := hqya.mem_support_iff_exists_append.mp hm
          have hlen2 : q2.length = T.dist b yb := isTree_dist_eq_length_of_isPath T hT q2 hq2
          have hle2 : q2.length ≤ qya.length := by rw [hqeq2, length_append]; omega
          rw [dist_comm, hyb_b] at hlen2
          rw [hqyalen, dist_comm, hyb_a] at hle2
          omega
        let qy' : T.Walk b yb := Walk.cons hadj.symm qya
        have hqy' : qy'.IsPath := (cons_isPath_iff hadj.symm qya).mpr ⟨hqya, hb_not_qya⟩
        have heq := isTree_path_eq T hT hqy hqy'
        rw [heq]; simp [qy']
      obtain ⟨qz1, qz2, hqz1, hqz2, hqz_eq⟩ := hqz.mem_support_iff_exists_append.mp huz
      obtain ⟨qy1, qy2, hqy1, hqy2, hqy_eq⟩ := hqy.mem_support_iff_exists_append.mp (List.mem_of_mem_tail huy)
      have hqy1_nn : ¬ qy1.Nil := not_nil_of_ne (Ne.symm hub)
      have hq1_eq := isTree_path_eq T hT hqz2.reverse hqy1
      have hsub1 : a ∈ qy1.support := by
        have h1 : qy1.snd = qy.snd := by
          cases qy1 with
          | nil => exact False.elim (hqy1_nn Walk.Nil.nil)
          | cons _ _ => rw [hqy_eq]; simp
        rw [← ha_eq_snd, ← h1]
        exact List.mem_of_mem_tail (qy1.snd_mem_tail_support hqy1_nn)
      rw [← hq1_eq, Walk.support_reverse, List.mem_reverse] at hsub1
      exact ha_not_qz (hqz_eq ▸ Walk.support_subset_support_append_right qz1 qz2 hsub1)
    have hpath : (qz.append qy).IsPath := isPath_append_of_first_meet hqz hqy hz_meet
    have hdist_z_yb : T.dist z yb = qz.length + qy.length := by
      rw [← isTree_dist_eq_length_of_isPath T hT (qz.append qy) hpath, length_append]
    have hpos : 0 < T.dist z b := hT.connected.pos_dist_of_ne hzb
    have hlt : (r : ℕ∞) < T.edist z yb := by
      rw [← (hT.connected z yb).coe_dist_eq_edist, hdist_z_yb, hqzlen, hqylen, dist_comm (u := b) (v := yb), hyb_b]
      exact_mod_cast (by omega : r < T.dist z b + r)
    exact lt_of_lt_of_le hlt edist_le_eccent
  · obtain ⟨qz, hqz, hqzlen⟩ := hT.connected.exists_path_of_dist z a
    obtain ⟨qy, hqy, hqylen⟩ := hT.connected.exists_path_of_dist a ya
    have hb_not_qz : b ∉ qz.support := by
      intro hm
      obtain ⟨q1, _, hq1, _, hqeq⟩ := hqz.mem_support_iff_exists_append.mp hm
      have hlen1 : q1.length = T.dist z b := isTree_dist_eq_length_of_isPath T hT q1 hq1
      have hle : q1.length ≤ qz.length := by rw [hqeq, length_append]; omega
      omega
    have hz_meet : ∀ u ∈ qz.support, u ∈ qy.support.tail → u = a := by
      intro u huz huy
      by_contra hua
      have hqy_nn : ¬ qy.Nil := not_nil_of_ne (fun h => by rw [h, dist_self] at hya_a; omega)
      have hb_eq_snd : qy.snd = b := by
        obtain ⟨qya, hqya, hqyalen⟩ := hT.connected.exists_path_of_dist b ya
        have ha_not_qya : a ∉ qya.support := by
          intro hm
          obtain ⟨_, q2, _, hq2, hqeq2⟩ := hqya.mem_support_iff_exists_append.mp hm
          have hlen2 : q2.length = T.dist a ya := isTree_dist_eq_length_of_isPath T hT q2 hq2
          have hle2 : q2.length ≤ qya.length := by rw [hqeq2, length_append]; omega
          rw [dist_comm, hya_a] at hlen2
          rw [hqyalen, dist_comm, hya_b] at hle2
          omega
        let qy' : T.Walk a ya := Walk.cons hadj qya
        have hqy' : qy'.IsPath := (cons_isPath_iff hadj qya).mpr ⟨hqya, ha_not_qya⟩
        have heq := isTree_path_eq T hT hqy hqy'
        rw [heq]; simp [qy']
      obtain ⟨qz1, qz2, hqz1, hqz2, hqz_eq⟩ := hqz.mem_support_iff_exists_append.mp huz
      obtain ⟨qy1, qy2, hqy1, hqy2, hqy_eq⟩ := hqy.mem_support_iff_exists_append.mp (List.mem_of_mem_tail huy)
      have hqy1_nn : ¬ qy1.Nil := not_nil_of_ne (Ne.symm hua)
      have hq1_eq := isTree_path_eq T hT hqz2.reverse hqy1
      have hsub1 : b ∈ qy1.support := by
        have h1 : qy1.snd = qy.snd := by
          cases qy1 with
          | nil => exact False.elim (hqy1_nn Walk.Nil.nil)
          | cons _ _ => rw [hqy_eq]; simp
        rw [← hb_eq_snd, ← h1]
        exact List.mem_of_mem_tail (qy1.snd_mem_tail_support hqy1_nn)
      rw [← hq1_eq, Walk.support_reverse, List.mem_reverse] at hsub1
      exact hb_not_qz (hqz_eq ▸ Walk.support_subset_support_append_right qz1 qz2 hsub1)
    have hpath : (qz.append qy).IsPath := isPath_append_of_first_meet hqz hqy hz_meet
    have hdist_z_ya : T.dist z ya = qz.length + qy.length := by
      rw [← isTree_dist_eq_length_of_isPath T hT (qz.append qy) hpath, length_append]
    have hpos : 0 < T.dist z a := hT.connected.pos_dist_of_ne hza
    have hlt : (r : ℕ∞) < T.edist z ya := by
      rw [← (hT.connected z ya).coe_dist_eq_edist, hdist_z_ya, hqzlen, hqylen, dist_comm (u := a) (v := ya), hya_a]
      exact_mod_cast (by omega : r < T.dist z a + r)
    exact lt_of_lt_of_le hlt edist_le_eccent
private lemma mem_compSet_of_walk_from_c {U : Type} [Fintype U] (T : SimpleGraph U)
    (c : U) (C : (T.induce {c}ᶜ).ConnectedComponent) {x : U} (hx : x ∈ compSet T c C)
    {p : T.Walk c x} (hp : p.IsPath) {w : U} (hw : w ∈ p.support) (hwc : w ≠ c) :
    w ∈ compSet T c C := by
  let q := p.dropUntil w hw
  have hc_not_q : c ∉ q.support := by
    intro hcm
    have hq_nn : ¬ q.Nil := fun hnil => by
      have hl1 : q.support.length = 1 := by
        rw [Walk.length_support, Walk.length_eq_zero_iff.mpr hnil]
      obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hl1
      have hw1 : w ∈ q.support := q.start_mem_support
      rw [ha, List.mem_singleton] at hw1 hcm
      exact hwc (hw1.trans hcm.symm)
    have h1 : ((p.takeUntil w hw).support ++ q.support.tail).Nodup := by
      have hs := hp.support_nodup
      rw [← p.take_spec hw, Walk.support_append] at hs
      exact hs
    have hdisj := (List.nodup_append'.mp h1).2.2
    have hc_take : c ∈ (p.takeUntil w hw).support := Walk.start_mem_support _
    have hq_tail : c ∈ q.support.tail := mem_support_tail_of_ne q hcm hwc.symm
    exact hdisj hc_take hq_tail
  obtain ⟨hne_x, hsupp_x⟩ := (mem_compSet_iff T c C x).mp hx
  have hq_supp : ∀ z ∈ q.support, z ∈ ({c}ᶜ : Set U) := by
    intro z hz hzc
    subst hzc
    exact hc_not_q hz
  let q' : (T.induce {c}ᶜ).Walk ⟨w, hwc⟩ ⟨x, hne_x⟩ := q.induce ({c}ᶜ : Set U) hq_supp
  exact (mem_compSet_iff T c C w).mpr ⟨hwc,
    (mem_supp_iff C _).mpr ((sound ⟨q'⟩).trans
      ((mem_supp_iff C _).mp hsupp_x))⟩
private lemma path_snd_eq_root_of_compSet {U : Type} [Fintype U] (T : SimpleGraph U) (hT : T.IsTree)
    (c : U) (C : (T.induce {c}ᶜ).ConnectedComponent) {x : U} (hx : x ∈ compSet T c C)
    {p : T.Walk c x} (hp : p.IsPath) :
    have hxc : x ≠ c := fun h => c_notMem_compSet T c C (h ▸ hx)
    p.snd = (existsUnique_root_of_component T hT c C).choose.1 := by
  intro hxc
  have hnp : ¬ p.Nil := not_nil_of_ne hxc.symm
  have hsnd_mem_p : p.snd ∈ p.support := List.mem_of_mem_tail (p.snd_mem_tail_support hnp)
  have hsnd_adj : T.Adj c p.snd := p.adj_snd hnp
  have hsnd_ne : p.snd ≠ c := hsnd_adj.ne.symm
  have hsnd_C := mem_compSet_of_walk_from_c T c C hx hp hsnd_mem_p hsnd_ne
  obtain ⟨h1, h2⟩ := (mem_compSet_iff T c C p.snd).mp hsnd_C
  have h_eq := (existsUnique_root_of_component T hT c C).choose_spec.2 ⟨p.snd, h1⟩ ⟨h2, hsnd_adj⟩
  exact congrArg Subtype.val h_eq
private lemma dist_comp_eq_one_add_root {U : Type} [Fintype U] (T : SimpleGraph U) (hT : T.IsTree)
    (c : U) (C : (T.induce {c}ᶜ).ConnectedComponent) {z : U} (hz : z ∈ compSet T c C) :
    let u := (existsUnique_root_of_component T hT c C).choose
    T.dist z c = T.dist z u.1 + 1 := by
  intro u
  have hub_mem := (existsUnique_root_of_component T hT c C).choose_spec.1.1
  have hub_adj := (existsUnique_root_of_component T hT c C).choose_spec.1.2
  obtain ⟨p, hp, hplen⟩ := hT.connected.exists_path_of_dist c z
  have hzc : z ≠ c := fun h => c_notMem_compSet T c C (h ▸ hz)
  have hnp : ¬ p.Nil := not_nil_of_ne hzc.symm
  have hsnd : p.snd = u.1 := path_snd_eq_root_of_compSet T hT c C hz hp
  let p' : T.Walk u.1 z := p.tail.copy hsnd rfl
  have hp' : p'.IsPath := (isPath_copy _ _ _).mpr hp.tail
  have h1 := isTree_dist_eq_length_of_isPath T hT p' hp'
  rw [length_copy, length_tail, hplen, dist_comm, dist_comm (u := u.1) (v := z)] at h1
  have hpos : 0 < T.dist c z := hT.connected.pos_dist_of_ne hzc.symm
  rw [dist_comm] at hpos
  omega
private lemma dist_add_of_ne_comp {U : Type} [Fintype U] (T : SimpleGraph U) (hT : T.IsTree)
    (c : U) {Ca Cb : (T.induce {c}ᶜ).ConnectedComponent} (hCab : Ca ≠ Cb)
    {x y : U} (hx : x ∈ compSet T c Ca) (hy : y ∈ compSet T c Cb) :
    T.dist x y = T.dist x c + T.dist c y := by
  obtain ⟨p, hp, hplen⟩ := hT.connected.exists_path_of_dist x y
  have hc_mem : c ∈ p.support := by
    by_contra hnc
    have hsupp : ∀ z ∈ p.support, z ∈ ({c}ᶜ : Set U) := fun z hz heq => hnc (heq ▸ hz)
    obtain ⟨hx1, hx2⟩ := (mem_compSet_iff T c Ca x).mp hx
    obtain ⟨hy1, hy2⟩ := (mem_compSet_iff T c Cb y).mp hy
    have hreach : (T.induce {c}ᶜ).Reachable ⟨x, hx1⟩ ⟨y, hy1⟩ := ⟨p.induce _ hsupp⟩
    exact hCab (((mem_supp_iff Ca _).mp hx2).symm.trans
      ((sound hreach).trans ((mem_supp_iff Cb _).mp hy2)))
  obtain ⟨q1, q2, hq1, hq2, hpeq⟩ := hp.mem_support_iff_exists_append.mp hc_mem
  have hsum := congrArg Walk.length hpeq
  rw [length_append, hplen, isTree_dist_eq_length_of_isPath T hT q1 hq1,
    isTree_dist_eq_length_of_isPath T hT q2 hq2] at hsum
  exact hsum
private lemma bicenter_del_leaf_info {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {r : ℕ} (hr : 2 ≤ r) (hdiam : T.diam = 2 * r)
    (c : U) (hecc : T.eccent c = r) (hdeg2 : T.degree c = 2)
    (Ca Cb : (T.induce {c}ᶜ).ConnectedComponent) (hCab : Ca ≠ Cb)
    {v : U} (hv1 : T.degree v = 1) (hvCa : v ∈ compSet T c Ca)
    (hdiam' : (T.induce {v}ᶜ).diam = 2 * r - 1) :
    let T' := T.induce ({v}ᶜ : Set U)
    let hvc : c ∈ ({v}ᶜ : Set U) := fun h => c_notMem_compSet T c Ca (h ▸ hvCa)
    let c' : ({v}ᶜ : Set U) := ⟨c, hvc⟩
    let ub := (existsUnique_root_of_component T hT c Cb).choose
    have hub_mem : ub ∈ Cb.supp := (existsUnique_root_of_component T hT c Cb).choose_spec.1.1
    have hub_adj : T.Adj c ub.1 := (existsUnique_root_of_component T hT c Cb).choose_spec.1.2
    have hub_v : ub.1 ∈ ({v}ᶜ : Set U) := fun h =>
      (Finset.disjoint_left.mp (compSet_disjoint T c hCab) hvCa)
        ((h : ub.1 = v) ▸ (mem_compSet_iff T c Cb ub.1).mpr ⟨ub.2, hub_mem⟩)
    let ub' : ({v}ᶜ : Set U) := ⟨ub.1, hub_v⟩
    (∀ y ∈ compSet T c Ca, y ≠ v → T.dist c y ≤ r - 1) ∧
    (T'.eccent c' = r ∧ T'.eccent ub' = r ∧
      (∀ z' : ({v}ᶜ : Set U), z' ≠ c' → z' ≠ ub' → (r : ℕ∞) < T'.eccent z')) ∧
    (univ.filter fun z' : ({v}ᶜ : Set U) => T'.dist z' ub' < T'.dist z' c').card =
      card Cb.supp ∧
    (univ.filter fun z' : ({v}ᶜ : Set U) => T'.dist z' c' < T'.dist z' ub').card =
      card Ca.supp ∧
    (∃ (φ : T'.induce {z' : ({v}ᶜ : Set U) | T'.dist z' ub' < T'.dist z' c'} ≃g
        T.induce (compSet T c Cb : Set U)),
      φ ⟨ub', by
        show T'.dist ub' ub' < T'.dist ub' c'
        rw [dist_self, dist_comm,
          dist_eq_one_iff_adj.mpr (show T'.Adj c' ub' from hub_adj)]
        omega⟩ = ⟨ub.1, (mem_compSet_iff T c Cb ub.1).mpr ⟨ub.2, hub_mem⟩⟩) ∧
    (∃ (φ : T'.induce {z' : ({v}ᶜ : Set U) | T'.dist z' c' < T'.dist z' ub'} ≃g
        T.induce (insert c ((compSet T c Ca).erase v : Set U))),
      φ ⟨c', by
        show T'.dist c' c' < T'.dist c' ub'
        rw [dist_self,
          dist_eq_one_iff_adj.mpr (show T'.Adj c' ub' from hub_adj)]
        omega⟩ = ⟨c, Set.mem_insert _ _⟩) := by
  intro T' hvc c' ub hub_mem hub_adj hub_v ub'
  have hT' : T'.IsTree := induce_compl_singleton_isTree_of_deg_one T hT hv1
  have hall_comp : ∀ C : (T.induce {c}ᶜ).ConnectedComponent, C = Ca ∨ C = Cb := by
    intro C
    by_contra hnot
    push Not at hnot
    have hcard_cc : card (T.induce {c}ᶜ).ConnectedComponent = 2 := by
      rw [card_connectedComponent_eq_degree T hT c, hdeg2]
    have h3 : ({Ca, Cb, C} : Finset (T.induce {c}ᶜ).ConnectedComponent).card ≤ 2 :=
      hcard_cc ▸ card_le_univ _
    have hcard3 : ({Ca, Cb, C} : Finset (T.induce {c}ᶜ).ConnectedComponent).card = 3 := by
      rw [card_insert_of_notMem, card_pair hnot.2.symm]
      simp [hCab, hnot.1.symm]
    omega
  obtain ⟨C_other, hC_other_ne, x_b, hx_b_mem, hx_b_dist⟩ :=
    exists_other_diam_comp T hT hr hdiam c hecc Ca
  have hC_other_eq : C_other = Cb := (hall_comp C_other).resolve_left hC_other_ne
  have hx_b_Cb : x_b ∈ compSet T c Cb := hC_other_eq ▸ hx_b_mem
  have hxb_ne_v : x_b ≠ v := fun h =>
    (Finset.disjoint_left.mp (compSet_disjoint T c hCab) hvCa) (h ▸ hx_b_Cb)
  have hdist_r_Ca : ∀ y ∈ compSet T c Ca, y ≠ v → T.dist c y ≤ r - 1 := by
    intro y hy hyv
    have hle := dist_le_of_eccent T hT (u := y) hecc
    by_contra hgt
    have hyd : T.dist c y = r := by omega
    have hdist_yx : T.dist y x_b = 2 * r := by
      rw [dist_add_of_ne_comp T hT c hCab hy hx_b_Cb, dist_comm, hyd, hx_b_dist]
      omega
    have : Nonempty ({v}ᶜ : Set U) := ⟨c'⟩
    have hediam' : T'.ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hT'.connected
    have hle' := dist_le_diam hediam' (u := ⟨y, hyv⟩) (v := ⟨x_b, hxb_ne_v⟩)
    rw [dist_induce_eq_of_isTree T hT {v}ᶜ hT', hdist_yx, hdiam'] at hle'
    omega
  have hub_Cb : ub.1 ∈ compSet T c Cb := (mem_compSet_iff T c Cb ub.1).mpr ⟨ub.2, hub_mem⟩
  have h_part_iff : ∀ z' : ({v}ᶜ : Set U),
      (T'.dist z' ub' < T'.dist z' c' ↔ z'.1 ∈ compSet T c Cb) ∧
      (T'.dist z' c' < T'.dist z' ub' ↔ z'.1 ∈ insert c ((compSet T c Ca).erase v)) := by
    intro z'
    have hz_eq_dist : ∀ (a' b' : ({v}ᶜ : Set U)), T'.dist a' b' = T.dist a'.1 b'.1 :=
      dist_induce_eq_of_isTree T hT {v}ᶜ hT'
    rw [hz_eq_dist z' ub', hz_eq_dist z' c']
    dsimp only [ub', c']
    by_cases hzc : z'.1 = c
    · rw [hzc, dist_self, dist_eq_one_iff_adj.mpr hub_adj]
      constructor
      · refine ⟨fun h => False.elim (by omega), fun h => False.elim (c_notMem_compSet T c Cb h)⟩
      · refine ⟨fun _ => mem_insert_self c _, fun _ => by omega⟩
    · let Cz := (T.induce {c}ᶜ).connectedComponentMk ⟨z'.1, hzc⟩
      have hz_mem : z'.1 ∈ compSet T c Cz := (mem_compSet_iff T c Cz z'.1).mpr ⟨hzc, rfl⟩
      rcases hall_comp Cz with hCz | hCz
      · rw [hCz] at hz_mem
        have hdist_zub : T.dist z'.1 ub.1 = T.dist z'.1 c + 1 := by
          rw [dist_add_of_ne_comp T hT c hCab hz_mem hub_Cb, dist_eq_one_iff_adj.mpr hub_adj]
        constructor
        · refine ⟨fun h => False.elim (by omega), fun h =>
            False.elim ((Finset.disjoint_left.mp (compSet_disjoint T c hCab) hz_mem) h)⟩
        · refine ⟨fun _ => mem_insert_of_mem (mem_erase.mpr ⟨z'.2, hz_mem⟩),
            fun _ => by omega⟩
      · rw [hCz] at hz_mem
        have hdist_zc : T.dist z'.1 c = T.dist z'.1 ub.1 + 1 := dist_comp_eq_one_add_root T hT c Cb hz_mem
        constructor
        · exact ⟨fun _ => hz_mem, fun _ => by omega⟩
        · refine ⟨fun h => False.elim (by omega), fun h => by
            rcases mem_insert.mp h with h1 | h1
            · exact False.elim (hzc h1)
            · exact False.elim ((Finset.disjoint_left.mp (compSet_disjoint T c hCab)
                (mem_erase.mp h1).2) hz_mem)⟩
  have hecc_c' : T'.eccent c' = r := by
    apply le_antisymm
    · rw [eccent_le_iff]
      intro y'
      rw [← (hT'.connected c' y').coe_dist_eq_edist, dist_induce_eq_of_isTree T hT {v}ᶜ hT']
      exact Nat.cast_le.mpr (dist_le_of_eccent T hT hecc)
    · have h1 : T'.dist c' ⟨x_b, hxb_ne_v⟩ = r := by
        rw [dist_induce_eq_of_isTree T hT {v}ᶜ hT']
        exact hx_b_dist
      rw [← h1, (hT'.connected c' ⟨x_b, hxb_ne_v⟩).coe_dist_eq_edist]
      exact edist_le_eccent
  have hecc_ub' : T'.eccent ub' = r := by
    apply le_antisymm
    · rw [eccent_le_iff]
      intro y'
      rw [← (hT'.connected ub' y').coe_dist_eq_edist, dist_induce_eq_of_isTree T hT {v}ᶜ hT']
      by_cases hyc : y'.1 = c
      · rw [hyc, dist_comm, dist_eq_one_iff_adj.mpr hub_adj]
        exact_mod_cast (by omega : 1 ≤ r)
      · let Cy := (T.induce {c}ᶜ).connectedComponentMk ⟨y'.1, hyc⟩
        have hy_mem : y'.1 ∈ compSet T c Cy := (mem_compSet_iff T c Cy y'.1).mpr ⟨hyc, rfl⟩
        rcases hall_comp Cy with hCy | hCy
        · rw [hCy] at hy_mem
          rw [dist_comm, dist_add_of_ne_comp T hT c hCab hy_mem hub_Cb,
            dist_eq_one_iff_adj.mpr hub_adj, dist_comm]
          have := hdist_r_Ca y'.1 hy_mem y'.2
          exact_mod_cast (by omega : T.dist c y'.1 + 1 ≤ r)
        · rw [hCy] at hy_mem
          have h1 : T.dist y'.1 c = T.dist y'.1 ub.1 + 1 := dist_comp_eq_one_add_root T hT c Cb hy_mem
          have h2 := dist_le_of_eccent T hT (u := y'.1) hecc
          rw [dist_comm (u := c) (v := y'.1)] at h2
          dsimp only [ub']
          rw [dist_comm (u := ub.1) (v := y'.1)]
          exact_mod_cast (by omega : T.dist y'.1 ub.1 ≤ r)
    · have hv_dist_r : T.dist c v = r := by
        have : Nonempty U := hT.connected.nonempty
        obtain ⟨x0, xd, hxd⟩ := T.exists_dist_eq_diam
        obtain ⟨p, hp, hplen⟩ := hT.connected.exists_path_of_dist x0 xd
        obtain ⟨_, hcx0, hcxd⟩ := diam_path_contains_center T hT c hecc p hp (hplen.trans (hxd.trans hdiam))
        have hx0_ne : x0 ≠ c := fun h => by rw [← h, dist_self] at hcx0; omega
        have hxd_ne : xd ≠ c := fun h => by rw [← h, dist_self] at hcxd; omega
        let C0 := (T.induce {c}ᶜ).connectedComponentMk ⟨x0, hx0_ne⟩
        let Cd := (T.induce {c}ᶜ).connectedComponentMk ⟨xd, hxd_ne⟩
        have hne0d : C0 ≠ Cd := by
          intro heq
          have h1 : T.dist x0 xd = T.dist x0 c + T.dist c xd := by
            rw [dist_comm (u := x0) (v := c), hcx0, hcxd]; omega
          obtain ⟨q⟩ := ConnectedComponent.exact heq
          let q_path := q.toPath
          let g : T.induce {c}ᶜ →g T := (Embedding.induce ({c}ᶜ : Set U)).toHom
          have hqG : (q_path.val.map g).IsPath := q_path.isPath.map val_injective
          have hqp := isTree_path_eq T hT hqG hp
          obtain ⟨hc_mem, _, _⟩ := diam_path_contains_center T hT c hecc p hp (hplen.trans (hxd.trans hdiam))
          have hc_not : c ∉ (q_path.val.map g).support := by
            rw [Walk.support_map, List.mem_map]; rintro ⟨y, _, hyc⟩; exact y.2 hyc
          rw [hqp] at hc_not
          exact hc_not hc_mem
        have hv_eq_x : v = x0 ∨ v = xd := by
          by_contra hnv; push Not at hnv
          rcases hall_comp C0 with h0 | h0 <;> rcases hall_comp Cd with hd | hd
          · exact hne0d (h0.trans hd.symm)
          · have hx0_Ca : x0 ∈ compSet T c Ca := (mem_compSet_iff T c Ca x0).mpr
              ⟨hx0_ne, h0 ▸ rfl⟩
            have := hdist_r_Ca x0 hx0_Ca hnv.1.symm
            omega
          · have hxd_Ca : xd ∈ compSet T c Ca := (mem_compSet_iff T c Ca xd).mpr
              ⟨hxd_ne, hd ▸ rfl⟩
            have := hdist_r_Ca xd hxd_Ca hnv.2.symm
            omega
          · exact hne0d (h0.trans hd.symm)
        rcases hv_eq_x with rfl | rfl <;> assumption
      obtain ⟨pv, hpv, hpvlen⟩ := hT.connected.exists_path_of_dist c v
      have hpv_len_r : pv.length = r := hpvlen.trans hv_dist_r
      let y_prev := pv.penultimate
      have hpv_nn : ¬ pv.Nil := not_nil_of_ne (fun h => by rw [← h, dist_self] at hv_dist_r; omega)
      have hy_dist : T.dist c y_prev = r - 1 := by
        have hp_take : (pv.take (pv.length - 1)).IsPath := hpv.take (pv.length - 1)
        have hlen_t : (pv.take (pv.length - 1)).length = r - 1 := by rw [Walk.take_length]; omega
        have hend : pv.getVert (pv.length - 1) = y_prev := rfl
        have h1 := isTree_dist_eq_length_of_isPath T hT (pv.take (pv.length - 1)) hp_take
        rw [hlen_t, hend] at h1
        exact h1.symm
      have hy_ne_v : y_prev ≠ v := (pv.adj_penultimate hpv_nn).ne
      have hy_ne_c : y_prev ≠ c := fun h => by rw [h, dist_self] at hy_dist; omega
      have hy_Ca : y_prev ∈ compSet T c Ca :=
        mem_compSet_of_walk_from_c T c Ca hvCa hpv (getVert_mem_support pv (pv.length - 1)) hy_ne_c
      have hdist_ub_y : T'.dist ub' ⟨y_prev, hy_ne_v⟩ = r := by
        rw [dist_induce_eq_of_isTree T hT {v}ᶜ hT', dist_comm,
          dist_add_of_ne_comp T hT c hCab hy_Ca hub_Cb, dist_comm (u := y_prev) (v := c), hy_dist,
          dist_eq_one_iff_adj.mpr hub_adj]
        omega
      rw [← hdist_ub_y, (hT'.connected ub' ⟨y_prev, hy_ne_v⟩).coe_dist_eq_edist]
      exact edist_le_eccent
  have huniq_bi : ∀ z' : ({v}ᶜ : Set U), z' ≠ c' → z' ≠ ub' → (r : ℕ∞) < T'.eccent z' :=
    bicenter_eccent_gt_of_ne T' hT' hr hdiam' hub_adj hecc_c' hecc_ub'
  have hcard_Cb : (univ.filter fun z' : ({v}ᶜ : Set U) => T'.dist z' ub' < T'.dist z' c').card =
      card Cb.supp := by
    rw [← compSet_card_eq T c Cb]
    refine card_bij (fun z' _ => z'.1) ?_ ?_ ?_
    · intro z' hz'
      rw [mem_filter] at hz'
      exact (h_part_iff z').1.mp hz'.2
    · intro a _ b _ hab; exact Subtype.ext hab
    · intro y hy
      have hyv : y ∈ ({v}ᶜ : Set U) := fun h =>
        (Finset.disjoint_left.mp (compSet_disjoint T c hCab) hvCa) (h ▸ hy)
      exact ⟨⟨y, hyv⟩, mem_filter.mpr ⟨mem_univ _, (h_part_iff ⟨y, hyv⟩).1.mpr hy⟩, rfl⟩
  have hcard_Ca : (univ.filter fun z' : ({v}ᶜ : Set U) => T'.dist z' c' < T'.dist z' ub').card =
      card Ca.supp := by
    have hcard_ins : (insert c ((compSet T c Ca).erase v)).card = card Ca.supp := by
      have hc_not_er : c ∉ (compSet T c Ca).erase v := fun h =>
        c_notMem_compSet T c Ca (mem_erase.mp h).2
      rw [card_insert_of_notMem hc_not_er, card_erase_of_mem hvCa, compSet_card_eq]
      have hpos : 1 ≤ card Ca.supp := by
        rw [← compSet_card_eq]
        exact card_pos.mpr ⟨v, hvCa⟩
      omega
    rw [← hcard_ins]
    refine card_bij (fun z' _ => z'.1) ?_ ?_ ?_
    · intro z' hz'
      rw [mem_filter] at hz'
      exact (h_part_iff z').2.mp hz'.2
    · intro a _ b _ hab; exact Subtype.ext hab
    · intro y hy
      have hyv : y ∈ ({v}ᶜ : Set U) := by
        rcases mem_insert.mp hy with rfl | hy1
        · exact hvc
        · exact (mem_erase.mp hy1).1
      exact ⟨⟨y, hyv⟩, mem_filter.mpr ⟨mem_univ _, (h_part_iff ⟨y, hyv⟩).2.mpr hy⟩, rfl⟩
  refine ⟨hdist_r_Ca, ⟨hecc_c', hecc_ub', huniq_bi⟩, hcard_Cb, hcard_Ca, ?_, ?_⟩
  · refine ⟨⟨⟨fun z' => ⟨z'.1.1, (h_part_iff z'.1).1.mp z'.2⟩,
      fun y => ⟨⟨y.1, fun h => (Finset.disjoint_left.mp (compSet_disjoint T c hCab) hvCa) (h ▸ y.2)⟩,
        (h_part_iff _).1.mpr y.2⟩,
      fun _ => Subtype.ext (Subtype.ext rfl), fun _ => Subtype.ext rfl⟩, ?_⟩, rfl⟩
    intro a b; rfl
  · have hiff2 : ∀ z' : ({v}ᶜ : Set U),
        T'.dist z' c' < T'.dist z' ub' ↔ z'.1 ∈ (insert c ((compSet T c Ca).erase v : Set U)) := by
      intro z'
      exact (h_part_iff z').2.trans (by simp only [mem_insert, mem_insert_iff, mem_coe])
    refine ⟨⟨⟨fun z' => ⟨z'.1.1, (hiff2 z'.1).mp z'.2⟩,
      fun y => ⟨⟨y.1, by
        rcases y.2 with hy_eq | hy1
        · rw [hy_eq]; exact hvc
        · exact (mem_erase.mp hy1).1⟩, (hiff2 _).mpr y.2⟩,
      fun _ => Subtype.ext (Subtype.ext rfl), fun _ => Subtype.ext rfl⟩, ?_⟩, rfl⟩
    intro a b; rfl
private lemma rootedCompIso_of_root_iso {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (hTG : G.IsTree) (hTH : H.IsTree)
    (cG : V) (cH : W)
    (C : (G.induce {cG}ᶜ).ConnectedComponent) (D : (H.induce {cH}ᶜ).ConnectedComponent)
    {uG : ({cG}ᶜ : Set V)} (huG_mem : uG ∈ C.supp) (huG_adj : G.Adj cG uG.1)
    {vH : ({cH}ᶜ : Set W)} (hvH_mem : vH ∈ D.supp) (hvH_adj : H.Adj cH vH.1)
    (φ : G.induce (compSet G cG C : Set V) ≃g H.induce (compSet H cH D : Set W))
    (hφ_root : φ ⟨uG.1, (mem_compSet_iff G cG C uG.1).mpr ⟨uG.2, huG_mem⟩⟩ =
      ⟨vH.1, (mem_compSet_iff H cH D vH.1).mpr ⟨vH.2, hvH_mem⟩⟩) :
    RootedCompIso G cG C H cH D := by
  have huniqG : ∀ x : V, x ∈ compSet G cG C → (G.Adj cG x ↔ x = uG.1) := by
    intro x hx
    refine ⟨fun hadj => ?_, fun h => h ▸ huG_adj⟩
    obtain ⟨hx1, hx2⟩ := (mem_compSet_iff G cG C x).mp hx
    have h1 := (existsUnique_root_of_component G hTG cG C).choose_spec.2 ⟨x, hx1⟩ ⟨hx2, hadj⟩
    have h2 := (existsUnique_root_of_component G hTG cG C).choose_spec.2 uG ⟨huG_mem, huG_adj⟩
    exact congrArg Subtype.val (h1.trans h2.symm)
  have huniqH : ∀ y : W, y ∈ compSet H cH D → (H.Adj cH y ↔ y = vH.1) := by
    intro y hy
    refine ⟨fun hadj => ?_, fun h => h ▸ hvH_adj⟩
    obtain ⟨hy1, hy2⟩ := (mem_compSet_iff H cH D y).mp hy
    have h1 := (existsUnique_root_of_component H hTH cH D).choose_spec.2 ⟨y, hy1⟩ ⟨hy2, hadj⟩
    have h2 := (existsUnique_root_of_component H hTH cH D).choose_spec.2 vH ⟨hvH_mem, hvH_adj⟩
    exact congrArg Subtype.val (h1.trans h2.symm)
  let toF : ↥(insert cG (compSet G cG C : Set V)) → ↥(insert cH (compSet H cH D : Set W)) := fun x =>
    if hx : x.1 ∈ (compSet G cG C : Set V) then ⟨(φ ⟨x.1, hx⟩).1, Set.mem_insert_of_mem cH (φ ⟨x.1, hx⟩).2⟩
    else ⟨cH, Set.mem_insert _ _⟩
  let invF : ↥(insert cH (compSet H cH D : Set W)) → ↥(insert cG (compSet G cG C : Set V)) := fun y =>
    if hy : y.1 ∈ (compSet H cH D : Set W) then ⟨(φ.symm ⟨y.1, hy⟩).1, Set.mem_insert_of_mem cG (φ.symm ⟨y.1, hy⟩).2⟩
    else ⟨cG, Set.mem_insert _ _⟩
  have hG_not : cG ∉ (compSet G cG C : Set V) := mem_coe.not.mpr (c_notMem_compSet G cG C)
  have hH_not : cH ∉ (compSet H cH D : Set W) := mem_coe.not.mpr (c_notMem_compSet H cH D)
  have hleft : LeftInverse invF toF := by
    intro x
    rcases x.2 with hx_eq | hx
    · apply Subtype.ext
      dsimp only [toF, invF]
      rw [hx_eq, dif_neg hG_not, dif_neg hH_not]
    · have hm : (φ ⟨x.1, hx⟩).1 ∈ (compSet H cH D : Set W) := (φ ⟨x.1, hx⟩).2
      apply Subtype.ext
      dsimp only [toF, invF]
      rw [dif_pos hx, dif_pos hm]
      have heta : (⟨(φ ⟨x.1, hx⟩).1, hm⟩ : ↥(compSet H cH D : Set W)) = φ ⟨x.1, hx⟩ := rfl
      rw [heta]
      exact congrArg (fun z : ↥(compSet G cG C : Set V) => z.1) (φ.left_inv ⟨x.1, hx⟩)
  have hright : RightInverse invF toF := by
    intro y
    rcases y.2 with hy_eq | hy
    · apply Subtype.ext
      dsimp only [toF, invF]
      rw [hy_eq, dif_neg hH_not, dif_neg hG_not]
    · have hm : (φ.symm ⟨y.1, hy⟩).1 ∈ (compSet G cG C : Set V) := (φ.symm ⟨y.1, hy⟩).2
      apply Subtype.ext
      dsimp only [toF, invF]
      rw [dif_pos hy, dif_pos hm]
      have heta : (⟨(φ.symm ⟨y.1, hy⟩).1, hm⟩ : ↥(compSet G cG C : Set V)) = φ.symm ⟨y.1, hy⟩ := rfl
      rw [heta]
      exact congrArg (fun z : ↥(compSet H cH D : Set W) => z.1) (φ.right_inv ⟨y.1, hy⟩)
  refine ⟨Set.mem_insert _ _, Set.mem_insert _ _, ⟨⟨toF, invF, hleft, hright⟩, ?_⟩, ?_⟩
  · intro a b
    have huG_C : uG.1 ∈ (compSet G cG C : Set V) := (mem_compSet_iff G cG C uG.1).mpr ⟨uG.2, huG_mem⟩
    have hvH_D : vH.1 ∈ (compSet H cH D : Set W) := (mem_compSet_iff H cH D vH.1).mpr ⟨vH.2, hvH_mem⟩
    rcases a.2 with ha_eq | ha <;> rcases b.2 with hb_eq | hb
    · change H.Adj (toF a).1 (toF b).1 ↔ G.Adj a.1 b.1
      dsimp only [toF]
      rw [ha_eq, hb_eq, dif_neg hG_not]
      simp
    · change H.Adj (toF a).1 (toF b).1 ↔ G.Adj a.1 b.1
      dsimp only [toF]
      rw [ha_eq, dif_neg hG_not, dif_pos hb, huniqG b.1 hb, huniqH _ (φ ⟨b.1, hb⟩).2]
      constructor
      · intro hval
        exact congrArg (fun z : ↥(compSet G cG C : Set V) => z.1)
          (φ.injective ((Subtype.ext hval : φ ⟨b.1, hb⟩ = ⟨vH.1, hvH_D⟩).trans hφ_root.symm))
      · intro hval
        have heq : (⟨b.1, hb⟩ : ↥(compSet G cG C : Set V)) = ⟨uG.1, huG_C⟩ := Subtype.ext hval
        exact congrArg Subtype.val ((congrArg φ heq).trans hφ_root)
    · have h1 : cG ∉ (compSet G cG C : Set V) := c_notMem_compSet G cG C
      change H.Adj (toF a).1 (toF b).1 ↔ G.Adj a.1 b.1
      dsimp only [toF]
      rw [hb_eq, G.adj_comm, H.adj_comm, dif_pos ha, dif_neg h1, huniqG a.1 ha, huniqH _ (φ ⟨a.1, ha⟩).2]
      constructor
      · intro hval
        exact congrArg (fun z : ↥(compSet G cG C : Set V) => z.1)
          (φ.injective ((Subtype.ext hval : φ ⟨a.1, ha⟩ = ⟨vH.1, hvH_D⟩).trans hφ_root.symm))
      · intro hval
        have heq : (⟨a.1, ha⟩ : ↥(compSet G cG C : Set V)) = ⟨uG.1, huG_C⟩ := Subtype.ext hval
        exact congrArg Subtype.val ((congrArg φ heq).trans hφ_root)
    · change H.Adj (toF a).1 (toF b).1 ↔ G.Adj a.1 b.1
      dsimp only [toF]
      rw [dif_pos ha, dif_pos hb]
      exact φ.map_rel_iff (a := ⟨a.1, ha⟩) (b := ⟨b.1, hb⟩)
  · exact Subtype.ext (by
      change (toF ⟨cG, Set.mem_insert _ _⟩).1 = cH
      dsimp only [toF]
      rw [dif_neg hG_not])
private lemma rootedCompIso_of_path_r {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (hTG : G.IsTree) (hTH : H.IsTree)
    {r : ℕ} (_hr : 1 ≤ r) (cG : V) (cH : W)
    (_heccG : G.eccent cG = r) (_heccH : H.eccent cH = r)
    (C : (G.induce {cG}ᶜ).ConnectedComponent) (hC : card C.supp = r)
    {x : ({cG}ᶜ : Set V)} (hx_mem : x ∈ C.supp) (hx_dist : G.dist cG x.1 = r)
    (D : (H.induce {cH}ᶜ).ConnectedComponent) (hD : card D.supp = r)
    {y : ({cH}ᶜ : Set W)} (hy_mem : y ∈ D.supp) (hy_dist : H.dist cH y.1 = r) :
    RootedCompIso G cG C H cH D := by
  obtain ⟨p, hp, hplen, hfinG⟩ := comp_path_of_card_eq_dist G hTG cG C hx_mem hx_dist hC
  obtain ⟨q, hq, hqlen, hfinH⟩ := comp_path_of_card_eq_dist H hTH cH D hy_mem hy_dist hD
  obtain ⟨φp, hφp0, _⟩ := induce_support_iso_pathG_rooted G hTG p hp
  obtain ⟨φq, hφq0, _⟩ := induce_support_iso_pathG_rooted H hTH q hq
  have hfinG_set : (p.support.toFinset : Set V) = insert cG (compSet G cG C : Set V) := by
    rw [hfinG, coe_insert]
  have hfinH_set : (q.support.toFinset : Set W) = insert cH (compSet H cH D : Set W) := by
    rw [hfinH, coe_insert]
  have hmemG : ∀ {v : V}, v ∈ insert cG (compSet G cG C : Set V) ↔ v ∈ (p.support.toFinset : Set V) :=
    fun {v} => by rw [hfinG_set]
  have hmemH : ∀ {w : W}, w ∈ insert cH (compSet H cH D : Set W) ↔ w ∈ (q.support.toFinset : Set W) :=
    fun {w} => by rw [hfinH_set]
  have h1 : RootedIso G cG (insert cG (compSet G cG C : Set V)) (pathG (r + 1)) ⟨0, Nat.zero_lt_succ r⟩ Set.univ := by
    refine ⟨Set.mem_insert _ _, Set.mem_univ _, ?_, ?_⟩
    · refine ⟨⟨fun z =>
          ⟨⟨(φp ⟨z.1, hmemG.mp z.2⟩).val, by
            have := (φp ⟨z.1, hmemG.mp z.2⟩).isLt; omega⟩, Set.mem_univ _⟩,
        fun u =>
          ⟨(φp.symm ⟨u.1.val, by rw [hplen]; exact u.1.isLt⟩).1,
            hmemG.mpr (φp.symm ⟨u.1.val, by rw [hplen]; exact u.1.isLt⟩).2⟩,
        fun z => Subtype.ext (by
          dsimp only
          have hinv := congrArg (fun a : Fin (p.length + 1) => φp.symm a)
            (Fin.ext rfl : (⟨(φp ⟨z.1, hmemG.mp z.2⟩).val, (φp ⟨z.1, hmemG.mp z.2⟩).isLt⟩ : Fin (p.length + 1)) =
              φp ⟨z.1, hmemG.mp z.2⟩)
          exact congrArg Subtype.val (hinv.trans (φp.left_inv ⟨z.1, hmemG.mp z.2⟩))),
        fun u => Subtype.ext (Fin.ext (by
          dsimp only
          have heta : (⟨(φp.symm ⟨u.1.val, by rw [hplen]; exact u.1.isLt⟩).1,
              hmemG.mp (hmemG.mpr (φp.symm ⟨u.1.val, by rw [hplen]; exact u.1.isLt⟩).2)⟩ :
              ↥(p.support.toFinset : Set V)) =
              φp.symm ⟨u.1.val, by rw [hplen]; exact u.1.isLt⟩ := rfl
          rw [heta]
          exact congrArg Fin.val (φp.right_inv ⟨u.1.val, by rw [hplen]; exact u.1.isLt⟩)))⟩, ?_⟩
      intro a b
      have h1a : (G.induce (insert cG (compSet G cG C : Set V))).Adj a b ↔
          (G.induce (p.support.toFinset : Set V)).Adj
            ⟨a.1, hmemG.mp a.2⟩ ⟨b.1, hmemG.mp b.2⟩ := Iff.rfl
      have h2a := φp.map_rel_iff
        (a := ⟨a.1, hmemG.mp a.2⟩) (b := ⟨b.1, hmemG.mp b.2⟩)
      exact h2a.trans h1a.symm
    · apply Subtype.ext
      apply Fin.ext
      change (φp ⟨cG, hmemG.mp (Set.mem_insert _ _)⟩).val = 0
      exact congrArg Fin.val hφp0
  have h2 : RootedIso H cH (insert cH (compSet H cH D : Set W)) (pathG (r + 1)) ⟨0, Nat.zero_lt_succ r⟩ Set.univ := by
    refine ⟨Set.mem_insert _ _, Set.mem_univ _, ?_, ?_⟩
    · refine ⟨⟨fun z =>
          ⟨⟨(φq ⟨z.1, hmemH.mp z.2⟩).val, by
            have := (φq ⟨z.1, hmemH.mp z.2⟩).isLt; omega⟩, Set.mem_univ _⟩,
        fun u =>
          ⟨(φq.symm ⟨u.1.val, by rw [hqlen]; exact u.1.isLt⟩).1,
            hmemH.mpr (φq.symm ⟨u.1.val, by rw [hqlen]; exact u.1.isLt⟩).2⟩,
        fun z => Subtype.ext (by
          dsimp only
          have hinv := congrArg (fun a : Fin (q.length + 1) => φq.symm a)
            (Fin.ext rfl : (⟨(φq ⟨z.1, hmemH.mp z.2⟩).val, (φq ⟨z.1, hmemH.mp z.2⟩).isLt⟩ : Fin (q.length + 1)) =
              φq ⟨z.1, hmemH.mp z.2⟩)
          exact congrArg Subtype.val (hinv.trans (φq.left_inv ⟨z.1, hmemH.mp z.2⟩))),
        fun u => Subtype.ext (Fin.ext (by
          dsimp only
          have heta : (⟨(φq.symm ⟨u.1.val, by rw [hqlen]; exact u.1.isLt⟩).1,
              hmemH.mp (hmemH.mpr (φq.symm ⟨u.1.val, by rw [hqlen]; exact u.1.isLt⟩).2)⟩ :
              ↥(q.support.toFinset : Set W)) =
              φq.symm ⟨u.1.val, by rw [hqlen]; exact u.1.isLt⟩ := rfl
          rw [heta]
          exact congrArg Fin.val (φq.right_inv ⟨u.1.val, by rw [hqlen]; exact u.1.isLt⟩)))⟩, ?_⟩
      intro a b
      have h1a : (H.induce (insert cH (compSet H cH D : Set W))).Adj a b ↔
          (H.induce (q.support.toFinset : Set W)).Adj
            ⟨a.1, hmemH.mp a.2⟩ ⟨b.1, hmemH.mp b.2⟩ := Iff.rfl
      have h2a := φq.map_rel_iff
        (a := ⟨a.1, hmemH.mp a.2⟩) (b := ⟨b.1, hmemH.mp b.2⟩)
      exact h2a.trans h1a.symm
    · apply Subtype.ext
      apply Fin.ext
      change (φq ⟨cH, hmemH.mp (Set.mem_insert _ _)⟩).val = 0
      exact congrArg Fin.val hφq0
  exact h1.trans h2.symm
private lemma deg_one_of_path_r_end {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {r : ℕ} (hr : 2 ≤ r) (c : U)
    (C : (T.induce {c}ᶜ).ConnectedComponent) (hC : card C.supp = r)
    {x : ({c}ᶜ : Set U)} (hx_mem : x ∈ C.supp) (hx_dist : T.dist c x.1 = r) :
    T.degree x.1 = 1 := by
  obtain ⟨p, hp, hplen, hfin⟩ := comp_path_of_card_eq_dist T hT c C hx_mem hx_dist hC
  obtain ⟨φp, hφp0, hφpr⟩ := induce_support_iso_pathG_rooted T hT p hp
  have hsub : T.neighborFinset x.1 ⊆
      (p.support.toFinset.erase x.1).filter (fun z => T.Adj x.1 z) := by
    intro z hz
    rw [mem_neighborFinset] at hz
    have hx_C : x.1 ∈ compSet T c C := (mem_compSet_iff T c C x.1).mpr ⟨x.2, hx_mem⟩
    have hz_in : z ∈ insert c (compSet T c C) := by
      by_cases hzc : z = c
      · rw [hzc]; exact mem_insert_self c _
      · refine mem_insert_of_mem ((mem_compSet_iff T c C z).mpr ⟨hzc, ?_⟩)
        have hreach : (T.induce {c}ᶜ).Reachable x ⟨z, hzc⟩ := Adj.reachable hz
        rw [mem_supp_iff] at hx_mem ⊢
        exact (sound hreach).symm.trans hx_mem
    rw [← hfin] at hz_in
    exact mem_filter.mpr ⟨mem_erase.mpr ⟨hz.ne.symm, hz_in⟩, hz⟩
  have hx_mem_fin : x.1 ∈ p.support.toFinset := List.mem_toFinset.mpr p.end_mem_support
  have hdeg_ind : (T.induce (p.support.toFinset : Set U)).degree ⟨x.1, hx_mem_fin⟩ = 1 := by
    rw [← φp.degree_eq ⟨x.1, hx_mem_fin⟩, hφpr]
    rw [← (pathG (p.length + 1)).card_neighborFinset_eq_degree]
    have heq : (pathG (p.length + 1)).neighborFinset ⟨p.length, Nat.lt_succ_self p.length⟩ =
        {⟨p.length - 1, by omega⟩} := by
      ext j
      rw [mem_neighborFinset, mem_singleton]
      constructor
      · rintro (h | h) <;> apply Fin.ext <;> dsimp only [pathG] at h ⊢
        · have := j.isLt; omega
        · omega
      · intro hj
        subst hj
        right; dsimp only; omega
    rw [heq, card_singleton]
  let f : (p.support.toFinset : Set U) ↪ U := ⟨Subtype.val, val_injective⟩
  have hsub2 : T.neighborFinset x.1 ⊆
      ((T.induce (p.support.toFinset : Set U)).neighborFinset ⟨x.1, hx_mem_fin⟩).map f := by
    intro z hz
    have hzf := mem_filter.mp (hsub hz)
    have hzp : z ∈ (p.support.toFinset : Set U) := (mem_erase.mp hzf.1).2
    refine mem_map.mpr ⟨⟨z, hzp⟩, ?_, rfl⟩
    rw [mem_neighborFinset]
    exact hzf.2
  have hdeg_le : T.degree x.1 ≤ (T.induce (p.support.toFinset : Set U)).degree ⟨x.1, hx_mem_fin⟩ := by
    rw [← T.card_neighborFinset_eq_degree,
      ← (T.induce (p.support.toFinset : Set U)).card_neighborFinset_eq_degree, ← card_map f]
    exact card_le_card hsub2
  have : Nontrivial U := ⟨⟨c, x.1, Ne.symm x.2⟩⟩
  have hpos := hT.preconnected.degree_pos_of_nontrivial x.1
  omega
private lemma diam_sub_of_path_r_end {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {r : ℕ} (hr : 2 ≤ r) (hdiam : T.diam = 2 * r)
    (c : U) (hecc : T.eccent c = r) (hdeg2 : T.degree c = 2)
    (Ca Cb : (T.induce {c}ᶜ).ConnectedComponent) (hCab : Ca ≠ Cb)
    (hCb : card Cb.supp = r)
    {x_b : ({c}ᶜ : Set U)} (hxb_mem : x_b ∈ Cb.supp) (hxb_dist : T.dist c x_b.1 = r) :
    T.degree x_b.1 = 1 ∧ (T.induce {x_b.1}ᶜ).diam = 2 * r - 1 := by
  have hx_deg1 : T.degree x_b.1 = 1 := deg_one_of_path_r_end T hT hr c Cb hCb hxb_mem hxb_dist
  refine ⟨hx_deg1, ?_⟩
  have hT' : (T.induce {x_b.1}ᶜ).IsTree := induce_compl_singleton_isTree_of_deg_one T hT hx_deg1
  have : Nonempty ({x_b.1}ᶜ : Set U) := hT'.connected.nonempty
  have hdist_eq := dist_induce_eq_of_isTree T hT {x_b.1}ᶜ hT'
  have hall_comp : ∀ C : (T.induce {c}ᶜ).ConnectedComponent, C = Ca ∨ C = Cb := by
    intro C; by_contra hnot; push Not at hnot
    have hcard_cc : card (T.induce {c}ᶜ).ConnectedComponent = 2 := by
      rw [card_connectedComponent_eq_degree T hT c, hdeg2]
    have h3 : ({Ca, Cb, C} : Finset (T.induce {c}ᶜ).ConnectedComponent).card ≤ 2 :=
      hcard_cc ▸ card_le_univ _
    have hc3 : ({Ca, Cb, C} : Finset (T.induce {c}ᶜ).ConnectedComponent).card = 3 := by
      rw [card_insert_of_notMem, card_pair hnot.2.symm]
      simp [hCab, hnot.1.symm]
    omega
  obtain ⟨_, _, huniq_b⟩ := comp_unique_dist_r_of_card_eq_r T hT c Cb (by omega) hecc hCb
    x_b hxb_mem hxb_dist
  have hCb_lt : ∀ y : ({x_b.1}ᶜ : Set U), y.1 ∈ compSet T c Cb → T.dist c y.1 ≤ r - 1 := by
    intro y hy
    have hle := dist_le_of_eccent T hT (u := y.1) hecc
    by_contra hgt
    obtain ⟨hy1, hy2⟩ := (mem_compSet_iff T c Cb y.1).mp hy
    have heq := (huniq_b ⟨⟨y.1, hy1⟩, hy2⟩ (by dsimp; omega)).trans (huniq_b ⟨x_b, hxb_mem⟩ hxb_dist).symm
    exact y.2 (congrArg (fun z : Cb.supp => z.1.1) heq)
  have hle_diam : (T.induce {x_b.1}ᶜ).diam ≤ 2 * r - 1 := by
    obtain ⟨a, b, hab⟩ := (T.induce {x_b.1}ᶜ).exists_dist_eq_diam
    rw [← hab, hdist_eq]
    by_cases hac : a.1 = c <;> by_cases hbc : b.1 = c
    · rw [hac, hbc, dist_self]; omega
    · rw [hac]; have := dist_le_of_eccent T hT (u := b.1) hecc; omega
    · rw [hbc, dist_comm]; have := dist_le_of_eccent T hT (u := a.1) hecc; omega
    · let CA := (T.induce {c}ᶜ).connectedComponentMk ⟨a.1, hac⟩
      let CB := (T.induce {c}ᶜ).connectedComponentMk ⟨b.1, hbc⟩
      have ha_mem : a.1 ∈ compSet T c CA := (mem_compSet_iff T c CA a.1).mpr ⟨hac, rfl⟩
      have hb_mem : b.1 ∈ compSet T c CB := (mem_compSet_iff T c CB b.1).mpr ⟨hbc, rfl⟩
      rcases hall_comp CA with hA | hA <;> rcases hall_comp CB with hB | hB
      · -- Both in Ca: dist(a, b) <= dist(a, root) + dist(root, b) <= (r-1)+(r-1) = 2r - 2!
        rw [hA] at ha_mem; rw [hB] at hb_mem
        let u := (existsUnique_root_of_component T hT c Ca).choose
        have h1 : T.dist a.1 c = T.dist a.1 u.1 + 1 := dist_comp_eq_one_add_root T hT c Ca ha_mem
        have h2 : T.dist b.1 c = T.dist b.1 u.1 + 1 := dist_comp_eq_one_add_root T hT c Ca hb_mem
        have htri := hT.connected.dist_triangle (u := a.1) (v := u.1) (w := b.1)
        have ha_le := dist_le_of_eccent T hT (u := a.1) hecc
        have hb_le := dist_le_of_eccent T hT (u := b.1) hecc
        rw [dist_comm (u := c) (v := a.1)] at ha_le
        rw [dist_comm (u := c) (v := b.1)] at hb_le
        rw [dist_comm (u := u.1) (v := b.1)] at htri
        omega
      · rw [hA] at ha_mem; rw [hB] at hb_mem
        rw [dist_add_of_ne_comp T hT c hCab ha_mem hb_mem]
        have ha_le := dist_le_of_eccent T hT (u := a.1) hecc
        have hb_le := hCb_lt b hb_mem
        rw [dist_comm (u := c) (v := a.1)] at ha_le
        omega
      · rw [hA] at ha_mem; rw [hB] at hb_mem
        rw [dist_add_of_ne_comp T hT c hCab.symm ha_mem hb_mem]
        have ha_le := hCb_lt a ha_mem
        have hb_le := dist_le_of_eccent T hT (u := b.1) hecc
        rw [dist_comm (u := c) (v := a.1)] at ha_le
        omega
      · rw [hA] at ha_mem; rw [hB] at hb_mem
        have ha_le := hCb_lt a ha_mem
        have hb_le := hCb_lt b hb_mem
        have htri := hT.connected.dist_triangle (u := a.1) (v := c) (w := b.1)
        rw [dist_comm (u := c) (v := a.1)] at ha_le
        omega
  obtain ⟨C_other, hC_ne, x_a, hxa_mem, hxa_dist⟩ := exists_other_diam_comp T hT hr hdiam c hecc Cb
  have hC_eq : C_other = Ca := (hall_comp C_other).resolve_right hC_ne
  subst hC_eq
  have hxa_ne_xb : x_a ≠ x_b.1 := fun h =>
    (Finset.disjoint_left.mp (compSet_disjoint T c hCab) hxa_mem)
      (h ▸ (mem_compSet_iff T c Cb x_b.1).mpr ⟨x_b.2, hxb_mem⟩)
  obtain ⟨pb, hpb, hpblen⟩ := hT.connected.exists_path_of_dist c x_b.1
  have hpb_nn : ¬ pb.Nil := not_nil_of_ne (Ne.symm x_b.2)
  let y_prev := pb.penultimate
  have hy_ne_xb : y_prev ≠ x_b.1 := (pb.adj_penultimate hpb_nn).ne
  have hy_dist : T.dist c y_prev = r - 1 := by
    have hp_take : (pb.take (pb.length - 1)).IsPath := hpb.take (pb.length - 1)
    have hlen_t : (pb.take (pb.length - 1)).length = r - 1 := by
      rw [Walk.take_length, hpblen, hxb_dist]
      omega
    have hend : pb.getVert (pb.length - 1) = y_prev := rfl
    have h1 := isTree_dist_eq_length_of_isPath T hT (pb.take (pb.length - 1)) hp_take
    rw [hlen_t, hend] at h1
    exact h1.symm
  have hy_ne_c : y_prev ≠ c := fun h => by rw [h, dist_self] at hy_dist; omega
  have hy_Cb : y_prev ∈ compSet T c Cb :=
    mem_compSet_of_walk_from_c T c Cb ((mem_compSet_iff T c Cb x_b.1).mpr ⟨x_b.2, hxb_mem⟩)
      hpb (getVert_mem_support pb (pb.length - 1)) hy_ne_c
  have hge_diam : 2 * r - 1 ≤ (T.induce {x_b.1}ᶜ).diam := by
    have hediam' : (T.induce {x_b.1}ᶜ).ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hT'.connected
    have h1 := dist_le_diam hediam' (u := ⟨x_a, hxa_ne_xb⟩) (v := ⟨y_prev, hy_ne_xb⟩)
    rw [hdist_eq, dist_add_of_ne_comp T hT c hCab hxa_mem hy_Cb, dist_comm (u := x_a) (v := c),
      hxa_dist, hy_dist] at h1
    omega
  omega
set_option maxHeartbeats 800000 in
private lemma boundary_contra_shifted_leaf {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (hTG : G.IsTree) (hTH : H.IsTree)
    (σ : V ≃ W) (hσ : ∀ v : V, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ))
    (hdeg : ∀ v : V, (G.neighborSet v).ncard = (H.neighborSet (σ v)).ncard)
    (hnonpath : ∃ v : V, 3 ≤ (G.neighborSet v).ncard)
    {r : ℕ} (hr : 2 ≤ r) (hdiamG : G.diam = 2 * r) (hdiamH : H.diam = 2 * r)
    (cG : V) (cH : W) (heccG : G.eccent cG = r) (heccH : H.eccent cH = r)
    (hdegG2 : G.degree cG = 2) (hdegH2 : H.degree cH = 2)
    (hnoLeafG : ∀ v : V, G.Adj cG v → 2 ≤ G.degree v)
    (hnoLeafH : ∀ w : W, H.Adj cH w → 2 ≤ H.degree w)
    {M : ℕ} (hM : r + 1 ≤ M)
    (C₀ C₁ : (G.induce {cG}ᶜ).ConnectedComponent) (hC01 : C₀ ≠ C₁)
    (hC0_card : card C₀.supp = M) (hC1_card : card C₁.supp = r)
    {xd : ({cG}ᶜ : Set V)} (hxd_mem : xd ∈ C₁.supp) (hxd_dist : G.dist cG xd.1 = r)
    (D₀ D₁ : (H.induce {cH}ᶜ).ConnectedComponent) (hD01 : D₀ ≠ D₁)
    (hD0_card : card D₀.supp = M) (hD1_card : card D₁.supp = r)
    {yd : ({cH}ᶜ : Set W)} (hyd_mem : yd ∈ D₁.supp) (hyd_dist : H.dist cH yd.1 = r)
    (hσxd_D0 : σ xd.1 ∈ compSet H cH D₀) :
    False := by
  have hTG' : ∀ C : (G.induce {cG}ᶜ).ConnectedComponent, C = C₀ ∨ C = C₁ := by
    intro C; by_contra hnot; push Not at hnot
    have hcard_cc : card (G.induce {cG}ᶜ).ConnectedComponent = 2 := by
      rw [card_connectedComponent_eq_degree G hTG cG, hdegG2]
    have h3 : ({C₀, C₁, C} : Finset _).card ≤ 2 := hcard_cc ▸ card_le_univ _
    have hc3 : ({C₀, C₁, C} : Finset _).card = 3 := by
      rw [card_insert_of_notMem, card_pair hnot.2.symm]
      simp [hC01, hnot.1.symm]
    omega
  have hTH' : ∀ D : (H.induce {cH}ᶜ).ConnectedComponent, D = D₀ ∨ D = D₁ := by
    intro D; by_contra hnot; push Not at hnot
    have hcard_cc : card (H.induce {cH}ᶜ).ConnectedComponent = 2 := by
      rw [card_connectedComponent_eq_degree H hTH cH, hdegH2]
    have h3 : ({D₀, D₁, D} : Finset _).card ≤ 2 := hcard_cc ▸ card_le_univ _
    have hc3 : ({D₀, D₁, D} : Finset _).card = 3 := by
      rw [card_insert_of_notMem, card_pair hnot.2.symm]
      simp [hD01, hnot.1.symm]
    omega
  obtain ⟨hxd_deg1, hxd_diam⟩ :=
    diam_sub_of_path_r_end G hTG hr hdiamG cG heccG hdegG2 C₀ C₁ hC01 hC1_card hxd_mem hxd_dist
  obtain ⟨hyd_deg1, hyd_diam⟩ :=
    diam_sub_of_path_r_end H hTH hr hdiamH cH heccH hdegH2 D₀ D₁ hD01 hD1_card hyd_mem hyd_dist
  obtain ⟨ψ⟩ := hσ xd.1
  have hσxd_deg1 : H.degree (σ xd.1) = 1 := by
    rw [← ncard_neighborSet_eq_degree, ← hdeg xd.1, ncard_neighborSet_eq_degree, hxd_deg1]
  have hσxd_diam : (H.induce {σ xd.1}ᶜ).diam = 2 * r - 1 :=
    (iso_diam_eq _ _ ψ).symm.trans hxd_diam
  have infoG := bicenter_del_leaf_info G hTG hr hdiamG cG heccG hdegG2 C₁ C₀ hC01.symm hxd_deg1
    ((mem_compSet_iff G cG C₁ xd.1).mpr ⟨xd.2, hxd_mem⟩) hxd_diam
  have infoH := bicenter_del_leaf_info H hTH hr hdiamH cH heccH hdegH2 D₀ D₁ hD01 hσxd_deg1
    hσxd_D0 hσxd_diam
  by_cases hr2 : r = 2
  · obtain ⟨k₀, ⟨hk0_mem, hk0_adj⟩, hk0_uniq⟩ := existsUnique_root_of_component H hTH cH D₀
    have hD0_sub : compSet H cH D₀ ⊆ {k₀.1, σ xd.1} := by
      intro y hy
      rw [mem_insert, mem_singleton]
      by_cases hyw : y = σ xd.1
      · exact Or.inr hyw
      · left
        have hd_le := infoH.1 y hy hyw
        have hyc : y ≠ cH := fun h => c_notMem_compSet H cH D₀ (h ▸ hy)
        have hd_pos : 0 < H.dist cH y := hTH.connected.pos_dist_of_ne hyc.symm
        have hd1 : H.dist cH y = 1 := by omega
        have hadj : H.Adj cH y := dist_eq_one_iff_adj.mp hd1
        obtain ⟨h1, h2⟩ := (mem_compSet_iff H cH D₀ y).mp hy
        exact congrArg Subtype.val (hk0_uniq ⟨y, h1⟩ ⟨h2, hadj⟩)
    have hD0_le2 : card D₀.supp ≤ 2 := by
      rw [← compSet_card_eq]
      exact (card_le_card hD0_sub).trans ((Finset.card_insert_le _ _).trans (by simp))
    omega
  have hr3 : 3 ≤ r := by omega
  let u_C0 := (existsUnique_root_of_component G hTG cG C₀).choose
  let v_D1 := (existsUnique_root_of_component H hTH cH D₁).choose
  have huC0_mem : u_C0 ∈ C₀.supp := (existsUnique_root_of_component G hTG cG C₀).choose_spec.1.1
  have huC0_adj : G.Adj cG u_C0.1 := (existsUnique_root_of_component G hTG cG C₀).choose_spec.1.2
  have hvD1_mem : v_D1 ∈ D₁.supp := (existsUnique_root_of_component H hTH cH D₁).choose_spec.1.1
  have hvD1_adj : H.Adj cH v_D1.1 := (existsUnique_root_of_component H hTH cH D₁).choose_spec.1.2
  have hcG_x : cG ∈ ({xd.1}ᶜ : Set V) := Ne.symm xd.2
  have hu_x : u_C0.1 ∈ ({xd.1}ᶜ : Set V) := fun h =>
    (Finset.disjoint_left.mp (compSet_disjoint G cG hC01)
      ((mem_compSet_iff G cG C₀ u_C0.1).mpr ⟨u_C0.2, huC0_mem⟩))
      (h ▸ (mem_compSet_iff G cG C₁ xd.1).mpr ⟨xd.2, hxd_mem⟩)
  have hcH_w : cH ∈ ({σ xd.1}ᶜ : Set W) := fun h => c_notMem_compSet H cH D₀ (h ▸ hσxd_D0)
  have hv_w : v_D1.1 ∈ ({σ xd.1}ᶜ : Set W) := fun h =>
    (Finset.disjoint_left.mp (compSet_disjoint H cH hD01) hσxd_D0)
      (h ▸ (mem_compSet_iff H cH D₁ v_D1.1).mpr ⟨v_D1.2, hvD1_mem⟩)
  let cG' : ({xd.1}ᶜ : Set V) := ⟨cG, hcG_x⟩
  let u_C0' : ({xd.1}ᶜ : Set V) := ⟨u_C0.1, hu_x⟩
  let cH' : ({σ xd.1}ᶜ : Set W) := ⟨cH, hcH_w⟩
  let v_D1' : ({σ xd.1}ᶜ : Set W) := ⟨v_D1.1, hv_w⟩
  have hψ_pair : ψ u_C0' = cH' ∧ ψ cG' = v_D1' := by
    have hbiH := infoH.2.1
    have hbiG := infoG.2.1
    have hu_in : ψ u_C0' = cH' ∨ ψ u_C0' = v_D1' := by
      by_contra hnot
      push Not at hnot
      have hlt := hbiH.2.2 (ψ u_C0') hnot.1 hnot.2
      rw [iso_eccent_eq _ _ ψ u_C0', hbiG.2.1] at hlt
      exact absurd hlt (lt_irrefl _)
    have hc_in : ψ cG' = cH' ∨ ψ cG' = v_D1' := by
      by_contra hnot
      push Not at hnot
      have hlt := hbiH.2.2 (ψ cG') hnot.1 hnot.2
      rw [iso_eccent_eq _ _ ψ cG', hbiG.1] at hlt
      exact absurd hlt (lt_irrefl _)
    rcases hu_in with hu1 | hu2
    · refine ⟨hu1, ?_⟩
      rcases hc_in with hc1 | hc2
      · exact False.elim (huC0_adj.ne.symm (congrArg Subtype.val (ψ.injective (hu1.trans hc1.symm))))
      · exact hc2
    · -- Impossible because dist < side around u_C0' has size M, whereas around v_D1' has size r < M!
      have hcard_u : (univ.filter fun z' : ({xd.1}ᶜ : Set V) =>
          (G.induce {xd.1}ᶜ).dist z' u_C0' < (G.induce {xd.1}ᶜ).dist z' cG').card = M := by
        simpa [hC0_card, u_C0', cG', u_C0] using infoG.2.2.1
      have hcard_v : (univ.filter fun w' : ({σ xd.1}ᶜ : Set W) =>
          (H.induce {σ xd.1}ᶜ).dist w' v_D1' < (H.induce {σ xd.1}ᶜ).dist w' cH').card = r := by
        simpa [hD1_card, v_D1', cH', v_D1] using infoH.2.2.1
      have hc1 : ψ cG' = cH' := by
        rcases hc_in with hc1 | hc2
        · exact hc1
        · exact False.elim (huC0_adj.ne.symm (congrArg Subtype.val (ψ.injective (hu2.trans hc2.symm))))
      have heq_card : (univ.filter fun z' : ({xd.1}ᶜ : Set V) =>
          (G.induce {xd.1}ᶜ).dist z' u_C0' < (G.induce {xd.1}ᶜ).dist z' cG').card =
          (univ.filter fun w' : ({σ xd.1}ᶜ : Set W) =>
          (H.induce {σ xd.1}ᶜ).dist w' v_D1' < (H.induce {σ xd.1}ᶜ).dist w' cH').card := by
        refine card_bij (fun z' _ => ψ z') ?_ ?_ ?_
        · intro z' hz'
          rw [mem_filter] at hz' ⊢
          refine ⟨mem_univ _, ?_⟩
          rw [← hu2, ← hc1, iso_dist_eq _ _ ψ z' u_C0', iso_dist_eq _ _ ψ z' cG']
          exact hz'.2
        · intro a _ b _ hab; exact ψ.injective hab
        · intro w' hw'
          rw [mem_filter] at hw'
          refine ⟨ψ.symm w', mem_filter.mpr ⟨mem_univ _, ?_⟩, ψ.apply_symm_apply w'⟩
          rw [← iso_dist_eq _ _ ψ (ψ.symm w') u_C0', ← iso_dist_eq _ _ ψ (ψ.symm w') cG',
            ψ.apply_symm_apply, hu2, hc1]
          exact hw'.2
      rw [hcard_u, hcard_v] at heq_card; omega
  obtain ⟨φG_u, hφGu⟩ := infoG.2.2.2.2.1
  obtain ⟨φH_c, hφHc⟩ := infoH.2.2.2.2.2
  have hside_ψ : ∀ z' : ({xd.1}ᶜ : Set V),
      ((G.induce {xd.1}ᶜ).dist z' u_C0' < (G.induce {xd.1}ᶜ).dist z' cG') ↔
      ((H.induce {σ xd.1}ᶜ).dist (ψ z') cH' < (H.induce {σ xd.1}ᶜ).dist (ψ z') v_D1') := by
    intro z'
    rw [← hψ_pair.1, ← hψ_pair.2, iso_dist_eq _ _ ψ z' u_C0', iso_dist_eq _ _ ψ z' cG']
  let SG_side : Set ({xd.1}ᶜ : Set V) :=
    {z' : ({xd.1}ᶜ : Set V) | (G.induce {xd.1}ᶜ).dist z' u_C0' < (G.induce {xd.1}ᶜ).dist z' cG'}
  let SH_side : Set ({σ xd.1}ᶜ : Set W) :=
    {w' : ({σ xd.1}ᶜ : Set W) | (H.induce {σ xd.1}ᶜ).dist w' cH' < (H.induce {σ xd.1}ᶜ).dist w' v_D1'}
  let ψ_side : (G.induce {xd.1}ᶜ).induce SG_side ≃g (H.induce {σ xd.1}ᶜ).induce SH_side :=
    ⟨⟨fun z' => ⟨ψ z'.1, (hside_ψ z'.1).mp z'.2⟩,
      fun w' => ⟨ψ.symm w'.1, (hside_ψ (ψ.symm w'.1)).mpr (by rw [ψ.apply_symm_apply]; exact w'.2)⟩,
      fun _ => Subtype.ext (ψ.symm_apply_apply _),
      fun _ => Subtype.ext (ψ.apply_symm_apply _)⟩, @fun _ _ => ψ.map_rel_iff⟩
  let ψ_sub : G.induce (compSet G cG C₀ : Set V) ≃g
      H.induce (insert cH ((compSet H cH D₀).erase (σ xd.1) : Set W)) :=
    φG_u.symm.trans (ψ_side.trans φH_c)
  have hψ_sub_root : ψ_sub ⟨u_C0.1, (mem_compSet_iff G cG C₀ u_C0.1).mpr ⟨u_C0.2, huC0_mem⟩⟩ =
      ⟨cH, Set.mem_insert _ _⟩ := by
    change φH_c (ψ_side (φG_u.symm ⟨u_C0.1, (mem_compSet_iff G cG C₀ u_C0.1).mpr ⟨u_C0.2, huC0_mem⟩⟩)) = _
    have hu_side : (G.induce {xd.1}ᶜ).dist u_C0' u_C0' < (G.induce {xd.1}ᶜ).dist u_C0' cG' := by
      rw [dist_self, dist_comm, dist_eq_one_iff_adj.mpr (show (G.induce {xd.1}ᶜ).Adj cG' u_C0' from huC0_adj)]
      omega
    have h1 : φG_u.symm ⟨u_C0.1, (mem_compSet_iff G cG C₀ u_C0.1).mpr ⟨u_C0.2, huC0_mem⟩⟩ =
        (⟨u_C0', hu_side⟩ : SG_side) := φG_u.symm_apply_eq.mpr hφGu.symm
    rw [h1]
    have hc_side : (H.induce {σ xd.1}ᶜ).dist cH' cH' < (H.induce {σ xd.1}ᶜ).dist cH' v_D1' := by
      rw [dist_self, dist_eq_one_iff_adj.mpr (show (H.induce {σ xd.1}ᶜ).Adj cH' v_D1' from hvD1_adj)]
      omega
    have h2 : ψ_side ⟨u_C0', hu_side⟩ = (⟨cH', hc_side⟩ : SH_side) := Subtype.ext hψ_pair.1
    rw [h2, hφHc]
  let SG_drop := univ.filter fun v : V => G.degree v = 1 ∧ (G.induce {v}ᶜ).diam = 2 * r - 1
  let SH_drop := univ.filter fun w : W => H.degree w = 1 ∧ (H.induce {w}ᶜ).diam = 2 * r - 1
  have hdrop_eq : SG_drop.card = SH_drop.card := by
    refine card_bij (fun v _ => σ v) ?_ (fun _ _ _ _ h => σ.injective h) ?_
    · intro v hv
      rw [mem_filter] at hv ⊢
      obtain ⟨φv⟩ := hσ v
      refine ⟨mem_univ _, ?_, (iso_diam_eq _ _ φv).symm.trans hv.2.2⟩
      rw [← ncard_neighborSet_eq_degree, ← hdeg v, ncard_neighborSet_eq_degree, hv.2.1]
    · intro w hw
      rw [mem_filter] at hw
      obtain ⟨φv⟩ := hσ (σ.symm w)
      rw [σ.apply_symm_apply] at φv
      refine ⟨σ.symm w, mem_filter.mpr ⟨mem_univ _, ?_, (iso_diam_eq _ _ φv).trans hw.2.2⟩,
        σ.apply_symm_apply w⟩
      have hd := hdeg (σ.symm w)
      rw [σ.apply_symm_apply, ncard_neighborSet_eq_degree, ncard_neighborSet_eq_degree] at hd
      omega
  have hSH_exact : SH_drop = {yd.1, σ xd.1} := by
    ext w
    rw [mem_insert, mem_singleton, mem_filter]
    constructor
    · rintro ⟨_, hw1, hwdiam⟩
      by_contra hnot; push Not at hnot
      have hwc : w ≠ cH := by
        rintro rfl
        omega
      let Dw := (H.induce {cH}ᶜ).connectedComponentMk ⟨w, hwc⟩
      have hw_mem : w ∈ compSet H cH Dw := (mem_compSet_iff H cH Dw w).mpr ⟨hwc, rfl⟩
      have hyd_ne_w : yd.1 ≠ w := hnot.1.symm
      have hsw_ne_w : σ xd.1 ≠ w := hnot.2.symm
      have hTH_del : (H.induce {w}ᶜ).IsTree := induce_compl_singleton_isTree_of_deg_one H hTH hw1
      have : Nonempty ({w}ᶜ : Set W) := hTH_del.connected.nonempty
      have hdist_yw : (H.induce {w}ᶜ).dist ⟨yd.1, hyd_ne_w⟩ ⟨σ xd.1, hsw_ne_w⟩ = 2 * r := by
        rw [dist_induce_eq_of_isTree H hTH {w}ᶜ hTH_del, dist_comm]
        rw [dist_add_of_ne_comp H hTH cH hD01 hσxd_D0 ((mem_compSet_iff H cH D₁ yd.1).mpr ⟨yd.2, hyd_mem⟩)]
        have h1 := dist_le_of_eccent H hTH (u := σ xd.1) heccH
        have hsw_r : H.dist cH (σ xd.1) = r := by
          obtain ⟨D_o, hDo_ne, y0H, hy0_mem, hy0_dist⟩ := exists_other_diam_comp H hTH hr hdiamH cH heccH D₁
          have hDo_eq : D_o = D₀ := (hTH' D_o).resolve_right hDo_ne
          subst hDo_eq
          by_contra hlt_r
          have hy0_ne : y0H ≠ σ xd.1 := fun h => hlt_r (h ▸ hy0_dist)
          have := infoH.1 y0H hy0_mem hy0_ne
          have hle := dist_le_of_eccent H hTH (u := y0H) heccH
          omega
        rw [dist_comm (u := σ xd.1) (v := cH), hsw_r, hyd_dist]
        omega
      have hediam' : (H.induce {w}ᶜ).ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hTH_del.connected
      have hle := dist_le_diam hediam' (u := ⟨yd.1, hyd_ne_w⟩) (v := ⟨σ xd.1, hsw_ne_w⟩)
      rw [hdist_yw, hwdiam] at hle
      omega
    · rintro (rfl | rfl)
      · exact ⟨mem_univ _, hyd_deg1, hyd_diam⟩
      · exact ⟨mem_univ _, hσxd_deg1, hσxd_diam⟩
  have hne_yw : yd.1 ≠ σ xd.1 := fun h =>
    (Finset.disjoint_left.mp (compSet_disjoint H cH hD01) hσxd_D0)
      (h ▸ (mem_compSet_iff H cH D₁ yd.1).mpr ⟨yd.2, hyd_mem⟩)
  have hSG_card : SG_drop.card = 2 := by rw [hdrop_eq, hSH_exact, card_pair hne_yw]
  have hxd_drop : xd.1 ∈ SG_drop := mem_filter.mpr ⟨mem_univ _, hxd_deg1, hxd_diam⟩
  have hex_q2 : ∃ q₂ ∈ SG_drop, q₂ ≠ xd.1 := by
    by_contra hnot; push Not at hnot
    have hsub : SG_drop ⊆ {xd.1} := fun z hz => mem_singleton.mpr (hnot z hz)
    have h1 := card_le_card hsub
    rw [hSG_card, card_singleton] at h1
    omega
  obtain ⟨q₂, hq2_drop, hq2_ne⟩ := hex_q2
  have hσq2_eq : σ q₂ = yd.1 := by
    have hm : σ q₂ ∈ SH_drop := by
      rw [mem_filter] at hq2_drop ⊢
      obtain ⟨φq⟩ := hσ q₂
      refine ⟨mem_univ _, ?_, (iso_diam_eq _ _ φq).symm.trans hq2_drop.2.2⟩
      rw [← ncard_neighborSet_eq_degree, ← hdeg q₂, ncard_neighborSet_eq_degree, hq2_drop.2.1]
    rw [hSH_exact, mem_insert, mem_singleton] at hm
    rcases hm with h | h
    · exact h
    · exact False.elim (hq2_ne (σ.injective h))
  rw [mem_filter] at hq2_drop
  obtain ⟨_, hq2_deg1, hq2_diam⟩ := hq2_drop
  have hq2_ne_cG : q₂ ≠ cG := by
    rintro rfl
    omega
  have hq2_C0 : q₂ ∈ compSet G cG C₀ := by
    let Cq := (G.induce {cG}ᶜ).connectedComponentMk ⟨q₂, hq2_ne_cG⟩
    have hm : q₂ ∈ compSet G cG Cq := (mem_compSet_iff G cG Cq q₂).mpr ⟨hq2_ne_cG, rfl⟩
    rcases hTG' Cq with h | h
    · rwa [h] at hm
    · rw [h] at hm
      obtain ⟨q2_1, q2_2⟩ := (mem_compSet_iff G cG C₁ q₂).mp hm
      have := deg_one_of_path_r_end G hTG hr cG C₁ hC1_card hxd_mem hxd_dist
      obtain ⟨C_o, hCo_ne, x0G, hx0_mem, hx0_dist⟩ := exists_other_diam_comp G hTG hr hdiamG cG heccG C₁
      have hCo_eq : C_o = C₀ := (hTG' C_o).resolve_right hCo_ne
      subst hCo_eq
      have hx0_ne : x0G ≠ q₂ := fun heq =>
        (Finset.disjoint_left.mp (compSet_disjoint G cG hC01) hx0_mem) (heq ▸ hm)
      have hTGq : (G.induce {q₂}ᶜ).IsTree := induce_compl_singleton_isTree_of_deg_one G hTG hq2_deg1
      have : Nonempty ({q₂}ᶜ : Set V) := hTGq.connected.nonempty
      have hed := connected_iff_ediam_ne_top.mp hTGq.connected
      have hle := dist_le_diam hed (u := ⟨x0G, hx0_ne⟩) (v := ⟨xd.1, hq2_ne.symm⟩)
      rw [dist_induce_eq_of_isTree G hTG {q₂}ᶜ hTGq,
        dist_add_of_ne_comp G hTG cG hC01 hx0_mem hm |> fun _ =>
          dist_add_of_ne_comp G hTG cG hC01 hx0_mem ((mem_compSet_iff G cG C₁ xd.1).mpr ⟨xd.2, hxd_mem⟩),
        dist_comm (u := x0G) (v := cG), hx0_dist, hxd_dist, hq2_diam] at hle
      omega
  obtain ⟨χ⟩ := hσ q₂
  have hχ_map : H.induce {σ q₂}ᶜ ≃g H.induce {yd.1}ᶜ :=
    ⟨⟨fun y => ⟨y.1, fun h => y.2 (h.trans hσq2_eq.symm)⟩,
      fun y => ⟨y.1, fun h => y.2 (h.trans hσq2_eq)⟩,
      fun _ => Subtype.ext rfl, fun _ => Subtype.ext rfl⟩, @fun _ _ => Iff.rfl⟩
  let χ' : G.induce {q₂}ᶜ ≃g H.induce {yd.1}ᶜ := χ.trans hχ_map
  have infoGq2 := bicenter_del_leaf_info G hTG hr hdiamG cG heccG hdegG2 C₀ C₁ hC01 hq2_deg1 hq2_C0 hq2_diam
  have infoHyd := bicenter_del_leaf_info H hTH hr hdiamH cH heccH hdegH2 D₁ D₀ hD01.symm hyd_deg1
    ((mem_compSet_iff H cH D₁ yd.1).mpr ⟨yd.2, hyd_mem⟩) hyd_diam
  let u_C1 := (existsUnique_root_of_component G hTG cG C₁).choose
  let k₀ := (existsUnique_root_of_component H hTH cH D₀).choose
  have huC1_mem : u_C1 ∈ C₁.supp := (existsUnique_root_of_component G hTG cG C₁).choose_spec.1.1
  have huC1_adj : G.Adj cG u_C1.1 := (existsUnique_root_of_component G hTG cG C₁).choose_spec.1.2
  have hk0_mem : k₀ ∈ D₀.supp := (existsUnique_root_of_component H hTH cH D₀).choose_spec.1.1
  have hk0_adj : H.Adj cH k₀.1 := (existsUnique_root_of_component H hTH cH D₀).choose_spec.1.2
  have hcG_q : cG ∈ ({q₂}ᶜ : Set V) := hq2_ne_cG.symm
  have hu1_q : u_C1.1 ∈ ({q₂}ᶜ : Set V) := fun h =>
    (Finset.disjoint_left.mp (compSet_disjoint G cG hC01) hq2_C0)
      (h ▸ (mem_compSet_iff G cG C₁ u_C1.1).mpr ⟨u_C1.2, huC1_mem⟩)
  have hcH_y : cH ∈ ({yd.1}ᶜ : Set W) := Ne.symm yd.2
  have hk0_y : k₀.1 ∈ ({yd.1}ᶜ : Set W) := fun h =>
    (Finset.disjoint_left.mp (compSet_disjoint H cH hD01)
      ((mem_compSet_iff H cH D₀ k₀.1).mpr ⟨k₀.2, hk0_mem⟩))
      (h ▸ (mem_compSet_iff H cH D₁ yd.1).mpr ⟨yd.2, hyd_mem⟩)
  let cG_q : ({q₂}ᶜ : Set V) := ⟨cG, hcG_q⟩
  let u_C1_q : ({q₂}ᶜ : Set V) := ⟨u_C1.1, hu1_q⟩
  let cH_y : ({yd.1}ᶜ : Set W) := ⟨cH, hcH_y⟩
  let k₀_y : ({yd.1}ᶜ : Set W) := ⟨k₀.1, hk0_y⟩
  have hχ_pair : χ' cG_q = k₀_y ∧ χ' u_C1_q = cH_y := by
    have hc_in : χ' cG_q = cH_y ∨ χ' cG_q = k₀_y := by
      by_contra hnot; push Not at hnot
      have hlt := infoHyd.2.1.2.2 (χ' cG_q) hnot.1 hnot.2
      rw [iso_eccent_eq _ _ χ' cG_q, infoGq2.2.1.1] at hlt
      exact absurd hlt (lt_irrefl _)
    have hu_in : χ' u_C1_q = cH_y ∨ χ' u_C1_q = k₀_y := by
      by_contra hnot; push Not at hnot
      have hlt := infoHyd.2.1.2.2 (χ' u_C1_q) hnot.1 hnot.2
      rw [iso_eccent_eq _ _ χ' u_C1_q, infoGq2.2.1.2.1] at hlt
      exact absurd hlt (lt_irrefl _)
    rcases hc_in with hc1 | hc2
    · -- Impossible because dist < side around cG_q has size M, around cH_y has size r < M!
      have hu2 : χ' u_C1_q = k₀_y := by
        rcases hu_in with hu1 | hu2
        · exact False.elim (huC1_adj.ne (congrArg Subtype.val (χ'.injective (hc1.trans hu1.symm))))
        · exact hu2
      have hcard_cG : (univ.filter fun z' : ({q₂}ᶜ : Set V) =>
          (G.induce {q₂}ᶜ).dist z' cG_q < (G.induce {q₂}ᶜ).dist z' u_C1_q).card = M := by
        simpa [hC0_card, cG_q, u_C1_q, u_C1] using infoGq2.2.2.2.1
      have hcard_cH : (univ.filter fun w' : ({yd.1}ᶜ : Set W) =>
          (H.induce {yd.1}ᶜ).dist w' cH_y < (H.induce {yd.1}ᶜ).dist w' k₀_y).card = r := by
        simpa [hD1_card, cH_y, k₀_y, k₀] using infoHyd.2.2.2.1
      have heq_card : (univ.filter fun z' : ({q₂}ᶜ : Set V) =>
          (G.induce {q₂}ᶜ).dist z' cG_q < (G.induce {q₂}ᶜ).dist z' u_C1_q).card =
          (univ.filter fun w' : ({yd.1}ᶜ : Set W) =>
          (H.induce {yd.1}ᶜ).dist w' cH_y < (H.induce {yd.1}ᶜ).dist w' k₀_y).card := by
        refine card_bij (fun z' _ => χ' z') ?_ (fun _ _ _ _ h => χ'.injective h) ?_
        · intro z' hz'
          rw [mem_filter] at hz' ⊢
          refine ⟨mem_univ _, ?_⟩
          rw [← hc1, ← hu2, iso_dist_eq _ _ χ' z' cG_q, iso_dist_eq _ _ χ' z' u_C1_q]
          exact hz'.2
        · intro w' hw'
          rw [mem_filter] at hw'
          refine ⟨χ'.symm w', mem_filter.mpr ⟨mem_univ _, ?_⟩, χ'.apply_symm_apply w'⟩
          rw [← iso_dist_eq _ _ χ' (χ'.symm w') cG_q, ← iso_dist_eq _ _ χ' (χ'.symm w') u_C1_q,
            χ'.apply_symm_apply, hc1, hu2]
          exact hw'.2
      rw [hcard_cG, hcard_cH] at heq_card; omega
    · refine ⟨hc2, ?_⟩
      rcases hu_in with hu1 | hu2
      · exact hu1
      · exact False.elim (huC1_adj.ne (congrArg Subtype.val (χ'.injective (hc2.trans hu2.symm))))
  obtain ⟨φG_c, hφGc⟩ := infoGq2.2.2.2.2.2
  obtain ⟨φH_k, hφHk⟩ := infoHyd.2.2.2.2.1
  have hside_χ : ∀ z' : ({q₂}ᶜ : Set V),
      ((G.induce {q₂}ᶜ).dist z' cG_q < (G.induce {q₂}ᶜ).dist z' u_C1_q) ↔
      ((H.induce {yd.1}ᶜ).dist (χ' z') k₀_y < (H.induce {yd.1}ᶜ).dist (χ' z') cH_y) := by
    intro z'
    rw [← hχ_pair.1, ← hχ_pair.2, iso_dist_eq _ _ χ' z' cG_q, iso_dist_eq _ _ χ' z' u_C1_q]
  let S_G := insert cG ((compSet G cG C₀).erase q₂)
  let S_H := compSet H cH D₀
  let eSG : G.induce (insert cG ((compSet G cG C₀).erase q₂ : Set V)) ≃g G.induce (S_G : Set V) :=
    ⟨⟨fun x => ⟨x.1, mem_coe.mpr (mem_insert.mpr x.2)⟩,
      fun x => ⟨x.1, mem_insert.mp (mem_coe.mp x.2)⟩,
      fun _ => Subtype.ext rfl, fun _ => Subtype.ext rfl⟩, @fun _ _ => Iff.rfl⟩
  let SG_qside : Set ({q₂}ᶜ : Set V) :=
    {z' : ({q₂}ᶜ : Set V) | (G.induce {q₂}ᶜ).dist z' cG_q < (G.induce {q₂}ᶜ).dist z' u_C1_q}
  let SH_yside : Set ({yd.1}ᶜ : Set W) :=
    {w' : ({yd.1}ᶜ : Set W) | (H.induce {yd.1}ᶜ).dist w' k₀_y < (H.induce {yd.1}ᶜ).dist w' cH_y}
  let χ_side : (G.induce {q₂}ᶜ).induce SG_qside ≃g (H.induce {yd.1}ᶜ).induce SH_yside :=
    ⟨⟨fun z' => ⟨χ' z'.1, (hside_χ z'.1).mp z'.2⟩,
      fun w' => ⟨χ'.symm w'.1, (hside_χ (χ'.symm w'.1)).mpr (by rw [χ'.apply_symm_apply]; exact w'.2)⟩,
      fun _ => Subtype.ext (χ'.symm_apply_apply _),
      fun _ => Subtype.ext (χ'.apply_symm_apply _)⟩, @fun _ _ => χ'.map_rel_iff⟩
  let χ_sub : G.induce (S_G : Set V) ≃g H.induce (S_H : Set W) :=
    eSG.symm.trans (φG_c.symm.trans (χ_side.trans φH_k))
  have hχ_sub_root : χ_sub ⟨cG, mem_insert_self cG _⟩ =
      ⟨k₀.1, (mem_compSet_iff H cH D₀ k₀.1).mpr ⟨k₀.2, hk0_mem⟩⟩ := by
    change φH_k (χ_side (φG_c.symm (eSG.symm ⟨cG, mem_insert_self cG _⟩))) = _
    have hc_side : (G.induce {q₂}ᶜ).dist cG_q cG_q < (G.induce {q₂}ᶜ).dist cG_q u_C1_q := by
      rw [dist_self, dist_eq_one_iff_adj.mpr (show (G.induce {q₂}ᶜ).Adj cG_q u_C1_q from huC1_adj)]
      omega
    have he_cG : eSG.symm ⟨cG, mem_insert_self cG _⟩ = ⟨cG, Set.mem_insert _ _⟩ := Subtype.ext rfl
    have h1 : φG_c.symm ⟨cG, Set.mem_insert _ _⟩ = (⟨cG_q, hc_side⟩ : SG_qside) :=
      φG_c.symm_apply_eq.mpr hφGc.symm
    rw [he_cG, h1]
    have hk_side : (H.induce {yd.1}ᶜ).dist k₀_y k₀_y < (H.induce {yd.1}ᶜ).dist k₀_y cH_y := by
      rw [dist_self, dist_comm, dist_eq_one_iff_adj.mpr (show (H.induce {yd.1}ᶜ).Adj cH_y k₀_y from hk0_adj)]
      omega
    have h2 : χ_side ⟨cG_q, hc_side⟩ = (⟨k₀_y, hk_side⟩ : SH_yside) := Subtype.ext hχ_pair.1
    rw [h2, hφHk]
  have hq2_ne_uC0 : q₂ ≠ u_C0.1 := fun h => by
    have := hnoLeafG u_C0.1 huC0_adj; rw [← h, hq2_deg1] at this; omega
  have huC0_SG : u_C0.1 ∈ (S_G : Set V) :=
    mem_insert_of_mem (mem_erase.mpr ⟨hq2_ne_uC0.symm,
      (mem_compSet_iff G cG C₀ u_C0.1).mpr ⟨u_C0.2, huC0_mem⟩⟩)
  have hdeg_SG_cG : (G.induce (S_G : Set V)).degree ⟨cG, mem_insert_self cG _⟩ = 1 := by
    rw [← (G.induce (S_G : Set V)).card_neighborFinset_eq_degree]
    have heq : (G.induce (S_G : Set V)).neighborFinset ⟨cG, mem_insert_self cG _⟩ =
        {⟨u_C0.1, huC0_SG⟩} := by
      ext z
      rw [mem_neighborFinset, mem_singleton]
      constructor
      · intro hadj
        change G.Adj cG z.1 at hadj
        rcases mem_insert.mp z.2 with hz_eq | hz_er
        · exact False.elim (G.ne_of_adj hadj hz_eq.symm)
        · obtain ⟨h1, h2⟩ := (mem_compSet_iff G cG C₀ z.1).mp (mem_erase.mp hz_er).2
          have h_u := (existsUnique_root_of_component G hTG cG C₀).choose_spec.2 ⟨z.1, h1⟩ ⟨h2, hadj⟩
          have h_u0 := (existsUnique_root_of_component G hTG cG C₀).choose_spec.2 u_C0 ⟨huC0_mem, huC0_adj⟩
          exact Subtype.ext (congrArg (fun w : ({cG}ᶜ : Set V) => w.1) (h_u.trans h_u0.symm))
      · rintro rfl
        exact huC0_adj
    rw [heq, card_singleton]
  have hk0_SH : k₀.1 ∈ (S_H : Set W) := (mem_compSet_iff H cH D₀ k₀.1).mpr ⟨k₀.2, hk0_mem⟩
  have hdeg_SH_k0 : (H.induce (S_H : Set W)).degree ⟨k₀.1, hk0_SH⟩ = 1 := by
    rw [← hχ_sub_root, χ_sub.degree_eq ⟨cG, mem_insert_self cG _⟩]
    exact hdeg_SG_cG
  have hH_deg_k0 : H.degree k₀.1 = 2 := by
    have h1 : (H.induce (S_H : Set W)).degree ⟨k₀.1, hk0_SH⟩ + 1 = H.degree k₀.1 := by
      let f : (S_H : Set W) ↪ W := ⟨Subtype.val, val_injective⟩
      have hnot : cH ∉ ((H.induce (S_H : Set W)).neighborFinset ⟨k₀.1, hk0_SH⟩).map f := by
        intro h; obtain ⟨x, _, hx⟩ := mem_map.mp h
        change x.1 = cH at hx
        have hxS : x.1 ∈ S_H := mem_coe.mp x.2
        rw [hx] at hxS
        exact c_notMem_compSet H cH D₀ hxS
      have heq : insert cH (((H.induce (S_H : Set W)).neighborFinset ⟨k₀.1, hk0_SH⟩).map f) =
          H.neighborFinset k₀.1 := by
        ext z
        rw [mem_insert, mem_map, mem_neighborFinset]
        constructor
        · rintro (rfl | ⟨x, hx, rfl⟩)
          · exact hk0_adj.symm
          · rw [mem_neighborFinset] at hx; exact hx
        · intro hadj
          by_cases hzc : z = cH
          · exact Or.inl hzc
          · refine Or.inr ⟨⟨z, (mem_compSet_iff H cH D₀ z).mpr ⟨hzc, ?_⟩⟩, ?_, rfl⟩
            · have hr : (H.induce {cH}ᶜ).Reachable k₀ ⟨z, hzc⟩ := Adj.reachable hadj
              exact (mem_supp_iff D₀ _).mpr ((sound hr).symm.trans
                ((mem_supp_iff D₀ k₀).mp hk0_mem))
            · rw [mem_neighborFinset]; exact hadj
      have hc := congrArg Finset.card heq
      rw [card_insert_of_notMem hnot, card_map,
        (H.induce (S_H : Set W)).card_neighborFinset_eq_degree, H.card_neighborFinset_eq_degree] at hc
      exact hc
    omega
  have hsw_r : H.dist cH (σ xd.1) = r := by
    obtain ⟨D_o, hDo_ne, y0H, hy0_mem, hy0_dist⟩ := exists_other_diam_comp H hTH hr hdiamH cH heccH D₁
    have hDo_eq : D_o = D₀ := (hTH' D_o).resolve_right hDo_ne
    subst hDo_eq
    by_contra hlt_r
    have hy0_ne : y0H ≠ σ xd.1 := fun h => hlt_r (h ▸ hy0_dist)
    have := infoH.1 y0H hy0_mem hy0_ne
    have hle := dist_le_of_eccent H hTH (u := y0H) heccH
    omega
  let K := S_H.erase (σ xd.1)
  let K' := (compSet G cG C₀).erase u_C0.1
  have hk0_K : k₀.1 ∈ (K : Set W) := mem_coe.mpr (mem_erase.mpr ⟨fun h => by
    have hd : H.dist cH k₀.1 = 1 := dist_eq_one_iff_adj.mpr hk0_adj
    rw [h, hsw_r] at hd; omega, hk0_SH⟩)
  have hK_cH_uniq : ∀ z ∈ insert cH (K : Set W), (H.Adj cH z ↔ z = k₀.1) := by
    intro z hz
    refine ⟨fun hadj => ?_, fun h => by rw [h]; exact hk0_adj⟩
    rcases mem_insert_iff.mp hz with rfl | hzK
    · exact False.elim (H.ne_of_adj hadj rfl)
    · obtain ⟨h1, h2⟩ := (mem_compSet_iff H cH D₀ z).mp (mem_erase.mp (mem_coe.mp hzK)).2
      have hu1 := (existsUnique_root_of_component H hTH cH D₀).choose_spec.2 ⟨z, h1⟩ ⟨h2, hadj⟩
      have hu2 := (existsUnique_root_of_component H hTH cH D₀).choose_spec.2 k₀ ⟨hk0_mem, hk0_adj⟩
      exact congrArg Subtype.val (hu1.trans hu2.symm)
  have hcH_notMem_K : cH ∉ K := fun h => c_notMem_compSet H cH D₀ (mem_erase.mp h).2
  have huC0_notMem_K' : u_C0.1 ∉ K' := Finset.notMem_erase _ _
  have hcH_deg_K : (H.induce (insert cH (K : Set W))).degree ⟨cH, Set.mem_insert cH _⟩ = 1 := by
    rw [← (H.induce (insert cH (K : Set W))).card_neighborFinset_eq_degree]
    have heq : (H.induce (insert cH (K : Set W))).neighborFinset ⟨cH, Set.mem_insert cH _⟩ =
        {⟨k₀.1, Set.mem_insert_of_mem cH hk0_K⟩} := by
      ext z
      rw [mem_neighborFinset, mem_singleton]
      constructor
      · intro hadj; exact Subtype.ext ((hK_cH_uniq z.1 z.2).1 hadj)
      · rintro rfl; exact hk0_adj
    rw [heq, card_singleton]
  have huC0_deg_C0 : (G.induce (compSet G cG C₀ : Set V)).degree
      ⟨u_C0.1, (mem_compSet_iff G cG C₀ u_C0.1).mpr ⟨u_C0.2, huC0_mem⟩⟩ = 1 := by
    rw [← ψ_sub.degree_eq ⟨u_C0.1, (mem_compSet_iff G cG C₀ u_C0.1).mpr ⟨u_C0.2, huC0_mem⟩⟩, hψ_sub_root]
    exact hcH_deg_K
  have hex_u2 : ∃! u₂ : ({u_C0.1}ᶜ : Set V), u₂.1 ∈ K' ∧ G.Adj u_C0.1 u₂.1 := by
    have hdeg_pos : 0 < ((G.induce (compSet G cG C₀ : Set V)).neighborFinset
        ⟨u_C0.1, (mem_compSet_iff G cG C₀ u_C0.1).mpr ⟨u_C0.2, huC0_mem⟩⟩).card := by
      rw [card_neighborFinset_eq_degree, huC0_deg_C0]; omega
    obtain ⟨u2, hu2⟩ := card_pos.mp hdeg_pos
    rw [mem_neighborFinset] at hu2
    have hu2_ne : u2.1 ≠ u_C0.1 := (G.ne_of_adj hu2).symm
    refine ⟨⟨u2.1, hu2_ne⟩, ⟨mem_erase.mpr ⟨hu2_ne, u2.2⟩, hu2⟩, fun y ⟨hyK', hyadj⟩ => ?_⟩
    have hyC0 : y.1 ∈ compSet G cG C₀ := (mem_erase.mp hyK').2
    have hpair : (G.induce (compSet G cG C₀ : Set V)).neighborFinset
        ⟨u_C0.1, (mem_compSet_iff G cG C₀ u_C0.1).mpr ⟨u_C0.2, huC0_mem⟩⟩ = {u2} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨(mem_neighborFinset _ _ _).mpr hu2, fun z hz => ?_⟩
      by_contra hne
      have h2 := Finset.one_lt_card.mpr ⟨u2, (mem_neighborFinset _ _ _).mpr hu2, z, hz, fun h => hne h.symm⟩
      rw [card_neighborFinset_eq_degree, huC0_deg_C0] at h2
      omega
    have hy_mem : (⟨y.1, hyC0⟩ : ↥(compSet G cG C₀ : Set V)) ∈
        (G.induce (compSet G cG C₀ : Set V)).neighborFinset
          ⟨u_C0.1, (mem_compSet_iff G cG C₀ u_C0.1).mpr ⟨u_C0.2, huC0_mem⟩⟩ :=
      (mem_neighborFinset _ _ _).mpr hyadj
    rw [hpair, mem_singleton] at hy_mem
    exact Subtype.ext (congrArg (fun z : ↥(compSet G cG C₀ : Set V) => z.1) hy_mem)
  let u₂ := hex_u2.choose
  have hu2_K' : u₂.1 ∈ K' := hex_u2.choose_spec.1.1
  have hu2_adj : G.Adj u_C0.1 u₂.1 := hex_u2.choose_spec.1.2
  have hu2_C0 : u₂.1 ∈ compSet G cG C₀ := (mem_erase.mp hu2_K').2
  have hψK_img : ∀ x : (K' : Set V), (ψ_sub ⟨x.1, (mem_erase.mp (mem_coe.mp x.2)).2⟩).1 ∈ (K : Set W) := by
    intro x
    have hne_uC0 : (⟨x.1, (mem_erase.mp (mem_coe.mp x.2)).2⟩ : (compSet G cG C₀ : Set V)) ≠
        ⟨u_C0.1, (mem_compSet_iff G cG C₀ u_C0.1).mpr ⟨u_C0.2, huC0_mem⟩⟩ := by
      intro heq
      exact (mem_erase.mp (mem_coe.mp x.2)).1 (congrArg Subtype.val heq)
    have hm := (ψ_sub ⟨x.1, (mem_erase.mp (mem_coe.mp x.2)).2⟩).2
    rcases mem_insert_iff.mp hm with hc_eq | hk_mem
    · exact False.elim (hne_uC0 (ψ_sub.injective (Subtype.ext hc_eq |>.trans hψ_sub_root.symm)))
    · exact hk_mem
  have hψK_symm_img : ∀ y : (K : Set W), (ψ_sub.symm ⟨y.1, Set.mem_insert_of_mem cH y.2⟩).1 ∈ (K' : Set V) := by
    intro y
    have hne_cH : (⟨y.1, Set.mem_insert_of_mem cH y.2⟩ : ↥(insert cH (K : Set W))) ≠ ⟨cH, Set.mem_insert cH _⟩ := by
      intro heq; have hyc : y.1 = cH := congrArg (fun z : ↥(insert cH (K : Set W)) => z.1) heq
      exact hcH_notMem_K (by simpa [hyc] using y.2)
    have hne_u : ψ_sub.symm ⟨y.1, Set.mem_insert_of_mem cH y.2⟩ ≠
        ⟨u_C0.1, (mem_compSet_iff G cG C₀ u_C0.1).mpr ⟨u_C0.2, huC0_mem⟩⟩ := by
      intro heq
      exact hne_cH ((ψ_sub.apply_symm_apply _).symm.trans ((congrArg ψ_sub heq).trans hψ_sub_root))
    exact mem_coe.mpr (mem_erase.mpr
      ⟨fun h => hne_u (Subtype.ext h), (ψ_sub.symm ⟨y.1, Set.mem_insert_of_mem cH y.2⟩).2⟩)
  let ψ_K : G.induce (K' : Set V) ≃g H.induce (K : Set W) :=
    ⟨⟨fun x => ⟨(ψ_sub ⟨x.1, (mem_erase.mp (mem_coe.mp x.2)).2⟩).1, hψK_img x⟩,
      fun y => ⟨(ψ_sub.symm ⟨y.1, Set.mem_insert_of_mem cH y.2⟩).1, hψK_symm_img y⟩,
      fun x => Subtype.ext (by
        dsimp only
        have heta : (⟨(ψ_sub ⟨x.1, (mem_erase.mp (mem_coe.mp x.2)).2⟩).1,
            Set.mem_insert_of_mem cH (hψK_img x)⟩ :
            ↥(insert cH ((compSet H cH D₀).erase (σ xd.1) : Set W))) =
            ψ_sub ⟨x.1, (mem_erase.mp (mem_coe.mp x.2)).2⟩ := rfl
        rw [heta]
        exact congrArg (fun z : ↥(compSet G cG C₀ : Set V) => z.1) (ψ_sub.left_inv _)),
      fun y => Subtype.ext (by
        dsimp only
        have heta : (⟨(ψ_sub.symm ⟨y.1, Set.mem_insert_of_mem cH y.2⟩).1,
            (mem_erase.mp (mem_coe.mp (hψK_symm_img y))).2⟩ :
            ↥(compSet G cG C₀ : Set V)) =
            ψ_sub.symm ⟨y.1, Set.mem_insert_of_mem cH y.2⟩ := rfl
        rw [heta]
        exact congrArg (fun z : ↥(insert cH ((compSet H cH D₀).erase (σ xd.1) : Set W)) => z.1)
          (ψ_sub.right_inv _))⟩,
     @fun a b => ψ_sub.map_rel_iff (a := ⟨a.1, (mem_erase.mp (mem_coe.mp a.2)).2⟩)
       (b := ⟨b.1, (mem_erase.mp (mem_coe.mp b.2)).2⟩)⟩
  have hψK_root : ψ_K ⟨u₂.1, hu2_K'⟩ = ⟨k₀.1, hk0_K⟩ := by
    apply Subtype.ext
    have hadj_H : (H.induce (insert cH (K : Set W))).Adj ⟨cH, Set.mem_insert cH _⟩
        (ψ_sub ⟨u₂.1, hu2_C0⟩) := by
      rw [← hψ_sub_root, ψ_sub.map_rel_iff]
      exact hu2_adj
    exact (hK_cH_uniq _ (ψ_sub ⟨u₂.1, hu2_C0⟩).2).1 hadj_H
  have hK_deg_k0 : (H.induce (K : Set W)).degree ⟨k₀.1, hk0_K⟩ = 1 := by
    have hnot_adj_w : ¬ H.Adj k₀.1 (σ xd.1) := fun hadj => by
      have hd := hTH.connected.dist_triangle (u := cH) (v := k₀.1) (w := σ xd.1)
      have hd1 : H.dist cH k₀.1 = 1 := dist_eq_one_iff_adj.mpr hk0_adj
      have hd2 : H.dist k₀.1 (σ xd.1) = 1 := dist_eq_one_iff_adj.mpr hadj
      rw [hsw_r, hd1, hd2] at hd; omega
    let f : (K : Set W) ↪ (S_H : Set W) := ⟨fun y => ⟨y.1, (mem_erase.mp y.2).2⟩,
      fun _ _ h => Subtype.ext (congrArg (fun z : (S_H : Set W) => z.1) h)⟩
    have heq : ((H.induce (K : Set W)).neighborFinset ⟨k₀.1, hk0_K⟩).map f =
        (H.induce (S_H : Set W)).neighborFinset ⟨k₀.1, hk0_SH⟩ := by
      ext y
      rw [mem_map, mem_neighborFinset]
      constructor
      · rintro ⟨z, hz, rfl⟩
        rw [mem_neighborFinset] at hz; exact hz
      · intro hadj
        have hy_ne : y.1 ≠ σ xd.1 := fun h => hnot_adj_w (h ▸ hadj)
        refine ⟨⟨y.1, mem_erase.mpr ⟨hy_ne, y.2⟩⟩, ?_, Subtype.ext rfl⟩
        rw [mem_neighborFinset]; exact hadj
    have hc := congrArg Finset.card heq
    rw [card_map, (H.induce (K : Set W)).card_neighborFinset_eq_degree,
      (H.induce (S_H : Set W)).card_neighborFinset_eq_degree] at hc
    omega
  have hG_deg_uC0 : G.degree u_C0.1 = 2 := by
    have h1 := degree_induce_compl_singleton_of_adj G u_C0.2 huC0_adj.symm
    rw [coe_eta] at h1
    have heq : (G.induce {cG}ᶜ).degree u_C0 =
        (G.induce (compSet G cG C₀ : Set V)).degree ⟨u_C0.1, (mem_compSet_iff G cG C₀ u_C0.1).mpr ⟨u_C0.2, huC0_mem⟩⟩ := by
      let f : (compSet G cG C₀ : Set V) ↪ ({cG}ᶜ : Set V) :=
        ⟨fun x => ⟨x.1, fun h => c_notMem_compSet G cG C₀ (by have hx := x.2; rwa [h] at hx)⟩,
         fun _ _ h => Subtype.ext (congrArg (fun z : ({cG}ᶜ : Set V) => z.1) h)⟩
      have heqn : ((G.induce (compSet G cG C₀ : Set V)).neighborFinset
          ⟨u_C0.1, (mem_compSet_iff G cG C₀ u_C0.1).mpr ⟨u_C0.2, huC0_mem⟩⟩).map f =
          (G.induce {cG}ᶜ).neighborFinset u_C0 := by
        ext z; rw [mem_map, mem_neighborFinset]
        constructor
        · rintro ⟨x, hx, rfl⟩; rw [mem_neighborFinset] at hx; exact hx
        · intro hadj
          have hzC0 : z.1 ∈ compSet G cG C₀ := by
            have hr : (G.induce {cG}ᶜ).Reachable u_C0 z := Adj.reachable hadj
            exact (mem_compSet_iff G cG C₀ z.1).mpr ⟨z.2,
              (mem_supp_iff C₀ z).mpr ((sound hr).symm.trans
                ((mem_supp_iff C₀ u_C0).mp huC0_mem))⟩
          exact ⟨⟨z.1, hzC0⟩, (mem_neighborFinset _ _ _).mpr hadj, Subtype.ext rfl⟩
      have hc := congrArg Finset.card heqn
      rw [card_map, card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at hc
      exact hc.symm
    omega
  have hG_deg_u2 : G.degree u₂.1 = 2 := by
    have hK'_u2 : (G.induce (K' : Set V)).degree ⟨u₂.1, hu2_K'⟩ = 1 := by
      rw [← ψ_K.degree_eq ⟨u₂.1, hu2_K'⟩, hψK_root]; exact hK_deg_k0
    have hnadj_cG : ¬ G.Adj cG u₂.1 := by
      intro hadj
      obtain ⟨h1, h2⟩ := (mem_compSet_iff G cG C₀ u₂.1).mp hu2_C0
      have he1 := (existsUnique_root_of_component G hTG cG C₀).choose_spec.2 ⟨u₂.1, h1⟩ ⟨h2, hadj⟩
      have he2 := (existsUnique_root_of_component G hTG cG C₀).choose_spec.2 u_C0 ⟨huC0_mem, huC0_adj⟩
      exact u₂.2 (congrArg Subtype.val (he1.trans he2.symm))
    let f : (K' : Set V) ↪ V := ⟨Subtype.val, val_injective⟩
    have hnot : u_C0.1 ∉ ((G.induce (K' : Set V)).neighborFinset ⟨u₂.1, hu2_K'⟩).map f := by
      intro h; obtain ⟨x, _, hx⟩ := mem_map.mp h
      exact (mem_erase.mp x.2).1 hx
    have heq : insert u_C0.1 (((G.induce (K' : Set V)).neighborFinset ⟨u₂.1, hu2_K'⟩).map f) =
        G.neighborFinset u₂.1 := by
      ext z; rw [mem_insert, mem_map, mem_neighborFinset]
      constructor
      · rintro (rfl | ⟨x, hx, rfl⟩)
        · exact hu2_adj.symm
        · rw [mem_neighborFinset] at hx; exact hx
      · intro hadj
        by_cases hzu : z = u_C0.1
        · exact Or.inl hzu
        · have hzc : z ≠ cG := fun h => hnadj_cG (h ▸ hadj.symm)
          have hzC0 : z ∈ compSet G cG C₀ := by
            obtain ⟨h1, h2⟩ := (mem_compSet_iff G cG C₀ u₂.1).mp hu2_C0
            have hr : (G.induce {cG}ᶜ).Reachable ⟨u₂.1, h1⟩ ⟨z, hzc⟩ := Adj.reachable hadj
            exact (mem_compSet_iff G cG C₀ z).mpr ⟨hzc,
              (mem_supp_iff C₀ _).mpr ((sound hr).symm.trans
                ((mem_supp_iff C₀ _).mp h2))⟩
          exact Or.inr ⟨⟨z, mem_erase.mpr ⟨hzu, hzC0⟩⟩,
            (mem_neighborFinset _ _ _).mpr hadj, rfl⟩
    have hc := congrArg Finset.card heq
    rw [card_insert_of_notMem hnot, card_map,
      card_neighborFinset_eq_degree, card_neighborFinset_eq_degree, hK'_u2] at hc
    omega
  obtain ⟨q_star, hqstar_adj, _⟩ := degree_eq_one_iff_existsUnique_adj.mp hσxd_deg1
  have hSH_deg_qstar : ∀ (hq : q_star ∈ (S_H : Set W)), (H.induce (S_H : Set W)).degree ⟨q_star, hq⟩ ≤ 2 := by
    intro hq
    have hq_dist : H.dist cH q_star = r - 1 := by
      obtain ⟨p, hp, hplen⟩ := hTH.connected.exists_path_of_dist cH (σ xd.1)
      have hnp : ¬ p.Nil := not_nil_of_ne (fun h => by rw [← h, dist_self] at hsw_r; omega)
      have hpen_eq : p.penultimate = q_star := by
        have h_u := (degree_eq_one_iff_existsUnique_adj.mp hσxd_deg1).choose_spec
        have h1 := h_u.2 q_star hqstar_adj
        have h2 := h_u.2 p.penultimate (p.adj_penultimate hnp).symm
        exact h2.trans h1.symm
      have hp_take : (p.take (p.length - 1)).IsPath := hp.take (p.length - 1)
      have h1 := isTree_dist_eq_length_of_isPath H hTH (p.take (p.length - 1)) hp_take
      rw [Walk.take_length, show min (p.length - 1) p.length = r - 1 by rw [hplen, hsw_r]; omega] at h1
      rw [← hpen_eq]; exact h1.symm
    obtain ⟨pq, hpq, hpqlen⟩ := hTH.connected.exists_path_of_dist cH q_star
    have hpq_nn : ¬ pq.Nil := not_nil_of_ne (fun h => by rw [← h, dist_self] at hq_dist; omega)
    have hsub : (H.induce (S_H : Set W)).neighborFinset ⟨q_star, hq⟩ ⊆
        {⟨σ xd.1, hσxd_D0⟩, ⟨pq.penultimate, by
          have hpq_ne_c : pq.penultimate ≠ cH := by
            have := pq.adj_penultimate hpq_nn
            have h1 : H.dist cH pq.penultimate = r - 2 := by
              have hpt := isTree_dist_eq_length_of_isPath H hTH (pq.take (pq.length - 1)) (hpq.take _)
              rw [Walk.take_length, show min (pq.length - 1) pq.length = r - 2 by rw [hpqlen, hq_dist]; omega] at hpt
              exact hpt.symm
            intro h; rw [h, dist_self] at h1; omega
          exact mem_compSet_of_walk_from_c H cH D₀ hq hpq (getVert_mem_support pq _) hpq_ne_c⟩} := by
      intro z hz
      rw [mem_neighborFinset] at hz
      rw [mem_insert, mem_singleton]
      by_cases hzw : z.1 = σ xd.1
      · exact Or.inl (Subtype.ext hzw)
      · right
        apply Subtype.ext
        have hz_le := infoH.1 z.1 z.2 hzw
        by_cases hq_mem : q_star ∈ (hTH.connected.exists_path_of_dist cH z.1).choose.support
        · obtain ⟨pz, hpz, hpzlen⟩ := hTH.connected.exists_path_of_dist cH z.1
          have hmem : q_star ∈ (hTH.connected.exists_path_of_dist cH z.1).choose.support := hq_mem
          let pz0 := (hTH.connected.exists_path_of_dist cH z.1).choose
          have hpz0 := (hTH.connected.exists_path_of_dist cH z.1).choose_spec.1
          have hpz0_len := (hTH.connected.exists_path_of_dist cH z.1).choose_spec.2
          obtain ⟨a1, a2, ha1, ha2, haeq⟩ := hpz0.mem_support_iff_exists_append.mp hmem
          have ha1_eq := isTree_path_eq H hTH ha1 hpq
          have ha2_len : a2.length = 1 := by
            rw [isTree_dist_eq_length_of_isPath H hTH a2 ha2, dist_eq_one_iff_adj.mpr (show H.Adj q_star z.1 from hz)]
          have hsum := congrArg Walk.length haeq
          rw [length_append, ha1_eq, hpqlen, hq_dist, hpz0_len, ha2_len] at hsum
          omega
        · let pz0 := (hTH.connected.exists_path_of_dist cH z.1).choose
          have hpz0 := (hTH.connected.exists_path_of_dist cH z.1).choose_spec.1
          let p' : H.Walk cH q_star := pz0.concat (show H.Adj z.1 q_star from hz.symm)
          have hp' : p'.IsPath := by
            dsimp only [p']
            rw [isPath_def, Walk.support_concat pz0 (show H.Adj z.1 q_star from hz.symm), List.nodup_append]
            exact ⟨hpz0.support_nodup, List.nodup_singleton _, fun w hw y hy heqv => by
              simp only [List.mem_singleton] at hy; rw [heqv, hy] at hw; exact hq_mem hw⟩
          have heq := isTree_path_eq H hTH hpq hp'
          change _ = pq.penultimate
          have : p'.penultimate = z.1 := by dsimp only [p']; exact Walk.penultimate_concat pz0 (show H.Adj z.1 q_star from hz.symm)
          rw [← this, heq]
    rw [← (H.induce (S_H : Set W)).card_neighborFinset_eq_degree]
    exact (card_le_card hsub).trans ((Finset.card_insert_le _ _).trans (by simp))
  have hex_SH3 : ∃ y : (S_H : Set W), 3 ≤ (H.induce (S_H : Set W)).degree y := by
    obtain ⟨v0, hv0⟩ := hnonpath
    have hw0 : 3 ≤ H.degree (σ v0) := by
      rw [← ncard_neighborSet_eq_degree, ← hdeg v0]; exact hv0
    have hw0_c : σ v0 ≠ cH := fun h => by rw [h, hdegH2] at hw0; omega
    have hw0_D1 : σ v0 ∉ compSet H cH D₁ := by
      intro hm
      have hd1 : H.degree (σ v0) ≤ 2 := by
        obtain ⟨q, hq, hqlen, hfin⟩ := comp_path_of_card_eq_dist H hTH cH D₁ hyd_mem hyd_dist hD1_card
        obtain ⟨φq, _, _⟩ := induce_support_iso_pathG_rooted H hTH q hq
        have hw_in : σ v0 ∈ (q.support.toFinset : Set W) := by
          rw [hfin]; exact mem_insert_of_mem hm
        have hle_ind : H.degree (σ v0) ≤ (H.induce (q.support.toFinset : Set W)).degree ⟨σ v0, hw_in⟩ := by
          let f : (q.support.toFinset : Set W) ↪ W := ⟨Subtype.val, val_injective⟩
          have hsub : H.neighborFinset (σ v0) ⊆
              ((H.induce (q.support.toFinset : Set W)).neighborFinset ⟨σ v0, hw_in⟩).map f := by
            intro z hz; rw [mem_neighborFinset] at hz
            have hzc : z ∈ insert cH (compSet H cH D₁) := by
              by_cases h1 : z = cH
              · rw [h1]; exact mem_insert_self _ _
              · refine mem_insert_of_mem ((mem_compSet_iff H cH D₁ z).mpr ⟨h1, ?_⟩)
                obtain ⟨a1, a2⟩ := (mem_compSet_iff H cH D₁ (σ v0)).mp hm
                exact (mem_supp_iff D₁ _).mpr
                  ((sound (Adj.reachable (show (H.induce {cH}ᶜ).Adj ⟨σ v0, a1⟩ ⟨z, h1⟩ from hz))).symm.trans
                    ((mem_supp_iff D₁ _).mp a2))
            rw [← hfin] at hzc
            exact mem_map.mpr ⟨⟨z, hzc⟩, (mem_neighborFinset _ _ _).mpr hz, rfl⟩
          rw [← H.card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree, ← card_map f]
          exact card_le_card hsub
        have hpath_le : ∀ i : Fin (q.length + 1), (pathG (q.length + 1)).degree i ≤ 2 := by
          intro i
          rw [← (pathG (q.length + 1)).card_neighborFinset_eq_degree]
          have hsub : (pathG (q.length + 1)).neighborFinset i ⊆
              (if h1 : i.val + 1 < q.length + 1 then {⟨i.val + 1, h1⟩} else ∅) ∪
              (if h2 : 0 < i.val then {⟨i.val - 1, by omega⟩} else ∅) := by
            intro j hj; rw [mem_neighborFinset] at hj
            rcases hj with h | h
            · refine mem_union_left _ ?_; have h1 : i.val + 1 < q.length + 1 := by rw [h]; exact j.isLt
              rw [dif_pos h1, mem_singleton]; exact Fin.ext h.symm
            · refine mem_union_right _ ?_; have h2 : 0 < i.val := by omega
              rw [dif_pos h2, mem_singleton]; exact Fin.ext (by simp; omega)
          exact (card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by split_ifs <;> simp))
        rw [← φq.degree_eq ⟨σ v0, hw_in⟩] at hle_ind
        exact hle_ind.trans (hpath_le _)
      omega
    let Cw := (H.induce {cH}ᶜ).connectedComponentMk ⟨σ v0, hw0_c⟩
    have hwm : σ v0 ∈ compSet H cH Cw := (mem_compSet_iff H cH Cw (σ v0)).mpr ⟨hw0_c, rfl⟩
    have hCw : Cw = D₀ := (hTH' Cw).resolve_right (fun h => hw0_D1 (h ▸ hwm))
    rw [hCw] at hwm
    have hw_ne_k0 : σ v0 ≠ k₀.1 := fun h => by rw [h, hH_deg_k0] at hw0; omega
    refine ⟨⟨σ v0, hwm⟩, ?_⟩
    have hdeg_eq : (H.induce (S_H : Set W)).degree ⟨σ v0, hwm⟩ = H.degree (σ v0) := by
      let f : (S_H : Set W) ↪ W := ⟨Subtype.val, val_injective⟩
      have heq : ((H.induce (S_H : Set W)).neighborFinset ⟨σ v0, hwm⟩).map f = H.neighborFinset (σ v0) := by
        ext z; rw [mem_map, mem_neighborFinset]
        constructor
        · rintro ⟨x, hx, rfl⟩; rw [mem_neighborFinset] at hx; exact hx
        · intro hadj
          have hzc : z ≠ cH := by
            intro hc
            obtain ⟨h1, h2⟩ := (mem_compSet_iff H cH D₀ (σ v0)).mp hwm
            have hu := (existsUnique_root_of_component H hTH cH D₀).choose_spec.2 ⟨σ v0, h1⟩ ⟨h2, hc ▸ hadj.symm⟩
            have hu0 := (existsUnique_root_of_component H hTH cH D₀).choose_spec.2 k₀ ⟨hk0_mem, hk0_adj⟩
            exact hw_ne_k0 (congrArg Subtype.val (hu.trans hu0.symm))
          obtain ⟨h1, h2⟩ := (mem_compSet_iff H cH D₀ (σ v0)).mp hwm
          have hr : (H.induce {cH}ᶜ).Reachable ⟨σ v0, h1⟩ ⟨z, hzc⟩ := Adj.reachable hadj
          exact ⟨⟨z, (mem_compSet_iff H cH D₀ z).mpr ⟨hzc,
            (mem_supp_iff D₀ _).mpr ((sound hr).symm.trans
              ((mem_supp_iff D₀ _).mp h2))⟩⟩,
            (mem_neighborFinset _ _ _).mpr hadj, rfl⟩
      have hc := congrArg Finset.card heq
      rw [card_map, card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at hc
      exact hc
    omega
  let F3 := univ.filter fun y : (S_H : Set W) => 3 ≤ (H.induce (S_H : Set W)).degree y
  have hF3_ne : F3.Nonempty := by
    obtain ⟨y, hy⟩ := hex_SH3
    exact ⟨y, mem_filter.mpr ⟨mem_univ _, hy⟩⟩
  obtain ⟨y_star, hy_star_mem, hy_star_min⟩ :=
    Finset.exists_min_image F3 (fun y => (H.induce (S_H : Set W)).dist ⟨k₀.1, hk0_SH⟩ y) hF3_ne
  have hy_star_deg : 3 ≤ (H.induce (S_H : Set W)).degree y_star := (mem_filter.mp hy_star_mem).2
  let x_star := χ_sub.symm y_star
  have hx_star_deg : 3 ≤ (G.induce (S_G : Set V)).degree x_star := by
    rw [← χ_sub.symm.degree_eq y_star] at hy_star_deg; exact hy_star_deg
  have hx_star_dist : (G.induce (S_G : Set V)).dist ⟨cG, mem_insert_self cG _⟩ x_star =
      (H.induce (S_H : Set W)).dist ⟨k₀.1, hk0_SH⟩ y_star := by
    rw [← hχ_sub_root]
    change (G.induce (S_G : Set V)).dist _ (χ_sub.symm y_star) =
      (H.induce (S_H : Set W)).dist (χ_sub ⟨cG, mem_insert_self cG _⟩) y_star
    rw [← χ_sub.apply_symm_apply y_star, iso_dist_eq _ _ χ_sub]
    simp [x_star]
  have hx_ne_cG : x_star.1 ≠ cG := fun h => by
    have heq : x_star = ⟨cG, mem_insert_self cG _⟩ := Subtype.ext h
    rw [heq, hdeg_SG_cG] at hx_star_deg; omega
  have hx_ne_uC0 : x_star.1 ≠ u_C0.1 := fun h => by
    have hle : (G.induce (S_G : Set V)).degree x_star ≤ G.degree x_star.1 := by
      let f : (S_G : Set V) ↪ V := ⟨Subtype.val, val_injective⟩
      have hsub : ((G.induce (S_G : Set V)).neighborFinset x_star).map f ⊆ G.neighborFinset x_star.1 := by
        intro z hz; obtain ⟨a, ha, rfl⟩ := mem_map.mp hz
        rw [mem_neighborFinset] at ha ⊢; exact ha
      rw [← card_neighborFinset_eq_degree, ← G.card_neighborFinset_eq_degree, ← card_map f]
      exact card_le_card hsub
    rw [h, hG_deg_uC0] at hle; omega
  have hx_ne_u2 : x_star.1 ≠ u₂.1 := fun h => by
    have hle : (G.induce (S_G : Set V)).degree x_star ≤ G.degree x_star.1 := by
      let f : (S_G : Set V) ↪ V := ⟨Subtype.val, val_injective⟩
      have hsub : ((G.induce (S_G : Set V)).neighborFinset x_star).map f ⊆ G.neighborFinset x_star.1 := by
        intro z hz; obtain ⟨a, ha, rfl⟩ := mem_map.mp hz
        rw [mem_neighborFinset] at ha ⊢; exact ha
      rw [← card_neighborFinset_eq_degree, ← G.card_neighborFinset_eq_degree, ← card_map f]
      exact card_le_card hsub
    rw [h, hG_deg_u2] at hle; omega
  have hx_K' : x_star.1 ∈ (K' : Set V) := by
    rcases mem_insert.mp x_star.2 with h1 | h1
    · exact False.elim (hx_ne_cG h1)
    · exact mem_erase.mpr ⟨hx_ne_uC0, (mem_erase.mp h1).2⟩
  have hK'_deg_x : 3 ≤ (G.induce (K' : Set V)).degree ⟨x_star.1, hx_K'⟩ := by
    have hsub : ((G.induce (S_G : Set V)).neighborFinset x_star).map
        ⟨fun z => z.1, fun _ _ h => Subtype.ext h⟩ ⊆
        ((G.induce (K' : Set V)).neighborFinset ⟨x_star.1, hx_K'⟩).map
        ⟨fun z => z.1, fun _ _ h => Subtype.ext h⟩ := by
      intro z hz
      obtain ⟨a, ha, rfl⟩ := mem_map.mp hz
      rw [mem_neighborFinset] at ha
      have ha_cG : a.1 ≠ cG := fun h => hx_ne_uC0 (by
        have hadj : G.Adj cG x_star.1 := h ▸ ha.symm
        have hxC0 := (mem_erase.mp hx_K').2
        obtain ⟨hc1, hc2⟩ := (mem_compSet_iff G cG C₀ x_star.1).mp hxC0
        have hu1 := (existsUnique_root_of_component G hTG cG C₀).choose_spec.2 ⟨x_star.1, hc1⟩ ⟨hc2, hadj⟩
        have hu2 := (existsUnique_root_of_component G hTG cG C₀).choose_spec.2 u_C0 ⟨huC0_mem, huC0_adj⟩
        exact congrArg Subtype.val (hu1.trans hu2.symm))
      have ha_uC0 : a.1 ≠ u_C0.1 := fun h => by
        have hadj : G.Adj u_C0.1 x_star.1 := h ▸ ha.symm
        have hxC0 := (mem_erase.mp hx_K').2
        have huniq := hex_u2.choose_spec.2 ⟨x_star.1, hx_ne_uC0⟩ ⟨hx_K', hadj⟩
        exact hx_ne_u2 (congrArg Subtype.val huniq)
      have ha_K' : a.1 ∈ (K' : Set V) := by
        rcases mem_insert.mp a.2 with h1 | h1
        · exact False.elim (ha_cG h1)
        · exact mem_erase.mpr ⟨ha_uC0, (mem_erase.mp h1).2⟩
      exact mem_map.mpr ⟨⟨a.1, ha_K'⟩, (mem_neighborFinset _ _ _).mpr ha, rfl⟩
    have hcard := card_le_card hsub
    rw [card_map, card_map, card_neighborFinset_eq_degree,
      card_neighborFinset_eq_degree] at hcard
    omega
  let y_img := ψ_K ⟨x_star.1, hx_K'⟩
  have hy_img_degK : 3 ≤ (H.induce (K : Set W)).degree y_img := by
    rw [ψ_K.degree_eq ⟨x_star.1, hx_K'⟩]; exact hK'_deg_x
  have hy_img_SH : y_img.1 ∈ (S_H : Set W) := (mem_erase.mp y_img.2).2
  have hy_img_degSH : 3 ≤ (H.induce (S_H : Set W)).degree ⟨y_img.1, hy_img_SH⟩ := by
    have hsub : ((H.induce (K : Set W)).neighborFinset y_img).map ⟨Subtype.val, val_injective⟩ ⊆
        ((H.induce (S_H : Set W)).neighborFinset ⟨y_img.1, hy_img_SH⟩).map ⟨Subtype.val, val_injective⟩ := by
      intro z hz; obtain ⟨a, ha, rfl⟩ := mem_map.mp hz
      rw [mem_neighborFinset] at ha
      exact mem_map.mpr ⟨⟨a.1, (mem_erase.mp a.2).2⟩, (mem_neighborFinset _ _ _).mpr ha, rfl⟩
    have hc := card_le_card hsub
    rw [card_map, card_map, card_neighborFinset_eq_degree,
      card_neighborFinset_eq_degree] at hc
    omega
  have hy_img_min := hy_star_min ⟨y_img.1, hy_img_SH⟩
    (mem_filter.mpr ⟨mem_univ _, hy_img_degSH⟩)
  have hSG_tree : (G.induce (S_G : Set V)).IsTree := by
    have hD0_tree : D₀.toSimpleGraph.IsTree := (hTH.isAcyclic.induce {cH}ᶜ).isTree_connectedComponent D₀
    have hSH_tree : (H.induce (S_H : Set W)).IsTree := by
      let eD : D₀.toSimpleGraph ≃g H.induce (S_H : Set W) :=
        ⟨⟨fun z => ⟨z.1.1, (mem_compSet_iff H cH D₀ z.1.1).mpr ⟨z.1.2, z.2⟩⟩,
          fun z => ⟨⟨z.1, ((mem_compSet_iff H cH D₀ z.1).mp z.2).choose⟩,
            ((mem_compSet_iff H cH D₀ z.1).mp z.2).choose_spec⟩,
          fun _ => Subtype.ext (Subtype.ext rfl), fun _ => Subtype.ext rfl⟩, @fun _ _ => Iff.rfl⟩
      exact (Iso.isTree_iff eD).mp hD0_tree
    exact (Iso.isTree_iff χ_sub).mpr hSH_tree
  have hSH_tree : (H.induce (S_H : Set W)).IsTree := (Iso.isTree_iff χ_sub).mp hSG_tree
  have hK_tree : (H.induce (K : Set W)).IsTree := by
    have hk_deg1 : (H.induce (S_H : Set W)).degree ⟨σ xd.1, hσxd_D0⟩ = 1 := by
      have hle : (H.induce (S_H : Set W)).degree ⟨σ xd.1, hσxd_D0⟩ ≤ H.degree (σ xd.1) := by
        let f : (S_H : Set W) ↪ W := ⟨Subtype.val, val_injective⟩
        have hsub : ((H.induce (S_H : Set W)).neighborFinset ⟨σ xd.1, hσxd_D0⟩).map f ⊆
            H.neighborFinset (σ xd.1) := fun z hz => by
          obtain ⟨a, ha, rfl⟩ := mem_map.mp hz
          rw [mem_neighborFinset] at ha ⊢; exact ha
        rw [← card_neighborFinset_eq_degree, ← H.card_neighborFinset_eq_degree, ← card_map f]
        exact card_le_card hsub
      have hge : 1 ≤ (H.induce (S_H : Set W)).degree ⟨σ xd.1, hσxd_D0⟩ := by
        have hq_SH : q_star ∈ S_H := by
          have hq_ne : q_star ≠ cH := fun h => by
            have hd : H.dist cH (σ xd.1) = 1 := dist_eq_one_iff_adj.mpr (h ▸ hqstar_adj.symm)
            omega
          obtain ⟨h1, h2⟩ := (mem_compSet_iff H cH D₀ (σ xd.1)).mp hσxd_D0
          exact (mem_compSet_iff H cH D₀ q_star).mpr ⟨hq_ne,
            (mem_supp_iff D₀ _).mpr ((sound
              (Adj.reachable (show (H.induce {cH}ᶜ).Adj ⟨σ xd.1, h1⟩ ⟨q_star, hq_ne⟩ from hqstar_adj))).symm.trans
              ((mem_supp_iff D₀ _).mp h2))⟩
        rw [← card_neighborFinset_eq_degree]
        exact card_pos.mpr ⟨⟨q_star, hq_SH⟩,
          (mem_neighborFinset _ _ _).mpr (show (H.induce (S_H : Set W)).Adj ⟨σ xd.1, hσxd_D0⟩ ⟨q_star, hq_SH⟩ from hqstar_adj)⟩
      omega
    have hsub_K : (H.induce (K : Set W)) ≃g (H.induce (S_H : Set W)).induce ({⟨σ xd.1, hσxd_D0⟩}ᶜ : Set (S_H : Set W)) :=
      ⟨⟨fun z => ⟨⟨z.1, (mem_erase.mp z.2).2⟩, fun h => (mem_erase.mp z.2).1 (congrArg Subtype.val h)⟩,
        fun z => ⟨z.1.1, mem_erase.mpr ⟨fun h => z.2 (Subtype.ext h), z.1.2⟩⟩,
        fun _ => Subtype.ext rfl, fun _ => Subtype.ext (Subtype.ext rfl)⟩, @fun _ _ => Iff.rfl⟩
    exact (Iso.isTree_iff hsub_K).mpr (induce_compl_singleton_isTree_of_deg_one _ hSH_tree hk_deg1)
  have hK'_tree : (G.induce (K' : Set V)).IsTree := (Iso.isTree_iff ψ_K).mpr hK_tree
  have hdist_G_x : (G.induce (S_G : Set V)).dist ⟨cG, mem_insert_self cG _⟩ x_star =
      2 + (G.induce (K' : Set V)).dist ⟨u₂.1, hu2_K'⟩ ⟨x_star.1, hx_K'⟩ := by
    rw [dist_induce_eq_of_isTree G hTG (S_G : Set V) hSG_tree,
      dist_induce_eq_of_isTree G hTG (K' : Set V) hK'_tree]
    dsimp only
    obtain ⟨px, hpx, hpxlen⟩ := hTG.connected.exists_path_of_dist cG x_star.1
    have hpx_snd : px.snd = u_C0.1 := path_snd_eq_root_of_compSet G hTG cG C₀
      (mem_erase.mp hx_K').2 hpx
    have hx_C0 : x_star.1 ∈ compSet G cG C₀ := (mem_erase.mp hx_K').2
    have hpx_np : ¬ px.Nil := not_nil_of_ne hx_ne_cG.symm
    let px1 : G.Walk u_C0.1 x_star.1 := px.tail.copy hpx_snd rfl
    have hpx1 : px1.IsPath := (isPath_copy _ _ _).mpr hpx.tail
    have hpx1_np : ¬ px1.Nil := not_nil_of_ne hx_ne_uC0.symm
    have hpx1_snd : px1.snd = u₂.1 := by
      have hadj : G.Adj u_C0.1 px1.snd := px1.adj_snd hpx1_np
      have h_in_C0 : px1.snd ∈ compSet G cG C₀ := by
        have hm : px1.snd ∈ px.support := by
          have := List.mem_of_mem_tail (px1.snd_mem_tail_support hpx1_np)
          change px1.snd ∈ (px.tail.copy hpx_snd rfl).support at this
          rw [support_copy, support_tail_of_not_nil px hpx_np] at this
          exact List.mem_of_mem_tail this
        have hne_c : px1.snd ≠ cG := fun h => by
          have : cG ∈ px.support.tail := by
            have := List.mem_of_mem_tail (px1.snd_mem_tail_support hpx1_np)
            change px1.snd ∈ (px.tail.copy hpx_snd rfl).support at this
            rw [support_copy, support_tail_of_not_nil px hpx_np] at this
            rw [h] at this; exact this
          exact start_notMem_tail_support_of_isPath hpx this
        exact mem_compSet_of_walk_from_c G cG C₀ hx_C0 hpx hm hne_c
      have h_eq := hex_u2.choose_spec.2 ⟨px1.snd, hadj.ne.symm⟩
        ⟨mem_erase.mpr ⟨hadj.ne.symm, h_in_C0⟩, hadj⟩
      dsimp only [u₂]; exact congrArg Subtype.val h_eq
    let px2 : G.Walk u₂.1 x_star.1 := px1.tail.copy hpx1_snd rfl
    have hpx2 : px2.IsPath := (isPath_copy _ _ _).mpr hpx1.tail
    have h1 : G.dist cG x_star.1 - 1 - 1 = G.dist u₂.1 x_star.1 := by
      have heq := isTree_dist_eq_length_of_isPath G hTG px2 hpx2
      simpa [px2, px1, length_copy, length_tail, hpxlen] using heq
    have h2 : G.dist cG x_star.1 - 1 = G.dist u_C0.1 x_star.1 := by
      have heq := isTree_dist_eq_length_of_isPath G hTG px1 hpx1
      simpa [px1, length_copy, length_tail, hpxlen] using heq
    have hpos2 : 1 ≤ G.dist u_C0.1 x_star.1 := hTG.connected.pos_dist_of_ne hx_ne_uC0.symm
    omega
  have hdist_img : (G.induce (K' : Set V)).dist ⟨u₂.1, hu2_K'⟩ ⟨x_star.1, hx_K'⟩ =
      (H.induce (S_H : Set W)).dist ⟨k₀.1, hk0_SH⟩ ⟨y_img.1, hy_img_SH⟩ := by
    have h1 : (G.induce (K' : Set V)).dist ⟨u₂.1, hu2_K'⟩ ⟨x_star.1, hx_K'⟩ =
        (H.induce (K : Set W)).dist (ψ_K ⟨u₂.1, hu2_K'⟩) y_img := (iso_dist_eq _ _ ψ_K _ _).symm
    rw [h1, hψK_root, dist_induce_eq_of_isTree H hTH (K : Set W) hK_tree,
      dist_induce_eq_of_isTree H hTH (S_H : Set W) hSH_tree]
  omega
set_option maxHeartbeats 800000 in
private lemma boundary_case {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (hTG : G.IsTree) (hTH : H.IsTree)
    (σ : V ≃ W) (hσ : ∀ v : V, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ))
    (hdeg : ∀ v : V, (G.neighborSet v).ncard = (H.neighborSet (σ v)).ncard)
    (hnonpath : ∃ v : V, 3 ≤ (G.neighborSet v).ncard)
    {r : ℕ} (hr : 2 ≤ r) (hdiamG : G.diam = 2 * r) (hdiamH : H.diam = 2 * r)
    (cG : V) (cH : W) (heccG : G.eccent cG = r) (heccH : H.eccent cH = r)
    (huG : ∀ v : V, v ≠ cG → (r : ℕ∞) < G.eccent v)
    (huH : ∀ w : W, w ≠ cH → (r : ℕ∞) < H.eccent w)
    (hdegc : G.degree cG = H.degree cH)
    (hnoLeafG : ∀ v : V, G.Adj cG v → 2 ≤ G.degree v)
    (hnoLeafH : ∀ w : W, H.Adj cH w → 2 ≤ H.degree w)
    (C₀ : (G.induce {cG}ᶜ).ConnectedComponent) {M : ℕ}
    (hM : r + 1 ≤ M) (hC0_card : card C₀.supp = M)
    (hmaxG : ∀ C : (G.induce {cG}ᶜ).ConnectedComponent, card C.supp ≤ M)
    (hmaxH : ∀ D : (H.induce {cH}ᶜ).ConnectedComponent, card D.supp ≤ M)
    (hbound : M + 1 + r = card V) :
    Nonempty (G ≃g H) := by
  have hcardVW : card V = card W := card_congr σ
  obtain ⟨C₁, hC01', xd_v, hxd_mem_v, hxd_dist⟩ :=
    exists_other_diam_comp G hTG hr hdiamG cG heccG C₀
  have hC01 : C₀ ≠ C₁ := hC01'.symm
  obtain ⟨hxd_ne_cG, hxd_supp⟩ := (mem_compSet_iff G cG C₁ xd_v).mp hxd_mem_v
  let xd : ({cG}ᶜ : Set V) := ⟨xd_v, hxd_ne_cG⟩
  have hr_le_C1 : r ≤ card C₁.supp := hxd_dist ▸ comp_dist_ge_of_mem G hTG cG C₁ hxd_supp
  have hsumG := sum_card_connectedComponent_eq G cG
  have hC1_card : card C₁.supp = r := by
    have hsub : card C₀.supp + card C₁.supp ≤
        ∑ C : (G.induce {cG}ᶜ).ConnectedComponent, card C.supp := by
      have h1 := add_sum_erase univ (fun C : (G.induce {cG}ᶜ).ConnectedComponent => card C.supp)
        (mem_univ C₀)
      have h2 : card C₁.supp ≤ ∑ C ∈ univ.erase C₀, card C.supp :=
        single_le_sum (fun (C : (G.induce {cG}ᶜ).ConnectedComponent) _ => Nat.zero_le (card C.supp))
          (mem_erase.mpr ⟨hC01', mem_univ _⟩)
      omega
    omega
  have hall_G : ∀ C : (G.induce {cG}ᶜ).ConnectedComponent, C = C₀ ∨ C = C₁ := by
    intro C
    by_contra hnot; push Not at hnot
    have hsum_3 : card C₀.supp + card C₁.supp + card C.supp ≤
        ∑ C' : (G.induce {cG}ᶜ).ConnectedComponent, card C'.supp := by
      have h1 := add_sum_erase univ (fun C' : (G.induce {cG}ᶜ).ConnectedComponent => card C'.supp)
        (mem_univ C₀)
      have h2 := add_sum_erase (univ.erase C₀)
        (fun C' : (G.induce {cG}ᶜ).ConnectedComponent => card C'.supp)
        (mem_erase.mpr ⟨hC01', mem_univ _⟩)
      have h3 : card C.supp ≤
          ∑ C' ∈ (univ.erase C₀).erase C₁, card C'.supp :=
        single_le_sum (fun (C' : (G.induce {cG}ᶜ).ConnectedComponent) _ => Nat.zero_le (card C'.supp))
          (mem_erase.mpr ⟨hnot.2, mem_erase.mpr ⟨hnot.1, mem_univ _⟩⟩)
      omega
    have hC_pos := comp_noLeaf_card_ge_two G hTG cG hnoLeafG C
    omega
  have hdegG2 : G.degree cG = 2 := by
    rw [← card_connectedComponent_eq_degree G hTG cG]
    have huniv : (univ : Finset (G.induce {cG}ᶜ).ConnectedComponent) = {C₀, C₁} := by
      ext C; simp [hall_G C]
    rw [← card_univ, huniv, card_pair hC01]
  have hdegH2 : H.degree cH = 2 := hdegc ▸ hdegG2
  obtain ⟨x₀, hx0_C0, hx0_deg1, hx0_diam⟩ :=
    comp_exists_good_leaf_of_radius_lt_card G hTG hr hdiamG cG heccG C₀ (hC0_card ▸ hM)
  obtain ⟨φ₀⟩ := hσ x₀
  have hσx0_deg1 : H.degree (σ x₀) = 1 := by
    rw [← ncard_neighborSet_eq_degree, ← hdeg x₀, ncard_neighborSet_eq_degree, hx0_deg1]
  obtain ⟨hcG_x0, hcH_x0, hφ0_c⟩ :=
    iso_map_center_of_good_leaf G H hTG hTH (by omega) cG cH heccG huG heccH huH hx0_deg1 hσx0_deg1 hx0_diam φ₀
  have hσx0_cH : σ x₀ ≠ cH := fun h => hcH_x0 h.symm
  let D_hit := (H.induce {cH}ᶜ).connectedComponentMk ⟨σ x₀, hσx0_cH⟩
  have hσx0_Dhit : σ x₀ ∈ compSet H cH D_hit := (mem_compSet_iff H cH D_hit (σ x₀)).mpr ⟨hσx0_cH, rfl⟩
  obtain ⟨D_other, hD_other_ne, yd_w, hyd_mem_w, hyd_dist⟩ :=
    exists_other_diam_comp H hTH hr hdiamH cH heccH D_hit
  have hall_H : ∀ D : (H.induce {cH}ᶜ).ConnectedComponent, D = D_hit ∨ D = D_other := by
    intro D; by_contra hnot; push Not at hnot
    have hcard_cc : card (H.induce {cH}ᶜ).ConnectedComponent = 2 := by
      rw [card_connectedComponent_eq_degree H hTH cH, hdegH2]
    have h3 : ({D_hit, D_other, D} : Finset _).card ≤ 2 := hcard_cc ▸ card_le_univ _
    have hc3 : ({D_hit, D_other, D} : Finset _).card = 3 := by
      rw [card_insert_of_notMem, card_pair hnot.2.symm]
      simp [hD_other_ne.symm, hnot.1.symm]
    omega
  have hx0_ne_cG : x₀ ≠ cG := fun h => hcG_x0 h.symm
  have hG_er := comp_erase_leaf_structure G hTG cG hnoLeafG hx0_deg1 hx0_ne_cG C₀ hx0_C0
  have hH_er := comp_erase_leaf_structure H hTH cH hnoLeafH hσx0_deg1 hσx0_cH D_hit hσx0_Dhit
  obtain ⟨C₀', hC0'_map, hC0'_iso, hC_G_other, _⟩ := hG_er
  obtain ⟨D_hit', hD'_map, hD'_iso, hD_H_other, hH_back⟩ := hH_er
  obtain ⟨eφ, heφ⟩ := iso_transport_comp (G.induce {x₀}ᶜ) (H.induce {σ x₀}ᶜ)
    ⟨cG, hcG_x0⟩ ⟨cH, hcH_x0⟩ φ₀ hφ0_c
  obtain ⟨C₁', hC1'_ne, hC1'_map, hC1'_iso⟩ := hC_G_other C₁ hC01.symm
  obtain ⟨D_other', hD_o'_ne, hD_o'_map, hD_o'_iso⟩ := hD_H_other D_other hD_other_ne
  have hC0'_card : card C₀'.supp = M - 1 := by
    have hc0' : card C₀'.supp = (compSet (G.induce {x₀}ᶜ) ⟨cG, hcG_x0⟩ C₀').card := by
      convert (compSet_card_eq (G.induce {x₀}ᶜ) ⟨cG, hcG_x0⟩ C₀').symm
    rw [hc0', ← card_map (⟨Subtype.val, val_injective⟩ : ({x₀}ᶜ : Set V) ↪ V), hC0'_map,
      card_erase_of_mem hx0_C0, compSet_card_eq, hC0_card]
  have hC1'_card : card C₁'.supp = r := by
    have hc1' : card C₁'.supp = (compSet (G.induce {x₀}ᶜ) ⟨cG, hcG_x0⟩ C₁').card := by
      convert (compSet_card_eq (G.induce {x₀}ᶜ) ⟨cG, hcG_x0⟩ C₁').symm
    rw [hc1', ← card_map (⟨Subtype.val, val_injective⟩ : ({x₀}ᶜ : Set V) ↪ V), hC1'_map,
      compSet_card_eq, hC1_card]
  have hD'_card : card D_hit'.supp = card D_hit.supp - 1 := by
    have hd' : card D_hit'.supp = (compSet (H.induce {σ x₀}ᶜ) ⟨cH, hcH_x0⟩ D_hit').card := by
      convert (compSet_card_eq (H.induce {σ x₀}ᶜ) ⟨cH, hcH_x0⟩ D_hit').symm
    rw [hd', ← card_map (⟨Subtype.val, val_injective⟩ : ({σ x₀}ᶜ : Set W) ↪ W), hD'_map,
      card_erase_of_mem hσx0_Dhit, compSet_card_eq]
  have hDo'_card : card D_other'.supp = card D_other.supp := by
    have hdo' : card D_other'.supp = (compSet (H.induce {σ x₀}ᶜ) ⟨cH, hcH_x0⟩ D_other').card := by
      convert (compSet_card_eq (H.induce {σ x₀}ᶜ) ⟨cH, hcH_x0⟩ D_other').symm
    rw [hdo', ← card_map (⟨Subtype.val, val_injective⟩ : ({σ x₀}ᶜ : Set W) ↪ W), hD_o'_map,
      compSet_card_eq]
  have hall_H_er : ∀ D' : ((H.induce {σ x₀}ᶜ).induce {⟨cH, hcH_x0⟩}ᶜ).ConnectedComponent,
      D' = D_hit' ∨ D' = D_other' := by
    intro D'
    by_cases heq : D' = D_hit'
    · exact Or.inl heq
    · right
      obtain ⟨D, hD_ne, _, _⟩ := hH_back D' heq
      have hDeq : D = D_other := (hall_H D).resolve_left hD_ne
      have hdeg2' : (H.induce {σ x₀}ᶜ).degree ⟨cH, hcH_x0⟩ = 2 := by
        rw [degree_induce_compl_singleton_of_not_adj H hcH_x0
          (fun h => by have := hnoLeafH (σ x₀) h; omega), hdegH2]
      have hHT' := induce_compl_singleton_isTree_of_deg_one H hTH hσx0_deg1
      have hcard_cc : card ((H.induce {σ x₀}ᶜ).induce {⟨cH, hcH_x0⟩}ᶜ).ConnectedComponent = 2 := by
        convert (card_connectedComponent_eq_degree _ hHT' ⟨cH, hcH_x0⟩).trans hdeg2'
      by_contra hne2
      have h3 : ({D_hit', D_other', D'} : Finset _).card ≤ 2 := hcard_cc ▸ card_le_univ _
      have hc3 : ({D_hit', D_other', D'} : Finset _).card = 3 := by
        rw [card_insert_of_notMem, card_pair (Ne.symm hne2)]
        simp only [mem_insert, mem_singleton]
        rintro (h | h) <;> [exact hD_o'_ne h.symm; exact heq h.symm]
      omega
  have hsumH := sum_card_connectedComponent_eq H cH
  have hsumH_2 : card D_hit.supp + card D_other.supp = M + r := by
    have h1 := add_sum_erase univ (fun D : (H.induce {cH}ᶜ).ConnectedComponent => card D.supp)
      (mem_univ D_hit)
    have huniv_er : univ.erase D_hit = {D_other} := by
      ext D; simp only [mem_erase, mem_singleton, mem_univ, and_true]
      exact ⟨fun h => (hall_H D).resolve_left h, fun h => h ▸ hD_other_ne⟩
    rw [huniv_er, Finset.sum_singleton] at h1
    omega
  have hex_D01 : ∃ (D₀ D₁ : (H.induce {cH}ᶜ).ConnectedComponent),
      D₀ ≠ D₁ ∧ card D₀.supp = M ∧ card D₁.supp = r := by
    rcases hall_H_er (eφ C₁') with h1 | h2
    · -- eφ C₁' = D_hit': so D_hit.card - 1 = r, D_other.card = M - 1!
      have hDhit_card : card D_hit.supp = r + 1 := by
        have h_eq1 := (heφ C₁').1
        rw [h1] at h_eq1
        have h_eq2 : card D_hit'.supp = card C₁'.supp := by convert h_eq1
        rw [hD'_card, hC1'_card] at h_eq2
        have := comp_noLeaf_card_ge_two H hTH cH hnoLeafH D_hit
        omega
      have hDo_card : card D_other.supp = M - 1 := by omega
      by_cases hMeq : M = r + 1
      · exact ⟨D_hit, D_other, hD_other_ne.symm, by omega, by omega⟩
      · -- Rule out {r+1, M-1} for M >= r + 2 via G - xd ≃ H - σ xd!
        have hMge : r + 2 ≤ M := by omega
        obtain ⟨hxd_deg1, hxd_diam⟩ :=
          diam_sub_of_path_r_end G hTG hr hdiamG cG heccG hdegG2 C₀ C₁ hC01 hC1_card hxd_supp hxd_dist
        obtain ⟨ψ⟩ := hσ xd.1
        have hσxd_deg1 : H.degree (σ xd.1) = 1 := by
          rw [← ncard_neighborSet_eq_degree, ← hdeg xd.1, ncard_neighborSet_eq_degree, hxd_deg1]
        have hσxd_diam : (H.induce {σ xd.1}ᶜ).diam = 2 * r - 1 :=
          (iso_diam_eq _ _ ψ).symm.trans hxd_diam
        have hσxd_ne_cH : σ xd.1 ≠ cH := by
          rintro rfl; have := hdegH2; omega
        let Da := (H.induce {cH}ᶜ).connectedComponentMk ⟨σ xd.1, hσxd_ne_cH⟩
        have hσxd_Da : σ xd.1 ∈ compSet H cH Da := (mem_compSet_iff H cH Da (σ xd.1)).mpr ⟨hσxd_ne_cH, rfl⟩
        obtain ⟨Db, hDab, hDb_card⟩ : ∃ Db, Da ≠ Db ∧
            ((Da = D_hit ∧ Db = D_other) ∨ (Da = D_other ∧ Db = D_hit)) := by
          rcases hall_H Da with hDa | hDa
          · exact ⟨D_other, hDa ▸ hD_other_ne.symm, Or.inl ⟨hDa, rfl⟩⟩
          · exact ⟨D_hit, hDa ▸ hD_other_ne, Or.inr ⟨hDa, rfl⟩⟩
        have infoG := bicenter_del_leaf_info G hTG hr hdiamG cG heccG hdegG2 C₁ C₀ hC01.symm hxd_deg1
          hxd_mem_v hxd_diam
        have infoH := bicenter_del_leaf_info H hTH hr hdiamH cH heccH hdegH2 Da Db hDab hσxd_deg1
          hσxd_Da hσxd_diam
        let uC0 := (existsUnique_root_of_component G hTG cG C₀).choose
        let vDb := (existsUnique_root_of_component H hTH cH Db).choose
        have hu_mem := (existsUnique_root_of_component G hTG cG C₀).choose_spec.1.1
        have hv_mem := (existsUnique_root_of_component H hTH cH Db).choose_spec.1.1
        have hu_v : uC0.1 ∈ ({xd.1}ᶜ : Set V) := fun h =>
          (Finset.disjoint_left.mp (compSet_disjoint G cG hC01)
            ((mem_compSet_iff G cG C₀ uC0.1).mpr ⟨uC0.2, hu_mem⟩))
            (h ▸ hxd_mem_v)
        have hv_v : vDb.1 ∈ ({σ xd.1}ᶜ : Set W) := fun h =>
          (Finset.disjoint_left.mp (compSet_disjoint H cH hDab) hσxd_Da)
            (h ▸ (mem_compSet_iff H cH Db vDb.1).mpr ⟨vDb.2, hv_mem⟩)
        let cG' : ({xd.1}ᶜ : Set V) := ⟨cG, Ne.symm xd.2⟩
        let uC0' : ({xd.1}ᶜ : Set V) := ⟨uC0.1, hu_v⟩
        let cH' : ({σ xd.1}ᶜ : Set W) := ⟨cH, hσxd_ne_cH.symm⟩
        let vDb' : ({σ xd.1}ᶜ : Set W) := ⟨vDb.1, hv_v⟩
        have hψ_map : (ψ uC0' = vDb' ∧ ψ cG' = cH') ∨ (ψ uC0' = cH' ∧ ψ cG' = vDb') := by
          have hu_in : ψ uC0' = cH' ∨ ψ uC0' = vDb' := by
            by_contra hnot; push Not at hnot
            have hlt := infoH.2.1.2.2 (ψ uC0') hnot.1 hnot.2
            rw [iso_eccent_eq _ _ ψ uC0', infoG.2.1.2.1] at hlt
            exact absurd hlt (lt_irrefl _)
          have hc_in : ψ cG' = cH' ∨ ψ cG' = vDb' := by
            by_contra hnot; push Not at hnot
            have hlt := infoH.2.1.2.2 (ψ cG') hnot.1 hnot.2
            rw [iso_eccent_eq _ _ ψ cG', infoG.2.1.1] at hlt
            exact absurd hlt (lt_irrefl _)
          rcases hu_in with hu1 | hu2 <;> rcases hc_in with hc1 | hc2
          · exact False.elim ((existsUnique_root_of_component G hTG cG C₀).choose_spec.1.2.ne.symm
              (congrArg Subtype.val (ψ.injective (hu1.trans hc1.symm))))
          · exact Or.inr ⟨hu1, hc2⟩
          · exact Or.inl ⟨hu2, hc1⟩
          · exact False.elim ((existsUnique_root_of_component G hTG cG C₀).choose_spec.1.2.ne.symm
              (congrArg Subtype.val (ψ.injective (hu2.trans hc2.symm))))
        rcases hψ_map with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have heq : card C₀.supp = card Db.supp := by
            have hG_eq : card C₀.supp = (univ.filter fun z' : ({xd.1}ᶜ : Set V) =>
                (G.induce {xd.1}ᶜ).dist z' uC0' < (G.induce {xd.1}ᶜ).dist z' cG').card :=
              infoG.2.2.1.symm.trans (by simp [uC0', cG', uC0, xd])
            have hH_eq : card Db.supp = (univ.filter fun w' : ({σ xd.1}ᶜ : Set W) =>
                (H.induce {σ xd.1}ᶜ).dist w' vDb' < (H.induce {σ xd.1}ᶜ).dist w' cH').card :=
              infoH.2.2.1.symm.trans (by simp [vDb', cH', vDb])
            rw [hG_eq, hH_eq]
            refine card_bij (fun z' _ => ψ z') ?_ (fun _ _ _ _ h => ψ.injective h) ?_
            · intro z' hz'; rw [mem_filter] at hz' ⊢; refine ⟨mem_univ _, ?_⟩
              rw [← h1, ← h2, iso_dist_eq _ _ ψ, iso_dist_eq _ _ ψ]; exact hz'.2
            · intro w' hw'; rw [mem_filter] at hw'
              refine ⟨ψ.symm w', mem_filter.mpr ⟨mem_univ _, ?_⟩, ψ.apply_symm_apply w'⟩
              rw [← iso_dist_eq _ _ ψ (ψ.symm w') uC0', ← iso_dist_eq _ _ ψ (ψ.symm w') cG',
                ψ.apply_symm_apply, h1, h2]; exact hw'.2
          rcases hDb_card with ⟨_, hDb⟩ | ⟨_, hDb⟩
          · rw [hDb] at heq; omega
          · rw [hDb] at heq; omega
        · have heq : card C₀.supp = card Da.supp := by
            have hG_eq : card C₀.supp = (univ.filter fun z' : ({xd.1}ᶜ : Set V) =>
                (G.induce {xd.1}ᶜ).dist z' uC0' < (G.induce {xd.1}ᶜ).dist z' cG').card :=
              infoG.2.2.1.symm.trans (by simp [uC0', cG', uC0, xd])
            have hH_eq : card Da.supp = (univ.filter fun w' : ({σ xd.1}ᶜ : Set W) =>
                (H.induce {σ xd.1}ᶜ).dist w' cH' < (H.induce {σ xd.1}ᶜ).dist w' vDb').card :=
              infoH.2.2.2.1.symm.trans (by simp [cH', vDb', vDb])
            rw [hG_eq, hH_eq]
            refine card_bij (fun z' _ => ψ z') ?_ (fun _ _ _ _ h => ψ.injective h) ?_
            · intro z' hz'; rw [mem_filter] at hz' ⊢; refine ⟨mem_univ _, ?_⟩
              rw [← h1, ← h2, iso_dist_eq _ _ ψ, iso_dist_eq _ _ ψ]; exact hz'.2
            · intro w' hw'; rw [mem_filter] at hw'
              refine ⟨ψ.symm w', mem_filter.mpr ⟨mem_univ _, ?_⟩, ψ.apply_symm_apply w'⟩
              rw [← iso_dist_eq _ _ ψ (ψ.symm w') uC0', ← iso_dist_eq _ _ ψ (ψ.symm w') cG',
                ψ.apply_symm_apply, h1, h2]; exact hw'.2
          rcases hDb_card with ⟨hDa, _⟩ | ⟨hDa, _⟩
          · rw [hDa] at heq; omega
          · rw [hDa] at heq; omega
    · have hDo_card : card D_other.supp = r := by
        have h_eq1 := (heφ C₁').1
        rw [h2] at h_eq1
        have h_eq2 : card D_other'.supp = card C₁'.supp := by convert h_eq1
        rw [hDo'_card, hC1'_card] at h_eq2; exact h_eq2
      exact ⟨D_hit, D_other, hD_other_ne.symm, by omega, hDo_card⟩
  obtain ⟨D₀, D₁, hD01, hD0_card, hD1_card⟩ := hex_D01
  have hall_H_01 : ∀ D : (H.induce {cH}ᶜ).ConnectedComponent, D = D₀ ∨ D = D₁ := by
    intro D; by_contra hnot; push Not at hnot
    have hcard_cc : card (H.induce {cH}ᶜ).ConnectedComponent = 2 := by
      rw [card_connectedComponent_eq_degree H hTH cH, hdegH2]
    have h3 : ({D₀, D₁, D} : Finset _).card ≤ 2 := hcard_cc ▸ card_le_univ _
    have hc3 : ({D₀, D₁, D} : Finset _).card = 3 := by
      rw [card_insert_of_notMem, card_pair hnot.2.symm]
      simp [hD01, hnot.1.symm]
    omega
  obtain ⟨D_o, hDo_ne, yd_w, hyd_mem_w, hyd_dist⟩ :=
    exists_other_diam_comp H hTH hr hdiamH cH heccH D₀
  have hDo_eq : D_o = D₁ := (hall_H_01 D_o).resolve_left hDo_ne
  rw [hDo_eq] at hyd_mem_w
  obtain ⟨hyd_ne_cH, hyd_supp⟩ := (mem_compSet_iff H cH D₁ yd_w).mp hyd_mem_w
  let yd : ({cH}ᶜ : Set W) := ⟨yd_w, hyd_ne_cH⟩
  by_cases hσxd_D1 : σ xd.1 ∈ compSet H cH D₁
  · obtain ⟨hxd_deg1, hxd_diam⟩ :=
      diam_sub_of_path_r_end G hTG hr hdiamG cG heccG hdegG2 C₀ C₁ hC01 hC1_card hxd_supp hxd_dist
    obtain ⟨ψ⟩ := hσ xd.1
    have hσxd_deg1 : H.degree (σ xd.1) = 1 := by
      rw [← ncard_neighborSet_eq_degree, ← hdeg xd.1, ncard_neighborSet_eq_degree, hxd_deg1]
    have hσxd_diam : (H.induce {σ xd.1}ᶜ).diam = 2 * r - 1 :=
      (iso_diam_eq _ _ ψ).symm.trans hxd_diam
    have infoG := bicenter_del_leaf_info G hTG hr hdiamG cG heccG hdegG2 C₁ C₀ hC01.symm hxd_deg1
      hxd_mem_v hxd_diam
    have infoH := bicenter_del_leaf_info H hTH hr hdiamH cH heccH hdegH2 D₁ D₀ hD01.symm hσxd_deg1
      hσxd_D1 hσxd_diam
    let uC0 := (existsUnique_root_of_component G hTG cG C₀).choose
    let vD0 := (existsUnique_root_of_component H hTH cH D₀).choose
    have huC0_mem := (existsUnique_root_of_component G hTG cG C₀).choose_spec.1.1
    have huC0_adj := (existsUnique_root_of_component G hTG cG C₀).choose_spec.1.2
    have hvD0_mem := (existsUnique_root_of_component H hTH cH D₀).choose_spec.1.1
    have hvD0_adj := (existsUnique_root_of_component H hTH cH D₀).choose_spec.1.2
    have hu_v : uC0.1 ∈ ({xd.1}ᶜ : Set V) := fun h =>
      (Finset.disjoint_left.mp (compSet_disjoint G cG hC01)
        ((mem_compSet_iff G cG C₀ uC0.1).mpr ⟨uC0.2, huC0_mem⟩))
        (h ▸ hxd_mem_v)
    have hv_v : vD0.1 ∈ ({σ xd.1}ᶜ : Set W) := fun h =>
      (Finset.disjoint_left.mp (compSet_disjoint H cH hD01)
        ((mem_compSet_iff H cH D₀ vD0.1).mpr ⟨vD0.2, hvD0_mem⟩)) (h ▸ hσxd_D1)
    let cG' : ({xd.1}ᶜ : Set V) := ⟨cG, Ne.symm xd.2⟩
    let uC0' : ({xd.1}ᶜ : Set V) := ⟨uC0.1, hu_v⟩
    let cH' : ({σ xd.1}ᶜ : Set W) := ⟨cH, fun h => c_notMem_compSet H cH D₁ (h ▸ hσxd_D1)⟩
    let vD0' : ({σ xd.1}ᶜ : Set W) := ⟨vD0.1, hv_v⟩
    have hψ_pair : ψ uC0' = vD0' ∧ ψ cG' = cH' := by
      have hu_in : ψ uC0' = cH' ∨ ψ uC0' = vD0' := by
        by_contra hnot; push Not at hnot
        have hlt := infoH.2.1.2.2 (ψ uC0') hnot.1 hnot.2
        rw [iso_eccent_eq _ _ ψ uC0', infoG.2.1.2.1] at hlt
        exact absurd hlt (lt_irrefl _)
      have hc_in : ψ cG' = cH' ∨ ψ cG' = vD0' := by
        by_contra hnot; push Not at hnot
        have hlt := infoH.2.1.2.2 (ψ cG') hnot.1 hnot.2
        rw [iso_eccent_eq _ _ ψ cG', infoG.2.1.1] at hlt
        exact absurd hlt (lt_irrefl _)
      rcases hu_in with hu1 | hu2
      · have hc2 : ψ cG' = vD0' := by
          rcases hc_in with hc1 | hc2
          · exact False.elim (huC0_adj.ne.symm (congrArg Subtype.val (ψ.injective (hu1.trans hc1.symm))))
          · exact hc2
        have heq : M = r := by
          have hM_eq : M = (univ.filter fun z' : ({xd.1}ᶜ : Set V) =>
              (G.induce {xd.1}ᶜ).dist z' uC0' < (G.induce {xd.1}ᶜ).dist z' cG').card :=
            hC0_card.symm.trans (infoG.2.2.1.symm.trans (by simp [uC0', cG', uC0, xd]))
          have hr_eq : r = (univ.filter fun w' : ({σ xd.1}ᶜ : Set W) =>
              (H.induce {σ xd.1}ᶜ).dist w' cH' < (H.induce {σ xd.1}ᶜ).dist w' vD0').card :=
            hD1_card.symm.trans (infoH.2.2.2.1.symm.trans (by simp [cH', vD0', vD0]))
          rw [hM_eq, hr_eq]
          refine card_bij (fun z' _ => ψ z') ?_ (fun _ _ _ _ h => ψ.injective h) ?_
          · intro z' hz'; rw [mem_filter] at hz' ⊢; refine ⟨mem_univ _, ?_⟩
            rw [← hu1, ← hc2, iso_dist_eq _ _ ψ, iso_dist_eq _ _ ψ]; exact hz'.2
          · intro w' hw'; rw [mem_filter] at hw'
            refine ⟨ψ.symm w', mem_filter.mpr ⟨mem_univ _, ?_⟩, ψ.apply_symm_apply w'⟩
            rw [← iso_dist_eq _ _ ψ (ψ.symm w') uC0', ← iso_dist_eq _ _ ψ (ψ.symm w') cG',
              ψ.apply_symm_apply, hu1, hc2]; exact hw'.2
        omega
      · refine ⟨hu2, ?_⟩
        rcases hc_in with hc1 | hc2
        · exact hc1
        · exact False.elim (huC0_adj.ne.symm (congrArg Subtype.val (ψ.injective (hu2.trans hc2.symm))))
    obtain ⟨φG_u, hφGu⟩ := infoG.2.2.2.2.1
    obtain ⟨φH_v, hφHv⟩ := infoH.2.2.2.2.1
    have hside : ∀ z' : ({xd.1}ᶜ : Set V),
        ((G.induce {xd.1}ᶜ).dist z' uC0' < (G.induce {xd.1}ᶜ).dist z' cG') ↔
        ((H.induce {σ xd.1}ᶜ).dist (ψ z') vD0' < (H.induce {σ xd.1}ᶜ).dist (ψ z') cH') := by
      intro z'
      rw [← hψ_pair.1, ← hψ_pair.2, iso_dist_eq _ _ ψ z' uC0', iso_dist_eq _ _ ψ z' cG']
    let SG_b : Set ({xd.1}ᶜ : Set V) :=
      {z' : ({xd.1}ᶜ : Set V) | (G.induce {xd.1}ᶜ).dist z' uC0' < (G.induce {xd.1}ᶜ).dist z' cG'}
    let SH_b : Set ({σ xd.1}ᶜ : Set W) :=
      {w' : ({σ xd.1}ᶜ : Set W) | (H.induce {σ xd.1}ᶜ).dist w' vD0' < (H.induce {σ xd.1}ᶜ).dist w' cH'}
    let ψ_b : (G.induce {xd.1}ᶜ).induce SG_b ≃g (H.induce {σ xd.1}ᶜ).induce SH_b :=
      ⟨⟨fun z' => ⟨ψ z'.1, (hside z'.1).mp z'.2⟩,
        fun w' => ⟨ψ.symm w'.1, (hside (ψ.symm w'.1)).mpr (by rw [ψ.apply_symm_apply]; exact w'.2)⟩,
        fun _ => Subtype.ext (ψ.symm_apply_apply _),
        fun _ => Subtype.ext (ψ.apply_symm_apply _)⟩, @fun _ _ => ψ.map_rel_iff⟩
    let φ_C0_D0 : G.induce (compSet G cG C₀ : Set V) ≃g H.induce (compSet H cH D₀ : Set W) :=
      φG_u.symm.trans (ψ_b.trans φH_v)
    have hφ_root : φ_C0_D0 ⟨uC0.1, (mem_compSet_iff G cG C₀ uC0.1).mpr ⟨uC0.2, huC0_mem⟩⟩ =
        ⟨vD0.1, (mem_compSet_iff H cH D₀ vD0.1).mpr ⟨vD0.2, hvD0_mem⟩⟩ := by
      change φH_v (ψ_b (φG_u.symm ⟨uC0.1, (mem_compSet_iff G cG C₀ uC0.1).mpr ⟨uC0.2, huC0_mem⟩⟩)) = _
      have hu_side : (G.induce {xd.1}ᶜ).dist uC0' uC0' < (G.induce {xd.1}ᶜ).dist uC0' cG' := by
        rw [dist_self, dist_comm, dist_eq_one_iff_adj.mpr (show (G.induce {xd.1}ᶜ).Adj cG' uC0' from huC0_adj)]
        omega
      have h1 : φG_u.symm ⟨uC0.1, (mem_compSet_iff G cG C₀ uC0.1).mpr ⟨uC0.2, huC0_mem⟩⟩ =
          (⟨uC0', hu_side⟩ : SG_b) := φG_u.symm_apply_eq.mpr (by convert hφGu.symm)
      rw [h1]
      have hv_side : (H.induce {σ xd.1}ᶜ).dist vD0' vD0' < (H.induce {σ xd.1}ᶜ).dist vD0' cH' := by
        rw [dist_self, dist_comm, dist_eq_one_iff_adj.mpr (show (H.induce {σ xd.1}ᶜ).Adj cH' vD0' from hvD0_adj)]
        omega
      have h2 : ψ_b ⟨uC0', hu_side⟩ = (⟨vD0', hv_side⟩ : SH_b) := Subtype.ext hψ_pair.1
      rw [h2, hφHv]
    have hR0 := rootedCompIso_of_root_iso G H hTG hTH cG cH C₀ D₀ huC0_mem huC0_adj hvD0_mem hvD0_adj
      φ_C0_D0 hφ_root
    have hR1 := rootedCompIso_of_path_r G H hTG hTH (by omega) cG cH heccG heccH C₁ hC1_card
      hxd_supp hxd_dist D₁ hD1_card hyd_supp hyd_dist
    let e : (G.induce {cG}ᶜ).ConnectedComponent ≃ (H.induce {cH}ᶜ).ConnectedComponent :=
      ⟨fun C => if C = C₀ then D₀ else D₁,
       fun D => if D = D₀ then C₀ else C₁,
       fun C => by rcases hall_G C with rfl | rfl <;> simp [hD01, hD01.symm, hC01, hC01.symm],
       fun D => by rcases hall_H_01 D with rfl | rfl <;> simp [hC01, hC01.symm, hD01, hD01.symm]⟩
    refine iso_of_rootedCompIso_bij G H cG cH e fun C => ?_
    rcases hall_G C with rfl | rfl
    · simpa [e] using hR0
    · simpa [e, hC01.symm] using hR1
  · have hσxd_D0 : σ xd.1 ∈ compSet H cH D₀ := by
      have hxd_deg1 := deg_one_of_path_r_end G hTG hr cG C₁ hC1_card hxd_supp hxd_dist
      have hσ_deg1 : H.degree (σ xd.1) = 1 := by
        rw [← ncard_neighborSet_eq_degree, ← hdeg xd.1, ncard_neighborSet_eq_degree, hxd_deg1]
      have hne_c : σ xd.1 ≠ cH := by rintro rfl; omega
      let Dx := (H.induce {cH}ᶜ).connectedComponentMk ⟨σ xd.1, hne_c⟩
      have hm : σ xd.1 ∈ compSet H cH Dx := (mem_compSet_iff H cH Dx (σ xd.1)).mpr ⟨hne_c, rfl⟩
      rcases hall_H_01 Dx with h | h
      · rwa [h] at hm
      · exact False.elim (hσxd_D1 (h ▸ hm))
    exact False.elim (boundary_contra_shifted_leaf G H hTG hTH σ hσ hdeg hnonpath hr hdiamG hdiamH
      cG cH heccG heccH hdegG2 hdegH2 hnoLeafG hnoLeafH hM C₀ C₁ hC01 hC0_card hC1_card
      hxd_supp hxd_dist D₀ D₁ hD01 hD0_card hD1_card hyd_supp hyd_dist hσxd_D0)
/-! ### Part 4: Kelly Q2, Q3, and path(2r+1) constructions and General Case (`M + 1 + r < n`) -/
private def Q2 {U₀ : Type} (T₀ : SimpleGraph U₀) (c₀ : U₀) (B₀ : Finset U₀) (r : ℕ) :
    SimpleGraph (Option (↥B₀ ⊕ Fin r)) where
  Adj a b := match a, b with
    | none, some (Sum.inl x) => T₀.Adj c₀ x.1
    | some (Sum.inl x), none => T₀.Adj c₀ x.1
    | none, some (Sum.inr i) => i.val = 0
    | some (Sum.inr i), none => i.val = 0
    | some (Sum.inl x), some (Sum.inl y) => T₀.Adj x.1 y.1
    | some (Sum.inr i), some (Sum.inr j) => (pathG r).Adj i j
    | _, _ => False
  symm := ⟨by
    rintro (_ | (x | i)) (_ | (y | j)) h <;> simp only at h ⊢
    · exact h
    · exact h
    · exact h
    · exact h.symm
    · exact h
    · exact h.symm⟩
  loopless := ⟨by
    rintro (_ | (x | i)) h <;> simp only at h
    · exact T₀.loopless.irrefl x.1 h
    · exact (pathG r).loopless.irrefl i h⟩
private def Q3 {U₀ : Type} (T₀ : SimpleGraph U₀) (c₀ : U₀) (B₀ : Finset U₀) (r : ℕ) :
    SimpleGraph (Option (↥B₀ ⊕ (Fin r ⊕ Fin r))) where
  Adj a b := match a, b with
    | none, some (Sum.inl x) => T₀.Adj c₀ x.1
    | some (Sum.inl x), none => T₀.Adj c₀ x.1
    | none, some (Sum.inr (Sum.inl i)) => i.val = 0
    | some (Sum.inr (Sum.inl i)), none => i.val = 0
    | none, some (Sum.inr (Sum.inr i)) => i.val = 0
    | some (Sum.inr (Sum.inr i)), none => i.val = 0
    | some (Sum.inl x), some (Sum.inl y) => T₀.Adj x.1 y.1
    | some (Sum.inr (Sum.inl i)), some (Sum.inr (Sum.inl j)) => (pathG r).Adj i j
    | some (Sum.inr (Sum.inr i)), some (Sum.inr (Sum.inr j)) => (pathG r).Adj i j
    | _, _ => False
  symm := ⟨by
    rintro (_ | (x | (i | i))) (_ | (y | (j | j))) h <;> simp only at h ⊢
    · exact h
    · exact h
    · exact h
    · exact h
    · exact h.symm
    · exact h
    · exact h.symm
    · exact h
    · exact h.symm⟩
  loopless := ⟨by
    rintro (_ | (x | (i | i))) h <;> simp only at h
    · exact T₀.loopless.irrefl x.1 h
    · exact (pathG r).loopless.irrefl i h
    · exact (pathG r).loopless.irrefl i h⟩
private lemma subset_comp_of_connected {U : Type} [Fintype U]
    (T : SimpleGraph U) (c : U) (A : Finset U) (hA_ne : A.Nonempty) (hc_not : c ∉ A)
    (hconn : (T.induce (A : Set U)).Connected) :
    ∃ D : (T.induce {c}ᶜ).ConnectedComponent, A ⊆ compSet T c D ∧ A.card ≤ card D.supp := by
  obtain ⟨a₀, ha₀⟩ := hA_ne
  have ha0_c : a₀ ≠ c := fun h => hc_not (h ▸ ha₀)
  let D := (T.induce {c}ᶜ).connectedComponentMk ⟨a₀, ha0_c⟩
  have hsub : A ⊆ compSet T c D := by
    intro a ha
    have hac : a ≠ c := fun h => hc_not (h ▸ ha)
    refine (mem_compSet_iff T c D a).mpr ⟨hac, ?_⟩
    obtain ⟨w⟩ := hconn ⟨a₀, ha₀⟩ ⟨a, ha⟩
    let g : T.induce (A : Set U) →g T.induce {c}ᶜ :=
      ⟨fun x => ⟨x.1, fun h => hc_not (h ▸ x.2)⟩, @fun _ _ h => h⟩
    have hreach : (T.induce {c}ᶜ).Reachable ⟨a₀, ha0_c⟩ ⟨a, hac⟩ := ⟨w.map g⟩
    exact (mem_supp_iff D _).mpr (sound hreach).symm
  exact ⟨D, hsub, (card_le_card hsub).trans (compSet_card_eq T c D).le⟩
private lemma pathG_walk_up {r : ℕ} (k : ℕ) (hk : k < r) :
    ∃ p : (pathG r).Walk ⟨0, by omega⟩ ⟨k, hk⟩,
      p.IsPath ∧ p.length = k ∧ ∀ i ∈ p.support, i.val ≤ k := by
  induction k with
  | zero => exact ⟨Walk.nil, Walk.IsPath.nil, rfl, fun i hi => by
      simp only [Walk.support_nil, List.mem_singleton] at hi; rw [hi]⟩
  | succ k ih =>
    obtain ⟨p, hp, hplen, hsupp⟩ := ih (by omega)
    have hadj : (pathG r).Adj ⟨k, by omega⟩ ⟨k + 1, hk⟩ := Or.inl rfl
    have hnot : (⟨k + 1, hk⟩ : Fin r) ∉ p.support := fun hm => by
      have h1 := hsupp _ hm; dsimp only at h1; omega
    refine ⟨p.concat hadj, ?_, by simp [hplen], fun i hi => ?_⟩
    · rw [isPath_def, Walk.support_concat, List.nodup_append]
      refine ⟨hp.support_nodup, List.nodup_singleton _, fun x hx y hy heq => ?_⟩
      simp only [List.mem_singleton] at hy; rw [heq, hy] at hx; exact hnot hx
    · rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hi
      rcases hi with hm | rfl
      · exact (hsupp i hm).trans (Nat.le_succ _)
      · exact le_rfl
private lemma pathG_walk_down {r : ℕ} (a b : Fin r) (hab : a.val ≤ b.val) :
    ∃ p : (pathG r).Walk a b, p.IsPath ∧ p.length = b.val - a.val := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hab
  induction d generalizing a b with
  | zero =>
    have heq : a = b := Fin.ext (by omega)
    subst heq
    exact ⟨Walk.nil, Walk.IsPath.nil, by simp⟩
  | succ d ih =>
    have ha1 : a.val + 1 < r := by omega
    let a1 : Fin r := ⟨a.val + 1, ha1⟩
    obtain ⟨p, hp, hplen⟩ := ih a1 b (by dsimp [a1]; omega) (by dsimp [a1]; omega)
    have hadj : (pathG r).Adj a a1 := Or.inl rfl
    have hsupp_ge : ∀ w : Fin r, (∃ q : (pathG r).Walk a1 b, q.IsPath ∧ q.length = b.val - a1.val) → True :=
      fun _ _ => trivial
    refine ⟨(Walk.cons hadj p).bypass, Walk.bypass_isPath _, ?_⟩
    have h1 := Walk.length_bypass_le_length (Walk.cons hadj p)
    have h2 : ∀ (u v : Fin r) (q : (pathG r).Walk u v), v.val - u.val ≤ q.length := by
      intro u v q
      induction q with
      | nil => simp
      | @cons x y z hxy q' ihq =>
        have hadj_xy : x.val + 1 = y.val ∨ y.val + 1 = x.val := hxy
        simp only [length_cons] at *
        omega
    have h3 := h2 a b (Walk.cons hadj p).bypass
    rw [length_cons, hplen] at h1
    dsimp [a1] at h1
    omega
private lemma Q2_center_forced {U₀ V' : Type} [Fintype U₀] [Fintype V']
    (T₀ : SimpleGraph U₀) (hT0 : T₀.IsTree) (c₀ : U₀) (B₀ : Finset U₀)
    (hc0_not : c₀ ∉ B₀)
    (hB0_conn : (T₀.induce (insert c₀ (B₀ : Set U₀))).Connected)
    (T : SimpleGraph V') (hT : T.IsTree) {r M : ℕ} (hr : 2 ≤ r)
    (c : V') (hecc : T.eccent c = r)
    (hmax : ∀ D : (T.induce {c}ᶜ).ConnectedComponent, card D.supp ≤ M)
    (hgtM : M < B₀.card + 1 + r) (hM_le : M ≤ B₀.card + 1)
    (hforce : B₀.card = M ∨ ∃ b ∈ B₀, r ≤ T₀.dist c₀ b)
    (S : Finset V') (ψ : T.induce (S : Set V') ≃g Q2 T₀ c₀ B₀ r) :
    ∃ hc : c ∈ S, ψ ⟨c, hc⟩ = none := by
  let Q := Q2 T₀ c₀ B₀ r
  have hQ_conn : Q.Connected := by
    refine Connected.mk fun a b => ?_
    suffices h0 : ∀ x : Option (↥B₀ ⊕ Fin r), Q.Reachable none x from (h0 a).symm.trans (h0 b)
    rintro (_ | (x | i))
    · exact Reachable.rfl
    · obtain ⟨w⟩ := hB0_conn ⟨c₀, Set.mem_insert c₀ _⟩ ⟨x.1, Set.mem_insert_of_mem c₀ x.2⟩
      let g : T₀.induce (insert c₀ (B₀ : Set U₀)) →g Q :=
        ⟨fun z => if hz : z.1 = c₀ then none else some (Sum.inl ⟨z.1, (mem_insert_iff.mp z.2).resolve_left hz⟩),
         @fun z₁ z₂ hadj => by
          by_cases h1 : z₁.1 = c₀ <;> by_cases h2 : z₂.1 = c₀
          · exact False.elim (T₀.ne_of_adj hadj (h1.trans h2.symm))
          · simp only [dif_pos h1, dif_neg h2]; exact (congrArg (fun u => T₀.Adj u z₂.1) h1).mp hadj
          · simp only [dif_neg h1, dif_pos h2]; exact (congrArg (fun u => T₀.Adj u z₁.1) h2).mp hadj.symm
          · simp only [dif_neg h1, dif_neg h2]; exact hadj⟩
      have heq1 : g ⟨c₀, Set.mem_insert c₀ _⟩ = none := by simp [g]
      have heq2 : g ⟨x.1, Set.mem_insert_of_mem c₀ x.2⟩ = some (Sum.inl x) := by
        have hx_ne : x.1 ≠ c₀ := fun h => hc0_not (h ▸ x.2)
        simp [g, hx_ne]
      exact ⟨(w.map g).copy heq1 heq2⟩
    · obtain ⟨p, _, _⟩ := pathG_walk_up i.val i.isLt
      have h0 : Q.Adj none (some (Sum.inr ⟨0, by omega⟩)) := rfl
      let g : pathG r →g Q := ⟨fun j => some (Sum.inr j), @fun _ _ h => h⟩
      exact ⟨Walk.cons h0 (p.map g)⟩
  have : Nonempty (S : Set V') := ⟨ψ.symm none⟩
  have hS_conn : (T.induce (S : Set V')).Connected :=
    ⟨fun a b => ⟨((hQ_conn (ψ a) (ψ b)).some.map ψ.symm.toHom).copy (ψ.symm_apply_apply a) (ψ.symm_apply_apply b)⟩⟩
  have hS_card : S.card = B₀.card + 1 + r := by
    have hsc : S.card = card (S : Set V') :=
      (card_coe S).symm.trans
        (card_congr ⟨fun x => ⟨x.1, x.2⟩, fun x => ⟨x.1, x.2⟩, fun _ => rfl, fun _ => rfl⟩)
    rw [hsc, card_congr ψ.toEquiv, card_option, card_sum, card_coe, card_fin]
    omega
  have hcS : c ∈ S := by
    by_contra hnc
    have hS_ne : S.Nonempty := by
      rw [← card_pos, hS_card]; omega
    obtain ⟨D, _, hDle⟩ := subset_comp_of_connected T c S hS_ne hnc hS_conn
    have := hmax D
    omega
  refine ⟨hcS, ?_⟩
  by_contra hne_none
  have h_no_long_path : ∀ (u : Option (↥B₀ ⊕ Fin r)) (p : Q.Walk (ψ ⟨c, hcS⟩) u),
      p.IsPath → p.length ≤ r := by
    intro u p hp
    let g : T.induce (S : Set V') →g T := (Embedding.induce (S : Set V')).toHom
    let pT : T.Walk c (ψ.symm u).1 := ((p.map ψ.symm.toHom).map g).copy
      (congrArg Subtype.val (ψ.symm_apply_apply ⟨c, hcS⟩)) rfl
    have hpT : pT.IsPath :=
      (isPath_copy _ _ _).mpr ((hp.map ψ.symm.injective).map val_injective)
    have hlen : pT.length = p.length :=
      (length_copy _ _ _).trans (by rw [length_map, length_map])
    rw [isTree_dist_eq_length_of_isPath T hT pT hpT] at hlen
    have hle := dist_le_of_eccent T hT (u := (ψ.symm u).1) hecc
    omega
  obtain ⟨pr, hpr, hprlen, _⟩ := pathG_walk_up (r := r) (r - 1) (by omega)
  let p_tail : Q.Walk none (some (Sum.inr ⟨r - 1, by omega⟩)) :=
    Walk.cons (by simp [Q, Q2] : Q.Adj none (some (Sum.inr ⟨0, by omega⟩)))
      (pr.map ⟨fun j => some (Sum.inr j), @fun _ _ h => h⟩)
  have hp_tail_path : p_tail.IsPath := by
    rw [cons_isPath_iff]
    refine ⟨hpr.map (fun _ _ h => Sum.inr.inj (Option.some.inj h)), fun hm => ?_⟩
    rw [Walk.support_map, List.mem_map] at hm
    obtain ⟨j, _, hj⟩ := hm
    simp at hj
  have hp_tail_len : p_tail.length = r := by
    simp only [p_tail, length_cons, length_map, hprlen]; omega
  cases hψc : ψ ⟨c, hcS⟩ with
  | none => exact hne_none hψc
  | some y =>
    cases y with
    | inl b =>
      obtain ⟨qb, hqb, _⟩ := (hB0_conn ⟨b.1, Set.mem_insert_of_mem c₀ b.2⟩
        ⟨c₀, Set.mem_insert c₀ _⟩).exists_path_of_dist
      let gB : T₀.induce (insert c₀ (B₀ : Set U₀)) →g Q :=
        ⟨fun z => if hz : z.1 = c₀ then none else some (Sum.inl ⟨z.1, (mem_insert_iff.mp z.2).resolve_left hz⟩),
         @fun z₁ z₂ hadj => by
          by_cases h1 : z₁.1 = c₀ <;> by_cases h2 : z₂.1 = c₀
          · exact False.elim (T₀.ne_of_adj hadj (h1.trans h2.symm))
          · simp only [dif_pos h1, dif_neg h2]; exact (congrArg (fun u => T₀.Adj u z₂.1) h1).mp hadj
          · simp only [dif_neg h1, dif_pos h2]; exact (congrArg (fun u => T₀.Adj u z₁.1) h2).mp hadj.symm
          · simp only [dif_neg h1, dif_neg h2]; exact hadj⟩
      have hgB_inj : Injective gB := by
        intro z₁ z₂ heq
        by_cases h1 : z₁.1 = c₀ <;> by_cases h2 : z₂.1 = c₀
        · exact Subtype.ext (h1.trans h2.symm)
        · simp [gB, h1, h2] at heq
        · simp [gB, h1, h2] at heq
        · dsimp only [gB] at heq; simp only [RelHom.coeFn_mk, dif_neg h1, dif_neg h2] at heq
          exact Subtype.ext (congrArg (fun z : ↥B₀ => z.1) (Sum.inl.inj (Option.some.inj heq)))
      have hqb_start : gB ⟨b.1, Set.mem_insert_of_mem c₀ b.2⟩ = some (Sum.inl b) := by
        have hbne : b.1 ≠ c₀ := fun h => hc0_not (h ▸ b.2)
        simp [gB, hbne]
      have hqb_end : gB ⟨c₀, Set.mem_insert c₀ _⟩ = none := by simp [gB]
      let qbQ : Q.Walk (some (Sum.inl b)) none := (qb.map gB).copy hqb_start hqb_end
      have hqbQ : qbQ.IsPath := (isPath_copy _ _ _).mpr (hqb.map hgB_inj)
      have hqbQ_len : 1 ≤ qbQ.length := by cases qbQ; simp
      have hmeet : ∀ u ∈ qbQ.support, u ∈ p_tail.support.tail → u = none := by
        intro u huq hut
        have hu1 : u = none ∨ ∃ x, u = some (Sum.inl x) := by
          have : u ∈ (qb.map gB).support := by simpa [qbQ, support_copy] using huq
          rw [Walk.support_map, List.mem_map] at this
          obtain ⟨z, _, rfl⟩ := this
          by_cases hz : z.1 = c₀
          · left; simp [gB, hz]
          · right; refine ⟨⟨z.1, (mem_insert_iff.mp z.2).resolve_left hz⟩, ?_⟩; simp [gB, hz]
        have hu2 : ∃ j, u = some (Sum.inr j) := by
          have : u ∈ (pr.map (⟨fun j => some (Sum.inr j), @fun _ _ h => h⟩ : pathG r →g Q)).support := by
            simpa [p_tail] using hut
          rw [Walk.support_map, List.mem_map] at this
          obtain ⟨j, _, rfl⟩ := this
          exact ⟨j, rfl⟩
        rcases hu1 with rfl | ⟨_, h1⟩ <;> obtain ⟨_, h2⟩ := hu2
        · rfl
        · have h := h1.symm.trans h2; simp at h
      have hpath := isPath_append_of_first_meet hqbQ hp_tail_path hmeet
      have hle := h_no_long_path _ ((qbQ.append p_tail).copy hψc.symm rfl) ((isPath_copy _ _ _).mpr hpath)
      rw [length_copy, length_append, hp_tail_len] at hle
      omega
    | inr k =>
      by_cases hkM : k.val ≥ 1 ∨ B₀.card = M
      · -- Subset A_sub = {none} ∪ inl B₀ ∪ {inr j | j.val < k.val} in Q \ {some (inr k)}:
        let A_sub : Finset (Option (↥B₀ ⊕ Fin r)) :=
          univ.filter fun u => match u with
            | none => True
            | some (Sum.inl _) => True
            | some (Sum.inr j) => j.val < k.val
        let S_sub : Finset V' := (A_sub.map ψ.symm.toEquiv.toEmbedding).map ⟨Subtype.val, val_injective⟩
        have hc_not_Ssub : c ∉ S_sub := by
          intro hm
          obtain ⟨y, hy, hyc⟩ := mem_map.mp hm
          obtain ⟨u, huA, huy⟩ := mem_map.mp hy
          have hyeq : y = ⟨c, hcS⟩ := Subtype.ext hyc
          have hu_eq : u = some (Sum.inr k) := by
            change ψ.symm u = y at huy
            have := congrArg ψ huy
            rw [ψ.apply_symm_apply, hyeq, hψc] at this
            exact this
          subst hu_eq
          simp [A_sub] at huA
        have hS_sub_conn : (T.induce (S_sub : Set V')).Connected := by
          let A_set : Set (Option (↥B₀ ⊕ Fin r)) := (A_sub : Set (Option (↥B₀ ⊕ Fin r)))
          have : Nonempty A_set := ⟨⟨none, by simp [A_set, A_sub]⟩⟩
          have hA_conn : (Q.induce A_set).Connected := by
            refine Connected.mk fun a b => ?_
            suffices h0 : ∀ z : A_set, (Q.induce A_set).Reachable ⟨none, mem_filter.mpr ⟨mem_univ _, trivial⟩⟩ z from
              (h0 a).symm.trans (h0 b)
            rintro ⟨u, hu⟩
            rcases u with _ | (b₀ | j)
            · exact Reachable.rfl
            · obtain ⟨w⟩ := hB0_conn ⟨c₀, Set.mem_insert c₀ _⟩ ⟨b₀.1, Set.mem_insert_of_mem c₀ b₀.2⟩
              let g : T₀.induce (insert c₀ (B₀ : Set U₀)) →g Q.induce A_set :=
                ⟨fun z => ⟨if hz : z.1 = c₀ then none else some (Sum.inl ⟨z.1, (mem_insert_iff.mp z.2).resolve_left hz⟩),
                  by split_ifs <;> exact mem_filter.mpr ⟨mem_univ _, trivial⟩⟩,
                 @fun z₁ z₂ hadj => by
                  by_cases h1 : z₁.1 = c₀ <;> by_cases h2 : z₂.1 = c₀
                  · exact False.elim (T₀.ne_of_adj hadj (h1.trans h2.symm))
                  · change Q.Adj _ _; simp only [dif_pos h1, dif_neg h2]; exact (congrArg (fun u => T₀.Adj u z₂.1) h1).mp hadj
                  · change Q.Adj _ _; simp only [dif_neg h1, dif_pos h2]; exact (congrArg (fun u => T₀.Adj u z₁.1) h2).mp hadj.symm
                  · change Q.Adj _ _; simp only [dif_neg h1, dif_neg h2]; exact hadj⟩
              have hb_ne : b₀.1 ≠ c₀ := fun h => hc0_not (h ▸ b₀.2)
              exact ⟨(w.map g).copy (Subtype.ext (by simp [g])) (Subtype.ext (by simp [g, hb_ne]))⟩
            · simp only [A_set, A_sub, mem_coe, mem_filter, mem_univ, true_and] at hu
              have hk0_pos : 0 < k.val := hkM.elim id fun hBM' => by omega
              obtain ⟨p, _, _, hsupp⟩ := pathG_walk_up j.val j.isLt
              have hp_mem : ∀ m ∈ p.support, some (Sum.inr m) ∈ A_set := fun m hm =>
                mem_coe.mpr (mem_filter.mpr ⟨mem_univ _, (hsupp m hm).trans_lt hu⟩)
              let q' : (Q.induce A_set).Walk
                  ⟨some (Sum.inr ⟨0, by omega⟩), mem_coe.mpr (mem_filter.mpr ⟨mem_univ _, hk0_pos⟩)⟩
                  ⟨some (Sum.inr j), mem_coe.mpr (mem_filter.mpr ⟨mem_univ _, hu⟩)⟩ :=
                (p.map ⟨fun m => some (Sum.inr m), @fun _ _ h => h⟩).induce A_set
                  (fun z hz => by
                    rw [Walk.support_map, List.mem_map] at hz
                    obtain ⟨m, hm, rfl⟩ := hz
                    exact hp_mem m hm) |>.copy rfl rfl
              have h0 : (Q.induce A_set).Adj
                  ⟨none, mem_filter.mpr ⟨mem_univ _, trivial⟩⟩
                  ⟨some (Sum.inr ⟨0, by omega⟩), mem_coe.mpr (mem_filter.mpr ⟨mem_univ _, hk0_pos⟩)⟩ :=
                by simp [Q, Q2]
              exact ⟨Walk.cons h0 q'⟩
          have : Nonempty (S_sub : Set V') := ⟨⟨(ψ.symm none).1, mem_map.mpr ⟨ψ.symm none, mem_map.mpr ⟨none, mem_filter.mpr ⟨mem_univ _, trivial⟩, rfl⟩, rfl⟩⟩⟩
          refine Connected.mk fun a b => ?_
          have ha_S : a.1 ∈ (S : Set V') := by
            obtain ⟨y, _, hy⟩ := mem_map.mp a.2; exact hy ▸ y.2
          have ha : ψ ⟨a.1, ha_S⟩ ∈ A_set := by
            obtain ⟨y, hy, hy_eq⟩ := mem_map.mp a.2
            obtain ⟨u, hu, huy⟩ := mem_map.mp hy
            change ψ.symm u = y at huy
            have h1 : ψ ⟨a.1, ha_S⟩ = u := by
              rw [show (⟨a.1, ha_S⟩ : (S : Set V')) = y from Subtype.ext hy_eq.symm, ← huy, ψ.apply_symm_apply]
            exact h1 ▸ hu
          have hb_S : b.1 ∈ (S : Set V') := by
            obtain ⟨y, _, hy⟩ := mem_map.mp b.2; exact hy ▸ y.2
          have hb : ψ ⟨b.1, hb_S⟩ ∈ A_set := by
            obtain ⟨y, hy, hy_eq⟩ := mem_map.mp b.2
            obtain ⟨u, hu, huy⟩ := mem_map.mp hy
            change ψ.symm u = y at huy
            have h1 : ψ ⟨b.1, hb_S⟩ = u := by
              rw [show (⟨b.1, hb_S⟩ : (S : Set V')) = y from Subtype.ext hy_eq.symm, ← huy, ψ.apply_symm_apply]
            exact h1 ▸ hu
          obtain ⟨w⟩ := hA_conn ⟨_, ha⟩ ⟨_, hb⟩
          let f : Q.induce A_set →g T.induce (S_sub : Set V') :=
            ⟨fun z => ⟨(ψ.symm z.1).1, mem_map.mpr ⟨ψ.symm z.1,
              mem_map.mpr ⟨z.1, z.2, rfl⟩, rfl⟩⟩,
             @fun z₁ z₂ hadj => (ψ.symm.map_rel_iff).mpr hadj⟩
          exact ⟨(w.map f).copy (by apply Subtype.ext; change (ψ.symm (ψ ⟨a.1, ha_S⟩)).1 = a.1; exact congrArg (fun z : (S : Set V') => z.1) (ψ.symm_apply_apply ⟨a.1, ha_S⟩))
            (by apply Subtype.ext; change (ψ.symm (ψ ⟨b.1, hb_S⟩)).1 = b.1; exact congrArg (fun z : (S : Set V') => z.1) (ψ.symm_apply_apply ⟨b.1, hb_S⟩))⟩
        have hA_card : M + 1 ≤ S_sub.card := by
          have hcard_eq : S_sub.card = A_sub.card := by
            rw [card_map, card_map]
          let eB : ↥B₀ ↪ Option (↥B₀ ⊕ Fin r) :=
            ⟨fun b => some (Sum.inl b), fun _ _ h => Sum.inl.inj (Option.some.inj h)⟩
          have hsub_A : insert (none : Option (↥B₀ ⊕ Fin r)) (B₀.attach.map eB) ⊆ A_sub := by
            intro u hu
            rcases mem_insert.mp hu with rfl | hb
            · exact mem_filter.mpr ⟨mem_univ _, trivial⟩
            · obtain ⟨b, _, rfl⟩ := mem_map.mp hb
              exact mem_filter.mpr ⟨mem_univ _, trivial⟩
          have h1 : B₀.card + 1 ≤ A_sub.card := by
            have hnot : (none : Option (↥B₀ ⊕ Fin r)) ∉ B₀.attach.map eB := by
              intro h; obtain ⟨b, _, hb⟩ := mem_map.mp h; change some (Sum.inl b) = none at hb; simp at hb
            have hc1 : (insert (none : Option (↥B₀ ⊕ Fin r)) (B₀.attach.map eB)).card = B₀.card + 1 := by
              rw [card_insert_of_notMem hnot, card_map, card_attach]
            exact hc1 ▸ card_le_card hsub_A
          rcases hkM with hk1 | hBM
          · -- k.val >= 1 so inr ⟨0, _⟩ ∈ A_sub too, disjoint from insert none (inl B₀)!
            have hinr0 : some (Sum.inr ⟨0, by omega⟩) ∈ A_sub :=
              mem_filter.mpr ⟨mem_univ _, hk1⟩
            have hnot2 : (some (Sum.inr ⟨0, by omega⟩) : Option (↥B₀ ⊕ Fin r)) ∉ insert (none : Option (↥B₀ ⊕ Fin r))
                (B₀.attach.map eB) := by
              intro h
              rcases mem_insert.mp h with h1a | h2a
              · simp at h1a
              · obtain ⟨b, _, hb⟩ := mem_map.mp h2a
                have hb' : (some (Sum.inl b) : Option (↥B₀ ⊕ Fin r)) = some (Sum.inr ⟨0, by omega⟩) := hb; simp at hb'
            have hsub2 := Finset.insert_subset_iff.mpr ⟨hinr0, hsub_A⟩
            have hc2 := card_le_card hsub2
            rw [card_insert_of_notMem hnot2, card_insert_of_notMem (by
              intro h; obtain ⟨b, _, hb⟩ := mem_map.mp h; change some (Sum.inl b) = none at hb; simp at hb),
              card_map, card_attach] at hc2
            omega
          · omega
        have hS_sub_ne : S_sub.Nonempty := card_pos.mp (by omega)
        obtain ⟨D, _, hD⟩ := subset_comp_of_connected T c S_sub hS_sub_ne hc_not_Ssub hS_sub_conn
        have := hmax D
        omega
      · push Not at hkM
        have hk0 : k.val = 0 := by omega
        rcases hforce with hBM | ⟨b, hb_mem, hb_dist⟩
        · exact False.elim (hkM.2 hBM)
        · -- Path from none to inl b inside insert c₀ B₀ has length >= r:
          have hk_eq : k = ⟨0, by omega⟩ := Fin.ext hk0
          obtain ⟨pb, hpb, hpblen⟩ := hT0.connected.exists_path_of_dist c₀ b
          have hB0_tree : (T₀.induce (insert c₀ (B₀ : Set U₀))).IsTree :=
            ⟨hB0_conn, hT0.isAcyclic.induce _⟩
          obtain ⟨pb_sub, hpb_sub, hpb_sub_len⟩ :=
            hB0_tree.connected.exists_path_of_dist ⟨c₀, Set.mem_insert c₀ _⟩ ⟨b, Set.mem_insert_of_mem c₀ hb_mem⟩
          rw [dist_induce_eq_of_isTree T₀ hT0 _ hB0_tree] at hpb_sub_len
          dsimp only at hpb_sub_len
          let gB : T₀.induce (insert c₀ (B₀ : Set U₀)) →g Q :=
            ⟨fun z => if hz : z.1 = c₀ then none else some (Sum.inl ⟨z.1, (mem_insert_iff.mp z.2).resolve_left hz⟩),
             @fun z₁ z₂ hadj => by
              by_cases h1 : z₁.1 = c₀ <;> by_cases h2 : z₂.1 = c₀
              · exact False.elim (T₀.ne_of_adj hadj (h1.trans h2.symm))
              · simp only [dif_pos h1, dif_neg h2]; exact (congrArg (fun u => T₀.Adj u z₂.1) h1).mp hadj
              · simp only [dif_neg h1, dif_pos h2]; exact (congrArg (fun u => T₀.Adj u z₁.1) h2).mp hadj.symm
              · simp only [dif_neg h1, dif_neg h2]; exact hadj⟩
          have hgB_inj : Injective gB := by
            intro z₁ z₂ heq
            by_cases h1 : z₁.1 = c₀ <;> by_cases h2 : z₂.1 = c₀
            · exact Subtype.ext (h1.trans h2.symm)
            · simp [gB, h1, h2] at heq
            · simp [gB, h1, h2] at heq
            · dsimp only [gB] at heq; simp only [RelHom.coeFn_mk, dif_neg h1, dif_neg h2] at heq
              exact Subtype.ext (congrArg (fun z : ↥B₀ => z.1) (Sum.inl.inj (Option.some.inj heq)))
          have hbne : b ≠ c₀ := fun h => hc0_not (h ▸ hb_mem)
          let qbQ : Q.Walk none (some (Sum.inl ⟨b, hb_mem⟩)) :=
            (pb_sub.map gB).copy (by simp [gB]) (by simp [gB, hbne])
          have hqbQ : qbQ.IsPath := (isPath_copy _ _ _).mpr (hpb_sub.map hgB_inj)
          have hnot_inr : some (Sum.inr k) ∉ qbQ.support := by
            intro hm
            have : some (Sum.inr k) ∈ (pb_sub.map gB).support := by simpa [qbQ, support_copy] using hm
            rw [Walk.support_map, List.mem_map] at this
            obtain ⟨z, _, hz⟩ := this
            by_cases hzc : z.1 = c₀ <;> simp [gB, hzc] at hz
          have hadj_k : Q.Adj (some (Sum.inr k)) none := by simp [Q, Q2, hk0]
          let full : Q.Walk (some (Sum.inr k)) (some (Sum.inl ⟨b, hb_mem⟩)) :=
            Walk.cons hadj_k qbQ
          have hfull : full.IsPath := (cons_isPath_iff hadj_k qbQ).mpr ⟨hqbQ, hnot_inr⟩
          have hle := h_no_long_path _ (full.copy hψc.symm rfl) ((isPath_copy _ _ _).mpr hfull)
          have hlen_full : full.length = 1 + pb_sub.length := by
            simp [full, qbQ, length_copy, length_map]; omega
          rw [length_copy, hlen_full, hpb_sub_len] at hle
          omega
private lemma Q3_center_forced {U₀ V' : Type} [Fintype U₀] [Fintype V']
    (T₀ : SimpleGraph U₀) (hT0 : T₀.IsTree) (c₀ : U₀) (B₀ : Finset U₀)
    (hc0_not : c₀ ∉ B₀)
    (hB0_conn : (T₀.induce (insert c₀ (B₀ : Set U₀))).Connected)
    (T : SimpleGraph V') (hT : T.IsTree) {r M : ℕ} (hr : 2 ≤ r)
    (c : V') (hecc : T.eccent c = r)
    (hmax : ∀ D : (T.induce {c}ᶜ).ConnectedComponent, card D.supp ≤ M)
    (hBM : B₀.card = M - 1) (hM_pos : 1 ≤ M)
    (S : Finset V') (ψ : T.induce (S : Set V') ≃g Q3 T₀ c₀ B₀ r) :
    ∃ hc : c ∈ S, ψ ⟨c, hc⟩ = none := by
  let Q := Q3 T₀ c₀ B₀ r
  have hQ_conn : Q.Connected := by
    refine Connected.mk fun a b => ?_
    suffices h0 : ∀ x : Option (↥B₀ ⊕ (Fin r ⊕ Fin r)), Q.Reachable none x from (h0 a).symm.trans (h0 b)
    rintro (_ | (x | (i | i)))
    · exact Reachable.rfl
    · obtain ⟨w⟩ := hB0_conn ⟨c₀, Set.mem_insert c₀ _⟩ ⟨x.1, Set.mem_insert_of_mem c₀ x.2⟩
      let g : T₀.induce (insert c₀ (B₀ : Set U₀)) →g Q :=
        ⟨fun z => if hz : z.1 = c₀ then none else some (Sum.inl ⟨z.1, (mem_insert_iff.mp z.2).resolve_left hz⟩),
         @fun z₁ z₂ hadj => by
          by_cases h1 : z₁.1 = c₀ <;> by_cases h2 : z₂.1 = c₀
          · exact False.elim (T₀.ne_of_adj hadj (h1.trans h2.symm))
          · simp only [dif_pos h1, dif_neg h2]; exact (congrArg (fun u => T₀.Adj u z₂.1) h1).mp hadj
          · simp only [dif_neg h1, dif_pos h2]; exact (congrArg (fun u => T₀.Adj u z₁.1) h2).mp hadj.symm
          · simp only [dif_neg h1, dif_neg h2]; exact hadj⟩
      have hx_ne : x.1 ≠ c₀ := fun h => hc0_not (h ▸ x.2)
      exact ⟨(w.map g).copy (by simp [g]) (by simp [g, hx_ne])⟩
    · obtain ⟨p, _, _⟩ := pathG_walk_up i.val i.isLt
      have h0 : Q.Adj none (some (Sum.inr (Sum.inl ⟨0, by omega⟩))) := rfl
      exact ⟨Walk.cons h0 (p.map ⟨fun j => some (Sum.inr (Sum.inl j)), @fun _ _ h => h⟩)⟩
    · obtain ⟨p, _, _⟩ := pathG_walk_up i.val i.isLt
      have h0 : Q.Adj none (some (Sum.inr (Sum.inr ⟨0, by omega⟩))) := rfl
      exact ⟨Walk.cons h0 (p.map ⟨fun j => some (Sum.inr (Sum.inr j)), @fun _ _ h => h⟩)⟩
  have : Nonempty (S : Set V') := ⟨ψ.symm none⟩
  have hS_conn : (T.induce (S : Set V')).Connected :=
    ⟨fun a b => ⟨((hQ_conn (ψ a) (ψ b)).some.map ψ.symm.toHom).copy (ψ.symm_apply_apply a) (ψ.symm_apply_apply b)⟩⟩
  have hS_card : S.card = B₀.card + 1 + r + r := by
    have hsc : S.card = card (S : Set V') :=
      (card_coe S).symm.trans
        (card_congr ⟨fun x => ⟨x.1, x.2⟩, fun x => ⟨x.1, x.2⟩, fun _ => rfl, fun _ => rfl⟩)
    rw [hsc, card_congr ψ.toEquiv, card_option, card_sum,
      card_sum, card_coe, card_fin]
    omega
  have hcS : c ∈ S := by
    by_contra hnc
    have hS_ne : S.Nonempty := by rw [← card_pos, hS_card]; omega
    obtain ⟨D, _, hDle⟩ := subset_comp_of_connected T c S hS_ne hnc hS_conn
    have := hmax D; omega
  refine ⟨hcS, ?_⟩
  by_contra hne_none
  have h_no_long_path : ∀ (u : Option (↥B₀ ⊕ (Fin r ⊕ Fin r))) (p : Q.Walk (ψ ⟨c, hcS⟩) u),
      p.IsPath → p.length ≤ r := by
    intro u p hp
    let g : T.induce (S : Set V') →g T := (Embedding.induce (S : Set V')).toHom
    let pT : T.Walk c (ψ.symm u).1 := ((p.map ψ.symm.toHom).map g).copy
      (congrArg Subtype.val (ψ.symm_apply_apply ⟨c, hcS⟩)) rfl
    have hpT : pT.IsPath :=
      (isPath_copy _ _ _).mpr ((hp.map ψ.symm.injective).map val_injective)
    have hlen : pT.length = p.length :=
      (length_copy _ _ _).trans (by rw [length_map, length_map])
    rw [isTree_dist_eq_length_of_isPath T hT pT hpT] at hlen
    have hle := dist_le_of_eccent T hT (u := (ψ.symm u).1) hecc
    omega
  obtain ⟨pr, hpr, hprlen, _⟩ := pathG_walk_up (r := r) (r - 1) (by omega)
  let p_tail : Q.Walk none (some (Sum.inr (Sum.inl ⟨r - 1, by omega⟩))) :=
    Walk.cons (by simp [Q, Q3] : Q.Adj none (some (Sum.inr (Sum.inl ⟨0, by omega⟩))))
      (pr.map ⟨fun j => some (Sum.inr (Sum.inl j)), @fun _ _ h => h⟩)
  have hp_tail_path : p_tail.IsPath := by
    rw [cons_isPath_iff]
    refine ⟨hpr.map (fun _ _ h => Sum.inl.inj (Sum.inr.inj (Option.some.inj h))), fun hm => ?_⟩
    rw [Walk.support_map, List.mem_map] at hm
    obtain ⟨j, _, hj⟩ := hm; simp at hj
  have hp_tail_len : p_tail.length = r := by simp [p_tail, hprlen]; omega
  cases hψc : ψ ⟨c, hcS⟩ with
  | none => exact hne_none hψc
  | some y =>
    cases y with
    | inl b =>
      obtain ⟨qb, hqb, _⟩ := (hB0_conn ⟨b.1, Set.mem_insert_of_mem c₀ b.2⟩
        ⟨c₀, Set.mem_insert c₀ _⟩).exists_path_of_dist
      let gB : T₀.induce (insert c₀ (B₀ : Set U₀)) →g Q :=
        ⟨fun z => if hz : z.1 = c₀ then none else some (Sum.inl ⟨z.1, (mem_insert_iff.mp z.2).resolve_left hz⟩),
         @fun z₁ z₂ hadj => by
          by_cases h1 : z₁.1 = c₀ <;> by_cases h2 : z₂.1 = c₀
          · exact False.elim (T₀.ne_of_adj hadj (h1.trans h2.symm))
          · simp only [dif_pos h1, dif_neg h2]; exact (congrArg (fun u => T₀.Adj u z₂.1) h1).mp hadj
          · simp only [dif_neg h1, dif_pos h2]; exact (congrArg (fun u => T₀.Adj u z₁.1) h2).mp hadj.symm
          · simp only [dif_neg h1, dif_neg h2]; exact hadj⟩
      have hgB_inj : Injective gB := by
        intro z₁ z₂ heq
        by_cases h1 : z₁.1 = c₀ <;> by_cases h2 : z₂.1 = c₀
        · exact Subtype.ext (h1.trans h2.symm)
        · simp [gB, h1, h2] at heq
        · simp [gB, h1, h2] at heq
        · dsimp only [gB] at heq; simp only [RelHom.coeFn_mk, dif_neg h1, dif_neg h2] at heq
          exact Subtype.ext (congrArg (fun z : ↥B₀ => z.1) (Sum.inl.inj (Option.some.inj heq)))
      have hbne : b.1 ≠ c₀ := fun h => hc0_not (h ▸ b.2)
      let qbQ : Q.Walk (some (Sum.inl b)) none := (qb.map gB).copy (by simp [gB, hbne]) (by simp [gB])
      have hqbQ : qbQ.IsPath := (isPath_copy _ _ _).mpr (hqb.map hgB_inj)
      have hqbQ_len : 1 ≤ qbQ.length := by cases qbQ; simp
      have hmeet : ∀ u ∈ qbQ.support, u ∈ p_tail.support.tail → u = none := by
        intro u huq hut
        have hu1 : u = none ∨ ∃ x, u = some (Sum.inl x) := by
          have : u ∈ (qb.map gB).support := by simpa [qbQ, support_copy] using huq
          rw [Walk.support_map, List.mem_map] at this; obtain ⟨z, _, rfl⟩ := this
          by_cases hz : z.1 = c₀
          · left; simp [gB, hz]
          · right; refine ⟨⟨z.1, (mem_insert_iff.mp z.2).resolve_left hz⟩, ?_⟩; simp [gB, hz]
        have hu2 : ∃ j, u = some (Sum.inr (Sum.inl j)) := by
          have : u ∈ (pr.map (⟨fun j => some (Sum.inr (Sum.inl j)), @fun _ _ h => h⟩ : pathG r →g Q)).support := by
            simpa [p_tail] using hut
          rw [Walk.support_map, List.mem_map] at this; obtain ⟨j, _, rfl⟩ := this; exact ⟨j, rfl⟩
        rcases hu1 with rfl | ⟨_, h1⟩ <;> obtain ⟨_, h2⟩ := hu2
        · rfl
        · have h := h1.symm.trans h2; simp at h
      have hle := h_no_long_path _ ((qbQ.append p_tail).copy hψc.symm rfl)
        ((isPath_copy _ _ _).mpr (isPath_append_of_first_meet hqbQ hp_tail_path hmeet))
      rw [length_copy, length_append, hp_tail_len] at hle
      omega
    | inr lr =>
      let keepRight : Bool := match lr with | Sum.inl _ => true | Sum.inr _ => false
      let A_sub : Finset (Option (↥B₀ ⊕ (Fin r ⊕ Fin r))) :=
        univ.filter fun u => match u with
          | none => True
          | some (Sum.inl _) => True
          | some (Sum.inr (Sum.inl _)) => !keepRight
          | some (Sum.inr (Sum.inr _)) => keepRight
      let S_sub : Finset V' := (A_sub.map ψ.symm.toEquiv.toEmbedding).map ⟨Subtype.val, val_injective⟩
      have hlr_not : some (Sum.inr lr) ∉ A_sub := by
        cases lr <;> simp [A_sub, keepRight]
      have hc_not : c ∉ S_sub := by
        intro hm
        obtain ⟨y, hy, hyc⟩ := mem_map.mp hm
        obtain ⟨u, huA, huy⟩ := mem_map.mp hy
        have hu_eq : u = some (Sum.inr lr) := by
          change ψ.symm u = y at huy
          have hyeq : y = ⟨c, hcS⟩ := Subtype.ext hyc
          have := congrArg ψ huy
          rw [ψ.apply_symm_apply, hyeq, hψc] at this
          exact this
        exact hlr_not (hu_eq ▸ huA)
      have hS_conn : (T.induce (S_sub : Set V')).Connected := by
        let A_set : Set (Option (↥B₀ ⊕ (Fin r ⊕ Fin r))) := (A_sub : Set (Option (↥B₀ ⊕ (Fin r ⊕ Fin r))))
        have : Nonempty A_set := ⟨⟨none, by simp [A_set, A_sub]⟩⟩
        have hA_conn : (Q.induce A_set).Connected := by
          refine Connected.mk fun a b => ?_
          suffices h0 : ∀ z : A_set, (Q.induce A_set).Reachable
              ⟨none, mem_filter.mpr ⟨mem_univ _, trivial⟩⟩ z from (h0 a).symm.trans (h0 b)
          rintro ⟨u, hu⟩
          rcases u with _ | (b₀ | (j | j))
          · exact Reachable.rfl
          · obtain ⟨w⟩ := hB0_conn ⟨c₀, Set.mem_insert c₀ _⟩ ⟨b₀.1, Set.mem_insert_of_mem c₀ b₀.2⟩
            let g : T₀.induce (insert c₀ (B₀ : Set U₀)) →g Q.induce A_set :=
              ⟨fun z => ⟨if hz : z.1 = c₀ then none else some (Sum.inl ⟨z.1, (mem_insert_iff.mp z.2).resolve_left hz⟩),
                by split_ifs <;> exact mem_filter.mpr ⟨mem_univ _, trivial⟩⟩,
               @fun z₁ z₂ hadj => by
                by_cases h1 : z₁.1 = c₀ <;> by_cases h2 : z₂.1 = c₀
                · exact False.elim (T₀.ne_of_adj hadj (h1.trans h2.symm))
                · change Q.Adj _ _; simp only [dif_pos h1, dif_neg h2]; exact (congrArg (fun u => T₀.Adj u z₂.1) h1).mp hadj
                · change Q.Adj _ _; simp only [dif_neg h1, dif_pos h2]; exact (congrArg (fun u => T₀.Adj u z₁.1) h2).mp hadj.symm
                · change Q.Adj _ _; simp only [dif_neg h1, dif_neg h2]; exact hadj⟩
            have hbne : b₀.1 ≠ c₀ := fun h => hc0_not (h ▸ b₀.2)
            exact ⟨(w.map g).copy (Subtype.ext (by simp [g])) (Subtype.ext (by simp [g, hbne]))⟩
          · have hu' := hu; simp only [A_set, A_sub, mem_coe, mem_filter, mem_univ, true_and] at hu'
            obtain ⟨p, _, _, _⟩ := pathG_walk_up j.val j.isLt
            have hmem : ∀ m : Fin r, some (Sum.inr (Sum.inl m)) ∈ A_set := fun m =>
              mem_coe.mpr (mem_filter.mpr ⟨mem_univ _, by simpa [A_set, A_sub] using hu'⟩)
            let q' : (Q.induce A_set).Walk ⟨some (Sum.inr (Sum.inl ⟨0, by omega⟩)), hmem _⟩ ⟨_, hu⟩ :=
              (p.map ⟨fun m => some (Sum.inr (Sum.inl m)), @fun _ _ h => h⟩).induce A_set
                (fun z hz => by rw [Walk.support_map, List.mem_map] at hz; obtain ⟨m, _, rfl⟩ := hz; exact hmem m) |>.copy rfl rfl
            exact ⟨Walk.cons (by simp [Q, Q3] : (Q.induce A_set).Adj ⟨none, _⟩ ⟨some (Sum.inr (Sum.inl ⟨0, by omega⟩)), hmem _⟩) q'⟩
          · have hu' := hu; simp only [A_set, A_sub, mem_coe, mem_filter, mem_univ, true_and] at hu'
            obtain ⟨p, _, _, _⟩ := pathG_walk_up j.val j.isLt
            have hmem : ∀ m : Fin r, some (Sum.inr (Sum.inr m)) ∈ A_set := fun m =>
              mem_coe.mpr (mem_filter.mpr ⟨mem_univ _, by simpa [A_set, A_sub] using hu'⟩)
            let q' : (Q.induce A_set).Walk ⟨some (Sum.inr (Sum.inr ⟨0, by omega⟩)), hmem _⟩ ⟨_, hu⟩ :=
              (p.map ⟨fun m => some (Sum.inr (Sum.inr m)), @fun _ _ h => h⟩).induce A_set
                (fun z hz => by rw [Walk.support_map, List.mem_map] at hz; obtain ⟨m, _, rfl⟩ := hz; exact hmem m) |>.copy rfl rfl
            exact ⟨Walk.cons (by simp [Q, Q3] : (Q.induce A_set).Adj ⟨none, _⟩ ⟨some (Sum.inr (Sum.inr ⟨0, by omega⟩)), hmem _⟩) q'⟩
        have : Nonempty (S_sub : Set V') := ⟨⟨(ψ.symm none).1, mem_map.mpr ⟨ψ.symm none, mem_map.mpr ⟨none, mem_filter.mpr ⟨mem_univ _, trivial⟩, rfl⟩, rfl⟩⟩⟩
        refine Connected.mk fun a b => ?_
        have ha_S : a.1 ∈ (S : Set V') := by
          obtain ⟨y, _, hy⟩ := mem_map.mp a.2; exact hy ▸ y.2
        have ha : ψ ⟨a.1, ha_S⟩ ∈ A_set := by
          obtain ⟨y, hy, hy_eq⟩ := mem_map.mp a.2
          obtain ⟨u, hu, huy⟩ := mem_map.mp hy
          change ψ.symm u = y at huy
          have h1 : ψ ⟨a.1, ha_S⟩ = u := by
            rw [show (⟨a.1, ha_S⟩ : (S : Set V')) = y from Subtype.ext hy_eq.symm, ← huy, ψ.apply_symm_apply]
          exact h1 ▸ hu
        have hb_S : b.1 ∈ (S : Set V') := by
          obtain ⟨y, _, hy⟩ := mem_map.mp b.2; exact hy ▸ y.2
        have hb : ψ ⟨b.1, hb_S⟩ ∈ A_set := by
          obtain ⟨y, hy, hy_eq⟩ := mem_map.mp b.2
          obtain ⟨u, hu, huy⟩ := mem_map.mp hy
          change ψ.symm u = y at huy
          have h1 : ψ ⟨b.1, hb_S⟩ = u := by
            rw [show (⟨b.1, hb_S⟩ : (S : Set V')) = y from Subtype.ext hy_eq.symm, ← huy, ψ.apply_symm_apply]
          exact h1 ▸ hu
        obtain ⟨w⟩ := hA_conn ⟨_, ha⟩ ⟨_, hb⟩
        let f : Q.induce A_set →g T.induce (S_sub : Set V') :=
          ⟨fun z => ⟨(ψ.symm z.1).1, mem_map.mpr ⟨ψ.symm z.1, mem_map.mpr ⟨z.1, z.2, rfl⟩, rfl⟩⟩,
           @fun _ _ h => (ψ.symm.map_rel_iff).mpr h⟩
        exact ⟨(w.map f).copy (by apply Subtype.ext; change (ψ.symm (ψ ⟨a.1, ha_S⟩)).1 = a.1; exact congrArg (fun z : (S : Set V') => z.1) (ψ.symm_apply_apply ⟨a.1, ha_S⟩))
          (by apply Subtype.ext; change (ψ.symm (ψ ⟨b.1, hb_S⟩)).1 = b.1; exact congrArg (fun z : (S : Set V') => z.1) (ψ.symm_apply_apply ⟨b.1, hb_S⟩))⟩
      have hS_card : M + r ≤ S_sub.card := by
        have hc : S_sub.card = A_sub.card := by rw [card_map, card_map]
        have hdisj : A_sub.card = 1 + B₀.card + r := by
          let eB : ↥B₀ ↪ Option (↥B₀ ⊕ (Fin r ⊕ Fin r)) :=
            ⟨fun b => some (Sum.inl b), fun _ _ h => Sum.inl.inj (Option.some.inj h)⟩
          let eR : Fin r ↪ Option (↥B₀ ⊕ (Fin r ⊕ Fin r)) :=
            ⟨fun j => some (Sum.inr (if keepRight then Sum.inr j else Sum.inl j)), fun j₁ j₂ h => by
              have h1 := Sum.inr.inj (Option.some.inj h)
              by_cases hkr : keepRight
              · simp only [if_pos hkr] at h1; exact Sum.inr.inj h1
              · simp only [if_neg hkr] at h1; exact Sum.inl.inj h1⟩
          have heB : ∀ x, eB x = some (Sum.inl x) := fun _ => rfl
          have heR : ∀ j, eR j = some (Sum.inr (if keepRight then Sum.inr j else Sum.inl j)) := fun _ => rfl
          have hset : A_sub = insert none ((B₀.attach.map eB) ∪ (univ.map eR)) := by
            ext u
            rw [mem_insert, mem_union, mem_map, mem_map]
            rcases u with _ | (b | (j | j))
            · simp [A_sub, heB, heR]
            · simp [A_sub, heB, heR]
            · by_cases hkr : keepRight <;> simp [A_sub, heB, heR, hkr]
            · by_cases hkr : keepRight <;> simp [A_sub, heB, heR, hkr]
          rw [hset, card_insert_of_notMem (by
            simp only [mem_union, mem_map, mem_attach, true_and, mem_univ]
            rintro (⟨_, hb⟩ | ⟨_, hb⟩) <;> [rw [heB] at hb; rw [heR] at hb] <;> cases hb),
            Finset.card_union_of_disjoint (Finset.disjoint_left.mpr fun u hu1 hu2 => by
              obtain ⟨_, _, rfl⟩ := mem_map.mp hu1
              obtain ⟨_, _, hu2'⟩ := mem_map.mp hu2
              rw [heB, heR] at hu2'; simp at hu2'),
            card_map, card_attach, card_map, card_univ, card_fin]
          omega
        omega
      have hS_ne : S_sub.Nonempty := card_pos.mp (by omega)
      obtain ⟨D, _, hD⟩ := subset_comp_of_connected T c S_sub hS_ne hc_not hS_conn
      have := hmax D; omega
private lemma path2r1_center_forced {V' : Type} [Fintype V']
    (T : SimpleGraph V') (hT : T.IsTree) {r : ℕ} (hr : 2 ≤ r)
    (c : V') (hecc : T.eccent c = r)
    (hmax : ∀ D : (T.induce {c}ᶜ).ConnectedComponent, card D.supp ≤ r + 1)
    (S : Finset V') (ψ : T.induce (S : Set V') ≃g pathG (2 * r + 1)) :
    ∃ hc : c ∈ S, (ψ ⟨c, hc⟩).val = r := by
  have hQ_conn : (pathG (2 * r + 1)).Connected := by
    refine Connected.mk fun a b => ?_
    suffices h0 : ∀ x : Fin (2 * r + 1), (pathG (2 * r + 1)).Reachable ⟨0, by omega⟩ x from
      (h0 a).symm.trans (h0 b)
    intro x
    obtain ⟨p, _, _⟩ := pathG_walk_up x.val x.isLt
    exact ⟨p⟩
  have : Nonempty (S : Set V') := ⟨ψ.symm ⟨0, by omega⟩⟩
  have hS_conn : (T.induce (S : Set V')).Connected :=
    ⟨fun a b => ⟨((hQ_conn (ψ a) (ψ b)).some.map ψ.symm.toHom).copy (ψ.symm_apply_apply a) (ψ.symm_apply_apply b)⟩⟩
  have hS_card : S.card = 2 * r + 1 := by
    have hsc : S.card = card (S : Set V') :=
      (card_coe S).symm.trans
        (card_congr ⟨fun x => ⟨x.1, x.2⟩, fun x => ⟨x.1, x.2⟩, fun _ => rfl, fun _ => rfl⟩)
    rw [hsc, card_congr ψ.toEquiv, card_fin]
  have hcS : c ∈ S := by
    by_contra hnc
    have hS_ne : S.Nonempty := by rw [← card_pos, hS_card]; omega
    obtain ⟨D, _, hD⟩ := subset_comp_of_connected T c S hS_ne hnc hS_conn
    have := hmax D; omega
  refine ⟨hcS, ?_⟩
  by_contra hne
  have h_no_long : ∀ (u : Fin (2 * r + 1)) (p : (pathG (2 * r + 1)).Walk (ψ ⟨c, hcS⟩) u),
      p.IsPath → p.length ≤ r := by
    intro u p hp
    let g : T.induce (S : Set V') →g T := (Embedding.induce (S : Set V')).toHom
    let pT : T.Walk c (ψ.symm u).1 := ((p.map ψ.symm.toHom).map g).copy
      (congrArg Subtype.val (ψ.symm_apply_apply ⟨c, hcS⟩)) rfl
    have hpT : pT.IsPath :=
      (isPath_copy _ _ _).mpr ((hp.map ψ.symm.injective).map val_injective)
    have hlen : pT.length = p.length :=
      (length_copy _ _ _).trans (by rw [length_map, length_map])
    rw [isTree_dist_eq_length_of_isPath T hT pT hpT] at hlen
    have hle := dist_le_of_eccent T hT (u := (ψ.symm u).1) hecc
    omega
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨p, hp, hplen⟩ := pathG_walk_down (ψ ⟨c, hcS⟩) ⟨2 * r, by omega⟩ (by simp; omega)
    have := h_no_long _ p hp
    simp only [hplen] at this
    omega
  · obtain ⟨p, hp, hplen⟩ := pathG_walk_down ⟨0, by omega⟩ (ψ ⟨c, hcS⟩) (by simp)
    have := h_no_long _ p.reverse hp.reverse
    simp only [length_reverse, hplen] at this
    omega
private noncomputable def pathTail {V' : Type} [Fintype V']
    (T : SimpleGraph V') (hT : T.IsTree) (c y : V') : Finset V' :=
  (hT.connected.exists_path_of_dist c y).choose.support.toFinset.erase c
private lemma pathTail_spec {V' : Type} [Fintype V']
    (T : SimpleGraph V') (hT : T.IsTree) {r : ℕ} (hr : 2 ≤ r) (c y : V')
    (hyd : T.dist c y = r) :
    let K := pathTail T hT c y
    have hyc : y ≠ c := fun h => by rw [← h, dist_self] at hyd; omega
    let D := (T.induce {c}ᶜ).connectedComponentMk ⟨y, hyc⟩
    c ∉ K ∧ y ∈ K ∧ K.card = r ∧ K ⊆ compSet T c D ∧
    (∀ z ∈ K, T.dist c z ≤ r ∧ (T.dist c z = r ↔ z = y)) ∧
    (∃ (φ : T.induce (insert c (K : Set V')) ≃g pathG (r + 1)),
      φ ⟨c, Set.mem_insert _ _⟩ = ⟨0, Nat.zero_lt_succ r⟩ ∧
      φ ⟨y, Set.mem_insert_of_mem c (by
        have : y ∈ K := by
          dsimp only [K, pathTail]
          rw [mem_erase, List.mem_toFinset]
          exact ⟨hyc, Walk.end_mem_support _⟩
        exact this)⟩ = ⟨r, Nat.lt_succ_self r⟩) := by
  intro K hyc D
  let p := (hT.connected.exists_path_of_dist c y).choose
  have hp : p.IsPath := (hT.connected.exists_path_of_dist c y).choose_spec.1
  have hplen : p.length = r := (hT.connected.exists_path_of_dist c y).choose_spec.2.trans hyd
  have hc_in : c ∈ p.support.toFinset := List.mem_toFinset.mpr p.start_mem_support
  have hy_in : y ∈ K := mem_erase.mpr ⟨hyc, List.mem_toFinset.mpr p.end_mem_support⟩
  have hK_card : K.card = r := by
    change (p.support.toFinset.erase c).card = r
    rw [card_erase_of_mem hc_in, List.toFinset_card_of_nodup hp.support_nodup, p.length_support, hplen]
    omega
  have hK_sub : K ⊆ compSet T c D := by
    intro z hz
    dsimp only [K, pathTail] at hz
    rw [mem_erase, List.mem_toFinset] at hz
    exact mem_compSet_of_walk_from_c T c D ((mem_compSet_iff T c D y).mpr ⟨hyc, rfl⟩) hp hz.2 hz.1
  have hK_dist : ∀ z ∈ K, T.dist c z ≤ r ∧ (T.dist c z = r ↔ z = y) := by
    intro z hz
    dsimp only [K, pathTail] at hz
    rw [mem_erase, List.mem_toFinset] at hz
    obtain ⟨q1, q2, hq1, hq2, hpeq⟩ := hp.mem_support_iff_exists_append.mp hz.2
    have hq1_len : q1.length = T.dist c z := isTree_dist_eq_length_of_isPath T hT q1 hq1
    have hsum := congrArg Walk.length hpeq
    rw [length_append, hplen] at hsum
    refine ⟨by omega, ⟨fun hdz => ?_, fun h => h ▸ hyd⟩⟩
    have hq2_len : q2.length = 0 := by omega
    cases q2 with
    | nil => rfl
    | cons _ _ => simp at hq2_len
  have hins : (insert c (K : Set V')) = (p.support.toFinset : Set V') := by
    ext z
    simp only [K, pathTail, mem_insert_iff, mem_coe, mem_erase, List.mem_toFinset]
    constructor
    · rintro (rfl | ⟨_, hz⟩)
      · exact p.start_mem_support
      · exact hz
    · intro hz
      by_cases hzc : z = c
      · exact Or.inl hzc
      · exact Or.inr ⟨hzc, hz⟩
  obtain ⟨φp, hφp0, hφpr⟩ := induce_support_iso_pathG_rooted T hT p hp
  have h_iso : ∃ (φ : T.induce (insert c (K : Set V')) ≃g pathG (r + 1)),
      φ ⟨c, Set.mem_insert _ _⟩ = ⟨0, Nat.zero_lt_succ r⟩ ∧
      φ ⟨y, Set.mem_insert_of_mem c hy_in⟩ = ⟨r, Nat.lt_succ_self r⟩ := by
    refine ⟨⟨⟨fun x =>
        ⟨(φp ⟨x.1, by rw [← hins]; exact x.2⟩).val, by
          have := (φp ⟨x.1, by rw [← hins]; exact x.2⟩).isLt; omega⟩,
      fun i =>
        ⟨(φp.symm ⟨i.val, by omega⟩).1, by rw [hins]; exact (φp.symm ⟨i.val, by omega⟩).2⟩,
      fun x => Subtype.ext (by
        dsimp only
        have hx' : (⟨(φp ⟨x.1, by rw [← hins]; exact x.2⟩).val, by omega⟩ : Fin (p.length + 1)) =
            φp ⟨x.1, by rw [← hins]; exact x.2⟩ := Fin.ext rfl
        exact congrArg Subtype.val ((congrArg φp.symm hx').trans (φp.left_inv _))),
      fun i => Fin.ext (by
        dsimp only
        have hi' : (⟨(φp.symm ⟨i.val, by omega⟩).1, (φp.symm ⟨i.val, by omega⟩).2⟩ :
            ↥(p.support.toFinset : Set V')) = φp.symm ⟨i.val, by omega⟩ := Subtype.ext rfl
        exact congrArg Fin.val ((congrArg φp hi').trans (φp.right_inv _)))⟩,
      @fun a b => (φp.map_rel_iff (a := ⟨a.1, by rw [← hins]; exact a.2⟩)
        (b := ⟨b.1, by rw [← hins]; exact b.2⟩))⟩, ?_, ?_⟩
    · apply Fin.ext; change (φp ⟨c, _⟩).val = 0; exact congrArg Fin.val hφp0
    · apply Fin.ext; change (φp ⟨y, _⟩).val = r; exact (congrArg Fin.val hφpr).trans hplen
  exact ⟨Finset.notMem_erase _ _, hy_in, hK_card, hK_sub, hK_dist, h_iso⟩
private lemma pathTail_eq_of_iso {V' : Type} [Fintype V']
    (T : SimpleGraph V') (hT : T.IsTree) {r : ℕ} (hr : 2 ≤ r) (c y : V')
    (hyd : T.dist c y = r) (K : Finset V') (hcK : c ∉ K) (hK_card : K.card = r)
    (ψ : T.induce (insert c (K : Set V')) ≃g pathG (r + 1))
    (hψ0 : ψ ⟨c, Set.mem_insert _ _⟩ = ⟨0, Nat.zero_lt_succ r⟩)
    (hψr : ∃ hy : y ∈ K, ψ ⟨y, Set.mem_insert_of_mem c hy⟩ = ⟨r, Nat.lt_succ_self r⟩) :
    K = pathTail T hT c y := by
  obtain ⟨hyK, hψr_eq⟩ := hψr
  obtain ⟨w_path, hw_path, hw_len, _⟩ := pathG_walk_up (r := r + 1) r (Nat.lt_succ_self r)
  let g : T.induce (insert c (K : Set V')) →g T := (Embedding.induce _).toHom
  let wT : T.Walk c y := ((w_path.map ψ.symm.toHom).map g).copy
    (by
      have h1 : ψ.symm ⟨0, Nat.zero_lt_succ r⟩ = ⟨c, Set.mem_insert _ _⟩ :=
        ψ.symm_apply_eq.mpr hψ0.symm
      exact congrArg Subtype.val h1)
    (by
      have h1 : ψ.symm ⟨r, Nat.lt_succ_self r⟩ = ⟨y, Set.mem_insert_of_mem c hyK⟩ :=
        ψ.symm_apply_eq.mpr hψr_eq.symm
      exact congrArg Subtype.val h1)
  have hwT_path : wT.IsPath :=
    (isPath_copy _ _ _).mpr ((hw_path.map ψ.symm.injective).map val_injective)
  let p := (hT.connected.exists_path_of_dist c y).choose
  have hp := (hT.connected.exists_path_of_dist c y).choose_spec.1
  have hw_eq : wT = p := isTree_path_eq T hT hwT_path hp
  have hsub : pathTail T hT c y ⊆ K := by
    intro z hz
    dsimp only [pathTail] at hz
    rw [mem_erase, List.mem_toFinset] at hz
    change z ≠ c ∧ z ∈ p.support at hz
    rw [← hw_eq] at hz
    have hm : z ∈ ((w_path.map ψ.symm.toHom).map g).support := by
      rw [← support_copy ((w_path.map ψ.symm.toHom).map g)
        (congrArg Subtype.val (ψ.symm_apply_eq.mpr hψ0.symm))
        (congrArg Subtype.val (ψ.symm_apply_eq.mpr hψr_eq.symm))]
      exact hz.2
    rw [Walk.support_map, List.mem_map] at hm
    obtain ⟨u, _, rfl⟩ := hm
    rcases u.2 with hc_eq | hzK
    · exact False.elim (hz.1 hc_eq)
    · exact hzK
  have hsp := pathTail_spec T hT hr c y hyd
  exact (eq_of_subset_of_card_le hsub (by rw [hK_card, hsp.2.2.1])).symm
private lemma compSet_root_adj {V' : Type} [Fintype V'] (T : SimpleGraph V') (hT : T.IsTree)
    (c : V') (D : (T.induce {c}ᶜ).ConnectedComponent) {x : V'} (hx : x ∈ compSet T c D)
    (hadj : T.Adj c x) :
    x = (existsUnique_root_of_component T hT c D).choose.1 := by
  obtain ⟨h1, h2⟩ := (mem_compSet_iff T c D x).mp hx
  exact congrArg Subtype.val ((existsUnique_root_of_component T hT c D).choose_spec.2 ⟨x, h1⟩ ⟨h2, hadj⟩)
private lemma Q2_induce_union_iso {U₀ V' : Type} [Fintype U₀] [Fintype V']
    (T₀ : SimpleGraph U₀) (c₀ : U₀) (B₀ : Finset U₀) (hc0_not : c₀ ∉ B₀)
    (T : SimpleGraph V') (hT : T.IsTree) {r : ℕ} (hr : 2 ≤ r) (c : V')
    (D : (T.induce {c}ᶜ).ConnectedComponent)
    {R : Finset V'} (hR_sub : R ⊆ compSet T c D) (hcR : c ∉ R)
    (hR_iso : RootedIso T c (insert c (R : Set V')) T₀ c₀ (insert c₀ (B₀ : Set U₀)))
    {y : V'} (hy_not : y ∉ compSet T c D) (hyd : T.dist c y = r) :
    Nonempty (T.induce (insert c (R ∪ pathTail T hT c y : Set V')) ≃g Q2 T₀ c₀ B₀ r) := by
  obtain ⟨h1R, h1B, φR, hφRc⟩ := hR_iso
  have hsp := pathTail_spec T hT hr c y hyd
  let K := pathTail T hT c y
  have hyc : y ≠ c := fun h => by rw [← h, dist_self] at hyd; omega
  let Dy := (T.induce {c}ᶜ).connectedComponentMk ⟨y, hyc⟩
  have hDDy : D ≠ Dy := fun h => hy_not (h ▸ (mem_compSet_iff T c Dy y).mpr ⟨hyc, rfl⟩)
  have hK_sub : K ⊆ compSet T c Dy := hsp.2.2.2.1
  have hdisj_RK : Disjoint R K :=
    (compSet_disjoint T c hDDy).mono hR_sub hK_sub
  have hcK : c ∉ K := hsp.1
  obtain ⟨φy, hφyc, _⟩ := hsp.2.2.2.2.2
  have hφR_B0 : ∀ (x : V') (hx : x ∈ R), (φR ⟨x, Set.mem_insert_of_mem c hx⟩).1 ∈ B₀ := by
    intro x hx
    have hmem := (φR ⟨x, Set.mem_insert_of_mem c hx⟩).2
    rcases mem_insert_iff.mp hmem with hceq | hxB
    · have hne : (⟨x, Set.mem_insert_of_mem c hx⟩ : ↥(insert c (R : Set V'))) ≠ ⟨c, h1R⟩ := fun h => by
        have heqv : x = c := congrArg Subtype.val h
        exact hcR (heqv ▸ hx)
      exact False.elim (hne (φR.injective (Subtype.ext (hceq.trans (congrArg Subtype.val hφRc).symm))))
    · exact hxB
  have hφR_symm_R : ∀ (b : ↥B₀), (φR.symm ⟨b.1, Set.mem_insert_of_mem c₀ b.2⟩).1 ∈ R := by
    intro b
    have hne : (⟨b.1, Set.mem_insert_of_mem c₀ b.2⟩ : ↥(insert c₀ (B₀ : Set U₀))) ≠ ⟨c₀, h1B⟩ := fun h => by
      have heqv : b.1 = c₀ := congrArg Subtype.val h
      exact hc0_not (heqv ▸ b.2)
    have hmem := (φR.symm ⟨b.1, Set.mem_insert_of_mem c₀ b.2⟩).2
    rcases mem_insert_iff.mp hmem with hceq | hxR
    · exact False.elim (hne (φR.symm.injective (Subtype.ext hceq |>.trans (φR.symm_apply_eq.mpr hφRc.symm).symm)))
    · exact hxR
  have hφy_pos : ∀ (z : V') (hz : z ∈ K), 0 < (φy ⟨z, Set.mem_insert_of_mem c hz⟩).val := by
    intro z hz
    by_contra h0
    have heqz : (φy ⟨z, Set.mem_insert_of_mem c hz⟩) = ⟨0, Nat.zero_lt_succ r⟩ := Fin.ext (Nat.eq_zero_of_not_pos h0)
    have hinj := φy.injective (heqz.trans hφyc.symm)
    have heqv : z = c := congrArg Subtype.val hinj
    exact hcK (heqv ▸ hz)
  have hφy_symm_K : ∀ (i : Fin r), (φy.symm ⟨i.val + 1, by omega⟩).1 ∈ K := by
    intro i
    have hne : (⟨i.val + 1, by omega⟩ : Fin (r + 1)) ≠ ⟨0, Nat.zero_lt_succ r⟩ :=
      fun h => by have hv := congrArg Fin.val h; dsimp at hv; omega
    have hmem := (φy.symm ⟨i.val + 1, by omega⟩).2
    rcases mem_insert_iff.mp hmem with hceq | hzK
    · have h1 : φy.symm ⟨i.val + 1, by omega⟩ = ⟨c, Set.mem_insert _ _⟩ := Subtype.ext hceq
      have h2 := congrArg φy h1
      rw [φy.apply_symm_apply, hφyc] at h2
      exact False.elim (hne h2)
    · exact hzK
  let S := insert c (R ∪ K)
  let toF : ↥(S : Set V') → Option (↥B₀ ⊕ Fin r) := fun x =>
    if hx : x.1 = c then none
    else if hxR : x.1 ∈ R then some (Sum.inl ⟨(φR ⟨x.1, Set.mem_insert_of_mem c hxR⟩).1, hφR_B0 x.1 hxR⟩)
    else
      have hxK : x.1 ∈ K := by
        rcases mem_insert.mp x.2 with h1 | h1
        · exact False.elim (hx h1)
        · exact (mem_union.mp h1).resolve_left hxR
      some (Sum.inr ⟨(φy ⟨x.1, Set.mem_insert_of_mem c hxK⟩).val - 1, by
        have := (φy ⟨x.1, Set.mem_insert_of_mem c hxK⟩).isLt; omega⟩)
  let invF : Option (↥B₀ ⊕ Fin r) → (S : Set V') := fun u =>
    match u with
    | none => ⟨c, mem_insert_self c _⟩
    | some (Sum.inl b) => ⟨(φR.symm ⟨b.1, Set.mem_insert_of_mem c₀ b.2⟩).1,
        mem_insert_of_mem (mem_union_left K (hφR_symm_R b))⟩
    | some (Sum.inr i) => ⟨(φy.symm ⟨i.val + 1, by omega⟩).1,
        mem_insert_of_mem (mem_union_right R (hφy_symm_K i))⟩
  have hleft : LeftInverse invF toF := by
    intro x
    apply Subtype.ext
    dsimp only [toF]
    by_cases hxc : x.1 = c
    · simp only [dif_pos hxc, invF]; exact hxc.symm
    · simp only [dif_neg hxc]
      by_cases hxR : x.1 ∈ R
      · simp only [dif_pos hxR, invF, coe_eta]
        exact congrArg Subtype.val (φR.left_inv ⟨x.1, Set.mem_insert_of_mem c hxR⟩)
      · simp only [dif_neg hxR, invF]
        have hxK : x.1 ∈ K := (mem_union.mp ((mem_insert.mp x.2).resolve_left hxc)).resolve_left hxR
        have hpos := hφy_pos x.1 hxK
        have hlt := (φy ⟨x.1, Set.mem_insert_of_mem c hxK⟩).isLt
        have hfin : (⟨(φy ⟨x.1, Set.mem_insert_of_mem c hxK⟩).val - 1 + 1, by omega⟩ : Fin (r + 1)) =
            φy ⟨x.1, Set.mem_insert_of_mem c hxK⟩ := Fin.ext (by dsimp; omega)
        rw [hfin]
        exact congrArg Subtype.val (φy.left_inv _)
  have hright : RightInverse invF toF := by
    intro u
    rcases u with _ | (b | i)
    · simp [invF, toF]
    · have hbR := hφR_symm_R b
      have hne : (φR.symm ⟨b.1, Set.mem_insert_of_mem c₀ b.2⟩).1 ≠ c := fun h => hcR (h ▸ hbR)
      dsimp only [invF, toF]
      rw [dif_neg hne, dif_pos hbR]
      exact congrArg (fun z : ↥B₀ => some (Sum.inl z)) (Subtype.ext (by
        have h1 : φR ⟨(φR.symm ⟨b.1, Set.mem_insert_of_mem c₀ b.2⟩).1, Set.mem_insert_of_mem c hbR⟩ =
            ⟨b.1, Set.mem_insert_of_mem c₀ b.2⟩ :=
          (congrArg φR (Subtype.ext rfl)).trans (φR.right_inv ⟨b.1, Set.mem_insert_of_mem c₀ b.2⟩)
        exact congrArg (fun z : ↥(insert c₀ (B₀ : Set U₀)) => z.1) h1))
    · have hiK := hφy_symm_K i
      have hne : (φy.symm ⟨i.val + 1, by omega⟩).1 ≠ c := fun h => hcK (h ▸ hiK)
      have hnotR : (φy.symm ⟨i.val + 1, by omega⟩).1 ∉ R := Finset.disjoint_right.mp hdisj_RK hiK
      dsimp only [invF, toF]
      rw [dif_neg hne, dif_neg hnotR]
      congr 1; congr 1; apply Fin.ext
      have h1 : φy ⟨(φy.symm ⟨i.val + 1, by omega⟩).1, Set.mem_insert_of_mem c hiK⟩ = ⟨i.val + 1, by omega⟩ :=
        (congrArg φy (Subtype.ext rfl)).trans (φy.right_inv ⟨i.val + 1, by omega⟩)
      have hval := congrArg Fin.val h1
      dsimp only at hval
      dsimp only
      omega
  change Nonempty (T.induce (insert c ((R : Set V') ∪ (K : Set V'))) ≃g Q2 T₀ c₀ B₀ r)
  rw [← coe_union, ← coe_insert]
  refine ⟨⟨⟨toF, invF, hleft, hright⟩, ?_⟩⟩
  intro x₁ x₂
  rw [iff_comm]
  change T.Adj x₁.1 x₂.1 ↔ (Q2 T₀ c₀ B₀ r).Adj (toF x₁) (toF x₂)
  dsimp only [toF]
  by_cases h1c : x₁.1 = c <;> by_cases h2c : x₂.1 = c
  · simp [h1c, h2c, Q2]
  · simp only [dif_pos h1c, dif_neg h2c]; simp only [h1c]
    by_cases h2R : x₂.1 ∈ R
    · simp only [dif_pos h2R, Q2]
      have h_eq := (φR.map_rel_iff (a := ⟨c, h1R⟩) (b := ⟨x₂.1, Set.mem_insert_of_mem c h2R⟩)).symm
      change T.Adj c x₂.1 ↔ T₀.Adj (φR ⟨c, h1R⟩).1 (φR ⟨x₂.1, _⟩).1 at h_eq
      rwa [congrArg Subtype.val hφRc] at h_eq
    · simp only [dif_neg h2R, Q2]
      have h2K : x₂.1 ∈ K := (mem_union.mp ((mem_insert.mp x₂.2).resolve_left h2c)).resolve_left h2R
      have h_eq := (φy.map_rel_iff (a := ⟨c, Set.mem_insert _ _⟩) (b := ⟨x₂.1, Set.mem_insert_of_mem c h2K⟩)).symm
      change T.Adj c x₂.1 ↔ (pathG (r + 1)).Adj (φy ⟨c, _⟩) (φy ⟨x₂.1, _⟩) at h_eq
      rw [hφyc] at h_eq
      have hpos := hφy_pos x₂.1 h2K
      refine h_eq.trans ⟨fun h => by dsimp only [pathG] at h; change _ = 0; rcases h with h | h <;> omega, fun h => by change 0 + 1 = _ ∨ _ + 1 = 0; left; omega⟩
  · simp only [dif_neg h1c, dif_pos h2c]; simp only [h2c]
    by_cases h1R : x₁.1 ∈ R
    · simp only [dif_pos h1R, Q2]
      have h_eq := (φR.map_rel_iff (a := ⟨x₁.1, Set.mem_insert_of_mem c h1R⟩) (b := ⟨c, Set.mem_insert _ _⟩)).symm
      change T.Adj x₁.1 c ↔ T₀.Adj (φR ⟨x₁.1, _⟩).1 (φR ⟨c, Set.mem_insert _ _⟩).1 at h_eq
      rw [congrArg Subtype.val hφRc, T₀.adj_comm] at h_eq
      exact h_eq
    · simp only [dif_neg h1R, Q2]
      have h1K : x₁.1 ∈ K := (mem_union.mp ((mem_insert.mp x₁.2).resolve_left h1c)).resolve_left h1R
      have h_eq := (φy.map_rel_iff (a := ⟨x₁.1, Set.mem_insert_of_mem c h1K⟩) (b := ⟨c, Set.mem_insert _ _⟩)).symm
      change T.Adj x₁.1 c ↔ (pathG (r + 1)).Adj (φy ⟨x₁.1, _⟩) (φy ⟨c, _⟩) at h_eq
      rw [hφyc] at h_eq
      have hpos := hφy_pos x₁.1 h1K
      refine h_eq.trans ⟨fun h => by dsimp only [pathG] at h; change _ = 0; rcases h with h | h <;> omega, fun h => by change _ + 1 = 0 ∨ 0 + 1 = _; right; omega⟩
  · simp only [dif_neg h1c, dif_neg h2c]
    by_cases h1R : x₁.1 ∈ R <;> by_cases h2R : x₂.1 ∈ R
    · simp only [dif_pos h1R, dif_pos h2R, Q2]
      exact (φR.map_rel_iff (a := ⟨x₁.1, Set.mem_insert_of_mem c h1R⟩) (b := ⟨x₂.1, Set.mem_insert_of_mem c h2R⟩)).symm
    · simp only [dif_pos h1R, dif_neg h2R, Q2]
      have h2K : x₂.1 ∈ K := (mem_union.mp ((mem_insert.mp x₂.2).resolve_left h2c)).resolve_left h2R
      exact ⟨fun hadj => hDDy (adj_compSet_eq T c (hR_sub h1R) (hK_sub h2K) hadj), False.elim⟩
    · simp only [dif_neg h1R, dif_pos h2R, Q2]
      have h1K : x₁.1 ∈ K := (mem_union.mp ((mem_insert.mp x₁.2).resolve_left h1c)).resolve_left h1R
      exact ⟨fun hadj => hDDy.symm (adj_compSet_eq T c (hK_sub h1K) (hR_sub h2R) hadj), False.elim⟩
    · simp only [dif_neg h1R, dif_neg h2R, Q2]
      have h1K : x₁.1 ∈ K := (mem_union.mp ((mem_insert.mp x₁.2).resolve_left h1c)).resolve_left h1R
      have h2K : x₂.1 ∈ K := (mem_union.mp ((mem_insert.mp x₂.2).resolve_left h2c)).resolve_left h2R
      have h_eq := (φy.map_rel_iff (a := ⟨x₁.1, Set.mem_insert_of_mem c h1K⟩) (b := ⟨x₂.1, Set.mem_insert_of_mem c h2K⟩)).symm
      change T.Adj x₁.1 x₂.1 ↔ (pathG (r + 1)).Adj (φy ⟨x₁.1, _⟩) (φy ⟨x₂.1, _⟩) at h_eq
      have hp1 := hφy_pos x₁.1 h1K
      have hp2 := hφy_pos x₂.1 h2K
      refine h_eq.trans ⟨?_, ?_⟩
      · rintro (h | h) <;> [left; right] <;> dsimp [pathG] at h ⊢ <;> omega
      · rintro (h | h) <;> [left; right] <;> dsimp [pathG] at h ⊢ <;> omega
set_option maxHeartbeats 400000 in
private lemma Q2_subgraphs_card_eq {U₀ V' : Type} [Fintype U₀] [Fintype V']
    (T₀ : SimpleGraph U₀) (hT0 : T₀.IsTree) (c₀ : U₀) (B₀ : Finset U₀)
    (hc0_not : c₀ ∉ B₀)
    (hB0_conn : (T₀.induce (B₀ : Set U₀)).Connected)
    (hB0_root : ∃ b ∈ B₀, T₀.Adj c₀ b)
    (r M : ℕ) (hr : 2 ≤ r)
    (hnot_path : ¬ RootedIso T₀ c₀ (insert c₀ (B₀ : Set U₀)) (pathG (r + 1)) ⟨0, Nat.zero_lt_succ r⟩ Set.univ)
    (hgtM : M < B₀.card + 1 + r) (hM_le : M ≤ B₀.card + 1)
    (hforce : B₀.card = M ∨ ∃ b ∈ B₀, r ≤ T₀.dist c₀ b)
    (T : SimpleGraph V') (hT : T.IsTree) (c : V') (hecc : T.eccent c = r)
    (hmax : ∀ D : (T.induce {c}ᶜ).ConnectedComponent, card D.supp ≤ M) :
    {S : Finset V' | Nonempty (T.induce (S : Set V') ≃g Q2 T₀ c₀ B₀ r)}.ncard =
      ∑ D : (T.induce {c}ᶜ).ConnectedComponent,
        (univ.filter fun R : Finset V' =>
          R ⊆ compSet T c D ∧ c ∉ R ∧ RootedIso T c (insert c (R : Set V')) T₀ c₀ (insert c₀ (B₀ : Set U₀))).card *
        ((univ.filter fun y : V' => T.dist c y = r).card -
          (univ.filter fun y : V' => y ∈ compSet T c D ∧ T.dist c y = r).card) := by
  have hB0_ins_conn : (T₀.induce (insert c₀ (B₀ : Set U₀))).Connected := by
    obtain ⟨b₀, hb₀, hadj0⟩ := hB0_root
    refine Connected.mk fun x y => ?_
    suffices h0 : ∀ z : (insert c₀ (B₀ : Set U₀) : Set U₀),
        (T₀.induce (insert c₀ (B₀ : Set U₀))).Reachable ⟨c₀, Set.mem_insert c₀ _⟩ z from
      (h0 x).symm.trans (h0 y)
    intro ⟨z, hz⟩
    rcases mem_insert_iff.mp hz with rfl | hzB
    · exact Reachable.rfl
    · obtain ⟨w⟩ := hB0_conn ⟨b₀, hb₀⟩ ⟨z, hzB⟩
      have hadj' : (T₀.induce (insert c₀ (B₀ : Set U₀))).Adj
          ⟨c₀, Set.mem_insert c₀ _⟩ ⟨b₀, Set.mem_insert_of_mem c₀ hb₀⟩ := hadj0
      let g : T₀.induce (B₀ : Set U₀) →g T₀.induce (insert c₀ (B₀ : Set U₀)) :=
        ⟨fun a => ⟨a.1, Set.mem_insert_of_mem c₀ a.2⟩, @fun _ _ h => h⟩
      exact (Adj.reachable hadj').trans ⟨(w.map g).copy rfl rfl⟩
  let LHS : Finset (Finset V') := univ.filter fun S : Finset V' =>
    Nonempty (T.induce (S : Set V') ≃g Q2 T₀ c₀ B₀ r)
  have hLHS : {S : Finset V' | Nonempty (T.induce (S : Set V') ≃g Q2 T₀ c₀ B₀ r)}.ncard = LHS.card := by
    have hs : {S : Finset V' | Nonempty (T.induce (S : Set V') ≃g Q2 T₀ c₀ B₀ r)} = (LHS : Set (Finset V')) := by
      ext S; simp [LHS]
    rw [hs, Set.ncard_coe_finset]
  let SubRoots (D : (T.induce {c}ᶜ).ConnectedComponent) :=
    univ.filter fun R : Finset V' =>
      R ⊆ compSet T c D ∧ c ∉ R ∧ RootedIso T c (insert c (R : Set V')) T₀ c₀ (insert c₀ (B₀ : Set U₀))
  let YOut (D : (T.induce {c}ᶜ).ConnectedComponent) :=
    univ.filter fun y : V' => y ∉ compSet T c D ∧ T.dist c y = r
  have hYOut_card : ∀ D : (T.induce {c}ᶜ).ConnectedComponent,
      (YOut D).card = (univ.filter fun y : V' => T.dist c y = r).card -
        (univ.filter fun y : V' => y ∈ compSet T c D ∧ T.dist c y = r).card := by
    intro D
    let A := univ.filter fun y : V' => T.dist c y = r
    let B := univ.filter fun y : V' => y ∈ compSet T c D ∧ T.dist c y = r
    have hsub : B ⊆ A := fun y hy => mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hy).2.2⟩
    have hsdiff : A \ B = YOut D := by
      ext y; simp only [A, B, YOut, mem_sdiff, mem_filter, mem_univ, true_and]
      tauto
    rw [← hsdiff, card_sdiff_of_subset hsub]
  let RHS := univ.sigma fun D : (T.induce {c}ᶜ).ConnectedComponent => (SubRoots D) ×ˢ (YOut D)
  have hRHS_card : RHS.card = ∑ D : (T.induce {c}ᶜ).ConnectedComponent, (SubRoots D).card * (YOut D).card := by
    rw [card_sigma]
    exact sum_congr rfl fun D _ => card_product _ _
  simp_rw [← hYOut_card]
  rw [hLHS, ← hRHS_card]
  have hcard_eq : RHS.card = LHS.card := by
    refine card_bij (fun ⟨D, ⟨R, y⟩⟩ _ => insert c (R ∪ pathTail T hT c y)) ?_ ?_ ?_
    · rintro ⟨D, ⟨R, y⟩⟩ hmem
      simp only [RHS, mem_sigma, mem_univ, true_and, mem_product,
        SubRoots, YOut, mem_filter] at hmem
      obtain ⟨⟨hR_sub, hcR, hR_iso⟩, hy_not, hyd⟩ := hmem
      exact mem_filter.mpr ⟨mem_univ _, by
        rw [coe_insert, coe_union]
        exact Q2_induce_union_iso T₀ c₀ B₀ hc0_not T hT hr c D hR_sub hcR hR_iso hy_not hyd⟩
    · rintro ⟨D₁, ⟨R₁, y₁⟩⟩ hm1 ⟨D₂, ⟨R₂, y₂⟩⟩ hm2 heq
      simp only [RHS, mem_sigma, mem_univ, true_and, mem_product,
        SubRoots, YOut, mem_filter] at hm1 hm2
      rcases hm1 with ⟨⟨hR1_sub, hcR1, hR1_iso⟩, hy1_not, hy1_dist⟩
      rcases hm2 with ⟨⟨hR2_sub, hcR2, hR2_iso⟩, hy2_not, hy2_dist⟩
      have hsp1 := pathTail_spec T hT hr c y₁ hy1_dist
      have hsp2 := pathTail_spec T hT hr c y₂ hy2_dist
      have hy1_c : y₁ ≠ c := fun h => by rw [← h, dist_self] at hy1_dist; omega
      have hy2_c : y₂ ≠ c := fun h => by rw [← h, dist_self] at hy2_dist; omega
      let Dy1 := (T.induce {c}ᶜ).connectedComponentMk ⟨y₁, hy1_c⟩
      let Dy2 := (T.induce {c}ᶜ).connectedComponentMk ⟨y₂, hy2_c⟩
      have hD1y1 : D₁ ≠ Dy1 := fun h => hy1_not (h ▸ (mem_compSet_iff T c Dy1 y₁).mpr ⟨hy1_c, rfl⟩)
      have hD2y2 : D₂ ≠ Dy2 := fun h => hy2_not (h ▸ (mem_compSet_iff T c Dy2 y₂).mpr ⟨hy2_c, rfl⟩)
      have hU_eq : R₁ ∪ pathTail T hT c y₁ = R₂ ∪ pathTail T hT c y₂ := by
        ext z
        have hm := Finset.ext_iff.mp heq z
        simp only [mem_insert] at hm
        constructor <;> intro hz
        · have hzc : z ≠ c := by
            rcases mem_union.mp hz with h | h <;> [exact fun he => hcR1 (he ▸ h); exact fun he => hsp1.1 (he ▸ h)]
          rcases hm.mp (Or.inr hz) with h | h
          · exact False.elim (hzc h)
          · exact h
        · have hzc : z ≠ c := by
            rcases mem_union.mp hz with h | h <;> [exact fun he => hcR2 (he ▸ h); exact fun he => hsp2.1 (he ▸ h)]
          rcases hm.mpr (Or.inr hz) with h | h
          · exact False.elim (hzc h)
          · exact h
      have hR1_ne : R₁.Nonempty := by
        obtain ⟨b₀, hb₀, _⟩ := hB0_root
        obtain ⟨h1R, h1B, φR, hφRc⟩ := hR1_iso
        have hne : (⟨b₀, Set.mem_insert_of_mem c₀ hb₀⟩ : ↥(insert c₀ (B₀ : Set U₀))) ≠ ⟨c₀, h1B⟩ :=
          fun h => hc0_not (by have h' := congrArg Subtype.val h; dsimp at h'; exact h' ▸ hb₀)
        have hm := (φR.symm ⟨b₀, Set.mem_insert_of_mem c₀ hb₀⟩).2
        rcases mem_insert_iff.mp hm with hceq | hxR
        · exact False.elim (hne (φR.symm.injective (Subtype.ext hceq |>.trans (φR.symm_apply_eq.mpr hφRc.symm).symm)))
        · exact ⟨_, hxR⟩
      obtain ⟨x₁, hx1⟩ := hR1_ne
      have hx1_U : x₁ ∈ R₂ ∪ pathTail T hT c y₂ := hU_eq ▸ mem_union_left _ hx1
      rcases mem_union.mp hx1_U with hx1_R2 | hx1_K2
      · have hD12 : D₁ = D₂ := by
          obtain ⟨h1, h2⟩ := (mem_compSet_iff T c D₁ x₁).mp (hR1_sub hx1)
          obtain ⟨h3, h4⟩ := (mem_compSet_iff T c D₂ x₁).mp (hR2_sub hx1_R2)
          exact ((mem_supp_iff D₁ _).mp h2).symm.trans
            ((mem_supp_iff D₂ _).mp h4)
        subst hD12
        have hR12 : R₁ = R₂ := by
          ext z; constructor <;> intro hz
          · rcases mem_union.mp (hU_eq ▸ mem_union_left _ hz) with h | h
            · exact h
            · exact False.elim (Finset.disjoint_left.mp (compSet_disjoint T c hD2y2) (hR1_sub hz) (hsp2.2.2.2.1 h))
          · rcases mem_union.mp (hU_eq.symm ▸ mem_union_left _ hz) with h | h
            · exact h
            · exact False.elim (Finset.disjoint_left.mp (compSet_disjoint T c hD1y1) (hR2_sub hz) (hsp1.2.2.2.1 h))
        have hK12 : pathTail T hT c y₁ = pathTail T hT c y₂ := by
          ext z; constructor <;> intro hz
          · rcases mem_union.mp (hU_eq ▸ mem_union_right _ hz) with h | h
            · exact False.elim (Finset.disjoint_left.mp (compSet_disjoint T c hD1y1) (hR2_sub h) (hsp1.2.2.2.1 hz))
            · exact h
          · rcases mem_union.mp (hU_eq.symm ▸ mem_union_right _ hz) with h | h
            · exact False.elim (Finset.disjoint_left.mp (compSet_disjoint T c hD2y2) (hR1_sub h) (hsp2.2.2.2.1 hz))
            · exact h
        have hy12 : y₁ = y₂ := (hsp2.2.2.2.2.1 y₁ (hK12 ▸ hsp1.2.1)).2.mp hy1_dist
        subst hy12; subst hR12; rfl
      · have hD1_y2 : D₁ = Dy2 := by
          obtain ⟨h1, h2⟩ := (mem_compSet_iff T c D₁ x₁).mp (hR1_sub hx1)
          obtain ⟨h3, h4⟩ := (mem_compSet_iff T c Dy2 x₁).mp (hsp2.2.2.2.1 hx1_K2)
          exact ((mem_supp_iff D₁ _).mp h2).symm.trans
            ((mem_supp_iff Dy2 _).mp h4)
        have hR2_ne : R₂.Nonempty := by
          obtain ⟨b₀, hb₀, _⟩ := hB0_root
          obtain ⟨h1R, h1B, φR, hφRc⟩ := hR2_iso
          have hne : (⟨b₀, Set.mem_insert_of_mem c₀ hb₀⟩ : ↥(insert c₀ (B₀ : Set U₀))) ≠ ⟨c₀, h1B⟩ :=
            fun h => hc0_not (by have h' := congrArg Subtype.val h; dsimp at h'; exact h' ▸ hb₀)
          have hm := (φR.symm ⟨b₀, Set.mem_insert_of_mem c₀ hb₀⟩).2
          rcases mem_insert_iff.mp hm with hceq | hxR
          · exact False.elim (hne (φR.symm.injective (Subtype.ext hceq |>.trans (φR.symm_apply_eq.mpr hφRc.symm).symm)))
          · exact ⟨_, hxR⟩
        obtain ⟨x₂, hx2⟩ := hR2_ne
        have hx2_K1 : x₂ ∈ pathTail T hT c y₁ := by
          rcases mem_union.mp (hU_eq.symm ▸ mem_union_left _ hx2) with h | h
          · exact False.elim (hD2y2 (by
              obtain ⟨h1, h2⟩ := (mem_compSet_iff T c D₂ x₂).mp (hR2_sub hx2)
              obtain ⟨h3, h4⟩ := (mem_compSet_iff T c D₁ x₂).mp (hR1_sub h)
              exact ((((mem_supp_iff D₂ _).mp h2).symm.trans
                ((mem_supp_iff D₁ _).mp h4)).trans hD1_y2)))
          · exact h
        have hD2_y1 : D₂ = Dy1 := by
          obtain ⟨h1, h2⟩ := (mem_compSet_iff T c D₂ x₂).mp (hR2_sub hx2)
          obtain ⟨h3, h4⟩ := (mem_compSet_iff T c Dy1 x₂).mp (hsp1.2.2.2.1 hx2_K1)
          exact ((mem_supp_iff D₂ _).mp h2).symm.trans
            ((mem_supp_iff Dy1 _).mp h4)
        have hD12_ne : D₁ ≠ D₂ := fun h => hD2y2 (h.symm.trans hD1_y2)
        have hy12_ne : Dy1 ≠ Dy2 := fun h => hD12_ne (hD1_y2.trans (h.symm.trans hD2_y1.symm))
        have hR1_eq_K2 : R₁ = pathTail T hT c y₂ := by
          ext z; constructor <;> intro hz
          · rcases mem_union.mp (hU_eq ▸ mem_union_left _ hz) with h | h
            · exact False.elim (Finset.disjoint_left.mp (compSet_disjoint T c hD12_ne) (hR1_sub hz) (hR2_sub h))
            · exact h
          · rcases mem_union.mp (hU_eq.symm ▸ mem_union_right _ hz) with h | h
            · exact h
            · exact False.elim (Finset.disjoint_left.mp (compSet_disjoint T c hy12_ne) (hsp1.2.2.2.1 h) (hsp2.2.2.2.1 hz))
        have h_iso_path : RootedIso T₀ c₀ (insert c₀ (B₀ : Set U₀)) (pathG (r + 1)) ⟨0, Nat.zero_lt_succ r⟩ Set.univ := by
          obtain ⟨φy, hφy0, _⟩ := hsp2.2.2.2.2.2
          have h1 : RootedIso T c (insert c (pathTail T hT c y₂ : Set V')) (pathG (r + 1)) ⟨0, Nat.zero_lt_succ r⟩ Set.univ :=
            ⟨Set.mem_insert _ _, Set.mem_univ _,
              φy.trans (induceUnivIso (pathG (r + 1))).symm, Subtype.ext hφy0⟩
          rw [← hR1_eq_K2] at h1
          exact hR1_iso.symm.trans h1
        exact False.elim (hnot_path h_iso_path)
    · -- Surjectivity:
      intro S hS
      obtain ⟨ψ⟩ := (mem_filter.mp hS).2
      have hcf := Q2_center_forced T₀ hT0 c₀ B₀ hc0_not hB0_ins_conn T hT hr c hecc hmax hgtM hM_le hforce S ψ
      obtain ⟨hcS, hψc⟩ := hcf
      let R : Finset V' := univ.filter fun x => ∃ (hx : x ∈ (S : Set V')), ∃ b, ψ ⟨x, hx⟩ = some (Sum.inl b)
      let K : Finset V' := univ.filter fun x => ∃ (hx : x ∈ (S : Set V')), ∃ i, ψ ⟨x, hx⟩ = some (Sum.inr i)
      obtain ⟨b₀, hb₀, hadj0⟩ := hB0_root
      let rb : V' := (ψ.symm (some (Sum.inl ⟨b₀, hb₀⟩))).1
      have hrb_ne : rb ≠ c := fun h => by
        have : ψ.symm (some (Sum.inl ⟨b₀, hb₀⟩)) = ⟨c, hcS⟩ := Subtype.ext h
        have := congrArg ψ this; rw [ψ.apply_symm_apply, hψc] at this; simp at this
      let D := (T.induce {c}ᶜ).connectedComponentMk ⟨rb, hrb_ne⟩
      let y := (ψ.symm (some (Sum.inr ⟨r - 1, by omega⟩))).1
      have hcR : c ∉ R := fun h => by
        obtain ⟨hx, b, hxb⟩ := (mem_filter.mp h).2
        have : (⟨c, hcS⟩ : (S : Set V')) = ⟨c, hx⟩ := rfl
        rw [this, hψc] at hxb; simp at hxb
      have hcK : c ∉ K := fun h => by
        obtain ⟨hx, i, hxi⟩ := (mem_filter.mp h).2
        have : (⟨c, hcS⟩ : (S : Set V')) = ⟨c, hx⟩ := rfl
        rw [this, hψc] at hxi; simp at hxi
      have hR_sub : R ⊆ compSet T c D := by
        intro x hx
        obtain ⟨hxS, bx, hψx⟩ := (mem_filter.mp hx).2
        have hxc : x ≠ c := fun h => hcR (h ▸ hx)
        refine (mem_compSet_iff T c D x).mpr ⟨hxc, ?_⟩
        obtain ⟨w⟩ := hB0_conn ⟨b₀, hb₀⟩ bx
        let g : T₀.induce (B₀ : Set U₀) →g T.induce {c}ᶜ :=
          ⟨fun z => ⟨(ψ.symm (some (Sum.inl z))).1, fun h => by
            have := congrArg ψ (Subtype.ext h : ψ.symm (some (Sum.inl z)) = ⟨c, hcS⟩)
            rw [ψ.apply_symm_apply, hψc] at this; simp at this⟩,
           @fun _ _ hadj => (ψ.symm.map_rel_iff).mpr hadj⟩
        have hreach : (T.induce {c}ᶜ).Reachable ⟨rb, hrb_ne⟩ ⟨x, hxc⟩ :=
          ⟨(w.map g).copy rfl (Subtype.ext (by
            change (ψ.symm (some (Sum.inl bx))).1 = x
            exact congrArg Subtype.val (ψ.symm_apply_eq.mpr hψx.symm)))⟩
        exact (mem_supp_iff D _).mpr (sound hreach).symm
      have hR_iso : RootedIso T c (insert c (R : Set V')) T₀ c₀ (insert c₀ (B₀ : Set U₀)) := by
        have hR_spec : ∀ x : V', x ∈ R → ∃ (hx : x ∈ (S : Set V')) (b : ↥B₀), ψ ⟨x, hx⟩ = some (Sum.inl b) :=
          fun _ hxR => (mem_filter.mp hxR).2
        let toR : ↥(insert c (R : Set V')) → ↥(insert c₀ (B₀ : Set U₀)) := fun x =>
          if hx : x.1 = c then ⟨c₀, Set.mem_insert _ _⟩
          else
            let hxR : x.1 ∈ R := (mem_insert_iff.mp x.2).resolve_left hx
            let b := (hR_spec x.1 hxR).choose_spec.choose
            ⟨b.1, Set.mem_insert_of_mem c₀ b.2⟩
        let invR : ↥(insert c₀ (B₀ : Set U₀)) → ↥(insert c (R : Set V')) := fun z =>
          if hz : z.1 = c₀ then ⟨c, Set.mem_insert _ _⟩
          else
            let zb : ↥B₀ := ⟨z.1, (mem_insert_iff.mp z.2).resolve_left hz⟩
            ⟨(ψ.symm (some (Sum.inl zb))).1, Or.inr (mem_filter.mpr ⟨mem_univ _,
              ⟨(ψ.symm (some (Sum.inl zb))).2, zb, ψ.apply_symm_apply _⟩⟩)⟩
        have hto_eq : ∀ (x : ↥(insert c (R : Set V'))) (hx : x.1 ≠ c),
            ∃ (hxS : x.1 ∈ (S : Set V')) (b : ↥B₀),
              ψ ⟨x.1, hxS⟩ = some (Sum.inl b) ∧ toR x = ⟨b.1, Set.mem_insert_of_mem c₀ b.2⟩ := by
          intro x hx
          let hxR : x.1 ∈ R := (mem_insert_iff.mp x.2).resolve_left hx
          refine ⟨(hR_spec x.1 hxR).choose, (hR_spec x.1 hxR).choose_spec.choose,
            (hR_spec x.1 hxR).choose_spec.choose_spec, ?_⟩
          simp [toR, hx]
        refine ⟨Set.mem_insert _ _, Set.mem_insert _ _, ⟨⟨toR, invR, ?_, ?_⟩, ?_⟩, ?_⟩
        · intro x
          by_cases hx : x.1 = c
          · apply Subtype.ext; simp [toR, invR, hx]
          · obtain ⟨hxS, b, hψb, hto⟩ := hto_eq x hx
            have hb_ne : b.1 ≠ c₀ := fun h => hc0_not (h ▸ b.2)
            apply Subtype.ext; rw [hto]; simp only [invR, dif_neg hb_ne]
            have hb_eq : (⟨b.1, (mem_insert_iff.mp (Set.mem_insert_of_mem c₀ b.2)).resolve_left hb_ne⟩ : ↥B₀) = b := Subtype.ext rfl
            rw [hb_eq]
            exact congrArg Subtype.val (ψ.symm_apply_eq.mpr hψb.symm)
        · intro z
          by_cases hz : z.1 = c₀
          · apply Subtype.ext; simp [invR, toR, hz]
          · obtain ⟨hxS, b, hψb, hto⟩ := hto_eq (invR z) (by
              intro h
              simp only [invR, dif_neg hz] at h
              have h1 := congrArg ψ (Subtype.ext h : ψ.symm (some (Sum.inl _)) = ⟨c, hcS⟩)
              rw [ψ.apply_symm_apply, hψc] at h1; simp at h1)
            apply Subtype.ext; rw [hto]
            have hinv1 : (invR z).1 = (ψ.symm (some (Sum.inl ⟨z.1, (mem_insert_iff.mp z.2).resolve_left hz⟩))).1 := by
              simp [invR, hz]
            have hinv2 : (⟨(invR z).1, hxS⟩ : ↥(S : Set V')) = ψ.symm (some (Sum.inl ⟨z.1, (mem_insert_iff.mp z.2).resolve_left hz⟩)) :=
              Subtype.ext hinv1
            rw [hinv2, ψ.apply_symm_apply] at hψb
            exact (congrArg Subtype.val (Sum.inl.inj (Option.some.inj hψb))).symm
        · intro x₁ x₂
          have hlift : ∀ x : ↥(insert c (R : Set V')), ∃ (hx : x.1 ∈ (S : Set V')),
              ((toR x).1 = c₀ ∧ ψ ⟨x.1, hx⟩ = none) ∨
              (∃ b : ↥B₀, (toR x).1 = b.1 ∧ ψ ⟨x.1, hx⟩ = some (Sum.inl b)) := by
            intro x
            by_cases hx : x.1 = c
            · have hxS : x.1 ∈ (S : Set V') := by rw [hx]; exact hcS
              exact ⟨hxS, Or.inl ⟨by simp [toR, hx], by rw [show (⟨x.1, hxS⟩ : ↥(S : Set V')) = ⟨c, hcS⟩ from Subtype.ext hx, hψc]⟩⟩
            · obtain ⟨hxS, b, hψb, hto⟩ := hto_eq x hx
              exact ⟨hxS, Or.inr ⟨b, congrArg Subtype.val hto, hψb⟩⟩
          obtain ⟨hx1, H1⟩ := hlift x₁
          obtain ⟨hx2, H2⟩ := hlift x₂
          have hadj := (ψ.map_rel_iff (a := ⟨x₁.1, hx1⟩) (b := ⟨x₂.1, hx2⟩)).symm
          change T.Adj x₁.1 x₂.1 ↔ (Q2 T₀ c₀ B₀ r).Adj (ψ ⟨x₁.1, hx1⟩) (ψ ⟨x₂.1, hx2⟩) at hadj
          change T₀.Adj (toR x₁).1 (toR x₂).1 ↔ T.Adj x₁.1 x₂.1
          rw [hadj]
          rcases H1 with ⟨h1c0, h1n⟩ | ⟨b1, h1b, h1n⟩ <;> rcases H2 with ⟨h2c0, h2n⟩ | ⟨b2, h2b, h2n⟩
          · rw [h1c0, h2c0, h1n, h2n]; exact ⟨fun h => absurd h (T₀.loopless.irrefl _), False.elim⟩
          · rw [h1c0, h2b, h1n, h2n]; rfl
          · rw [h1b, h2c0, h1n, h2n]; exact T₀.adj_comm b1.1 c₀
          · rw [h1b, h2b, h1n, h2n]; rfl
        · apply Subtype.ext; simp [toR]
      have hy_not_D : y ∉ compSet T c D := by
        let y₁ : V' := (ψ.symm (some (Sum.inr ⟨0, by omega⟩))).1
        have hy1_ne : y₁ ≠ c := fun h => by
          have : ψ.symm (some (Sum.inr ⟨0, by omega⟩)) = ⟨c, hcS⟩ := Subtype.ext h
          have := congrArg ψ this; rw [ψ.apply_symm_apply, hψc] at this; simp at this
        have hy_ne : y ≠ c := fun h => by
          have : ψ.symm (some (Sum.inr ⟨r - 1, by omega⟩)) = ⟨c, hcS⟩ := Subtype.ext h
          have := congrArg ψ this; rw [ψ.apply_symm_apply, hψc] at this; simp at this
        have hadj_y1 : T.Adj c y₁ := by
          have hq : (Q2 T₀ c₀ B₀ r).Adj (ψ ⟨c, hcS⟩) (some (Sum.inr ⟨0, by omega⟩)) := by rw [hψc]; rfl
          simpa [ψ.symm_apply_apply] using ψ.symm.map_rel_iff.mpr hq
        have hadj_rb : T.Adj c rb := by
          have hq : (Q2 T₀ c₀ B₀ r).Adj (ψ ⟨c, hcS⟩) (some (Sum.inl ⟨b₀, hb₀⟩)) := by rw [hψc]; exact hadj0
          simpa [ψ.symm_apply_apply] using ψ.symm.map_rel_iff.mpr hq
        have hne_rb_y1 : rb ≠ y₁ := fun h => by
          have h1 : (ψ.symm (some (Sum.inl ⟨b₀, hb₀⟩))) = ψ.symm (some (Sum.inr ⟨0, by omega⟩)) := Subtype.ext h
          have h2 := ψ.symm.injective h1
          simp at h2
        obtain ⟨pr, _, _, _⟩ := pathG_walk_up (r := r) (r - 1) (by omega)
        let gR : pathG r →g T.induce {c}ᶜ :=
          ⟨fun j => ⟨(ψ.symm (some (Sum.inr j))).1, fun h => by
            have : ψ.symm (some (Sum.inr j)) = ⟨c, hcS⟩ := Subtype.ext h
            have := congrArg ψ this; rw [ψ.apply_symm_apply, hψc] at this; simp at this⟩,
           @fun _ _ hadj => (ψ.symm.map_rel_iff).mpr hadj⟩
        have hreach_y : (T.induce {c}ᶜ).Reachable ⟨y₁, hy1_ne⟩ ⟨y, hy_ne⟩ := ⟨pr.map gR⟩
        intro hyD; obtain ⟨_, hy2⟩ := (mem_compSet_iff T c D y).mp hyD
        have hy1_D : y₁ ∈ compSet T c D := (mem_compSet_iff T c D y₁).mpr ⟨hy1_ne,
          (mem_supp_iff D _).mpr ((sound hreach_y).trans
            ((mem_supp_iff D _).mp hy2))⟩
        have he1 := compSet_root_adj T hT c D ((mem_compSet_iff T c D rb).mpr ⟨hrb_ne, rfl⟩) hadj_rb
        have he2 := compSet_root_adj T hT c D hy1_D hadj_y1
        exact hne_rb_y1 (he1.trans he2.symm)
      have hy_dist : T.dist c y = r := by
        obtain ⟨pr, hpr, hprlen, _⟩ := pathG_walk_up (r := r) (r - 1) (by omega)
        let pQ : (Q2 T₀ c₀ B₀ r).Walk none (some (Sum.inr ⟨r - 1, by omega⟩)) :=
          Walk.cons (by simp [Q2] : (Q2 T₀ c₀ B₀ r).Adj none (some (Sum.inr ⟨0, by omega⟩)))
            (pr.map ⟨fun j => some (Sum.inr j), @fun _ _ h => h⟩)
        have hpQ : pQ.IsPath :=
          (cons_isPath_iff _ _).mpr ⟨hpr.map (fun _ _ h => Sum.inr.inj (Option.some.inj h)), fun hm => by
            rw [Walk.support_map, List.mem_map] at hm; obtain ⟨j, _, hj⟩ := hm; simp at hj⟩
        let gS : T.induce (S : Set V') →g T := (Embedding.induce (S : Set V')).toHom
        let pT : T.Walk c y := ((pQ.map ψ.symm.toHom).map gS).copy
          (congrArg Subtype.val (ψ.symm_apply_eq.mpr hψc.symm)) rfl
        have hpT : pT.IsPath := (isPath_copy _ _ _).mpr ((hpQ.map ψ.symm.injective).map val_injective)
        rw [← isTree_dist_eq_length_of_isPath T hT pT hpT]
        have hlen : pT.length = pQ.length := (length_copy _ _ _).trans (by rw [length_map, length_map])
        have hq : pQ.length = 1 + pr.length := by dsimp only [pQ]; erw [length_cons, length_map]; omega
        omega
      have hK_eq_pathTail : K = pathTail T hT c y := by
        have hK_card : K.card = r := by
          rw [← card_coe K, ← card_fin r]
          refine card_congr ⟨fun x => (mem_filter.mp x.2).2.choose_spec.choose,
            fun i => ⟨(ψ.symm (some (Sum.inr i))).1, mem_filter.mpr ⟨mem_univ _,
              ⟨(ψ.symm (some (Sum.inr i))).2, i, ψ.apply_symm_apply _⟩⟩⟩,
            fun x => by
              dsimp only
              have hm := (mem_filter.mp x.2).2
              exact Subtype.ext (congrArg (fun z : (S : Set V') => z.1) (ψ.symm_apply_eq.mpr hm.choose_spec.choose_spec.symm)),
            fun i => by
              dsimp only
              set z := (ψ.symm (some (Sum.inr i))).1
              have hz : z ∈ K := mem_filter.mpr ⟨mem_univ _,
                ⟨(ψ.symm (some (Sum.inr i))).2, i, ψ.apply_symm_apply _⟩⟩
              have hm := (mem_filter.mp hz).2
              exact Sum.inr.inj (Option.some.inj ((hm.choose_spec.choose_spec).symm.trans (ψ.apply_symm_apply _)))⟩
        have hK_spec : ∀ x : V', x ∈ K → ∃ (hx : x ∈ (S : Set V')) (j : Fin r), ψ ⟨x, hx⟩ = some (Sum.inr j) :=
          fun _ hxK => (mem_filter.mp hxK).2
        let toK : ↥(insert c (K : Set V')) → Fin (r + 1) := fun x =>
          if hx : x.1 = c then ⟨0, Nat.zero_lt_succ r⟩
          else
            let j := (hK_spec x.1 ((mem_insert_iff.mp x.2).resolve_left hx)).choose_spec.choose
            ⟨j.val + 1, by omega⟩
        let invK : Fin (r + 1) → ↥(insert c (K : Set V')) := fun i =>
          if hi : i.val = 0 then ⟨c, Set.mem_insert _ _⟩
          else
            let j : Fin r := ⟨i.val - 1, by omega⟩
            ⟨(ψ.symm (some (Sum.inr j))).1, Or.inr (mem_filter.mpr ⟨mem_univ _,
              ⟨(ψ.symm (some (Sum.inr j))).2, j, ψ.apply_symm_apply _⟩⟩)⟩
        have htoK_eq : ∀ (x : ↥(insert c (K : Set V'))) (hx : x.1 ≠ c),
            ∃ (hxS : x.1 ∈ (S : Set V')) (j : Fin r),
              ψ ⟨x.1, hxS⟩ = some (Sum.inr j) ∧ toK x = ⟨j.val + 1, by omega⟩ := by
          intro x hx
          let hxK : x.1 ∈ K := (mem_insert_iff.mp x.2).resolve_left hx
          refine ⟨(hK_spec x.1 hxK).choose, (hK_spec x.1 hxK).choose_spec.choose,
            (hK_spec x.1 hxK).choose_spec.choose_spec, ?_⟩
          simp [toK, hx]
        let ψK : T.induce (insert c (K : Set V')) ≃g pathG (r + 1) :=
          ⟨⟨toK, invK,
            fun x => by
              by_cases hx : x.1 = c
              · apply Subtype.ext; simp [toK, invK, hx]
              · obtain ⟨hxS, j, hψj, hto⟩ := htoK_eq x hx
                apply Subtype.ext; rw [hto]
                have hne0 : j.val + 1 ≠ 0 := by omega
                simp only [invK, dif_neg hne0]
                have hj_eq : (⟨j.val + 1 - 1, by omega⟩ : Fin r) = j := Fin.ext rfl
                rw [hj_eq]
                exact congrArg Subtype.val (ψ.symm_apply_eq.mpr hψj.symm),
            fun i => by
              by_cases hi : i.val = 0
              · apply Fin.ext; simp only [invK, dif_pos hi, toK, dif_pos rfl]; exact hi.symm
              · obtain ⟨hxS, j, hψj, hto⟩ := htoK_eq (invK i) (by
                  intro h; simp only [invK, dif_neg hi] at h
                  have h1 := congrArg ψ (Subtype.ext h : ψ.symm (some (Sum.inr _)) = ⟨c, hcS⟩)
                  rw [ψ.apply_symm_apply, hψc] at h1; simp at h1)
                rw [hto]; apply Fin.ext
                have hinv1 : (invK i).1 = (ψ.symm (some (Sum.inr ⟨i.val - 1, by omega⟩))).1 := by simp only [invK, dif_neg hi]
                have hinv2 : (⟨(invK i).1, hxS⟩ : ↥(S : Set V')) = ψ.symm (some (Sum.inr ⟨i.val - 1, by omega⟩)) :=
                  Subtype.ext hinv1
                rw [hinv2, ψ.apply_symm_apply] at hψj
                have hv := congrArg Fin.val (Sum.inr.inj (Option.some.inj hψj))
                dsimp at hv ⊢; omega⟩,
            by
              intro x₁ x₂
              have hlift : ∀ x : ↥(insert c (K : Set V')), ∃ (hx : x.1 ∈ (S : Set V')),
                  ((toK x).val = 0 ∧ ψ ⟨x.1, hx⟩ = none) ∨
                  (∃ j : Fin r, (toK x).val = j.val + 1 ∧ ψ ⟨x.1, hx⟩ = some (Sum.inr j)) := by
                intro x
                by_cases hx : x.1 = c
                · have hxS : x.1 ∈ (S : Set V') := by rw [hx]; exact hcS
                  exact ⟨hxS, Or.inl ⟨by simp [toK, hx], by rw [show (⟨x.1, hxS⟩ : ↥(S : Set V')) = ⟨c, hcS⟩ from Subtype.ext hx, hψc]⟩⟩
                · obtain ⟨hxS, j, hψj, hto⟩ := htoK_eq x hx
                  exact ⟨hxS, Or.inr ⟨j, congrArg Fin.val hto, hψj⟩⟩
              obtain ⟨hx1, H1⟩ := hlift x₁
              obtain ⟨hx2, H2⟩ := hlift x₂
              have hadj := (ψ.map_rel_iff (a := ⟨x₁.1, hx1⟩) (b := ⟨x₂.1, hx2⟩)).symm
              change T.Adj x₁.1 x₂.1 ↔ (Q2 T₀ c₀ B₀ r).Adj (ψ ⟨x₁.1, hx1⟩) (ψ ⟨x₂.1, hx2⟩) at hadj
              rw [iff_comm]
              change T.Adj x₁.1 x₂.1 ↔ (pathG (r + 1)).Adj (toK x₁) (toK x₂)
              rw [hadj]
              rcases H1 with ⟨h1z, h1n⟩ | ⟨j1, h1v, h1n⟩ <;> rcases H2 with ⟨h2z, h2n⟩ | ⟨j2, h2v, h2n⟩
              · rw [h1n, h2n]; dsimp only [Q2, pathG]; simp [h1z, h2z]
              · rw [h1n, h2n]; simp only [Q2, pathG, h1z, h2v]; constructor <;> [intro h; rintro (h | h)] <;> omega
              · rw [h1n, h2n]; simp only [Q2, pathG, h1v, h2z]; constructor <;> [intro h; rintro (h | h)] <;> omega
              · rw [h1n, h2n]; simp only [Q2, pathG, h1v, h2v]; constructor <;> [rintro (h | h); rintro (h | h)] <;> [left; right; left; right] <;> omega⟩
        refine pathTail_eq_of_iso T hT hr c y hy_dist K hcK hK_card ψK ?_ ?_
        · apply Fin.ext; simp [ψK, toK]
        · have hyK : y ∈ K := mem_filter.mpr ⟨mem_univ _,
            ⟨(ψ.symm (some (Sum.inr ⟨r - 1, by omega⟩))).2, ⟨r - 1, by omega⟩, ψ.apply_symm_apply _⟩⟩
          refine ⟨hyK, ?_⟩
          apply Fin.ext
          have hy_ne : y ≠ c := fun h => hcK (h ▸ hyK)
          obtain ⟨hxS, j, hψj, hto⟩ := htoK_eq ⟨y, Set.mem_insert_of_mem c hyK⟩ hy_ne
          have hψy : ψ ⟨y, hxS⟩ = some (Sum.inr ⟨r - 1, by omega⟩) := by
            have hsub : (⟨y, hxS⟩ : ↥(S : Set V')) = ψ.symm (some (Sum.inr ⟨r - 1, by omega⟩)) := Subtype.ext rfl
            rw [hsub, ψ.apply_symm_apply]
          have hv := congrArg Fin.val (Sum.inr.inj (Option.some.inj (hψj.symm.trans hψy)))
          simp only [ψK, RelIso.coe_fn_mk, Equiv.coe_fn_mk]; rw [hto]; dsimp at hv ⊢; omega
      have hS_eq : insert c (R ∪ pathTail T hT c y) = S := by
        rw [← hK_eq_pathTail]
        ext x; constructor
        · intro hx
          rcases mem_insert.mp hx with rfl | hx
          · exact hcS
          · rcases mem_union.mp hx with hxR | hxK
            · exact (mem_filter.mp hxR).2.choose
            · exact (mem_filter.mp hxK).2.choose
        · intro hxS
          by_cases hxc : x = c
          · rw [hxc]; exact mem_insert_self c _
          · refine mem_insert_of_mem ?_
            cases hψx : ψ ⟨x, hxS⟩ with
            | none => exact False.elim (hxc (congrArg Subtype.val (ψ.injective (hψx.trans hψc.symm))))
            | some v => cases v with
              | inl b => exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, ⟨hxS, b, hψx⟩⟩)
              | inr j => exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, ⟨hxS, j, hψx⟩⟩)
      exact ⟨⟨D, (R, y)⟩, mem_sigma.mpr ⟨mem_univ _, mem_product.mpr
        ⟨mem_filter.mpr ⟨mem_univ _, hR_sub, hcR, hR_iso⟩,
         mem_filter.mpr ⟨mem_univ _, hy_not_D, hy_dist⟩⟩⟩, hS_eq⟩
  rw [← hcard_eq]
private lemma comp_ins_isTree {V' : Type} [Fintype V'] (T : SimpleGraph V') (hT : T.IsTree)
    (c : V') (D : (T.induce {c}ᶜ).ConnectedComponent) :
    (T.induce (insert c (compSet T c D : Set V'))).IsTree := by
  refine ⟨?_, hT.isAcyclic.induce _⟩
  obtain ⟨u, ⟨hu_mem, hu_adj⟩, _⟩ := existsUnique_root_of_component T hT c D
  have hu_D : u.1 ∈ compSet T c D := (mem_compSet_iff T c D u.1).mpr ⟨u.2, hu_mem⟩
  refine Connected.mk fun a b => ?_
  suffices h0 : ∀ x : (insert c (compSet T c D : Set V') : Set V'),
      (T.induce _).Reachable ⟨c, Set.mem_insert _ _⟩ x from (h0 a).symm.trans (h0 b)
  intro ⟨x, hx⟩
  rcases mem_insert_iff.mp hx with rfl | hxD
  · exact Reachable.rfl
  · obtain ⟨hx1, hx2⟩ := (mem_compSet_iff T c D x).mp hxD
    obtain ⟨wD⟩ := ((hT.isAcyclic.induce {c}ᶜ).isTree_connectedComponent D).connected
      ⟨u, hu_mem⟩ ⟨⟨x, hx1⟩, hx2⟩
    let gD : D.toSimpleGraph →g T.induce (insert c (compSet T c D : Set V')) :=
      ⟨fun z => ⟨z.1.1, Or.inr ((mem_compSet_iff T c D z.1.1).mpr ⟨z.1.2, z.2⟩)⟩, @fun _ _ h => h⟩
    have hadj' : (T.induce (insert c (compSet T c D : Set V'))).Adj
        ⟨c, Set.mem_insert _ _⟩ ⟨u.1, Or.inr hu_D⟩ := hu_adj
    exact (Adj.reachable hadj').trans ⟨(wD.map gD).copy rfl rfl⟩
private lemma Q3_induce_union_iso {U₀ V' : Type} [Fintype U₀] [Fintype V']
    (T₀ : SimpleGraph U₀) (c₀ : U₀) (B₀ : Finset U₀) (hc0_not : c₀ ∉ B₀)
    (T : SimpleGraph V') (hT : T.IsTree) {r : ℕ} (hr : 2 ≤ r) (c : V')
    (D : (T.induce {c}ᶜ).ConnectedComponent)
    {R : Finset V'} (hR_sub : R ⊆ compSet T c D) (hcR : c ∉ R)
    (hR_iso : RootedIso T c (insert c (R : Set V')) T₀ c₀ (insert c₀ (B₀ : Set U₀)))
    {y₁ y₂ : V'} (hy1_not : y₁ ∉ compSet T c D) (hy2_not : y₂ ∉ compSet T c D)
    (hy1_dist : T.dist c y₁ = r) (hy2_dist : T.dist c y₂ = r)
    (hy1c : y₁ ≠ c) (hy2c : y₂ ≠ c)
    (hy12 : (T.induce {c}ᶜ).connectedComponentMk ⟨y₁, hy1c⟩ ≠
      (T.induce {c}ᶜ).connectedComponentMk ⟨y₂, hy2c⟩) :
    Nonempty (T.induce (insert c (R ∪ pathTail T hT c y₁ ∪ pathTail T hT c y₂ : Set V')) ≃g
      Q3 T₀ c₀ B₀ r) := by
  obtain ⟨h1R, h1B, φR, hφRc⟩ := hR_iso
  have hsp1 := pathTail_spec T hT hr c y₁ hy1_dist
  have hsp2 := pathTail_spec T hT hr c y₂ hy2_dist
  let K₁ := pathTail T hT c y₁
  let K₂ := pathTail T hT c y₂
  let D₁ := (T.induce {c}ᶜ).connectedComponentMk ⟨y₁, hy1c⟩
  let D₂ := (T.induce {c}ᶜ).connectedComponentMk ⟨y₂, hy2c⟩
  have hDD1 : D ≠ D₁ := fun h => hy1_not (h ▸ (mem_compSet_iff T c D₁ y₁).mpr ⟨hy1c, rfl⟩)
  have hDD2 : D ≠ D₂ := fun h => hy2_not (h ▸ (mem_compSet_iff T c D₂ y₂).mpr ⟨hy2c, rfl⟩)
  have hD12 : D₁ ≠ D₂ := hy12
  have hK1_sub : K₁ ⊆ compSet T c D₁ := hsp1.2.2.2.1
  have hK2_sub : K₂ ⊆ compSet T c D₂ := hsp2.2.2.2.1
  have hdisj_R1 : Disjoint R K₁ := (compSet_disjoint T c hDD1).mono hR_sub hK1_sub
  have hdisj_R2 : Disjoint R K₂ := (compSet_disjoint T c hDD2).mono hR_sub hK2_sub
  have hdisj_12 : Disjoint K₁ K₂ := (compSet_disjoint T c hD12).mono hK1_sub hK2_sub
  have hcK1 : c ∉ K₁ := hsp1.1
  have hcK2 : c ∉ K₂ := hsp2.1
  obtain ⟨φ1, hφ1c, _⟩ := hsp1.2.2.2.2.2
  obtain ⟨φ2, hφ2c, _⟩ := hsp2.2.2.2.2.2
  have hφR_B0 : ∀ (x : V') (hx : x ∈ R), (φR ⟨x, Set.mem_insert_of_mem c hx⟩).1 ∈ B₀ := by
    intro x hx
    have hmem := (φR ⟨x, Set.mem_insert_of_mem c hx⟩).2
    rcases mem_insert_iff.mp hmem with hceq | hxB
    · have hne : (⟨x, Set.mem_insert_of_mem c hx⟩ : ↥(insert c (R : Set V'))) ≠ ⟨c, h1R⟩ := fun h => by
        have heqv : x = c := congrArg Subtype.val h
        exact hcR (heqv ▸ hx)
      exact False.elim (hne (φR.injective (Subtype.ext (hceq.trans (congrArg Subtype.val hφRc).symm))))
    · exact hxB
  have hφR_symm_R : ∀ (b : ↥B₀), (φR.symm ⟨b.1, Set.mem_insert_of_mem c₀ b.2⟩).1 ∈ R := by
    intro b
    have hne : (⟨b.1, Set.mem_insert_of_mem c₀ b.2⟩ : ↥(insert c₀ (B₀ : Set U₀))) ≠ ⟨c₀, h1B⟩ := fun h => by
      have heqv : b.1 = c₀ := congrArg Subtype.val h
      exact hc0_not (heqv ▸ b.2)
    have hmem := (φR.symm ⟨b.1, Set.mem_insert_of_mem c₀ b.2⟩).2
    rcases mem_insert_iff.mp hmem with hceq | hxR
    · exact False.elim (hne (φR.symm.injective (Subtype.ext hceq |>.trans (φR.symm_apply_eq.mpr hφRc.symm).symm)))
    · exact hxR
  have hφ1_pos : ∀ (z : V') (hz : z ∈ K₁), 0 < (φ1 ⟨z, Set.mem_insert_of_mem c hz⟩).val := fun z hz => by
    by_contra h0
    have heqv : z = c := congrArg Subtype.val (φ1.injective ((Fin.ext (Nat.eq_zero_of_not_pos h0) :
      φ1 ⟨z, Set.mem_insert_of_mem c hz⟩ = ⟨0, Nat.zero_lt_succ r⟩).trans hφ1c.symm))
    exact hcK1 (heqv ▸ hz)
  have hφ2_pos : ∀ (z : V') (hz : z ∈ K₂), 0 < (φ2 ⟨z, Set.mem_insert_of_mem c hz⟩).val := fun z hz => by
    by_contra h0
    have heqv : z = c := congrArg Subtype.val (φ2.injective ((Fin.ext (Nat.eq_zero_of_not_pos h0) :
      φ2 ⟨z, Set.mem_insert_of_mem c hz⟩ = ⟨0, Nat.zero_lt_succ r⟩).trans hφ2c.symm))
    exact hcK2 (heqv ▸ hz)
  have hφ1_symm : ∀ (i : Fin r), (φ1.symm ⟨i.val + 1, by omega⟩).1 ∈ K₁ := fun i => by
    have hmem := (φ1.symm ⟨i.val + 1, by omega⟩).2
    rcases mem_insert_iff.mp hmem with hceq | hz
    · have h2 := congrArg φ1 (Subtype.ext hceq : φ1.symm ⟨i.val + 1, by omega⟩ = ⟨c, Set.mem_insert _ _⟩)
      rw [φ1.apply_symm_apply, hφ1c] at h2
      have hv := congrArg Fin.val h2; dsimp at hv; omega
    · exact hz
  have hφ2_symm : ∀ (i : Fin r), (φ2.symm ⟨i.val + 1, by omega⟩).1 ∈ K₂ := fun i => by
    have hmem := (φ2.symm ⟨i.val + 1, by omega⟩).2
    rcases mem_insert_iff.mp hmem with hceq | hz
    · have h2 := congrArg φ2 (Subtype.ext hceq : φ2.symm ⟨i.val + 1, by omega⟩ = ⟨c, Set.mem_insert _ _⟩)
      rw [φ2.apply_symm_apply, hφ2c] at h2
      have hv := congrArg Fin.val h2; dsimp at hv; omega
    · exact hz
  let S := insert c (R ∪ K₁ ∪ K₂)
  let toF : ↥(S : Set V') → Option (↥B₀ ⊕ (Fin r ⊕ Fin r)) := fun x =>
    if hx : x.1 = c then none
    else if hxR : x.1 ∈ R then some (Sum.inl ⟨(φR ⟨x.1, Set.mem_insert_of_mem c hxR⟩).1, hφR_B0 x.1 hxR⟩)
    else if hx1 : x.1 ∈ K₁ then some (Sum.inr (Sum.inl ⟨(φ1 ⟨x.1, Set.mem_insert_of_mem c hx1⟩).val - 1, by
      have := (φ1 ⟨x.1, Set.mem_insert_of_mem c hx1⟩).isLt; omega⟩))
    else
      have hx2 : x.1 ∈ K₂ := ((mem_union.mp ((mem_insert.mp x.2).resolve_left hx)).resolve_left
        fun h => (mem_union.mp h).elim hxR hx1)
      some (Sum.inr (Sum.inr ⟨(φ2 ⟨x.1, Set.mem_insert_of_mem c hx2⟩).val - 1, by
        have := (φ2 ⟨x.1, Set.mem_insert_of_mem c hx2⟩).isLt; omega⟩))
  let invF : Option (↥B₀ ⊕ (Fin r ⊕ Fin r)) → (S : Set V') := fun u =>
    match u with
    | none => ⟨c, mem_insert_self c _⟩
    | some (Sum.inl b) => ⟨(φR.symm ⟨b.1, Set.mem_insert_of_mem c₀ b.2⟩).1,
        mem_insert_of_mem (mem_union_left K₂ (mem_union_left K₁ (hφR_symm_R b)))⟩
    | some (Sum.inr (Sum.inl i)) => ⟨(φ1.symm ⟨i.val + 1, by omega⟩).1,
        mem_insert_of_mem (mem_union_left K₂ (mem_union_right R (hφ1_symm i)))⟩
    | some (Sum.inr (Sum.inr i)) => ⟨(φ2.symm ⟨i.val + 1, by omega⟩).1,
        mem_insert_of_mem (mem_union_right _ (hφ2_symm i))⟩
  have hleft : LeftInverse invF toF := by
    intro x; apply Subtype.ext; dsimp only [toF]
    by_cases hxc : x.1 = c
    · simp only [dif_pos hxc, invF]; exact hxc.symm
    · simp only [dif_neg hxc]
      by_cases hxR : x.1 ∈ R
      · simp only [dif_pos hxR, invF, coe_eta]
        exact congrArg Subtype.val (φR.left_inv ⟨x.1, Set.mem_insert_of_mem c hxR⟩)
      · simp only [dif_neg hxR]
        by_cases hx1 : x.1 ∈ K₁
        · simp only [dif_pos hx1, invF]
          have hpos := hφ1_pos x.1 hx1
          have hlt := (φ1 ⟨x.1, Set.mem_insert_of_mem c hx1⟩).isLt
          have hfin : (⟨(φ1 ⟨x.1, Set.mem_insert_of_mem c hx1⟩).val - 1 + 1, by omega⟩ : Fin (r + 1)) =
              φ1 ⟨x.1, Set.mem_insert_of_mem c hx1⟩ := Fin.ext (by dsimp; omega)
          rw [hfin]; exact congrArg Subtype.val (φ1.left_inv _)
        · simp only [dif_neg hx1, invF]
          have hx2 : x.1 ∈ K₂ := ((mem_union.mp ((mem_insert.mp x.2).resolve_left hxc)).resolve_left
            fun h => (mem_union.mp h).elim hxR hx1)
          have hpos := hφ2_pos x.1 hx2
          have hlt := (φ2 ⟨x.1, Set.mem_insert_of_mem c hx2⟩).isLt
          have hfin : (⟨(φ2 ⟨x.1, Set.mem_insert_of_mem c hx2⟩).val - 1 + 1, by omega⟩ : Fin (r + 1)) =
              φ2 ⟨x.1, Set.mem_insert_of_mem c hx2⟩ := Fin.ext (by dsimp; omega)
          rw [hfin]; exact congrArg Subtype.val (φ2.left_inv _)
  have hright : RightInverse invF toF := by
    intro u
    rcases u with _ | (b | (i | i))
    · simp [invF, toF]
    · have hbR := hφR_symm_R b
      have hne : (φR.symm ⟨b.1, Set.mem_insert_of_mem c₀ b.2⟩).1 ≠ c := fun h => hcR (h ▸ hbR)
      dsimp only [invF, toF]; rw [dif_neg hne, dif_pos hbR]
      exact congrArg (fun z : ↥B₀ => some (Sum.inl z)) (Subtype.ext (by
        have h1 : φR ⟨(φR.symm ⟨b.1, Set.mem_insert_of_mem c₀ b.2⟩).1, Set.mem_insert_of_mem c hbR⟩ =
            ⟨b.1, Set.mem_insert_of_mem c₀ b.2⟩ :=
          (congrArg φR (Subtype.ext rfl)).trans (φR.right_inv ⟨b.1, Set.mem_insert_of_mem c₀ b.2⟩)
        exact congrArg (fun z : ↥(insert c₀ (B₀ : Set U₀)) => z.1) h1))
    · have hi1 := hφ1_symm i
      have hne : (φ1.symm ⟨i.val + 1, by omega⟩).1 ≠ c := fun h => hcK1 (h ▸ hi1)
      have hnotR : (φ1.symm ⟨i.val + 1, by omega⟩).1 ∉ R := Finset.disjoint_right.mp hdisj_R1 hi1
      dsimp only [invF, toF]; rw [dif_neg hne, dif_neg hnotR, dif_pos hi1]
      congr 1; congr 1; congr 1; apply Fin.ext
      have h1 : φ1 ⟨(φ1.symm ⟨i.val + 1, by omega⟩).1, Set.mem_insert_of_mem c hi1⟩ = ⟨i.val + 1, by omega⟩ :=
        (congrArg φ1 (Subtype.ext rfl)).trans (φ1.right_inv ⟨i.val + 1, by omega⟩)
      have hval := congrArg Fin.val h1; dsimp only at hval; dsimp only; omega
    · have hi2 := hφ2_symm i
      have hne : (φ2.symm ⟨i.val + 1, by omega⟩).1 ≠ c := fun h => hcK2 (h ▸ hi2)
      have hnotR : (φ2.symm ⟨i.val + 1, by omega⟩).1 ∉ R := Finset.disjoint_right.mp hdisj_R2 hi2
      have hnot1 : (φ2.symm ⟨i.val + 1, by omega⟩).1 ∉ K₁ := Finset.disjoint_right.mp hdisj_12 hi2
      dsimp only [invF, toF]; rw [dif_neg hne, dif_neg hnotR, dif_neg hnot1]
      congr 1; congr 1; congr 1; apply Fin.ext
      have h1 : φ2 ⟨(φ2.symm ⟨i.val + 1, by omega⟩).1, Set.mem_insert_of_mem c hi2⟩ = ⟨i.val + 1, by omega⟩ :=
        (congrArg φ2 (Subtype.ext rfl)).trans (φ2.right_inv ⟨i.val + 1, by omega⟩)
      have hval := congrArg Fin.val h1; dsimp only at hval; dsimp only; omega
  change Nonempty (T.induce (insert c ((R : Set V') ∪ (K₁ : Set V') ∪ (K₂ : Set V'))) ≃g Q3 T₀ c₀ B₀ r)
  rw [← coe_union, ← coe_union, ← coe_insert]
  refine ⟨⟨⟨toF, invF, hleft, hright⟩, ?_⟩⟩
  intro x₁ x₂
  rw [iff_comm]
  change T.Adj x₁.1 x₂.1 ↔ (Q3 T₀ c₀ B₀ r).Adj (toF x₁) (toF x₂)
  dsimp only [toF]
  have mem_K2_of : ∀ (x : (S : Set V')), x.1 ≠ c → x.1 ∉ R → x.1 ∉ K₁ → x.1 ∈ K₂ := fun x h1 h2 h3 =>
    ((mem_union.mp ((mem_insert.mp x.2).resolve_left h1)).resolve_left
      fun h => (mem_union.mp h).elim h2 h3)
  by_cases h1c : x₁.1 = c <;> by_cases h2c : x₂.1 = c
  · simp [h1c, h2c, Q3]
  · simp only [dif_pos h1c, dif_neg h2c]; simp only [h1c]
    by_cases h2R : x₂.1 ∈ R
    · simp only [dif_pos h2R, Q3]
      have h_eq := (φR.map_rel_iff (a := ⟨c, h1R⟩) (b := ⟨x₂.1, Set.mem_insert_of_mem c h2R⟩)).symm
      change T.Adj c x₂.1 ↔ T₀.Adj (φR ⟨c, h1R⟩).1 (φR ⟨x₂.1, _⟩).1 at h_eq
      rwa [congrArg Subtype.val hφRc] at h_eq
    · simp only [dif_neg h2R]
      by_cases h21 : x₂.1 ∈ K₁
      · simp only [dif_pos h21, Q3]
        have h_eq := (φ1.map_rel_iff (a := ⟨c, Set.mem_insert _ _⟩) (b := ⟨x₂.1, Set.mem_insert_of_mem c h21⟩)).symm
        change T.Adj c x₂.1 ↔ (pathG (r + 1)).Adj (φ1 ⟨c, _⟩) (φ1 ⟨x₂.1, _⟩) at h_eq
        rw [hφ1c] at h_eq; have := hφ1_pos x₂.1 h21
        refine h_eq.trans ⟨fun h => by dsimp only [pathG] at h; change _ = 0; rcases h with h | h <;> omega, fun h => by change 0 + 1 = _ ∨ _ + 1 = 0; left; omega⟩
      · simp only [dif_neg h21, Q3]
        have h22 := mem_K2_of x₂ h2c h2R h21
        have h_eq := (φ2.map_rel_iff (a := ⟨c, Set.mem_insert _ _⟩) (b := ⟨x₂.1, Set.mem_insert_of_mem c h22⟩)).symm
        change T.Adj c x₂.1 ↔ (pathG (r + 1)).Adj (φ2 ⟨c, _⟩) (φ2 ⟨x₂.1, _⟩) at h_eq
        rw [hφ2c] at h_eq; have := hφ2_pos x₂.1 h22
        refine h_eq.trans ⟨fun h => by dsimp only [pathG] at h; change _ = 0; rcases h with h | h <;> omega, fun h => by change 0 + 1 = _ ∨ _ + 1 = 0; left; omega⟩
  · simp only [dif_neg h1c, dif_pos h2c]; simp only [h2c]
    by_cases h1R : x₁.1 ∈ R
    · simp only [dif_pos h1R, Q3]
      have h_eq := (φR.map_rel_iff (a := ⟨x₁.1, Set.mem_insert_of_mem c h1R⟩) (b := ⟨c, Set.mem_insert _ _⟩)).symm
      change T.Adj x₁.1 c ↔ T₀.Adj (φR ⟨x₁.1, _⟩).1 (φR ⟨c, Set.mem_insert _ _⟩).1 at h_eq
      rw [congrArg Subtype.val hφRc, T₀.adj_comm] at h_eq; exact h_eq
    · simp only [dif_neg h1R]
      by_cases h11 : x₁.1 ∈ K₁
      · simp only [dif_pos h11, Q3]
        have h_eq := (φ1.map_rel_iff (a := ⟨x₁.1, Set.mem_insert_of_mem c h11⟩) (b := ⟨c, Set.mem_insert _ _⟩)).symm
        change T.Adj x₁.1 c ↔ (pathG (r + 1)).Adj (φ1 ⟨x₁.1, _⟩) (φ1 ⟨c, _⟩) at h_eq
        rw [hφ1c] at h_eq; have := hφ1_pos x₁.1 h11
        refine h_eq.trans ⟨fun h => by dsimp only [pathG] at h; change _ = 0; rcases h with h | h <;> omega, fun h => by change _ + 1 = 0 ∨ 0 + 1 = _; right; omega⟩
      · simp only [dif_neg h11, Q3]
        have h12 := mem_K2_of x₁ h1c h1R h11
        have h_eq := (φ2.map_rel_iff (a := ⟨x₁.1, Set.mem_insert_of_mem c h12⟩) (b := ⟨c, Set.mem_insert _ _⟩)).symm
        change T.Adj x₁.1 c ↔ (pathG (r + 1)).Adj (φ2 ⟨x₁.1, _⟩) (φ2 ⟨c, _⟩) at h_eq
        rw [hφ2c] at h_eq; have := hφ2_pos x₁.1 h12
        refine h_eq.trans ⟨fun h => by dsimp only [pathG] at h; change _ = 0; rcases h with h | h <;> omega, fun h => by change _ + 1 = 0 ∨ 0 + 1 = _; right; omega⟩
  · simp only [dif_neg h1c, dif_neg h2c]
    by_cases h1R : x₁.1 ∈ R <;> by_cases h2R : x₂.1 ∈ R
    · simp only [dif_pos h1R, dif_pos h2R, Q3]
      exact (φR.map_rel_iff (a := ⟨x₁.1, Set.mem_insert_of_mem c h1R⟩) (b := ⟨x₂.1, Set.mem_insert_of_mem c h2R⟩)).symm
    · simp only [dif_pos h1R, dif_neg h2R]
      by_cases h21 : x₂.1 ∈ K₁
      · simp only [dif_pos h21, Q3]
        exact ⟨fun hadj => hDD1 (adj_compSet_eq T c (hR_sub h1R) (hK1_sub h21) hadj), False.elim⟩
      · simp only [dif_neg h21, Q3]
        exact ⟨fun hadj => hDD2 (adj_compSet_eq T c (hR_sub h1R) (hK2_sub (mem_K2_of x₂ h2c h2R h21)) hadj), False.elim⟩
    · simp only [dif_neg h1R, dif_pos h2R]
      by_cases h11 : x₁.1 ∈ K₁
      · simp only [dif_pos h11, Q3]
        exact ⟨fun hadj => hDD1.symm (adj_compSet_eq T c (hK1_sub h11) (hR_sub h2R) hadj), False.elim⟩
      · simp only [dif_neg h11, Q3]
        exact ⟨fun hadj => hDD2.symm (adj_compSet_eq T c (hK2_sub (mem_K2_of x₁ h1c h1R h11)) (hR_sub h2R) hadj), False.elim⟩
    · simp only [dif_neg h1R, dif_neg h2R]
      by_cases h11 : x₁.1 ∈ K₁ <;> by_cases h21 : x₂.1 ∈ K₁
      · simp only [dif_pos h11, dif_pos h21, Q3]
        have h_eq := (φ1.map_rel_iff (a := ⟨x₁.1, Set.mem_insert_of_mem c h11⟩) (b := ⟨x₂.1, Set.mem_insert_of_mem c h21⟩)).symm
        change T.Adj x₁.1 x₂.1 ↔ (pathG (r + 1)).Adj (φ1 ⟨x₁.1, _⟩) (φ1 ⟨x₂.1, _⟩) at h_eq
        have hp1 := hφ1_pos x₁.1 h11; have hp2 := hφ1_pos x₂.1 h21
        refine h_eq.trans ⟨?_, ?_⟩ <;> rintro (h | h) <;> [left; right; left; right] <;> dsimp [pathG] at h ⊢ <;> omega
      · simp only [dif_pos h11, dif_neg h21, Q3]
        exact ⟨fun hadj => hD12 (adj_compSet_eq T c (hK1_sub h11) (hK2_sub (mem_K2_of x₂ h2c h2R h21)) hadj), False.elim⟩
      · simp only [dif_neg h11, dif_pos h21, Q3]
        exact ⟨fun hadj => hD12.symm (adj_compSet_eq T c (hK2_sub (mem_K2_of x₁ h1c h1R h11)) (hK1_sub h21) hadj), False.elim⟩
      · simp only [dif_neg h11, dif_neg h21, Q3]
        have h12 := mem_K2_of x₁ h1c h1R h11; have h22 := mem_K2_of x₂ h2c h2R h21
        have h_eq := (φ2.map_rel_iff (a := ⟨x₁.1, Set.mem_insert_of_mem c h12⟩) (b := ⟨x₂.1, Set.mem_insert_of_mem c h22⟩)).symm
        change T.Adj x₁.1 x₂.1 ↔ (pathG (r + 1)).Adj (φ2 ⟨x₁.1, _⟩) (φ2 ⟨x₂.1, _⟩) at h_eq
        have hp1 := hφ2_pos x₁.1 h12; have hp2 := hφ2_pos x₂.1 h22
        refine h_eq.trans ⟨?_, ?_⟩ <;> rintro (h | h) <;> [left; right; left; right] <;> dsimp [pathG] at h ⊢ <;> omega
set_option maxHeartbeats 400000 in
private lemma Q3_two_mul_subgraphs_card_eq {U₀ V' : Type} [Fintype U₀] [Fintype V']
    (T₀ : SimpleGraph U₀) (hT0 : T₀.IsTree) (c₀ : U₀) (B₀ : Finset U₀)
    (hc0_not : c₀ ∉ B₀)
    (hB0_conn : (T₀.induce (B₀ : Set U₀)).Connected)
    (hB0_root : ∃ b ∈ B₀, T₀.Adj c₀ b)
    (r M : ℕ) (hr : 2 ≤ r)
    (hB0_no_r : ∀ b ∈ B₀, T₀.dist c₀ b ≤ r - 1)
    (hBM : B₀.card = M - 1) (hM_pos : 1 ≤ M)
    (T : SimpleGraph V') (hT : T.IsTree) (c : V') (hecc : T.eccent c = r)
    (hmax : ∀ D : (T.induce {c}ᶜ).ConnectedComponent, card D.supp ≤ M) :
    2 * {S : Finset V' | Nonempty (T.induce (S : Set V') ≃g Q3 T₀ c₀ B₀ r)}.ncard =
      ∑ D : (T.induce {c}ᶜ).ConnectedComponent,
        (univ.filter fun R : Finset V' =>
          R ⊆ compSet T c D ∧ c ∉ R ∧ RootedIso T c (insert c (R : Set V')) T₀ c₀ (insert c₀ (B₀ : Set U₀))).card *
        (univ.filter fun p : V' × V' =>
          p.1 ∉ compSet T c D ∧ p.2 ∉ compSet T c D ∧ T.dist c p.1 = r ∧ T.dist c p.2 = r ∧
          ∃ (h1 : p.1 ≠ c) (h2 : p.2 ≠ c),
            (T.induce {c}ᶜ).connectedComponentMk ⟨p.1, h1⟩ ≠
            (T.induce {c}ᶜ).connectedComponentMk ⟨p.2, h2⟩).card := by
  have hB0_ins_conn : (T₀.induce (insert c₀ (B₀ : Set U₀))).Connected := by
    obtain ⟨b₀, hb₀, hadj0⟩ := hB0_root
    refine Connected.mk fun x y => ?_
    suffices h0 : ∀ z : (insert c₀ (B₀ : Set U₀) : Set U₀),
        (T₀.induce (insert c₀ (B₀ : Set U₀))).Reachable ⟨c₀, Set.mem_insert c₀ _⟩ z from
      (h0 x).symm.trans (h0 y)
    intro ⟨z, hz⟩
    rcases mem_insert_iff.mp hz with rfl | hzB
    · exact Reachable.rfl
    · obtain ⟨w⟩ := hB0_conn ⟨b₀, hb₀⟩ ⟨z, hzB⟩
      have hadj' : (T₀.induce (insert c₀ (B₀ : Set U₀))).Adj
          ⟨c₀, Set.mem_insert c₀ _⟩ ⟨b₀, Set.mem_insert_of_mem c₀ hb₀⟩ := hadj0
      let g : T₀.induce (B₀ : Set U₀) →g T₀.induce (insert c₀ (B₀ : Set U₀)) :=
        ⟨fun a => ⟨a.1, Set.mem_insert_of_mem c₀ a.2⟩, @fun _ _ h => h⟩
      exact (Adj.reachable hadj').trans ⟨(w.map g).copy rfl rfl⟩
  let LHS : Finset (Finset V') := univ.filter fun S : Finset V' =>
    Nonempty (T.induce (S : Set V') ≃g Q3 T₀ c₀ B₀ r)
  have hLHS : {S : Finset V' | Nonempty (T.induce (S : Set V') ≃g Q3 T₀ c₀ B₀ r)}.ncard = LHS.card := by
    have hs : {S : Finset V' | Nonempty (T.induce (S : Set V') ≃g Q3 T₀ c₀ B₀ r)} = (LHS : Set (Finset V')) := by
      ext S; simp [LHS]
    rw [hs, Set.ncard_coe_finset]
  let SubRoots (D : (T.induce {c}ᶜ).ConnectedComponent) :=
    univ.filter fun R : Finset V' =>
      R ⊆ compSet T c D ∧ c ∉ R ∧ RootedIso T c (insert c (R : Set V')) T₀ c₀ (insert c₀ (B₀ : Set U₀))
  let PairsOut (D : (T.induce {c}ᶜ).ConnectedComponent) :=
    univ.filter fun p : V' × V' =>
      p.1 ∉ compSet T c D ∧ p.2 ∉ compSet T c D ∧ T.dist c p.1 = r ∧ T.dist c p.2 = r ∧
      ∃ (h1 : p.1 ≠ c) (h2 : p.2 ≠ c),
        (T.induce {c}ᶜ).connectedComponentMk ⟨p.1, h1⟩ ≠
        (T.induce {c}ᶜ).connectedComponentMk ⟨p.2, h2⟩
  let RHS := univ.sigma fun D : (T.induce {c}ᶜ).ConnectedComponent =>
    (SubRoots D) ×ˢ (PairsOut D)
  have hRHS_card : RHS.card = ∑ D : (T.induce {c}ᶜ).ConnectedComponent,
      (SubRoots D).card * (PairsOut D).card := by
    rw [card_sigma]
    exact sum_congr rfl fun D _ => card_product _ _
  rw [hLHS, ← hRHS_card]
  let π : (Σ _D : (T.induce {c}ᶜ).ConnectedComponent, Finset V' × V' × V') → Finset V' :=
    fun ⟨_, ⟨R, y₁, y₂⟩⟩ => insert c (R ∪ pathTail T hT c y₁ ∪ pathTail T hT c y₂)
  have hmaps : ∀ a ∈ RHS, π a ∈ LHS := by
    rintro ⟨D, ⟨R, y₁, y₂⟩⟩ ha
    simp only [RHS, mem_sigma, mem_univ, true_and, mem_product,
      SubRoots, PairsOut, mem_filter] at ha
    obtain ⟨⟨hR_sub, hcR, hR_iso⟩, hy1_not, hy2_not, hy1d, hy2d, hy1c, hy2c, hy12⟩ := ha
    exact mem_filter.mpr ⟨mem_univ _,
      (by dsimp only [π]; rw [coe_insert, coe_union, coe_union]
          exact Q3_induce_union_iso T₀ c₀ B₀ hc0_not T hT hr c D hR_sub hcR hR_iso
            hy1_not hy2_not hy1d hy2d hy1c hy2c hy12)⟩
  have hfib : ∀ s ∈ LHS, (RHS.filter fun a => π a = s).card = 2 := by
    intro s hs
    obtain ⟨ψ⟩ := (mem_filter.mp hs).2
    have hcf := Q3_center_forced T₀ hT0 c₀ B₀ hc0_not hB0_ins_conn T hT hr c hecc hmax hBM hM_pos s ψ
    obtain ⟨hcs, hψc⟩ := hcf
    let R₀ : Finset V' := univ.filter fun x => ∃ (hx : x ∈ (s : Set V')), ∃ b, ψ ⟨x, hx⟩ = some (Sum.inl b)
    obtain ⟨b₀, hb₀, hadj0⟩ := hB0_root
    let rb : V' := (ψ.symm (some (Sum.inl ⟨b₀, hb₀⟩))).1
    have hrb_ne : rb ≠ c := fun h => by
      have := congrArg ψ (Subtype.ext h : ψ.symm (some (Sum.inl ⟨b₀, hb₀⟩)) = ⟨c, hcs⟩)
      rw [ψ.apply_symm_apply, hψc] at this; simp at this
    let D₀ := (T.induce {c}ᶜ).connectedComponentMk ⟨rb, hrb_ne⟩
    let a : V' := (ψ.symm (some (Sum.inr (Sum.inl ⟨r - 1, by omega⟩)))).1
    let b : V' := (ψ.symm (some (Sum.inr (Sum.inr ⟨r - 1, by omega⟩)))).1
    have hcR0 : c ∉ R₀ := fun h => by
      obtain ⟨hx, _, hxb⟩ := (mem_filter.mp h).2
      have : (⟨c, hcs⟩ : (s : Set V')) = ⟨c, hx⟩ := rfl
      rw [this, hψc] at hxb; simp at hxb
    have hR0_sub : R₀ ⊆ compSet T c D₀ := by
      intro x hx; obtain ⟨hxS, bx, hψx⟩ := (mem_filter.mp hx).2
      have hxc : x ≠ c := fun h => hcR0 (h ▸ hx)
      refine (mem_compSet_iff T c D₀ x).mpr ⟨hxc, ?_⟩
      obtain ⟨w⟩ := hB0_conn ⟨b₀, hb₀⟩ bx
      let g : T₀.induce (B₀ : Set U₀) →g T.induce {c}ᶜ :=
        ⟨fun z => ⟨(ψ.symm (some (Sum.inl z))).1, fun h => by
          have := congrArg ψ (Subtype.ext h : ψ.symm (some (Sum.inl z)) = ⟨c, hcs⟩)
          rw [ψ.apply_symm_apply, hψc] at this; simp at this⟩,
         @fun _ _ hadj => (ψ.symm.map_rel_iff).mpr hadj⟩
      have hreach : (T.induce {c}ᶜ).Reachable ⟨rb, hrb_ne⟩ ⟨x, hxc⟩ :=
        ⟨(w.map g).copy rfl (Subtype.ext (by
          change (ψ.symm (some (Sum.inl bx))).1 = x
          exact congrArg Subtype.val (ψ.symm_apply_eq.mpr hψx.symm)))⟩
      exact (mem_supp_iff D₀ _).mpr (sound hreach).symm
    have hR0_iso : RootedIso T c (insert c (R₀ : Set V')) T₀ c₀ (insert c₀ (B₀ : Set U₀)) := by
      have hR0_spec : ∀ x : V', x ∈ R₀ → ∃ (hx : x ∈ (s : Set V')) (b : ↥B₀), ψ ⟨x, hx⟩ = some (Sum.inl b) :=
        fun _ hxR => (mem_filter.mp hxR).2
      let toR : ↥(insert c (R₀ : Set V')) → ↥(insert c₀ (B₀ : Set U₀)) := fun x =>
        if hx : x.1 = c then ⟨c₀, Set.mem_insert _ _⟩
        else
          let hxR : x.1 ∈ R₀ := (mem_insert_iff.mp x.2).resolve_left hx
          let b := (hR0_spec x.1 hxR).choose_spec.choose
          ⟨b.1, Set.mem_insert_of_mem c₀ b.2⟩
      let invR : ↥(insert c₀ (B₀ : Set U₀)) → ↥(insert c (R₀ : Set V')) := fun z =>
        if hz : z.1 = c₀ then ⟨c, Set.mem_insert _ _⟩
        else
          let zb : ↥B₀ := ⟨z.1, (mem_insert_iff.mp z.2).resolve_left hz⟩
          ⟨(ψ.symm (some (Sum.inl zb))).1, Or.inr (mem_filter.mpr ⟨mem_univ _,
            ⟨(ψ.symm (some (Sum.inl zb))).2, zb, ψ.apply_symm_apply _⟩⟩)⟩
      have hto_eq : ∀ (x : ↥(insert c (R₀ : Set V'))) (hx : x.1 ≠ c),
          ∃ (hxS : x.1 ∈ (s : Set V')) (b : ↥B₀),
            ψ ⟨x.1, hxS⟩ = some (Sum.inl b) ∧ toR x = ⟨b.1, Set.mem_insert_of_mem c₀ b.2⟩ := by
        intro x hx
        let hxR : x.1 ∈ R₀ := (mem_insert_iff.mp x.2).resolve_left hx
        refine ⟨(hR0_spec x.1 hxR).choose, (hR0_spec x.1 hxR).choose_spec.choose,
          (hR0_spec x.1 hxR).choose_spec.choose_spec, ?_⟩
        simp [toR, hx]
      refine ⟨Set.mem_insert _ _, Set.mem_insert _ _, ⟨⟨toR, invR, ?_, ?_⟩, ?_⟩, ?_⟩
      · intro x
        by_cases hx : x.1 = c
        · apply Subtype.ext; simp [toR, invR, hx]
        · obtain ⟨hxS, b, hψb, hto⟩ := hto_eq x hx
          have hb_ne : b.1 ≠ c₀ := fun h => hc0_not (h ▸ b.2)
          apply Subtype.ext; rw [hto]; simp only [invR, dif_neg hb_ne]
          have hb_eq : (⟨b.1, (mem_insert_iff.mp (Set.mem_insert_of_mem c₀ b.2)).resolve_left hb_ne⟩ : ↥B₀) = b := Subtype.ext rfl
          rw [hb_eq]
          exact congrArg Subtype.val (ψ.symm_apply_eq.mpr hψb.symm)
      · intro z
        by_cases hz : z.1 = c₀
        · apply Subtype.ext; simp [invR, toR, hz]
        · obtain ⟨hxS, b, hψb, hto⟩ := hto_eq (invR z) (by
            intro h
            simp only [invR, dif_neg hz] at h
            have h1 := congrArg ψ (Subtype.ext h : ψ.symm (some (Sum.inl _)) = ⟨c, hcs⟩)
            rw [ψ.apply_symm_apply, hψc] at h1; simp at h1)
          apply Subtype.ext; rw [hto]
          have hinv1 : (invR z).1 = (ψ.symm (some (Sum.inl ⟨z.1, (mem_insert_iff.mp z.2).resolve_left hz⟩))).1 := by
            simp [invR, hz]
          have hinv2 : (⟨(invR z).1, hxS⟩ : ↥(s : Set V')) = ψ.symm (some (Sum.inl ⟨z.1, (mem_insert_iff.mp z.2).resolve_left hz⟩)) :=
            Subtype.ext hinv1
          rw [hinv2, ψ.apply_symm_apply] at hψb
          exact (congrArg Subtype.val (Sum.inl.inj (Option.some.inj hψb))).symm
      · intro x₁ x₂
        have hlift : ∀ x : ↥(insert c (R₀ : Set V')), ∃ (hx : x.1 ∈ (s : Set V')),
            ((toR x).1 = c₀ ∧ ψ ⟨x.1, hx⟩ = none) ∨
            (∃ b : ↥B₀, (toR x).1 = b.1 ∧ ψ ⟨x.1, hx⟩ = some (Sum.inl b)) := by
          intro x
          by_cases hx : x.1 = c
          · have hxS : x.1 ∈ (s : Set V') := by rw [hx]; exact hcs
            exact ⟨hxS, Or.inl ⟨by simp [toR, hx], by rw [show (⟨x.1, hxS⟩ : ↥(s : Set V')) = ⟨c, hcs⟩ from Subtype.ext hx, hψc]⟩⟩
          · obtain ⟨hxS, b, hψb, hto⟩ := hto_eq x hx
            exact ⟨hxS, Or.inr ⟨b, congrArg Subtype.val hto, hψb⟩⟩
        obtain ⟨hx1, H1⟩ := hlift x₁
        obtain ⟨hx2, H2⟩ := hlift x₂
        have hadj := (ψ.map_rel_iff (a := ⟨x₁.1, hx1⟩) (b := ⟨x₂.1, hx2⟩)).symm
        change T.Adj x₁.1 x₂.1 ↔ (Q3 T₀ c₀ B₀ r).Adj (ψ ⟨x₁.1, hx1⟩) (ψ ⟨x₂.1, hx2⟩) at hadj
        change T₀.Adj (toR x₁).1 (toR x₂).1 ↔ T.Adj x₁.1 x₂.1
        rw [hadj]
        rcases H1 with ⟨h1c0, h1n⟩ | ⟨b1, h1b, h1n⟩ <;> rcases H2 with ⟨h2c0, h2n⟩ | ⟨b2, h2b, h2n⟩
        · rw [h1c0, h2c0, h1n, h2n]; exact ⟨fun h => absurd h (T₀.loopless.irrefl _), False.elim⟩
        · rw [h1c0, h2b, h1n, h2n]; rfl
        · rw [h1b, h2c0, h1n, h2n]; exact T₀.adj_comm b1.1 c₀
        · rw [h1b, h2b, h1n, h2n]; rfl
      · apply Subtype.ext; simp [toR]
    have hac : a ≠ c := fun h => by
      have := congrArg ψ (Subtype.ext h : ψ.symm _ = ⟨c, hcs⟩)
      rw [ψ.apply_symm_apply, hψc] at this; simp at this
    have hbc : b ≠ c := fun h => by
      have := congrArg ψ (Subtype.ext h : ψ.symm _ = ⟨c, hcs⟩)
      rw [ψ.apply_symm_apply, hψc] at this; simp at this
    have had : T.dist c a = r := by
      obtain ⟨pr, hpr, hprlen, _⟩ := pathG_walk_up (r := r) (r - 1) (by omega)
      let pQ : (Q3 T₀ c₀ B₀ r).Walk none (some (Sum.inr (Sum.inl ⟨r - 1, by omega⟩))) :=
        Walk.cons (by simp [Q3] : (Q3 T₀ c₀ B₀ r).Adj none (some (Sum.inr (Sum.inl ⟨0, by omega⟩))))
          (pr.map ⟨fun j => some (Sum.inr (Sum.inl j)), @fun _ _ h => h⟩)
      have hpQ : pQ.IsPath :=
        (cons_isPath_iff _ _).mpr ⟨hpr.map (fun _ _ h => Sum.inl.inj (Sum.inr.inj (Option.some.inj h))), fun hm => by
          rw [Walk.support_map, List.mem_map] at hm; obtain ⟨j, _, hj⟩ := hm; simp at hj⟩
      let gS : T.induce (s : Set V') →g T := (Embedding.induce (s : Set V')).toHom
      let pT : T.Walk c a := ((pQ.map ψ.symm.toHom).map gS).copy
        (congrArg Subtype.val (ψ.symm_apply_eq.mpr hψc.symm)) rfl
      have hpT : pT.IsPath := (isPath_copy _ _ _).mpr ((hpQ.map ψ.symm.injective).map val_injective)
      rw [← isTree_dist_eq_length_of_isPath T hT pT hpT]
      have hlen : pT.length = pQ.length := (length_copy _ _ _).trans (by rw [length_map, length_map])
      have hq : pQ.length = 1 + pr.length := by dsimp only [pQ]; erw [length_cons, length_map]; omega
      omega
    have hbd : T.dist c b = r := by
      obtain ⟨pr, hpr, hprlen, _⟩ := pathG_walk_up (r := r) (r - 1) (by omega)
      let pQ : (Q3 T₀ c₀ B₀ r).Walk none (some (Sum.inr (Sum.inr ⟨r - 1, by omega⟩))) :=
        Walk.cons (by simp [Q3] : (Q3 T₀ c₀ B₀ r).Adj none (some (Sum.inr (Sum.inr ⟨0, by omega⟩))))
          (pr.map ⟨fun j => some (Sum.inr (Sum.inr j)), @fun _ _ h => h⟩)
      have hpQ : pQ.IsPath :=
        (cons_isPath_iff _ _).mpr ⟨hpr.map (fun _ _ h => Sum.inr.inj (Sum.inr.inj (Option.some.inj h))), fun hm => by
          rw [Walk.support_map, List.mem_map] at hm; obtain ⟨j, _, hj⟩ := hm; simp at hj⟩
      let gS : T.induce (s : Set V') →g T := (Embedding.induce (s : Set V')).toHom
      let pT : T.Walk c b := ((pQ.map ψ.symm.toHom).map gS).copy
        (congrArg Subtype.val (ψ.symm_apply_eq.mpr hψc.symm)) rfl
      have hpT : pT.IsPath := (isPath_copy _ _ _).mpr ((hpQ.map ψ.symm.injective).map val_injective)
      rw [← isTree_dist_eq_length_of_isPath T hT pT hpT]
      have hlen : pT.length = pQ.length := (length_copy _ _ _).trans (by rw [length_map, length_map])
      have hq : pQ.length = 1 + pr.length := by dsimp only [pQ]; erw [length_cons, length_map]; omega
      omega
    have ha_not_D : a ∉ compSet T c D₀ := by
      let a₁ : V' := (ψ.symm (some (Sum.inr (Sum.inl ⟨0, by omega⟩)))).1
      have ha1_ne : a₁ ≠ c := fun h => by
        have := congrArg ψ (Subtype.ext h : ψ.symm _ = ⟨c, hcs⟩); rw [ψ.apply_symm_apply, hψc] at this; simp at this
      have hadj_a1 : T.Adj c a₁ := by
        have hq : (Q3 T₀ c₀ B₀ r).Adj (ψ ⟨c, hcs⟩) (some (Sum.inr (Sum.inl ⟨0, by omega⟩))) := by rw [hψc]; rfl
        simpa [ψ.symm_apply_apply] using ψ.symm.map_rel_iff.mpr hq
      have hadj_rb : T.Adj c rb := by
        have hq : (Q3 T₀ c₀ B₀ r).Adj (ψ ⟨c, hcs⟩) (some (Sum.inl ⟨b₀, hb₀⟩)) := by rw [hψc]; exact hadj0
        simpa [ψ.symm_apply_apply] using ψ.symm.map_rel_iff.mpr hq
      have hne_rb_a1 : rb ≠ a₁ := fun h => by
        have h1 := ψ.symm.injective (Subtype.ext h : ψ.symm (some (Sum.inl ⟨b₀, hb₀⟩)) = ψ.symm (some (Sum.inr (Sum.inl ⟨0, by omega⟩))))
        simp at h1
      obtain ⟨pr, _, _, _⟩ := pathG_walk_up (r := r) (r - 1) (by omega)
      let gR : pathG r →g T.induce {c}ᶜ :=
        ⟨fun j => ⟨(ψ.symm (some (Sum.inr (Sum.inl j)))).1, fun h => by
          have := congrArg ψ (Subtype.ext h : ψ.symm _ = ⟨c, hcs⟩); rw [ψ.apply_symm_apply, hψc] at this; simp at this⟩,
         @fun _ _ hadj => (ψ.symm.map_rel_iff).mpr hadj⟩
      intro haD; obtain ⟨_, ha2⟩ := (mem_compSet_iff T c D₀ a).mp haD
      have ha1_D : a₁ ∈ compSet T c D₀ := (mem_compSet_iff T c D₀ a₁).mpr ⟨ha1_ne,
        (mem_supp_iff D₀ _).mpr ((sound ⟨pr.map gR⟩).trans
          ((mem_supp_iff D₀ _).mp ha2))⟩
      exact hne_rb_a1 ((compSet_root_adj T hT c D₀ ((mem_compSet_iff T c D₀ rb).mpr ⟨hrb_ne, rfl⟩) hadj_rb).trans
        (compSet_root_adj T hT c D₀ ha1_D hadj_a1).symm)
    have hb_not_D : b ∉ compSet T c D₀ := by
      let b₁ : V' := (ψ.symm (some (Sum.inr (Sum.inr ⟨0, by omega⟩)))).1
      have hb1_ne : b₁ ≠ c := fun h => by
        have := congrArg ψ (Subtype.ext h : ψ.symm _ = ⟨c, hcs⟩); rw [ψ.apply_symm_apply, hψc] at this; simp at this
      have hadj_b1 : T.Adj c b₁ := by
        have hq : (Q3 T₀ c₀ B₀ r).Adj (ψ ⟨c, hcs⟩) (some (Sum.inr (Sum.inr ⟨0, by omega⟩))) := by rw [hψc]; rfl
        simpa [ψ.symm_apply_apply] using ψ.symm.map_rel_iff.mpr hq
      have hadj_rb : T.Adj c rb := by
        have hq : (Q3 T₀ c₀ B₀ r).Adj (ψ ⟨c, hcs⟩) (some (Sum.inl ⟨b₀, hb₀⟩)) := by rw [hψc]; exact hadj0
        simpa [ψ.symm_apply_apply] using ψ.symm.map_rel_iff.mpr hq
      have hne_rb_b1 : rb ≠ b₁ := fun h => by
        have h1 := ψ.symm.injective (Subtype.ext h : ψ.symm (some (Sum.inl ⟨b₀, hb₀⟩)) = ψ.symm (some (Sum.inr (Sum.inr ⟨0, by omega⟩))))
        simp at h1
      obtain ⟨pr, _, _, _⟩ := pathG_walk_up (r := r) (r - 1) (by omega)
      let gR : pathG r →g T.induce {c}ᶜ :=
        ⟨fun j => ⟨(ψ.symm (some (Sum.inr (Sum.inr j)))).1, fun h => by
          have := congrArg ψ (Subtype.ext h : ψ.symm _ = ⟨c, hcs⟩); rw [ψ.apply_symm_apply, hψc] at this; simp at this⟩,
         @fun _ _ hadj => (ψ.symm.map_rel_iff).mpr hadj⟩
      intro hbD; obtain ⟨_, hb2⟩ := (mem_compSet_iff T c D₀ b).mp hbD
      have hb1_D : b₁ ∈ compSet T c D₀ := (mem_compSet_iff T c D₀ b₁).mpr ⟨hb1_ne,
        (mem_supp_iff D₀ _).mpr ((sound ⟨pr.map gR⟩).trans
          ((mem_supp_iff D₀ _).mp hb2))⟩
      exact hne_rb_b1 ((compSet_root_adj T hT c D₀ ((mem_compSet_iff T c D₀ rb).mpr ⟨hrb_ne, rfl⟩) hadj_rb).trans
        (compSet_root_adj T hT c D₀ hb1_D hadj_b1).symm)
    have hab_comp : (T.induce {c}ᶜ).connectedComponentMk ⟨a, hac⟩ ≠
        (T.induce {c}ᶜ).connectedComponentMk ⟨b, hbc⟩ := by
      let a₁ : V' := (ψ.symm (some (Sum.inr (Sum.inl ⟨0, by omega⟩)))).1
      let b₁ : V' := (ψ.symm (some (Sum.inr (Sum.inr ⟨0, by omega⟩)))).1
      have ha1_ne : a₁ ≠ c := fun h => by
        have := congrArg ψ (Subtype.ext h : ψ.symm _ = ⟨c, hcs⟩); rw [ψ.apply_symm_apply, hψc] at this; simp at this
      have hb1_ne : b₁ ≠ c := fun h => by
        have := congrArg ψ (Subtype.ext h : ψ.symm _ = ⟨c, hcs⟩); rw [ψ.apply_symm_apply, hψc] at this; simp at this
      have hadj_a1 : T.Adj c a₁ := by
        have hq : (Q3 T₀ c₀ B₀ r).Adj (ψ ⟨c, hcs⟩) (some (Sum.inr (Sum.inl ⟨0, by omega⟩))) := by rw [hψc]; rfl
        simpa [ψ.symm_apply_apply] using ψ.symm.map_rel_iff.mpr hq
      have hadj_b1 : T.Adj c b₁ := by
        have hq : (Q3 T₀ c₀ B₀ r).Adj (ψ ⟨c, hcs⟩) (some (Sum.inr (Sum.inr ⟨0, by omega⟩))) := by rw [hψc]; rfl
        simpa [ψ.symm_apply_apply] using ψ.symm.map_rel_iff.mpr hq
      have hne_a1_b1 : a₁ ≠ b₁ := fun h => by
        have h1 := ψ.symm.injective (Subtype.ext h : ψ.symm (some (Sum.inr (Sum.inl ⟨0, by omega⟩))) =
          ψ.symm (some (Sum.inr (Sum.inr ⟨0, by omega⟩))))
        simp at h1
      obtain ⟨pr, _, _, _⟩ := pathG_walk_up (r := r) (r - 1) (by omega)
      let g1 : pathG r →g T.induce {c}ᶜ :=
        ⟨fun j => ⟨(ψ.symm (some (Sum.inr (Sum.inl j)))).1, fun h => by
          have := congrArg ψ (Subtype.ext h : ψ.symm _ = ⟨c, hcs⟩); rw [ψ.apply_symm_apply, hψc] at this; simp at this⟩,
         @fun _ _ hadj => (ψ.symm.map_rel_iff).mpr hadj⟩
      let g2 : pathG r →g T.induce {c}ᶜ :=
        ⟨fun j => ⟨(ψ.symm (some (Sum.inr (Sum.inr j)))).1, fun h => by
          have := congrArg ψ (Subtype.ext h : ψ.symm _ = ⟨c, hcs⟩); rw [ψ.apply_symm_apply, hψc] at this; simp at this⟩,
         @fun _ _ hadj => (ψ.symm.map_rel_iff).mpr hadj⟩
      intro heq
      let Da := (T.induce {c}ᶜ).connectedComponentMk ⟨a, hac⟩
      have ha1_Da : a₁ ∈ compSet T c Da := (mem_compSet_iff T c Da a₁).mpr ⟨ha1_ne,
        (mem_supp_iff Da _).mpr (sound ⟨pr.map g1⟩)⟩
      have hb1_Da : b₁ ∈ compSet T c Da := (mem_compSet_iff T c Da b₁).mpr ⟨hb1_ne,
        (mem_supp_iff Da _).mpr ((sound ⟨pr.map g2⟩).trans heq.symm)⟩
      exact hne_a1_b1 ((compSet_root_adj T hT c Da ha1_Da hadj_a1).trans
        (compSet_root_adj T hT c Da hb1_Da hadj_b1).symm)
    have hab_ne : a ≠ b := fun h => hab_comp (by simp only [h])
    have hs_dist_r : ∀ z ∈ s, T.dist c z = r → z = a ∨ z = b := by
      intro z hzs hzd
      cases hψz : ψ ⟨z, hzs⟩ with
      | none =>
        have hzc : z = c := congrArg Subtype.val (ψ.injective (hψz.trans hψc.symm))
        rw [hzc, SimpleGraph.dist_self] at hzd; omega
      | some v => cases v with
        | inl bx =>
          obtain ⟨h1R, h1B, φR, hφRc⟩ := hR0_iso
          have hzR : z ∈ R₀ := mem_filter.mpr ⟨mem_univ _, ⟨hzs, bx, hψz⟩⟩
          obtain ⟨w0, hw0, hw0len⟩ := hT0.connected.exists_path_of_dist c₀ ((φR ⟨z, Set.mem_insert_of_mem c hzR⟩).1)
          have : Nonempty (insert c (R₀ : Set V') : Set V') := ⟨⟨c, Set.mem_insert _ _⟩⟩
          have hR_tree : (T.induce (insert c (R₀ : Set V'))).IsTree := by
            refine ⟨?_, hT.isAcyclic.induce _⟩
            have h1 := hB0_ins_conn
            exact ⟨fun u v => ⟨((h1 (φR u) (φR v)).some.map φR.symm.toHom).copy
              (φR.symm_apply_apply u) (φR.symm_apply_apply v)⟩⟩
          have hz_le : T.dist c z ≤ (T.induce (insert c (R₀ : Set V'))).dist
              ⟨c, Set.mem_insert _ _⟩ ⟨z, Set.mem_insert_of_mem c hzR⟩ := by
            obtain ⟨q, hq, hqlen⟩ := hR_tree.connected.exists_path_of_dist ⟨c, Set.mem_insert _ _⟩
              ⟨z, Set.mem_insert_of_mem c hzR⟩
            let g : T.induce (insert c (R₀ : Set V')) →g T := (Embedding.induce _).toHom
            rw [← hqlen, ← length_map (f := g)]
            exact T.dist_le (q.map g)
          have hφ_dist : (T.induce (insert c (R₀ : Set V'))).dist ⟨c, Set.mem_insert _ _⟩
              ⟨z, Set.mem_insert_of_mem c hzR⟩ =
              (T₀.induce (insert c₀ (B₀ : Set U₀))).dist ⟨c₀, Set.mem_insert _ _⟩
                (φR ⟨z, Set.mem_insert_of_mem c hzR⟩) := by
            have := iso_dist_eq _ _ φR ⟨c, h1R⟩ ⟨z, Set.mem_insert_of_mem c hzR⟩
            simpa [hφRc] using this.symm
          have hB0_tree : (T₀.induce (insert c₀ (B₀ : Set U₀))).IsTree := ⟨hB0_ins_conn, hT0.isAcyclic.induce _⟩
          rw [hφ_dist, dist_induce_eq_of_isTree T₀ hT0 _ hB0_tree] at hz_le
          dsimp only at hz_le
          have hm := (φR ⟨z, Set.mem_insert_of_mem c hzR⟩).2
          rcases mem_insert_iff.mp hm with h1c0 | h1B0
          · rw [h1c0, SimpleGraph.dist_self] at hz_le; omega
          · have := hB0_no_r _ h1B0; omega
        | inr lr =>
          cases lr with
          | inl j =>
            have hdj : T.dist c z = j.val + 1 := by
              obtain ⟨pj, hpj, hpjlen, _⟩ := pathG_walk_up j.val j.isLt
              let pQ : (Q3 T₀ c₀ B₀ r).Walk none (some (Sum.inr (Sum.inl j))) :=
                Walk.cons (by change (Q3 T₀ c₀ B₀ r).Adj _ _; rfl)
                  (pj.map ⟨fun m => some (Sum.inr (Sum.inl m)), @fun _ _ h => h⟩)
              have hpQ : pQ.IsPath := (cons_isPath_iff _ _).mpr ⟨hpj.map (fun _ _ h => Sum.inl.inj (Sum.inr.inj (Option.some.inj h))),
                fun hm => by rw [Walk.support_map, List.mem_map] at hm; obtain ⟨m, _, hm⟩ := hm; simp at hm⟩
              let gS : T.induce (s : Set V') →g T := (Embedding.induce (s : Set V')).toHom
              let pT : T.Walk c z := ((pQ.map ψ.symm.toHom).map gS).copy
                (congrArg Subtype.val (ψ.symm_apply_eq.mpr hψc.symm))
                (congrArg Subtype.val (ψ.symm_apply_eq.mpr hψz.symm))
              have hpT : pT.IsPath := (isPath_copy _ _ _).mpr ((hpQ.map ψ.symm.injective).map val_injective)
              rw [← isTree_dist_eq_length_of_isPath T hT pT hpT]
              have hlen : pT.length = pQ.length := (length_copy _ _ _).trans (by rw [length_map, length_map])
              have hq : pQ.length = 1 + pj.length := by dsimp only [pQ]; erw [length_cons, length_map]; omega
              omega
            have hj_eq : j = ⟨r - 1, by omega⟩ := Fin.ext (by dsimp; omega)
            rw [hj_eq] at hψz
            left
            exact congrArg Subtype.val ((ψ.symm_apply_eq.mpr hψz.symm).symm)
          | inr j =>
            have hdj : T.dist c z = j.val + 1 := by
              obtain ⟨pj, hpj, hpjlen, _⟩ := pathG_walk_up j.val j.isLt
              let pQ : (Q3 T₀ c₀ B₀ r).Walk none (some (Sum.inr (Sum.inr j))) :=
                Walk.cons (by change (Q3 T₀ c₀ B₀ r).Adj _ _; rfl)
                  (pj.map ⟨fun m => some (Sum.inr (Sum.inr m)), @fun _ _ h => h⟩)
              have hpQ : pQ.IsPath := (cons_isPath_iff _ _).mpr ⟨hpj.map (fun _ _ h => Sum.inr.inj (Sum.inr.inj (Option.some.inj h))),
                fun hm => by rw [Walk.support_map, List.mem_map] at hm; obtain ⟨m, _, hm⟩ := hm; simp at hm⟩
              let gS : T.induce (s : Set V') →g T := (Embedding.induce (s : Set V')).toHom
              let pT : T.Walk c z := ((pQ.map ψ.symm.toHom).map gS).copy
                (congrArg Subtype.val (ψ.symm_apply_eq.mpr hψc.symm))
                (congrArg Subtype.val (ψ.symm_apply_eq.mpr hψz.symm))
              have hpT : pT.IsPath := (isPath_copy _ _ _).mpr ((hpQ.map ψ.symm.injective).map val_injective)
              rw [← isTree_dist_eq_length_of_isPath T hT pT hpT]
              have hlen : pT.length = pQ.length := (length_copy _ _ _).trans (by rw [length_map, length_map])
              have hq : pQ.length = 1 + pj.length := by dsimp only [pQ]; erw [length_cons, length_map]; omega
              omega
            have hj_eq : j = ⟨r - 1, by omega⟩ := Fin.ext (by dsimp; omega)
            rw [hj_eq] at hψz
            right
            exact congrArg Subtype.val ((ψ.symm_apply_eq.mpr hψz.symm).symm)
    have hK_eq_gen : ∀ (tag : Bool),
        let emb : Fin r → Fin r ⊕ Fin r := fun j => if tag then Sum.inr j else Sum.inl j
        let endPt : V' := if tag then b else a
        have hendDist : T.dist c endPt = r := if h : tag then by simp [endPt, h, hbd] else by simp [endPt, h, had]
        univ.filter (fun x => ∃ (hx : x ∈ (s : Set V')), ∃ j, ψ ⟨x, hx⟩ = some (Sum.inr (emb j))) =
          pathTail T hT c endPt := by
      intro tag emb endPt hendDist
      let K := univ.filter fun x => ∃ (hx : x ∈ (s : Set V')), ∃ j, ψ ⟨x, hx⟩ = some (Sum.inr (emb j))
      have hcK : c ∉ K := fun hm => by
        obtain ⟨hx, _, hxj⟩ := (mem_filter.mp hm).2
        have : (⟨c, hcs⟩ : (s : Set V')) = ⟨c, hx⟩ := rfl
        rw [this, hψc] at hxj; simp at hxj
      have hemb_inj : Injective emb := fun j₁ j₂ h => by
        cases htag : tag <;> simp [emb, htag] at h <;> exact h
      have hK_card : K.card = r := by
        rw [← card_coe K, ← card_fin r]
        refine card_congr ⟨fun x => (mem_filter.mp x.2).2.choose_spec.choose,
          fun i => ⟨(ψ.symm (some (Sum.inr (emb i)))).1, mem_filter.mpr ⟨mem_univ _,
            ⟨(ψ.symm (some (Sum.inr (emb i)))).2, i, ψ.apply_symm_apply _⟩⟩⟩,
          fun x => by
            dsimp only; have hm := (mem_filter.mp x.2).2
            exact Subtype.ext (congrArg (fun z : (s : Set V') => z.1) (ψ.symm_apply_eq.mpr hm.choose_spec.choose_spec.symm)),
          fun i => by
            dsimp only
            set z := (ψ.symm (some (Sum.inr (emb i)))).1
            have hz : z ∈ K := mem_filter.mpr ⟨mem_univ _,
              ⟨(ψ.symm (some (Sum.inr (emb i)))).2, i, ψ.apply_symm_apply _⟩⟩
            exact hemb_inj (Sum.inr.inj (Option.some.inj
              (((mem_filter.mp hz).2.choose_spec.choose_spec).symm.trans (ψ.apply_symm_apply _))))⟩
      have hK_spec : ∀ x : V', x ∈ K → ∃ (hx : x ∈ (s : Set V')) (j : Fin r), ψ ⟨x, hx⟩ = some (Sum.inr (emb j)) :=
        fun _ hxK => (mem_filter.mp hxK).2
      let toK : ↥(insert c (K : Set V')) → Fin (r + 1) := fun x =>
        if hx : x.1 = c then ⟨0, Nat.zero_lt_succ r⟩
        else
          let j := (hK_spec x.1 ((mem_insert_iff.mp x.2).resolve_left hx)).choose_spec.choose
          ⟨j.val + 1, by omega⟩
      let invK : Fin (r + 1) → ↥(insert c (K : Set V')) := fun i =>
        if hi : i.val = 0 then ⟨c, Set.mem_insert _ _⟩
        else
          let j : Fin r := ⟨i.val - 1, by omega⟩
          ⟨(ψ.symm (some (Sum.inr (emb j)))).1, Or.inr (mem_filter.mpr ⟨mem_univ _,
            ⟨(ψ.symm (some (Sum.inr (emb j)))).2, j, ψ.apply_symm_apply _⟩⟩)⟩
      have htoK_eq : ∀ (x : ↥(insert c (K : Set V'))) (hx : x.1 ≠ c),
          ∃ (hxS : x.1 ∈ (s : Set V')) (j : Fin r),
            ψ ⟨x.1, hxS⟩ = some (Sum.inr (emb j)) ∧ toK x = ⟨j.val + 1, by omega⟩ := by
        intro x hx
        let hxK : x.1 ∈ K := (mem_insert_iff.mp x.2).resolve_left hx
        refine ⟨(hK_spec x.1 hxK).choose, (hK_spec x.1 hxK).choose_spec.choose,
          (hK_spec x.1 hxK).choose_spec.choose_spec, ?_⟩
        simp [toK, hx]
      let ψK : T.induce (insert c (K : Set V')) ≃g pathG (r + 1) :=
        ⟨⟨toK, invK,
          fun x => by
            by_cases hx : x.1 = c
            · apply Subtype.ext; simp [toK, invK, hx]
            · obtain ⟨hxS, j, hψj, hto⟩ := htoK_eq x hx
              apply Subtype.ext; rw [hto]
              have hne0 : j.val + 1 ≠ 0 := by omega
              simp only [invK, dif_neg hne0]
              have hj_eq : (⟨j.val + 1 - 1, by omega⟩ : Fin r) = j := Fin.ext rfl
              rw [hj_eq]
              exact congrArg Subtype.val (ψ.symm_apply_eq.mpr hψj.symm),
          fun i => by
            by_cases hi : i.val = 0
            · apply Fin.ext; simp only [invK, dif_pos hi, toK, dif_pos rfl]; exact hi.symm
            · obtain ⟨hxS, j, hψj, hto⟩ := htoK_eq (invK i) (by
                intro h; simp only [invK, dif_neg hi] at h
                have h1 := congrArg ψ (Subtype.ext h : ψ.symm (some (Sum.inr (emb _))) = ⟨c, hcs⟩)
                rw [ψ.apply_symm_apply, hψc] at h1; simp at h1)
              rw [hto]; apply Fin.ext
              have hinv1 : (invK i).1 = (ψ.symm (some (Sum.inr (emb ⟨i.val - 1, by omega⟩)))).1 := by
                simp only [invK, dif_neg hi]
              have hinv2 : (⟨(invK i).1, hxS⟩ : ↥(s : Set V')) = ψ.symm (some (Sum.inr (emb ⟨i.val - 1, by omega⟩))) :=
                Subtype.ext hinv1
              rw [hinv2, ψ.apply_symm_apply] at hψj
              have hj := hemb_inj (Sum.inr.inj (Option.some.inj hψj))
              have hv := congrArg Fin.val hj
              dsimp at hv ⊢; omega⟩,
          by
            intro x₁ x₂
            have hlift : ∀ x : ↥(insert c (K : Set V')), ∃ (hx : x.1 ∈ (s : Set V')),
                ((toK x).val = 0 ∧ ψ ⟨x.1, hx⟩ = none) ∨
                (∃ j : Fin r, (toK x).val = j.val + 1 ∧ ψ ⟨x.1, hx⟩ = some (Sum.inr (emb j))) := by
              intro x
              by_cases hx : x.1 = c
              · have hxS : x.1 ∈ (s : Set V') := by rw [hx]; exact hcs
                exact ⟨hxS, Or.inl ⟨by simp [toK, hx], by rw [show (⟨x.1, hxS⟩ : ↥(s : Set V')) = ⟨c, hcs⟩ from Subtype.ext hx, hψc]⟩⟩
              · obtain ⟨hxS, j, hψj, hto⟩ := htoK_eq x hx
                exact ⟨hxS, Or.inr ⟨j, congrArg Fin.val hto, hψj⟩⟩
            obtain ⟨hx1, H1⟩ := hlift x₁
            obtain ⟨hx2, H2⟩ := hlift x₂
            have hadj := (ψ.map_rel_iff (a := ⟨x₁.1, hx1⟩) (b := ⟨x₂.1, hx2⟩)).symm
            change T.Adj x₁.1 x₂.1 ↔ (Q3 T₀ c₀ B₀ r).Adj (ψ ⟨x₁.1, hx1⟩) (ψ ⟨x₂.1, hx2⟩) at hadj
            rw [iff_comm]
            change T.Adj x₁.1 x₂.1 ↔ (pathG (r + 1)).Adj (toK x₁) (toK x₂)
            rw [hadj]
            rcases H1 with ⟨h1z, h1n⟩ | ⟨j1, h1v, h1n⟩ <;> rcases H2 with ⟨h2z, h2n⟩ | ⟨j2, h2v, h2n⟩
            · rw [h1n, h2n]; dsimp only [Q3, pathG]; simp [h1z, h2z]
            · rw [h1n, h2n]; cases htag : tag <;> simp [emb, htag, Q3, pathG, h1z, h2v] <;> omega
            · rw [h1n, h2n]; cases htag : tag <;> simp [emb, htag, Q3, pathG, h1v, h2z] <;> omega
            · rw [h1n, h2n]
              cases htag : tag <;> simp only [emb, htag, Q3, pathG, h1v, h2v] <;>
                exact ⟨fun h => by rcases h with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)],
                       fun h => by rcases h with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)]⟩⟩
      refine pathTail_eq_of_iso T hT hr c endPt hendDist K hcK hK_card ψK ?_ ?_
      · apply Fin.ext; simp [ψK, toK]
      · have hendK : endPt ∈ K := by
          refine mem_filter.mpr ⟨mem_univ _, ?_⟩
          by_cases htag : tag
          · simp only [endPt, emb, htag, if_true]
            exact ⟨(ψ.symm (some (Sum.inr (Sum.inr ⟨r - 1, by omega⟩)))).2, ⟨r - 1, by omega⟩, ψ.apply_symm_apply _⟩
          · simp only [endPt, emb, htag, Bool.false_eq_true, if_false]
            exact ⟨(ψ.symm (some (Sum.inr (Sum.inl ⟨r - 1, by omega⟩)))).2, ⟨r - 1, by omega⟩, ψ.apply_symm_apply _⟩
        refine ⟨hendK, ?_⟩
        apply Fin.ext
        have hend_ne : endPt ≠ c := fun h => hcK (h ▸ hendK)
        obtain ⟨hxS, j, hψj, hto⟩ := htoK_eq ⟨endPt, Set.mem_insert_of_mem c hendK⟩ hend_ne
        have hψe : ψ ⟨endPt, hxS⟩ = some (Sum.inr (emb ⟨r - 1, by omega⟩)) := by
          have hend1 : endPt = (ψ.symm (some (Sum.inr (emb ⟨r - 1, by omega⟩)))).1 := by
            by_cases htag : tag <;> simp [endPt, emb, htag] <;> rfl
          have hsub : (⟨endPt, hxS⟩ : ↥(s : Set V')) = ψ.symm (some (Sum.inr (emb ⟨r - 1, by omega⟩))) :=
            Subtype.ext hend1
          rw [hsub, ψ.apply_symm_apply]
        have hj := hemb_inj (Sum.inr.inj (Option.some.inj (hψj.symm.trans hψe)))
        simp only [ψK, RelIso.coe_fn_mk, Equiv.coe_fn_mk]; rw [hto]
        have hv := congrArg Fin.val hj
        dsimp at hv ⊢; omega
    have hK1_eq : univ.filter (fun x => ∃ (hx : x ∈ (s : Set V')), ∃ j, ψ ⟨x, hx⟩ = some (Sum.inr (Sum.inl j))) =
        pathTail T hT c a := hK_eq_gen false
    have hK2_eq : univ.filter (fun x => ∃ (hx : x ∈ (s : Set V')), ∃ j, ψ ⟨x, hx⟩ = some (Sum.inr (Sum.inr j))) =
        pathTail T hT c b := hK_eq_gen true
    have hs_eq_ab : s = insert c (R₀ ∪ pathTail T hT c a ∪ pathTail T hT c b) := by
      rw [← hK1_eq, ← hK2_eq]
      ext x; constructor
      · intro hxS
        by_cases hxc : x = c
        · rw [hxc]; exact mem_insert_self c _
        · refine mem_insert_of_mem ?_
          cases hψx : ψ ⟨x, hxS⟩ with
          | none => exact False.elim (hxc (congrArg Subtype.val (ψ.injective (hψx.trans hψc.symm))))
          | some v => cases v with
            | inl bx => exact mem_union_left _ (mem_union_left _
                (mem_filter.mpr ⟨mem_univ _, ⟨hxS, bx, hψx⟩⟩))
            | inr lr => cases lr with
              | inl j => exact mem_union_left _ (mem_union_right _
                  (mem_filter.mpr ⟨mem_univ _, ⟨hxS, j, hψx⟩⟩))
              | inr j => exact mem_union_right _ (mem_filter.mpr
                  ⟨mem_univ _, ⟨hxS, j, hψx⟩⟩)
      · intro hx
        rcases mem_insert.mp hx with rfl | hx
        · exact hcs
        · rcases mem_union.mp hx with hx1 | hx2
          · rcases mem_union.mp hx1 with hxR | hxK1
            · exact (mem_filter.mp hxR).2.choose
            · exact (mem_filter.mp hxK1).2.choose
          · exact (mem_filter.mp hx2).2.choose
    have hR0_mem : R₀ ∈ SubRoots D₀ := mem_filter.mpr ⟨mem_univ _, hR0_sub, hcR0, hR0_iso⟩
    have hfib_set : RHS.filter (fun t => π t = s) =
        {⟨D₀, (R₀, a, b)⟩, ⟨D₀, (R₀, b, a)⟩} := by
      ext ⟨D', ⟨R', y₁, y₂⟩⟩
      rw [mem_filter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hmR, hπ⟩
        simp only [RHS, mem_sigma, mem_univ, true_and, mem_product,
          SubRoots, PairsOut, mem_filter] at hmR
        obtain ⟨⟨hR'_sub, hcR', hR'_iso⟩, hy1_not, hy2_not, hy1d, hy2d, hy1c, hy2c, hy12⟩ := hmR
        have hy1_s : y₁ ∈ s := by
          rw [← hπ]; refine mem_insert_of_mem (mem_union_left _ (mem_union_right _ ?_))
          exact (pathTail_spec T hT hr c y₁ hy1d).2.1
        have hy2_s : y₂ ∈ s := by
          rw [← hπ]; refine mem_insert_of_mem (mem_union_right _ ?_)
          exact (pathTail_spec T hT hr c y₂ hy2d).2.1
        have h_pair : (y₁ = a ∧ y₂ = b) ∨ (y₁ = b ∧ y₂ = a) := by
          rcases hs_dist_r y₁ hy1_s hy1d with rfl | rfl <;> rcases hs_dist_r y₂ hy2_s hy2d with rfl | rfl
          · exact False.elim (hy12 rfl)
          · exact Or.inl ⟨rfl, rfl⟩
          · exact Or.inr ⟨rfl, rfl⟩
          · exact False.elim (hy12 rfl)
        have hU : R' ∪ (pathTail T hT c y₁ ∪ pathTail T hT c y₂) =
            R₀ ∪ (pathTail T hT c a ∪ pathTail T hT c b) := by
          have hs_eq' : s = insert c (R₀ ∪ (pathTail T hT c a ∪ pathTail T hT c b)) := by
            rw [← union_assoc]; exact hs_eq_ab
          have hπ' : insert c (R' ∪ (pathTail T hT c y₁ ∪ pathTail T hT c y₂)) =
              insert c (R₀ ∪ (pathTail T hT c a ∪ pathTail T hT c b)) := by
            rw [← union_assoc, ← hs_eq']; exact hπ
          have hz_sp1 := pathTail_spec T hT hr c y₁ hy1d
          have hz_sp2 := pathTail_spec T hT hr c y₂ hy2d
          have hz_spa := pathTail_spec T hT hr c a had
          have hz_spb := pathTail_spec T hT hr c b hbd
          ext z; have hm := Finset.ext_iff.mp hπ' z
          constructor <;> intro hz
          · have hzc : z ≠ c := by
              rcases mem_union.mp hz with h | h
              · exact fun he => hcR' (he ▸ h)
              · rcases mem_union.mp h with h | h <;> [exact fun he => hz_sp1.1 (he ▸ h); exact fun he => hz_sp2.1 (he ▸ h)]
            exact (mem_insert.mp (hm.mp (mem_insert_of_mem hz))).resolve_left hzc
          · have hzc : z ≠ c := by
              rcases mem_union.mp hz with h | h
              · exact fun he => hcR0 (he ▸ h)
              · rcases mem_union.mp h with h | h <;> [exact fun he => hz_spa.1 (he ▸ h); exact fun he => hz_spb.1 (he ▸ h)]
            exact (mem_insert.mp (hm.mpr (mem_insert_of_mem hz))).resolve_left hzc
        have hK_eq : pathTail T hT c y₁ ∪ pathTail T hT c y₂ = pathTail T hT c a ∪ pathTail T hT c b := by
          rcases h_pair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [rfl; exact Finset.union_comm _ _]
        have hR_disj : Disjoint R' (pathTail T hT c y₁ ∪ pathTail T hT c y₂) := by
          rw [Finset.disjoint_union_right]
          let Dy1 := (T.induce {c}ᶜ).connectedComponentMk ⟨y₁, hy1c⟩
          let Dy2 := (T.induce {c}ᶜ).connectedComponentMk ⟨y₂, hy2c⟩
          refine ⟨(compSet_disjoint T c (fun h => hy1_not (by rw [h]; exact (mem_compSet_iff T c Dy1 y₁).mpr ⟨hy1c, rfl⟩))).mono
              hR'_sub (pathTail_spec T hT hr c y₁ hy1d).2.2.2.1,
            (compSet_disjoint T c (fun h => hy2_not (by rw [h]; exact (mem_compSet_iff T c Dy2 y₂).mpr ⟨hy2c, rfl⟩))).mono
              hR'_sub (pathTail_spec T hT hr c y₂ hy2d).2.2.2.1⟩
        have hR0_disj : Disjoint R₀ (pathTail T hT c a ∪ pathTail T hT c b) := by
          rw [Finset.disjoint_union_right]
          let Da := (T.induce {c}ᶜ).connectedComponentMk ⟨a, hac⟩
          let Db := (T.induce {c}ᶜ).connectedComponentMk ⟨b, hbc⟩
          refine ⟨(compSet_disjoint T c (fun h => ha_not_D (by rw [h]; exact (mem_compSet_iff T c Da a).mpr ⟨hac, rfl⟩))).mono
              hR0_sub (pathTail_spec T hT hr c a had).2.2.2.1,
            (compSet_disjoint T c (fun h => hb_not_D (by rw [h]; exact (mem_compSet_iff T c Db b).mpr ⟨hbc, rfl⟩))).mono
              hR0_sub (pathTail_spec T hT hr c b hbd).2.2.2.1⟩
        have hRR0 : R' = R₀ := by
          rw [← Finset.union_sdiff_cancel_right hR_disj, hU, hK_eq, Finset.union_sdiff_cancel_right hR0_disj]
        have hDD0 : D' = D₀ := by
          have hxR0 : ∃ x, x ∈ R₀ := ⟨rb, mem_filter.mpr ⟨mem_univ _,
            ⟨(ψ.symm (some (Sum.inl ⟨b₀, hb₀⟩))).2, ⟨b₀, hb₀⟩, ψ.apply_symm_apply _⟩⟩⟩
          obtain ⟨x, hx⟩ := hxR0
          obtain ⟨h1, h2⟩ := (mem_compSet_iff T c D' x).mp (hR'_sub (hRR0 ▸ hx))
          obtain ⟨h3, h4⟩ := (mem_compSet_iff T c D₀ x).mp (hR0_sub hx)
          exact ((mem_supp_iff D' ⟨x, h1⟩).mp h2).symm.trans ((mem_supp_iff D₀ ⟨x, h3⟩).mp h4)
        subst hDD0; subst hRR0
        rcases h_pair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (h | h) <;> cases h
        · refine ⟨mem_sigma.mpr ⟨mem_univ _, mem_product.mpr ⟨hR0_mem,
            mem_filter.mpr ⟨mem_univ _, ha_not_D, hb_not_D, had, hbd, hac, hbc, hab_comp⟩⟩⟩,
            hs_eq_ab.symm⟩
        · refine ⟨mem_sigma.mpr ⟨mem_univ _, mem_product.mpr ⟨hR0_mem,
            mem_filter.mpr ⟨mem_univ _, hb_not_D, ha_not_D, hbd, had, hbc, hac, hab_comp.symm⟩⟩⟩, ?_⟩
          dsimp only [π]; rw [union_assoc, Finset.union_comm (pathTail T hT c b), ← union_assoc]
          exact hs_eq_ab.symm
    have hpair_ne : (⟨D₀, (R₀, a, b)⟩ : Σ D : (T.induce {c}ᶜ).ConnectedComponent, Finset V' × V' × V') ≠
        ⟨D₀, (R₀, b, a)⟩ := by
      intro h
      have h1 := congrArg (fun t => t.2.2.1) h
      exact hab_ne h1
    rw [hfib_set, card_pair hpair_ne]
  have := Finset.card_eq_sum_card_fiberwise hmaps
  rw [sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, mul_comm] at this
  exact this.symm
private lemma path2r1_induce_union_iso {V' : Type} [Fintype V']
    (T : SimpleGraph V') (hT : T.IsTree) {r : ℕ} (hr : 2 ≤ r) (c : V')
    {y₁ y₂ : V'} (hy1d : T.dist c y₁ = r) (hy2d : T.dist c y₂ = r)
    (hy1c : y₁ ≠ c) (hy2c : y₂ ≠ c)
    (hy12 : (T.induce {c}ᶜ).connectedComponentMk ⟨y₁, hy1c⟩ ≠
      (T.induce {c}ᶜ).connectedComponentMk ⟨y₂, hy2c⟩) :
    Nonempty (T.induce (insert c (pathTail T hT c y₁ ∪ pathTail T hT c y₂ : Set V')) ≃g pathG (2 * r + 1)) := by
  have hsp1 := pathTail_spec T hT hr c y₁ hy1d
  have hsp2 := pathTail_spec T hT hr c y₂ hy2d
  let K₁ := pathTail T hT c y₁
  let K₂ := pathTail T hT c y₂
  let D₁ := (T.induce {c}ᶜ).connectedComponentMk ⟨y₁, hy1c⟩
  let D₂ := (T.induce {c}ᶜ).connectedComponentMk ⟨y₂, hy2c⟩
  have hdisj : Disjoint K₁ K₂ := (compSet_disjoint T c hy12).mono hsp1.2.2.2.1 hsp2.2.2.2.1
  obtain ⟨φ1, hφ1c, _⟩ := hsp1.2.2.2.2.2
  obtain ⟨φ2, hφ2c, _⟩ := hsp2.2.2.2.2.2
  have hφ1_pos : ∀ (z : V') (hz : z ∈ K₁), 0 < (φ1 ⟨z, Set.mem_insert_of_mem c hz⟩).val := fun z hz => by
    by_contra h0
    have heqv : z = c := congrArg Subtype.val (φ1.injective ((Fin.ext (Nat.eq_zero_of_not_pos h0) :
      φ1 ⟨z, Set.mem_insert_of_mem c hz⟩ = ⟨0, Nat.zero_lt_succ r⟩).trans hφ1c.symm))
    rw [heqv] at hz; exact hsp1.1 hz
  have hφ2_pos : ∀ (z : V') (hz : z ∈ K₂), 0 < (φ2 ⟨z, Set.mem_insert_of_mem c hz⟩).val := fun z hz => by
    by_contra h0
    have heqv : z = c := congrArg Subtype.val (φ2.injective ((Fin.ext (Nat.eq_zero_of_not_pos h0) :
      φ2 ⟨z, Set.mem_insert_of_mem c hz⟩ = ⟨0, Nat.zero_lt_succ r⟩).trans hφ2c.symm))
    rw [heqv] at hz; exact hsp2.1 hz
  have hφ1_symm : ∀ (i : Fin r), (φ1.symm ⟨i.val + 1, by omega⟩).1 ∈ K₁ := fun i => by
    have hm := (φ1.symm ⟨i.val + 1, by omega⟩).2
    rcases mem_insert_iff.mp hm with heq | hz
    · have h2 := congrArg φ1 (Subtype.ext heq : φ1.symm ⟨i.val + 1, by omega⟩ = ⟨c, Set.mem_insert _ _⟩)
      rw [φ1.apply_symm_apply, hφ1c] at h2
      have hv := congrArg Fin.val h2; dsimp at hv; omega
    · exact hz
  have hφ2_symm : ∀ (i : Fin r), (φ2.symm ⟨i.val + 1, by omega⟩).1 ∈ K₂ := fun i => by
    have hm := (φ2.symm ⟨i.val + 1, by omega⟩).2
    rcases mem_insert_iff.mp hm with heq | hz
    · have h2 := congrArg φ2 (Subtype.ext heq : φ2.symm ⟨i.val + 1, by omega⟩ = ⟨c, Set.mem_insert _ _⟩)
      rw [φ2.apply_symm_apply, hφ2c] at h2
      have hv := congrArg Fin.val h2; dsimp at hv; omega
    · exact hz
  let S := insert c (K₁ ∪ K₂)
  let toF : ↥(S : Set V') → Fin (2 * r + 1) := fun x =>
    if hx : x.1 = c then ⟨r, by omega⟩
    else if hx1 : x.1 ∈ K₁ then ⟨r - (φ1 ⟨x.1, Set.mem_insert_of_mem c hx1⟩).val, by omega⟩
    else
      have hx2 : x.1 ∈ K₂ := (mem_union.mp ((mem_insert.mp x.2).resolve_left hx)).resolve_left hx1
      ⟨r + (φ2 ⟨x.1, Set.mem_insert_of_mem c hx2⟩).val, by
        have := (φ2 ⟨x.1, Set.mem_insert_of_mem c hx2⟩).isLt; omega⟩
  let invF : Fin (2 * r + 1) → (S : Set V') := fun i =>
    if hi0 : i.val < r then
      ⟨(φ1.symm ⟨r - i.val, by omega⟩).1,
        mem_insert_of_mem (mem_union_left K₂ (by
          have h := hφ1_symm ⟨r - i.val - 1, by omega⟩
          have hfin : (⟨r - i.val - 1 + 1, by omega⟩ : Fin (r + 1)) = ⟨r - i.val, by omega⟩ := Fin.ext (by dsimp; omega)
          rwa [hfin] at h))⟩
    else if hie : i.val = r then ⟨c, mem_insert_self c _⟩
    else
      ⟨(φ2.symm ⟨i.val - r, by have := i.isLt; omega⟩).1,
        mem_insert_of_mem (mem_union_right K₁ (by
          have := i.isLt
          have h := hφ2_symm ⟨i.val - r - 1, by omega⟩
          have hfin : (⟨i.val - r - 1 + 1, by omega⟩ : Fin (r + 1)) = ⟨i.val - r, by omega⟩ := Fin.ext (by dsimp; omega)
          rwa [hfin] at h))⟩
  have hleft : LeftInverse invF toF := by
    intro x; apply Subtype.ext; dsimp only [toF]
    by_cases hxc : x.1 = c
    · simp only [dif_pos hxc, invF, dif_neg (by omega : ¬ r < r), dif_pos rfl]; exact hxc.symm
    · simp only [dif_neg hxc]
      by_cases hx1 : x.1 ∈ K₁
      · have hp := hφ1_pos x.1 hx1
        have hlt := (φ1 ⟨x.1, Set.mem_insert_of_mem c hx1⟩).isLt
        simp only [dif_pos hx1, invF, dif_pos (by omega : r - (φ1 ⟨x.1, _⟩).val < r)]
        have hfin : (⟨r - (r - (φ1 ⟨x.1, Set.mem_insert_of_mem c hx1⟩).val), by omega⟩ : Fin (r + 1)) =
            φ1 ⟨x.1, Set.mem_insert_of_mem c hx1⟩ := Fin.ext (by simp; omega)
        rw [hfin]; exact congrArg Subtype.val (φ1.left_inv _)
      · have hx2 : x.1 ∈ K₂ := (mem_union.mp ((mem_insert.mp x.2).resolve_left hxc)).resolve_left hx1
        have hp := hφ2_pos x.1 hx2
        have hlt := (φ2 ⟨x.1, Set.mem_insert_of_mem c hx2⟩).isLt
        simp only [dif_neg hx1, invF, dif_neg (by omega : ¬ r + (φ2 ⟨x.1, _⟩).val < r),
          dif_neg (by omega : r + (φ2 ⟨x.1, _⟩).val ≠ r)]
        have hfin : (⟨r + (φ2 ⟨x.1, Set.mem_insert_of_mem c hx2⟩).val - r, by omega⟩ : Fin (r + 1)) =
            φ2 ⟨x.1, Set.mem_insert_of_mem c hx2⟩ := Fin.ext (by simp)
        rw [hfin]; exact congrArg Subtype.val (φ2.left_inv _)
  have hright : RightInverse invF toF := by
    intro i; apply Fin.ext; dsimp only [invF]
    by_cases hi0 : i.val < r
    · have hk1 : (φ1.symm ⟨r - i.val, by omega⟩).1 ∈ K₁ := by
        have h := hφ1_symm ⟨r - i.val - 1, by omega⟩
        have hfin : (⟨r - i.val - 1 + 1, by omega⟩ : Fin (r + 1)) = ⟨r - i.val, by omega⟩ := Fin.ext (by dsimp; omega)
        rwa [hfin] at h
      have hne : (φ1.symm ⟨r - i.val, by omega⟩).1 ≠ c := fun h => by rw [h] at hk1; exact hsp1.1 hk1
      simp only [dif_pos hi0, toF, dif_neg hne, dif_pos hk1]
      have h1 : φ1 ⟨(φ1.symm ⟨r - i.val, by omega⟩).1, Set.mem_insert_of_mem c hk1⟩ = ⟨r - i.val, by omega⟩ :=
        (congrArg φ1 (Subtype.ext rfl)).trans (φ1.right_inv ⟨r - i.val, by omega⟩)
      have hval := congrArg Fin.val h1; dsimp only at hval; omega
    · by_cases hie : i.val = r
      · simp only [dif_neg hi0, dif_pos hie, toF, dif_pos rfl]; exact hie.symm
      · have hi_lt := i.isLt
        have hk2 : (φ2.symm ⟨i.val - r, by omega⟩).1 ∈ K₂ := by
          have h := hφ2_symm ⟨i.val - r - 1, by omega⟩
          have hfin : (⟨i.val - r - 1 + 1, by omega⟩ : Fin (r + 1)) = ⟨i.val - r, by omega⟩ := Fin.ext (by dsimp; omega)
          rwa [hfin] at h
        have hne : (φ2.symm ⟨i.val - r, by omega⟩).1 ≠ c := fun h => by rw [h] at hk2; exact hsp2.1 hk2
        have hnot1 : (φ2.symm ⟨i.val - r, by omega⟩).1 ∉ K₁ := Finset.disjoint_right.mp hdisj hk2
        simp only [dif_neg hi0, dif_neg hie, toF, dif_neg hne, dif_neg hnot1]
        have h1 : φ2 ⟨(φ2.symm ⟨i.val - r, by omega⟩).1, Set.mem_insert_of_mem c hk2⟩ = ⟨i.val - r, by omega⟩ :=
          (congrArg φ2 (Subtype.ext rfl)).trans (φ2.right_inv ⟨i.val - r, by omega⟩)
        have hval := congrArg Fin.val h1; dsimp only at hval; omega
  change Nonempty (T.induce (insert c ((K₁ : Set V') ∪ (K₂ : Set V'))) ≃g pathG (2 * r + 1))
  rw [← coe_union, ← coe_insert]
  refine ⟨⟨⟨toF, invF, hleft, hright⟩, ?_⟩⟩
  intro x₁ x₂
  rw [iff_comm]
  change T.Adj x₁.1 x₂.1 ↔ (pathG (2 * r + 1)).Adj (toF x₁) (toF x₂)
  dsimp only [toF, pathG]
  have mem_K2_of : ∀ (x : (S : Set V')), x.1 ≠ c → x.1 ∉ K₁ → x.1 ∈ K₂ := fun x h1 h2 =>
    (mem_union.mp ((mem_insert.mp x.2).resolve_left h1)).resolve_left h2
  by_cases h1c : x₁.1 = c <;> by_cases h2c : x₂.1 = c
  · simp [h1c, h2c]
  · simp only [dif_pos h1c, dif_neg h2c]; simp only [h1c]
    by_cases h21 : x₂.1 ∈ K₁
    · simp only [dif_pos h21]
      have h_eq := (φ1.map_rel_iff (a := ⟨c, Set.mem_insert _ _⟩) (b := ⟨x₂.1, Set.mem_insert_of_mem c h21⟩)).symm
      change T.Adj c x₂.1 ↔ (pathG (r + 1)).Adj (φ1 ⟨c, _⟩) (φ1 ⟨x₂.1, _⟩) at h_eq
      rw [hφ1c] at h_eq; have := hφ1_pos x₂.1 h21; have hlt := (φ1 ⟨x₂.1, Set.mem_insert_of_mem c h21⟩).isLt
      exact h_eq.trans ⟨fun h => Or.inr (by dsimp only [pathG] at h ⊢; rcases h with h | h <;> omega), fun h => Or.inl (by dsimp only [pathG] at h ⊢; rcases h with h | h <;> omega)⟩
    · simp only [dif_neg h21]
      have h22 := mem_K2_of x₂ h2c h21
      have h_eq := (φ2.map_rel_iff (a := ⟨c, Set.mem_insert _ _⟩) (b := ⟨x₂.1, Set.mem_insert_of_mem c h22⟩)).symm
      change T.Adj c x₂.1 ↔ (pathG (r + 1)).Adj (φ2 ⟨c, _⟩) (φ2 ⟨x₂.1, _⟩) at h_eq
      rw [hφ2c] at h_eq; have := hφ2_pos x₂.1 h22
      exact h_eq.trans ⟨fun h => Or.inl (by dsimp only [pathG] at h ⊢; rcases h with h | h <;> omega), fun h => Or.inl (by dsimp only [pathG] at h ⊢; rcases h with h | h <;> omega)⟩
  · simp only [dif_neg h1c, dif_pos h2c]; simp only [h2c]
    by_cases h11 : x₁.1 ∈ K₁
    · simp only [dif_pos h11]
      have h_eq := (φ1.map_rel_iff (a := ⟨x₁.1, Set.mem_insert_of_mem c h11⟩) (b := ⟨c, Set.mem_insert _ _⟩)).symm
      change T.Adj x₁.1 c ↔ (pathG (r + 1)).Adj (φ1 ⟨x₁.1, _⟩) (φ1 ⟨c, _⟩) at h_eq
      rw [hφ1c] at h_eq; have := hφ1_pos x₁.1 h11; have hlt := (φ1 ⟨x₁.1, Set.mem_insert_of_mem c h11⟩).isLt
      exact h_eq.trans ⟨fun h => Or.inl (by dsimp only [pathG] at h ⊢; rcases h with h | h <;> omega), fun h => Or.inr (by dsimp only [pathG] at h ⊢; rcases h with h | h <;> omega)⟩
    · simp only [dif_neg h11]
      have h12 := mem_K2_of x₁ h1c h11
      have h_eq := (φ2.map_rel_iff (a := ⟨x₁.1, Set.mem_insert_of_mem c h12⟩) (b := ⟨c, Set.mem_insert _ _⟩)).symm
      change T.Adj x₁.1 c ↔ (pathG (r + 1)).Adj (φ2 ⟨x₁.1, _⟩) (φ2 ⟨c, _⟩) at h_eq
      rw [hφ2c] at h_eq; have := hφ2_pos x₁.1 h12
      exact h_eq.trans ⟨fun h => Or.inr (by dsimp only [pathG] at h ⊢; rcases h with h | h <;> omega), fun h => Or.inr (by dsimp only [pathG] at h ⊢; rcases h with h | h <;> omega)⟩
  · simp only [dif_neg h1c, dif_neg h2c]
    by_cases h11 : x₁.1 ∈ K₁ <;> by_cases h21 : x₂.1 ∈ K₁
    · simp only [dif_pos h11, dif_pos h21]
      have h_eq := (φ1.map_rel_iff (a := ⟨x₁.1, Set.mem_insert_of_mem c h11⟩) (b := ⟨x₂.1, Set.mem_insert_of_mem c h21⟩)).symm
      change T.Adj x₁.1 x₂.1 ↔ (pathG (r + 1)).Adj (φ1 ⟨x₁.1, _⟩) (φ1 ⟨x₂.1, _⟩) at h_eq
      have := (φ1 ⟨x₁.1, Set.mem_insert_of_mem c h11⟩).isLt
      have := (φ1 ⟨x₂.1, Set.mem_insert_of_mem c h21⟩).isLt
      exact h_eq.trans ⟨by rintro (h | h) <;> dsimp [pathG] at h ⊢ <;> omega,
        by rintro (h | h) <;> dsimp [pathG] at h ⊢ <;> omega⟩
    · simp only [dif_pos h11, dif_neg h21]
      have h22 := mem_K2_of x₂ h2c h21
      have h1_pos := hφ1_pos x₁.1 h11; have h2_pos := hφ2_pos x₂.1 h22
      have h1_lt := (φ1 ⟨x₁.1, Set.mem_insert_of_mem c h11⟩).isLt
      exact ⟨fun hadj => False.elim (hy12 (adj_compSet_eq T c (hsp1.2.2.2.1 h11) (hsp2.2.2.2.1 h22) hadj)), by rintro (h | h) <;> omega⟩
    · simp only [dif_neg h11, dif_pos h21]
      have h12 := mem_K2_of x₁ h1c h11
      have h1_pos := hφ2_pos x₁.1 h12; have h2_pos := hφ1_pos x₂.1 h21
      have h2_lt := (φ1 ⟨x₂.1, Set.mem_insert_of_mem c h21⟩).isLt
      exact ⟨fun hadj => False.elim (hy12.symm (adj_compSet_eq T c (hsp2.2.2.2.1 h12) (hsp1.2.2.2.1 h21) hadj)), by rintro (h | h) <;> omega⟩
    · simp only [dif_neg h11, dif_neg h21]
      have h12 := mem_K2_of x₁ h1c h11; have h22 := mem_K2_of x₂ h2c h21
      have h_eq := (φ2.map_rel_iff (a := ⟨x₁.1, Set.mem_insert_of_mem c h12⟩) (b := ⟨x₂.1, Set.mem_insert_of_mem c h22⟩)).symm
      change T.Adj x₁.1 x₂.1 ↔ (pathG (r + 1)).Adj (φ2 ⟨x₁.1, _⟩) (φ2 ⟨x₂.1, _⟩) at h_eq
      exact h_eq.trans ⟨by rintro (h | h) <;> dsimp [pathG] at h ⊢ <;> omega,
        by rintro (h | h) <;> dsimp [pathG] at h ⊢ <;> omega⟩
private lemma path2r1_two_mul_subgraphs_card_eq {V' : Type} [Fintype V']
    (T : SimpleGraph V') (hT : T.IsTree) {r : ℕ} (hr : 2 ≤ r)
    (c : V') (hecc : T.eccent c = r)
    (hmax : ∀ D : (T.induce {c}ᶜ).ConnectedComponent, card D.supp ≤ r + 1) :
    2 * {S : Finset V' | Nonempty (T.induce (S : Set V') ≃g pathG (2 * r + 1))}.ncard =
      ∑ D₁ : (T.induce {c}ᶜ).ConnectedComponent,
        (univ.filter fun y : V' => y ∈ compSet T c D₁ ∧ T.dist c y = r).card *
        ((univ.filter fun y : V' => T.dist c y = r).card -
          (univ.filter fun y : V' => y ∈ compSet T c D₁ ∧ T.dist c y = r).card) := by
  let LHS : Finset (Finset V') := univ.filter fun S : Finset V' =>
    Nonempty (T.induce (S : Set V') ≃g pathG (2 * r + 1))
  have hLHS : {S : Finset V' | Nonempty (T.induce (S : Set V') ≃g pathG (2 * r + 1))}.ncard = LHS.card := by
    have hs : {S : Finset V' | Nonempty (T.induce (S : Set V') ≃g pathG (2 * r + 1))} = (LHS : Set (Finset V')) := by
      ext S; simp [LHS]
    rw [hs, Set.ncard_coe_finset]
  let Pairs := univ.filter fun p : V' × V' =>
    T.dist c p.1 = r ∧ T.dist c p.2 = r ∧
    ∃ (h1 : p.1 ≠ c) (h2 : p.2 ≠ c),
      (T.induce {c}ᶜ).connectedComponentMk ⟨p.1, h1⟩ ≠
      (T.induce {c}ᶜ).connectedComponentMk ⟨p.2, h2⟩
  have hPairs_card : Pairs.card =
      ∑ D₁ : (T.induce {c}ᶜ).ConnectedComponent,
        (univ.filter fun y : V' => y ∈ compSet T c D₁ ∧ T.dist c y = r).card *
        ((univ.filter fun y : V' => T.dist c y = r).card -
          (univ.filter fun y : V' => y ∈ compSet T c D₁ ∧ T.dist c y = r).card) := by
    let S_rhs := univ.sigma fun D₁ : (T.induce {c}ᶜ).ConnectedComponent =>
      (univ.filter fun y : V' => y ∈ compSet T c D₁ ∧ T.dist c y = r) ×ˢ
      (univ.filter fun y : V' => y ∉ compSet T c D₁ ∧ T.dist c y = r)
    have hS : S_rhs.card =
        ∑ D₁ : (T.induce {c}ᶜ).ConnectedComponent,
          (univ.filter fun y : V' => y ∈ compSet T c D₁ ∧ T.dist c y = r).card *
          ((univ.filter fun y : V' => T.dist c y = r).card -
            (univ.filter fun y : V' => y ∈ compSet T c D₁ ∧ T.dist c y = r).card) := by
      rw [card_sigma]
      refine sum_congr rfl fun D₁ _ => ?_
      rw [card_product]
      congr 1
      let A := univ.filter fun y : V' => T.dist c y = r
      let B := univ.filter fun y : V' => y ∈ compSet T c D₁ ∧ T.dist c y = r
      have hsub : B ⊆ A := fun y hy => mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hy).2.2⟩
      have hsd : A \ B = univ.filter fun y : V' => y ∉ compSet T c D₁ ∧ T.dist c y = r := by
        ext y; simp only [A, B, mem_sdiff, mem_filter, mem_univ, true_and]; tauto
      rw [← hsd, card_sdiff_of_subset hsub]
    rw [← hS]
    refine card_bij (fun p hp =>
        let D₁ := (T.induce {c}ᶜ).connectedComponentMk ⟨p.1, fun h => by
          have := (mem_filter.mp hp).2.1; rw [h, dist_self] at this; omega⟩
        ⟨D₁, p⟩) ?_ ?_ ?_
    · rintro ⟨y₁, y₂⟩ hp
      obtain ⟨_, hy1d, hy2d, hy1c, hy2c, hy12⟩ := mem_filter.mp hp
      refine mem_sigma.mpr ⟨mem_univ _, mem_product.mpr
        ⟨mem_filter.mpr ⟨mem_univ _, (mem_compSet_iff T c _ y₁).mpr ⟨_, rfl⟩, hy1d⟩,
         mem_filter.mpr ⟨mem_univ _, fun h => hy12 (by
            obtain ⟨h1, h2⟩ := (mem_compSet_iff T c _ y₂).mp h
            exact ((mem_supp_iff _ _).mp h2).symm), hy2d⟩⟩⟩
    · rintro ⟨a1, b1⟩ _ ⟨a2, b2⟩ _ heq
      have := congrArg Sigma.snd heq
      exact Prod.ext (congrArg Prod.fst this) (congrArg Prod.snd this)
    · rintro ⟨D₁, ⟨y₁, y₂⟩⟩ hmem
      simp only [S_rhs, mem_sigma, mem_univ, true_and, mem_product, mem_filter] at hmem
      obtain ⟨⟨hy1D, hy1d⟩, hy2_not, hy2d⟩ := hmem
      have hy1c : y₁ ≠ c := fun h => c_notMem_compSet T c D₁ (h ▸ hy1D)
      have hy2c : y₂ ≠ c := fun h => by rw [← h, dist_self] at hy2d; omega
      obtain ⟨h1, h2⟩ := (mem_compSet_iff T c D₁ y₁).mp hy1D
      have hD1 : (T.induce {c}ᶜ).connectedComponentMk ⟨y₁, hy1c⟩ = D₁ :=
        (mem_supp_iff D₁ _).mp (by convert h2)
      have hne : (T.induce {c}ᶜ).connectedComponentMk ⟨y₁, hy1c⟩ ≠
          (T.induce {c}ᶜ).connectedComponentMk ⟨y₂, hy2c⟩ := by
        intro heq
        exact hy2_not ((mem_compSet_iff T c D₁ y₂).mpr ⟨hy2c,
          (mem_supp_iff D₁ _).mpr (heq.symm.trans hD1)⟩)
      refine ⟨(y₁, y₂), mem_filter.mpr ⟨mem_univ _, hy1d, hy2d, hy1c, hy2c, hne⟩, ?_⟩
      exact Sigma.ext hD1 (heq_of_eq rfl)
  rw [hLHS, ← hPairs_card]
  let π : V' × V' → Finset V' := fun (y₁, y₂) => insert c (pathTail T hT c y₁ ∪ pathTail T hT c y₂)
  have hmaps : ∀ p ∈ Pairs, π p ∈ LHS := by
    rintro ⟨y₁, y₂⟩ hp
    obtain ⟨_, hy1d, hy2d, hy1c, hy2c, hy12⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_univ _,
      (by dsimp only [π]; rw [coe_insert, coe_union]
          exact path2r1_induce_union_iso T hT hr c hy1d hy2d hy1c hy2c hy12)⟩
  have hfib : ∀ s ∈ LHS, (Pairs.filter fun p => π p = s).card = 2 := by
    intro s hs
    obtain ⟨ψ⟩ := (mem_filter.mp hs).2
    obtain ⟨hcs, hψc⟩ := path2r1_center_forced T hT hr c hecc hmax s ψ
    let a := (ψ.symm ⟨0, by omega⟩).1
    let b := (ψ.symm ⟨2 * r, by omega⟩).1
    have hac : a ≠ c := fun h => by
      have h1 := congrArg ψ (Subtype.ext h : ψ.symm ⟨0, by omega⟩ = ⟨c, hcs⟩)
      rw [ψ.apply_symm_apply] at h1
      have hval := congrArg Fin.val h1; rw [hψc] at hval; dsimp only at hval; omega
    have hbc : b ≠ c := fun h => by
      have h1 := congrArg ψ (Subtype.ext h : ψ.symm ⟨2 * r, by omega⟩ = ⟨c, hcs⟩)
      rw [ψ.apply_symm_apply] at h1
      have hval := congrArg Fin.val h1; rw [hψc] at hval; dsimp only at hval; omega
    have h_dist_fin : ∀ (j : Fin (2 * r + 1)), T.dist c (ψ.symm j).1 ≤ if j.val ≤ r then r - j.val else j.val - r := by
      intro j
      by_cases hj : j.val ≤ r
      · obtain ⟨p, hp, hplen⟩ := pathG_walk_down j ⟨r, by omega⟩ hj
        let gS : T.induce (s : Set V') →g T := (Embedding.induce (s : Set V')).toHom
        let pT : T.Walk c (ψ.symm j).1 := ((p.reverse.map ψ.symm.toHom).map gS).copy
          (by change (ψ.symm ⟨r, by omega⟩).1 = c; exact congrArg Subtype.val (ψ.symm_apply_eq.mpr (Fin.ext hψc.symm : (⟨r, by omega⟩ : Fin (2 * r + 1)) = ψ ⟨c, hcs⟩))) rfl
        rw [← isTree_dist_eq_length_of_isPath T hT pT
          ((isPath_copy _ _ _).mpr ((hp.reverse.map ψ.symm.injective).map val_injective))]
        have hlen : pT.length = p.length := (length_copy _ _ _).trans (by rw [length_map, length_map, length_reverse])
        rw [hlen, hplen]; simp [hj]
      · obtain ⟨p, hp, hplen⟩ := pathG_walk_down ⟨r, by omega⟩ j (by dsimp; omega)
        let gS : T.induce (s : Set V') →g T := (Embedding.induce (s : Set V')).toHom
        let pT : T.Walk c (ψ.symm j).1 := ((p.map ψ.symm.toHom).map gS).copy
          (by change (ψ.symm ⟨r, by omega⟩).1 = c; exact congrArg Subtype.val (ψ.symm_apply_eq.mpr (Fin.ext hψc.symm : (⟨r, by omega⟩ : Fin (2 * r + 1)) = ψ ⟨c, hcs⟩))) rfl
        rw [← isTree_dist_eq_length_of_isPath T hT pT
          ((isPath_copy _ _ _).mpr ((hp.map ψ.symm.injective).map val_injective))]
        have hlen : pT.length = p.length := (length_copy _ _ _).trans (by rw [length_map, length_map])
        rw [hlen, hplen]; simp [hj]
    have hs_tree : (T.induce (s : Set V')).IsTree := by
      have hpc : (pathG (2 * r + 1)).IsTree := by
        refine ⟨Connected.mk fun i j => ?_, fun u c_w hc_w => ?_⟩
        · suffices h0 : ∀ x : Fin (2 * r + 1), (pathG (2 * r + 1)).Reachable ⟨0, by omega⟩ x from (h0 i).symm.trans (h0 j)
          intro x; obtain ⟨p, _, _⟩ := pathG_walk_up x.val x.isLt; exact ⟨p⟩
        · have hne : c_w.support.toFinset.Nonempty := ⟨u, List.mem_toFinset.mpr c_w.start_mem_support⟩
          let m : Fin (2 * r + 1) := c_w.support.toFinset.max' hne
          have hm : m ∈ c_w.support := List.mem_toFinset.mp (Finset.max'_mem _ hne)
          let c' : (pathG (2 * r + 1)).Walk m m := c_w.rotate m hm
          have hc' : c'.IsCycle := hc_w.rotate hm
          have hperm := (c_w.support_rotate m hm).perm
          have hadj1 : (pathG (2 * r + 1)).Adj m c'.snd := c'.adj_snd hc'.not_nil
          have hadj2 : (pathG (2 * r + 1)).Adj m c'.penultimate := (c'.adj_penultimate hc'.not_nil).symm
          have hsnd_mem : c'.snd ∈ c_w.support := List.mem_of_mem_tail (hperm.subset (c'.snd_mem_tail_support hc'.not_nil))
          have hpen_mem : c'.penultimate ∈ c_w.support := List.mem_of_mem_tail (hperm.subset
            (mem_support_tail_of_ne c' (c'.getVert_mem_support _) hadj2.ne.symm))
          have hsnd_le : c'.snd.val ≤ m.val := Finset.le_max' _ _ (List.mem_toFinset.mpr hsnd_mem)
          have hpen_le : c'.penultimate.val ≤ m.val := Finset.le_max' _ _ (List.mem_toFinset.mpr hpen_mem)
          have h1 : m.val + 1 = c'.snd.val ∨ c'.snd.val + 1 = m.val := hadj1
          have h2 : m.val + 1 = c'.penultimate.val ∨ c'.penultimate.val + 1 = m.val := hadj2
          have hsp_eq : c'.snd = c'.penultimate := Fin.ext (by omega)
          have h3 : 3 ≤ c'.length := hc'.three_le_length
          have hlen1 : 1 ≤ c'.length := by omega
          have hlen2 : c'.length - 1 ≤ c'.length := Nat.sub_le _ _
          have hs_eq1 : c'.snd = c'.support[1]'(by rw [c'.length_support]; omega) := by
            rw [← getVert_eq_support_getElem c' hlen1]
          have hs_eq2 : c'.penultimate = c'.support[c'.length - 1]'(by rw [c'.length_support]; omega) := by
            rw [← getVert_eq_support_getElem c' hlen2]
          have hlt_t1 : 0 < c'.support.tail.length := by rw [List.length_tail, c'.length_support]; omega
          have hlt_t2 : c'.length - 2 < c'.support.tail.length := by rw [List.length_tail, c'.length_support]; omega
          have helem : c'.support.tail[0]'hlt_t1 = c'.support.tail[c'.length - 2]'hlt_t2 := by
            have ha1 : c'.support.tail[0]'hlt_t1 = c'.support[1]'(by rw [c'.length_support]; omega) := List.getElem_tail hlt_t1
            have ha2 : c'.support.tail[c'.length - 2]'hlt_t2 = c'.support[c'.length - 1]'(by rw [c'.length_support]; omega) := by
              rw [List.getElem_tail]; congr 1; omega
            rw [ha1, ha2, ← hs_eq1, ← hs_eq2, hsp_eq]
          have hidx_eq := (List.Nodup.getElem_inj_iff hc'.support_nodup).mp helem
          omega
      exact (Iso.isTree_iff ψ.symm).mp hpc
    have hs_dist_eq : ∀ z : (s : Set V'), T.dist c z.1 = (if (ψ z).val ≤ r then r - (ψ z).val else (ψ z).val - r) := by
      intro z
      have hψc_fin : ψ ⟨c, hcs⟩ = ⟨r, by omega⟩ := Fin.ext hψc
      rw [← dist_induce_eq_of_isTree T hT (s : Set V') hs_tree ⟨c, hcs⟩ z,
        ← iso_dist_eq _ _ ψ ⟨c, hcs⟩ z, hψc_fin]
      have h_pg_dist : ∀ j : Fin (2 * r + 1), (pathG (2 * r + 1)).dist ⟨r, by omega⟩ j =
          (if j.val ≤ r then r - j.val else j.val - r) := by
        intro j
        by_cases hj : j.val ≤ r
        · rw [if_pos hj]
          obtain ⟨p, hp, hplen⟩ := pathG_walk_down j ⟨r, by omega⟩ hj
          have hp_pc : (pathG (2 * r + 1)).IsTree := (Iso.isTree_iff ψ).mp hs_tree
          rw [← isTree_dist_eq_length_of_isPath _ hp_pc p.reverse hp.reverse, length_reverse, hplen]
        · rw [if_neg hj]
          obtain ⟨p, hp, hplen⟩ := pathG_walk_down ⟨r, by omega⟩ j (by dsimp; omega)
          have hp_pc : (pathG (2 * r + 1)).IsTree := (Iso.isTree_iff ψ).mp hs_tree
          rw [← isTree_dist_eq_length_of_isPath _ hp_pc p hp, hplen]
      exact h_pg_dist (ψ z)
    have hs_dist_r : ∀ z ∈ s, T.dist c z = r → z = a ∨ z = b := by
      intro z hzs hzd
      rw [hs_dist_eq ⟨z, hzs⟩] at hzd
      by_cases hle : (ψ ⟨z, hzs⟩).val ≤ r
      · rw [if_pos hle] at hzd
        have hj0 : ψ ⟨z, hzs⟩ = ⟨0, by omega⟩ := Fin.ext (by dsimp; omega)
        left; exact congrArg Subtype.val ((ψ.symm_apply_eq.mpr hj0.symm).symm)
      · rw [if_neg hle] at hzd
        have hj2 : ψ ⟨z, hzs⟩ = ⟨2 * r, by omega⟩ := Fin.ext (by dsimp; omega)
        right; exact congrArg Subtype.val ((ψ.symm_apply_eq.mpr hj2.symm).symm)
    have had : T.dist c a = r := by
      have ha_s : a ∈ s := (ψ.symm ⟨0, by omega⟩).2
      have := hs_dist_eq ⟨a, ha_s⟩
      have hψa : ψ ⟨a, ha_s⟩ = ⟨0, by omega⟩ := ψ.apply_symm_apply _
      rw [hψa] at this; dsimp only at this
      rw [if_pos (Nat.zero_le r)] at this; exact this
    have hbd : T.dist c b = r := by
      have hb_s : b ∈ s := (ψ.symm ⟨2 * r, by omega⟩).2
      have := hs_dist_eq ⟨b, hb_s⟩
      have hψb : ψ ⟨b, hb_s⟩ = ⟨2 * r, by omega⟩ := ψ.apply_symm_apply _
      rw [hψb] at this; dsimp only at this
      rw [if_neg (by omega)] at this; exact this.trans (by omega)
    have hab_comp : (T.induce {c}ᶜ).connectedComponentMk ⟨a, hac⟩ ≠
        (T.induce {c}ᶜ).connectedComponentMk ⟨b, hbc⟩ := by
      intro heq
      obtain ⟨p_pg, hp_pg, hplen⟩ := pathG_walk_down (r := 2 * r + 1) ⟨0, by omega⟩ ⟨2 * r, by omega⟩ (by dsimp; omega)
      let gS : T.induce (s : Set V') →g T := (Embedding.induce (s : Set V')).toHom
      let pT : T.Walk a b := ((p_pg.map ψ.symm.toHom).map gS).copy rfl rfl
      have hpT : pT.IsPath :=
        (isPath_copy _ _ _).mpr ((hp_pg.map ψ.symm.injective).map val_injective)
      have huniv : p_pg.support.toFinset = univ := by
        apply Finset.eq_univ_of_card
        rw [List.toFinset_card_of_nodup hp_pg.support_nodup, p_pg.length_support, hplen]
        simp [card_fin]
      have hr_in : (⟨r, by omega⟩ : Fin (2 * r + 1)) ∈ p_pg.support := by
        rw [← List.mem_toFinset, huniv]; exact mem_univ _
      have hc_in_pT : c ∈ pT.support := by
        have hm1 : ψ.symm ⟨r, by omega⟩ ∈ (p_pg.map ψ.symm.toHom).support := by
          rw [Walk.support_map, List.mem_map]; exact ⟨⟨r, by omega⟩, hr_in, rfl⟩
        have hm : (ψ.symm ⟨r, by omega⟩).1 ∈ ((p_pg.map ψ.symm.toHom).map gS).support := by
          rw [Walk.support_map, List.mem_map]; exact ⟨_, hm1, rfl⟩
        have hcr : (ψ.symm ⟨r, by omega⟩).1 = c :=
          congrArg Subtype.val (ψ.symm_apply_eq.mpr (Fin.ext hψc.symm : (⟨r, by omega⟩ : Fin (2 * r + 1)) = ψ ⟨c, hcs⟩))
        dsimp only [pT]; erw [support_copy]; rwa [hcr] at hm
      obtain ⟨q⟩ := ConnectedComponent.exact heq
      let q_path := q.toPath
      let gc : T.induce {c}ᶜ →g T := (Embedding.induce ({c}ᶜ : Set V')).toHom
      have hqG : (q_path.val.map gc).IsPath := q_path.isPath.map val_injective
      have hqp := isTree_path_eq T hT hqG hpT
      have hnc : c ∉ (q_path.val.map gc).support := by
        rw [Walk.support_map, List.mem_map]; rintro ⟨z, _, hzc⟩; exact z.2 hzc
      rw [hqp] at hnc
      exact hnc hc_in_pT
    have hab_ne : a ≠ b := fun h => hab_comp (by simp only [h])
    have hs_card : s.card = 2 * r + 1 := by
      have hsc : s.card = card (s : Set V') :=
        (card_coe s).symm.trans
          (card_congr ⟨fun x => ⟨x.1, x.2⟩, fun x => ⟨x.1, x.2⟩, fun _ => rfl, fun _ => rfl⟩)
      rw [hsc, card_congr ψ.toEquiv, card_fin]
    have h_pathTail_sub : ∀ {y : V'} (hyd : T.dist c y = r) (hys : y ∈ s), pathTail T hT c y ⊆ s := by
      intro y hyd hys z hz
      dsimp only [pathTail] at hz
      rw [mem_erase, List.mem_toFinset] at hz
      change z ≠ c ∧ z ∈ ((hT.connected.exists_path_of_dist c y).choose).support at hz
      let py := (hT.connected.exists_path_of_dist c y).choose
      have hpy := (hT.connected.exists_path_of_dist c y).choose_spec.1
      obtain ⟨qs, hqs, _⟩ := hs_tree.connected.exists_path_of_dist ⟨c, hcs⟩ ⟨y, hys⟩
      let gS : T.induce (s : Set V') →g T := (Embedding.induce (s : Set V')).toHom
      have hq_eq : qs.map gS = py := isTree_path_eq T hT (hqs.map val_injective) hpy
      have hz_m : z ∈ (qs.map gS).support := by rw [hq_eq]; exact hz.2
      rw [Walk.support_map, List.mem_map] at hz_m
      obtain ⟨u, _, rfl⟩ := hz_m
      exact u.2
    have hdisj_ab : Disjoint (pathTail T hT c a) (pathTail T hT c b) :=
      (compSet_disjoint T c hab_comp).mono (pathTail_spec T hT hr c a had).2.2.2.1
        (pathTail_spec T hT hr c b hbd).2.2.2.1
    have hs_eq_ab : s = insert c (pathTail T hT c a ∪ pathTail T hT c b) := by
      refine (eq_of_subset_of_card_le (Finset.insert_subset_iff.mpr ⟨hcs,
        Finset.union_subset (h_pathTail_sub had (ψ.symm ⟨0, by omega⟩).2)
          (h_pathTail_sub hbd (ψ.symm ⟨2 * r, by omega⟩).2)⟩) ?_).symm
      have hsp1 := pathTail_spec T hT hr c a had
      have hsp2 := pathTail_spec T hT hr c b hbd
      rw [card_insert_of_notMem (by simp [hsp1.1, hsp2.1]), Finset.card_union_of_disjoint hdisj_ab,
        hsp1.2.2.1, hsp2.2.2.1, hs_card]; omega
    have hfib_set : Pairs.filter (fun p => π p = s) = {(a, b), (b, a)} := by
      ext ⟨y₁, y₂⟩
      rw [mem_filter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hp, hπ⟩
        obtain ⟨_, hy1d, hy2d, hy1c, hy2c, hy12⟩ := mem_filter.mp hp
        have hy1_s : y₁ ∈ s := by
          rw [← hπ]; exact mem_insert_of_mem (mem_union_left _ (pathTail_spec T hT hr c y₁ hy1d).2.1)
        have hy2_s : y₂ ∈ s := by
          rw [← hπ]; exact mem_insert_of_mem (mem_union_right _ (pathTail_spec T hT hr c y₂ hy2d).2.1)
        rcases hs_dist_r y₁ hy1_s hy1d with rfl | rfl <;> rcases hs_dist_r y₂ hy2_s hy2d with rfl | rfl
        · exact False.elim (hy12 rfl)
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact False.elim (hy12 rfl)
      · rintro (h | h) <;> cases h
        · exact ⟨mem_filter.mpr ⟨mem_univ _, had, hbd, hac, hbc, hab_comp⟩, hs_eq_ab.symm⟩
        · exact ⟨mem_filter.mpr ⟨mem_univ _, hbd, had, hbc, hac, hab_comp.symm⟩,
            by dsimp only [π]; rw [Finset.union_comm]; exact hs_eq_ab.symm⟩
    have hpair_ne : (a, b) ≠ (b, a) := fun h => hab_ne (congrArg Prod.fst h)
    rw [hfib_set, card_pair hpair_ne]
  have := Finset.card_eq_sum_card_fiberwise hmaps
  rw [sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, mul_comm] at this
  exact this.symm
private lemma comp_erase_bij {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) (c : U)
    (hnoLeaf : ∀ u : U, T.Adj c u → 2 ≤ T.degree u)
    {v : U} (hv1 : T.degree v = 1) (hvc : v ≠ c)
    (C₀ : (T.induce {c}ᶜ).ConnectedComponent) (hvC0 : v ∈ compSet T c C₀) :
    let hc' : c ∈ ({v}ᶜ : Set U) := hvc.symm
    let T' := T.induce ({v}ᶜ : Set U)
    let c' : ({v}ᶜ : Set U) := ⟨c, hc'⟩
    ∃ (C₀' : (T'.induce {c'}ᶜ).ConnectedComponent)
      (ι : (T.induce {c}ᶜ).ConnectedComponent ≃ (T'.induce {c'}ᶜ).ConnectedComponent),
      ι C₀ = C₀' ∧
      card C₀'.supp + 1 = card C₀.supp ∧
      RootedIso T c (insert c ((compSet T c C₀).erase v : Set U))
        T' c' (insert c' (compSet T' c' C₀' : Set ({v}ᶜ : Set U))) ∧
      (∀ C, C ≠ C₀ → card (ι C).supp = card C.supp ∧ RootedCompIso T c C T' c' (ι C)) := by
  intro hc' T' c'
  obtain ⟨C₀', hC0'_map, hC0'_iso, hother, hback⟩ :=
    comp_erase_leaf_structure T hT c hnoLeaf hv1 hvc C₀ hvC0
  have hC0'_card : card C₀'.supp + 1 = card C₀.supp := by
    have h1 : card C₀'.supp = (compSet T' c' C₀').card := by
      convert (compSet_card_eq T' c' C₀').symm
    rw [h1, ← card_map (⟨Subtype.val, val_injective⟩ : ({v}ᶜ : Set U) ↪ U), hC0'_map,
      card_erase_of_mem hvC0, compSet_card_eq]
    have := comp_noLeaf_card_ge_two T hT c hnoLeaf C₀
    omega
  let toF : (T.induce {c}ᶜ).ConnectedComponent → (T'.induce {c'}ᶜ).ConnectedComponent := fun C =>
    if h : C = C₀ then C₀' else (hother C h).choose
  let invF : (T'.induce {c'}ᶜ).ConnectedComponent → (T.induce {c}ᶜ).ConnectedComponent := fun D' =>
    if h : D' = C₀' then C₀ else (hback D' h).choose
  have hdisj_comp : ∀ {C₁ C₂ : (T.induce {c}ᶜ).ConnectedComponent} {D' : (T'.induce {c'}ᶜ).ConnectedComponent},
      (compSet T' c' D').map ⟨Subtype.val, val_injective⟩ = compSet T c C₁ →
      (compSet T' c' D').map ⟨Subtype.val, val_injective⟩ = compSet T c C₂ →
      C₁ = C₂ := by
    intro C₁ C₂ D' h1 h2
    have hne : (compSet T c C₁).Nonempty := by
      rw [← card_pos]
      have : 2 ≤ (compSet T c C₁).card := by rw [compSet_card_eq]; exact comp_noLeaf_card_ge_two T hT c hnoLeaf C₁
      omega
    obtain ⟨x, hx⟩ := hne
    have hx2 : x ∈ compSet T c C₂ := h2 ▸ (h1 ▸ hx)
    obtain ⟨a1, a2⟩ := (mem_compSet_iff T c C₁ x).mp hx
    obtain ⟨b1, b2⟩ := (mem_compSet_iff T c C₂ x).mp hx2
    exact ((mem_supp_iff C₁ ⟨x, a1⟩).mp a2).symm.trans
      ((mem_supp_iff C₂ ⟨x, b1⟩).mp b2)
  have hleft : LeftInverse invF toF := by
    intro C
    dsimp only [toF, invF]
    by_cases h : C = C₀
    · simp only [dif_pos h, dif_pos rfl]; exact h.symm
    · simp only [dif_neg h]
      have hspec := (hother C h).choose_spec
      rw [dif_neg hspec.1]
      have hback_spec := (hback (hother C h).choose hspec.1).choose_spec
      exact hdisj_comp hback_spec.2.1 hspec.2.1
  have hright : RightInverse invF toF := by
    intro D'
    dsimp only [toF, invF]
    by_cases h : D' = C₀'
    · simp only [dif_pos h, dif_pos rfl]; exact h.symm
    · simp only [dif_neg h]
      have hspec := (hback D' h).choose_spec
      rw [dif_neg hspec.1]
      have hother_spec := (hother (hback D' h).choose hspec.1).choose_spec
      have he1 := hspec.2.1
      have he2 := hother_spec.2.1
      have hne : (compSet T' c' D').Nonempty := by
        obtain ⟨w, hw⟩ := D'.nonempty_supp
        exact ⟨w.1, (mem_compSet_iff T' c' D' w.1).mpr ⟨w.2, hw⟩⟩
      obtain ⟨x, hx⟩ := hne
      have hxC : x.1 ∈ compSet T c (hback D' h).choose := he1 ▸ mem_map.mpr ⟨x, hx, rfl⟩
      rw [← he2] at hxC
      obtain ⟨x', hx', hxx'⟩ := mem_map.mp hxC
      have hx'_eq : x' = x := Subtype.ext hxx'
      obtain ⟨a1, a2⟩ := (mem_compSet_iff T' c' _ x').mp hx'
      obtain ⟨b1, b2⟩ := (mem_compSet_iff T' c' D' x).mp hx
      have ha_eq : (⟨x', a1⟩ : ({c'}ᶜ : Set ({v}ᶜ : Set U))) = ⟨x, b1⟩ := Subtype.ext hx'_eq
      rw [ha_eq] at a2
      exact ((mem_supp_iff _ _).mp a2).symm.trans ((mem_supp_iff D' _).mp b2)
  refine ⟨C₀', ⟨toF, invF, hleft, hright⟩, ?_, hC0'_card, hC0'_iso, fun C hC => ?_⟩
  · simp [toF]
  · simp only [toF, Equiv.coe_fn_mk, dif_neg hC]
    have hspec := (hother C hC).choose_spec
    refine ⟨?_, by dsimp only [T', c']; exact hspec.2.2⟩
    have h1 : card (hother C hC).choose.supp = (compSet T' c' (hother C hC).choose).card := by
      convert (compSet_card_eq T' c' (hother C hC).choose).symm
    rw [h1, ← card_map (⟨Subtype.val, val_injective⟩ : ({v}ᶜ : Set U) ↪ U), hspec.2.1, compSet_card_eq]
set_option maxHeartbeats 400000 in
private lemma subCount_eq_of_rootedCompIso {U₀ V₁ V₂ : Type} [Fintype U₀] [Fintype V₁] [Fintype V₂]
    (T₀ : SimpleGraph U₀) (c₀ : U₀) (B₀ : Finset U₀)
    (T₁ : SimpleGraph V₁) (c₁ : V₁) (C₁ : (T₁.induce {c₁}ᶜ).ConnectedComponent)
    (T₂ : SimpleGraph V₂) (c₂ : V₂) (C₂ : (T₂.induce {c₂}ᶜ).ConnectedComponent)
    (hiso : RootedCompIso T₁ c₁ C₁ T₂ c₂ C₂) :
    (univ.filter fun R : Finset V₁ =>
      R ⊆ compSet T₁ c₁ C₁ ∧ c₁ ∉ R ∧ RootedIso T₁ c₁ (insert c₁ (R : Set V₁)) T₀ c₀ (insert c₀ (B₀ : Set U₀))).card =
    (univ.filter fun R : Finset V₂ =>
      R ⊆ compSet T₂ c₂ C₂ ∧ c₂ ∉ R ∧ RootedIso T₂ c₂ (insert c₂ (R : Set V₂)) T₀ c₀ (insert c₀ (B₀ : Set U₀))).card := by
  obtain ⟨hc1, hc2, φ, hφc⟩ := hiso
  have hφ_c : ∀ x : V₁, ∀ hx : x ∈ insert c₁ (compSet T₁ c₁ C₁ : Set V₁),
      ((φ ⟨x, hx⟩ : ↥(insert c₂ (compSet T₂ c₂ C₂ : Set V₂))).1 = c₂ ↔ x = c₁) := by
    intro x hx
    constructor
    · intro hval; exact congrArg Subtype.val (φ.injective ((Subtype.ext hval).trans hφc.symm))
    · intro hx1; rcases hx1 with rfl; exact congrArg Subtype.val hφc
  let mapR : ∀ R : Finset V₁, R ⊆ compSet T₁ c₁ C₁ → Finset V₂ := fun R hR =>
    (R.attach.map ⟨fun x : ↥R => (φ ⟨x.1, Set.mem_insert_of_mem c₁ (hR x.2)⟩).1, fun _ _ hab =>
      Subtype.ext (congrArg (fun z : ↥(insert c₁ (compSet T₁ c₁ C₁ : Set V₁)) => z.1) (φ.injective (Subtype.ext hab)))⟩)
  have mapR_iso : ∀ (R : Finset V₁) (hR_sub : R ⊆ compSet T₁ c₁ C₁), c₁ ∉ R →
      RootedIso T₁ c₁ (insert c₁ (R : Set V₁)) T₂ c₂ (insert c₂ (mapR R hR_sub : Set V₂)) := by
    intro R hR_sub hc1R
    refine ⟨Set.mem_insert _ _, Set.mem_insert _ _, ⟨⟨fun x =>
        if hx : x.1 = c₁ then ⟨c₂, Set.mem_insert _ _⟩
        else
          have hxR : x.1 ∈ R := (mem_insert_iff.mp x.2).resolve_left hx
          ⟨(φ ⟨x.1, Set.mem_insert_of_mem c₁ (hR_sub hxR)⟩).1,
            Set.mem_insert_of_mem c₂ (mem_map.mpr ⟨⟨x.1, hxR⟩, mem_attach _ _, rfl⟩)⟩,
      fun y =>
        if hy : y.1 = c₂ then ⟨c₁, Set.mem_insert _ _⟩
        else
          have hyM : y.1 ∈ mapR R hR_sub := (mem_insert_iff.mp y.2).resolve_left hy
          ⟨(mem_map.mp hyM).choose.1, Set.mem_insert_of_mem c₁ (mem_map.mp hyM).choose.2⟩,
      fun x => by
        apply Subtype.ext; dsimp only
        by_cases hx : x.1 = c₁
        · have hx' : x = ⟨c₁, Set.mem_insert _ _⟩ := Subtype.ext hx
          rw [hx']; simp
        · simp only [dif_neg hx]
          have hxR : x.1 ∈ R := (mem_insert_iff.mp x.2).resolve_left hx
          have hne2 : (φ ⟨x.1, Set.mem_insert_of_mem c₁ (hR_sub hxR)⟩).1 ≠ c₂ :=
            fun h => hx ((hφ_c x.1 (Set.mem_insert_of_mem c₁ (hR_sub hxR))).mp h)
          simp only [dif_neg hne2]
          have hsp := (mem_map.mp (mem_map.mpr ⟨⟨x.1, hxR⟩, mem_attach _ _, rfl⟩ :
            (φ ⟨x.1, Set.mem_insert_of_mem c₁ (hR_sub hxR)⟩).1 ∈ mapR R hR_sub)).choose_spec.2
          exact congrArg Subtype.val (φ.injective (Subtype.ext hsp)),
      fun y => by
        apply Subtype.ext; dsimp only
        by_cases hy : y.1 = c₂
        · have hy' : y = ⟨c₂, Set.mem_insert _ _⟩ := Subtype.ext hy
          rw [hy']; simp
        · simp only [dif_neg hy]
          have hyM : y.1 ∈ mapR R hR_sub := (mem_insert_iff.mp y.2).resolve_left hy
          have hsp := (mem_map.mp hyM).choose_spec.2
          have hx_ne : ((mem_map.mp hyM).choose).1 ≠ c₁ := fun h => hc1R (h ▸ (mem_map.mp hyM).choose.2)
          simp only [dif_neg hx_ne]; exact hsp⟩, ?_⟩, by simp⟩
    · intro x₁ x₂
      have hx1 : ¬x₁.1 = c₁ → x₁.1 ∈ compSet T₁ c₁ C₁ := fun h => hR_sub ((mem_insert_iff.mp x₁.2).resolve_left h)
      have hx2 : ¬x₂.1 = c₁ → x₂.1 ∈ compSet T₁ c₁ C₁ := fun h => hR_sub ((mem_insert_iff.mp x₂.2).resolve_left h)
      dsimp only; simp only [Equiv.coe_fn_mk]
      by_cases h1c : x₁.1 = c₁ <;> by_cases h2c : x₂.1 = c₁
      · simp only [dif_pos h1c, dif_pos h2c]
        change T₂.Adj c₂ c₂ ↔ T₁.Adj x₁.1 x₂.1; rw [h1c, h2c]
        exact ⟨fun h => absurd h (T₂.loopless.irrefl _), fun h => absurd h (T₁.loopless.irrefl _)⟩
      · simp only [dif_pos h1c, dif_neg h2c]
        change T₂.Adj c₂ (φ ⟨x₂.1, Set.mem_insert_of_mem c₁ (hx2 h2c)⟩).1 ↔ T₁.Adj x₁.1 x₂.1
        have heq := φ.map_rel_iff (a := ⟨c₁, Set.mem_insert _ _⟩) (b := ⟨x₂.1, Set.mem_insert_of_mem c₁ (hx2 h2c)⟩)
        change T₂.Adj (φ ⟨c₁, _⟩).1 (φ ⟨x₂.1, _⟩).1 ↔ T₁.Adj c₁ x₂.1 at heq
        rw [h1c]; rw [congrArg Subtype.val hφc] at heq; exact heq
      · simp only [dif_neg h1c, dif_pos h2c]
        change T₂.Adj (φ ⟨x₁.1, Set.mem_insert_of_mem c₁ (hx1 h1c)⟩).1 c₂ ↔ T₁.Adj x₁.1 x₂.1
        have heq := φ.map_rel_iff (a := ⟨x₁.1, Set.mem_insert_of_mem c₁ (hx1 h1c)⟩) (b := ⟨c₁, Set.mem_insert _ _⟩)
        change T₂.Adj (φ ⟨x₁.1, _⟩).1 (φ ⟨c₁, _⟩).1 ↔ T₁.Adj x₁.1 c₁ at heq
        rw [h2c]; rw [congrArg Subtype.val hφc] at heq; exact heq
      · simp only [dif_neg h1c, dif_neg h2c]
        have heq := φ.map_rel_iff (a := ⟨x₁.1, Set.mem_insert_of_mem c₁ (hx1 h1c)⟩) (b := ⟨x₂.1, Set.mem_insert_of_mem c₁ (hx2 h2c)⟩)
        change T₂.Adj (φ ⟨x₁.1, _⟩).1 (φ ⟨x₂.1, _⟩).1 ↔ T₁.Adj x₁.1 x₂.1 at heq
        change T₂.Adj (φ ⟨x₁.1, _⟩).1 (φ ⟨x₂.1, _⟩).1 ↔ T₁.Adj x₁.1 x₂.1
        exact heq
  refine card_bij (fun R hR =>
      let hm := (mem_filter.mp hR).2
      mapR R hm.1) ?_ ?_ ?_
  · intro R hR
    obtain ⟨_, hR_sub, hc1R, hR_iso⟩ := mem_filter.mp hR
    refine mem_filter.mpr ⟨mem_univ _, ?_, ?_, (mapR_iso R hR_sub hc1R).symm.trans hR_iso⟩
    · intro y hy
      obtain ⟨x, _, rfl⟩ := mem_map.mp hy
      have hx_ne : x.1 ≠ c₁ := fun h => hc1R (h ▸ x.2)
      have hm := (φ ⟨x.1, Set.mem_insert_of_mem c₁ (hR_sub x.2)⟩).2
      rcases mem_insert_iff.mp hm with hceq | hyC2
      · exact False.elim (hx_ne ((hφ_c x.1 (Set.mem_insert_of_mem c₁ (hR_sub x.2))).mp hceq))
      · exact hyC2
    · intro hc2m
      obtain ⟨x, _, hx⟩ := mem_map.mp hc2m
      exact hc1R (((hφ_c x.1 (Set.mem_insert_of_mem c₁ (hR_sub x.2))).mp hx) ▸ x.2)
  · intro R₁ hR1 R₂ hR2 heq
    obtain ⟨_, h1_sub, hc1R1, _⟩ := mem_filter.mp hR1
    obtain ⟨_, h2_sub, hc1R2, _⟩ := mem_filter.mp hR2
    dsimp only at heq
    ext x
    constructor <;> intro hx
    · have hy : (φ ⟨x, Set.mem_insert_of_mem c₁ (h1_sub hx)⟩).1 ∈ mapR R₂ h2_sub := by
        rw [← heq]; exact mem_map.mpr ⟨⟨x, hx⟩, mem_attach _ _, rfl⟩
      obtain ⟨x', _, hx'⟩ := mem_map.mp hy
      have hxx' : x'.1 = x := congrArg Subtype.val (φ.injective (Subtype.ext hx'))
      exact hxx' ▸ x'.2
    · have hy : (φ ⟨x, Set.mem_insert_of_mem c₁ (h2_sub hx)⟩).1 ∈ mapR R₁ h1_sub := by
        rw [heq]; exact mem_map.mpr ⟨⟨x, hx⟩, mem_attach _ _, rfl⟩
      obtain ⟨x', _, hx'⟩ := mem_map.mp hy
      have hxx' : x'.1 = x := congrArg Subtype.val (φ.injective (Subtype.ext hx'))
      exact hxx' ▸ x'.2
  · intro R₂ hR2
    obtain ⟨_, hR2_sub, hc2R2, hR2_iso⟩ := mem_filter.mp hR2
    let R₁ : Finset V₁ := univ.filter fun x => ∃ hx : x ∈ compSet T₁ c₁ C₁,
      (φ ⟨x, Set.mem_insert_of_mem c₁ hx⟩).1 ∈ R₂
    have hR1_sub : R₁ ⊆ compSet T₁ c₁ C₁ := fun x hx => (mem_filter.mp hx).2.choose
    have hc1R1 : c₁ ∉ R₁ := fun h => c_notMem_compSet T₁ c₁ C₁ (hR1_sub h)
    have hmap_eq : mapR R₁ hR1_sub = R₂ := by
      ext y; constructor <;> intro hy
      · obtain ⟨x, _, rfl⟩ := mem_map.mp hy
        exact (mem_filter.mp x.2).2.choose_spec
      · have hyC2 : y ∈ insert c₂ (compSet T₂ c₂ C₂ : Set V₂) := Set.mem_insert_of_mem c₂ (hR2_sub hy)
        let x := (φ.symm ⟨y, hyC2⟩).1
        have hx_ne : x ≠ c₁ := fun h => hc2R2 (by
          have h1 : φ.symm ⟨y, hyC2⟩ = ⟨c₁, hc1⟩ := Subtype.ext h
          have h2 := congrArg φ h1
          rw [φ.apply_symm_apply, hφc] at h2
          have hv : y = c₂ := congrArg Subtype.val h2
          exact hv ▸ hy)
        have hxC1 : x ∈ compSet T₁ c₁ C₁ := ((φ.symm ⟨y, hyC2⟩).2).resolve_left hx_ne
        have hxR1 : x ∈ R₁ := mem_filter.mpr ⟨mem_univ _, hxC1, by
          have := congrArg Subtype.val (φ.apply_symm_apply ⟨y, hyC2⟩)
          dsimp only at this
          show (φ ⟨x, Set.mem_insert_of_mem c₁ hxC1⟩).1 ∈ R₂
          change (φ (φ.symm ⟨y, hyC2⟩)).1 ∈ R₂
          rwa [this]⟩
        exact mem_map.mpr ⟨⟨x, hxR1⟩, mem_attach _ _,
          congrArg Subtype.val (φ.apply_symm_apply ⟨y, hyC2⟩)⟩
    have hR1_iso : RootedIso T₁ c₁ (insert c₁ (R₁ : Set V₁)) T₀ c₀ (insert c₀ (B₀ : Set U₀)) := by
      have hiso12 : RootedIso T₁ c₁ (insert c₁ (R₁ : Set V₁)) T₂ c₂ (insert c₂ (R₂ : Set V₂)) := by
        rw [← hmap_eq]
        exact mapR_iso R₁ hR1_sub hc1R1
      exact hiso12.trans hR2_iso
    exact ⟨R₁, mem_filter.mpr ⟨mem_univ _, hR1_sub, hc1R1, hR1_iso⟩, hmap_eq⟩
private lemma rVerts_eq_of_rootedCompIso {V₁ V₂ : Type} [Fintype V₁] [Fintype V₂]
    (T₁ : SimpleGraph V₁) (hT1 : T₁.IsTree) (c₁ : V₁) (C₁ : (T₁.induce {c₁}ᶜ).ConnectedComponent)
    (T₂ : SimpleGraph V₂) (hT2 : T₂.IsTree) (c₂ : V₂) (C₂ : (T₂.induce {c₂}ᶜ).ConnectedComponent)
    (r : ℕ) (hiso : RootedCompIso T₁ c₁ C₁ T₂ c₂ C₂) :
    (univ.filter fun y : V₁ => y ∈ compSet T₁ c₁ C₁ ∧ T₁.dist c₁ y = r).card =
    (univ.filter fun y : V₂ => y ∈ compSet T₂ c₂ C₂ ∧ T₂.dist c₂ y = r).card := by
  obtain ⟨hc1, hc2, φ, hφc⟩ := hiso
  have hT1_sub := comp_ins_isTree T₁ hT1 c₁ C₁
  have hT2_sub := comp_ins_isTree T₂ hT2 c₂ C₂
  have hdist1 : ∀ (y : V₁) (hy : y ∈ compSet T₁ c₁ C₁), T₁.dist c₁ y =
      (T₁.induce (insert c₁ (compSet T₁ c₁ C₁ : Set V₁))).dist ⟨c₁, hc1⟩ ⟨y, Set.mem_insert_of_mem c₁ hy⟩ := fun y hy =>
    (dist_induce_eq_of_isTree T₁ hT1 _ hT1_sub ⟨c₁, hc1⟩ ⟨y, Set.mem_insert_of_mem c₁ hy⟩).symm
  have hdist2 : ∀ (y : V₂) (hy : y ∈ compSet T₂ c₂ C₂), T₂.dist c₂ y =
      (T₂.induce (insert c₂ (compSet T₂ c₂ C₂ : Set V₂))).dist ⟨c₂, hc2⟩ ⟨y, Set.mem_insert_of_mem c₂ hy⟩ := fun y hy =>
    (dist_induce_eq_of_isTree T₂ hT2 _ hT2_sub ⟨c₂, hc2⟩ ⟨y, Set.mem_insert_of_mem c₂ hy⟩).symm
  refine card_bij (fun y hy => (φ ⟨y, Set.mem_insert_of_mem c₁ (mem_filter.mp hy).2.1⟩).1) ?_ ?_ ?_
  · intro y hy
    obtain ⟨_, hyC1, hyd⟩ := mem_filter.mp hy
    have hne : (φ ⟨y, Set.mem_insert_of_mem c₁ hyC1⟩).1 ≠ c₂ := fun h => by
      have heqv : y = c₁ := congrArg Subtype.val (φ.injective ((Subtype.ext h).trans hφc.symm))
      exact c_notMem_compSet T₁ c₁ C₁ (heqv ▸ hyC1)
    have hm : (φ ⟨y, Set.mem_insert_of_mem c₁ hyC1⟩).1 ∈ compSet T₂ c₂ C₂ :=
      ((φ ⟨y, Set.mem_insert_of_mem c₁ hyC1⟩).2).resolve_left hne
    refine mem_filter.mpr ⟨mem_univ _, hm, ?_⟩
    calc T₂.dist c₂ (φ ⟨y, Set.mem_insert_of_mem c₁ hyC1⟩).1
        = (T₂.induce (insert c₂ (compSet T₂ c₂ C₂ : Set V₂))).dist ⟨c₂, hc2⟩
            ⟨(φ ⟨y, Set.mem_insert_of_mem c₁ hyC1⟩).1, Set.mem_insert_of_mem c₂ hm⟩ := hdist2 _ hm
      _ = (T₂.induce (insert c₂ (compSet T₂ c₂ C₂ : Set V₂))).dist ⟨c₂, hc2⟩
            (φ ⟨y, Set.mem_insert_of_mem c₁ hyC1⟩) := by rw [coe_eta]
      _ = (T₁.induce (insert c₁ (compSet T₁ c₁ C₁ : Set V₁))).dist ⟨c₁, hc1⟩
            ⟨y, Set.mem_insert_of_mem c₁ hyC1⟩ := by rw [← hφc, iso_dist_eq _ _ φ]
      _ = T₁.dist c₁ y := (hdist1 _ hyC1).symm
      _ = r := hyd
  · intro a ha b hb heq
    exact congrArg Subtype.val (φ.injective (Subtype.ext heq))
  · intro z hz
    obtain ⟨_, hzC2, hzd⟩ := mem_filter.mp hz
    let y := (φ.symm ⟨z, Set.mem_insert_of_mem c₂ hzC2⟩).1
    have hne : y ≠ c₁ := fun h => c_notMem_compSet T₂ c₂ C₂ (by
      have h1 := congrArg φ (Subtype.ext h : φ.symm ⟨z, Set.mem_insert_of_mem c₂ hzC2⟩ = ⟨c₁, hc1⟩)
      rw [φ.apply_symm_apply, hφc] at h1
      have hv : c₂ = z := congrArg Subtype.val h1.symm
      exact hv ▸ hzC2)
    have hyC1 : y ∈ compSet T₁ c₁ C₁ := ((φ.symm ⟨z, Set.mem_insert_of_mem c₂ hzC2⟩).2).resolve_left hne
    have hyd : T₁.dist c₁ y = r := by
      rw [hdist1 y hyC1, ← iso_dist_eq _ _ φ, hφc]
      have h2 := φ.apply_symm_apply ⟨z, Set.mem_insert_of_mem c₂ hzC2⟩
      change (T₂.induce _).dist ⟨c₂, hc2⟩ (φ (φ.symm ⟨z, Set.mem_insert_of_mem c₂ hzC2⟩)) = r
      rw [h2, ← hdist2 z hzC2, hzd]
    exact ⟨y, mem_filter.mpr ⟨mem_univ _, hyC1, hyd⟩,
      congrArg Subtype.val (φ.apply_symm_apply ⟨z, Set.mem_insert_of_mem c₂ hzC2⟩)⟩
private lemma subCount_eq_one_if_card_eq {U₀ V' : Type} [Fintype U₀] [Fintype V']
    (T₀ : SimpleGraph U₀) (c₀ : U₀) (B₀ : Finset U₀) (hc0_not : c₀ ∉ B₀)
    (T : SimpleGraph V') (c : V') (D : (T.induce {c}ᶜ).ConnectedComponent)
    (hcard : card D.supp = B₀.card) :
    (univ.filter fun R : Finset V' =>
      R ⊆ compSet T c D ∧ c ∉ R ∧ RootedIso T c (insert c (R : Set V')) T₀ c₀ (insert c₀ (B₀ : Set U₀))).card =
      if RootedIso T c (insert c (compSet T c D : Set V')) T₀ c₀ (insert c₀ (B₀ : Set U₀)) then 1 else 0 := by
  split_ifs with h
  · rw [Finset.card_eq_one]
    refine ⟨compSet T c D, ?_⟩
    ext R; rw [mem_filter, mem_singleton]
    constructor
    · rintro ⟨_, hsub, hcR, hiso⟩
      have hc1 : (insert c R).card = (insert c₀ B₀).card :=
        RootedIso.card_eq (by simpa only [coe_insert] using hiso)
      rw [card_insert_of_notMem hcR, card_insert_of_notMem hc0_not] at hc1
      exact eq_of_subset_of_card_le hsub (by rw [compSet_card_eq, hcard]; omega)
    · rintro rfl; exact ⟨mem_univ _, Finset.Subset.rfl, c_notMem_compSet T c D, h⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro R _ ⟨hsub, hcR, hiso⟩
    have hc1 : (insert c R).card = (insert c₀ B₀).card :=
      RootedIso.card_eq (by simpa only [coe_insert] using hiso)
    rw [card_insert_of_notMem hcR, card_insert_of_notMem hc0_not] at hc1
    have heq := eq_of_subset_of_card_le hsub (by rw [compSet_card_eq, hcard]; omega)
    exact h (heq ▸ hiso)
private lemma subCount_eq_zero_if_card_lt {U₀ V' : Type} [Fintype U₀] [Fintype V']
    (T₀ : SimpleGraph U₀) (c₀ : U₀) (B₀ : Finset U₀) (hc0_not : c₀ ∉ B₀)
    (T : SimpleGraph V') (c : V') (D : (T.induce {c}ᶜ).ConnectedComponent)
    (hlt : card D.supp < B₀.card) :
    (univ.filter fun R : Finset V' =>
      R ⊆ compSet T c D ∧ c ∉ R ∧ RootedIso T c (insert c (R : Set V')) T₀ c₀ (insert c₀ (B₀ : Set U₀))).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro R _ ⟨hsub, hcR, hiso⟩
  have hc1 : (insert c R).card = (insert c₀ B₀).card := RootedIso.card_eq (by simpa only [coe_insert] using hiso)
  rw [card_insert_of_notMem hcR, card_insert_of_notMem hc0_not] at hc1
  have := (card_le_card hsub).trans (compSet_card_eq T c D).le
  omega
/-! ### Part 5: General case and main theorem -/
private lemma compSet_connected {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) (c : U) (D : (T.induce {c}ᶜ).ConnectedComponent) :
    (T.induce (compSet T c D : Set U)).Connected := by
  obtain ⟨x, hx⟩ := D.nonempty_supp
  have : Nonempty (compSet T c D : Set U) := ⟨⟨x.1, (mem_compSet_iff T c D x.1).mpr ⟨x.2, hx⟩⟩⟩
  refine Connected.mk fun ⟨a, ha⟩ ⟨b, hb⟩ => ?_
  obtain ⟨ha1, ha2⟩ := (mem_compSet_iff T c D a).mp ha
  obtain ⟨hb1, hb2⟩ := (mem_compSet_iff T c D b).mp hb
  obtain ⟨w⟩ := ((hT.isAcyclic.induce {c}ᶜ).isTree_connectedComponent D).connected
    ⟨⟨a, ha1⟩, ha2⟩ ⟨⟨b, hb1⟩, hb2⟩
  let g : D.toSimpleGraph →g T.induce (compSet T c D : Set U) :=
    ⟨fun z => ⟨z.1.1, (mem_compSet_iff T c D z.1.1).mpr ⟨z.1.2, z.2⟩⟩, @fun _ _ h => h⟩
  exact ⟨(w.map g).copy rfl rfl⟩
private lemma not_rootedIso_path_of_card_gt {U : Type} [Fintype U]
    (T : SimpleGraph U) (c : U) (D : (T.induce {c}ᶜ).ConnectedComponent)
    {r : ℕ} (hcard : r + 1 ≤ card D.supp) :
    ¬ RootedIso T c (insert c (compSet T c D : Set U))
        (pathG (r + 1)) ⟨0, Nat.zero_lt_succ r⟩ Set.univ := by
  intro hiso
  have hiso' : RootedIso T c ((insert c (compSet T c D) : Finset U) : Set U)
      (pathG (r + 1)) ⟨0, Nat.zero_lt_succ r⟩ ((univ : Finset (Fin (r + 1))) : Set (Fin (r + 1))) := by
    simpa only [coe_insert, Finset.coe_univ] using hiso
  have hceq := hiso'.card_eq
  rw [card_insert_of_notMem (c_notMem_compSet T c D), card_univ, card_fin,
    compSet_card_eq] at hceq
  omega
private lemma exists_pos_rTotal_diff {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {r : ℕ} (hr : 2 ≤ r) (hdiam : T.diam = 2 * r)
    (c : U) (hecc : T.eccent c = r) (D : (T.induce {c}ᶜ).ConnectedComponent) :
    1 ≤ (univ.filter fun y : U => T.dist c y = r).card -
        (univ.filter fun y : U => y ∈ compSet T c D ∧ T.dist c y = r).card := by
  obtain ⟨C₁, hne, x, hx_mem, hx_dist⟩ := exists_other_diam_comp T hT hr hdiam c hecc D
  let A := univ.filter fun y : U => T.dist c y = r
  let B := univ.filter fun y : U => y ∈ compSet T c D ∧ T.dist c y = r
  have hsub : B ⊆ A := fun y hy => mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hy).2.2⟩
  rw [← card_sdiff_of_subset hsub]
  refine card_pos.mpr ⟨x, mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _, hx_dist⟩, ?_⟩⟩
  intro hBx
  have hxD : x ∈ compSet T c D := (mem_filter.mp hBx).2.1
  exact (Finset.disjoint_left.mp (compSet_disjoint T c hne) hx_mem) hxD
private lemma comp_erase_count_eq {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) (c : U)
    (hnoLeaf : ∀ u : U, T.Adj c u → 2 ≤ T.degree u)
    {v : U} (hv1 : T.degree v = 1) (hvc : v ≠ c)
    (D : (T.induce {c}ᶜ).ConnectedComponent) (hvD : v ∈ compSet T c D)
    {M : ℕ} (hmax : ∀ C : (T.induce {c}ᶜ).ConnectedComponent, card C.supp ≤ M) :
    let T' := T.induce ({v}ᶜ : Set U)
    let c' : ({v}ᶜ : Set U) := ⟨c, hvc.symm⟩
    let m := (univ.filter fun C : (T.induce {c}ᶜ).ConnectedComponent => card C.supp = M).card
    let m' := (univ.filter fun C' : (T'.induce {c'}ᶜ).ConnectedComponent => card C'.supp = M).card
    (card D.supp = M → m' + 1 = m) ∧ (card D.supp < M → m' = m) := by
  intro T' c' m m'
  obtain ⟨D', ι, hιD, hD'_card, _, hother⟩ := comp_erase_bij T hT c hnoLeaf hv1 hvc D hvD
  have hD'_lt : card D'.supp < M := by have := hmax D; omega
  have hm'_eq : m' = (univ.filter fun C : (T.induce {c}ᶜ).ConnectedComponent =>
      C ≠ D ∧ card C.supp = M).card := by
    refine card_bij (fun C' _ => ι.symm C') ?_ ?_ ?_
    · intro C' hC'
      have hcard' : card C'.supp = M := (mem_filter.mp hC').2
      have hne' : C' ≠ D' := fun h => by subst h; omega
      have hne : ι.symm C' ≠ D := fun h => hne' (by rw [← ι.apply_symm_apply C', h, hιD])
      have heq := (hother (ι.symm C') hne).1
      rw [ι.apply_symm_apply] at heq
      exact mem_filter.mpr ⟨mem_univ _, hne, heq.symm.trans hcard'⟩
    · intro a _ b _ h; exact ι.symm.injective h
    · intro C hC
      obtain ⟨_, hne, hcardC⟩ := mem_filter.mp hC
      refine ⟨ι C, mem_filter.mpr ⟨mem_univ _, (hother C hne).1.trans hcardC⟩, ι.symm_apply_apply C⟩
  constructor
  · intro hDM
    have hsplit : univ.filter (fun C : (T.induce {c}ᶜ).ConnectedComponent => card C.supp = M) =
        insert D (univ.filter fun C : (T.induce {c}ᶜ).ConnectedComponent =>
          C ≠ D ∧ card C.supp = M) := by
      ext C; simp only [mem_filter, mem_insert, mem_univ, true_and]
      constructor
      · intro hC
        by_cases h : C = D
        · left; exact h
        · right; exact ⟨h, hC⟩
      · rintro (rfl | ⟨_, hC⟩) <;> assumption
    have hnot : D ∉ univ.filter (fun C : (T.induce {c}ᶜ).ConnectedComponent =>
        C ≠ D ∧ card C.supp = M) := fun h => (mem_filter.mp h).2.1 rfl
    change m' + 1 = m
    rw [hm'_eq]
    dsimp only [m]
    rw [hsplit, card_insert_of_notMem hnot]
  · intro hDlt
    change m' = m
    rw [hm'_eq]
    dsimp only [m]
    congr 1; ext C; simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨fun heq => by subst heq; omega, h⟩⟩
private lemma iso_transport_maxComp_count {V₁ V₂ : Type} [Fintype V₁] [Fintype V₂]
    (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂) (c₁ : V₁) (c₂ : V₂)
    (φ : G₁ ≃g G₂) (hφc : φ c₁ = c₂) (M : ℕ) :
    (univ.filter fun C : (G₁.induce {c₁}ᶜ).ConnectedComponent => card C.supp = M).card =
    (univ.filter fun D : (G₂.induce {c₂}ᶜ).ConnectedComponent => card D.supp = M).card := by
  obtain ⟨e, he⟩ := iso_transport_comp G₁ G₂ c₁ c₂ φ hφc
  refine card_bij (fun C _ => e C) ?_ ?_ ?_
  · intro C hC
    exact mem_filter.mpr ⟨mem_univ _, (he C).1.trans (mem_filter.mp hC).2⟩
  · intro a _ b _ h; exact e.injective h
  · intro D hD
    refine ⟨e.symm D, mem_filter.mpr ⟨mem_univ _, ?_⟩, e.apply_symm_apply D⟩
    have h1 := (he (e.symm D)).1
    rw [e.apply_symm_apply] at h1
    exact h1.symm.trans (mem_filter.mp hD).2
private lemma fintype_card_cast {α : Type} (i₁ i₂ : Fintype α) :
    @card α i₁ = @card α i₂ := by
  obtain rfl : i₁ = i₂ := Subsingleton.elim _ _
  rfl
private lemma RootedCompIso.cast_both {V W : Type} {iV₁ : Fintype V} [iV₂ : Fintype V]
    {iW₁ : Fintype W} [iW₂ : Fintype W]
    {G : SimpleGraph V} {cG : V} {C : (G.induce {cG}ᶜ).ConnectedComponent}
    {H : SimpleGraph W} {cH : W} {D : (H.induce {cH}ᶜ).ConnectedComponent}
    (h : @RootedCompIso V W iV₁ iW₁ G cG C H cH D) :
    @RootedCompIso V W iV₂ iW₂ G cG C H cH D := by
  obtain rfl : iV₁ = iV₂ := Subsingleton.elim _ _
  obtain rfl : iW₁ = iW₂ := Subsingleton.elim _ _
  exact h
private lemma card_filter_card_norm {α : Type} {β : α → Type}
    {i₁ : Fintype α} (i₂ : Fintype α)
    {j₁ : ∀ a, Fintype (β a)} (j₂ : ∀ a, Fintype (β a))
    (M : ℕ) {d₁ : DecidablePred fun a => @card (β a) (j₁ a) = M}
    (d₂ : DecidablePred fun a => @card (β a) (j₂ a) = M) :
    (@univ α i₁ |>.filter (fun a => @card (β a) (j₁ a) = M)).card =
    (@univ α i₂ |>.filter (fun a => @card (β a) (j₂ a) = M)).card := by
  obtain rfl : i₁ = i₂ := Subsingleton.elim _ _
  exact congrArg Finset.card (Finset.filter_congr fun a _ => by rw [@fintype_card_cast (β a) (j₁ a) (j₂ a)])
private lemma comp_erase_count_norm {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) (c : U)
    (hnoLeaf : ∀ u : U, T.Adj c u → 2 ≤ T.degree u)
    {v : U} (hv1 : T.degree v = 1) (hvc : v ≠ c)
    (D : (T.induce {c}ᶜ).ConnectedComponent) (hvD : v ∈ compSet T c D)
    {M : ℕ} (hmax : ∀ C : (T.induce {c}ᶜ).ConnectedComponent, card C.supp ≤ M) :
    (card D.supp = M →
      (univ.filter fun C' : ((T.induce {v}ᶜ).induce ({⟨c, hvc.symm⟩}ᶜ)).ConnectedComponent =>
        card C'.supp = M).card + 1 =
      (univ.filter fun C : (T.induce {c}ᶜ).ConnectedComponent => card C.supp = M).card) ∧
    (card D.supp < M →
      (univ.filter fun C' : ((T.induce {v}ᶜ).induce ({⟨c, hvc.symm⟩}ᶜ)).ConnectedComponent =>
        card C'.supp = M).card =
      (univ.filter fun C : (T.induce {c}ᶜ).ConnectedComponent => card C.supp = M).card) := by
  have h := comp_erase_count_eq T hT c hnoLeaf hv1 hvc D hvD hmax
  dsimp only at h
  refine ⟨fun hM => ?_, fun hlt => ?_⟩
  · have h1 := h.1 hM
    rw [card_filter_card_norm (α := ((T.induce {v}ᶜ).induce ({⟨c, hvc.symm⟩}ᶜ)).ConnectedComponent)
          inferInstance (fun _ => inferInstance) M inferInstance,
        card_filter_card_norm (α := (T.induce {c}ᶜ).ConnectedComponent)
          inferInstance (fun _ => inferInstance) M inferInstance] at h1
    exact h1
  · have h2 := h.2 hlt
    rw [card_filter_card_norm (α := ((T.induce {v}ᶜ).induce ({⟨c, hvc.symm⟩}ᶜ)).ConnectedComponent)
          inferInstance (fun _ => inferInstance) M inferInstance,
        card_filter_card_norm (α := (T.induce {c}ᶜ).ConnectedComponent)
          inferInstance (fun _ => inferInstance) M inferInstance] at h2
    exact h2
private lemma pairsOut_card_eq {V' : Type} [Fintype V']
    (T : SimpleGraph V') (c : V') (D : (T.induce {c}ᶜ).ConnectedComponent) (r : ℕ) (hr : 1 ≤ r) :
    (univ.filter fun p : V' × V' =>
      p.1 ∉ compSet T c D ∧ p.2 ∉ compSet T c D ∧ T.dist c p.1 = r ∧ T.dist c p.2 = r ∧
      ∃ (h1 : p.1 ≠ c) (h2 : p.2 ≠ c),
        (T.induce {c}ᶜ).connectedComponentMk ⟨p.1, h1⟩ ≠
        (T.induce {c}ᶜ).connectedComponentMk ⟨p.2, h2⟩).card =
    ∑ D₁ : (T.induce {c}ᶜ).ConnectedComponent,
      if D₁ = D then 0 else
        (univ.filter fun y : V' => y ∈ compSet T c D₁ ∧ T.dist c y = r).card *
        ((univ.filter fun y : V' => T.dist c y = r).card -
          (univ.filter fun y : V' => y ∈ compSet T c D ∧ T.dist c y = r).card -
          (univ.filter fun y : V' => y ∈ compSet T c D₁ ∧ T.dist c y = r).card) := by
  let Pairs := univ.filter fun p : V' × V' =>
    p.1 ∉ compSet T c D ∧ p.2 ∉ compSet T c D ∧ T.dist c p.1 = r ∧ T.dist c p.2 = r ∧
    ∃ (h1 : p.1 ≠ c) (h2 : p.2 ≠ c),
      (T.induce {c}ᶜ).connectedComponentMk ⟨p.1, h1⟩ ≠
      (T.induce {c}ᶜ).connectedComponentMk ⟨p.2, h2⟩
  let A := univ.filter fun y : V' => T.dist c y = r
  let BD := univ.filter fun y : V' => y ∈ compSet T c D ∧ T.dist c y = r
  let B (D₁ : (T.induce {c}ᶜ).ConnectedComponent) :=
    univ.filter fun y : V' => y ∈ compSet T c D₁ ∧ T.dist c y = r
  let S_rhs := (univ.filter fun D₁ : (T.induce {c}ᶜ).ConnectedComponent => D₁ ≠ D).sigma fun D₁ =>
    (B D₁) ×ˢ (univ.filter fun y : V' => y ∉ compSet T c D ∧ y ∉ compSet T c D₁ ∧ T.dist c y = r)
  have hdiff : ∀ D₁ : (T.induce {c}ᶜ).ConnectedComponent, D₁ ≠ D →
      (univ.filter fun y : V' => y ∉ compSet T c D ∧ y ∉ compSet T c D₁ ∧ T.dist c y = r).card =
      A.card - BD.card - (B D₁).card := by
    intro D₁ hD1D
    have hsub1 : BD ⊆ A := fun y hy => mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hy).2.2⟩
    have hsub2 : B D₁ ⊆ A \ BD := by
      intro y hy
      obtain ⟨_, hy1, hy2⟩ := mem_filter.mp hy
      refine mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _, hy2⟩, fun hyB => ?_⟩
      exact (Finset.disjoint_left.mp (compSet_disjoint T c hD1D) hy1) (mem_filter.mp hyB).2.1
    have heq : univ.filter (fun y : V' => y ∉ compSet T c D ∧ y ∉ compSet T c D₁ ∧ T.dist c y = r) =
        (A \ BD) \ B D₁ := by
      ext y; simp only [A, BD, B, mem_sdiff, mem_filter, mem_univ, true_and]; tauto
    rw [heq, card_sdiff_of_subset hsub2, card_sdiff_of_subset hsub1]
  have hS : S_rhs.card = ∑ D₁ : (T.induce {c}ᶜ).ConnectedComponent,
      if D₁ = D then 0 else (B D₁).card * (A.card - BD.card - (B D₁).card) := by
    rw [card_sigma]
    have hs : ∀ D₁ ∈ univ.filter (fun D₁ : (T.induce {c}ᶜ).ConnectedComponent => D₁ ≠ D),
        ((B D₁) ×ˢ (univ.filter fun y : V' =>
          y ∉ compSet T c D ∧ y ∉ compSet T c D₁ ∧ T.dist c y = r)).card =
        (B D₁).card * (A.card - BD.card - (B D₁).card) := fun D₁ hD1 => by
      rw [card_product, hdiff D₁ (mem_filter.mp hD1).2]
    rw [sum_congr rfl hs, Finset.sum_filter]
    refine sum_congr rfl fun D₁ _ => ?_
    split_ifs with h1 h2 <;> simp_all
  change Pairs.card = _
  rw [← hS]
  refine card_bij (fun p hp =>
      let hp' := (mem_filter.mp hp).2
      let h1 : p.1 ≠ c := hp'.2.2.2.2.choose
      ⟨(T.induce {c}ᶜ).connectedComponentMk ⟨p.1, h1⟩, p⟩) ?_ ?_ ?_
  · intro p hp
    obtain ⟨_, hp1_not, hp2_not, hp1_r, hp2_r, h1, h2, hne⟩ := mem_filter.mp hp
    let D₁ := (T.induce {c}ᶜ).connectedComponentMk ⟨p.1, h1⟩
    have hD1D : D₁ ≠ D := fun heq => hp1_not (heq ▸ (mem_compSet_iff T c D₁ p.1).mpr ⟨h1, rfl⟩)
    have hp2_not_D1 : p.2 ∉ compSet T c D₁ := fun hm => by
      obtain ⟨_, h2m⟩ := (mem_compSet_iff T c D₁ p.2).mp hm
      exact hne ((mem_supp_iff D₁ _).mp h2m).symm
    exact mem_sigma.mpr ⟨mem_filter.mpr ⟨mem_univ _, hD1D⟩,
      mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _,
        (mem_compSet_iff T c D₁ p.1).mpr ⟨h1, rfl⟩, hp1_r⟩,
        mem_filter.mpr ⟨mem_univ _, hp2_not, hp2_not_D1, hp2_r⟩⟩⟩
  · intro a _ b _ h
    exact (Sigma.ext_iff.mp h).2 |> eq_of_heq
  · rintro ⟨D₁, p⟩ hp
    obtain ⟨hD1, hpprod⟩ := mem_sigma.mp hp
    have hD1D : D₁ ≠ D := (mem_filter.mp hD1).2
    obtain ⟨hp1, hp2⟩ := mem_product.mp hpprod
    obtain ⟨_, hp1_D1, hp1_r⟩ := mem_filter.mp hp1
    obtain ⟨_, hp2_notD, hp2_notD1, hp2_r⟩ := mem_filter.mp hp2
    have h1 : p.1 ≠ c := fun h => by rw [h, dist_self] at hp1_r; omega
    have h2 : p.2 ≠ c := fun h => by rw [h, dist_self] at hp2_r; omega
    have hD1_eq : (T.induce {c}ᶜ).connectedComponentMk ⟨p.1, h1⟩ = D₁ :=
      (mem_supp_iff D₁ ⟨p.1, h1⟩).mp ((mem_compSet_iff T c D₁ p.1).mp hp1_D1).2
    have hp1_notD : p.1 ∉ compSet T c D := fun h =>
      (Finset.disjoint_left.mp (compSet_disjoint T c hD1D) hp1_D1) h
    have hne : (T.induce {c}ᶜ).connectedComponentMk ⟨p.1, h1⟩ ≠
        (T.induce {c}ᶜ).connectedComponentMk ⟨p.2, h2⟩ := by
      rw [hD1_eq]
      intro h
      exact hp2_notD1 ((mem_compSet_iff T c D₁ p.2).mpr ⟨h2, h.symm⟩)
    refine ⟨p, mem_filter.mpr ⟨mem_univ _, hp1_notD, hp2_notD, hp1_r, hp2_r, h1, h2, hne⟩, ?_⟩
    exact Sigma.ext hD1_eq (heq_of_eq rfl)
private lemma exists_diam_pair_comps {U : Type} [Fintype U]
    (T : SimpleGraph U) (hT : T.IsTree) {r : ℕ} (hr : 2 ≤ r) (hdiam : T.diam = 2 * r)
    (c : U) (hecc : T.eccent c = r) :
    ∃ (C₁ C₂ : (T.induce {c}ᶜ).ConnectedComponent), C₁ ≠ C₂ ∧
      (∃ x ∈ compSet T c C₁, T.dist c x = r) ∧
      (∃ y ∈ compSet T c C₂, T.dist c y = r) := by
  have : Nonempty U := hT.connected.nonempty
  obtain ⟨x0, xd, hxd⟩ := T.exists_dist_eq_diam
  obtain ⟨p, hp, hplen⟩ := hT.connected.exists_path_of_dist x0 xd
  obtain ⟨hc_mem, hcx0, hcxd⟩ := diam_path_contains_center T hT c hecc p hp (hplen.trans (hxd.trans hdiam))
  have hx0_ne : x0 ≠ c := fun h => by rw [← h, dist_self] at hcx0; omega
  have hxd_ne : xd ≠ c := fun h => by rw [← h, dist_self] at hcxd; omega
  let C₁ := (T.induce {c}ᶜ).connectedComponentMk ⟨x0, hx0_ne⟩
  let C₂ := (T.induce {c}ᶜ).connectedComponentMk ⟨xd, hxd_ne⟩
  have hne : C₁ ≠ C₂ := by
    intro heq
    obtain ⟨q⟩ := ConnectedComponent.exact heq
    let q_path := q.toPath
    let g : T.induce {c}ᶜ →g T := (Embedding.induce ({c}ᶜ : Set U)).toHom
    have hqG : (q_path.val.map g).IsPath := q_path.isPath.map val_injective
    have hqp := isTree_path_eq T hT hqG hp
    have hc_not : c ∉ (q_path.val.map g).support := by
      rw [Walk.support_map, List.mem_map]; rintro ⟨y, _, hyc⟩; exact y.2 hyc
    rw [hqp] at hc_not
    exact hc_not hc_mem
  exact ⟨C₁, C₂, hne, ⟨x0, (mem_compSet_iff T c C₁ x0).mpr ⟨hx0_ne, rfl⟩, hcx0⟩,
    ⟨xd, (mem_compSet_iff T c C₂ xd).mpr ⟨hxd_ne, rfl⟩, hcxd⟩⟩
private lemma kelly_Q2_rTotal_lt {U₁ U₂ : Type} [Fintype U₁] [Fintype U₂]
    {r M M₀ : ℕ}
    (T₁ : SimpleGraph U₁) (hT1 : T₁.IsTree) (c₁ : U₁) (hecc1 : T₁.eccent c₁ = r)
    (T₂ : SimpleGraph U₂) (hT2 : T₂.IsTree) (c₂ : U₂) (hecc2 : T₂.eccent c₂ = r)
    (hr : 2 ≤ r) (hdiam1 : T₁.diam = 2 * r) (hdiam2 : T₂.diam = 2 * r)
    (hmax1 : ∀ C : (T₁.induce {c₁}ᶜ).ConnectedComponent, card C.supp ≤ M)
    (hmax2 : ∀ D : (T₂.induce {c₂}ᶜ).ConnectedComponent, card D.supp ≤ M)
    (A : (T₁.induce {c₁}ᶜ).ConnectedComponent) (B : (T₂.induce {c₂}ᶜ).ConnectedComponent)
    (hA_card : card A.supp = M₀) (hB_card : card B.supp = M₀)
    (hM0 : r + 1 ≤ M₀) (hgtM : M < M₀ + 1 + r) (hM_le : M ≤ M₀ + 1)
    (hforce : M₀ = M ∨ ∃ b ∈ compSet T₁ c₁ A, r ≤ T₁.dist c₁ b)
    (hne_iso : ¬ RootedCompIso T₁ c₁ A T₂ c₂ B)
    (π : (T₁.induce {c₁}ᶜ).ConnectedComponent ≃ (T₂.induce {c₂}ᶜ).ConnectedComponent)
    (hπA : π A = B)
    (hmatch : ∀ C, C ≠ A →
      ((univ.filter fun R : Finset U₁ =>
          R ⊆ compSet T₁ c₁ C ∧ c₁ ∉ R ∧
          RootedIso T₁ c₁ (insert c₁ (R : Set U₁)) T₁ c₁ (insert c₁ (compSet T₁ c₁ A : Set U₁))).card =
        (univ.filter fun R : Finset U₂ =>
          R ⊆ compSet T₂ c₂ (π C) ∧ c₂ ∉ R ∧
          RootedIso T₂ c₂ (insert c₂ (R : Set U₂)) T₁ c₁ (insert c₁ (compSet T₁ c₁ A : Set U₁))).card) ∧
      ((univ.filter fun R : Finset U₁ =>
          R ⊆ compSet T₁ c₁ C ∧ c₁ ∉ R ∧
          RootedIso T₁ c₁ (insert c₁ (R : Set U₁)) T₁ c₁ (insert c₁ (compSet T₁ c₁ A : Set U₁))).card ≠ 0 →
        (univ.filter fun y : U₁ => y ∈ compSet T₁ c₁ C ∧ T₁.dist c₁ y = r).card =
        (univ.filter fun y : U₂ => y ∈ compSet T₂ c₂ (π C) ∧ T₂.dist c₂ y = r).card))
    (hncard_eq :
      {S : Finset U₁ | Nonempty (T₁.induce (S : Set U₁) ≃g Q2 T₁ c₁ (compSet T₁ c₁ A) r)}.ncard =
      {S : Finset U₂ | Nonempty (T₂.induce (S : Set U₂) ≃g Q2 T₁ c₁ (compSet T₁ c₁ A) r)}.ncard) :
    (univ.filter fun y : U₁ => T₁.dist c₁ y = r).card <
    (univ.filter fun y : U₂ => T₂.dist c₂ y = r).card := by
  let B₀ := compSet T₁ c₁ A
  have hB0_card : B₀.card = M₀ := by rw [compSet_card_eq, hA_card]
  have hc0_not : c₁ ∉ B₀ := c_notMem_compSet T₁ c₁ A
  have hB0_conn : (T₁.induce (B₀ : Set U₁)).Connected := compSet_connected T₁ hT1 c₁ A
  have hB0_root : ∃ b ∈ B₀, T₁.Adj c₁ b := by
    obtain ⟨u, ⟨hu_mem, hu_adj⟩, _⟩ := existsUnique_root_of_component T₁ hT1 c₁ A
    exact ⟨u.1, (mem_compSet_iff T₁ c₁ A u.1).mpr ⟨u.2, hu_mem⟩, hu_adj⟩
  have hnot_path := not_rootedIso_path_of_card_gt T₁ c₁ A (by rw [hA_card]; omega)
  have hgtM' : M < B₀.card + 1 + r := by rw [hB0_card]; exact hgtM
  have hM_le' : M ≤ B₀.card + 1 := by rw [hB0_card]; exact hM_le
  have hforce' : B₀.card = M ∨ ∃ b ∈ B₀, r ≤ T₁.dist c₁ b := by
    rcases hforce with h | h; exact Or.inl (hB0_card.trans h); exact Or.inr h
  have heq1 := Q2_subgraphs_card_eq T₁ hT1 c₁ B₀ hc0_not hB0_conn hB0_root r M hr hnot_path hgtM' hM_le' hforce'
    T₁ hT1 c₁ hecc1 hmax1
  have heq2 := Q2_subgraphs_card_eq T₁ hT1 c₁ B₀ hc0_not hB0_conn hB0_root r M hr hnot_path hgtM' hM_le' hforce'
    T₂ hT2 c₂ hecc2 hmax2
  by_contra hnot_lt
  have hr_le : (univ.filter fun y : U₂ => T₂.dist c₂ y = r).card ≤
      (univ.filter fun y : U₁ => T₁.dist c₁ y = r).card := by omega
  let rT1 := (univ.filter fun y : U₁ => T₁.dist c₁ y = r).card
  let rT2 := (univ.filter fun y : U₂ => T₂.dist c₂ y = r).card
  let v1 (C : (T₁.induce {c₁}ᶜ).ConnectedComponent) :=
    (univ.filter fun y : U₁ => y ∈ compSet T₁ c₁ C ∧ T₁.dist c₁ y = r).card
  let v2 (D : (T₂.induce {c₂}ᶜ).ConnectedComponent) :=
    (univ.filter fun y : U₂ => y ∈ compSet T₂ c₂ D ∧ T₂.dist c₂ y = r).card
  let a1 (C : (T₁.induce {c₁}ᶜ).ConnectedComponent) :=
    (univ.filter fun R : Finset U₁ =>
      R ⊆ compSet T₁ c₁ C ∧ c₁ ∉ R ∧ RootedIso T₁ c₁ (insert c₁ (R : Set U₁)) T₁ c₁ (insert c₁ (B₀ : Set U₁))).card
  let a2 (D : (T₂.induce {c₂}ᶜ).ConnectedComponent) :=
    (univ.filter fun R : Finset U₂ =>
      R ⊆ compSet T₂ c₂ D ∧ c₂ ∉ R ∧ RootedIso T₂ c₂ (insert c₂ (R : Set U₂)) T₁ c₁ (insert c₁ (B₀ : Set U₁))).card
  have ha1_A : a1 A = 1 := by
    have h1 := subCount_eq_one_if_card_eq T₁ c₁ B₀ hc0_not T₁ c₁ A (by rw [hB0_card, hA_card])
    change a1 A = _ at h1
    rw [h1, if_pos (RootedIso.refl T₁ c₁ (Set.mem_insert _ _))]
  have ha2_B : a2 B = 0 := by
    have h2 := subCount_eq_one_if_card_eq T₁ c₁ B₀ hc0_not T₂ c₂ B (by rw [hB0_card, hB_card])
    change a2 B = _ at h2
    have hno : ¬ RootedIso T₂ c₂ (insert c₂ (compSet T₂ c₂ B : Set U₂)) T₁ c₁ (insert c₁ (B₀ : Set U₁)) := fun h =>
      hne_iso h.symm
    rw [h2, if_neg hno]
  have hsum1 : a1 A * (rT1 - v1 A) + ∑ C ∈ univ.erase A, a1 C * (rT1 - v1 C) =
      ∑ C : (T₁.induce {c₁}ᶜ).ConnectedComponent, a1 C * (rT1 - v1 C) :=
    add_sum_erase univ (fun C => a1 C * (rT1 - v1 C)) (mem_univ A)
  have hsum2 : a2 B * (rT2 - v2 B) + ∑ D ∈ univ.erase B, a2 D * (rT2 - v2 D) =
      ∑ D : (T₂.induce {c₂}ᶜ).ConnectedComponent, a2 D * (rT2 - v2 D) :=
    add_sum_erase univ (fun D => a2 D * (rT2 - v2 D)) (mem_univ B)
  have hpi_sum : ∑ D ∈ univ.erase B, a2 D * (rT2 - v2 D) =
      ∑ C ∈ univ.erase A, a2 (π C) * (rT2 - v2 (π C)) := by
    symm
    refine sum_bij (fun C _ => π C) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro C hC
      have hCA := (mem_erase.mp hC).1
      exact mem_erase.mpr ⟨fun h => hCA (π.injective (h.trans hπA.symm)), mem_univ _⟩
    · intro C₁ _ C₂ _ h; exact π.injective h
    · intro D hD
      have hDB := (mem_erase.mp hD).1
      exact ⟨π.symm D, mem_erase.mpr ⟨fun h => hDB (by rw [← hπA, ← h, π.apply_symm_apply]), mem_univ _⟩, π.apply_symm_apply D⟩
  have hle_sum : ∑ C ∈ univ.erase A, a2 (π C) * (rT2 - v2 (π C)) ≤
      ∑ C ∈ univ.erase A, a1 C * (rT1 - v1 C) := by
    refine Finset.sum_le_sum fun C hC => ?_
    have hCA := (mem_erase.mp hC).1
    obtain ⟨ha_eq, hv_eq⟩ := hmatch C hCA
    change a1 C = a2 (π C) at ha_eq
    by_cases h0 : a1 C = 0
    · rw [← ha_eq, h0]; simp
    · have hv := hv_eq h0
      change v1 C = v2 (π C) at hv
      rw [← ha_eq, ← hv]
      exact Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hr_le _)
  have hpos_A : 1 ≤ a1 A * (rT1 - v1 A) := by
    rw [ha1_A, one_mul]
    exact exists_pos_rTotal_diff T₁ hT1 hr hdiam1 c₁ hecc1 A
  have hrhs_eq : ∑ C : (T₁.induce {c₁}ᶜ).ConnectedComponent, a1 C * (rT1 - v1 C) =
      ∑ D : (T₂.induce {c₂}ᶜ).ConnectedComponent, a2 D * (rT2 - v2 D) := by
    rw [← heq1, ← heq2, hncard_eq]
  rw [← hsum1, ← hsum2, ha2_B, zero_mul, zero_add, hpi_sum] at hrhs_eq
  omega
private lemma general_case_h1_mH {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (hTG : G.IsTree) (hTH : H.IsTree)
    {r M : ℕ} (hr : 2 ≤ r) (hdiamG : G.diam = 2 * r)
    (cG : V) (cH : W) (heccG : G.eccent cG = r) (heccH : H.eccent cH = r)
    (hmaxH : ∀ D : (H.induce {cH}ᶜ).ConnectedComponent, card D.supp ≤ M)
    (hkelly : ∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
      card U < card V →
      {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard =
        {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard)
    (C₀ : (G.induce {cG}ᶜ).ConnectedComponent)
    (hM : r + 1 ≤ M) (hC0_card : card C₀.supp = M)
    (hltV : M + 1 + r < card V) :
    ∃ D₀ : (H.induce {cH}ᶜ).ConnectedComponent, card D₀.supp = M := by
  let B_C0 := compSet G cG C₀
  let Q_C0 := Q2 G cG B_C0 r
  have hB_C0_card : B_C0.card = M := by rw [compSet_card_eq, hC0_card]
  have hQ_C0_lt : card (Option (↥B_C0 ⊕ Fin r)) < card V := by
    rw [card_option, card_sum, card_coe, card_fin, hB_C0_card]
    omega
  obtain ⟨C_o2, hCo2_ne, x_o2, hxo2_mem, hxo2_dist⟩ := exists_other_diam_comp G hTG hr hdiamG cG heccG C₀
  have hxo2_not : x_o2 ∉ B_C0 := fun h =>
    (Finset.disjoint_left.mp (compSet_disjoint G cG hCo2_ne.symm) h) hxo2_mem
  obtain ⟨ψG⟩ := Q2_induce_union_iso G cG B_C0 (c_notMem_compSet G cG C₀) G hTG hr cG C₀
    Finset.Subset.rfl (c_notMem_compSet G cG C₀) (RootedIso.refl G cG (Set.mem_insert _ _)) hxo2_not hxo2_dist
  let S_G : Finset V := insert cG (B_C0 ∪ pathTail G hTG cG x_o2)
  have hSG_mem : S_G ∈ {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q_C0)} := by
    rw [Set.mem_setOf_eq]
    exact ⟨by dsimp only [S_G, B_C0, Q_C0]; rw [coe_insert, coe_union]; exact ψG⟩
  have hposG : 0 < {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q_C0)}.ncard :=
    (Set.ncard_pos).mpr ⟨S_G, hSG_mem⟩
  have hposH : 0 < {S : Finset W | Nonempty (H.induce (S : Set W) ≃g Q_C0)}.ncard := by
    rw [← hkelly _ Q_C0 hQ_C0_lt]; exact hposG
  obtain ⟨S_H, hSH_mem⟩ := Set.nonempty_of_ncard_ne_zero (by omega : {S : Finset W | Nonempty (H.induce (S : Set W) ≃g Q_C0)}.ncard ≠ 0)
  obtain ⟨ψH⟩ := hSH_mem
  obtain ⟨hcH_S, hψH_c⟩ := Q2_center_forced G hTG cG B_C0 (c_notMem_compSet G cG C₀)
    (comp_ins_isTree G hTG cG C₀).connected H hTH hr cH heccH hmaxH (by rw [hB_C0_card]; omega)
    (by rw [hB_C0_card]; omega) (Or.inl hB_C0_card) S_H ψH
  let R_H : Finset W := univ.image fun b : ↥B_C0 => (ψH.symm (some (Sum.inl b))).1
  have hcH_not_RH : cH ∉ R_H := by
    intro hcH_in
    obtain ⟨b, _, hb⟩ := mem_image.mp hcH_in
    have h1 : ψH.symm (some (Sum.inl b)) = ⟨cH, hcH_S⟩ := Subtype.ext hb
    have h2 := congrArg ψH h1
    rw [ψH.apply_symm_apply, hψH_c] at h2
    simp at h2
  have hRH_ne : R_H.Nonempty := by
    have hneB : B_C0.Nonempty := by rw [← card_pos, hB_C0_card]; omega
    obtain ⟨b, hb⟩ := hneB
    exact ⟨_, mem_image.mpr ⟨⟨b, hb⟩, mem_univ _, rfl⟩⟩
  have hRH_card : R_H.card = M := by
    rw [← hB_C0_card, ← card_coe B_C0, ← card_univ (α := ↥B_C0)]
    exact Finset.card_image_of_injective _ fun b₁ b₂ h => by
      have h1 : ψH.symm (some (Sum.inl b₁)) = ψH.symm (some (Sum.inl b₂)) := Subtype.ext h
      have h2 := ψH.symm.injective h1
      exact Sum.inl.inj (Option.some.inj h2)
  have hRH_conn : (H.induce (R_H : Set W)).Connected := by
    have : Nonempty (R_H : Set W) := ⟨⟨hRH_ne.choose, hRH_ne.choose_spec⟩⟩
    let g : G.induce (B_C0 : Set V) →g H.induce (R_H : Set W) :=
      ⟨fun b => ⟨(ψH.symm (some (Sum.inl b))).1, Finset.mem_image_of_mem _ (mem_univ b)⟩, by
        intro b₁ b₂ hadj
        change (H.induce (S_H : Set W)).Adj (ψH.symm (some (Sum.inl b₁))) (ψH.symm (some (Sum.inl b₂)))
        exact (ψH.symm.map_rel_iff).mpr hadj⟩
    refine Connected.mk fun x y => ?_
    obtain ⟨bx, _, hbx⟩ := mem_image.mp x.2
    obtain ⟨by_, _, hby⟩ := mem_image.mp y.2
    obtain ⟨w⟩ := (compSet_connected G hTG cG C₀) bx by_
    exact ⟨(w.map g).copy (Subtype.ext hbx) (Subtype.ext hby)⟩
  obtain ⟨D₀, _, hRD0⟩ := subset_comp_of_connected H cH R_H hRH_ne hcH_not_RH hRH_conn
  exact ⟨D₀, le_antisymm (hmaxH D₀) (hRH_card ▸ hRD0)⟩
private lemma general_case_subcase_p0_lt {V₁ V₂ : Type} [Fintype V₁] [Fintype V₂]
    {r M : ℕ} (hr : 2 ≤ r) (hM : r + 1 ≤ M)
    (T₁ : SimpleGraph V₁) (hT1 : T₁.IsTree) (c₁ : V₁) (hecc1 : T₁.eccent c₁ = r)
    (hdiam1 : T₁.diam = 2 * r)
    (T₂ : SimpleGraph V₂) (hT2 : T₂.IsTree) (c₂ : V₂) (hecc2 : T₂.eccent c₂ = r)
    (hdiam2 : T₂.diam = 2 * r)
    (hltV1 : M + 1 + r < card V₁) (hcard12 : card V₁ = card V₂)
    (hmax1 : ∀ C : (T₁.induce {c₁}ᶜ).ConnectedComponent, card C.supp ≤ M)
    (hmax2 : ∀ D : (T₂.induce {c₂}ᶜ).ConnectedComponent, card D.supp ≤ M)
    (E₁ : (T₁.induce {c₁}ᶜ).ConnectedComponent)
    (E₂ : (T₂.induce {c₂}ᶜ).ConnectedComponent)
    (hE1_card : card E₁.supp = M - 1)
    (hE2_card : card E₂.supp = M - 1)
    (hnot_E : ¬ RootedCompIso T₁ c₁ E₁ T₂ c₂ E₂)
    (π : (T₁.induce {c₁}ᶜ).ConnectedComponent ≃ (T₂.induce {c₂}ᶜ).ConnectedComponent)
    (hπE : π E₁ = E₂)
    (hall_ne : ∀ C, C ≠ E₁ → RootedCompIso T₁ c₁ C T₂ c₂ (π C))
    (P0 : ℕ) (hP0_pos : 1 ≤ P0)
    (hp1_zero : (univ.filter fun y : V₁ => y ∈ compSet T₁ c₁ E₁ ∧ T₁.dist c₁ y = r).card = 0)
    (hp2_pos : 1 ≤ (univ.filter fun y : V₂ => y ∈ compSet T₂ c₂ E₂ ∧ T₂.dist c₂ y = r).card)
    (hr1_eq : (univ.filter fun y : V₁ => T₁.dist c₁ y = r).card =
      (univ.filter fun y : V₁ => y ∈ compSet T₁ c₁ E₁ ∧ T₁.dist c₁ y = r).card + P0)
    (hr2_eq : (univ.filter fun y : V₂ => T₂.dist c₂ y = r).card =
      (univ.filter fun y : V₂ => y ∈ compSet T₂ c₂ E₂ ∧ T₂.dist c₂ y = r).card + P0)
    (hkelly_rev : ∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
      card U < card V₁ →
      {S : Finset V₂ | Nonempty (T₂.induce (S : Set V₂) ≃g Q)}.ncard =
        {S : Finset V₁ | Nonempty (T₁.induce (S : Set V₁) ≃g Q)}.ncard) :
    False := by
  by_cases hM_eq : M = r + 1
  · have hpath_lt1 : card (Fin (2 * r + 1)) < card V₁ := by
      rw [card_fin]; omega
    have hpath_lt2 : card (Fin (2 * r + 1)) < card V₂ := by
      rw [← hcard12]; exact hpath_lt1
    have heq1 := path2r1_two_mul_subgraphs_card_eq T₁ hT1 hr c₁ hecc1 (fun D => by have := hmax1 D; omega)
    have heq2 := path2r1_two_mul_subgraphs_card_eq T₂ hT2 hr c₂ hecc2 (fun D => by have := hmax2 D; omega)
    have hkelly_p := (hkelly_rev (Fin (2 * r + 1)) (pathG (2 * r + 1)) hpath_lt1).symm
    set p1 := (univ.filter fun y : V₁ => y ∈ compSet T₁ c₁ E₁ ∧ T₁.dist c₁ y = r).card
    set p2 := (univ.filter fun y : V₂ => y ∈ compSet T₂ c₂ E₂ ∧ T₂.dist c₂ y = r).card
    set r1 := (univ.filter fun y : V₁ => T₁.dist c₁ y = r).card
    set r2 := (univ.filter fun y : V₂ => T₂.dist c₂ y = r).card
    let v1 (C : (T₁.induce {c₁}ᶜ).ConnectedComponent) :=
      (univ.filter fun y : V₁ => y ∈ compSet T₁ c₁ C ∧ T₁.dist c₁ y = r).card
    let v2 (D : (T₂.induce {c₂}ᶜ).ConnectedComponent) :=
      (univ.filter fun y : V₂ => y ∈ compSet T₂ c₂ D ∧ T₂.dist c₂ y = r).card
    have hr1_eq' : r1 = p1 + P0 := hr1_eq
    have hr2_eq' : r2 = p2 + P0 := hr2_eq
    have hr_lt : r1 < r2 := by omega
    have hsum_eq : ∑ C : (T₁.induce {c₁}ᶜ).ConnectedComponent, v1 C * (r1 - v1 C) =
        ∑ D : (T₂.induce {c₂}ᶜ).ConnectedComponent, v2 D * (r2 - v2 D) := by
      rw [← heq1, ← heq2, hkelly_p]
    have hsplit1 := add_sum_erase univ (fun C => v1 C * (r1 - v1 C)) (mem_univ E₁)
    have hsplit2 := add_sum_erase univ (fun D => v2 D * (r2 - v2 D)) (mem_univ E₂)
    have hvE1_0 : v1 E₁ = 0 := hp1_zero
    have hvE2_p2 : v2 E₂ = p2 := rfl
    have hE2_term_pos : 1 ≤ v2 E₂ * (r2 - v2 E₂) := by
      rw [hvE2_p2]
      have hsub : r2 - p2 = P0 := by omega
      rw [hsub]
      exact Nat.mul_pos hp2_pos hP0_pos
    have hle_sum : ∑ C ∈ univ.erase E₁, v1 C * (r1 - v1 C) ≤
        ∑ D ∈ univ.erase E₂, v2 D * (r2 - v2 D) := by
      have hbij : ∑ C ∈ univ.erase E₁, v1 C * (r1 - v1 C) =
          ∑ D ∈ univ.erase E₂, v1 (π.symm D) * (r1 - v1 (π.symm D)) := by
        refine sum_bij (fun C _ => π C) ?_ (fun _ _ _ _ h => π.injective h) ?_ ?_
        · intro C hC
          have hCE := (mem_erase.mp hC).1
          exact mem_erase.mpr ⟨fun h => hCE (π.injective (h.trans hπE.symm)), mem_univ _⟩
        · intro D hD
          have hDE2 := (mem_erase.mp hD).1
          exact ⟨π.symm D, mem_erase.mpr ⟨fun h => hDE2 (by rw [← hπE, ← h, π.apply_symm_apply]), mem_univ _⟩,
            π.apply_symm_apply D⟩
        · intro C _; rw [π.symm_apply_apply]
      rw [hbij]
      refine Finset.sum_le_sum fun D hD => ?_
      have hDE2 := (mem_erase.mp hD).1
      have hCE1 : π.symm D ≠ E₁ := fun h => hDE2 (by rw [← hπE, ← h, π.apply_symm_apply])
      have hv := rVerts_eq_of_rootedCompIso T₁ hT1 c₁ (π.symm D) T₂ hT2 c₂ D r
        (by have := hall_ne (π.symm D) hCE1; rwa [π.apply_symm_apply] at this)
      change v1 (π.symm D) = v2 D at hv
      rw [hv]
      exact Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hr_lt.le _)
    have h1 : v1 E₁ * (r1 - v1 E₁) = 0 := by rw [hvE1_0, zero_mul]
    linarith [hsum_eq, hsplit1, hsplit2, h1, hE2_term_pos, hle_sum]
  · have hM_ge : r + 2 ≤ M := by omega
    let B_E2 := compSet T₂ c₂ E₂
    have hB_E2_card : B_E2.card = M - 1 := by rw [compSet_card_eq, hE2_card]
    have hQ_E2_lt : card (Option (↥B_E2 ⊕ Fin r)) < card V₁ := by
      rw [card_option, card_sum, card_coe, card_fin, hB_E2_card]
      omega
    have hforce_E2 : ∃ b ∈ B_E2, r ≤ T₂.dist c₂ b := by
      obtain ⟨b, hb⟩ := card_pos.mp hp2_pos
      obtain ⟨_, hbE2, hbd⟩ := mem_filter.mp hb
      exact ⟨b, hbE2, hbd.ge⟩
    have hmatch_E2 : ∀ D, D ≠ E₂ →
        ((univ.filter fun R : Finset V₂ =>
            R ⊆ compSet T₂ c₂ D ∧ c₂ ∉ R ∧ RootedIso T₂ c₂ (insert c₂ (R : Set V₂)) T₂ c₂ (insert c₂ (B_E2 : Set V₂))).card =
          (univ.filter fun R : Finset V₁ =>
            R ⊆ compSet T₁ c₁ (π.symm D) ∧ c₁ ∉ R ∧ RootedIso T₁ c₁ (insert c₁ (R : Set V₁)) T₂ c₂ (insert c₂ (B_E2 : Set V₂))).card) ∧
        ((univ.filter fun R : Finset V₂ =>
            R ⊆ compSet T₂ c₂ D ∧ c₂ ∉ R ∧ RootedIso T₂ c₂ (insert c₂ (R : Set V₂)) T₂ c₂ (insert c₂ (B_E2 : Set V₂))).card ≠ 0 →
          (univ.filter fun y : V₂ => y ∈ compSet T₂ c₂ D ∧ T₂.dist c₂ y = r).card =
          (univ.filter fun y : V₁ => y ∈ compSet T₁ c₁ (π.symm D) ∧ T₁.dist c₁ y = r).card) := by
      intro D hDE2
      have hCE1 : π.symm D ≠ E₁ := fun h => hDE2 (by rw [← hπE, ← h, π.apply_symm_apply])
      have hiso : RootedCompIso T₂ c₂ D T₁ c₁ (π.symm D) := by
        have := (hall_ne (π.symm D) hCE1).symm
        rwa [π.apply_symm_apply] at this
      exact ⟨subCount_eq_of_rootedCompIso T₂ c₂ B_E2 T₂ c₂ D T₁ c₁ (π.symm D) hiso,
        fun _ => rVerts_eq_of_rootedCompIso T₂ hT2 c₂ D T₁ hT1 c₁ (π.symm D) r hiso⟩
    have hlt := kelly_Q2_rTotal_lt T₂ hT2 c₂ hecc2 T₁ hT1 c₁ hecc1 hr hdiam2 hdiam1 hmax2 hmax1
      E₂ E₁ hE2_card hE1_card (by omega) (by omega) (by omega) (Or.inr hforce_E2) (fun h => hnot_E h.symm)
      π.symm (by rw [← hπE, π.symm_apply_apply]) hmatch_E2 (hkelly_rev _ (Q2 T₂ c₂ B_E2 r) hQ_E2_lt)
    omega
private lemma general_case_subcase_A {V W : Type} [Fintype V] [Fintype W]
    {r M : ℕ} (hr : 2 ≤ r) (hM : r + 1 ≤ M)
    (G : SimpleGraph V) (H : SimpleGraph W) (hTG : G.IsTree) (hTH : H.IsTree)
    (hdiamG : G.diam = 2 * r) (cG : V) (cH : W) (heccG : G.eccent cG = r) (heccH : H.eccent cH = r)
    (hmaxG : ∀ C : (G.induce {cG}ᶜ).ConnectedComponent, card C.supp ≤ M)
    (hmaxH : ∀ D : (H.induce {cH}ᶜ).ConnectedComponent, card D.supp ≤ M)
    (hltV : M + 1 + r < card V)
    (hkelly : ∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
      card U < card V →
      {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard =
        {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard)
    (C₀ E : (G.induce {cG}ᶜ).ConnectedComponent)
    (E' : (H.induce {cH}ᶜ).ConnectedComponent)
    (hEC0 : E ≠ C₀) (hC0_card : card C₀.supp = M)
    (hE_card : card E.supp = M - 1) (hE'_card : card E'.supp = M - 1)
    (hnot_E : ¬ RootedCompIso G cG E H cH E')
    (π₁ : (G.induce {cG}ᶜ).ConnectedComponent ≃ (H.induce {cH}ᶜ).ConnectedComponent)
    (hπ1_E : π₁ E = E')
    (hall_ne_E : ∀ C, C ≠ E → card (π₁ C).supp = card C.supp ∧ RootedCompIso G cG C H cH (π₁ C))
    (hpE0 : (univ.filter fun y : V => y ∈ compSet G cG E ∧ G.dist cG y = r).card = 0)
    (hpE'0 : (univ.filter fun y : W => y ∈ compSet H cH E' ∧ H.dist cH y = r).card = 0)
    (hrG_eq_hrH : (univ.filter fun y : V => G.dist cG y = r).card =
      (univ.filter fun y : W => H.dist cH y = r).card) :
    False := by
  obtain ⟨Cx, Cy, hCxy, ⟨x_d, hxd_mem, hxd_dist⟩, ⟨y_d, hyd_mem, hyd_dist⟩⟩ :=
    exists_diam_pair_comps G hTG hr hdiamG cG heccG
  have hCx_ne_E : Cx ≠ E := fun h => by
    have hpos : 0 < (univ.filter fun y : V => y ∈ compSet G cG E ∧ G.dist cG y = r).card :=
      card_pos.mpr ⟨x_d, mem_filter.mpr ⟨mem_univ _, h ▸ hxd_mem, hxd_dist⟩⟩
    omega
  have hCy_ne_E : Cy ≠ E := fun h => by
    have hpos : 0 < (univ.filter fun y : V => y ∈ compSet G cG E ∧ G.dist cG y = r).card :=
      card_pos.mpr ⟨y_d, mem_filter.mpr ⟨mem_univ _, h ▸ hyd_mem, hyd_dist⟩⟩
    omega
  have hV_gt_M2r : M + 2 * r < card V := by
    obtain ⟨Cz, hzE, hzC0, hz_card⟩ : ∃ Cz : (G.induce {cG}ᶜ).ConnectedComponent,
        Cz ≠ E ∧ Cz ≠ C₀ ∧ r ≤ card Cz.supp := by
      by_cases h1 : Cx = C₀
      · exact ⟨Cy, hCy_ne_E, fun h => hCxy (h1.trans h.symm),
          hyd_dist ▸ comp_dist_ge_of_mem G hTG cG Cy ((mem_compSet_iff G cG Cy y_d).mp hyd_mem).2⟩
      · exact ⟨Cx, hCx_ne_E, h1,
          hxd_dist ▸ comp_dist_ge_of_mem G hTG cG Cx ((mem_compSet_iff G cG Cx x_d).mp hxd_mem).2⟩
    have hsumV := sum_card_connectedComponent_eq G cG
    have h1 := add_sum_erase univ (fun C : (G.induce {cG}ᶜ).ConnectedComponent => card C.supp)
      (mem_univ C₀)
    have h2 := add_sum_erase (univ.erase C₀) (fun C : (G.induce {cG}ᶜ).ConnectedComponent => card C.supp)
      (mem_erase.mpr ⟨hEC0, mem_univ _⟩)
    have h3 : card Cz.supp ≤ ∑ C ∈ (univ.erase C₀).erase E, card C.supp :=
      single_le_sum (f := fun C : (G.induce {cG}ᶜ).ConnectedComponent => card C.supp)
        (fun _ _ => Nat.zero_le _) (mem_erase.mpr ⟨hzE, mem_erase.mpr ⟨hzC0, mem_univ _⟩⟩)
    omega
  let B_E := compSet G cG E
  have hB_E_card : B_E.card = M - 1 := by rw [compSet_card_eq, hE_card]
  have hQ3_lt : card (Option (↥B_E ⊕ (Fin r ⊕ Fin r))) < card V := by
    rw [card_option, card_sum, card_sum, card_coe,
      card_fin, hB_E_card]
    omega
  have hB_E_no_r : ∀ b ∈ B_E, G.dist cG b ≤ r - 1 := by
    intro b hb
    have hle := dist_le_of_eccent G hTG (u := b) heccG
    have hne : G.dist cG b ≠ r := fun h => by
      have hpos : 0 < (univ.filter fun y : V => y ∈ compSet G cG E ∧ G.dist cG y = r).card :=
        card_pos.mpr ⟨b, mem_filter.mpr ⟨mem_univ _, hb, h⟩⟩
      omega
    omega
  have hB_E_root : ∃ b ∈ B_E, G.Adj cG b := by
    obtain ⟨u, ⟨hu_mem, hu_adj⟩, _⟩ := existsUnique_root_of_component G hTG cG E
    exact ⟨u.1, (mem_compSet_iff G cG E u.1).mpr ⟨u.2, hu_mem⟩, hu_adj⟩
  have heqQ3_G := Q3_two_mul_subgraphs_card_eq G hTG cG B_E (c_notMem_compSet G cG E)
    (compSet_connected G hTG cG E) hB_E_root r M hr hB_E_no_r hB_E_card (by omega)
    G hTG cG heccG hmaxG
  have heqQ3_H := Q3_two_mul_subgraphs_card_eq G hTG cG B_E (c_notMem_compSet G cG E)
    (compSet_connected G hTG cG E) hB_E_root r M hr hB_E_no_r hB_E_card (by omega)
    H hTH cH heccH hmaxH
  have hkelly_Q3 := hkelly _ (Q3 G cG B_E r) hQ3_lt
  have hrV_all : ∀ C, (univ.filter fun y : V => y ∈ compSet G cG C ∧ G.dist cG y = r).card =
      (univ.filter fun y : W => y ∈ compSet H cH (π₁ C) ∧ H.dist cH y = r).card := by
    intro C
    by_cases hCE : C = E
    · subst hCE; rw [hπ1_E, hpE0, hpE'0]
    · exact rVerts_eq_of_rootedCompIso G hTG cG C H hTH cH (π₁ C) r (hall_ne_E C hCE).2
  have hpairs_match : ∀ C, C ≠ E →
      (univ.filter fun p : V × V =>
        p.1 ∉ compSet G cG C ∧ p.2 ∉ compSet G cG C ∧ G.dist cG p.1 = r ∧ G.dist cG p.2 = r ∧
        ∃ (h1 : p.1 ≠ cG) (h2 : p.2 ≠ cG),
          (G.induce {cG}ᶜ).connectedComponentMk ⟨p.1, h1⟩ ≠
          (G.induce {cG}ᶜ).connectedComponentMk ⟨p.2, h2⟩).card =
      (univ.filter fun p : W × W =>
        p.1 ∉ compSet H cH (π₁ C) ∧ p.2 ∉ compSet H cH (π₁ C) ∧ H.dist cH p.1 = r ∧ H.dist cH p.2 = r ∧
        ∃ (h1 : p.1 ≠ cH) (h2 : p.2 ≠ cH),
          (H.induce {cH}ᶜ).connectedComponentMk ⟨p.1, h1⟩ ≠
          (H.induce {cH}ᶜ).connectedComponentMk ⟨p.2, h2⟩).card := by
    intro C _
    rw [pairsOut_card_eq G cG C r (by omega), pairsOut_card_eq H cH (π₁ C) r (by omega)]
    refine Fintype.sum_equiv π₁ _ _ fun D₁ => ?_
    by_cases hD1 : D₁ = C
    · subst hD1; simp
    · have hne : π₁ D₁ ≠ π₁ C := fun h => hD1 (π₁.injective h)
      rw [if_neg hD1, if_neg hne, hrV_all D₁, hrV_all C, hrG_eq_hrH]
  let termG (C : (G.induce {cG}ᶜ).ConnectedComponent) :=
    (univ.filter fun R : Finset V =>
      R ⊆ compSet G cG C ∧ cG ∉ R ∧ RootedIso G cG (insert cG (R : Set V)) G cG (insert cG (B_E : Set V))).card *
    (univ.filter fun p : V × V =>
      p.1 ∉ compSet G cG C ∧ p.2 ∉ compSet G cG C ∧ G.dist cG p.1 = r ∧ G.dist cG p.2 = r ∧
      ∃ (h1 : p.1 ≠ cG) (h2 : p.2 ≠ cG),
        (G.induce {cG}ᶜ).connectedComponentMk ⟨p.1, h1⟩ ≠
        (G.induce {cG}ᶜ).connectedComponentMk ⟨p.2, h2⟩).card
  let termH (D : (H.induce {cH}ᶜ).ConnectedComponent) :=
    (univ.filter fun R : Finset W =>
      R ⊆ compSet H cH D ∧ cH ∉ R ∧ RootedIso H cH (insert cH (R : Set W)) G cG (insert cG (B_E : Set V))).card *
    (univ.filter fun p : W × W =>
      p.1 ∉ compSet H cH D ∧ p.2 ∉ compSet H cH D ∧ H.dist cH p.1 = r ∧ H.dist cH p.2 = r ∧
      ∃ (h1 : p.1 ≠ cH) (h2 : p.2 ≠ cH),
        (H.induce {cH}ᶜ).connectedComponentMk ⟨p.1, h1⟩ ≠
        (H.induce {cH}ᶜ).connectedComponentMk ⟨p.2, h2⟩).card
  have hterm_E_pos : 1 ≤ termG E := by
    have hsub1 : (univ.filter fun R : Finset V =>
        R ⊆ compSet G cG E ∧ cG ∉ R ∧
        RootedIso G cG (insert cG (R : Set V)) G cG (insert cG (B_E : Set V))).card = 1 := by
      rw [subCount_eq_one_if_card_eq G cG B_E (c_notMem_compSet G cG E) G cG E (by rw [hB_E_card, hE_card])]
      exact if_pos (RootedIso.refl G cG (Set.mem_insert _ _))
    have hxd_not : x_d ∉ B_E := fun h =>
      (Finset.disjoint_left.mp (compSet_disjoint G cG hCx_ne_E) hxd_mem) h
    have hyd_not : y_d ∉ B_E := fun h =>
      (Finset.disjoint_left.mp (compSet_disjoint G cG hCy_ne_E) hyd_mem) h
    have hxd_c : x_d ≠ cG := (mem_compSet_iff G cG Cx x_d).mp hxd_mem |>.1
    have hyd_c : y_d ≠ cG := (mem_compSet_iff G cG Cy y_d).mp hyd_mem |>.1
    have hpair_pos : 1 ≤ (univ.filter fun p : V × V =>
        p.1 ∉ B_E ∧ p.2 ∉ B_E ∧ G.dist cG p.1 = r ∧ G.dist cG p.2 = r ∧
        ∃ (h1 : p.1 ≠ cG) (h2 : p.2 ≠ cG),
          (G.induce {cG}ᶜ).connectedComponentMk ⟨p.1, h1⟩ ≠
          (G.induce {cG}ᶜ).connectedComponentMk ⟨p.2, h2⟩).card := by
      refine card_pos.mpr ⟨(x_d, y_d), mem_filter.mpr ⟨mem_univ _,
        hxd_not, hyd_not, hxd_dist, hyd_dist, hxd_c, hyd_c, ?_⟩⟩
      rwa [(mem_supp_iff Cx ⟨x_d, hxd_c⟩).mp ((mem_compSet_iff G cG Cx x_d).mp hxd_mem).2,
        (mem_supp_iff Cy ⟨y_d, hyd_c⟩).mp ((mem_compSet_iff G cG Cy y_d).mp hyd_mem).2]
    exact Nat.mul_pos (by omega) hpair_pos
  have hterm_E'_0 : termH E' = 0 := by
    have hsub0 : (univ.filter fun R : Finset W =>
        R ⊆ compSet H cH E' ∧ cH ∉ R ∧
        RootedIso H cH (insert cH (R : Set W)) G cG (insert cG (B_E : Set V))).card = 0 := by
      rw [subCount_eq_one_if_card_eq G cG B_E (c_notMem_compSet G cG E) H cH E' (by rw [hB_E_card, hE'_card])]
      exact if_neg (fun h => hnot_E h.symm)
    simp [termH, hsub0]
  have hsumG_eq : ∑ C : (G.induce {cG}ᶜ).ConnectedComponent, termG C =
      ∑ D : (H.induce {cH}ᶜ).ConnectedComponent, termH D := by
    rw [← heqQ3_G, ← heqQ3_H, hkelly_Q3]
  have hsplitG := add_sum_erase univ termG (mem_univ E)
  have hsplitH := add_sum_erase univ termH (mem_univ E')
  have hpi_sum : ∑ D ∈ univ.erase E', termH D = ∑ C ∈ univ.erase E, termG C := by
    refine sum_bij (fun D _ => π₁.symm D) ?_ (fun _ _ _ _ h => π₁.symm.injective h) ?_ ?_
    · intro D hD
      have hDE' := (mem_erase.mp hD).1
      exact mem_erase.mpr ⟨fun h => hDE' (by rw [← hπ1_E, ← h, π₁.apply_symm_apply]), mem_univ _⟩
    · intro C hC
      have hCE := (mem_erase.mp hC).1
      exact ⟨π₁ C, mem_erase.mpr ⟨fun h => hCE (π₁.injective (h.trans hπ1_E.symm)), mem_univ _⟩,
        π₁.symm_apply_apply C⟩
    · intro D hD
      have hDE' := (mem_erase.mp hD).1
      have hCE : π₁.symm D ≠ E := fun h => hDE' (by rw [← hπ1_E, ← h, π₁.apply_symm_apply])
      have ha := subCount_eq_of_rootedCompIso G cG B_E G cG (π₁.symm D) H cH D
        (by have := (hall_ne_E (π₁.symm D) hCE).2; rwa [π₁.apply_symm_apply] at this)
      have hp := hpairs_match (π₁.symm D) hCE
      rw [π₁.apply_symm_apply] at hp
      simp only [termG, termH, ha, hp]
  linarith [hsumG_eq, hsplitG, hsplitH, hterm_E_pos, hterm_E'_0, hpi_sum]
private lemma general_case_subcase_D {V W : Type} [Fintype V] [Fintype W]
    {r M : ℕ} (hr : 2 ≤ r) (hM : r + 1 ≤ M)
    (G : SimpleGraph V) (H : SimpleGraph W) (hTG : G.IsTree) (hTH : H.IsTree)
    (hdiamG : G.diam = 2 * r) (hdiamH : H.diam = 2 * r)
    (cG : V) (cH : W) (heccG : G.eccent cG = r) (heccH : H.eccent cH = r)
    (hmaxG : ∀ C : (G.induce {cG}ᶜ).ConnectedComponent, card C.supp ≤ M)
    (hmaxH : ∀ D : (H.induce {cH}ᶜ).ConnectedComponent, card D.supp ≤ M)
    (hltV : M + 1 + r < card V) (hcardVW : card V = card W)
    (hkelly : ∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
      card U < card V →
      {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard =
        {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard)
    (hkelly_rev : ∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
      card U < card V →
      {S : Finset W | Nonempty (H.induce (S : Set W) ≃g Q)}.ncard =
        {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard)
    (E : (G.induce {cG}ᶜ).ConnectedComponent)
    (E' : (H.induce {cH}ᶜ).ConnectedComponent)
    (hE_card : card E.supp = M - 1) (hE'_card : card E'.supp = M - 1)
    (hnot_E : ¬ RootedCompIso G cG E H cH E')
    (π₁ : (G.induce {cG}ᶜ).ConnectedComponent ≃ (H.induce {cH}ᶜ).ConnectedComponent)
    (hπ1_E : π₁ E = E')
    (hall_ne_E : ∀ C, C ≠ E → card (π₁ C).supp = card C.supp ∧ RootedCompIso G cG C H cH (π₁ C))
    (hpE_pos : 1 ≤ (univ.filter fun y : V => y ∈ compSet G cG E ∧ G.dist cG y = r).card)
    (hpE'_pos : 1 ≤ (univ.filter fun y : W => y ∈ compSet H cH E' ∧ H.dist cH y = r).card) :
    False := by
  by_cases hM_eq : M = r + 1
  · obtain ⟨x_e, hx_e⟩ := card_pos.mp hpE_pos
    obtain ⟨_, hx_e_E, hx_e_d⟩ := mem_filter.mp hx_e
    obtain ⟨y_e, hy_e⟩ := card_pos.mp hpE'_pos
    obtain ⟨_, hy_e_E', hy_e_d⟩ := mem_filter.mp hy_e
    exact hnot_E (rootedCompIso_of_path_r G H hTG hTH (by omega) cG cH heccG heccH
      E (by omega) ((mem_compSet_iff G cG E x_e).mp hx_e_E).2 hx_e_d
      E' (by omega) ((mem_compSet_iff H cH E' y_e).mp hy_e_E').2 hy_e_d)
  · have hM_ge : r + 2 ≤ M := by omega
    let B_E := compSet G cG E
    have hB_E_card : B_E.card = M - 1 := by rw [compSet_card_eq, hE_card]
    have hQ_E_lt : card (Option (↥B_E ⊕ Fin r)) < card V := by
      rw [card_option, card_sum, card_coe, card_fin, hB_E_card]
      omega
    have hforce_E : ∃ b ∈ B_E, r ≤ G.dist cG b := by
      obtain ⟨b, hb⟩ := card_pos.mp hpE_pos
      obtain ⟨_, hbE, hbd⟩ := mem_filter.mp hb
      exact ⟨b, hbE, hbd.ge⟩
    have hmatch_E : ∀ C, C ≠ E →
        ((univ.filter fun R : Finset V =>
            R ⊆ compSet G cG C ∧ cG ∉ R ∧ RootedIso G cG (insert cG (R : Set V)) G cG (insert cG (B_E : Set V))).card =
          (univ.filter fun R : Finset W =>
            R ⊆ compSet H cH (π₁ C) ∧ cH ∉ R ∧ RootedIso H cH (insert cH (R : Set W)) G cG (insert cG (B_E : Set V))).card) ∧
        ((univ.filter fun R : Finset V =>
            R ⊆ compSet G cG C ∧ cG ∉ R ∧ RootedIso G cG (insert cG (R : Set V)) G cG (insert cG (B_E : Set V))).card ≠ 0 →
          (univ.filter fun y : V => y ∈ compSet G cG C ∧ G.dist cG y = r).card =
          (univ.filter fun y : W => y ∈ compSet H cH (π₁ C) ∧ H.dist cH y = r).card) := by
      intro C hCE
      have hiso := (hall_ne_E C hCE).2
      exact ⟨subCount_eq_of_rootedCompIso G cG B_E G cG C H cH (π₁ C) hiso,
        fun _ => rVerts_eq_of_rootedCompIso G hTG cG C H hTH cH (π₁ C) r hiso⟩
    have hlt1 := kelly_Q2_rTotal_lt G hTG cG heccG H hTH cH heccH hr hdiamG hdiamH hmaxG hmaxH
      E E' hE_card hE'_card (by omega) (by omega) (by omega) (Or.inr hforce_E) hnot_E
      π₁ hπ1_E hmatch_E (hkelly _ (Q2 G cG B_E r) hQ_E_lt)
    let B_E' := compSet H cH E'
    have hB_E'_card : B_E'.card = M - 1 := by rw [compSet_card_eq, hE'_card]
    have hQ_E'_lt : card (Option (↥B_E' ⊕ Fin r)) < card V := by
      rw [card_option, card_sum, card_coe, card_fin, hB_E'_card]
      omega
    have hforce_E' : ∃ b ∈ B_E', r ≤ H.dist cH b := by
      obtain ⟨b, hb⟩ := card_pos.mp hpE'_pos
      obtain ⟨_, hbE', hbd⟩ := mem_filter.mp hb
      exact ⟨b, hbE', hbd.ge⟩
    have hmatch_E' : ∀ D, D ≠ E' →
        ((univ.filter fun R : Finset W =>
            R ⊆ compSet H cH D ∧ cH ∉ R ∧ RootedIso H cH (insert cH (R : Set W)) H cH (insert cH (B_E' : Set W))).card =
          (univ.filter fun R : Finset V =>
            R ⊆ compSet G cG (π₁.symm D) ∧ cG ∉ R ∧ RootedIso G cG (insert cG (R : Set V)) H cH (insert cH (B_E' : Set W))).card) ∧
        ((univ.filter fun R : Finset W =>
            R ⊆ compSet H cH D ∧ cH ∉ R ∧ RootedIso H cH (insert cH (R : Set W)) H cH (insert cH (B_E' : Set W))).card ≠ 0 →
          (univ.filter fun y : W => y ∈ compSet H cH D ∧ H.dist cH y = r).card =
          (univ.filter fun y : V => y ∈ compSet G cG (π₁.symm D) ∧ G.dist cG y = r).card) := by
      intro D hDE'
      have hCE : π₁.symm D ≠ E := fun h => hDE' (by rw [← hπ1_E, ← h, π₁.apply_symm_apply])
      have hiso : RootedCompIso H cH D G cG (π₁.symm D) := by
        have := (hall_ne_E (π₁.symm D) hCE).2.symm
        rwa [π₁.apply_symm_apply] at this
      exact ⟨subCount_eq_of_rootedCompIso H cH B_E' H cH D G cG (π₁.symm D) hiso,
        fun _ => rVerts_eq_of_rootedCompIso H hTH cH D G hTG cG (π₁.symm D) r hiso⟩
    have hlt2 := kelly_Q2_rTotal_lt H hTH cH heccH G hTG cG heccG hr hdiamH hdiamG hmaxH hmaxG
      E' E hE'_card hE_card (by omega) (by omega) (by omega) (Or.inr hforce_E') (fun h => hnot_E h.symm)
      π₁.symm (by rw [← hπ1_E, π₁.symm_apply_apply]) hmatch_E' (hkelly_rev _ (Q2 H cH B_E' r) hQ_E'_lt)
    exact absurd hlt1 (lt_asymm hlt2)
private lemma general_case_E_iso_E' {V W : Type} [Fintype V] [Fintype W]
    {r M : ℕ} (hr : 2 ≤ r) (hM : r + 1 ≤ M)
    (G : SimpleGraph V) (H : SimpleGraph W) (hTG : G.IsTree) (hTH : H.IsTree)
    (hdiamG : G.diam = 2 * r) (hdiamH : H.diam = 2 * r)
    (cG : V) (cH : W) (heccG : G.eccent cG = r) (heccH : H.eccent cH = r)
    (hmaxG : ∀ C : (G.induce {cG}ᶜ).ConnectedComponent, card C.supp ≤ M)
    (hmaxH : ∀ D : (H.induce {cH}ᶜ).ConnectedComponent, card D.supp ≤ M)
    (hltV : M + 1 + r < card V) (hcardVW : card V = card W)
    (hkelly : ∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
      card U < card V →
      {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard =
        {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard)
    (hkelly_rev : ∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
      card U < card V →
      {S : Finset W | Nonempty (H.induce (S : Set W) ≃g Q)}.ncard =
        {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard)
    (C₀ E : (G.induce {cG}ᶜ).ConnectedComponent)
    (E' : (H.induce {cH}ᶜ).ConnectedComponent)
    (hEC0 : E ≠ C₀) (hC0_card : card C₀.supp = M)
    (hE_card : card E.supp = M - 1) (hE'_card : card E'.supp = M - 1)
    (π₁ : (G.induce {cG}ᶜ).ConnectedComponent ≃ (H.induce {cH}ᶜ).ConnectedComponent)
    (hπ1_E : π₁ E = E')
    (hall_ne_E : ∀ C, C ≠ E → card (π₁ C).supp = card C.supp ∧ RootedCompIso G cG C H cH (π₁ C)) :
    RootedCompIso G cG E H cH E' := by
  by_contra hnot_E
  set pE := (univ.filter fun y : V => y ∈ compSet G cG E ∧ G.dist cG y = r).card
  set pE' := (univ.filter fun y : W => y ∈ compSet H cH E' ∧ H.dist cH y = r).card
  set rG := (univ.filter fun y : V => G.dist cG y = r).card
  set rH := (univ.filter fun y : W => H.dist cH y = r).card
  set P0 := ∑ C ∈ univ.erase E,
    (univ.filter fun y : V => y ∈ compSet G cG C ∧ G.dist cG y = r).card
  have hP0_H : P0 = ∑ D ∈ univ.erase E',
      (univ.filter fun y : W => y ∈ compSet H cH D ∧ H.dist cH y = r).card := by
    refine sum_bij (fun C _ => π₁ C) ?_ (fun _ _ _ _ h => π₁.injective h) ?_ ?_
    · intro C hC
      have hCE := (mem_erase.mp hC).1
      exact mem_erase.mpr ⟨fun h => hCE (π₁.injective (h.trans hπ1_E.symm)), mem_univ _⟩
    · intro D hD
      have hDE' := (mem_erase.mp hD).1
      exact ⟨π₁.symm D, mem_erase.mpr ⟨fun h => hDE' (by rw [← hπ1_E, ← h, π₁.apply_symm_apply]), mem_univ _⟩,
        π₁.apply_symm_apply D⟩
    · intro C hC
      exact rVerts_eq_of_rootedCompIso G hTG cG C H hTH cH (π₁ C) r
        (hall_ne_E C (mem_erase.mp hC).1).2
  have hP0_pos : 1 ≤ P0 := by
    obtain ⟨C_o, hCo_ne, x_o, hxo_mem, hxo_dist⟩ := exists_other_diam_comp G hTG hr hdiamG cG heccG E
    have hle : (univ.filter fun y : V => y ∈ compSet G cG C_o ∧ G.dist cG y = r).card ≤ P0 :=
      single_le_sum (f := fun C : (G.induce {cG}ᶜ).ConnectedComponent =>
          (univ.filter fun y : V => y ∈ compSet G cG C ∧ G.dist cG y = r).card)
        (fun _ _ => Nat.zero_le _) (mem_erase.mpr ⟨hCo_ne, mem_univ _⟩)
    have hpos : 1 ≤ (univ.filter fun y : V => y ∈ compSet G cG C_o ∧ G.dist cG y = r).card :=
      card_pos.mpr ⟨x_o, mem_filter.mpr ⟨mem_univ _, hxo_mem, hxo_dist⟩⟩
    omega
  have hrG_split : rG = pE + P0 := by
    have hpart : rG = ∑ C : (G.induce {cG}ᶜ).ConnectedComponent,
        (univ.filter fun y : V => y ∈ compSet G cG C ∧ G.dist cG y = r).card := by
      rw [← card_sigma]
      refine card_bij (fun y hy =>
          let hyd := (mem_filter.mp hy).2
          let hyc : y ≠ cG := fun h => by rw [h, dist_self] at hyd; omega
          ⟨(G.induce {cG}ᶜ).connectedComponentMk ⟨y, hyc⟩, y⟩) ?_ ?_ ?_
      · intro y hy
        have hyd := (mem_filter.mp hy).2
        have hyc : y ≠ cG := fun h => by rw [h, dist_self] at hyd; omega
        exact mem_sigma.mpr ⟨mem_univ _, mem_filter.mpr ⟨mem_univ _,
          (mem_compSet_iff G cG _ y).mpr ⟨hyc, rfl⟩, hyd⟩⟩
      · intro a _ b _ h; exact eq_of_heq (Sigma.ext_iff.mp h).2
      · rintro ⟨C, y⟩ hy
        obtain ⟨_, hyC, hyd⟩ := mem_filter.mp ((mem_sigma.mp hy).2)
        have hyc := (mem_compSet_iff G cG C y).mp hyC |>.1
        exact ⟨y, mem_filter.mpr ⟨mem_univ _, hyd⟩,
          Sigma.ext ((mem_compSet_iff G cG C y).mp hyC).2 (heq_of_eq rfl)⟩
    rw [hpart]
    exact (add_sum_erase univ _ (mem_univ E)).symm
  have hrH_split : rH = pE' + P0 := by
    have hpart : rH = ∑ D : (H.induce {cH}ᶜ).ConnectedComponent,
        (univ.filter fun y : W => y ∈ compSet H cH D ∧ H.dist cH y = r).card := by
      rw [← card_sigma]
      refine card_bij (fun y hy =>
          let hyd := (mem_filter.mp hy).2
          let hyc : y ≠ cH := fun h => by rw [h, dist_self] at hyd; omega
          ⟨(H.induce {cH}ᶜ).connectedComponentMk ⟨y, hyc⟩, y⟩) ?_ ?_ ?_
      · intro y hy
        have hyd := (mem_filter.mp hy).2
        have hyc : y ≠ cH := fun h => by rw [h, dist_self] at hyd; omega
        exact mem_sigma.mpr ⟨mem_univ _, mem_filter.mpr ⟨mem_univ _,
          (mem_compSet_iff H cH _ y).mpr ⟨hyc, rfl⟩, hyd⟩⟩
      · intro a _ b _ h; exact eq_of_heq (Sigma.ext_iff.mp h).2
      · rintro ⟨D, y⟩ hy
        obtain ⟨_, hyD, hyd⟩ := mem_filter.mp ((mem_sigma.mp hy).2)
        exact ⟨y, mem_filter.mpr ⟨mem_univ _, hyd⟩,
          Sigma.ext ((mem_compSet_iff H cH D y).mp hyD).2 (heq_of_eq rfl)⟩
    rw [hpart, hP0_H]
    exact (add_sum_erase univ _ (mem_univ E')).symm
  by_cases hpE0 : pE = 0 <;> by_cases hpE'0 : pE' = 0
  · exact general_case_subcase_A hr hM G H hTG hTH hdiamG cG cH heccG heccH hmaxG hmaxH hltV hkelly
      C₀ E E' hEC0 hC0_card hE_card hE'_card hnot_E π₁ hπ1_E hall_ne_E hpE0 hpE'0 (by omega)
  · exact general_case_subcase_p0_lt hr hM G hTG cG heccG hdiamG H hTH cH heccH hdiamH
      hltV hcardVW hmaxG hmaxH E E' hE_card hE'_card hnot_E π₁ hπ1_E (fun C hC => (hall_ne_E C hC).2)
      P0 hP0_pos hpE0 (Nat.pos_of_ne_zero hpE'0) hrG_split hrH_split hkelly_rev
  · exact general_case_subcase_p0_lt hr hM H hTH cH heccH hdiamH G hTG cG heccG hdiamG
      (by omega) hcardVW.symm hmaxH hmaxG E' E hE'_card hE_card (fun h => hnot_E h.symm)
      π₁.symm (by rw [← hπ1_E, π₁.symm_apply_apply])
      (fun D hD => by
        have hCE : π₁.symm D ≠ E := fun h => hD (by rw [← hπ1_E, ← h, π₁.apply_symm_apply])
        have := (hall_ne_E (π₁.symm D) hCE).2.symm
        rwa [π₁.apply_symm_apply] at this)
      P0 hP0_pos hpE'0 (Nat.pos_of_ne_zero hpE0) hrH_split hrG_split
      (fun U _ Q hU => hkelly U Q (by rw [hcardVW]; exact hU))
  · exact general_case_subcase_D hr hM G H hTG hTH hdiamG hdiamH cG cH heccG heccH
      hmaxG hmaxH hltV hcardVW hkelly hkelly_rev E E' hE_card hE'_card hnot_E π₁ hπ1_E hall_ne_E
      (Nat.pos_of_ne_zero hpE0) (Nat.pos_of_ne_zero hpE'0)
private lemma erase_iso_maxComp_norm {U₁ U₂ : Type} [Fintype U₁] [Fintype U₂]
    (G₁ : SimpleGraph U₁) (G₂ : SimpleGraph U₂) (v₁ : U₁) (v₂ : U₂)
    (c₁ : U₁) (c₂ : U₂) (hvc1 : v₁ ≠ c₁) (hvc2 : v₂ ≠ c₂)
    (φ : G₁.induce {v₁}ᶜ ≃g G₂.induce {v₂}ᶜ) (hφc : φ ⟨c₁, hvc1.symm⟩ = ⟨c₂, hvc2.symm⟩) (M : ℕ) :
    (Finset.univ.filter fun C : ((G₁.induce {v₁}ᶜ).induce ({⟨c₁, hvc1.symm⟩}ᶜ)).ConnectedComponent =>
      card C.supp = M).card =
    (Finset.univ.filter fun D : ((G₂.induce {v₂}ᶜ).induce ({⟨c₂, hvc2.symm⟩}ᶜ)).ConnectedComponent =>
      card D.supp = M).card := by
  obtain ⟨e, he⟩ := iso_transport_comp (G₁.induce {v₁}ᶜ) (G₂.induce {v₂}ᶜ) ⟨c₁, hvc1.symm⟩ ⟨c₂, hvc2.symm⟩ φ hφc
  refine card_bij (fun C _ => e C) ?_ ?_ ?_
  · intro C hC
    have hc := (@fintype_card_cast (e C).supp inferInstance _).trans ((he C).1.trans (@fintype_card_cast C.supp _ inferInstance))
    exact mem_filter.mpr ⟨mem_univ _, hc.trans (mem_filter.mp hC).2⟩
  · intro a _ b _ h; exact e.injective h
  · intro D hD
    refine ⟨e.symm D, mem_filter.mpr ⟨mem_univ _, ?_⟩, e.apply_symm_apply D⟩
    have h1 := (he (e.symm D)).1
    rw [e.apply_symm_apply] at h1
    have hc := (@fintype_card_cast (e.symm D).supp inferInstance _).trans
      (h1.symm.trans (@fintype_card_cast D.supp _ inferInstance))
    exact hc.trans (mem_filter.mp hD).2
set_option maxHeartbeats 400000 in
private lemma general_case_maxCount_le {U₁ U₂ : Type} [Fintype U₁] [Fintype U₂]
    (G₁ : SimpleGraph U₁) (G₂ : SimpleGraph U₂) (hT1 : G₁.IsTree) (hT2 : G₂.IsTree)
    (c₁ : U₁) (c₂ : U₂) (hnl1 : ∀ u, G₁.Adj c₁ u → 2 ≤ G₁.degree u)
    (hnl2 : ∀ w, G₂.Adj c₂ w → 2 ≤ G₂.degree w) {M : ℕ}
    (hmax1 : ∀ C : (G₁.induce {c₁}ᶜ).ConnectedComponent, card C.supp ≤ M)
    (hmax2 : ∀ D : (G₂.induce {c₂}ᶜ).ConnectedComponent, card D.supp ≤ M)
    (C₁ : (G₁.induce {c₁}ᶜ).ConnectedComponent) (hC1_card : card C₁.supp = M)
    (D₂ : (G₂.induce {c₂}ᶜ).ConnectedComponent)
    {v₁ : U₁} {v₂ : U₂} (hv1 : G₁.degree v₁ = 1) (hv2 : G₂.degree v₂ = 1)
    (hvc1 : v₁ ≠ c₁) (hvc2 : v₂ ≠ c₂)
    (hv1C : v₁ ∈ compSet G₁ c₁ C₁) (hv2D : v₂ ∈ compSet G₂ c₂ D₂)
    (φ : G₁.induce {v₁}ᶜ ≃g G₂.induce {v₂}ᶜ) (hφc : φ ⟨c₁, hvc1.symm⟩ = ⟨c₂, hvc2.symm⟩) :
    (univ.filter fun D : (G₂.induce {c₂}ᶜ).ConnectedComponent => card D.supp = M).card ≤
    (univ.filter fun C : (G₁.induce {c₁}ᶜ).ConnectedComponent => card C.supp = M).card := by
  let m1 := (univ.filter fun C : (G₁.induce {c₁}ᶜ).ConnectedComponent => card C.supp = M).card
  let m2 := (univ.filter fun D : (G₂.induce {c₂}ᶜ).ConnectedComponent => card D.supp = M).card
  let n1 := (univ.filter fun C' : ((G₁.induce {v₁}ᶜ).induce ({⟨c₁, hvc1.symm⟩}ᶜ)).ConnectedComponent => card C'.supp = M).card
  let n2 := (univ.filter fun D' : ((G₂.induce {v₂}ᶜ).induce ({⟨c₂, hvc2.symm⟩}ᶜ)).ConnectedComponent => card D'.supp = M).card
  have h1 := (comp_erase_count_norm G₁ hT1 c₁ hnl1 hv1 hvc1 C₁ hv1C hmax1).1 hC1_card
  have hiso : n1 = n2 := erase_iso_maxComp_norm G₁ G₂ v₁ v₂ c₁ c₂ hvc1 hvc2 φ hφc M
  have hm1_pos : 1 ≤ m1 := card_pos.mpr ⟨C₁, mem_filter.mpr ⟨mem_univ _, hC1_card⟩⟩
  have hnat : ∀ a b c d : ℕ, 1 ≤ a → c + 1 = a → (d + 1 = b ∨ d = b) → c = d → b ≤ a := by
    intro a b c d _ ha hb hc; rcases hb with hb | hb <;> omega
  refine hnat m1 m2 n1 n2 hm1_pos h1 ?_ hiso
  by_cases hD : card D₂.supp = M
  · exact Or.inl ((comp_erase_count_norm G₂ hT2 c₂ hnl2 hv2 hvc2 D₂ hv2D hmax2).1 hD)
  · exact Or.inr ((comp_erase_count_norm G₂ hT2 c₂ hnl2 hv2 hvc2 D₂ hv2D hmax2).2 (lt_of_le_of_ne (hmax2 D₂) hD))

set_option maxHeartbeats 400000 in
private lemma general_case_Dhit_card {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (hTG : G.IsTree) (hTH : H.IsTree)
    (σ : V ≃ W) (hσ : ∀ v : V, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ))
    {r : ℕ} (hr : 2 ≤ r) (hdiamH : H.diam = 2 * r)
    (cG : V) (cH : W) (heccG : G.eccent cG = r) (heccH : H.eccent cH = r)
    (huG : ∀ v : V, v ≠ cG → (r : ℕ∞) < G.eccent v)
    (huH : ∀ w : W, w ≠ cH → (r : ℕ∞) < H.eccent w)
    (hnoLeafG : ∀ v : V, G.Adj cG v → 2 ≤ G.degree v)
    (hnoLeafH : ∀ w : W, H.Adj cH w → 2 ≤ H.degree w)
    (hdeg_G : ∀ v : V, G.degree v = H.degree (σ v))
    (C₀ : (G.induce {cG}ᶜ).ConnectedComponent) {M : ℕ}
    (hM : r + 1 ≤ M) (hC0_card : card C₀.supp = M)
    (hmaxG : ∀ C : (G.induce {cG}ᶜ).ConnectedComponent, card C.supp ≤ M)
    (hmaxH : ∀ D : (H.induce {cH}ᶜ).ConnectedComponent, card D.supp ≤ M)
    (h1_mH : ∃ D₀ : (H.induce {cH}ᶜ).ConnectedComponent, card D₀.supp = M)
    (x₀ : V) (hx0_C0 : x₀ ∈ compSet G cG C₀) (hx0_deg1 : G.degree x₀ = 1)
    (hx0_ne_cG : x₀ ≠ cG) (hσx0_deg1 : H.degree (σ x₀) = 1) (hσx0_ne_cH : σ x₀ ≠ cH)
    (φ₀ : G.induce {x₀}ᶜ ≃g H.induce {σ x₀}ᶜ)
    (hφ0_c : φ₀ ⟨cG, hx0_ne_cG.symm⟩ = ⟨cH, hσx0_ne_cH.symm⟩) :
    card ((H.induce {cH}ᶜ).connectedComponentMk ⟨σ x₀, hσx0_ne_cH⟩).supp = M := by
  let D_hit := (H.induce {cH}ᶜ).connectedComponentMk ⟨σ x₀, hσx0_ne_cH⟩
  have hσx0_mem : σ x₀ ∈ compSet H cH D_hit := (mem_compSet_iff H cH D_hit (σ x₀)).mpr ⟨hσx0_ne_cH, rfl⟩
  have hmH_le_mG := general_case_maxCount_le G H hTG hTH cG cH hnoLeafG hnoLeafH hmaxG hmaxH
    C₀ hC0_card D_hit hx0_deg1 hσx0_deg1 hx0_ne_cG hσx0_ne_cH hx0_C0 hσx0_mem φ₀ hφ0_c
  have hmG_le_mH :
      (univ.filter fun C : (G.induce {cG}ᶜ).ConnectedComponent => card C.supp = M).card ≤
      (univ.filter fun D : (H.induce {cH}ᶜ).ConnectedComponent => card D.supp = M).card := by
    obtain ⟨D₀, hD0_card⟩ := h1_mH
    obtain ⟨w₀, hw0_D0, hw0_deg1, hw0_diam⟩ :=
      comp_exists_good_leaf_of_radius_lt_card H hTH hr hdiamH cH heccH D₀ (by rw [hD0_card]; exact hM)
    have hw0_ne_cH : w₀ ≠ cH := (mem_compSet_iff H cH D₀ w₀).mp hw0_D0 |>.1
    have hsw_deg1 : G.degree (σ.symm w₀) = 1 := by
      have := hdeg_G (σ.symm w₀); rw [σ.apply_symm_apply] at this; omega
    have hsw_ne_cG : σ.symm w₀ ≠ cG := ne_center_of_deg_one G hTG (by omega) cG heccG huG hsw_deg1
    have hψ0_eq : σ (σ.symm w₀) = w₀ := σ.apply_symm_apply w₀
    obtain ⟨ψ₀'⟩ : Nonempty (G.induce {σ.symm w₀}ᶜ ≃g H.induce {w₀}ᶜ) := by
      have h0 := hσ (σ.symm w₀); rwa [hψ0_eq] at h0
    have hdiamG_sw : (G.induce {σ.symm w₀}ᶜ).diam = 2 * r := (iso_diam_eq _ _ ψ₀').trans hw0_diam
    obtain ⟨_, _, hψ0_c⟩ := iso_map_center_of_good_leaf G H hTG hTH (by omega) cG cH
      heccG huG heccH huH hsw_deg1 hw0_deg1 hdiamG_sw ψ₀'
    let C_hit := (G.induce {cG}ᶜ).connectedComponentMk ⟨σ.symm w₀, hsw_ne_cG⟩
    have hsw_mem : σ.symm w₀ ∈ compSet G cG C_hit := (mem_compSet_iff G cG C_hit (σ.symm w₀)).mpr ⟨hsw_ne_cG, rfl⟩
    exact general_case_maxCount_le H G hTH hTG cH cG hnoLeafH hnoLeafG hmaxH hmaxG
      D₀ hD0_card C_hit hw0_deg1 hsw_deg1 hw0_ne_cH hsw_ne_cG hw0_D0 hsw_mem ψ₀'.symm
      (by rw [ψ₀'.symm_apply_eq]; exact hψ0_c.symm)
  have hm_eq := le_antisymm hmG_le_mH hmH_le_mG
  by_contra hne
  have h1 := (comp_erase_count_norm G hTG cG hnoLeafG hx0_deg1 hx0_ne_cG C₀ hx0_C0 hmaxG).1 hC0_card
  have h2 := (comp_erase_count_norm H hTH cH hnoLeafH hσx0_deg1 hσx0_ne_cH D_hit hσx0_mem hmaxH).2
    (lt_of_le_of_ne (hmaxH D_hit) hne)
  have hiso := erase_iso_maxComp_norm G H x₀ (σ x₀) cG cH hx0_ne_cG hσx0_ne_cH φ₀ hφ0_c M
  have hnat : ∀ a b c d : ℕ, a = b → c + 1 = a → d = b → c = d → False := by
    intro a b c d _ _ _ _; omega
  exact hnat _ _ _ _ hm_eq h1 h2 hiso
private lemma general_case_C0_iso_Dhit {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (hTG : G.IsTree) (hTH : H.IsTree)
    {r : ℕ} (hr : 2 ≤ r) (hdiamG : G.diam = 2 * r) (hdiamH : H.diam = 2 * r)
    (cG : V) (cH : W) (heccG : G.eccent cG = r) (heccH : H.eccent cH = r)
    (hkelly : ∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
      card U < card V →
      {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard =
        {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard)
    (C₀ E : (G.induce {cG}ᶜ).ConnectedComponent)
    (D_hit E' : (H.induce {cH}ᶜ).ConnectedComponent)
    {M : ℕ} (hM : r + 1 ≤ M) (hC0_card : card C₀.supp = M)
    (hDhit_card : card D_hit.supp = M)
    (hmaxG : ∀ C : (G.induce {cG}ᶜ).ConnectedComponent, card C.supp ≤ M)
    (hmaxH : ∀ D : (H.induce {cH}ᶜ).ConnectedComponent, card D.supp ≤ M)
    (hltV : M + 1 + r < card V)
    (π₁ : (G.induce {cG}ᶜ).ConnectedComponent ≃ (H.induce {cH}ᶜ).ConnectedComponent)
    (hπ1_C0 : π₁ C₀ = D_hit) (hπ1_E : π₁ E = E')
    (hπ1_good : ∀ C, C ≠ C₀ → C ≠ E →
      card (π₁ C).supp = card C.supp ∧ RootedCompIso G cG C H cH (π₁ C))
    (hE_cards : E ≠ C₀ → card E.supp = M - 1 ∧ card E'.supp = M - 1) :
    RootedCompIso G cG C₀ H cH D_hit := by
  by_contra hnot
  have hkelly_rev : ∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
      card U < card V →
      {S : Finset W | Nonempty (H.induce (S : Set W) ≃g Q)}.ncard =
        {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard := fun U _ Q hU =>
    (hkelly U Q hU).symm
  let B_C0 := compSet G cG C₀
  have hB_C0_card : B_C0.card = M := by rw [compSet_card_eq, hC0_card]
  have hQ_C0_lt : card (Option (↥B_C0 ⊕ Fin r)) < card V := by
    rw [card_option, card_sum, card_coe, card_fin, hB_C0_card]; omega
  have hmatch1 : ∀ C, C ≠ C₀ →
      ((univ.filter fun R : Finset V =>
          R ⊆ compSet G cG C ∧ cG ∉ R ∧ RootedIso G cG (insert cG (R : Set V)) G cG (insert cG (B_C0 : Set V))).card =
        (univ.filter fun R : Finset W =>
          R ⊆ compSet H cH (π₁ C) ∧ cH ∉ R ∧ RootedIso H cH (insert cH (R : Set W)) G cG (insert cG (B_C0 : Set V))).card) ∧
      ((univ.filter fun R : Finset V =>
          R ⊆ compSet G cG C ∧ cG ∉ R ∧ RootedIso G cG (insert cG (R : Set V)) G cG (insert cG (B_C0 : Set V))).card ≠ 0 →
        (univ.filter fun y : V => y ∈ compSet G cG C ∧ G.dist cG y = r).card =
        (univ.filter fun y : W => y ∈ compSet H cH (π₁ C) ∧ H.dist cH y = r).card) := by
    intro C hCC0
    by_cases hCE : C = E
    · rw [hCE, hπ1_E]
      obtain ⟨hE_eq, hE'_eq⟩ := hE_cards (fun h => hCC0 (hCE.trans h))
      have h0G := subCount_eq_zero_if_card_lt G cG B_C0 (c_notMem_compSet G cG C₀) G cG E (by rw [hB_C0_card, hE_eq]; omega)
      have h0H := subCount_eq_zero_if_card_lt G cG B_C0 (c_notMem_compSet G cG C₀) H cH E' (by rw [hB_C0_card, hE'_eq]; omega)
      exact ⟨h0G.trans h0H.symm, fun h => False.elim (h h0G)⟩
    · obtain ⟨_, hiso⟩ := hπ1_good C hCC0 hCE
      exact ⟨subCount_eq_of_rootedCompIso G cG B_C0 G cG C H cH (π₁ C) hiso,
        fun _ => rVerts_eq_of_rootedCompIso G hTG cG C H hTH cH (π₁ C) r hiso⟩
  have hlt1 := kelly_Q2_rTotal_lt G hTG cG heccG H hTH cH heccH hr hdiamG hdiamH hmaxG hmaxH
    C₀ D_hit hC0_card hDhit_card hM (by omega) (by omega) (Or.inl rfl) hnot π₁ hπ1_C0 hmatch1
    (hkelly _ (Q2 G cG B_C0 r) hQ_C0_lt)
  let B_D := compSet H cH D_hit
  have hB_D_card : B_D.card = M := by rw [compSet_card_eq, hDhit_card]
  have hQ_D_lt : card (Option (↥B_D ⊕ Fin r)) < card V := by
    rw [card_option, card_sum, card_coe, card_fin, hB_D_card]; omega
  have hmatch2 : ∀ D, D ≠ D_hit →
      ((univ.filter fun R : Finset W =>
          R ⊆ compSet H cH D ∧ cH ∉ R ∧ RootedIso H cH (insert cH (R : Set W)) H cH (insert cH (B_D : Set W))).card =
        (univ.filter fun R : Finset V =>
          R ⊆ compSet G cG (π₁.symm D) ∧ cG ∉ R ∧ RootedIso G cG (insert cG (R : Set V)) H cH (insert cH (B_D : Set W))).card) ∧
      ((univ.filter fun R : Finset W =>
          R ⊆ compSet H cH D ∧ cH ∉ R ∧ RootedIso H cH (insert cH (R : Set W)) H cH (insert cH (B_D : Set W))).card ≠ 0 →
        (univ.filter fun y : W => y ∈ compSet H cH D ∧ H.dist cH y = r).card =
        (univ.filter fun y : V => y ∈ compSet G cG (π₁.symm D) ∧ G.dist cG y = r).card) := by
    intro D hDD
    let C := π₁.symm D
    have hCC0 : C ≠ C₀ := fun h => hDD (by rw [← hπ1_C0, ← h, π₁.apply_symm_apply])
    by_cases hCE : C = E
    · have hDE' : D = E' := by rw [← hπ1_E, ← hCE]; exact (π₁.apply_symm_apply D).symm
      obtain ⟨hE_eq, hE'_eq⟩ := hE_cards (fun h => hCC0 (hCE.trans h))
      have h0H := subCount_eq_zero_if_card_lt H cH B_D (c_notMem_compSet H cH D_hit) H cH D (by rw [hDE', hB_D_card, hE'_eq]; omega)
      have h0G := subCount_eq_zero_if_card_lt H cH B_D (c_notMem_compSet H cH D_hit) G cG C (by rw [hCE, hB_D_card, hE_eq]; omega)
      exact ⟨h0H.trans h0G.symm, fun h => False.elim (h h0H)⟩
    · obtain ⟨_, hiso⟩ := hπ1_good C hCC0 hCE
      have hiso' : RootedCompIso H cH D G cG C := by have := hiso.symm; rwa [π₁.apply_symm_apply] at this
      exact ⟨subCount_eq_of_rootedCompIso H cH B_D H cH D G cG C hiso',
        fun _ => rVerts_eq_of_rootedCompIso H hTH cH D G hTG cG C r hiso'⟩
  have hlt2 := kelly_Q2_rTotal_lt H hTH cH heccH G hTG cG heccG hr hdiamH hdiamG hmaxH hmaxG
    D_hit C₀ hDhit_card hC0_card hM (by omega) (by omega) (Or.inl rfl) (fun h => hnot h.symm) π₁.symm
    (by rw [← hπ1_C0, π₁.symm_apply_apply]) hmatch2 (hkelly_rev _ (Q2 H cH B_D r) hQ_D_lt)
  exact absurd hlt1 (lt_asymm hlt2)
set_option maxHeartbeats 800000 in
private lemma general_case {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (hTG : G.IsTree) (hTH : H.IsTree)
    (σ : V ≃ W) (hσ : ∀ v : V, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ))
    (hdeg : ∀ v : V, (G.neighborSet v).ncard = (H.neighborSet (σ v)).ncard)
    {r : ℕ} (hr : 2 ≤ r) (hdiamG : G.diam = 2 * r) (hdiamH : H.diam = 2 * r)
    (cG : V) (cH : W) (heccG : G.eccent cG = r) (heccH : H.eccent cH = r)
    (huG : ∀ v : V, v ≠ cG → (r : ℕ∞) < G.eccent v)
    (huH : ∀ w : W, w ≠ cH → (r : ℕ∞) < H.eccent w)
    (hnoLeafG : ∀ v : V, G.Adj cG v → 2 ≤ G.degree v)
    (hnoLeafH : ∀ w : W, H.Adj cH w → 2 ≤ H.degree w)
    (hkelly : ∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
      card U < card V →
      {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard =
        {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard)
    (C₀ : (G.induce {cG}ᶜ).ConnectedComponent) {M : ℕ}
    (hM : r + 1 ≤ M) (hC0_card : card C₀.supp = M)
    (hmaxG : ∀ C : (G.induce {cG}ᶜ).ConnectedComponent, card C.supp ≤ M)
    (hmaxH : ∀ D : (H.induce {cH}ᶜ).ConnectedComponent, card D.supp ≤ M)
    (hltV : M + 1 + r < card V) :
    Nonempty (G ≃g H) := by
  have hcardVW : card V = card W := card_congr σ
  have hkelly_rev : ∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
      card U < card V →
      {S : Finset W | Nonempty (H.induce (S : Set W) ≃g Q)}.ncard =
        {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard := fun U _ Q hU =>
    (hkelly U Q hU).symm
  have h1_mH : ∃ D₀ : (H.induce {cH}ᶜ).ConnectedComponent, card D₀.supp = M :=
    general_case_h1_mH G H hTG hTH hr hdiamG cG cH heccG heccH hmaxH hkelly C₀ hM hC0_card hltV
  have hdeg_G : ∀ v : V, G.degree v = H.degree (σ v) := fun v => by
    rw [← ncard_neighborSet_eq_degree, ← ncard_neighborSet_eq_degree, hdeg v]
  obtain ⟨x₀, hx0_C0, hx0_deg1, hx0_diam⟩ :=
    comp_exists_good_leaf_of_radius_lt_card G hTG hr hdiamG cG heccG C₀ (by rw [hC0_card]; exact hM)
  have hx0_ne_cG : x₀ ≠ cG := (mem_compSet_iff G cG C₀ x₀).mp hx0_C0 |>.1
  have hσx0_deg1 : H.degree (σ x₀) = 1 := by rw [← hdeg_G x₀, hx0_deg1]
  have hσx0_ne_cH : σ x₀ ≠ cH := ne_center_of_deg_one H hTH (by omega) cH heccH huH hσx0_deg1
  obtain ⟨φ₀⟩ := hσ x₀
  obtain ⟨_, _, hφ0_c⟩ := iso_map_center_of_good_leaf G H hTG hTH (by omega) cG cH
    heccG huG heccH huH hx0_deg1 hσx0_deg1 hx0_diam φ₀
  let D_hit := (H.induce {cH}ᶜ).connectedComponentMk ⟨σ x₀, hσx0_ne_cH⟩
  have hσx0_mem : σ x₀ ∈ compSet H cH D_hit := (mem_compSet_iff H cH D_hit (σ x₀)).mpr ⟨hσx0_ne_cH, rfl⟩
  have hDhit_card : card D_hit.supp = M :=
    general_case_Dhit_card G H hTG hTH σ hσ hr hdiamH cG cH heccG heccH huG huH
      hnoLeafG hnoLeafH hdeg_G C₀ hM hC0_card hmaxG hmaxH h1_mH x₀ hx0_C0 hx0_deg1 hx0_ne_cG
      hσx0_deg1 hσx0_ne_cH φ₀ hφ0_c
  obtain ⟨C₀', ιG, hιG_C0, hC0'_card, _, hotherG⟩ :=
    comp_erase_bij G hTG cG hnoLeafG hx0_deg1 hx0_ne_cG C₀ hx0_C0
  obtain ⟨D_hit', ιH, hιH_D, hDhit'_card, _, hotherH⟩ :=
    comp_erase_bij H hTH cH hnoLeafH hσx0_deg1 hσx0_ne_cH D_hit hσx0_mem
  obtain ⟨eφ, heφ⟩ := iso_transport_comp (G.induce {x₀}ᶜ) (H.induce {σ x₀}ᶜ)
    ⟨cG, hx0_ne_cG.symm⟩ ⟨cH, hσx0_ne_cH.symm⟩ φ₀ hφ0_c
  let π : (G.induce {cG}ᶜ).ConnectedComponent ≃ (H.induce {cH}ᶜ).ConnectedComponent :=
    ιG.trans (eφ.trans ιH.symm)
  have hπ_good : ∀ C, C ≠ C₀ → π C ≠ D_hit →
      card (π C).supp = card C.supp ∧ RootedCompIso G cG C H cH (π C) := by
    intro C hCC0 hπD
    obtain ⟨h1c, h1r⟩ := hotherG C hCC0
    obtain ⟨h2c, h2r⟩ := heφ (ιG C)
    have hιHD : ιH (π C) = eφ (ιG C) := ιH.apply_symm_apply (eφ (ιG C))
    obtain ⟨h3c, h3r⟩ := hotherH (π C) hπD
    rw [hιHD] at h3c h3r
    refine ⟨?_, ?_⟩
    · have hc1 : card (ιG C).supp = card C.supp :=
        (@fintype_card_cast (ιG C).supp inferInstance _).trans (h1c.trans (@fintype_card_cast C.supp _ inferInstance))
      have hc2 : card (eφ (ιG C)).supp = card (ιG C).supp :=
        (@fintype_card_cast (eφ (ιG C)).supp inferInstance _).trans (h2c.trans (@fintype_card_cast (ιG C).supp _ inferInstance))
      have hc3 : card (eφ (ιG C)).supp = card (π C).supp :=
        (@fintype_card_cast (eφ (ιG C)).supp inferInstance _).trans (h3c.trans (@fintype_card_cast (π C).supp _ inferInstance))
      exact hc3.symm.trans (hc2.trans hc1)
    · exact (RootedCompIso.cast_both (iV₂ := inferInstance) (iW₂ := inferInstance) h1r).trans
        ((RootedCompIso.cast_both (iV₂ := inferInstance) (iW₂ := inferInstance) h2r).trans
          (RootedCompIso.cast_both (iV₂ := inferInstance) (iW₂ := inferInstance) h3r).symm)
  let E := π.symm D_hit
  let E' := π C₀
  let π₁ : (G.induce {cG}ᶜ).ConnectedComponent ≃ (H.induce {cH}ᶜ).ConnectedComponent :=
    (Equiv.swap C₀ E).trans π
  have hπ1_C0 : π₁ C₀ = D_hit := by simp [π₁, E]
  have hπ1_E : π₁ E = E' := by
    by_cases hEC0 : E = C₀
    · simp [π₁, hEC0, E']
    · simp [π₁, Equiv.swap_apply_right, E']
  have hπ1_good : ∀ C, C ≠ C₀ → C ≠ E →
      card (π₁ C).supp = card C.supp ∧ RootedCompIso G cG C H cH (π₁ C) := by
    intro C hCC0 hCE
    have hsw : Equiv.swap C₀ E C = C := Equiv.swap_apply_of_ne_of_ne hCC0 hCE
    have hne_D : π C ≠ D_hit := fun h => hCE (by dsimp only [E]; rw [← h, Equiv.symm_apply_apply])
    change card (π (Equiv.swap C₀ E C)).supp = card C.supp ∧
      RootedCompIso G cG C H cH (π (Equiv.swap C₀ E C))
    rw [hsw]
    exact hπ_good C hCC0 hne_D
  have hE_cards : E ≠ C₀ → card E.supp = M - 1 ∧ card E'.supp = M - 1 := by
    intro hEC0
    have hE'_ne_D : E' ≠ D_hit := fun h => hEC0 (by dsimp only [E]; dsimp only [E'] at h; rw [← h, Equiv.symm_apply_apply])
    have h1 := (hotherG E hEC0).1
    have h2 := (heφ (ιG E)).1
    have h4 : eφ (ιG E) = D_hit' := by
      have h5 := congrArg ιH (π.apply_symm_apply D_hit)
      simp only [π, Equiv.trans_apply, ιH.apply_symm_apply, hιH_D] at h5
      exact h5
    have hE_eq : card E.supp = M - 1 := by
      have hc1 : @card E.supp inferInstance = @card (ιG E).supp inferInstance :=
        (@fintype_card_cast E.supp inferInstance _).trans (h1.symm.trans (@fintype_card_cast (ιG E).supp _ inferInstance))
      have hc2 : @card (ιG E).supp inferInstance = @card (eφ (ιG E)).supp inferInstance :=
        (@fintype_card_cast (ιG E).supp inferInstance _).trans (h2.symm.trans (@fintype_card_cast (eφ (ιG E)).supp _ inferInstance))
      have hc4 : @card (eφ (ιG E)).supp inferInstance = @card D_hit'.supp inferInstance := by
        rw [h4]
      have hcD' : @card D_hit'.supp inferInstance + 1 = @card D_hit.supp inferInstance :=
        (congrArg (· + 1) (@fintype_card_cast D_hit'.supp inferInstance _)).trans
          (hDhit'_card.trans (@fintype_card_cast D_hit.supp _ inferInstance))
      have hcD : @card D_hit.supp inferInstance = M :=
        (@fintype_card_cast D_hit.supp inferInstance _).trans hDhit_card
      rw [hc1, hc2, hc4]; omega
    have h5 := (hotherH E' hE'_ne_D).1
    have h6 : ιH E' = eφ (ιG C₀) := ιH.apply_symm_apply (eφ (ιG C₀))
    have h7 := (heφ (ιG C₀)).1
    rw [hιG_C0] at h6 h7
    have hE'_eq : card E'.supp = M - 1 := by
      have hc5 : @card E'.supp inferInstance = @card (ιH E').supp inferInstance :=
        (@fintype_card_cast E'.supp inferInstance _).trans (h5.symm.trans (@fintype_card_cast (ιH E').supp _ inferInstance))
      have hc6 : @card (ιH E').supp inferInstance = @card (eφ C₀').supp inferInstance := by
        rw [h6]
      have hc7 : @card (eφ C₀').supp inferInstance = @card C₀'.supp inferInstance :=
        (@fintype_card_cast (eφ C₀').supp inferInstance _).trans (h7.trans (@fintype_card_cast C₀'.supp _ inferInstance))
      have hcC' : @card C₀'.supp inferInstance + 1 = @card C₀.supp inferInstance :=
        (congrArg (· + 1) (@fintype_card_cast C₀'.supp inferInstance _)).trans
          (hC0'_card.trans (@fintype_card_cast C₀.supp _ inferInstance))
      have hcC : @card C₀.supp inferInstance = M :=
        (@fintype_card_cast C₀.supp inferInstance _).trans hC0_card
      rw [hc5, hc6, hc7]; omega
    exact ⟨hE_eq, hE'_eq⟩
  have hC0_iso_Dhit : RootedCompIso G cG C₀ H cH D_hit :=
    general_case_C0_iso_Dhit G H hTG hTH hr hdiamG hdiamH cG cH heccG heccH hkelly C₀ E D_hit E'
      hM hC0_card hDhit_card hmaxG hmaxH hltV π₁ hπ1_C0 hπ1_E hπ1_good hE_cards
  by_cases hEC0 : E = C₀
  · refine iso_of_rootedCompIso_bij G H cG cH π₁ fun C => ?_
    by_cases hCC0 : C = C₀
    · subst hCC0; rw [hπ1_C0]; exact hC0_iso_Dhit
    · exact (hπ1_good C hCC0 (by rw [hEC0]; exact hCC0)).2
  have hall_ne_E : ∀ C, C ≠ E →
      card (π₁ C).supp = card C.supp ∧ RootedCompIso G cG C H cH (π₁ C) := by
    intro C hCE
    by_cases hCC0 : C = C₀
    · subst hCC0; rw [hπ1_C0]; exact ⟨by rw [hDhit_card, hC0_card], hC0_iso_Dhit⟩
    · exact hπ1_good C hCC0 hCE
  obtain ⟨hE_card, hE'_card⟩ := hE_cards hEC0
  have hE_iso_E' : RootedCompIso G cG E H cH E' :=
    general_case_E_iso_E' hr hM G H hTG hTH hdiamG hdiamH cG cH heccG heccH hmaxG hmaxH
      hltV hcardVW hkelly hkelly_rev C₀ E E' hEC0 hC0_card hE_card hE'_card π₁ hπ1_E hall_ne_E
  refine iso_of_rootedCompIso_bij G H cG cH π₁ fun C => ?_
  by_cases hCE : C = E
  · subst hCE; rw [hπ1_E]; exact hE_iso_E'
  · exact (hall_ne_E C hCE).2
private lemma tree_R1_H3_R1_H4_aux {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (σ : V ≃ W)
    (hTG : G.IsTree) (hTH : H.IsTree)
    (hσ : ∀ v : V, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ))
    (hdeg : ∀ v : V, (G.neighborSet v).ncard = (H.neighborSet (σ v)).ncard)
    (hnonpath : ∃ v : V, 3 ≤ (G.neighborSet v).ncard)
    {r : ℕ} (hr : 2 ≤ r) (hdiamG : G.diam = 2 * r) (hdiamH : H.diam = 2 * r)
    (cG : V) (cH : W) (heccG : G.eccent cG = r) (heccH : H.eccent cH = r)
    (huG : ∀ v : V, v ≠ cG → (r : ℕ∞) < G.eccent v)
    (huH : ∀ w : W, w ≠ cH → (r : ℕ∞) < H.eccent w)
    (hkelly : ∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
      card U < card V →
      {S : Finset V | Nonempty (G.induce (S : Set V) ≃g Q)}.ncard =
        {T : Finset W | Nonempty (H.induce (T : Set W) ≃g Q)}.ncard)
    (hdegc_nc : (G.neighborSet cG).ncard = (H.neighborSet cH).ncard)
    (hnoLeafG_nc : ∀ v : V, G.Adj cG v → 2 ≤ (G.neighborSet v).ncard)
    (hnoLeafH_nc : ∀ w : W, H.Adj cH w → 2 ≤ (H.neighborSet w).ncard)
    (C₀ : (G.induce {cG}ᶜ).ConnectedComponent) {M : ℕ}
    (hM : r + 1 ≤ M) (hC0_card : card C₀.supp = M)
    (hmaxG : ∀ C : (G.induce {cG}ᶜ).ConnectedComponent, card C.supp ≤ M)
    (hmaxH : ∀ D : (H.induce {cH}ᶜ).ConnectedComponent, card D.supp ≤ M) :
    Nonempty (G ≃g H) := by
  have hdegc : G.degree cG = H.degree cH := by
    rw [← ncard_neighborSet_eq_degree, ← ncard_neighborSet_eq_degree]; exact hdegc_nc
  have hnoLeafG : ∀ v : V, G.Adj cG v → 2 ≤ G.degree v := fun v hv => by
    rw [← ncard_neighborSet_eq_degree]; exact hnoLeafG_nc v hv
  have hnoLeafH : ∀ w : W, H.Adj cH w → 2 ≤ H.degree w := fun w hw => by
    rw [← ncard_neighborSet_eq_degree]; exact hnoLeafH_nc w hw
  have hleV : M + 1 + r ≤ card V := by
    rw [← hC0_card]
    exact maxComp_add_one_add_r_le_card G hTG hr hdiamG cG heccG C₀
  rcases Nat.lt_or_eq_of_le hleV with hltV | hbound
  · exact general_case G H hTG hTH σ hσ hdeg hr hdiamG hdiamH cG cH heccG heccH huG huH
      hnoLeafG hnoLeafH hkelly C₀ hM hC0_card hmaxG hmaxH hltV
  · exact boundary_case G H hTG hTH σ hσ hdeg hnonpath hr hdiamG hdiamH cG cH heccG heccH
      huG huH hdegc hnoLeafG hnoLeafH C₀ hM hC0_card hmaxG hmaxH hbound
private lemma tree_R1_H3_R1_H4 :
    OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H3_R1.H4 := by
  intro V W _ _ _ G H σ hTG hTH hσ hdeg hnonpath r cG cH hr hdiamG hdiamH
    heccG heccH huG huH hkelly hdegc hnoLeafG hnoLeafH hbranch
  have hneG : Nonempty (G.induce {cG}ᶜ).ConnectedComponent := by
    obtain ⟨C, _, _, _, _⟩ := exists_diam_pair_comps G hTG hr hdiamG cG heccG
    exact ⟨C⟩
  have hneH : Nonempty (H.induce {cH}ᶜ).ConnectedComponent := by
    obtain ⟨D, _, _, _, _⟩ := exists_diam_pair_comps H hTH hr hdiamH cH heccH
    exact ⟨D⟩
  let fG : (G.induce {cG}ᶜ).ConnectedComponent → ℕ := fun C => card C.supp
  let fH : (H.induce {cH}ᶜ).ConnectedComponent → ℕ := fun D => card D.supp
  obtain ⟨C₀, _, hC0_max⟩ := Finset.exists_max_image univ fG Finset.univ_nonempty
  obtain ⟨D₀, _, hD0_max⟩ := Finset.exists_max_image univ fH Finset.univ_nonempty
  let MG := fG C₀
  let MH := fH D₀
  have hbr_nat : r < MG ∨ r < MH := by
    rcases hbranch with ⟨C, hC⟩ | ⟨D, hD⟩
    · left
      have h1 : C.supp.ncard = fG C := by
        simp [fG, Set.ncard_eq_toFinset_card', Set.toFinset_card]
      have h2 := hC0_max C (mem_univ _)
      omega
    · right
      have h1 : D.supp.ncard = fH D := by
        simp [fH, Set.ncard_eq_toFinset_card', Set.toFinset_card]
      have h2 := hD0_max D (mem_univ _)
      omega
  by_cases hle : MH ≤ MG
  · have hMG : r + 1 ≤ MG := by omega
    exact tree_R1_H3_R1_H4_aux G H σ hTG hTH hσ hdeg hnonpath hr hdiamG hdiamH
      cG cH heccG heccH huG huH hkelly hdegc hnoLeafG hnoLeafH C₀ hMG rfl
      (fun C => hC0_max C (mem_univ _))
      (fun D => (hD0_max D (mem_univ _)).trans hle)
  · have hlt : MG < MH := Nat.lt_of_not_le hle
    have hMH : r + 1 ≤ MH := by omega
    have hσ' : ∀ w : W, Nonempty (H.induce {w}ᶜ ≃g G.induce {σ.symm w}ᶜ) := fun w => by
      obtain ⟨φ⟩ := hσ (σ.symm w)
      rw [σ.apply_symm_apply] at φ
      exact ⟨φ.symm⟩
    have hdeg' : ∀ w : W, (H.neighborSet w).ncard = (G.neighborSet (σ.symm w)).ncard := fun w => by
      have := hdeg (σ.symm w)
      rw [σ.apply_symm_apply] at this
      exact this.symm
    have hnonpath' : ∃ w : W, 3 ≤ (H.neighborSet w).ncard := by
      obtain ⟨v, hv⟩ := hnonpath
      exact ⟨σ v, by rw [← hdeg v]; exact hv⟩
    have hcardVW : card V = card W := card_congr σ
    have hkelly' : ∀ (U : Type) [Fintype U] (Q : SimpleGraph U),
        card U < card W →
        {S : Finset W | Nonempty (H.induce (S : Set W) ≃g Q)}.ncard =
          {T : Finset V | Nonempty (G.induce (T : Set V) ≃g Q)}.ncard := fun U _ Q hU =>
      (hkelly U Q (hcardVW ▸ hU)).symm
    obtain ⟨φ⟩ := tree_R1_H3_R1_H4_aux H G σ.symm hTH hTG hσ' hdeg' hnonpath' hr hdiamH hdiamG
      cH cG heccH heccG huH huG hkelly' hdegc.symm hnoLeafH hnoLeafG D₀ hMH rfl
      (fun D => hD0_max D (mem_univ _))
      (fun C => (hC0_max C (mem_univ _)).trans hlt.le)
    exact ⟨φ.symm⟩
end TreeR1H3R1H4
theorem OMA.solution :
    OMA.R_ReconstructionConjecture_reconstruction_conjecture_variants_tree_R1_H3_R1.H4 :=
  tree_R1_H3_R1_H4
