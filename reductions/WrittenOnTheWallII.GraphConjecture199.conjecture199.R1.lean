import FormalConjectures.WrittenOnTheWallII.GraphConjecture199

namespace OMA.R_WrittenOnTheWallII_GraphConjecture199_conjecture199_R1

section

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] in
private theorem star_tree (v : V) (S : Finset V)
    (hind : (S : Set V).Pairwise (fun a b => ¬ G.Adj a b)) (hadj : ∀ x ∈ S, G.Adj v x) :
    (G.induce (↑(insert v S) : Set V)).IsTree := by
  induction S using Finset.induction_on with
  | empty =>
    have hs : (↑(insert v (∅ : Finset V)) : Set V) = {v} := by ext y; simp
    rw [hs]
    let _ : Nonempty ↥({v} : Set V) := ⟨⟨v, by simp⟩⟩
    let _ : Subsingleton ↥({v} : Set V) := ⟨fun a b => Subtype.ext
      ((Set.mem_singleton_iff.mp a.property).trans (Set.mem_singleton_iff.mp b.property).symm)⟩
    exact IsTree.of_subsingleton
  | @insert x S hx ih =>
    have hvx := hadj x (mem_insert_self x S)
    have hS : (S : Set V).Pairwise (fun a b => ¬ G.Adj a b) :=
      hind.mono (by simpa only [coe_insert] using Set.subset_insert x (S : Set V))
    have hT := ih hS (fun y hy => hadj y (mem_insert_of_mem hy))
    rw [insert_comm]
    apply hT.induce_insert_of_unique_adj (by simp [hx, hvx.ne.symm])
      (mem_insert_self v S) hvx.symm
    intro y hy hxy
    rcases mem_insert.mp hy with rfl | hy
    · rfl
    exact (hind (mem_insert_self x S) (mem_insert_of_mem hy) hxy.ne hxy).elim

/-- An independent subset of a neighborhood extends to an induced star. -/
theorem star_bound (v : V) (S : Finset V) (hind : (S : Set V).Pairwise (fun a b => ¬ G.Adj a b))
    (hadj : ∀ x ∈ S, G.Adj v x) : S.card + 1 ≤ largestInducedTreeSize G := by
  have hvS : v ∉ S := fun h => (hadj v h).ne rfl
  simpa only [card_insert_of_notMem hvS] using
    card_le_largestInducedTreeSize (star_tree v S hind hadj)

private theorem dist_le_two (hG : G.Connected) (ht : largestInducedTreeSize G ≤ 3)
    (x y : V) : G.dist x y ≤ 2 := by
  obtain ⟨p, hp, hlen⟩ := (hG x y).exists_path_of_dist
  have hc := card_le_largestInducedTreeSize (p.induce_support_isTree_of_length_eq_dist hlen)
  rw [List.toFinset_card_of_nodup hp.support_nodup, Walk.length_support, hlen] at hc
  omega

omit [Fintype V] [DecidableEq V] in
private theorem adj_of_cross_walk {v x y : V} (L : Set V)
    (hx : x ∈ L) (hy : y ∉ L) (hyv : y ≠ v)
    (hcross : ∀ a ∈ L, ∀ b ∉ L, b ≠ v → ¬ G.Adj a b)
    (p : G.Walk x y) (hp : p.length ≤ 2) : G.Adj x v ∧ G.Adj v y := by
  cases p with
  | nil => exact (hy hx).elim
  | @cons _ z _ hxz q =>
    cases q with
    | nil => exact (hcross _ hx _ hy hyv hxz).elim
    | @cons _ w _ hzw r =>
      cases r with
      | nil =>
        by_cases hz : z ∈ L
        · exact (hcross _ hz _ hy hyv hzw).elim
        · have hzv : z = v := by
            by_contra hne
            exact hcross _ hx _ hz hne hxz
          subst z
          exact ⟨hxz, hzw⟩
      | cons _ _ =>
        simp at hp


private theorem no_star_three (v a b c : V) (ht : largestInducedTreeSize G ≤ 3)
    (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hnab : ¬ G.Adj a b) (hnac : ¬ G.Adj a c) (hnbc : ¬ G.Adj b c) : False := by
  have hind : ((↑({a, b, c} : Finset V)) : Set V).Pairwise (fun a b => ¬ G.Adj a b) := by
    intro x hx y hy hne
    simp only [mem_coe, mem_insert, mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first | exact hnab | exact hnac | exact hnbc | exact (fun h => hnab h.symm)
            | exact (fun h => hnac h.symm) | exact (fun h => hnbc h.symm) | contradiction
  have h := star_bound v {a, b, c} hind (by simp [ha, hb, hc])
  have hcard : ({a, b, c} : Finset V).card = 3 := by
    rw [card_insert_of_notMem (by simp [hab, hac]), card_insert_of_notMem (by simp [hbc]),
      card_singleton]
  omega

private theorem hamiltonian_of_cut_partition (v : V) (L : Set V)
    (hG : G.Connected) (ht : largestInducedTreeSize G ≤ 3)
    (hv : v ∉ L) (hL : L.Nonempty) (hR : ∃ y ∉ L, y ≠ v)
    (hcross : ∀ a ∈ L, ∀ b ∉ L, b ≠ v → ¬ G.Adj a b) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  obtain ⟨x, hx⟩ := hL
  obtain ⟨y, hy, hyv⟩ := hR
  have cross_adj {a b : V} (ha : a ∈ L) (hb : b ∉ L) (hbv : b ≠ v) :
      G.Adj a v ∧ G.Adj v b := by
    obtain ⟨p, plen⟩ := (hG a b).exists_walk_length_eq_dist
    exact adj_of_cross_walk L ha hb hbv hcross p (by rw [plen]; exact dist_le_two hG ht a b)
  have hall {a : V} (ha : a ≠ v) : G.Adj v a := by
    by_cases haL : a ∈ L
    · exact (cross_adj haL hy hyv).1.symm
    · exact (cross_adj hx haL ha).2
  have hleft {a b : V} (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b) : G.Adj a b := by
    by_contra hn
    have hav : a ≠ v := fun h => hv (h ▸ ha)
    have hbv : b ≠ v := fun h => hv (h ▸ hb)
    exact no_star_three v a b y ht (hall hav) (hall hbv) (hall hyv) hab
      (fun h => hy (h ▸ ha)) (fun h => hy (h ▸ hb)) hn
      (hcross a ha y hy hyv) (hcross b hb y hy hyv)
  have hright {a b : V} (ha : a ∉ L) (hav : a ≠ v) (hb : b ∉ L) (hbv : b ≠ v)
      (hab : a ≠ b) : G.Adj a b := by
    by_contra hn
    have hxv : x ≠ v := fun h => hv (h ▸ hx)
    exact no_star_three v x a b ht (hall hxv) (hall hav) (hall hbv)
      (fun h => ha (h ▸ hx)) (fun h => hb (h ▸ hx)) hab
      (hcross x hx a ha hav) (hcross x hx b hb hbv) hn
  let left := (univ.filter (· ∈ L)).toList
  let right := (univ.filter (fun a => a ∉ L ∧ a ≠ v)).toList
  have memLeft {a : V} : a ∈ left ↔ a ∈ L := by simp [left]
  have memRight {a : V} : a ∈ right ↔ a ∉ L ∧ a ≠ v := by simp [right]
  have ndLeft : left.Nodup := nodup_toList _
  have ndRight : right.Nodup := nodup_toList _
  have lc : left.IsChain G.Adj := by
    apply List.Pairwise.isChain
    apply List.pairwise_iff_get.mpr
    intro i j hij
    exact hleft (memLeft.mp (List.get_mem _ _)) (memLeft.mp (List.get_mem _ _))
      (List.pairwise_iff_get.mp ndLeft i j hij)
  have rc : right.IsChain G.Adj := by
    apply List.Pairwise.isChain
    apply List.pairwise_iff_get.mpr
    intro i j hij
    obtain ⟨hni, hiv⟩ := memRight.mp (List.get_mem right i)
    obtain ⟨hnj, hjv⟩ := memRight.mp (List.get_mem right j)
    exact hright hni hiv hnj hjv (List.pairwise_iff_get.mp ndRight i j hij)
  let l := left ++ v :: right
  have hchain : l.IsChain G.Adj := by
    apply lc.append
    · apply rc.cons
      intro z hz
      exact hall (memRight.mp (List.mem_of_mem_head? hz)).2
    · intro a ha b hb
      have hav : a ≠ v := fun h => hv (h ▸ memLeft.mp (List.mem_of_mem_getLast? ha))
      have hbv : v = b := by simpa using hb
      simpa [hbv] using (hall hav).symm
  have hn : l.Nodup := by
    refine List.nodup_append'.mpr ⟨ndLeft, List.nodup_cons.mpr ⟨?_, ndRight⟩, ?_⟩
    · exact fun h => (memRight.mp h).2 rfl
    · intro z hz hz'
      rcases List.mem_cons.mp hz' with rfl | hz'
      · exact hv (memLeft.mp hz)
      · exact (memRight.mp hz').1 (memLeft.mp hz)
  have hmem (z : V) : z ∈ l := by
    by_cases hz : z ∈ L
    · exact List.mem_append_left _ (memLeft.mpr hz)
    · apply List.mem_append_right
      by_cases hzv : z = v
      · simp [hzv]
      · exact List.mem_cons_of_mem _ (memRight.mpr ⟨hz, hzv⟩)
  have hne : l ≠ [] := fun he => by simpa [he] using hmem v
  let p := Walk.ofSupport l hne hchain
  have hs : p.support = l := Walk.support_ofSupport hne hchain
  have hp : p.IsPath := by
    apply Walk.IsPath.mk'
    rwa [hs]
  exact ⟨_, _, p, hp.isHamiltonian_of_mem (fun z => by rw [hs]; exact hmem z)⟩

/-- In a connected graph with a cut vertex, induced-tree order at most three forces a
Hamiltonian path. The two sides of the cut are cliques, and the cut vertex joins both. -/
theorem hamiltonian_of_cut_vertex [Nontrivial V] (hG : G.Connected)
    (ht : largestInducedTreeSize G ≤ 3) (v : V)
    (hcut : ¬ (G.induce ({v} : Set V)ᶜ).Connected) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  obtain ⟨x, hx⟩ := exists_ne v
  let a : ↥(({v} : Set V)ᶜ) := ⟨x, by simpa using hx⟩
  let K := G.induce ({v} : Set V)ᶜ
  obtain ⟨b, hb⟩ : ∃ b, ¬ K.Reachable a b := by
    by_contra! h
    let _ : Nonempty ↥(({v} : Set V)ᶜ) := ⟨a⟩
    have hc : K.Connected := ⟨fun c d => (h c).symm.trans (h d)⟩
    exact hcut hc
  let L : Set V := {z | ∃ c : ↥(({v} : Set V)ᶜ), c.val = z ∧ K.Reachable a c}
  have hv : v ∉ L := by
    rintro ⟨⟨z, hz⟩, he, -⟩
    change z = v at he
    exact hz (Set.mem_singleton_iff.mpr he)
  have hL : L.Nonempty := ⟨x, a, rfl, Reachable.refl _⟩
  have hR : ∃ y ∉ L, y ≠ v := by
    refine ⟨b.val, ?_, fun he => b.property (Set.mem_singleton_iff.mpr he)⟩
    rintro ⟨c, hc, hac⟩
    exact hb ((Subtype.ext hc) ▸ hac)
  have hcross : ∀ u ∈ L, ∀ w ∉ L, w ≠ v → ¬ G.Adj u w := by
    rintro u ⟨c, rfl, hac⟩ w hw hwv hcw
    let d : ↥(({v} : Set V)ᶜ) := ⟨w, by simpa using hwv⟩
    have hcd : K.Adj c d := hcw
    exact hw ⟨d, rfl, hac.trans hcd.reachable⟩
  exact hamiltonian_of_cut_partition v L hG ht hv hL hR hcross

/-- The cut-vertex case of Written on the Wall II conjecture 199. -/
theorem conjecture199_of_cut_vertex [Nontrivial V] (hG : G.Connected)
    (hκ : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) (v : V)
    (hcut : ¬ (G.induce ({v} : Set V)ᶜ).Connected) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  have hk : vertexConnectivity G ≤ 1 := by
    unfold vertexConnectivity
    split_ifs
    · omega
    · apply csInf_le'
      refine ⟨{v}, by simp, Or.inl ?_⟩
      rwa [coe_singleton]
  exact hamiltonian_of_cut_vertex hG (by omega) v hcut

private theorem hamiltonian_of_card_two [Nontrivial V] (hG : G.Connected)
    (hn : Fintype.card V = 2) : ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne V
  obtain ⟨p, hp⟩ := (hG a b).exists_isPath
  have hin : ({a, b} : Finset V) ⊆ p.support.toFinset := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact List.mem_toFinset.mpr p.start_mem_support
    · exact List.mem_toFinset.mpr p.end_mem_support
  have hc := card_le_card hin
  rw [card_insert_of_notMem (by simpa using hab), card_singleton] at hc
  have hs : p.support.toFinset = univ := by
    apply eq_of_subset_of_card_le (subset_univ _)
    simpa [hn] using hc
  exact ⟨a, b, p, hp.isHamiltonian_of_mem (fun x => List.mem_toFinset.mp (by simp [hs]))⟩

/-- Written on the Wall II conjecture 199 holds at vertex connectivity at most one. -/
theorem conjecture199_of_connectivity_le_one [Nontrivial V] (hG : G.Connected)
    (hκ : largestInducedTreeSize G - 2 ≤ vertexConnectivity G)
    (hκ1 : vertexConnectivity G ≤ 1) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  have hn : 1 < Fintype.card V := Fintype.one_lt_card
  by_cases hn2 : Fintype.card V = 2
  · exact hamiltonian_of_card_two hG hn2
  let A : Set ℕ := {k | ∃ S : Finset V, S.card = k ∧
    (¬ (G.induce ((S : Set V)ᶜ)).Connected ∨ S.card = Fintype.card V - 1)}
  have hkn : vertexConnectivity G = sInf A := by
    unfold vertexConnectivity
    rw [if_neg hn.not_ge]
  have hA : A.Nonempty := by
    let v : V := Classical.choice hG.nonempty
    exact ⟨Fintype.card V - 1, univ.erase v, by simp, Or.inr (by simp)⟩
  obtain ⟨S, hS, hcut | hcard⟩ := Nat.sInf_mem hA
  · rw [← hkn] at hS
    have hS1 : S.card = 1 := by
      by_contra hne
      have hz : S.card = 0 := by omega
      have hempty : S = ∅ := card_eq_zero.mp hz
      apply hcut
      rw [hempty, coe_empty, Set.compl_empty]
      exact G.induceUnivIso.connected_iff.mpr hG
    obtain ⟨v, rfl⟩ := card_eq_one.mp hS1
    exact conjecture199_of_cut_vertex hG hκ v (by rwa [coe_singleton] at hcut)
  · rw [← hkn] at hS
    omega

end

section

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Removing fewer vertices than the vertex connectivity leaves a connected graph. -/
theorem connected_of_card_lt_vertexConnectivity (T : Finset V)
    (hT : T.card < vertexConnectivity G) :
    (G.induce ((T : Set V)ᶜ)).Connected := by
  classical
  by_contra hn
  have hk : vertexConnectivity G ≤ T.card := by
    unfold vertexConnectivity
    split_ifs
    · omega
    · exact csInf_le' ⟨T, rfl, Or.inl hn⟩
  omega

/-- Every vertex of a minimum cut has a neighbor on either side of a nontrivial
separation of the remaining vertices. The set `L` can be the support of any one
connected component. -/
theorem minCut_adj_side (S : Finset V) (u : V) (hu : u ∈ S)
    (hS : S.card ≤ vertexConnectivity G) (L : Set V)
    (hL : ∃ x ∈ L, x ∉ S) (hR : ∃ y ∉ L, y ∉ S)
    (hcross : ∀ x ∈ L, ∀ y ∉ L, x ∉ S → y ∉ S → ¬ G.Adj x y) :
    ∃ x ∈ L, x ∉ S ∧ G.Adj u x := by
  classical
  by_contra hn
  obtain ⟨x, hx, hxs⟩ := hL
  obtain ⟨y, hy, hys⟩ := hR
  let T := S.erase u
  have hT : T.card < vertexConnectivity G :=
    (Finset.card_erase_lt_of_mem hu).trans_le hS
  let K := G.induce ((T : Set V)ᶜ)
  have hK : K.Connected := connected_of_card_lt_vertexConnectivity T hT
  let a : ↥((T : Set V)ᶜ) := ⟨x, fun hx' => hxs (mem_of_mem_erase hx')⟩
  let b : ↥((T : Set V)ᶜ) := ⟨y, fun hy' => hys (mem_of_mem_erase hy')⟩
  have step (c d : ↥((T : Set V)ᶜ)) (hcd : K.Adj c d)
      (hc : c.val ∈ L ∧ c.val ∉ S) : d.val ∈ L ∧ d.val ∉ S := by
    have hda : G.Adj c.val d.val := hcd
    have hds : d.val ∉ S := by
      intro hm
      have hdu : d.val = u := by
        by_contra hne
        exact d.property (mem_erase.mpr ⟨hne, hm⟩)
      apply hn
      exact ⟨c.val, hc.1, hc.2, hdu ▸ hda.symm⟩
    exact ⟨by_contra (fun hd => hcross c.val hc.1 d.val hd hc.2 hds hda), hds⟩
  have closed {c : ↥((T : Set V)ᶜ)} (hc : Relation.ReflTransGen K.Adj a c) :
      c.val ∈ L ∧ c.val ∉ S := by
    induction hc with
    | refl => exact ⟨hx, hxs⟩
    | tail _ hadj ih => exact step _ _ hadj ih
  exact hy (closed ((K.reachable_iff_reflTransGen a b).mp (hK a b))).1

end

section

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- A star and an induced two-edge arm can be combined when the arm has no edges to the spokes. -/
theorem arm_star_bound (v a b : V) (S : Finset V)
    (hind : (S : Set V).Pairwise (fun x y => ¬ G.Adj x y))
    (hadj : ∀ x ∈ S, G.Adj v x) (hva : G.Adj v a) (hab : G.Adj a b)
    (hvb : ¬ G.Adj v b) (hbv : b ≠ v) (ha : a ∉ S) (hb : b ∉ S)
    (hba : ∀ x ∈ S, ¬ G.Adj b x) (haa : ∀ x ∈ S, ¬ G.Adj a x) :
    S.card + 3 ≤ largestInducedTreeSize G := by
  have hv : v ∉ S := fun h => (hadj v h).ne rfl
  have htree : (G.induce (↑(insert v S) : Set V)).IsTree := by
    induction S using Finset.induction_on with
    | empty =>
      have hs : (↑(insert v (∅ : Finset V)) : Set V) = {v} := by ext x; simp
      rw [hs]
      let _ : Nonempty ↥({v} : Set V) := ⟨⟨v, by simp⟩⟩
      let _ : Subsingleton ↥({v} : Set V) := ⟨fun x y => Subtype.ext
        ((Set.mem_singleton_iff.mp x.property).trans (Set.mem_singleton_iff.mp y.property).symm)⟩
      exact IsTree.of_subsingleton
    | @insert x S hx ih =>
      have hvx := hadj x (mem_insert_self x S)
      have hi : (S : Set V).Pairwise (fun a b => ¬ G.Adj a b) :=
        hind.mono (by simpa only [coe_insert] using Set.subset_insert x (S : Set V))
      have hind' := ih hi (fun y hy => hadj y (mem_insert_of_mem hy))
        (fun hy => ha (mem_insert_of_mem hy)) (fun hy => hb (mem_insert_of_mem hy))
        (fun y hy => hba y (mem_insert_of_mem hy)) (fun y hy => haa y (mem_insert_of_mem hy))
        (fun hy => hv (mem_insert_of_mem hy))
      rw [insert_comm]
      apply hind'.induce_insert_of_unique_adj (by simp [hx, hvx.ne.symm])
        (mem_insert_self v S) hvx.symm
      intro y hy hxy
      rcases mem_insert.mp hy with rfl | hy
      · rfl
      exact (hind (mem_insert_self x S) (mem_insert_of_mem hy) hxy.ne hxy).elim
  have hamem : a ∉ insert v S := by simp [hva.ne.symm, ha]
  have htree' := htree.induce_insert_of_unique_adj hamem (mem_insert_self v S) hva.symm (by
    intro x hx hax
    rcases mem_insert.mp hx with rfl | hx
    · rfl
    · exact (haa x hx hax).elim)
  have hbmem : b ∉ insert a (insert v S) := by simp [hab.ne.symm, hbv, hb]
  have htree'' := htree'.induce_insert_of_unique_adj hbmem (mem_insert_self a (insert v S))
    hab.symm (by
      intro x hx hbx
      rcases mem_insert.mp hx with rfl | hx
      · rfl
      rcases mem_insert.mp hx with rfl | hx
      · exact (hvb hbx.symm).elim
      · exact (hba x hx hbx).elim)
  have h := card_le_largestInducedTreeSize htree''
  rw [card_insert_of_notMem hbmem, card_insert_of_notMem hamem,
    card_insert_of_notMem hv] at h
  omega


/-- When the induced-tree bound is tight for a separator and its components, every
separator vertex meeting all components is adjacent to every vertex in them.
The same bound forces each component to be a clique. -/
theorem tight_cut_component_structure {I : Type*} [Fintype I] [DecidableEq I]
    (v : V) (C : I → Set V)
    (hsep : ∀ {i j : I} {x y : V}, i ≠ j → x ∈ C i → y ∈ C j → x ≠ y ∧ ¬ G.Adj x y)
    (hout : ∀ i, v ∉ C i)
    (hconn : ∀ i, (G.induce (C i)).Connected)
    (hmeet : ∀ i, ∃ x ∈ C i, G.Adj v x)
    (ht : largestInducedTreeSize G ≤ Fintype.card I + 1) :
    (∀ i x, x ∈ C i → G.Adj v x) ∧
      (∀ i x y, x ∈ C i → y ∈ C i → x ≠ y → G.Adj x y) := by
  classical
  choose f hf hadjf using hmeet
  have hinj : Function.Injective f := by
    intro i j he
    by_contra hn
    exact (hsep hn (hf i) (hf j)).1 he
  have sides (i : I) : ∃ S : Finset V,
      S.card = Fintype.card I - 1 ∧
      (∀ x ∈ S, ∃ j ≠ i, x ∈ C j) ∧
      (S : Set V).Pairwise (fun x y => ¬ G.Adj x y) ∧
      (∀ x ∈ S, G.Adj v x) := by
    let T := (univ : Finset I).erase i
    refine ⟨T.image f, ?_, ?_, ?_, ?_⟩
    · simp [T, card_image_of_injective _ hinj]
    · intro x hx
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
      exact ⟨j, (mem_erase.mp hj).1, hf j⟩
    · intro x hx y hy hxy
      obtain ⟨j, _, rfl⟩ := mem_image.mp hx
      obtain ⟨l, _, rfl⟩ := mem_image.mp hy
      exact (hsep (fun h => hxy (congrArg f h)) (hf j) (hf l)).2
    · intro x hx
      obtain ⟨j, _, rfl⟩ := mem_image.mp hx
      exact hadjf j
  have hcomplete (i : I) (x : V) (hx : x ∈ C i) : G.Adj v x := by
    by_contra hnx
    let T : Finset (C i) := univ.filter (fun a => G.Adj v a.val)
    have hT : T.Nonempty := ⟨⟨f i, hf i⟩, by simp [T, hadjf]⟩
    have hTu : T ≠ univ := by
      intro he
      have h : (⟨x, hx⟩ : C i) ∈ T := he ▸ mem_univ _
      exact hnx (mem_filter.mp h).2
    obtain ⟨b, hb, a, ha, hba⟩ := (hconn i).exists_adj_finset_compl hT hTu
    have hva : G.Adj v a.val := (mem_filter.mp ha).2
    have hvb : ¬ G.Adj v b.val := fun h => hb (mem_filter.mpr ⟨mem_univ _, h⟩)
    obtain ⟨S, hSc, hsides, hind, hadjS⟩ := sides i
    have hsep' (y : V) (hy : y ∈ C i) (z : V) (hz : z ∈ S) :
        y ≠ z ∧ ¬ G.Adj y z := by
      obtain ⟨j, hj, hzc⟩ := hsides z hz
      exact hsep hj.symm hy hzc
    have h := arm_star_bound v a.val b.val S hind hadjS hva
      (induce_adj.mp hba).symm hvb
      (fun he => hout i (he ▸ b.property))
      (fun haS => (hsep' _ a.property _ haS).1 rfl)
      (fun hbS => (hsep' _ b.property _ hbS).1 rfl)
      (fun z hz => (hsep' _ b.property z hz).2)
      (fun z hz => (hsep' _ a.property z hz).2)
    let _ : Nonempty I := ⟨i⟩
    have hi : 0 < Fintype.card I := Fintype.card_pos
    omega
  refine ⟨hcomplete, ?_⟩
  intro i x y hx hy hxy
  by_contra hn
  obtain ⟨S, hSc, hsides, hind, hadjS⟩ := sides i
  have cross (a : V) (ha : a ∈ C i) (z : V) (hz : z ∈ S) :
      a ≠ z ∧ ¬ G.Adj a z := by
    obtain ⟨j, hj, hzc⟩ := hsides z hz
    exact hsep hj.symm ha hzc
  have hxS : x ∉ S := fun h => (cross x hx x h).1 rfl
  have hyS : y ∉ S := fun h => (cross y hy y h).1 rfl
  have hi' : (↑(insert y S) : Set V).Pairwise (fun a b => ¬ G.Adj a b) := by
    rw [coe_insert]
    apply Set.Pairwise.insert_of_notMem hyS hind
    intro z hz
    exact ⟨(cross y hy z hz).2, fun he => (cross y hy z hz).2 he.symm⟩
  have hxSy : x ∉ insert y S := by simp [hxy, hxS]
  have hi'' : (↑(insert x (insert y S)) : Set V).Pairwise (fun a b => ¬ G.Adj a b) := by
    rw [coe_insert]
    apply Set.Pairwise.insert_of_notMem hxSy hi'
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact ⟨hn, fun he => hn he.symm⟩
    · exact ⟨(cross x hx z hz).2, fun he => (cross x hx z hz).2 he.symm⟩
  have h := star_bound v (insert x (insert y S)) hi'' (by
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact hcomplete i _ hx
    rcases mem_insert.mp hz with rfl | hz
    · exact hcomplete i _ hy
    · exact hadjS z hz)
  rw [card_insert_of_notMem hxSy, card_insert_of_notMem hyS] at h
  let _ : Nonempty I := ⟨i⟩
  have hi : 0 < Fintype.card I := Fintype.card_pos
  omega


/-- In a decomposition by a two-vertex cut, deleting only the other cut vertex
forces the remaining cut vertex to meet every component. -/
private theorem two_cut_neighbours (u v : V) (huv : u ≠ v) (C : Fin 3 → Set V)
    (hout : ∀ i, u ∉ C i ∧ v ∉ C i)
    (hcover : ∀ x, x ≠ u → x ≠ v → ∃ i, x ∈ C i)
    (hsep : ∀ {i j : Fin 3} {x y : V}, i ≠ j → x ∈ C i → y ∈ C j → ¬ G.Adj x y)
    (hc : ∀ i, (G.induce (C i)).Connected)
    (hG : (G.induce ({v} : Set V)ᶜ).Connected) (i : Fin 3) :
    ∃ x ∈ C i, G.Adj u x := by
  classical
  let W := ↥(({v} : Set V)ᶜ)
  let S : Finset W := univ.filter fun x => x.val ∈ C i
  have hS : S.Nonempty := by
    obtain ⟨x⟩ := (hc i).nonempty
    exact ⟨⟨x.val, fun he => (hout i).2 ((Set.mem_singleton_iff.mp he).symm ▸ x.property)⟩,
      mem_filter.mpr ⟨mem_univ _, x.property⟩⟩
  have hSu : S ≠ univ := by
    intro he
    let a : W := ⟨u, fun h => huv (Set.mem_singleton_iff.mp h)⟩
    have h : a ∈ S := he ▸ mem_univ a
    exact (hout i).1 (mem_filter.mp h).2
  obtain ⟨b, hb, a, ha, hba⟩ := hG.exists_adj_finset_compl hS hSu
  have hai : a.val ∈ C i := (mem_filter.mp ha).2
  have hbi : b.val ∉ C i := fun h => hb (mem_filter.mpr ⟨mem_univ _, h⟩)
  have hbu : b.val = u := by
    by_contra hne
    obtain ⟨j, hj⟩ := hcover b.val hne (fun he => b.property (Set.mem_singleton_iff.mpr he))
    have hij : i ≠ j := by
      intro he
      subst j
      exact hbi hj
    exact hsep hij hai hj (induce_adj.mp hba).symm
  exact ⟨a.val, hai, hbu ▸ induce_adj.mp hba⟩

/-- The three-component case for a two-vertex cut in Written on the Wall II #199. -/
theorem hamiltonian_of_three_components (u v : V) (huv : u ≠ v) (C : Fin 3 → Set V)
    (hout : ∀ i, u ∉ C i ∧ v ∉ C i)
    (hcover : ∀ x, x ≠ u → x ≠ v → ∃ i, x ∈ C i)
    (hsep : ∀ {i j : Fin 3} {x y : V}, i ≠ j → x ∈ C i → y ∈ C j → x ≠ y ∧ ¬ G.Adj x y)
    (hc : ∀ i, (G.induce (C i)).Connected)
    (hGu : (G.induce ({u} : Set V)ᶜ).Connected)
    (hGv : (G.induce ({v} : Set V)ᶜ).Connected)
    (ht : largestInducedTreeSize G ≤ 4) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  have hbt : largestInducedTreeSize G ≤ Fintype.card (Fin 3) + 1 := by simpa using ht
  have ⟨hu, hclique⟩ := tight_cut_component_structure u C (@hsep)
    (fun i => (hout i).1) hc
    (two_cut_neighbours u v huv C hout hcover (fun h a b => (hsep h a b).2) hc hGv) hbt
  have ⟨hv, _⟩ := tight_cut_component_structure v C (@hsep)
    (fun i => (hout i).2) hc
    (two_cut_neighbours v u huv.symm C (fun i => (hout i).symm)
      (fun x hx hy => hcover x hy hx) (fun h a b => (hsep h a b).2) hc hGu) hbt
  let B (i : Fin 3) := (univ.filter (· ∈ C i)).toList
  have hmem (i : Fin 3) (x : V) : x ∈ B i ↔ x ∈ C i := by simp [B]
  have hnd (i : Fin 3) : (B i).Nodup := nodup_toList _
  have hchain (i : Fin 3) : (B i).IsChain G.Adj := by
    apply List.Pairwise.isChain
    apply List.pairwise_iff_get.mpr
    intro a b hab
    exact hclique i _ _ ((hmem i _).mp (List.get_mem _ _)) ((hmem i _).mp (List.get_mem _ _))
      (List.pairwise_iff_get.mp (hnd i) a b hab)
  have cons_chain (i : Fin 3) (x : V) (hz : ∀ z ∈ C i, G.Adj x z)
      (p : List V) (hp : (B i ++ p).IsChain G.Adj)
      (hp' : B i ≠ []) : (x :: (B i ++ p)).IsChain G.Adj := by
    apply hp.cons
    intro z hz'
    rw [List.head?_append_of_ne_nil _ hp'] at hz'
    exact hz z ((hmem i z).mp (List.mem_of_mem_head? hz'))
  have hnon (i : Fin 3) : B i ≠ [] := by
    obtain ⟨x⟩ := (hc i).nonempty
    exact List.ne_nil_of_mem ((hmem i x.val).mpr x.property)
  let L := B 0 ++ u :: (B 1 ++ v :: B 2)
  have hL : L.IsChain G.Adj := by
    apply (hchain 0).append
    · apply cons_chain 1 u (hu 1)
      · apply (hchain 1).append
        · exact (hchain 2).cons (fun z hz => hv 2 z ((hmem 2 z).mp (List.mem_of_mem_head? hz)))
        · intro x hx y hy
          have hy' : v = y := by simpa using hy
          exact hy' ▸ (hv 1 x ((hmem 1 x).mp (List.mem_of_mem_getLast? hx))).symm
      · exact hnon 1
    · intro x hx y hy
      have hy' : u = y := by simpa using hy
      exact hy' ▸ (hu 0 x ((hmem 0 x).mp (List.mem_of_mem_getLast? hx))).symm
  have hcsep (i j : Fin 3) (hij : i ≠ j) (x : V) (hx : x ∈ B i) : x ∉ B j :=
    fun hy => (hsep hij ((hmem i x).mp hx) ((hmem j x).mp hy)).1 rfl
  have hua (i : Fin 3) : u ∉ B i := fun hu => (hout i).1 ((hmem i u).mp hu)
  have hva (i : Fin 3) : v ∉ B i := fun hv => (hout i).2 ((hmem i v).mp hv)
  have hndL : L.Nodup := by
    simp only [L, List.nodup_append', List.nodup_cons, List.mem_append, List.mem_cons]
    refine ⟨hnd 0, ⟨?_, hnd 1, ⟨hva 2, hnd 2⟩, ?_⟩, ?_⟩
    · push Not
      exact ⟨hua 1, huv, hua 2⟩
    · intro x hx hxc
      rcases List.mem_cons.mp hxc with rfl | hxc
      · exact hva 1 hx
      · exact hcsep 1 2 (by decide) x hx hxc
    · intro x hx hxc
      rcases List.mem_cons.mp hxc with rfl | hxc
      · exact hua 0 hx
      · rcases List.mem_append.mp hxc with hxc | hxc
        · exact hcsep 0 1 (by decide) x hx hxc
        · rcases List.mem_cons.mp hxc with rfl | hxc
          · exact hva 0 hx
          · exact hcsep 0 2 (by decide) x hx hxc
  have hmemL (x : V) : x ∈ L := by
    by_cases hxu : x = u
    · simp [L, hxu]
    by_cases hxv : x = v
    · simp [L, hxv]
    obtain ⟨i, hi⟩ := hcover x hxu hxv
    have hm := (hmem i x).mpr hi
    fin_cases i
    · exact List.mem_append_left _ (show x ∈ B 0 from hm)
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _
        (show x ∈ B 1 from hm)))
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _
        (List.mem_cons_of_mem _ (show x ∈ B 2 from hm))))
  have hnL : L ≠ [] := List.ne_nil_of_mem (hmemL u)
  let p := Walk.ofSupport L hnL hL
  have hs : p.support = L := Walk.support_ofSupport hnL hL
  have hp : p.IsPath := by
    apply Walk.IsPath.mk'
    rwa [hs]
  exact ⟨_, _, p, hp.isHamiltonian_of_mem (fun z => by rw [hs]; exact hmemL z)⟩

/-- Conjecture 199 for graphs of vertex connectivity two with a two-vertex cut
whose deletion leaves exactly three connected components. -/
theorem conjecture199_connectivity_two_three_components (u v : V) (huv : u ≠ v)
    (hκ : vertexConnectivity G = 2)
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G)
    (C : Fin 3 → Set V)
    (hout : ∀ i, u ∉ C i ∧ v ∉ C i)
    (hcover : ∀ x, x ≠ u → x ≠ v → ∃ i, x ∈ C i)
    (hsep : ∀ {i j : Fin 3} {x y : V}, i ≠ j → x ∈ C i → y ∈ C j → x ≠ y ∧ ¬ G.Adj x y)
    (hc : ∀ i, (G.induce (C i)).Connected) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  have delete_one (w : V) : (G.induce ({w} : Set V)ᶜ).Connected := by
    have h := connected_of_card_lt_vertexConnectivity (G := G) ({w} : Finset V)
      (by simp [hκ])
    rwa [coe_singleton] at h
  exact hamiltonian_of_three_components u v huv C hout hcover (@hsep) hc
    (delete_one u) (delete_one v) (by omega)

/-- Under the catalog hypothesis, a minimum cut leaves at most one more component
than its own size. This is the component-count condition for that cut. -/
theorem min_cut_component_count {I : Type*} [Fintype I]
    (S : Finset V) (v : V) (hv : v ∈ S) (hS : S.card = vertexConnectivity G)
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G)
    (C : I → Set V) (hne : ∀ i, (C i).Nonempty)
    (hout : ∀ i x, x ∈ C i → x ∉ S)
    (hcover : ∀ x ∉ S, ∃ i, x ∈ C i)
    (hsep : ∀ {i j : I} {x y : V}, i ≠ j → x ∈ C i → y ∈ C j → x ≠ y ∧ ¬ G.Adj x y) :
    Fintype.card I ≤ S.card + 1 := by
  classical
  by_contra hn
  have hi : 1 < Fintype.card I := by omega
  let _ : Nontrivial I := Fintype.one_lt_card_iff_nontrivial.mp hi
  have hadj (i : I) : ∃ x ∈ C i, G.Adj v x := by
    obtain ⟨x, hx⟩ := hne i
    obtain ⟨j, hj⟩ := exists_ne i
    obtain ⟨y, hy⟩ := hne j
    have hyi : y ∉ C i := fun he => (hsep hj.symm he hy).1 rfl
    obtain ⟨z, hz, _, hzv⟩ := minCut_adj_side S v hv hS.le (C i)
      ⟨x, hx, hout i x hx⟩ ⟨y, hyi, hout j y hy⟩ (by
        intro a ha b hb _ hbS
        obtain ⟨k, hk⟩ := hcover b hbS
        have hik : i ≠ k := by
          intro he
          subst k
          exact hb hk
        exact (hsep hik ha hk).2)
    exact ⟨z, hz, hzv⟩
  choose f hf hfadj using hadj
  have hinj : Function.Injective f := by
    intro i j he
    by_contra hne
    exact (hsep hne (hf i) (hf j)).1 he
  let B := univ.image f
  have hind : (B : Set V).Pairwise (fun x y => ¬ G.Adj x y) := by
    intro x hx y hy hxy
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := mem_image.mp hy
    exact (hsep (fun he => hxy (congrArg f he)) (hf i) (hf j)).2
  have h := star_bound v B hind (by
    intro x hx
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    exact hfadj i)
  have hc : B.card = Fintype.card I := by simp [B, card_image_of_injective _ hinj]
  omega

end

section

open SimpleGraph Finset

/-- A finite connected graph with no independent triple has a Hamiltonian path. -/
theorem hamiltonian_of_no_independent_triple {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : G.Connected)
    (hα : ∀ a b c : V, a ≠ b → a ≠ c → b ≠ c →
      ¬ G.Adj a b → ¬ G.Adj a c → ¬ G.Adj b c → False) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let T : Set ℕ := {n | ∃ a b : V, ∃ p : G.Walk a b, p.IsPath ∧ p.length = n}
  have hT : T.Finite := (Set.finite_le_nat (Fintype.card V)).subset (by
    rintro _ ⟨a,b,p,hp,rfl⟩
    exact hp.length_lt.le)
  let a₀ : V := Classical.choice hG.nonempty
  obtain ⟨n, hn, hmax₀⟩ := hT.exists_maximal
    ⟨0, a₀, a₀, Walk.nil, Walk.IsPath.nil, rfl⟩
  obtain ⟨a,b,p,hp,hpn⟩ := hn
  have hmax (a' b' : V) (p' : G.Walk a' b') (hp' : p'.IsPath) : p'.length ≤ p.length := by
    have h := hmax₀ ⟨a', b', p', hp', rfl⟩
    lia
  refine ⟨a, b, p, hp.isHamiltonian_of_mem ?_⟩
  intro x
  by_contra hx
  have nofirst (z : V) (hz : z ∉ p.support) : ¬ G.Adj a z := by
    intro he
    have h := hmax z b (p.cons he.symm) (hp.cons hz)
    simp at h
  have nolast (z : V) (hz : z ∉ p.support) : ¬ G.Adj b z := by
    intro he
    have h := hmax a z (p.concat he) (hp.concat hz he)
    simp at h
  have hs : p.support.toFinset ≠ univ := by
    intro he
    exact hx (List.mem_toFinset.mp (he ▸ mem_univ x))
  obtain ⟨z, hz, w, hw, hzw⟩ := hG.exists_adj_finset_compl
    (show p.support.toFinset.Nonempty from ⟨a, List.mem_toFinset.mpr p.start_mem_support⟩) hs
  have hzs : z ∉ p.support := fun hz' => hz (List.mem_toFinset.mpr hz')
  have hws : w ∈ p.support := List.mem_toFinset.mp hw
  have hab : a ≠ b := by
    intro he
    have hnil : p.Nil := hp.nil_iff_eq.mpr he
    have hw' : w = a := by simpa [Walk.nil_iff_support_eq.mp hnil] using hws
    exact nofirst z hzs (hw' ▸ hzw.symm)
  have hax : a ≠ x := fun h => hx (h ▸ p.start_mem_support)
  have hbx : b ≠ x := fun h => hx (h ▸ p.end_mem_support)
  have hab' : G.Adj a b := by
    by_contra he
    exact hα a b x hab hax hbx he (nofirst x hx) (nolast x hx)
  let c := p.concat hab'.symm
  have hcs : c.support = p.support ++ [a] := p.support_concat _
  have hcw : w ∈ c.support := by rw [hcs]; exact List.mem_append_left _ hws
  let r := c.rotate w hcw
  have hcnd : c.support.tail.Nodup := by
    apply (c.tail_support_perm_dropLast_support).nodup_iff.mpr
    rw [hcs, List.dropLast_append_cons, List.dropLast_singleton, List.append_nil]
    exact hp.support_nodup
  have hrnd : r.support.tail.Nodup := (c.support_rotate w hcw).perm.nodup_iff.mpr hcnd
  have hrnil : ¬ r.Nil := by
    rw [← Walk.length_eq_zero_iff, Walk.length_rotate, Walk.length_concat]
    omega
  have hrp : r.dropLast.IsPath := by
    apply Walk.IsPath.mk'
    rw [r.support_dropLast hrnil]
    exact r.tail_support_perm_dropLast_support.nodup_iff.mp hrnd
  have hzr : z ∉ r.dropLast.support := by
    intro h
    rw [r.support_dropLast hrnil] at h
    have hz' : z ∈ r.support := List.mem_of_mem_dropLast h
    rw [Walk.mem_support_rotate_iff, hcs, List.mem_append, List.mem_singleton] at hz'
    exact hz'.elim hzs (fun he => hzs (he.symm ▸ p.start_mem_support))
  have hlong := hmax z _ (r.dropLast.cons hzw) (hrp.cons hzr)
  rw [Walk.length_cons, Walk.length_dropLast_add_one hrnil] at hlong
  change (c.rotate w hcw).length ≤ p.length at hlong
  rw [Walk.length_rotate, Walk.length_concat] at hlong
  omega

/-- The independence-number-at-most-two case of Written on the Wall II #199. -/
theorem conjecture199_of_indepNum_le_two {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : G.Connected) (hα : G.indepNum ≤ 2) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  apply hamiltonian_of_no_independent_triple hG
  intro a b c hab hac hbc hna hnb hnc
  have hind : G.IsIndepSet ((↑({a,b,c} : Finset V)) : Set V) := by
    intro x hx y hy hne
    simp only [mem_coe, mem_insert, mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first | exact hna | exact hnb | exact hnc | exact (fun h => hna h.symm)
            | exact (fun h => hnb h.symm) | exact (fun h => hnc h.symm) | contradiction
  have hc := hind.card_le_indepNum
  rw [card_insert_of_notMem (by simp [hab, hac]), card_insert_of_notMem (by simp [hbc]),
    card_singleton] at hc
  omega

end

section

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Deleting any one vertex forces each of the two cut vertices to meet each side. -/
private theorem two_clique_meets (u v : V) (huv : u ≠ v) (A B : Set V)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (houtA : u ∉ A ∧ v ∉ A) (houtB : u ∉ B ∧ v ∉ B)
    (hs : ∀ a ∈ A, ∀ b ∈ B, a ≠ b ∧ ¬ G.Adj a b)
    (hcover : ∀ x, x ≠ u → x ≠ v → x ∈ A ∨ x ∈ B)
    (hκ : 2 ≤ vertexConnectivity G) : ∃ a ∈ A, G.Adj u a := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  let S : Finset V := {u,v}
  have hS : S.card ≤ vertexConnectivity G := by
    change ({u,v} : Finset V).card ≤ _
    rw [card_insert_of_notMem (show u ∉ ({v} : Finset V) from by simpa using huv), card_singleton]
    exact hκ
  have hbA : b ∉ A := fun he => (hs b he b hb).1 rfl
  obtain ⟨x, hx, _, hux⟩ := minCut_adj_side S u (by simp [S]) hS A
    ⟨a, ha, by simpa [S] using (show a ≠ u ∧ a ≠ v from
      ⟨fun e => houtA.1 (e ▸ ha), fun e => houtA.2 (e ▸ ha)⟩)⟩
    ⟨b, hbA, by simpa [S] using (show b ≠ u ∧ b ≠ v from
      ⟨fun e => houtB.1 (e ▸ hb), fun e => houtB.2 (e ▸ hb)⟩)⟩ (by
        intro x hx y hy _ hyS
        have hy' : y ≠ u ∧ y ≠ v := by simpa [S] using hyS
        exact (hs x hx y ((hcover y hy'.1 hy'.2).resolve_left hy)).2)
  exact ⟨x, hx, hux⟩

private theorem two_clique_middle_attachments (u v : V) (A B : Set V)
    (houtB : u ∉ B ∧ v ∉ B)
    (hs : ∀ a ∈ A, ∀ b ∈ B, a ≠ b ∧ ¬ G.Adj a b)
    (hcover : ∀ x, x ≠ u → x ≠ v → x ∈ A ∨ x ∈ B)
    (hκ : 2 ≤ vertexConnectivity G)
    (hu : ∃ b ∈ B, G.Adj u b) (hv : ∃ b ∈ B, G.Adj v b) :
    ∃ b c, b ∈ B ∧ c ∈ B ∧ G.Adj u b ∧ G.Adj v c ∧ (b ≠ c ∨ B = {b}) := by
  obtain ⟨b, hb, hub⟩ := hu
  obtain ⟨c, hc, hvc⟩ := hv
  by_cases hne : b ≠ c
  · exact ⟨b,c,hb,hc,hub,hvc,Or.inl hne⟩
  have he : b = c := by simpa using hne
  subst c
  by_cases hB : B = {b}
  · exact ⟨b,b,hb,hb,hub,hvc,Or.inr hB⟩
  by_contra hn
  have hou (x : V) (hx : x ∈ B) (hxb : x ≠ b) : ¬ G.Adj u x :=
    fun h => hn ⟨x,b,hx,hb,h,hvc,Or.inl hxb⟩
  have hov (x : V) (hx : x ∈ B) (hxb : x ≠ b) : ¬ G.Adj v x :=
    fun h => hn ⟨b,x,hb,hx,hub,h,Or.inl hxb.symm⟩
  have hG : (G.induce ({b} : Set V)ᶜ).Connected := by
    have h := connected_of_card_lt_vertexConnectivity (G := G) ({b} : Finset V)
      (by simpa using Nat.lt_of_lt_of_le (by decide : 1 < 2) hκ)
    rwa [coe_singleton] at h
  let W := ↥(({b} : Set V)ᶜ)
  classical
  let T : Finset W := univ.filter fun x => x.val ∈ B
  have hT : T.Nonempty := by
    have hbad : ∃ x ∈ B, x ≠ b := by
      by_contra! h
      exact hB (Set.Subset.antisymm (fun x hx => Set.mem_singleton_iff.mpr (h x hx))
        (Set.singleton_subset_iff.mpr hb))
    obtain ⟨x,hx,hxb⟩ := hbad
    exact ⟨⟨x, fun he => hxb (Set.mem_singleton_iff.mp he)⟩, mem_filter.mpr ⟨mem_univ _, hx⟩⟩
  have hTu : T ≠ univ := by
    intro he
    let z : W := ⟨u, fun h => houtB.1 ((Set.mem_singleton_iff.mp h).symm ▸ hb)⟩
    have h : z ∈ T := he ▸ mem_univ z
    exact houtB.1 (mem_filter.mp h).2
  obtain ⟨y, hy, x, hx, hyx⟩ := hG.exists_adj_finset_compl hT hTu
  have hxB : x.val ∈ B := (mem_filter.mp hx).2
  have hxb : x.val ≠ b := fun h => x.property (Set.mem_singleton_iff.mpr h)
  have hyB : y.val ∉ B := fun h => hy (mem_filter.mpr ⟨mem_univ _, h⟩)
  have hxy : G.Adj y.val x.val := induce_adj.mp hyx
  by_cases hyu : y.val = u
  · exact hou x.val hxB hxb (hyu ▸ hxy)
  by_cases hyv : y.val = v
  · exact hov x.val hxB hxb (hyv ▸ hxy)
  exact (hs _ ((hcover y.val hyu hyv).resolve_right hyB) _ hxB).2 hxy


omit [Fintype V] [DecidableEq V] in
private theorem chain_of_clique (A : Set V)
    (hA : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → G.Adj x y)
    (L : List V) (hn : L.Nodup) (hmem : ∀ x ∈ L, x ∈ A) : L.IsChain G.Adj := by
  apply List.Pairwise.isChain
  apply List.pairwise_iff_get.mpr
  intro i j hij
  exact hA _ (hmem _ (List.get_mem _ _)) _ (hmem _ (List.get_mem _ _))
    (List.pairwise_iff_get.mp hn i j hij)

/-- A two-vertex cut with two separated clique components yields a Hamiltonian path
when deleting any single vertex preserves connectivity. -/
theorem hamiltonian_of_two_clique_components (u v : V) (huv : u ≠ v) (A B : Set V)
    (hAn : A.Nonempty) (hBn : B.Nonempty)
    (houtA : u ∉ A ∧ v ∉ A) (houtB : u ∉ B ∧ v ∉ B)
    (hs : ∀ a ∈ A, ∀ b ∈ B, a ≠ b ∧ ¬ G.Adj a b)
    (hcover : ∀ x, x ≠ u → x ≠ v → x ∈ A ∨ x ∈ B)
    (hA : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → G.Adj x y)
    (hB : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → G.Adj x y)
    (hκ : 2 ≤ vertexConnectivity G) :
    ∃ s t : V, ∃ p : G.Walk s t, p.IsHamiltonian := by
  classical
  have hs' : ∀ b ∈ B, ∀ a ∈ A, b ≠ a ∧ ¬ G.Adj b a :=
    fun b hb a ha => ⟨(hs a ha b hb).1.symm, fun h => (hs a ha b hb).2 h.symm⟩
  obtain ⟨a, ha, hua⟩ := two_clique_meets u v huv A B hAn hBn houtA houtB hs hcover hκ
  have hub := two_clique_meets u v huv B A hBn hAn houtB houtA hs'
    (fun x hx hy => (hcover x hx hy).symm) hκ
  have hvb := two_clique_meets v u huv.symm B A hBn hAn houtB.symm houtA.symm hs'
    (fun x hx hy => (hcover x hy hx).symm) hκ
  obtain ⟨b, c, hb, hc, hub, hvc, hbc⟩ :=
    two_clique_middle_attachments u v A B houtB hs hcover hκ hub hvb
  let L := (A.toFinset.erase a).toList ++ [a]
  have hLn : L.Nodup := by
    refine List.nodup_append.mpr ⟨nodup_toList _, by simp, ?_⟩
    intro x hx y hy
    have hya : y = a := by simpa using hy
    subst y
    exact (mem_erase.mp (mem_toList.mp hx)).1
  have hLm (x : V) : x ∈ L ↔ x ∈ A := by
    by_cases hx : x = a <;> simp [L, hx, ha]
  have hLl : L.getLast? = some a := by simp [L]
  have hM : ∃ M : List V, M.Nodup ∧ (∀ x, x ∈ M ↔ x ∈ B) ∧
      M.head? = some b ∧ M.getLast? = some c := by
    rcases hbc with hn | hs
    · let M := b :: ((B.toFinset.erase b |>.erase c).toList ++ [c])
      refine ⟨M, ?_, ?_, by simp [M], ?_⟩
      · apply List.nodup_cons.mpr
        refine ⟨by simp [hn], List.nodup_append.mpr ⟨nodup_toList _, by simp, ?_⟩⟩
        intro x hx y hy
        have hyc : y = c := by simpa using hy
        subst y
        exact (mem_erase.mp (mem_toList.mp hx)).1
      · intro x
        by_cases hxb : x = b
        · simp [M, hxb, hb]
        by_cases hxc : x = c
        · simp [M, hxc, hc]
        · simp [M, hxb, hxc]
      · change ((b :: ((B.toFinset.erase b).erase c).toList) ++ [c]).getLast? = some c
        simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or]
    · have he : c = b := Set.mem_singleton_iff.mp (hs ▸ hc)
      subst c
      exact ⟨[b], by simp, by intro x; simp [hs], by simp, by simp⟩
  obtain ⟨M, hMn, hMm, hMh, hMl⟩ := hM
  let W := L ++ u :: (M ++ [v])
  have hlast : (M ++ [v]).IsChain G.Adj := by
    apply (chain_of_clique B hB M hMn (fun x hx => (hMm x).mp hx)).append
      (List.IsChain.singleton v)
    intro x hx y hy
    have hx' : c = x := by simpa [hMl] using hx
    have hy' : v = y := by simpa using hy
    subst x
    subst y
    exact hvc.symm
  have hmid : (u :: (M ++ [v])).IsChain G.Adj := by
    apply hlast.cons
    intro x hx
    have hMne : M ≠ [] := by
      intro he
      simp [he] at hMh
    rw [List.head?_append_of_ne_nil _ hMne, hMh] at hx
    have he : b = x := by simpa using hx
    exact he ▸ hub
  have hWc : W.IsChain G.Adj := by
    apply (chain_of_clique A hA L hLn (fun x hx => (hLm x).mp hx)).append hmid
    intro x hx y hy
    have he : a = x := by simpa [hLl] using hx
    have he' : u = y := by simpa using hy
    subst x
    subst y
    exact hua.symm
  have huM : u ∉ M := fun h => houtB.1 ((hMm u).mp h)
  have hvM : v ∉ M := fun h => houtB.2 ((hMm v).mp h)
  have hWn : W.Nodup := by
    refine List.nodup_append.mpr ⟨hLn, ?_, ?_⟩
    · apply List.nodup_cons.mpr
      refine ⟨by simp [huv, huM], List.nodup_append.mpr ⟨hMn, by simp, ?_⟩⟩
      intro x hx y hy
      have hyv : y = v := by simpa using hy
      subst y
      exact fun he => hvM (he ▸ hx)
    · intro x hx y hy
      have hxA := (hLm x).mp hx
      rcases List.mem_cons.mp hy with rfl | hy
      · exact fun he => houtA.1 (he ▸ hxA)
      rcases List.mem_append.mp hy with hy | hy
      · exact (hs x hxA y ((hMm y).mp hy)).1
      · have he : y = v := by simpa using hy
        exact fun h => houtA.2 ((h.trans he) ▸ hxA)
  have hWm (x : V) : x ∈ W := by
    by_cases hu : x = u
    · simp [W, hu]
    by_cases hv : x = v
    · simp [W, hv]
    rcases hcover x hu hv with h | h
    · exact List.mem_append_left _ ((hLm x).mpr h)
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ ((hMm x).mpr h)))
  have hWe : W ≠ [] := List.ne_nil_of_mem (hWm u)
  let p := Walk.ofSupport W hWe hWc
  have hp : p.support = W := Walk.support_ofSupport hWe hWc
  have hpath : p.IsPath := by
    apply Walk.IsPath.mk'
    rwa [hp]
  exact ⟨_, _, p, hpath.isHamiltonian_of_mem (fun x => by rw [hp]; exact hWm x)⟩

end

section

open SimpleGraph Finset

/-- The two-component case with a nonclique side at connectivity two. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    vertexConnectivity G = 2 → largestInducedTreeSize G ≤ 4 →
    ∀ (v w : V) (A B : Set V), v ≠ w →
    A.Nonempty → B.Nonempty → v ∉ A → w ∉ A → v ∉ B → w ∉ B →
    (G.induce A).Connected → (G.induce B).Connected →
    (∀ x, x ≠ v → x ≠ w → x ∈ A ∨ x ∈ B) →
    (∀ x ∈ A, ∀ y ∈ B, x ≠ y ∧ ¬ G.Adj x y) →
    (¬ G.IsClique A ∨ ¬ G.IsClique B) →
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian

/-- Connectivity at least three, with an independent triple. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    G.Connected → 3 ≤ vertexConnectivity G → 3 ≤ G.indepNum →
    largestInducedTreeSize G - 2 ≤ vertexConnectivity G →
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian

variable {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V}

private theorem exists_minimum_two_cut (hk : vertexConnectivity G = 2)
    (hn : 3 < Fintype.card V) :
    ∃ S : Finset V, S.card = 2 ∧ ¬ (G.induce ((S : Set V)ᶜ)).Connected := by
  classical
  let A : Set ℕ := {k | ∃ S : Finset V, S.card = k ∧
    (¬ (G.induce ((S : Set V)ᶜ)).Connected ∨ S.card = Fintype.card V - 1)}
  have hkn : vertexConnectivity G = sInf A := by
    unfold vertexConnectivity
    rw [if_neg (by omega)]
  have hA : A.Nonempty := by
    let v : V := Classical.choice (inferInstance : Nonempty V)
    exact ⟨Fintype.card V - 1, univ.erase v, by simp, Or.inr (by simp)⟩
  obtain ⟨S, hS, hcut | hcard⟩ := Nat.sInf_mem hA
  · exact ⟨S, by rwa [← hkn, hk] at hS, hcut⟩
  · rw [← hkn, hk] at hS
    omega

omit [DecidableEq V] in
private theorem card_ge_four_of_indepNum (hc : G.Connected) (hi : 3 ≤ G.indepNum) :
    3 < Fintype.card V := by
  classical
  obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
  by_contra! hn
  have hsu : s = univ := by
    refine eq_of_subset_of_card_le (subset_univ _) ?_
    rw [card_univ, hs.card_eq]
    exact hn.trans hi
  obtain ⟨a,b,hab⟩ := exists_pair_ne V
  obtain ⟨p⟩ := hc a b
  cases p with
  | nil => exact hab rfl
  | @cons _ c _ h _ =>
    exact (hs.isIndepSet (by simp [hsu]) (by simp [hsu]) h.ne) h

private theorem connectivity_two_reduction (step : H1)
    (hg : G.Connected) (hk : vertexConnectivity G = 2)
    (hi : 3 ≤ G.indepNum) (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  obtain ⟨S, hS, hs⟩ := exists_minimum_two_cut hk (card_ge_four_of_indepNum hg hi)
  obtain ⟨v,w,hvw,rfl⟩ := card_eq_two.mp hS
  let W := ↥((↑({v,w} : Finset V) : Set V)ᶜ)
  let K : SimpleGraph W := G.induce ((↑({v,w} : Finset V) : Set V)ᶜ)
  let I := K.ConnectedComponent
  let _ : Finite I := Finite.of_surjective K.connectedComponentMk Quot.mk_surjective
  let _ : Fintype I := Fintype.ofFinite I
  let C (i : I) : Set V := Subtype.val '' i.supp
  have hn (i : I) : (C i).Nonempty := ⟨i.out.val, i.out, i.out_eq, rfl⟩
  have hout (i : I) (x : V) (hx : x ∈ C i) : x ∉ ({v,w} : Finset V) := by
    obtain ⟨y, hy, rfl⟩ := hx
    exact y.property
  have hcover (x : V) (hx : x ∉ ({v,w} : Finset V)) : ∃ i, x ∈ C i := by
    let y : W := ⟨x, hx⟩
    exact ⟨K.connectedComponentMk y, y, rfl, rfl⟩
  have hsep {i j : I} {x y : V} (hij : i ≠ j)
      (hx : x ∈ C i) (hy : y ∈ C j) : x ≠ y ∧ ¬ G.Adj x y := by
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    change K.connectedComponentMk a = i at ha
    change K.connectedComponentMk b = j at hb
    have hne : K.connectedComponentMk a ≠ K.connectedComponentMk b := by rwa [ha,hb]
    exact ⟨fun he => hne (congrArg K.connectedComponentMk (Subtype.ext he)),
      fun he => hne (ConnectedComponent.connectedComponentMk_eq_of_adj
        (show K.Adj a b from he))⟩
  have hconn (i : I) : (G.induce (C i)).Connected := by
    let e : i.supp → C i := fun x => ⟨x.val.val, x.val, x.property, rfl⟩
    have hinj : Function.Injective e := by
      intro a b h
      have hv : a.val.val = b.val.val := congrArg (fun x : C i => x.val) h
      exact Subtype.ext (Subtype.ext hv)
    have hsurj : Function.Surjective e := by
      rintro ⟨x,y,hy,rfl⟩
      exact ⟨⟨y,hy⟩, rfl⟩
    let iso : K.induce i.supp ≃g G.induce (C i) :=
      ⟨Equiv.ofBijective e ⟨hinj,hsurj⟩, by intro a b; rfl⟩
    exact iso.connected_iff.mp i.maximal_connected_induce_supp.1
  have hnon : Nonempty W := by
    have hlt : ({v,w} : Finset V).card < Fintype.card V := by
      have hnV := card_ge_four_of_indepNum hg hi
      omega
    have hne : ∃ z : V, z ∉ ({v,w} : Finset V) := by
      by_contra! he
      have he' : ({v,w} : Finset V) = univ := eq_univ_of_forall he
      simp [he'] at hlt
    obtain ⟨z,hz⟩ := hne
    exact ⟨⟨z,hz⟩⟩
  have hlow : 1 < Fintype.card I := by
    by_contra! hnI
    have hsub : Subsingleton I := Fintype.card_le_one_iff_subsingleton.mp hnI
    apply hs
    let _ : Nonempty W := hnon
    exact ⟨fun a b => ConnectedComponent.exact (Subsingleton.elim _ _)⟩
  have hsκ : ({v,w} : Finset V).card = vertexConnectivity G := hS.trans hk.symm
  have hhigh := min_cut_component_count ({v,w} : Finset V) v (by simp) hsκ ht C hn hout hcover
    (fun h a b => hsep h a b)
  have hcount : Fintype.card I = 2 ∨ Fintype.card I = 3 := by omega
  have hout' (i : I) : v ∉ C i ∧ w ∉ C i :=
    ⟨fun h => hout i v h (by simp), fun h => hout i w h (by simp)⟩
  have hcover' (x : V) (hxv : x ≠ v) (hxw : x ≠ w) : ∃ i, x ∈ C i :=
    hcover x (by simp [hxv,hxw])
  rcases hcount with htwo | hthree
  · let e := Fintype.equivFinOfCardEq htwo
    let A := C (e.symm 0)
    let B := C (e.symm 1)
    have hsep' : ∀ x ∈ A, ∀ y ∈ B, x ≠ y ∧ ¬ G.Adj x y :=
      fun x hx y hy => hsep (e.symm.injective.ne (by decide)) hx hy
    have hcover'' (x : V) (hxv : x ≠ v) (hxw : x ≠ w) : x ∈ A ∨ x ∈ B := by
      obtain ⟨i,hi⟩ := hcover' x hxv hxw
      have hEq : i = e.symm (e i) := (e.symm_apply_apply i).symm
      rw [hEq] at hi
      have hIdx : e i = 0 ∨ e i = 1 := by
        have hv : (e i).val < 2 := (e i).isLt
        rcases (show (e i).val = 0 ∨ (e i).val = 1 by omega) with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)
      rcases hIdx with h | h
      · rw [h] at hi
        exact Or.inl hi
      · rw [h] at hi
        exact Or.inr hi
    by_cases hAB : G.IsClique A ∧ G.IsClique B
    · exact hamiltonian_of_two_clique_components v w hvw A B (hn _) (hn _) (hout' _) (hout' _)
        hsep' hcover'' (fun x hx y hy hne => hAB.1 hx hy hne)
        (fun x hx y hy hne => hAB.2 hx hy hne) hk.ge
    · exact step G hk (by omega) v w A B hvw (hn _) (hn _)
        (hout' _).1 (hout' _).2 (hout' _).1 (hout' _).2 (hconn _) (hconn _)
        hcover'' hsep' (by tauto)
  · let e := Fintype.equivFinOfCardEq hthree
    exact conjecture199_connectivity_two_three_components v w hvw hk ht (C ∘ e.symm)
      (fun i => hout' (e.symm i))
      (fun x hx hy => by obtain ⟨i,hi⟩ := hcover' x hx hy; exact ⟨e i, by simpa using hi⟩)
      (fun hij hx hy => hsep (e.symm.injective.ne hij) hx hy) (fun i => hconn (e.symm i))

/-- A checked split of WOWII #199 into the two remaining classes. -/
theorem conjecture199_reduction_local (h1 : H1) (h2 : H2)
    (G : SimpleGraph V) (hc : G.Connected)
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  by_cases hα : G.indepNum ≤ 2
  · exact conjecture199_of_indepNum_le_two hc hα
  by_cases hκ1 : vertexConnectivity G ≤ 1
  · exact conjecture199_of_connectivity_le_one hc ht hκ1
  by_cases hκ2 : vertexConnectivity G = 2
  · exact connectivity_two_reduction h1 hc hκ2 (by omega) ht
  exact h2 G hc (by omega) (by omega) ht

end

section

open SimpleGraph Finset

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {K : SimpleGraph W}

omit [Fintype W] [DecidableEq V] [DecidableEq W] in
private theorem tree_iso_le (e : G ≃g K) :
    largestInducedTreeSize K ≤ largestInducedTreeSize G := by
  unfold largestInducedTreeSize
  apply csSup_le'
  rintro n ⟨t,rfl,ht⟩
  let s := t.map e.symm.toEquiv.toEmbedding
  have hbij : Set.BijOn e (s : Set V) (t : Set W) := by
    refine ⟨?_,e.injective.injOn,?_⟩
    · intro x hx
      rcases mem_map.mp hx with ⟨y,hy,rfl⟩
      simpa using hy
    · intro y hy
      refine ⟨e.symm y, ?_, by simp⟩
      exact mem_map.mpr ⟨y,hy,rfl⟩
  have hs := (Iso.induce e hbij).isTree_iff.mpr ht
  have hb := card_le_largestInducedTreeSize hs
  unfold largestInducedTreeSize at hb
  simpa [s] using hb

private theorem transfer_cut {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {P : SimpleGraph A} {Q : SimpleGraph B} (f : P ≃g Q) (n : ℕ)
    (hn : ∃ S : Finset A, S.card = n ∧
      (¬ (P.induce ((S : Set A)ᶜ)).Connected ∨ S.card = Fintype.card A - 1)) :
    ∃ T : Finset B, T.card = n ∧
      (¬ (Q.induce ((T : Set B)ᶜ)).Connected ∨ T.card = Fintype.card B - 1) := by
  obtain ⟨S,hS,hCut⟩ := hn
  let T := S.map f.toEquiv.toEmbedding
  have hT : T.card = S.card := card_map _
  refine ⟨T, hT.trans hS, ?_⟩
  rcases hCut with hdis | hconv
  · apply Or.inl
    have hbij : Set.BijOn f ((S : Set A)ᶜ) ((T : Set B)ᶜ) := by
      refine ⟨?_, f.injective.injOn, ?_⟩
      · intro x hx hfx
        obtain ⟨y,hy,hyx⟩ := mem_map.mp hfx
        exact hx (f.injective hyx ▸ hy)
      · intro y hy
        refine ⟨f.symm y, ?_, by simp⟩
        intro h
        apply hy
        exact mem_map.mpr ⟨f.symm y, h, by simp⟩
    exact fun ht => hdis ((Iso.induce f hbij).connected_iff.mpr ht)
  · exact Or.inr (hT.trans (hconv.trans (by rw [Fintype.card_congr f.toEquiv])))

private theorem vertexConnectivity_iso (e : G ≃g K) :
    vertexConnectivity G = vertexConnectivity K := by
  classical
  have hcard : Fintype.card V = Fintype.card W := Fintype.card_congr e.toEquiv
  unfold vertexConnectivity
  rw [hcard]
  split_ifs
  · rfl
  · congr 1
    ext n
    constructor
    · intro hn
      have h : ∃ S : Finset V, S.card = n ∧
          (¬ (G.induce ((S : Set V)ᶜ)).Connected ∨ S.card = Fintype.card V - 1) := by
        simpa only [hcard, Set.mem_ofPred_eq] using hn
      exact transfer_cut e n h
    · intro hn
      simpa only [hcard, Set.mem_ofPred_eq] using transfer_cut e.symm n (by simpa only [Set.mem_ofPred_eq] using hn)

/-- Universe-zero instances of the two remaining steps suffice for all finite vertex types. -/
theorem conjecture199_reduction_small (h1 : H1) (h2 : H2)
    {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) (hc : G.Connected)
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let e := Fintype.equivFin V
  let K : SimpleGraph (Fin (Fintype.card V)) := G.map e.toEmbedding
  let i : G ≃g K := SimpleGraph.Iso.map e G
  let _ : Nontrivial (Fin (Fintype.card V)) :=
    Fin.nontrivial_iff_two_le.mpr Fintype.one_lt_card
  have hc' := i.connected_iff.mp hc
  have ht' : largestInducedTreeSize K - 2 ≤ vertexConnectivity K := by
    rw [← vertexConnectivity_iso i]
    exact (Nat.sub_le_sub_right (tree_iso_le i) 2).trans ht
  obtain ⟨x,y,p,hp⟩ := conjecture199_reduction_local h1 h2 K hc' ht'
  exact ⟨_,_,p.map i.symm.toHom,hp.map i.symm.toHom i.symm.bijective⟩

end

theorem main : H1 → H2 → type_of% @WrittenOnTheWallII.GraphConjecture199.conjecture199 := by
  intro h1 h2 V _ _ _ G hc ht
  exact conjecture199_reduction_small h1 h2 G hc ht

end OMA.R_WrittenOnTheWallII_GraphConjecture199_conjecture199_R1
