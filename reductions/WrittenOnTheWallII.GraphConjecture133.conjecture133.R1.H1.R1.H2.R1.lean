import OMAReductions.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1_H1_R1

/-!
This reduction proves the radius-two, gap-three case of the exact average bound.
It also uses the induced-path radius bound and proves a local counting estimate
for radius-two graphs with a center of degree below the gap.
-/

namespace OMA.W133Gap
open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1
open OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1_H1_R1

variable {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α)

private def SquareFree : Prop :=
  ¬ (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)

-- Common-neighbor uniqueness follows the merged gap-two proof.
omit [Fintype α] in
private lemma common_eq (hC : SquareFree G)
    {x p s t : α} (hs : G.Adj x s) (hsp : G.Adj s p) (ht : G.Adj x t)
    (htp : G.Adj t p) (hxp : x ≠ p) : s = t := by
  by_contra hst
  exact hC ⟨x, s, p, t, hs.ne, hxp, ht.ne, hsp.ne, hst,
    htp.ne.symm, hs, hsp, htp.symm, ht.symm⟩

private lemma path6 (a b c d e f : α)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hde : G.Adj d e)
    (hef : G.Adj e f)
    (nac : ¬ G.Adj a c) (nad : ¬ G.Adj a d) (nae : ¬ G.Adj a e) (naf : ¬ G.Adj a f)
    (nbd : ¬ G.Adj b d) (nbe : ¬ G.Adj b e) (nbf : ¬ G.Adj b f)
    (nce : ¬ G.Adj c e) (ncf : ¬ G.Adj c f) (ndf : ¬ G.Adj d f)
    (h : [a,b,c,d,e,f].Nodup) : 6 ≤ SimpleGraph.path G := by
  let l := [a,b,c,d,e,f]
  have hi : G.isInducedPath l := by
    refine ⟨h, ?_⟩
    intro ⟨i, hi⟩ ⟨j, hj⟩
    have hi' : i < 6 := hi
    have hj' : j < 6 := hj
    have nac' : ¬ G.Adj c a := fun ha => nac ha.symm
    have nad' : ¬ G.Adj d a := fun ha => nad ha.symm
    have nae' : ¬ G.Adj e a := fun ha => nae ha.symm
    have naf' : ¬ G.Adj f a := fun ha => naf ha.symm
    have nbd' : ¬ G.Adj d b := fun ha => nbd ha.symm
    have nbe' : ¬ G.Adj e b := fun ha => nbe ha.symm
    have nbf' : ¬ G.Adj f b := fun ha => nbf ha.symm
    have nce' : ¬ G.Adj e c := fun ha => nce ha.symm
    have ncf' : ¬ G.Adj f c := fun ha => ncf ha.symm
    have ndf' : ¬ G.Adj f d := fun ha => ndf ha.symm
    interval_cases i <;> interval_cases j <;>
      simp [l, hab, hbc, hcd, hde, hef, hab.symm, hbc.symm, hcd.symm, hde.symm,
        hef.symm, nac, nad, nae, naf, nbd, nbe, nbf, nce, ncf, ndf, nac', nad',
        nae', naf', nbd', nbe', nbf', nce', ncf', ndf']
  exact length_le_path_of_isInducedPath G l hi

private def Outer (c x : α) : Prop := x ≠ c ∧ ¬ G.Adj c x

private structure Branches where
  root : α
  parent : α → α
  root_adj : ∀ x, Outer G root x → G.Adj root (parent x)
  parent_adj : ∀ x, Outer G root x → G.Adj (parent x) x

variable {G}

omit [Fintype α] in
private lemma Branches.parent_eq (B : Branches G) (hc : SquareFree G)
    {x a : α} (hx : Outer G B.root x) (ha : G.Adj B.root a) (hax : G.Adj a x) :
    a = B.parent x :=
  common_eq G hc ha hax (B.root_adj x hx) (B.parent_adj x hx) hx.1.symm

omit [Fintype α] in
private lemma Branches.same_branch (B : Branches G) (hc : SquareFree G)
    {x y z : α} (hy : Outer G B.root y) (hz : Outer G B.root z)
    (hyz : B.parent y = B.parent z) (hxy : G.Adj x y) (hxz : G.Adj x z)
    (hxp : x ≠ B.parent y) : y = z := by
  apply common_eq G hc hxy (B.parent_adj y hy).symm hxz _ hxp
  rw [hyz]
  exact (B.parent_adj z hz).symm

private def Cross (B : Branches G) (x y : α) : Prop :=
  Outer G B.root y ∧ B.parent x ≠ B.parent y ∧ G.Adj x y

private def Active (B : Branches G) (x : α) : Prop :=
  ∃ y z, Cross B x y ∧ Cross B x z ∧ y ≠ z ∧ ¬G.Adj y z

private def EndBranch (B : Branches G) (a : α) : Prop :=
  ∃ x y z, Outer G B.root x ∧ Cross B x y ∧ Cross B x z ∧ y ≠ z ∧ ¬G.Adj y z ∧
    B.parent y = a

private lemma active_colors (B : Branches G) (hc : SquareFree G)
    {x y z : α} (hx : Outer G B.root x) (hy : Cross B x y) (hz : Cross B x z)
    (hyz : y ≠ z) : B.parent y ≠ B.parent z := by
  intro h
  exact hyz (B.same_branch hc hy.1 hz.1 h hy.2.2 hz.2.2
    (fun heq => hx.2 (heq ▸ B.root_adj y hy.1)))

private lemma extend_at_root (B : Branches G) (hc : SquareFree G) {x y z w : α}
    (hx : Outer G B.root x) (hy : Cross B x y) (hz : Cross B x z)
    (hyz : y ≠ z) (hn : ¬ G.Adj y z) (hw : G.Adj B.root w)
    (hwp : w ≠ B.parent x) (hwy : w ≠ B.parent y) (hwz : w ≠ B.parent z)
    (hwzn : ¬ G.Adj (B.parent z) w) : 6 ≤ SimpleGraph.path G := by
  have hna {a u : α} (hu : Outer G B.root u) (ha : G.Adj B.root a)
      (h : a ≠ B.parent u) : ¬ G.Adj a u :=
    fun hadj => h (B.parent_eq hc hu ha hadj)
  have hyz' := active_colors B hc hx hy hz hyz
  have hzr := B.root_adj z hz.1
  refine path6 G y x z (B.parent z) B.root w hy.2.2.symm hz.2.2
    (B.parent_adj z hz.1).symm hzr.symm hw hn
    (fun he => hna hy.1 hzr hyz'.symm he.symm) (fun hah => hy.1.2 hah.symm)
    (fun he => hna hy.1 hw hwy he.symm)
    (fun he => hna hx hzr hz.2.1.symm he.symm) (fun hah => hx.2 hah.symm)
    (fun he => hna hx hw hwp he.symm) (fun hah => hz.1.2 hah.symm)
    (fun he => hna hz.1 hw hwz he.symm) hwzn ?_
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_false_eq_true, not_or, List.nodup_nil,
    and_true]
  have rx := hx.1
  have ry := hy.1.1
  have rz := hz.1.1
  have hxy := hy.2.2.ne
  have hxz := hz.2.2.ne
  have hzw := (B.parent_adj z hz.1).ne
  have heq {u a : α} (hu : Outer G B.root u) (ha : G.Adj B.root a) : u ≠ a :=
    fun h => hu.2 (h ▸ ha)
  exact ⟨⟨hxy.symm, hyz, heq hy.1 hzr, ry, heq hy.1 hw⟩,
    ⟨hxz, heq hx hzr, rx, heq hx hw⟩,
    ⟨hzw.symm, rz, heq hz.1 hw⟩, ⟨hzr.ne.symm, hwz.symm⟩, hw.ne⟩

private lemma extend_at_branch (B : Branches G) (hc : SquareFree G) {x y z u : α}
    (hx : Outer G B.root x) (hy : Cross B x y) (hz : Cross B x z)
    (hyz : y ≠ z) (hn : ¬ G.Adj y z) (hu : Outer G B.root u)
    (huy : B.parent u = B.parent y) (hne : u ≠ y)
    (huy' : ¬ G.Adj u y) (huz : ¬ G.Adj u z) : 6 ≤ SimpleGraph.path G := by
  have hyr := B.root_adj y hy.1
  have hzr := B.root_adj z hz.1
  have hyz' := active_colors B hc hx hy hz hyz
  have hyu : G.Adj (B.parent y) u := huy ▸ B.parent_adj u hu
  have hna {a v : α} (hv : Outer G B.root v) (ha : G.Adj B.root a)
      (h : a ≠ B.parent v) : ¬ G.Adj a v :=
    fun hadj => h (B.parent_eq hc hv ha hadj)
  have nux : ¬ G.Adj u x := by
    intro ha
    exact hne (B.same_branch hc hu hy.1 huy ha.symm hy.2.2
      (fun heq => hx.2 (heq ▸ B.root_adj u hu)))
  have hxr := B.root_adj x hx
  have heq {v a : α} (hv : Outer G B.root v) (ha : G.Adj B.root a) : v ≠ a :=
    fun h => hv.2 (h ▸ ha)
  by_cases np : G.Adj (B.parent y) (B.parent z)
  · have nyp : ¬ G.Adj (B.parent y) (B.parent x) := by
      intro ha
      exact hz.2.1 (common_eq G hc hxr ha.symm hzr np.symm hyr.ne)
    have nup : ¬ G.Adj (B.parent x) u :=
      hna hu hxr (fun he => hy.2.1 (he.trans huy))
    refine path6 G u (B.parent y) B.root (B.parent x) x z hyu.symm hyr.symm
      hxr (B.parent_adj x hx) hz.2.2 (fun hah => hu.2 hah.symm) (fun he => nup he.symm) nux huz nyp
      (hna hx hyr hy.2.1.symm) (hna hz.1 hyr hyz') hx.2 hz.1.2
      (hna hz.1 hxr hz.2.1) ?_
    simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_false_eq_true, not_or, List.nodup_nil,
      and_true]
    exact ⟨⟨heq hu hyr, hu.1, heq hu hxr, fun he => hy.2.1 (he ▸ huy), fun he =>
        hyz' (he ▸ huy).symm⟩,
      ⟨hyr.ne.symm, hy.2.1.symm, (heq hx hyr).symm, (heq hz.1 hyr).symm⟩,
      ⟨hxr.ne, hx.1.symm, hz.1.1.symm⟩,
      ⟨(heq hx hxr).symm, (heq hz.1 hxr).symm⟩, hz.2.2.ne⟩
  · refine path6 G u (B.parent y) y x z (B.parent z) hyu.symm
      (B.parent_adj y hy.1) hy.2.2.symm hz.2.2 (B.parent_adj z hz.1).symm
      huy' nux huz (fun he => hna hu hzr (fun he' => hyz' (he'.trans huy).symm) he.symm)
      (hna hx hyr hy.2.1.symm) (hna hz.1 hyr hyz') np hn
      (fun he => hna hy.1 hzr hyz'.symm he.symm)
      (fun he => hna hx hzr hz.2.1.symm he.symm) ?_
    simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_false_eq_true, not_or, List.nodup_nil,
      and_true]
    exact ⟨⟨heq hu hyr, hne, fun h => hy.2.1 (h ▸ huy), fun h => hyz' (h ▸ huy).symm,
      heq hu hzr⟩,
      ⟨(heq hy.1 hyr).symm, (heq hx hyr).symm, (heq hz.1 hyr).symm, hyz'⟩,
      ⟨hy.2.2.ne.symm, hyz, heq hy.1 hzr⟩, ⟨hz.2.2.ne, heq hx hzr⟩, heq hz.1 hzr⟩

variable [DecidableRel G.Adj]

private def roots (B : Branches G) : Finset α := univ.filter (G.Adj B.root)
private def children (B : Branches G) : Finset α :=
  univ.filter (fun x => x ≠ B.root ∧ ¬ G.Adj B.root x)
private def branch (B : Branches G) (a : α) : Finset α :=
  (children B).filter (fun x => B.parent x = a)

omit [DecidableEq α] in
@[simp] private lemma mem_roots (B : Branches G) (a : α) :
    a ∈ roots B ↔ G.Adj B.root a := by simp [roots]

@[simp] private lemma mem_children (B : Branches G) (x : α) :
    x ∈ children B ↔ Outer G B.root x := by simp [children, Outer]

@[simp] private lemma mem_branch (B : Branches G) (a x : α) :
    x ∈ branch B a ↔ Outer G B.root x ∧ B.parent x = a := by simp [branch]

private lemma root_count (B : Branches G) :
    indepNeighborsCard G B.root ≤ (roots B).card := by
  obtain ⟨S, ha, -, hn⟩ := exists_indepNeighbors G B.root
  rw [← hn]
  exact card_le_card (fun x hx => (mem_roots B x).mpr (ha x hx))

private lemma parent_mem_branch (B : Branches G) (hc : SquareFree G)
    {a x : α} (ha : G.Adj B.root a) (hax : G.Adj a x) :
    x ∈ branch B a ∨ x = B.root ∨ G.Adj B.root x := by
  by_cases hx : Outer G B.root x
  · exact Or.inl ((mem_branch B a x).mpr ⟨hx, (B.parent_eq hc hx ha hax).symm⟩)
  · right
    by_cases he : x = B.root
    · exact Or.inl he
    · exact Or.inr (by_contra (fun hn => hx ⟨he, hn⟩))

omit [Fintype α] [DecidableRel G.Adj] in
private lemma clique_near_parent (B : Branches G) (hc : SquareFree G)
    {a x y : α} (ha : G.Adj B.root a) (hax : G.Adj a x) (hay : G.Adj a y)
    (hx : x = B.root ∨ G.Adj B.root x) (hy : y = B.root ∨ G.Adj B.root y) :
    x = y ∨ G.Adj x y := by
  rcases hx with rfl | hx <;> rcases hy with rfl | hy
  · exact Or.inl rfl
  · exact Or.inr hy
  · exact Or.inr hx.symm
  · exact Or.inl (common_eq G hc hx hax.symm hy hay.symm ha.ne)

private noncomputable def penalty (B : Branches G) (a : α) : ℕ :=
  open scoped Classical in
  if ∃ x ∈ branch B a, ∃ y ∈ branch B a, G.Adj x y then 1 else 0

private lemma parent_count (B : Branches G) (hc : SquareFree G)
    {a : α} (ha : G.Adj B.root a) :
    indepNeighborsCard G a + penalty B a ≤ (branch B a).card + 1 := by
  classical
  obtain ⟨S, hSA, hSI, hSc⟩ := exists_indepNeighbors G a
  let S₁ := S.filter (· ∈ branch B a)
  let S₂ := S.filter (· ∉ branch B a)
  have h₁ : S₁.card + penalty B a ≤ (branch B a).card := by
    have hsub : S₁ ⊆ branch B a := fun x hx => (mem_filter.mp hx).2
    by_cases h : ∃ x ∈ branch B a, ∃ y ∈ branch B a, G.Adj x y
    · obtain ⟨x, hx, y, hy, hxy⟩ := h
      have hlt : S₁.card < (branch B a).card := by
        apply card_lt_card
        refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
        intro he
        have hmem (u : α) (hu : u ∈ branch B a) : u ∈ S :=
          (mem_filter.mp (show u ∈ S₁ by rwa [he])).1
        exact hSI (hmem x hx) (hmem y hy) hxy.ne hxy
      have : penalty B a = 1 := by
        simp only [penalty, if_pos (show ∃ x ∈ branch B a, ∃ y ∈ branch B a, G.Adj x y from
          ⟨x, hx, y, hy, hxy⟩)]
      omega
    · simpa only [penalty, if_neg h, add_zero] using card_le_card hsub
  have h₂ : S₂.card ≤ 1 := by
    rw [card_le_one]
    intro x hx y hy
    obtain ⟨hxS, hxn⟩ := mem_filter.mp hx
    obtain ⟨hyS, hyn⟩ := mem_filter.mp hy
    rcases clique_near_parent B hc ha (hSA x hxS) (hSA y hyS)
      ((parent_mem_branch B hc ha (hSA x hxS)).resolve_left hxn)
      ((parent_mem_branch B hc ha (hSA y hyS)).resolve_left hyn) with he | he
    · exact he
    · exact by_contra (fun h => hSI hxS hyS h he)
  have hs : S₁.card + S₂.card = S.card := card_filter_add_card_filter_not _
  omega

omit [DecidableRel G.Adj] in
private lemma clique_near_child (B : Branches G) (hc : SquareFree G)
    {u x y : α} (hu : Outer G B.root u) (hux : G.Adj u x) (huy : G.Adj u y)
    (hx : ¬ Cross B u x) (hy : ¬ Cross B u y) : x = y ∨ G.Adj x y := by
  have aux {z : α} (haz : G.Adj u z) (hn : ¬ Cross B u z) :
      z = B.parent u ∨ (Outer G B.root z ∧ B.parent u = B.parent z) := by
    by_cases hz : Outer G B.root z
    · right
      exact ⟨hz, by_contra (fun hp => hn ⟨hz, hp, haz⟩)⟩
    · left
      have hne : z ≠ B.root := fun he => hu.2 (he ▸ haz.symm)
      have hz' : G.Adj B.root z := by_contra (fun hn => hz ⟨hne, hn⟩)
      exact B.parent_eq hc hu hz' haz.symm
  rcases aux hux hx with rfl | ⟨hx, hpx⟩ <;> rcases aux huy hy with rfl | ⟨hy, hpy⟩
  · exact Or.inl rfl
  · exact Or.inr (hpy.symm ▸ B.parent_adj y hy)
  · exact Or.inr (hpx.symm ▸ (B.parent_adj x hx).symm)
  · exact Or.inl (B.same_branch hc hx hy (hpx.symm.trans hpy) hux huy
      (fun he => hu.2 (he ▸ B.root_adj x hx)))

omit [DecidableRel G.Adj] in
private lemma parent_colors_triple (B : Branches G) (hc : SquareFree G)
    {x y z : α} (hx : Outer G B.root x) (hy : Cross B x y) (hz : Cross B x z)
    (hyz : y ≠ z) :
    ({B.parent x, B.parent y, B.parent z} : Finset α).card = 3 := by
  have hd1 := hy.2.1
  have hd2 := hz.2.1
  have hd3 := active_colors B hc hx hy hz hyz
  simp [Finset.card_insert_of_notMem, hd1, hd2, hd3]

private lemma active_roots (B : Branches G) (hc : SquareFree G) (hp : SimpleGraph.path G ≤ 5)
    {x : α} (hx : Outer G B.root x) (ha : Active B x) : (roots B).card = 3 := by
  classical
  obtain ⟨y,z,hy,hz,hyz,hn⟩ := ha
  let T : Finset α := {B.parent x, B.parent y, B.parent z}
  have hs : T ⊆ roots B := by
    intro a ha
    have := B.root_adj x hx
    have := B.root_adj y hy.1
    have := B.root_adj z hz.1
    simpa [T] using (show G.Adj B.root a by
      simp only [T, mem_insert, mem_singleton] at ha
      rcases ha with rfl | rfl | rfl <;> assumption)
  have hT : T.card = 3 := parent_colors_triple B hc hx hy hz hyz
  suffices he : T = roots B by rwa [← he]
  apply eq_of_subset_of_card_le hs
  by_contra h
  have hlt : T.card < (roots B).card := by omega
  obtain ⟨w, hw, hwn⟩ := exists_mem_notMem_of_card_lt_card hlt
  have hw' := (mem_roots B w).mp hw
  have hwyz := active_colors B hc hx hy hz hyz
  simp only [T, mem_insert, mem_singleton, not_or] at hwn
  by_cases hz' : G.Adj (B.parent z) w
  · have hy' : ¬ G.Adj (B.parent y) w := by
      intro ha
      exact hwyz (common_eq G hc (B.root_adj y hy.1) ha
        (B.root_adj z hz.1) hz' hw'.ne)
    have := extend_at_root B hc hx hz hy hyz.symm (fun h => hn h.symm)
      hw' hwn.1 hwn.2.2 hwn.2.1 hy'
    omega
  · have := extend_at_root B hc hx hy hz hyz hn hw' hwn.1 hwn.2.1 hwn.2.2 hz'
    omega

private lemma cross_card (B : Branches G) (hc : SquareFree G)
    {u : α} (hu : Outer G B.root u) (S : Finset α) [DecidablePred (Cross B u)] :
    (S.filter (Cross B u)).card ≤ ((roots B).erase (B.parent u)).card := by
  apply card_le_card_of_injOn B.parent
  · intro y hy
    have hyC : Cross B u y := (mem_filter.mp hy).2
    exact mem_erase.mpr ⟨hyC.2.1.symm, (mem_roots B _).mpr (B.root_adj y hyC.1)⟩
  · intro y hy z hz he
    have hyC : Cross B u y := (mem_filter.mp hy).2
    have hzC : Cross B u z := (mem_filter.mp hz).2
    exact B.same_branch hc hyC.1 hzC.1 he hyC.2.2 hzC.2.2
      (fun heq => hu.2 (heq ▸ B.root_adj y hyC.1))

omit [DecidableRel G.Adj] in
private lemma local_split (B : Branches G) (hc : SquareFree G)
    {u : α} (hu : Outer G B.root u) (S : Finset α)
    [DecidablePred (Cross B u)]
    (hSA : ∀ x ∈ S, G.Adj u x) (hSI : G.IsIndepSet (S : Set α)) :
    S.card ≤ 1 + (S.filter (Cross B u)).card := by
  have h₂ : (S.filter (fun x => ¬ Cross B u x)).card ≤ 1 := by
    rw [card_le_one]
    intro x hx y hy
    obtain ⟨hxS, hxn⟩ := mem_filter.mp hx
    obtain ⟨hyS, hyn⟩ := mem_filter.mp hy
    rcases clique_near_child B hc hu (hSA x hxS) (hSA y hyS) hxn hyn with he | he
    · exact he
    · exact by_contra (fun h => hSI hxS hyS h he)
  have hsplit := card_filter_add_card_filter_not (s := S) (Cross B u)
  omega

private lemma child_count (B : Branches G) (hc : SquareFree G) (hp : SimpleGraph.path G ≤ 5)
    {u : α} (hu : Outer G B.root u) :
    indepNeighborsCard G u ≤ 2 + (open scoped Classical in if Active B u then 1 else 0) := by
  classical
  obtain ⟨S, hSA, hSI, hSc⟩ := exists_indepNeighbors G u
  have hsplit := local_split B hc hu S hSA hSI
  by_cases h : Active B u
  · have hroots := active_roots B hc hp hu h
    have h₁ := cross_card B hc hu S
    rw [card_erase_of_mem ((mem_roots B _).mpr (B.root_adj u hu)), hroots] at h₁
    simp only [if_pos h]
    omega
  · have h₁ : (S.filter (Cross B u)).card ≤ 1 := by
      rw [card_le_one]
      intro x hx y hy
      obtain ⟨hxS, hxC⟩ := mem_filter.mp hx
      obtain ⟨hyS, hyC⟩ := mem_filter.mp hy
      by_contra hxy
      exact h ⟨x,y,hxC,hyC,hxy,hSI hxS hyS hxy⟩
    simp only [if_neg h]
    omega

private lemma child_count_roots (B : Branches G) (hc : SquareFree G)
    {u : α} (hu : Outer G B.root u) :
    indepNeighborsCard G u ≤ (roots B).card := by
  classical
  obtain ⟨S, hSA, hSI, hSc⟩ := exists_indepNeighbors G u
  have hsplit := local_split B hc hu S hSA hSI
  have h₁ := cross_card B hc hu S
  have hmem := (mem_roots B _).mpr (B.root_adj u hu)
  have hpos := card_pos.mpr ⟨_, hmem⟩
  rw [card_erase_of_mem hmem] at h₁
  omega

private lemma end_branch_count (B : Branches G) (hc : SquareFree G)
    (hp : SimpleGraph.path G ≤ 5) {a : α} (ha : EndBranch B a) :
    (branch B a).card ≤ 2 + penalty B a := by
  classical
  obtain ⟨x,y,z,hx,hy,hz,hyz,hn,rfl⟩ := ha
  let U := branch B (B.parent y)
  let Sy := U.filter (G.Adj y)
  let Sz := U.filter (G.Adj z)
  have hyU : y ∈ U := (mem_branch B _ _).mpr ⟨hy.1, rfl⟩
  have hsub : U ⊆ insert y (Sy ∪ Sz) := by
    intro u hu
    obtain ⟨hu', hup⟩ := (mem_branch B _ _).mp hu
    by_cases h : u = y
    · subst u
      exact mem_insert_self y (Sy ∪ Sz)
    by_cases h' : G.Adj y u
    · exact mem_insert_of_mem (mem_union_left _ (mem_filter.mpr ⟨hu, h'⟩))
    by_cases h'' : G.Adj z u
    · exact mem_insert_of_mem (mem_union_right _ (mem_filter.mpr ⟨hu, h''⟩))
    have := extend_at_branch B hc hx hy hz hyz hn hu' hup h
      (fun ha => h' ha.symm) (fun ha => h'' ha.symm)
    omega
  have hz1 : Sz.card ≤ 1 := by
    rw [card_le_one]
    intro u hu v hv
    obtain ⟨huU, huA⟩ := mem_filter.mp hu
    obtain ⟨hvU, hvA⟩ := mem_filter.mp hv
    obtain ⟨hu', hup⟩ := (mem_branch B _ _).mp huU
    obtain ⟨hv', hvp⟩ := (mem_branch B _ _).mp hvU
    exact B.same_branch hc hu' hv' (hup.trans hvp.symm) huA hvA
      (fun he => hz.1.2 (he ▸ B.root_adj u hu'))
  have hy1 : Sy.card ≤ penalty B (B.parent y) := by
    by_cases hE : ∃ u ∈ U, ∃ v ∈ U, G.Adj u v
    · have hpen : penalty B (B.parent y) = 1 := by exact if_pos hE
      rw [hpen, card_le_one]
      intro u hu v hv
      obtain ⟨huU, huA⟩ := mem_filter.mp hu
      obtain ⟨hvU, hvA⟩ := mem_filter.mp hv
      obtain ⟨hu', hup⟩ := (mem_branch B _ _).mp huU
      obtain ⟨hv', hvp⟩ := (mem_branch B _ _).mp hvU
      exact B.same_branch hc hu' hv' (hup.trans hvp.symm) huA hvA
        (fun he => hy.1.2 (he ▸ B.root_adj u hu'))
    · have hSy : Sy = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro u hu
        obtain ⟨huU, huA⟩ := mem_filter.mp hu
        exact hE ⟨y, hyU, u, huU, huA⟩
      rw [hSy, card_empty]
      exact Nat.zero_le _
  have hu : U.card ≤ (insert y (Sy ∪ Sz)).card := card_le_card hsub
  have hins := card_insert_le y (Sy ∪ Sz)
  have hun := card_union_le (s := Sy) (t := Sz)
  change U.card ≤ _
  omega

private noncomputable def activeChildren (B : Branches G) : Finset α :=
  open scoped Classical in (children B).filter (Active B)

private lemma branch_sum (B : Branches G) :
    ∑ a ∈ roots B, (branch B a).card = (children B).card := by
  classical
  unfold branch
  rw [sum_card_fiberwise_eq_card_filter]
  congr 1
  apply filter_true_of_mem
  intro x hx
  exact (mem_roots B _).mpr (B.root_adj x ((mem_children B x).mp hx))

private lemma eq_parent_of_not_end (B : Branches G) (hc : SquareFree G)
    (hk : (roots B).card = 3)
    {x y z a : α} (hx : Outer G B.root x) (hy : Cross B x y) (hz : Cross B x z)
    (hyz : y ≠ z) (hn : ¬ G.Adj y z) (ha : a ∈ roots B) (hE : ¬ EndBranch B a) :
    B.parent x = a := by
  let T : Finset α := {B.parent x, B.parent y, B.parent z}
  have hs : T ⊆ roots B := by
    intro u hu
    simp only [T, mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact (mem_roots B _).mpr (B.root_adj x hx)
    · exact (mem_roots B _).mpr (B.root_adj y hy.1)
    · exact (mem_roots B _).mpr (B.root_adj z hz.1)
  have hT : T.card = 3 := parent_colors_triple B hc hx hy hz hyz
  have he : T = roots B := eq_of_subset_of_card_le hs (by omega)
  rw [← he] at ha
  simp only [T, mem_insert, mem_singleton] at ha
  rcases ha with h | h | h
  · exact h.symm
  · exact (hE ⟨x,y,z,hx,hy,hz,hyz,hn,h.symm⟩).elim
  · exact (hE ⟨x,z,y,hx,hz,hy,hyz.symm,fun h => hn h.symm,h.symm⟩).elim

private lemma active_sum (B : Branches G) (hc : SquareFree G)
    (hp : SimpleGraph.path G ≤ 5) :
    (activeChildren B).card ≤ (roots B).card + 3 + ∑ a ∈ roots B, penalty B a := by
  classical
  have implies (x) (hx : x ∈ activeChildren B) : Outer G B.root x ∧ Active B x := by
    simpa [activeChildren] using hx
  by_cases hnon : (activeChildren B).Nonempty
  · obtain ⟨u, hu⟩ := hnon
    obtain ⟨huO, huA⟩ := implies u hu
    have hk := active_roots B hc hp huO huA
    by_cases he : ∀ a ∈ roots B, EndBranch B a
    · have hsum : ∑ a ∈ roots B, (branch B a).card ≤
          ∑ a ∈ roots B, (2 + penalty B a) :=
        sum_le_sum (fun a ha => end_branch_count B hc hp (he a ha))
      rw [branch_sum B, sum_add_distrib, sum_const, smul_eq_mul, hk] at hsum
      have hs : (activeChildren B).card ≤ (children B).card :=
        card_le_card (filter_subset _ _)
      omega
    · push Not at he
      obtain ⟨a, ha, hn⟩ := he
      obtain ⟨v,w,hv,hw,hvw,hnvw⟩ := huA
      have hq : B.parent u = a := eq_parent_of_not_end B hc hk huO hv hw hvw hnvw ha hn
      have hab : a ≠ B.parent v := hq ▸ hv.2.1
      have hmaps : ∀ x ∈ activeChildren B, ∃ y ∈ branch B (B.parent v), G.Adj x y := by
        intro x hx
        obtain ⟨hxO,s,t,hs,ht,hst,hnst⟩ := implies x hx
        have hxa := eq_parent_of_not_end B hc hk hxO hs ht hst hnst ha hn
        let T : Finset α := {B.parent x, B.parent s, B.parent t}
        have hT : T.card = 3 := parent_colors_triple B hc hxO hs ht hst
        have hsub : T ⊆ roots B := by
          intro b hb
          simp only [T, mem_insert, mem_singleton] at hb
          rcases hb with rfl | rfl | rfl
          · exact (mem_roots B _).mpr (B.root_adj x hxO)
          · exact (mem_roots B _).mpr (B.root_adj s hs.1)
          · exact (mem_roots B _).mpr (B.root_adj t ht.1)
        have hTr : T = roots B := eq_of_subset_of_card_le hsub (by omega)
        have hvm : B.parent v ∈ T := hTr.symm ▸ (mem_roots B _).mpr (B.root_adj v hv.1)
        simp only [T, mem_insert, mem_singleton] at hvm
        rcases hvm with h | h | h
        · exact (hab (hxa.symm.trans h.symm)).elim
        · exact ⟨s, (mem_branch B _ _).mpr ⟨hs.1,h.symm⟩, hs.2.2⟩
        · exact ⟨t, (mem_branch B _ _).mpr ⟨ht.1,h.symm⟩, ht.2.2⟩
      let f (x : α) : α := if hx : x ∈ activeChildren B then (hmaps x hx).choose else x
      have hcard : (activeChildren B).card ≤ (branch B (B.parent v)).card := by
        apply card_le_card_of_injOn f
        · intro x hx
          have hx' : x ∈ activeChildren B := hx
          simpa [f, hx'] using (hmaps x hx').choose_spec.1
        · intro x hx y hy hxy
          have hx' : x ∈ activeChildren B := hx
          have hy' : y ∈ activeChildren B := hy
          have get (z : α) (hz : z ∈ activeChildren B) : G.Adj z (f z) := by
            simpa [f, hz] using (hmaps z hz).choose_spec.2
          have hax : B.parent x = a := by
            obtain ⟨hxO, s,t,hs,ht,hst,hnst⟩ := implies x hx'
            exact eq_parent_of_not_end B hc hk hxO hs ht hst hnst ha hn
          have hay : B.parent y = a := by
            obtain ⟨hyO,s,t,hs,ht,hst,hnst⟩ := implies y hy'
            exact eq_parent_of_not_end B hc hk hyO hs ht hst hnst ha hn
          have hfr : Outer G B.root (f x) := by
            have hm : f x ∈ branch B (B.parent v) := by
              simpa [f, hx'] using (hmaps x hx').choose_spec.1
            exact ((mem_branch B _ _).mp hm).1
          exact B.same_branch hc (implies x hx').1 (implies y hy').1
            (hax.trans hay.symm) (get x hx').symm (hxy ▸ (get y hy').symm)
            (fun he => hfr.2 (he ▸ B.root_adj x (implies x hx').1))
      have hcb := end_branch_count B hc hp (show EndBranch B (B.parent v) from
        ⟨u,v,w,huO,hv,hw,hvw,hnvw,rfl⟩)
      have hpen : penalty B (B.parent v) ≤ ∑ b ∈ roots B, penalty B b :=
        single_le_sum (fun b _ => Nat.zero_le (penalty B b))
          ((mem_roots B _).mpr (B.root_adj v hv.1))
      omega
  · have : activeChildren B = ∅ := not_nonempty_iff_eq_empty.mp hnon
    simp [this]

private lemma partition_counts (B : Branches G) :
    (roots B).card + (children B).card + 1 = Fintype.card α ∧
    (∑ x, indepNeighborsCard G x) = indepNeighborsCard G B.root +
      (∑ x ∈ roots B, indepNeighborsCard G x) +
      (∑ x ∈ children B, indepNeighborsCard G x) := by
  classical
  have hsplit : roots B ∪ children B = (univ : Finset α).erase B.root := by
    ext x
    simp only [mem_union, mem_roots, mem_children, mem_erase, mem_univ, and_true, Outer]
    by_cases h : G.Adj B.root x
    · simp [h, h.ne.symm]
    · simp [h]
  have hd : Disjoint (roots B) (children B) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    exact ((mem_children B x).mp hy).2 ((mem_roots B x).mp hx)
  have hcard : (roots B).card + (children B).card + 1 = Fintype.card α := by
    have h := card_union_of_disjoint hd
    rw [hsplit, card_erase_of_mem (mem_univ B.root), card_univ] at h
    have : Nonempty α := ⟨B.root⟩
    have hpos := Fintype.card_pos (α := α)
    omega
  have htotal : ∑ x, indepNeighborsCard G x = indepNeighborsCard G B.root +
      (∑ x ∈ roots B, indepNeighborsCard G x) +
      (∑ x ∈ children B, indepNeighborsCard G x) := by
    have hi := sum_erase_add (s := (univ : Finset α)) (indepNeighborsCard G) (mem_univ B.root)
    rw [← hsplit, sum_union hd] at hi
    omega
  exact ⟨hcard, htotal⟩

private lemma branches_count (B : Branches G) (hc : SquareFree G)
    (hp : SimpleGraph.path G ≤ 5) : ∑ x, indepNeighborsCard G x ≤ 3 * Fintype.card α := by
  classical
  obtain ⟨hcard, htotal⟩ := partition_counts B
  have hr := root_count B
  have hparents : ∑ x ∈ roots B, (indepNeighborsCard G x + penalty B x) ≤
      ∑ x ∈ roots B, ((branch B x).card + 1) :=
    sum_le_sum (fun x hx => parent_count B hc ((mem_roots B x).mp hx))
  rw [sum_add_distrib, sum_add_distrib, sum_const, smul_eq_mul, mul_one, branch_sum B] at hparents
  have hchildren : ∑ x ∈ children B, indepNeighborsCard G x ≤
      ∑ x ∈ children B, (2 + if Active B x then 1 else 0) :=
    sum_le_sum (fun x hx => child_count B hc hp ((mem_children B x).mp hx))
  rw [sum_add_distrib, sum_const, smul_eq_mul, sum_ite, sum_const_zero, add_zero, sum_const,
    smul_eq_mul, mul_one] at hchildren
  change _ ≤ _ + (activeChildren B).card at hchildren
  have ha := active_sum B hc hp
  omega

omit [DecidableEq α] in
private lemma exists_branches (G : SimpleGraph α) [Nonempty α] (hG : G.Connected)
    {c : α} (hc : G.eccent c = G.radius) (hr : G.radius.toNat ≤ 2) :
    ∃ B : Branches G, B.root = c := by
  classical
  have hfar (x : α) : G.dist c x ≤ 2 := by
    have hh : G.edist c x ≤ G.radius := hc ▸ G.edist_le_eccent
    exact (ENat.toNat_le_toNat hh (G.radius_ne_top_iff.mpr hG)).trans hr
  have hparent : ∀ x, Outer G c x → ∃ a, G.Adj c a ∧ G.Adj a x := by
    intro x hx
    have hd₁ : G.dist c x ≠ 0 := fun he => hx.1 ((hG.dist_eq_zero_iff.mp he).symm)
    have hd₂ : G.dist c x ≠ 1 := fun he => hx.2 (dist_eq_one_iff_adj.mp he)
    have hd : G.dist c x = 2 := by have := hfar x; omega
    obtain ⟨w, hw⟩ := hG.exists_walk_length_eq_dist c x
    rw [hd] at hw
    cases w with
    | nil => simp at hw
    | @cons _ a _ h wa =>
      cases wa with
      | nil => simp at hw
      | @cons _ b _ h' wb =>
        cases wb with
        | nil => exact ⟨a, h, h'⟩
        | cons h'' tail => simp only [Walk.length_cons] at hw; omega
  let p (x : α) : α := if hx : Outer G c x then (hparent x hx).choose else c
  let B : Branches G := ⟨c,p,fun x hx => by simpa [p, hx] using (hparent x hx).choose_spec.1,
    fun x hx => by simpa [p,hx] using (hparent x hx).choose_spec.2⟩
  exact ⟨B, rfl⟩

omit [DecidableEq α] in
private lemma l_le_of_sum (G : SimpleGraph α) [Nonempty α] {d : ℕ}
    (hs : ∑ x, indepNeighborsCard G x ≤ d * Fintype.card α) :
    G.l ≤ (d : ℝ) := by
  have hpos : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  change (∑ x, (indepNeighborsCard G x : ℝ)) / (Fintype.card α : ℝ) ≤ (d : ℝ)
  exact (div_le_iff₀ hpos).mpr (by exact_mod_cast hs)

private lemma l_le_three (G : SimpleGraph α) [Nonempty α] (hG : G.Connected)
    (hc : SquareFree G) (hr : G.radius.toNat ≤ 2) (hp : SimpleGraph.path G ≤ 5) :
    G.l ≤ 3 := by
  classical
  obtain ⟨c, hcR⟩ := G.exists_eccent_eq_radius
  obtain ⟨B, -⟩ := exists_branches G hG hcR hr
  exact_mod_cast l_le_of_sum G (branches_count B hc hp)

private lemma l_le_two (G : SimpleGraph α) [Nonempty α] (hG : G.Connected)
    (hc : SquareFree G) (hr : G.radius.toNat ≤ 1) : G.l ≤ 2 := by
  classical
  obtain ⟨c, hcR⟩ := G.exists_eccent_eq_radius
  obtain ⟨B, hB⟩ := exists_branches G hG hcR (hr.trans (by decide))
  have hno (x : α) : ¬ Outer G B.root x := by
    intro hx
    have he : G.edist c x ≤ G.radius := hcR ▸ G.edist_le_eccent
    have hd : G.dist c x ≤ 1 :=
      (ENat.toNat_le_toNat he (G.radius_ne_top_iff.mpr hG)).trans hr
    rw [hB] at hx
    have h₀ : G.dist c x ≠ 0 := fun he => hx.1 ((hG.dist_eq_zero_iff.mp he).symm)
    have h₁ : G.dist c x ≠ 1 := fun he => hx.2 (dist_eq_one_iff_adj.mp he)
    omega
  have hX : children B = ∅ := by
    ext x
    simp [hno]
  have hpa : ∑ a ∈ roots B, indepNeighborsCard G a ≤ (roots B).card := by
    have hl : ∑ a ∈ roots B, indepNeighborsCard G a ≤ ∑ a ∈ roots B, 1 := by
      apply sum_le_sum
      intro a ha
      have h := parent_count B hc ((mem_roots B a).mp ha)
      simp [branch, hX] at h
      omega
    simpa using hl
  obtain ⟨hcount, hsum⟩ := partition_counts B
  rw [hX, sum_empty, add_zero] at hsum
  simp only [hX, card_empty, add_zero] at hcount
  have hroot := root_count B
  have ht : ∑ x, indepNeighborsCard G x ≤ 2 * Fintype.card α := by omega
  exact_mod_cast l_le_of_sum G ht

private lemma l_le_of_small_center (G : SimpleGraph α) [Nonempty α] [DecidableRel G.Adj]
    (hG : G.Connected) (hc : SquareFree G) (hr : G.radius.toNat ≤ 2)
    {c : α} (hcenter : G.eccent c = G.radius) {d : ℕ} (hd : 2 ≤ d)
    (hdegree : (univ.filter (G.Adj c)).card + 1 ≤ d) : G.l ≤ (d : ℝ) := by
  obtain ⟨B, hB⟩ := exists_branches G hG hcenter hr
  have hrootcard : (roots B).card + 1 ≤ d := by simpa [roots, hB] using hdegree
  obtain ⟨hcount, hsum⟩ := partition_counts B
  have hroot := root_count B
  have hpa : ∑ a ∈ roots B, indepNeighborsCard G a ≤
      (children B).card + (roots B).card := by
    have hl : ∑ a ∈ roots B, indepNeighborsCard G a ≤
        ∑ a ∈ roots B, ((branch B a).card + 1) :=
      sum_le_sum (fun a ha => Nat.le_trans (Nat.le_add_right _ _)
        (parent_count B hc ((mem_roots B a).mp ha)))
    simpa [sum_add_distrib, branch_sum B] using hl
  have hch : ∑ x ∈ children B, indepNeighborsCard G x ≤ (children B).card * (roots B).card := by
    have hl : ∑ x ∈ children B, indepNeighborsCard G x ≤
        ∑ _ ∈ children B, (roots B).card :=
      sum_le_sum (fun _ hx => child_count_roots B hc ((mem_children B _).mp hx))
    simpa using hl
  apply l_le_of_sum G
  calc
    ∑ x, indepNeighborsCard G x ≤
        (roots B).card * 2 + (children B).card * ((roots B).card + 1) := by
      rw [Nat.mul_add, Nat.mul_one, hsum]
      omega
    _ ≤ (roots B).card * d + (children B).card * d :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hd) (Nat.mul_le_mul_left _ hrootcard)
    _ ≤ d * Fintype.card α := by
      rw [← Nat.add_mul, Nat.mul_comm d]
      exact Nat.mul_le_mul_right _ (by omega)

end OMA.W133Gap


/-
The induced-path radius bound is due to Fan Chung in Erdős, Saks and Sós,
Maximum Induced Trees in Graphs, J. Combin. Theory Ser. B 41 (1986).
We use a largest ambient ball to produce the two geodesics.
-/
namespace OMA.W133Radius
open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1_H1_R1

variable {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α)

omit [Fintype α] [DecidableEq α] in
private lemma geodesic_metric (hG : G.Connected) {a b : α}
    (p : G.Walk a b) (hp : p.length = G.dist a b) {i j : ℕ} (hi : i ≤ j)
    (hj : j ≤ p.length) :
    G.dist (p.getVert i) (p.getVert j) = j - i := by
  have hl : (p.drop i).length = p.length - i := Walk.drop_length _ _
  have hg : (p.drop i).getVert (j - i) = p.getVert j := by
    rw [Walk.drop_getVert, show i + (j - i) = j by omega]
  have hc := dist_le ((p.drop i).take (j - i))
  rw [Walk.take_length, hg, hl, min_eq_left (by omega : j - i ≤ p.length - i)] at hc
  have ha := dist_le (p.take i)
  have hb := dist_le (p.drop j)
  rw [Walk.take_length, min_eq_left (hi.trans hj)] at ha
  rw [Walk.drop_length] at hb
  have h₁ := hG.dist_triangle (u := a) (v := p.getVert i) (w := b)
  have h₂ := hG.dist_triangle (u := p.getVert i) (v := p.getVert j) (w := b)
  omega

omit [Fintype α] [DecidableEq α] in
private lemma geodesic_adj_iff (hG : G.Connected) {a b : α}
    (p : G.Walk a b) (hp : p.length = G.dist a b) {i j : ℕ} (hi : i ≤ p.length)
    (hj : j ≤ p.length) :
    G.Adj (p.getVert i) (p.getVert j) ↔ i + 1 = j ∨ j + 1 = i := by
  rw [← dist_eq_one_iff_adj]
  rcases le_total i j with hij | hji
  · rw [geodesic_metric G hG p hp hij hj]
    omega
  · rw [dist_comm, geodesic_metric G hG p hp hji hi]
    omega

omit [Fintype α] [DecidableEq α] in
private lemma geodesic_inj (hG : G.Connected) {a b : α}
    (p : G.Walk a b) (hp : p.length = G.dist a b) {i j : ℕ} (hi : i ≤ p.length)
    (hj : j ≤ p.length) (he : p.getVert i = p.getVert j) :
    i = j := by
  have h0 := hG.dist_eq_zero_iff.mpr he
  rcases le_total i j with hij | hji
  · rw [geodesic_metric G hG p hp hij hj] at h0
    omega
  · rw [dist_comm, geodesic_metric G hG p hp hji hi] at h0
    omega

private lemma two_geodesics (hG : G.Connected) {a b c : α}
    (p : G.Walk a b) (q : G.Walk a c) (hp : p.length = G.dist a b)
    (hq : q.length = G.dist a c) (hr : 2 ≤ p.length)
    (hshort : q.length < p.length)
    (hfar : p.length ≤ G.dist (p.getVert 2) c) :
    2 * p.length - 1 ≤ G.path := by
  classical
  let r := p.length
  let l := q.length
  have hpc (i : ℕ) (hi : i ≤ r) : G.dist a (p.getVert i) = i := by
    simpa using geodesic_metric G hG p hp (Nat.zero_le i) hi
  have hqc (j : ℕ) (hj : j ≤ l) : G.dist a (q.getVert j) = j := by
    simpa using geodesic_metric G hG q hq (Nat.zero_le j) hj
  have hqend (j : ℕ) (hj : j ≤ l) : G.dist (q.getVert j) c = l - j := by
    simpa [l] using geodesic_metric G hG q hq hj (le_refl l)
  have hlen : r - 2 ≤ l := by
    have h := hG.dist_triangle (u := p.getVert 2) (v := a) (w := c)
    rw [dist_comm (u := p.getVert 2) (v := a), hpc 2 hr, ← hq] at h
    change r ≤ _ at hfar
    change _ ≤ 2 + l at h
    omega
  have hdiff (i j : ℕ) (hi : 0 < i) (hir : i ≤ r) (hjl : j ≤ l) :
      p.getVert i ≠ q.getVert j := by
    intro he
    have hij : i = j := by rw [← hpc i hir, ← hqc j hjl, he]
    have ht := hG.dist_triangle (u := p.getVert 2) (v := p.getVert i) (w := c)
    rw [show G.dist (p.getVert i) c = l - j by rw [he, hqend j hjl]] at ht
    by_cases h : 2 ≤ i
    · rw [geodesic_metric G hG p hp h hir] at ht
      change r ≤ _ at hfar
      omega
    · have h₁ : i = 1 := by omega
      rw [h₁, dist_comm (u := p.getVert 2) (v := p.getVert 1),
        geodesic_metric G hG p hp (by decide : 1 ≤ 2) hr] at ht
      change r ≤ _ at hfar
      omega
  have hcross (i j : ℕ) (hi : 0 < i) (hir : i ≤ r) (hjl : j ≤ l)
      (ha : G.Adj (p.getVert i) (q.getVert j)) :
      (i = 1 ∧ j = 0) ∨ (i = 1 ∧ j = 1 ∧ l + 1 = r) := by
    have h₁ := dist_le_of_adj G hG (v := a) ha
    have h₁' := dist_le_of_adj G hG (v := a) ha.symm
    rw [hpc i hir, hqc j hjl] at h₁ h₁'
    have h₂ := hG.dist_triangle (u := p.getVert 2) (v := p.getVert i) (w := c)
    have h₃ := hG.dist_triangle (u := p.getVert i) (v := q.getVert j) (w := c)
    rw [dist_eq_one_iff_adj.mpr ha, hqend j hjl] at h₃
    have hlr : l < r := hshort
    change r ≤ _ at hfar
    by_cases h : 2 ≤ i
    · rw [geodesic_metric G hG p hp h hir] at h₂
      omega
    · have hi' : i = 1 := by omega
      subst i
      rw [dist_comm (u := p.getVert 2) (v := p.getVert 1),
        geodesic_metric G hG p hp (by decide : 1 ≤ 2) hr] at h₂
      omega
  let k : ℕ := if 1 ≤ l ∧ G.Adj (p.getVert 1) (q.getVert 1) then 1 else 0
  have hk : k = 0 ∨ k = 1 := by dsimp [k]; split <;> simp
  have hkpos : k = 1 → 1 ≤ l ∧ G.Adj (p.getVert 1) (q.getVert 1) := by
    intro hh
    by_contra hn
    simp [k, hn] at hh
  let m := r + l + 1 - k
  have hm : 2 * r - 1 ≤ m := by
    rcases hk with hk' | hk'
    · dsimp [m]
      omega
    · obtain ⟨hl, ha⟩ := hkpos hk'
      have hh := hcross 1 1 (by decide) (by omega) hl ha
      dsimp [m]
      omega
  let f (i : ℕ) := if i < r then p.getVert (r - i) else q.getVert (i - r + k)
  have hw := le_path_of_fun G f m
  apply hm.trans
  apply hw
  · intro i j hi hj he
    have hh : ∀ w < m, ¬ w < r → w - r + k ≤ l := by
      intro w hw hwr
      dsimp [m] at hw
      omega
    by_cases hir : i < r <;> by_cases hjr : j < r
    · have := geodesic_inj G hG p hp (i := r-i) (j := r-j) (by omega) (by omega)
        (by simpa only [f, if_pos hir, if_pos hjr] using he)
      omega
    · exact (hdiff (r-i) (j-r+k) (by omega) (by omega) (hh j hj hjr)
        (by simpa only [f, if_pos hir, if_neg hjr] using he)).elim
    · exact (hdiff (r-j) (i-r+k) (by omega) (by omega) (hh i hi hir)
        (by simpa only [f, if_neg hir, if_pos hjr] using he.symm)).elim
    · have := geodesic_inj G hG q hq (hh i hi hir) (hh j hj hjr)
        (by simpa only [f, if_neg hir, if_neg hjr] using he)
      omega
  · intro i j hi hj
    have hh : ∀ w < m, ¬ w < r → w - r + k ≤ l := by
      intro w hw hwr
      dsimp [m] at hw
      omega
    have hmix (i j : ℕ) (hi : i < r) (hj : ¬ j < r) (hjm : j < m) :
        G.Adj (p.getVert (r-i)) (q.getVert (j-r+k)) ↔ i + 1 = j := by
      constructor
      · intro ha
        rcases hcross _ _ (by omega) (by omega) (hh j hjm hj) ha with h | h
        · omega
        · by_cases hK : k = 1
          · omega
          · have hka : k = 1 := by
              have h₁ : r-i = 1 := h.1
              have h₂ : j-r+k = 1 := h.2.1
              rw [h₁,h₂] at ha
              have := hh j hjm hj
              have h₃ : 1 ≤ l := by omega
              simp [k, h₃, ha]
            contradiction
      · intro h
        have hi' : r-i = 1 := by omega
        have hj' : j-r+k = k := by omega
        rw [hi', hj']
        rcases hk with hK | hK
        · rw [hK, Walk.getVert_zero]
          simpa using (p.adj_getVert_succ (by omega : 0 < p.length)).symm
        · rw [hK]
          exact (hkpos hK).2
    by_cases hir : i < r <;> by_cases hjr : j < r
    · simp only [f, if_pos hir, if_pos hjr, geodesic_adj_iff G hG p hp
        (i := r-i) (j := r-j) (by omega) (by omega)]
      omega
    · simp only [f, if_pos hir, if_neg hjr, hmix i j hir hjr hj]
      omega
    · rw [show f i = q.getVert (i-r+k) by simp only [f, if_neg hir],
          show f j = p.getVert (r-j) by simp only [f, if_pos hjr]]
      rw [show G.Adj (q.getVert (i-r+k)) (p.getVert (r-j)) ↔
            G.Adj (p.getVert (r-j)) (q.getVert (i-r+k)) from adj_comm G _ _,
          hmix j i hjr hir hi]
      omega
    · simp only [f, if_neg hir, if_neg hjr, geodesic_adj_iff G hG q hq
        (hh i hi hir) (hh j hj hjr)]
      omega

private lemma radius_bound [Nonempty α] (hG : G.Connected) :
    2 * G.radius.toNat - 1 ≤ G.path := by
  let r := G.radius.toNat
  by_cases hr : 2 ≤ r
  · have hfar (c : α) : ∃ w, r ≤ G.dist c w := by
      obtain ⟨w, hw⟩ := G.exists_edist_eq_eccent_of_finite c
      exact ⟨w, ENat.toNat_le_toNat (hw ▸ G.radius_le_eccent)
        (edist_ne_top_iff_reachable.mpr (hG c w))⟩
    let B (c : α) := (univ : Finset α).filter (fun x => G.dist c x < r)
    obtain ⟨a, -, ha⟩ := exists_max_image (univ : Finset α) (fun c => (B c).card) univ_nonempty
    obtain ⟨z,hz⟩ := hfar a
    obtain ⟨p,hp⟩ := hG.exists_walk_length_eq_dist a z
    let b := p.getVert r
    have hb : G.dist a b = r := by
      simpa [b] using geodesic_metric G hG p hp (Nat.zero_le r) (by omega)
    obtain ⟨q,hq⟩ := hG.exists_walk_length_eq_dist a b
    have hq' : q.length = r := hq.trans hb
    have hfar' : ∃ w ∈ B a, r ≤ G.dist (q.getVert 2) w := by
      by_contra! hn
      have hmap : insert b (B a) ⊆ B (q.getVert 2) := by
        intro w hw
        rcases mem_insert.mp hw with rfl | hw
        · apply mem_filter.mpr
          refine ⟨mem_univ _, ?_⟩
          have hd : G.dist (q.getVert 2) b = q.length - 2 := by
            simpa using geodesic_metric G hG q hq (by omega : 2 ≤ q.length) le_rfl
          omega
        · exact mem_filter.mpr ⟨mem_univ _, hn w hw⟩
      have hb' : b ∉ B a := by simp [B, hb]
      have hcard := card_le_card hmap
      rw [card_insert_of_notMem hb'] at hcard
      have hmax := ha (q.getVert 2) (mem_univ _)
      omega
    obtain ⟨w, hw, hdist⟩ := hfar'
    obtain ⟨s, hs⟩ := hG.exists_walk_length_eq_dist a w
    have hl : G.dist a w < r := (mem_filter.mp hw).2
    have H := two_geodesics G hG q s hq hs (by omega) (by omega) (by omega)
    simpa [hq'] using H
  · obtain ⟨a⟩ := ‹Nonempty α›
    have h := length_le_path_of_isInducedPath G [a] (by
      refine ⟨by simp, ?_⟩
      intro ⟨i,hi⟩ ⟨j,hj⟩
      have hi' : i = 0 := by simpa using hi
      have hj' : j = 0 := by simpa using hj
      subst i
      subst j
      simp)
    change 1 ≤ G.path at h
    omega

end OMA.W133Radius

namespace OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1_H1_R1_H2_R1

open SimpleGraph

/-- The gap-three case at radius three. -/
def H1 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α), G.Connected →
    ¬ (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) →
    G.radius.toNat = 3 → G.path = 6 →
    (∃ v, 3 < G.indepNeighborsCard v) →
    3 * Fintype.card α < 2 * Nat.card G.edgeSet →
    G.l ≤ 3

/-- The gap-three case at radius four. -/
def H2 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α), G.Connected →
    ¬ (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) →
    G.radius.toNat = 4 → G.path = 7 →
    (∃ v, 3 < G.indepNeighborsCard v) →
    3 * Fintype.card α < 2 * Nat.card G.edgeSet →
    G.l ≤ 3

/-- Gaps at least four at radius at least three. -/
def H3 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α), G.Connected →
    ¬ (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) →
    3 ≤ G.radius.toNat → 2 * G.radius.toNat - 1 ≤ G.path →
    G.radius.toNat + 4 ≤ G.path →
    (∃ v, G.path < G.radius.toNat + G.indepNeighborsCard v) →
    (G.path - G.radius.toNat) * Fintype.card α < 2 * Nat.card G.edgeSet →
    (G.radius.toNat : ℝ) + G.l ≤ (G.path : ℝ)

/-- Gaps at least four at radius two, with every center having degree at least the gap. -/
def H4 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α), G.Connected →
    ¬ (∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) →
    G.radius.toNat = 2 → 6 ≤ G.path →
    (∀ c, G.eccent c = G.radius → G.path - 2 ≤ Nat.card (G.neighborSet c)) →
    (∃ v, G.path < G.radius.toNat + G.indepNeighborsCard v) →
    (G.path - G.radius.toNat) * Fintype.card α < 2 * Nat.card G.edgeSet →
    (G.radius.toNat : ℝ) + G.l ≤ (G.path : ℝ)

theorem main : H1 → H2 → H3 → H4 → OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1_H1_R1.H2 := by
  intro h1 h2 h3 h4 α _ _ _ G hG hc hp hv hdense
  classical
  let r := G.radius.toNat
  let d := G.path - r
  have hp' : r + 3 ≤ G.path := hp
  have hd : 3 ≤ d := by dsimp [d]; omega
  have close (hl : G.l ≤ (d : ℝ)) : (G.radius.toNat : ℝ) + G.l ≤ (G.path : ℝ) := by
    dsimp [d] at hl
    rw [Nat.cast_sub (by omega : r ≤ G.path)] at hl
    change (r : ℝ) + G.l ≤ (G.path : ℝ)
    linarith
  by_cases hr1 : r ≤ 1
  · apply close
    exact (OMA.W133Gap.l_le_two G hG hc hr1).trans (by exact_mod_cast (show 2 ≤ d by omega))
  have hrbound : 2 * r - 1 ≤ G.path := OMA.W133Radius.radius_bound G hG
  by_cases hd3 : d = 3
  · have he : G.path = r + 3 := by dsimp [d] at hd3; omega
    have hv' : ∃ v, 3 < G.indepNeighborsCard v := by
      obtain ⟨v, hv⟩ := hv
      exact ⟨v, by change G.path < r + _ at hv; omega⟩
    have hdense' : 3 * Fintype.card α < 2 * Nat.card G.edgeSet := by
      change d * Fintype.card α < _ at hdense
      simpa only [hd3] using hdense
    apply close
    rw [hd3]
    change G.l ≤ 3
    rcases (by omega : r = 2 ∨ r = 3 ∨ r = 4) with hr | hr | hr
    · exact OMA.W133Gap.l_le_three G hG hc (by omega) (by omega)
    · exact h1 G hG hc hr (by omega) hv' hdense'
    · exact h2 G hG hc hr (by omega) hv' hdense'
  have hd4 : r + 4 ≤ G.path := by dsimp [d] at hd3; omega
  by_cases hr2 : r = 2
  · by_cases hcenter : ∀ c, G.eccent c = G.radius → d ≤ Nat.card (G.neighborSet c)
    · apply h4 G hG hc hr2 (by omega) _ hv hdense
      simpa only [d, hr2] using hcenter
    · push Not at hcenter
      obtain ⟨c, hcR, hdeg⟩ := hcenter
      have he : Nat.card (G.neighborSet c) = (Finset.univ.filter (G.Adj c)).card := by
        rw [Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree,
          ← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter]
      apply close
      apply OMA.W133Gap.l_le_of_small_center G hG hc (show r ≤ 2 by omega) hcR (by omega)
      omega
  · exact h3 G hG hc (by omega) hrbound hd4 hv hdense

end OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1_H1_R1_H2_R1
