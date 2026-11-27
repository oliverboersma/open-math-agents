import OMAReductions.R_Erdos813_erdos_813_variants_erdos_hajnal_R1

/-! The core of this file is the proof merged in open-math-agents for
Erdos813.erdos_813.variants.lower (proofs/Erdos813.erdos_813.variants.lower.lean, pull request
4620, by @Genbox): n^(1/3 + c) ≪ h(n) with c = 1/15. It is reused unchanged apart from the name
of its final statement. The step then follows because n^(1/3) ≤ n^(1/3 + c) for n ≥ 1. -/

/-!
A neighborhood-expansion proof of the Erdős–Hajnal bound, specializing Section 2.1 of
Bučić and Sudakov, *Large independent sets from local considerations* (arXiv:2007.03667).
-/

open Finset Asymptotics
open scoped Topology

namespace E813Lower

noncomputable section
variable {V : Type*} [DecidableEq V] [Fintype V]

private def neighbors (G : SimpleGraph V) (S : Finset V) (v : V) : Finset V := by
  classical
  exact S.filter (G.Adj v)

private lemma mem_neighbors {G : SimpleGraph V} {S : Finset V} {v w : V} :
    w ∈ neighbors G S v ↔ w ∈ S ∧ G.Adj v w := by
  classical
  simp [neighbors]

private def near (G : SimpleGraph V) (S A : Finset V) : Finset V := by
  classical
  exact A.biUnion (neighbors G S)

private lemma mem_near {G : SimpleGraph V} {S A : Finset V} {w : V} :
    w ∈ near G S A ↔ w ∈ S ∧ ∃ v ∈ A, G.Adj v w := by
  classical
  simp only [near, mem_biUnion, mem_neighbors]
  aesop

private lemma max_subset (S : Finset V) (P : Finset V → Prop) (h : P ∅) :
    ∃ A ⊆ S, P A ∧ ∀ B ⊆ S, P B → B.card ≤ A.card := by
  classical
  obtain ⟨A, hA, hmax⟩ := (S.powerset.filter P).exists_max_image card
    ⟨∅, by simp [h]⟩
  rw [mem_filter, mem_powerset] at hA
  exact ⟨A, hA.1, hA.2, fun B hBS hB => hmax B (by simp [hBS, hB])⟩

private lemma indep_bound {G : SimpleGraph V} {A : Finset V}
    (h : G.IsIndepSet (A : Set V)) : A.card ≤ G.indepNum :=
  h.card_le_indepNum

private lemma indep_mono {G : SimpleGraph V} {S T : Finset V} (hST : S ⊆ T)
    (hT : G.IsIndepSet (T : Set V)) : G.IsIndepSet (S : Set V) := by
  rw [G.isIndepSet_iff] at hT ⊢
  intro a ha b hb hab
  exact hT (hST ha) (hST hb) hab

private lemma cover_bound (G : SimpleGraph V) (S : Finset V) (D : ℝ) (hD : 0 ≤ D)
    (h : ∀ v ∈ S, ((neighbors G S v).card : ℝ) ≤ D) :
    (S.card : ℝ) ≤ (G.indepNum : ℝ) * (D + 1) := by
  classical
  obtain ⟨A, hAS, hA, hmax⟩ := max_subset S (fun s => G.IsIndepSet (s : Set V)) (by simp)
  have hcover : S ⊆ A ∪ near G S A := by
    intro v hv
    by_contra hh
    have hvA : v ∉ A := fun hin => hh (mem_union_left _ hin)
    have hn : ∀ u ∈ A, ¬ G.Adj u v := by
      intro u hu hadj
      exact hh (mem_union_right _ (mem_near.mpr ⟨hv,u,hu,hadj⟩))
    have hi : G.IsIndepSet (↑(insert v A) : Set V) := by
      rw [G.isIndepSet_iff]
      intro u hu w hw huw
      simp only [coe_insert, Set.mem_insert_iff, mem_coe] at hu hw
      rcases hu with rfl | hu <;> rcases hw with rfl | hw
      · exact False.elim (huw rfl)
      · exact fun hadj => hn w hw hadj.symm
      · exact hn u hu
      · exact (G.isIndepSet_iff.mp hA) hu hw huw
    have hm := hmax _ (insert_subset hv hAS) hi
    rw [card_insert_of_notMem hvA] at hm
    omega
  have hu := card_le_card hcover
  have hc := (card_union_le A (near G S A)).trans (Nat.add_le_add_left
    (card_biUnion_le (s := A) (t := neighbors G S)) _)
  have hh : (S.card : ℝ) ≤ A.card + ∑ v ∈ A, ((neighbors G S v).card : ℝ) := by
    exact_mod_cast hu.trans hc
  calc
    _ ≤ A.card + ∑ v ∈ A, ((neighbors G S v).card : ℝ) := hh
    _ ≤ A.card + ∑ _v ∈ A, D := add_le_add le_rfl (sum_le_sum fun v hv => h v (hAS hv))
    _ = (A.card : ℝ) * (D + 1) := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast indep_bound hA) (by positivity)

private lemma card_triangle_free (G : SimpleGraph V) (S : Finset V)
    (h : ∀ v ∈ S, G.IsIndepSet ((neighbors G S v : Finset V) : Set V)) :
    (S.card : ℝ) ≤ (G.indepNum : ℝ) * (G.indepNum + 1) :=
  cover_bound G S _ (by positivity) (fun v hv => by exact_mod_cast indep_bound (h v hv))

private lemma expanding_neighbors (G : SimpleGraph V) (S : Finset V)
    (D : ℝ) (hD : 0 ≤ D) :
    ∃ T ⊆ S, (S.card : ℝ) - (G.indepNum : ℝ) * (D + 1) ≤ T.card ∧
      ∀ A ⊆ T, G.IsIndepSet (A : Set V) → D * A.card ≤ (near G T A).card := by
  classical
  obtain ⟨X, hXS, hX, hmax⟩ := max_subset S
    (fun X => G.IsIndepSet (X : Set V) ∧ (near G S X).card ≤ D * X.card)
    (by simp [near])
  let W := X ∪ near G S X
  let T := S \ W
  have hs : (S \ W).card + W.card ≥ S.card := card_le_card_sdiff_add_card
  have hw : (W.card : ℝ) ≤ (G.indepNum : ℝ) * (D + 1) := by
    have ha : (W.card : ℝ) ≤ X.card + (near G S X).card := by
      exact_mod_cast card_union_le X (near G S X)
    have hx : (X.card : ℝ) ≤ G.indepNum := by exact_mod_cast indep_bound hX.1
    nlinarith
  refine ⟨T, sdiff_subset, ?_, ?_⟩
  · have hs' : (S.card : ℝ) ≤ ((S \ W).card : ℝ) + W.card := by exact_mod_cast hs
    change _ ≤ ((S \ W).card : ℝ)
    linarith
  intro A hAT hA
  by_contra! hsmall
  have hAX : Disjoint X A := by
    apply disjoint_left.mpr
    intro x hx ha
    exact (mem_sdiff.mp (hAT ha)).2 (mem_union_left _ hx)
  have hInd : G.IsIndepSet (↑(X ∪ A) : Set V) := by
    rw [G.isIndepSet_iff]
    intro x hx y hy hxy hadj
    simp only [mem_coe, mem_union] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact (G.isIndepSet_iff.mp hX.1) hx hy hxy hadj
    · obtain ⟨hys, hyw⟩ := mem_sdiff.mp (hAT hy)
      exact hyw (mem_union_right _ (mem_near.mpr ⟨hys,x,hx,hadj⟩))
    · obtain ⟨hxs, hxw⟩ := mem_sdiff.mp (hAT hx)
      exact hxw (mem_union_right _ (mem_near.mpr ⟨hxs,y,hy,hadj.symm⟩))
    · exact (G.isIndepSet_iff.mp hA) hx hy hxy hadj
  have hnears : near G S (X ∪ A) ⊆ near G S X ∪ near G T A := by
    intro w hw
    obtain ⟨hws,v,hv,hvw⟩ := mem_near.mp hw
    by_cases hvX : v ∈ X
    · exact mem_union_left _ (mem_near.mpr ⟨hws,v,hvX,hvw⟩)
    have hvA := (mem_union.mp hv).resolve_left hvX
    by_cases hwX : w ∈ near G S X
    · exact mem_union_left _ hwX
    have hwT : w ∈ T := by
      apply mem_sdiff.mpr
      refine ⟨hws, fun h => ?_⟩
      rcases mem_union.mp h with hx | hx
      · exact (mem_sdiff.mp (hAT hvA)).2 (mem_union_right _
          (mem_near.mpr ⟨(mem_sdiff.mp (hAT hvA)).1,w,hx,hvw.symm⟩))
      · exact hwX hx
    exact mem_union_right _ (mem_near.mpr ⟨hwT,v,hvA,hvw⟩)
  have hcard : ((near G S (X ∪ A)).card : ℝ) ≤
      (near G S X).card + (near G T A).card := by
    exact_mod_cast (card_le_card hnears).trans (card_union_le _ _)
  have hSmall : ((near G S (X ∪ A)).card : ℝ) ≤ D * (X ∪ A).card := by
    rw [card_union_of_disjoint hAX, Nat.cast_add, mul_add]
    linarith [hX.2]
  have hma := hmax (X ∪ A) (union_subset hXS (hAT.trans sdiff_subset)) ⟨hInd,hSmall⟩
  rw [card_union_of_disjoint hAX] at hma
  have he : A = ∅ := card_eq_zero.mp (by omega)
  simp [he, near] at hsmall


private def LocalIndep (G : SimpleGraph V) : Prop :=
  ∀ S : Finset V, S.card = 7 →
    ∃ I ⊆ S, I.card = 3 ∧ G.IsIndepSet (I : Set V)

private lemma overlap_le_one (G : SimpleGraph V) (I K : Finset V)
    (hi : G.IsIndepSet (I : Set V)) (hk : G.IsClique (K : Set V)) :
    (I ∩ K).card ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro x hx y hy
  by_contra h
  exact (G.isIndepSet_iff.mp hi) (mem_inter.mp hx).1 (mem_inter.mp hy).1 h
    (hk (mem_inter.mp hx).2 (mem_inter.mp hy).2 h)

private lemma two_cliques (G : SimpleGraph V) (I K L : Finset V)
    (hi : G.IsIndepSet (I : Set V)) (hk : G.IsClique (K : Set V))
    (hl : G.IsClique (L : Set V)) (h : I ⊆ K ∪ L) : I.card ≤ 2 := by
  classical
  have hsub : I ⊆ (I ∩ K) ∪ (I ∩ L) := by
    intro v hv
    rcases mem_union.mp (h hv) with hh | hh
    · exact mem_union_left _ (mem_inter.mpr ⟨hv,hh⟩)
    · exact mem_union_right _ (mem_inter.mpr ⟨hv,hh⟩)
  have h' := (card_le_card hsub).trans (card_union_le _ _)
  have h1 := overlap_le_one G I K hi hk
  have h2 := overlap_le_one G I L hi hl
  omega

private lemma pair_clique (G : SimpleGraph V) {a b : V} (hab : G.Adj a b) :
    G.IsClique (↑({a,b} : Finset V) : Set V) := by
  rw [coe_insert, coe_singleton]
  exact (G.isClique_singleton b).insert (fun _ hv _ => (Set.mem_singleton_iff.mp hv) ▸ hab)

private lemma triple_clique (G : SimpleGraph V) {a b c : V}
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    G.IsNClique 3 ({a,b,c} : Finset V) := by
  constructor
  · rw [coe_insert]
    apply (pair_clique G hbc).insert
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    intro v hv _
    rcases hv with rfl | rfl <;> assumption
  · rw [card_insert_of_notMem (by simp [hab.ne, hac.ne]), card_pair hbc.ne]

private lemma quad_clique (G : SimpleGraph V) {a b c d : V}
    (hab : G.Adj a b) (hac : G.Adj a c) (had : G.Adj a d)
    (hbc : G.Adj b c) (hbd : G.Adj b d) (hcd : G.Adj c d) :
    G.IsNClique 4 ({a,b,c,d} : Finset V) := by
  have h := triple_clique G hbc hbd hcd
  constructor
  · rw [coe_insert]
    apply h.isClique.insert
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    intro v hv _
    rcases hv with rfl | rfl | rfl <;> assumption
  · rw [card_insert_of_notMem (by simp [hab.ne,hac.ne,had.ne]), h.card_eq]

private lemma common_indep (G : SimpleGraph V) (hG : G.CliqueFree 4)
    (S : Finset V) {a b : V} (hab : G.Adj a b) :
    G.IsIndepSet (neighbors G (neighbors G S a) b : Set V) := by
  classical
  rw [G.isIndepSet_iff]
  intro c hc d hd _ hcd
  obtain ⟨hc', hbc⟩ := mem_neighbors.mp (show c ∈ neighbors G (neighbors G S a) b from hc)
  obtain ⟨hd', hbd⟩ := mem_neighbors.mp (show d ∈ neighbors G (neighbors G S a) b from hd)
  exact hG _ (quad_clique G hab (mem_neighbors.mp hc').2 (mem_neighbors.mp hd').2 hbc hbd hcd)

private lemma bound_of_clique (G : SimpleGraph V) (hloc : LocalIndep G)
    {K : Finset V} (hK : G.IsNClique 4 K) :
    (Fintype.card V : ℝ) ≤ (G.indepNum : ℝ) * (G.indepNum + 1) + 4 := by
  classical
  let S : Finset V := univ \ K
  have htri : ∀ v ∈ S, G.IsIndepSet (neighbors G S v : Set V) := by
    intro v hv
    rw [G.isIndepSet_iff]
    intro a ha b hb _ hab
    obtain ⟨has,hva⟩ := mem_neighbors.mp (show a ∈ neighbors G S v from ha)
    obtain ⟨hbs,hvb⟩ := mem_neighbors.mp (show b ∈ neighbors G S v from hb)
    let L : Finset V := {v,a,b}
    have hL : G.IsNClique 3 L := triple_clique G hva hvb hab
    have hKL : Disjoint K L := disjoint_left.mpr (by
      intro x hx hx'
      simp only [L, mem_insert, mem_singleton] at hx'
      rcases hx' with rfl | rfl | rfl
      · exact (mem_sdiff.mp hv).2 hx
      · exact (mem_sdiff.mp has).2 hx
      · exact (mem_sdiff.mp hbs).2 hx)
    obtain ⟨I,hIS,hI,hi⟩ := hloc (K ∪ L) (by
      rw [card_union_of_disjoint hKL,hK.card_eq,hL.card_eq])
    have := two_cliques G I K L hi hK.isClique hL.isClique hIS
    omega
  have hs : (S.card : ℝ) + 4 = Fintype.card V := by
    exact_mod_cast (by
      simpa [S, hK.card_eq] using card_sdiff_add_card_eq_card (subset_univ K) :
      S.card + 4 = Fintype.card V)
  linarith [card_triangle_free G S htri]

private def support (t : V × V × V) : Finset V := by
  classical
  exact {t.1, t.2.1, t.2.2}

private def Good (G : SimpleGraph V) (v : V) (t : V × V × V) : Prop :=
  G.Adj v t.1 ∧ G.Adj v t.2.1 ∧ G.Adj t.1 t.2.1 ∧
    G.Adj t.1 t.2.2 ∧ G.Adj t.2.1 t.2.2 ∧ v ≠ t.2.2 ∧ ¬G.Adj v t.2.2

private lemma mem_support {t : V × V × V} {x : V} :
    x ∈ support t ↔ x = t.1 ∨ x = t.2.1 ∨ x = t.2.2 := by
  classical
  simp [support]

private lemma good_clique (G : SimpleGraph V) {v : V} {t : V × V × V}
    (h : Good G v t) : G.IsNClique 3 (support t) := by
  classical
  exact triple_clique G h.2.2.1 h.2.2.2.1 h.2.2.2.2.1

private lemma v_not_mem_support (G : SimpleGraph V) {v : V} {t : V × V × V}
    (h : Good G v t) : v ∉ support t := by
  simp only [mem_support, not_or]
  exact ⟨h.1.ne,h.2.1.ne,h.2.2.2.2.2.1⟩

private lemma good_pair (G : SimpleGraph V) (hloc : LocalIndep G) {v : V} {s t : V × V × V}
    (hs : Good G v s) (ht : Good G v t) (hst : Disjoint (support s) (support t)) :
    ¬ G.Adj s.2.2 t.2.2 := by
  classical
  intro hedge
  have hv : v ∉ support s ∪ support t := by
    simp [v_not_mem_support G hs, v_not_mem_support G ht]
  obtain ⟨I, hIS, hI, hi⟩ := hloc (insert v (support s ∪ support t)) (by
    rw [card_insert_of_notMem hv, card_union_of_disjoint hst,
      (good_clique G hs).card_eq, (good_clique G ht).card_eq])
  by_cases hvI : v ∈ I
  · have hsub : I ⊆ {v, s.2.2, t.2.2} := by
      intro x hx
      rcases mem_insert.mp (hIS hx) with rfl | hx'
      · simp
      have hne : v ≠ x := fun h => hv (h ▸ hx')
      have hnon := (G.isIndepSet_iff.mp hi) (show v ∈ (I : Set V) from hvI)
        (show x ∈ (I : Set V) from hx) hne
      rcases mem_union.mp hx' with hx | hx
      · rcases mem_support.mp hx with rfl | rfl | rfl
        · exact False.elim (hnon hs.1)
        · exact False.elim (hnon hs.2.1)
        · simp
      · rcases mem_support.mp hx with rfl | rfl | rfl
        · exact False.elim (hnon ht.1)
        · exact False.elim (hnon ht.2.1)
        · simp
    have hcover : I ⊆ ({v} : Finset V) ∪ {s.2.2,t.2.2} := by
      intro x hx
      simpa [or_left_comm, or_assoc] using hsub hx
    have := two_cliques G I ({v} : Finset V) {s.2.2,t.2.2} hi (by simp) (pair_clique G hedge) hcover
    omega
  · have hsub : I ⊆ support s ∪ support t := by
      intro x hx
      exact (mem_insert.mp (hIS hx)).resolve_left (fun h => hvI (h ▸ hx))
    have := two_cliques G I _ _ hi (good_clique G hs).isClique (good_clique G ht).isClique hsub
    omega

private lemma small_cover (G : SimpleGraph V) (hloc : LocalIndep G) (v : V) :
    ∃ W : Finset V, W.card ≤ 3 * G.indepNum ∧ ∀ t, Good G v t → ¬ Disjoint W (support t) := by
  classical
  let Pack (M : Finset (V × V × V)) := (∀ t ∈ M, Good G v t) ∧
    (M : Set (V × V × V)).Pairwise (fun s t => Disjoint (support s) (support t))
  obtain ⟨M, _, hM, hmax⟩ := max_subset univ Pack (by simp [Pack])
  let W := M.biUnion support
  have hM' : M.card ≤ G.indepNum := by
    let f : V × V × V → V := fun t => t.2.2
    have hf : (M : Set (V × V × V)).InjOn f := by
      intro s hs t ht he
      by_contra hst
      have hd := disjoint_left.mp (hM.2 hs ht hst)
      exact hd (mem_support.mpr (Or.inr (Or.inr rfl)))
        (mem_support.mpr (Or.inr (Or.inr he)))
    have hi : G.IsIndepSet (M.image f : Set V) := by
      rw [G.isIndepSet_iff]
      intro a ha b hb hab
      obtain ⟨s,hs,rfl⟩ := mem_image.mp (show a ∈ M.image f from ha)
      obtain ⟨t,ht,rfl⟩ := mem_image.mp (show b ∈ M.image f from hb)
      exact good_pair G hloc (hM.1 s hs) (hM.1 t ht) (hM.2 hs ht (ne_of_apply_ne f hab))
    rw [← card_image_of_injOn hf]
    exact indep_bound hi
  have hw : W.card ≤ 3 * G.indepNum := by
    have hW := card_biUnion_le (s := M) (t := support)
    have hsum : (∑ t ∈ M, (support t).card) = M.card * 3 := by
      rw [sum_congr rfl (g := fun _ => 3) (fun t ht => (good_clique G (hM.1 t ht)).card_eq)]
      simp
    exact hW.trans (by rw [hsum, Nat.mul_comm M.card 3]; gcongr)
  refine ⟨W,hw,fun t ht hd => ?_⟩
  have hWSub (s) (hs : s ∈ M) : support s ⊆ W :=
    fun _ h => mem_biUnion.mpr ⟨s,hs,h⟩
  have hDisj (s) (hs : s ∈ M) : Disjoint (support s) (support t) :=
    hd.mono_left (hWSub s hs)
  have htM : t ∉ M := by
    intro hh
    exact disjoint_left.mp (hDisj t hh)
      (mem_support.mpr (Or.inl rfl)) (mem_support.mpr (Or.inl rfl))
  have hnew : Pack (insert t M) := by
    refine ⟨?_, ?_⟩
    · intro s hs
      rcases mem_insert.mp hs with rfl | hs
      · exact ht
      · exact hM.1 s hs
    · intro s hs u hu hne
      change s ∈ insert t M at hs
      change u ∈ insert t M at hu
      rcases mem_insert.mp hs with he | hs'
      · subst s
        rcases mem_insert.mp hu with he | hu'
        · exact False.elim (hne he.symm)
        · exact (hDisj u hu').symm
      · rcases mem_insert.mp hu with he | hu'
        · subst u
          exact hDisj s hs'
        · exact hM.2 hs' hu' hne
  have hh := hmax _ (subset_univ _) hnew
  rw [card_insert_of_notMem htM] at hh
  omega

private lemma sum_card_neighbors (B C : Finset V) (D : V → Finset V) :
    (∑ u ∈ B, ((D u ∩ C).card : ℝ)) =
      ∑ w ∈ C, ((B.filter (fun u => w ∈ D u)).card : ℝ) := by
  classical
  have he (u : V) : D u ∩ C = C.filter (fun w => w ∈ D u) := by
    ext w
    simp [and_comm]
  simp_rw [he, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, sum_filter]
  exact sum_comm

private lemma eligible_vertices (G : SimpleGraph V) (a m : ℝ) (ha : a = (G.indepNum : ℝ) + 1)
    (hm : m = Fintype.card V) (hlarge : 100 * a ≤ m) :
    (m / 2) ≤ ((univ.filter (fun v => m / (4*a) ≤ (neighbors G univ v).card)).card : ℝ) := by
  classical
  have ha0 : 0 < a := by rw [ha]; positivity
  have hm0 : 0 ≤ m := by linarith
  let g := m / (4*a)
  have hg0 : 0 ≤ g := div_nonneg hm0 (by positivity)
  let L : Finset V := univ.filter (fun v => ((neighbors G univ v).card : ℝ) < g)
  have hDeg (u) (hu : u ∈ L) : ((neighbors G L u).card : ℝ) ≤ g := by
    apply le_trans _ ((mem_filter.mp hu).2.le)
    exact_mod_cast card_le_card (show neighbors G L u ⊆ neighbors G univ u by
      intro v hv
      exact mem_neighbors.mpr ⟨mem_univ _, (mem_neighbors.mp hv).2⟩)
  have hL := cover_bound G L g hg0 hDeg
  have heq : (univ.filter (fun v => m / (4*a) ≤ (neighbors G univ v).card) : Finset V) = univ \ L := by
    ext u
    simp [L, g, not_lt]
  rw [heq, cast_card_sdiff (subset_univ L), card_univ, ← hm]
  have hg : a * g = m / 4 := by dsimp [g]; field_simp
  have hbound : (G.indepNum : ℝ) * (g + 1) ≤ a * (g + 1) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  nlinarith

private lemma real_main (G : SimpleGraph V) (hloc : LocalIndep G) :
    (Fintype.card V : ℝ) ≤ 100 * Real.sqrt (((G.indepNum : ℝ) + 1) ^ 5) := by
  classical
  let a : ℝ := (G.indepNum : ℝ) + 1
  let m : ℝ := Fintype.card V
  change m ≤ 100 * Real.sqrt (a^5)
  by_contra! hContra
  have ha : 1 ≤ a := by dsimp [a]; linarith [show 0 ≤ (G.indepNum : ℝ) by positivity]
  have ha0 : 0 < a := by linarith
  have ha2 : a ≤ a^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr ha) ha0.le]
  have hAsqrt : a^2 ≤ Real.sqrt (a^5) := by
    have hS : (Real.sqrt (a^5))^2 = a^5 := Real.sq_sqrt (by positivity)
    apply le_of_not_gt
    intro h
    have hs := pow_lt_pow_left₀ h (Real.sqrt_nonneg _) (n := 2) (by decide)
    have hp : (a^2)^2 ≤ a^5 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ha) (show 0 ≤ a^4 by positivity)]
    linarith
  have hM : 100*a^2 < m := by linarith
  have hm : 100*a ≤ m := by linarith
  have hM2 : 10000*a^5 < m^2 := by
    have hs := pow_lt_pow_left₀ hContra (show 0 ≤ 100 * Real.sqrt (a^5) by positivity) (n := 2) (by decide)
    rw [mul_pow, Real.sq_sqrt (by positivity)] at hs
    norm_num at hs
    exact hs
  have hm0 : 0 < m := by linarith
  by_cases hbad : ¬ G.CliqueFree 4
  · simp only [SimpleGraph.CliqueFree, not_forall, not_not] at hbad
    obtain ⟨K,hK⟩ := hbad
    have h := bound_of_clique G hloc hK
    change m ≤ (G.indepNum : ℝ) * a + 4 at h
    have he : (G.indepNum : ℝ) = a - 1 := by dsimp [a]; ring
    rw [he] at h
    nlinarith
  have hG : G.CliqueFree 4 := not_not.mp hbad
  let N (u : V) := neighbors G univ u
  let g := m / (4*a)
  let d := m / (16*a^2)
  have hg0 : 0 ≤ g := by positivity
  have hd0 : 0 < d := by positivity
  have hgd : g = 4 * a * d := by
    dsimp [g,d]
    field_simp
    ring
  have hgL : 25*a ≤ g := by
    apply (le_div_iff₀ (by positivity : 0 < 4*a)).mpr
    linarith
  have htrim : (G.indepNum : ℝ) * (d + 1) ≤ g / 2 := by
    have h₁ : (G.indepNum : ℝ) * (d + 1) ≤ a * (d + 1) :=
      mul_le_mul_of_nonneg_right (by dsimp [a]; linarith) (by positivity)
    linarith
  -- Prune each neighborhood while keeping enough incoming incidences.
  choose T hTN hTcard hTexp using fun u : V => expanding_neighbors G (N u) d hd0.le
  let H := univ.filter (fun u => g ≤ (N u).card)
  have hH : m / 2 ≤ (H.card : ℝ) := eligible_vertices G a m rfl rfl hm
  have hTA (u) (hu : u ∈ H) : g / 2 ≤ ((T u).card : ℝ) := by
    have h := (mem_filter.mp hu).2
    linarith [hTcard u]
  let B (v : V) := H.filter (fun u => v ∈ T u)
  have hsum : (m / 2) * (g / 2) ≤ ∑ v : V, ((B v).card : ℝ) := by
    calc
      _ ≤ (H.card : ℝ) * (g / 2) := mul_le_mul_of_nonneg_right hH (by positivity)
      _ = ∑ u ∈ H, g / 2 := by simp
      _ ≤ ∑ u ∈ H, ((T u).card : ℝ) := sum_le_sum hTA
      _ = _ := by simpa [B] using sum_card_neighbors H univ T
  obtain ⟨v,hv⟩ : ∃ v : V, g / 4 ≤ ((B v).card : ℝ) := by
    by_contra! h
    have hn : (univ : Finset V).Nonempty := card_pos.mp (by
      rw [card_univ]
      exact_mod_cast (show (0 : ℝ) < (Fintype.card V : ℝ) from hm0))
    have h' := sum_lt_sum_of_nonempty hn (fun v _ => h v)
    rw [sum_const, nsmul_eq_mul, card_univ, ← show m = Fintype.card V from rfl] at h'
    linarith
  have hvB (u : V) (hu : u ∈ B v) : v ∈ T u := (mem_filter.mp hu).2
  obtain ⟨W,hW,hcovers⟩ := small_cover G hloc v
  let D (u : V) := neighbors G (T u) v
  have hDind (u) (hu : u ∈ B v) : G.IsIndepSet (D u : Set V) := by
    have huv := (mem_neighbors.mp (hTN u (hvB u hu))).2
    have hsub : D u ⊆ neighbors G (N u) v := by
      intro x hx
      obtain ⟨hx', hadj⟩ := mem_neighbors.mp hx
      exact mem_neighbors.mpr ⟨hTN u hx',hadj⟩
    exact indep_mono hsub (common_indep G hG univ huv)
  have hDcard (u) (hu : u ∈ B v) : d ≤ ((D u).card : ℝ) := by
    have h := hTexp u {v} (singleton_subset_iff.mpr (hvB u hu)) (by simp)
    simpa [D, near] using h
  let C := B v \ W
  have hCSub : C ⊆ B v := sdiff_subset
  have hWC : (W.card : ℝ) ≤ 3 * (G.indepNum : ℝ) := by exact_mod_cast hW
  have hC (u) (hu : u ∈ C) : u ∉ W := (mem_sdiff.mp hu).2
  have hc : (g / 8) ≤ (C.card : ℝ) := by
    have hb : ((B v).card : ℝ) ≤ C.card + W.card := by
      exact_mod_cast (card_le_card_sdiff_add_card (s := B v) (t := W))
    have hr : (G.indepNum : ℝ) ≤ a := by dsimp [a]; linarith
    linarith
  have hfib (w : V) :
      ((C.filter (fun u => w ∈ D u)).card : ℝ) ≤ (G.indepNum : ℝ) := by
    by_cases hw : G.Adj v w
    · have hh : ((neighbors G (neighbors G univ v) w).card : ℝ) ≤ G.indepNum := by
        exact_mod_cast indep_bound (common_indep G hG univ hw)
      apply le_trans _ hh
      exact_mod_cast card_le_card (show C.filter (fun u => w ∈ D u) ⊆
          neighbors G (neighbors G univ v) w by
        intro u hu
        obtain ⟨hu,hw'⟩ := mem_filter.mp hu
        have h₁ := (mem_neighbors.mp (hTN u (hvB u (hCSub hu)))).2.symm
        have h₂ := (mem_neighbors.mp (hTN u (mem_neighbors.mp hw').1)).2.symm
        exact mem_neighbors.mpr ⟨mem_neighbors.mpr ⟨mem_univ _,h₁⟩,h₂⟩)
    · have hz : C.filter (fun u => w ∈ D u) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro u hu
        exact hw (mem_neighbors.mp (mem_filter.mp hu).2).2
      simp [hz]
  -- Each covered vertex blocks at most one independent fiber of incidences.
  have hblocked : ∑ u ∈ C, ((D u ∩ W).card : ℝ) ≤ W.card * (G.indepNum : ℝ) := by
    rw [sum_card_neighbors C W D]
    calc
      _ ≤ ∑ _w ∈ W, (G.indepNum : ℝ) := sum_le_sum fun w _ => hfib w
      _ = _ := by simp
  have hr : (G.indepNum : ℝ) ≤ a := by dsimp [a]; linarith
  have hBnd : (W.card : ℝ) * (G.indepNum : ℝ) ≤ 3 * a^2 := by
    calc
      _ ≤ (3 * a) * a := mul_le_mul (by linarith) hr (by positivity) (by positivity)
      _ = _ := by ring
  have hgd' : g / 8 * (d / 2) = m^2 / (1024 * a^3) := by
    dsimp [g,d]
    field_simp
    ring
  have hmany : 3 * a^2 < (C.card : ℝ) * (d / 2) := by
    apply lt_of_lt_of_le _ (mul_le_mul_of_nonneg_right hc (by positivity))
    rw [hgd', lt_div_iff₀ (by positivity)]
    nlinarith
  obtain ⟨u,hu,hBig⟩ : ∃ u ∈ C, d / 2 ≤ ((D u \ W).card : ℝ) := by
    by_contra! h
    have he (u : V) : ((D u).card : ℝ) = ((D u \ W).card : ℝ) + (D u ∩ W).card := by
      exact_mod_cast (card_sdiff_add_card_inter (D u) W).symm
    have hEach (u) (hu : u ∈ C) : d / 2 ≤ ((D u ∩ W).card : ℝ) := by
      linarith [he u,h u hu,hDcard u (hCSub hu)]
    have hh := sum_le_sum hEach
    rw [sum_const, nsmul_eq_mul] at hh
    exact (not_lt_of_ge ((hh.trans hblocked).trans hBnd)) hmany
  let A := D u \ W
  have huB : u ∈ B v := hCSub hu
  have hAS : A ⊆ T u := by
    intro w hw
    exact (mem_neighbors.mp (mem_sdiff.mp hw).1).1
  have hi : G.IsIndepSet (A : Set V) :=
    indep_mono (sdiff_subset : A ⊆ D u) (hDind u huB)
  have hExpand := hTexp u A hAS hi
  have hD2 : d * (d / 2) = m^2 / (512 * a^4) := by
    dsimp [d]
    field_simp
    ring
  have hWv : ((insert v W).card : ℝ) ≤ 3 * a + 1 := by
    have hcard : ((insert v W).card : ℝ) ≤ W.card + 1 := by exact_mod_cast card_insert_le v W
    linarith
  have hMore : ((insert v W).card : ℝ) < ((near G (T u) A).card : ℝ) := by
    apply lt_of_le_of_lt hWv
    apply lt_of_lt_of_le _ ((mul_le_mul_of_nonneg_left hBig hd0.le).trans hExpand)
    rw [hD2, lt_div_iff₀ (by positivity)]
    have hA5 : a^4 ≤ a^5 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ha) (show 0 ≤ a^4 by positivity)]
    nlinarith
  obtain ⟨z,hz,hzn⟩ := exists_mem_notMem_of_card_lt_card (show
    (insert v W).card < (near G (T u) A).card by exact_mod_cast hMore)
  obtain ⟨hzT,x,hx,hxz⟩ := mem_near.mp hz
  have hxD := (mem_sdiff.mp hx).1
  have hvx := (mem_neighbors.mp hxD).2
  have hux := (mem_neighbors.mp (hTN u (mem_neighbors.mp hxD).1)).2
  have huz := (mem_neighbors.mp (hTN u hzT)).2
  have hvu := (mem_neighbors.mp (hTN u (hvB u huB))).2.symm
  have hnot : ¬ G.Adj v z := fun h =>
    hG _ (quad_clique G hvu hvx h hux huz hxz)
  let t : V × V × V := (u,x,z)
  have ht : Good G v t := ⟨hvu,hvx,hux,huz,hxz,
    fun h => hzn (mem_insert.mpr (Or.inl h.symm)),hnot⟩
  apply hcovers t ht
  apply disjoint_left.mpr
  intro w hw hs
  rcases mem_support.mp hs with he | he | he
  · change w = u at he
    rw [he] at hw
    exact hC u hu hw
  · change w = x at he
    rw [he] at hw
    exact (mem_sdiff.mp hx).2 hw
  · change w = z at he
    rw [he] at hw
    exact hzn (mem_insert.mpr (Or.inr hw))

private lemma estimate (n : ℕ) :
    (n : ℝ) ≤ 100 * Real.sqrt (((Erdos813.h n : ℝ) + 1)^5) := by
  classical
  let S : Set ℕ := {k | ∃ G : SimpleGraph (Fin n), Erdos813.EverySevenHasTriangle G ∧
    G.cliqueNum = k}
  have hS : S.Nonempty := ⟨(⊤ : SimpleGraph (Fin n)).cliqueNum,
    ⟨⊤, Erdos813.everySevenHasTriangle_top n, rfl⟩⟩
  obtain ⟨G,hG,hk⟩ : ∃ G : SimpleGraph (Fin n), Erdos813.EverySevenHasTriangle G ∧
      G.cliqueNum = Erdos813.h n := Nat.sInf_mem hS
  have hloc : LocalIndep Gᶜ := by
    intro A hA
    obtain ⟨I,hI,hc⟩ := hG A hA
    exact ⟨I,hI,hc.card_eq,by simpa using hc.isClique⟩
  simpa [hk] using real_main Gᶜ hloc

end

end E813Lower

/-- The weak lower bound follows from the (2/5) exponent of Bučić and Sudakov. -/
theorem E813Lower.lowerCore : ∃ c₁ > (0 : ℝ),
    (fun n : ℕ ↦ (n : ℝ) ^ (1 / 3 + c₁ : ℝ)) =O[Filter.atTop] (fun n ↦ (Erdos813.h n : ℝ)) := by
  refine ⟨1/15, by norm_num, ?_⟩
  rw [show (1:ℝ)/3 + 1/15 = 2/5 by norm_num]
  refine Asymptotics.IsBigO.of_bound (2 * (100:ℝ)^(2/5:ℝ)) ?_
  filter_upwards [Filter.eventually_ge_atTop (101:ℕ)] with n hn
  have hb := E813Lower.estimate n
  let a : ℝ := (Erdos813.h n : ℝ) + 1
  have hA : 0 ≤ a := by dsimp [a]; positivity
  have hH : (1:ℝ) ≤ Erdos813.h n := by
    by_contra! h
    have hn0 : Erdos813.h n < 1 := by exact_mod_cast h
    have hz : Erdos813.h n = 0 := by omega
    have hn' : (101:ℝ) ≤ n := by exact_mod_cast hn
    norm_num [hz] at hb
    linarith
  have hPow : (n:ℝ) ^ (2/5:ℝ) ≤ (100:ℝ)^(2/5:ℝ) * a := by
    have hh := Real.rpow_le_rpow (by positivity : 0 ≤ (n:ℝ)) hb (by norm_num : 0 ≤ (2/5:ℝ))
    change _ ≤ (100 * Real.sqrt (a^5)) ^ (2/5:ℝ) at hh
    rw [Real.mul_rpow (by norm_num) (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
      ← Real.rpow_mul (by positivity : 0 ≤ a ^ (5:ℕ)),
      ← Real.rpow_natCast_mul hA] at hh
    norm_num at hh
    simpa using hh
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (n:ℝ)^(2/5:ℝ)),
    abs_of_nonneg (by positivity : 0 ≤ (Erdos813.h n:ℝ))]
  calc
    _ ≤ (100:ℝ)^(2/5:ℝ) * a := hPow
    _ ≤ (100:ℝ)^(2/5:ℝ) * (2 * (Erdos813.h n : ℝ)) :=
      mul_le_mul_of_nonneg_left (by dsimp [a]; linarith) (by positivity)
    _ = _ := by ring

theorem OMA.solution : OMA.R_Erdos813_erdos_813_variants_erdos_hajnal_R1.H2 := by
  obtain ⟨c, hc, h⟩ := E813Lower.lowerCore
  refine Asymptotics.IsBigO.trans ?_ h
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
