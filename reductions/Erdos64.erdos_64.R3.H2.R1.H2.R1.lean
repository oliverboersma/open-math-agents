import OMAReductions.R_Erdos64_erdos_64_R3_H2_R1

/-!
# Sparsifying the marked-edge problem

Starting with the marked-edge problem from @Hennyrick's reduction, keep the same
vertices and marked edge while preserving two-connectivity and all degree thresholds.
Every induced subgraph of the resulting graph has a vertex of degree at most three.
In a subgraph of minimum degree four, a longest path has four neighbours of its
first vertex on the path. Either interior spoke is removable: the earlier and later
spokes give two bypasses with disjoint interiors, so deleting any one vertex cannot
make the chord essential. One interior spoke differs from the marked edge.
Iterate by strictly decreasing the number of edges.

The two remaining cases separate graphs that peel completely at degree two from
those with a nonempty induced subgraph of minimum degree three.
-/

namespace OMA.R_Erdos64_erdos_64_R3_H2_R1_H2_R1

open SimpleGraph
open scoped Classical

def H1 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (a b : V),
    G.Adj b a → (∀ x, 2 ≤ G.degree x) → (∀ x, x ≠ a → x ≠ b → 3 ≤ G.degree x) →
    (∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, (G).Adj x y) →
    (∀ S : Finset V, S.Nonempty → ∃ x ∈ S, (S.filter (fun y => (G).Adj x y)).card ≤ 2) →
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧
      (c.length = 2^k ∨ (c.length + 1 = 2^k ∧ s(b,a) ∈ c.edges))

def H2 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (a b : V),
    G.Adj b a → (∀ x, 2 ≤ G.degree x) → (∀ x, x ≠ a → x ≠ b → 3 ≤ G.degree x) →
    (∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, (G).Adj x y) →
    (∀ S : Finset V, S.Nonempty → ∃ x ∈ S, (S.filter (fun y => (G).Adj x y)).card ≤ 3) →
    (∃ S : Finset V, S.Nonempty ∧ ∀ x ∈ S, 3 ≤ (S.filter (G.Adj x)).card) →
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧
      (c.length = 2^k ∨ (c.length + 1 = 2^k ∧ s(b,a) ∈ c.edges))

variable {V : Type} [Fintype V]

private lemma interval_same (f : ℕ → V) (P : V → Prop) (i j : ℕ) (h : i ≤ j)
    (same : ∀ t, i ≤ t → t < j → (P (f t) ↔ P (f (t+1)))) : P (f i) ↔ P (f j) := by
  induction j, h using Nat.le_induction with
  | base => rfl
  | succ j h ih =>
    exact (ih (fun t ht hj => same t ht (by omega))).trans (same j h (by omega))

private lemma chord_safe (G : SimpleGraph V) (cuts : (∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, (G).Adj x y)) (f : ℕ → V) (l m r : ℕ)
    (hl : 0 < l) (lm : l < m) (mr : m < r)
    (inj : ∀ i ≤ r, ∀ j ≤ r, f i = f j → i = j)
    (path : ∀ i < r, G.Adj (f i) (f (i+1)))
    (left : G.Adj (f 0) (f l)) (right : G.Adj (f 0) (f r)) :
    (∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, (G.deleteEdges {s(f 0,f m)}).Adj x y) := by
  classical
  let D := G.deleteEdges {s(f 0,f m)}
  intro z S hz hex hout
  by_contra! miss
  have eqside (x y : V) (hx : x ≠ z) (hy : y ≠ z) (e : D.Adj x y) : x ∈ S ↔ y ∈ S := by
    constructor
    · intro h; by_contra h'; exact miss x h hx y h' e
    · intro h; by_contra h'; exact miss y h hy x h' e.symm
  obtain ⟨x,hx,hxz,y,hy,edge⟩ := cuts z S hz hex hout
  have hmark : s(x,y) = s(f 0,f m) := by
    by_contra hn
    exact miss x hx hxz y hy (SimpleGraph.deleteEdges_adj.mpr ⟨edge,by simpa using hn⟩)
  have hyz : y ≠ z := fun e => hy (e ▸ hz)
  have ends : f 0 ≠ z ∧ f m ≠ z ∧ ¬(f 0 ∈ S ↔ f m ∈ S) := by
    rw [Sym2.eq,Sym2.rel_iff'] at hmark
    rcases hmark with ⟨h,h'⟩ | ⟨h,h'⟩ <;> grind
  have adjD (i j : ℕ) (hi : i ≤ r) (hj : j ≤ r) (avoid : ¬((i=0 ∧ j=m) ∨ (i=m ∧ j=0)))
      (e : G.Adj (f i) (f j)) : D.Adj (f i) (f j) := by
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨e,?_⟩
    simp only [Set.mem_singleton_iff,Sym2.eq,Sym2.rel_iff',Prod.mk.injEq,Prod.swap_prod_mk]
    intro h
    apply avoid
    rcases h with ⟨h,h'⟩ | ⟨h,h'⟩
    · exact Or.inl ⟨inj _ hi _ (by omega) h,inj _ hj _ (by omega) h'⟩
    · exact Or.inr ⟨inj _ hi _ (by omega) h,inj _ hj _ (by omega) h'⟩
  have step (i) (pos : 0 < i) (lim : i < r) : D.Adj (f i) (f (i+1)) :=
    adjD _ _ (by omega) (by omega) (by omega) (path i lim)
  apply ends.2.2
  by_cases first : ∀ i, l ≤ i → i ≤ m → f i ≠ z
  · apply (eqside _ _ ends.1 (first l le_rfl lm.le)
      (adjD 0 l (by omega) (by omega) (by omega) left)).trans
    exact interval_same f (· ∈ S) l m lm.le (fun t ht hm =>
      eqside _ _ (first _ ht (by omega)) (first _ (by omega) (by omega)) (step t (by omega) (by omega)))
  · push Not at first
    obtain ⟨i,hi,him,hz'⟩ := first
    have last (j) (hj : m ≤ j) (hjr : j ≤ r) : f j ≠ z := by
      intro e
      have := inj i (by omega) j hjr (hz'.trans e.symm)
      have : i = m := by omega
      exact ends.2.1 (this ▸ hz')
    apply (eqside _ _ ends.1 (last r mr.le le_rfl)
      (adjD 0 r (by omega) le_rfl (by omega) right)).trans
    exact (interval_same f (· ∈ S) m r mr.le (fun t ht hm =>
      eqside _ _ (last _ ht (by omega)) (last _ (by omega) (by omega)) (step t (by omega) hm))).symm

private lemma removable (G : SimpleGraph V) (cuts : (∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, (G).Adj x y))
    (bad : ¬ (∀ S : Finset V, S.Nonempty → ∃ x ∈ S, (S.filter (fun y => (G).Adj x y)).card ≤ 3)) (mark : Sym2 V) :
    ∃ u w, G.Adj u w ∧ 4 ≤ G.degree u ∧ 4 ≤ G.degree w ∧
      s(u,w) ≠ mark ∧ (∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, (G.deleteEdges {s(u,w)}).Adj x y) := by
  classical
  push Not at bad
  obtain ⟨S,Sne,high⟩ := bad
  have highS (x) (hx : x ∈ S) : 4 ≤ (S.filter (G.Adj x)).card := by
    exact high x hx
  haveI : Nonempty S := ⟨⟨Sne.choose,Sne.choose_spec⟩⟩
  let H := G.induce (S : Set V)
  obtain ⟨u,v,p,hp,longest⟩ := Walk.exists_isPath_forall_isPath_length_le_length H
  let f := fun i => (p.getVert i).val
  have inj (i) (hi : i ≤ p.length) (j) (hj : j ≤ p.length) (e : f i = f j) : i = j :=
    hp.getVert_injOn hi hj (Subtype.ext e)
  have high' (x : S) : 4 ≤ G.degree x.val := by
    have inc : S.filter (G.Adj x.val) ⊆ G.neighborFinset x.val :=
      fun y hy => (G.mem_neighborFinset _ _).mpr (Finset.mem_filter.mp hy).2
    exact (highS _ x.property).trans (Finset.card_le_card inc)
  let I := (Finset.Icc 1 p.length).filter (fun i => G.Adj (f 0) (f i))
  have positions (y) (hy : y ∈ S.filter (G.Adj u.val)) :
      ∃ i ∈ I, f i = y := by
    obtain ⟨ys,uy⟩ := Finset.mem_filter.mp hy
    let w : S := ⟨y,ys⟩
    have ew : H.Adj u w := uy
    have inpath : w ∈ p.support := by
      by_contra hn
      have h := longest w v (.cons ew.symm p) (hp.cons hn)
      simp at h <;> omega
    obtain ⟨i,hi,hiw⟩ := List.mem_iff_getElem.mp inpath
    have il : i ≤ p.length := by rw [p.length_support] at hi; omega
    have hit : p.getVert i = w := (p.getVert_eq_support_getElem il).trans hiw
    have ip : 0 < i := by
      by_contra! h
      have : i = 0 := by omega
      rw [this] at hit
      simp only [Walk.getVert_zero] at hit
      exact ew.ne hit
    refine ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ip,il⟩,?_⟩,congrArg Subtype.val hit⟩
    simpa [f,hit] using uy
  have icard : 4 ≤ I.card := by
    have hsub : S.filter (G.Adj u.val) ⊆ I.image f := fun y hy =>
      Finset.mem_image.mpr (positions _ hy)
    exact (highS _ u.property).trans ((Finset.card_le_card hsub).trans Finset.card_image_le)
  let atI (j : Fin 4) := I.orderEmbOfFin rfl ⟨j.val,lt_of_lt_of_le j.isLt icard⟩
  have atmem (j : Fin 4) : atI j ∈ I := I.orderEmbOfFin_mem rfl _
  have mono : StrictMono atI := fun i j hij => (I.orderEmbOfFin rfl).strictMono hij
  have bounds (j : Fin 4) := Finset.mem_Icc.mp (Finset.mem_filter.mp (atmem j)).1
  have spokes (j : Fin 4) := (Finset.mem_filter.mp (atmem j)).2
  have diff : s(f 0,f (atI 1)) ≠ s(f 0,f (atI 2)) := by
    intro he
    have hv : f (atI 1) = f (atI 2) := by
      simp only [Sym2.eq,Sym2.rel_iff',Prod.mk.injEq,Prod.swap_prod_mk] at he
      grind
    have hn := inj _ (bounds 1).2 _ (bounds 2).2 hv
    exact (mono (show (1 : Fin 4) < 2 by decide)).ne hn
  obtain ⟨j,jlo,jhi,jne⟩ : ∃ j : Fin 4, 0 < j ∧ j < 3 ∧ s(f 0,f (atI j)) ≠ mark := by
    by_cases e : s(f 0,f (atI 1)) = mark
    · exact ⟨2,by decide,by decide,fun h => diff (e.trans h.symm)⟩
    · exact ⟨1,by decide,by decide,e⟩
  refine ⟨f 0,f (atI j),spokes j,high' _,high' _,jne,?_⟩
  apply chord_safe G cuts f (atI 0) (atI j) (atI 3) (bounds 0).1 (mono jlo) (mono jhi)
  · intro i hi j hj
    exact inj _ (hi.trans (bounds 3).2) _ (hj.trans (bounds 3).2)
  · intro i hi
    exact p.adj_getVert_succ (hi.trans_le (bounds 3).2)
  · exact spokes 0
  · exact spokes 3

private lemma delete_degrees (G : SimpleGraph V) (u w : V)
    (uw : G.Adj u w) (du : 4 ≤ G.degree u) (dw : 4 ≤ G.degree w) (x : V) :
    min 3 (G.degree x) ≤ (G.deleteEdges {s(u,w)}).degree x := by
  classical
  let D := G.deleteEdges {s(u,w)}
  have atEnd (a b : V) (e : s(a,b) = s(u,w)) (hab : G.Adj a b) (hi : 4 ≤ G.degree a) :
      3 ≤ D.degree a := by
    have nsub : (G.neighborFinset a).erase b ⊆ D.neighborFinset a := by
      intro y hy
      obtain ⟨hne,hy⟩ := Finset.mem_erase.mp hy
      apply (D.mem_neighborFinset _ _).mpr
      refine SimpleGraph.deleteEdges_adj.mpr ⟨(G.mem_neighborFinset _ _).mp hy,?_⟩
      simp [← e,hne,hab.ne]
    have := Finset.card_le_card nsub
    have := Finset.card_erase_add_one ((G.mem_neighborFinset _ _).mpr hab)
    change 3 ≤ (D.neighborFinset a).card
    change 4 ≤ (G.neighborFinset a).card at hi
    omega
  by_cases xu : x = u
  · subst x; exact (min_le_left _ _).trans (atEnd u w rfl uw du)
  by_cases xw : x = w
  · subst x; exact (min_le_left _ _).trans (atEnd w u Sym2.eq_swap uw.symm dw)
  apply (min_le_right _ _).trans
  apply Finset.card_le_card
  intro y hy
  refine (D.mem_neighborFinset _ _).mpr (SimpleGraph.deleteEdges_adj.mpr ⟨(G.mem_neighborFinset _ _).mp hy,?_⟩)
  simp only [Set.mem_singleton_iff,Sym2.eq,Sym2.rel_iff',Prod.mk.injEq,Prod.swap_prod_mk]
  tauto

private lemma thin (G : SimpleGraph V) (a b : V) (ab : G.Adj b a)
    (cuts : (∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, (G).Adj x y)) :
    ∃ T : SimpleGraph V, T ≤ G ∧ T.Adj b a ∧ (∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, (T).Adj x y) ∧
      (∀ S : Finset V, S.Nonempty → ∃ x ∈ S, (S.filter (fun y => (T).Adj x y)).card ≤ 3) ∧ ∀ x : V, min 3 (G.degree x) ≤ T.degree x := by
  classical
  by_cases h : (∀ S : Finset V, S.Nonempty → ∃ x ∈ S, (S.filter (fun y => (G).Adj x y)).card ≤ 3)
  · exact ⟨G,le_rfl,ab,cuts,h,fun x => min_le_right _ _⟩
  obtain ⟨u,w,uw,du,dw,ne,keep⟩ := removable G cuts h s(b,a)
  let D := G.deleteEdges {s(u,w)}
  have inc : D ≤ G := fun _ _ h => (SimpleGraph.deleteEdges_adj.mp h).1
  have da : D.Adj b a := SimpleGraph.deleteEdges_adj.mpr ⟨ab,by simpa using ne.symm⟩
  have smaller : D.edgeFinset.card < G.edgeFinset.card := by
    have hset : D.edgeFinset = G.edgeFinset.erase s(u,w) := by
      ext e
      simp [D,SimpleGraph.mem_edgeFinset,SimpleGraph.edgeSet_deleteEdges, and_comm]
    rw [hset]
    exact Finset.card_erase_lt_of_mem (G.mem_edgeFinset.mpr uw)
  obtain ⟨T,sub,adj,cut,sparse,deg⟩ := thin D a b da keep
  refine ⟨T,sub.trans inc,adj,cut,sparse,?_⟩
  intro x
  apply LE.le.trans _ (deg x)
  apply le_min (min_le_left _ _)
  convert delete_degrees G u w uw du dw x using 1 <;> congr 1 <;> apply Subsingleton.elim
termination_by G.edgeFinset.card
decreasing_by convert smaller using 1 <;> congr 3 <;> apply Subsingleton.elim

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R3_H2_R1.H2 := by
  intro low core V G fin dec a b ab small other cuts
  classical
  have idec : dec = fun x y => Classical.propDecidable (G.Adj x y) := Subsingleton.elim _ _
  subst dec
  obtain ⟨T,inc,edge,keep,degenerate,degree⟩ := thin G a b ab cuts
  have lo (x : V) : 2 ≤ T.degree x := (le_min (by decide) (small x)).trans (degree x)
  have hi (x : V) (xa : x ≠ a) (xb : x ≠ b) : 3 ≤ T.degree x :=
    (le_min le_rfl (other x xa xb)).trans (degree x)
  have result : ∃ (k : ℕ) (v : V) (c : T.Walk v v), 2 ≤ k ∧ c.IsCycle ∧
      (c.length = 2^k ∨ (c.length + 1 = 2^k ∧ s(b,a) ∈ c.edges)) := by
    by_cases two : (∀ S : Finset V, S.Nonempty → ∃ x ∈ S, (S.filter (fun y => (T).Adj x y)).card ≤ 2)
    · exact low V T a b edge lo hi keep two
    · push Not at two
      exact core V T a b edge lo hi keep degenerate two
  obtain ⟨k,v,c,hk,hc,hlen⟩ := result
  refine ⟨k,v,c.mapLe inc,hk,hc.mapLe inc,?_⟩
  simpa only [Walk.length_mapLe,Walk.edges_mapLe_eq_edges] using hlen

end OMA.R_Erdos64_erdos_64_R3_H2_R1_H2_R1
