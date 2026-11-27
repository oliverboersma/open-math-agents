import FormalConjectures.WrittenOnTheWallII.GraphConjecture372

open SimpleGraph

namespace W372

variable {α : Type*} [Fintype α] [DecidableEq α] {T : SimpleGraph α}

/-- `y` has at most two neighbours. -/
def NB2 (T : SimpleGraph α) (y : α) : Prop :=
  ∀ a b c, T.Adj y a → T.Adj y b → T.Adj y c → a = b ∨ a = c ∨ b = c

lemma vc_le (C : Finset α) (hC : T.IsVertexCover (C : Set α)) :
    T.vertexCoverNum.toNat ≤ C.card := by
  have h := hC.vertexCoverNum_le
  rw [Set.encard_coe_eq_coe_finsetCard] at h
  exact ENat.toNat_le_of_le_natCast h

/-- Injection lemma: a vertex cover `X` all of whose non-`D` vertices have a
`D`-neighbour outside `X` of degree at most two is no larger than `D`. -/
lemma card_le_of_inj (D X : Finset α) (hD : T.IsTotalDominating (D : Set α))
    (hX : ∀ x ∈ X, x ∉ D → ∃ y, y ∈ D ∧ y ∉ X ∧ T.Adj x y ∧ NB2 T y) :
    X.card ≤ D.card := by
  classical
  let ψ : α → α := fun x =>
    if h : x ∈ X ∧ x ∉ D then Classical.choose (hX x h.1 h.2) else x
  have hψ1 : ∀ x, x ∈ X → x ∉ D →
      ψ x ∈ D ∧ ψ x ∉ X ∧ T.Adj x (ψ x) ∧ NB2 T (ψ x) := by
    intro x hx hxD
    have h : x ∈ X ∧ x ∉ D := ⟨hx, hxD⟩
    simp only [ψ, dif_pos h]
    exact Classical.choose_spec (hX x hx hxD)
  have hψ2 : ∀ x, x ∈ D → ψ x = x := by
    intro x hxD
    have h : ¬ (x ∈ X ∧ x ∉ D) := fun h => h.2 hxD
    simp only [ψ, dif_neg h]
  apply Finset.card_le_card_of_injOn ψ
  · intro x hx
    by_cases hxD : x ∈ D
    · rw [hψ2 x hxD]; exact hxD
    · exact (hψ1 x hx hxD).1
  · intro x1 hx1 x2 hx2 heq
    have hx1 : x1 ∈ X := hx1
    have hx2 : x2 ∈ X := hx2
    by_cases h1 : x1 ∈ D <;> by_cases h2 : x2 ∈ D
    · rwa [hψ2 x1 h1, hψ2 x2 h2] at heq
    · exfalso
      have := (hψ1 x2 hx2 h2).2.1
      rw [← heq, hψ2 x1 h1] at this
      exact this hx1
    · exfalso
      have := (hψ1 x1 hx1 h1).2.1
      rw [heq, hψ2 x2 h2] at this
      exact this hx2
    · obtain ⟨hyD, -, hadj1, hnb⟩ := hψ1 x1 hx1 h1
      obtain ⟨-, -, hadj2, -⟩ := hψ1 x2 hx2 h2
      rw [← heq] at hadj2
      obtain ⟨z, hzD, hz⟩ := hD (ψ x1)
      rcases hnb x1 x2 z hadj1.symm hadj2.symm hz with h | h | h
      · exact h
      · exact absurd (h ▸ hzD) h1
      · exact absurd (h ▸ hzD) h2

lemma vc_two (hT : T.IsTree) (D : Finset α) (hD : T.IsTotalDominating (D : Set α)) :
    T.vertexCoverNum.toNat ≤ 2 * D.card := by
  classical
  have hf : ∀ v, ∃ d, d ∈ D ∧ T.Adj v d := fun v => by
    obtain ⟨d, hd, h⟩ := hD v
    exact ⟨d, hd, h⟩
  let f : α → α := fun v => Classical.choose (hf v)
  have hfD : ∀ v, f v ∈ D := fun v => (Classical.choose_spec (hf v)).1
  have hfA : ∀ v, T.Adj v (f v) := fun v => (Classical.choose_spec (hf v)).2
  let O := Dᶜ
  let EOO := T.edgeFinset.filter (fun e => ∀ v ∈ e, v ∉ D)
  let EDO := O.image (fun v => s(v, f v))
  have hsub : EOO ∪ EDO ⊆ T.edgeFinset := by
    intro e he
    rcases Finset.mem_union.mp he with h | h
    · exact (Finset.mem_filter.mp h).1
    · obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp h
      exact (mem_edgeFinset).mpr (hfA v)
  have hdisj : Disjoint EOO EDO := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp h2
    exact (Finset.mem_filter.mp h1).2 (f v) (Sym2.mem_mk_right _ _) (hfD v)
  have hEDO : EDO.card = O.card := by
    apply Finset.card_image_of_injOn
    intro v hv v' hv' h
    have hv : v ∉ D := Finset.mem_compl.mp hv
    rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd (h1 ▸ hfD v') hv
  have hO : O.card + D.card = Fintype.card α := by
    rw [Finset.card_compl]
    have := Finset.card_le_univ D
    omega
  have hE := hT.card_edgeFinset
  have hcount : EOO.card + O.card ≤ T.edgeFinset.card := by
    rw [← hEDO, ← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card hsub
  let C := D ∪ EOO.image (fun e => e.out.1)
  have hC : T.IsVertexCover (C : Set α) := by
    intro x y hxy
    by_cases hx : x ∈ D
    · left; exact Finset.mem_union_left _ hx
    by_cases hy : y ∈ D
    · right; exact Finset.mem_union_left _ hy
    have he : s(x, y) ∈ EOO := by
      refine Finset.mem_filter.mpr ⟨(mem_edgeFinset).mpr hxy, ?_⟩
      intro v hv
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact hx
      · exact hy
    have hm : (s(x, y)).out.1 ∈ C := Finset.mem_union_right _ (Finset.mem_image_of_mem _ he)
    rcases Sym2.mem_iff.mp (Sym2.out_fst_mem s(x, y)) with h | h
    · left; rw [← h]; exact hm
    · right; rw [← h]; exact hm
  have hCc : C.card ≤ D.card + EOO.card :=
    (Finset.card_union_le _ _).trans (by have := Finset.card_image_le (s := EOO) (f := fun e => e.out.1); omega)
  have := vc_le C hC
  omega

section paths
variable {a b : α}

def PX (p : T.Walk a b) (c : Prop) (v : α) : Prop :=
  ∃ i, i ≤ p.length ∧ p.getVert i = v ∧ (Even i ↔ c)

lemma PX_getVert {p : T.Walk a b} (hp : p.IsPath) (c : Prop) {i : ℕ} (hi : i ≤ p.length) :
    PX p c (p.getVert i) ↔ (Even i ↔ c) := by
  constructor
  · rintro ⟨j, hj, hjv, hjc⟩
    have : j = i := hp.getVert_injOn hj hi hjv
    subst this
    exact hjc
  · intro h
    exact ⟨i, hi, rfl, h⟩

lemma PX_edge {p : T.Walk a b} (hp : p.IsPath) (c : Prop) {x y : α}
    (h : s(x, y) ∈ p.edges) : (PX p c x ↔ ¬ PX p c y) := by
  obtain ⟨i, hi, he⟩ := (p.mk_mem_edges_iff_exists).mp h
  have h1 := PX_getVert hp c (i := i) (by omega)
  have h2 := PX_getVert hp c (i := i + 1) (by omega)
  have hpar : Even (i + 1) ↔ ¬ Even i := Nat.even_add_one
  rcases Sym2.eq_iff.mp he with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · rw [← hx, ← hy, h1, h2, hpar]; tauto
  · rw [← hx, ← hy, h1, h2, hpar]; tauto

lemma nbr_cases {p : T.Walk a b} (hp : p.IsPath) {y z : α} {k : ℕ} (hk : k ≤ p.length)
    (hy : p.getVert k = y) (h : s(y, z) ∈ p.edges) :
    z = p.getVert (k + 1) ∨ z = p.getVert (k - 1) := by
  obtain ⟨i, hi, he⟩ := (p.mk_mem_edges_iff_exists).mp h
  rcases Sym2.eq_iff.mp he with ⟨hx, hz⟩ | ⟨hz, hx⟩
  · have : i = k := hp.getVert_injOn (show i ≤ p.length by omega) hk (hx.trans hy.symm)
    subst this
    exact Or.inl hz.symm
  · have : i + 1 = k := hp.getVert_injOn (show i + 1 ≤ p.length by omega) hk (hx.trans hy.symm)
    subst this
    right
    rw [← hz]
    simp

lemma path_NB {p : T.Walk a b} (hp : p.IsPath) {y u v w : α} (hy : y ∈ p.support)
    (hu : s(y, u) ∈ p.edges) (hv : s(y, v) ∈ p.edges) (hw : s(y, w) ∈ p.edges) :
    u = v ∨ u = w ∨ v = w := by
  obtain ⟨k, hk, hkl⟩ := (Walk.mem_support_iff_exists_getVert).mp hy
  rcases nbr_cases hp hkl hk hu with h1 | h1 <;>
  rcases nbr_cases hp hkl hk hv with h2 | h2 <;>
  rcases nbr_cases hp hkl hk hw with h3 | h3 <;>
  · subst h1 h2 h3; simp

lemma PX_mem {a b : α} {p : T.Walk a b} {c : Prop} {v : α} (h : PX p c v) : v ∈ p.support := by
  obtain ⟨i, -, rfl, -⟩ := h
  exact p.getVert_mem_support i

lemma sym2_ne {x y u w : α} (hx : x ≠ u) (hx' : x ≠ w) : s(x, y) ≠ s(u, w) := by
  intro h
  rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact hx h1
  · exact hx' h1

lemma card_support {a b : α} {p : T.Walk a b} (hp : p.IsPath) :
    p.support.toFinset.card = p.length + 1 := by
  rw [List.toFinset_card_of_nodup hp.support_nodup, Walk.length_support]

lemma card_edges {a b : α} {p : T.Walk a b} (hp : p.IsPath) :
    p.edges.toFinset.card = p.length := by
  rw [List.toFinset_card_of_nodup hp.isTrail.edges_nodup, Walk.length_edges]

lemma edges_sub [Fintype T.edgeSet] {a b : α} (p : T.Walk a b) : p.edges.toFinset ⊆ T.edgeFinset := by
  intro e he
  rw [mem_edgeFinset]
  exact p.edges_subset_edgeSet (List.mem_toFinset.mp he)

lemma exists_tds (hT : T.IsTree) (hn : 2 ≤ Fintype.card α) :
    ∃ D : Finset α, T.IsTotalDominating (D : Set α) ∧ D.card = T.totalDominationNumber := by
  have huniv : T.IsTotalDominating ((Finset.univ : Finset α) : Set α) := by
    intro v
    obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card (by omega) v
    obtain ⟨W⟩ := hT.connected v w
    cases W with
    | nil => exact absurd rfl hw
    | cons h _ => exact ⟨_, by simp, h⟩
  have hne : {n | ∃ D : Finset α, T.IsTotalNDominatingSet n D}.Nonempty :=
    ⟨_, Finset.univ, ⟨huniv, rfl⟩⟩
  obtain ⟨D, hD⟩ := Nat.sInf_mem hne
  exact ⟨D, hD.isTotalDominating, hD.card_eq⟩

lemma one_path (hT : T.IsTree) {a b : α} (p : T.Walk a b) (hp : p.IsPath)
    (hcov : ∀ v, v ∈ p.support) (D : Finset α) (hD : T.IsTotalDominating (D : Set α)) :
    T.vertexCoverNum.toNat ≤ D.card := by
  classical
  have hsupp : p.support.toFinset = Finset.univ := by
    ext v; simp [hcov v]
  have hn : Fintype.card α = p.length + 1 := by
    rw [← Finset.card_univ, ← hsupp, card_support hp]
  have hE : p.edges.toFinset = T.edgeFinset := by
    apply Finset.eq_of_subset_of_card_le (edges_sub p)
    have := hT.card_edgeFinset
    rw [card_edges hp]
    omega
  have hall : ∀ x y, T.Adj x y → s(x, y) ∈ p.edges := by
    intro x y h
    have : s(x, y) ∈ T.edgeFinset := mem_edgeFinset.mpr h
    rw [← hE] at this
    exact List.mem_toFinset.mp this
  let X := Finset.univ.filter (fun v => PX p True v)
  have hmem : ∀ v, v ∈ X ↔ PX p True v := fun v => by simp [X]
  have hcover : T.IsVertexCover (X : Set α) := by
    intro x y h
    have := PX_edge hp True (hall x y h)
    simp only [Finset.mem_coe, hmem]
    tauto
  refine (vc_le X hcover).trans (card_le_of_inj D X hD ?_)
  intro x hx hxD
  obtain ⟨y, hyD, hxy⟩ := hD x
  refine ⟨y, hyD, ?_, hxy, ?_⟩
  · rw [hmem]
    exact (PX_edge hp True (hall x y hxy)).mp ((hmem x).mp hx)
  · intro a b c ha hb hc
    exact path_NB hp (hcov y) (hall _ _ ha) (hall _ _ hb) (hall _ _ hc)

lemma two_path (hT : T.IsTree) {a1 b1 a2 b2 : α} (p1 : T.Walk a1 b1) (p2 : T.Walk a2 b2)
    (hp1 : p1.IsPath) (hp2 : p2.IsPath)
    (hdisj : ∀ v, v ∈ p1.support → v ∉ p2.support)
    (hcov : ∀ v, v ∈ p1.support ∨ v ∈ p2.support)
    (D : Finset α) (hD : T.IsTotalDominating (D : Set α)) :
    T.vertexCoverNum.toNat ≤ D.card := by
  classical
  -- the crossing edge
  obtain ⟨W⟩ := hT.connected a1 a2
  obtain ⟨d, -, hd1, hd2⟩ := W.exists_boundary_dart {v | v ∈ p1.support}
    p1.start_mem_support (fun h => hdisj a2 h p2.start_mem_support)
  set u := d.fst with hu_def
  set w := d.snd with hw_def
  have hu1 : u ∈ p1.support := hd1
  have hw1 : w ∉ p1.support := hd2
  have hw2 : w ∈ p2.support := (hcov w).resolve_left hw1
  have hu2 : u ∉ p2.support := hdisj u hu1
  have huw : T.Adj u w := d.adj
  -- counting edges
  have hs : p1.support.toFinset ∪ p2.support.toFinset = Finset.univ := by
    ext v; simp only [Finset.mem_union, List.mem_toFinset, Finset.mem_univ, iff_true]
    exact hcov v
  have hsd : Disjoint p1.support.toFinset p2.support.toFinset := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    exact hdisj v (List.mem_toFinset.mp h1) (List.mem_toFinset.mp h2)
  have hn : Fintype.card α = (p1.length + 1) + (p2.length + 1) := by
    rw [← Finset.card_univ, ← hs, Finset.card_union_of_disjoint hsd, card_support hp1,
      card_support hp2]
  have hEd : Disjoint p1.edges.toFinset p2.edges.toFinset := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    induction e using Sym2.ind with
    | h x y =>
      exact hdisj x (p1.fst_mem_support_of_mem_edges (List.mem_toFinset.mp h1))
        (p2.fst_mem_support_of_mem_edges (List.mem_toFinset.mp h2))
  have hnot : s(u, w) ∉ p1.edges.toFinset ∪ p2.edges.toFinset := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact hw1 (p1.snd_mem_support_of_mem_edges (List.mem_toFinset.mp h))
    · exact hu2 (p2.fst_mem_support_of_mem_edges (List.mem_toFinset.mp h))
  have hE : insert s(u, w) (p1.edges.toFinset ∪ p2.edges.toFinset) = T.edgeFinset := by
    apply Finset.eq_of_subset_of_card_le
    · intro e he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact mem_edgeFinset.mpr huw
      · rcases Finset.mem_union.mp he with h | h
        · exact edges_sub p1 h
        · exact edges_sub p2 h
    · rw [Finset.card_insert_of_notMem hnot, Finset.card_union_of_disjoint hEd, card_edges hp1,
        card_edges hp2]
      have := hT.card_edgeFinset
      omega
  have hall : ∀ x y, T.Adj x y → s(x, y) = s(u, w) ∨ s(x, y) ∈ p1.edges ∨ s(x, y) ∈ p2.edges := by
    intro x y h
    have : s(x, y) ∈ T.edgeFinset := mem_edgeFinset.mpr h
    rw [← hE] at this
    simpa using this
  -- edges at a vertex other than u, w
  have hloc : ∀ y z, T.Adj y z → y ≠ u → y ≠ w →
      (y ∈ p1.support → s(y, z) ∈ p1.edges) ∧ (y ∈ p2.support → s(y, z) ∈ p2.edges) := by
    intro y z h hyu hyw
    rcases hall y z h with h' | h' | h'
    · exact absurd h' (sym2_ne hyu hyw)
    · refine ⟨fun _ => h', fun hy2 => ?_⟩
      exact absurd hy2 (hdisj y (p1.fst_mem_support_of_mem_edges h'))
    · refine ⟨fun hy1 => ?_, fun _ => h'⟩
      exact absurd (p2.fst_mem_support_of_mem_edges h') (hdisj y hy1)
  have hNB : ∀ y, y ≠ u → y ≠ w → NB2 T y := by
    intro y hyu hyw a' b' c' ha hb hc
    rcases hcov y with hy | hy
    · exact path_NB hp1 hy ((hloc _ _ ha hyu hyw).1 hy) ((hloc _ _ hb hyu hyw).1 hy)
        ((hloc _ _ hc hyu hyw).1 hy)
    · exact path_NB hp2 hy ((hloc _ _ ha hyu hyw).2 hy) ((hloc _ _ hb hyu hyw).2 hy)
        ((hloc _ _ hc hyu hyw).2 hy)
  -- colourings
  let XX : Prop → Prop → Finset α := fun c c' =>
    Finset.univ.filter (fun v => PX p1 c v ∨ PX p2 c' v)
  have memX1 : ∀ c c' v, v ∈ p1.support → (v ∈ XX c c' ↔ PX p1 c v) := by
    intro c c' v hv
    simp only [XX, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.resolve_right (fun h2 => hdisj v hv (PX_mem h2)), Or.inl⟩
  have memX2 : ∀ c c' v, v ∈ p2.support → (v ∈ XX c c' ↔ PX p2 c' v) := by
    intro c c' v hv
    simp only [XX, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.resolve_left (fun h1 => hdisj v (PX_mem h1) hv), Or.inr⟩
  have edgeX : ∀ c c' x y, (s(x, y) ∈ p1.edges ∨ s(x, y) ∈ p2.edges) →
      (x ∈ XX c c' ↔ y ∉ XX c c') := by
    intro c c' x y h
    rcases h with h | h
    · rw [memX1 c c' x (p1.fst_mem_support_of_mem_edges h),
        memX1 c c' y (p1.snd_mem_support_of_mem_edges h)]
      exact PX_edge hp1 c h
    · rw [memX2 c c' x (p2.fst_mem_support_of_mem_edges h),
        memX2 c c' y (p2.snd_mem_support_of_mem_edges h)]
      exact PX_edge hp2 c' h
  have key : ∀ c c', (u ∈ XX c c' ∨ w ∈ XX c c') →
      (∀ y ∈ D, y ∉ XX c c' → y ≠ u ∧ y ≠ w) →
      (∀ x ∈ XX c c', x ∉ D → ∃ y ∈ D, T.Adj x y ∧ s(x, y) ≠ s(u, w)) →
      T.vertexCoverNum.toNat ≤ D.card := by
    intro c c' h1 h2 h3
    have hcover : T.IsVertexCover ((XX c c' : Finset α) : Set α) := by
      intro x y h
      simp only [Finset.mem_coe]
      rcases hall x y h with h' | h'
      · rcases Sym2.eq_iff.mp h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact h1
        · exact h1.symm
      · have := edgeX c c' x y h'
        tauto
    refine (vc_le _ hcover).trans (card_le_of_inj D _ hD ?_)
    intro x hx hxD
    obtain ⟨y, hyD, hxy, hne⟩ := h3 x hx hxD
    have hpe : s(x, y) ∈ p1.edges ∨ s(x, y) ∈ p2.edges := (hall x y hxy).resolve_left hne
    have hyX : y ∉ XX c c' := (edgeX c c' x y hpe).mp hx
    obtain ⟨hyu, hyw⟩ := h2 y hyD hyX
    exact ⟨y, hyD, hyX, hxy, hNB y hyu hyw⟩
  obtain ⟨iu, hiu, hiul⟩ := (Walk.mem_support_iff_exists_getVert).mp hu1
  obtain ⟨iw, hiw, hiwl⟩ := (Walk.mem_support_iff_exists_getVert).mp hw2
  have uX : ∀ c c', u ∈ XX c c' ↔ (Even iu ↔ c) := by
    intro c c'
    rw [memX1 c c' u hu1, ← hiu, PX_getVert hp1 c hiul]
  have wX : ∀ c c', w ∈ XX c c' ↔ (Even iw ↔ c') := by
    intro c c'
    rw [memX2 c c' w hw2, ← hiw, PX_getVert hp2 c' hiwl]
  by_cases hu : u ∈ D ∨ ∃ y ∈ D, T.Adj u y ∧ y ≠ w
  · by_cases hw : w ∈ D ∨ ∃ y ∈ D, T.Adj w y ∧ y ≠ u
    · apply key (Even iu) (Even iw)
      · left; exact (uX _ _).mpr Iff.rfl
      · intro y _ hy
        refine ⟨fun h => hy (h ▸ (uX _ _).mpr Iff.rfl), fun h => hy (h ▸ (wX _ _).mpr Iff.rfl)⟩
      · intro x _ hxD
        by_cases hxu : x = u
        · rw [hxu] at hxD ⊢
          rcases hu with h | ⟨y, hyD, hy, hyw⟩
          · exact absurd h hxD
          · refine ⟨y, hyD, hy, fun h => hyw ?_⟩
            exact (Sym2.congr_right.mp h)
        by_cases hxw : x = w
        · rw [hxw] at hxD ⊢
          rcases hw with h | ⟨y, hyD, hy, hyu⟩
          · exact absurd h hxD
          · refine ⟨y, hyD, hy, fun h => hyu ?_⟩
            rw [Sym2.eq_swap (a := u)] at h
            exact (Sym2.congr_right.mp h)
        obtain ⟨y, hyD, hy⟩ := hD x
        exact ⟨y, hyD, hy, sym2_ne hxu hxw⟩
    · -- w is dominated only by u
      push_neg at hw
      obtain ⟨hwD, hwonly⟩ := hw
      have huD : u ∈ D := by
        obtain ⟨y, hyD, hy⟩ := hD w
        rw [← hwonly y hyD hy]; exact hyD
      apply key (Even iu) (¬ Even iw)
      · left; exact (uX _ _).mpr Iff.rfl
      · intro y hyD hy
        refine ⟨fun h => hy (h ▸ (uX _ _).mpr Iff.rfl), fun h => hwD (h ▸ hyD)⟩
      · intro x hx hxD
        have hxu : x ≠ u := fun h => hxD (h ▸ huD)
        have hxw : x ≠ w := by
          intro h
          have := (wX (Even iu) (¬ Even iw)).mp (h ▸ hx)
          tauto
        obtain ⟨y, hyD, hy⟩ := hD x
        exact ⟨y, hyD, hy, sym2_ne hxu hxw⟩
  · -- u is dominated only by w
    push_neg at hu
    obtain ⟨huD, huonly⟩ := hu
    have hwD : w ∈ D := by
      obtain ⟨y, hyD, hy⟩ := hD u
      rw [← huonly y hyD hy]; exact hyD
    apply key (¬ Even iu) (Even iw)
    · right; exact (wX _ _).mpr Iff.rfl
    · intro y hyD hy
      refine ⟨fun h => huD (h ▸ hyD), fun h => hy (h ▸ (wX _ _).mpr Iff.rfl)⟩
    · intro x hx hxD
      have hxw : x ≠ w := fun h => hxD (h ▸ hwD)
      have hxu : x ≠ u := by
        intro h
        have := (uX (¬ Even iu) (Even iw)).mp (h ▸ hx)
        tauto
      obtain ⟨y, hyD, hy⟩ := hD x
      exact ⟨y, hyD, hy, sym2_ne hxu hxw⟩

lemma core2 (hT : T.IsTree) (hn : 2 ≤ Fintype.card α) (hp : T.pathCoverNumber ≤ 2) :
    T.vertexCoverNum.toNat ≤ T.totalDominationNumber := by
  classical
  have hne : {k | ∃ P : Finset (Finset α), P.card = k ∧ T.IsPathCover P}.Nonempty := by
    refine ⟨_, Finset.univ.image (fun v => ({v} : Finset α)), rfl, ?_, ?_, ?_⟩
    · intro s1 h1 s2 h2 hne
      obtain ⟨v1, -, rfl⟩ := Finset.mem_image.mp h1
      obtain ⟨v2, -, rfl⟩ := Finset.mem_image.mp h2
      rw [Finset.disjoint_singleton]
      intro h
      exact hne (h ▸ rfl)
    · intro v _
      rw [Finset.mem_biUnion]
      exact ⟨{v}, Finset.mem_image_of_mem _ (Finset.mem_univ v), Finset.mem_singleton_self v⟩
    · intro s hs
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hs
      exact ⟨v, v, Walk.nil, Walk.IsPath.nil, by simp⟩
  obtain ⟨P, hPc, hP⟩ := Nat.sInf_mem hne
  have hPc' : P.card ≤ 2 := by
    rw [hPc]; exact hp
  obtain ⟨D, hD, hDc⟩ := exists_tds hT hn
  rw [← hDc]
  have hmem : ∀ v, ∃ s ∈ P, v ∈ s := by
    intro v
    have := hP.2.1 (Finset.mem_univ v)
    rw [Finset.mem_biUnion] at this
    simpa using this
  obtain ⟨v0⟩ : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  have hPpos : 0 < P.card := by
    obtain ⟨s, hs, -⟩ := hmem v0
    exact Finset.card_pos.mpr ⟨s, hs⟩
  rcases (show P.card = 1 ∨ P.card = 2 by omega) with h1 | h2
  · obtain ⟨s, rfl⟩ := Finset.card_eq_one.mp h1
    obtain ⟨a, b, p, hpp, hs⟩ := hP.2.2 s (Finset.mem_singleton_self s)
    apply one_path hT p hpp _ D hD
    intro v
    obtain ⟨s', hs', hv⟩ := hmem v
    rw [Finset.mem_singleton.mp hs', hs] at hv
    exact List.mem_toFinset.mp hv
  · obtain ⟨s1, s2, hne12, rfl⟩ := Finset.card_eq_two.mp h2
    obtain ⟨a1, b1, p1, hp1, hs1⟩ := hP.2.2 s1 (by simp)
    obtain ⟨a2, b2, p2, hp2, hs2⟩ := hP.2.2 s2 (by simp)
    have hdj := hP.1 s1 (by simp) s2 (by simp) hne12
    apply two_path hT p1 p2 hp1 hp2 _ _ D hD
    · intro v h1 h2
      rw [hs1, hs2] at hdj
      exact Finset.disjoint_left.mp hdj (List.mem_toFinset.mpr h1) (List.mem_toFinset.mpr h2)
    · intro v
      obtain ⟨s', hs', hv⟩ := hmem v
      rcases Finset.mem_insert.mp hs' with rfl | hs'
      · rw [hs1] at hv; exact Or.inl (List.mem_toFinset.mp hv)
      · rw [Finset.mem_singleton.mp hs', hs2] at hv; exact Or.inr (List.mem_toFinset.mp hv)

lemma core3 (hT : T.IsTree) (hn : 2 ≤ Fintype.card α) :
    T.vertexCoverNum.toNat ≤ 2 * T.totalDominationNumber := by
  obtain ⟨D, hD, hDc⟩ := exists_tds hT hn
  rw [← hDc]
  exact vc_two hT D hD

end paths

end W372

theorem OMA.solution :
    type_of% @WrittenOnTheWallII.GraphConjecture372.conjecture372.variants.two_paths := by
  intro α _ _ T hT hn hp
  exact W372.core2 hT hn hp
