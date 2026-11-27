import FormalConjectures.ErdosProblems.«917»

/-! Edge counts in critical graphs. Formalizes the partition and matching argument of C. Luo, J. Ma and T. Yang, On the maximum number of edges in k-critical graphs, Theorem 1.1 (arXiv:2301.01656). The clique-removal argument uses separating incidence vectors. -/

/-! The private-neighbor matching of Luo, Ma and Yang, *On the maximum
number of edges in k-critical graphs*, Lemma 2.1 (arXiv:2301.01656). -/

namespace OMA.Structural917
open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

private theorem palette {u w : V} (hk : 4≤k) (hG : Erdos917.IsKCritical G k)
    (huw : G.Adj u w) :
    ∃ c : V → Fin (k-1), c u = c w ∧
      (∀ {x y}, x≠u → x≠w → G.Adj x y → c x ≠ c y) ∧
      ∀ a, ∃ y, G.Adj w y ∧ c y = a := by
  classical
  let H := G.deleteEdges {s(u,w)}
  have hed : H.chromaticNumber < G.chromaticNumber := hG.2 _ huw
  have hs : G.chromaticNumber = ((k-1 : ℕ) : ℕ∞) + 1 := by
    rw [hG.1.1]
    exact_mod_cast (show k=k-1+1 by omega)
  rw [hs, ENat.lt_natCast_add_one_iff] at hed
  obtain ⟨c⟩ := chromaticNumber_le_iff_colorable.mp hed
  have mono {x y : V} (hxy : G.Adj x y) (e : c x=c y) :
      x=u ∧ y=w ∨ x=w ∧ y=u := by
    apply Sym2.eq_iff.mp
    by_contra ne
    exact c.valid (deleteEdges_adj.mpr ⟨hxy,by simpa only [Set.mem_singleton_iff] using ne⟩) e
  have miss : ¬G.Colorable (k-1) := by
    apply lt_chromaticNumber_iff_not_colorable.mp
    rw [hG.1.1]
    exact_mod_cast (show k-1<k by omega)
  have all (a : Fin (k-1)) : ∃ y, G.Adj w y ∧ c y=a := by
    by_contra! no
    apply miss
    refine ⟨Coloring.mk (fun x => if x=w then a else c x) ?_⟩
    intro x y hxy
    split_ifs with hx hy hy
    · exact (hxy.ne (hx.trans hy.symm)).elim
    · subst x
      exact (no y hxy).symm
    · subst y
      exact no x hxy.symm
    · intro e
      rcases mono hxy e with h|h
      · exact hy h.2
      · exact hx h.1
  obtain ⟨y,hy,ec⟩ := all (c w)
  refine ⟨c,?_,?_,all⟩
  · rcases mono hy ec.symm with he|he
    · exact (huw.ne he.1.symm).elim
    · simpa only [he.2] using ec
  · intro x y xu xw hxy e
    rcases mono hxy e with he|he
    · exact xu he.1
    · exact xw he.1

private theorem private_neighbor (hk : 4≤k) (hG : Erdos917.IsKCritical G k)
    (K W : Finset V) (u : V) (hK : G.IsNClique (k-3) K) (hu : u∉K)
    (hW : ∀ w∈W, G.Adj u w ∧ ∀ x∈K,G.Adj x w) (w : W) :
    (∃ v : V, ∀ z : W, G.Adj v z ↔ w=z) ∧
      ∀ ⦃x⦄, x∈W → x≠w.val → ∀ ⦃y⦄, y∈W → y≠w.val → ¬G.Adj x y := by
  classical
  obtain ⟨c,uc,properAt,all⟩ := palette hk hG (hW w w.2).1
  have good {x y : V} (hx : x∈K) (he : G.Adj x y) : c x ≠ c y :=
    properAt (fun e => hu (e ▸ hx)) ((hW w w.2).2 x hx).ne he
  have inj : Set.InjOn c K := by
    intro x hx y hy e
    by_contra ne
    exact good hx (hK.isClique hx hy ne) e
  have notin : c w ∉ K.image c := by
    rintro he
    obtain ⟨x,hx,ex⟩ := mem_image.mp he
    exact good hx ((hW w w.2).2 x hx) ex
  let used := insert (c w) (K.image c)
  have hcard : usedᶜ.card = 1 := by
    rw [Finset.card_compl, Fintype.card_fin]
    simp only [used,card_insert_of_notMem notin,card_image_iff.mpr inj,hK.card_eq]
    omega
  obtain ⟨a,ha⟩ := card_eq_one.mp hcard
  have rest {z : V} (hz : z ∈ W) (zw : z ≠ w.val) : c z = a := by
    apply mem_singleton.mp
    rw [← ha]
    apply mem_compl.mpr
    intro hm
    rcases mem_insert.mp hm with ew|eK
    · exact properAt ((hW z hz).1.ne.symm) zw ((hW z hz).1.symm) (ew.trans uc.symm)
    · obtain ⟨x,hx,he⟩ := mem_image.mp eK
      exact good hx ((hW z hz).2 x hx) he
  obtain ⟨v,hv,va⟩ := all a
  constructor
  · refine ⟨v,fun z => ⟨fun hvz => ?_,fun he => he ▸ hv.symm⟩⟩
    by_contra ne
    have zw : z.val≠w.val := fun e => ne (Subtype.ext e.symm)
    exact properAt ((hW z z.2).1.ne.symm) zw hvz.symm ((rest z.2 zw).trans va.symm)
  · intro x hx xw y hy yw hxy
    exact properAt ((hW x hx).1.ne.symm) xw hxy ((rest hx xw).trans (rest hy yw).symm)

theorem matching (hk : 4≤k) (hG : Erdos917.IsKCritical G k) (K W : Finset V)
    (u : V) (hK : G.IsNClique (k-3) K) (hu : u∉K)
    (hW : ∀ w∈W, G.Adj u w ∧ ∀ x∈K,G.Adj x w) :
    ∃ f : W ↪ V, (∀ w z : W, G.Adj (f w) z ↔ w=z) ∧
      (3≤W.card → G.IsIndepSet (W : Set V)) := by
  classical
  have local' := private_neighbor hk hG K W u hK hu hW
  choose f hf using fun w : W => (local' w).1
  have inj : Function.Injective f := by
    intro w z e
    apply (hf w z).mp
    rw [e]
    exact (hf z z).mpr rfl
  refine ⟨⟨f,inj⟩,hf,?_⟩
  intro hsize x hx y hy _ hxy
  have more : ¬W ⊆ {x,y} := by
    intro sub
    have hle := card_le_card sub
    have hh := card_insert_le x ({y} : Finset V)
    simp only [card_singleton] at hh
    omega
  obtain ⟨w,hw,wout⟩ := Finset.not_subset.mp more
  simp only [mem_insert,mem_singleton,not_or] at wout
  exact (local' ⟨w,hw⟩).2 hx (Ne.symm wout.1) hy (Ne.symm wout.2) hxy

/-- Counting the private neighbors, the common neighbors and a set visible
from a single common neighbor gives the inequality used in Theorem 1.1. -/
theorem counting [Fintype V] (hk : 4≤k) (hG : Erdos917.IsKCritical G k)
    (K W Y : Finset V) (u : V) (hK : G.IsNClique (k-3) K) (hu : u∉K)
    (hW : ∀ w∈W, G.Adj u w ∧ ∀ x∈K,G.Adj x w) (w₀ : W)
    (hd : Disjoint W Y) (hY : ∀ y∈Y,G.Adj w₀ y) :
    2*W.card + Y.card ≤ Fintype.card V + 3 := by
  classical
  obtain ⟨f,hf,hind⟩ := matching hk hG K W u hK hu hW
  let R := univ.map f
  have hc : R.card=W.card := by simp [R]
  have hR {v : V} (hv : v∈R) : ∃ z : W, f z=v := by simpa [R] using hv
  have smallW : (R∩W).card≤2 := by
    by_cases h3 : 3≤W.card
    · have he : R∩W=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro v hv
        obtain ⟨r,s⟩ := mem_inter.mp hv
        obtain ⟨z,rfl⟩ := hR r
        have hadj := (hf z z).mpr rfl
        exact (hind h3) s z.2 hadj.ne hadj
      simp [he]
    · have hle := card_le_card (inter_subset_right (s₁:=R) (s₂:=W))
      omega
  have smallY : (R∩Y).card≤1 := by
    let : Nonempty V := ⟨u⟩
    apply card_le_one_iff_subset_singleton.mpr
    refine ⟨f w₀,?_⟩
    intro v hv
    obtain ⟨r,s⟩ := mem_inter.mp hv
    obtain ⟨z,rfl⟩ := hR r
    exact mem_singleton.mpr (congrArg f ((hf z w₀).mp (hY _ s).symm))
  have p := card_le_univ (R ∪ (W ∪ Y))
  have q := card_union_add_card_inter R (W∪Y)
  have w := card_union_of_disjoint hd
  have i : (R∩(W∪Y)).card ≤ (R∩W).card+(R∩Y).card := by
    rw [inter_union_distrib_left]
    exact card_union_le _ _
  omega

end OMA.Structural917

/-! A linear bound on the cost of eliminating almost-spanning-color cliques from a
critical graph. A coloring after one edge is deleted separates its own clique from
all the other members of an edge-disjoint clique packing. -/
namespace OMA.Removal917
open Finset SimpleGraph
open scoped Classical

private def edges {V : Type*} [DecidableEq V] (s : Finset V) : Finset (Sym2 V) :=
  s.offDiag.image (fun p ↦ s(p.1,p.2))

private lemma edge_mem {V : Type*} [DecidableEq V] {s : Finset V} {x y : V} :
    s(x,y) ∈ edges s ↔ x∈s ∧ y∈s ∧ x≠y := by
  constructor
  · intro h
    obtain ⟨⟨a,b⟩,hab,eq⟩ := mem_image.mp h
    obtain ⟨ha,hb,ne⟩ := mem_offDiag.mp hab
    rcases Sym2.eq_iff.mp eq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact ⟨ha,hb,ne⟩
    · exact ⟨hb,ha,Ne.symm ne⟩
  · rintro h
    exact mem_image.mpr ⟨(x,y),mem_offDiag.mpr h,rfl⟩

private lemma edgeless_color {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (crit : Erdos917.IsKCritical G (r+1)) {x y : V} (h : G.Adj x y) :
    ∃ c : V → Fin r, c x=c y ∧ ∀ u v, G.Adj u v → s(u,v)≠s(x,y) → c u≠c v := by
  let H := G.deleteEdges {s(x,y)}
  have drop : H.chromaticNumber < G.chromaticNumber := crit.2 _ h
  have kk : G.chromaticNumber = (r:ℕ∞)+1 := by simpa using crit.1.1
  rw [kk] at drop
  obtain ⟨c⟩ := chromaticNumber_le_iff_colorable.mp (Order.le_of_lt_add_one drop)
  have rest (u v : V) (hu : G.Adj u v) (hn : s(u,v)≠s(x,y)) : c u≠c v :=
    c.valid (SimpleGraph.deleteEdges_adj.mpr ⟨hu,hn⟩)
  refine ⟨c,?_,rest⟩
  by_contra different
  have proper : G.Colorable r := ⟨(⟨c,fun {u v} hu => by
    by_cases he : s(u,v)=s(x,y)
    · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simpa [ne_comm] using different
    · exact rest _ _ hu he⟩ : G.Coloring (Fin r))⟩
  have bad := chromaticNumber_le_iff_colorable.mpr proper
  rw [kk] at bad
  have bad' : ((r+1:ℕ):ℕ∞) ≤ r := by simpa using bad
  exact Nat.not_succ_le_self r (by exact_mod_cast bad')

private lemma separator {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {r : ℕ} (hr : 2≤r) (crit : Erdos917.IsKCritical G (r+1))
    (A : Finset (Finset V)) (cl : ∀ s∈A, G.IsNClique r s)
    (dis : (A:Set (Finset V)).PairwiseDisjoint edges) (s : A) :
    ∃ B : Finset V, ∀ t : A, (t.val ∩ B).card = if t=s then 0 else 1 := by
  classical
  have hs := cl _ s.property
  obtain ⟨x,hx,y,hy,ne⟩ := Finset.one_lt_card.mp (show 1<s.val.card by rw [hs.2]; omega)
  obtain ⟨c,eq,ok⟩ := edgeless_color crit (hs.1 hx hy ne)
  let cs := fun i : s.val => c i
  have sizes : Fintype.card s.val = Fintype.card (Fin r) := by simp [hs.2]
  have miss : ¬Function.Surjective cs := by
    intro sur
    have inj := (Fintype.bijective_iff_surjective_and_card ..).2 ⟨sur,sizes⟩
    exact ne (congrArg Subtype.val (inj.1 (a₁:=⟨x,hx⟩) (a₂:=⟨y,hy⟩) eq))
  unfold Function.Surjective at miss
  push Not at miss
  obtain ⟨z,no⟩ := miss
  let B := univ.filter (fun v : V => c v=z)
  have b (v:V) : v∈B ↔ c v=z := by simp [B]
  refine ⟨B,fun t => ?_⟩
  split
  · rename_i h; subst t
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro i hi
    exact no (⟨i,(mem_inter.mp hi).1⟩ : s.val) ((b _).mp (mem_inter.mp hi).2)
  · rename_i diff
    have ht := cl _ t.property
    have ds := dis t.property s.property (fun e => diff (Subtype.ext e))
    let ct := fun i : t.val => c i
    have inj : Function.Injective ct := by
      intro i j ij
      apply Subtype.ext
      by_contra h
      have edge := edge_mem.mpr ⟨i.property,j.property,h⟩
      have exy := edge_mem.mpr ⟨hx,hy,ne⟩
      exact ok _ _ (ht.1 i.property j.property h)
        (fun e => Finset.disjoint_left.mp ds edge (e ▸ exy)) ij
    have bij : Function.Bijective ct := (Fintype.bijective_iff_injective_and_card ..).2
      ⟨inj,by simp [ht.2]⟩
    obtain ⟨i,hi⟩ := bij.2 z
    apply card_eq_one.mpr
    refine ⟨i.val,Finset.ext fun x => ?_⟩
    simp only [mem_inter,mem_singleton,b]
    constructor
    · rintro ⟨xt,xc⟩
      exact congrArg Subtype.val (inj (a₁:=⟨x,xt⟩) (a₂:=i) (xc.trans hi.symm))
    · rintro rfl; exact ⟨i.property,hi⟩

private lemma packing {V : Type*} [Fintype V] [DecidableEq V] {A : Finset (Finset V)}
    (sep : ∀ s : A, ∃ B : Finset V, ∀ t : A, (t.val ∩ B).card = if t=s then 0 else 1) :
    A.card ≤ Fintype.card V+1 := by
  classical
  let row (s:A) : Option V → ℚ := fun v => match v with
    | none => 1
    | some x => if x∈s.val then 1 else 0
  have ind : LinearIndependent ℚ row := by
    apply Fintype.linearIndependent_iff.mpr
    intro w zero i
    have atx (x : Option V) : ∑ j, w j * row j x=0 := by
      simpa [Finset.sum_apply, Pi.smul_apply,smul_eq_mul] using congrFun zero x
    have total : ∑ j, w j=0 := by simpa [row] using atx none
    obtain ⟨B,hB⟩ := sep i
    have sumrow (j:A) : ∑ x ∈ B, row j (some x) = (if j=i then 0 else 1 : ℚ) := by
      change (∑ x ∈ B, if x ∈ j.val then (1:ℚ) else 0)=_
      rw [Finset.sum_boole]
      have eq : B.filter (fun x => x∈j.val) = j.val∩B := by ext; simp [and_comm]
      rw [eq,hB]; split <;> simp
    have Bsum : ∑ j, w j*(∑ x ∈ B, row j (some x))=0 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact sum_eq_zero fun x _ => atx (some x)
    simp_rw [sumrow,mul_ite,mul_zero,mul_one] at Bsum
    have restore : (∑ j : A, w j) = (∑ j : A, if j=i then 0 else w j)+w i := by
      have hi : (∑ j : A, if j=i then w j else 0) = w i := by simp
      rw [←hi,←Finset.sum_add_distrib]
      exact sum_congr rfl fun j _ => by by_cases j=i <;> simp [*]
    linarith
  simpa using ind.fintype_card_le_finrank

/-- Removing linearly many edges suffices to destroy every clique of size r in
an (r+1)-critical graph. The constant is uniform in the order. -/
theorem removal {n r : ℕ} (hr : 2≤r) (G : SimpleGraph (Fin n))
    (crit : Erdos917.IsKCritical G (r+1)) :
    ∃ E : Finset (Sym2 (Fin n)), E.card≤(n+1)*r^2 ∧ (G.deleteEdges E).CliqueFree r := by
  classical
  let Fs := (G.cliqueFinset r).powerset.filter (fun A : Finset (Finset (Fin n)) => (A:Set (Finset (Fin n))).PairwiseDisjoint edges)
  have empty : ∅∈Fs := by simp [Fs]
  obtain ⟨A,hA,best⟩ := Fs.exists_max_image Finset.card ⟨∅,empty⟩
  obtain ⟨sub,dis⟩ := mem_filter.mp hA
  have cl (s) (hs : s∈A) := mem_cliqueFinset_iff.mp (mem_powerset.mp sub hs)
  have bound := packing (separator hr crit A cl dis)
  let E := A.biUnion edges
  refine ⟨E, ?_,?_⟩
  · calc
      E.card ≤ ∑ s ∈ A, (edges s).card := card_biUnion_le
      _ ≤ ∑ _ ∈ A, r^2 := sum_le_sum fun s hs => by
        apply (card_image_le).trans
        have sub : s.offDiag ⊆ s ×ˢ s := fun _ he => mem_product.mpr ⟨(mem_offDiag.mp he).1,(mem_offDiag.mp he).2.1⟩
        calc
          s.offDiag.card ≤ (s ×ˢ s).card := card_le_card sub
          _ = _ := by simp [(cl s hs).card_eq,pow_two]
      _ ≤ (n+1)*r^2 := by simpa using Nat.mul_le_mul_right (r^2) bound
  · intro t ht
    have survivors (s) (hs : s∈A) : Disjoint (edges t) (edges s) := by
      apply Finset.disjoint_left.mpr
      intro e he
      induction e using Sym2.inductionOn with
      | _ u v =>
        intro old
        obtain ⟨uT,vT,ne⟩ := edge_mem.mp he
        exact (deleteEdges_adj.mp (ht.1 uT vT ne)).2 (mem_biUnion.mpr ⟨s,hs,old⟩)
    have non : t∉A := by
      intro htA
      obtain ⟨x,hx,y,hy,ne⟩ := one_lt_card.mp (show 1<t.card by rw [ht.2]; omega)
      have e := edge_mem.mpr ⟨hx,hy,ne⟩
      exact disjoint_left.mp (survivors _ htA) e e
    have larger : insert t A ∈ Fs := by
      apply mem_filter.mpr
      constructor
      · apply mem_powerset.mpr
        exact insert_subset (mem_cliqueFinset_iff.mpr (ht.mono (deleteEdges_le _))) (mem_powerset.mp sub)
      · rw [coe_insert]
        exact dis.insert_of_notMem non (fun s hs => survivors s hs)
    have final := best _ larger
    rw [card_insert_of_notMem non] at final
    omega

end OMA.Removal917

/-! Füredi's stability argument (the maximum-degree neighborhood induction),
as used in Luo–Ma–Yang, Lemma 3.1.  We retain the stronger comparison with
the complete graph on the partition actually constructed. -/
open Finset SimpleGraph
open scoped Classical
noncomputable section
namespace OMA.Stability917

variable {V : Type*}

private def pairs (P : V → V → Prop) (S T : Finset V) : ℕ :=
  ∑ x ∈ S, ∑ y ∈ T, if P x y then 1 else 0

private lemma pairs_swap {P : V → V → Prop} (sym : ∀ x y, P x y ↔ P y x)
    (S T : Finset V) : pairs P S T = pairs P T S := by
  unfold pairs
  rw [sum_comm]
  exact sum_congr rfl fun y _ => sum_congr rfl fun x _ => if_congr (sym x y) rfl rfl

private lemma pairs_congr {P Q : V → V → Prop} {S T : Finset V}
    (h : ∀ x ∈ S, ∀ y ∈ T, P x y ↔ Q x y) : pairs P S T = pairs Q S T :=
  sum_congr rfl fun x hx => sum_congr rfl fun y hy => if_congr (h x hx y hy) rfl rfl

private lemma pairs_split (P : V → V → Prop) {A B S : Finset V}
    (dis : Disjoint A B) (cover : A ∪ B = S) :
    pairs P S S = pairs P A A + pairs P A B + pairs P B A + pairs P B B := by
  subst S
  simp only [pairs, sum_union dis, sum_add_distrib]
  omega

private lemma pair_induction (G : SimpleGraph V) (r : ℕ) (S : Finset V)
    (free : ∀ Q ⊆ S, ¬ G.IsNClique (r+1) Q) :
    ∃ c : V → ℕ, (∀ x ∈ S, c x < r) ∧
      pairs G.Adj S S + pairs (fun x y => G.Adj x y ∧ c x = c y) S S ≤
        pairs (fun x y => c x ≠ c y) S S := by
  induction r generalizing S with
  | zero =>
    have hem : S = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro a ha
      exact free {a} (by simpa) (by simp)
    subst S
    exact ⟨fun _ => 0, by simp, by simp [pairs]⟩
  | succ r ih =>
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact ⟨fun _ => 0, by simp, by simp [pairs]⟩
    obtain ⟨v, hv, hmax⟩ := S.exists_max_image (fun x => (S.filter (G.Adj x)).card) hne
    let A := S.filter (G.Adj v)
    let B := S \ A
    have dis : Disjoint A B := disjoint_sdiff
    have cover : A ∪ B = S := union_sdiff_of_subset (filter_subset _ _)
    have hfree : ∀ Q ⊆ A, ¬G.IsNClique (r+1) Q := by
      intro Q hQ hcl
      apply free (insert v Q) (insert_subset hv (hQ.trans (filter_subset _ _)))
      exact hcl.insert fun x hx => (mem_filter.mp (hQ hx)).2
    obtain ⟨c, hc, hi⟩ := ih A hfree
    let d x := if x ∈ A then c x else r
    have da : ∀ x ∈ A, d x = c x := fun x hx => if_pos hx
    have db : ∀ x ∈ B, d x = r := fun x hx => if_neg (mem_sdiff.mp hx).2
    refine ⟨d, ?_, ?_⟩
    · intro x hx
      by_cases ha : x ∈ A
      · rw [da x ha]; exact (hc x ha).trans (Nat.lt_succ_self _)
      · simp [d, ha]
    let I x y := G.Adj x y ∧ d x = d y
    let K x y := d x ≠ d y
    have iAA : pairs I A A = pairs (fun x y => G.Adj x y ∧ c x = c y) A A :=
      pairs_congr fun x hx y hy => by simp [I, da x hx, da y hy]
    have kAA : pairs K A A = pairs (fun x y => c x ≠ c y) A A :=
      pairs_congr fun x hx y hy => by simp [K, da x hx, da y hy]
    have iAB : pairs I A B = 0 := by
      unfold pairs
      apply sum_eq_zero
      intro x hx
      apply sum_eq_zero
      intro y hy
      simp [I, da x hx, db y hy, (hc x hx).ne]
    have iBB : pairs I B B = pairs G.Adj B B :=
      pairs_congr fun x hx y hy => by simp [I, db x hx, db y hy]
    have kAB : pairs K A B = A.card * B.card := by
      calc
        _ = pairs (fun _ _ => True) A B := pairs_congr fun x hx y hy => by
          simp [K, da x hx, db y hy, (hc x hx).ne]
        _ = _ := by simp [pairs]
    have bound : pairs G.Adj B A + pairs G.Adj B B ≤ A.card * B.card := by
      calc
        _ = pairs G.Adj B S := by
          rw [← cover]
          simp only [pairs, sum_union dis, sum_add_distrib]
        _ ≤ ∑ _x ∈ B, A.card := by
          apply sum_le_sum
          intro x hx
          simpa only [A, card_filter] using hmax x (mem_sdiff.mp hx).1
        _ = _ := by simp [Nat.mul_comm]
    change pairs G.Adj S S + pairs I S S ≤ pairs K S S
    rw [pairs_split G.Adj dis cover, pairs_split I dis cover, pairs_split K dis cover,
      pairs_swap G.adj_comm A B,
      pairs_swap (P := I) (fun x y => and_congr (G.adj_comm x y) eq_comm) B A,
      pairs_swap (P := K) (fun x y => ne_comm) B A,
      iAA, iAB, iBB, kAA, kAB]
    omega

/-- The complete multipartite graph with prescribed class labels. -/
def K {r : ℕ} (c : V → Fin r) : SimpleGraph V := (⊤ : SimpleGraph (Fin r)).comap c

private lemma all_pairs [Fintype V] (G : SimpleGraph V) :
    pairs G.Adj univ univ = 2 * G.edgeFinset.card := by
  rw [← G.sum_degrees_eq_twice_card_edges]
  simp only [pairs, degree, neighborFinset_eq_filter, card_filter]

/-- The number of edges plus the number internal to the chosen partition is bounded by
the number of edges of the complete multipartite graph on that same partition. -/
theorem partition {V : Type*} [Fintype V] {r : ℕ} (_hr : 0 < r)
    (G : SimpleGraph V) (free : G.CliqueFree (r+1)) :
    ∃ c : V → Fin r, G.edgeFinset.card + (G \ K c).edgeFinset.card ≤ (K c).edgeFinset.card := by
  obtain ⟨c,hc,hi⟩ := pair_induction G r univ (fun Q _ => free Q)
  let d (x : V) : Fin r := ⟨c x, hc x (mem_univ _)⟩
  have inner : pairs (fun x y => G.Adj x y ∧ c x = c y) univ univ =
      pairs (G \ K d).Adj univ univ := pairs_congr fun x _ y _ => by
    simp [K, SimpleGraph.sdiff_adj, SimpleGraph.comap_adj, SimpleGraph.top_adj, d, Fin.ext_iff]
  have outer : pairs (fun x y => c x ≠ c y) univ univ = pairs (K d).Adj univ univ :=
    pairs_congr fun x _ y _ => by simp [K, SimpleGraph.comap_adj, SimpleGraph.top_adj, d, Fin.ext_iff]
  rw [inner, outer, all_pairs, all_pairs, all_pairs] at hi
  refine ⟨d, ?_⟩
  simp only [edgeFinset, ← Set.ncard_eq_toFinset_card'] at hi ⊢
  omega

/-- Exact variance identity for the sizes of the color classes. -/
theorem variance {n r : ℕ} (hr : 0 < r) (c : Fin n → Fin r) :
    (∑ i : Fin r, (((univ.filter fun x => c x = i).card : ℝ) - n / (r:ℝ))^2) +
      2 * ((K c).edgeFinset.card : ℝ) = (1 - 1 / (r:ℝ)) * (n:ℝ)^2 := by
  let w (i : Fin r) := (univ.filter fun x => c x = i).card
  have ws : ∑ i, w i = n := by
    simpa [w] using sum_card_fiberwise_eq_card_filter univ univ c
  have eqpairs : pairs (fun x y => c x = c y) univ univ = ∑ i, (w i)^2 := by
    calc
      _ = ∑ x : Fin n, w (c x) := sum_congr rfl fun x _ => by
        simp only [w, card_filter]
        apply sum_congr rfl
        intro y _
        by_cases h : c x = c y
        · simp [h]
        · simp [h, Ne.symm h]
      _ = ∑ i : Fin r, ∑ x ∈ univ.filter (fun x => c x = i), w (c x) :=
        (sum_fiberwise univ c _).symm
      _ = _ := by
        apply sum_congr rfl
        intro i _
        calc
          _ = ∑ _x ∈ univ.filter (fun x => c x = i), w i :=
            sum_congr rfl fun x hx => by rw [(mem_filter.mp hx).2]
          _ = _ := by simp [w, sq]
  have total : pairs (K c).Adj univ univ + pairs (fun x y => c x = c y) univ univ = n^2 := by
    unfold pairs
    simp only [← sum_add_distrib]
    calc
      _ = ∑ _x : Fin n, ∑ _y : Fin n, (1:ℕ) := by
        apply sum_congr rfl
        intro x _
        apply sum_congr rfl
        intro y _
        by_cases h : c x = c y <;> simp [K, SimpleGraph.comap_adj, SimpleGraph.top_adj, h]
      _ = _ := by simp [sq]
  rw [eqpairs, all_pairs] at total
  have sumw : ∑ i, (w i : ℝ) = n := by exact_mod_cast ws
  have sumsq : 2 * ((K c).edgeFinset.card : ℝ) + ∑ i, (w i : ℝ)^2 = (n:ℝ)^2 := by
    exact_mod_cast total
  change (∑ i, ((w i:ℝ) - _ )^2) + _ = _
  have expnd (a b : ℝ) : (a-b)^2 = a^2 - 2*b*a + b^2 := by ring
  simp_rw [expnd]
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, sumw, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hr' : (r:ℝ) ≠ 0 := by positivity
  have scalar : -(2*((n:ℝ)/r))*n + (r:ℝ)*((n:ℝ)/r)^2 = -(1/(r:ℝ))*(n:ℝ)^2 := by
    field_simp
    ring
  linear_combination sumsq + scalar

private lemma compare_edges {V : Type*} [Fintype V] (G H : SimpleGraph V) :
    (H \ G).edgeFinset.card + G.edgeFinset.card = H.edgeFinset.card + (G \ H).edgeFinset.card := by
  simp only [edgeFinset_sdiff]
  have ha := card_sdiff_add_card_inter H.edgeFinset G.edgeFinset
  have hb := card_sdiff_add_card_inter G.edgeFinset H.edgeFinset
  rw [inter_comm] at hb
  omega

/-- Starting within `t` edges of the quadratic Turán bound leaves at most `2t` missing
cross-edges and at most `2t` total squared deviation from the mean class size. -/
theorem deficit {n r : ℕ} (hr : 0 < r) (G : SimpleGraph (Fin n)) (free : G.CliqueFree (r+1))
    {t : ℝ} (dense : (1 - 1/(r:ℝ))*(n:ℝ)^2/2 - t ≤ G.edgeFinset.card) :
    ∃ c : Fin n → Fin r, ((K c \ G).edgeFinset.card : ℝ) ≤ 2*t ∧
      (∑ i : Fin r, (((univ.filter fun x => c x = i).card : ℝ) - n/(r:ℝ))^2) ≤ 2*t := by
  obtain ⟨c, cmp⟩ := partition hr G free
  have swap := compare_edges G (K c)
  have hvar := variance hr c
  have hnon : 0 ≤ ∑ i : Fin r, (((univ.filter fun x => c x = i).card : ℝ) - n/(r:ℝ))^2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have cr : (G.edgeFinset.card:ℝ) + (G \ K c).edgeFinset.card ≤ (K c).edgeFinset.card := by
    simp only [edgeFinset, ← Set.ncard_eq_toFinset_card'] at cmp ⊢
    exact_mod_cast cmp
  have sr : ((K c \ G).edgeFinset.card:ℝ) + G.edgeFinset.card =
      (K c).edgeFinset.card + (G \ K c).edgeFinset.card := by
    simp only [edgeFinset, ← Set.ncard_eq_toFinset_card'] at swap ⊢
    exact_mod_cast swap
  have ni : 0 ≤ ((G \ K c).edgeFinset.card:ℝ) := Nat.cast_nonneg _
  exact ⟨c, by linarith, by linarith⟩


end OMA.Stability917
end

/-! Trimming the vertices of greatest missing degree in each part, as in
Luo, Ma and Yang, *On the maximum number of edges in k-critical graphs*,
proof of Theorem 1.1. -/

namespace OMA.Trim917
open Finset

private theorem remove_largest {V : Type*} (d : V → ℕ) (b : ℕ) (S : Finset V)
    (hb : b ≤ S.card) :
    ∃ U ⊆ S, U.card+b=S.card ∧ b*U.sup d ≤ ∑ v∈S,d v := by
  classical
  induction b generalizing S with
  | zero => exact ⟨S,Subset.rfl,by simp,by simp⟩
  | succ b ih =>
    obtain ⟨v,hv,top⟩ := S.exists_max_image d (card_pos.mp (by omega))
    have he : (S.erase v).card=S.card-1 := card_erase_of_mem hv
    obtain ⟨U,sub,hc,hw⟩ := ih (S.erase v) (by omega)
    refine ⟨U,sub.trans (erase_subset _ _),by omega,?_⟩
    have e : U.sup d ≤ d v := Finset.sup_le fun x hx => top x (mem_of_mem_erase (sub hx))
    have add := sum_erase_add S d hv
    rw [Nat.succ_mul]
    omega

theorem trim {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq ι]
    (c : V → ι) (d : V → ℕ) (b : ℕ) (hb : ∀ i, b≤(univ.filter (fun v => c v=i)).card) :
    ∃ (U : ι → Finset V) (m : ι → ℕ),
      (∀ i, U i ⊆ univ.filter (fun v => c v=i)) ∧
      (∀ i, (U i).card+b=(univ.filter (fun v => c v=i)).card) ∧
      (∀ i v, v ∈ U i → d v ≤ m i) ∧ b*(∑ i,m i) ≤ ∑ v,d v := by
  classical
  choose U sub cnt bound using fun i => remove_largest d b _ (hb i)
  refine ⟨U,fun i => (U i).sup d,sub,cnt,fun i v hv => le_sup hv,?_⟩
  rw [mul_sum]
  exact (sum_le_sum (fun i _ => bound i)).trans_eq (sum_fiberwise univ c d)

end OMA.Trim917

/-! The integer rounding in Turán's formula is bounded uniformly in the order
when the clique size is fixed. -/
namespace OMA.Round917
open SimpleGraph Filter
open scoped Topology

theorem rounding (n r : ℕ) (hr : 2≤r) :
    (1-1/(r:ℝ))*(n:ℝ)^2/2-((r:ℝ)^2+1) ≤
      (extremalNumber n (completeGraph (Fin (r+1))) : ℝ) ∧
    (extremalNumber n (completeGraph (Fin (r+1))) : ℝ) ≤ (1-1/(r:ℝ))*(n:ℝ)^2/2 := by
  classical
  have : Nontrivial (Fin (r+1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have eq : extremalNumber n (completeGraph (Fin (r+1))) = (turanGraph n r).edgeFinset.card := by
    change extremalNumber n (⊤ : SimpleGraph (Fin (r+1))) = _
    rw [extremalNumber_top,Fintype.card_fin,Nat.add_sub_cancel]
  rw [eq]
  let u := n%r
  let a := (n^2-u^2)*(r-1)
  let b := 2*r
  let m := (turanGraph n r).edgeFinset.card
  have mlo : a/b ≤ m := by
    change _ ≤ (turanGraph n r).edgeFinset.card
    rw [card_edgeFinset_turanGraph]; exact Nat.le_add_right ..
  have bpos : 0<b := by dsimp [b]; omega
  have qr := Nat.mod_add_div a b
  have rem := Nat.mod_lt a bpos
  have natlower : a ≤ b*m+b := by nlinarith only [qr,rem,Nat.mul_le_mul_left b mlo]
  have uN : u≤n := Nat.mod_le ..
  have uR : u≤r := (Nat.mod_lt n (by omega)).le
  have un2 : u^2≤n^2 := Nat.pow_le_pow_left uN _
  have hr' : 1≤r := by omega
  dsimp [a,b] at natlower
  have castlow : ((n:ℝ)^2-(u:ℝ)^2)*((r:ℝ)-1) ≤ (2*r)*(m:ℝ)+2*r := by
    exact_mod_cast (by simpa only [Nat.cast_mul,Nat.cast_sub un2,Nat.cast_sub hr',
      Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] using
      (Nat.cast_le (α:=ℝ)).mpr natlower :
      ((n:ℝ)^2-(u:ℝ)^2)*((r:ℝ)-1) ≤ (2*r)*(m:ℝ)+2*r)
  have rup : (u:ℝ)^2 ≤ (r:ℝ)^2 := by exact_mod_cast Nat.pow_le_pow_left uR 2
  have rp : 0<(r:ℝ) := by exact_mod_cast (show 0<r by omega)
  have cn := mul_card_edgeFinset_turanGraph_le (n:=n) (r:=r)
  have castup : 2*(r:ℝ)*(m:ℝ)≤((r:ℝ)-1)*(n:ℝ)^2 := by
    simpa only [Nat.cast_mul,Nat.cast_sub hr',Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] using
      (Nat.cast_le (α:=ℝ)).mpr cn
  change _ ≤ (m:ℝ) ∧ (m:ℝ) ≤ _
  constructor
  · field_simp
    nlinarith only [castlow,mul_le_mul_of_nonneg_left rup rp.le,sq_nonneg (u:ℝ),
      mul_nonneg rp.le (sq_nonneg (r:ℝ))]
  · field_simp
    nlinarith only [castup]

theorem nonnegative (r : ℕ) (hr : 2≤r) :
    ∀ᶠ n : ℕ in atTop, 0 ≤ (extremalNumber n (completeGraph (Fin (r+1))) : ℝ) -
      (n:ℝ)^2/(36*((r:ℝ)+1)^2) := by
  filter_upwards [eventually_ge_atTop (4*(r+1))] with n hn
  have rp : (2:ℝ)≤r := by exact_mod_cast hr
  have np : 4*((r:ℝ)+1) ≤ n := by exact_mod_cast hn
  have q : 1/(r:ℝ) ≤ 1/2 := by gcongr
  have big := mul_le_mul_of_nonneg_right (show (1:ℝ)/2 ≤ 1-1/r by linarith) (sq_nonneg (n:ℝ))
  have sqn : (4*((r:ℝ)+1))^2≤(n:ℝ)^2 := by gcongr
  have div : (n:ℝ)^2/(36*((r:ℝ)+1)^2) ≤ (n:ℝ)^2/8 := by
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num)
    nlinarith only [rp,sq_nonneg (r:ℝ)]
  nlinarith only [(rounding n r hr).1,div,big,sqn,rp]

end OMA.Round917

/-! Finding the clique and the common neighbor set in a nearly complete
multipartite graph, following Luo, Ma and Yang (2023, Theorem 1.1). -/
namespace OMA.Transversal917
open Finset SimpleGraph
open scoped Classical
variable {ι V : Type} [Fintype ι] [Fintype V] [DecidableEq ι] [DecidableEq V]

noncomputable def misses (G : SimpleGraph V) (c : V → ι) (v : V) :=
  univ.filter (fun w => c w ≠ c v ∧ ¬G.Adj v w)

omit [Fintype ι] [DecidableEq V] in
private theorem fail_le (G : SimpleGraph V) (c : V → ι) {i : ι} {U : Finset V}
    (hU : ∀ u ∈ U, c u=i) {v : V} (hv : c v≠i) :
    (U.filter (fun w => ¬G.Adj v w)).card ≤ (misses G c v).card := by
  apply card_le_card
  intro w hw
  obtain ⟨hw₁,hw₂⟩ := mem_filter.mp hw
  exact mem_filter.mpr ⟨mem_univ _,by rw [hU _ hw₁]; exact ⟨Ne.symm hv,hw₂⟩⟩

theorem transversal [Nonempty V] (G : SimpleGraph V) (c : V → ι)
    (U : ι → Finset V) (m : ι → ℕ)
    (fiber : ∀ i v, v ∈ U i → c v=i)
    (good : ∀ i v, v ∈ U i → (misses G c v).card ≤ m i)
    (size : ∀ i, ∑ j, m j < (U i).card) :
    ∃ x : ι → V, (∀ i, x i ∈ U i) ∧ ∀ i j, i≠j → G.Adj (x i) (x j) := by
  classical
  suffices step : ∀ S : Finset ι, ∃ x : ι → V, (∀ i ∈ S, x i ∈ U i) ∧
      ∀ i ∈ S, ∀ j ∈ S, i≠j → G.Adj (x i) (x j) by
    simpa using step univ
  intro S
  induction S using Finset.induction_on with
  | empty => exact ⟨fun _ => Classical.arbitrary V,by simp,by simp⟩
  | @insert i S hi ih =>
    obtain ⟨x,hx,hadj⟩ := ih
    let F (j : ι) := (U i).filter fun v => ¬G.Adj (x j) v
    have bound := calc
      (S.biUnion F).card ≤ ∑ j ∈ S, (F j).card := card_biUnion_le
      _ ≤ ∑ j ∈ S, m j := sum_le_sum (fun j hj => by
        apply (fail_le G c (fiber i) ?_).trans (good j _ (hx j hj))
        rw [fiber j _ (hx j hj)]
        exact fun h => hi (h ▸ hj))
      _ ≤ ∑ j, m j := sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
      _ < (U i).card := size i
    obtain ⟨v,hv,hv'⟩ := not_subset.mp (fun sub : U i ⊆ S.biUnion F => (not_le.mpr bound) (card_le_card sub))
    have connects (j : ι) (hj : j ∈ S) : G.Adj (x j) v := by
      by_contra bad; exact hv' (mem_biUnion.mpr ⟨j,hj,mem_filter.mpr ⟨hv,bad⟩⟩)
    refine ⟨Function.update x i v,?_,?_⟩
    · intro j hj
      rcases mem_insert.mp hj with rfl|h
      · simpa using hv
      · simpa [Function.update_of_ne (ne_of_mem_of_not_mem h hi)] using hx j h
    · intro j hj k hk jk
      by_cases ji : j=i
      · subst j
        simpa [Function.update_of_ne jk.symm] using (connects k ((mem_insert.mp hk).resolve_left jk.symm)).symm
      · have hj' := (mem_insert.mp hj).resolve_left ji
        by_cases ki : k=i
        · subst k; simpa [Function.update_of_ne ji] using connects j hj'
        · simpa [Function.update_of_ne ji,Function.update_of_ne ki] using
            hadj j hj' k ((mem_insert.mp hk).resolve_left ki) jk

noncomputable def part (c : V → ι) (i : ι) := univ.filter fun v => c v=i

/-- A quantitative obstruction to almost complete cross-edges, retaining
the sharper contribution of the least missing degree outside the last part. -/
theorem obstruction [Nonempty V] {k : ℕ} (hk : 4≤k) (dim : Fintype.card ι=k-2)
    (G : SimpleGraph V) (crit : Erdos917.IsKCritical G k) (c : V → ι)
    (U : ι → Finset V) (m : ι → ℕ) (o q : ι) (hqo : q≠o)
    (fiber : ∀ i v, v ∈ U i → c v=i)
    (good : ∀ i v, v ∈ U i → (misses G c v).card ≤ m i)
    (size : ∀ i, (∑ j, m j)+1 < (U i).card) :
    (part c o).card ≤ 3+2*((∑ j ∈ univ.erase o,m j)+m q)+m o := by
  classical
  obtain ⟨x,hx,hcl⟩ := transversal G c U m fiber good (fun i => by have := size i; omega)
  have cx (i) := fiber i (x i) (hx i)
  have inj : Function.Injective x := by
    intro i j e; simpa only [cx] using congrArg c e
  let S := univ.erase o
  let P := part c o
  let K := S.image x
  have hK : G.IsNClique (k-3) K := by
    constructor
    · intro v hv w hw ne
      obtain ⟨i,_,rfl⟩ := mem_image.mp hv
      obtain ⟨j,_,rfl⟩ := mem_image.mp hw
      exact hcl _ _ (fun e => ne (congrArg x e))
    · rw [show K=S.image x from rfl,card_image_of_injective _ inj]
      simp [S,card_erase_of_mem,dim]; omega
  let bset := ((U q).filter fun v => ¬G.Adj (x o) v) ∪ {x q}
  have blim : bset.card ≤ m o+1 := by
    apply (card_union_le ..).trans
    simpa using Nat.add_le_add_right ((fail_le G c (fiber q) (by rw [cx]; exact hqo.symm)).trans (good o _ (hx o))) 1
  have mo : m o ≤ ∑ j, m j := by exact single_le_sum (f:=m) (fun _ _ => Nat.zero_le _) (mem_univ o)
  obtain ⟨u,hu,notbad⟩ := not_subset.mp (fun sub : U q ⊆ bset => by
    have := (card_le_card sub).trans blim; have := size q; omega)
  have cu := fiber q u hu
  have ux : u ≠ x q := by intro e; exact notbad (mem_union_right _ (mem_singleton.mpr e))
  have axu : G.Adj (x o) u := by by_contra h; exact notbad (mem_union_left _ (mem_filter.mpr ⟨hu,h⟩))
  have notK : u∉K := by
    intro mem
    obtain ⟨i,_,e⟩ := mem_image.mp mem
    have eq : i=q := by simpa only [cx,cu] using congrArg c e
    exact ux (eq ▸ e.symm)
  let F (v : V) := P.filter fun w => ¬G.Adj v w
  let blocked := (S.biUnion fun j => F (x j)) ∪ F u
  let W := P \ blocked
  have pf (v) (hv : v∈P) : c v=o := (mem_filter.mp hv).2
  have bcap : blocked.card ≤ (∑ j ∈ S,m j)+m q := by
    apply (card_union_le ..).trans
    apply Nat.add_le_add ((card_biUnion_le).trans (sum_le_sum ?_))
    · exact (fail_le G c pf (cu ▸ hqo)).trans (good q u hu)
    · intro j hj
      exact (fail_le G c pf (by rw [cx]; exact ne_of_mem_erase hj)).trans (good j _ (hx j))
  have ws : P.card ≤ W.card+((∑ j ∈ S,m j)+m q) :=
    (card_le_card_sdiff_add_card (s:=P) (t:=blocked)).trans (Nat.add_le_add_left bcap _)
  have desc (w : V) : w∈W ↔ w∈P ∧ (∀ j∈S,G.Adj (x j) w) ∧ G.Adj u w := by
    simp [W,blocked,F]; tauto
  have xmem : x o∈W := (desc _).mpr ⟨mem_filter.mpr ⟨mem_univ _,cx o⟩,
    fun j hj => hcl j o (ne_of_mem_erase hj),axu.symm⟩
  let Y := (univ \ P).filter fun w => G.Adj (x o) w
  have dis : Disjoint W Y := by
    rw [Finset.disjoint_left]; intro w hw hy
    exact (mem_sdiff.mp (mem_filter.mp hy).1).2 ((desc _).mp hw).1
  have vis (y) (hy : y∈Y) : G.Adj (x o) y := (mem_filter.mp hy).2
  have core (w) (hw : w∈W) : G.Adj u w ∧ ∀ v∈K,G.Adj v w := by
    obtain ⟨_,ha,hb⟩ := (desc _).mp hw
    refine ⟨hb,?_⟩
    intro v hv; obtain ⟨j,hj,rfl⟩ := mem_image.mp hv; exact ha j hj
  have mass := OMA.Structural917.counting hk crit K W Y u hK notK core ⟨x o,xmem⟩ dis vis
  have outside : ((univ \ P).filter (fun w => ¬G.Adj (x o) w)).card ≤ m o := by
    apply (card_le_card ?_).trans (good o _ (hx o))
    intro w hw
    obtain ⟨hn,ha⟩ := mem_filter.mp hw
    have hnp := (mem_sdiff.mp hn).2
    exact mem_filter.mpr ⟨mem_univ _,by rw [cx]; exact ⟨fun e => hnp (mem_filter.mpr ⟨mem_univ _,e⟩),ha⟩⟩
  have sumo := card_filter_add_card_filter_not (s:=univ \ P) (p:=fun w => G.Adj (x o) w)
  have total := card_sdiff_add_card_eq_card (subset_univ P)
  rw [card_univ] at total
  change Y.card+_=_ at sumo
  change P.card ≤ _
  change P.card ≤ 3+2*((∑ j ∈ S,m j)+m q)+m o
  omega

end OMA.Transversal917

/-! Quantify the slack in the proof of the Luo–Ma–Yang density bound. -/
namespace OMA.Scalar917
open Finset SimpleGraph Filter OMA.Transversal917
open scoped Classical

private theorem parameters (r A : ℝ) (hr : 2≤r) (hA : 0<A) :
    ∀ᶠ n : ℝ in atTop,
      let B := n/(3*(r+1))
      let E := 24*(r+1)*A
      let t := n^2/(36*(r+1)^2)+A*(n+1)
      0<B ∧ 4*t ≤ B*(B+E) ∧ 4*t ≤ (B+E)^2 ∧
      3*B+2*E+2 < n/r ∧ (2+2/(r-1))*(B+E)+3 < n/r := by
  have rp : 0<r := by linarith
  have r1 : 0<r+1 := by linarith
  have r0 : 0<r-1 := by linarith
  have s₁ : 0<1/r-1/(r+1) := by
    field_simp; nlinarith
  have s₂ : 0<1/r-(2+2/(r-1))/(3*(r+1)) := by
    field_simp; nlinarith [mul_self_nonneg (r-2)]
  let E := 24*(r+1)*A
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (tendsto_id.const_mul_atTop s₁).eventually_gt_atTop (2*E+2),
    (tendsto_id.const_mul_atTop s₂).eventually_gt_atTop ((2+2/(r-1))*E+3)] with n hn h₁ h₂
  change (1/r-1/(r+1))*n > 2*E+2 at h₁
  change (1/r-(2+2/(r-1))/(3*(r+1)))*n > (2+2/(r-1))*E+3 at h₂
  let B := n/(3*(r+1))
  have bp : 0<B := by dsimp [B]; positivity
  have ep : 0<E := by dsimp [E]; positivity
  have sq : 4*(n^2/(36*(r+1)^2)) = B^2 := by dsimp [B]; field_simp; ring
  have prod : B*E = 8*n*A := by dsimp [B,E]; field_simp; ring
  have part1 : 4*(n^2/(36*(r+1)^2)+A*(n+1)) ≤ B*(B+E) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) hA.le]
  refine ⟨bp,part1,part1.trans ?_,?_,?_⟩
  · nlinarith [mul_nonneg bp.le ep.le,sq_nonneg E]
  · change 3*B+2*E+2<n/r
    rw [show 3*B=n/(r+1) by dsimp [B]; field_simp]
    ring_nf at h₁ ⊢; linarith
  · change (2+2/(r-1))*(B+E)+3<n/r
    dsimp [B]; ring_nf at h₂ ⊢; linarith

theorem impossible (r : ℕ) (hr : 2≤r) (A : ℝ) (hA : 0<A) :
    ∀ᶠ n : ℕ in atTop, ∀ (G : SimpleGraph (Fin n)) (c : Fin n → Fin r),
    Erdos917.IsKCritical G (r+2) →
    (let t := (n:ℝ)^2/(36*((r:ℝ)+1)^2)+A*((n:ℝ)+1)
     ((∑ v, (misses G c v).card : ℕ):ℝ) ≤ 4*t →
     (∀ i, (((part c i).card:ℝ)-(n:ℝ)/r)^2 ≤ 4*t) → False) := by
  classical
  filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (parameters r A (by exact_mod_cast hr) hA),
    eventually_ge_atTop 1] with n pars npos
  intro G c crit
  let B := (n:ℝ)/(3*((r:ℝ)+1))
  let E := 24*((r:ℝ)+1)*A
  let t := (n:ℝ)^2/(36*((r:ℝ)+1)^2)+A*((n:ℝ)+1)
  obtain ⟨(bp : 0<B),(bound₁ : 4*t≤B*(B+E)),(bound₂ : 4*t≤(B+E)^2),h₁,h₂⟩ := pars
  change 3*B+2*E+2 < (n:ℝ)/r at h₁
  change (2+2/((r:ℝ)-1))*(B+E)+3 < (n:ℝ)/r at h₂
  change ((∑ v, (misses G c v).card : ℕ):ℝ) ≤ 4*t →
    (∀ i, (((part c i).card:ℝ)-(n:ℝ)/r)^2 ≤ 4*t) → False
  intro misses' variance
  have ep : 0<E := by dsimp [E]; positivity
  let b := ⌈B⌉₊
  have blo : B≤(b:ℝ) := Nat.le_ceil _
  have bhi : (b:ℝ)<B+1 := Nat.ceil_lt_add_one bp.le
  have lower (i : Fin r) : (n:ℝ)/r-(B+E) ≤ (part c i).card := by
    have hh := (variance i).trans bound₂
    by_contra! h
    nlinarith [sq_nonneg (((n:ℝ)/r-(part c i).card) - (B+E)),
      mul_pos (by linarith : 0 < (n:ℝ)/r-(part c i).card-(B+E))
        (by linarith : 0 < (n:ℝ)/r-(part c i).card+(B+E))]
  let d := fun v => (misses G c v).card
  have bfit (i : Fin r) : b ≤ (part c i).card := by
    exact_mod_cast (by linarith [lower i] : (b:ℝ) ≤ (part c i).card)
  obtain ⟨U,m,sub,cardU,good,hprod⟩ := OMA.Trim917.trim c d b bfit
  have mcap : ((∑ j,m j : ℕ):ℝ) ≤ B+E := by
    have mul' : (b:ℝ)*((∑ j,m j : ℕ):ℝ) ≤ (∑ v,d v : ℕ) := by exact_mod_cast hprod
    have := (mul_le_mul_of_nonneg_right blo (Nat.cast_nonneg (∑ j,m j) : (0:ℝ)≤_)).trans
      (mul'.trans (misses'.trans bound₁))
    exact (le_of_mul_le_mul_left this bp)
  have size (i : Fin r) : (∑ j,m j)+1 < (U i).card := by
    have cu : ((U i).card:ℝ)+b=(part c i).card := by exact_mod_cast cardU i
    exact_mod_cast (by linarith [lower i] : ((∑ j,m j : ℕ):ℝ)+1 < (U i).card)
  let : Nonempty (Fin r) := ⟨⟨0,by omega⟩⟩
  let : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  obtain ⟨o,ho,maxi⟩ := exists_max_image (univ : Finset (Fin r)) (fun i => (part c i).card) univ_nonempty
  have allparts : ∑ i, (part c i).card = n := by
    simpa [part] using (sum_card_fiberwise_eq_card_filter (univ : Finset (Fin n)) (univ : Finset (Fin r)) c)
  have om : (n:ℝ)/r ≤ (part c o).card := by
    apply (div_le_iff₀ (by exact_mod_cast (show 0<r by omega))).mpr
    have hh := sum_le_sum (f:=fun i => (part c i).card) (g:=fun _ => (part c o).card) (s:=univ) (fun i hi => maxi i hi)
    rw [allparts,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_comm] at hh
    exact_mod_cast hh
  let S := (univ : Finset (Fin r)).erase o
  have cs : S.card=r-1 := by simp [S]
  have ns : S.Nonempty := card_pos.mp (by rw [cs]; omega)
  obtain ⟨q,hq,minq⟩ := exists_min_image S m ns
  have small := sum_le_sum (s:=S) (f:=fun _ => m q) (g:=m) minq
  rw [sum_const,cs,nsmul_eq_mul] at small
  have ob := obstruction (k:=r+2) (by omega) (by simp) G crit c U m o q (ne_of_mem_erase hq)
    (fun i v hv => (mem_filter.mp (sub i hv)).2) good size
  let M := (∑ i ∈ S,m i : ℕ)
  change (part c o).card ≤ 3+2*(M+m q)+m o at ob
  have r2 : (2:ℝ)≤r := by exact_mod_cast hr
  have rp : 0<(r:ℝ)-1 := by linarith
  have small' : ((r:ℝ)-1)*(m q:ℝ) ≤ M := by
    have hh : (((r-1:ℕ):ℝ))*(m q:ℝ) ≤ M := by exact_mod_cast (show (r-1)*m q ≤ M from small)
    simpa only [Nat.cast_sub (show 1≤r by omega),Nat.cast_one] using hh
  have qle := (le_div_iff₀ rp).mpr (by linarith only [small'] : (m q:ℝ)*((r:ℝ)-1) ≤ M)
  have sums : M+m o=∑ j,m j := sum_erase_add _ _ (mem_univ o)
  have sums' : (M:ℝ)+m o=((∑ j,m j : ℕ):ℝ) := by exact_mod_cast sums
  have ob' : ((part c o).card:ℝ) ≤ 3+2*((M:ℝ)+m q)+m o := by exact_mod_cast ob
  have coeff : 0≤2+2/((r:ℝ)-1) := by positivity
  have loss := mul_le_mul_of_nonneg_left mcap coeff
  have em : 0≤(m o:ℝ)/((r:ℝ)-1) := by positivity
  rw [← sums'] at loss
  ring_nf at loss qle h₂ em om
  linarith [Nat.cast_nonneg (α:=ℝ) (m o)]

end OMA.Scalar917

/-! Putting together the clique removal, stability and critical-graph
obstruction for Theorem 1.1 of Luo, Ma and Yang. -/

namespace OMA.Assemble917
open SimpleGraph Finset Filter
open scoped Classical
open OMA.Transversal917 OMA.Stability917

private theorem missing_sum {n r : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → Fin r) :
    (∑ v, (misses G c v).card) = 2*(K c \ G).edgeFinset.card := by
  have hand := (K c \ G).sum_degrees_eq_twice_card_edges
  simp only [edgeFinset,← Set.ncard_eq_toFinset_card'] at hand ⊢
  rw [← hand]
  apply sum_congr rfl
  intro v _
  unfold misses degree
  rw [neighborFinset_eq_filter]
  congr 1
  ext w
  simp only [mem_filter,mem_univ,true_and,sdiff_adj]
  change (c w ≠ c v ∧ ¬G.Adj v w) ↔ (c v ≠ c w ∧ ¬G.Adj v w)
  exact and_congr_left' ne_comm

private theorem extremal {k n : ℕ} {z : ℝ} (hz : 0 ≤ z)
    (all : ∀ G : SimpleGraph (Fin n), Erdos917.IsKCritical G k → (G.edgeFinset.card : ℝ) ≤ z) :
    (Erdos917.f k n : ℝ) ≤ z := by
  let M := {m : ℕ | ∃ G : SimpleGraph (Fin n), Erdos917.IsKCritical G k ∧ G.edgeSet.ncard=m}
  change (sSup M : ℕ) ≤ z
  rcases M.eq_empty_or_nonempty with he|hn
  · simpa [he] using hz
  · have sub : M ⊆ Set.Iic (Nat.card (Sym2 (Fin n))) := by
      rintro m ⟨G,_,rfl⟩
      exact Set.ncard_le_card _
    obtain ⟨G,hG,he⟩ := hn.csSup_mem ((Set.finite_Iic _).subset sub)
    rw [← he, Set.ncard_eq_toFinset_card']
    exact all G hG

private theorem dense_parts {n r : ℕ} (hr : 2≤r) (G : SimpleGraph (Fin n))
    (crit : Erdos917.IsKCritical G (r+2))
    (round : (1-1/(r:ℝ))*(n:ℝ)^2/2-((r:ℝ)^2+1) ≤
      (extremalNumber n (completeGraph (Fin (r+1))) : ℝ))
    (large : (extremalNumber n (completeGraph (Fin (r+1))) : ℝ) -
      (n:ℝ)^2/(36*((r:ℝ)+1)^2) < G.edgeFinset.card) :
    let t := (n:ℝ)^2/(36*((r:ℝ)+1)^2) +
      (((r:ℝ)+1)^2+(r:ℝ)^2+2)*((n:ℝ)+1)
    ∃ c : Fin n → Fin r, ((∑ v, (misses G c v).card : ℕ):ℝ) ≤ 4*t ∧
      ∀ i, (((part c i).card:ℝ)-(n:ℝ)/r)^2 ≤ 4*t := by
  intro t
  obtain ⟨E,small,free⟩ := OMA.Removal917.removal (r:=r+1) (by omega) G crit
  let H := G.deleteEdges E
  have hle : H ≤ G := deleteEdges_le ..
  have loss : G.edgeFinset.card ≤ H.edgeFinset.card + E.card := by
    simpa only [H,edgeFinset_deleteEdges] using
      card_le_card_sdiff_add_card (s:=G.edgeFinset) (t:=E)
  have sl : (E.card:ℝ) ≤ ((n:ℝ)+1)*((r:ℝ)+1)^2 := by exact_mod_cast small
  have ls : (G.edgeFinset.card:ℝ) ≤ H.edgeFinset.card + (E.card:ℝ) := by exact_mod_cast loss
  have dense : (1-1/(r:ℝ))*(n:ℝ)^2/2-t ≤ H.edgeFinset.card := by
    dsimp [t]
    nlinarith only [round,large,sl,ls, (show 0≤(n:ℝ) by positivity),
      mul_nonneg (sq_nonneg (r:ℝ)) (show 0≤(n:ℝ) by positivity)]
  obtain ⟨c,hcross,hvar⟩ := deficit (t:=t) (by omega : 0<r) H free
    (by simpa only [edgeFinset,← Set.ncard_eq_toFinset_card'] using dense)
  refine ⟨c,?_,?_⟩
  · have mon : K c \ G ≤ K c \ H := by
      intro v w ha
      exact ⟨ha.1,fun e => ha.2 (hle e)⟩
    have cardmon : ((K c \ G).edgeFinset.card:ℝ) ≤ (K c \ H).edgeFinset.card := by
      exact_mod_cast card_le_card (edgeFinset_mono mon)
    rw [missing_sum, Nat.cast_mul, Nat.cast_ofNat]
    simp only [edgeFinset,← Set.ncard_eq_toFinset_card'] at cardmon hcross ⊢
    linarith
  · intro i
    have hterm := single_le_sum (s:=univ)
      (f:=fun j : Fin r => (((univ.filter fun x => c x=j).card:ℝ)-(n:ℝ)/r)^2)
      (fun j _ => sq_nonneg _) (mem_univ i)
    change (((univ.filter fun x => c x=i).card:ℝ)-(n:ℝ)/r)^2 ≤ 4*t
    nlinarith only [hterm,hvar,sq_nonneg (((univ.filter fun x => c x=i).card:ℝ)-(n:ℝ)/r)]

/-- Passage from the obstruction in each critical graph to the extremal
function, including orders where the family of critical graphs is empty. -/
theorem upper_of_obstruction
    (no_partition : ∀ (r : ℕ), 2 ≤ r → ∀ A : ℝ, 0<A →
      ∀ᶠ n : ℕ in atTop, ∀ (G : SimpleGraph (Fin n)) (c : Fin n → Fin r),
        Erdos917.IsKCritical G (r+2) →
        (let t := (n:ℝ)^2/(36*((r:ℝ)+1)^2)+A*((n:ℝ)+1)
         ((∑ v, (misses G c v).card : ℕ):ℝ) ≤ 4*t →
         (∀ i, (((part c i).card:ℝ)-(n:ℝ)/r)^2 ≤ 4*t) → False)) :
    type_of% @Erdos917.erdos_917.variants.luo_ma_yang := by
  intro k hk
  obtain ⟨r,rfl⟩ : ∃ r, k=r+2 := ⟨k-2,by omega⟩
  have hr : 2≤r := by omega
  let A := ((r:ℝ)+1)^2+(r:ℝ)^2+2
  have pos : 0<A := by dsimp [A]; positivity
  filter_upwards [no_partition r hr A pos, OMA.Round917.nonnegative r hr] with n no hnon
  have idx : r+2-1=r+1 := by omega
  have coef : ((r+2:ℕ):ℝ)-1=(r:ℝ)+1 := by push_cast; ring
  rw [idx,coef]
  apply extremal hnon
  intro G hG
  by_contra! large
  obtain ⟨c,hm,hv⟩ := dense_parts hr G hG (OMA.Round917.rounding n r hr).1 large
  exact no G c hG hm hv

theorem luo_ma_yang : type_of% @Erdos917.erdos_917.variants.luo_ma_yang :=
  upper_of_obstruction OMA.Scalar917.impossible

theorem stiebitz_of_lmy
    (lmy : type_of% @Erdos917.erdos_917.variants.luo_ma_yang) :
    type_of% @Erdos917.erdos_917.variants.stiebitz_upper := by
  intro k hk
  filter_upwards [lmy k hk,eventually_ge_atTop 1] with n h hn
  have hk' : 1 < (k:ℝ) := by exact_mod_cast (show 1<k by omega)
  have hn' : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have pos : 0 < (n:ℝ)^2/(36*((k:ℝ)-1)^2) := by
    exact div_pos (sq_pos_of_pos hn') (mul_pos (by norm_num) (sq_pos_of_pos (by linarith)))
  exact_mod_cast (lt_of_le_of_lt h (sub_lt_self _ pos))

theorem stiebitz : type_of% @Erdos917.erdos_917.variants.stiebitz_upper :=
  stiebitz_of_lmy luo_ma_yang

end OMA.Assemble917

theorem OMA.solution : type_of% @Erdos917.erdos_917.variants.luo_ma_yang :=
  OMA.Assemble917.luo_ma_yang
