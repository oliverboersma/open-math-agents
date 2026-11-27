import OMAReductions.R_Erdos81_erdos_81_R1
import Mathlib

/-!
Dirac's two-simplicial-vertices theorem for finite chordal graphs.

The proof constructs an inclusion-minimal vertex separator, proves that it is
a clique by ruling out a chordless cycle, and inducts on the vertex set.
Reference: G. A. Dirac, On rigid circuit graphs (1961), pp. 71–76.
This completes both separator ingredients of reduction PR #7530.
Credit: @rgoldman73-dev.
-/
namespace OMA.ChordalSeparators
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

lemma cycle_adj_iff_succ {n : ℕ} [NeZero n] (hn : 2 ≤ n) (i j : Fin n) :
    (cycleGraph n).Adj i j ↔ i + 1 = j ∨ j + 1 = i := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simp only [cycleGraph_adj, sub_eq_iff_eq_add]
  constructor
  · rintro (h | h)
    · exact Or.inr (by simpa [add_comm] using h.symm)
    · exact Or.inl (by simpa [add_comm] using h.symm)
  · rintro (h | h)
    · exact Or.inr (by simpa [add_comm] using h.symm)
    · exact Or.inl (by simpa [add_comm] using h.symm)

lemma cycle_getVert_succ {a : V} (p : G.Walk a a) [NeZero p.length] (hp : p.IsCycle) (i : Fin p.length) :
    p.getVert (i + 1 : Fin p.length).val = p.getVert (i.val + 1) := by
  have hl := hp.three_le_length
  have hone : (1 : Fin p.length).val = 1 := by simp [Nat.mod_eq_of_lt (by omega : 1 < p.length)]
  rw [Fin.val_add, hone]
  by_cases h : i.val + 1 < p.length
  · rw [Nat.mod_eq_of_lt h]
  · have he : i.val + 1 = p.length := by omega
    simp [he]

lemma induced_cycle_of_chordless {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    (hc : p.IsChordless) : (cycleGraph p.length).IsIndContained G := by
  have hl := hp.three_le_length
  let : NeZero p.length := ⟨by omega⟩
  let f : Fin p.length → V := fun i => p.getVert i.val
  have hinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact hp.getVert_injOn' (by have := i.isLt; simp only [Set.mem_ofPred_eq]; omega)
      (by have := j.isLt; simp only [Set.mem_ofPred_eq]; omega) hij
  have hadj : ∀ i : Fin p.length, G.Adj (f i) (f (i + 1)) := by
    intro i
    dsimp [f]
    rw [cycle_getVert_succ p hp i]
    exact p.adj_getVert_succ i.isLt
  refine ⟨⟨⟨f, hinj⟩, ?_⟩⟩
  intro i j
  rw [cycle_adj_iff_succ (by omega)]
  constructor
  · intro hij
    have he := hc.mem_edges (p.getVert_mem_support i.val) (p.getVert_mem_support j.val) hij
    obtain ⟨k, hk, he⟩ := (p.mk_mem_edges_iff_exists).mp he
    let t : Fin p.length := ⟨k, hk⟩
    have he' : s(f t, f (t + 1)) = s(f i, f j) := by
      simpa only [f, cycle_getVert_succ p hp, t] using he
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at he'
    rcases he' with ⟨hti, htj⟩ | ⟨htj, hti⟩
    · have hti' := hinj hti
      have htj' := hinj htj
      exact Or.inl (hti' ▸ htj')
    · have htj' := hinj htj
      have hti' := hinj hti
      exact Or.inr (htj' ▸ hti')
  · rintro (h | h)
    · exact h ▸ hadj i
    · exact (h ▸ hadj j).symm

lemma shortest_isChordless {a b : V} (p : G.Walk a b) (hp : p.length = G.dist a b) :
    p.IsChordless := by
  have key : ∀ i j : ℕ, i ≤ j → j ≤ p.length → G.Adj (p.getVert i) (p.getVert j) →
      s(p.getVert i, p.getVert j) ∈ p.edges := by
    intro i j hij hj hAdj
    let q := (p.take i).append (hAdj.toWalk.append (p.drop j))
    have hmin := dist_le q
    rw [← hp] at hmin
    simp only [q, Walk.length_append, Walk.take_length, Adj.length_toWalk,
      Walk.drop_length] at hmin
    have hne : i ≠ j := fun h => hAdj.ne (congrArg p.getVert h)
    have he : j = i + 1 := by omega
    exact (p.mk_mem_edges_iff_exists).mpr ⟨i, by omega, by rw [he]⟩
  apply Walk.isChordless_iff_forall_mem_edges.mpr
  intro x y hx hy hxy
  obtain ⟨i, hi, hil⟩ := p.mem_support_iff_exists_getVert.mp hx
  obtain ⟨j, hj, hjl⟩ := p.mem_support_iff_exists_getVert.mp hy
  rw [← hi, ← hj] at hxy ⊢
  rcases le_total i j with hij | hji
  · exact key i j hij hjl hxy
  · simpa only [Sym2.eq_swap] using key j i hji hil hxy.symm

lemma chordal_no_chordless_cycle (hG : G.IsChordal) {a : V} (p : G.Walk a a)
    (hp : p.IsCycle) (hl : 4 ≤ p.length) : ¬ p.IsChordless := by
  intro hc
  exact hG p.length hl (induced_cycle_of_chordless p hp hc)

end OMA.ChordalSeparators
namespace OMA.ChordalSeparators
open SimpleGraph
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

lemma chordless_map (f : G ↪g H) {a b : V} (p : G.Walk a b)
    (hp : p.IsChordless) : (p.map f.toHom).IsChordless := by
  apply Walk.isChordless_iff_forall_mem_edges.mpr
  intro x y hx hy hxy
  simp only [Walk.support_map, List.mem_map] at hx hy
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  have hxy' : G.Adj x' y' := f.map_adj_iff.mp hxy
  rw [Walk.edges_map]
  exact List.mem_map.mpr ⟨s(x', y'), hp.mem_edges hx' hy' hxy', rfl⟩

lemma exists_chordless_path_inside {a b : V} (T : Set V) (w : G.Walk a b)
    (hw : ∀ x ∈ w.support, x ∈ T) :
    ∃ p : G.Walk a b, p.IsPath ∧ p.IsChordless ∧ ∀ x ∈ p.support, x ∈ T := by
  let wi := w.induce T hw
  obtain ⟨q, hq, hlen⟩ := wi.reachable.exists_path_of_dist
  have hinside : ∀ x ∈ (q.map (Embedding.induce T).toHom).support, x ∈ T := by
    intro x hx
    rw [Walk.support_map] at hx
    obtain ⟨x', _, rfl⟩ := List.mem_map.mp hx
    exact x'.property
  exact ⟨q.map (Embedding.induce T).toHom, hq.map Subtype.val_injective,
    chordless_map (Embedding.induce T) q (shortest_isChordless q hlen), hinside⟩

end OMA.ChordalSeparators

/- Finite vertex separators and their two sides. -/
namespace OMA.ChordalSeparators
open Finset SimpleGraph
variable {V : Type*}

def Separates (G : SimpleGraph V) (S C : Finset V) (a b : V) : Prop :=
  C ⊆ S ∧ a ∉ C ∧ b ∉ C ∧
    ∀ w : G.Walk a b, (∀ x ∈ w.support, x ∈ S) → ∃ x ∈ w.support, x ∈ C

def MinimalSeparator (G : SimpleGraph V) (S C : Finset V) (a b : V) : Prop :=
  Separates G S C a b ∧ ∀ D : Finset V, D ⊆ C → Separates G S D a b → C ⊆ D

def ReachesAvoiding (G : SimpleGraph V) (S C : Finset V) (a x : V) : Prop :=
  ∃ w : G.Walk a x, ∀ y ∈ w.support, y ∈ S ∧ y ∉ C

lemma walk_has_interior {G : SimpleGraph V} {a b : V}
    (hab : a ≠ b) (hnab : ¬ G.Adj a b) (w : G.Walk a b) :
    ∃ x ∈ w.support, x ≠ a ∧ x ≠ b := by
  cases w with
  | nil => exact (hab rfl).elim
  | @cons _ c _ hac w =>
    refine ⟨c, ?_, hac.ne.symm, fun h => hnab (h ▸ hac)⟩
    simp [w.start_mem_support]

lemma exists_minimal_separator (G : SimpleGraph V) (S : Finset V) (a b : V)
    (hab : a ≠ b) (hnab : ¬ G.Adj a b) :
    ∃ C : Finset V, MinimalSeparator G S C a b := by
  classical
  have hfull : Separates G S (S \ {a, b}) a b := by
    refine ⟨sdiff_subset, by simp, by simp, ?_⟩
    intro w hw
    obtain ⟨x, hx, hxa, hxb⟩ := walk_has_interior hab hnab w
    exact ⟨x, hx, mem_sdiff.mpr ⟨hw x hx, by simp [hxa, hxb]⟩⟩
  let family := S.powerset.filter (fun C => Separates G S C a b)
  have hfamily : family.Nonempty :=
    ⟨S \ {a, b}, mem_filter.mpr ⟨mem_powerset.mpr sdiff_subset, hfull⟩⟩
  obtain ⟨C, hC, hmin⟩ := exists_min_image family Finset.card hfamily
  have hsep : Separates G S C a b := (mem_filter.mp hC).2
  refine ⟨C, hsep, ?_⟩
  intro D hDC hD
  have hcD : C.card ≤ D.card :=
    hmin D (mem_filter.mpr ⟨mem_powerset.mpr hD.1, hD⟩)
  exact (Finset.eq_of_subset_of_card_le hDC hcD).ge

lemma separator_sides [DecidableEq V] (G : SimpleGraph V) (S C : Finset V) (a b : V)
    (ha : a ∈ S) (hb : b ∈ S) (hsep : Separates G S C a b) :
    ∃ L R : Finset V, S = L ∪ R ∪ C ∧
      Disjoint L R ∧ Disjoint L C ∧ Disjoint R C ∧ a ∈ L ∧ b ∈ R ∧
      (∀ x ∈ L, ∀ y ∈ R, ¬ G.Adj x y) := by
  classical
  let L := S.filter (ReachesAvoiding G S C a)
  let R := S \ (L ∪ C)
  have hLS : L ⊆ S := filter_subset _ _
  have hLC : ∀ x ∈ L, x ∉ C := by
    intro x hx
    obtain ⟨w, hw⟩ := (mem_filter.mp hx).2
    exact (hw x w.end_mem_support).2
  have haL : a ∈ L := by
    refine mem_filter.mpr ⟨ha, .intro .nil ?_⟩
    intro x hx
    have hxa : x = a := by simpa using hx
    subst x
    exact ⟨ha, hsep.2.1⟩
  have hbL : b ∉ L := by
    intro hbL
    obtain ⟨w, hw⟩ := (mem_filter.mp hbL).2
    obtain ⟨x, hx, hxC⟩ := hsep.2.2.2 w (fun y hy => (hw y hy).1)
    exact (hw x hx).2 hxC
  refine ⟨L, R, ?_, ?_, ?_, ?_, haL, ?_, ?_⟩
  · ext x
    simp only [mem_union, R, mem_sdiff]
    constructor
    · intro hx
      by_cases hxL : x ∈ L
      · exact Or.inl (Or.inl hxL)
      · by_cases hxC : x ∈ C
        · exact Or.inr hxC
        · exact Or.inl (Or.inr ⟨hx, by simp [hxL, hxC]⟩)
    · rintro ((hx | hx) | hx)
      · exact hLS hx
      · exact hx.1
      · exact hsep.1 hx
  · apply Finset.disjoint_left.mpr
    intro x hxL hxR
    exact (mem_sdiff.mp hxR).2 (mem_union_left C hxL)
  · exact Finset.disjoint_left.mpr (fun x hxL hxC => hLC x hxL hxC)
  · apply Finset.disjoint_left.mpr
    intro x hxR hxC
    exact (mem_sdiff.mp hxR).2 (mem_union_right L hxC)
  · exact mem_sdiff.mpr ⟨hb, by simp [hbL, hsep.2.2.1]⟩
  · intro x hxL y hyR hxy
    obtain ⟨w, hw⟩ := (mem_filter.mp hxL).2
    have hyS : y ∈ S := (mem_sdiff.mp hyR).1
    have hyC : y ∉ C := fun hyC => (mem_sdiff.mp hyR).2 (mem_union_right L hyC)
    have hyL : y ∈ L := by
      refine mem_filter.mpr ⟨hyS, w.concat hxy, ?_⟩
      intro z hz
      simp only [Walk.support_concat, List.mem_append, List.mem_singleton] at hz
      rcases hz with hz | rfl
      · exact hw z hz
      · exact ⟨hyS, hyC⟩
    exact (mem_sdiff.mp hyR).2 (mem_union_left C hyL)

lemma finite_separator_exists [DecidableEq V] (G : SimpleGraph V) (S : Finset V) (a b : V)
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (hnab : ¬ G.Adj a b) :
    ∃ L R C : Finset V, S = L ∪ R ∪ C ∧
      Disjoint L R ∧ Disjoint L C ∧ Disjoint R C ∧ a ∈ L ∧ b ∈ R ∧
      (∀ x ∈ L, ∀ y ∈ R, ¬ G.Adj x y) ∧ MinimalSeparator G S C a b := by
  classical
  obtain ⟨C, hC⟩ := exists_minimal_separator G S a b hab hnab
  obtain ⟨L, R, hp, hLR, hLC, hRC, haL, hbR, hcross⟩ := separator_sides G S C a b ha hb hC.1
  exact ⟨L, R, C, hp, hLR, hLC, hRC, haL, hbR, hcross, hC⟩

end OMA.ChordalSeparators
namespace OMA.ChordalSeparators
open Finset SimpleGraph
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma minimal_separator_path {S C : Finset V} {a b c : V}
    (hmin : MinimalSeparator G S C a b) (hc : c ∈ C) :
    ∃ p : G.Walk a b, p.IsPath ∧ c ∈ p.support ∧
      ∀ x ∈ p.support, x ∈ S ∧ (x ∈ C → x = c) := by
  classical
  have hnot : ¬ Separates G S (C.erase c) a b := by
    intro h
    exact notMem_erase c C (hmin.2 (C.erase c) (erase_subset c C) h hc)
  have hex : ∃ w : G.Walk a b, (∀ x ∈ w.support, x ∈ S) ∧
      ∀ x ∈ w.support, x ∉ C.erase c := by
    by_contra! h
    apply hnot
    refine ⟨(erase_subset c C).trans hmin.1.1, ?_, ?_, ?_⟩
    · exact fun ha => hmin.1.2.1 (mem_of_mem_erase ha)
    · exact fun hb => hmin.1.2.2.1 (mem_of_mem_erase hb)
    · intro w hw
      simpa using h w hw
  obtain ⟨w, hwS, hwC⟩ := hex
  have hpS : ∀ x ∈ w.bypass.support, x ∈ S ∧ (x ∈ C → x = c) := by
    intro x hx
    have hxw := w.support_bypass_subset_support hx
    refine ⟨hwS x hxw, ?_⟩
    intro hxC
    by_contra hxc
    exact hwC x hxw (mem_erase.mpr ⟨hxc, hxC⟩)
  have hcP : c ∈ w.bypass.support := by
    obtain ⟨x, hx, hxC⟩ := hmin.1.2.2.2 w.bypass (fun y hy => (hpS y hy).1)
    exact (hpS x hx).2 hxC ▸ hx
  exact ⟨w.bypass, w.bypass_isPath, hcP, hpS⟩

lemma path_stays_side {S L R C : Finset V}
    (hS : S = L ∪ R ∪ C) (hcross : ∀ x ∈ L, ∀ y ∈ R, ¬ G.Adj x y)
    {a c : V} (p : G.Walk a c) :
    p.IsPath → a ∈ L → (∀ x ∈ p.support, x ∈ S ∧ (x ∈ C → x = c)) →
      ∀ x ∈ p.support, x ∈ L ∨ x = c := by
  induction p with
  | nil =>
    intro _ _ _ x hx
    exact Or.inr (by simpa using hx)
  | @cons a d c had w ih =>
    intro hp ha hw
    have hpw : w.IsPath := hp.of_cons
    have hw' : ∀ x ∈ w.support, x ∈ S ∧ (x ∈ C → x = c) := by
      intro x hx
      exact hw x (by simp [hx])
    by_cases hdc : d = c
    · subst d
      have hn : w = .nil := (Walk.isPath_iff_nil.mp hpw).eq_nil
      subst w
      intro x hx
      simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact Or.inl ha
      · exact Or.inr rfl
    · have hdC : d ∉ C := fun h => hdc ((hw' d w.start_mem_support).2 h)
      have hdS := (hw' d w.start_mem_support).1
      rw [hS] at hdS
      have hdL : d ∈ L := by
        rcases mem_union.mp hdS with hd | hd
        · rcases mem_union.mp hd with hd | hd
          · exact hd
          · exact (hcross a ha d hd had).elim
        · exact (hdC hd).elim
      intro x hx
      simp only [Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Or.inl ha
      · exact ih hpw hdL hw' x hx

end OMA.ChordalSeparators

namespace OMA.ChordalSeparators
open Finset SimpleGraph
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma separator_vertex_paths {S L R C : Finset V} {a b c : V}
    (hS : S = L ∪ R ∪ C) (hcross : ∀ x ∈ L, ∀ y ∈ R, ¬ G.Adj x y)
    (ha : a ∈ L) (hb : b ∈ R) (hmin : MinimalSeparator G S C a b) (hc : c ∈ C) :
    (∃ p : G.Walk a c, ∀ x ∈ p.support, x ∈ L ∨ x = c) ∧
    (∃ q : G.Walk b c, ∀ x ∈ q.support, x ∈ R ∨ x = c) := by
  obtain ⟨p, hp, hcP, hw⟩ := minimal_separator_path hmin hc
  constructor
  · refine ⟨p.takeUntil c hcP, path_stays_side hS hcross _ (hp.takeUntil hcP) ha ?_⟩
    intro x hx
    exact hw x (p.support_takeUntil_subset_support hcP hx)
  · have hS' : S = R ∪ L ∪ C := by rwa [union_comm R L]
    have hcross' : ∀ x ∈ R, ∀ y ∈ L, ¬ G.Adj x y :=
      fun x hx y hy h => hcross y hy x hx h.symm
    refine ⟨(p.dropUntil c hcP).reverse,
      path_stays_side hS' hcross' _ (hp.dropUntil hcP).reverse hb ?_⟩
    intro x hx
    simp only [Walk.support_reverse, List.mem_reverse] at hx
    exact hw x (p.support_dropUntil_subset_support hcP hx)

omit [DecidableEq V] in
lemma path_between_through_side {X : Finset V} {a u v : V}
    (p : G.Walk a u) (q : G.Walk a v)
    (hp : ∀ x ∈ p.support, x ∈ X ∨ x = u)
    (hq : ∀ x ∈ q.support, x ∈ X ∨ x = v) :
    ∃ r : G.Walk u v, r.IsPath ∧ r.IsChordless ∧
      ∀ x ∈ r.support, x ∈ X ∨ x = u ∨ x = v := by
  apply exists_chordless_path_inside {x | x ∈ X ∨ x = u ∨ x = v} (p.reverse.append q)
  intro x hx
  simp only [Walk.mem_support_append_iff] at hx
  rcases hx with hx | hx
  · simp only [Walk.support_reverse, List.mem_reverse] at hx
    rcases hp x hx with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases hq x hx with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

end OMA.ChordalSeparators

namespace OMA.ChordalSeparators
open Finset SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

lemma cycle_from_two_sides {L R : Finset V} (hLR : Disjoint L R)
    (hcross : ∀ x ∈ L, ∀ y ∈ R, ¬ G.Adj x y) {u v : V}
    (huv : u ≠ v) (hnuv : ¬ G.Adj u v) (p q : G.Walk u v)
    (hp : p.IsPath) (hq : q.IsPath) (hcp : p.IsChordless) (hcq : q.IsChordless)
    (hpS : ∀ x ∈ p.support, x ∈ L ∨ x = u ∨ x = v)
    (hqS : ∀ x ∈ q.support, x ∈ R ∨ x = u ∨ x = v) :
    (p.append q.reverse).IsCycle ∧ 4 ≤ (p.append q.reverse).length ∧
      (p.append q.reverse).IsChordless := by
  have hinter : ∀ x ∈ p.support, x ∈ q.support → x = u ∨ x = v := by
    intro x hx hy
    rcases hpS x hx with hxL | h
    · rcases hqS x hy with hxR | h
      · exact (Finset.disjoint_left.mp hLR hxL hxR).elim
      · exact h
    · exact h
  have hpnot : u ∉ p.support.tail := by
    have h := hp.support_nodup
    rw [← p.cons_tail_support, List.nodup_cons] at h
    exact h.1
  have hqnot : v ∉ q.reverse.support.tail := by
    have h := hq.reverse.support_nodup
    rw [← q.reverse.cons_tail_support, List.nodup_cons] at h
    exact h.1
  have htail : p.support.tail.Disjoint q.reverse.support.tail := by
    intro x hx hy
    have hxP := List.mem_of_mem_tail hx
    have hxQ : x ∈ q.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using List.mem_of_mem_tail hy
    rcases hinter x hxP hxQ with rfl | rfl
    · exact hpnot hx
    · exact hqnot hy
  have length_two : ∀ w : G.Walk u v, 2 ≤ w.length := by
    intro w
    have h0 : w.length ≠ 0 := fun h => huv (Walk.eq_of_length_eq_zero h)
    have h1 : w.length ≠ 1 := fun h => hnuv (Walk.adj_of_length_eq_one h)
    omega
  have hpLen := length_two p
  have hqLen := length_two q
  refine ⟨hp.isCycle_append hq.reverse htail (Or.inl (by omega)), ?_, ?_⟩
  · simp only [Walk.length_append, Walk.length_reverse]
    omega
  · have edgeP {x y : V} (h : s(x, y) ∈ p.edges) : s(x, y) ∈ (p.append q.reverse).edges := by
      simp only [Walk.edges_append, List.mem_append]
      exact Or.inl h
    have edgeQ {x y : V} (h : s(x, y) ∈ q.edges) : s(x, y) ∈ (p.append q.reverse).edges := by
      simp only [Walk.edges_append, Walk.edges_reverse, List.mem_append, List.mem_reverse]
      exact Or.inr h
    have crossEdge : ∀ x ∈ p.support, ∀ y ∈ q.support, G.Adj x y →
        s(x, y) ∈ (p.append q.reverse).edges := by
      intro x hx y hy hxy
      rcases hpS x hx with hxL | rfl | rfl
      · rcases hqS y hy with hyR | rfl | rfl
        · exact (hcross x hxL y hyR hxy).elim
        · exact edgeP (hcp.mem_edges hx p.start_mem_support hxy)
        · exact edgeP (hcp.mem_edges hx p.end_mem_support hxy)
      · exact edgeQ (hcq.mem_edges q.start_mem_support hy hxy)
      · exact edgeQ (hcq.mem_edges q.end_mem_support hy hxy)
    apply Walk.isChordless_iff_forall_mem_edges.mpr
    intro x y hx hy hxy
    simp only [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact edgeP (hcp.mem_edges hx hy hxy)
    · exact crossEdge x hx y hy hxy
    · simpa only [Sym2.eq_swap] using crossEdge y hy x hx hxy.symm
    · exact edgeQ (hcq.mem_edges hx hy hxy)

end OMA.ChordalSeparators

namespace OMA.ChordalSeparators
open Finset SimpleGraph
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma minimal_separator_isClique (hG : G.IsChordal) {S C : Finset V} {a b : V}
    (ha : a ∈ S) (hb : b ∈ S) (hmin : MinimalSeparator G S C a b) :
    G.IsClique (C : Set V) := by
  obtain ⟨L, R, hS, hLR, _, _, haL, hbR, hcross⟩ := separator_sides G S C a b ha hb hmin.1
  intro u hu v hv huv
  by_contra hnuv
  obtain ⟨⟨pu, hpu⟩, ⟨qu, hqu⟩⟩ := separator_vertex_paths hS hcross haL hbR hmin hu
  obtain ⟨⟨pv, hpv⟩, ⟨qv, hqv⟩⟩ := separator_vertex_paths hS hcross haL hbR hmin hv
  obtain ⟨p, hp, hcp, hpS⟩ := path_between_through_side pu pv hpu hpv
  obtain ⟨q, hq, hcq, hqS⟩ := path_between_through_side qu qv hqu hqv
  obtain ⟨hcyc, hlen, hchordless⟩ := cycle_from_two_sides hLR hcross huv hnuv p q hp hq hcp hcq hpS hqS
  exact chordal_no_chordless_cycle hG (p.append q.reverse) hcyc hlen hchordless

end OMA.ChordalSeparators


namespace OMA.ChordalSeparators
open Finset SimpleGraph

/-- Given the induction conclusion, a clique cannot contain both nonadjacent witnesses. -/
private lemma simplicial_outside_clique {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (T C : Finset (Fin n)) (hC : G.IsClique (C : Set (Fin n)))
    (hout : ∃ x ∈ T, x ∉ C)
    (ih : (∃ u ∈ T, ∃ v ∈ T, u ≠ v ∧ ¬ G.Adj u v) →
      ∃ u ∈ T, ∃ v ∈ T, u ≠ v ∧ ¬ G.Adj u v ∧
        G.IsClique ((T.filter (G.Adj u)) : Set (Fin n)) ∧
        G.IsClique ((T.filter (G.Adj v)) : Set (Fin n))) :
    ∃ x ∈ T, x ∉ C ∧ G.IsClique ((T.filter (G.Adj x)) : Set (Fin n)) := by
  classical
  by_cases hT : G.IsClique (T : Set (Fin n))
  · obtain ⟨x, hx, hxC⟩ := hout
    exact ⟨x, hx, hxC, fun _ hy _ hz hne => hT (mem_filter.mp hy).1 (mem_filter.mp hz).1 hne⟩
  · obtain ⟨u, v, huv, hna⟩ := (G.not_isClique_iff).mp hT
    obtain ⟨x, hx, y, hy, hxy, hna, hsx, hsy⟩ := ih
      ⟨u, u.property, v, v.property, fun h => huv (Subtype.ext h), hna⟩
    by_cases hxC : x ∈ C
    · exact ⟨y, hy, fun hyC => hna (hC hxC hyC hxy), hsy⟩
    · exact ⟨x, hx, hxC, hsx⟩

end OMA.ChordalSeparators

open OMA.ChordalSeparators Finset SimpleGraph

theorem OMA.solution : OMA.R_Erdos81_erdos_81_R1.H1 := by
  classical
  intro n G _ hch S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro hnon
    obtain ⟨a, ha, b, hb, hab, hnab⟩ := hnon
    obtain ⟨L, R, C, hS, hLR, hLC, hRC, haL, hbR, hcross, hsep⟩ :=
      finite_separator_exists G S a b ha hb hab hnab
    have hC := minimal_separator_isClique hch ha hb hsep
    have haC : a ∉ C := fun h => Finset.disjoint_left.mp hLC haL h
    have hbC : b ∉ C := fun h => Finset.disjoint_left.mp hRC hbR h
    have hleft : L ∪ C ⊂ S := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [hS]
        simp only [mem_union] at hx ⊢
        tauto
      · intro he
        have hb' : b ∈ L ∪ C := he.symm ▸ hb
        rcases mem_union.mp hb' with hbL | hbC'
        · exact Finset.disjoint_left.mp hLR hbL hbR
        · exact hbC hbC'
    have hright : R ∪ C ⊂ S := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [hS]
        simp only [mem_union] at hx ⊢
        tauto
      · intro he
        have ha' : a ∈ R ∪ C := he.symm ▸ ha
        rcases mem_union.mp ha' with haR | haC'
        · exact Finset.disjoint_left.mp hLR haL haR
        · exact haC haC'
    obtain ⟨u, hu, huC, hus⟩ := simplicial_outside_clique G (L ∪ C) C hC
      ⟨a, mem_union_left C haL, haC⟩ (ih (L ∪ C) hleft)
    obtain ⟨v, hv, hvC, hvs⟩ := simplicial_outside_clique G (R ∪ C) C hC
      ⟨b, mem_union_left C hbR, hbC⟩ (ih (R ∪ C) hright)
    have huL : u ∈ L := (mem_union.mp hu).resolve_right huC
    have hvR : v ∈ R := (mem_union.mp hv).resolve_right hvC
    refine ⟨u, hleft.subset hu, v, hright.subset hv, ?_, hcross u huL v hvR, ?_, ?_⟩
    · intro huv
      exact Finset.disjoint_left.mp hLR huL (huv.symm ▸ hvR)
    · apply Set.Pairwise.mono _ hus
      intro x hx
      obtain ⟨hxS, hux⟩ := mem_filter.mp hx
      rw [hS] at hxS
      rcases mem_union.mp hxS with hxLR | hxC
      · rcases mem_union.mp hxLR with hxL | hxR
        · exact mem_filter.mpr ⟨mem_union_left C hxL, hux⟩
        · exact (hcross u huL x hxR hux).elim
      · exact mem_filter.mpr ⟨mem_union_right L hxC, hux⟩
    · apply Set.Pairwise.mono _ hvs
      intro x hx
      obtain ⟨hxS, hvx⟩ := mem_filter.mp hx
      rw [hS] at hxS
      rcases mem_union.mp hxS with hxLR | hxC
      · rcases mem_union.mp hxLR with hxL | hxR
        · exact (hcross x hxL v hvR hvx.symm).elim
        · exact mem_filter.mpr ⟨mem_union_left C hxR, hvx⟩
      · exact mem_filter.mpr ⟨mem_union_right R hxC, hvx⟩

