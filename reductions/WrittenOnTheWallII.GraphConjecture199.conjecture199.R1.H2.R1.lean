import OMAReductions.R_WrittenOnTheWallII_GraphConjecture199_conjecture199_R1
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The path-splicing argument formalizes the Chvátal–Erdős traceability condition
(Chvátal and Erdős, 1972). We also prove the separator bound for all small cuts
and all pairwise compatible cuts under the original induced-tree hypothesis.
-/

namespace OMA.R_WrittenOnTheWallII_GraphConjecture199_conjecture199_R1_H2_R1
open OMA.R_WrittenOnTheWallII_GraphConjecture199_conjecture199_R1
section

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V}

private theorem chain_join {L R : List V} {x y : V}
    (hL : L.IsChain G.Adj) (hR : R.IsChain G.Adj)
    (hx : L.getLast? = some x) (hy : R.head? = some y) (hxy : G.Adj x y) :
    (L ++ R).IsChain G.Adj := by
  apply hL.append hR
  intro a ha b hb
  have he : x = a := by simpa [hx] using ha
  have he' : y = b := by simpa [hy] using hb
  exact he ▸ he' ▸ hxy

/-- A longest vertex list may be chosen by maximizing its length. -/
theorem exists_longest_chain [Fintype V] [Nonempty V] :
    ∃ L : List V, L ≠ [] ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      ∀ Q : List V, Q.Nodup → Q.IsChain G.Adj → Q.length ≤ L.length := by
  classical
  let T : Set ℕ := {n | ∃ l : List V, l.Nodup ∧ l.IsChain G.Adj ∧ l.length = n}
  have hf : T.Finite := (Set.finite_le_nat (Fintype.card V)).subset (by
    rintro _ ⟨l,hl,_,rfl⟩
    change l.length ≤ _
    simpa only [List.toFinset_card_of_nodup hl] using card_le_univ l.toFinset)
  let x : V := Classical.choice (inferInstance : Nonempty V)
  obtain ⟨n,⟨L,hn,hc,hlen⟩,hmax⟩ := hf.exists_maximal
    ⟨1,[x],by simp,List.IsChain.singleton x,rfl⟩
  refine ⟨L,?_,hn,hc,?_⟩
  · intro he
    have hh : n ≤ 1 → 1 ≤ n := hmax ⟨[x],by simp,List.IsChain.singleton x,rfl⟩
    simp [he] at hlen
    omega
  · intro Q hQn hQc
    have hh := hmax ⟨Q,hQn,hQc,rfl⟩
    omega

/-- Neither endpoint of a longest path has a neighbor off the path. -/
theorem longest_chain_endpoints {L : List V} (hn : L.Nodup) (hc : L.IsChain G.Adj)
    (hm : ∀ Q : List V, Q.Nodup → Q.IsChain G.Adj → Q.length ≤ L.length)
    {x : V} (hx : x ∉ L) :
    (∀ a ∈ L.head?, ¬ G.Adj a x) ∧ (∀ a ∈ L.getLast?, ¬ G.Adj a x) := by
  constructor
  · intro a ha hax
    have h := hm (x :: L) (List.nodup_cons.mpr ⟨hx,hn⟩) (hc.cons (by
      intro b hb
      rw [ha] at hb
      have he : a = b := by simpa using hb
      exact he ▸ hax.symm))
    simp at h
  · intro a ha hax
    have hn' : (L ++ [x]).Nodup := by
      refine List.nodup_append.mpr ⟨hn,by simp,?_⟩
      intro y hy z hz
      have he : z = x := by simpa using hz
      exact fun h => hx ((h.trans he) ▸ hy)
    have hc' := chain_join hc (List.IsChain.singleton x)
      ha (by simp : ([x] : List V).head? = some x) hax
    have h := hm (L ++ [x]) hn' hc'
    simp at h

/-- The start of a longest path cannot see the successor of a vertex with an
off-path neighbor. -/
theorem longest_chain_head_misses_successor (P B : List V) (a x y c : V)
    (hhead : (P ++ x :: y :: B).head? = some a)
    (hn : (P ++ x :: y :: B).Nodup) (hc : (P ++ x :: y :: B).IsChain G.Adj)
    (hm : ∀ Q : List V, Q.Nodup → Q.IsChain G.Adj → Q.length ≤ (P ++ x :: y :: B).length)
    (hco : c ∉ P ++ x :: y :: B) (hxc : G.Adj x c) : ¬ G.Adj a y := by
  intro hay
  let A := P ++ [x]
  let D := y :: B
  have hsplit : A ++ D = P ++ x :: y :: B := by simp [A,D,List.append_assoc]
  have hAn : A.Nodup := (hsplit ▸ hn : (A ++ D).Nodup).of_append_left
  have hDn : D.Nodup := (hsplit ▸ hn : (A ++ D).Nodup).of_append_right
  have hAc : A.IsChain G.Adj := (hsplit ▸ hc : (A ++ D).IsChain G.Adj).left_of_append
  have hDc : D.IsChain G.Adj := (hsplit ▸ hc : (A ++ D).IsChain G.Adj).right_of_append
  have hAl : A.getLast? = some x := by simp [A]
  have hAh : A.head? = some a := by
    have hAne : A ≠ [] := by simp [A]
    rw [← List.head?_append_of_ne_nil _ hAne, hsplit, hhead]
  have hR : A.reverse.IsChain G.Adj :=
    List.isChain_reverse.mpr (hAc.imp fun _ _ h => h.symm)
  have hR' : (A.reverse ++ D).IsChain G.Adj :=
    chain_join hR hDc (by simpa using hAh) rfl hay
  have hc' : (c :: (A.reverse ++ D)).IsChain G.Adj := by
    apply hR'.cons
    intro z hz
    have hAne : A.reverse ≠ [] := by simp [A]
    rw [List.head?_append_of_ne_nil _ hAne, List.head?_reverse, hAl] at hz
    have he : x = z := by simpa using hz
    exact he ▸ hxc.symm
  have hn' : (A.reverse ++ D).Nodup := by
    refine List.nodup_append.mpr ⟨List.nodup_reverse.mpr hAn,hDn,?_⟩
    intro u hu z hz
    exact (List.nodup_append.mp (hsplit ▸ hn : (A ++ D).Nodup)).2.2
      u (List.mem_reverse.mp hu) z hz
  have hcc : c ∉ A.reverse ++ D := by
    simpa only [List.mem_append,List.mem_reverse,hsplit.symm] using hco
  have hh := hm _ (List.nodup_cons.mpr ⟨hcc,hn'⟩) hc'
  rw [← hsplit] at hh
  simp at hh

/-- An off-path connecting path may replace any split into two consecutive
pieces, contradicting maximality. -/
theorem longest_chain_no_detour_gap {A D M : List V} {x y c d : V}
    (hAn : A.Nodup) (hDn : D.Nodup) (hMn : M.Nodup)
    (hAc : A.IsChain G.Adj) (hDc : D.IsChain G.Adj) (hMc : M.IsChain G.Adj)
    (hAD : A.Disjoint D) (hAM : A.Disjoint M) (hMD : M.Disjoint D)
    (hAl : A.getLast? = some x) (hDh : D.head? = some y)
    (hMh : M.head? = some c) (hMl : M.getLast? = some d)
    (hxc : G.Adj x c) (hdy : G.Adj d y)
    (hm : ∀ Q : List V, Q.Nodup → Q.IsChain G.Adj → Q.length ≤ (A ++ D).length) : False := by
  have hAMn := hAn.append hMn hAM
  have hAMc := chain_join hAc hMc hAl hMh hxc
  have hAMl : (A ++ M).getLast? = some d := by simp [hMl]
  have hAMD : (A ++ M).Disjoint D := by
    intro z hz hz'
    exact (List.mem_append.mp hz).elim (fun h => hAD h hz') (fun h => hMD h hz')
  have h := hm ((A ++ M) ++ D) (hAMn.append hDn hAMD)
    (chain_join hAMc hDc hAMl hDh hdy)
  have hne : M ≠ [] := by intro he; simp [he] at hMh
  have hp : 0 < M.length := List.length_pos_iff.mpr hne
  simp only [List.length_append] at h
  omega

/-- The successors of two separated attachments cannot see each other. A
detour joins the attachments and the intervening piece is traversed backwards. -/
theorem longest_chain_no_detour_chord {A B D M : List V} {x y z t c d : V}
    (hA : A.getLast? = some x) (hB : B.head? = some y) (hB' : B.getLast? = some z)
    (hD : D.head? = some t) (hM : M.head? = some c) (hM' : M.getLast? = some d)
    (hn : ((A ++ B) ++ D).Nodup) (hc : ((A ++ B) ++ D).IsChain G.Adj)
    (hMn : M.Nodup) (hMc : M.IsChain G.Adj)
    (hdis : M.Disjoint ((A ++ B) ++ D)) (hxc : G.Adj x c) (hdz : G.Adj d z)
    (hm : ∀ Q : List V, Q.Nodup → Q.IsChain G.Adj →
      Q.length ≤ ((A ++ B) ++ D).length) : ¬ G.Adj y t := by
  intro hyt
  have hAc := hc.left_of_append.left_of_append
  have hBc := hc.left_of_append.right_of_append
  have hDc := hc.right_of_append
  have hR : B.reverse.IsChain G.Adj := List.isChain_reverse.mpr (hBc.imp fun _ _ h => h.symm)
  have hAMc := chain_join hAc hMc hA hM hxc
  have hAMl : (A ++ M).getLast? = some d := by simp [hM']
  have hARc := chain_join hAMc hR hAMl (by simpa using hB') hdz
  have hARl : ((A ++ M) ++ B.reverse).getLast? = some y := by simp [hB]
  have hnewc := chain_join hARc hDc hARl hD hyt
  have hperm : (((A ++ M) ++ B.reverse) ++ D).Perm (((A ++ B) ++ D) ++ M) := by
    calc
      (((A ++ M) ++ B.reverse) ++ D).Perm (((A ++ M) ++ B) ++ D) :=
        ((List.reverse_perm B).append_left (A ++ M)).append_right D
      _ = A ++ (M ++ (B ++ D)) := by simp [List.append_assoc]
      (A ++ (M ++ (B ++ D))).Perm (A ++ ((B ++ D) ++ M)) := (show (M ++ (B ++ D)).Perm ((B ++ D) ++ M) from List.perm_append_comm).append_left A
      _ = (((A ++ B) ++ D) ++ M) := by simp [List.append_assoc]
  have hnewn := hperm.nodup_iff.mpr (hn.append hMn hdis.symm)
  have h := hm _ hnewn hnewc
  have hne : M ≠ [] := by intro he; simp [he] at hM
  have hp : 0 < M.length := List.length_pos_iff.mpr hne
  simp only [List.length_append,List.length_reverse] at h
  omega

end

section

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] [DecidableEq V] in
private theorem pathSuccGivesMem {L : List V} {x y : V} (h : (∃ P B : List _, L = P ++ x :: y :: B)) :
    x ∈ L ∧ y ∈ L := by
  obtain ⟨P,B,rfl⟩ := h
  simp

omit [Fintype V] in
private theorem pathSuccIndex {L : List V} (hn : L.Nodup) {x y : V}
    (h : (∃ P B : List _, L = P ++ x :: y :: B)) : L.idxOf y = L.idxOf x + 1 := by
  obtain ⟨P,B,rfl⟩ := h
  have hp := List.nodup_append.mp hn
  have hx : x ∉ P := fun h => hp.2.2 x h x (by simp) rfl
  have hy : y ∉ P := fun h => hp.2.2 y h y (by simp) rfl
  have hxy : x ≠ y := fun h => (List.nodup_cons.mp hp.2.1).1 (by simp [h])
  rw [List.idxOf_append_of_notMem hx,List.idxOf_append_of_notMem hy]
  simp [List.idxOf_cons_ne _ hxy]

omit [Fintype V] in
private theorem eq_of_same_idx {L : List V} {x y : V}
    (hx : x ∈ L) (hy : y ∈ L) (h : L.idxOf x = L.idxOf y) : x = y := by
  have hx' := List.getElem?_idxOf hx
  have hy' := List.getElem?_idxOf hy
  rw [h,hy'] at hx'
  exact (Option.some.inj hx').symm

omit [Fintype V] in
private theorem pathSuccRightUnique {L : List V} (hn : L.Nodup) {x y z : V}
    (h : (∃ P B : List _, L = P ++ x :: y :: B)) (h' : (∃ P B : List _, L = P ++ x :: z :: B)) : y = z :=
  eq_of_same_idx (pathSuccGivesMem h).2 (pathSuccGivesMem h').2
    ((pathSuccIndex hn h).trans (pathSuccIndex hn h').symm)

omit [Fintype V] in
private theorem pathSuccLeftUnique {L : List V} (hn : L.Nodup) {x y z : V}
    (h : (∃ P B : List _, L = P ++ x :: z :: B)) (h' : (∃ P B : List _, L = P ++ y :: z :: B)) : x = y := by
  apply eq_of_same_idx (pathSuccGivesMem h).1 (pathSuccGivesMem h').1
  have hx := pathSuccIndex hn h
  have hy := pathSuccIndex hn h'
  omega

omit [Fintype V] [DecidableEq V] in
private theorem outside_path_list {C : Set V} (hc : (G.induce C).Connected)
    {a b : V} (ha : a ∈ C) (hb : b ∈ C) :
    ∃ L : List V, L.Nodup ∧ L.IsChain G.Adj ∧ L.head? = some a ∧
      L.getLast? = some b ∧ (∀ x ∈ L, x ∈ C) := by
  obtain ⟨p,hp⟩ := (hc ⟨a,ha⟩ ⟨b,hb⟩).exists_isPath
  let q := p.map (SimpleGraph.Embedding.induce C).toHom
  refine ⟨q.support, ?_, q.isChain_adj_support, ?_, ?_, ?_⟩
  · rw [Walk.support_map]
    exact hp.support_nodup.map Subtype.val_injective
  · rw [List.head?_eq_some_head q.support_ne_nil, q.head_support]
    rfl
  · rw [List.getLast?_eq_some_getLast q.support_ne_nil, q.getLast_support]
    rfl
  · intro x hx
    rw [Walk.support_map,List.mem_map] at hx
    obtain ⟨z,_,rfl⟩ := hx
    exact z.property

/-- A vertex separator surrounding an off-path component has at least κ
vertices. -/
theorem longest_chain_attachment_card (L : List V) (C : Set V) (a : V)
    (hC : C.Nonempty) (hdis : ∀ x ∈ C, x ∉ L)
    (hclosed : ∀ x ∈ C, ∀ y ∉ L, G.Adj x y → y ∈ C)
    (ha : a ∈ L) (hna : ∀ x ∈ C, ¬ G.Adj a x)
    (S : Finset V) (hS : ∀ x, x ∈ S ↔ x ∈ L ∧ ∃ y ∈ C, G.Adj x y) :
    vertexConnectivity G ≤ S.card := by
  by_contra! hlt
  have hConn := connected_of_card_lt_vertexConnectivity S hlt
  obtain ⟨c,hc⟩ := hC
  have hcs : c ∉ S := fun h => hdis c hc ((hS c).mp h).1
  have has : a ∉ S := by
    intro hs
    obtain ⟨_,hx,hax⟩ := ((hS a).mp hs).2
    exact hna _ hx hax
  let W := ↥((S : Set V)ᶜ)
  let K := G.induce ((S : Set V)ᶜ)
  let c' : W := ⟨c,hcs⟩
  let a' : W := ⟨a,has⟩
  have chain_closed {y : W} (hy : Relation.ReflTransGen K.Adj c' y) : y.val ∈ C := by
    induction hy with
    | refl => exact hc
    | tail _ hxy ih =>
      rename_i x y _
      have he : G.Adj x.val y.val := hxy
      have hyL : y.val ∉ L := fun h => y.property ((hS y.val).mpr ⟨h,x.val,ih,he.symm⟩)
      exact hclosed _ ih _ hyL he
  exact hdis a (chain_closed ((K.reachable_iff_reflTransGen _ _).mp (hConn c' a'))) ha

omit [Fintype V] [DecidableEq V] in
private theorem pathSucc_of_attachment {L : List V} {C : Set V} {x : V}
    (hn : L.Nodup) (hc : L.IsChain G.Adj)
    (hm : ∀ Q : List V, Q.Nodup → Q.IsChain G.Adj → Q.length ≤ L.length)
    (hdis : ∀ x ∈ C, x ∉ L) (hx : x ∈ L) (hxc : ∃ c ∈ C, G.Adj x c) :
    ∃ y, (∃ P B : List _, L = P ++ x :: y :: B) := by
  obtain ⟨P,B,hL⟩ := List.append_of_mem hx
  obtain ⟨c,hcC,hAdj⟩ := hxc
  cases B with
  | nil =>
    have hl : L.getLast? = some x := by simp [hL]
    exact ((longest_chain_endpoints hn hc hm (hdis c hcC)).2 _ hl hAdj).elim
  | cons y B => exact ⟨y,P,B,hL⟩

omit [Fintype V] [DecidableEq V] in
private theorem pathSucc_not_attachment {L : List V} {C : Set V} {x y : V}
    (hn : L.Nodup) (hc : L.IsChain G.Adj)
    (hm : ∀ Q : List V, Q.Nodup → Q.IsChain G.Adj → Q.length ≤ L.length)
    (hC : (G.induce C).Connected) (hdis : ∀ x ∈ C, x ∉ L)
    (hs : (∃ P B : List _, L = P ++ x :: y :: B)) (hx : ∃ c ∈ C, G.Adj x c) :
    ¬ ∃ d ∈ C, G.Adj y d := by
  intro hy
  obtain ⟨P,B,rfl⟩ := hs
  obtain ⟨c,hcC,hxc⟩ := hx
  obtain ⟨d,hdC,hyd⟩ := hy
  obtain ⟨M,hMn,hMc,hMh,hMl,hMC⟩ := outside_path_list hC hcC hdC
  let A := P ++ [x]
  let D := y :: B
  have hL : A ++ D = P ++ x :: y :: B := by simp [A,D,List.append_assoc]
  have hADn : (A ++ D).Nodup := by rwa [hL]
  have hADc : (A ++ D).IsChain G.Adj := by rwa [hL]
  have hDM : M.Disjoint (A ++ D) := by
    intro z hz hz'
    exact hdis z (hMC z hz) (hL ▸ hz')
  exact longest_chain_no_detour_gap hADn.of_append_left hADn.of_append_right hMn
    hADc.left_of_append hADc.right_of_append hMc hADn.disjoint
    (fun _ ha hm => hDM hm (List.mem_append_left _ ha))
    (fun _ hm hd => hDM hm (List.mem_append_right _ hd))
    (by simp [A]) rfl hMh hMl hxc hyd.symm (by rw [hL]; exact hm)

omit [Fintype V] in
private theorem pathSucc_pair_no_adjacency_aux {L : List V} {C : Set V} {x x' y y' : V}
    (hn : L.Nodup) (hc : L.IsChain G.Adj)
    (hm : ∀ Q : List V, Q.Nodup → Q.IsChain G.Adj → Q.length ≤ L.length)
    (hC : (G.induce C).Connected) (hdis : ∀ x ∈ C, x ∉ L)
    (hs : (∃ P B : List _, L = P ++ x :: y :: B)) (hs' : (∃ P B : List _, L = P ++ x' :: y' :: B))
    (hx : ∃ c ∈ C, G.Adj x c) (hx' : ∃ d ∈ C, G.Adj x' d)
    (hind : L.idxOf x < L.idxOf x') :
    ¬ G.Adj y y' := by
  have hney : x' ≠ y := fun he => pathSucc_not_attachment hn hc hm hC hdis hs hx (he ▸ hx')
  have hne : x' ≠ x := fun he => (Nat.ne_of_lt hind) (congrArg L.idxOf he).symm
  obtain ⟨P,B,hP⟩ := hs
  have hmem := (pathSuccGivesMem hs').1
  have hnod : (P ++ x :: y :: B).Nodup := hP ▸ hn
  have hnot : x' ∉ P := by
    intro hp
    have hxP : x ∉ P := fun h =>
      (List.nodup_append.mp hnod).2.2 _ h _ (by simp) rfl
    have hxi : L.idxOf x = P.length := by
      rw [hP,List.idxOf_append_of_notMem hxP]
      simp
    have hl : P.idxOf x' < P.length := List.idxOf_lt_length_iff.mpr hp
    rw [hxi,hP,List.idxOf_append_of_mem hp] at hind
    omega
  have hxB : x' ∈ B := by
    rw [hP,List.mem_append,List.mem_cons,List.mem_cons] at hmem
    exact ((hmem.resolve_left hnot).resolve_left hne).resolve_left hney
  obtain ⟨Q,R,hBR⟩ := List.append_of_mem hxB
  have hR : R ≠ [] := by
    intro he
    have hl : L.getLast? = some x' := by
      rw [hP,hBR,he]
      simp [List.getLast?_cons]
    obtain ⟨d,hd,hdx⟩ := hx'
    exact (longest_chain_endpoints hn hc hm (hdis d hd)).2 _ hl hdx
  cases R with
  | nil => contradiction
  | cons t D =>
    let A := P ++ [x]
    let B' := (y :: Q) ++ [x']
    have hEq : L = (A ++ B') ++ t :: D := by
      simp only [hP,hBR,A,B',List.append_assoc,List.cons_append,List.nil_append]
    have hsT : (∃ P B : List _, L = P ++ x' :: t :: B) := by
      refine ⟨P ++ [x,y] ++ Q,D,?_⟩
      simp [hP,hBR,List.append_assoc]
    have he : t = y' := pathSuccRightUnique hn hsT hs'
    obtain ⟨c,hcC,hxc⟩ := hx
    obtain ⟨d,hdC,hxd⟩ := hx'
    obtain ⟨M,hMn,hMc,hMh,hMl,hMC⟩ := outside_path_list hC hcC hdC
    have hdisM : M.Disjoint ((A ++ B') ++ t :: D) :=
      fun z hz hz' => hdis z (hMC z hz) (hEq.symm ▸ hz')
    rw [← he]
    exact longest_chain_no_detour_chord (by simp [A]) (by simp [B'])
      (by change ((y :: Q) ++ [x']).getLast? = some x';
          simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or])
      rfl hMh hMl (hEq ▸ hn) (hEq ▸ hc) hMn hMc hdisM hxc hxd.symm
      (by rw [← hEq]; exact hm)

/-- A longest path with an outside component forces an independent set of at
least two more vertices than the vertex connectivity. -/
theorem indepNum_at_least_of_longest_outside (L : List V) (a : V) (C : Set V)
    (hhead : L.head? = some a) (hn : L.Nodup) (hc : L.IsChain G.Adj)
    (hm : ∀ Q : List V, Q.Nodup → Q.IsChain G.Adj → Q.length ≤ L.length)
    (hC : (G.induce C).Connected) (hdis : ∀ x ∈ C, x ∉ L)
    (hclosed : ∀ x ∈ C, ∀ y ∉ L, G.Adj x y → y ∈ C) :
    vertexConnectivity G + 2 ≤ G.indepNum := by
  classical
  let S := L.toFinset.filter (fun x => ∃ y ∈ C, G.Adj x y)
  have hS (x : V) : x ∈ S ↔ x ∈ L ∧ ∃ y ∈ C, G.Adj x y := by simp [S]
  have haL : a ∈ L := List.mem_of_mem_head? hhead
  have hna (x : V) (hx : x ∈ C) : ¬ G.Adj a x :=
    (longest_chain_endpoints hn hc hm (hdis x hx)).1 _ hhead
  obtain ⟨c⟩ := hC.nonempty
  have hκ := longest_chain_attachment_card L C a ⟨c.val,c.property⟩ hdis hclosed haL hna S hS
  have hsucc (x : S) : ∃ y, (∃ P B : List _, L = P ++ x.val :: y :: B) :=
    pathSucc_of_attachment hn hc hm hdis ((hS x.val).mp x.property).1 ((hS x.val).mp x.property).2
  choose f hf using hsucc
  have hfi : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    exact pathSuccLeftUnique hn (hf x) (he ▸ hf y)
  let Y := S.attach.image f
  have hY : Y.card = S.card := by simp [Y,card_image_of_injective _ hfi]
  have hfL (x : V) (hx : x ∈ Y) : x ∈ L := by
    obtain ⟨y,_,rfl⟩ := mem_image.mp hx
    exact (pathSuccGivesMem (hf y)).2
  have hfc (x : V) (hx : x ∈ Y) : ¬ G.Adj x c.val := by
    obtain ⟨y,_,rfl⟩ := mem_image.mp hx
    intro he
    exact pathSucc_not_attachment hn hc hm hC hdis (hf y) ((hS y.val).mp y.property).2
      ⟨c.val,c.property,he⟩
  have hfa (x : V) (hx : x ∈ Y) : ¬ G.Adj a x := by
    obtain ⟨y,_,rfl⟩ := mem_image.mp hx
    obtain ⟨P,B,hPB⟩ := hf y
    obtain ⟨z,hz,haz⟩ := ((hS y.val).mp y.property).2
    apply longest_chain_head_misses_successor P B a y.val (f y) z
    · rwa [← hPB]
    · rwa [← hPB]
    · rwa [← hPB]
    · rw [← hPB]; exact hm
    · rw [← hPB]; exact hdis z hz
    · exact haz
  have hYa : a ∉ Y := by
    intro he
    obtain ⟨x,_,hfx⟩ := mem_image.mp he
    have hidx := pathSuccIndex hn (hf x)
    rw [hfx] at hidx
    have ha0 : L.idxOf a = 0 := by
      cases L with
      | nil => simp at hhead
      | cons h t =>
        have he : h = a := Option.some.inj hhead
        subst h
        simp
    omega
  have hYc : c.val ∉ Y := fun h => hdis c.val c.property (hfL _ h)
  have hYind : G.IsIndepSet (Y : Set V) := by
    intro x hx y hy hne
    obtain ⟨x',_,rfl⟩ := mem_image.mp hx
    obtain ⟨y',_,rfl⟩ := mem_image.mp hy
    have hxc := ((hS x'.val).mp x'.property).2
    have hyc := ((hS y'.val).mp y'.property).2
    rcases lt_trichotomy (L.idxOf x'.val) (L.idxOf y'.val) with h | h | h
    · exact pathSucc_pair_no_adjacency_aux hn hc hm hC hdis (hf x') (hf y') hxc hyc h
    · have hxy : x' = y' := Subtype.ext (eq_of_same_idx
        (pathSuccGivesMem (hf x')).1 (pathSuccGivesMem (hf y')).1 h)
      exact (hne (congrArg f hxy)).elim
    · exact fun he => pathSucc_pair_no_adjacency_aux hn hc hm hC hdis (hf y') (hf x') hyc hxc h he.symm
  have hI : G.IsIndepSet (↑(insert c.val Y) : Set V) := by
    rw [coe_insert]
    apply Set.Pairwise.insert_of_notMem hYc hYind
    intro x hx
    exact ⟨fun he => hfc x hx he.symm,hfc x hx⟩
  have hca : a ≠ c.val := fun he => hdis c.val c.property (he ▸ haL)
  have haI : a ∉ insert c.val Y := by simp [hca,hYa]
  have hI' : G.IsIndepSet (↑(insert a (insert c.val Y)) : Set V) := by
    rw [coe_insert]
    apply Set.Pairwise.insert_of_notMem haI hI
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact ⟨hna _ c.property,fun h => hna _ c.property h.symm⟩
    · exact ⟨hfa x hx,fun h => hfa x hx h.symm⟩
  have hbig := hI'.card_le_indepNum
  rw [card_insert_of_notMem haI,card_insert_of_notMem hYc,hY] at hbig
  omega

/-- The traceability form of the Chvátal–Erdős theorem. -/
theorem hamiltonian_of_indepNum_le_vertexConnectivity_add_one
    (hG : G.Connected) (hα : G.indepNum ≤ vertexConnectivity G + 1) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let _ : Nonempty V := hG.nonempty
  obtain ⟨L,hLe,hn,hc,hm⟩ := exists_longest_chain (G := G)
  let a := L.head hLe
  have ha : L.head? = some a := List.head?_eq_some_head hLe
  let p := Walk.ofSupport L hLe hc
  have hp : p.support = L := Walk.support_ofSupport hLe hc
  have hpath : p.IsPath := by
    apply Walk.IsPath.mk'
    rwa [hp]
  refine ⟨_,_,p,hpath.isHamiltonian_of_mem ?_⟩
  intro x
  rw [hp]
  by_contra hx
  let T := {x | x ∉ L}
  let K := G.induce T
  let q : T := ⟨x,hx⟩
  let i := K.connectedComponentMk q
  let C : Set V := Subtype.val '' i.supp
  have hdis (z : V) (hz : z ∈ C) : z ∉ L := by
    obtain ⟨y,_,rfl⟩ := hz
    exact y.property
  have hclosed (z : V) (hz : z ∈ C) (y : V) (hy : y ∉ L) (he : G.Adj z y) : y ∈ C := by
    obtain ⟨s,hs,rfl⟩ := hz
    let t : T := ⟨y,hy⟩
    have hst : K.Adj s t := he
    exact ⟨t,i.mem_supp_of_adj_mem_supp hs hst,rfl⟩
  have hC : (G.induce C).Connected := by
    let f : i.supp → C := fun x => ⟨x.val.val,x.val,x.property,rfl⟩
    have hinj : Function.Injective f := by
      intro a b h
      exact Subtype.ext (Subtype.ext (congrArg (fun x : C => x.val) h))
    have hsurj : Function.Surjective f := by
      rintro ⟨x,y,hy,rfl⟩
      exact ⟨⟨y,hy⟩,rfl⟩
    let iso : K.induce i.supp ≃g G.induce C :=
      ⟨Equiv.ofBijective f ⟨hinj,hsurj⟩, by intro a b; rfl⟩
    exact iso.connected_iff.mp i.maximal_connected_induce_supp.1
  have h := indepNum_at_least_of_longest_outside L a C ha hn hc hm hC hdis hclosed
  omega

end

section

open SimpleGraph Finset

/-- A maximum independent set lies in one connected component of the complement.
A vertex in a different component is a common neighbor in the original graph.
Together they induce a star on one more vertex than the independence number. -/
theorem indepNum_add_one_le_tree_of_compl_disconnected
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) (hd : ¬ Gᶜ.Connected) :
    G.indepNum + 1 ≤ largestInducedTreeSize G := by
  classical
  obtain ⟨S,hS⟩ := G.maximumIndepSet_exists
  have card := G.maximumIndepSet_card_eq_indepNum S hS
  rw [← card]
  have common : ∃ z, ∀ y ∈ S, G.Adj z y := by
    by_cases hne : S.Nonempty
    · obtain ⟨x,hx⟩ := hne
      obtain ⟨z,hz⟩ : ∃ z, ¬ Gᶜ.Reachable x z := by
        by_contra! h
        exact hd (Gᶜ.connected_iff_exists_forall_reachable.mpr ⟨x,h⟩)
      refine ⟨z,fun y hy => ?_⟩
      have hxy : Gᶜ.Reachable x y := by
        by_cases he : x = y
        · exact he ▸ Reachable.rfl
        · exact ((G.compl_adj x y).mpr ⟨he,hS.isIndepSet hx hy he⟩).reachable
      have hn : ¬Gᶜ.Reachable y z := fun h => hz (hxy.trans h)
      have e := (Gᶜ.reachable_or_compl_adj y z).resolve_left hn
      simpa using e.symm
    · exact ⟨Classical.arbitrary V,fun y hy => (hne ⟨y,hy⟩).elim⟩
  obtain ⟨z,hz⟩ := common
  exact star_bound z S hS.isIndepSet hz

/-- The conjecture's tree bound implies the Chvátal–Erdős numerical
traceability condition when the complement is disconnected. -/
theorem indepNum_le_connectivity_add_one_of_compl_disconnected
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) (hd : ¬ Gᶜ.Connected)
    (h : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) :
    G.indepNum ≤ vertexConnectivity G + 1 := by
  have := indepNum_add_one_le_tree_of_compl_disconnected G hd
  omega

end

section


/-- In a separator incidence matrix, total edges e and total ordered
row distances t constrain the number c of columns in terms of rows m. -/
theorem incidence_numbers {k m c e t : ℤ} (hk : 0 < k) (hm : 0 ≤ m)
    (he₁ : k*c ≤ e) (he₂ : e ≤ m*(k+1))
    (hs₁ : 2*k*c*m ≤ t + 2*k*e) (hs₂ : t ≤ k*m*(m-1)) :
    c ≤ m+1 := by
  by_contra! h
  have hlarge : m+2 ≤ c := by omega
  have hkm : 2*k ≤ m := by
    have h := mul_le_mul_of_nonneg_left hlarge hk.le
    nlinarith
  have hpos : 0 < k*m := mul_pos hk (by omega)
  have bound : k*m*(2*c) ≤ k*m*(m+2*k+1) := by
    have he := mul_le_mul_of_nonneg_left he₂ (show 0 ≤ 2*k by omega)
    nlinarith
  have hh : 2*c ≤ m+2*k+1 := (mul_le_mul_iff_right₀ hpos).mp bound
  omega

end

section

open Finset
open scoped BigOperators

private theorem sum_indicator {α : Type*} (s : Finset α) (p : α → Prop)
    [DecidablePred p] :
    (∑ a ∈ s, if p a then (1 : ℤ) else 0) = ((s.filter p).card : ℤ) := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- Incidence bound for a collection of columns with minimum degree k,
row degree at most k+1, and pairwise row distance at most k. -/
theorem incidence_clique_bound {U C : Type*} [Fintype U] [Fintype C] [DecidableEq C]
    (R : U → Finset C) (k : ℕ) (hk : 0 < k)
    (col : ∀ i, k ≤ (univ.filter fun u => i ∈ R u).card)
    (row : ∀ u, (R u).card ≤ k + 1)
    (dist : ∀ u v, u ≠ v → ((R u \ R v) ∪ (R v \ R u)).card ≤ k) :
    Fintype.card C ≤ Fintype.card U + 1 := by
  classical
  let m : ℤ := Fintype.card U
  let c : ℤ := Fintype.card C
  let I (i : C) (u : U) : ℤ := if i ∈ R u then 1 else 0
  let D (i : C) : ℤ := (univ.filter fun u => i ∈ R u).card
  let E : ℤ := ∑ i : C, D i
  let F (u v : U) : ℤ := ((R u \ R v) ∪ (R v \ R u)).card
  let T : ℤ := ∑ u : U, ∑ v : U, F u v
  have hI (i : C) : (∑ u : U, I i u) = D i := sum_indicator univ _
  have hrowI (u : U) : (∑ i : C, I i u) = ((R u).card : ℤ) := by
    rw [show (∑ i : C, I i u) = ((univ.filter fun i => i ∈ R u).card : ℤ) by
      exact sum_indicator univ _]
    simp
  have hE : E = ∑ u : U, ((R u).card : ℤ) := by
    simp only [E, ← hI, ← hrowI]
    exact Finset.sum_comm
  have he₁ : (k : ℤ) * c ≤ E := by
    calc
      _ = ∑ _i : C, (k : ℤ) := by simp [c, mul_comm]
      _ ≤ E := Finset.sum_le_sum fun i _ => by
        change (k : ℤ) ≤ ((univ.filter fun u => i ∈ R u).card : ℤ)
        exact_mod_cast col i
  have he₂ : E ≤ m * ((k : ℤ) + 1) := by
    rw [hE]
    calc
      _ ≤ ∑ _u : U, ((k : ℤ) + 1) :=
        Finset.sum_le_sum fun u _ => by exact_mod_cast row u
      _ = _ := by simp [m]
  have hF (u v : U) : F u v =
      ∑ i : C, (I i u * (1 - I i v) + (1 - I i u) * I i v) := by
    let S := (R u \ R v) ∪ (R v \ R u)
    have hcnt : (∑ i : C, if i ∈ S then (1 : ℤ) else 0) = F u v := by
      calc
        _ = ((univ.filter fun i => i ∈ S).card : ℤ) := sum_indicator univ _
        _ = _ := by
          have hS : univ.filter (fun i => i ∈ S) = S := by ext i; simp only [mem_filter, mem_univ, true_and]
          change _ = (S.card : ℤ)
          rw [hS]
    rw [← hcnt]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hu : i ∈ R u <;> by_cases hv : i ∈ R v <;> simp [I, S, hu, hv]
  have hnotI (i : C) : (∑ v : U, (1 - I i v)) = m - D i := by
    rw [Finset.sum_sub_distrib, hI]
    simp [m]
  have hT : T = ∑ i : C, 2 * D i * (m - D i) := by
    calc
      T = ∑ u : U, ∑ v : U, ∑ i : C,
          (I i u * (1 - I i v) + (1 - I i u) * I i v) := by simp only [T, hF]
      _ = ∑ i : C, ∑ u : U, ∑ v : U,
          (I i u * (1 - I i v) + (1 - I i u) * I i v) := by
        calc
          _ = ∑ u : U, ∑ i : C, ∑ v : U,
              (I i u * (1 - I i v) + (1 - I i u) * I i v) := by
            exact Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
          _ = _ := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hnotI, hI]
        rw [← Finset.sum_mul, ← Finset.sum_mul, hI, hnotI]
        ring
  have hs₁ : 2 * (k : ℤ) * c * m ≤ T + 2 * (k : ℤ) * E := by
    change _ ≤ T + 2 * (k : ℤ) * (∑ i : C, D i)
    rw [hT, Finset.mul_sum, ← Finset.sum_add_distrib]
    calc
      _ = ∑ _i : C, 2 * (k : ℤ) * m := by
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, c]
        ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        have hlo : (k : ℤ) ≤ D i := by
          change (k : ℤ) ≤ ((univ.filter fun u => i ∈ R u).card : ℤ)
          exact_mod_cast col i
        have hhi : D i ≤ m := by
          change ((univ.filter fun u => i ∈ R u).card : ℤ) ≤ (Fintype.card U : ℤ)
          exact_mod_cast (Finset.card_le_univ (univ.filter fun u : U => i ∈ R u))
        nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)]
  have hs₂ : T ≤ (k : ℤ) * m * (m - 1) := by
    have hinner (u : U) : (∑ v : U, F u v) ≤ (k : ℤ) * (m - 1) := by
      have hzero : F u u = 0 := by simp [F]
      have hm1 : 1 ≤ Fintype.card U := Fintype.card_pos_iff.mpr ⟨u⟩
      calc
        _ = ∑ v ∈ univ.erase u, F u v := by
          have he := Finset.sum_erase_add (s := univ) (F u) (Finset.mem_univ u)
          rw [hzero, add_zero] at he
          exact he.symm
        _ ≤ ∑ _v ∈ univ.erase u, (k : ℤ) := by
          apply Finset.sum_le_sum
          intro v hv
          change ((((R u \ R v) ∪ (R v \ R u)).card : ℤ)) ≤ (k : ℤ)
          exact_mod_cast dist u v (Finset.ne_of_mem_erase hv).symm
        _ = _ := by
          simp [m, Finset.card_erase_of_mem (Finset.mem_univ u),
            Nat.cast_sub hm1, mul_comm]
    calc
      T ≤ ∑ _u : U, (k : ℤ) * (m - 1) :=
        Finset.sum_le_sum fun u _ => hinner u
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, m]; ring
  have hc : c ≤ m + 1 :=
    incidence_numbers (by exact_mod_cast hk) (Int.natCast_nonneg _) he₁ he₂ hs₁ hs₂
  change (Fintype.card C : ℤ) ≤ (Fintype.card U : ℤ) + 1 at hc
  exact_mod_cast hc

end

section

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] in
private theorem tree_add_leaves (T S : Finset V) (v : V)
    (hT : (G.induce (↑T : Set V)).IsTree) (hv : v ∈ T)
    (hdis : Disjoint S T) (hi : G.IsIndepSet (S : Set V))
    (ha : ∀ x ∈ S, G.Adj x v)
    (hu : ∀ x ∈ S, ∀ y ∈ T, G.Adj x y → y = v) :
    (G.induce (↑(T ∪ S) : Set V)).IsTree := by
  induction S using Finset.induction_on with
  | empty => rwa [Finset.union_empty]
  | @insert a S hx ih =>
    have hST : Disjoint S T := hdis.mono_left (subset_insert _ _)
    have hSi : G.IsIndepSet (S : Set V) :=
      hi.mono (by simpa only [coe_insert] using Set.subset_insert a (S : Set V))
    have htree := ih hST hSi (fun x hx => ha x (mem_insert_of_mem hx))
      (fun x hx y hy => hu x (mem_insert_of_mem hx) y hy)
    have haT : a ∉ T := fun h => Finset.disjoint_left.mp hdis (mem_insert_self _ _) h
    have haU : a ∉ (T ∪ S) := by simp [hx, haT]
    have hvU : v ∈ T ∪ S := mem_union.mpr (Or.inl hv)
    have hxa := ha a (mem_insert_self _ _)
    have hnew := htree.induce_insert_of_unique_adj haU hvU hxa (by
      intro y hy he
      rcases mem_union.mp hy with hy | hy
      · exact hu _ (mem_insert_self _ _) _ hy he
      · exact (hi (mem_insert_self a S) (mem_insert_of_mem hy) he.ne he).elim)
    rwa [union_insert]

omit [Fintype V] [DecidableEq V] in
private theorem tree_singleton (v : V) :
    (G.induce (↑({v} : Finset V) : Set V)).IsTree := by
  rw [coe_singleton]
  let _ : Nonempty ↥({v} : Set V) := ⟨⟨v, by simp⟩⟩
  let _ : Subsingleton ↥({v} : Set V) := ⟨fun x y => Subtype.ext
    ((Set.mem_singleton_iff.mp x.property).trans (Set.mem_singleton_iff.mp y.property).symm)⟩
  exact IsTree.of_subsingleton

/-- Append two disjoint independent leaf classes to a connecting induced
tree. Each class has a single possible neighbor in the core. -/
theorem leaf_sets_on_induced_tree (B S T : Finset V) (u v : V)
    (hB : (G.induce (B : Set V)).IsTree) (hu : u ∈ B) (hv : v ∈ B)
    (hSB : Disjoint S B) (hTB : Disjoint T B)
    (hSi : G.IsIndepSet (S : Set V)) (hTi : G.IsIndepSet (T : Set V))
    (hST : ∀ x ∈ S, ∀ y ∈ T, x ≠ y ∧ ¬ G.Adj x y)
    (hS : ∀ x ∈ S, G.Adj x u) (hT : ∀ y ∈ T, G.Adj y v)
    (hSu : ∀ x ∈ S, ∀ y ∈ B, G.Adj x y → y = u)
    (hTv : ∀ x ∈ T, ∀ y ∈ B, G.Adj x y → y = v) :
    B.card + S.card + T.card ≤ largestInducedTreeSize G := by
  have hBS := tree_add_leaves B S u hB hu hSB hSi hS hSu
  have hTBS : Disjoint T (B ∪ S) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    rcases mem_union.mp hy with hb | hs
    · exact Finset.disjoint_left.mp hTB hx hb
    · exact (hST x hs x hx).1 rfl
  have hBST := tree_add_leaves (B ∪ S) T v hBS (mem_union.mpr (Or.inl hv))
    hTBS hTi hT (by
      intro x hx y hy hxy
      rcases mem_union.mp hy with hy | hy
      · exact hTv x hx y hy hxy
      · exact ((hST y hy x hx).2 hxy.symm).elim)
  have hb := card_le_largestInducedTreeSize hBST
  simpa only [card_union_of_disjoint hTBS.symm,card_union_of_disjoint hSB.symm] using hb

omit [Fintype V] in
/-- Two distinct nonadjacent vertices meeting the same connected set have
an induced connecting tree inside the set and those vertices. -/
theorem connector_tree_of_common_component (u v : V) (C : Set V)
    (hne : u ≠ v) (hno : ¬ G.Adj u v) (hc : (G.induce C).Connected)
    (huC : ∃ x ∈ C, G.Adj u x) (hvC : ∃ x ∈ C, G.Adj v x) :
    ∃ B : Finset V, 3 ≤ B.card ∧ u ∈ B ∧ v ∈ B ∧
      (∀ x ∈ B, x = u ∨ x = v ∨ x ∈ C) ∧ (G.induce (B : Set V)).IsTree := by
  classical
  obtain ⟨a,ha,hua⟩ := huC
  obtain ⟨b,hb,hvb⟩ := hvC
  let S := insert u (insert v C)
  let K := G.induce S
  let u' : S := ⟨u,by simp [S]⟩
  let v' : S := ⟨v,by simp [S]⟩
  let a' : S := ⟨a,by simp [S,ha]⟩
  let b' : S := ⟨b,by simp [S,hb]⟩
  let i : G.induce C →g K :=
    ⟨fun x => ⟨x.val, Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ x.property)⟩,
      fun h => h⟩
  have haReach : K.Reachable a' b' := (hc ⟨a,ha⟩ ⟨b,hb⟩).map i
  have huAdj : K.Adj u' a' := hua
  have hvAdj : K.Adj v' b' := hvb
  have hr : K.Reachable u' v' := huAdj.reachable.trans (haReach.trans hvAdj.symm.reachable)
  obtain ⟨p,hp,hpLen⟩ := hr.exists_path_of_dist
  let B₀ := p.support.toFinset
  let f : S ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  let B := B₀.map f
  have hdist0 : K.dist u' v' ≠ 0 :=
    fun he => hne (congrArg Subtype.val (hr.dist_eq_zero_iff.mp he))
  have hdist1 : K.dist u' v' ≠ 1 := fun he =>
    hno (show K.Adj u' v' from dist_eq_one_iff_adj.mp he)
  have hBc : B.card = K.dist u' v' + 1 := by
    dsimp [B,B₀]
    rw [card_map,List.toFinset_card_of_nodup hp.support_nodup,Walk.length_support,hpLen]
  have hBu : u ∈ B := mem_map.mpr ⟨u',List.mem_toFinset.mpr p.start_mem_support,rfl⟩
  have hBv : v ∈ B := mem_map.mpr ⟨v',List.mem_toFinset.mpr p.end_mem_support,rfl⟩
  have hSet (x : V) (hx : x ∈ B) : x = u ∨ x = v ∨ x ∈ C := by
    obtain ⟨y,_,rfl⟩ := mem_map.mp hx
    have hy : y.val ∈ insert u (insert v C) := y.property
    rcases Set.mem_insert_iff.mp hy with h | h
    · exact Or.inl h
    · exact Or.inr (Set.mem_insert_iff.mp h)
  have htree : (K.induce (B₀ : Set S)).IsTree :=
    p.induce_support_isTree_of_length_eq_dist hpLen
  let g : ↥(B₀ : Set S) → ↥(B : Set V) := fun a => ⟨a.val.val,
    mem_map.mpr ⟨a.val,a.property,rfl⟩⟩
  have hgi : Function.Injective g := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun x : ↥(B : Set V) => x.val) he))
  have hgs : Function.Surjective g := by
    intro a
    obtain ⟨x,hx,he⟩ := mem_map.mp a.property
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  let iso : K.induce (B₀ : Set S) ≃g G.induce (B : Set V) :=
    ⟨Equiv.ofBijective g ⟨hgi,hgs⟩,by intro x y; rfl⟩
  exact ⟨B,by omega,hBu,hBv,hSet,iso.isTree_iff.mp htree⟩

/-- An edge with two sets of private, independent neighbors induces a tree
on the two centers and all selected neighbors. -/
theorem double_star_bound (u v : V) (huv : G.Adj u v) (S T : Finset V)
    (hS : G.IsIndepSet (S : Set V)) (hT : G.IsIndepSet (T : Set V))
    (hST : ∀ x ∈ S, ∀ y ∈ T, x ≠ y ∧ ¬ G.Adj x y)
    (hs : ∀ x ∈ S, G.Adj u x ∧ ¬ G.Adj v x)
    (ht : ∀ y ∈ T, G.Adj v y ∧ ¬ G.Adj u y)
    (hSv : v ∉ S) (hTu : u ∉ T) :
    S.card + T.card + 2 ≤ largestInducedTreeSize G := by
  let B : Finset V := {u,v}
  have hB : (G.induce (↑B : Set V)).IsTree :=
    (tree_singleton v).induce_insert_of_unique_adj
      (by simpa using huv.ne) (mem_singleton_self v) huv (by simp)
  have hSB : Disjoint S B := by
    apply Finset.disjoint_left.mpr
    intro x hx h
    simp only [B,mem_insert,mem_singleton] at h
    rcases h with rfl | rfl
    · exact (hs _ hx).1.ne rfl
    · exact hSv hx
  have hTB : Disjoint T B := by
    apply Finset.disjoint_left.mpr
    intro y hy h
    simp only [B,mem_insert,mem_singleton] at h
    rcases h with rfl | rfl
    · exact hTu hy
    · exact (ht _ hy).1.ne rfl
  have hBS : (G.induce (↑(B ∪ S) : Set V)).IsTree :=
    tree_add_leaves B S u hB (by simp [B]) hSB hS (fun x hx => (hs x hx).1.symm) (by
      intro x hx y hy hxy
      simp only [B,mem_insert,mem_singleton] at hy
      rcases hy with rfl | rfl
      · rfl
      · exact ((hs x hx).2 hxy.symm).elim)
  have hTBS : Disjoint T (B ∪ S) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    rcases mem_union.mp hy with hb | hs'
    · exact Finset.disjoint_left.mp hTB hx hb
    · exact (hST x hs' x hx).1 rfl
  have hBST : (G.induce (↑((B ∪ S) ∪ T) : Set V)).IsTree :=
    tree_add_leaves (B ∪ S) T v hBS (by simp [B]) hTBS hT (fun y hy => (ht y hy).1.symm) (by
      intro y hy x hx hey
      rcases mem_union.mp hx with hxb | hxs
      · simp only [B,mem_insert,mem_singleton] at hxb
        rcases hxb with rfl | rfl
        · exact ((ht y hy).2 hey.symm).elim
        · rfl
      · exact ((hST x hxs y hy).2 hey.symm).elim)
  have hcardB : B.card = 2 := by
    dsimp [B]
    rw [card_insert_of_notMem (show u ∉ ({v} : Finset V) from by simpa using huv.ne),
      card_singleton]
  have hb := card_le_largestInducedTreeSize hBST
  rw [card_union_of_disjoint hTBS.symm,card_union_of_disjoint hSB.symm,hcardB] at hb
  omega

open scoped Classical in
/-- Every component of the complement of a separator meets at least κ
separator vertices, provided another component is present. -/
theorem component_neighbour_count {I : Type*} [Nontrivial I]
    (U : Finset V) (C : I → Set V) (hn : ∀ i, (C i).Nonempty)
    (hout : ∀ i x, x ∈ C i → x ∉ U)
    (hcover : ∀ x ∉ U, ∃ i, x ∈ C i)
    (hsep : ∀ {i j : I} {x y : V}, i ≠ j → x ∈ C i → y ∈ C j → x ≠ y ∧ ¬ G.Adj x y)
    (i : I) :
    vertexConnectivity G ≤ (U.filter fun u => ∃ x ∈ C i, G.Adj u x).card := by
  classical
  let N := U.filter fun u => ∃ x ∈ C i, G.Adj u x
  change vertexConnectivity G ≤ N.card
  by_contra! hN
  have hK := connected_of_card_lt_vertexConnectivity N hN
  let W := ↥((N : Set V)ᶜ)
  let S : Finset W := univ.filter fun x => x.val ∈ C i
  have hSn : S.Nonempty := by
    obtain ⟨x,hx⟩ := hn i
    have hxN : x ∉ N := fun h => hout i x hx (mem_filter.mp h).1
    exact ⟨⟨x,hxN⟩, mem_filter.mpr ⟨mem_univ _,hx⟩⟩
  have hSu : S ≠ univ := by
    obtain ⟨j,hj⟩ := exists_ne i
    obtain ⟨y,hy⟩ := hn j
    have hyN : y ∉ N := fun h => hout j y hy (mem_filter.mp h).1
    let q : W := ⟨y,hyN⟩
    intro he
    have hm : q ∈ S := he ▸ mem_univ _
    exact (hsep hj.symm (mem_filter.mp hm).2 hy).1 rfl
  obtain ⟨y,hy,x,hx,hyx⟩ := hK.exists_adj_finset_compl hSn hSu
  have hxi : x.val ∈ C i := (mem_filter.mp hx).2
  have hyi : y.val ∉ C i := fun h => hy (mem_filter.mpr ⟨mem_univ _,h⟩)
  have hadj : G.Adj y.val x.val := induce_adj.mp hyx
  by_cases hyU : y.val ∈ U
  · exact y.property (mem_filter.mpr ⟨hyU,x.val,hxi,hadj⟩)
  · obtain ⟨j,hyj⟩ := hcover y.val hyU
    have hne : i ≠ j := fun he => hyi (he ▸ hyj)
    exact (hsep hne hxi hyj).2 hadj.symm

omit [Fintype V] in
private theorem touching_representatives {I : Type*} (C : I → Set V) (J : Finset I)
    (u : V)
    (hsep : ∀ {i j : I} {x y : V}, i ≠ j → x ∈ C i → y ∈ C j → x ≠ y ∧ ¬ G.Adj x y)
    (hmeet : ∀ i ∈ J, ∃ x ∈ C i, G.Adj u x) :
    ∃ B : Finset V, B.card = J.card ∧ G.IsIndepSet (B : Set V) ∧
      (∀ x ∈ B, ∃ i ∈ J, x ∈ C i) ∧ (∀ x ∈ B, G.Adj u x) := by
  classical
  have hex (i : J) : ∃ x ∈ C i.val, G.Adj u x := hmeet i.val i.property
  choose f hf hAdj using hex
  have hfi : Function.Injective f := by
    intro i j he
    apply Subtype.ext
    by_contra hn
    exact (hsep hn (hf i) (hf j)).1 he
  let B := J.attach.image f
  refine ⟨B,by simp [B,card_image_of_injective _ hfi],?_,?_,?_⟩
  · intro x hx y hy hne
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    obtain ⟨j,_,rfl⟩ := mem_image.mp hy
    exact (hsep (fun h => hne (congrArg f (Subtype.ext h))) (hf i) (hf j)).2
  · intro x hx
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    exact ⟨i.val,i.property,hf i⟩
  · intro x hx
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    exact hAdj i

/-- Separator incidence obeys a pairwise difference bound for each pair of distinct
centers that is adjacent or meets a common component. -/
theorem separator_incidence_partial {I : Type*} [Fintype I] [DecidableEq I] [Nontrivial I]
    (U : Finset V) (C : I → Set V)
    (hn : ∀ i, (C i).Nonempty)
    (hout : ∀ i x, x ∈ C i → x ∉ U)
    (hcover : ∀ x ∉ U, ∃ i, x ∈ C i)
    (hsep : ∀ {i j : I} {x y : V}, i ≠ j → x ∈ C i → y ∈ C j → x ≠ y ∧ ¬ G.Adj x y)
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) :
    ∃ R : U → Finset I,
      (∀ u i, i ∈ R u ↔ ∃ x ∈ C i, G.Adj u.val x) ∧
      (∀ i, vertexConnectivity G ≤ (univ.filter fun u : U => i ∈ R u).card) ∧
      (∀ u, (R u).card ≤ vertexConnectivity G + 1) ∧
      (∀ u v, u ≠ v →
        (G.Adj u.val v.val ∨ ∃ i, (G.induce (C i)).Connected ∧
          (∃ x ∈ C i, G.Adj u.val x) ∧ (∃ x ∈ C i, G.Adj v.val x)) →
        (((R u \ R v) ∪ (R v \ R u))).card ≤ vertexConnectivity G) := by
  classical
  let R (u : U) := univ.filter fun i => ∃ x ∈ C i, G.Adj u.val x
  have hR (u : U) (i : I) : i ∈ R u ↔ ∃ x ∈ C i, G.Adj u.val x := by simp [R]
  refine ⟨R,hR,?_,?_,?_⟩
  · intro i
    have h := component_neighbour_count U C hn hout hcover (fun he hx hy => hsep he hx hy) i
    let emb : U ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
    have he : (univ.filter fun u : U => i ∈ R u).map emb =
        U.filter (fun u => ∃ x ∈ C i, G.Adj u x) := by
      ext x
      constructor
      · intro hx
        obtain ⟨y,hy,rfl⟩ := mem_map.mp hx
        exact mem_filter.mpr ⟨y.property,(hR y i).mp (mem_filter.mp hy).2⟩
      · intro hx
        obtain ⟨hxU,hxc⟩ := mem_filter.mp hx
        refine mem_map.mpr ⟨⟨x,hxU⟩,mem_filter.mpr ⟨mem_univ _,?_⟩,rfl⟩
        exact (hR _ i).mpr hxc
    rwa [← he,card_map] at h
  · intro u
    obtain ⟨B,hB,hBin,_,hBAdj⟩ := touching_representatives C (R u) u.val
      (fun he hx hy => hsep he hx hy) (fun i hi => (hR u i).mp hi)
    have hstar := star_bound u.val B hBin hBAdj
    omega
  · intro u v huv hcompat
    let Iu := R u \ R v
    let Iv := R v \ R u
    have hdis : Disjoint Iu Iv := by
      apply Finset.disjoint_left.mpr
      intro i hi hj
      exact (mem_sdiff.mp hi).2 (mem_sdiff.mp hj).1
    obtain ⟨S,hSc,hSi,hSF,hSa⟩ := touching_representatives C Iu u.val
      (fun he hx hy => hsep he hx hy) (fun i hi => (hR u i).mp (mem_sdiff.mp hi).1)
    obtain ⟨T,hTc,hTi,hTF,hTa⟩ := touching_representatives C Iv v.val
      (fun he hx hy => hsep he hx hy) (fun i hi => (hR v i).mp (mem_sdiff.mp hi).1)
    have hST (x : V) (hx : x ∈ S) (y : V) (hy : y ∈ T) : x ≠ y ∧ ¬ G.Adj x y := by
      obtain ⟨i,hi,hxc⟩ := hSF x hx
      obtain ⟨j,hj,hyc⟩ := hTF y hy
      have hne : i ≠ j := fun he => Finset.disjoint_left.mp hdis (he ▸ hi) hj
      exact hsep hne hxc hyc
    have hS (x : V) (hx : x ∈ S) : G.Adj u.val x ∧ ¬ G.Adj v.val x := by
      refine ⟨hSa x hx,?_⟩
      obtain ⟨i,hi,hxc⟩ := hSF x hx
      exact fun he => (mem_sdiff.mp hi).2 ((hR v i).mpr ⟨x,hxc,he⟩)
    have hT (x : V) (hx : x ∈ T) : G.Adj v.val x ∧ ¬ G.Adj u.val x := by
      refine ⟨hTa x hx,?_⟩
      obtain ⟨i,hi,hxc⟩ := hTF x hx
      exact fun he => (mem_sdiff.mp hi).2 ((hR u i).mpr ⟨x,hxc,he⟩)
    have hSv : v.val ∉ S := by
      intro hx
      obtain ⟨i,_,hxc⟩ := hSF _ hx
      exact hout i _ hxc v.property
    have hTu : u.val ∉ T := by
      intro hx
      obtain ⟨i,_,hxc⟩ := hTF _ hx
      exact hout i _ hxc u.property
    have htree : S.card + T.card + 2 ≤ largestInducedTreeSize G := by
      by_cases hAdj : G.Adj u.val v.val
      · exact double_star_bound u.val v.val hAdj S T hSi hTi hST hS hT hSv hTu
      obtain ⟨i,hCi,huI,hvI⟩ := hcompat.resolve_left hAdj
      have hune : u.val ≠ v.val := fun he => huv (Subtype.ext he)
      obtain ⟨B,hBc,hBu,hBv,hBC,hBtree⟩ :=
        connector_tree_of_common_component u.val v.val (C i) hune hAdj hCi huI hvI
      have leftFar (x : V) (hx : x ∈ S) (y : V) (hy : y ∈ C i) :
          x ≠ y ∧ ¬ G.Adj x y := by
        obtain ⟨j,hj,hxC⟩ := hSF x hx
        have hji : j ≠ i := fun he => (mem_sdiff.mp hj).2 (he.symm ▸ (hR v i).mpr hvI)
        exact hsep hji hxC hy
      have rightFar (x : V) (hx : x ∈ T) (y : V) (hy : y ∈ C i) :
          x ≠ y ∧ ¬ G.Adj x y := by
        obtain ⟨j,hj,hxC⟩ := hTF x hx
        have hji : j ≠ i := fun he => (mem_sdiff.mp hj).2 (he.symm ▸ (hR u i).mpr huI)
        exact hsep hji hxC hy
      have hSB : Disjoint S B := by
        apply Finset.disjoint_left.mpr
        intro x hx hb
        rcases hBC x hb with he | he | he
        · exact (hSa x hx).ne he.symm
        · exact hSv (he ▸ hx)
        · exact (leftFar x hx x he).1 rfl
      have hTB : Disjoint T B := by
        apply Finset.disjoint_left.mpr
        intro x hx hb
        rcases hBC x hb with he | he | he
        · exact hTu (he ▸ hx)
        · exact (hTa x hx).ne he.symm
        · exact (rightFar x hx x he).1 rfl
      have hSu (x : V) (hx : x ∈ S) (y : V) (hy : y ∈ B) (he : G.Adj x y) :
          y = u.val := by
        rcases hBC y hy with hu | hv | hc
        · exact hu
        · exact ((hS x hx).2 (hv ▸ he.symm)).elim
        · exact ((leftFar x hx y hc).2 he).elim
      have hTv (x : V) (hx : x ∈ T) (y : V) (hy : y ∈ B) (he : G.Adj x y) :
          y = v.val := by
        rcases hBC y hy with hu | hv | hc
        · exact ((hT x hx).2 (hu ▸ he.symm)).elim
        · exact hv
        · exact ((rightFar x hx y hc).2 he).elim
      have hh := leaf_sets_on_induced_tree B S T u.val v.val hBtree hBu hBv hSB hTB
        hSi hTi hST (fun x hx => (hSa x hx).symm) (fun x hx => (hTa x hx).symm) hSu hTv
      omega
    change (Iu ∪ Iv).card ≤ _
    rw [card_union_of_disjoint hdis,← hSc,← hTc]
    omega

/-- Separator incidence obeys the clique-style difference bound whenever every
pair of distinct separator vertices is adjacent or meets a common component. -/
theorem separator_incidence_of_common_component {I : Type*} [Fintype I] [DecidableEq I]
    [Nontrivial I] (U : Finset V) (C : I → Set V) (hn : ∀ i, (C i).Nonempty)
    (hout : ∀ i x, x ∈ C i → x ∉ U)
    (hcover : ∀ x ∉ U, ∃ i, x ∈ C i)
    (hsep : ∀ {i j : I} {x y : V}, i ≠ j → x ∈ C i → y ∈ C j → x ≠ y ∧ ¬ G.Adj x y)
    (hcompat : ∀ u v : U, u ≠ v →
      G.Adj u.val v.val ∨ ∃ i, (G.induce (C i)).Connected ∧
        (∃ x ∈ C i, G.Adj u.val x) ∧ (∃ x ∈ C i, G.Adj v.val x))
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) :
    ∃ R : U → Finset I,
      (∀ i, vertexConnectivity G ≤ (univ.filter fun u : U => i ∈ R u).card) ∧
      (∀ u, (R u).card ≤ vertexConnectivity G + 1) ∧
      (∀ u v, u ≠ v → (((R u \ R v) ∪ (R v \ R u))).card ≤ vertexConnectivity G) := by
  obtain ⟨R,_,hc,hr,hd⟩ := separator_incidence_partial U C hn hout hcover
    (fun h hx hy => hsep h hx hy) ht
  exact ⟨R,hc,hr,fun u v h => hd u v h (hcompat u v h)⟩

/-- Every clique separator satisfies the pairwise compatibility hypothesis. -/
theorem clique_separator_incidence {I : Type*} [Fintype I] [DecidableEq I] [Nontrivial I]
    (U : Finset V) (hU : G.IsClique (U : Set V)) (C : I → Set V)
    (hn : ∀ i, (C i).Nonempty)
    (hout : ∀ i x, x ∈ C i → x ∉ U)
    (hcover : ∀ x ∉ U, ∃ i, x ∈ C i)
    (hsep : ∀ {i j : I} {x y : V}, i ≠ j → x ∈ C i → y ∈ C j → x ≠ y ∧ ¬ G.Adj x y)
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) :
    ∃ R : U → Finset I,
      (∀ i, vertexConnectivity G ≤ (univ.filter fun u : U => i ∈ R u).card) ∧
      (∀ u, (R u).card ≤ vertexConnectivity G + 1) ∧
      (∀ u v, u ≠ v → (((R u \ R v) ∪ (R v \ R u))).card ≤ vertexConnectivity G) :=
  separator_incidence_of_common_component U C hn hout hcover (fun he hx hy => hsep he hx hy)
    (fun u v h => Or.inl (hU u.property v.property (fun he => h (Subtype.ext he)))) ht

end

section

open SimpleGraph Finset

/-- Under the induced-tree bound in WOWII #199, removing any clique leaves
at most one more component than the clique's order. -/
theorem clique_separator_component_bound {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (U : Finset V) (hU : G.IsClique (U : Set V))
    (hk : 0 < vertexConnectivity G)
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) :
    Nat.card (G.induce ((U : Set V)ᶜ)).ConnectedComponent ≤ U.card + 1 := by
  classical
  let W := ↥((U : Set V)ᶜ)
  let K := G.induce ((U : Set V)ᶜ)
  let I := K.ConnectedComponent
  let _ : Finite I := Finite.of_surjective K.connectedComponentMk Quot.mk_surjective
  let _ : Fintype I := Fintype.ofFinite I
  change Nat.card I ≤ _
  rw [Nat.card_eq_fintype_card]
  rcases subsingleton_or_nontrivial I with hs | hi
  · have h : Fintype.card I ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr hs
    omega
  let C (i : I) : Set V := Subtype.val '' i.supp
  have hCn (i : I) : (C i).Nonempty :=
    ⟨i.out.val,i.out,i.out_eq,rfl⟩
  have hCo (i : I) (x : V) (hx : x ∈ C i) : x ∉ U := by
    obtain ⟨y,_,rfl⟩ := hx
    exact y.property
  have hCc (x : V) (hx : x ∉ U) : ∃ i, x ∈ C i := by
    let y : W := ⟨x,hx⟩
    exact ⟨K.connectedComponentMk y,y,rfl,rfl⟩
  have hCs {i j : I} {x y : V} (hij : i ≠ j)
      (hx : x ∈ C i) (hy : y ∈ C j) : x ≠ y ∧ ¬ G.Adj x y := by
    obtain ⟨a,ha,rfl⟩ := hx
    obtain ⟨b,hb,rfl⟩ := hy
    change K.connectedComponentMk a = i at ha
    change K.connectedComponentMk b = j at hb
    have hne : K.connectedComponentMk a ≠ K.connectedComponentMk b := by rwa [ha,hb]
    exact ⟨fun he => hne (congrArg K.connectedComponentMk (Subtype.ext he)),
      fun he => hne (ConnectedComponent.connectedComponentMk_eq_of_adj (show K.Adj a b from he))⟩
  obtain ⟨R,hcol,hrow,hdist⟩ := clique_separator_incidence U hU C hCn hCo hCc
    (fun he hx hy => hCs he hx hy) ht
  simpa only [Fintype.card_coe] using incidence_clique_bound R (vertexConnectivity G) hk hcol hrow hdist

/-- The catalogue's connected, nontrivial graphs have positive vertex connectivity. -/
theorem vertexConnectivity_pos_of_connected {V : Type*} [Fintype V] [DecidableEq V]
    [Nontrivial V] {G : SimpleGraph V} (hc : G.Connected) :
    0 < vertexConnectivity G := by
  classical
  have hn : 1 < Fintype.card V := Fintype.one_lt_card
  let A : Set ℕ := {k | ∃ S : Finset V, S.card = k ∧
    (¬ (G.induce ((S : Set V)ᶜ)).Connected ∨ S.card = Fintype.card V - 1)}
  have he : vertexConnectivity G = sInf A := by
    unfold vertexConnectivity
    rw [if_neg hn.not_ge]
  have hA : A.Nonempty := by
    let v : V := Classical.choice hc.nonempty
    exact ⟨Fintype.card V - 1, univ.erase v, by simp, Or.inr (by simp)⟩
  by_contra! hk
  have hz : sInf A = 0 := by omega
  obtain ⟨S, hS, hcut | hcard⟩ := Nat.sInf_mem hA
  · have hs : S = ∅ := card_eq_zero.mp (hS.trans hz)
    apply hcut
    rw [hs, coe_empty, Set.compl_empty]
    exact G.induceUnivIso.connected_iff.mpr hc
  · omega

/-- Connected graphs satisfying WOWII #199's size hypothesis obey the clique
separator component condition. -/
theorem clique_separator_component_bound_of_connected {V : Type*} [Fintype V] [DecidableEq V]
    [Nontrivial V] {G : SimpleGraph V} (hc : G.Connected)
    (U : Finset V) (hU : G.IsClique (U : Set V))
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) :
    Nat.card (G.induce ((U : Set V)ᶜ)).ConnectedComponent ≤ U.card + 1 :=
  clique_separator_component_bound U hU (vertexConnectivity_pos_of_connected hc) ht

end

section

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- A separator has the same component-count bound if every distinct pair
of its vertices is adjacent or meets a common complementary component. -/
theorem compatible_separator_component_bound (U : Finset V)
    (hcompat : ∀ u v : U, u ≠ v →
      G.Adj u.val v.val ∨ ∃ i : (G.induce ((U : Set V)ᶜ)).ConnectedComponent,
        (∃ x : ↥((U : Set V)ᶜ), x ∈ i.supp ∧ G.Adj u.val x.val) ∧ (∃ x : ↥((U : Set V)ᶜ), x ∈ i.supp ∧ G.Adj v.val x.val))
    (hk : 0 < vertexConnectivity G)
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) :
    Nat.card (G.induce ((U : Set V)ᶜ)).ConnectedComponent ≤ U.card + 1 := by
  classical
  let W := ↥((U : Set V)ᶜ)
  let K := G.induce ((U : Set V)ᶜ)
  let I := K.ConnectedComponent
  let _ : Finite I := Finite.of_surjective K.connectedComponentMk Quot.mk_surjective
  let _ : Fintype I := Fintype.ofFinite I
  change Nat.card I ≤ _
  rw [Nat.card_eq_fintype_card]
  rcases subsingleton_or_nontrivial I with hs | hi
  · have h : Fintype.card I ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr hs
    omega
  let C (i : I) : Set V := Subtype.val '' i.supp
  have hCn (i : I) : (C i).Nonempty :=
    ⟨i.out.val,i.out,i.out_eq,rfl⟩
  have hCo (i : I) (x : V) (hx : x ∈ C i) : x ∉ U := by
    obtain ⟨y,_,rfl⟩ := hx
    exact y.property
  have hCc (x : V) (hx : x ∉ U) : ∃ i, x ∈ C i := by
    let y : W := ⟨x,hx⟩
    exact ⟨K.connectedComponentMk y,y,rfl,rfl⟩
  have hCs {i j : I} {x y : V} (hij : i ≠ j)
      (hx : x ∈ C i) (hy : y ∈ C j) : x ≠ y ∧ ¬ G.Adj x y := by
    obtain ⟨a,ha,rfl⟩ := hx
    obtain ⟨b,hb,rfl⟩ := hy
    change K.connectedComponentMk a = i at ha
    change K.connectedComponentMk b = j at hb
    have hne : K.connectedComponentMk a ≠ K.connectedComponentMk b := by rwa [ha,hb]
    exact ⟨fun he => hne (congrArg K.connectedComponentMk (Subtype.ext he)),
      fun he => hne (ConnectedComponent.connectedComponentMk_eq_of_adj (show K.Adj a b from he))⟩
  have hconn (i : I) : (G.induce (C i)).Connected := by
    let e : i.supp → C i := fun x => ⟨x.val.val,x.val,x.property,rfl⟩
    have hinj : Function.Injective e := by
      intro a b h
      exact Subtype.ext (Subtype.ext (congrArg (fun x : C i => x.val) h))
    have hsurj : Function.Surjective e := by
      rintro ⟨x,y,hy,rfl⟩
      exact ⟨⟨y,hy⟩,rfl⟩
    let iso : K.induce i.supp ≃g G.induce (C i) :=
      ⟨Equiv.ofBijective e ⟨hinj,hsurj⟩,by intro a b; rfl⟩
    exact iso.connected_iff.mp i.maximal_connected_induce_supp.1
  obtain ⟨R,hcol,hrow,hdist⟩ := separator_incidence_of_common_component U C hCn hCo hCc
    (fun he hx hy => hCs he hx hy) (by
      intro u v huv
      rcases hcompat u v huv with he | ⟨i,⟨x,hx,hux⟩,⟨y,hy,hvy⟩⟩
      · exact Or.inl he
      · exact Or.inr ⟨i,hconn i,⟨x.val,⟨x,hx,rfl⟩,hux⟩,⟨y.val,⟨y,hy,rfl⟩,hvy⟩⟩) ht
  simpa only [Fintype.card_coe] using incidence_clique_bound R (vertexConnectivity G) hk hcol hrow hdist


end

section

open Finset
open scoped BigOperators

/-- The row-distance bound need only hold on adjacent or overlapping rows
when there are at most twice the minimum column degree plus one rows, and the
adjacency-or-overlap graph is connected. -/
theorem incidence_small_cut_bound_succ {U C : Type*} [Fintype U] [Fintype C]
    [DecidableEq C] (R : U → Finset C) (adj : U → U → Prop) (k : ℕ) (hk : 0 < k)
    (hm : Fintype.card U ≤ 2 * k + 1)
    (col : ∀ i, k ≤ (univ.filter fun u => i ∈ R u).card)
    (row : ∀ u, (R u).card ≤ k + 1)
    (dist : ∀ u v, u ≠ v → (adj u v ∨ (R u ∩ R v).Nonempty) →
      ((R u \ R v) ∪ (R v \ R u)).card ≤ k)
    (connected : ∀ u v, Relation.ReflTransGen (fun a b => adj a b ∨ (R a ∩ R b).Nonempty) u v) :
    Fintype.card C ≤ Fintype.card U + 1 := by
  classical
  let m := Fintype.card U
  let c := Fintype.card C
  let E : ℕ := ∑ u : U, (R u).card
  have Hm : m ≤ 2 * k + 1 := hm
  change c ≤ m + 1
  by_contra! h
  have hc : m + 2 ≤ c := by omega
  have hE : E = ∑ i : C, (univ.filter fun u => i ∈ R u).card := by
    calc
      E = ∑ u : U, ∑ i : C, if i ∈ R u then (1 : ℕ) else 0 := by
        dsimp [E]
        apply sum_congr rfl
        intro u _
        rw [sum_boole]
        congr
        ext i
        simp
      _ = ∑ i : C, ∑ u : U, if i ∈ R u then (1 : ℕ) else 0 := sum_comm
      _ = _ := by
        apply sum_congr rfl
        intro i _
        simp
  have he₁ : k * c ≤ E := by
    rw [hE]
    calc
      _ = ∑ _i : C, k := by simp [c,mul_comm]
      _ ≤ _ := sum_le_sum fun i _ => col i
  let D (u : U) := k + 1 - (R u).card
  let Δ : ℕ := ∑ u : U, D u
  have hbalance (u : U) : (R u).card + D u = k + 1 := by
    dsimp [D]
    have h := row u
    omega
  have he₂ : E + Δ = m * (k + 1) := by
    change (∑ u : U, (R u).card) + (∑ u : U, D u) = _
    rw [← sum_add_distrib]
    simp [hbalance,m]
  have hΔ : Δ ≤ 1 := by
    have hh := Nat.mul_le_mul_left k hc
    nlinarith
  have hpos (u : U) : 0 < (R u).card := by
    have hD : D u ≤ Δ :=
      single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ u)
    have hbal := hbalance u
    omega
  have pair_large (u v : U) (hne : u ≠ v) : 2 * k + 1 ≤ (R u).card + (R v).card := by
    have hp : D u + D v ≤ Δ := by
      have hle : (∑ x ∈ ({u,v} : Finset U), D x) ≤ Δ :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
      simpa [sum_pair hne] using hle
    have hu := hbalance u
    have hv := hbalance v
    omega
  have intersection (u v : U) (hp : adj u v ∨ (R u ∩ R v).Nonempty) :
      (R u).card + (R v).card ≤ k + 2 * ((R u ∩ R v).card) := by
    by_cases he : u = v
    · subst v
      simp only [inter_self]
      omega
    have hd := dist u v he hp
    have hdis : Disjoint (R u \ R v) (R v \ R u) := by
      apply Finset.disjoint_left.mpr
      intro i hi hj
      exact (mem_sdiff.mp hi).2 (mem_sdiff.mp hj).1
    rw [card_union_of_disjoint hdis] at hd
    have h1 := card_sdiff_add_card_inter (R u) (R v)
    have h2 := card_sdiff_add_card_inter (R v) (R u)
    rw [inter_comm (R v)] at h2
    omega
  have over_of_edge (u v : U) (hp : adj u v ∨ (R u ∩ R v).Nonempty) :
      (R u ∩ R v).Nonempty := by
    by_cases he : u = v
    · subst v
      simpa using card_pos.mp (hpos u)
    apply card_pos.mp
    have h1 := pair_large u v he
    have h2 := intersection u v hp
    omega
  have over_trans (u v w : U) (huv : (R u ∩ R v).Nonempty) (hvw : (R v ∩ R w).Nonempty) :
      (R u ∩ R w).Nonempty := by
    by_cases he : u = w
    · subst w
      simpa using card_pos.mp (hpos u)
    have hu := intersection u v (Or.inr huv)
    have hw := intersection v w (Or.inr hvw)
    have hh := pair_large u w he
    have hlt : (R v).card < (R u ∩ R v).card + (R v ∩ R w).card := by omega
    obtain ⟨x,hx⟩ := inter_nonempty_of_card_lt_card_add_card inter_subset_right inter_subset_left hlt
    obtain ⟨hL,hR⟩ := mem_inter.mp hx
    exact ⟨x,mem_inter.mpr ⟨(mem_inter.mp hL).1,(mem_inter.mp hR).2⟩⟩
  have all_overlap (u v : U) : (R u ∩ R v).Nonempty := by
    induction connected u v with
    | refl => simpa using card_pos.mp (hpos u)
    | tail _ he ih => exact over_trans _ _ _ ih (over_of_edge _ _ he)
  exact (not_le.mpr h) (incidence_clique_bound R k hk col row
    (fun u v hne => dist u v hne (Or.inr (all_overlap u v))))

/-- The boundary at twice the column degree is a special case of the
small-cut incidence bound. -/
theorem incidence_small_cut_bound {U C : Type*} [Fintype U] [Fintype C]
    [DecidableEq C] (R : U → Finset C) (adj : U → U → Prop) (k : ℕ) (hk : 0 < k)
    (hm : Fintype.card U ≤ 2 * k)
    (col : ∀ i, k ≤ (univ.filter fun u => i ∈ R u).card)
    (row : ∀ u, (R u).card ≤ k + 1)
    (dist : ∀ u v, u ≠ v → (adj u v ∨ (R u ∩ R v).Nonempty) →
      ((R u \ R v) ∪ (R v \ R u)).card ≤ k)
    (connected : ∀ u v, Relation.ReflTransGen (fun a b => adj a b ∨ (R a ∩ R b).Nonempty) u v) :
    Fintype.card C ≤ Fintype.card U + 1 :=
  incidence_small_cut_bound_succ R adj k hk (by omega) col row dist connected

end

section

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Any separator of size at most twice vertex connectivity plus one leaves
at most one more component than its size under the tree-size hypothesis of WOWII #199. -/
theorem small_separator_component_bound_succ [Nontrivial V] (hG : G.Connected)
    (U : Finset V) (hU : U.card ≤ 2 * vertexConnectivity G + 1)
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) :
    Nat.card (G.induce ((U : Set V)ᶜ)).ConnectedComponent ≤ U.card + 1 := by
  classical
  have hk := vertexConnectivity_pos_of_connected hG
  let W := ↥((U : Set V)ᶜ)
  let K := G.induce ((U : Set V)ᶜ)
  let I := K.ConnectedComponent
  let _ : Finite I := Finite.of_surjective K.connectedComponentMk Quot.mk_surjective
  let _ : Fintype I := Fintype.ofFinite I
  change Nat.card I ≤ _
  rw [Nat.card_eq_fintype_card]
  rcases subsingleton_or_nontrivial I with hs | hi
  · have h : Fintype.card I ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr hs
    omega
  let C (i : I) : Set V := Subtype.val '' i.supp
  have hCn (i : I) : (C i).Nonempty := ⟨i.out.val,i.out,i.out_eq,rfl⟩
  have hCo (i : I) (x : V) (hx : x ∈ C i) : x ∉ U := by
    obtain ⟨y,_,rfl⟩ := hx
    exact y.property
  have hCc (x : V) (hx : x ∉ U) : ∃ i, x ∈ C i := by
    let y : W := ⟨x,hx⟩
    exact ⟨K.connectedComponentMk y,y,rfl,rfl⟩
  have hCs {i j : I} {x y : V} (hij : i ≠ j)
      (hx : x ∈ C i) (hy : y ∈ C j) : x ≠ y ∧ ¬ G.Adj x y := by
    obtain ⟨a,ha,rfl⟩ := hx
    obtain ⟨b,hb,rfl⟩ := hy
    change K.connectedComponentMk a = i at ha
    change K.connectedComponentMk b = j at hb
    have hne : K.connectedComponentMk a ≠ K.connectedComponentMk b := by rwa [ha,hb]
    exact ⟨fun he => hne (congrArg K.connectedComponentMk (Subtype.ext he)),
      fun he => hne (ConnectedComponent.connectedComponentMk_eq_of_adj (show K.Adj a b from he))⟩
  have hconn (i : I) : (G.induce (C i)).Connected := by
    let e : i.supp → C i := fun x => ⟨x.val.val,x.val,x.property,rfl⟩
    have hinj : Function.Injective e := by
      intro a b h
      exact Subtype.ext (Subtype.ext (congrArg (fun x : C i => x.val) h))
    have hsurj : Function.Surjective e := by
      rintro ⟨x,y,hy,rfl⟩
      exact ⟨⟨y,hy⟩,rfl⟩
    let iso : K.induce i.supp ≃g G.induce (C i) :=
      ⟨Equiv.ofBijective e ⟨hinj,hsurj⟩,by intro a b; rfl⟩
    exact iso.connected_iff.mp i.maximal_connected_induce_supp.1
  obtain ⟨R,hR,hcol,hrow,hdist⟩ := separator_incidence_partial U C hCn hCo hCc
    (fun he hx hy => hCs he hx hy) ht
  let adj (u v : U) := G.Adj u.val v.val
  have hcompat (u v : U) (huv : u ≠ v) (h : adj u v ∨ (R u ∩ R v).Nonempty) :
      ((R u \ R v) ∪ (R v \ R u)).card ≤ vertexConnectivity G := by
    apply hdist u v huv
    rcases h with h | ⟨i,hi⟩
    · exact Or.inl h
    · obtain ⟨hu,hv⟩ := mem_inter.mp hi
      exact Or.inr ⟨i,hconn i,(hR u i).mp hu,(hR v i).mp hv⟩
  have hlabel (x : V) : ∃ u : U, (x ∈ U → u.val = x) ∧
      (∀ i, x ∈ C i → i ∈ R u) := by
    by_cases hxu : x ∈ U
    · exact ⟨⟨x,hxu⟩,fun _ => rfl,fun i h => (hCo i x h hxu).elim⟩
    · obtain ⟨i,hi⟩ := hCc x hxu
      have hpos := hk.trans_le (hcol i)
      obtain ⟨u,hu⟩ := card_pos.mp hpos
      have hu' := (mem_filter.mp hu).2
      refine ⟨u,fun h => (hxu h).elim,?_⟩
      intro j hj
      have he : i = j := by
        by_contra h
        exact (hCs h hi hj).1 rfl
      exact he ▸ hu'
  choose f hf using hlabel
  have hedge (x y : V) (he : G.Adj x y) : adj (f x) (f y) ∨ (R (f x) ∩ R (f y)).Nonempty := by
    by_cases hx : x ∈ U
    · by_cases hy : y ∈ U
      · exact Or.inl (by change G.Adj (f x).val (f y).val; rwa [(hf x).1 hx,(hf y).1 hy])
      · obtain ⟨i,hi⟩ := hCc y hy
        have hm := (hf y).2 i hi
        have hn : i ∈ R (f x) := (hR _ _).mpr ⟨y,hi,by rwa [(hf x).1 hx]⟩
        exact Or.inr ⟨i,mem_inter.mpr ⟨hn,hm⟩⟩
    · obtain ⟨i,hi⟩ := hCc x hx
      have hm := (hf x).2 i hi
      by_cases hy : y ∈ U
      · have hn : i ∈ R (f y) := (hR _ _).mpr ⟨x,hi,by rw [(hf y).1 hy]; exact he.symm⟩
        exact Or.inr ⟨i,mem_inter.mpr ⟨hm,hn⟩⟩
      · obtain ⟨j,hj⟩ := hCc y hy
        have hij : i = j := by
          by_contra hn
          exact (hCs hn hi hj).2 he
        subst j
        exact Or.inr ⟨i,mem_inter.mpr ⟨hm,(hf y).2 i hj⟩⟩
  have hreach (u v : U) :
      Relation.ReflTransGen (fun a b => adj a b ∨ (R a ∩ R b).Nonempty) u v := by
    have hf' (x : U) : f x.val = x := Subtype.ext ((hf x.val).1 x.property)
    have hh {x y : V} (h : Relation.ReflTransGen G.Adj x y) :
        Relation.ReflTransGen (fun a b => adj a b ∨ (R a ∩ R b).Nonempty) (f x) (f y) := by
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hxy ih => exact ih.tail (hedge _ _ hxy)
    have h := hh ((G.reachable_iff_reflTransGen _ _).mp (hG u.val v.val))
    rwa [hf',hf'] at h
  have hu : Fintype.card U ≤ 2 * vertexConnectivity G + 1 := by simpa only [Fintype.card_coe] using hU
  simpa only [Fintype.card_coe] using
    incidence_small_cut_bound_succ R adj (vertexConnectivity G) hk hu hcol hrow hcompat hreach

/-- In particular, the separator may have order twice the vertex connectivity. -/
theorem small_separator_component_bound [Nontrivial V] (hG : G.Connected)
    (U : Finset V) (hU : U.card ≤ 2 * vertexConnectivity G)
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) :
    Nat.card (G.induce ((U : Set V)ᶜ)).ConnectedComponent ≤ U.card + 1 :=
  small_separator_component_bound_succ hG U (by omega) ht

end

open SimpleGraph

/-- Prove the component bound for the remaining large separators with an incompatible pair. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    G.Connected → Gᶜ.Connected → 3 ≤ vertexConnectivity G →
    vertexConnectivity G + 2 ≤ G.indepNum →
    largestInducedTreeSize G - 2 ≤ vertexConnectivity G →
    ∀ U : Finset V, 2 * vertexConnectivity G + 1 < U.card →
      (¬ ∀ u v : U, u ≠ v →
        G.Adj u.val v.val ∨ ∃ i : (G.induce ((U : Set V)ᶜ)).ConnectedComponent,
          (∃ x : ↥((U : Set V)ᶜ), x ∈ i.supp ∧ G.Adj u.val x.val) ∧
          (∃ x : ↥((U : Set V)ᶜ), x ∈ i.supp ∧ G.Adj v.val x.val)) →
      Nat.card (G.induce ((U : Set V)ᶜ)).ConnectedComponent ≤ U.card + 1

/-- Find a spanning path when every separator satisfies the necessary component bound. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    G.Connected → Gᶜ.Connected → 3 ≤ vertexConnectivity G →
    vertexConnectivity G + 2 ≤ G.indepNum →
    largestInducedTreeSize G - 2 ≤ vertexConnectivity G →
    (∀ U : Finset V, Nat.card (G.induce ((U : Set V)ᶜ)).ConnectedComponent ≤ U.card + 1) →
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian

theorem main : H1 → H2 → OMA.R_WrittenOnTheWallII_GraphConjecture199_conjecture199_R1.H2 := by
  intro hsmall htrace V _ _ G hc hk _ ht
  let _ : Nonempty V := hc.nonempty
  by_cases ha : G.indepNum ≤ vertexConnectivity G + 1
  · exact hamiltonian_of_indepNum_le_vertexConnectivity_add_one hc ha
  have hα : vertexConnectivity G + 2 ≤ G.indepNum := by omega
  have hco : Gᶜ.Connected := by
    by_contra h
    exact ha (indepNum_le_connectivity_add_one_of_compl_disconnected G h ht)
  have hn : Nontrivial V := by
    rcases subsingleton_or_nontrivial V with hs | hn
    · obtain ⟨s,hs'⟩ := G.exists_isNIndepSet_indepNum
      have hle := Finset.card_le_univ s
      have hcard := Fintype.card_le_one_iff_subsingleton.mpr hs
      rw [hs'.card_eq] at hle
      omega
    · exact hn
  apply htrace G hc hco hk hα ht
  intro U
  by_cases small : U.card ≤ 2 * vertexConnectivity G + 1
  · exact small_separator_component_bound_succ hc U small ht
  by_cases compat : ∀ u v : U, u ≠ v →
        G.Adj u.val v.val ∨ ∃ i : (G.induce ((U : Set V)ᶜ)).ConnectedComponent,
          (∃ x : ↥((U : Set V)ᶜ), x ∈ i.supp ∧ G.Adj u.val x.val) ∧
          (∃ x : ↥((U : Set V)ᶜ), x ∈ i.supp ∧ G.Adj v.val x.val)
  · exact compatible_separator_component_bound U compat (by omega) ht
  exact hsmall G hc hco hk hα ht U (by omega) compat

end OMA.R_WrittenOnTheWallII_GraphConjecture199_conjecture199_R1_H2_R1
