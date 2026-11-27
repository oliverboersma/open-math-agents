import OMAReductions.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1

/-! Non-neighborhood deficiency for triangle-free Ramsey graphs. -/
open SimpleGraph Finset
namespace OMA.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1_H2_R1

lemma lift_card {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (hi : Gᶜ.CliqueFree 8) (S : Finset (Gᶜ.neighborFinset v))
    (cl : ((G.induce ((Gᶜ.neighborFinset v : Finset V) : Set V))ᶜ).IsClique S) :
    S.card ≤ 6 := by
  classical
  let B := Gᶜ.neighborFinset v
  let f : B ↪ V := Function.Embedding.subtype _
  have free : Gᶜ.IsClique (S.map f) := by
    intro x hx y hy hxy
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
    obtain ⟨b,hb,rfl⟩ := mem_map.mp hy
    exact ⟨hxy,(cl ha hb (fun h => hxy (congrArg f h))).2⟩
  have hv : v ∉ S.map f := by
    intro hm
    obtain ⟨b,_,eq⟩ := mem_map.mp hm
    exact ((Gᶜ.mem_neighborFinset _ _).mp b.2).ne eq.symm
  have ext : Gᶜ.IsClique (insert v (S.map f)) := free.insert (by
    intro b hb _
    obtain ⟨i,_,rfl⟩ := mem_map.mp hb
    exact (Gᶜ.mem_neighborFinset _ _).mp i.2)
  have lim : (insert v (S.map f)).card < 8 := lt_of_not_ge (fun h =>
    hi.mono h _ ⟨by simpa only [Finset.coe_insert] using ext,rfl⟩)
  rw [card_insert_of_notMem hv,card_map] at lim
  omega

theorem neighborhood_data {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (ht : G.CliqueFree 3) (hi : Gᶜ.CliqueFree 8) :
    let N := G.neighborFinset v
    let B := Gᶜ.neighborFinset v
    let D := G.induce (B : Set V)
    let A (i : N) := (univ : Finset B).filter fun x => G.Adj i.val x.val
    D.CliqueFree 3 ∧ Dᶜ.CliqueFree 7 ∧
      (∀ i, Dᶜ.IsClique (A i)) ∧
      (∀ (J : Finset N) (S : Finset B), Dᶜ.IsClique S → (∀ a ∈ J, Disjoint (A a) S) → J.card+S.card≤7) ∧
      N.card + (∑ a, (A a).card) ≤ ∑ a ∈ N, G.degree a := by
  classical
  let N := G.neighborFinset v
  let B := Gᶜ.neighborFinset v
  let D := G.induce (B : Set V)
  let A (i : N) := (univ : Finset B).filter fun x => G.Adj i.val x.val
  let f : B ↪ V := Function.Embedding.subtype _
  let g : N ↪ V := Function.Embedding.subtype _
  let em : D ↪g G := SimpleGraph.Embedding.comap f G
  have nd (a : N) := (G.mem_neighborFinset v a.val).mp a.2
  have bd (a : B) := (Gᶜ.mem_neighborFinset v a.val).mp a.2
  have split (a : N) (b : B) : a.val≠b.val := fun eq => (bd b).2 (eq ▸ nd a)
  have nr (a b : N) : ¬G.Adj a.val b.val := by
    intro h
    exact G.isIndepSet_neighborSet_of_triangleFree ht v (nd a) (nd b) h.ne h
  change D.CliqueFree 3 ∧ Dᶜ.CliqueFree 7 ∧ (∀ i, Dᶜ.IsClique (A i)) ∧ _ ∧ _
  refine ⟨CliqueFree.comap em.isContained ht,?_,?_,?_,?_⟩
  · intro S hS
    have h := lift_card G v hi S hS.isClique
    have eq := hS.card_eq
    omega
  · intro i a ha b hb hne
    refine ⟨hne,?_⟩
    intro h
    exact G.isIndepSet_neighborSet_of_triangleFree ht i.val (mem_filter.mp ha).2 (mem_filter.mp hb).2
      (Subtype.val_injective.ne hne) h
  · intro J S cl dis
    let X := J.map g
    let Y := S.map f
    have apart : Disjoint X Y := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      obtain ⟨a,_,rfl⟩ := mem_map.mp hx
      obtain ⟨b,_,eq⟩ := mem_map.mp hy
      exact split a b eq.symm
    have sx : Gᶜ.IsClique X := by
      intro u hu w hw hne
      obtain ⟨a,_,rfl⟩ := mem_map.mp hu
      obtain ⟨b,_,rfl⟩ := mem_map.mp hw
      exact ⟨hne,nr a b⟩
    have sy : Gᶜ.IsClique Y := by
      intro u hu w hw hne
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hu
      obtain ⟨b,hb,rfl⟩ := mem_map.mp hw
      exact ⟨hne,(cl ha hb (fun h => hne (congrArg f h))).2⟩
    have cross (u : V) (hu : u∈X) (w : V) (hw : w∈Y) : Gᶜ.Adj u w := by
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hu
      obtain ⟨b,hb,rfl⟩ := mem_map.mp hw
      exact ⟨split a b,fun h => Finset.disjoint_left.mp (dis a ha) (mem_filter.mpr ⟨mem_univ _,h⟩) hb⟩
    have full : Gᶜ.IsClique (X ∪ Y) := by
      intro u hu w hw hne
      rcases hu with hu|hu <;> rcases hw with hw|hw
      · exact sx hu hw hne
      · exact cross _ hu _ hw
      · exact (cross _ hw _ hu).symm
      · exact sy hu hw hne
    have lim : (X ∪ Y).card < 8 := lt_of_not_ge (fun h =>
      hi.mono h _ ⟨by simpa only [Finset.coe_union] using full,rfl⟩)
    rw [card_union_of_disjoint apart,card_map,card_map] at lim
    omega
  · have each (a : N) : 1 + (A a).card ≤ G.degree a.val := by
      let Y := (A a).map f
      have nv : v ∉ Y := by
        rintro mem
        obtain ⟨b,_,eq⟩ := mem_map.mp mem
        exact (bd b).1 eq.symm
      have sub : insert v Y ⊆ G.neighborFinset a.val := by
        intro w hw
        rcases mem_insert.mp hw with rfl|mem
        · exact (G.mem_neighborFinset _ _).mpr (nd a).symm
        · obtain ⟨b,hb,rfl⟩ := mem_map.mp mem
          exact (G.mem_neighborFinset _ _).mpr (mem_filter.mp hb).2
      have le := card_le_card sub
      rw [card_insert_of_notMem nv,card_map,G.card_neighborFinset_eq_degree] at le
      omega
    have total := Finset.sum_le_sum (s := (univ : Finset N)) (fun a _ => each a)
    change N.card + (∑ a : N,(A a).card) ≤ ∑ a ∈ N,G.degree a
    rw [← Finset.sum_coe_sort N (fun i => G.degree i)]
    simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.mul_one,
      Fintype.card_coe,Nat.cast_id] using total


theorem removed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ht : G.CliqueFree 3) (v : Fin n) :
    let N := G.neighborFinset v
    let B := Gᶜ.neighborFinset v
    let D := G.induce (B : Set (Fin n))
    D.edgeFinset.card+(∑ i ∈ N, G.degree i) ≤ G.edgeFinset.card := by
  let N := G.neighborFinset v
  let B := Gᶜ.neighborFinset v
  let D := G.induce (B : Set (Fin n))
  let U : Finset (Fin n) := univ
  let W (X Y : Finset (Fin n)) := ∑ i ∈ X, ∑ j ∈ Y, (if G.Adj i j then 1 else 0 : ℕ)
  have flip (X Y) : W X Y = W Y X := by
    unfold W
    rw [Finset.sum_comm]
    simp only [G.adj_comm]
  have partition (X Y) : W X Y + W Xᶜ Y = W U Y := Finset.sum_add_sum_compl X _
  have total (X) : W X U=∑ i ∈ X, G.degree i := by
    simp [W,U,SimpleGraph.degree,SimpleGraph.neighborFinset_eq_filter]
  have vanish : W N N=0 := by
    apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro b hb
    have un : ¬G.Adj a b := fun adj => G.isIndepSet_neighborSet_of_triangleFree ht v
      ((G.mem_neighborFinset _ _).mp ha) ((G.mem_neighborFinset _ _).mp hb) adj.ne adj
    simp [un]
  have inside : B ⊆ Nᶜ := fun i hi => Finset.mem_compl.mpr fun h =>
    ((Gᶜ.mem_neighborFinset _ _).mp hi).2 ((G.mem_neighborFinset _ _).mp h)
  have inc (X Y Z : Finset (Fin n)) (sub : X ⊆ Y) : W X Z ≤ W Y Z :=
    Finset.sum_le_sum_of_subset_of_nonneg sub (by intros; omega)
  have le : W B B ≤ W Nᶜ Nᶜ :=
    (inc B Nᶜ B inside).trans ((flip Nᶜ B) ▸ inc B Nᶜ Nᶜ inside)
  have db : W B B = 2*D.edgeFinset.card := by
    calc
      W B B = ∑ i : B, ∑ j ∈ B, (if G.Adj i.val j then 1 else 0 : ℕ) :=
        (Finset.sum_coe_sort B _).symm
      _ = ∑ i : B, ∑ j : B, (if D.Adj i j then 1 else 0 : ℕ) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (Finset.sum_coe_sort B (fun j => if G.Adj i.val j then 1 else 0)).symm
      _ = ∑ i : B, D.degree i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [SimpleGraph.degree,SimpleGraph.neighborFinset_eq_filter]
        exact Finset.sum_boole (R:=ℕ) (D.Adj i) univ
      _ = _ := D.sum_degrees_eq_twice_card_edges
  have p1 := partition N U
  have p2 := partition N N
  have p3 := partition N Nᶜ
  have f1 := flip Nᶜ U
  have f2 := flip N U
  have f3 := flip Nᶜ N
  have a := total N
  have b := total U
  have all : (∑ i ∈ U,G.degree i) = 2*G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  change D.edgeFinset.card+(∑ i ∈ N,G.degree i)≤G.edgeFinset.card
  omega

theorem sum_neighbor_degrees {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (∑ v, ∑ w ∈ G.neighborFinset v, G.degree w) = ∑ v, G.degree v ^ 2 := by
  simp only [SimpleGraph.neighborFinset_eq_filter,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  calc
    (∑ v, if G.Adj v w then G.degree w else 0) =
        ∑ v ∈ univ.filter (G.Adj w), G.degree w := by
          rw [Finset.sum_filter]
          simp only [G.adj_comm]
    _ = G.degree w^2 := by
      rw [← G.neighborFinset_eq_filter,Finset.sum_const,G.card_neighborFinset_eq_degree,nsmul_eq_mul,pow_two]
      norm_cast


/-- The smaller 22-vertex (3,7) density estimate, weakened by one edge. -/
def H1 : Prop := ∀ (G : SimpleGraph (Fin 22)) [DecidableRel G.Adj],
  G.CliqueFree 3 → Gᶜ.CliqueFree 7 → 59 ≤ G.edgeFinset.card

/-- Forbid extensions of the sparse non-neighborhoods on 19 to 21 vertices.
Rows are independent and describe the neighbors of each added vertex.
An independent set chosen from the added vertices and the untouched old
vertices gives exactly the displayed cardinality constraint. -/
def H2 : Prop := ∀ (j : Fin 3) (V W : Type) [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W],
  Fintype.card V = 21-j.val → Fintype.card W=j.val+5 →
  ∀ (K : SimpleGraph V) [DecidableRel K.Adj], K.CliqueFree 3 → Kᶜ.CliqueFree 7 →
    K.edgeFinset.card ≤ (![52,46,38] : Fin 3 → ℕ) j →
    ∀ A : W → Finset V, (∀ a, Kᶜ.IsClique (A a)) →
    (∀ S : Finset V, Kᶜ.IsClique S →
      ((univ : Finset W).filter (fun a => Disjoint (A a) S)).card+S.card≤7) →
    85 ≤ K.edgeFinset.card + Fintype.card W + ∑ a, (A a).card

lemma restrict22 (small : H1) {V : Type} [Fintype V] [DecidableEq V] (K : SimpleGraph V) [DecidableRel K.Adj]
    (hcard : 22 ≤ Fintype.card V) (tr : K.CliqueFree 3) (hi : Kᶜ.CliqueFree 7) : 59≤K.edgeFinset.card := by
  classical
  obtain ⟨f, _⟩ := Function.Embedding.exists_of_card_le_finset (α := Fin 22) (s := (univ : Finset V)) (by simpa using hcard)
  let D := K.comap f
  let e : D ↪g K := SimpleGraph.Embedding.comap f K
  let ec := SimpleGraph.Embedding.complEquiv e
  have a := small D (CliqueFree.comap e.isContained tr) (CliqueFree.comap ec.isContained hi)
  have b := Fintype.card_le_of_embedding e.toCopy.mapEdgeSet
  rw [D.card_edgeSet,K.card_edgeSet] at b
  exact a.trans b

theorem main : H1 → H2 → OMA.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1.H2 := by
  intro small glue G inst tri ind
  by_contra! few
  let Z (v) := ∑ a ∈ G.neighborFinset v,G.degree a
  have localBound (v : Fin 27) : 53 + 5*G.degree v + Z v ≤ G.degree v ^ 2 + G.edgeFinset.card := by
    let N := G.neighborFinset v
    let B := Gᶜ.neighborFinset v
    let D := G.induce (B : Set (Fin 27))
    let A (i : N) := (univ : Finset B).filter fun x => G.Adj i.val x.val
    obtain ⟨t,h,rows,cover,incident⟩ := neighborhood_data G v tri ind
    have nc : Fintype.card N = G.degree v := (Fintype.card_coe _).trans (G.card_neighborFinset_eq_degree _)
    have deg := (show G.degree v < 8 from OMA.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1.degree_lt G tri ind v)
    have bc : Fintype.card B=27-1-G.degree v := by
      rw [Fintype.card_coe]
      change Gᶜ.degree v = 27-1-G.degree v
      rw [G.degree_compl,Fintype.card_fin]
    have rem : D.edgeFinset.card+Z v ≤ G.edgeFinset.card := removed G tri v
    have inc : Fintype.card N+(∑ a,(A a).card) ≤ Z v := by simpa only [Fintype.card_coe] using incident
    by_cases lo : G.degree v ≤ 4
    · have card : 22 ≤ Fintype.card B := by omega
      have bound := restrict22 small D card t h
      have poly : ∀ k : Fin 5, 53+5*k.val ≤ k.val^2+59 := by decide
      have pv := poly ⟨G.degree v,by omega⟩
      change 53+5*G.degree v ≤ G.degree v^2+59 at pv
      omega
    · let j : Fin 3 := ⟨G.degree v-5,by omega⟩
      have dv : Fintype.card N = j.val+5 := by dsimp [j]; omega
      have bv : Fintype.card B = 21-j.val := by dsimp [j]; omega
      have above : (![52,46,38] : Fin 3 → ℕ) j < D.edgeFinset.card := by
        by_contra! below
        have cost := glue j B N bv dv D t h below A rows (fun S hS =>
          cover _ S hS (fun a ha => (Finset.mem_filter.mp ha).2))
        omega
      have poly : ∀ i : Fin 3, 53+5*(i.val+5) ≤ (i.val+5)^2+((![52,46,38] : Fin 3 → ℕ) i+1) := by decide
      have pv := poly j
      have d : j.val+5=G.degree v := dv.symm.trans nc
      rw [d] at pv
      omega
  have sum := Finset.sum_le_sum (s := (univ : Finset (Fin 27))) (fun v _ => localBound v)
  have z : (∑ v,Z v) = ∑ v,G.degree v^2 := sum_neighbor_degrees G
  have hand := G.sum_degrees_eq_twice_card_edges
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_id,z,hand] at sum
  omega
end OMA.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1_H2_R1
