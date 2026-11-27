import FormalConjectures.ErdosProblems.«23»
import Mathlib

/-! # A two-vertex reduction for triangle-free graphs of order 25

Balogh, Clemen and Lidický's asymptotic high-density theorem applies to
balanced blow-ups with 25 equal fibers. Averaging a transversal pulls its
cut back to the original graph. Below 100 edges, discard a minimum-degree
vertex twice. Restoring the vertices in reverse costs at most six edges.
McKay's complete extremal catalogue on 23 vertices lists six graphs
requiring twenty deletions, with 100, 101, 102, 103, 104 and 105 edges.
The two inputs below are precisely the restrictions of these results needed here.
Sources: arXiv:2103.14179, Theorem 2(b); B. McKay, Extremal graphs for
bipartization of triangle-free graphs, minbip23_20x.g6. -/

namespace OMA.R_Erdos23_erdos_23_variants_n5_R2
open Finset SimpleGraph Filter
open scoped Classical

-- The large-order theorem, restricted to balanced blow-ups. Both counts
-- use ordered pairs, so each undirected edge contributes twice.
def H1 : Prop := ∀ᶠ r : ℕ in atTop, ∀ G : SimpleGraph (Fin 25), G.CliqueFree 3 →
    3197*(25*r)*(25*r-1) ≤ 10000*r^2*(∑ i,∑ j,if G.Adj i j then 1 else 0) →
    ∃ c : Fin 25 → Fin r → Bool, 25*(∑ i,∑ j,∑ a,∑ b,
      if G.Adj i j ∧ c i a=c j b then (1:ℕ) else 0) ≤ 2*(25*r)^2

-- McKay's finite catalogue rules out the extremal twenty-deletion case
-- in any induced 23-vertex graph with at most 99 edges.
def H2 : Prop := ∀ G : SimpleGraph (Fin 25), G.CliqueFree 3 → ∀ W : Finset (Fin 25),
    W.card=23 → (∑ i ∈ W,∑ j ∈ W,if G.Adj i j then 1 else 0) ≤ (198:ℕ) →
    ∃ c : Fin 25 → Bool,
      (∑ i ∈ W,∑ j ∈ W,if G.Adj i j ∧ c i=c j then 1 else 0) ≤ (38:ℕ)


lemma erase_total {V : Type*} [DecidableEq V] (W : Finset V) {x : V} (hx : x∈W)
    (w : V → V → ℕ) (sym : ∀ i j,w i j = w j i) (diag : w x x=0) :
    (∑ i ∈ W, ∑ j ∈ W, w i j) =
      (∑ i ∈ W.erase x, ∑ j ∈ W.erase x, w i j) + 2*(∑ j ∈ W.erase x,w x j) := by
  let T := W.erase x
  have nx : x∉T := notMem_erase _ _
  have eqW : insert x T = W := insert_erase hx
  change (∑ i ∈ W, ∑ j ∈ W, w i j) = (∑ i ∈ T,∑ j ∈ T,w i j)+2*∑ j ∈ T,w x j
  conv_lhs => rw [←eqW]
  simp only [sum_insert nx,diag,zero_add,sum_add_distrib]
  have swap : (∑ i ∈ T,w i x) = ∑ i ∈ T,w x i := sum_congr rfl (fun i _ => sym i x)
  omega

lemma choose_low {V : Type*} [DecidableEq V] (W : Finset V) (hW : W.Nonempty)
    (w : V → V → ℕ) (diag : ∀ x,w x x=0) :
    ∃ x ∈ W, W.card*(∑ j ∈ W.erase x,w x j) ≤ ∑ i ∈ W,∑ j ∈ W,w i j := by
  classical
  let d (i : V) := ∑ j ∈ W,w i j
  obtain ⟨x,hx,low⟩ := W.exists_min_image d hW
  refine ⟨x,hx,?_⟩
  have dr := sum_erase_add W (w x) hx
  rw [diag,add_zero] at dr
  rw [dr]
  change W.card*d x ≤ ∑ i ∈ W,d i
  simpa using sum_le_sum (s:=W) (f:=fun _ => d x) low

lemma extend_color {V : Type*} [DecidableEq V] (W : Finset V) {x : V} (hx : x∈W)
    (w : V → V → ℕ) (sym : ∀ i j,w i j=w j i) (diag : ∀ i,w i i=0) (c : V → Bool) :
    ∃ f : V → Bool, (∑ i ∈ W, ∑ j ∈ W, if f i=f j then w i j else 0) ≤
      (∑ i ∈ W.erase x,∑ j ∈ W.erase x,if c i=c j then w i j else 0) +
        2*((∑ j ∈ W.erase x,w x j)/2) := by
  classical
  let T := W.erase x
  let count (b : Bool) := ∑ j ∈ T, if b=c j then w x j else 0
  have partition : count false + count true = ∑ j ∈ T,w x j := by
    dsimp [count]; rw [←sum_add_distrib]; apply sum_congr rfl; intro j _; cases c j <;> simp
  have pick : ∃ b : Bool, count b ≤ (∑ j ∈ T,w x j)/2 := by
    by_cases b : count false ≤ count true
    · exact ⟨false,by omega⟩
    · exact ⟨true,by omega⟩
  obtain ⟨b,hb⟩ := pick
  let f i := if i=x then b else c i
  let cost (i j : V) := if f i=f j then w i j else 0
  have sy (i j : V) : cost i j=cost j i := by
    by_cases e : f i=f j
    · simp [cost,e,sym i j]
    · simp [cost,e,Ne.symm e]
  have eq := erase_total W hx cost sy (by simp [cost,diag])
  have agree (i : V) (h : i∈T) : f i=c i := if_neg (mem_erase.mp h).1
  have row : (∑ j ∈ T,cost x j) = count b := by
    apply sum_congr rfl; intro j hj; simp [cost,agree _ hj,f]
  have sub : (∑ i ∈ T,∑ j ∈ T,cost i j) =
      ∑ i ∈ T,∑ j ∈ T,if c i=c j then w i j else 0 := by
    apply sum_congr rfl; intro i hi; apply sum_congr rfl; intro j hj
    simp [cost,agree _ hi,agree _ hj]
  refine ⟨f,?_⟩
  change (∑ i ∈ W,∑ j ∈ W,cost i j) ≤ (∑ i ∈ T,∑ j ∈ T,if c i=c j then w i j else 0)+2*((∑ j ∈ T,w x j)/2)
  change (∑ i ∈ W,∑ j ∈ W,cost i j) = (∑ i ∈ T,∑ j ∈ T,cost i j)+2*(∑ j ∈ T,cost x j) at eq
  rw [eq,sub,row]; omega

lemma sum_two_fibers (r : ℕ) {x y : Fin 25} (xy : x≠y) (w : Fin r → Fin r → ℕ) :
    (∑ f : Fin 25 → Fin r, w (f x) (f y)) = r^23*(∑ a,∑ b,w a b) := by
  classical
  let A := {j : Fin 25 // j≠x}
  let v : A := ⟨y,Ne.symm xy⟩
  let B := {j : A // j≠v}
  let e : (Fin 25 → Fin r) ≃ Fin r × (Fin r × (B → Fin r)) :=
    (Equiv.funSplitAt x (Fin r)).trans ((Equiv.refl (Fin r)).prodCongr (Equiv.funSplitAt v (Fin r)))
  have ca : Fintype.card A = 24 := by simp [A]
  have cb : Fintype.card B = 23 := by simp [B,Fintype.card_subtype_compl,ca]
  calc
    _ = ∑ t : Fin r × (Fin r × (B → Fin r)), w t.1 t.2.1 := e.sum_comp (fun t => w t.1 t.2.1)
    _ = _ := by
      simp only [Fintype.sum_prod_type,sum_const,card_univ,Fintype.card_fun,Fintype.card_fin,cb,nsmul_eq_mul,mul_sum,Nat.cast_id]

lemma pull_back_cut {r : ℕ} (hr : 0<r) (G : SimpleGraph (Fin 25)) (c : Fin 25 → Fin r → Bool)
    (bound : (∑ i, ∑ j, ∑ a, ∑ b,
      if G.Adj i j ∧ c i a=c j b then 1 else 0) ≤ 50*r^2) :
    ∃ f : Fin 25 → Bool, (∑ i,∑ j, if G.Adj i j ∧ f i=f j then 1 else 0) ≤ (50:ℕ) := by
  classical
  let a (f : Fin 25 → Fin r) i j : ℕ := if G.Adj i j ∧ c i (f i)=c j (f j) then 1 else 0
  have total : (∑ f, ∑ i, ∑ j, a f i j) ≤ ∑ _f : Fin 25 → Fin r, (50:ℕ) := by
    rw [sum_comm]
    calc
      _ = ∑ i, ∑ j, ∑ f, a f i j := by apply sum_congr rfl; intro i _; rw [sum_comm]
      _ = r^23*(∑ i,∑ j,∑ a,∑ b,if G.Adj i j ∧ c i a=c j b then (1:ℕ) else 0) := by
        rw [mul_sum]; apply sum_congr rfl; intro i _
        rw [mul_sum]; apply sum_congr rfl; intro j _
        by_cases h : i=j
        · subst j; simp [a]
        · exact sum_two_fibers r h (fun u v => if G.Adj i j ∧ c i u=c j v then 1 else 0)
      _ ≤ r^23*(50*r^2) := Nat.mul_le_mul_left _ bound
      _ = _ := by simp; ring
  let : Nonempty (Fin r) := ⟨⟨0,hr⟩⟩
  obtain ⟨f,_,h⟩ := Finset.exists_le_of_sum_le (Finset.univ_nonempty) total
  exact ⟨fun i => c i (f i),h⟩

lemma edge_sum {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ i, ∑ j, if G.Adj i j then 1 else 0) = 2*G.edgeFinset.card := by
  classical
  rw [←G.sum_degrees_eq_twice_card_edges]
  apply sum_congr rfl
  intro i _
  simp [←G.card_neighborFinset_eq_degree,G.neighborFinset_eq_filter,Finset.sum_boole]

lemma cut_subgraph (G : SimpleGraph (Fin 25)) (c : Fin 25 → Bool)
    (cut : (∑ i,∑ j, if G.Adj i j ∧ c i=c j then 1 else 0) ≤ (50:ℕ)) :
    ∃ H : SimpleGraph (Fin 25), H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ 25 := by
  let H : SimpleGraph (Fin 25) := {
    Adj := fun i j => G.Adj i j ∧ c i≠c j
    symm := ⟨fun _ _ h => ⟨h.1.symm,Ne.symm h.2⟩⟩
    loopless := ⟨fun v h => h.2 rfl⟩ }
  let M : SimpleGraph (Fin 25) := {
    Adj := fun i j => G.Adj i j ∧ c i=c j
    symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
    loopless := ⟨fun v h => G.loopless.irrefl v h.1⟩ }
  letI : DecidableRel H.Adj := fun _ _ => Classical.propDecidable _
  letI : DecidableRel M.Adj := fun _ _ => Classical.propDecidable _
  let e : Bool ≃ Fin 2 := Fintype.equivFin Bool
  refine ⟨H,fun _ _ h => h.1,⟨SimpleGraph.Coloring.mk (fun i => e (c i))
    (fun h eq => h.2 (e.injective eq))⟩,?_⟩
  have diff : G.edgeFinset \ H.edgeFinset = M.edgeFinset := by
    apply Finset.ext
    intro t
    induction t using Sym2.inductionOn with
    | _ i j =>
      constructor
      · intro h
        obtain ⟨hg,hn⟩ := Finset.mem_sdiff.mp h
        have ge : G.Adj i j := SimpleGraph.mem_edgeFinset.mp hg
        have eq : c i=c j := by
          by_contra ne
          exact hn (SimpleGraph.mem_edgeFinset.mpr (show H.Adj i j from ⟨ge,ne⟩))
        exact SimpleGraph.mem_edgeFinset.mpr (show M.Adj i j from ⟨ge,eq⟩)
      · intro h
        have mh : M.Adj i j := SimpleGraph.mem_edgeFinset.mp h
        apply Finset.mem_sdiff.mpr
        exact ⟨SimpleGraph.mem_edgeFinset.mpr mh.1,fun hh =>
          (show H.Adj i j from SimpleGraph.mem_edgeFinset.mp hh).2 mh.2⟩
  have edges := edge_sum M
  have bound : 2*M.edgeFinset.card ≤ (50:ℕ) := by
    apply edges.symm.le.trans
    apply le_trans _ cut
    apply le_of_eq
    apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _
    by_cases h : G.Adj i j ∧ c i=c j
    · simp [h,show M.Adj i j from h]
    · simp [h,show ¬M.Adj i j from h]
  rw [diff]; omega

theorem main : H1 → H2 → type_of% @Erdos23.erdos_23.variants.n5 := by
  intro dense catalogue G triangleFree
  classical
  let w (i j : Fin 25) : ℕ := if G.Adj i j then 1 else 0
  let cost (W : Finset (Fin 25)) := ∑ i ∈ W, ∑ j ∈ W,w i j
  let bad (W : Finset (Fin 25)) (c : Fin 25 → Bool) :=
    ∑ i ∈ W,∑ j ∈ W, if c i=c j then w i j else 0
  have sym (i j : Fin 25) : w i j = w j i := by simp only [w,G.adj_comm i j]
  have diag (i : Fin 25) : w i i=0 := by simp [w]
  have express (W : Finset (Fin 25)) (c : Fin 25 → Bool) :
      bad W c = ∑ i ∈ W,∑ j ∈ W,if G.Adj i j ∧ c i=c j then 1 else 0 := by
    apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _
    by_cases h : c i=c j <;> simp [h,w]
  by_cases many : 100 ≤ G.edgeFinset.card
  · obtain ⟨r,large,hr⟩ := (dense.and (eventually_ge_atTop 1)).exists
    have q : 200 ≤ ∑ i,∑ j,if G.Adj i j then 1 else (0:ℕ) := by rw [edge_sum]; omega
    have dens : 3197*(25*r)*(25*r-1) ≤ 10000*r^2*(∑ i,∑ j,if G.Adj i j then 1 else 0) := calc
      _ ≤ 3197*(25*r)*(25*r) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ ≤ 10000*r^2*200 := by nlinarith [sq_nonneg (r:ℤ)]
      _ ≤ _ := Nat.mul_le_mul_left _ q
    obtain ⟨c,hc⟩ := large G triangleFree dens
    have size : 2*(25*r)^2=25*(50*r^2) := by ring
    rw [size] at hc
    obtain ⟨f,hf⟩ := pull_back_cut (by omega : 0<r) G c (Nat.le_of_mul_le_mul_left hc (by decide))
    exact cut_subgraph G f hf
  · let W : Finset (Fin 25) := univ
    have cw : W.card=25 := by simp [W]
    have sparse : cost W ≤ 198 := by change (∑ i,∑ j, if G.Adj i j then 1 else 0) ≤ 198; rw [edge_sum]; omega
    obtain ⟨x,hx,dx⟩ := choose_low W (card_pos.mp (by omega)) w diag
    let T := W.erase x
    let d := ∑ j ∈ T,w x j
    have ct : T.card=24 := by dsimp [T]; rw [card_erase_of_mem hx,cw]
    change W.card*d ≤ cost W at dx
    have ex : cost W=cost T+2*d := erase_total W hx w sym (diag x)
    obtain ⟨y,hy,dy⟩ := choose_low T (card_pos.mp (by omega)) w diag
    let U := T.erase y
    let e := ∑ j ∈ U,w y j
    have cu : U.card=23 := by dsimp [U]; rw [card_erase_of_mem hy,ct]
    change T.card*e ≤ cost T at dy
    have ey : cost T=cost U+2*e := erase_total T hy w sym (diag y)
    rw [cw] at dx
    rw [ct] at dy
    obtain ⟨c,base⟩ := catalogue G triangleFree U cu (show cost U ≤ 198 by omega)
    rw [←express] at base
    obtain ⟨f,hf⟩ := extend_color T hy w sym diag c
    change bad T f ≤ bad U c + 2*(e/2) at hf
    obtain ⟨g,hg⟩ := extend_color W hx w sym diag f
    change bad W g ≤ bad T f + 2*(d/2) at hg
    have dg : d ≤ 7 := by omega
    have allowance : 2*(e/2) + 2*(d/2) ≤ 12 := by
      by_cases lo : d≤3 <;> omega
    apply cut_subgraph G g
    change (∑ i ∈ W,∑ j ∈ W,if G.Adj i j ∧ g i=g j then 1 else 0) ≤ 50
    rw [←express]; omega

end OMA.R_Erdos23_erdos_23_variants_n5_R2
