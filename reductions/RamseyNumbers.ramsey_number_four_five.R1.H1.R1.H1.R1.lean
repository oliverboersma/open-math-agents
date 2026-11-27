import OMAReductions.R_RamseyNumbers_ramsey_number_four_five_R1_H1_R1
import Mathlib

/-!
# A rooted classification of the Ramsey(4,4,16) graphs

No Ramsey(3,4,9) graph exists, so both neighbourhoods at a vertex of a
Ramsey(4,4,16) graph have at most eight vertices. Their sizes sum to fifteen.
After taking a complement if needed, the vertex has seven neighbours and
eight non-neighbours. The short atlases classify the induced graphs on
these blocks. A gluing certificate then identifies the graph.

The graph words encode the catalogued graphs in graph6 column order.
Source: https://users.cecs.anu.edu.au/~bdm/data/ramsey.html.
-/

open Finset SimpleGraph

namespace OMA.R_RamseyNumbers_ramsey_number_four_five_R1_H1_R1_H1_R1

/-- The needed bounds and small atlases for Ramsey(3,4). -/
def H1 : Prop :=
  (∀ G : SimpleGraph (Fin 9), G.CliqueFree 3 → Gᶜ.CliqueFree 4 → False) ∧
  (∀ G : SimpleGraph (Fin 7), G.CliqueFree 3 → Gᶜ.CliqueFree 4 →
    ∃ w ∈ ([480904,944196,944204,483585,746529,1581345,666115,1714691,946323] : List Nat),
      ∃ e : Fin 7 ≃ Fin 7, ∀ i j : Fin 7, i < j →
        (G.Adj (e i) (e j) ↔ w.testBit (j.val*(j.val-1)/2+i.val) = true)) ∧
  (∀ G : SimpleGraph (Fin 8), G.CliqueFree 3 → Gᶜ.CliqueFree 4 →
    ∃ w ∈ ([153315680,206327905,60117131] : List Nat),
      ∃ e : Fin 8 ≃ Fin 8, ∀ i j : Fin 8, i < j →
        (G.Adj (e i) (e j) ↔ w.testBit (j.val*(j.val-1)/2+i.val) = true))

/-- Classify all gluings in the labelled seven-by-eight split. -/
def H2 : Prop :=
  ∀ G : SimpleGraph (Fin 16), G.CliqueFree 4 → Gᶜ.CliqueFree 4 →
    (∀ i : Fin 16, G.Adj (Fin.last 15) i ↔ i.val < 7) →
    ∀ a ∈ ([480904,944196,944204,483585,746529,1581345,666115,1714691,946323] : List Nat),
    ∀ b ∈ ([153315680,206327905,60117131] : List Nat),
      (∀ i j : Fin 7, i < j → (G.Adj ((Fin.castAdd 8 i).castSucc) ((Fin.castAdd 8 j).castSucc) ↔
        a.testBit (j.val*(j.val-1)/2+i.val) = true)) →
      (∀ i j : Fin 8, i < j → (Gᶜ.Adj ((Fin.natAdd 7 i).castSucc) ((Fin.natAdd 7 j).castSucc) ↔
        b.testBit (j.val*(j.val-1)/2+i.val) = true)) →
      ∃ w : Nat, (w = 0xcb94e332f53ae143a3b6933356490b ∨ w = 0xacb96354eb266b51b2b6553699403b) ∧
        ∃ e : Fin 16 ≃ Fin 16, ∀ i j : Fin 16, i < j →
          (G.Adj (e i) (e j) ↔ w.testBit (j.val*(j.val-1)/2+i.val) = true)

/-- The neighbours of a vertex form a Ramsey(3,4) graph. -/
theorem neighbor_valid {n : Nat} {G : SimpleGraph (Fin 16)} {p : Fin 16}
    (hG : G.CliqueFree 4) (hC : Gᶜ.CliqueFree 4) (f : Fin n ↪ Fin 16)
    (adj : ∀ i, G.Adj p (f i)) : (G.comap f).CliqueFree 3 ∧ (G.comap f)ᶜ.CliqueFree 4 := by
  let e := SimpleGraph.Embedding.comap f G
  constructor
  · intro S hS
    have mapped : G.IsNClique 3 (S.map f) :=
      OMA.R_RamseyNumbers_ramsey_number_four_five_R1.map_clique e hS
    apply hG _ (mapped.insert (a := p) ?_)
    intro b hb
    obtain ⟨i,_,rfl⟩ := mem_map.mp hb
    exact adj i
  · exact hC.comap (SimpleGraph.Embedding.complEquiv e).isContained

private theorem degree_le (atlas : H1) (G : SimpleGraph (Fin 16)) [DecidableRel G.Adj]
    (p : Fin 16) (hG : G.CliqueFree 4) (hC : Gᶜ.CliqueFree 4) : G.degree p ≤ 8 := by
  by_contra! more
  obtain ⟨f,hf⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin 9) (s := G.neighborFinset p) (by simpa using (show 9 ≤ G.degree p by omega))
  have adj (i : Fin 9) : G.Adj p (f i) := (G.mem_neighborFinset p (f i)).mp (hf ⟨i,rfl⟩)
  obtain ⟨no3,no4⟩ := neighbor_valid hG hC f adj
  exact atlas.1 (G.comap f) no3 no4

private theorem exists_root_relabel {G : SimpleGraph (Fin 16)} (p : Fin 16)
    (a : Fin 7 ↪ Fin 16) (b : Fin 8 ↪ Fin 16)
    (ha : ∀ i, G.Adj p (a i)) (hb : ∀ j, Gᶜ.Adj p (b j)) :
    ∃ e : Fin 16 ≃ Fin 16, e (Fin.last 15) = p ∧ (∀ i, e ((Fin.castAdd 8 i).castSucc) = a i) ∧
      (∀ j, e ((Fin.natAdd 7 j).castSucc) = b j) ∧ (∀ x : Fin 16, (G.comap e).Adj (Fin.last 15) x ↔ x.val < 7) := by
  have apart : Disjoint (Set.range a) (Set.range b) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨i,rfl⟩ ⟨j,he⟩
    exact ((G.compl_adj p (b j)).mp (hb j)).2 (by rw [he]; exact ha i)
  let pre : Fin 15 ↪ Fin 16 := Fin.Embedding.append apart
  have pre_left (i : Fin 7) : pre (Fin.castAdd 8 i) = a i := Fin.append_left a b i
  have pre_right (j : Fin 8) : pre (Fin.natAdd 7 j) = b j := Fin.append_right a b j
  have absent : p ∉ Set.range pre := by
    rintro ⟨v,hv⟩
    obtain ⟨x,rfl⟩ := (finSumFinEquiv : Fin 7 ⊕ Fin 8 ≃ Fin 15).surjective v
    rcases x with i | j
    · rw [finSumFinEquiv_apply_left,pre_left] at hv
      have h := ha i
      rw [hv] at h
      exact G.loopless.irrefl _ h
    · rw [finSumFinEquiv_apply_right,pre_right] at hv
      have h := hb j
      rw [hv] at h
      exact Gᶜ.loopless.irrefl _ h
  let f := Fin.Embedding.snoc pre absent
  let e : Fin 16 ≃ Fin 16 := Equiv.ofBijective f ⟨f.injective,Finite.surjective_of_injective f.injective⟩
  have hr : e (Fin.last 15) = p := by
    change Fin.Embedding.snoc pre absent (Fin.last 15) = p
    exact Fin.Embedding.snoc_last
  have ea (i : Fin 7) : e ((Fin.castAdd 8 i).castSucc) = a i := by
    change Fin.Embedding.snoc pre absent (Fin.castAdd 8 i).castSucc = a i
    rw [Fin.Embedding.snoc_castSucc,pre_left]
  have eb (j : Fin 8) : e ((Fin.natAdd 7 j).castSucc) = b j := by
    change Fin.Embedding.snoc pre absent (Fin.natAdd 7 j).castSucc = b j
    rw [Fin.Embedding.snoc_castSucc,pre_right]
  refine ⟨e,hr,ea,eb,?_⟩
  intro x
  refine Fin.lastCases ?_ (fun v => ?_) x
  · change G.Adj (e (Fin.last 15)) (e (Fin.last 15)) ↔ (15 : Nat) < 7
    rw [hr]
    simp
  · obtain ⟨y,rfl⟩ := (finSumFinEquiv : Fin 7 ⊕ Fin 8 ≃ Fin 15).surjective v
    rcases y with i | j
    · rw [finSumFinEquiv_apply_left]
      change G.Adj (e (Fin.last 15)) (e ((Fin.castAdd 8 i).castSucc)) ↔ i.val < 7
      rw [hr,ea]
      exact ⟨fun _ => i.isLt,fun _ => ha i⟩
    · rw [finSumFinEquiv_apply_right]
      change G.Adj (e (Fin.last 15)) (e ((Fin.natAdd 7 j).castSucc)) ↔ 7+j.val < 7
      rw [hr,eb]
      exact ⟨fun h => (((G.compl_adj p (b j)).mp (hb j)).2 h).elim,
        fun h => (Nat.not_lt_of_ge (Nat.le_add_right ..) h).elim⟩

private theorem degree_seven (atlas : H1) (glue : H2)
    (G : SimpleGraph (Fin 16)) [DecidableRel G.Adj] (p : Fin 16)
    (hG : G.CliqueFree 4) (hC : Gᶜ.CliqueFree 4) (seven : G.degree p = 7) :
    ∃ w : Nat, (w = 0xcb94e332f53ae143a3b6933356490b ∨ w = 0xacb96354eb266b51b2b6553699403b) ∧
      ∃ e : Fin 16 ≃ Fin 16, ∀ i j : Fin 16, i < j →
        (G.Adj (e i) (e j) ↔ w.testBit (j.val*(j.val-1)/2+i.val) = true) := by
  have eight : Gᶜ.degree p = 8 := by rw [G.degree_compl,Fintype.card_fin,seven]
  have cardL : (G.neighborFinset p).card = 7 := by simpa using seven
  have cardR : (Gᶜ.neighborFinset p).card = 8 := by simpa using eight
  let L : Fin 7 ↪ Fin 16 := ((G.neighborFinset p).equivFinOfCardEq cardL).symm.toEmbedding.trans
    (Function.Embedding.subtype (· ∈ G.neighborFinset p))
  let R : Fin 8 ↪ Fin 16 := ((Gᶜ.neighborFinset p).equivFinOfCardEq cardR).symm.toEmbedding.trans
    (Function.Embedding.subtype (· ∈ Gᶜ.neighborFinset p))
  have hl (i : Fin 7) : G.Adj p (L i) :=
    (G.mem_neighborFinset p (L i)).mp (((G.neighborFinset p).equivFinOfCardEq cardL).symm i).property
  have hr (i : Fin 8) : Gᶜ.Adj p (R i) :=
    (Gᶜ.mem_neighborFinset p (R i)).mp (((Gᶜ.neighborFinset p).equivFinOfCardEq cardR).symm i).property
  have hcc : Gᶜᶜ.CliqueFree 4 := by simpa only [compl_compl] using hG
  obtain ⟨lf,lc⟩ := neighbor_valid hG hC L hl
  obtain ⟨rf,rc⟩ := neighbor_valid hC hcc R hr
  obtain ⟨u,hu,eu,ulaw⟩ := atlas.2.1 (G.comap L) lf lc
  obtain ⟨v,hv,ev,vlaw⟩ := atlas.2.2 (Gᶜ.comap R) rf rc
  let a := eu.toEmbedding.trans L
  let b := ev.toEmbedding.trans R
  obtain ⟨e,_,ea,eb,rooted⟩ := exists_root_relabel p a b
    (fun i => hl (eu i)) (fun j => hr (ev j))
  let K := G.comap e
  have iso : K ≃g G := SimpleGraph.Iso.comap e G
  have comps : Kᶜ = Gᶜ.comap e := by
    ext x y
    simp only [K, SimpleGraph.compl_adj, SimpleGraph.comap_adj]
    exact and_congr e.injective.ne_iff.symm Iff.rfl
  have kl (i j : Fin 7) (hij : i < j) :
      K.Adj ((Fin.castAdd 8 i).castSucc) ((Fin.castAdd 8 j).castSucc) ↔
        u.testBit (j.val*(j.val-1)/2+i.val) = true := by
    change G.Adj (e ((Fin.castAdd 8 i).castSucc)) (e ((Fin.castAdd 8 j).castSucc)) ↔ _
    rw [ea,ea]
    exact ulaw i j hij
  have kr (i j : Fin 8) (hij : i < j) :
      Kᶜ.Adj ((Fin.natAdd 7 i).castSucc) ((Fin.natAdd 7 j).castSucc) ↔
        v.testBit (j.val*(j.val-1)/2+i.val) = true := by
    rw [comps]
    change Gᶜ.Adj (e ((Fin.natAdd 7 i).castSucc)) (e ((Fin.natAdd 7 j).castSucc)) ↔ _
    rw [eb,eb]
    exact vlaw i j hij
  obtain ⟨w,hw,perm,law⟩ := glue K (hG.comap iso.toEmbedding.isContained)
    (hC.comap (SimpleGraph.Embedding.complEquiv iso.toEmbedding).isContained) rooted u hu v hv kl kr
  exact ⟨w,hw,perm.trans e,law⟩

private theorem flip_from_permutation (w : Nat) (f : Fin 16 → Fin 16)
    (hf : Function.Injective f) (edges : ∀ i j : Fin 16, i < j →
      (w.testBit (max (f i).val (f j).val*(max (f i).val (f j).val-1)/2 + min (f i).val (f j).val) = false ↔
        w.testBit (j.val*(j.val-1)/2+i.val) = true)) :
    ∃ e : Fin 16 ≃ Fin 16, ∀ i j : Fin 16, i < j →
      (w.testBit (max (e i).val (e j).val*(max (e i).val (e j).val-1)/2 + min (e i).val (e j).val) = false ↔
        w.testBit (j.val*(j.val-1)/2+i.val) = true) :=
  ⟨Equiv.ofBijective f ⟨hf,Finite.surjective_of_injective hf⟩,edges⟩

set_option maxRecDepth 8000 in
private theorem self_flip (w : Nat)
    (hw : w = 0xcb94e332f53ae143a3b6933356490b ∨ w = 0xacb96354eb266b51b2b6553699403b) :
    ∃ e : Fin 16 ≃ Fin 16, ∀ i j : Fin 16, i < j →
      (w.testBit (max (e i).val (e j).val*(max (e i).val (e j).val-1)/2 + min (e i).val (e j).val) = false ↔
        w.testBit (j.val*(j.val-1)/2+i.val) = true) := by
  rcases hw with rfl | rfl
  · apply flip_from_permutation _ (fun i => ⟨([8,14,11,12,10,9,15,13,7,2,6,3,1,5,4,0][i.val]! : Nat)%16,
      Nat.mod_lt _ (by decide)⟩) <;> decide +kernel
  · apply flip_from_permutation _ (fun i => ⟨([9,10,14,12,15,11,13,8,1,4,7,3,5,2,6,0][i.val]! : Nat)%16,
      Nat.mod_lt _ (by decide)⟩) <;> decide +kernel

private theorem ordered_bits {G : SimpleGraph (Fin 16)} (w : Nat) (f : Fin 16 → Fin 16)
    (law : ∀ i j : Fin 16, i < j → (G.Adj (f i) (f j) ↔ w.testBit (j.val*(j.val-1)/2+i.val) = true))
    {i j : Fin 16} (ne : i ≠ j) : G.Adj (f i) (f j) ↔
      w.testBit (max i.val j.val*(max i.val j.val-1)/2+min i.val j.val) = true := by
  rcases lt_or_gt_of_ne ne with lt | gt
  · have le : i.val ≤ j.val := lt.le
    simpa only [max_eq_right le,min_eq_left le] using law i j lt
  · have le : j.val ≤ i.val := gt.le
    simpa only [max_eq_left le,min_eq_right le] using (G.adj_comm (f i) (f j)).trans (law j i gt)

theorem main : H1 → H2 → OMA.R_RamseyNumbers_ramsey_number_four_five_R1_H1_R1.H1 := by
  classical
  intro atlas glue G hG hC
  let p := Fin.last 15
  have hcc : Gᶜᶜ.CliqueFree 4 := by simpa only [compl_compl] using hG
  have up := degree_le atlas G p hG hC
  have upC := degree_le atlas Gᶜ p hC hcc
  have sum : Gᶜ.degree p = 15-G.degree p := by rw [G.degree_compl,Fintype.card_fin]
  by_cases h7 : G.degree p = 7
  · exact degree_seven atlas glue G p hG hC h7
  have h7c : Gᶜ.degree p = 7 := by omega
  obtain ⟨w,hw,e,edges⟩ := degree_seven atlas glue Gᶜ p hC hcc h7c
  obtain ⟨f,flip⟩ := self_flip w hw
  refine ⟨w,hw,f.trans e,?_⟩
  intro i j hij
  change G.Adj (e (f i)) (e (f j)) ↔ _
  have ne : f i ≠ f j := f.injective.ne hij.ne
  have ne' : e (f i) ≠ e (f j) := e.injective.ne ne
  calc
    _ ↔ ¬ Gᶜ.Adj (e (f i)) (e (f j)) := by simp [SimpleGraph.compl_adj,ne']
    _ ↔ w.testBit (max (f i).val (f j).val*(max (f i).val (f j).val-1)/2+min (f i).val (f j).val) = false := by
      rw [ordered_bits w e edges ne]
      simp
    _ ↔ _ := flip i j hij

end OMA.R_RamseyNumbers_ramsey_number_four_five_R1_H1_R1_H1_R1