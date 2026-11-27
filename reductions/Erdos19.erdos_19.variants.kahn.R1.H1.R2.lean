import OMAReductions.R_Erdos19_erdos_19_variants_kahn_R1
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Card

/-!
# Reduce the bounded-rank list-colouring step to uniform hypergraphs

Give each edge its own padding vertices and then complete the degrees using
the construction in Corollary 16 of Katsamaktsis, Letzter, Pokrovskiy and Sudakov,
[Ascending subgraph decomposition](https://doi.org/10.1016/j.jctb.2025.01.003).
Pull back the colours along the resulting incidence-preserving embeddings.

The rank-two argument is credited to the earlier reduction by @mucoucah
([#5024](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5024)).
The hypotheses keep the positive palette condition of the original step.
-/

namespace OMA.R_Erdos19_erdos_19_variants_kahn_R1_H1_R2

open Finset

namespace Erdos19Uniform

variable {V : Type} [Fintype V] [DecidableEq V]

private theorem padding (r D : ℕ) (hD : 0 < D) (H : Finset (Finset V))
    (hlin : ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1)
    (hrank : ∀ A ∈ H, A.card ≤ r)
    (hdeg : ∀ v, (H.filter (fun A => v ∈ A)).card ≤ D) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (f : V ↪ W)
      (g : Finset V ↪ Finset W) (K : Finset (Finset W)),
      (∀ A ∈ H, g A ∈ K) ∧
      (∀ A v, f v ∈ g A ↔ v ∈ A) ∧
      (∀ A ∈ K, A.card = r) ∧
      (∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).card ≤ 1) ∧
      ∀ v, (K.filter (fun A => v ∈ A)).card ≤ D := by
  classical
  let W := V ⊕ (Finset V × Fin r)
  let f : V ↪ W := ⟨Sum.inl, Sum.inl_injective⟩
  let pad (A : Finset V) : Finset W :=
    A.map f ∪ (univ.filter fun i : Fin r => i.val < r - A.card).image (fun i => Sum.inr (A,i))
  have hin (A : Finset V) (v : V) : f v ∈ pad A ↔ v ∈ A := by simp [pad,f]
  have hout (A B : Finset V) (i : Fin r) :
      Sum.inr (B,i) ∈ pad A ↔ B = A ∧ i.val < r-A.card := by
    simp [pad,f,eq_comm, and_comm]
  let g : Finset V ↪ Finset W := ⟨pad, fun A B h => by
    ext v
    rw [← hin A v, ← hin B v, h]⟩
  let K := H.map g
  refine ⟨W, inferInstance, inferInstance, f, g, K, fun A h => mem_map.mpr ⟨A,h,rfl⟩,
    hin, ?_, ?_, ?_⟩
  · intro A hA
    obtain ⟨B,hB,rfl⟩ := mem_map.mp hA
    change (pad B).card = r
    have hdis : Disjoint (B.map f) ((univ.filter fun i : Fin r => i.val < r-B.card).image
        (fun i => Sum.inr (B,i))) := by
      apply disjoint_left.mpr
      intro x hx hy
      obtain ⟨v,_,rfl⟩ := mem_map.mp hx
      simp [f] at hy
    have hcount : (univ.filter fun i : Fin r => i.val < r-B.card).card = r-B.card := by
      let e : Fin (r-B.card) ↪ Fin r := ⟨fun i => ⟨i.val, i.isLt.trans_le (Nat.sub_le ..)⟩,
        fun _ _ h => Fin.ext (congrArg (fun j : Fin r => j.val) h)⟩
      have he : univ.filter (fun i : Fin r => i.val < r-B.card) = univ.map e := by
        ext i
        simp only [mem_filter,mem_univ,true_and,mem_map]
        constructor
        · intro h
          exact ⟨⟨i.val,h⟩,Fin.ext rfl⟩
        · rintro ⟨j,rfl⟩
          exact j.isLt
      rw [he,card_map,card_univ,Fintype.card_fin]
    unfold pad
    rw [card_union_of_disjoint hdis,card_map,card_image_of_injective _ (by
      intro x y he
      exact congrArg Prod.snd (Sum.inr.inj he)),hcount]
    have := hrank B hB
    omega
  · intro E hE F hF hAB
    obtain ⟨A,hA,rfl⟩ := mem_map.mp hE
    obtain ⟨B,hB,rfl⟩ := mem_map.mp hF
    have hn : A ≠ B := fun h => hAB (congrArg g h)
    apply card_le_one.mpr
    have old (x : W) (hx : x ∈ g A ∩ g B) : ∃ v ∈ A ∩ B, f v = x := by
      rcases x with x|⟨C,i⟩
      · exact ⟨x,mem_inter.mpr ⟨(hin A x).mp (mem_inter.mp hx).1,
          (hin B x).mp (mem_inter.mp hx).2⟩,rfl⟩
      · exact (hn (((hout A C i).mp (mem_inter.mp hx).1).1.symm.trans
          ((hout B C i).mp (mem_inter.mp hx).2).1)).elim
    intro x hx y hy
    obtain ⟨u,hu,rfl⟩ := old x hx
    obtain ⟨v,hv,rfl⟩ := old y hy
    exact congrArg f (card_le_one.mp (hlin A hA B hB hn) u hu v hv)
  · intro v
    rcases v with v|⟨A,i⟩
    · have he : K.filter (fun E => f v ∈ E) = (H.filter (fun E => v ∈ E)).map g := by
        ext E
        simp only [K,mem_filter,mem_map]
        constructor
        · rintro ⟨⟨A,hA,rfl⟩,hv⟩
          exact ⟨A,⟨hA,(hin A v).mp hv⟩,rfl⟩
        · rintro ⟨A,⟨hA,hv⟩,rfl⟩
          exact ⟨⟨A,hA,rfl⟩,(hin A v).mpr hv⟩
      change (K.filter (fun E => f v ∈ E)).card ≤ D
      rw [he,card_map]
      exact hdeg v
    · apply le_trans _ hD
      apply card_le_one.mpr
      intro E hE F hF
      obtain ⟨hE,hVE⟩ := mem_filter.mp hE
      obtain ⟨hF,hVF⟩ := mem_filter.mp hF
      obtain ⟨B,_,rfl⟩ := mem_map.mp hE
      obtain ⟨C,_,rfl⟩ := mem_map.mp hF
      exact congrArg g (((hout B A i).mp hVE).1.symm.trans ((hout C A i).mp hVF).1)


/-- The degree-completion round from Corollary 16 of Katsamaktsis, Letzter,
Pokrovskiy and Sudakov, restricted to linear hypergraphs. -/
private theorem augment {r D : ℕ} (hr : 2 ≤ r) (H : Finset (Finset V))
    (hlin : ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1)
    (hunif : ∀ A ∈ H, A.card = r) :
    ∃ (f : V ↪ Fin r × V) (K : Finset (Finset (Fin r × V))),
      (∀ A ∈ H, A.map f ∈ K) ∧
      (∀ A ∈ K, A.card = r) ∧
      (∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).card ≤ 1) ∧
      ∀ i : Fin r × V, (K.filter (fun A => i ∈ A)).card =
        (H.filter (fun A => i.2 ∈ A)).card +
        if (H.filter (fun A => i.2 ∈ A)).card < D then 1 else 0 := by
  classical
  let side (j : Fin r) : V ↪ Fin r × V := ⟨(j, ·),fun _ _ h => congrArg Prod.snd h⟩
  let line (v : V) : Finset (Fin r × V) :=
    univ.map ⟨(·, v),fun _ _ h => congrArg Prod.fst h⟩
  have hs (i j : Fin r) (v : V) (A : Finset V) :
      (i,v) ∈ A.map (side j) ↔ i=j ∧ v∈A := by
    constructor
    · intro h
      obtain ⟨w,hw,he⟩ := mem_map.mp h
      have he' : w=v := congrArg Prod.snd he
      exact ⟨(congrArg Prod.fst he).symm, he' ▸ hw⟩
    · rintro ⟨rfl,hv⟩
      exact mem_map.mpr ⟨v,hv,rfl⟩
  have hb (i : Fin r) (v w : V) : (i,v)∈line w ↔ v=w := by
    constructor
    · intro h
      obtain ⟨j,_,he⟩ := mem_map.mp h
      exact (congrArg Prod.snd he).symm
    · rintro rfl
      exact mem_map.mpr ⟨i,mem_univ _,rfl⟩
  let old := (univ : Finset (Fin r)).biUnion (fun j => H.map (Finset.mapEmbedding (side j)).toEmbedding)
  let deficient := univ.filter (fun v => (H.filter (fun A => v∈A)).card < D)
  let added := deficient.image line
  let K := old ∪ added
  let z : Fin r := ⟨0,by omega⟩
  have ho (E : Finset (Fin r × V)) : E∈old ↔ ∃ j, ∃ A∈H, A.map (side j)=E := by
    simp [old, Finset.mapEmbedding]
  have ha (E : Finset (Fin r × V)) : E∈added ↔ ∃ v∈deficient, line v=E := mem_image
  have hdis : Disjoint old added := by
    apply disjoint_left.mpr
    intro E hE hE'
    obtain ⟨i,A,_,rfl⟩ := (ho E).mp hE
    obtain ⟨v,_,hv⟩ := (ha _).mp hE'
    have hj : ∃ j : Fin r, j≠i := by
      let j0 : Fin r := ⟨0,by omega⟩
      let j1 : Fin r := ⟨1,by omega⟩
      by_cases h : j0=i
      · exact ⟨j1,fun he => by have hh:= congrArg Fin.val (he.trans h.symm); simp [j0,j1] at hh⟩
      · exact ⟨j0,h⟩
    obtain ⟨j,hj⟩ := hj
    exact hj ((hs j i v A).mp (hv ▸ (hb j v v).mpr rfl)).1
  refine ⟨side z,K,fun A hA => mem_union_left _ ((ho _).mpr ⟨z,A,hA,rfl⟩),?_,?_,?_⟩
  · intro E hE
    rcases mem_union.mp hE with h|h
    · obtain ⟨i,A,hA,rfl⟩ := (ho _).mp h
      rw [card_map,hunif A hA]
    · obtain ⟨v,_,rfl⟩ := (ha _).mp h
      simp [line]
  · intro E hE F hF hEF
    apply card_le_one.mpr
    rintro ⟨i,v⟩ hx ⟨j,w⟩ hy
    obtain ⟨hxe,hxf⟩ := mem_inter.mp hx
    obtain ⟨hye,hyf⟩ := mem_inter.mp hy
    rcases mem_union.mp hE with hE|hE <;> rcases mem_union.mp hF with hF|hF
    · obtain ⟨k,A,hA,rfl⟩ := (ho _).mp hE
      obtain ⟨l,B,hB,rfl⟩ := (ho _).mp hF
      obtain ⟨hk,hvA⟩ := (hs i k v A).mp hxe
      obtain ⟨hl,hvB⟩ := (hs i l v B).mp hxf
      subst k l
      have hAB : A≠B := fun h => hEF (congrArg (Finset.map (side i)) h)
      exact Prod.ext ((hs j i w A).mp hye).1.symm
        (card_le_one.mp (hlin A hA B hB hAB) _ (mem_inter.mpr ⟨hvA,hvB⟩)
          _ (mem_inter.mpr ⟨((hs j i w A).mp hye).2,((hs j i w B).mp hyf).2⟩))
    · obtain ⟨k,A,_,rfl⟩ := (ho _).mp hE
      obtain ⟨u,_,rfl⟩ := (ha _).mp hF
      exact Prod.ext (((hs i k v A).mp hxe).1.trans ((hs j k w A).mp hye).1.symm)
        (((hb i v u).mp hxf).trans ((hb j w u).mp hyf).symm)
    · obtain ⟨u,_,rfl⟩ := (ha _).mp hE
      obtain ⟨k,A,_,rfl⟩ := (ho _).mp hF
      exact Prod.ext (((hs i k v A).mp hxf).1.trans ((hs j k w A).mp hyf).1.symm)
        (((hb i v u).mp hxe).trans ((hb j w u).mp hye).symm)
    · obtain ⟨u,_,rfl⟩ := (ha _).mp hE
      obtain ⟨w,_,rfl⟩ := (ha _).mp hF
      exact (hEF (congrArg line (((hb i v u).mp hxe).symm.trans ((hb i v w).mp hxf)))).elim
  · rintro ⟨i,v⟩
    have hO : old.filter (fun E => (i,v)∈E) =
        (H.filter (fun A => v∈A)).map (Finset.mapEmbedding (side i)).toEmbedding := by
      ext E
      rw [mem_filter,ho,mem_map]
      constructor
      · rintro ⟨⟨j,A,hA,rfl⟩,hv⟩
        obtain ⟨rfl,hvA⟩ := (hs i j v A).mp hv
        exact ⟨A,mem_filter.mpr ⟨hA,hvA⟩,rfl⟩
      · rintro ⟨A,hA,rfl⟩
        obtain ⟨hA,hvA⟩ := mem_filter.mp hA
        exact ⟨⟨i,A,hA,rfl⟩,(hs i i v A).mpr ⟨rfl,hvA⟩⟩
    have hA : added.filter (fun E => (i,v)∈E) =
        if v∈deficient then {line v} else ∅ := by
      ext E
      rw [mem_filter,ha]
      by_cases hv : v∈deficient
      · rw [if_pos hv,mem_singleton]
        constructor
        · rintro ⟨⟨w,_,rfl⟩,h⟩
          exact congrArg line ((hb i v w).mp h).symm
        · rintro rfl
          exact ⟨⟨v,hv,rfl⟩,(hb i v v).mpr rfl⟩
      · simp only [if_neg hv,notMem_empty,iff_false]
        rintro ⟨⟨w,hw,rfl⟩,h⟩
        exact hv (((hb i v w).mp h).symm ▸ hw)
    change ((old ∪ added).filter (fun E => (i,v)∈E)).card = _
    rw [filter_union,card_union_of_disjoint (hdis.mono (filter_subset ..) (filter_subset ..)),
      hO,hA,card_map]
    by_cases h : (H.filter (fun A => v∈A)).card < D
    · simp [deficient,h]
    · simp [deficient,h]

private theorem rounds (r D : ℕ) (hr : 2 ≤ r) (k t : ℕ) :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (H : Finset (Finset V)),
      (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1) →
      (∀ A ∈ H, A.card=r) →
      (∀ i, min t D ≤ (H.filter (fun A => i∈A)).card ∧ (H.filter (fun A => i∈A)).card ≤ D) →
      ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
        (f : V ↪ W) (K : Finset (Finset W)),
        (∀ A ∈ H, A.map f ∈ K) ∧
        (∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).card ≤ 1) ∧
        (∀ A ∈ K, A.card=r) ∧
        ∀ i, min (t+k) D ≤ (K.filter (fun A => i∈A)).card ∧ (K.filter (fun A => i∈A)).card ≤ D := by
  induction k generalizing t with
  | zero =>
    intro V _ _ H hlin hu hd
    exact ⟨V,inferInstance,inferInstance,Function.Embedding.refl V,H,
      fun A hA => by simpa using hA,hlin,hu,by simpa using hd⟩
  | succ k ih =>
    intro V _ _ H hlin hu hd
    obtain ⟨f,K,hf,hKu,hKl,hKd⟩ := augment (D:=D) hr H hlin hu
    have hstep (i : Fin r × V) :
        min (t+1) D ≤ (K.filter (fun A => i∈A)).card ∧ (K.filter (fun A => i∈A)).card ≤ D := by
      rw [hKd]
      have hi := hd i.2
      split <;> omega
    obtain ⟨W,fw,dw,g,L,hg,hLl,hLu,hLd⟩ := ih (t+1) _ K hKl hKu hstep
    refine ⟨W,fw,dw,f.trans g,L,?_,hLl,hLu,?_⟩
    · intro A hA
      rw [←map_map]
      exact hg _ (hf A hA)
    · simpa only [show t+1+k=t+(k+1) by omega] using hLd

/-- Extend a rank-bounded linear hypergraph to an exactly uniform and regular linear
hypergraph, preserving the incidence of the original vertices and edges. -/
theorem regular_uniform_embedding (r D n : ℕ) (hr : 2 ≤ r) (hD : 0 < D)
    (H : Finset (Finset (Fin n)))
    (hlin : ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1)
    (hsize : ∀ A ∈ H, A.card ≤ r) (hdeg : ∀ i, (H.filter (fun A => i∈A)).card ≤ D) :
    ∃ n' : ℕ, ∃ f : Fin n ↪ Fin n', ∃ g : Finset (Fin n) ↪ Finset (Fin n'),
    ∃ K : Finset (Finset (Fin n')),
      (∀ A ∈ H, g A ∈ K) ∧ (∀ A i, f i ∈ g A ↔ i∈A) ∧
      (∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).card ≤ 1) ∧
      (∀ A ∈ K, A.card=r) ∧ ∀ i, (K.filter (fun A => i∈A)).card=D := by
  obtain ⟨W,fw,dw,f,g,K,hg,hfg,hKu,hKl,hKd⟩ := padding r D hD H hlin hsize hdeg
  let _ : Fintype W := fw
  let _ : DecidableEq W := dw
  obtain ⟨X,fx,dx,a,L,ha,hLl,hLu,hLd⟩ := rounds r D hr D 0 W K hKl hKu
    (fun i => ⟨Nat.zero_le _,hKd i⟩)
  let _ : Fintype X := fx
  let _ : DecidableEq X := dx
  let e := Fintype.equivFin X
  let E := (Finset.mapEmbedding e.toEmbedding).toEmbedding
  let F := (Finset.mapEmbedding a).toEmbedding
  refine ⟨Fintype.card X,f.trans (a.trans e.toEmbedding),g.trans (F.trans E),L.map E,
    ?_,?_,?_,?_,?_⟩
  · exact fun A hA => mem_map.mpr ⟨_,ha _ (hg A hA),rfl⟩
  · intro A i
    change e (a (f i)) ∈ ((g A).map a).map e.toEmbedding ↔ i∈A
    exact (mem_map' e.toEmbedding).trans ((mem_map' a).trans (hfg A i))
  · intro A hA B hB hne
    obtain ⟨P,hP,rfl⟩ := mem_map.mp hA
    obtain ⟨Q,hQ,rfl⟩ := mem_map.mp hB
    change (P.map e.toEmbedding ∩ Q.map e.toEmbedding).card ≤ 1
    rw [←map_inter,card_map]
    exact hLl P hP Q hQ (fun he => hne (congrArg E he))
  · intro A hA
    obtain ⟨P,hP,rfl⟩ := mem_map.mp hA
    change (P.map e.toEmbedding).card=r
    rw [card_map,hLu P hP]
  · intro i
    rw [filter_map,card_map]
    have he : L.filter ((fun A => i∈A) ∘ E) = L.filter (fun A => e.symm i∈A) := by
      ext A
      simp [E]
    rw [he]
    have h := hLd (e.symm i)
    omega

/-- A list-colouring theorem for regular uniform hypergraphs transfers to all
linear hypergraphs with the same upper bounds. -/
theorem list_coloring_of_uniform (r D n m b : ℕ) (hr : 2 ≤ r) (hD : 0 < D) (hm : 0 < m)
    (H : Finset (Finset (Fin n))) (L : Finset (Fin n) → Finset (Fin m))
    (hlin : ∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1)
    (hsize : ∀ A ∈ H, A.card ≤ r) (hdeg : ∀ i, (H.filter (fun A => i∈A)).card ≤ D)
    (hL : ∀ A∈H, b ≤ (L A).card)
    (huniform : ∀ n' : ℕ, ∀ (K : Finset (Finset (Fin n')))
      (M : Finset (Fin n') → Finset (Fin m)),
      (∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).card ≤ 1) →
      (∀ A ∈ K, A.card=r) → (∀ i, (K.filter (fun A => i∈A)).card=D) →
      (∀ A ∈ K, b ≤ (M A).card) →
      ∃ c : Finset (Fin n') → Fin m,
        (∀ A ∈ K, ∀ B ∈ K, A≠B → (A∩B).Nonempty → c A≠c B) ∧
        (∀ A ∈ K, c A∈M A)) :
      ∃ c : Finset (Fin n) → Fin m,
        (∀ A ∈ H, ∀ B ∈ H, A≠B → (A∩B).Nonempty → c A≠c B) ∧
        (∀ A ∈ H, c A∈L A) := by
  classical
  by_cases hH : H.Nonempty
  · obtain ⟨A₀,hA₀⟩ := hH
    have hbm : b ≤ m := (hL A₀ hA₀).trans (by
      simpa using Finset.card_le_card (Finset.subset_univ (L A₀)))
    obtain ⟨n',f,g,K,hg,hfg,hKl,hKu,hKd⟩ := regular_uniform_embedding r D n hr hD H hlin hsize hdeg
    let M (E : Finset (Fin n')) : Finset (Fin m) :=
      if he : E ∈ H.map g then L (Classical.choose (mem_map.mp he)) else univ
    have hM (A : Finset (Fin n)) (hA : A∈H) : M (g A)=L A := by
      have he : g A∈H.map g := mem_map.mpr ⟨A,hA,rfl⟩
      simp only [M,dif_pos he]
      exact congrArg L (g.injective (Classical.choose_spec (mem_map.mp he)).2)
    have hML : ∀ E∈K,b ≤ (M E).card := by
      intro E hE
      by_cases he : E∈H.map g
      · obtain ⟨A,hA,rfl⟩ := mem_map.mp he
        rw [hM A hA]
        exact hL A hA
      · simp only [M,dif_neg he,card_univ,Fintype.card_fin]
        exact hbm
    obtain ⟨c,hc,hcL⟩ := huniform n' K M hKl hKu hKd hML
    refine ⟨c ∘ g,?_,?_⟩
    · intro A hA B hB hab hAB
      obtain ⟨i,hi⟩ := hAB
      apply hc _ (hg A hA) _ (hg B hB) (fun he => hab (g.injective he))
      exact ⟨f i,mem_inter.mpr ⟨(hfg A i).mpr (mem_inter.mp hi).1,
        (hfg B i).mpr (mem_inter.mp hi).2⟩⟩
    · intro A hA
      simpa only [Function.comp_apply,hM A hA] using hcL (g A) (hg A hA)
  · exact ⟨fun _ => ⟨0,hm⟩,fun A hA => (hH ⟨A,hA⟩).elim,fun A hA => (hH ⟨A,hA⟩).elim⟩

end Erdos19Uniform

theorem meet_le {n : ℕ} (H : Finset (Finset (Fin n))) (A : Finset (Fin n))
    (d : ℕ) (hd : ∀ i ∈ A, (H.filter (fun A => i ∈ A)).card ≤ d) :
    (H.filter (fun B => (A ∩ B).Nonempty)).card ≤ A.card * d := by
  have heq : H.filter (fun B => (A ∩ B).Nonempty) =
      A.biUnion (fun i => H.filter (fun A => i ∈ A)) := by
    ext B
    simp only [mem_filter, mem_biUnion, Finset.Nonempty, mem_inter]
    constructor
    · rintro ⟨hB, i, hiA, hiB⟩
      exact ⟨i, hiA, hB, hiB⟩
    · rintro ⟨i, hiA, hB, hiB⟩
      exact ⟨hB, i, hiA, hiB⟩
  rw [heq]
  calc (A.biUnion (fun i => H.filter (fun A => i ∈ A))).card
 ≤ ∑ i ∈ A, (H.filter (fun A => i ∈ A)).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ A, d := Finset.sum_le_sum hd
    _ = A.card * d := by simp

/-- Greedy list colouring. -/
theorem greedy {n m : ℕ} (H : Finset (Finset (Fin n))) (L : Finset (Fin n) → Finset (Fin m))
    (hm : 0 < m)
    (hL : ∀ A ∈ H, ((H.erase A).filter (fun B => (A ∩ B).Nonempty)).card < (L A).card) :
    ∃ c : Finset (Fin n) → Fin m,
      (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B) ∧ ∀ A ∈ H, c A ∈ L A := by
  induction H using Finset.strongInductionOn with
  | _ H ih =>
    by_cases hH : H.Nonempty
    · obtain ⟨A, hA⟩ := hH
      let K := H.erase A
      have hKH : K ⊆ H := Finset.erase_subset _ _
      obtain ⟨c, hc, hcL⟩ := ih K (Finset.erase_ssubset hA) (by
        intro B hB
        refine lt_of_le_of_lt ?_ (hL B (hKH hB))
        apply Finset.card_le_card
        apply Finset.filter_subset_filter
        exact Finset.erase_subset_erase _ hKH)
      let blocked := (K.filter (fun B => (A ∩ B).Nonempty)).image c
      have hblocked : blocked.card < (L A).card :=
        lt_of_le_of_lt Finset.card_image_le (hL A hA)
      have hfree : (L A \ blocked).Nonempty := by
        apply Finset.card_pos.mp
        have := Finset.le_card_sdiff blocked (L A)
        omega
      obtain ⟨w, hw⟩ := hfree
      have hne : ∀ B ∈ K, (A ∩ B).Nonempty → w ≠ c B := by
        intro B hB hi he
        exact (mem_sdiff.mp hw).2 (he ▸ mem_image_of_mem c (mem_filter.mpr ⟨hB, hi⟩))
      refine ⟨fun B => if B = A then w else c B, ?_, ?_⟩
      · intro B hB D hD hBD hi
        by_cases hBA : B = A
        · subst B
          have hDA := Ne.symm hBD
          simpa only [if_pos rfl, if_true, if_neg hDA] using hne D (mem_erase.mpr ⟨hDA, hD⟩) hi
        by_cases hDA : D = A
        · subst D
          have hi' : (A ∩ B).Nonempty := by simpa only [Finset.inter_comm] using hi
          simpa only [if_pos rfl, if_true, if_neg hBA] using
            (hne B (mem_erase.mpr ⟨hBA, hB⟩) hi').symm
        simpa only [if_neg hBA, if_neg hDA] using
          hc B (mem_erase.mpr ⟨hBA, hB⟩) D (mem_erase.mpr ⟨hDA, hD⟩) hBD hi
      · intro B hB
        by_cases hBA : B = A
        · subst B; simpa using (mem_sdiff.mp hw).1
        · simpa only [if_neg hBA] using hcL B (mem_erase.mpr ⟨hBA, hB⟩)
    · exact ⟨fun _ => ⟨0, hm⟩, fun A hA => (hH ⟨A, hA⟩).elim, fun A hA => (hH ⟨A, hA⟩).elim⟩

/-- Neighbourhood bound in a hypergraph of maximum degree D. -/
theorem nbhd_le {n : ℕ} (H : Finset (Finset (Fin n))) (D : ℕ) (A : Finset (Fin n)) (hA : A ∈ H)
    (hdeg : ∀ i, (H.filter (fun A => i ∈ A)).card ≤ D) :
    ((H.erase A).filter (fun B => (A ∩ B).Nonempty)).card ≤ A.card * (D - 1) := by
  apply meet_le
  intro i hi
  have : (H.erase A).filter (fun B => i ∈ B) = (H.filter (fun B => i ∈ B)).erase A := by
    ext B; simp [mem_filter, mem_erase]; tauto
  rw [this, Finset.card_erase_of_mem (mem_filter.mpr ⟨hA, hi⟩)]
  have := hdeg i
  omega

/-- The case q = 1 (rank at most 2): greedy works with lists of size 2D. -/
theorem case_one : ∃ D₀ : ℕ, ∀ n D m : ℕ, D₀ ≤ D → 0 < m →
    ∀ (H : Finset (Finset (Fin n))) (L : Finset (Fin n) → Finset (Fin m)),
      (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).card ≤ 1) →
      (∀ A ∈ H, 2 ≤ A.card ∧ A.card ≤ 2 * 1) →
      (∀ i, (H.filter (fun A => i ∈ A)).card ≤ D) → (∀ A ∈ H, D + D / 1 ≤ (L A).card) →
      ∃ c : Finset (Fin n) → Fin m,
        (∀ A ∈ H, ∀ B ∈ H, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B) ∧ ∀ A ∈ H, c A ∈ L A := by
  refine ⟨1, fun n D m hD hm H L _ hsize hdeg hL => greedy H L hm ?_⟩
  intro A hA
  have h1 := nbhd_le H D A hA hdeg
  have h2 := hsize A hA
  have h3 := hL A hA
  rw [Nat.div_one] at h3
  have h4 : A.card * (D - 1) ≤ 2 * (D - 1) := Nat.mul_le_mul_right _ h2.2
  omega


/-- The regular uniform case on edges of size four. -/
def H1 : Prop :=
  ∃ D₀ : ℕ,
    ∀ n D m : ℕ, D₀ ≤ D → 0 < D → 0 < m →
      ∀ (K : Finset (Finset (Fin n))) (L : Finset (Fin n) → Finset (Fin m)),
        (∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).card ≤ 1) →
        (∀ A ∈ K, A.card = 4) → (∀ i, (K.filter (fun A => i ∈ A)).card = D) →
        (∀ A ∈ K, D + D / 2 ≤ (L A).card) →
        ∃ c : Finset (Fin n) → Fin m,
          (∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B) ∧
          ∀ A ∈ K, c A ∈ L A

/-- The regular uniform case for even edge sizes at least six. -/
def H2 : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∃ D₀ : ℕ,
    ∀ n D m : ℕ, D₀ ≤ D → 0 < D → 0 < m →
      ∀ (K : Finset (Finset (Fin n))) (L : Finset (Fin n) → Finset (Fin m)),
        (∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).card ≤ 1) →
        (∀ A ∈ K, A.card = 2 * q) → (∀ i, (K.filter (fun A => i ∈ A)).card = D) →
        (∀ A ∈ K, D + D / q ≤ (L A).card) →
        ∃ c : Finset (Fin n) → Fin m,
          (∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B) ∧
          ∀ A ∈ K, c A ∈ L A

theorem main : H1 → H2 → OMA.R_Erdos19_erdos_19_variants_kahn_R1.H1 := by
  intro hfour hlarge q hq
  by_cases hq1 : q = 1
  · subst q
    exact case_one
  by_cases hq2 : q = 2
  · subst q
    obtain ⟨D₀,h⟩ := hfour
    refine ⟨max D₀ 1,?_⟩
    intro n D m hD hm H L hlin hsize hdeg hL
    have hD₀ : D₀ ≤ D := (le_max_left _ _).trans hD
    have hD' : 0 < D := by omega
    exact Erdos19Uniform.list_coloring_of_uniform 4 D n m (D + D/2) (by decide) hD' hm
      H L hlin (fun A hA => (hsize A hA).2) hdeg hL (fun n' => h n' D m hD₀ hD' hm)
  · obtain ⟨D₀,h⟩ := hlarge q (by omega)
    refine ⟨max D₀ 1,?_⟩
    intro n D m hD hm H L hlin hsize hdeg hL
    have hD₀ : D₀ ≤ D := (le_max_left _ _).trans hD
    have hD' : 0 < D := by omega
    exact Erdos19Uniform.list_coloring_of_uniform (2*q) D n m (D + D/q) (by omega) hD' hm
      H L hlin (fun A hA => (hsize A hA).2) hdeg hL (fun n' => h n' D m hD₀ hD' hm)

end OMA.R_Erdos19_erdos_19_variants_kahn_R1_H1_R2
