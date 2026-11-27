import OMAReductions.R_WrittenOnTheWallII_GraphConjecture199_conjecture199_R1_H2_R1
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
A shortest path in the separator's compatibility graph yields an induced tree.
At each endpoint, keep either the center and its private components or one leaf
from each component it shares with its neighbor. The resulting tree forces
overlap for high-degree rows. Counting incidences then bounds the number of
components after any vertex deletion.
-/

namespace Graph199
open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture199_conjecture199_R1_H2_R1
open OMA.R_WrittenOnTheWallII_GraphConjecture199_conjecture199_R1

section
universe u

variable {V : Type u} {G : SimpleGraph V}

/-- A walk crossing a level must visit its designated vertex if all ascending
edges cross one level and land on that vertex. -/
private theorem hit_rank {S : Set V} {d : ℕ} (rank : S → ℕ)
    (center : Fin (d+1) ↪ S)
    (hstep : ∀ x y : S, (G.induce S).Adj x y → rank x < rank y →
      rank y = rank x+1 ∧ ∃ j : Fin (d+1), rank y = j.val ∧ y = center j)
    {x y : S} (p : (G.induce S).Walk x y) (i : Fin (d+1))
    (hx : rank x < i.val) (hy : i.val ≤ rank y) : center i ∈ p.support := by
  induction p with
  | nil => omega
  | @cons a b c hab p ih =>
    by_cases hb : rank b < i.val
    · exact List.mem_cons_of_mem _ (ih hb hy)
    · have he : rank a < rank b := by omega
      obtain ⟨hne,j,hj,hbj⟩ := hstep a b hab he
      have hji : j = i := Fin.ext (by omega)
      subst j
      exact List.mem_cons_of_mem _ (hbj ▸ p.start_mem_support)

/-- An induced graph with mandatory level crossings has an induced path
through all designated vertices from its first to its last level. -/
theorem ranked_connector {S : Set V} {d : ℕ} (rank : S → ℕ)
    (center : Fin (d+1) ↪ S) (hc : ∀ i, rank (center i) = i.val)
    (hstep : ∀ x y : S, (G.induce S).Adj x y → rank x < rank y →
      rank y = rank x+1 ∧ ∃ j : Fin (d+1), rank y = j.val ∧ y = center j)
    (hreach : (G.induce S).Reachable (center 0) (center (Fin.last d))) :
    ∃ B : Finset V, (∀ x ∈ B, x ∈ S) ∧ (∀ i, (center i).val ∈ B) ∧
      d+1 ≤ B.card ∧ (G.induce (B : Set V)).IsTree := by
  classical
  obtain ⟨p,_,hpLen⟩ := hreach.exists_path_of_dist
  let B₀ := p.support.toFinset
  let f : S ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  let B := B₀.map f
  have hmem (i : Fin (d+1)) : center i ∈ p.support := by
    by_cases h0 : i = 0
    · subst i
      exact p.start_mem_support
    · apply hit_rank rank center hstep p i
      · rw [hc]
        have hp : i.val ≠ 0 := fun he => h0 (Fin.ext he)
        change 0 < i.val
        omega
      · rw [hc]
        change i.val ≤ d
        omega
  have hSet (x : V) (hx : x ∈ B) : x ∈ S := by
    obtain ⟨y,_,rfl⟩ := mem_map.mp hx
    exact y.property
  have hcenter (i : Fin (d+1)) : (center i).val ∈ B :=
    mem_map.mpr ⟨center i,List.mem_toFinset.mpr (hmem i),rfl⟩
  have hcard : d+1 ≤ B.card := by
    have hsub : univ.map (center.trans f) ⊆ B := by
      intro x hx
      obtain ⟨i,_,rfl⟩ := mem_map.mp hx
      exact hcenter i
    simpa using card_le_card hsub
  have htree : ((G.induce S).induce (B₀ : Set S)).IsTree :=
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
  let iso : (G.induce S).induce (B₀ : Set S) ≃g G.induce (B : Set V) :=
    ⟨Equiv.ofBijective g ⟨hgi,hgs⟩,by intro x y; rfl⟩
  exact ⟨B,hSet,hcenter,hcard,iso.isTree_iff.mp htree⟩
end

section
universe u

variable {V : Type u} {G : SimpleGraph V}

/-- Connect consecutive centers using disjoint intermediate vertex sets.
Each intermediate set can meet only its two incident centers. -/
theorem connector_of_ordered_blocks {d : ℕ}
    (center : Fin (d+1) ↪ V) (block : Fin d → Set V)
    (havoid : ∀ i j, center i ∉ block j)
    (hdis : ∀ i j, i ≠ j → Disjoint (block i) (block j))
    (hcross : ∀ i j, i ≠ j → ∀ x ∈ block i, ∀ y ∈ block j, ¬ G.Adj x y)
    (hclose : ∀ i j, G.Adj (center i) (center j) →
      i.val ≤ j.val+1 ∧ j.val ≤ i.val+1)
    (hincident : ∀ i j, ∀ x ∈ block j, G.Adj (center i) x →
      i.val = j.val ∨ i.val = j.val+1)
    (hconnect : ∀ j : Fin d, G.Adj (center j.castSucc) (center j.succ) ∨
      ((G.induce (block j)).Connected ∧
        (∃ x ∈ block j, G.Adj (center j.castSucc) x) ∧
        (∃ x ∈ block j, G.Adj (center j.succ) x))) :
    ∃ B : Finset V, (∀ x ∈ B, (∃ i, x = center i) ∨ (∃ j, x ∈ block j)) ∧
      (∀ i, center i ∈ B) ∧ d+1 ≤ B.card ∧
      (G.induce (B : Set V)).IsTree := by
  classical
  let S : Set V := {x | (∃ i, x = center i) ∨ (∃ j, x ∈ block j)}
  let c : Fin (d+1) ↪ S :=
    ⟨fun i => ⟨center i,Or.inl ⟨i,rfl⟩⟩, fun i j he => center.injective (congrArg Subtype.val he)⟩
  let index (x : V) (n : ℕ) :=
    (∃ i : Fin (d+1), x = center i ∧ n = i.val) ∨
    (∃ j : Fin d, x ∈ block j ∧ n = j.val)
  have hex (x : S) : ∃ n, index x.val n := by
    rcases x.property with ⟨i,hi⟩ | ⟨j,hj⟩
    · exact ⟨i.val,Or.inl ⟨i,hi,rfl⟩⟩
    · exact ⟨j.val,Or.inr ⟨j,hj,rfl⟩⟩
  have huniq {x : V} {n m : ℕ} (hn : index x n) (hm : index x m) : n = m := by
    rcases hn with ⟨i,rfl,rfl⟩ | ⟨i,hi,rfl⟩
    · rcases hm with ⟨j,hj,rfl⟩ | ⟨j,hj,rfl⟩
      · rw [center.injective hj]
      · exact False.elim (havoid i j hj)
    · rcases hm with ⟨j,rfl,rfl⟩ | ⟨j,hj,rfl⟩
      · exact False.elim (havoid j i hi)
      · by_cases he : i = j
        · rw [he]
        · exact False.elim (Set.disjoint_left.mp (hdis i j he) hi hj)
  let rank (x : S) : ℕ := (hex x).choose
  have hindex (x : S) : index x.val (rank x) := (hex x).choose_spec
  have hc (i : Fin (d+1)) : rank (c i) = i.val :=
    huniq (hindex (c i)) (Or.inl ⟨i,rfl,rfl⟩)
  have hs x y (he : (G.induce S).Adj x y) (hlt : rank x < rank y) :
      rank y = rank x+1 ∧ ∃ i : Fin (d+1), rank y = i.val ∧ y = c i := by
    have he' : G.Adj x.val y.val := he
    rcases hindex x with ⟨i,hi,hir⟩ | ⟨i,hi,hir⟩ <;>
      rcases hindex y with ⟨j,hj,hjr⟩ | ⟨j,hj,hjr⟩
    · have hh := hclose i j (hi ▸ hj ▸ he')
      exact ⟨by omega, j,hjr,Subtype.ext hj⟩
    · have hh := hincident i j y.val hj (hi ▸ he')
      omega
    · have hh := hincident j i x.val hi (hj ▸ he'.symm)
      exact ⟨by omega, j,hjr,Subtype.ext hj⟩
    · have hne : i ≠ j := by
        intro heq
        subst j
        omega
      exact False.elim (hcross i j hne x.val hi y.val hj he')
  have hreachStep (j : Fin d) : (G.induce S).Reachable (c j.castSucc) (c j.succ) := by
    rcases hconnect j with he | ⟨hj,⟨a,ha,hea⟩,⟨b,hb,heb⟩⟩
    · exact (show (G.induce S).Adj (c j.castSucc) (c j.succ) from he).reachable
    · let e : G.induce (block j) →g G.induce S :=
        ⟨fun x => ⟨x.val,Or.inr ⟨j,x.property⟩⟩, fun h => h⟩
      have hr := (hj ⟨a,ha⟩ ⟨b,hb⟩).map e
      have hae : (G.induce S).Adj (c j.castSucc) (e ⟨a,ha⟩) := hea
      have hbe : (G.induce S).Adj (c j.succ) (e ⟨b,hb⟩) := heb
      exact hae.reachable.trans (hr.trans hbe.symm.reachable)
  have huu (i : Fin (d+1)) : (G.induce S).Reachable (c 0) (c i) := by
    induction i using Fin.induction with
    | zero => exact ⟨Walk.nil⟩
    | succ i ih => exact ih.trans (hreachStep i)
  exact ranked_connector rank c hc hs (huu (Fin.last d))


/-- The centers and blocks in a closed interval of an ordered connector
contain an induced tree through all interval centers. -/
theorem connector_of_ordered_interval {d : ℕ}
    (center : Fin (d+1) ↪ V) (block : Fin d → Set V)
    (havoid : ∀ i j, center i ∉ block j)
    (hdis : ∀ i j, i ≠ j → Disjoint (block i) (block j))
    (hcross : ∀ i j, i ≠ j → ∀ x ∈ block i, ∀ y ∈ block j, ¬ G.Adj x y)
    (hclose : ∀ i j, G.Adj (center i) (center j) →
      i.val ≤ j.val+1 ∧ j.val ≤ i.val+1)
    (hincident : ∀ i j, ∀ x ∈ block j, G.Adj (center i) x →
      i.val = j.val ∨ i.val = j.val+1)
    (hconnect : ∀ j : Fin d, G.Adj (center j.castSucc) (center j.succ) ∨
      ((G.induce (block j)).Connected ∧
        (∃ x ∈ block j, G.Adj (center j.castSucc) x) ∧
        (∃ x ∈ block j, G.Adj (center j.succ) x)))
    (l n : ℕ) (hlt : l+n ≤ d) :
    ∃ B : Finset V,
      (∀ x ∈ B, (∃ i, l ≤ i.val ∧ i.val ≤ l+n ∧ x = center i) ∨
        (∃ j, l ≤ j.val ∧ j.val < l+n ∧ x ∈ block j)) ∧
      (∀ i, l ≤ i.val → i.val ≤ l+n → center i ∈ B) ∧
      n+1 ≤ B.card ∧ (G.induce (B : Set V)).IsTree := by
  let ci (i : Fin (n+1)) : Fin (d+1) := ⟨l+i.val, by have hi := i.isLt; omega⟩
  let bi (j : Fin n) : Fin d := ⟨l+j.val, by have hj := j.isLt; omega⟩
  let c : Fin (n+1) ↪ V :=
    ⟨fun i => center (ci i),fun i j he => Fin.ext (by
      have h := Fin.ext_iff.mp (center.injective he)
      change l+i.val = l+j.val at h
      omega)⟩
  let b (j : Fin n) := block (bi j)
  have hinjb : Function.Injective bi := by
    intro i j he
    apply Fin.ext
    have h := Fin.ext_iff.mp he
    change l+i.val = l+j.val at h
    omega
  have hc j : (bi j).castSucc = ci (Fin.castSucc j) := Fin.ext rfl
  have hs j : (bi j).succ = ci (Fin.succ j) := Fin.ext (by simp [ci,bi,Nat.add_assoc])
  have hbnd i j (he : G.Adj (c i) (c j)) :
      i.val ≤ j.val+1 ∧ j.val ≤ i.val+1 := by
    have h := hclose (ci i) (ci j) he
    change l+i.val ≤ l+j.val+1 ∧ l+j.val ≤ l+i.val+1 at h
    omega
  have hinc i j x (hm : x ∈ b j) (he : G.Adj (c i) x) :
      i.val = j.val ∨ i.val = j.val+1 := by
    have h := hincident (ci i) (bi j) x hm he
    change l+i.val = l+j.val ∨ l+i.val = l+j.val+1 at h
    omega
  have hcon (j : Fin n) : G.Adj (c j.castSucc) (c j.succ) ∨
      ((G.induce (b j)).Connected ∧
        (∃ x ∈ b j, G.Adj (c j.castSucc) x) ∧
        (∃ x ∈ b j, G.Adj (c j.succ) x)) := by
    have h := hconnect (bi j)
    rw [hc,hs] at h
    exact h
  obtain ⟨B,hB,hcent,hcard,htree⟩ := connector_of_ordered_blocks c b
    (fun i j => havoid (ci i) (bi j))
    (fun i j he => hdis (bi i) (bi j) (fun hh => he (hinjb hh)))
    (fun i j he => hcross (bi i) (bi j) (fun hh => he (hinjb hh)))
    hbnd hinc hcon
  refine ⟨B,?_,?_,hcard,htree⟩
  · intro x hx
    rcases hB x hx with ⟨i,hi⟩ | ⟨j,hj⟩
    · have he := i.isLt
      exact Or.inl ⟨ci i, by change l ≤ l+i.val; omega,
        by change l+i.val ≤ l+n; omega, hi⟩
    · have he := j.isLt
      exact Or.inr ⟨bi j, by change l ≤ l+j.val; omega,
        by change l+j.val < l+n; omega, hj⟩
  · intro i hl hr
    let j : Fin (n+1) := ⟨i.val-l,by omega⟩
    have he : ci j = i := Fin.ext (by change l+(i.val-l) = i.val; omega)
    simpa only [show c j = center (ci j) from rfl,he] using hcent j
end

section
/-- Choose the larger of keeping a center with its private leaves, and
replacing it with leaves from its overlap with the neighboring center. -/
def endpointKeeps {C : Type*} [DecidableEq C] (R N : Finset C) : Bool :=
  decide ((R ∩ N).card ≤ (R \ N).card + 1)

/-- The leaves chosen at one endpoint. -/
def endpointPool {C : Type*} [DecidableEq C] (R N : Finset C) : Finset C :=
  if endpointKeeps R N then R \ N else R ∩ N

/-- The number of vertices lost from the core when making the choice. -/
def endpointDrop {C : Type*} [DecidableEq C] (R N : Finset C) : ℕ :=
  if endpointKeeps R N then 0 else 1

theorem endpoint_pool_subset {C : Type*} [DecidableEq C] (R N : Finset C) :
    endpointPool R N ⊆ R := by
  unfold endpointPool
  split
  · exact sdiff_subset
  · exact inter_subset_left

/-- The endpoint choice retains at least half the endpoint row and center,
with a rounding gain when that total is odd. -/
theorem endpoint_pool_gain {C : Type*} [DecidableEq C] (R N : Finset C) :
    R.card + 1 + 2 * endpointDrop R N ≤ 2 * (endpointPool R N).card + 2 := by
  have h := card_sdiff_add_card_inter R N
  simp only [endpointPool,endpointDrop,endpointKeeps,decide_eq_true_eq]
  split <;> omega
end

section
open SimpleGraph Finset
variable {V I : Type*} {G : SimpleGraph V}

/-- On a chordless sequence of separator vertices, choose one bridging component
for each pair which is not an edge. Distinct bridges are separated, and the only
separator vertices with neighbors in a bridge are its two incident centers. -/
theorem chosen_bridging_blocks {d : ℕ} (c : Fin (d+1) ↪ V) (C : I → Set V)
    (R : Fin (d+1) → Finset I)
    (touch : ∀ i k, k ∈ R i ↔ ∃ x ∈ C k, G.Adj (c i) x)
    (outside : ∀ i k, c i ∉ C k)
    (separate : ∀ i j, i ≠ j → ∀ x ∈ C i, ∀ y ∈ C j, x ≠ y ∧ ¬ G.Adj x y)
    (conn : ∀ k, (G.induce (C k)).Connected)
    (consec : ∀ j : Fin d, G.Adj (c j.castSucc) (c j.succ) ∨
      ∃ k, k ∈ R j.castSucc ∧ k ∈ R j.succ)
    (near : ∀ i j k, k ∈ R i → k ∈ R j →
      i.val ≤ j.val + 1 ∧ j.val ≤ i.val + 1) :
    ∃ B : Fin d → Set V,
      (∀ i j, c i ∉ B j) ∧
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
      (∀ i j, i ≠ j → ∀ x ∈ B i, ∀ y ∈ B j, ¬ G.Adj x y) ∧
      (∀ i j, ∀ x ∈ B j, G.Adj (c i) x → i.val = j.val ∨ i.val = j.val+1) ∧
      (∀ j : Fin d, G.Adj (c j.castSucc) (c j.succ) ∨
        ((G.induce (B j)).Connected ∧ (∃ x ∈ B j, G.Adj (c j.castSucc) x) ∧
         (∃ x ∈ B j, G.Adj (c j.succ) x))) ∧
      (∀ j x, x ∈ B j → ∃ k, x ∈ C k ∧ k ∈ R j.castSucc ∧ k ∈ R j.succ) := by
  classical
  have hex (j : Fin d) : ∃ S : Set V,
      (S = ∅ ∧ G.Adj (c j.castSucc) (c j.succ)) ∨
        ∃ k, S = C k ∧ k ∈ R j.castSucc ∧ k ∈ R j.succ := by
    rcases consec j with e | ⟨k,h1,h2⟩
    · exact ⟨∅,Or.inl ⟨rfl,e⟩⟩
    · exact ⟨C k,Or.inr ⟨k,rfl,h1,h2⟩⟩
  choose B hB using hex
  have spec j x (hx : x ∈ B j) : ∃ k, x ∈ C k ∧ k ∈ R j.castSucc ∧ k ∈ R j.succ := by
    rcases hB j with ⟨h,_⟩ | ⟨k,h,h1,h2⟩
    · simp [h] at hx
    · exact ⟨k,h ▸ hx,h1,h2⟩
  have apart {i j : Fin d} (hne : i ≠ j) {x y : V} (hx : x ∈ B i) (hy : y ∈ B j) :
      x ≠ y ∧ ¬ G.Adj x y := by
    obtain ⟨k,hx,k1,k2⟩ := spec _ _ hx
    obtain ⟨l,hy,l1,l2⟩ := spec _ _ hy
    apply separate k l _ x hx y hy
    rintro rfl
    have h := near _ _ k k1 l2
    have h' := near _ _ k l1 k2
    simp only [Fin.val_castSucc,Fin.val_succ] at h h'
    exact hne (Fin.ext (by omega))
  refine ⟨B,?_,?_,?_,?_,?_,spec⟩
  · intro i j hx
    obtain ⟨k,hk,_⟩ := spec _ _ hx
    exact outside _ _ hk
  · intro i j hij
    exact Set.disjoint_left.mpr (fun _ hx hy => (apart hij hx hy).1 rfl)
  · intro i j hij x hx y hy
    exact (apart hij hx hy).2
  · intro i j x hx hadj
    obtain ⟨k,hk,h1,h2⟩ := spec _ _ hx
    have h' := (touch i k).mpr ⟨x,hk,hadj⟩
    have c1 := near _ _ _ h' h1
    have c2 := near _ _ _ h' h2
    simp only [Fin.val_castSucc,Fin.val_succ] at c1 c2
    omega
  · intro j
    rcases hB j with ⟨_,e⟩ | ⟨k,e,h1,h2⟩
    · exact Or.inl e
    · rw [e]
      exact Or.inr ⟨conn k,(touch _ k).mp h1,(touch _ k).mp h2⟩
end

section
open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable {ι : Type*} [DecidableEq ι]

omit [Fintype V] [DecidableEq ι] in
private theorem choose_component_leaves (C : ι → Set V) (J : Finset ι) (u : V)
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ C i, ∀ y ∈ C j, x ≠ y ∧ ¬ G.Adj x y)
    (hJ : ∀ i ∈ J, ∃ x ∈ C i, G.Adj x u) :
    ∃ S : Finset V, S.card = J.card ∧ G.IsIndepSet (S : Set V) ∧
      ∀ x ∈ S, G.Adj x u ∧ ∃ i ∈ J, x ∈ C i := by
  classical
  let pick (i : J) : V := Classical.choose (hJ i i.property)
  have hmem (i : J) : pick i ∈ C i := (Classical.choose_spec (hJ i i.property)).1
  have hadj (i : J) : G.Adj (pick i) u := (Classical.choose_spec (hJ i i.property)).2
  have hinj : Function.Injective pick := by
    intro i j h
    apply Subtype.ext
    by_contra hne
    exact (hsep i j hne (pick i) (hmem i) (pick j) (hmem j)).1 h
  let S := J.attach.image pick
  refine ⟨S, ?_, ?_, ?_⟩
  · rw [card_image_of_injective _ hinj, card_attach]
  · intro x hx y hy hxy
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := mem_image.mp hy
    have hij : (i : ι) ≠ j := fun h => hxy (congrArg pick (Subtype.ext h))
    exact (hsep i j hij _ (hmem i) _ (hmem j)).2
  · intro x hx
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    exact ⟨hadj i, i, i.property, hmem i⟩

/-- Attach one leaf from each of two disjoint pools of components to the designated
vertices of a core induced tree. The two designated vertices may coincide. -/
theorem component_leaf_pools_bound (B : Finset V) (C : ι → Set V) (J₁ J₂ : Finset ι)
    (u v : V) (hB : (G.induce (B : Set V)).IsTree) (hu : u ∈ B) (hv : v ∈ B)
    (hJ : Disjoint J₁ J₂)
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ C i, ∀ y ∈ C j, x ≠ y ∧ ¬ G.Adj x y)
    (hdis : ∀ i ∈ J₁ ∪ J₂, Disjoint (C i) (B : Set V))
    (h₁ : ∀ i ∈ J₁, ∃ x ∈ C i, G.Adj x u)
    (h₂ : ∀ i ∈ J₂, ∃ x ∈ C i, G.Adj x v)
    (honly₁ : ∀ i ∈ J₁, ∀ x ∈ C i, ∀ y ∈ B, G.Adj x y → y = u)
    (honly₂ : ∀ i ∈ J₂, ∀ x ∈ C i, ∀ y ∈ B, G.Adj x y → y = v) :
    B.card + J₁.card + J₂.card ≤ largestInducedTreeSize G := by
  obtain ⟨S, hSc, hSind, hSmem⟩ := choose_component_leaves C J₁ u hsep h₁
  obtain ⟨T, hTc, hTind, hTmem⟩ := choose_component_leaves C J₂ v hsep h₂
  have hSB : Disjoint S B := by
    apply Finset.disjoint_left.mpr
    intro x hx hb
    obtain ⟨i, hi, hxi⟩ := (hSmem x hx).2
    exact Set.disjoint_left.mp (hdis i (mem_union.mpr (Or.inl hi))) hxi hb
  have hTB : Disjoint T B := by
    apply Finset.disjoint_left.mpr
    intro x hx hb
    obtain ⟨i, hi, hxi⟩ := (hTmem x hx).2
    exact Set.disjoint_left.mp (hdis i (mem_union.mpr (Or.inr hi))) hxi hb
  have hST (x : V) (hx : x ∈ S) (y : V) (hy : y ∈ T) : x ≠ y ∧ ¬ G.Adj x y := by
    obtain ⟨i, hi, hxi⟩ := (hSmem x hx).2
    obtain ⟨j, hj, hyj⟩ := (hTmem y hy).2
    have hij : i ≠ j := by
      rintro rfl
      exact Finset.disjoint_left.mp hJ hi hj
    exact hsep i j hij x hxi y hyj
  rw [← hSc, ← hTc]
  apply leaf_sets_on_induced_tree B S T u v hB hu hv hSB hTB hSind hTind hST
    (fun x hx => (hSmem x hx).1) (fun y hy => (hTmem y hy).1)
  · intro x hx y hy hxy
    obtain ⟨i, hi, hxi⟩ := (hSmem x hx).2
    exact honly₁ i hi x hxi y hy hxy
  · intro x hx y hy hxy
    obtain ⟨i, hi, hxi⟩ := (hTmem x hx).2
    exact honly₂ i hi x hxi y hy hxy
end

section
open Finset SimpleGraph

variable {V I : Type*} [Fintype V] [DecidableEq I] {G : SimpleGraph V}

/-- A sequence whose nonconsecutive centers neither see each other nor meet
the same component forces a large induced tree. At either end, the tree uses
either the endpoint and its private leaves or leaves from the shared components. -/
theorem large_tree_of_distant_rows {d : ℕ} (hd : 2 ≤ d)
    (c : Fin (d+1) ↪ V) (C : I → Set V) (R : Fin (d+1) → Finset I)
    (touch : ∀ i k, k ∈ R i ↔ ∃ x ∈ C k, G.Adj (c i) x)
    (outside : ∀ i k, c i ∉ C k)
    (separate : ∀ i j, i ≠ j → ∀ x ∈ C i, ∀ y ∈ C j, x ≠ y ∧ ¬ G.Adj x y)
    (conn : ∀ k, (G.induce (C k)).Connected)
    (consec : ∀ j : Fin d, G.Adj (c j.castSucc) (c j.succ) ∨
      ∃ k, k ∈ R j.castSucc ∧ k ∈ R j.succ)
    (close : ∀ i j, G.Adj (c i) (c j) → i.val ≤ j.val + 1 ∧ j.val ≤ i.val + 1)
    (near : ∀ i j k, k ∈ R i → k ∈ R j → i.val ≤ j.val + 1 ∧ j.val ≤ i.val + 1) :
    2*d + (R 0).card + (R (Fin.last d)).card ≤ 2 * largestInducedTreeSize G := by
  classical
  let a : Fin (d+1) := 0
  let b : Fin (d+1) := ⟨1,by omega⟩
  let y : Fin (d+1) := ⟨d-1,by omega⟩
  let z : Fin (d+1) := Fin.last d
  let JL := endpointPool (R a) (R b)
  let JR := endpointPool (R z) (R y)
  let l := endpointDrop (R a) (R b)
  let r := endpointDrop (R z) (R y)
  let n := d-l-r
  have ha : a.val = 0 := rfl
  have hb : b.val = 1 := rfl
  have hy : y.val = d-1 := rfl
  have hz : z.val = d := rfl
  have hl (hk : endpointKeeps (R a) (R b) = true) : l = 0 := by simp [l,endpointDrop,hk]
  have hl' (hk : endpointKeeps (R a) (R b) = false) : l = 1 := by simp [l,endpointDrop,hk]
  have hr (hk : endpointKeeps (R z) (R y) = true) : r = 0 := by simp [r,endpointDrop,hk]
  have hr' (hk : endpointKeeps (R z) (R y) = false) : r = 1 := by simp [r,endpointDrop,hk]
  have hlb : l ≤ 1 := by cases h : endpointKeeps (R a) (R b) <;> simp [l,endpointDrop,h]
  have hrb : r ≤ 1 := by cases h : endpointKeeps (R z) (R y) <;> simp [r,endpointDrop,h]
  have hend : l+n = d-r := by dsimp [n]; omega
  let eL : Fin (d+1) := ⟨l,by omega⟩
  let eR : Fin (d+1) := ⟨d-r,by omega⟩
  have heL : eL.val = l := rfl
  have heR : eR.val = d-r := rfl
  have hLsub : JL ⊆ R a := endpoint_pool_subset _ _
  have hRsub : JR ⊆ R z := endpoint_pool_subset _ _
  have hJustL i k (hk : k ∈ JL) (hm : k ∈ R i) (hi : l ≤ i.val) :
      i = eL := by
    have h := near a i k (hLsub hk) hm
    apply Fin.ext
    rw [heL]
    cases hK : endpointKeeps (R a) (R b)
    · have := hl' hK
      omega
    · have hh : k ∉ R b := (mem_sdiff.mp (by simpa [JL,endpointPool,hK] using hk)).2
      have hne : i.val ≠ 1 := fun he => hh (Fin.ext (he.trans hb.symm) ▸ hm)
      have := hl hK
      omega
  have hJustR i k (hk : k ∈ JR) (hm : k ∈ R i) (hi : i.val ≤ l+n) :
      i = eR := by
    have h := near z i k (hRsub hk) hm
    apply Fin.ext
    rw [heR]
    cases hK : endpointKeeps (R z) (R y)
    · have := hr' hK
      omega
    · have hh : k ∉ R y := (mem_sdiff.mp (by simpa [JR,endpointPool,hK] using hk)).2
      have hne : i.val ≠ d-1 := fun he => hh (Fin.ext (he.trans hy.symm) ▸ hm)
      have := hr hK
      omega
  have hMeetL k (hk : k ∈ JL) : k ∈ R eL := by
    cases hK : endpointKeeps (R a) (R b)
    · have he : eL = b := Fin.ext (by rw [heL,hl' hK,hb])
      rw [he]
      exact (mem_inter.mp (by simpa [JL,endpointPool,hK] using hk)).2
    · have he : eL = a := Fin.ext (by rw [heL,hl hK,ha])
      rw [he]
      exact hLsub hk
  have hMeetR k (hk : k ∈ JR) : k ∈ R eR := by
    cases hK : endpointKeeps (R z) (R y)
    · have he : eR = y := Fin.ext (by rw [heR,hr' hK,hy])
      rw [he]
      exact (mem_inter.mp (by simpa [JR,endpointPool,hK] using hk)).2
    · have he : eR = z := Fin.ext (by rw [heR,hr hK,hz,Nat.sub_zero])
      rw [he]
      exact hRsub hk
  obtain ⟨B,hav,hdis,hcross,hinc,hcon,hBspec⟩ :=
    chosen_bridging_blocks c C R touch outside separate conn consec near
  obtain ⟨D,hD,hDcent,hDcard,hDtree⟩ :=
    connector_of_ordered_interval c B hav hdis hcross close hinc hcon l n (by omega)
  have hleft : c eL ∈ D := hDcent eL (by rw [heL]) (by rw [heL]; omega)
  have hright : c eR ∈ D := hDcent eR (by omega) (by rw [heR,hend])
  have hpool : Disjoint JL JR := by
    apply Finset.disjoint_left.mpr
    intro k hL hR
    have hh := near a z k (hLsub hL) (hRsub hR)
    omega
  have hblock (k : I) (hk : k ∈ JL ∨ k ∈ JR) (j : Fin d)
      (hlj : l ≤ j.val) (hrj : j.val < l+n)
      {x : V} (hx : x ∈ C k) {w : V} (hw : w ∈ B j) : x ≠ w ∧ ¬ G.Adj x w := by
    obtain ⟨t,ht,htL,htR⟩ := hBspec j w hw
    refine separate k t ?_ x hx w ht
    rintro rfl
    rcases hk with hk | hk
    · have e1 := congrArg Fin.val (hJustL _ _ hk htL (by simpa using hlj))
      have e2 := congrArg Fin.val (hJustL _ _ hk htR (by simp; omega))
      simp only [Fin.val_castSucc,Fin.val_succ] at e1 e2
      omega
    · have e1 := congrArg Fin.val (hJustR _ _ hk htL (by simp; omega))
      have e2 := congrArg Fin.val (hJustR _ _ hk htR (by simp; omega))
      simp only [Fin.val_castSucc,Fin.val_succ] at e1 e2
      omega
  have hOutside k (hk : k ∈ JL ∪ JR) : Disjoint (C k) (D : Set V) := by
    apply Set.disjoint_left.mpr
    intro x hx hxD
    rcases hD x hxD with ⟨i,_,_,rfl⟩ | ⟨j,hj,hj',hxB⟩
    · exact outside i k hx
    · exact (hblock k (mem_union.mp hk) j hj hj' hx hxB).1 rfl
  have hOnlyL k (hk : k ∈ JL) x (hx : x ∈ C k) w (hw : w ∈ D) (he : G.Adj x w) :
      w = c eL := by
    rcases hD w hw with ⟨i,hi,_,rfl⟩ | ⟨j,hj,hj',hwB⟩
    · rw [hJustL i k hk ((touch i k).mpr ⟨x,hx,he.symm⟩) hi]
    · exact False.elim ((hblock k (Or.inl hk) j hj hj' hx hwB).2 he)
  have hOnlyR k (hk : k ∈ JR) x (hx : x ∈ C k) w (hw : w ∈ D) (he : G.Adj x w) :
      w = c eR := by
    rcases hD w hw with ⟨i,_,hi,rfl⟩ | ⟨j,hj,hj',hwB⟩
    · rw [hJustR i k hk ((touch i k).mpr ⟨x,hx,he.symm⟩) hi]
    · exact False.elim ((hblock k (Or.inr hk) j hj hj' hx hwB).2 he)
  have ht := component_leaf_pools_bound D C JL JR (c eL) (c eR) hDtree
    hleft hright hpool separate hOutside (fun k hk => by
      obtain ⟨x,hx,he⟩ := (touch _ _).mp (hMeetL k hk)
      exact ⟨x,hx,he.symm⟩)
    (fun k hk => by
      obtain ⟨x,hx,he⟩ := (touch _ _).mp (hMeetR k hk)
      exact ⟨x,hx,he.symm⟩) hOnlyL hOnlyR
  have hGainL := endpoint_pool_gain (R a) (R b)
  have hGainR := endpoint_pool_gain (R z) (R y)
  change (R a).card + 1 + 2*l ≤ 2*JL.card + 2 at hGainL
  change (R z).card + 1 + 2*r ≤ 2*JR.card + 2 at hGainR
  change 2*d + (R a).card + (R z).card ≤ _
  omega
end

section
open Finset
open scoped BigOperators

private theorem incidence_degree_sum {U C : Type*} [Fintype U] [Fintype C]
    [DecidableEq C] (R : U → Finset C) :
    (∑ u : U, (R u).card) = ∑ i : C, (univ.filter fun u => i ∈ R u).card := by
  classical
  calc
    _ = ∑ u : U, ∑ i : C, if i ∈ R u then (1 : ℕ) else 0 := by
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

/-- Counting indicator differences over two ordered rows can be performed
column by column. -/
private theorem distance_sum_eq {U C : Type*} [Fintype U] [Fintype C] [DecidableEq C]
    (R : U → Finset C) :
    (∑ u : U, ∑ v : U, (((R u \ R v) ∪ (R v \ R u)).card : ℤ)) =
      ∑ i : C, 2 * ((univ.filter fun u => i ∈ R u).card : ℤ) *
        ((Fintype.card U : ℤ) - ((univ.filter fun u => i ∈ R u).card : ℤ)) := by
  classical
  let m : ℤ := Fintype.card U
  let J (i : C) (u : U) : ℤ := if i ∈ R u then 1 else 0
  let d (i : C) : ℤ := (univ.filter fun u => i ∈ R u).card
  have hd (i : C) : (∑ u : U, J i u) = d i := sum_boole _ _
  have hd' (i : C) : (∑ u : U, (1 - J i u)) = m - d i := by
    rw [sum_sub_distrib,hd]
    simp [m]
  have hF (u v : U) :
      (((R u \ R v) ∪ (R v \ R u)).card : ℤ) =
        ∑ i : C, (J i u * (1 - J i v) + (1 - J i u) * J i v) := by
    let S := (R u \ R v) ∪ (R v \ R u)
    change (S.card : ℤ) = _
    rw [show (S.card : ℤ) = ∑ i : C, if i ∈ S then (1 : ℤ) else 0 by
      rw [sum_boole]
      congr
      ext i
      simp]
    apply sum_congr rfl
    intro i _
    by_cases hu : i ∈ R u <;> by_cases hv : i ∈ R v <;> simp [J,S,hu,hv]
  calc
    _ = ∑ u : U, ∑ v : U, ∑ i : C,
        (J i u * (1 - J i v) + (1 - J i u) * J i v) := by simp only [hF]
    _ = ∑ i : C, ∑ u : U, ∑ v : U,
        (J i u * (1 - J i v) + (1 - J i u) * J i v) := by
      calc
        _ = ∑ u : U, ∑ i : C, ∑ v : U,
            (J i u * (1 - J i v) + (1 - J i u) * J i v) :=
          sum_congr rfl (fun _ _ => sum_comm)
        _ = _ := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro i _
      simp only [sum_add_distrib, ← mul_sum, hd', hd]
      rw [← sum_mul, ← sum_mul, hd, hd']
      change d i * (m - d i) + (m - d i) * d i = _
      ring

/-- The component-count bound when full rows overlap every almost full row. -/
theorem incidence_cut_bound_of_full_overlap {U C : Type*} [Fintype U] [Fintype C]
    [DecidableEq C] (R : U → Finset C) (adj : U → U → Prop) (k : ℕ) (hk : 0 < k)
    (col : ∀ i, k ≤ (univ.filter fun u => i ∈ R u).card)
    (row : ∀ u, (R u).card ≤ k + 1)
    (dist : ∀ u v, u ≠ v → (adj u v ∨ (R u ∩ R v).Nonempty) →
      ((R u \ R v) ∪ (R v \ R u)).card ≤ k)
    (full_overlap : ∀ u v, (R u).card = k+1 → k ≤ (R v).card → (R u ∩ R v).Nonempty) :
    Fintype.card C ≤ Fintype.card U + 1 := by
  classical
  let m := Fintype.card U
  let c := Fintype.card C
  let E := ∑ u : U, (R u).card
  let D (u : U) := k + 1 - (R u).card
  let Δ := ∑ u : U, D u
  change c ≤ m + 1
  by_contra! h
  have hc : m + 2 ≤ c := by omega
  have hE := incidence_degree_sum R
  change E = _ at hE
  have he₁ : k * c ≤ E := by
    rw [hE]
    calc
      _ = ∑ _i : C, k := by simp [c,mul_comm]
      _ ≤ _ := sum_le_sum fun i _ => col i
  have hbal (u : U) : (R u).card + D u = k + 1 := by
    dsimp [D]
    have h := row u
    omega
  have he₂ : E + Δ = m * (k + 1) := by
    change (∑ u : U, (R u).card) + (∑ u : U, D u) = _
    rw [← sum_add_distrib]
    simp [hbal,m]
  have hΔ : Δ + 2 * k ≤ m := by
    have hh := Nat.mul_le_mul_left k hc
    nlinarith
  have shallow (u v : U) (hu : D u = 0) (hv : D v ≤ 1) :
      (R u ∩ R v).Nonempty := by
    have hu' := hbal u
    have hv' := hbal v
    exact full_overlap u v (by omega) (by omega)
  let M : ℤ := m
  let K : ℤ := k
  let Cn : ℤ := c
  let Ee : ℤ := E
  let X : ℤ := Δ
  let F (u v : U) : ℤ := ((R u \ R v) ∪ (R v \ R u)).card
  let T := ∑ u : U, ∑ v : U, F u v
  have hK : 0 < K := by
    dsimp [K]
    exact_mod_cast hk
  have hM : 0 < M := by
    have hm' : 0 < m := by omega
    dsimp [M]
    exact_mod_cast hm'
  have hX : 0 ≤ X := Int.natCast_nonneg _
  have hXL : X + 2 * K ≤ M := by
    dsimp [M,K,X]
    exact_mod_cast hΔ
  have hCc : M + 2 ≤ Cn := by
    dsimp [M,Cn]
    exact_mod_cast hc
  have hEe : Ee ≤ M * (K + 1) := by
    have hNat : E ≤ m * (k + 1) := by omega
    dsimp [Ee,M,K]
    exact_mod_cast hNat
  have hXsum : (∑ u : U, (D u : ℤ)) = X := by
    dsimp [X,Δ]
    norm_cast
  have hPoint (u v : U) :
      2 * F u v ≤ (if u = v then 0 else 2 * K) + K * ((D u : ℤ) + D v) := by
    by_cases huv : u = v
    · subst v
      have hno : 0 ≤ K * ((D u : ℤ) + D u) := by positivity
      simpa [F] using hno
    have hmain : 2 * (((R u \ R v) ∪ (R v \ R u)).card) ≤ 2 * k + k * (D u + D v) := by
      by_cases hd : D u + D v ≤ 1
      · have hO : (R u ∩ R v).Nonempty := by
          by_cases hu : D u = 0
          · exact shallow u v hu (by omega)
          · rw [inter_comm]
            exact shallow v u (by omega) (by omega)
        have hh := dist u v huv (Or.inr hO)
        have hnon : 0 ≤ k * (D u + D v) := Nat.zero_le _
        omega
      · have hD : 2 ≤ D u + D v := by omega
        have hmul := Nat.mul_le_mul_left k hD
        have h2 : ((R u \ R v) ∪ (R v \ R u)).card ≤ (R u).card + (R v).card := by
          have hu : (R u \ R v).card ≤ (R u).card := card_le_card sdiff_subset
          have hv : (R v \ R u).card ≤ (R v).card := card_le_card sdiff_subset
          have hUnion := card_union_le (R u \ R v) (R v \ R u)
          omega
        have hBu := hbal u
        have hBv := hbal v
        omega
    simp only [if_neg huv]
    dsimp [F,K]
    exact_mod_cast hmain
  have hbase (u : U) : (∑ v : U, if u = v then 0 else 2 * K) = 2 * K * (M - 1) := by
    have h0 : 1 ≤ Fintype.card U := Fintype.card_pos_iff.mpr ⟨u⟩
    have he : (∑ v ∈ univ.erase u, if u = v then 0 else 2 * K) =
        ∑ v : U, if u = v then 0 else 2 * K := by
      simp
    rw [← he]
    calc
      _ = ∑ _v ∈ univ.erase u, 2 * K := by
        apply sum_congr rfl
        intro v hv
        simp [ne_of_mem_erase hv |>.symm]
      _ = _ := by
        simp [M,m,Finset.card_erase_of_mem (Finset.mem_univ u),Nat.cast_sub h0,mul_comm]
  have hSum (u : U) :
      (∑ v : U, ((if u = v then 0 else 2 * K) + K * ((D u : ℤ) + D v))) =
        2 * K * (M - 1) + K * (M * D u + X) := by
    rw [sum_add_distrib,hbase,← mul_sum,sum_add_distrib,hXsum]
    simp [M,m]
  have hTop : 2 * T ≤ 2 * K * M * (M - 1) + 2 * K * M * X := by
    calc
      2 * T = ∑ u : U, ∑ v : U, 2 * F u v := by simp only [T,mul_sum]
      _ ≤ ∑ u : U, ∑ v : U, ((if u = v then 0 else 2 * K) +
          K * ((D u : ℤ) + D v)) := sum_le_sum fun u _ => sum_le_sum fun v _ => hPoint u v
      _ = ∑ u : U, (2 * K * (M - 1) + K * (M * D u + X)) := by simp only [hSum]
      _ = _ := by
        simp only [sum_add_distrib, ← mul_sum, hXsum, sum_const, card_univ, nsmul_eq_mul]
        dsimp [M,m]
        ring
  let d (i : C) : ℤ := (univ.filter fun u => i ∈ R u).card
  have heD : Ee = ∑ i : C, d i := by
    dsimp [Ee,d]
    exact_mod_cast hE
  have hT : T = ∑ i : C, 2 * d i * (M - d i) := distance_sum_eq R
  have hLow : 2 * K * Cn * M ≤ T + 2 * K * Ee := by
    rw [hT,heD,mul_sum,← sum_add_distrib]
    calc
      _ = ∑ _i : C, 2 * K * M := by simp [Cn,c]; ring
      _ ≤ _ := by
        apply sum_le_sum
        intro i _
        have hlo : K ≤ d i := by
          dsimp [K,d]
          exact_mod_cast col i
        have hhi : d i ≤ M := by
          dsimp [d,M,m]
          exact_mod_cast (card_le_univ (univ.filter fun u : U => i ∈ R u))
        nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)]
  have hKM : 0 < K * M := mul_pos hK hM
  have hTX := mul_le_mul_of_nonneg_left hXL hKM.le
  have hEx := mul_le_mul_of_nonneg_left hEe (show 0 ≤ 2 * K by omega)
  have hCc' := mul_le_mul_of_nonneg_left hCc hKM.le
  nlinarith
end

section
open SimpleGraph Finset

/-- A geodesic can be indexed by an embedding, with edges exactly at
consecutive indices. -/
theorem shortest_indexed_connector {U : Type*} {K : SimpleGraph U} {a b : U}
    (hr : K.Reachable a b) :
    ∃ d, ∃ center : Fin (d + 1) ↪ U, d = K.dist a b ∧
      center 0 = a ∧ center (Fin.last d) = b ∧
      (∀ i : Fin d, K.Adj (center i.castSucc) (center i.succ)) ∧
      (∀ i j : Fin (d+1), i.val + 1 < j.val → ¬ K.Adj (center i) (center j)) := by
  obtain ⟨p, _, hp⟩ := hr.exists_path_of_dist
  let d := p.length
  have hdist (i : Fin (d + 1)) : K.dist a (p.getVert i.val) = i.val := by
    have hsub := SimpleGraph.length_eq_dist_of_subwalk hp (p.isSubwalk_take i.val)
    have hi : i.val ≤ p.length := Nat.le_of_lt_succ i.isLt
    simpa [Walk.take_length, min_eq_left hi] using hsub.symm
  let center : Fin (d+1) ↪ U := ⟨fun i => p.getVert i.val, by
    intro i j he
    apply Fin.ext
    exact (hdist i).symm.trans <| (congrArg (K.dist a) he).trans (hdist j)⟩
  refine ⟨d, center, hp, ?_, ?_, ?_, ?_⟩
  · exact p.getVert_zero
  · exact p.getVert_length
  · intro i
    exact p.adj_getVert_succ i.isLt
  · intro i j hij he
    have hstep := he.diff_dist_adj (u := a)
    change K.Adj (p.getVert i.val) (p.getVert j.val) at he
    change K.dist a (p.getVert j.val) = K.dist a (p.getVert i.val) ∨
      K.dist a (p.getVert j.val) = K.dist a (p.getVert i.val) + 1 ∨
      K.dist a (p.getVert j.val) = K.dist a (p.getVert i.val) - 1 at hstep
    rw [hdist j, hdist i] at hstep
    omega

/-- Two reachable vertices with no edge and no common neighbor have a
geodesic of length at least three. -/
theorem connector_dist_ge_three {U : Type*} {K : SimpleGraph U} {a b : U}
    (hr : K.Reachable a b) (hne : a ≠ b) (hn : ¬ K.Adj a b)
    (hcommon : ∀ x, ¬ (K.Adj a x ∧ K.Adj x b)) : 3 ≤ K.dist a b := by
  by_contra! h
  rcases (show K.dist a b = 0 ∨ K.dist a b = 1 ∨ K.dist a b = 2 by omega) with hz | ho | ht
  · exact hne (hr.dist_eq_zero_iff.mp hz)
  · exact hn (dist_eq_one_iff_adj.mp ho)
  · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
    have hlen : p.length = 2 := hp.trans ht
    have ha := p.adj_getVert_succ (i := 0) (by omega)
    have hb := p.adj_getVert_succ (i := 1) (by omega)
    have he := p.getVert_length
    rw [hlen] at he
    exact hcommon (p.getVert 1) ⟨by simpa using ha, by simpa [he] using hb⟩

/-- Distinct separator rows are compatible if their vertices are adjacent
or the rows name a common outside component. -/
def separatorCompatibility {U C : Type*} [DecidableEq C]
    (K : SimpleGraph U) (R : U → Finset C) : SimpleGraph U where
  Adj u v := u ≠ v ∧ (K.Adj u v ∨ (R u ∩ R v).Nonempty)
  symm := ⟨by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with he | hi
    · exact Or.inl he.symm
    · exact Or.inr (by simpa only [inter_comm] using hi)⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

@[simp]
theorem separatorCompatibility_adj {U C : Type*} [DecidableEq C]
    (K : SimpleGraph U) (R : U → Finset C) (u v : U) :
    (separatorCompatibility K R).Adj u v ↔
      u ≠ v ∧ (K.Adj u v ∨ (R u ∩ R v).Nonempty) := Iff.rfl

/-- Nonconsecutive centers in a shortest compatibility path have no edge
and no common component label. -/
theorem separator_shortest_connector {U C : Type*} [DecidableEq C]
    (K : SimpleGraph U) (R : U → Finset C) {a b : U}
    (hr : (separatorCompatibility K R).Reachable a b) :
    ∃ d, ∃ center : Fin (d+1) ↪ U, d = (separatorCompatibility K R).dist a b ∧
      center 0 = a ∧ center (Fin.last d) = b ∧
      (∀ i : Fin d, K.Adj (center i.castSucc) (center i.succ) ∨
        (R (center i.castSucc) ∩ R (center i.succ)).Nonempty) ∧
      (∀ i j : Fin (d+1), i.val + 1 < j.val →
        ¬ K.Adj (center i) (center j) ∧ Disjoint (R (center i)) (R (center j))) := by
  obtain ⟨d, center, hd, ha, hb, hstep, hno⟩ := shortest_indexed_connector hr
  refine ⟨d,center,hd,ha,hb,fun i => (hstep i).2, ?_⟩
  intro i j hij
  have hne : center i ≠ center j := fun h => by
    have hv : i.val = j.val := congrArg Fin.val (center.injective h)
    omega
  refine ⟨fun h => hno i j hij ⟨hne,Or.inl h⟩, ?_⟩
  apply Finset.disjoint_left.mpr
  intro c hc h'c
  exact hno i j hij ⟨hne,Or.inr ⟨c, Finset.mem_inter.mpr ⟨hc,h'c⟩⟩⟩
end

section
open SimpleGraph Finset

universe u

/-- Data extracted from a shortest compatibility connector between disjoint
full and almost-full separator rows. The outside sets are the actual
components of the graph left after deletion. -/
structure DistantRowConnector {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) {I : Type u} [Fintype I] [DecidableEq I]
    (C : I → Set V) (R : U → Finset I) (d : ℕ) (center : Fin (d+1) ↪ U) : Prop where
  component_nonempty : ∀ i, (C i).Nonempty
  component_outside : ∀ i x, x ∈ C i → x ∉ U
  component_cover : ∀ x ∉ U, ∃ i, x ∈ C i
  component_separated : ∀ {i j : I} {x y : V}, i ≠ j → x ∈ C i → y ∈ C j →
    x ≠ y ∧ ¬ G.Adj x y
  component_connected : ∀ i, (G.induce (C i)).Connected
  touches : ∀ u i, i ∈ R u ↔ ∃ x ∈ C i, G.Adj u.val x
  column_bound : ∀ i, vertexConnectivity G ≤ (univ.filter fun u : U => i ∈ R u).card
  row_bound : ∀ u, (R u).card ≤ vertexConnectivity G + 1
  difference_bound : ∀ u v : U, u ≠ v →
    (G.Adj u.val v.val ∨ (R u ∩ R v).Nonempty) →
    ((R u \ R v) ∪ (R v \ R u)).card ≤ vertexConnectivity G
  length_bound : 3 ≤ d
  first_full : (R (center 0)).card = vertexConnectivity G + 1
  last_near_full : vertexConnectivity G ≤ (R (center (Fin.last d))).card
  endpoints_disjoint : Disjoint (R (center 0)) (R (center (Fin.last d)))
  consecutive : ∀ i : Fin d, G.Adj (center i.castSucc).val (center i.succ).val ∨
    (R (center i.castSucc) ∩ R (center i.succ)).Nonempty
  separated_centers : ∀ i j : Fin (d+1), i.val + 1 < j.val →
    ¬ G.Adj (center i).val (center j).val ∧ Disjoint (R (center i)) (R (center j))

private theorem compatible_size_bound {U I : Type*} [DecidableEq I]
    (R : U → Finset I) (K : SimpleGraph U) (k : ℕ)
    (hdist : ∀ u v, u ≠ v → (K.Adj u v ∨ (R u ∩ R v).Nonempty) →
      ((R u \ R v) ∪ (R v \ R u)).card ≤ k)
    {a b : U} (h : (separatorCompatibility K R).Adj a b) :
    (R a).card + (R b).card ≤ k + 2 * (R a ∩ R b).card := by
  have hb := hdist a b h.1 h.2
  have hdis : Disjoint (R a \ R b) (R b \ R a) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (mem_sdiff.mp hi).2 (mem_sdiff.mp hj).1
  rw [card_union_of_disjoint hdis] at hb
  have ha := card_sdiff_add_card_inter (R a) (R b)
  have hc := card_sdiff_add_card_inter (R b) (R a)
  rw [inter_comm (R b)] at hc
  omega

/-- Disjoint rows whose total size exceeds 2k have no compatibility edge
and no common compatibility neighbor. -/
theorem distant_rows_of_disjoint_large_sets {U I : Type*} [DecidableEq I]
    (R : U → Finset I) (K : SimpleGraph U) (k : ℕ)
    (hdist : ∀ u v, u ≠ v → (K.Adj u v ∨ (R u ∩ R v).Nonempty) →
      ((R u \ R v) ∪ (R v \ R u)).card ≤ k)
    {a b : U} (hdisj : Disjoint (R a) (R b)) (hlarge : 2*k < (R a).card + (R b).card) :
    a ≠ b ∧ ¬ (separatorCompatibility K R).Adj a b ∧
      ∀ w, ¬ ((separatorCompatibility K R).Adj a w ∧
        (separatorCompatibility K R).Adj w b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro he
    subst b
    have hz : R a = ∅ := disjoint_self.mp hdisj
    simp [hz] at hlarge
  · intro he
    have hb := compatible_size_bound R K k hdist he
    have hz : R a ∩ R b = ∅ := disjoint_iff_inter_eq_empty.mp hdisj
    simp only [hz, card_empty, mul_zero, add_zero] at hb
    omega
  · intro w he
    have hl := compatible_size_bound R K k hdist he.1
    have hr := compatible_size_bound R K k hdist he.2
    have hlt : (R w).card < (R a ∩ R w).card + (R w ∩ R b).card := by omega
    obtain ⟨x,hx⟩ := inter_nonempty_of_card_lt_card_add_card inter_subset_right inter_subset_left hlt
    obtain ⟨hL,hR⟩ := mem_inter.mp hx
    exact Finset.disjoint_left.mp hdisj (mem_inter.mp hL).1 (mem_inter.mp hR).2

/-- An induced-tree bound on distant compatibility rows suffices for the
component-count conclusion for every separator. -/
theorem all_separator_component_bound_of_distant_rows {V : Type u}
    [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V}
    (large_tree_of_distant_rows :
      ∀ {I : Type u} [Fintype I] [DecidableEq I] {U : Finset V} {C : I → Set V}
        {R : U → Finset I} {d : ℕ} {center : Fin (d+1) ↪ U},
        DistantRowConnector G U C R d center →
          vertexConnectivity G + 3 ≤ largestInducedTreeSize G)
    (hG : G.Connected) (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) :
    ∀ U : Finset V, Nat.card (G.induce ((U : Set V)ᶜ)).ConnectedComponent ≤ U.card + 1 := by
  classical
  intro U
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
  let Ksep := G.induce (U : Set V)
  let H := separatorCompatibility Ksep R
  have hcompat (u v : U) (huv : u ≠ v) (h : Ksep.Adj u v ∨ (R u ∩ R v).Nonempty) :
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
  have hedge (x y : V) (he : G.Adj x y) :
      Ksep.Adj (f x) (f y) ∨ (R (f x) ∩ R (f y)).Nonempty := by
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
  have hreach (u v : U) : H.Reachable u v := by
    have hf' (x : U) : f x.val = x := Subtype.ext ((hf x.val).1 x.property)
    have hh {x y : V} (h : Relation.ReflTransGen G.Adj x y) :
        H.Reachable (f x) (f y) := by
      induction h with
      | refl => exact Reachable.rfl
      | @tail a b _ hab ih =>
        by_cases he : f a = f b
        · exact he ▸ ih
        · exact ih.trans (show H.Adj (f a) (f b) from ⟨he,hedge a b hab⟩).reachable
    have h := hh ((G.reachable_iff_reflTransGen _ _).mp (hG u.val v.val))
    rwa [hf',hf'] at h
  have hoverlap (a b : U) (ha : (R a).card = vertexConnectivity G + 1)
      (hb : vertexConnectivity G ≤ (R b).card) : (R a ∩ R b).Nonempty := by
    by_contra! hn
    have hdisj : Disjoint (R a) (R b) := disjoint_iff_inter_eq_empty.mpr hn
    have hlarge : 2 * vertexConnectivity G < (R a).card + (R b).card := by omega
    obtain ⟨hne, hnot, hno2⟩ :=
      distant_rows_of_disjoint_large_sets R Ksep _ hcompat hdisj hlarge
    have hdl := connector_dist_ge_three (hreach a b) hne hnot hno2
    obtain ⟨d, center, hde, hf, hl, hstep, hgap⟩ :=
      separator_shortest_connector Ksep R (hreach a b)
    have hd : 3 ≤ d := hde.symm ▸ hdl
    have profile : DistantRowConnector G U C R d center :=
      ⟨hCn, hCo, hCc, @hCs, hconn, hR, hcol, hrow, hcompat, hd,
       hf.symm ▸ ha, hl.symm ▸ hb, hf.symm ▸ hl.symm ▸ hdisj, hstep, hgap⟩
    have ht' := large_tree_of_distant_rows profile
    omega
  simpa only [Fintype.card_coe] using
    incidence_cut_bound_of_full_overlap R Ksep.Adj _ hk hcol hrow hcompat hoverlap

/-- In the ambient graph the distant-row profile gives an induced tree
with at least four more vertices than the vertex connectivity. -/
theorem large_tree_of_distant_row_profile {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {I : Type u} [Fintype I] [DecidableEq I] {U : Finset V}
    {C : I → Set V} {R : U → Finset I} {d : ℕ} {center : Fin (d+1) ↪ U}
    (D : DistantRowConnector G U C R d center) :
    vertexConnectivity G + 4 ≤ largestInducedTreeSize G := by
  let c : Fin (d+1) ↪ V := center.trans ⟨Subtype.val,Subtype.val_injective⟩
  let S (i : Fin (d+1)) := R (center i)
  have ht (i : Fin (d+1)) (k : I) : k ∈ S i ↔ ∃ x ∈ C k, G.Adj (c i) x :=
    D.touches (center i) k
  have ho (i : Fin (d+1)) (k : I) : c i ∉ C k := by
    intro hi
    exact D.component_outside k _ hi (center i).property
  have hc (j : Fin d) : G.Adj (c j.castSucc) (c j.succ) ∨
      ∃ k, k ∈ S j.castSucc ∧ k ∈ S j.succ := by
    rcases D.consecutive j with h | ⟨k,hk⟩
    · exact Or.inl h
    · exact Or.inr ⟨k,mem_inter.mp hk⟩
  have hclose (i j : Fin (d+1)) (h : G.Adj (c i) (c j)) :
      i.val ≤ j.val + 1 ∧ j.val ≤ i.val + 1 := by
    constructor
    · by_contra! he
      exact (D.separated_centers j i he).1 h.symm
    · by_contra! he
      exact (D.separated_centers i j he).1 h
  have hnear (i j : Fin (d+1)) (k : I) (hi : k ∈ S i) (hj : k ∈ S j) :
      i.val ≤ j.val + 1 ∧ j.val ≤ i.val + 1 := by
    constructor
    · by_contra! he
      exact Finset.disjoint_left.mp (D.separated_centers j i he).2 hj hi
    · by_contra! he
      exact Finset.disjoint_left.mp (D.separated_centers i j he).2 hi hj
  have htree := large_tree_of_distant_rows (G := G) (by have := D.length_bound; omega)
    c C S ht ho (fun _ _ he _ hx _ hy => D.component_separated he hx hy)
    D.component_connected hc hclose hnear
  change 2*d + (R (center 0)).card + (R (center (Fin.last d))).card ≤
    2 * largestInducedTreeSize G at htree
  rw [D.first_full] at htree
  have hl := D.last_near_full
  have hd := D.length_bound
  omega

/-- The induced-tree hypothesis forces the component-count condition for
every deleted vertex set, at every positive vertex connectivity. -/
theorem all_separator_component_bound {V : Type u}
    [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V}
    (hG : G.Connected) (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) :
    ∀ U : Finset V, Nat.card (G.induce ((U : Set V)ᶜ)).ConnectedComponent ≤ U.card + 1 :=
  all_separator_component_bound_of_distant_rows
    (fun D => Nat.le_trans (by omega) (large_tree_of_distant_row_profile D)) hG ht
end
end Graph199

theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture199_conjecture199_R1_H2_R1.H1 := by
  intro V _ _ G hG _ hk _ ht U _ _
  have hnontrivial : Nontrivial V := by
    by_contra! h
    have := SimpleGraph.vertexConnectivity_of_subsingleton G
    omega
  exact Graph199.all_separator_component_bound hG ht U
