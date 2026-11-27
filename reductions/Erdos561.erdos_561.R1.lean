import FormalConjectures.ErdosProblems.«561»
import Mathlib

/-!
# The size Ramsey number of two star forests

A host star for each antidiagonal has exactly the conjectured number of
edges. A matching of the component demands into the red or blue capacities
of its stars makes it a Ramsey host. Conversely, to rule out every smaller
host, it suffices to color graphs with exactly one fewer edge on twice that
many labeled vertices. The proof removes isolated vertices, relabels the
support, and adds edges to reach that single size.

The diagonal construction is the classical upper bound for the Burr–Erdős–
Faudree–Rousseau–Schelp star forest problem. See P. Liu, Size Ramsey
Numbers of Arbitrary Star Forests, doi:10.5281/zenodo.23879458.
Credit: @marcusbuffett.
-/

open SimpleGraph Finset

namespace OMA.R_Erdos561_erdos_561_R1

/-- One color can supply every demand through distinct host stars. -/
def H1 : Prop := ∀ (s t : ℕ) (n : Fin s → ℕ) (m : Fin t → ℕ)
    (r b : Fin (s+t-1) → ℕ),
    (∀ i j (k : Fin (s+t-1)), k.val ≤ i.val+j.val →
      n i + m j - 1 ≤ r k + b k) →
    (∃ f : Fin s ↪ Fin (s+t-1), ∀ i, n i ≤ r (f i)) ∨
      (∃ f : Fin t ↪ Fin (s+t-1), ∀ j, m j ≤ b (f j))

/-- The fixed-size finite coloring obstruction for the lower bound. -/
def H2 : Prop := ∀ (s t : ℕ), 1 ≤ s → 1 ≤ t →
    ∀ (n : Fin s → ℕ) (m : Fin t → ℕ), Antitone n → Antitone m →
    (∀ i, 1 ≤ n i) → (∀ j, 1 ≤ m j) →
    let k := (∑ j ∈ Icc 2 (s+t), (((univ : Finset (Fin s × Fin t)).filter (fun p => (p.1.val+1)+(p.2.val+1)=j)).sup (fun p => n p.1+m p.2-1))) - 1
    let F {v : ℕ} (a : Fin v → ℕ) := fromRel (fun (x y : Σ i, Fin (a i+1)) =>
      x.1 = y.1 ∧ (x.2.val = 0 ∨ y.2.val = 0))
    ∀ H : SimpleGraph (Fin (2*k)), H.edgeSet.ncard = k →
      ∃ R ≤ H, ¬ (F n).IsContained R ∧ ¬ (F m).IsContained (H \ R)

theorem forest_adj {ι : Type} (n : ι → ℕ) {u v : Σ i, Fin (n i+1)} :
    (fromRel (fun (u v : Σ i, Fin (n i+1)) => u.1 = v.1 ∧ (u.2.val = 0 ∨ v.2.val = 0))).Adj u v ↔ ∃ (i : ι) (a : Fin (n i)),
      (u = ⟨i,0⟩ ∧ v = ⟨i,a.succ⟩) ∨ (v = ⟨i,0⟩ ∧ u = ⟨i,a.succ⟩) := by
  constructor
  · rcases u with ⟨i,a⟩
    rcases v with ⟨j,b⟩
    rintro ⟨hne,hrel⟩
    have hij : i = j := by rcases hrel with h | h; exact h.1; exact h.1.symm
    subst j
    induction a using Fin.cases with
    | zero =>
      induction b using Fin.cases with
      | zero => exact (hne rfl).elim
      | succ b => exact ⟨i,b,Or.inl ⟨rfl,rfl⟩⟩
    | succ a =>
      induction b using Fin.cases with
      | zero => exact ⟨i,a,Or.inr ⟨rfl,rfl⟩⟩
      | succ b => rcases hrel with ⟨_,h|h⟩ | ⟨_,h|h⟩ <;> simp at h
  · rintro ⟨i,a,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩ <;> simp [Ne.symm (Fin.succ_ne_zero a)]

private theorem forest_edges {ι : Type} [Fintype ι] (n : ι → ℕ) :
    ((fromRel (fun (u v : Σ i, Fin (n i+1)) => u.1 = v.1 ∧ (u.2.val = 0 ∨ v.2.val = 0)))).edgeSet.ncard = ∑ i, n i := by
  classical
  let key (z : Σ i, Fin (n i)) : Sym2 (Σ i, Fin (n i+1)) :=
    s((⟨z.1,0⟩ : Σ i, Fin (n i+1)), ⟨z.1,z.2.succ⟩)
  have he : ((fromRel (fun (u v : Σ i, Fin (n i+1)) => u.1 = v.1 ∧ (u.2.val = 0 ∨ v.2.val = 0)))).edgeSet = Set.range key := by
    ext x
    induction x using Sym2.inductionOn with
    | _ a b =>
      rw [mem_edgeSet,forest_adj]
      constructor
      · rintro ⟨i,j,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩
        · exact ⟨⟨i,j⟩,rfl⟩
        · exact ⟨⟨i,j⟩, Sym2.eq_swap⟩
      · rintro ⟨⟨i,j⟩,h⟩
        exact ⟨i,j,(Sym2.eq_iff.mp h.symm).imp id And.symm⟩
  have hi : Function.Injective key := by
    rintro ⟨i,a⟩ ⟨j,b⟩ h
    rcases Sym2.eq_iff.mp h with ⟨hc,hl⟩ | ⟨hc,hl⟩
    · obtain rfl : i = j := congrArg Sigma.fst hc
      have he : a.succ = b.succ := by simpa using hl
      exact congrArg (Sigma.mk i) (Fin.succ_injective _ he)
    · obtain rfl : i = j := congrArg Sigma.fst hc
      exact ((Fin.succ_ne_zero b).symm (by simpa using hc)).elim
  rw [he, Set.ncard_range_of_injective hi, Nat.card_eq_fintype_card]
  simp

private theorem forest_copy {ι κ : Type} (n : ι → ℕ) (L : κ → ℕ)
    (R : SimpleGraph (Σ k, Fin (L k+1))) [DecidableRel R.Adj] (f : ι ↪ κ)
    (avail : ∀ i, n i ≤ (Finset.univ.filter
      (fun a : Fin (L (f i)) => R.Adj ⟨f i,0⟩ ⟨f i,a.succ⟩)).card) :
    ((fromRel (fun (u v : Σ i, Fin (n i+1)) => u.1 = v.1 ∧ (u.2.val = 0 ∨ v.2.val = 0)))).IsContained R := by
  classical
  let A (i : ι) := Finset.univ.filter
    (fun a : Fin (L (f i)) => R.Adj ⟨f i,0⟩ ⟨f i,a.succ⟩)
  have hcard (i : ι) : Fintype.card (Fin (n i)) ≤ Fintype.card (A i) := by
    rw [Fintype.card_fin, Fintype.card_coe]
    exact avail i
  let g (i : ι) : Fin (n i) ↪ A i := Classical.choice (Function.Embedding.nonempty_of_card_le (hcard i))
  let leaf (i : ι) : Fin (n i) ↪ Fin (L (f i)+1) :=
    ((g i).trans (Function.Embedding.subtype _)).trans (Fin.succEmb _)
  have nz (i : ι) : 0 ∉ Set.range (leaf i) := by
    rintro ⟨a,h⟩
    exact Fin.succ_ne_zero _ h
  let comp (i : ι) := Fin.Embedding.cons (leaf i) (nz i)
  let embedding : (Σ i, Fin (n i+1)) ↪ (Σ k, Fin (L k+1)) := Function.Embedding.sigmaMap f comp
  refine ⟨⟨⟨embedding, ?_⟩, embedding.injective⟩⟩
  have edge (i : ι) (a : Fin (n i)) :
      R.Adj (embedding ⟨i,0⟩) (embedding ⟨i,a.succ⟩) := by
    change R.Adj ⟨f i,0⟩ ⟨f i,((g i a).val).succ⟩
    exact (Finset.mem_filter.mp (g i a).property).2
  intro u v huv
  obtain ⟨i,a,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩ := (forest_adj n).mp huv
  · exact edge i a
  · exact (edge i a).symm

private theorem diagonal_prefix {s t : ℕ} (n : Fin s → ℕ) (m : Fin t → ℕ)
    (hn : Antitone n) (hm : Antitone m) (i : Fin s) (j : Fin t) (k : ℕ)
    (hk : k ≤ i.val+j.val) : n i + m j - 1 ≤ (((univ : Finset (Fin s × Fin t)).filter (fun p => (p.1.val+1)+(p.2.val+1)=(k+2))).sup (fun p => n p.1+m p.2-1)) := by
  let a : Fin s := ⟨min i.val k, lt_of_le_of_lt (min_le_left ..) i.isLt⟩
  let b : Fin t := ⟨k-a.val, by dsimp [a]; have := j.isLt; omega⟩
  have ha : a ≤ i := (min_le_left i.val k : min i.val k ≤ i.val)
  have hb : b ≤ j := by change k-min i.val k ≤ j.val; omega
  have hmem : (a,b) ∈ (univ : Finset (Fin s × Fin t)).filter
      (fun p => (p.1.val+1)+(p.2.val+1)=k+2) := by
    simp [a,b]; omega
  exact (Nat.sub_le_sub_right (Nat.add_le_add (hn ha) (hm hb)) 1).trans (Finset.le_sup (f := fun p : Fin s × Fin t => n p.1 + m p.2 - 1) hmem)

private theorem diagonal_sum {s t : ℕ} (n : Fin s → ℕ) (m : Fin t → ℕ) :
    (∑ k : Fin (s+t-1), (((univ : Finset (Fin s × Fin t)).filter (fun p => (p.1.val+1)+(p.2.val+1)=(k.val+2))).sup (fun p => n p.1+m p.2-1))) =
      ∑ k ∈ Icc 2 (s+t), (((univ : Finset (Fin s × Fin t)).filter (fun p => (p.1.val+1)+(p.2.val+1)=k)).sup (fun p => n p.1+m p.2-1)) := by
  apply sum_bij (fun (k : Fin (s+t-1)) _ => k.val+2)
  · intro k _
    have := k.isLt
    simp; omega
  · intro k _ l _ h
    apply Fin.ext
    omega
  · intro k hk
    obtain ⟨h₁,h₂⟩ := mem_Icc.mp hk
    exact ⟨⟨k-2,by omega⟩,mem_univ _,by dsimp; omega⟩
  · intro _ _
    rfl

private theorem mapped_forcing {α β V W : Type}
    (A : SimpleGraph α) (B : SimpleGraph β) (G : SimpleGraph V) (f : V ↪ W)
    (h : ∀ R ≤ G, A.IsContained R ∨ B.IsContained (G \ R)) :
    ∀ R ≤ G.map f, A.IsContained R ∨ B.IsContained (G.map f \ R) := by
  intro R hR
  have hsub : R.comap f ≤ G := by
    intro u v huv
    exact SimpleGraph.map_adj_apply.mp (hR huv)
  rcases h (R.comap f) hsub with hred | hblue
  · obtain ⟨hc⟩ := hred
    exact Or.inl ⟨((SimpleGraph.Embedding.comap f R).toCopy).comp hc⟩
  · obtain ⟨hc⟩ := hblue
    let g : (G \ R.comap f).Copy (G.map f \ R) :=
      ⟨⟨f,fun h => ⟨SimpleGraph.map_adj_apply.mpr h.1, h.2⟩⟩, f.injective⟩
    exact Or.inr ⟨g.comp hc⟩

private theorem size_host {α β V : Type} [Fintype V]
    (A : SimpleGraph α) (B : SimpleGraph β) (G : SimpleGraph V)
    (h : ∀ R ≤ G, A.IsContained R ∨ B.IsContained (G \ R)) :
    ∃ (N : ℕ) (H : SimpleGraph (Fin N)), H.edgeSet.ncard = G.edgeSet.ncard ∧
      ∀ R ≤ H, A.IsContained R ∨ B.IsContained (H \ R) := by
  let e := Fintype.equivFin V
  exact ⟨_, G.map e.toEmbedding, (Nat.card_congr (Iso.map e G).mapEdgeSet).symm,
    mapped_forcing A B G e.toEmbedding h⟩

private theorem upper_host {s t : ℕ} (n : Fin s → ℕ) (m : Fin t → ℕ)
    (hn : Antitone n) (hm : Antitone m)
    (hmatch : ∀ (r b : Fin (s+t-1) → ℕ),
      (∀ (i : Fin s) (j : Fin t) (k : Fin (s+t-1)), k.val ≤ i.val+j.val →
        n i+m j-1 ≤ r k+b k) →
      (∃ f : Fin s ↪ Fin (s+t-1), ∀ i, n i ≤ r (f i)) ∨
      (∃ f : Fin t ↪ Fin (s+t-1), ∀ j, m j ≤ b (f j))) :
    ∃ (N : ℕ) (H : SimpleGraph (Fin N)),
      H.edgeSet.ncard = (∑ k ∈ Icc 2 (s+t), (((univ : Finset (Fin s × Fin t)).filter (fun p => (p.1.val+1)+(p.2.val+1)=k)).sup (fun p => n p.1+m p.2-1))) ∧
      ∀ R ≤ H, ((fromRel (fun (u v : Σ i, Fin (n i+1)) => u.1 = v.1 ∧ (u.2.val = 0 ∨ v.2.val = 0)))).IsContained R ∨ ((fromRel (fun (u v : Σ i, Fin (m i+1)) => u.1 = v.1 ∧ (u.2.val = 0 ∨ v.2.val = 0)))).IsContained (H \ R) := by
  classical
  let L (k : Fin (s+t-1)) := (((univ : Finset (Fin s × Fin t)).filter (fun p => (p.1.val+1)+(p.2.val+1)=(k.val+2))).sup (fun p => n p.1+m p.2-1))
  have he : ((fromRel (fun (u v : Σ i, Fin (L i+1)) => u.1 = v.1 ∧ (u.2.val = 0 ∨ v.2.val = 0)))).edgeSet.ncard = ∑ k ∈ Icc 2 (s+t), (((univ : Finset (Fin s × Fin t)).filter (fun p => (p.1.val+1)+(p.2.val+1)=k)).sup (fun p => n p.1+m p.2-1)) :=
    (forest_edges L).trans (diagonal_sum n m)
  rw [← he]
  apply size_host _ _ ((fromRel (fun (u v : Σ i, Fin (L i+1)) => u.1 = v.1 ∧ (u.2.val = 0 ∨ v.2.val = 0))))
  intro R _
  let B := (fromRel (fun (u v : Σ i, Fin (L i+1)) => u.1 = v.1 ∧ (u.2.val = 0 ∨ v.2.val = 0))) \ R
  let red (k : Fin (s+t-1)) := (univ.filter
    (fun a : Fin (L k) => R.Adj ⟨k,0⟩ ⟨k,a.succ⟩)).card
  let blue (k : Fin (s+t-1)) := (univ.filter
    (fun a : Fin (L k) => B.Adj ⟨k,0⟩ ⟨k,a.succ⟩)).card
  have hc (k : Fin (s+t-1)) : red k + blue k = L k := by
    have hB (a : Fin (L k)) : B.Adj ⟨k,0⟩ ⟨k,a.succ⟩ ↔ ¬ R.Adj ⟨k,0⟩ ⟨k,a.succ⟩ := by
      exact and_iff_right ((forest_adj L).mpr ⟨k,a,Or.inl ⟨rfl,rfl⟩⟩)
    simp only [red, blue, hB]
    rw [Finset.card_filter_add_card_filter_not]
    simp
  rcases hmatch red blue (fun i j k hk => (diagonal_prefix n m hn hm i j k.val hk).trans (hc k).ge)
    with ⟨f,hf⟩ | ⟨f,hf⟩
  · exact Or.inl (forest_copy n L R f hf)
  · exact Or.inr (forest_copy m L B f hf)



private theorem forest_active {ι : Type} (n : ι → ℕ) (hn : ∀ i, 1 ≤ n i) :
    ∀ v, ∃ w, (fromRel (fun (u v : Σ i, Fin (n i+1)) => u.1 = v.1 ∧ (u.2.val = 0 ∨ v.2.val = 0))).Adj v w := by
  rintro ⟨i,a⟩
  induction a using Fin.cases with
  | zero =>
    let z : Fin (n i) := ⟨0, hn i⟩
    exact ⟨⟨i,z.succ⟩, (forest_adj n).mpr ⟨i,z,Or.inl ⟨rfl,rfl⟩⟩⟩
  | succ a => exact ⟨⟨i,0⟩, (forest_adj n).mpr ⟨i,a,Or.inr ⟨rfl,rfl⟩⟩⟩

private theorem compact_copy {α V : Type} {A : SimpleGraph α} {C G : SimpleGraph V}
    (ha : ∀ a, ∃ b, A.Adj a b) (hCG : C ≤ G) (h : A.IsContained C) :
    A.IsContained (C.induce G.support) := by
  obtain ⟨f⟩ := h
  have hx (a : α) : f a ∈ G.support := by
    obtain ⟨b,hb⟩ := ha a
    exact (hCG (f.toHom.map_adj hb)).mem_support_left
  exact ⟨⟨⟨fun a => ⟨f a,hx a⟩,fun h => f.toHom.map_adj h⟩,
    fun _ _ h => f.injective (congrArg Subtype.val h)⟩⟩

private theorem compact_forcing {α β V : Type} {A : SimpleGraph α} {B : SimpleGraph β}
    (ha : ∀ a, ∃ b, A.Adj a b) (hb : ∀ a, ∃ b, B.Adj a b) (G : SimpleGraph V)
    (h : ∀ R ≤ G, A.IsContained R ∨ B.IsContained (G \ R)) :
    ∀ R ≤ G.induce G.support, A.IsContained R ∨ B.IsContained (G.induce G.support \ R) := by
  intro R hR
  let f : G.support ↪ V := Function.Embedding.subtype _
  let E := R.map f
  have hE : E ≤ G := by
    intro a b hed
    obtain ⟨x,y,hxy,rfl,rfl⟩ := (SimpleGraph.map_adj f R a b).mp hed
    exact hR hxy
  have hred : E.induce G.support = R := by
    ext a b
    exact SimpleGraph.map_adj_apply (f := f)
  have hblue : (G \ E).induce G.support = (G.induce G.support \ R) := by
    ext a b
    change (G.Adj a.val b.val ∧ ¬ E.Adj (f a) (f b)) ↔ _
    simp only [E, SimpleGraph.map_adj_apply]
    rfl
  rcases h E hE with h | h
  · exact Or.inl (hred ▸ compact_copy ha hE h)
  · exact Or.inr (hblue ▸ compact_copy hb (show G \ E ≤ G from sdiff_le) h)

private theorem finite_support_bound {V : Type} [Fintype V] (G : SimpleGraph V) :
    G.support.ncard ≤ 2 * G.edgeSet.ncard := by
  classical
  have hs := G.sum_degrees_support_eq_twice_card_edges
  rw [G.edgeFinset_card, Set.fintypeCard_eq_ncard] at hs
  rw [← hs, Set.ncard_eq_toFinset_card']
  calc
    _ = ∑ v ∈ G.support.toFinset, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum (fun v hv => (G.degree_pos_iff_mem_support v).mpr (Set.mem_toFinset.mp hv))

private theorem filling {k : ℕ} (G : SimpleGraph (Fin (2*k))) (he : G.edgeSet.ncard ≤ k) :
    ∃ H : SimpleGraph (Fin (2*k)), G ≤ H ∧ H.edgeSet.ncard = k := by
  classical
  let T := (⊤ : SimpleGraph (Fin (2*k))).edgeFinset
  have hs : G.edgeFinset.card ≤ k := by simpa only [edgeFinset_card, Set.fintypeCard_eq_ncard] using he
  have ht : k ≤ T.card := by
    rw [show T.card = (2*k).choose 2 by simp only [T,card_edgeFinset_top_eq_card_choose_two,Fintype.card_fin], Nat.choose_two_right]
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
    cases k with
    | zero => simp
    | succ k =>
      have hk : 1 ≤ 2*(k+1)-1 := by omega
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left (2*(k+1)) hk
  obtain ⟨S,hGS,hST,hcard⟩ := exists_subsuperset_card_eq (edgeFinset_mono (show G ≤ ⊤ from le_top)) hs ht
  let E : Set (Sym2 (Fin (2*k))) := S
  refine ⟨fromEdgeSet E, (le_fromEdgeSet_iff G E).mpr (fun _ he => hGS (mem_edgeFinset.mpr he)), ?_⟩
  have heq : (fromEdgeSet E).edgeSet = E := by
    rw [edgeSet_fromEdgeSet]
    ext e
    constructor
    · exact And.left
    · intro he
      exact ⟨he, (⊤ : SimpleGraph (Fin (2*k))).not_isDiag_of_mem_edgeSet (mem_edgeFinset.mp (hST he))⟩
  rw [heq]
  simpa only [E, Set.ncard_coe_finset] using hcard

private theorem extension_forcing {α β V : Type} {A : SimpleGraph α} {B : SimpleGraph β}
    {G H : SimpleGraph V} (hGH : G ≤ H)
    (h : ∀ R ≤ G, A.IsContained R ∨ B.IsContained (G \ R)) :
    ∀ R ≤ H, A.IsContained R ∨ B.IsContained (H \ R) := by
  intro R _
  rcases h (G ⊓ R) inf_le_left with h | h
  · obtain ⟨f⟩ := h
    exact Or.inl ⟨(Copy.ofLE _ _ inf_le_right).comp f⟩
  · obtain ⟨f⟩ := h
    have hle : G \ (G ⊓ R) ≤ H \ R := by
      intro a b hab
      exact ⟨hGH hab.1, fun hR => hab.2 ⟨hab.1,hR⟩⟩
    exact Or.inr ⟨(Copy.ofLE _ _ hle).comp f⟩

private theorem padded_host {α β : Type} {A : SimpleGraph α} {B : SimpleGraph β}
    (ha : ∀ a, ∃ b, A.Adj a b) (hb : ∀ a, ∃ b, B.Adj a b)
    {v k : ℕ} (G : SimpleGraph (Fin v)) (he : G.edgeSet.ncard ≤ k)
    (h : ∀ R ≤ G, A.IsContained R ∨ B.IsContained (G \ R)) :
    ∃ H : SimpleGraph (Fin (2*k)), H.edgeSet.ncard = k ∧
      ∀ R ≤ H, A.IsContained R ∨ B.IsContained (H \ R) := by
  classical
  let C := G.induce G.support
  have hs : Fintype.card G.support ≤ Fintype.card (Fin (2*k)) := by
    rw [Fintype.card_fin, Set.fintypeCard_eq_ncard]
    exact (finite_support_bound G).trans (Nat.mul_le_mul_left _ he)
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hs
  have hm := mapped_forcing A B C f (compact_forcing ha hb G h)
  have hc : (C.map f).edgeSet.ncard ≤ k := by
    simpa only [← Set.fintypeCard_eq_ncard, ← edgeFinset_card, card_edgeFinset_map, C,
      card_edgeFinset_induce_support] using he
  obtain ⟨H,hCH,hsize⟩ := filling (C.map f) hc
  exact ⟨H,hsize,extension_forcing hCH hm⟩


theorem main : H1 → H2 → type_of% @Erdos561.erdos_561 := by
  intro h₁ h₂ s t hs ht n m hn hm pn pm
  let D := ∑ k ∈ Icc 2 (s+t), (((univ : Finset (Fin s × Fin t)).filter (fun p => (p.1.val+1)+(p.2.val+1)=k)).sup (fun p => n p.1+m p.2-1))
  let P : Set ℕ := {c | ∃ (v : ℕ) (G : SimpleGraph (Fin v)), G.edgeSet.ncard = c ∧
    ∀ R ≤ G, ((fromRel (fun (u v : Σ i, Fin (n i+1)) => u.1 = v.1 ∧ (u.2.val = 0 ∨ v.2.val = 0)))).IsContained R ∨ ((fromRel (fun (u v : Σ i, Fin (m i+1)) => u.1 = v.1 ∧ (u.2.val = 0 ∨ v.2.val = 0)))).IsContained (G \ R)}
  change sInf P = D
  have hw : D ∈ P := upper_host n m hn hm (h₁ s t n m)
  apply le_antisymm (Nat.sInf_le hw)
  by_contra! hlt
  obtain ⟨v,G,hsize,hforce⟩ := Nat.sInf_mem (show P.Nonempty from ⟨D,hw⟩)
  have he : G.edgeSet.ncard ≤ D-1 := by omega
  obtain ⟨H,hK,hcolor⟩ := padded_host (forest_active n pn) (forest_active m pm) G he hforce
  obtain ⟨R,hR,hr,hb⟩ := h₂ s t hs ht n m hn hm pn pm H hK
  exact (hcolor R hR).elim hr hb


end OMA.R_Erdos561_erdos_561_R1
