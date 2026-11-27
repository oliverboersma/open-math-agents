import FormalConjectures.ErdosProblems.«1177»
import Mathlib

/-!
Erdős Problem 1177, part (ii). The Erdos593 development is adapted from Eric Li's
Lean formalization accompanying arXiv:2606.24882, with proofs by Li and Aristotle.
Source (commit 5dcb6e49): https://github.com/ericlisg/erdos-593-1177-lean
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).

The single-file bundling and Mathlib compatibility changes are from the port in
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3792.
-/

-- Lift
section
open Cardinal Ordinal

namespace Erdos593

universe u

structure Hypergraph (V : Type u) where
  edges : Set (Set V)

def Hypergraph.ProperColoring {V : Type u} {C : Type*} (H : Hypergraph V)
    (c : V → C) : Prop :=
  ∀ e ∈ H.edges, ∃ u ∈ e, ∃ v ∈ e, c u ≠ c v

def Hypergraph.ColorableBy {V : Type u} (H : Hypergraph V) (θ : Cardinal.{u}) :
    Prop :=
  ∃ c : V → θ.out, H.ProperColoring c

def Hypergraph.HasChromatic {V : Type u} (H : Hypergraph V) (κ : Cardinal.{u}) :
    Prop :=
  H.ColorableBy κ ∧ ∀ θ, θ < κ → ¬ H.ColorableBy θ

def SimpleGraph.toHG {α : Type u} (A : SimpleGraph α) : Hypergraph α :=
  ⟨{ e | ∃ x y, A.Adj x y ∧ e = ({x, y} : Set α) }⟩

section Lift

variable {α : Type u} (A : SimpleGraph α) (κ : Cardinal.{u})

abbrev Idx := κ.ord.ToType

structure Node where
  pos : Idx κ
  seq : {q : Idx κ // q < pos} → A.edgeSet

def edgeOf {x y : α} (h : A.Adj x y) : A.edgeSet := ⟨s(x, y), by simpa using h⟩

def Node.pre (σ τ : Node A κ) : Prop :=
  ∃ h : σ.pos < τ.pos, ∀ (q : Idx κ) (hq : q < σ.pos),
     τ.seq ⟨q, lt_trans hq h⟩ = σ.seq ⟨q, hq⟩

def liftHG : Hypergraph (Node A κ × α) :=
  ⟨ { s | ∃ (σ τ : Node A κ) (x y z : α) (hpre : Node.pre A κ σ τ),
        (τ.seq ⟨σ.pos, hpre.1⟩ : Sym2 α) = s(x, y) ∧
        s = ({(σ, x), (σ, y), (τ, z)} : Set (Node A κ × α)) } ⟩

theorem liftHG_isTripleSystem :
    ∀ e ∈ (liftHG A κ).edges, ∃ a b c : Node A κ × α,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ e = {a, b, c} := by
  intro e he
  obtain ⟨σ, τ, x, y, z, hpre, h_edge⟩ := (Set.mem_setOf.mp he);
  refine' ⟨ ( σ, x ), ( σ, y ), ( τ, z ), _, _, _, h_edge.2 ⟩ <;> simp_all +decide ;
  · intro h; simp_all +decide ;
    exact absurd h_edge.1 ( by exact fun h => by have := τ.seq ⟨ σ.pos, hpre.1 ⟩ |>.2; aesop );
  · rintro rfl; exact absurd hpre.1 ( lt_irrefl _ )
  · rintro rfl; exact absurd hpre.1 ( lt_irrefl _ ) ;

end Lift

theorem toHG_proper_iff {α : Type u} (A : SimpleGraph α) {C : Type*}
    (c : α → C) :
    (SimpleGraph.toHG A).ProperColoring c ↔ ∀ x y, A.Adj x y → c x ≠ c y := by
  simp [SimpleGraph.toHG, Hypergraph.ProperColoring];
  grind

theorem exists_mono_edge {α : Type u} {A : SimpleGraph α} {θ : Cardinal.{u}}
    (hA : ¬ (SimpleGraph.toHG A).ColorableBy θ) (g : α → θ.out) :
    ∃ x y, A.Adj x y ∧ g x = g y := by
  contrapose! hA;
  exact ⟨ g, fun e he => by rcases he with ⟨ x, y, hxy, rfl ⟩ ; exact ⟨ x, by simp, y, by simp, hA x y hxy ⟩ ⟩

theorem lift_colorableBy {α : Type u} (A : SimpleGraph α) (κ : Cardinal.{u})
    (hA : (SimpleGraph.toHG A).ColorableBy κ) :
    (liftHG A κ).ColorableBy κ := by
  obtain ⟨c, hc⟩ := hA;
  refine' ⟨ fun ⟨ σ, x ⟩ => c x, _ ⟩;
  intro e he
  obtain ⟨σ, τ, x, y, z, hpre, hseq, rfl⟩ := he;
  have := hc ( τ.seq ⟨ σ.pos, hpre.1 ⟩ : Set α ) ?_ <;> simp_all +decide [ SimpleGraph.toHG ];
  · tauto;
  · cases h : τ.seq ⟨ σ.pos, hpre.1 ⟩ ; aesop

section LowerBound

variable {α : Type u} (A : SimpleGraph α) (κ : Cardinal.{u})
  {θ : Cardinal.{u}} (c : Node A κ × α → θ.out)
  (hA : ¬ (SimpleGraph.toHG A).ColorableBy θ)

noncomputable def stepEdge (a : Idx κ)
    (g : (q : Idx κ) → q < a → {p : α × α // A.Adj p.1 p.2}) :
    {p : α × α // A.Adj p.1 p.2} :=
  let node : Node A κ := ⟨a, fun q => edgeOf A (g q.1 q.2).2⟩
  let h := exists_mono_edge hA (fun x => c (node, x))
  ⟨(Classical.choose h, Classical.choose (Classical.choose_spec h)),
   (Classical.choose_spec (Classical.choose_spec h)).1⟩

noncomputable def branch : Idx κ → {p : α × α // A.Adj p.1 p.2} :=
  WellFounded.fix wellFounded_lt (stepEdge A κ c hA)

theorem branch_eq (a : Idx κ) :
    branch A κ c hA a = stepEdge A κ c hA a (fun q _ => branch A κ c hA q) :=
  WellFounded.fix_eq _ _ _

noncomputable def branchNode (a : Idx κ) : Node A κ :=
  ⟨a, fun q => edgeOf A (branch A κ c hA q.1).2⟩

theorem branch_mono (a : Idx κ) :
    c (branchNode A κ c hA a, (branch A κ c hA a).1.1)
      = c (branchNode A κ c hA a, (branch A κ c hA a).1.2) := by
  rw [ branch_eq ]
  exact (Classical.choose_spec (Classical.choose_spec (exists_mono_edge hA
    (fun x => c (⟨a, fun q => edgeOf A (branch A κ c hA q.1).2⟩, x))))).2

theorem branchNode_seq (a b : Idx κ) (hab : a < b) :
    ((branchNode A κ c hA b).seq ⟨a, hab⟩ : Sym2 α)
      = s((branch A κ c hA a).1.1, (branch A κ c hA a).1.2) := by
  rfl

theorem lift_not_colorableBy (hA : ¬ (SimpleGraph.toHG A).ColorableBy θ)
    (hθ : θ < κ) :
    ¬ (liftHG A κ).ColorableBy θ := by
  intro hLift;

  obtain ⟨c, hc⟩ := hLift
  set d : Idx κ → θ.out := fun a => c (branchNode A κ c hA a, (branch A κ c hA a).1.1);

  obtain ⟨a, b, hab, hd⟩ : ∃ a b : Idx κ, a < b ∧ d a = d b := by
    by_contra! h;
    have h_card : Cardinal.mk (Idx κ) ≤ Cardinal.mk (Quotient.out θ) := by
      exact Cardinal.mk_le_of_injective ( show Function.Injective d from fun a b hab => le_antisymm ( le_of_not_gt fun h' => h _ _ h' hab.symm ) ( le_of_not_gt fun h' => h _ _ h' hab ) );
    simp_all +decide [ Cardinal.mk_toType ];
    exact not_lt_of_ge h_card hθ;
  obtain ⟨ u, hu, v, hv, huv ⟩ := hc { ( branchNode A κ c hA a, ( branch A κ c hA a ).1.1 ), ( branchNode A κ c hA a, ( branch A κ c hA a ).1.2 ), ( branchNode A κ c hA b, ( branch A κ c hA b ).1.1 ) } ⟨ branchNode A κ c hA a, branchNode A κ c hA b, ( branch A κ c hA a ).1.1, ( branch A κ c hA a ).1.2, ( branch A κ c hA b ).1.1, ⟨ hab, fun q hq => rfl ⟩, by
    convert branchNode_seq A κ c hA a b hab <;> rfl, rfl ⟩ ; simp_all +decide [ Set.mem_insert_iff, Set.mem_singleton_iff ];
  rcases hu with ( rfl | rfl | rfl ) <;> rcases hv with ( rfl | rfl | rfl ) <;> simp_all +decide [ branch_mono ]; all_goals have := branch_mono A κ c hA a; have := branch_mono A κ c hA b; aesop;

end LowerBound

theorem lift_hasChromatic {α : Type u} (A : SimpleGraph α) (κ : Cardinal.{u})
    (hA : (SimpleGraph.toHG A).HasChromatic κ) :
    (liftHG A κ).HasChromatic κ := by
  refine' ⟨ lift_colorableBy A κ hA.1, fun θ hθ => _ ⟩;
  apply lift_not_colorableBy A κ;
  · exact hA.2 θ hθ;
  · exact hθ

end Erdos593
end

-- Defs
section
open Cardinal Ordinal

namespace Erdos593

universe u v

def Hypergraph.IsTripleSystem {V : Type*} (H : Hypergraph V) : Prop :=
  ∀ e ∈ H.edges, e.ncard = 3

def Hypergraph.UncountablyChromatic {V : Type u} (H : Hypergraph V) : Prop :=
  ¬ H.ColorableBy ℵ₀

structure FTS where

  V : Type
  [finV : Fintype V]
  [decV : DecidableEq V]

  edges : Finset (Finset V)

  card3 : ∀ e ∈ edges, e.card = 3

instance FTS.instFintypeV (F : FTS) : Fintype F.V := F.finV
instance FTS.instDecEqV (F : FTS) : DecidableEq F.V := F.decV

def FTS.Isolated (F : FTS) (x : F.V) : Prop :=
  ∀ e ∈ F.edges, x ∉ e

def FTS.Linear (F : FTS) : Prop :=
  ∀ e₁ ∈ F.edges, ∀ e₂ ∈ F.edges, e₁ ≠ e₂ → (e₁ ∩ e₂).card ≤ 1

def FTS.Embeds (F : FTS) {W : Type u} (H : Hypergraph W) : Prop :=
  ∃ f : F.V → W, Function.Injective f ∧
    ∀ e ∈ F.edges, (f '' (↑e : Set F.V)) ∈ H.edges

def FTS.Obligatory (F : FTS) : Prop :=
  ∀ {W : Type u} (H : Hypergraph W),
    H.IsTripleSystem → H.UncountablyChromatic → F.Embeds H

def FTS.InSpec (F : FTS) (lam : Cardinal.{u}) : Prop :=
  ℵ₀ < lam ∧ ∃ (W : Type u) (H : Hypergraph W),
    H.IsTripleSystem ∧ H.HasChromatic lam ∧ ¬ F.Embeds H

def FTS.FGnonempty (G : FTS) (kappa : Cardinal.{u}) : Prop :=
  ∃ (W : Type u) (H : Hypergraph W),
    H.IsTripleSystem ∧ H.HasChromatic kappa ∧ ¬ G.Embeds H

end Erdos593
end

-- Reduce
section
open Cardinal Function

namespace Erdos593

universe u

open Classical in

noncomputable def FTS.reduce (F : FTS) : FTS where
  V := {x : F.V // ¬ F.Isolated x}
  finV := Fintype.ofFinite _
  decV := Subtype.instDecidableEq
  edges := F.edges.attach.image (fun e => Finset.subtype (fun x => ¬ F.Isolated x) e.1)
  card3 := by
    classical
    intro e he
    simp only [Finset.mem_image, Finset.mem_attach, true_and] at he
    obtain ⟨d, rfl⟩ := he
    have hd : d.1 ∈ F.edges := d.2
    rw [Finset.card_subtype]
    have : d.1.filter (fun x => ¬ F.Isolated x) = d.1 := by
      apply Finset.filter_true_of_mem
      intro x hx
      simp only [FTS.Isolated, not_forall]
      exact ⟨d.1, hd, by simpa using hx⟩
    rw [this]
    exact F.card3 d.1 hd

open Classical in
theorem FTS.mem_reduce_edges (F : FTS) (e : Finset {x : F.V // ¬ F.Isolated x}) :
    e ∈ F.reduce.edges ↔
      ∃ d : {d // d ∈ F.edges}, Finset.subtype (fun x => ¬ F.Isolated x) d.1 = e := by
  constructor
  · intro h
    obtain ⟨d, -, hd⟩ := Finset.mem_image.1 h
    exact ⟨d, hd⟩
  · rintro ⟨d, hd⟩
    exact Finset.mem_image.2 ⟨d, Finset.mem_attach _ _, hd⟩

theorem Hypergraph.UncountablyChromatic.infinite {W : Type u} {H : Hypergraph W}
    (htri : H.IsTripleSystem) (h : H.UncountablyChromatic) : Infinite W := by
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  apply h
  have hinf : Infinite ((ℵ₀ : Cardinal.{u}).out) := by
    rw [Cardinal.infinite_iff, Cardinal.mk_out]
  have hle : (#W) ≤ (#((ℵ₀ : Cardinal.{u}).out)) :=
    le_trans (le_of_lt (Cardinal.lt_aleph0_of_finite W)) (Cardinal.infinite_iff.mp hinf)
  obtain ⟨c, hc⟩ := (Cardinal.le_def _ _).mp hle
  exact ⟨c, fun e he => by
    obtain ⟨a, b, d, hab, had, hbd, rfl⟩ := Set.ncard_eq_three.mp (htri e he)
    exact ⟨a, by simp, b, by simp, fun hcab => hab (hc hcab)⟩⟩

theorem FTS.reduce_embeds_of_embeds (F : FTS) {W : Type u} {H : Hypergraph W}
    (h : F.Embeds H) : F.reduce.Embeds H := by
  classical
  obtain ⟨f, hf₁, hf₂⟩ := h
  refine ⟨fun x => f x.val, hf₁.comp Subtype.coe_injective, ?_⟩
  intro e he
  obtain ⟨d, rfl⟩ := (FTS.mem_reduce_edges F e).1 he
  convert hf₂ d.1 d.2 using 1
  ext w
  simp only [Set.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.val, Finset.mem_coe.2 (Finset.mem_subtype.1 (Finset.mem_coe.1 ha)), rfl⟩
  · rintro ⟨a, ha, rfl⟩
    have hna : ¬ F.Isolated a := fun hiso => hiso d.1 d.2 ha
    exact ⟨⟨a, hna⟩, Finset.mem_coe.2 (Finset.mem_subtype.2 (Finset.mem_coe.1 ha)), rfl⟩

theorem exists_injective_avoiding {A : Type} [Finite A] {W : Type u} (g : A → W)
    [Infinite W] (S : Type) [Finite S] :
    ∃ emb : S → W, Function.Injective emb ∧ ∀ x, emb x ∉ Set.range g := by
  classical
  have hcompl : Set.Infinite ((Set.range g)ᶜ) := (Set.finite_range g).infinite_compl
  obtain ⟨t, ht_sub, ht_card⟩ := hcompl.exists_subset_card_eq (Nat.card S)
  have e : S ≃ Fin (Nat.card S) := by
    have := Fintype.ofFinite S; simpa [Nat.card_eq_fintype_card] using Fintype.equivFin S
  have e2 := (Finset.equivFinOfCardEq ht_card).symm
  exact ⟨fun x => (e2 (e x)).1, fun a b hab => e.injective (e2.injective (Subtype.ext hab)),
    fun x hx => (ht_sub (e2 (e x)).2) hx⟩

theorem FTS.embeds_of_reduce_embeds (F : FTS) {W : Type u} [Infinite W]
    {H : Hypergraph W} (h : F.reduce.Embeds H) : F.Embeds H := by
  classical
  obtain ⟨g, hg, hge⟩ := h
  obtain ⟨emb, hemb_inj, hemb_range⟩ := exists_injective_avoiding g {x : F.V // F.Isolated x}
  set f : F.V → W := fun x => if hx : ¬ F.Isolated x then g ⟨x, hx⟩ else emb ⟨x, not_not.mp hx⟩
    with hf
  refine ⟨f, ?_, ?_⟩
  · intro a b hab
    simp only [hf] at hab
    by_cases ha : ¬ F.Isolated a <;> by_cases hb : ¬ F.Isolated b
    · rw [dif_pos ha, dif_pos hb] at hab; exact congrArg Subtype.val (hg hab)
    · rw [dif_pos ha, dif_neg hb] at hab
      exact absurd ⟨_, hab⟩ (hemb_range ⟨b, not_not.mp hb⟩)
    · rw [dif_neg ha, dif_pos hb] at hab
      exact absurd ⟨_, hab.symm⟩ (hemb_range ⟨a, not_not.mp ha⟩)
    · rw [dif_neg ha, dif_neg hb] at hab; exact congrArg Subtype.val (hemb_inj hab)
  · intro e he
    have hre : Finset.subtype (fun x => ¬ F.Isolated x) e ∈ F.reduce.edges := by
      exact (FTS.mem_reduce_edges F _).2 ⟨⟨e, he⟩, rfl⟩
    have hE := hge _ hre
    convert hE using 1
    ext w
    simp only [Set.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩
      have haa : a ∈ e := by simpa using ha
      have hna : ¬ F.Isolated a := fun hiso => hiso e he haa
      refine ⟨⟨a, hna⟩, Finset.mem_coe.mpr (Finset.mem_subtype.mpr haa), ?_⟩
      simp only [hf]; rw [dif_pos hna]
    · rintro ⟨a, ha, rfl⟩
      have haa : a.val ∈ e := Finset.mem_subtype.mp (Finset.mem_coe.mp ha)
      refine ⟨a.val, Finset.mem_coe.mpr haa, ?_⟩
      simp only [hf]; rw [dif_pos a.2]; exact congrArg g (Subtype.eta a a.2)

theorem FTS.embeds_reduce_iff (F : FTS) {W : Type u} [Infinite W] (H : Hypergraph W) :
    F.Embeds H ↔ F.reduce.Embeds H :=
  ⟨F.reduce_embeds_of_embeds, F.embeds_of_reduce_embeds⟩

theorem FTS.obligatory_reduce_iff (F : FTS) :
    FTS.Obligatory.{u} F ↔ FTS.Obligatory.{u} F.reduce := by
  constructor
  · intro hF W H htri huc
    exact F.reduce_embeds_of_embeds (hF H htri huc)
  · intro hF W H htri huc
    have : Infinite W := huc.infinite htri
    exact F.embeds_of_reduce_embeds (hF H htri huc)

theorem FTS.inSpec_reduce_iff (F : FTS) (lam : Cardinal.{u}) :
    F.InSpec lam ↔ F.reduce.InSpec lam := by
  unfold FTS.InSpec
  constructor
  · rintro ⟨hlam, W, H, htri, hchr, hne⟩
    have hInf : Infinite W := Hypergraph.UncountablyChromatic.infinite htri (by
      intro hc; exact absurd (hchr.2 ℵ₀ hlam hc) (by simp))
    exact ⟨hlam, W, H, htri, hchr, fun hcon => hne (F.embeds_of_reduce_embeds hcon)⟩
  · rintro ⟨hlam, W, H, htri, hchr, hne⟩
    exact ⟨hlam, W, H, htri, hchr, fun hcon => hne (F.reduce_embeds_of_embeds hcon)⟩

end Erdos593
end

-- Structures
section
open Cardinal

namespace Erdos593

universe u

structure BergeCycle (F : FTS) where
  m : ℕ
  hm : 2 ≤ m
  v : ZMod m → F.V
  e : ZMod m → {e : Finset F.V // e ∈ F.edges}
  vinj : Function.Injective v
  einj : Function.Injective e
  mem_left : ∀ i, v i ∈ (e i).1
  mem_right : ∀ i, v (i + 1) ∈ (e i).1

def OnBergeCycle (F : FTS) (w : F.V) (ed : {e : Finset F.V // e ∈ F.edges}) : Prop :=
  ∃ (c : BergeCycle F) (i : ZMod c.m), c.e i = ed ∧ (c.v i = w ∨ c.v (i + 1) = w)

def IsBridgeInc (F : FTS) (w : F.V) (ed : {e : Finset F.V // e ∈ F.edges}) : Prop :=
  w ∈ ed.1 ∧ ¬ OnBergeCycle F w ed

structure BridgeSelector (F : FTS) where
  p : {e : Finset F.V // e ∈ F.edges} → F.V
  isBridge : ∀ ed, IsBridgeInc F (p ed) ed

def FTS.IntrinsicObligatory (F : FTS) : Prop :=
  F.Linear ∧
  (∀ ed : {e : Finset F.V // e ∈ F.edges}, ∃ w ∈ ed.1, IsBridgeInc F w ed) ∧
  (∀ c : BergeCycle F, Even c.m)

def FTS.disjUnion (F G : FTS) : FTS where
  V := F.V ⊕ G.V
  edges := F.edges.image (Finset.map Function.Embedding.inl) ∪
           G.edges.image (Finset.map Function.Embedding.inr)
  card3 := by
    intro e he
    simp only [Finset.mem_union, Finset.mem_image] at he
    rcases he with ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩ <;>
      rw [Finset.card_map] <;> [exact F.card3 d hd; exact G.card3 d hd]

noncomputable def FTS.amalgamate (F G : FTS) (x : F.V) (y : G.V) : FTS where
  V := F.V ⊕ {b : G.V // b ≠ y}
  edges :=
    F.edges.image (Finset.map Function.Embedding.inl) ∪
    G.edges.image (Finset.map ⟨fun b => if h : b = y then Sum.inl x else Sum.inr ⟨b, h⟩, by
      intro a b hab
      by_cases ha : a = y <;> by_cases hb : b = y <;> simp_all⟩)
  card3 := by
    intro e he
    simp only [Finset.mem_union, Finset.mem_image] at he
    rcases he with ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩ <;>
      rw [Finset.card_map] <;> [exact F.card3 d hd; exact G.card3 d hd]

theorem FTS.mem_amalgamate_edges (F G : FTS) (x : F.V) (y : G.V)
    (e : Finset (F.amalgamate G x y).V) :
    e ∈ (F.amalgamate G x y).edges ↔
      (∃ a ∈ F.edges, Finset.map Function.Embedding.inl a = e) ∨
      (∃ a ∈ G.edges, Finset.map ⟨fun b => if h : b = y then Sum.inl x else Sum.inr ⟨b, h⟩, by
        intro a b hab
        by_cases ha : a = y <;> by_cases hb : b = y <;> simp_all⟩ a = e) := by
  constructor
  · intro h
    rcases Finset.mem_union.1 h with h | h
    · exact Or.inl (Finset.mem_image.1 h)
    · exact Or.inr (Finset.mem_image.1 h)
  · rintro (h | h)
    · exact Finset.mem_union.2 (Or.inl (Finset.mem_image.2 h))
    · exact Finset.mem_union.2 (Or.inr (Finset.mem_image.2 h))

noncomputable def graphExpansion {VJ : Type} [Fintype VJ] [DecidableEq VJ]
    (J : SimpleGraph VJ) [DecidableRel J.Adj] : FTS where
  V := VJ ⊕ {e : Sym2 VJ // e ∈ J.edgeFinset}
  edges := J.edgeFinset.attach.image (fun e =>
    {Sum.inl (Quot.out e.1).1, Sum.inl (Quot.out e.1).2, Sum.inr e})
  card3 := by
    classical
    intro s hs
    simp only [Finset.mem_image, Finset.mem_attach, true_and] at hs
    obtain ⟨e, rfl⟩ := hs
    have hmem : e.1 ∈ J.edgeSet := SimpleGraph.mem_edgeFinset.mp e.2
    rw [← Quot.out_eq e.1] at hmem
    have hadj : J.Adj (Quot.out e.1).1 (Quot.out e.1).2 := hmem
    have hne : (Quot.out e.1).1 ≠ (Quot.out e.1).2 := hadj.ne
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton]; exact fun h => Sum.inl_ne_inr h
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨fun h => hne (Sum.inl_injective h), fun h => Sum.inl_ne_inr h⟩

def FTS.Iso (F G : FTS) : Prop :=
  ∃ φ : F.V ≃ G.V, ∀ e : Finset F.V, e ∈ F.edges ↔ e.map φ.toEmbedding ∈ G.edges

inductive Bclass : FTS → Prop
  | edgeless (F : FTS) (h : F.edges = ∅) : Bclass F
  | expansion {VJ : Type} [Fintype VJ] [DecidableEq VJ] (J : SimpleGraph VJ)
      [DecidableRel J.Adj] (hJ : J.Colorable 2) : Bclass (graphExpansion J)
  | iso {F G : FTS} (h : FTS.Iso F G) : Bclass F → Bclass G
  | union {F G : FTS} : Bclass F → Bclass G → Bclass (F.disjUnion G)
  | amalg {F G : FTS} (x : F.V) (y : G.V) : Bclass F → Bclass G → Bclass (F.amalgamate G x y)

def Hypergraph.Linear {W : Type*} (H : Hypergraph W) : Prop :=
  ∀ e₁ ∈ H.edges, ∀ e₂ ∈ H.edges, e₁ ≠ e₂ → (e₁ ∩ e₂).Subsingleton

theorem obligatory_iso {F G : FTS} (h : FTS.Iso F G) (ih : FTS.Obligatory.{u} F) :
    FTS.Obligatory.{u} G := by
  intro W H htri huc;
  obtain ⟨ φ, hφ ⟩ := h;
  obtain ⟨ f, hf, hfe ⟩ := ih H htri huc;
  use fun x => f ( φ.symm x );
  refine' ⟨ hf.comp φ.symm.injective, _ ⟩;
  intro e he; specialize hφ ( Finset.map φ.symm.toEmbedding e ) ; simp_all +decide [ Finset.map_map ] ;
  convert hfe _ hφ using 1 ; ext ; aesop

end Erdos593
end

-- Compactness
section
open SimpleGraph

namespace Erdos593

theorem colorable_of_forall_finite {V : Type*} (G : SimpleGraph V) (k : ℕ) [NeZero k]
    (h : ∀ s : Finset V, ∃ c : V → Fin k, ∀ a ∈ s, ∀ b ∈ s, G.Adj a b → c a ≠ c b) :
    ∃ c : V → Fin k, ∀ a b, G.Adj a b → c a ≠ c b := by
  classical
  by_contra h_contra
  push_neg at h_contra
  set T : V × V → Set (V → Fin k) := fun p => {c | G.Adj p.1 p.2 → c p.1 ≠ c p.2} with hT_def
  have hT_closed : ∀ p : V × V, IsClosed (T p) := by
    intro p
    by_cases h_adj : G.Adj p.1 p.2
    · simp_all +decide
      exact isClosed_compl_iff.mpr (isOpen_discrete {x : Fin k × Fin k | x.1 = x.2}
        |> IsOpen.preimage (show Continuous fun c : V → Fin k => (c p.1, c p.2) from
          Continuous.prodMk (continuous_apply _) (continuous_apply _)))
    · aesop
  have h_empty : (Set.univ : Set (V → Fin k)) ∩ ⋂ p : V × V, T p = ∅ := by
    ext c
    simp only [Set.mem_inter_iff, Set.mem_univ, true_and, Set.mem_iInter, Set.mem_empty_iff_false,
      iff_false, not_forall]
    obtain ⟨a, b, hab, hcab⟩ := h_contra c
    exact ⟨(a, b), by simp only [hT_def, Set.mem_setOf_eq, not_forall]; exact ⟨hab, not_not.mpr hcab⟩⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subfamily_closed T hT_closed h_empty

  set s' : Finset V := s.image Prod.fst ∪ s.image Prod.snd with hs'_def
  have hs' : ∀ p ∈ s, p.1 ∈ s' ∧ p.2 ∈ s' := by
    intro p hp
    exact ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp),
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)⟩
  obtain ⟨c, hc⟩ := h s'
  apply Set.not_nonempty_empty
  rw [← hs]
  exact ⟨c, Set.mem_univ _, Set.mem_iInter₂.2 fun p hp hadj =>
    hc _ (hs' p hp).1 _ (hs' p hp).2 hadj⟩

end Erdos593
end

-- AmalgHelpers
section
open Cardinal SimpleGraph

namespace Erdos593

universe u

def Hypergraph.restrict {W : Type u} (H : Hypergraph W) (S : Set W) : Hypergraph W :=
  ⟨{e | e ∈ H.edges ∧ e ⊆ S}⟩

theorem colorableBy_aleph0_of_countable {W : Type u} (H : Hypergraph W) {T : Type u}
    (hT : #T ≤ ℵ₀) {c : W → T} (hc : H.ProperColoring c) : H.ColorableBy ℵ₀ := by
  obtain ⟨ f, hf ⟩ := Cardinal.mk_le_aleph0_iff.mp hT;
  obtain ⟨ g, hg ⟩ := Cardinal.eq.1 ( Cardinal.mk_out ℵ₀ );
  refine' ⟨ fun w => hg ⟨ f ( c w ) ⟩, _ ⟩;
  intro e he; obtain ⟨ u, hu, v, hv, huv ⟩ := hc e he; use u, hu, v, hv; simp +decide [ * ] ;
  grind +qlia

theorem countable_prod_out {I : Type} [Fintype I] : #(I × (ℵ₀ : Cardinal.{u}).out) ≤ ℵ₀ := by
  convert Cardinal.mk_le_aleph0;
  convert instCountableProd;
  · infer_instance;
  · convert Cardinal.mk_le_aleph0_iff.mp ( le_of_eq ( Cardinal.mk_out ℵ₀ ) )

theorem restrict_colorable_of_obligatory {W : Type u} {H : Hypergraph W}
    (htri : H.IsTripleSystem) {F : FTS} (hF : FTS.Obligatory.{u} F)
    {S : Set W} (hfree : ¬ F.Embeds (H.restrict S)) :
    (H.restrict S).ColorableBy ℵ₀ := by
  contrapose! hfree;
  apply hF;
  · exact fun e he => htri e he.1;
  · exact hfree

theorem colorableBy_of_finite_parts {W : Type u} (H : Hypergraph W) {I : Type}
    [Fintype I] [Nonempty I] (part : W → I)
    (hcol : ∀ i : I, (H.restrict (part ⁻¹' {i})).ColorableBy ℵ₀) :
    H.ColorableBy ℵ₀ := by
  choose f hf using hcol;
  refine' colorableBy_aleph0_of_countable H _ _;
  exact I × Quotient.out ℵ₀;
  apply countable_prod_out;
  exact fun w => ( part w, f ( part w ) w );
  intro e he; by_cases h : ∃ i, e ⊆ part ⁻¹' { i } <;> simp_all +decide [ Set.subset_def ] ;
  · obtain ⟨ i, hi ⟩ := h;
    have := hf i;
    obtain ⟨ u, hu, v, hv, huv ⟩ := this e ⟨ he, fun x hx => by aesop ⟩ ; use u, hu, v, hv; aesop;
  · obtain ⟨ u, hu, hu' ⟩ := h ( part ( Classical.choose ( Set.nonempty_iff_ne_empty.mpr ( show e ≠ ∅ from by rintro rfl; simpa using h ( Classical.arbitrary I ) ) ) ) ) ; obtain ⟨ v, hv, hv' ⟩ := h ( part u ) ; use u, hu, v, hv; aesop;

theorem exists_low_degree_vertex {B : Type u} (D : SimpleGraph B) (d : ℕ)
    (out : B → Finset B) (hout : ∀ v, (out v).card ≤ d)
    (hcov : ∀ v w, D.Adj v w → w ∈ out v ∨ v ∈ out w) [DecidableRel D.Adj]
    (s : Finset B) (hs : s.Nonempty) :
    ∃ v₀ ∈ s, (s.filter (fun w => D.Adj v₀ w)).card ≤ 2 * d := by
  classical
  by_contra h_contra
  push_neg at h_contra
  have h_sum_ge : (2 * d + 1) * s.card ≤ ∑ v ∈ s, (s.filter (fun w => D.Adj v w)).card := by
    calc (2 * d + 1) * s.card = ∑ _v ∈ s, (2 * d + 1) := by
            rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ v ∈ s, (s.filter (fun w => D.Adj v w)).card :=
            Finset.sum_le_sum (fun v hv => h_contra v hv)
  have h_eq : ∑ v ∈ s, (s.filter (fun w => D.Adj v w)).card
      = ((s ×ˢ s).filter (fun p => D.Adj p.1 p.2)).card := by
    rw [Finset.card_filter, Finset.sum_product]
    exact Finset.sum_congr rfl (fun a _ => (Finset.card_filter _ _))
  have h_sub : (s ×ˢ s).filter (fun p => D.Adj p.1 p.2) ⊆
      ((s ×ˢ s).filter (fun p => p.2 ∈ out p.1)) ∪
      ((s ×ˢ s).filter (fun p => p.1 ∈ out p.2)) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rcases hcov p.1 p.2 hp.2 with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp.1, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp.1, h⟩)
  have hc1 : ((s ×ˢ s).filter (fun p => p.2 ∈ out p.1)).card ≤ d * s.card := by
    rw [Finset.card_filter, Finset.sum_product]
    calc ∑ a ∈ s, ∑ b ∈ s, (if b ∈ out a then 1 else 0)
        = ∑ a ∈ s, (s.filter (fun b => b ∈ out a)).card :=
          Finset.sum_congr rfl (fun a _ => (Finset.card_filter _ _).symm)
      _ ≤ ∑ a ∈ s, (out a).card :=
          Finset.sum_le_sum (fun a _ => Finset.card_le_card
            (fun b hb => (Finset.mem_filter.mp hb).2))
      _ ≤ ∑ _a ∈ s, d := Finset.sum_le_sum (fun a _ => hout a)
      _ = d * s.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hc2 : ((s ×ˢ s).filter (fun p => p.1 ∈ out p.2)).card ≤ d * s.card := by
    rw [Finset.card_filter, Finset.sum_product_right]
    calc ∑ b ∈ s, ∑ a ∈ s, (if a ∈ out b then 1 else 0)
        = ∑ b ∈ s, (s.filter (fun a => a ∈ out b)).card :=
          Finset.sum_congr rfl (fun b _ => (Finset.card_filter _ _).symm)
      _ ≤ ∑ b ∈ s, (out b).card :=
          Finset.sum_le_sum (fun b _ => Finset.card_le_card
            (fun a ha => (Finset.mem_filter.mp ha).2))
      _ ≤ ∑ _b ∈ s, d := Finset.sum_le_sum (fun b _ => hout b)
      _ = d * s.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have h_sum_le : ∑ v ∈ s, (s.filter (fun w => D.Adj v w)).card ≤ 2 * d * s.card := by
    rw [h_eq]
    calc ((s ×ˢ s).filter (fun p => D.Adj p.1 p.2)).card
        ≤ (((s ×ˢ s).filter (fun p => p.2 ∈ out p.1)) ∪
            ((s ×ˢ s).filter (fun p => p.1 ∈ out p.2))).card := Finset.card_le_card h_sub
      _ ≤ ((s ×ˢ s).filter (fun p => p.2 ∈ out p.1)).card +
            ((s ×ˢ s).filter (fun p => p.1 ∈ out p.2)).card := Finset.card_union_le _ _
      _ ≤ d * s.card + d * s.card := Nat.add_le_add hc1 hc2
      _ = 2 * d * s.card := by ring
  have hpos : 0 < s.card := Finset.card_pos.mpr hs
  nlinarith [h_sum_ge, h_sum_le, hpos]

theorem finite_degenerate_coloring {B : Type u} (D : SimpleGraph B) (d : ℕ)
    (out : B → Finset B) (hout : ∀ v, (out v).card ≤ d)
    (hcov : ∀ v w, D.Adj v w → w ∈ out v ∨ v ∈ out w) [DecidableRel D.Adj]
    (s : Finset B) :
    ∃ c : B → Fin (2 * d + 1), ∀ a ∈ s, ∀ b ∈ s, D.Adj a b → c a ≠ c b := by
  classical
  suffices H : ∀ n (s : Finset B), s.card = n →
      ∃ c : B → Fin (2 * d + 1), ∀ a ∈ s, ∀ b ∈ s, D.Adj a b → c a ≠ c b by
    exact H s.card s rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs
    rcases s.eq_empty_or_nonempty with rfl | hne
    · exact ⟨fun _ => 0, by simp⟩
    · obtain ⟨v₀, hv₀, hdeg⟩ := exists_low_degree_vertex D d out hout hcov s hne
      have hcard' : (s.erase v₀).card < n := by
        rw [← hs]; exact Finset.card_erase_lt_of_mem hv₀
      obtain ⟨c', hc'⟩ := ih (s.erase v₀).card hcard' (s.erase v₀) rfl
      set Bad := (s.filter (fun w => D.Adj v₀ w)).image c' with hBad
      have hBadcard : Bad.card ≤ 2 * d := le_trans (Finset.card_image_le) hdeg
      obtain ⟨col, hcolBad⟩ : ∃ col : Fin (2 * d + 1), col ∉ Bad := by
        by_contra hcon
        push_neg at hcon
        have hsub : (Finset.univ : Finset (Fin (2 * d + 1))) ⊆ Bad := fun x _ => hcon x
        have := Finset.card_le_card hsub
        rw [Finset.card_univ, Fintype.card_fin] at this
        omega
      refine ⟨Function.update c' v₀ col, ?_⟩
      intro a ha b hb hab
      have hane : a ≠ b := hab.ne
      by_cases haeq : a = v₀
      · subst haeq
        have hbne : b ≠ a := fun h => hane h.symm
        have hc'bBad : c' b ∈ Bad :=
          Finset.mem_image_of_mem c' (Finset.mem_filter.mpr ⟨hb, hab⟩)
        rw [Function.update_self, Function.update_of_ne hbne]
        exact fun h => hcolBad (h ▸ hc'bBad)
      · by_cases hbeq : b = v₀
        · subst hbeq
          have hc'aBad : c' a ∈ Bad :=
            Finset.mem_image_of_mem c' (Finset.mem_filter.mpr ⟨ha, hab.symm⟩)
          rw [Function.update_of_ne haeq, Function.update_self]
          exact fun h => hcolBad (h ▸ hc'aBad)
        · rw [Function.update_of_ne haeq, Function.update_of_ne hbeq]
          exact hc' a (Finset.mem_erase.mpr ⟨haeq, ha⟩) b (Finset.mem_erase.mpr ⟨hbeq, hb⟩) hab

theorem colorable_of_out {B : Type u} (D : SimpleGraph B) (d : ℕ)
    (out : B → Finset B) (hout : ∀ v, (out v).card ≤ d)
    (hcov : ∀ v w, D.Adj v w → w ∈ out v ∨ v ∈ out w) [DecidableRel D.Adj] :
    ∃ c : B → Fin (2 * d + 1), ∀ a b, D.Adj a b → c a ≠ c b := by
  have : NeZero (2 * d + 1) := ⟨by omega⟩
  exact colorable_of_forall_finite D (2 * d + 1)
    (finite_degenerate_coloring D d out hout hcov)

theorem restrict_uc {W : Type u} {H : Hypergraph W} (htri : H.IsTripleSystem)
    (huc : H.UncountablyChromatic) {S : Set W} (hS : S.Finite) :
    (⟨{e | e ∈ H.edges ∧ e ⊆ Sᶜ}⟩ : Hypergraph W).UncountablyChromatic := by
  rintro ⟨c, hc⟩
  apply huc
  have hSfin : Finite ↥S := hS
  have hle : (#((ℵ₀ : Cardinal.{u}).out ⊕ ↥S)) ≤ (#((ℵ₀ : Cardinal.{u}).out)) := by
    rw [Cardinal.mk_sum, Cardinal.mk_out]
    have h2 : Cardinal.lift.{u,u} (#(↥S)) ≤ ℵ₀ := by
      rw [Cardinal.lift_le_aleph0]; exact le_of_lt (Cardinal.lt_aleph0_of_finite _)
    calc Cardinal.lift.{u,u} ℵ₀ + Cardinal.lift.{u,u} (#(↥S))
        ≤ ℵ₀ + ℵ₀ := add_le_add (by simp) h2
      _ = ℵ₀ := by simp
  obtain ⟨j, hj⟩ := (Cardinal.le_def _ _).mp hle
  classical
  refine ⟨fun w => if h : w ∈ S then j (Sum.inr ⟨w, h⟩) else j (Sum.inl (c w)), ?_⟩
  intro e he
  by_cases heS : e ⊆ Sᶜ
  · obtain ⟨u, hu, v, hv, huv⟩ := hc e ⟨he, heS⟩
    have hus : u ∉ S := fun h => (heS hu) h
    have hvs : v ∉ S := fun h => (heS hv) h
    refine ⟨u, hu, v, hv, ?_⟩
    simp only [dif_neg hus, dif_neg hvs]
    exact fun h => huv (by have := hj h; simpa using this)
  · rw [Set.not_subset] at heS
    obtain ⟨w, hwe, hwS⟩ := heS
    have hwS' : w ∈ S := by simpa [Set.mem_compl_iff, not_not] using hwS
    obtain ⟨a, b, d, hab, had, hbd, rfl⟩ := Set.ncard_eq_three.mp (htri e he)
    have : ∃ v ∈ ({a, b, d} : Set W), v ≠ w := by
      rcases hwe with rfl | rfl | rfl
      · exact ⟨b, by simp, hab.symm⟩
      · exact ⟨a, by simp, hab⟩
      · exact ⟨a, by simp, had⟩
    obtain ⟨v, hv, hvw⟩ := this
    refine ⟨w, hwe, v, hv, ?_⟩
    simp only [dif_pos hwS']
    by_cases hvS : v ∈ S
    · simp only [dif_pos hvS]
      exact fun h => hvw (by have := hj h; simp at this; exact this.symm)
    · simp only [dif_neg hvS]
      exact fun h => by have := hj h; simp at this

end Erdos593
end

-- AmalgClosure
section
open Cardinal SimpleGraph

namespace Erdos593

universe u

theorem amalgamate_embeds_of_copies {W : Type u} {H : Hypergraph W} {F G : FTS}
    (x : F.V) (y : G.V)
    (f : F.V → W) (hf : Function.Injective f) (hfe : ∀ e ∈ F.edges, f '' (↑e : Set F.V) ∈ H.edges)
    (g : G.V → W) (hg : Function.Injective g) (hge : ∀ e ∈ G.edges, g '' (↑e : Set G.V) ∈ H.edges)
    (hglue : f x = g y)
    (hmeet : ∀ a b, f a = g b → a = x ∧ b = y) :
    (F.amalgamate G x y).Embeds H := by
  refine ⟨fun v => Sum.elim f (fun b => g b.1) v, ?_, ?_⟩
  · intro a b hab
    cases a <;> cases b <;> simp_all +decide [ hf.eq_iff, hg.eq_iff ]; all_goals grind
  · intro e he
    rw [FTS.mem_amalgamate_edges] at he
    rcases he with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
    · erw [Finset.coe_map, Set.image_image]
      exact hfe a ha
    · erw [Finset.coe_map, Set.image_image]
      convert hge a ha using 2
      rename_i b _
      by_cases hb : b = y
      · subst hb
        show Sum.elim f (fun c : {c : G.V // c ≠ b} => g c.1) (if h : b = b then Sum.inl x else Sum.inr ⟨b, h⟩) = g b
        rw [dif_pos rfl]; exact hglue
      · show Sum.elim f (fun c : {c : G.V // c ≠ y} => g c.1) (if h : b = y then Sum.inl x else Sum.inr ⟨b, h⟩) = g b
        rw [dif_neg hb]; rfl

theorem reroute_isolated {W : Type u} [Infinite W] {G : FTS} (g : G.V → W)
    (hg : Function.Injective g) (Avoid : Set W) (hAvoid : Avoid.Finite) :
    ∃ g' : G.V → W, Function.Injective g' ∧
      (∀ b, ¬ G.Isolated b → g' b = g b) ∧
      (∀ b, G.Isolated b → g' b ∉ Avoid ∧ g' b ∉ g '' {b' : G.V | ¬ G.Isolated b'}) := by
  classical
  set Bad : Set W := Avoid ∪ g '' {b' : G.V | ¬ G.Isolated b'} with hBad_def
  have hBad : Bad.Finite := Set.Finite.union hAvoid (Set.Finite.image _ (Set.toFinite _))
  have hcompl : Set.Infinite (Set.univ \ Bad) := Set.infinite_univ.diff hBad
  obtain ⟨iso, hiso_inj, hiso_mem⟩ :
      ∃ iso : {b : G.V // G.Isolated b} → W, Function.Injective iso ∧ ∀ t, iso t ∉ Bad := by
    obtain ⟨t, ht₁, ht₂⟩ := hcompl.exists_subset_card_eq (Nat.card {b : G.V // G.Isolated b})
    have hfin : Fintype {b : G.V // G.Isolated b} := Set.Finite.fintype (Set.toFinite _)
    have e : {b : G.V // G.Isolated b} ≃ (t : Type _) :=
      Fintype.equivOfCardEq (by rw [Fintype.card_coe, ht₂, Nat.card_eq_fintype_card])
    refine ⟨fun s => (e s : W), ?_, ?_⟩
    · exact Subtype.val_injective.comp e.injective
    · intro s; exact (ht₁ (Finset.mem_coe.mpr (e s).2)).2
  refine ⟨fun b => if h : G.Isolated b then iso ⟨b, h⟩ else g b, ?_, ?_, ?_⟩
  · intro a b hab
    by_cases ha : G.Isolated a <;> by_cases hb : G.Isolated b
    · simp only [dif_pos ha, dif_pos hb] at hab
      exact congrArg Subtype.val (hiso_inj hab)
    · simp only [dif_pos ha, dif_neg hb] at hab
      exact absurd (Set.mem_union_right _ (Set.mem_image_of_mem g hb)) (hab ▸ hiso_mem ⟨a, ha⟩)
    · simp only [dif_neg ha, dif_pos hb] at hab
      exact absurd (Set.mem_union_right _ (Set.mem_image_of_mem g ha)) (hab.symm ▸ hiso_mem ⟨b, hb⟩)
    · simp only [dif_neg ha, dif_neg hb] at hab
      exact hg hab
  · intro b hb; simp only [dif_neg hb]
  · intro b hb
    simp only [dif_pos hb]
    exact ⟨fun hA => hiso_mem ⟨b, hb⟩ (Set.mem_union_left _ hA),
      fun hI => hiso_mem ⟨b, hb⟩ (Set.mem_union_right _ hI)⟩

def RootSetF {W : Type u} (H : Hypergraph W) (F : FTS) (x : F.V) : Set W :=
  {v | ∃ f : F.V → W, Function.Injective f ∧
    (∀ e ∈ F.edges, f '' (↑e : Set F.V) ∈ H.edges) ∧ f x = v}

theorem rootSetF_compl_Ffree {W : Type u} (H : Hypergraph W) {F : FTS} (x : F.V)
    (hx : ¬ F.Isolated x) : ¬ F.Embeds (H.restrict (RootSetF H F x)ᶜ) := by
  rintro ⟨g, hg_inj, hg_e⟩
  obtain ⟨e0, he0, hxe0⟩ : ∃ e ∈ F.edges, x ∈ e := by
    by_contra hc; push_neg at hc; exact hx hc
  have hmem := hg_e e0 he0
  have hsub : g '' (↑e0 : Set F.V) ⊆ (RootSetF H F x)ᶜ := hmem.2
  have hgx : g x ∈ g '' (↑e0 : Set F.V) := ⟨x, Finset.mem_coe.mpr hxe0, rfl⟩
  have hgxB : g x ∈ RootSetF H F x := ⟨g, hg_inj, fun e he => (hg_e e he).1, rfl⟩
  exact (hsub hgx) hgxB

theorem class_Gfree {W : Type u} [Infinite W] {H : Hypergraph W}
    {F G : FTS} {x : F.V} {y : G.V} (hy : ¬ G.Isolated y)
    (hcon : ¬ (F.amalgamate G x y).Embeds H)
    (K : W → F.V → W)
    (hKinj : ∀ v ∈ RootSetF H F x, Function.Injective (K v))
    (hKe : ∀ v ∈ RootSetF H F x, ∀ e ∈ F.edges, (K v) '' (↑e : Set F.V) ∈ H.edges)
    (hKx : ∀ v ∈ RootSetF H F x, K v x = v)
    (C : Set W) (hCB : C ⊆ RootSetF H F x)
    (hdisj : ∀ v ∈ C, ∀ a : F.V, a ≠ x → K v a ∉ C) :
    ¬ G.Embeds (H.restrict C) := by
  contrapose! hcon;
  obtain ⟨g, hg_inj, hg_e⟩ := hcon;
  obtain ⟨v, hvC⟩ : ∃ v ∈ C, g y = v := by
    simp_all +decide [ Hypergraph.restrict ];
    simp_all +decide [ FTS.Isolated ];
    exact hg_e _ hy.choose_spec.1 |>.2 hy.choose_spec.2;
  obtain ⟨g', hg'inj, hg'0, hg'1⟩ : ∃ g' : G.V → W, Function.Injective g' ∧ (∀ b, ¬ G.Isolated b → g' b = g b) ∧ (∀ b, G.Isolated b → g' b ∉ Set.range (K v) ∧ g' b ∉ g '' {b' : G.V | ¬ G.Isolated b'}) := by
    apply reroute_isolated g hg_inj (Set.range (K v)) (Set.finite_range _);
  apply amalgamate_embeds_of_copies x y (K v) (hKinj v (hCB hvC.left)) (hKe v (hCB hvC.left)) g' hg'inj (by
  intro e he
  have h_image : g' '' (↑e : Set G.V) = g '' (↑e : Set G.V) := by
    ext w; simp;
    constructor <;> rintro ⟨ x, hx, rfl ⟩ <;> use x <;> simp_all +decide [ FTS.Isolated ];
    · rw [ hg'0 x e he hx ];
    · exact hg'0 x e he hx
  rw [h_image]
  exact (hg_e e he).1) (by
  rw [ hKx v ( hCB hvC.1 ), hg'0 y hy, hvC.2 ]) (by
  intro a b hab;
  by_cases hb : G.Isolated b <;> simp_all +decide;
  have h_contra : g b ∈ C := by
    obtain ⟨ e, he ⟩ := not_forall.mp hb;
    simp +zetaDelta at *;
    exact hg_e e he.1 |>.2 ( Set.mem_image_of_mem _ he.2 );
  grind)

theorem amalgamate_obligatory_of_nonisolated {F G : FTS} (x : F.V) (y : G.V)
    (hx : ¬ F.Isolated x) (hy : ¬ G.Isolated y)
    (hF : FTS.Obligatory.{u} F) (hG : FTS.Obligatory.{u} G) :
    FTS.Obligatory.{u} (F.amalgamate G x y) := by
  intro W H htri huc
  by_contra hcon
  haveI : Infinite W := huc.infinite htri
  classical
  refine huc ?_

  have hKex : ∀ v : ↑(RootSetF H F x), ∃ f : F.V → W, Function.Injective f ∧
      (∀ e ∈ F.edges, f '' (↑e : Set F.V) ∈ H.edges) ∧ f x = v.1 := fun v => v.2
  choose K0 hK0inj hK0e hK0x using hKex
  set K : W → F.V → W := fun w => if h : w ∈ RootSetF H F x then K0 ⟨w, h⟩ else (fun _ => w)
    with hKdef
  have hKinj : ∀ v ∈ RootSetF H F x, Function.Injective (K v) := by
    intro v hv; simp only [hKdef, dif_pos hv]; exact hK0inj ⟨v, hv⟩
  have hKe : ∀ v ∈ RootSetF H F x, ∀ e ∈ F.edges, (K v) '' (↑e : Set F.V) ∈ H.edges := by
    intro v hv e he; simp only [hKdef, dif_pos hv]; exact hK0e ⟨v, hv⟩ e he
  have hKx : ∀ v ∈ RootSetF H F x, K v x = v := by
    intro v hv; simp only [hKdef, dif_pos hv]; exact hK0x ⟨v, hv⟩

  set d : ℕ := Fintype.card F.V - 1 with hddef
  set out : W → Finset W := fun v =>
    if v ∈ RootSetF H F x then (Finset.univ.image (K v)).erase v else ∅ with houtdef
  have hout : ∀ v, (out v).card ≤ d := by
    intro v; simp only [houtdef]
    by_cases hv : v ∈ RootSetF H F x
    · rw [if_pos hv]
      have hvmem : v ∈ Finset.univ.image (K v) :=
        Finset.mem_image.mpr ⟨x, Finset.mem_univ x, hKx v hv⟩
      have hcard : (Finset.univ.image (K v)).card = Fintype.card F.V := by
        rw [Finset.card_image_of_injective _ (hKinj v hv), Finset.card_univ]
      rw [Finset.card_erase_of_mem hvmem, hcard]
    · rw [if_neg hv]; simp
  set D : SimpleGraph W := SimpleGraph.fromRel (fun v w => w ∈ out v) with hDdef
  have hcov : ∀ v w, D.Adj v w → w ∈ out v ∨ v ∈ out w := by
    intro v w h; rw [hDdef, SimpleGraph.fromRel_adj] at h; exact h.2
  haveI : DecidableRel D.Adj := fun _ _ => Classical.dec _
  obtain ⟨χ, hχ⟩ := colorable_of_out D d out hout hcov

  set part : W → Option (Fin (2 * d + 1)) :=
    fun w => if h : w ∈ RootSetF H F x then some (χ w) else none with hpartdef
  apply colorableBy_of_finite_parts H part
  intro i
  cases i with
  | none =>
    have hset : part ⁻¹' {none} = (RootSetF H F x)ᶜ := by
      ext w
      simp only [hpartdef, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff]
      by_cases h : w ∈ RootSetF H F x <;> simp [h]
    rw [hset]
    exact restrict_colorable_of_obligatory htri hF (rootSetF_compl_Ffree H x hx)
  | some c =>
    have hmemCc : ∀ w, w ∈ part ⁻¹' {some c} ↔ ∃ h : w ∈ RootSetF H F x, χ w = c := by
      intro w
      simp only [hpartdef, Set.mem_preimage, Set.mem_singleton_iff]
      by_cases hb : w ∈ RootSetF H F x
      · simp only [dif_pos hb, Option.some.injEq]; exact ⟨fun h => ⟨hb, h⟩, fun h => h.2⟩
      · simp only [dif_neg hb]; exact ⟨fun h => absurd h (by simp), fun h => h.elim (fun hh => absurd hh hb)⟩
    have hCcB : part ⁻¹' {some c} ⊆ RootSetF H F x := fun w hw => ((hmemCc w).mp hw).choose
    have hdisj : ∀ v ∈ part ⁻¹' {some c}, ∀ a : F.V, a ≠ x → K v a ∉ part ⁻¹' {some c} := by
      intro v hv a ha hKva
      obtain ⟨hvB, hvc⟩ := (hmemCc v).mp hv
      obtain ⟨hwB, hwc⟩ := (hmemCc _).mp hKva
      have hne : K v a ≠ v := fun h => ha (hKinj v hvB (by rw [h, hKx v hvB]))
      have hadj : D.Adj v (K v a) := by
        rw [hDdef, SimpleGraph.fromRel_adj]
        refine ⟨Ne.symm hne, Or.inl ?_⟩
        simp only [houtdef, if_pos hvB, Finset.mem_erase]
        exact ⟨hne, Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩⟩
      have hcol := hχ v (K v a) hadj
      rw [hvc, hwc] at hcol
      exact hcol rfl
    exact restrict_colorable_of_obligatory htri hG
      (class_Gfree hy hcon K hKinj hKe hKx (part ⁻¹' {some c}) hCcB hdisj)

theorem amalgamate_symm_iso {F G : FTS} (x : F.V) (y : G.V) :
    FTS.Iso (F.amalgamate G x y) (G.amalgamate F y x) := by
  classical
  let φ : (F.V ⊕ {b : G.V // b ≠ y}) ≃ (G.V ⊕ {a : F.V // a ≠ x}) :=
    { toFun := fun v => match v with
      | Sum.inl a => if h : a = x then Sum.inl y else Sum.inr ⟨a, h⟩
      | Sum.inr ⟨b, _⟩ => Sum.inl b,
      invFun := fun v => match v with
      | Sum.inl b => if h : b = y then Sum.inl x else Sum.inr ⟨b, h⟩
      | Sum.inr ⟨a, _⟩ => Sum.inl a,
      left_inv := by
        rintro (a | ⟨b, hb⟩)
        · by_cases h : a = x
          · subst h; simp
          · simp [h]
        · simp [hb],
      right_inv := by
        rintro (b | ⟨a, ha⟩)
        · by_cases h : b = y
          · subst h; simp
          · simp [h]
        · simp [ha] }
  refine ⟨φ, fun e => (FTS.mem_amalgamate_edges F G x y e).trans
    (Iff.trans ?_ (FTS.mem_amalgamate_edges G F y x (e.map φ.toEmbedding)).symm)⟩
  have hinj := Finset.map_injective φ.toEmbedding
  have hF : ∀ a : Finset F.V,
      Finset.map ⟨fun b => if h : b = x then Sum.inl y else Sum.inr ⟨b, h⟩, by
        intro a b hab
        by_cases ha : a = x <;> by_cases hb : b = x <;> simp_all⟩ a =
      (a.map Function.Embedding.inl).map φ.toEmbedding := by
    intro a
    rw [Finset.map_map]
    rfl
  have hG : ∀ c : Finset G.V, c.map Function.Embedding.inl =
      (Finset.map ⟨fun b => if h : b = y then Sum.inl x else Sum.inr ⟨b, h⟩, by
        intro a b hab
        by_cases ha : a = y <;> by_cases hb : b = y <;> simp_all⟩ c).map φ.toEmbedding := by
    intro c
    rw [Finset.map_map]
    congr 1
    ext b
    by_cases hb : b = y
    · subst hb
      show Sum.inl b = φ (if h : b = b then Sum.inl x else Sum.inr ⟨b, h⟩)
      rw [dif_pos rfl]
      show Sum.inl b =
        (if h : x = x then (Sum.inl b : G.V ⊕ {a : F.V // a ≠ x}) else Sum.inr ⟨x, h⟩)
      rw [dif_pos rfl]
    · show Sum.inl b = φ (if h : b = y then Sum.inl x else Sum.inr ⟨b, h⟩)
      rw [dif_neg hb]
      rfl
  constructor
  · rintro (⟨a, ha, rfl⟩ | ⟨c, hc, rfl⟩)
    · exact Or.inr ⟨a, ha, hF a⟩
    · exact Or.inl ⟨c, hc, hG c⟩
  · rintro (⟨c, hc, he⟩ | ⟨a, ha, he⟩)
    · exact Or.inr ⟨c, hc, hinj ((hG c).symm.trans he)⟩
    · exact Or.inl ⟨a, ha, hinj ((hF a).symm.trans he)⟩

theorem amalgamate_obligatory_of_isolated {F G : FTS} (x : F.V) (y : G.V)
    (hx : F.Isolated x) (hF : FTS.Obligatory.{u} F) (hG : FTS.Obligatory.{u} G) :
    FTS.Obligatory.{u} (F.amalgamate G x y) := by
  intro W H htri huc;
  obtain ⟨g, hg_inj, hg_e⟩ := hG H htri huc;
  haveI : Infinite W := huc.infinite htri
  set v := g y
  set S := Set.range g
  have hS : S.Finite := Set.finite_range g;

  set H1 : Hypergraph W := ⟨{e | e ∈ H.edges ∧ e ⊆ Sᶜ}⟩
  have hH1_uc : H1.UncountablyChromatic := by
    convert restrict_uc htri huc hS using 1
  have hH1_tri : H1.IsTripleSystem := by
    exact fun e he => htri e he.1;

  obtain ⟨f0, hf0_inj, hf0_e⟩ := hF H1 hH1_tri hH1_uc;

  obtain ⟨f1, hf1_inj, hf1_0, hf1_1⟩ := reroute_isolated f0 hf0_inj S hS;
  have hf1_avoid : ∀ a, f1 a ∉ S := by
    intro a; by_cases ha : F.Isolated a <;> simp_all +decide ;
    obtain ⟨ e, he ⟩ := not_forall.mp ha;
    exact fun h => by have := hf0_e e ( by tauto ) |>.2 ( Set.mem_image_of_mem _ ( by tauto : a ∈ e ) ) ; aesop;;
  have hf1_e : ∀ e ∈ F.edges, f1 '' (↑e : Set F.V) ∈ H.edges := by
    intro e he
    have h_image : f1 '' (↑e : Set F.V) = f0 '' (↑e : Set F.V) := by
      ext w;
      constructor <;> rintro ⟨ a, ha, rfl ⟩;
      · by_cases ha' : F.Isolated a <;> simp_all +decide;
        · exact False.elim ( ha' e he ha );
        · exact ⟨ a, ha, rfl ⟩;
      · by_cases ha' : F.Isolated a <;> simp_all +decide [ Set.image ];
        · exact False.elim ( ha' e he ha );
        · exact ⟨ a, ha, hf1_0 a ha' ⟩;
    exact h_image.symm ▸ hf0_e e he |>.1;
  apply amalgamate_embeds_of_copies x y (Function.update f1 x v) (by
  intro a b hab;
  grind) (by
  intro e he
  have h_image : (Function.update f1 x v) '' (↑e : Set F.V) = f1 '' (↑e : Set F.V) := by
    have h_image : ∀ a ∈ e, a ≠ x := by
      exact fun a ha => by rintro rfl; exact hx e he ha;
    exact Set.image_congr fun a ha => by rw [ Function.update_of_ne ( h_image a ha ) ] ;
  rw [h_image]
  exact hf1_e e he) g hg_inj hg_e (by
  grind +splitImp) (by
  grind +qlia)

theorem amalgamate_obligatory {F G : FTS} (x : F.V) (y : G.V)
    (hF : FTS.Obligatory.{u} F) (hG : FTS.Obligatory.{u} G) :
    FTS.Obligatory.{u} (F.amalgamate G x y) := by
  by_cases hx : F.Isolated x
  · exact amalgamate_obligatory_of_isolated x y hx hF hG
  · by_cases hy : G.Isolated y
    · exact obligatory_iso (amalgamate_symm_iso y x)
        (amalgamate_obligatory_of_isolated y x hy hG hF)
    · exact amalgamate_obligatory_of_nonisolated x y hx hy hF hG

end Erdos593
end

-- DecompForward
section
open Cardinal

namespace Erdos593

open Classical

universe u

theorem zmod_const_of_succ_eq {m : ℕ} [NeZero m] {α : Type*} (s : ZMod m → α)
    (h : ∀ i, s i = s (i + 1)) (i : ZMod m) : s i = s 0 := by
  have h_ind : ∀ k : ℕ, s (k : ZMod m) = s 0 := by
    intro k; induction' k with k ih <;> norm_num at *;
    rw [ ← h, ih ];
  simpa using h_ind i.val

theorem zmod_succ_eq_of_unique_change {m : ℕ} [NeZero m] (s : ZMod m → Bool)
    (h : ∀ i j, s i ≠ s (i + 1) → s j ≠ s (j + 1) → i = j) (i : ZMod m) :
    s i = s (i + 1) := by
  by_contra h_contra;

  set T := Finset.univ.filter (fun i => s i ≠ s (i + 1)) with hT_def
  have hT_card : T.card ≤ 1 := by
    exact Finset.card_le_one.mpr fun x hx y hy => h x y ( Finset.mem_filter.mp hx |>.2 ) ( Finset.mem_filter.mp hy |>.2 );
  have hT_even : Even T.card := by
    have hT_even : ∑ i : ZMod m, (if s i then 1 else 0 : ZMod 2) + ∑ i : ZMod m, (if s (i + 1) then 1 else 0 : ZMod 2) = 0 := by
      erw [ Equiv.sum_comp ( Equiv.addRight 1 ) fun i => if s i = true then 1 else 0 ] ; ring;
      grind;
    have hT_even : ∑ i : ZMod m, (if s i ≠ s (i + 1) then 1 else 0 : ZMod 2) = ∑ i : ZMod m, (if s i then 1 else 0 : ZMod 2) + ∑ i : ZMod m, (if s (i + 1) then 1 else 0 : ZMod 2) := by
      rw [ ← Finset.sum_add_distrib ] ; congr ; ext i ; by_cases hi : s i <;> by_cases hi' : s ( i + 1 ) <;> simp +decide [ hi, hi' ] ;
    simp_all +decide [ Finset.sum_ite ];
    rw [ ZMod.natCast_eq_zero_iff ] at hT_even ; exact even_iff_two_dvd.mpr hT_even;
  exact absurd hT_even ( by rw [ show T.card = 1 by exact le_antisymm hT_card ( Finset.card_pos.mpr ⟨ i, by aesop ⟩ ) ] ; decide )

theorem zmod_even_of_alt {m : ℕ} [NeZero m] (s : ZMod m → ZMod 2)
    (h : ∀ i, s (i + 1) = s i + 1) : Even m := by
  have h_m_even : ∀ k : ℕ, s k = s 0 + k := by
    intro k; induction k <;> simp_all +decide [ ← add_assoc ] ;
  specialize h_m_even m; simp_all +decide ;
  rw [ ZMod.natCast_eq_zero_iff ] at h_m_even ; exact even_iff_two_dvd.mpr h_m_even

theorem zmod_one_ne_zero_of_two_le {m : ℕ} (hm : 2 ≤ m) : (1 : ZMod m) ≠ 0 := by
  haveI : Fact (1 < m) := ⟨by omega⟩
  exact one_ne_zero

theorem zmod2_succ_of_ne : ∀ x y : ZMod 2, x ≠ y → y = x + 1 := by decide

theorem card_map_inter_le {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α ↪ β)
    (s t : Finset α) : (s.map f ∩ t.map f).card ≤ (s ∩ t).card := by
  rw [← Finset.map_inter, Finset.card_map]

theorem sym2_mk_eq_of_mem {α : Type*} {z : α × α} {p q : α} (hpq : p ≠ q)
    (hp : p = z.1 ∨ p = z.2) (hq : q = z.1 ∨ q = z.2) : s(z.1, z.2) = s(p, q) := by
  obtain ⟨z1, z2⟩ := z
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact absurd rfl hpq
  · rfl
  · exact Sym2.eq_swap
  · exact absurd rfl hpq

theorem expansion_inter_aux {α β : Type*} {x : α ⊕ β} {p₁ q₁ p₂ q₂ : α} {b₁ b₂ : β}
    (hb : b₁ ≠ b₂)
    (h₁ : x = Sum.inl p₁ ∨ x = Sum.inl q₁ ∨ x = Sum.inr b₁)
    (h₂ : x = Sum.inl p₂ ∨ x = Sum.inl q₂ ∨ x = Sum.inr b₂) :
    ∃ p, x = Sum.inl p ∧ (p = p₁ ∨ p = q₁) ∧ (p = p₂ ∨ p = q₂) := by
  rcases h₁ with rfl | rfl | rfl <;> rcases h₂ with h | h | h
  all_goals first
    | exact absurd h Sum.inl_ne_inr
    | exact absurd h Sum.inr_ne_inl
    | exact absurd (Sum.inr_injective h) hb
    | exact ⟨_, rfl, Or.inl rfl, Or.inl (Sum.inl_injective h)⟩
    | exact ⟨_, rfl, Or.inl rfl, Or.inr (Sum.inl_injective h)⟩
    | exact ⟨_, rfl, Or.inr rfl, Or.inl (Sum.inl_injective h)⟩
    | exact ⟨_, rfl, Or.inr rfl, Or.inr (Sum.inl_injective h)⟩

theorem FTS.not_isolated_of_mem {F : FTS} {x : F.V} {e : Finset F.V}
    (he : e ∈ F.edges) (hx : x ∈ e) : ¬ F.Isolated x := by
  exact fun h => h e he hx

theorem FTS.subtype_edge_mem {F : FTS} {e : Finset F.V} (he : e ∈ F.edges) :
    Finset.subtype (fun x => ¬ F.Isolated x) e ∈ F.reduce.edges := by
  exact Finset.mem_image.mpr ⟨ ⟨ e, he ⟩, Finset.mem_attach _ _, rfl ⟩

theorem FTS.subtype_map_eq {F : FTS} {e : Finset F.V} (he : e ∈ F.edges) :
    (Finset.subtype (fun x => ¬ F.Isolated x) e).map
      (Function.Embedding.subtype (fun x => ¬ F.Isolated x)) = e := by
  ext x; simp [Finset.mem_map, Finset.mem_subtype];
  exact fun hx => FTS.not_isolated_of_mem he hx

theorem FTS.reduce_edge_map_mem {F : FTS} {d : Finset F.reduce.V} (hd : d ∈ F.reduce.edges) :
    d.map (Function.Embedding.subtype (fun x => ¬ F.Isolated x)) ∈ F.edges := by
  obtain ⟨e, rfl⟩ := (FTS.mem_reduce_edges F d).1 hd
  convert e.2 using 1
  exact FTS.subtype_map_eq e.2

noncomputable def BergeCycle.ofReduce {F : FTS} (c : BergeCycle F.reduce) : BergeCycle F where
  m := c.m
  hm := c.hm
  v := fun i => Function.Embedding.subtype (fun x => ¬ F.Isolated x) (c.v i)
  e := fun i => ⟨(c.e i).1.map (Function.Embedding.subtype (fun x => ¬ F.Isolated x)),
    FTS.reduce_edge_map_mem (c.e i).2⟩
  vinj := fun i j h => c.vinj ((Function.Embedding.subtype _).injective h)
  einj := by
    intro i j h
    apply c.einj
    have h2 : (c.e i).1.map (Function.Embedding.subtype (fun x => ¬ F.Isolated x)) =
        (c.e j).1.map (Function.Embedding.subtype (fun x => ¬ F.Isolated x)) := by
      simpa using congrArg Subtype.val h
    exact Subtype.ext (Finset.map_injective _ h2)
  mem_left := fun i => Finset.mem_map_of_mem _ (c.mem_left i)
  mem_right := fun i => Finset.mem_map_of_mem _ (c.mem_right i)

noncomputable def BergeCycle.toReduce {F : FTS} (c : BergeCycle F) : BergeCycle F.reduce where
  m := c.m
  hm := c.hm
  v := fun i => ⟨c.v i, FTS.not_isolated_of_mem (c.e i).2 (c.mem_left i)⟩
  e := fun i => ⟨Finset.subtype (fun x => ¬ F.Isolated x) (c.e i).1,
    FTS.subtype_edge_mem (c.e i).2⟩
  vinj := fun i j h => c.vinj (by simpa using congrArg Subtype.val h)
  einj := by
    intro i j h
    apply c.einj
    apply Subtype.ext
    have h1 := FTS.subtype_map_eq (c.e i).2
    have h2 := FTS.subtype_map_eq (c.e j).2
    have hh : Finset.subtype (fun x => ¬ F.Isolated x) (c.e i).1
        = Finset.subtype (fun x => ¬ F.Isolated x) (c.e j).1 := congrArg Subtype.val h
    rw [← h1, ← h2, hh]
  mem_left := fun i => Finset.mem_subtype.2 (c.mem_left i)
  mem_right := fun i => Finset.mem_subtype.2 (c.mem_right i)

theorem FTS.intrinsic_reduce_iff (F : FTS) :
    F.IntrinsicObligatory ↔ F.reduce.IntrinsicObligatory := by
  constructor <;> intro h
  · obtain ⟨hlin, hbr, hev⟩ := h
    refine ⟨?_, ?_, ?_⟩
    · intro e₁ he₁ e₂ he₂ hne
      have h1 := hlin _ (FTS.reduce_edge_map_mem he₁) _ (FTS.reduce_edge_map_mem he₂)
        (fun h => hne (Finset.map_injective _ h))
      calc (e₁ ∩ e₂).card
          = ((e₁ ∩ e₂).map (Function.Embedding.subtype (fun x => ¬ F.Isolated x))).card :=
            (Finset.card_map _).symm
        _ ≤ (e₁.map (Function.Embedding.subtype (fun x => ¬ F.Isolated x)) ∩
              e₂.map (Function.Embedding.subtype (fun x => ¬ F.Isolated x))).card := by
            apply Finset.card_le_card
            intro z hz
            obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hz
            obtain ⟨ha1, ha2⟩ := Finset.mem_inter.1 ha
            exact Finset.mem_inter.2 ⟨Finset.mem_map_of_mem _ ha1, Finset.mem_map_of_mem _ ha2⟩
        _ ≤ 1 := h1
    · intro ed
      obtain ⟨w, hw, -, hw₂⟩ := hbr ⟨ed.1.map (Function.Embedding.subtype (fun x => ¬ F.Isolated x)),
        FTS.reduce_edge_map_mem ed.2⟩
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hw
      refine ⟨a, ha, ?_⟩
      unfold IsBridgeInc
      refine ⟨ha, ?_⟩
      rintro ⟨c, i, hci, hv⟩
      apply hw₂
      refine ⟨BergeCycle.ofReduce c, i, ?_, ?_⟩
      · subst hci; rfl
      · rcases hv with hv | hv
        · left; exact congrArg Subtype.val hv
        · right; exact congrArg Subtype.val hv
    · exact fun c => hev (BergeCycle.ofReduce c)
  · refine ⟨?_, ?_, ?_⟩
    · intro e₁ he₁ e₂ he₂ hne
      have hne' : Finset.subtype (fun x => ¬ F.Isolated x) e₁ ≠
          Finset.subtype (fun x => ¬ F.Isolated x) e₂ := by
        intro h
        apply hne
        rw [← FTS.subtype_map_eq he₁, ← FTS.subtype_map_eq he₂, h]
      have h1 := h.1 _ (FTS.subtype_edge_mem he₁) _ (FTS.subtype_edge_mem he₂) hne'
      refine le_trans ?_ h1
      calc (e₁ ∩ e₂).card
          ≤ ((Finset.subtype (fun x => ¬ F.Isolated x) e₁ ∩
              Finset.subtype (fun x => ¬ F.Isolated x) e₂).map
                (Function.Embedding.subtype (fun x => ¬ F.Isolated x))).card := by
            apply Finset.card_le_card
            intro z hz
            obtain ⟨hz1, hz2⟩ := Finset.mem_inter.1 hz
            have hz' : ¬ F.Isolated z := FTS.not_isolated_of_mem he₁ hz1
            exact Finset.mem_map.2 ⟨⟨z, hz'⟩,
              Finset.mem_inter.2 ⟨Finset.mem_subtype.2 hz1, Finset.mem_subtype.2 hz2⟩, rfl⟩
        _ = _ := Finset.card_map _
    · intro ed
      obtain ⟨⟨w, hwI⟩, hw, -, hw₂⟩ :=
        h.2.1 ⟨Finset.subtype (fun x => ¬ F.Isolated x) ed.1, FTS.subtype_edge_mem ed.2⟩
      have hw' : w ∈ ed.1 := Finset.mem_subtype.1 hw
      refine ⟨w, hw', ?_⟩
      unfold IsBridgeInc
      refine ⟨hw', ?_⟩
      rintro ⟨c, i, hci, hv⟩
      apply hw₂
      refine ⟨BergeCycle.toReduce c, i, ?_, ?_⟩
      · subst hci; rfl
      · rcases hv with hv | hv
        · left; exact Subtype.ext hv
        · right; exact Subtype.ext hv
    · exact fun c => h.2.2 (BergeCycle.toReduce c)

theorem intrinsic_iso {F G : FTS} (h : FTS.Iso F G) (hF : F.IntrinsicObligatory) :
    G.IntrinsicObligatory := by
  refine' ⟨ _, _, _ ⟩;
  · obtain ⟨ φ, hφ ⟩ := h;
    intro e₁ he₁ e₂ he₂ hne;
    have h_card : (Finset.map (Equiv.toEmbedding φ.symm) e₁ ∩ Finset.map (Equiv.toEmbedding φ.symm) e₂).card ≤ 1 := by
      have := hF.1 ( Finset.map φ.symm.toEmbedding e₁ ) ?_ ( Finset.map φ.symm.toEmbedding e₂ ) ?_ ?_ <;> simp_all +decide [ Finset.map_map ];
    convert h_card using 1;
    rw [ ← Finset.card_image_of_injective _ φ.symm.injective ] ; congr ; ext ; aesop;
  · intro ed;
    obtain ⟨ φ, hφ ⟩ := h;
    obtain ⟨ w', hw' ⟩ := hF.2.1 ⟨ Finset.map φ.symm.toEmbedding ed.val, by
      rw [ hφ ];
      convert ed.2 using 1;
      ext; simp +decide [ Finset.mem_map ] ; ⟩
    generalize_proofs at *;
    refine' ⟨ φ w', _, _ ⟩ <;> simp_all +decide [ IsBridgeInc ];
    contrapose! hw';
    intro hw''; obtain ⟨ c, i, hi, hi' ⟩ := hw'; use ⟨ c.m, c.hm, fun j => φ.symm ( c.v j ), fun j => ⟨ Finset.map φ.symm.toEmbedding ( c.e j |>.1 ), by
      convert hφ _ |>.2 _ using 1;
      simp +decide [ Finset.map_map, Equiv.symm_trans_self ] ⟩, by
      exact fun x y hxy => c.vinj <| by simpa using hxy;, by
      intro j k hjk; have := c.einj; aesop;, by
      exact fun i => Finset.mem_map.mpr ⟨ c.v i, c.mem_left i, by simp +decide ⟩, by
      simp +decide [ Finset.mem_map, c.mem_right ] ⟩ ; aesop;
  · intro c
    obtain ⟨φ, hφ⟩ := h
    have h_cycle : ∃ c' : BergeCycle F, c'.m = c.m := by
      refine' ⟨ ⟨ c.m, c.hm, fun i => φ.symm ( c.v i ), fun i => ⟨ Finset.map φ.symm.toEmbedding ( c.e i |>.1 ), _ ⟩, _, _, _, _ ⟩, rfl ⟩ <;> simp_all +decide [ Function.Injective ];
      · simp +decide [ Finset.map_map, Equiv.toEmbedding_apply ];
      · exact c.vinj;
      · exact c.einj;
      · exact fun i => c.mem_left i;
      · exact c.mem_right;
    exact h_cycle.choose_spec ▸ hF.2.2 _

theorem edgeless_intrinsic (F : FTS) (h : F.edges = ∅) : F.IntrinsicObligatory := by
  refine' ⟨ _, _, _ ⟩;
  · intro e₁ he₁ e₂ he₂; aesop;
  · grind;
  · intro c;
    exact absurd ( c.e 0 |>.2 ) ( by simp +decide [ h ] )

theorem expansion_edge_cases {VJ : Type} [Fintype VJ] [DecidableEq VJ] (J : SimpleGraph VJ)
    [DecidableRel J.Adj] {s : Finset ((graphExpansion J).V)}
    (hs : s ∈ (graphExpansion J).edges) :
    ∃ e : {x : Sym2 VJ // x ∈ J.edgeFinset},
      s = {Sum.inl (Quot.out e.1).1, Sum.inl (Quot.out e.1).2, Sum.inr e} := by
  obtain ⟨e, -, rfl⟩ := Finset.mem_image.1 hs
  exact ⟨e, rfl⟩

theorem expansion_mem_triple {VJ : Type} [Fintype VJ] [DecidableEq VJ] (J : SimpleGraph VJ)
    [DecidableRel J.Adj] (e : {x : Sym2 VJ // x ∈ J.edgeFinset}) (z : (graphExpansion J).V) :
    z ∈ ({Sum.inl (Quot.out e.1).1, Sum.inl (Quot.out e.1).2, Sum.inr e} :
      Finset (graphExpansion J).V) ↔
      z = Sum.inl (Quot.out e.1).1 ∨ z = Sum.inl (Quot.out e.1).2 ∨ z = Sum.inr e :=
  Finset.mem_insert.trans (or_congr Iff.rfl (Finset.mem_insert.trans
    (or_congr Iff.rfl Finset.mem_singleton)))

theorem expansion_core_mem {VJ : Type} [Fintype VJ] [DecidableEq VJ] (J : SimpleGraph VJ)
    [DecidableRel J.Adj] (e : {x : Sym2 VJ // x ∈ J.edgeFinset}) (a : VJ)
    (h : (Sum.inl a : (graphExpansion J).V) ∈
      ({Sum.inl (Quot.out e.1).1, Sum.inl (Quot.out e.1).2, Sum.inr e} :
        Finset (graphExpansion J).V)) :
    a = (Quot.out e.1).1 ∨ a = (Quot.out e.1).2 := by
  rcases (expansion_mem_triple J e _).1 h with h | h | h
  · exact Or.inl (Sum.inl_injective h)
  · exact Or.inr (Sum.inl_injective h)
  · exact absurd h Sum.inl_ne_inr

theorem expansion_endpoints_adj {VJ : Type} [Fintype VJ] [DecidableEq VJ] (J : SimpleGraph VJ)
    [DecidableRel J.Adj] (e : {x : Sym2 VJ // x ∈ J.edgeFinset}) :
    J.Adj (Quot.out e.1).1 (Quot.out e.1).2 := by
  have hmem : e.val ∈ J.edgeSet := SimpleGraph.mem_edgeFinset.mp e.2
  rw [ ← Quot.out_eq e.val ] at hmem; exact hmem;

theorem expansion_private {VJ : Type} [Fintype VJ] [DecidableEq VJ] (J : SimpleGraph VJ)
    [DecidableRel J.Adj] {s : Finset ((graphExpansion J).V)}
    (hs : s ∈ (graphExpansion J).edges) {e : {x : Sym2 VJ // x ∈ J.edgeFinset}}
    (hmem : Sum.inr e ∈ s) :
    s = {Sum.inl (Quot.out e.1).1, Sum.inl (Quot.out e.1).2, Sum.inr e} := by
  obtain ⟨e', rfl⟩ := expansion_edge_cases J hs
  rcases (expansion_mem_triple J e' _).1 hmem with h | h | h
  · exact absurd h Sum.inr_ne_inl
  · exact absurd h Sum.inr_ne_inl
  · obtain rfl := Sum.inr_injective h
    rfl

theorem expansion_linear {VJ : Type} [Fintype VJ] [DecidableEq VJ] (J : SimpleGraph VJ)
    [DecidableRel J.Adj] : (graphExpansion J).Linear := by
  intro e₁ he₁ e₂ he₂ hne
  obtain ⟨a₁, rfl⟩ := expansion_edge_cases J he₁
  obtain ⟨a₂, rfl⟩ := expansion_edge_cases J he₂
  have hne' : a₁ ≠ a₂ := by rintro rfl; exact hne rfl
  by_contra hcon
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 (not_le.1 hcon)
  have hx' := Finset.mem_inter.1 hx
  have hy' := Finset.mem_inter.1 hy
  obtain ⟨p, rfl, hp₁, hp₂⟩ := expansion_inter_aux hne' ((expansion_mem_triple J a₁ _).1 hx'.1)
    ((expansion_mem_triple J a₂ _).1 hx'.2)
  obtain ⟨q, rfl, hq₁, hq₂⟩ := expansion_inter_aux hne' ((expansion_mem_triple J a₁ _).1 hy'.1)
    ((expansion_mem_triple J a₂ _).1 hy'.2)
  have hpq : p ≠ q := fun h => hxy (congrArg Sum.inl h)
  apply hne'
  apply Subtype.ext
  exact (Quot.out_eq a₁.1).symm.trans ((sym2_mk_eq_of_mem hpq hp₁ hq₁).trans
    ((sym2_mk_eq_of_mem hpq hp₂ hq₂).symm.trans (Quot.out_eq a₂.1)))

theorem expansion_bridge {VJ : Type} [Fintype VJ] [DecidableEq VJ] (J : SimpleGraph VJ)
    [DecidableRel J.Adj]
    (ed : {e : Finset ((graphExpansion J).V) // e ∈ (graphExpansion J).edges}) :
    ∃ w ∈ ed.1, IsBridgeInc (graphExpansion J) w ed := by
  obtain ⟨e, he⟩ := expansion_edge_cases J ed.2
  have hpriv : ∀ j : {s // s ∈ (graphExpansion J).edges}, Sum.inr e ∈ j.1 → j = ed := by
    intro j hj
    exact Subtype.ext ((expansion_private J j.2 hj).trans he.symm)
  have hmem : (Sum.inr e : (graphExpansion J).V) ∈ ed.1 := by
    rw [he]; exact (expansion_mem_triple J e _).2 (Or.inr (Or.inr rfl))
  refine ⟨Sum.inr e, hmem, ?_⟩
  unfold IsBridgeInc
  refine ⟨hmem, ?_⟩
  rintro ⟨c, i, hci, hv⟩
  rcases hv with hv | hv
  · have h1 := c.mem_right (i - 1)
    rw [sub_add_cancel, hv] at h1
    have h2 := c.einj ((hpriv _ h1).trans hci.symm)
    exact zmod_one_ne_zero_of_two_le c.hm (by linear_combination -h2)
  · have h1 := c.mem_left (i + 1)
    rw [hv] at h1
    have h2 := c.einj ((hpriv _ h1).trans hci.symm)
    exact zmod_one_ne_zero_of_two_le c.hm (by linear_combination h2)

theorem expansion_cycle_core {VJ : Type} [Fintype VJ] [DecidableEq VJ] (J : SimpleGraph VJ)
    [DecidableRel J.Adj] (c : BergeCycle (graphExpansion J)) (i : ZMod c.m) :
    ∃ a : VJ, c.v i = Sum.inl a := by
  obtain ⟨z, hz⟩ : ∃ z, c.v i = z := ⟨_, rfl⟩
  rw [hz]
  cases z with
  | inl a => exact ⟨a, rfl⟩
  | inr e =>
    exfalso
    have h1 := c.mem_left i
    have h2 := c.mem_right (i - 1)
    rw [sub_add_cancel] at h2
    rw [hz] at h1 h2
    have h3 := c.einj (Subtype.ext ((expansion_private J (c.e i).2 h1).trans
      (expansion_private J (c.e (i - 1)).2 h2).symm))
    exact zmod_one_ne_zero_of_two_le c.hm (by linear_combination h3)

theorem expansion_even {VJ : Type} [Fintype VJ] [DecidableEq VJ] (J : SimpleGraph VJ)
    [DecidableRel J.Adj] (hJ : J.Colorable 2) (c : BergeCycle (graphExpansion J)) :
    Even c.m := by
  obtain ⟨col⟩ := hJ
  haveI : NeZero c.m := ⟨by have := c.hm; omega⟩
  choose a ha using expansion_cycle_core J c
  have hadj : ∀ i, J.Adj (a i) (a (i + 1)) := by
    intro i
    obtain ⟨e, he⟩ := expansion_edge_cases J (c.e i).2
    have hx := c.mem_left i
    have hy := c.mem_right i
    rw [ha, he] at hx
    rw [ha, he] at hy
    replace hx := expansion_core_mem J e _ hx
    replace hy := expansion_core_mem J e _ hy
    have hxy : a i ≠ a (i + 1) := by
      intro h
      have := c.vinj ((ha i).trans ((congrArg Sum.inl h).trans (ha (i + 1)).symm))
      exact zmod_one_ne_zero_of_two_le c.hm (by linear_combination -this)
    have hadj0 := expansion_endpoints_adj J e
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact absurd (hx.trans hy.symm) hxy
    · rw [hx, hy]; exact hadj0
    · rw [hx, hy]; exact hadj0.symm
    · exact absurd (hx.trans hy.symm) hxy
  exact zmod_even_of_alt (fun i => (col (a i) : ZMod 2))
    (fun i => zmod2_succ_of_ne _ _ (col.valid (hadj i)))

theorem expansion_intrinsic {VJ : Type} [Fintype VJ] [DecidableEq VJ] (J : SimpleGraph VJ)
    [DecidableRel J.Adj] (hJ : J.Colorable 2) : (graphExpansion J).IntrinsicObligatory :=
  ⟨expansion_linear J, expansion_bridge J, expansion_even J hJ⟩

theorem disjUnion_edge_cases {F G : FTS} {e : Finset (F.V ⊕ G.V)}
    (he : e ∈ (F.disjUnion G).edges) :
    (∃ d ∈ F.edges, e = d.map Function.Embedding.inl) ∨
    (∃ d ∈ G.edges, e = d.map Function.Embedding.inr) := by
  unfold FTS.disjUnion at he; aesop;

theorem disjUnion_berge_side {F G : FTS} (c : BergeCycle (F.disjUnion G)) :
    (∀ i, ∃ a : F.V, c.v i = Sum.inl a) ∨ (∀ i, ∃ b : G.V, c.v i = Sum.inr b) := by

  haveI : NeZero c.m := ⟨by have := c.hm; omega⟩
  have hconst : ∀ i, (c.v i).isLeft = (c.v (i + 1)).isLeft := by
    intro i
    have h1 := c.mem_left i
    have h2 := c.mem_right i
    rcases disjUnion_edge_cases (c.e i).2 with ⟨d, -, hd⟩ | ⟨d, -, hd⟩
    · rw [hd] at h1 h2
      obtain ⟨a, -, ha⟩ := Finset.mem_map.1 h1
      obtain ⟨b, -, hb⟩ := Finset.mem_map.1 h2
      rw [← ha, ← hb]; rfl
    · rw [hd] at h1 h2
      obtain ⟨a, -, ha⟩ := Finset.mem_map.1 h1
      obtain ⟨b, -, hb⟩ := Finset.mem_map.1 h2
      rw [← ha, ← hb]; rfl
  have h_const := zmod_const_of_succ_eq (fun i => (c.v i).isLeft) hconst
  cases h0 : (c.v 0).isLeft
  · right
    intro i
    have hi : (c.v i).isLeft = false := (h_const i).trans h0
    obtain ⟨z, hz⟩ : ∃ z, c.v i = z := ⟨_, rfl⟩
    rw [hz] at hi ⊢
    cases z with
    | inl a => simp at hi
    | inr b => exact ⟨b, rfl⟩
  · left
    intro i
    have hi : (c.v i).isLeft = true := (h_const i).trans h0
    obtain ⟨z, hz⟩ : ∃ z, c.v i = z := ⟨_, rfl⟩
    rw [hz] at hi ⊢
    cases z with
    | inl a => exact ⟨a, rfl⟩
    | inr b => simp at hi

noncomputable def BergeCycle.ofDisjLeft {F G : FTS} (c : BergeCycle (F.disjUnion G))
    (hv : ∀ i, ∃ a : F.V, c.v i = Sum.inl a)
    (he : ∀ i, ∃ d : Finset F.V, d ∈ F.edges ∧ (c.e i).1 = d.map Function.Embedding.inl) :
    BergeCycle F where
  m := c.m
  hm := c.hm
  v := fun i => (hv i).choose
  e := fun i => ⟨(he i).choose, (he i).choose_spec.1⟩
  vinj := by
    intro i j hij
    apply c.vinj
    rw [(hv i).choose_spec, (hv j).choose_spec]
    exact congrArg Sum.inl hij
  einj := by
    intro i j hij
    apply c.einj
    apply Subtype.ext
    have hd : (he i).choose = (he j).choose := congrArg Subtype.val hij
    rw [(he i).choose_spec.2, (he j).choose_spec.2, hd]
  mem_left := by
    intro i
    have h1 := c.mem_left i
    rw [(hv i).choose_spec, (he i).choose_spec.2] at h1
    exact (Finset.mem_map' _).mp h1
  mem_right := by
    intro i
    have h1 := c.mem_right i
    rw [(hv (i + 1)).choose_spec, (he i).choose_spec.2] at h1
    exact (Finset.mem_map' _).mp h1

noncomputable def BergeCycle.ofDisjRight {F G : FTS} (c : BergeCycle (F.disjUnion G))
    (hv : ∀ i, ∃ b : G.V, c.v i = Sum.inr b)
    (he : ∀ i, ∃ d : Finset G.V, d ∈ G.edges ∧ (c.e i).1 = d.map Function.Embedding.inr) :
    BergeCycle G where
  m := c.m
  hm := c.hm
  v := fun i => (hv i).choose
  e := fun i => ⟨(he i).choose, (he i).choose_spec.1⟩
  vinj := by
    intro i j hij
    apply c.vinj
    rw [(hv i).choose_spec, (hv j).choose_spec]
    exact congrArg Sum.inr hij
  einj := by
    intro i j hij
    apply c.einj
    apply Subtype.ext
    have hd : (he i).choose = (he j).choose := congrArg Subtype.val hij
    rw [(he i).choose_spec.2, (he j).choose_spec.2, hd]
  mem_left := by
    intro i
    have h1 := c.mem_left i
    rw [(hv i).choose_spec, (he i).choose_spec.2] at h1
    exact (Finset.mem_map' _).mp h1
  mem_right := by
    intro i
    have h1 := c.mem_right i
    rw [(hv (i + 1)).choose_spec, (he i).choose_spec.2] at h1
    exact (Finset.mem_map' _).mp h1

theorem disjUnion_berge_edges_left {F G : FTS} (c : BergeCycle (F.disjUnion G))
    (hv : ∀ i, ∃ a : F.V, c.v i = Sum.inl a) :
    ∀ i, ∃ d : Finset F.V, d ∈ F.edges ∧ (c.e i).1 = d.map Function.Embedding.inl := by
  intro i
  rcases disjUnion_edge_cases (c.e i).2 with ⟨d, hd, hde⟩ | ⟨d, hd, hde⟩
  · exact ⟨d, hd, hde⟩
  · exfalso
    obtain ⟨a, ha⟩ := hv i
    have h1 := c.mem_left i
    rw [hde, ha] at h1
    obtain ⟨b, -, hb⟩ := Finset.mem_map.1 h1
    exact Sum.inr_ne_inl hb

theorem disjUnion_berge_edges_right {F G : FTS} (c : BergeCycle (F.disjUnion G))
    (hv : ∀ i, ∃ b : G.V, c.v i = Sum.inr b) :
    ∀ i, ∃ d : Finset G.V, d ∈ G.edges ∧ (c.e i).1 = d.map Function.Embedding.inr := by
  intro i
  rcases disjUnion_edge_cases (c.e i).2 with ⟨d, hd, hde⟩ | ⟨d, hd, hde⟩
  · exfalso
    obtain ⟨b, hb⟩ := hv i
    have h1 := c.mem_left i
    rw [hde, hb] at h1
    obtain ⟨a, -, ha⟩ := Finset.mem_map.1 h1
    exact Sum.inl_ne_inr ha
  · exact ⟨d, hd, hde⟩

theorem disjUnion_linear {F G : FTS} (hF : F.Linear) (hG : G.Linear) :
    (F.disjUnion G).Linear := by
  intro e₁ he₁ e₂ he₂ hne
  rcases disjUnion_edge_cases he₁ with ⟨d₁, hd₁, rfl⟩ | ⟨d₁, hd₁, rfl⟩ <;>
    rcases disjUnion_edge_cases he₂ with ⟨d₂, hd₂, rfl⟩ | ⟨d₂, hd₂, rfl⟩
  · exact (card_map_inter_le _ _ _).trans (hF _ hd₁ _ hd₂ (fun h => hne (by rw [h])))
  · apply Finset.card_le_one.2
    intro a ha
    exfalso
    obtain ⟨h1, h2⟩ := Finset.mem_inter.1 ha
    obtain ⟨u, -, rfl⟩ := Finset.mem_map.1 h1
    obtain ⟨v, -, hv⟩ := Finset.mem_map.1 h2
    exact Sum.inr_ne_inl hv
  · apply Finset.card_le_one.2
    intro a ha
    exfalso
    obtain ⟨h1, h2⟩ := Finset.mem_inter.1 ha
    obtain ⟨u, -, rfl⟩ := Finset.mem_map.1 h1
    obtain ⟨v, -, hv⟩ := Finset.mem_map.1 h2
    exact Sum.inl_ne_inr hv
  · exact (card_map_inter_le _ _ _).trans (hG _ hd₁ _ hd₂ (fun h => hne (by rw [h])))

theorem disjUnion_even {F G : FTS} (hF : ∀ c : BergeCycle F, Even c.m)
    (hG : ∀ c : BergeCycle G, Even c.m) (c : BergeCycle (F.disjUnion G)) : Even c.m := by
  cases' disjUnion_berge_side c with hv hv;
  · exact hF ( BergeCycle.ofDisjLeft c hv ( disjUnion_berge_edges_left c hv ) )
  · specialize hG (BergeCycle.ofDisjRight c hv (disjUnion_berge_edges_right c hv));
    exact hG

theorem disjUnion_bridge {F G : FTS} (hF : F.IntrinsicObligatory)
    (hG : G.IntrinsicObligatory)
    (ed : {e : Finset (F.disjUnion G).V // e ∈ (F.disjUnion G).edges}) :
    ∃ w ∈ ed.1, IsBridgeInc (F.disjUnion G) w ed := by

  obtain ⟨d, hd, hdamap⟩ | ⟨d, hd, hdamap⟩ := disjUnion_edge_cases ed.2
  · obtain ⟨w, hw₁, -, hw₂⟩ := hF.2.1 ⟨d, hd⟩
    have hmem : (Sum.inl w : (F.disjUnion G).V) ∈ ed.1 := by
      rw [hdamap]; exact Finset.mem_map_of_mem Function.Embedding.inl hw₁
    refine ⟨Sum.inl w, hmem, ?_⟩
    unfold IsBridgeInc
    refine ⟨hmem, ?_⟩
    rintro ⟨c, i, hci, hv⟩
    have hL : ∀ i, ∃ a : F.V, c.v i = Sum.inl a := by
      rcases disjUnion_berge_side c with hv' | hv'
      · exact hv'
      · exfalso
        rcases hv with hv | hv
        · obtain ⟨b, hb⟩ := hv' i; rw [hb] at hv; exact Sum.inr_ne_inl hv
        · obtain ⟨b, hb⟩ := hv' (i + 1); rw [hb] at hv; exact Sum.inr_ne_inl hv
    have hE := disjUnion_berge_edges_left c hL
    apply hw₂
    refine ⟨BergeCycle.ofDisjLeft c hL hE, i, ?_, ?_⟩
    · exact Subtype.ext (Finset.map_injective Function.Embedding.inl
        (((hE i).choose_spec.2).symm.trans (by rw [hci]; exact hdamap)))
    · rcases hv with hv | hv
      · left; exact Sum.inl_injective (((hL i).choose_spec).symm.trans hv)
      · right; exact Sum.inl_injective (((hL (i + 1)).choose_spec).symm.trans hv)
  · obtain ⟨w, hw₁, -, hw₂⟩ := hG.2.1 ⟨d, hd⟩
    have hmem : (Sum.inr w : (F.disjUnion G).V) ∈ ed.1 := by
      rw [hdamap]; exact Finset.mem_map_of_mem Function.Embedding.inr hw₁
    refine ⟨Sum.inr w, hmem, ?_⟩
    unfold IsBridgeInc
    refine ⟨hmem, ?_⟩
    rintro ⟨c, i, hci, hv⟩
    have hR : ∀ i, ∃ b : G.V, c.v i = Sum.inr b := by
      rcases disjUnion_berge_side c with hv' | hv'
      · exfalso
        rcases hv with hv | hv
        · obtain ⟨b, hb⟩ := hv' i; rw [hb] at hv; exact Sum.inl_ne_inr hv
        · obtain ⟨b, hb⟩ := hv' (i + 1); rw [hb] at hv; exact Sum.inl_ne_inr hv
      · exact hv'
    have hE := disjUnion_berge_edges_right c hR
    apply hw₂
    refine ⟨BergeCycle.ofDisjRight c hR hE, i, ?_, ?_⟩
    · exact Subtype.ext (Finset.map_injective Function.Embedding.inr
        (((hE i).choose_spec.2).symm.trans (by rw [hci]; exact hdamap)))
    · rcases hv with hv | hv
      · left; exact Sum.inr_injective (((hR i).choose_spec).symm.trans hv)
      · right; exact Sum.inr_injective (((hR (i + 1)).choose_spec).symm.trans hv)

theorem disjUnion_intrinsic {F G : FTS} (hF : F.IntrinsicObligatory)
    (hG : G.IntrinsicObligatory) : (F.disjUnion G).IntrinsicObligatory :=
  ⟨disjUnion_linear hF.1 hG.1, disjUnion_bridge hF hG,
    disjUnion_even hF.2.2 hG.2.2⟩

noncomputable def BergeCycle.ofEmbedding {F H : FTS} (ρ : F.V ↪ H.V)
    (c : BergeCycle H)
    (hv : ∀ i, ∃ a : F.V, c.v i = ρ a)
    (he : ∀ i, ∃ d : Finset F.V, d ∈ F.edges ∧ (c.e i).1 = d.map ρ) : BergeCycle F where
  m := c.m
  hm := c.hm
  v := fun i => (hv i).choose
  e := fun i => ⟨(he i).choose, (he i).choose_spec.1⟩
  vinj := by
    intro i j hij
    apply c.vinj
    rw [(hv i).choose_spec, (hv j).choose_spec]
    exact congrArg (⇑ρ) hij
  einj := by
    intro i j hij
    apply c.einj
    apply Subtype.ext
    have hd : (he i).choose = (he j).choose := congrArg Subtype.val hij
    rw [(he i).choose_spec.2, (he j).choose_spec.2, hd]
  mem_left := by
    intro i
    have h1 := c.mem_left i
    rw [(hv i).choose_spec, (he i).choose_spec.2] at h1
    exact (Finset.mem_map' _).mp h1
  mem_right := by
    intro i
    have h1 := c.mem_right i
    rw [(hv (i + 1)).choose_spec, (he i).choose_spec.2] at h1
    exact (Finset.mem_map' _).mp h1

def amalgEmbG (F G : FTS) (x : F.V) (y : G.V) : G.V ↪ (F.amalgamate G x y).V :=
  ⟨fun b => if h : b = y then Sum.inl x else Sum.inr ⟨b, h⟩, by
    intro a b hab
    simp only at hab
    by_cases ha : a = y <;> by_cases hb : b = y
    · rw [ha, hb]
    · exact absurd ((dif_pos ha).symm.trans (hab.trans (dif_neg hb))) Sum.inl_ne_inr
    · exact absurd ((dif_neg ha).symm.trans (hab.trans (dif_pos hb))) Sum.inr_ne_inl
    · exact congrArg Subtype.val
        (Sum.inr_injective ((dif_neg ha).symm.trans (hab.trans (dif_neg hb))))⟩

theorem amalgEmbG_self (F G : FTS) (x : F.V) (y : G.V) :
    amalgEmbG F G x y y = Sum.inl x := dif_pos rfl

theorem amalgEmbG_ne (F G : FTS) (x : F.V) {y b : G.V} (h : b ≠ y) :
    amalgEmbG F G x y b = Sum.inr ⟨b, h⟩ := dif_neg h

theorem amalgamate_edge_cases {F G : FTS} {x : F.V} {y : G.V}
    {e : Finset (F.amalgamate G x y).V} (he : e ∈ (F.amalgamate G x y).edges) :
    (∃ d ∈ F.edges, e = d.map Function.Embedding.inl) ∨
    (∃ d ∈ G.edges, e = d.map (amalgEmbG F G x y)) := by
  rcases (FTS.mem_amalgamate_edges F G x y e).1 he with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · exact Or.inl ⟨a, ha, rfl⟩
  · exact Or.inr ⟨a, ha, rfl⟩

theorem amalgamate_cross_inter {F G : FTS} {x : F.V} {y : G.V}
    {dF : Finset F.V} {dG : Finset G.V} (hdG : dG ∈ G.edges)
    {w : (F.amalgamate G x y).V}
    (h1 : w ∈ dF.map Function.Embedding.inl) (h2 : w ∈ dG.map (amalgEmbG F G x y)) :
    w = Sum.inl x := by
  obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 h1
  obtain ⟨b, -, hb⟩ := Finset.mem_map.1 h2
  by_cases hby : b = y
  · subst hby
    exact (hb.symm.trans (amalgEmbG_self F G x b))
  · rw [amalgEmbG_ne F G x hby] at hb
    exact absurd hb Sum.inr_ne_inl

theorem amalgamate_berge_side {F G : FTS} {x : F.V} {y : G.V}
    (c : BergeCycle (F.amalgamate G x y)) :
    (∀ i, ∃ d ∈ F.edges, (c.e i).1 = d.map Function.Embedding.inl) ∨
    (∀ i, ∃ d ∈ G.edges, (c.e i).1 = d.map (amalgEmbG F G x y)) := by
  haveI : NeZero c.m := ⟨by have := c.hm; omega⟩
  have hG : ∀ i, ¬ (∃ d ∈ F.edges, (c.e i).1 = d.map Function.Embedding.inl) →
      ∃ d ∈ G.edges, (c.e i).1 = d.map (amalgEmbG F G x y) := by
    intro i hi
    rcases amalgamate_edge_cases (c.e i).2 with h | h
    · exact absurd h hi
    · exact h
  have hvert : ∀ i, (∃ d ∈ F.edges, (c.e i).1 = d.map Function.Embedding.inl) →
      ¬ (∃ d ∈ F.edges, (c.e (i + 1)).1 = d.map Function.Embedding.inl) →
      c.v (i + 1) = Sum.inl x := by
    intro i hi hi'
    obtain ⟨dF, -, hdF⟩ := hi
    obtain ⟨dG, hdG, hdG'⟩ := hG _ hi'
    have h1 := c.mem_right i
    have h2 := c.mem_left (i + 1)
    rw [hdF] at h1
    rw [hdG'] at h2
    exact amalgamate_cross_inter hdG h1 h2
  have hvert' : ∀ i, ¬ (∃ d ∈ F.edges, (c.e i).1 = d.map Function.Embedding.inl) →
      (∃ d ∈ F.edges, (c.e (i + 1)).1 = d.map Function.Embedding.inl) →
      c.v (i + 1) = Sum.inl x := by
    intro i hi hi'
    obtain ⟨dF, -, hdF⟩ := hi'
    obtain ⟨dG, hdG, hdG'⟩ := hG _ hi
    have h1 := c.mem_left (i + 1)
    have h2 := c.mem_right i
    rw [hdF] at h1
    rw [hdG'] at h2
    exact amalgamate_cross_inter hdG h1 h2
  let s : ZMod c.m → Bool := fun i =>
    decide (∃ d ∈ F.edges, (c.e i).1 = d.map Function.Embedding.inl)
  have hchg : ∀ i, s i ≠ s (i + 1) → c.v (i + 1) = Sum.inl x := by
    intro i h
    by_cases hi : ∃ d ∈ F.edges, (c.e i).1 = d.map Function.Embedding.inl <;>
      by_cases hi' : ∃ d ∈ F.edges, (c.e (i + 1)).1 = d.map Function.Embedding.inl
    · exact absurd ((decide_eq_true hi).trans (decide_eq_true hi').symm) h
    · exact hvert i hi hi'
    · exact hvert' i hi hi'
    · exact absurd ((decide_eq_false hi).trans (decide_eq_false hi').symm) h
  have h_change : ∀ i j, s i ≠ s (i + 1) → s j ≠ s (j + 1) → i = j := by
    intro i j hi hj
    exact add_right_cancel (c.vinj ((hchg i hi).trans (hchg j hj).symm))
  have h_const := zmod_const_of_succ_eq s (zmod_succ_eq_of_unique_change s h_change)
  by_cases h0 : ∃ d ∈ F.edges, (c.e 0).1 = d.map Function.Embedding.inl
  · left
    intro i
    exact of_decide_eq_true ((h_const i).trans (decide_eq_true h0))
  · right
    intro i
    exact hG i (of_decide_eq_false ((h_const i).trans (decide_eq_false h0)))

theorem amalgamate_berge_vertsF {F G : FTS} {x : F.V} {y : G.V}
    (c : BergeCycle (F.amalgamate G x y))
    (he : ∀ i, ∃ d ∈ F.edges, (c.e i).1 = d.map Function.Embedding.inl) :
    ∀ i, ∃ a : F.V, c.v i = Sum.inl a := by
  intro i
  obtain ⟨d, _, hde⟩ := he i
  have hmem := c.mem_left i
  rw [hde] at hmem
  obtain ⟨a, _, hEq⟩ := Finset.mem_map.1 hmem
  exact ⟨a, hEq.symm⟩

theorem amalgamate_berge_vertsG {F G : FTS} {x : F.V} {y : G.V}
    (c : BergeCycle (F.amalgamate G x y))
    (he : ∀ i, ∃ d ∈ G.edges, (c.e i).1 = d.map (amalgEmbG F G x y)) :
    ∀ i, ∃ b : G.V, c.v i = amalgEmbG F G x y b := by
  intro i
  obtain ⟨d, _, hde⟩ := he i
  have hmem := c.mem_left i
  rw [hde, Finset.mem_map] at hmem
  obtain ⟨b, _, hEq⟩ := hmem
  exact ⟨b, hEq.symm⟩

theorem amalgamate_linear {F G : FTS} (x : F.V) (y : G.V) (hF : F.Linear) (hG : G.Linear) :
    (F.amalgamate G x y).Linear := by
  intro e₁ he₁ e₂ he₂ hne
  rcases amalgamate_edge_cases he₁ with ⟨d₁, hd₁, rfl⟩ | ⟨d₁, hd₁, rfl⟩ <;>
    rcases amalgamate_edge_cases he₂ with ⟨d₂, hd₂, rfl⟩ | ⟨d₂, hd₂, rfl⟩
  · exact (card_map_inter_le _ _ _).trans (hF _ hd₁ _ hd₂ (fun h => hne (by rw [h])))
  · apply Finset.card_le_one.2
    intro a ha b hb
    obtain ⟨ha1, ha2⟩ := Finset.mem_inter.1 ha
    obtain ⟨hb1, hb2⟩ := Finset.mem_inter.1 hb
    exact (amalgamate_cross_inter hd₂ ha1 ha2).trans (amalgamate_cross_inter hd₂ hb1 hb2).symm
  · apply Finset.card_le_one.2
    intro a ha b hb
    obtain ⟨ha1, ha2⟩ := Finset.mem_inter.1 ha
    obtain ⟨hb1, hb2⟩ := Finset.mem_inter.1 hb
    exact (amalgamate_cross_inter hd₁ ha2 ha1).trans (amalgamate_cross_inter hd₁ hb2 hb1).symm
  · exact (card_map_inter_le _ _ _).trans (hG _ hd₁ _ hd₂ (fun h => hne (by rw [h])))

theorem amalgamate_even {F G : FTS} (x : F.V) (y : G.V) (hF : ∀ c : BergeCycle F, Even c.m)
    (hG : ∀ c : BergeCycle G, Even c.m) (c : BergeCycle (F.amalgamate G x y)) : Even c.m := by
  cases' amalgamate_berge_side c with heF heG;
  · exact hF ( BergeCycle.ofEmbedding ( Function.Embedding.inl : F.V ↪ ( F.amalgamate G x y ).V ) c ( amalgamate_berge_vertsF c heF ) heF )
  · exact hG ( BergeCycle.ofEmbedding ( amalgEmbG F G x y ) c ( amalgamate_berge_vertsG c heG ) heG )

theorem amalgamate_FG_ne {F G : FTS} {x : F.V} {y : G.V} {dF : Finset F.V} {dG : Finset G.V}
    (hdG : dG ∈ G.edges) :
    dF.map Function.Embedding.inl ≠ dG.map (amalgEmbG F G x y) := by
  intro h_eq
  obtain ⟨b, hb, hb'⟩ := Finset.exists_mem_ne
    (by have := FTS.card3 G dG hdG; omega : 1 < dG.card) y
  have hmem : amalgEmbG F G x y b ∈ dF.map Function.Embedding.inl := by
    rw [h_eq]; exact Finset.mem_map_of_mem _ hb
  obtain ⟨a, -, ha⟩ := Finset.mem_map.1 hmem
  rw [amalgEmbG_ne F G x hb'] at ha
  exact Sum.inl_ne_inr ha

theorem amalgamate_bridge {F G : FTS} (x : F.V) (y : G.V) (hF : F.IntrinsicObligatory)
    (hG : G.IntrinsicObligatory)
    (ed : {e : Finset (F.amalgamate G x y).V // e ∈ (F.amalgamate G x y).edges}) :
    ∃ w ∈ ed.1, IsBridgeInc (F.amalgamate G x y) w ed := by
  rcases amalgamate_edge_cases ed.2 with ⟨d, hd, hde⟩ | ⟨d, hd, hde⟩
  · obtain ⟨w, hw₁, -, hw₂⟩ := hF.2.1 ⟨d, hd⟩
    have hmem : (Sum.inl w : (F.amalgamate G x y).V) ∈ ed.1 := by
      rw [hde]; exact Finset.mem_map_of_mem Function.Embedding.inl hw₁
    refine ⟨Sum.inl w, hmem, ?_⟩
    unfold IsBridgeInc
    refine ⟨hmem, ?_⟩
    rintro ⟨c, i, hci, hv⟩
    rcases amalgamate_berge_side c with heF | heG
    · apply hw₂
      refine ⟨BergeCycle.ofEmbedding (Function.Embedding.inl : F.V ↪ (F.amalgamate G x y).V) c
        (amalgamate_berge_vertsF c heF) heF, i, ?_, ?_⟩
      · exact Subtype.ext (Finset.map_injective (Function.Embedding.inl : F.V ↪ (F.amalgamate G x y).V)
          (((heF i).choose_spec.2).symm.trans (by rw [hci]; exact hde)))
      · rcases hv with hv | hv
        · left
          exact Sum.inl_injective (((amalgamate_berge_vertsF c heF i).choose_spec).symm.trans hv)
        · right
          exact Sum.inl_injective
            (((amalgamate_berge_vertsF c heF (i + 1)).choose_spec).symm.trans hv)
    · obtain ⟨d', hd', hde'⟩ := heG i
      exact amalgamate_FG_ne hd' (hde.symm.trans ((congrArg Subtype.val hci).symm.trans hde'))
  · obtain ⟨w, hw₁, -, hw₂⟩ := hG.2.1 ⟨d, hd⟩
    have hmem : amalgEmbG F G x y w ∈ ed.1 := by
      rw [hde]; exact Finset.mem_map_of_mem _ hw₁
    refine ⟨amalgEmbG F G x y w, hmem, ?_⟩
    unfold IsBridgeInc
    refine ⟨hmem, ?_⟩
    rintro ⟨c, i, hci, hv⟩
    rcases amalgamate_berge_side c with heF | heG
    · obtain ⟨d', hd', hde'⟩ := heF i
      exact amalgamate_FG_ne hd (hde'.symm.trans ((congrArg Subtype.val hci).trans hde))
    · apply hw₂
      refine ⟨BergeCycle.ofEmbedding (amalgEmbG F G x y) c (amalgamate_berge_vertsG c heG) heG,
        i, ?_, ?_⟩
      · exact Subtype.ext (Finset.map_injective (amalgEmbG F G x y)
          (((heG i).choose_spec.2).symm.trans (by rw [hci]; exact hde)))
      · rcases hv with hv | hv
        · left
          exact (amalgEmbG F G x y).injective
            (((amalgamate_berge_vertsG c heG i).choose_spec).symm.trans hv)
        · right
          exact (amalgEmbG F G x y).injective
            (((amalgamate_berge_vertsG c heG (i + 1)).choose_spec).symm.trans hv)

theorem amalgamate_intrinsic {F G : FTS} (x : F.V) (y : G.V)
    (hF : F.IntrinsicObligatory) (hG : G.IntrinsicObligatory) :
    (F.amalgamate G x y).IntrinsicObligatory :=
  ⟨amalgamate_linear x y hF.1 hG.1, amalgamate_bridge x y hF hG,
    amalgamate_even x y hF.2.2 hG.2.2⟩

theorem bclass_intrinsic {F : FTS} (h : Bclass F) : F.IntrinsicObligatory := by
  induction h with
  | edgeless F hF => exact edgeless_intrinsic F hF
  | expansion J hJ => exact expansion_intrinsic J hJ
  | iso hiso _ ih => exact intrinsic_iso hiso ih
  | union _ _ ihF ihG => exact disjUnion_intrinsic ihF ihG
  | amalg x y _ _ ihF ihG => exact amalgamate_intrinsic x y ihF ihG

end Erdos593
end

-- DecompRestrict
section
open Cardinal

namespace Erdos593

open Classical

universe u

def ReconOK (F : FTS) : Prop :=
  F.Linear ∧ (∀ x : F.V, ¬ F.Isolated x) ∧
  (∀ ed : {e : Finset F.V // e ∈ F.edges}, ∃ w ∈ ed.1, IsBridgeInc F w ed) ∧
  (∀ c : BergeCycle F, Even c.m)

noncomputable def FTS.restrict (F : FTS) (S : Finset {e : Finset F.V // e ∈ F.edges}) : FTS where
  V := {v : F.V // ∃ e ∈ S, v ∈ e.1}
  finV := Fintype.ofFinite _
  decV := Subtype.instDecidableEq
  edges := S.attach.image (fun e =>
    Finset.subtype (fun v => ∃ e' ∈ S, v ∈ e'.1) e.1.1)
  card3 := by
    intro s hs
    simp only [Finset.mem_image, Finset.mem_attach, true_and] at hs
    obtain ⟨e, rfl⟩ := hs
    rw [Finset.card_subtype]
    have hfil : e.1.1.filter (fun v => ∃ e' ∈ S, v ∈ e'.1) = e.1.1 := by
      apply Finset.filter_true_of_mem
      intro v hv
      exact ⟨e.1, e.2, hv⟩
    rw [hfil]
    exact F.card3 e.1.1 e.1.2

theorem FTS.mem_restrict_edges {F : FTS} {S : Finset {e : Finset F.V // e ∈ F.edges}}
    {s : Finset (F.restrict S).V} :
    s ∈ (F.restrict S).edges ↔
      ∃ e ∈ S, s = Finset.subtype (fun v => ∃ e' ∈ S, v ∈ e'.1) e.1 := by
  constructor
  · intro hs
    obtain ⟨e, -, he⟩ := Finset.mem_image.1 hs
    exact ⟨e.1, e.2, he.symm⟩
  · rintro ⟨e, he, rfl⟩
    exact Finset.mem_image.2 ⟨⟨e, he⟩, Finset.mem_attach _ _, rfl⟩

theorem FTS.restrict_edges_card {F : FTS} (S : Finset {e : Finset F.V // e ∈ F.edges}) :
    (F.restrict S).edges.card = S.card := by
  rw [ FTS.restrict, Finset.card_image_of_injOn ];
  · exact Finset.card_attach;
  · intro e₁ he₁ e₂ he₂ h_eq; simp_all +decide [ Finset.ext_iff ] ;
    exact Subtype.ext (Subtype.ext (Finset.ext fun a => ⟨fun ha => (h_eq a _ e₁.1.2 e₁.2 ha).1 ha, fun ha => (h_eq a _ e₂.1.2 e₂.2 ha).2 ha⟩))

theorem FTS.card_inter_map_subtype {α : Type*} [DecidableEq α] (p : α → Prop)
    (s₁ s₂ : Finset (Subtype p)) :
    (s₁ ∩ s₂).card =
      (s₁.map (Function.Embedding.subtype p) ∩ s₂.map (Function.Embedding.subtype p)).card := by
  rw [← Finset.map_inter, Finset.card_map]

theorem FTS.restrict_linear {F : FTS} (S : Finset {e : Finset F.V // e ∈ F.edges})
    (hlin : F.Linear) : (F.restrict S).Linear := by
  intro s₁ hs₁ s₂ hs₂ hne;
  convert hlin _ _ _ _ _;
  rotate_left;
  exact s₁.map ( Function.Embedding.subtype fun v => ∃ e' ∈ S, v ∈ e'.1 );
  rotate_left;
  exact s₂.map ( Function.Embedding.subtype fun v => ∃ e' ∈ S, v ∈ e'.1 );
  · obtain ⟨ e, he, rfl ⟩ := FTS.mem_restrict_edges.mp hs₂;
    rw [Finset.subtype_map_of_mem (fun x hx => ⟨e, he, hx⟩)]; exact e.2;
  · exact fun h => hne <| Finset.map_injective ( Function.Embedding.subtype _ ) h;
  · exact FTS.card_inter_map_subtype _ _ _
  · obtain ⟨ e₁, he₁, rfl ⟩ := FTS.mem_restrict_edges.mp hs₁;
    convert e₁.2 using 1;
    ext; simp [Finset.mem_map, Finset.mem_subtype];
    exact fun h => ⟨ e₁.1, ⟨ e₁.2, he₁ ⟩, h ⟩

theorem FTS.restrict_no_isolated {F : FTS} (S : Finset {e : Finset F.V // e ∈ F.edges})
    (v : (F.restrict S).V) : ¬ (F.restrict S).Isolated v := by
  have h_isolated : ¬(F.restrict S).Isolated v := by

    obtain ⟨e, heS, hev⟩ := v.2
    let s := Finset.subtype (fun v => ∃ e' ∈ S, v ∈ e'.1) e.1

    have hs : s ∈ (F.restrict S).edges := by
      exact FTS.mem_restrict_edges.mpr ⟨ e, heS, rfl ⟩

    have hv_s : v ∈ s := by
      exact Finset.mem_subtype.mpr ( by aesop )

    unfold FTS.Isolated
    push_neg
    exact ⟨s, hs, hv_s⟩;
  grind

theorem FTS.restrict_edge_map_mem {F : FTS} {S : Finset {e : Finset F.V // e ∈ F.edges}}
    {d : Finset (F.restrict S).V} (hd : d ∈ (F.restrict S).edges) :
    d.map (Function.Embedding.subtype (fun v => ∃ e' ∈ S, v ∈ e'.1)) ∈ F.edges := by
  obtain ⟨ e, heS, rfl ⟩ := FTS.mem_restrict_edges.mp hd;
  rw [Finset.subtype_map_of_mem (fun x hx => ⟨e, heS, hx⟩)]; exact e.2

noncomputable def BergeCycle.ofRestrict {F : FTS}
    {S : Finset {e : Finset F.V // e ∈ F.edges}} (c : BergeCycle (F.restrict S)) :
    BergeCycle F where
  m := c.m
  hm := c.hm
  v := fun i => Function.Embedding.subtype (fun v => ∃ e' ∈ S, v ∈ e'.1) (c.v i)
  e := fun i => ⟨(c.e i).1.map (Function.Embedding.subtype (fun v => ∃ e' ∈ S, v ∈ e'.1)),
    FTS.restrict_edge_map_mem (c.e i).2⟩
  vinj := fun i j h => c.vinj ((Function.Embedding.subtype _).injective h)
  einj := by
    intro i j h
    apply c.einj
    have h2 : (c.e i).1.map (Function.Embedding.subtype (fun v => ∃ e' ∈ S, v ∈ e'.1)) =
        (c.e j).1.map (Function.Embedding.subtype (fun v => ∃ e' ∈ S, v ∈ e'.1)) := by
      simpa using congrArg Subtype.val h
    exact Subtype.ext (Finset.map_injective _ h2)
  mem_left := fun i => Finset.mem_map_of_mem _ (c.mem_left i)
  mem_right := fun i => Finset.mem_map_of_mem _ (c.mem_right i)

theorem FTS.restrict_even {F : FTS} (S : Finset {e : Finset F.V // e ∈ F.edges})
    (hev : ∀ c : BergeCycle F, Even c.m) (c : BergeCycle (F.restrict S)) : Even c.m :=
  hev (BergeCycle.ofRestrict c)

theorem FTS.restrict_bridge {F : FTS} (S : Finset {e : Finset F.V // e ∈ F.edges})
    (hbr : ∀ ed : {e : Finset F.V // e ∈ F.edges}, ∃ w ∈ ed.1, IsBridgeInc F w ed)
    (ed : {e : Finset (F.restrict S).V // e ∈ (F.restrict S).edges}) :
    ∃ w ∈ ed.1, IsBridgeInc (F.restrict S) w ed := by
  obtain ⟨ e, heS, he ⟩ := FTS.mem_restrict_edges.mp ed.2;
  obtain ⟨ w, hw₁, hw₂ ⟩ := hbr e;
  refine' ⟨ ⟨ w, ⟨ e, heS, hw₁ ⟩ ⟩, _, _ ⟩ <;> simp_all +decide [ IsBridgeInc ];
  · exact Finset.mem_subtype.mpr ( by aesop );
  · refine' ⟨ Finset.mem_subtype.mpr ( by aesop ), _ ⟩;
    rintro ⟨ c, i, hi, h ⟩;
    refine' hw₂ ⟨ BergeCycle.ofRestrict c, i, _, _ ⟩ <;> simp_all +decide [ BergeCycle.ofRestrict ];
    · ext; aesop;
    · rcases h with h | h
      · left; rw [h]
      · right; exact congrArg Subtype.val h

theorem FTS.restrict_reconOK {F : FTS} (S : Finset {e : Finset F.V // e ∈ F.edges})
    (hlin : F.Linear)
    (hbr : ∀ ed : {e : Finset F.V // e ∈ F.edges}, ∃ w ∈ ed.1, IsBridgeInc F w ed)
    (hev : ∀ c : BergeCycle F, Even c.m) : ReconOK (F.restrict S) :=
  ⟨FTS.restrict_linear S hlin, FTS.restrict_no_isolated S,
    FTS.restrict_bridge S hbr, FTS.restrict_even S hev⟩

end Erdos593
end

-- DecompSep
section
open Cardinal

namespace Erdos593

open Classical

universe u

variable {F : FTS} (S : Finset {e : Finset F.V // e ∈ F.edges})

abbrev IncS (v : F.V) : Prop := ∃ e ∈ S, v ∈ e.1

noncomputable def sepEquiv
    (hcov : ∀ v : F.V, IncS S v ∨ (∃ e ∈ Sᶜ, v ∈ e.1))
    (hsep : ∀ v : F.V, IncS S v → (∃ e ∈ Sᶜ, v ∈ e.1) → False) :
    F.V ≃ (F.restrict S).V ⊕ (F.restrict Sᶜ).V where
  toFun v := if hv : IncS S v then Sum.inl ⟨v, hv⟩ else Sum.inr ⟨v, (hcov v).resolve_left hv⟩
  invFun := Sum.elim Subtype.val Subtype.val
  left_inv := by
    intro v; by_cases hv : IncS S v <;> simp [hv] <;> rfl
  right_inv := by
    rintro (⟨v, hv⟩ | ⟨v, hv⟩)
    · exact dif_pos hv
    · exact dif_neg (fun hS => hsep v hS hv)

@[simp] theorem sepEquiv_inl {hcov hsep} {v : F.V} (hv : IncS S v) :
    sepEquiv S hcov hsep v = Sum.inl ⟨v, hv⟩ := by
  simp only [sepEquiv, Equiv.coe_fn_mk]; rw [dif_pos hv]

theorem sepEquiv_inr {hcov hsep} {v : F.V} (hv : ¬ IncS S v)
    (hv' : ∃ e ∈ Sᶜ, v ∈ e.1) :
    sepEquiv S hcov hsep v = Sum.inr ⟨v, hv'⟩ := by
  simp only [sepEquiv, Equiv.coe_fn_mk]; rw [dif_neg hv]

theorem sepEquiv_map_left {hcov hsep} {e : Finset F.V} (he : ∀ v ∈ e, IncS S v) :
    e.map (sepEquiv S hcov hsep).toEmbedding =
      (Finset.subtype (fun v => IncS S v) e).map Function.Embedding.inl := by
  ext x
  constructor
  · intro hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.1 hx
    exact Finset.mem_map.2 ⟨⟨v, he v hv⟩, Finset.mem_subtype.2 hv,
      (sepEquiv_inl (hcov := hcov) (hsep := hsep) S (he v hv)).symm⟩
  · intro hx
    obtain ⟨⟨v, hvS⟩, hv, rfl⟩ := Finset.mem_map.1 hx
    exact Finset.mem_map.2 ⟨v, Finset.mem_subtype.1 hv,
      sepEquiv_inl (hcov := hcov) (hsep := hsep) S hvS⟩

theorem sepEquiv_map_right {hcov hsep} {e : Finset F.V} (he : ∀ v ∈ e, ¬ IncS S v)
    (he' : ∀ v ∈ e, ∃ e' ∈ Sᶜ, v ∈ e'.1) :
    e.map (sepEquiv S hcov hsep).toEmbedding =
      (Finset.subtype (fun v => ∃ e' ∈ Sᶜ, v ∈ e'.1) e).map Function.Embedding.inr := by
  ext x
  constructor
  · intro hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.1 hx
    exact Finset.mem_map.2 ⟨⟨v, he' v hv⟩, Finset.mem_subtype.2 hv,
      (sepEquiv_inr (hcov := hcov) (hsep := hsep) S (he v hv) (he' v hv)).symm⟩
  · intro hx
    obtain ⟨⟨v, hvT⟩, hv, rfl⟩ := Finset.mem_map.1 hx
    exact Finset.mem_map.2 ⟨v, Finset.mem_subtype.1 hv,
      sepEquiv_inr (hcov := hcov) (hsep := hsep) S (he v (Finset.mem_subtype.1 hv)) hvT⟩

theorem FTS.mem_disjUnion_edges_iff (F G : FTS) (e : Finset (F.disjUnion G).V) :
    e ∈ (F.disjUnion G).edges ↔
      (∃ a ∈ F.edges, Finset.map Function.Embedding.inl a = e) ∨
      (∃ a ∈ G.edges, Finset.map Function.Embedding.inr a = e) := by
  constructor
  · intro h
    rcases Finset.mem_union.1 h with h | h
    · exact Or.inl (Finset.mem_image.1 h)
    · exact Or.inr (Finset.mem_image.1 h)
  · rintro (h | h)
    · exact Finset.mem_union.2 (Or.inl (Finset.mem_image.2 h))
    · exact Finset.mem_union.2 (Or.inr (Finset.mem_image.2 h))


variable (g : F.V)

noncomputable def amalgEquiv
    (hcov : ∀ v : F.V, IncS S v ∨ (∃ e ∈ Sᶜ, v ∈ e.1))
    (hsep : ∀ v : F.V, IncS S v → (∃ e ∈ Sᶜ, v ∈ e.1) → v = g)
    (hgS : IncS S g) (hgT : ∃ e ∈ Sᶜ, g ∈ e.1) :
    F.V ≃ (F.restrict S).V ⊕ {b : (F.restrict Sᶜ).V // b ≠ ⟨g, hgT⟩} where
  toFun v := if hv : IncS S v then Sum.inl ⟨v, hv⟩
    else Sum.inr ⟨⟨v, (hcov v).resolve_left hv⟩, by
      intro heq
      apply hv
      have hvg : v = g := congrArg Subtype.val heq
      rw [hvg]; exact hgS⟩
  invFun := Sum.elim Subtype.val (fun b => b.1.1)
  left_inv := by
    intro v; by_cases hv : IncS S v <;> simp [hv] <;> rfl
  right_inv := by
    rintro (⟨v, hv⟩ | ⟨⟨v, hv⟩, hne⟩)
    · exact dif_pos hv
    · exact dif_neg (fun hS => hne (Subtype.ext (hsep v hS hv)))

@[simp] theorem amalgEquiv_inl {hcov hsep hgS hgT} {v : F.V} (hv : IncS S v) :
    amalgEquiv S g hcov hsep hgS hgT v = Sum.inl ⟨v, hv⟩ := by
  simp only [amalgEquiv, Equiv.coe_fn_mk]; rw [dif_pos hv]

theorem amalgEquiv_inr {hcov hsep hgS hgT} {v : F.V} (hv : ¬ IncS S v)
    (hv' : ∃ e ∈ Sᶜ, v ∈ e.1) (hne : v ≠ g) :
    amalgEquiv S g hcov hsep hgS hgT v = Sum.inr ⟨⟨v, hv'⟩, by
      intro heq; exact hne (congrArg Subtype.val heq)⟩ := by
  simp only [amalgEquiv, Equiv.coe_fn_mk]; rw [dif_neg hv]

theorem amalgEquiv_map_left {hcov hsep hgS hgT} {e : Finset F.V} (he : ∀ v ∈ e, IncS S v) :
    e.map (amalgEquiv S g hcov hsep hgS hgT).toEmbedding =
      (Finset.subtype (fun v => IncS S v) e).map Function.Embedding.inl := by
  ext x
  constructor
  · intro hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.1 hx
    exact Finset.mem_map.2 ⟨⟨v, he v hv⟩, Finset.mem_subtype.2 hv,
      (amalgEquiv_inl (hcov := hcov) (hsep := hsep) (hgS := hgS) (hgT := hgT) S g (he v hv)).symm⟩
  · intro hx
    obtain ⟨⟨v, hvS⟩, hv, rfl⟩ := Finset.mem_map.1 hx
    exact Finset.mem_map.2 ⟨v, Finset.mem_subtype.1 hv,
      amalgEquiv_inl (hcov := hcov) (hsep := hsep) (hgS := hgS) (hgT := hgT) S g hvS⟩

theorem amalgEmbG_apply_self (F G : FTS) (x : F.V) (y : G.V) :
    amalgEmbG F G x y y = Sum.inl x := by
  unfold amalgEmbG
  exact dif_pos rfl

theorem amalgEmbG_apply_ne (F G : FTS) (x : F.V) (y : G.V) (b : G.V) (h : b ≠ y) :
    amalgEmbG F G x y b = Sum.inr ⟨b, h⟩ := by
  unfold amalgEmbG
  exact dif_neg h

theorem FTS.mem_amalgamate_edges_emb (F G : FTS) (x : F.V) (y : G.V)
    (e : Finset (F.amalgamate G x y).V) :
    e ∈ (F.amalgamate G x y).edges ↔
      (∃ a ∈ F.edges, Finset.map Function.Embedding.inl a = e) ∨
      (∃ a ∈ G.edges, Finset.map (amalgEmbG F G x y) a = e) := by
  rw [FTS.mem_amalgamate_edges]
  apply or_congr Iff.rfl
  apply exists_congr
  intro a
  apply and_congr Iff.rfl
  apply Eq.congr_left
  congr 1

theorem amalgEquiv_map_amalg {hcov hsep hgS hgT} {e : Finset F.V}
    (he' : ∀ v ∈ e, ∃ e' ∈ Sᶜ, v ∈ e'.1) :
    e.map (amalgEquiv S g hcov hsep hgS hgT).toEmbedding =
      (Finset.subtype (fun v => ∃ e' ∈ Sᶜ, v ∈ e'.1) e).map
        (amalgEmbG (F.restrict S) (F.restrict Sᶜ) ⟨g, hgS⟩ ⟨g, hgT⟩) := by
  have key : ∀ (v : F.V) (hv' : ∃ e' ∈ Sᶜ, v ∈ e'.1),
      amalgEquiv S g hcov hsep hgS hgT v =
        amalgEmbG (F.restrict S) (F.restrict Sᶜ) ⟨g, hgS⟩ ⟨g, hgT⟩ ⟨v, hv'⟩ := by
    intro v hv'
    by_cases hvg : v = g
    · subst hvg
      rw [amalgEquiv_inl S v hgS]
      exact (amalgEmbG_apply_self (F.restrict S) (F.restrict Sᶜ) ⟨v, hgS⟩ ⟨v, hgT⟩).symm
    · have hS : ¬ IncS S v := fun hS => hvg (hsep v hS hv')
      rw [amalgEquiv_inr S g hS hv' hvg]
      exact (amalgEmbG_apply_ne (F.restrict S) (F.restrict Sᶜ) ⟨g, hgS⟩ ⟨g, hgT⟩ ⟨v, hv'⟩
        (fun h : (⟨v, hv'⟩ : (F.restrict Sᶜ).V) = ⟨g, hgT⟩ =>
          hvg (congrArg Subtype.val h))).symm
  ext x
  constructor
  · intro hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.1 hx
    exact Finset.mem_map.2 ⟨⟨v, he' v hv⟩, Finset.mem_subtype.2 hv, (key v (he' v hv)).symm⟩
  · intro hx
    obtain ⟨⟨v, hvT⟩, hv, rfl⟩ := Finset.mem_map.1 hx
    exact Finset.mem_map.2 ⟨v, Finset.mem_subtype.1 hv, key v hvT⟩

theorem recon_amalg
    (hcov : ∀ v : F.V, IncS S v ∨ (∃ e ∈ Sᶜ, v ∈ e.1))
    (hsep : ∀ v : F.V, IncS S v → (∃ e ∈ Sᶜ, v ∈ e.1) → v = g)
    (hgS : IncS S g) (hgT : ∃ e ∈ Sᶜ, g ∈ e.1) :
    FTS.Iso F (FTS.amalgamate (F.restrict S) (F.restrict Sᶜ) ⟨g, hgS⟩ ⟨g, hgT⟩) := by
  refine ⟨amalgEquiv S g hcov hsep hgS hgT, fun e => ?_⟩
  refine Iff.trans ?_ (FTS.mem_amalgamate_edges_emb _ _ _ _
    (e.map (amalgEquiv S g hcov hsep hgS hgT).toEmbedding)).symm
  constructor
  · intro he
    by_cases h : ⟨e, he⟩ ∈ S
    · exact Or.inl ⟨Finset.subtype (fun v => IncS S v) e,
        FTS.mem_restrict_edges.mpr ⟨⟨e, he⟩, h, rfl⟩,
        (amalgEquiv_map_left (hcov := hcov) (hsep := hsep) (hgS := hgS) (hgT := hgT) S g
          (fun v hv => ⟨⟨e, he⟩, h, hv⟩)).symm⟩
    · exact Or.inr ⟨Finset.subtype (fun v => ∃ e' ∈ Sᶜ, v ∈ e'.1) e,
        FTS.mem_restrict_edges.mpr ⟨⟨e, he⟩, Finset.mem_compl.mpr h, rfl⟩,
        (amalgEquiv_map_amalg (hcov := hcov) (hsep := hsep) (hgS := hgS) (hgT := hgT) S g
          (fun v hv => ⟨⟨e, he⟩, Finset.mem_compl.mpr h, hv⟩)).symm⟩
  · rintro (⟨a, ha, ha'⟩ | ⟨a, ha, ha'⟩)
    · obtain ⟨e₀, he₀, rfl⟩ := FTS.mem_restrict_edges.mp ha
      have h_eq := (amalgEquiv_map_left (hcov := hcov) (hsep := hsep) (hgS := hgS) (hgT := hgT)
        S g (fun v hv => ⟨e₀, he₀, hv⟩)).trans ha'
      rw [← Finset.map_injective _ h_eq]
      exact e₀.2
    · obtain ⟨e₀, he₀, rfl⟩ := FTS.mem_restrict_edges.mp ha
      have h_eq := (amalgEquiv_map_amalg (hcov := hcov) (hsep := hsep) (hgS := hgS) (hgT := hgT)
        S g (fun v hv => ⟨e₀, he₀, hv⟩)).trans ha'
      rw [← Finset.map_injective _ h_eq]
      exact e₀.2

end Erdos593
end

-- DecompDichotomy
section
open Cardinal

namespace Erdos593

open Classical

universe u


variable {F : FTS}

set_option maxHeartbeats 2000000 in
def ShareOff (w : F.V) (a b : {e : Finset F.V // e ∈ F.edges}) : Prop :=
  ∃ v, v ≠ w ∧ v ∈ a.1 ∧ v ∈ b.1

set_option maxHeartbeats 2000000 in
def EReach (w : F.V) : {e : Finset F.V // e ∈ F.edges} → {e : Finset F.V // e ∈ F.edges} → Prop :=
  Relation.ReflTransGen (ShareOff w)

set_option maxHeartbeats 2000000 in
theorem chain_shortcut {α : Type*} {R : α → α → Prop} (L : List α)
    (hchain : List.IsChain R L) (i j : ℕ) (hi : i < L.length) (hj : j < L.length)
    (hij : i < j) (hR : R (L.get ⟨i, hi⟩) (L.get ⟨j, hj⟩)) :
    ∃ L' : List α, L'.head? = L.head? ∧ L'.getLast? = L.getLast? ∧
      List.IsChain R L' ∧ L'.length = i + 1 + (L.length - j) := by
  refine' ⟨ L.take ( i + 1 ) ++ L.drop j, _, _, _, _ ⟩ <;> simp_all +decide [ List.isChain_append ];
  · cases L <;> simp_all +decide [ List.take ];
    contradiction;
  · rw [ List.getLast?_drop ];
    grind;
  · refine' ⟨ hchain.take _, hchain.drop _, _ ⟩;
    grind

set_option maxHeartbeats 2000000 in
theorem exists_chain_list (w : F.V) (a b : {e : Finset F.V // e ∈ F.edges})
    (hab : EReach w a b) :
    ∃ L : List {e : Finset F.V // e ∈ F.edges},
      L.head? = some a ∧ L.getLast? = some b ∧ List.IsChain (ShareOff w) L := by
  revert hab;
  intro hab
  induction' hab with c hc ih;
  · exact ⟨ [ a ], rfl, rfl, List.isChain_singleton _ ⟩;
  · obtain ⟨ L, hL₁, hL₂, hL₃ ⟩ := ‹_›; use L ++ [ hc ] ; simp_all +decide [ List.isChain_append ] ;

set_option maxHeartbeats 2000000 in
theorem onBergeCycle_of_cycle_data (w : F.V) {m : ℕ} (hm : 2 ≤ m)
    (g : ZMod m → {e : Finset F.V // e ∈ F.edges})
    (v : ZMod m → F.V)
    (hg : Function.Injective g) (hv : Function.Injective v)
    (hmem1 : ∀ i, v i ∈ (g i).1)
    (hmem2 : ∀ i, v (i + 1) ∈ (g i).1)
    (e0 : {e : Finset F.V // e ∈ F.edges}) (hg0 : g 0 = e0) (hv0 : v 0 = w) :
    OnBergeCycle F w e0 :=
  ⟨{ m := m, hm := hm, v := v, e := g, vinj := hv, einj := hg,
      mem_left := hmem1, mem_right := hmem2 }, 0, hg0, Or.inl hv0⟩

set_option maxHeartbeats 2000000 in
theorem exists_minimal_chain (w : F.V)
    (e0 f : {e : Finset F.V // e ∈ F.edges})
    (hne : e0 ≠ f) (hreach : EReach w e0 f) :
    ∃ L : List {e : Finset F.V // e ∈ F.edges},
      L.head? = some e0 ∧ L.getLast? = some f ∧ List.IsChain (ShareOff w) L ∧
      2 ≤ L.length ∧ L.Nodup ∧
      (∀ i j (hi : i < L.length) (hj : j < L.length), i + 2 ≤ j →
        ¬ ShareOff w (L.get ⟨i, hi⟩) (L.get ⟨j, hj⟩)) := by
  obtain ⟨L, hL⟩ : ∃ L : List {e : Finset F.V // e ∈ F.edges},
    L.head? = some e0 ∧ L.getLast? = some f ∧ List.IsChain (ShareOff w) L ∧ ∀ L' : List {e : Finset F.V // e ∈ F.edges}, L'.head? = some e0 ∧ L'.getLast? = some f ∧ List.IsChain (ShareOff w) L' → L.length ≤ L'.length := by
      have h_exists_min : ∃ n, n ∈ {n : ℕ | ∃ L : List {e : Finset F.V // e ∈ F.edges}, L.head? = some e0 ∧ L.getLast? = some f ∧ List.IsChain (ShareOff w) L ∧ L.length = n} := by
        exact Exists.elim ( exists_chain_list w e0 f hreach ) fun L hL => ⟨ _, ⟨ L, hL.1, hL.2.1, hL.2.2, rfl ⟩ ⟩;
      obtain ⟨ n, hn ⟩ := Nat.findX h_exists_min;
      rcases hn.1 with ⟨ L, hL₁, hL₂, hL₃, rfl ⟩ ; exact ⟨ L, hL₁, hL₂, hL₃, fun L' hL' => not_lt.1 fun contra => hn.2 _ contra ⟨ L', hL'.1, hL'.2.1, hL'.2.2, rfl ⟩ ⟩ ;

  use L;
  refine' ⟨ hL.1, hL.2.1, hL.2.2.1, _, _, _ ⟩;
  · rcases L with ( _ | ⟨ x, _ | ⟨ y, L ⟩ ⟩ ) <;> simp_all +decide;
    grind;
  · by_contra h_dup;
    obtain ⟨i, j, hij, h_eq⟩ : ∃ i j : Fin L.length, i < j ∧ L.get i = L.get j := by
      rw [ List.nodup_iff_injective_get ] at h_dup;
      obtain ⟨ i, j, hij, h ⟩ := Function.not_injective_iff.mp h_dup; cases lt_trichotomy i j <;> tauto;
    obtain ⟨v, hv⟩ : ∃ v : F.V, v ≠ w ∧ v ∈ (L.get i).1 ∧ v ∈ (L.get j).1 := by
      have := F.card3 ( L.get i |>.1 ) ( L.get i |>.2 );
      exact Exists.imp ( by aesop ) ( Finset.exists_mem_ne ( show 1 < Finset.card ( L.get i |>.1 ) from by linarith ) w );
    by_cases h_cases : j.val = i.val + 1;
    · by_cases h_cases2 : j.val + 1 < L.length;
      · have h_chain : ShareOff w (L.get ⟨i.val, by
          exact i.2⟩) (L.get ⟨i.val + 2, by
          grind⟩) := by
          have := hL.2.2.1; simp_all +decide [ List.isChain_iff_getElem ] ;
        generalize_proofs at *;
        obtain ⟨ L', hL' ⟩ := chain_shortcut L hL.2.2.1 i ( i + 2 ) ( by linarith ) ( by linarith ) ( by linarith ) h_chain;
        grind;
      · have h_contra : L.take (L.length - 1) = L.take (i.val + 1) ∧ L.take (i.val + 1) ≠ L := by
          grind;
        have h_contra : L.take (L.length - 1) = L.take (i.val + 1) ∧ L.take (i.val + 1) ≠ L ∧ List.IsChain (ShareOff w) (L.take (i.val + 1)) ∧ (L.take (i.val + 1)).head? = some e0 ∧ (L.take (i.val + 1)).getLast? = some f := by
          refine' ⟨ h_contra.1, h_contra.2, _, _, _ ⟩;
          · exact hL.2.2.1.take _;
          · cases L <;> aesop;
          · grind;
        have := hL.2.2.2 ( List.take ( i.val + 1 ) L ) ⟨ h_contra.2.2.2.1, h_contra.2.2.2.2, h_contra.2.2.1 ⟩ ; simp_all +decide ;
    · have := chain_shortcut L hL.2.2.1 i j ( by simp ) ( by simp ) ( by simpa [ Fin.ext_iff ] using hij ) ( by
        exact ⟨ v, hv.1, hv.2.1, hv.2.2 ⟩ );
      obtain ⟨L', h1, h2, h3, h4⟩ := this
      have hle := hL.2.2.2 L' ⟨h1.trans hL.1, h2.trans hL.2.1, h3⟩
      have hij' : (i : ℕ) < j := hij
      have hj := j.2
      omega
  · intro i j hi hj hij hR
    obtain ⟨L', h1, h2, h3, h4⟩ := chain_shortcut L hL.2.2.1 i j hi hj (by omega) hR
    have hle := hL.2.2.2 L' ⟨h1.trans hL.1, h2.trans hL.2.1, h3⟩
    omega

set_option maxHeartbeats 2000000 in
theorem chain_get_shareoff {w : F.V} {L : List {e : Finset F.V // e ∈ F.edges}}
    (hchain : List.IsChain (ShareOff w) L) {k : ℕ} (h : k + 1 < L.length) :
    ShareOff w (L.get ⟨k, by omega⟩) (L.get ⟨k + 1, h⟩) :=
  List.isChain_iff_getElem.mp hchain k h

set_option maxHeartbeats 2000000 in
theorem zmod_val_sub_one {m : ℕ} [NeZero m] (i : ZMod m) (h : i ≠ 0) :
    (i - 1).val = i.val - 1 := by
  by_cases hi : i.val = 0;
  · exact False.elim <| h <| by rw [ ← ZMod.natCast_zmod_val i, hi ] ; norm_num;
  · have h_val : (i - 1 : ZMod m) = (i.val - 1 : ℕ) := by
      simp +decide [ Nat.cast_sub ( Nat.one_le_iff_ne_zero.mpr hi ) ];
    rw [ h_val, ZMod.val_cast_of_lt ];
    exact lt_of_le_of_lt ( Nat.pred_le _ ) ( ZMod.val_lt i )

set_option maxHeartbeats 2000000 in
theorem cycle_data_of_ereach (hlin : F.Linear) (w : F.V)
    (e0 f : {e : Finset F.V // e ∈ F.edges}) (hwe0 : w ∈ e0.1) (hwf : w ∈ f.1)
    (hne : e0 ≠ f) (hreach : EReach w e0 f) :
    ∃ (m : ℕ) (_ : 2 ≤ m)
      (g : ZMod m → {e : Finset F.V // e ∈ F.edges}) (v : ZMod m → F.V),
      Function.Injective g ∧ Function.Injective v ∧
      (∀ i, v i ∈ (g i).1) ∧ (∀ i, v (i + 1) ∈ (g i).1) ∧
      g 0 = e0 ∧ v 0 = w := by

  obtain ⟨L, hhead, hlast, hchain, h2, hnodup, hnochord⟩ := exists_minimal_chain w e0 f hne hreach
  set m := L.length
  haveI : NeZero m := ⟨by omega⟩;

  set g : ZMod m → {e : Finset F.V // e ∈ F.edges} := fun i => L.get ⟨i.val, ZMod.val_lt i⟩
  have hg0 : g 0 = e0 := by
    cases L <;> aesop
  have g_last : g (0 - 1) = f := by
    convert hlast using 1;
    rw [ List.getLast?_eq_getElem? ];
    simp +zetaDelta at *;
    rcases L with ( _ | ⟨ _, _ | L ⟩ ) <;> norm_num at *
  have hg_inj : Function.Injective g := by
    intro i j hij; have := List.nodup_iff_injective_get.mp hnodup; simp_all +decide ;
    exact ZMod.val_injective m <| by have := List.nodup_iff_injective_get.mp hnodup; have := @this ⟨ i.val, ZMod.val_lt i ⟩ ⟨ j.val, ZMod.val_lt j ⟩ ; aesop;

  have hshare : ∀ i : ZMod m, ∃ x : F.V, x ∈ (g (i - 1)).1 ∧ x ∈ (g i).1 := by
    intro i
    by_cases hi : i = 0;
    · grind;
    · have hcons : ShareOff w (g (i - 1)) (g i) := by
        convert chain_get_shareoff hchain _;
        · rw [ zmod_val_sub_one ];
          · rw [ Nat.sub_add_cancel ( Nat.pos_of_ne_zero ( by simpa [ ZMod.val_eq_zero ] using hi ) ) ];
          · exact hi;
        · rw [ zmod_val_sub_one ];
          · rw [ Nat.sub_add_cancel ( Nat.pos_of_ne_zero ( by simpa [ ZMod.val_eq_zero ] using hi ) ) ] ; exact ZMod.val_lt i;
          · exact hi;
      exact ⟨ hcons.choose, hcons.choose_spec.2.1, hcons.choose_spec.2.2 ⟩;
  choose v hv_prev hv_cur using hshare;

  have huniq : ∀ i : ZMod m, ∀ y : F.V, y ∈ (g (i - 1)).1 → y ∈ (g i).1 → y = v i := by
    intros i y hy_prev hy_cur
    have h_inter : ((g (i - 1)).1 ∩ (g i).1).card ≤ 1 := by
      apply hlin;
      · exact g _ |>.2;
      · exact g i |>.2;
      · intro h; have := hg_inj ( Subtype.ext h ) ; simp_all +decide ;
    contrapose! h_inter;
    exact Finset.one_lt_card.mpr ⟨ y, by aesop, v i, by aesop ⟩;
  refine' ⟨ m, h2, g, v, hg_inj, _, hv_cur, _, hg0, _ ⟩;
  ·
    intro i j hij
    by_cases hp : v i = w;
    ·
      have hk_zero : ∀ k : ZMod m, v k = w → k = 0 := by
        intro k hk
        by_contra hk_ne_zero;
        obtain ⟨ x, hx ⟩ := chain_get_shareoff hchain ( show k.val - 1 + 1 < L.length from by
                                                          rw [ Nat.sub_add_cancel ];
                                                          · exact ZMod.val_lt k;
                                                          · exact Nat.pos_of_ne_zero ( by simpa [ ZMod.val_eq_zero ] using hk_ne_zero ) );
        have hpos : 1 ≤ k.val :=
          Nat.pos_of_ne_zero ( by simpa [ ZMod.val_eq_zero ] using hk_ne_zero )
        have hk1 : (k - 1).val = k.val - 1 := zmod_val_sub_one k hk_ne_zero
        have hkl : k.val < L.length := ZMod.val_lt k
        have hga : g (k - 1) = L.get ⟨k.val - 1, by omega⟩ :=
          congrArg L.get (Fin.ext hk1)
        have hgb : g k = L.get ⟨k.val - 1 + 1, by omega⟩ :=
          congrArg L.get (Fin.ext (Nat.sub_add_cancel hpos).symm)
        rw [← hga, ← hgb] at hx
        exact hx.1 ((huniq k x hx.2.1 hx.2.2).trans hk)
      rw [ hk_zero i hp, hk_zero j ( hij ▸ hp ) ];
    ·
      wlog hij' : i.val < j.val generalizing i j;
      · by_cases hij'' : j.val < i.val;
        · exact Eq.symm ( this ( hij.symm ) ( by simpa [ hij ] using hp ) hij'' );
        · exact ZMod.val_injective m ( le_antisymm ( le_of_not_gt hij'' ) ( le_of_not_gt hij' ) );
      ·
        set a := i.val - 1
        set b := j.val
        have hab : a + 2 ≤ b := by
          by_cases hi : i = 0;
          · grind +revert;
          · linarith [ Nat.sub_add_cancel ( show 1 ≤ i.val from Nat.pos_of_ne_zero ( by simpa [ ZMod.val_eq_zero ] using hi ) ) ];

        have hp_a : v i ∈ (L.get ⟨a, by
          exact lt_of_le_of_lt ( Nat.sub_le _ _ ) ( ZMod.val_lt i )⟩).1 := by
          convert hv_prev i using 1;
          congr! 2;
          simp +zetaDelta at *;
          rw [ zmod_val_sub_one ];
          rintro rfl; simp_all +decide;
          specialize huniq 0 w ; simp_all +decide [ ZMod.val ];
          exact hp ( huniq ( by cases L <;> aesop ) ▸ rfl )
        have hp_b : v i ∈ (L.get ⟨b, by
          grind⟩).1 := by
          grind
        generalize_proofs at *;
        exact False.elim <| hnochord a b ‹_› ‹_› hab ⟨ v i, hp, hp_a, hp_b ⟩;
  · intro i; specialize hv_prev ( i + 1 ) ; specialize hv_cur ( i + 1 ) ; aesop;
  · exact (huniq 0 w (by rw [g_last]; exact hwf) (by rw [hg0]; exact hwe0)).symm

set_option maxHeartbeats 2000000 in
theorem bridge_ereach_false (hlin : F.Linear) (w : F.V)
    (e0 f : {e : Finset F.V // e ∈ F.edges}) (hwe0 : w ∈ e0.1) (hwf : w ∈ f.1)
    (hne : e0 ≠ f) (hbr : ¬ OnBergeCycle F w e0) : ¬ EReach w e0 f := by
  intro hreach
  obtain ⟨m, hm, g, v, hg, hv, hmem1, hmem2, hg0, hv0⟩ :=
    cycle_data_of_ereach hlin w e0 f hwe0 hwf hne hreach
  exact hbr (onBergeCycle_of_cycle_data w hm g v hg hv hmem1 hmem2 e0 hg0 hv0)

end Erdos593
end

-- DecompExpansion
section
open Cardinal

namespace Erdos593

open Classical

universe u


variable {F : FTS}

set_option maxHeartbeats 2000000 in
theorem walk_split_at {V : Type*} {G : SimpleGraph V} {u v : V} (w : G.Walk u v)
    (k : ℕ) (hk : k ≤ w.length) :
    ∃ (w1 : G.Walk u (w.getVert k)) (w2 : G.Walk (w.getVert k) v),
      w = w1.append w2 ∧ w1.length = k := by
  induction w generalizing k with
  | nil => exact ⟨SimpleGraph.Walk.nil, SimpleGraph.Walk.nil, rfl, (Nat.le_zero.mp hk).symm⟩
  | cons h p ih =>
    cases k with
    | zero => exact ⟨SimpleGraph.Walk.nil, SimpleGraph.Walk.cons h p, rfl, rfl⟩
    | succ k =>
      rw [SimpleGraph.Walk.length_cons] at hk
      obtain ⟨w1, w2, hw, hl⟩ := ih k (by omega)
      refine ⟨SimpleGraph.Walk.cons h w1, w2, ?_, ?_⟩
      · exact (congrArg (SimpleGraph.Walk.cons h) hw).trans rfl
      · exact congrArg (· + 1) hl

set_option maxHeartbeats 2000000 in
theorem walk_vertex_repeat {V : Type*} {G : SimpleGraph V} {v : V} (w : G.Walk v v)
    (hcyc : ¬ w.IsCycle) (hlen : 3 ≤ w.length) :
    ∃ i j, i < j ∧ j < w.length ∧ w.getVert i = w.getVert j := by
  have h_not_path : ¬ w.tail.IsPath := by
    grind [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length];

  obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, 1 ≤ a ∧ a < b ∧ b ≤ w.length ∧ w.getVert a = w.getVert b := by
    contrapose! h_not_path;
    have h_tail_nodup : List.Nodup (List.tail (w.support)) := by
      rw [ List.nodup_iff_getElem?_ne_getElem? ];
      grind [List.length_tail, List.getElem?_tail, SimpleGraph.Walk.length_support, getElem?_pos, SimpleGraph.Walk.support_getElem_eq_getVert];
    convert h_tail_nodup using 1;
    simp +decide [ SimpleGraph.Walk.isPath_def ];
    cases w <;> simp +decide [ SimpleGraph.Walk.support ];
  by_cases hb : b = w.length;
  · aesop;
  · exact ⟨ a, b, hab.2.1, lt_of_le_of_ne hab.2.2.1 hb, hab.2.2.2 ⟩

set_option maxHeartbeats 2000000 in
theorem exists_odd_cycle_aux {V : Type*} (G : SimpleGraph V) (n : ℕ) :
    ∀ (v : V) (w : G.Walk v v), w.length = n → Odd n →
      ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ Odd c.length := by
  intro v w hw hn_odd
  induction' n using Nat.strong_induction_on with n ih generalizing v w;
  by_cases hw_cycle : w.IsCycle;
  · exact ⟨ v, w, hw_cycle, hw ▸ hn_odd ⟩;
  ·
    obtain ⟨i, j, hij, hjn, hx⟩ : ∃ i j, i < j ∧ j < n ∧ w.getVert i = w.getVert j := by
      convert walk_vertex_repeat w hw_cycle _;
      · exact hw.symm;
      · rcases w with ( _ | ⟨ _, _, w ⟩ ) <;> simp_all +decide;
        · grind +extAll;
        · exact absurd ‹G.Adj v v› ( by simp +decide );
        · rcases n with ( _ | _ | _ | n ) <;> simp_all +arith +decide;

    obtain ⟨w1, w2, hw1, hw2⟩ : ∃ w1 : G.Walk v (w.getVert i), ∃ w2 : G.Walk (w.getVert i) v, w = w1.append w2 ∧ w1.length = i := by
      exact walk_split_at w i ( by linarith )
    obtain ⟨c₁, w3, hc₁, hw3⟩ : ∃ c₁ : G.Walk (w.getVert i) (w.getVert i), ∃ w3 : G.Walk (w.getVert i) v, w2 = c₁.append w3 ∧ c₁.length = j - i := by
      have := walk_split_at w2 ( j - i ) ( by
        have := congr_arg SimpleGraph.Walk.length hw1; norm_num at this; omega; );
      grind [SimpleGraph.Walk.getVert_append];

    set c₂ : G.Walk (w.getVert i) (w.getVert i) := w3.append w1
    have hc₂ : c₂.length = n - (j - i) := by
      simp +zetaDelta at *;
      simp_all +decide [ SimpleGraph.Walk.length_append ];
      omega
    have hc₁_odd : Odd c₁.length ∨ Odd c₂.length := by
      grind +qlia
    generalize_proofs at *;
    grind

set_option maxHeartbeats 2000000 in
theorem colorable_two_of_cycle_even {V : Type*} (G : SimpleGraph V)
    (h : ∀ (v : V) (c : G.Walk v v), c.IsCycle → Even c.length) : G.Colorable 2 := by
  rw [SimpleGraph.two_colorable_iff_forall_loop_even]
  intro u w
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  obtain ⟨x, c, hc, hcodd⟩ := exists_odd_cycle_aux G w.length u w rfl hodd
  exact (Nat.not_odd_iff_even.mpr (h x c hc)) hcodd

set_option maxHeartbeats 2000000 in
theorem decomp_amalg (h : ReconOK F)
    (ed : {e : Finset F.V // e ∈ F.edges}) (w : F.V) (hbrid : IsBridgeInc F w ed)
    (f : {e : Finset F.V // e ∈ F.edges}) (hfne : f ≠ ed) (hwf : w ∈ f.1) :
    ∃ (F₁ F₂ : FTS) (x : F₁.V) (y : F₂.V),
        F₁.edges.card < F.edges.card ∧ F₂.edges.card < F.edges.card ∧
        ReconOK F₁ ∧ ReconOK F₂ ∧ FTS.Iso F (F₁.amalgamate F₂ x y) := by
  obtain ⟨hlin, hno_iso, hbrEx, hev⟩ := h;

  set S : Finset {e : Finset F.V // e ∈ F.edges} := Finset.univ.filter (fun e' => EReach w ed e');

  have hgS : IncS S w := by
    exact ⟨ ed, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, Relation.ReflTransGen.refl ⟩, hbrid.1 ⟩
  have hgT : ∃ e ∈ Sᶜ, w ∈ e.1 := by
    use f;
    simp +zetaDelta at *;
    exact ⟨ bridge_ereach_false hlin w ed f hbrid.1 hwf ( Ne.symm hfne ) hbrid.2, hwf ⟩
  have hcov : ∀ v : F.V, IncS S v ∨ (∃ e ∈ Sᶜ, v ∈ e.1) := by
    intro v; specialize hno_iso v; simp_all +decide [ FTS.Isolated ] ;
    grind
  have hsep : ∀ v : F.V, IncS S v → (∃ e ∈ Sᶜ, v ∈ e.1) → v = w := by
    intro v hv hv'; obtain ⟨ a, ha, hv ⟩ := hv; obtain ⟨ b, hb, hv' ⟩ := hv'; simp_all +decide [ IncS ] ;
    contrapose! hb;
    exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, Relation.ReflTransGen.tail ( Finset.mem_filter.mp ha |>.2 ) ⟨ v, hb, hv, hv' ⟩ ⟩;
  refine' ⟨ F.restrict S, F.restrict Sᶜ, ⟨ w, hgS ⟩, ⟨ w, hgT ⟩, _, _, _, _, recon_amalg S w hcov hsep hgS hgT ⟩;
  · rw [ FTS.restrict_edges_card ];
    refine' lt_of_lt_of_le ( Finset.card_lt_card ( Finset.filter_ssubset.mpr _ ) ) _;
    · exact ⟨ f, Finset.mem_univ _, fun h => bridge_ereach_false hlin w ed f hbrid.1 hwf ( Ne.symm hfne ) hbrid.2 h ⟩;
    · simp +decide;
  · rw [ FTS.restrict_edges_card ];
    rw [ Finset.card_compl ];
    rw [ Fintype.card_coe ];
    exact Nat.sub_lt ( Finset.card_pos.mpr ⟨ _, ed.2 ⟩ ) ( Finset.card_pos.mpr ⟨ _, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, Relation.ReflTransGen.refl ⟩ ⟩ );
  · exact FTS.restrict_reconOK S hlin hbrEx hev;
  · apply FTS.restrict_reconOK;
    · assumption;
    · exact hbrEx;
    · exact hev

set_option maxHeartbeats 2000000 in
abbrev CoreV (F : FTS) (pr : {e : Finset F.V // e ∈ F.edges} → F.V) : Type :=
  {v : F.V // ∀ ed, pr ed ≠ v}

set_option maxHeartbeats 2000000 in
noncomputable instance instFintypeCoreV (F : FTS)
    (pr : {e : Finset F.V // e ∈ F.edges} → F.V) : Fintype (CoreV F pr) :=
  Fintype.ofFinite _

set_option maxHeartbeats 2000000 in
instance instDecEqCoreV (F : FTS)
    (pr : {e : Finset F.V // e ∈ F.edges} → F.V) : DecidableEq (CoreV F pr) :=
  Subtype.instDecidableEq

set_option maxHeartbeats 2000000 in
def coreGraph (F : FTS) (pr : {e : Finset F.V // e ∈ F.edges} → F.V) :
    SimpleGraph (CoreV F pr) where
  Adj a b := (a : F.V) ≠ (b : F.V) ∧
    ∃ ed : {e : Finset F.V // e ∈ F.edges}, (a : F.V) ∈ ed.1 ∧ (b : F.V) ∈ ed.1
  symm := ⟨by rintro a b ⟨h1, ed, h2, h3⟩; exact ⟨h1.symm, ed, h3, h2⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

set_option maxHeartbeats 2000000 in
noncomputable instance instDecRelCoreGraph (F : FTS)
    (pr : {e : Finset F.V // e ∈ F.edges} → F.V) :
    DecidableRel (coreGraph F pr).Adj :=
  fun _ _ => Classical.dec _

set_option maxHeartbeats 2000000 in
theorem cycle_getVert_inj {V : Type*} {G : SimpleGraph V} {x : V} {c : G.Walk x x}
    (hc : c.IsCycle) {i j : ℕ} (hi : i < c.length) (hj : j < c.length)
    (h : c.getVert i = c.getVert j) : i = j := by
  have h_tail_nodup : List.Nodup (c.support.tail) := by
    exact hc.support_nodup;
  have h_tail_nodup : ∀ i j, i < c.length → j < c.length → i ≠ j → c.getVert (i + 1) ≠ c.getVert (j + 1) := by
    intro i j hi hj hij;
    have := List.nodup_iff_injective_get.mp h_tail_nodup;
    have := @this ⟨ i, by
      grind ⟩ ⟨ j, by
      simp +decide [ hj ] ⟩ ; simp_all +decide
    generalize_proofs at *;
    grind [SimpleGraph.Walk.getVert_eq_support_getElem];
  rcases i with ( _ | i ) <;> rcases j with ( _ | j ) <;> simp_all +decide;
  · specialize h_tail_nodup j ( c.length - 1 ) ( by linarith ) ( by omega ) ( by omega ) ; simp_all +decide [ Nat.sub_add_cancel hi ];
  · grind [SimpleGraph.Walk.IsCycle.getVert_endpoint_iff];
  · exact Classical.not_not.1 fun h' => h_tail_nodup i j ( Nat.lt_of_succ_lt hi ) ( Nat.lt_of_succ_lt hj ) h' h

set_option maxHeartbeats 2000000 in
theorem coreGraph_colorable (F : FTS) (pr : {e : Finset F.V // e ∈ F.edges} → F.V)
    (hpm : ∀ ed, pr ed ∈ ed.1)
    (hev : ∀ c : BergeCycle F, Even c.m) : (coreGraph F pr).Colorable 2 := by
  apply colorable_two_of_cycle_even;
  intro v c hc
  set m := c.length with hm
  have hm3 : 3 ≤ m := by
    exact hc.three_le_length
  have : NeZero m := ⟨by omega⟩
  generalize_proofs at *;

  obtain ⟨v', e', hv', he'⟩ : ∃ (v' : ZMod m → F.V) (e' : ZMod m → {e : Finset F.V // e ∈ F.edges}),
    (∀ i, v' i = (c.getVert i.val : F.V)) ∧
    (∀ i, v' i ∈ (e' i).1 ∧ v' (i + 1) ∈ (e' i).1) := by
      have h_adj : ∀ i : ZMod m, (coreGraph F pr).Adj (c.getVert i.val) (c.getVert ((i.val + 1) % m)) := by
        intro i
        have h_adj : (coreGraph F pr).Adj (c.getVert i.val) (c.getVert (i.val + 1)) := by
          convert c.adj_getVert_succ _ using 1
          generalize_proofs at *;
          exact i.val_lt
        generalize_proofs at *;
        cases eq_or_ne ( i.val + 1 ) m <;> simp_all +decide;
        rwa [ Nat.mod_eq_of_lt ( lt_of_le_of_ne ( Nat.succ_le_of_lt ( show i.val < c.length from i.val_lt ) ) ‹_› ) ];
      choose e' he' using fun i => h_adj i |>.2;
      haveI : Fact (1 < m) := ⟨by omega⟩
      refine ⟨fun i => (c.getVert i.val : F.V), e', fun i => rfl, fun i => ⟨(he' i).1, ?_⟩⟩
      have hval : (i + 1 : ZMod m).val = (i.val + 1) % m := by
        rw [ZMod.val_add, ZMod.val_one]
      simp only [hval]
      exact (he' i).2

  have hv'_inj : Function.Injective v' := by
    intro i j hij
    have h_eq : c.getVert i.val = c.getVert j.val := by
      exact Subtype.ext <| by simpa [ hv' ] using hij;
    have h_eq' : i.val = j.val := by
      apply cycle_getVert_inj hc (ZMod.val_lt i) (ZMod.val_lt j) h_eq
    have h_eq'' : i = j := by
      exact ZMod.val_injective m h_eq'
    exact h_eq''
  have he'_inj : Function.Injective e' := by
    intro i j hij
    have h_core : (e' i).1.erase (pr (e' i)) = {v' i, v' (i + 1)} ∧ (e' j).1.erase (pr (e' j)) = {v' j, v' (j + 1)} := by
      have h_core : ∀ i, (e' i).1.erase (pr (e' i)) ⊇ {v' i, v' (i + 1)} := by
        grind +revert;
      have h_core_card : ∀ i, ((e' i).1.erase (pr (e' i))).card = 2 := by
        intro i; rw [ Finset.card_erase_of_mem ( hpm _ ) ] ; simp +decide [ F.card3 _ ( e' i |>.2 ) ] ;
      have h_core_eq : ∀ i, {v' i, v' (i + 1)} = (e' i).1.erase (pr (e' i)) := by
        intros i
        apply Finset.eq_of_subset_of_card_le (h_core i);
        rw [ h_core_card i, Finset.card_insert_of_notMem, Finset.card_singleton ] ; simp +decide [ hv'_inj.eq_iff ];
        exact by haveI := Fact.mk ( by linarith : 1 < m ) ; exact by simp +decide ;
      exact ⟨ h_core_eq i ▸ rfl, h_core_eq j ▸ rfl ⟩;
    have h_core_eq : v' j ∈ ({v' i, v' (i + 1)} : Finset F.V) ∧ v' (j + 1) ∈ ({v' i, v' (i + 1)} : Finset F.V) := by
      grind;
    simp_all +decide;
    cases h_core_eq.1 <;> cases h_core_eq.2 <;> simp_all +decide;
    · grind;
    · grind;
    · have h_contra : (i + 1 + 1 : ZMod m) = i := by
        grind;
      norm_num [ add_assoc ] at h_contra;
      erw [ ZMod.natCast_eq_zero_iff ] at h_contra ; have := Nat.le_of_dvd ( by linarith ) h_contra ; linarith;
    · grind [Finset.insert_eq_of_mem, Finset.mem_erase, Finset.mem_singleton];
  exact hev ⟨ m, by linarith, v', e', hv'_inj, he'_inj, fun i => he' i |>.1, fun i => he' i |>.2 ⟩

set_option maxHeartbeats 2000000 in
theorem edge_core_structure (F : FTS) (pr : {e : Finset F.V // e ∈ F.edges} → F.V)
    (hpm : ∀ ed, pr ed ∈ ed.1)
    (hpu : ∀ ed, ∀ g ∈ F.edges, pr ed ∈ g → g = ed.1)
    (ed : {e : Finset F.V // e ∈ F.edges}) :
    ∃ a b : F.V, a ≠ b ∧ (∀ g, pr g ≠ a) ∧ (∀ g, pr g ≠ b) ∧
      ed.1 = {a, b, pr ed} := by
  obtain ⟨a, b, hab⟩ : ∃ a b : F.V, a ≠ b ∧ a ∈ ed.1 ∧ b ∈ ed.1 ∧ a ≠ pr ed ∧ b ≠ pr ed ∧ ed.1 = {a, b, pr ed} := by
    obtain ⟨a, b, hab⟩ : ∃ a b : F.V, a ≠ b ∧ a ∈ ed.1 ∧ b ∈ ed.1 ∧ a ≠ pr ed ∧ b ≠ pr ed := by
      have h_core : (ed.1.erase (pr ed)).card = 2 := by
        rw [ Finset.card_erase_of_mem ( hpm ed ), F.card3 _ ed.2 ];
      obtain ⟨ a, ha, b, hb, hab ⟩ := Finset.one_lt_card.1 ( by linarith ) ; use a, b; aesop;
    refine' ⟨ a, b, hab.1, hab.2.1, hab.2.2.1, hab.2.2.2.1, hab.2.2.2.2, _ ⟩;
    have h_card : ed.1.card = 3 := by
      exact F.card3 _ ed.2;
    rw [ Finset.eq_of_subset_of_card_le ( Finset.insert_subset_iff.mpr ⟨ hab.2.1, Finset.insert_subset_iff.mpr ⟨ hab.2.2.1, Finset.singleton_subset_iff.mpr ( hpm ed ) ⟩ ⟩ ) ] ; aesop;
  grind

set_option maxHeartbeats 2000000 in
theorem pr_injective (F : FTS) (pr : {e : Finset F.V // e ∈ F.edges} → F.V)
    (hpm : ∀ ed, pr ed ∈ ed.1)
    (hpu : ∀ ed, ∀ g ∈ F.edges, pr ed ∈ g → g = ed.1) :
    Function.Injective pr := by
  intro ed1 ed2 h_eq;
  grind

set_option maxHeartbeats 2000000 in
theorem core_edge_mem (F : FTS) (pr : {e : Finset F.V // e ∈ F.edges} → F.V)
    (a b : CoreV F pr) (ed : {e : Finset F.V // e ∈ F.edges})
    (hab : a ≠ b) (hae : (a : F.V) ∈ ed.1) (hbe : (b : F.V) ∈ ed.1) :
    s(a, b) ∈ (coreGraph F pr).edgeFinset := by
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  exact ⟨ Subtype.coe_injective.ne hab, ed, hae, hbe ⟩

set_option maxHeartbeats 2000000 in
theorem edge_unique_of_two (F : FTS) (hlin : F.Linear)
    {ed ed' : {e : Finset F.V // e ∈ F.edges}} {a b : F.V} (hab : a ≠ b)
    (h1 : a ∈ ed.1) (h2 : b ∈ ed.1) (h3 : a ∈ ed'.1) (h4 : b ∈ ed'.1) : ed = ed' := by
  exact Subtype.ext <| Classical.not_not.1 fun h => absurd ( hlin _ ed.2 _ ed'.2 h ) ( by exact Nat.not_le_of_gt ( Finset.one_lt_card.2 ⟨ a, by aesop, b, by aesop ⟩ ) )

set_option maxHeartbeats 2000000 in
theorem jedge_exists_edge (F : FTS) (pr : {e : Finset F.V // e ∈ F.edges} → F.V)
    (a b : CoreV F pr) (hx : s(a, b) ∈ (coreGraph F pr).edgeFinset) :
    ∃ ed : {e : Finset F.V // e ∈ F.edges}, (a : F.V) ∈ ed.1 ∧ (b : F.V) ∈ ed.1 := by
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hx
  obtain ⟨_, ed, h1, h2⟩ := hx
  exact ⟨ed, h1, h2⟩

set_option maxHeartbeats 2000000 in
theorem exists_expEquiv (F : FTS) (pr : {e : Finset F.V // e ∈ F.edges} → F.V)
    (hlin : F.Linear) (hpm : ∀ ed, pr ed ∈ ed.1)
    (hpu : ∀ ed, ∀ g ∈ F.edges, pr ed ∈ g → g = ed.1) :
    ∃ (φ : F.V ≃ (graphExpansion (coreGraph F pr)).V)
      (A B : {e : Finset F.V // e ∈ F.edges} → CoreV F pr),
      (∀ ed, A ed ≠ B ed) ∧
      (∀ ed, ed.1 = {(A ed : F.V), (B ed : F.V), pr ed}) ∧
      (∀ (v : F.V) (hv : ∀ ed, pr ed ≠ v), φ v = Sum.inl ⟨v, hv⟩) ∧
      (∀ ed, ∃ x : {x : Sym2 (CoreV F pr) // x ∈ (coreGraph F pr).edgeFinset},
          φ (pr ed) = Sum.inr x ∧ x.1 = s(A ed, B ed)) ∧
      (∀ x : {x : Sym2 (CoreV F pr) // x ∈ (coreGraph F pr).edgeFinset},
          ∃ ed, φ (pr ed) = Sum.inr x) := by
  classical
  have hce : ∀ ed : {e : Finset F.V // e ∈ F.edges}, ∃ a b : CoreV F pr,
      a ≠ b ∧ ed.1 = {(a : F.V), (b : F.V), pr ed} := by
    intro ed
    obtain ⟨a, b, hne, hca, hcb, hs⟩ := edge_core_structure F pr hpm hpu ed
    exact ⟨⟨a, hca⟩, ⟨b, hcb⟩, by simpa [Subtype.ext_iff] using hne, hs⟩
  choose A B hAB hset using hce
  have hmemA : ∀ ed, (A ed : F.V) ∈ ed.1 := by intro ed; rw [hset ed]; simp
  have hmemB : ∀ ed, (B ed : F.V) ∈ ed.1 := by intro ed; rw [hset ed]; simp
  have hmem : ∀ ed, s(A ed, B ed) ∈ (coreGraph F pr).edgeFinset :=
    fun ed => core_edge_mem F pr (A ed) (B ed) ed (hAB ed) (hmemA ed) (hmemB ed)
  set jE : {e : Finset F.V // e ∈ F.edges} →
      {x : Sym2 (CoreV F pr) // x ∈ (coreGraph F pr).edgeFinset} :=
    fun ed => ⟨s(A ed, B ed), hmem ed⟩ with hjEdef
  have hjE : ∀ ed, (jE ed).1 = s(A ed, B ed) := fun ed => rfl
  have hjE_inj : Function.Injective jE := by
    intro ed1 ed2 h
    have h2 : s(A ed1, B ed1) = s(A ed2, B ed2) := by
      have := congrArg Subtype.val h; rwa [hjE, hjE] at this
    rw [Sym2.eq_iff] at h2
    have hane : (A ed1 : F.V) ≠ (B ed1 : F.V) := by simpa [Subtype.ext_iff] using hAB ed1
    refine edge_unique_of_two F hlin hane (hmemA ed1) (hmemB ed1) ?_ ?_
    · rcases h2 with ⟨ha, _⟩ | ⟨ha, _⟩
      · rw [congrArg Subtype.val ha]; exact hmemA ed2
      · rw [congrArg Subtype.val ha]; exact hmemB ed2
    · rcases h2 with ⟨_, hb⟩ | ⟨_, hb⟩
      · rw [congrArg Subtype.val hb]; exact hmemB ed2
      · rw [congrArg Subtype.val hb]; exact hmemA ed2
  have hjE_surj : ∀ x : {x : Sym2 (CoreV F pr) // x ∈ (coreGraph F pr).edgeFinset},
      ∃ ed, jE ed = x := by
    intro x
    obtain ⟨P, Q, hPQ⟩ : ∃ P Q : CoreV F pr, x.1 = s(P, Q) := by
      induction x.1 using Sym2.ind with | _ P Q => exact ⟨P, Q, rfl⟩
    have hxmem : s(P, Q) ∈ (coreGraph F pr).edgeFinset := hPQ ▸ x.2
    obtain ⟨ed, hP, hQ⟩ := jedge_exists_edge F pr P Q hxmem
    have hadj := hxmem
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hadj
    have hPneQ : P ≠ Q := fun h => hadj.1 (by rw [h])
    have hPpr : (P : F.V) ≠ pr ed := (P.2 ed).symm
    have hQpr : (Q : F.V) ≠ pr ed := (Q.2 ed).symm
    have hPin : (P : F.V) = (A ed : F.V) ∨ (P : F.V) = (B ed : F.V) := by
      have := hP; rw [hset ed] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hPpr
    have hQin : (Q : F.V) = (A ed : F.V) ∨ (Q : F.V) = (B ed : F.V) := by
      have := hQ; rw [hset ed] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hQpr
    refine ⟨ed, ?_⟩
    apply Subtype.ext
    rw [hjE, hPQ, Sym2.eq_iff]
    have hPQne : (P:F.V) ≠ (Q:F.V) := fun h => hPneQ (Subtype.ext h)
    rcases hPin with hpA | hpB
    · rcases hQin with hqA | hqB
      · exact absurd (hpA.trans hqA.symm) hPQne
      · exact Or.inl ⟨(Subtype.ext hpA.symm), (Subtype.ext hqB.symm)⟩
    · rcases hQin with hqA | hqB
      · exact Or.inr ⟨Subtype.ext hqA.symm, Subtype.ext hpB.symm⟩
      · exact absurd (hpB.trans hqB.symm) hPQne
  set f : F.V → CoreV F pr ⊕ {x : Sym2 (CoreV F pr) // x ∈ (coreGraph F pr).edgeFinset} :=
    fun v => if hv : (∀ ed, pr ed ≠ v) then Sum.inl ⟨v, hv⟩
      else Sum.inr (jE (Classical.choose (not_forall.mp hv))) with hfdef
  have hf_core : ∀ (v : F.V) (hv : ∀ ed, pr ed ≠ v), f v = Sum.inl ⟨v, hv⟩ := by
    intro v hv; rw [hfdef]; simp only [dif_pos hv]
  have hf_priv : ∀ ed, f (pr ed) = Sum.inr (jE ed) := by
    intro ed
    have hv : ¬ (∀ ed', pr ed' ≠ pr ed) := fun h => h ed rfl
    rw [hfdef]; simp only [dif_neg hv]
    have hchoose : pr (Classical.choose (not_forall.mp hv)) = pr ed :=
      not_not.mp (Classical.choose_spec (not_forall.mp hv))
    rw [pr_injective F pr hpm hpu hchoose]
  have hf_bij : Function.Bijective f := by
    constructor
    · intro v w hvw
      by_cases hv : (∀ ed, pr ed ≠ v) <;> by_cases hw : (∀ ed, pr ed ≠ w)
      · rw [hf_core v hv, hf_core w hw] at hvw
        exact congrArg Subtype.val (Sum.inl.inj hvw)
      · rw [hfdef] at hvw; simp only [dif_pos hv, dif_neg hw] at hvw
        exact (Sum.inl_ne_inr hvw).elim
      · rw [hfdef] at hvw; simp only [dif_neg hv, dif_pos hw] at hvw
        exact (Sum.inl_ne_inr hvw.symm).elim
      · rw [hfdef] at hvw; simp only [dif_neg hv, dif_neg hw] at hvw
        have hh := hjE_inj (Sum.inr.inj hvw)
        have h1 : pr (Classical.choose (not_forall.mp hv)) = v :=
          not_not.mp (Classical.choose_spec (not_forall.mp hv))
        have h2 : pr (Classical.choose (not_forall.mp hw)) = w :=
          not_not.mp (Classical.choose_spec (not_forall.mp hw))
        rw [← h1, ← h2, hh]
    · intro y
      rcases y with a | x
      · exact ⟨a.1, by rw [hf_core a.1 a.2]⟩
      · obtain ⟨ed, hed⟩ := hjE_surj x
        exact ⟨pr ed, by rw [hf_priv ed, hed]⟩
  refine ⟨Equiv.ofBijective f hf_bij, A, B, hAB, hset, ?_, ?_, ?_⟩
  · intro v hv; exact hf_core v hv
  · intro ed; exact ⟨jE ed, hf_priv ed, hjE ed⟩
  · intro x; obtain ⟨ed, hed⟩ := hjE_surj x
    exact ⟨ed, by rw [← hed]; exact hf_priv ed⟩

set_option maxHeartbeats 2000000 in
theorem F_iso_expansion (F : FTS) (pr : {e : Finset F.V // e ∈ F.edges} → F.V)
    (hlin : F.Linear)
    (hpm : ∀ ed, pr ed ∈ ed.1)
    (hpu : ∀ ed, ∀ g ∈ F.edges, pr ed ∈ g → g = ed.1) :
    FTS.Iso F (graphExpansion (coreGraph F pr)) := by
  classical
  obtain ⟨φ, A, B, hAB, hset, hcore, hpr, hsurj⟩ := exists_expEquiv F pr hlin hpm hpu
  have key : ∀ (ed : {e : Finset F.V // e ∈ F.edges})
      (x : {x : Sym2 (CoreV F pr) // x ∈ (coreGraph F pr).edgeFinset}),
      φ (pr ed) = Sum.inr x → x.1 = s(A ed, B ed) →
      ed.1.map φ.toEmbedding =
        ({Sum.inl (Quot.out x.1).1, Sum.inl (Quot.out x.1).2, Sum.inr x} :
          Finset (graphExpansion (coreGraph F pr)).V) := by
    intro ed x hx hxval
    have hφA : φ (A ed : F.V) = Sum.inl (A ed) := by
      have := hcore (A ed : F.V) (A ed).2; simpa using this
    have hφB : φ (B ed : F.V) = Sum.inl (B ed) := by
      have := hcore (B ed : F.V) (B ed).2; simpa using this
    have hmkout : s((Quot.out x.1).1, (Quot.out x.1).2) = x.1 := by
      exact Quot.out_eq x.1
    have hout : (Quot.out x.1).1 = A ed ∧ (Quot.out x.1).2 = B ed ∨
        (Quot.out x.1).1 = B ed ∧ (Quot.out x.1).2 = A ed := by
      have h : s((Quot.out x.1).1, (Quot.out x.1).2) = s(A ed, B ed) := by
        rw [hmkout, hxval]
      rwa [Sym2.eq_iff] at h
    rw [hset ed, Finset.map_insert, Finset.map_insert, Finset.map_singleton]
    simp only [Equiv.coe_toEmbedding]
    rw [hφA, hφB, hx]
    rcases hout with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; rfl
    · rw [h1, h2]; exact Finset.insert_comm _ _ _
  refine ⟨φ, fun e => ⟨fun he => ?_, fun he => ?_⟩⟩
  · obtain ⟨x, hx, hxval⟩ := hpr ⟨e, he⟩
    have hk := key ⟨e, he⟩ x hx hxval
    exact Finset.mem_image.mpr ⟨x, Finset.mem_attach _ _, hk.symm⟩
  · obtain ⟨x, hxeq⟩ := expansion_edge_cases (coreGraph F pr) he
    obtain ⟨ed, hed⟩ := hsurj x
    obtain ⟨x', hx', hx'val⟩ := hpr ed
    have hxx' : x = x' := Sum.inr.inj (hed.symm.trans hx')
    have hxval : x.1 = s(A ed, B ed) := hxx' ▸ hx'val
    have hk := key ed x hed hxval
    have heq : e.map φ.toEmbedding = ed.1.map φ.toEmbedding := by rw [hxeq, ← hk]
    have he2 : e = ed.1 := Finset.map_injective φ.toEmbedding heq
    rw [he2]; exact ed.2

set_option maxHeartbeats 2000000 in
theorem exists_expansion_of_private (hlin : F.Linear)
    (hpriv : ∀ ed : {e : Finset F.V // e ∈ F.edges}, ∃ w ∈ ed.1,
      ∀ g ∈ F.edges, w ∈ g → g = ed.1)
    (hev : ∀ c : BergeCycle F, Even c.m) :
    ∃ (VJ : Type) (_ : Fintype VJ) (_ : DecidableEq VJ) (J : SimpleGraph VJ)
        (_ : DecidableRel J.Adj), J.Colorable 2 ∧ FTS.Iso F (graphExpansion J) := by
  choose pr hpm hpu using hpriv
  exact ⟨CoreV F pr, instFintypeCoreV F pr, instDecEqCoreV F pr, coreGraph F pr,
    instDecRelCoreGraph F pr, coreGraph_colorable F pr hpm hev,
    F_iso_expansion F pr hlin hpm hpu⟩

end Erdos593
end

-- DecompReverse
section
open Cardinal

namespace Erdos593

open Classical

universe u

theorem FTS.Iso.refl (F : FTS) : FTS.Iso F F :=
  ⟨Equiv.refl _, by intro e; simp⟩

theorem FTS.Iso.symm {F G : FTS} (h : FTS.Iso F G) : FTS.Iso G F := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ.symm, ?_⟩
  intro e
  rw [hφ (e.map φ.symm.toEmbedding)]
  simp [Finset.map_map]

theorem decomp_step (F : FTS) (h : ReconOK F) :
    (∃ (VJ : Type) (_ : Fintype VJ) (_ : DecidableEq VJ) (J : SimpleGraph VJ)
        (_ : DecidableRel J.Adj), J.Colorable 2 ∧ FTS.Iso F (graphExpansion J)) ∨
    (∃ F₁ F₂ : FTS, F₁.edges.card < F.edges.card ∧ F₂.edges.card < F.edges.card ∧
        ReconOK F₁ ∧ ReconOK F₂ ∧ FTS.Iso F (F₁.disjUnion F₂)) ∨
    (∃ (F₁ F₂ : FTS) (x : F₁.V) (y : F₂.V),
        F₁.edges.card < F.edges.card ∧ F₂.edges.card < F.edges.card ∧
        ReconOK F₁ ∧ ReconOK F₂ ∧ FTS.Iso F (F₁.amalgamate F₂ x y)) := by
  obtain ⟨hlin, hno_iso, hbr, hev⟩ := h
  by_cases hA : ∃ (ed : {e : Finset F.V // e ∈ F.edges}) (w : F.V),
      IsBridgeInc F w ed ∧ ∃ f : {e : Finset F.V // e ∈ F.edges}, f ≠ ed ∧ w ∈ f.1
  ·
    obtain ⟨ed, w, hbrid, f, hfne, hwf⟩ := hA
    exact Or.inr (Or.inr
      (decomp_amalg ⟨hlin, hno_iso, hbr, hev⟩ ed w hbrid f hfne hwf))
  ·
    push_neg at hA
    refine Or.inl (exists_expansion_of_private hlin ?_ hev)
    intro ed
    obtain ⟨w, hw_mem, hw_bridge⟩ := hbr ed
    refine ⟨w, hw_mem, ?_⟩
    intro g hg hwg
    by_contra hgne
    exact hA ed w hw_bridge ⟨g, hg⟩ (fun hcontra => hgne (congrArg Subtype.val hcontra)) hwg

theorem bclass_of_reconOK (F : FTS) (h : ReconOK F) : Bclass F := by

  generalize hn : F.edges.card = n
  induction n using Nat.strong_induction_on generalizing F with
  | _ n ih =>
    rcases F.edges.eq_empty_or_nonempty with hE | -
    · exact Bclass.edgeless F hE
    · rcases decomp_step F h with
        ⟨VJ, _, _, J, _, hJ, hiso⟩ | ⟨F₁, F₂, h1, h2, hr1, hr2, hiso⟩ |
        ⟨F₁, F₂, x, y, h1, h2, hr1, hr2, hiso⟩
      · exact Bclass.iso hiso.symm (Bclass.expansion J hJ)
      · subst hn
        exact Bclass.iso hiso.symm
          (Bclass.union (ih _ h1 F₁ hr1 rfl) (ih _ h2 F₂ hr2 rfl))
      · subst hn
        exact Bclass.iso hiso.symm
          (Bclass.amalg x y (ih _ h1 F₁ hr1 rfl) (ih _ h2 F₂ hr2 rfl))

theorem FTS.reduce_no_isolated (F : FTS) (v : F.reduce.V) : ¬ F.reduce.Isolated v := by
  simp +decide [ FTS.reduce ];
  cases v;
  unfold FTS.Isolated at *; aesop;

theorem reconOK_reduce (F : FTS) (hlin : F.Linear)
    (hbr : ∀ ed : {e : Finset F.V // e ∈ F.edges}, ∃ w ∈ ed.1, IsBridgeInc F w ed)
    (hev : ∀ c : BergeCycle F, Even c.m) : ReconOK F.reduce := by
  obtain ⟨hlinR, hbrR, hevR⟩ := (FTS.intrinsic_reduce_iff F).mp ⟨hlin, hbr, hev⟩;
  exact ⟨ hlinR, FTS.reduce_no_isolated F, hbrR, hevR ⟩

theorem FTS.mem_disjUnion_edges_rev (F G : FTS) (e : Finset (F.disjUnion G).V) :
    e ∈ (F.disjUnion G).edges ↔
      (∃ a ∈ F.edges, Finset.map Function.Embedding.inl a = e) ∨
      (∃ a ∈ G.edges, Finset.map Function.Embedding.inr a = e) := by
  constructor
  · intro h
    rcases Finset.mem_union.1 h with h | h
    · exact Or.inl (Finset.mem_image.1 h)
    · exact Or.inr (Finset.mem_image.1 h)
  · rintro (h | h)
    · exact Finset.mem_union.2 (Or.inl (Finset.mem_image.2 h))
    · exact Finset.mem_union.2 (Or.inr (Finset.mem_image.2 h))

theorem bclass_of_bclass_reduce (F : FTS) (h : Bclass F.reduce) : Bclass F := by

  set E : FTS := ⟨{x : F.V // F.Isolated x}, ∅, by
    aesop⟩
  generalize_proofs at *;

  obtain ⟨φ, hφ⟩ : ∃ φ : F.V ≃ F.reduce.V ⊕ E.V, ∀ x, φ x = if hx : ¬ F.Isolated x then Sum.inl ⟨x, hx⟩ else Sum.inr ⟨x, by
    exact Classical.not_not.mp hx⟩ := by
    refine' ⟨ _, _ ⟩;
    refine' Equiv.ofBijective ( fun x => if hx : ¬ F.Isolated x then Sum.inl ⟨ x, hx ⟩ else Sum.inr ⟨ x, by simpa using hx ⟩ ) ⟨ fun x y hxy => _, fun x => _ ⟩;
    all_goals norm_num at *;
    · grind;
    · rcases x with ( ⟨ x, hx ⟩ | ⟨ x, hx ⟩ ) <;> [ exact ⟨ x, by aesop ⟩ ; exact ⟨ x, by aesop ⟩ ]
  generalize_proofs at *;
  have hφl : ∀ x (hx : ¬ F.Isolated x), φ x = Sum.inl ⟨x, hx⟩ := by
    intro x hx; rw [hφ x, dif_pos hx]
  have h_map : ∀ e ∈ F.edges, e.map φ.toEmbedding =
      (Finset.subtype (fun x => ¬ F.Isolated x) e).map Function.Embedding.inl := by
    intro e he
    ext a
    constructor
    · intro ha
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 ha
      have hni := FTS.not_isolated_of_mem he hx
      exact Finset.mem_map.2 ⟨⟨x, hni⟩, Finset.mem_subtype.2 hx, (hφl x hni).symm⟩
    · intro ha
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 ha
      exact Finset.mem_map.2 ⟨y.1, Finset.mem_subtype.1 hy, hφl y.1 y.2⟩

  have h_iso : ∀ e : Finset F.V, e ∈ F.edges ↔ e.map φ.toEmbedding ∈ (F.reduce.disjUnion E).edges := by
    intro e
    refine Iff.trans ?_ (FTS.mem_disjUnion_edges_rev _ _ _).symm
    constructor
    · intro he
      exact Or.inl ⟨_, FTS.subtype_edge_mem he, (h_map e he).symm⟩
    · rintro (⟨a, ha, hae⟩ | ⟨a, ha, _⟩)
      · obtain ⟨d, rfl⟩ := (FTS.mem_reduce_edges F a).1 ha
        have h3 : e.map φ.toEmbedding = d.1.map φ.toEmbedding :=
          hae.symm.trans (h_map d.1 d.2).symm
        rw [Finset.map_injective φ.toEmbedding h3]; exact d.2
      · exact absurd ha (Finset.notMem_empty _)
  exact Bclass.iso (FTS.Iso.symm ⟨φ, h_iso⟩) (Bclass.union h (Bclass.edgeless E rfl))

theorem intrinsic_bclass (F : FTS) (h : F.IntrinsicObligatory) : Bclass F := by
  apply bclass_of_bclass_reduce
  exact bclass_of_reconOK F.reduce (reconOK_reduce F h.1 h.2.1 h.2.2)

theorem finiteDecomposition_holds (F : FTS) :
    Bclass F ↔ F.reduce.IntrinsicObligatory :=
  ⟨fun h => (F.intrinsic_reduce_iff).mp (bclass_intrinsic h),
    fun h => intrinsic_bclass F ((F.intrinsic_reduce_iff).mpr h)⟩

end Erdos593
end

-- Results
section
open Cardinal

namespace Erdos593

universe u

theorem obligatory_not_inSpec (F : FTS) (lam : Cardinal.{u})
    (hobl : FTS.Obligatory.{u} F) : ¬ F.InSpec lam := by
  rintro ⟨hlam, W, H, htri, hchr, hne⟩
  exact hne (hobl H htri (hchr.2 ℵ₀ hlam))

theorem edgeless_obligatory (F : FTS) (h : F.edges = ∅) : FTS.Obligatory.{u} F := by
  intro W H htri huc
  have hinf : Infinite W := huc.infinite htri
  obtain ⟨f, hf, -⟩ := exists_injective_avoiding (fun (_ : Empty) => (Classical.arbitrary W)) F.V
  exact ⟨f, hf, fun e he => absurd he (by rw [h]; simp)⟩

theorem obligatory_disjUnion {F G : FTS} (ihF : FTS.Obligatory.{u} F)
    (ihG : FTS.Obligatory.{u} G) : FTS.Obligatory.{u} (F.disjUnion G) := by
  intro W H htri huc
  obtain ⟨fF, hfF, hfFe⟩ := ihF H htri huc
  obtain ⟨gG, hgG, hgGe⟩ := ihG H htri huc
  have hS : Set.Finite (Set.range fF) := by
    exact Set.toFinite _
  generalize_proofs at *; (
  obtain ⟨g0, hg0, hg0e⟩ : ∃ g0 : G.V → W, Function.Injective g0 ∧ ∀ e ∈ G.edges, g0 '' (e : Set G.V) ∈ {e | e ∈ H.edges ∧ e ⊆ (Set.range fF)ᶜ} := by
    have hHR : (⟨{e | e ∈ H.edges ∧ e ⊆ (Set.range fF)ᶜ}⟩ : Hypergraph W).UncountablyChromatic :=
      restrict_uc htri huc hS
    have htriR : (⟨{e | e ∈ H.edges ∧ e ⊆ (Set.range fF)ᶜ}⟩ : Hypergraph W).IsTripleSystem :=
      fun e he => htri e he.1
    exact ihG _ htriR hHR
  generalize_proofs at *; (
  obtain ⟨g, hg, hg'⟩ : ∃ g : G.V → W, Function.Injective g ∧ (∀ e ∈ G.edges, g '' (e : Set G.V) ∈ H.edges) ∧ ∀ x, g x ∉ Set.range fF := by
    obtain ⟨Bad, hBad⟩ : ∃ Bad : Finset G.V, ∀ x, g0 x ∈ Set.range fF ↔ x ∈ Bad := by
      have hBad : Set.Finite {x : G.V | g0 x ∈ Set.range fF} := by
        exact Set.Finite.preimage ( fun x => by aesop ) hS
      generalize_proofs at *; (
      exact ⟨ hBad.toFinset, fun x => by simp ⟩)
    generalize_proofs at *; (
    obtain ⟨emb, hemb, hemb'⟩ : ∃ emb : Bad → W, Function.Injective emb ∧ ∀ x, emb x ∉ Set.range g0 ∧ emb x ∉ Set.range fF := by
      have h_inf : Set.Infinite (Set.univ \ (Set.range g0 ∪ Set.range fF)) := by
        have h_infinite : Infinite W := by
          apply Hypergraph.UncountablyChromatic.infinite htri huc
        generalize_proofs at *; (
        exact Set.infinite_univ.diff ( Set.Finite.union ( Set.toFinite ( Set.range g0 ) ) hS ))
      generalize_proofs at *; (
      have := h_inf.natEmbedding
      generalize_proofs at *; (
      use fun x => this (Fintype.equivFin Bad x).val
      generalize_proofs at *; (
      exact ⟨ fun x y hxy => by simpa [ Fin.ext_iff ] using Fintype.equivFin Bad |>.injective <| Fin.ext <| by simpa using this.injective <| Subtype.ext hxy, fun x => ⟨ fun hx => this ( Fintype.equivFin Bad x ).val |>.2.2 <| Or.inl hx, fun hx => this ( Fintype.equivFin Bad x ).val |>.2.2 <| Or.inr hx ⟩ ⟩)))
    generalize_proofs at *; (
    use fun x => if hx : x ∈ Bad then emb ⟨x, hx⟩ else g0 x
    generalize_proofs at *; (
    refine' ⟨ _, _, _ ⟩;
    · intro x y hxy; by_cases hx : x ∈ Bad <;> by_cases hy : y ∈ Bad <;> simp_all +decide [ Function.Injective.eq_iff hg0, Function.Injective.eq_iff hemb ] ;
      exact False.elim ( hemb' x hx |>.1 y hxy.symm );
    · intro e he
      have h_image : (fun x => if hx : x ∈ Bad then emb ⟨x, hx⟩ else g0 x) '' (e : Set G.V) = g0 '' (e : Set G.V) := by
        ext x
        simp;
        constructor <;> rintro ⟨ y, hy, rfl ⟩ <;> use y <;> simp_all +decide ;
        · exact fun h => hg0e e he |>.2 hy <| by obtain ⟨ x, hx ⟩ := hBad y |>.2 h; aesop;
        · exact fun h => False.elim <| hg0e e he |>.2 hy <| by aesop;
      generalize_proofs at *; (
      exact h_image.symm ▸ hg0e e he |>.1);
    · grind)))
  generalize_proofs at *; (
  refine' ⟨ Sum.elim fF g, _, _ ⟩ <;> simp_all +decide [ Function.Injective ];
  · rintro ( a | a ) ( b | b ) <;> simp +decide [ * ];
    · exact fun h => congr_arg Sum.inl ( hfF h );
    · exact Ne.symm ( hg'.2 a b );
    · exact fun h => congr_arg Sum.inr ( hg h );
  · intro e he
    rcases (FTS.mem_disjUnion_edges_rev F G e).1 he with ⟨ a, ha, rfl ⟩ | ⟨ a, ha, rfl ⟩
    · have h1 : (Sum.elim fF g : F.V ⊕ G.V → W) ''
          ((a.map Function.Embedding.inl : Finset (F.V ⊕ G.V)) : Set (F.V ⊕ G.V)) =
            fF '' (a : Set F.V) := by
        rw [Finset.coe_map, Set.image_image]; rfl
      have h2 : (Sum.elim fF g : F.V ⊕ G.V → W) ''
          ((a.map Function.Embedding.inl : Finset (F.V ⊕ G.V)) : Set (F.V ⊕ G.V)) ∈ H.edges :=
        h1 ▸ hfFe a ha
      exact h2
    · have h1 : (Sum.elim fF g : F.V ⊕ G.V → W) ''
          ((a.map Function.Embedding.inr : Finset (F.V ⊕ G.V)) : Set (F.V ⊕ G.V)) =
            g '' (a : Set G.V) := by
        rw [Finset.coe_map, Set.image_image]; rfl
      have h2 : (Sum.elim fF g : F.V ⊕ G.V → W) ''
          ((a.map Function.Embedding.inr : Finset (F.V ⊕ G.V)) : Set (F.V ⊕ G.V)) ∈ H.edges :=
        h1 ▸ hg'.1 a ha
      exact h2)))

def ReiherExpansion : Prop :=
  ∀ {VJ : Type} [Fintype VJ] [DecidableEq VJ] (J : SimpleGraph VJ) [DecidableRel J.Adj],
    J.Colorable 2 → FTS.Obligatory.{u} (graphExpansion J)

def AmalgClosure : Prop :=
  ∀ {F G : FTS} (x : F.V) (y : G.V), FTS.Obligatory.{u} F → FTS.Obligatory.{u} G →
    FTS.Obligatory.{u} (F.amalgamate G x y)

theorem amalgClosure_holds : AmalgClosure.{u} :=
  fun x y hF hG => amalgamate_obligatory x y hF hG

def NegativeCore : Prop :=
  ∀ (F : FTS) (lam : Cardinal.{u}), ¬ Bclass F → ℵ₀ < lam → F.FGnonempty lam

def FiniteDecomposition : Prop :=
  ∀ (F : FTS), Bclass F ↔ F.reduce.IntrinsicObligatory

theorem finiteDecomposition_valid : FiniteDecomposition :=
  finiteDecomposition_holds

theorem bclass_obligatory (hexp : ReiherExpansion.{u})
    (F : FTS) (h : Bclass F) : FTS.Obligatory.{u} F := by
  induction h with
  | edgeless F hF => exact edgeless_obligatory F hF
  | expansion J hJ => exact hexp J hJ
  | iso hiso _ ih => exact obligatory_iso hiso ih
  | union _ _ ihF ihG => exact obligatory_disjUnion ihF ihG
  | amalg x y _ _ ihF ihG => exact amalgClosure_holds x y ihF ihG

theorem classification (hexp : ReiherExpansion.{u})
    (hneg : NegativeCore.{u}) (F : FTS) :
    (FTS.Obligatory.{u} F ↔ Bclass F) ∧
    (Bclass F ↔ F.reduce.IntrinsicObligatory) := by
  refine ⟨⟨fun hobl => ?_, bclass_obligatory hexp F⟩, finiteDecomposition_holds F⟩
  by_contra hnb
  obtain ⟨W, H, htri, hchr, hne⟩ :=
    hneg F (Order.succ (ℵ₀ : Cardinal.{u})) hnb (Order.lt_succ _)
  exact hne (hobl H htri (hchr.2 ℵ₀ (Order.lt_succ _)))

theorem obligatory_iff_bclass (hexp : ReiherExpansion.{u})
    (hneg : NegativeCore.{u}) (F : FTS) :
    FTS.Obligatory.{u} F ↔ Bclass F :=
  (classification hexp hneg F).1

theorem spectrum_dichotomy (hexp : ReiherExpansion.{u})
    (hneg : NegativeCore.{u}) (F : FTS) (lam : Cardinal.{u}) :
    F.InSpec lam ↔ (¬ Bclass F ∧ ℵ₀ < lam) := by
  constructor
  · intro hspec
    exact ⟨fun hb => obligatory_not_inSpec F lam (bclass_obligatory hexp F hb) hspec,
      hspec.1⟩
  · rintro ⟨hb, hlam⟩
    exact ⟨hlam, hneg F lam hb hlam⟩

theorem problem_1177_part3 (hexp : ReiherExpansion.{u})
    (hneg : NegativeCore.{u}) (G : FTS) (kappa : Cardinal.{u}) (hk : ℵ₀ < kappa)
    (h : G.FGnonempty kappa) (lam : Cardinal.{u}) (hlam : ℵ₀ < lam) :
    G.FGnonempty lam := by
  have hnb : ¬ Bclass G := ((spectrum_dichotomy hexp hneg G kappa).mp ⟨hk, h⟩).1
  exact ((spectrum_dichotomy hexp hneg G lam).mpr ⟨hnb, hlam⟩).2

end Erdos593
end

-- PropertyP
section
open Cardinal

namespace Erdos593

universe u

def SimpleGraph.PropertyP {S : Type u} (G : SimpleGraph S) {I : Type u}
    (ℓ : G.edgeSet → I) (κ : Cardinal.{u}) : Prop :=
  ∀ (θ : Cardinal.{u}), θ < κ → ∀ (c : S → θ.out),
    ∃ a : θ.out, ∀ i : I, ∃ (x y : S) (h : G.Adj x y),
      ℓ ⟨s(x, y), h⟩ = i ∧ c x = a ∧ c y = a

theorem SimpleGraph.PropertyP.mono {S : Type u} {G : SimpleGraph S} {I : Type u}
    {ℓ : G.edgeSet → I} {κ δ : Cardinal.{u}} (h : SimpleGraph.PropertyP G ℓ δ)
    (hκδ : κ ≤ δ) :
    SimpleGraph.PropertyP G ℓ κ := by
  intro θ hθ c
  exact h θ (lt_of_lt_of_le hθ hκδ) c

end Erdos593
end

-- DeltaRho
section
open Cardinal

namespace Erdos593

noncomputable def deltaRho (ρ : Cardinal) : Cardinal := sInf {δ | ρ < ρ ^ δ}

theorem pow_pow_eq_of_le {μ θ : Cardinal} (hμ : ℵ₀ ≤ μ) (h1 : θ ≠ 0) (hθ : θ ≤ μ) :
    ((2 : Cardinal) ^ μ) ^ θ = (2 : Cardinal) ^ μ := by
  rw [← Cardinal.power_mul, Cardinal.mul_eq_left hμ hθ h1]

theorem deltaRho_mem {ρ : Cardinal} (hρ : ℵ₀ ≤ ρ) : ρ ∈ {δ | ρ < ρ ^ δ} := by
  show ρ < ρ ^ ρ
  calc ρ < 2 ^ ρ := Cardinal.cantor ρ
    _ ≤ ρ ^ ρ := Cardinal.power_le_power_right (le_trans (by norm_num) hρ)

theorem succ_le_deltaRho {μ : Cardinal} (hμ : ℵ₀ ≤ μ) :
    Order.succ μ ≤ deltaRho ((2 : Cardinal) ^ μ) := by
  set ρ := (2 : Cardinal) ^ μ with hρdef
  have hρ : ℵ₀ ≤ ρ := le_of_lt (lt_of_le_of_lt hμ (Cardinal.cantor μ))
  show Order.succ μ ≤ sInf {δ | ρ < ρ ^ δ}
  apply le_csInf ⟨ρ, deltaRho_mem hρ⟩
  intro θ hθ
  by_contra h
  push_neg at h
  rw [Order.lt_succ_iff] at h
  have hle : ρ ^ θ ≤ ρ := by
    rcases eq_or_ne θ 0 with rfl | h1
    · simpa using one_le_aleph0.trans hρ
    · rw [hρdef, pow_pow_eq_of_le hμ h1 h]
  exact absurd hθ (not_lt.mpr hle)

end Erdos593
end

-- External
section
open Cardinal

namespace Erdos593

universe u

def E1_EHR_nonlinear : Prop :=
  ∀ (F : FTS), ¬ F.Linear → ¬ FTS.Obligatory.{u} F

def NoShortOddCycle {V : Type u} (A : SimpleGraph V) (s : ℕ) : Prop :=
  ∀ m : ℕ, Odd m → 3 ≤ m → m ≤ 2 * s + 1 →
    ¬ ∃ v : ZMod m → V, Function.Injective v ∧ ∀ i : ZMod m, A.Adj (v i) (v (i + 1))

def E2_EH_oddgirth : Prop :=
  ∀ (κ : Cardinal.{u}), ℵ₀ < κ → ∀ (s : ℕ),
    ∃ (V : Type u) (A : SimpleGraph V),
      Cardinal.mk V = κ ∧ (SimpleGraph.toHG A).HasChromatic κ ∧ NoShortOddCycle A s

def E3_EGH_P : Prop :=
  ∀ (ρ : Cardinal.{u}), ℵ₀ ≤ ρ →
    ∃ (S : Type u) (G : SimpleGraph S) (I : Type u),
      Cardinal.mk S = ρ ∧ Cardinal.mk I = ρ ∧
        ∃ ℓ : G.edgeSet → I, SimpleGraph.PropertyP G ℓ (deltaRho ρ)

open Classical in

def E4_Reiher : Prop :=
  ∀ n : ℕ,
    FTS.Obligatory.{u} (graphExpansion (completeBipartiteGraph (Fin n) (Fin n)))

open Classical in

theorem completeBipartite_colorable_two (n : ℕ) :
    (completeBipartiteGraph (Fin n) (Fin n)).Colorable 2 := by
  refine ⟨SimpleGraph.Coloring.mk (fun x => Sum.elim (fun _ => 0) (fun _ => 1) x) ?_⟩
  rintro (a | a) (b | b) hadj <;> simp_all [completeBipartiteGraph]

open Classical in

theorem E4_Reiher_of_reiherExpansion (h : ReiherExpansion.{u}) : E4_Reiher.{u} :=
  fun n => h (J := completeBipartiteGraph (Fin n) (Fin n)) (completeBipartite_colorable_two n)

theorem colorableBy_mono {V : Type u} {E F : Set (Set V)} (hEF : E ⊆ F)
    {θ : Cardinal.{u}} (h : (⟨F⟩ : Hypergraph V).ColorableBy θ) :
    (⟨E⟩ : Hypergraph V).ColorableBy θ := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun e he => hc e (hEF he)⟩

theorem colorableBy_aleph0_union {V : Type u} (E' E'' : Set (Set V))
    (h' : (⟨E'⟩ : Hypergraph V).ColorableBy ℵ₀)
    (h'' : (⟨E''⟩ : Hypergraph V).ColorableBy ℵ₀) :
    (⟨E' ∪ E''⟩ : Hypergraph V).ColorableBy ℵ₀ := by
  obtain ⟨c', hc'⟩ := h'
  obtain ⟨c'', hc''⟩ := h''
  have hle : Cardinal.mk ((ℵ₀ : Cardinal.{u}).out × (ℵ₀ : Cardinal.{u}).out)
      ≤ Cardinal.mk ((ℵ₀ : Cardinal.{u}).out) := by
    simp only [Cardinal.mk_prod, Cardinal.mk_out, Cardinal.lift_id]
    exact le_of_eq Cardinal.aleph0_mul_aleph0
  obtain ⟨g, hg⟩ := hle
  refine ⟨fun v => g (c' v, c'' v), ?_⟩
  intro e he
  rcases he with he | he
  · obtain ⟨u, hu, v, hv, huv⟩ := hc' e he
    exact ⟨u, hu, v, hv, fun h => huv (congrArg Prod.fst (hg h))⟩
  · obtain ⟨u, hu, v, hv, huv⟩ := hc'' e he
    exact ⟨u, hu, v, hv, fun h => huv (congrArg Prod.snd (hg h))⟩

theorem uncountablyChromatic_diff {V : Type u} (E E' : Set (Set V))
    (hE : (⟨E⟩ : Hypergraph V).UncountablyChromatic)
    (hE' : (⟨E'⟩ : Hypergraph V).ColorableBy ℵ₀) :
    (⟨E \ E'⟩ : Hypergraph V).UncountablyChromatic := by
  intro hdiff
  exact hE (colorableBy_mono
    (by intro x hx; by_cases h : x ∈ E' <;> [left; right] <;> simp_all)
    (colorableBy_aleph0_union E' (E \ E') hE' hdiff))

def FTS.LinearlyObligatory (F : FTS) : Prop :=
  ∀ {W : Type u} (H : Hypergraph W),
    H.IsTripleSystem → H.Linear → H.UncountablyChromatic → F.Embeds H

open Classical in

noncomputable def looseCycle7 : FTS where
  V := Fin 7 ⊕ Fin 7
  edges := (Finset.univ : Finset (Fin 7)).image
      (fun i => ({Sum.inl i, Sum.inl (i + 1), Sum.inr i} : Finset (Fin 7 ⊕ Fin 7)))
  card3 := by
    have hne : ∀ j : Fin 7, j ≠ j + 1 := by decide
    intro e he
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at he
    obtain ⟨i, rfl⟩ := he
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨fun h => hne i (Sum.inl_injective h), fun h => Sum.inl_ne_inr h⟩

def E5_HK_loose7 : Prop :=
  FTS.LinearlyObligatory.{u} looseCycle7

end Erdos593
end

-- CardinalArith
section
open Cardinal Ordinal

namespace Erdos593

universe u

theorem small_union {ι : Type u} {V : Type u} (ρ μ : Cardinal.{u})
    (hρ : ℵ₀ ≤ ρ) (hμ : μ < ρ.ord.cof) (hI : #ι ≤ μ)
    (X : ι → Set V) (hX : ∀ i, #(X i) < ρ) :
    #(↥(⋃ i, X i)) < ρ := by
  convert Cardinal.mk_iUnion_le ( fun i => X i ) |> lt_of_le_of_lt <| ?_;
  convert Cardinal.mul_lt_of_lt hρ _ _;
  · exact lt_of_le_of_lt hI ( lt_of_lt_of_le hμ ( Ordinal.cof_ord_le _ ) );
  · convert Ordinal.iSup_lt _ _;
    · exact lt_of_le_of_lt hI hμ;
    · assumption

theorem cf_two_pow (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) :
    μ < ((2:Cardinal.{u}) ^ μ).ord.cof :=
  Cardinal.lt_cof_power hμ one_lt_two

theorem succ_le_two_pow (μ : Cardinal.{u}) :
    Order.succ μ ≤ (2:Cardinal.{u}) ^ μ :=
  Order.succ_le_of_lt (Cardinal.cantor μ)

theorem pow_two_pow_self (ρ : Cardinal.{u}) (hρ : ℵ₀ ≤ ρ) :
    ((2:Cardinal.{u}) ^ ρ) ^ ρ = (2:Cardinal.{u}) ^ ρ := by
  rw [ ← Cardinal.power_mul, Cardinal.mul_eq_self ] ; aesop

theorem succ_le_two_pow' (ρ : Cardinal.{u}) :
    Order.succ ρ ≤ (2:Cardinal.{u}) ^ ρ :=
  Order.succ_le_of_lt (Cardinal.cantor ρ)

theorem successors_cofinal (κ : Cardinal.{u}) (hκ : ℵ₀ < κ)
    (hlim : ∀ ν : Cardinal.{u}, κ ≠ Order.succ ν) (α : Ordinal.{u}) (hα : α < κ.ord) :
    ∃ ν : Cardinal.{u}, ℵ₀ ≤ ν ∧ Order.succ ν < κ ∧ α < (Order.succ ν).ord := by
  obtain ⟨ν, hν⟩ : ∃ ν : Cardinal, Cardinal.aleph0 ≤ ν ∧ ν < κ ∧ α < (Order.succ ν).ord := by
    refine' ⟨ Max.max ℵ₀ α.card, _, _, _ ⟩ <;> simp_all +decide [ Cardinal.lt_ord ];
  refine' ⟨ ν, hν.1, lt_of_le_of_ne _ _, hν.2.2 ⟩;
  · exact Order.succ_le_of_lt hν.2.1;
  · exact Ne.symm ( hlim ν )

theorem cofinal_fibres (κ ρ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (hρ : κ ≤ ρ) :
    ∃ q : Ordinal.{u} → Ordinal.{u},
      (∀ α, α < (Order.succ ρ).ord → q α < κ.ord) ∧
      (∀ ξ, ξ < κ.ord → ∀ β, β < (Order.succ ρ).ord →
        ∃ α, β ≤ α ∧ α < (Order.succ ρ).ord ∧ q α = ξ) := by
  refine' ⟨ fun α => α % κ.ord, _, _ ⟩;
  · intro α hα;
    by_cases h : κ.ord = 0;
    · simp_all +decide [ Cardinal.ord_eq_zero ];
      exact absurd hκ ( ne_of_gt ( Cardinal.aleph0_pos ) );
    · exact Ordinal.mod_lt _ h;
  · intro ξ hξ β hβ;
    refine' ⟨ κ.ord * β + ξ, _, _, _ ⟩;
    · refine' le_trans _ le_self_add;
      refine' le_mul_of_one_le_left' _;
      contrapose! hκ; aesop;
    ·
      have hβ_card : β.card ≤ ρ :=
        Order.lt_succ_iff.mp (Cardinal.lt_ord.mp hβ);

      have hξ_card : ξ.card < κ := Cardinal.lt_ord.mp hξ;

      have h_card : (κ.ord * β + ξ).card ≤ κ * β.card + ξ.card := by
        refine' le_trans ( Ordinal.card_add _ _ |> le_of_eq ) _;
        rw [ Ordinal.card_mul ];
        rw [ Cardinal.card_ord ];

      have h_card_le_ρ : (κ.ord * β + ξ).card ≤ ρ := by
        refine le_trans h_card ?_;
        refine' le_trans ( add_le_add ( mul_le_mul' hρ le_rfl ) hξ_card.le ) _;
        refine' le_trans ( add_le_add ( mul_le_mul' le_rfl hβ_card ) hρ ) _;
        rw [ Cardinal.mul_eq_self ];
        · rw [ Cardinal.add_eq_self ];
          exact le_trans hκ hρ;
        · exact le_trans hκ hρ;
      exact Cardinal.lt_ord.mpr (Order.lt_succ_iff.mpr h_card_le_ρ);
    · simp +decide [ Ordinal.mod_eq_of_lt, hξ ]

end Erdos593
end

-- ReservoirSetup
section
open Cardinal Ordinal


namespace Erdos593

universe u

set_option maxHeartbeats 4000000 in
abbrev rhoC (μ : Cardinal.{u}) : Cardinal.{u} := (2 : Cardinal.{u}) ^ μ

set_option maxHeartbeats 4000000 in
noncomputable def Rord (ρ : Cardinal.{u}) : Ordinal.{u} := (Order.succ ρ).ord

set_option maxHeartbeats 4000000 in
abbrev Lev (ρ : Cardinal.{u}) : Type u := (Rord ρ).ToType

set_option maxHeartbeats 4000000 in
abbrev Fib (ρ : Cardinal.{u}) : Type u := ((2 : Cardinal.{u}) ^ ρ).out

set_option maxHeartbeats 4000000 in
abbrev Vtx (ρ : Cardinal.{u}) : Type u := Lev ρ × Fib ρ

set_option maxHeartbeats 4000000 in
noncomputable def lrank {ρ : Cardinal.{u}} (a : Lev ρ) : Ordinal.{u} :=
  Ordinal.typein (α := Lev ρ) (· < ·) a

set_option maxHeartbeats 4000000 in
def Vbelow {ρ : Cardinal.{u}} (a : Lev ρ) : Set (Vtx ρ) := {v | v.1 < a}

set_option maxHeartbeats 4000000 in
def IsReservoir {ρ : Cardinal.{u}} {Ilab : Type u} (q : Ordinal.{u} → Ordinal.{u})
    (a : Lev ρ) (X : Ilab → Set (Vtx ρ)) : Prop :=
  (∀ i, X i ⊆ Vbelow a) ∧
  (∀ i, X i = ∅ ∨ #(X i) = ρ) ∧
  (∀ i j, i ≠ j → (X i).Nonempty → (X j).Nonempty → Disjoint (X i) (X j)) ∧
  (∀ i, ∀ v ∈ X i, q (lrank v.1) ≠ q (lrank a))

set_option maxHeartbeats 4000000 in
structure CalibData (μ : Cardinal.{u}) where

  hμ : ℵ₀ ≤ μ

  S : Type u

  G : SimpleGraph S

  Ilab : Type u

  hIlab : #Ilab = rhoC μ

  hS : #S ≤ rhoC μ

  lbl : G.edgeSet → Ilab

  hP : SimpleGraph.PropertyP G lbl (Order.succ μ)

  q : Ordinal.{u} → Ordinal.{u}

  hq1 : ∀ a, a < Rord (rhoC μ) → q a < (Order.succ μ).ord

  hq2 : ∀ ξ, ξ < (Order.succ μ).ord → ∀ β, β < Rord (rhoC μ) →
          ∃ α, β ≤ α ∧ α < Rord (rhoC μ) ∧ q α = ξ

  copy : ∀ a : Lev (rhoC μ),
    {X : Ilab → Set (Vtx (rhoC μ)) // IsReservoir q a X} → Fib (rhoC μ) → S → Vtx (rhoC μ)

  copy_lev : ∀ a X η s, (copy a X η s).1 = a

  copy_inj : ∀ a : Lev (rhoC μ),
    Function.Injective
      (fun p : ({X : Ilab → Set (Vtx (rhoC μ)) // IsReservoir q a X} × Fib (rhoC μ) × S) =>
        copy a p.1 p.2.1 p.2.2)

  phi : ∀ a : Lev (rhoC μ),
    {X : Ilab → Set (Vtx (rhoC μ)) // IsReservoir q a X} → G.edgeSet → Vtx (rhoC μ)

  phi_mem : ∀ a X e, (X.val (lbl e)).Nonempty → phi a X e ∈ X.val (lbl e)

  phi_inj : ∀ a X, Set.InjOn (phi a X) {e | (X.val (lbl e)).Nonempty}

namespace CalibData

variable {μ : Cardinal.{u}} (D : CalibData μ)

set_option maxHeartbeats 4000000 in
def edgeBase (e : D.G.edgeSet) : Set D.S := {x | x ∈ (e : Sym2 D.S)}

set_option maxHeartbeats 4000000 in
def edgeSetL : Set (Set (Vtx (rhoC μ))) :=
  {t | ∃ (a : Lev (rhoC μ))
        (X : {X : D.Ilab → Set (Vtx (rhoC μ)) // IsReservoir D.q a X})
        (η : Fib (rhoC μ)) (e : D.G.edgeSet),
      (X.val (D.lbl e)).Nonempty ∧
      t = (fun s => D.copy a X η s) '' (D.edgeBase e) ∪ {D.phi a X e} }

set_option maxHeartbeats 4000000 in
def L : Hypergraph (Vtx (rhoC μ)) := ⟨D.edgeSetL⟩

end CalibData

set_option maxHeartbeats 4000000 in
theorem colorableBy_of_proper_le {V : Type u} {H : Hypergraph V} {T : Type u} (c : V → T)
    (hc : H.ProperColoring c) {θ : Cardinal.{u}} (hT : #T ≤ θ) : H.ColorableBy θ := by
  have : #T ≤ #θ.out := by simpa [Cardinal.mk_out] using hT
  obtain ⟨g, hg⟩ := this
  refine ⟨fun v => g (c v), ?_⟩
  intro e he
  obtain ⟨u, hu, v, hv, huv⟩ := hc e he
  exact ⟨u, hu, v, hv, fun h => huv (hg h)⟩

namespace CalibData

variable {μ : Cardinal.{u}} (D : CalibData μ)

set_option maxHeartbeats 4000000 in
theorem mem_edgeSetL {t : Set (Vtx (rhoC μ))} :
    t ∈ D.edgeSetL ↔ ∃ (a : Lev (rhoC μ))
        (X : {X : D.Ilab → Set (Vtx (rhoC μ)) // IsReservoir D.q a X})
        (η : Fib (rhoC μ)) (e : D.G.edgeSet),
      (X.val (D.lbl e)).Nonempty ∧
      t = (fun s => D.copy a X η s) '' (D.edgeBase e) ∪ {D.phi a X e} := Iff.rfl

set_option maxHeartbeats 4000000 in
theorem edgeBase_ncard (e : D.G.edgeSet) : (D.edgeBase e).ncard = 2 := by
  unfold CalibData.edgeBase;
  convert Set.ncard_eq_two.mpr _;
  rcases e with ⟨ e, he ⟩;
  rcases e with ⟨ x, y ⟩;
  exact ⟨ x, y, by rintro rfl; exact absurd he ( by simp +decide ), by ext; simp +decide ⟩

set_option maxHeartbeats 4000000 in
theorem L_isTripleSystem : (D.L).IsTripleSystem := by
  intro t ht
  obtain ⟨a, X, η, e, hX, ht⟩ := (D.mem_edgeSetL).mp ht;
  rw [ ht, @Set.ncard_union_eq ];
  · rw [ Set.ncard_image_of_injective, Set.ncard_singleton ];
    · exact D.edgeBase_ncard e ▸ rfl;
    · exact fun x y hxy => by have := D.copy_inj a; have := @this ( X, η, x ) ( X, η, y ) ; aesop;
  · simp +decide [ Set.disjoint_left ];
    intro s hs h_eq
    have h_level : (D.copy a X η s).1 = a := by
      exact D.copy_lev a X η s
    have h_level_phi : (D.phi a X e).1 < a := by
      exact X.2.1 _ ( D.phi_mem _ _ _ hX )
    exact absurd h_level (by
    exact ne_of_lt ( h_eq ▸ h_level_phi ));
  · exact Set.Finite.image _ ( Set.finite_of_ncard_pos ( by rw [ D.edgeBase_ncard ] ; positivity ) );
  · exact Set.finite_singleton _

set_option maxHeartbeats 4000000 in
theorem edgeBase_inter_subsingleton {e₁ e₂ : D.G.edgeSet} (h : e₁ ≠ e₂) :
    (D.edgeBase e₁ ∩ D.edgeBase e₂).Subsingleton := by
  unfold CalibData.edgeBase;
  rcases e₁ with ⟨ ⟨ x, y ⟩, hxy ⟩ ; rcases e₂ with ⟨ ⟨ u, v ⟩, huv ⟩ ; simp_all +decide [ Set.Subsingleton ];
  grind

set_option maxHeartbeats 4000000 in
theorem phi_level_lt {a : Lev (rhoC μ)}
    {X : {X : D.Ilab → Set (Vtx (rhoC μ)) // IsReservoir D.q a X}} {e : D.G.edgeSet}
    (hX : (X.val (D.lbl e)).Nonempty) : (D.phi a X e).1 < a :=
  X.property.1 (D.lbl e) (D.phi_mem a X e hX)

set_option maxHeartbeats 4000000 in
theorem L_linear : (D.L).Linear := by
  intro t₁ ht₁ t₂ ht₂ hne
  obtain ⟨a₁, X₁, η₁, e₁, hX₁, rfl⟩ := D.mem_edgeSetL.mp ht₁
  obtain ⟨a₂, X₂, η₂, e₂, hX₂, rfl⟩ := D.mem_edgeSetL.mp ht₂;
  by_cases h_cases : a₁ < a₂;
  · have h_level : ∀ p ∈ (fun s => D.copy a₁ X₁ η₁ s) '' D.edgeBase e₁ ∪ {D.phi a₁ X₁ e₁}, p.1 < a₂ := by
      simp +zetaDelta at *;
      exact ⟨ lt_trans ( D.phi_level_lt hX₁ ) h_cases, fun x hx => lt_of_le_of_lt ( by simp +decide [ D.copy_lev ] ) h_cases ⟩;
    intro p hp q hq; have := h_level p hp.1; have := h_level q hq.1; simp_all +decide [ D.copy_lev ] ;
    grind only [copy_lev];
  · by_cases h_cases : a₂ < a₁;
    · have h_inter : ∀ p ∈ (fun s => D.copy a₂ X₂ η₂ s) '' D.edgeBase e₂ ∪ {D.phi a₂ X₂ e₂}, p.1 < a₁ := by
        simp [D.copy_lev];
        exact ⟨ lt_of_lt_of_le ( D.phi_level_lt hX₂ ) h_cases.le, fun _ _ => h_cases ⟩;
      intro p hp q hq; have := h_inter p hp.2; have := h_inter q hq.2; simp_all +decide [ D.copy_lev ] ;
      rcases hp.1 with ( rfl | ⟨ x, hx, rfl ⟩ ) <;> rcases hq.1 with ( rfl | ⟨ y, hy, rfl ⟩ ) <;> simp_all +decide [ D.copy_lev ];
    · cases lt_or_eq_of_le ( le_of_not_gt h_cases ) <;> simp_all +decide;
      by_cases h_cases : X₁.val = X₂.val ∧ η₁ = η₂;
      · have h_base_inter : (D.copy a₁ X₁ η₁ '' D.edgeBase e₁ ∩ D.copy a₁ X₁ η₁ '' D.edgeBase e₂).Subsingleton := by
          have h_base_inter : (D.edgeBase e₁ ∩ D.edgeBase e₂).Subsingleton := by
            apply D.edgeBase_inter_subsingleton;
            lia;
          have h_base_inter : (D.copy a₁ X₁ η₁ '' (D.edgeBase e₁ ∩ D.edgeBase e₂)).Subsingleton := by
            exact Set.Subsingleton.image h_base_inter _;
          convert h_base_inter using 1;
          rw [ Set.image_inter ];
          exact fun x y hxy => by have := D.copy_inj a₁; have := @this ( X₁, η₁, x ) ( X₁, η₁, y ) ; aesop;
        have h_apex_inter : ¬(D.phi a₁ X₁ e₁ = D.phi a₂ X₂ e₂) := by
          have := D.phi_inj a₁ X₁; simp_all +decide [ Set.InjOn ] ;
          specialize this _ e₁.2 hX₁ _ e₂.2 hX₂ ; aesop;
        have h_apex_not_in_base : D.phi a₁ X₁ e₁ ∉ D.copy a₁ X₁ η₁ '' D.edgeBase e₂ ∧ D.phi a₂ X₂ e₂ ∉ D.copy a₁ X₁ η₁ '' D.edgeBase e₁ := by
          constructor <;> intro h <;> obtain ⟨ s, hs, hs' ⟩ := h <;> have := D.copy_lev a₁ X₁ η₁ s <;> simp_all +decide;
          · have := D.phi_level_lt ( show ( X₁.val ( D.lbl e₁ ) ).Nonempty from by aesop ) ; aesop;
          · exact absurd this ( ne_of_lt ( by simpa [ * ] using phi_level_lt D hX₂ ) );
        intro x hx y hy; simp_all +decide [ Set.Subsingleton ] ;
        grind;
      · have h_disjoint : Disjoint ((fun s => D.copy a₁ X₁ η₁ s) '' D.edgeBase e₁) ((fun s => D.copy a₂ X₂ η₂ s) '' D.edgeBase e₂) := by
          have := D.copy_inj a₁;
          simp_all +decide [ Set.disjoint_left, Function.Injective ];
          grind;
        have h_disjoint : D.phi a₁ X₁ e₁ ∉ (fun s => D.copy a₂ X₂ η₂ s) '' D.edgeBase e₂ ∧ D.phi a₂ X₂ e₂ ∉ (fun s => D.copy a₁ X₁ η₁ s) '' D.edgeBase e₁ := by
          constructor <;> intro h <;> obtain ⟨ s, hs, hs' ⟩ := h <;> have := D.copy_lev a₂ X₂ η₂ s <;> simp_all +decide;
          · have := D.phi_level_lt hX₁; aesop;
          · have := D.copy_lev a₁ X₁ η₁ s; simp_all +decide ;
            exact absurd this ( ne_of_lt ( D.phi_level_lt hX₂ ) );
        simp_all +decide [ Set.Subsingleton ];
        simp_all +decide [ Set.disjoint_left ]

set_option maxHeartbeats 4000000 in
theorem L_colorable : (D.L).ColorableBy (Order.succ μ) := by
  set c : Vtx (rhoC μ) → {o : Ordinal // o < (Order.succ μ).ord} := fun v => ⟨D.q (lrank v.1), by
    exact D.hq1 _ ( by exact Ordinal.typein_lt_self _ )⟩
  generalize_proofs at *;

  have hc_proper : (D.L).ProperColoring c := by
    intro t ht
    obtain ⟨a, X, η, e, hX, rfl⟩ := D.mem_edgeSetL.mp ht;
    obtain ⟨ s, hs ⟩ := Set.nonempty_of_ncard_ne_zero ( by rw [ D.edgeBase_ncard e ] ; norm_num );
    refine' ⟨ _, Or.inl ⟨ s, hs, rfl ⟩, _, Or.inr rfl, _ ⟩ ; simp +decide [ c ];
    convert X.2.2.2.2 ( D.lbl e ) _ ( D.phi_mem a X e hX ) using 1;
    rw [ D.copy_lev ] ; aesop;
  have h1 : Cardinal.mk {o : Ordinal.{u} // o < (Order.succ μ).ord} =
      Cardinal.lift.{u+1} (Order.succ μ) := by
    have h2 := Cardinal.mk_Iio_ordinal (Order.succ μ).ord
    rw [Cardinal.card_ord] at h2
    exact h2
  refine' ⟨ _, _ ⟩;
  exact fun v => Classical.choice ( Cardinal.mk_out ( Order.succ μ ) |> fun h => Cardinal.lift_mk_eq'.mp <| by simp [h1] ) ( c v );
  intro e he; specialize hc_proper e he; aesop;

end CalibData

end Erdos593
end

-- ReservoirBuild
section
open Cardinal Ordinal


namespace Erdos593

universe u

set_option maxHeartbeats 4000000 in
theorem mk_Vtx (ρ : Cardinal.{u}) (hρ : ℵ₀ ≤ ρ) : #(Vtx ρ) = (2 : Cardinal.{u}) ^ ρ := by
  have h_lev : #(Lev ρ) = Order.succ ρ := by
    rw [Lev, Rord, Cardinal.mk_toType, Cardinal.card_ord]
  have h_fib : #(Fib ρ) = (2 : Cardinal.{u}) ^ ρ := Cardinal.mk_out _
  rw [Vtx, Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id, h_lev, h_fib,
    Cardinal.mul_eq_max (le_trans hρ (Order.le_succ ρ)) (le_trans hρ (Cardinal.cantor ρ).le)]
  exact max_eq_right (Order.succ_le_of_lt (Cardinal.cantor ρ))

set_option maxHeartbeats 4000000 in
theorem stage_capacity {ρ : Cardinal.{u}} (hρ : ℵ₀ ≤ ρ) {Ilab : Type u}
    (hI : #Ilab ≤ ρ) (q : Ordinal.{u} → Ordinal.{u}) (a : Lev ρ) :
    #{X : Ilab → Set (Vtx ρ) // IsReservoir q a X} ≤ (2 : Cardinal.{u}) ^ ρ := by
  refine' le_trans ( Cardinal.mk_le_mk_of_subset _ ) _;
  exact { X : Ilab → Set ( Vtx ρ ) | ∀ i, X i ⊆ Vbelow a ∧ ( X i = ∅ ∨ # ( X i ) ≤ ρ ) };
  · exact fun X hX i => ⟨ hX.1 i, Or.imp id ( fun h => h.le ) ( hX.2.1 i ) ⟩;
  ·
    have h_card : #(Ilab → {t : Set (Vtx ρ) | t ⊆ Vbelow a ∧ (t = ∅ ∨ #t ≤ ρ)}) ≤ (2 ^ ρ) ^ #Ilab := by
      have h_card_pi : Cardinal.mk {t : Set (Vtx ρ) | t ⊆ Vbelow a ∧ (t = ∅ ∨ #t ≤ ρ)} ≤ 2 ^ ρ := by
        refine' le_trans ( Cardinal.mk_le_mk_of_subset _ ) _;
        exact { t : Set ( Vtx ρ ) | #t ≤ ρ };
        · aesop;
        · refine (Cardinal.mk_bounded_set_le ( Vtx ρ ) ρ).trans (le_of_eq ?_);
          rw [ mk_Vtx ρ hρ ];
          rw [ max_eq_left ( by exact le_trans ( by exact Cardinal.aleph0_le_continuum ) ( Cardinal.power_le_power_left two_ne_zero hρ ) ), Erdos593.pow_two_pow_self ρ hρ ];
      exact le_trans ( by simp +decide ) ( Cardinal.power_le_power_right h_card_pi );
    refine le_trans (le_of_eq ?_) (h_card.trans ?_);
    · fapply Cardinal.mk_congr;
      exact ⟨ fun X => fun i => ⟨ X.val i, X.property i ⟩, fun X => ⟨ fun i => X i, fun i => X i |>.2 ⟩, fun X => rfl, fun X => rfl ⟩;
    · calc ((2 : Cardinal.{u}) ^ ρ) ^ #Ilab ≤ ((2 : Cardinal.{u}) ^ ρ) ^ ρ :=
            Cardinal.power_le_power_left (ne_of_gt (Cardinal.power_pos _ (by norm_num))) hI
        _ = (2 : Cardinal.{u}) ^ ρ := Erdos593.pow_two_pow_self ρ hρ

set_option maxHeartbeats 4000000 in
theorem mk_edgeSet_le {S : Type u} (G : SimpleGraph S) {ρ : Cardinal.{u}}
    (hρ : ℵ₀ ≤ ρ) (hS : #S ≤ ρ) : #G.edgeSet ≤ ρ := by
  refine' le_trans _ ( show ρ * ρ ≤ ρ from _ );
  · refine' le_trans ( Cardinal.mk_subtype_le _ ) _;
    refine' le_trans _ ( mul_le_mul hS hS ( by positivity ) ( by positivity ) );
    refine (Cardinal.mk_le_of_surjective Sym2.mk_surjective).trans (le_of_eq ?_);
    rw [Cardinal.mk_prod, Cardinal.lift_id]
  · rw [ Cardinal.mul_eq_self ] ; aesop

set_option maxHeartbeats 4000000 in
theorem exists_copy {ρ : Cardinal.{u}} (hρ : ℵ₀ ≤ ρ) {Ilab : Type u} (hI : #Ilab ≤ ρ)
    {S : Type u} (hS : #S ≤ ρ) (q : Ordinal.{u} → Ordinal.{u}) (a : Lev ρ) :
    ∃ f : {X : Ilab → Set (Vtx ρ) // IsReservoir q a X} → Fib ρ → S → Vtx ρ,
      (∀ X η s, (f X η s).1 = a) ∧
      Function.Injective
        (fun p : ({X : Ilab → Set (Vtx ρ) // IsReservoir q a X} × Fib ρ × S) =>
          f p.1 p.2.1 p.2.2) := by
  obtain ⟨e, he⟩ : ∃ e : ({X : Ilab → Set (Vtx ρ) // IsReservoir q a X} × Fib ρ × S) ↪ Fib ρ, True := by
    refine' ⟨ _, trivial ⟩;
    refine' ( Cardinal.lift_mk_le'.mp _ ) |> Classical.choice;
    simp +zetaDelta at *;
    refine' le_trans ( mul_le_mul' ( stage_capacity hρ hI q a ) ( mul_le_mul' le_rfl hS ) ) _;
    rw [ ← mul_assoc, Cardinal.mul_eq_self ];
    · rw [ Cardinal.mul_eq_left ];
      · exact le_trans hρ ( le_of_lt ( Cardinal.cantor _ ) );
      · exact le_of_lt ( Cardinal.cantor ρ );
      · exact ne_of_gt ( lt_of_lt_of_le ( Cardinal.aleph0_pos ) hρ );
    · exact le_trans hρ ( le_of_lt ( Cardinal.cantor _ ) );
  refine' ⟨ fun X η s => ⟨ a, e ⟨ X, η, s ⟩ ⟩, _, _ ⟩ <;> simp +decide [ Function.Injective ]

set_option maxHeartbeats 4000000 in
theorem exists_phi {ρ : Cardinal.{u}} (hρ : ℵ₀ ≤ ρ) {S : Type u} {Ilab : Type u}
    {G : SimpleGraph S} (lbl : G.edgeSet → Ilab) (hE : #G.edgeSet ≤ ρ)
    (q : Ordinal.{u} → Ordinal.{u}) (a : Lev ρ)
    (X : {X : Ilab → Set (Vtx ρ) // IsReservoir q a X}) :
    ∃ φ : G.edgeSet → Vtx ρ,
      (∀ e, (X.val (lbl e)).Nonempty → φ e ∈ X.val (lbl e)) ∧
      Set.InjOn φ {e | (X.val (lbl e)).Nonempty} := by
  have h_card_le : ∀ i : Ilab, ∃ (f : {e : G.edgeSet // lbl e = i} → Vtx ρ), (∀ (ee : {e : G.edgeSet // lbl e = i}), (X.val i).Nonempty → f ee ∈ X.val i) ∧ Function.Injective f := by
    intro i
    by_cases hX : (X.val i).Nonempty;
    · obtain ⟨f, hf⟩ : ∃ f : {e : G.edgeSet // lbl e = i} ↪ ↥(X.val i), True := by
        have h_card_le : #(X.val i) = ρ := by
          exact X.2.2.1 i |> Or.resolve_left <| by aesop;
        have h_card_le : #{e : G.edgeSet // lbl e = i} ≤ ρ := by
          exact le_trans ( Cardinal.mk_subtype_le _ ) hE;
        exact ⟨ Classical.choice <| Cardinal.lift_mk_le'.mp <| by aesop, trivial ⟩;
      exact ⟨ fun ee => f ee, fun ee _ => f ee |>.2, Subtype.val_injective.comp f.injective ⟩;
    · have h_card_le : #{e : G.edgeSet // lbl e = i} ≤ Cardinal.mk (Vtx ρ) := by
        refine' le_trans _ ( le_trans hE _ );
        · exact Cardinal.mk_subtype_le _;
        · rw [ Erdos593.mk_Vtx ρ hρ ];
          exact le_of_lt ( Cardinal.cantor _ );
      have := Cardinal.le_mk_iff_exists_set.mp h_card_le;
      obtain ⟨ p, hp ⟩ := this;
      have := Cardinal.eq.1 hp.symm;
      exact ⟨ fun x => this.some x |>.1, by tauto, fun x y hxy => by simpa [ Subtype.ext_iff ] using this.some.injective <| Subtype.ext hxy ⟩;
  choose f hf₁ hf₂ using h_card_le;
  refine' ⟨ fun e => f ( lbl e ) ⟨ e, rfl ⟩, _, _ ⟩ <;> simp_all +decide [ Set.InjOn ];
  intro e₁ he₁ he₁' e₂ he₂ he₂' h; have := X.2.2.2.1; simp_all +decide [ Set.disjoint_left ] ;
  grind

set_option maxHeartbeats 4000000 in
theorem exists_calibData (h3 : E3_EGH_P.{u}) (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) :
    Nonempty (CalibData μ) := by

  have hρ : ℵ₀ ≤ rhoC μ := le_trans hμ (le_of_lt (Cardinal.cantor μ))

  obtain ⟨S, G, Ilab, hSρ, hIρ, lbl, hP0⟩ := h3 (rhoC μ) hρ

  have hP : SimpleGraph.PropertyP G lbl (Order.succ μ) :=
    hP0.mono (succ_le_deltaRho hμ)

  obtain ⟨q, hq1, hq2⟩ := cofinal_fibres (Order.succ μ) (rhoC μ)
    (le_trans hμ (le_of_lt (Order.lt_succ μ))) (succ_le_two_pow μ)

  have hIle : #Ilab ≤ rhoC μ := le_of_eq hIρ
  have hSle : #S ≤ rhoC μ := le_of_eq hSρ
  choose cf cf_lev cf_inj using
    (fun a => exists_copy hρ hIle hSle q a :
      ∀ a : Lev (rhoC μ), ∃ f : _ → Fib (rhoC μ) → S → Vtx (rhoC μ),
        (∀ X η s, (f X η s).1 = a) ∧ _)

  have hE : #G.edgeSet ≤ rhoC μ := mk_edgeSet_le G hρ hSle
  choose pf pf_mem pf_inj using
    (fun a X => exists_phi hρ lbl hE q a X :
      ∀ (a : Lev (rhoC μ)) (X : {X : Ilab → Set (Vtx (rhoC μ)) // IsReservoir q a X}),
        ∃ φ : G.edgeSet → Vtx (rhoC μ), _ ∧ _)
  exact ⟨{
    hμ := hμ
    S := S
    G := G
    Ilab := Ilab
    hIlab := hIρ
    hS := hSle
    lbl := lbl
    hP := hP
    q := q
    hq1 := hq1
    hq2 := hq2
    copy := cf
    copy_lev := fun a X η s => cf_lev a X η s
    copy_inj := cf_inj
    phi := pf
    phi_mem := pf_mem
    phi_inj := pf_inj }⟩

end Erdos593
end

-- ReservoirLower
section
open Cardinal Ordinal


namespace Erdos593

universe u

namespace CalibData

variable {μ : Cardinal.{u}} (D : CalibData μ)

set_option maxHeartbeats 4000000 in
theorem Dsmall_lt (hμ : ℵ₀ ≤ μ) {θ : Cardinal.{u}} (hθ : θ < Order.succ μ)
    (c : Vtx (rhoC μ) → θ.out) :
    #({v : Vtx (rhoC μ) | #({w | c w = c v}) < rhoC μ}) < rhoC μ := by
  have hρ : ℵ₀ ≤ rhoC μ := le_trans hμ (le_of_lt (Cardinal.cantor μ))
  have hpos : (0 : Cardinal) < rhoC μ := lt_of_lt_of_le Cardinal.aleph0_pos hρ
  refine lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset
    (t := ⋃ a : θ.out, {v : Vtx (rhoC μ) | c v = a ∧ #({w | c w = a}) < rhoC μ}) ?_) ?_
  · intro x hx
    exact Set.mem_iUnion.2 ⟨c x, rfl, hx⟩
  · refine small_union (rhoC μ) μ hρ (cf_two_pow μ hμ) ?_
      (fun a => {v : Vtx (rhoC μ) | c v = a ∧ #({w | c w = a}) < rhoC μ}) ?_
    · rw [Cardinal.mk_out]; exact Order.lt_succ_iff.mp hθ
    · intro a
      show #({v : Vtx (rhoC μ) | c v = a ∧ #({w | c w = a}) < rhoC μ}) < rhoC μ
      by_cases ha : #({w | c w = a}) < rhoC μ
      · exact lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset (fun x hx => hx.1)) ha
      · have he : {v : Vtx (rhoC μ) | c v = a ∧ #({w | c w = a}) < rhoC μ} = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro v hv; exact ha hv.2
        rw [he]; simpa using hpos

set_option maxHeartbeats 4000000 in
theorem exceptional_subsingleton {θ : Cardinal.{u}} (c : Vtx (rhoC μ) → θ.out)
    (a : θ.out) (hlarge : rhoC μ ≤ #({v | c v = a})) :
    {ξ : Ordinal.{u} | #(↥(({v | c v = a} : Set (Vtx (rhoC μ))) \ {v | D.q (lrank v.1) = ξ})) < rhoC μ}.Subsingleton := by
  intro ξ hξ ζ hζ;
  contrapose! hlarge;
  refine' lt_of_le_of_lt _ ( Cardinal.add_lt_of_lt _ hξ hζ );
  · refine' le_trans _ ( Cardinal.mk_union_le _ _ );
    refine' Cardinal.mk_le_mk_of_subset _;
    grind;
  · exact le_trans D.hμ ( le_of_lt ( Cardinal.cantor μ ) )

set_option maxHeartbeats 4000000 in
theorem exists_xi {θ : Cardinal.{u}} (hθ : θ < Order.succ μ) (c : Vtx (rhoC μ) → θ.out) :
    ∃ ξ : Ordinal.{u}, ξ < (Order.succ μ).ord ∧
      ∀ a : θ.out, rhoC μ ≤ #({v | c v = a}) →
        rhoC μ ≤ #(↥(({v | c v = a} : Set (Vtx (rhoC μ))) \ {v | D.q (lrank v.1) = ξ})) := by
  by_contra! h;

  set T := (Order.succ μ).ord.ToType
  have hT : #T = Order.succ μ := by
    rw [Cardinal.mk_toType, Cardinal.card_ord]
  choose! F hF₁ hF₂ using fun lv : T => h ( Ordinal.typein ( α := T ) ( · < · ) lv ) ( Ordinal.typein_lt_self lv );

  have hF_inj : Function.Injective F := by
    intro lv lv' hF;
    have := D.exceptional_subsingleton c ( F lv ) ( hF₁ lv );
    exact Ordinal.typein_injective ( · < · ) ( this ( hF₂ lv ) ( by simpa [ hF ] using hF₂ lv' ) );
  have hF_card : #T ≤ #θ.out := by
    exact Cardinal.mk_le_of_injective hF_inj;
  rw [hT, Cardinal.mk_out] at hF_card
  exact absurd hθ (not_lt.mpr hF_card)

set_option maxHeartbeats 4000000 in
theorem exists_level_above (Y : Set (Vtx (rhoC μ))) (hY : #Y ≤ rhoC μ)
    (ξ : Ordinal.{u}) (hξ : ξ < (Order.succ μ).ord) :
    ∃ lv : Lev (rhoC μ), D.q (lrank lv) = ξ ∧ ∀ v ∈ Y, v.1 < lv := by

  set f : Y → Ordinal := fun v => lrank v.val.1;

  have hs : ⨆ v : Y, f v < Rord (rhoC μ) := by
    apply Ordinal.iSup_lt_ord_lift;
    · have hcof : (Rord (rhoC μ)).cof = Order.succ (rhoC μ) := by
        exact Cardinal.IsRegular.cof_eq ( Cardinal.isRegular_succ ( by exact le_trans D.hμ ( le_of_lt ( Cardinal.cantor μ ) ) ) );
      exact hcof.symm ▸ lt_of_le_of_lt ( by simpa ) ( Order.lt_succ ( rhoC μ ) );
    · exact fun v => Ordinal.typein_lt_self _;
  obtain ⟨α, hα⟩ : ∃ α : Ordinal, ⨆ v : Y, f v < α ∧ α < Rord (rhoC μ) ∧ D.q α = ξ := by
    obtain ⟨α, hα⟩ : ∃ α : Ordinal, ⨆ v : Y, f v < α ∧ α < Rord (rhoC μ) ∧ D.q α = ξ := by
      have := D.hq2 ξ hξ (Order.succ (⨆ v : Y, f v)) (by
      refine' lt_of_le_of_ne _ _;
      · exact Order.succ_le_of_lt hs;
      · intro h;
        have := D.hμ;
        have := Cardinal.isRegular_succ ( show ℵ₀ ≤ rhoC μ from le_trans this ( le_of_lt ( Cardinal.cantor μ ) ) );
        have := this.2; simp_all +decide [ Rord ] ;
        rw [ ← h ] at this;
        rw [ Ordinal.cof_add_one ] at this ; norm_num at this;
        exact absurd this ( ne_of_gt ( Cardinal.power_pos _ ( by norm_num ) ) ))
      exact ⟨ this.choose, lt_of_lt_of_le ( Order.lt_succ _ ) this.choose_spec.1, this.choose_spec.2.1, this.choose_spec.2.2 ⟩;
    use α;
  obtain ⟨lv, hlv⟩ : ∃ lv : Lev (rhoC μ), lrank lv = α := by
    have h_enum : ∀ α : Ordinal, α < Rord (rhoC μ) → ∃ lv : Lev (rhoC μ), lrank lv = α := by
      intro α hα;
      have h_enum : ∀ α : Ordinal, α < Rord (rhoC μ) → ∃ lv : Lev (rhoC μ), lrank lv = α := by
        intro α hα
        have h_enum : α < Ordinal.type (· < · : Lev (rhoC μ) → Lev (rhoC μ) → Prop) := by
          convert hα using 1;
          convert Ordinal.type_toType ( Rord ( rhoC μ ) ) using 1
        exact ⟨ Ordinal.enum ( · < · ) ⟨ α, h_enum ⟩, by simp +decide [ lrank ] ⟩;
      exact h_enum α hα;
    exact h_enum α hα.2.1;
  refine' ⟨ lv, _, _ ⟩ <;> simp_all +decide [ lrank ];
  intro a b hab;
  exact Ordinal.typein_lt_typein ( · < · ) |>.1 ( hlv.symm ▸ lt_of_le_of_lt ( Ordinal.le_iSup ( fun v : Y => lrank v.val.1 ) ⟨ ( a, b ), hab ⟩ ) hα.1 )

set_option maxHeartbeats 4000000 in
theorem exists_disjoint_copy (Bad : Set (Vtx (rhoC μ))) (hBad : #Bad < rhoC μ)
    (lv : Lev (rhoC μ))
    (X : {X : D.Ilab → Set (Vtx (rhoC μ)) // IsReservoir D.q lv X}) :
    ∃ η : Fib (rhoC μ), ∀ s : D.S, D.copy lv X η s ∉ Bad := by
  contrapose! hBad; have := D.copy_inj lv; simp_all +decide [ Function.Injective ] ;
  choose f hf using hBad;
  refine' le_trans _ ( Cardinal.mk_le_mk_of_subset <| show Set.range ( fun η : Fib ( rhoC μ ) => D.copy lv X η ( f η ) ) ⊆ Bad from Set.range_subset_iff.mpr hf );
  rw [ Cardinal.mk_range_eq ];
  · rw [ Cardinal.mk_out ];
    exact le_of_lt ( Cardinal.cantor _ );
  · intro η η' h; specialize this _ X.2 _ _ _ X.2 _ _ h; aesop;

set_option maxHeartbeats 4000000 in
theorem reservoir_capture {θ : Cardinal.{u}} (hθ : θ < Order.succ μ)
    (c : Vtx (rhoC μ) → θ.out) :
    ∃ (a : Lev (rhoC μ))
      (X : {X : D.Ilab → Set (Vtx (rhoC μ)) // IsReservoir D.q a X})
      (η : Fib (rhoC μ)) (bigLabel : θ.out → D.Ilab),
      (∀ s : D.S, (X.val (bigLabel (c (D.copy a X η s)))).Nonempty) ∧
      (∀ s : D.S, X.val (bigLabel (c (D.copy a X η s))) ⊆ {v | c v = c (D.copy a X η s)}) := by
  have hμ : ℵ₀ ≤ μ := D.hμ
  have hρ : ℵ₀ ≤ rhoC μ := le_trans hμ (le_of_lt (Cardinal.cantor μ))
  have hpos : (0 : Cardinal) < rhoC μ := lt_of_lt_of_le Cardinal.aleph0_pos hρ
  have hθμ : θ ≤ μ := Order.lt_succ_iff.mp hθ
  obtain ⟨ξ, hξord, hξlarge⟩ := D.exists_xi hθ c
  have hemb : Nonempty (θ.out ↪ D.Ilab) := by
    rw [← Cardinal.le_def, Cardinal.mk_out, D.hIlab]
    exact le_trans hθμ (le_of_lt (Cardinal.cantor μ))
  obtain ⟨bigLabelE⟩ := hemb
  set bigLabel : θ.out → D.Ilab := ⇑bigLabelE with hblab
  have hbig : Function.Injective bigLabel := bigLabelE.injective
  set diff : θ.out → Set (Vtx (rhoC μ)) :=
    fun a => (({v | c v = a} : Set (Vtx (rhoC μ))) \ {v | D.q (lrank v.1) = ξ}) with hdiff
  have hZex : ∀ a : θ.out, ∃ Z : Set (Vtx (rhoC μ)),
      (rhoC μ ≤ #(diff a) → Z ⊆ diff a ∧ #Z = rhoC μ) ∧
      (#(diff a) < rhoC μ → Z = ∅) := by
    intro a
    by_cases ha : rhoC μ ≤ #(diff a)
    · obtain ⟨Z, hZsub, hZcard⟩ := Cardinal.le_mk_iff_exists_subset.mp ha
      exact ⟨Z, fun _ => ⟨hZsub, hZcard⟩, fun h => absurd h (not_lt.mpr ha)⟩
    · exact ⟨∅, fun h => absurd h ha, fun _ => rfl⟩
  choose Z hZ1 hZ2 using hZex
  have hZle : ∀ a, #(Z a) ≤ rhoC μ := by
    intro a
    by_cases ha : rhoC μ ≤ #(diff a)
    · exact le_of_eq (hZ1 a ha).2
    · rw [hZ2 a (not_le.mp ha)]; simp
  set X : D.Ilab → Set (Vtx (rhoC μ)) := fun i => ⋃ (a : θ.out) (_ : bigLabel a = i), Z a with hXdef
  have hXbig : ∀ a, X (bigLabel a) = Z a := by
    intro a; ext v
    simp only [hXdef, Set.mem_iUnion]
    constructor
    · rintro ⟨a', ha', hv⟩; rwa [hbig ha'] at hv
    · intro hv; exact ⟨a, rfl, hv⟩
  have hXsub : ∀ i, X i ⊆ ⋃ a, Z a := by
    intro i v hv
    simp only [hXdef, Set.mem_iUnion] at hv ⊢
    obtain ⟨a, _, hv⟩ := hv; exact ⟨a, hv⟩
  have hUcard : #(↥(⋃ a, Z a)) ≤ rhoC μ := by
    refine le_trans (Cardinal.mk_iUnion_le Z) ?_
    have h1 : #θ.out ≤ rhoC μ := by
      rw [Cardinal.mk_out]; exact le_trans hθμ (le_of_lt (Cardinal.cantor μ))
    calc #θ.out * ⨆ a, #(Z a) ≤ rhoC μ * rhoC μ :=
            mul_le_mul' h1 (ciSup_le' hZle)
      _ = rhoC μ := Cardinal.mul_eq_self hρ
  obtain ⟨lv, hlvq, hlvabove⟩ := D.exists_level_above (⋃ a, Z a) hUcard ξ hξord
  have hres : IsReservoir D.q lv X := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i v hv
      exact hlvabove v (hXsub i hv)
    · intro i
      by_cases hi : ∃ a, bigLabel a = i
      · obtain ⟨a, rfl⟩ := hi
        rw [hXbig a]
        by_cases ha : rhoC μ ≤ #(diff a)
        · exact Or.inr (hZ1 a ha).2
        · exact Or.inl (hZ2 a (not_le.mp ha))
      · left
        ext v; simp only [hXdef, Set.mem_iUnion, Set.mem_empty_iff_false, iff_false]
        rintro ⟨a, ha, _⟩; exact hi ⟨a, ha⟩
    · intro i j hij hi hj
      obtain ⟨v, hv⟩ := hi
      simp only [hXdef, Set.mem_iUnion] at hv
      obtain ⟨a, hai, _⟩ := hv
      obtain ⟨w, hw⟩ := hj
      simp only [hXdef, Set.mem_iUnion] at hw
      obtain ⟨a', ha'j, _⟩ := hw
      subst hai; subst ha'j
      have haa' : a ≠ a' := fun h => hij (by rw [h])
      rw [hXbig a, hXbig a']
      rw [Set.disjoint_left]
      intro x hxa hxa'
      have hda : rhoC μ ≤ #(diff a) := by
        by_contra h; rw [hZ2 a (not_le.mp h)] at hxa; exact hxa
      have hda' : rhoC μ ≤ #(diff a') := by
        by_contra h; rw [hZ2 a' (not_le.mp h)] at hxa'; exact hxa'
      have e1 : c x = a := ((hZ1 a hda).1 hxa).1
      have e2 : c x = a' := ((hZ1 a' hda').1 hxa').1
      exact haa' (by rw [← e1, e2])
    · intro i v hv
      have hvU : v ∈ ⋃ a, Z a := hXsub i hv
      simp only [Set.mem_iUnion] at hvU
      obtain ⟨a, hva⟩ := hvU
      have hda : rhoC μ ≤ #(diff a) := by
        by_contra h; rw [hZ2 a (not_le.mp h)] at hva; exact hva
      have hvdiff : v ∈ diff a := (hZ1 a hda).1 hva
      rw [hlvq]
      exact fun hq => hvdiff.2 hq
  obtain ⟨η, hη⟩ := D.exists_disjoint_copy
    {v : Vtx (rhoC μ) | #({w | c w = c v}) < rhoC μ} (Dsmall_lt hμ hθ c) lv ⟨X, hres⟩
  refine ⟨lv, ⟨X, hres⟩, η, bigLabel, ?_, ?_⟩
  · intro s
    set p := c (D.copy lv ⟨X, hres⟩ η s) with hpdef
    have hnotsmall : ¬ (#({w | c w = p}) < rhoC μ) := hη s
    have hlarge : rhoC μ ≤ #({v | c v = p}) := not_lt.mp hnotsmall
    have hdifflarge : rhoC μ ≤ #(diff p) := hξlarge p hlarge
    show (X (bigLabel p)).Nonempty
    rw [hXbig p, ← Set.nonempty_coe_sort]
    exact Cardinal.mk_ne_zero_iff.mp (by rw [(hZ1 p hdifflarge).2]; exact ne_of_gt hpos)
  · intro s
    set p := c (D.copy lv ⟨X, hres⟩ η s) with hpdef
    have hnotsmall : ¬ (#({w | c w = p}) < rhoC μ) := hη s
    have hlarge : rhoC μ ≤ #({v | c v = p}) := not_lt.mp hnotsmall
    have hdifflarge : rhoC μ ≤ #(diff p) := hξlarge p hlarge
    show X (bigLabel p) ⊆ {v | c v = p}
    rw [hXbig p]
    exact fun v hv => ((hZ1 p hdifflarge).1 hv).1

set_option maxHeartbeats 4000000 in
theorem L_lower : ∀ θ, θ < Order.succ μ → ¬ (D.L).ColorableBy θ := by
  intro θ hθ hcolorable
  obtain ⟨c, hc⟩ := hcolorable;
  obtain ⟨ a, X, η, bigLabel, h1, h2 ⟩ := D.reservoir_capture hθ c;
  obtain ⟨ p, hp ⟩ := D.hP θ hθ ( fun s => c ( D.copy a X η s ) );
  obtain ⟨ x, y, hxy, hi, hx, hy ⟩ := hp ( bigLabel p );
  have h_contradiction : c (D.phi a X ⟨s(x, y), hxy⟩) = p := by
    have := D.phi_mem a X ⟨ s(x, y), hxy ⟩ ?_;
    · grind;
    · grind;
  have := hc _ ( D.mem_edgeSetL.mpr ⟨ a, X, η, ⟨ s(x, y), hxy ⟩, by
    grind, rfl ⟩ );
  simp_all +decide [ CalibData.edgeBase ]

end CalibData

end Erdos593
end

-- CycleCollapse
section
open Cardinal Ordinal

namespace Erdos593

universe u

variable {α : Type u} {A : SimpleGraph α} {κ : Cardinal.{u}}

def Node.comparable (σ τ : Node A κ) : Prop :=
  σ = τ ∨ Node.pre A κ σ τ ∨ Node.pre A κ τ σ

def Node.wpre (σ τ : Node A κ) : Prop :=
  σ = τ ∨ Node.pre A κ σ τ

theorem Node.pre.pos_lt {σ τ : Node A κ} (h : Node.pre A κ σ τ) : σ.pos < τ.pos :=
  h.1

theorem Node.pre.agree {σ τ : Node A κ} (h : Node.pre A κ σ τ)
    (q : Idx κ) (hq : q < σ.pos) :
    τ.seq ⟨q, lt_trans hq h.1⟩ = σ.seq ⟨q, hq⟩ :=
  h.2 q hq

theorem Node.wpre_pos_eq {σ τ : Node A κ} (h : Node.wpre σ τ) (hpos : τ.pos ≤ σ.pos) :
    σ = τ := by
  rcases h with h | h
  · exact h
  · exact absurd h.1 (not_lt.mpr hpos)

theorem Node.pre.trans {ρ σ τ : Node A κ} (h1 : Node.pre A κ ρ σ)
    (h2 : Node.pre A κ σ τ) : Node.pre A κ ρ τ := by
  refine ⟨lt_trans h1.1 h2.1, ?_⟩
  intro q hq
  rw [h2.2 q (lt_trans hq h1.1), h1.2 q hq]

theorem Node.wpre.trans_pre {ρ σ τ : Node A κ} (h1 : Node.wpre ρ σ)
    (h2 : Node.pre A κ σ τ) : Node.wpre ρ τ := by
  rcases h1 with rfl | h1
  · exact Or.inr h2
  · exact Or.inr (h1.trans h2)

theorem Node.wpre_of_comparable {ρ a b : Node A κ} (hρa : Node.wpre ρ a)
    (hcomp : Node.comparable a b) (hpos : ρ.pos ≤ b.pos) :
    Node.wpre ρ b := by
  rcases hρa with ( rfl | hρa ) <;> rcases hcomp with ( rfl | hcomp | hcomp ) <;> simp_all +decide [ Node.wpre ];
  · exact absurd hpos ( not_le_of_gt hcomp.1 );
  · exact Or.inr ( Node.pre.trans hρa hcomp );
  · cases lt_or_eq_of_le hpos <;> simp_all +decide [ pre ];
    · grind only [Subtype.mk_eq_mk];
    · cases ρ ; cases b ; aesop

theorem Node.seqAt_eq_of_comparable {p q : Node A κ} (hcomp : Node.comparable p q)
    {d : Idx κ} (hp : d < p.pos) (hq : d < q.pos) :
    p.seq ⟨d, hp⟩ = q.seq ⟨d, hq⟩ := by
  rcases hcomp with ( rfl | hcomp | hcomp );
  · grind;
  · exact hcomp.agree d hp ▸ rfl;
  · exact hcomp.agree d hq ▸ rfl

theorem liftEdge_fst_mem {σ τ : Node A κ} {x y z : α}
    {p : Node A κ × α} (hp : p ∈ ({(σ, x), (σ, y), (τ, z)} : Set (Node A κ × α))) :
    p.1 = σ ∨ p.1 = τ := by
  rcases hp with rfl | rfl | rfl
  · left; rfl
  · left; rfl
  · right; rfl

theorem bergeEdge_nodes_comparable {F : FTS} {f : F.V → Node A κ × α}
    (e : Finset F.V) (he : (f '' (↑e : Set F.V)) ∈ (liftHG A κ).edges)
    {u w : F.V} (hu : u ∈ e) (hw : w ∈ e) :
    Node.comparable (f u).1 (f w).1 := by
  obtain ⟨σ, τ, x, y, z, hpre, hseq, hset⟩ := he
  have hfu : f u ∈ ({(σ, x), (σ, y), (τ, z)} : Set (Node A κ × α)) := by
    rw [← hset]; exact ⟨u, hu, rfl⟩
  have hfw : f w ∈ ({(σ, x), (σ, y), (τ, z)} : Set (Node A κ × α)) := by
    rw [← hset]; exact ⟨w, hw, rfl⟩
  rcases liftEdge_fst_mem hfu with hu' | hu' <;> rcases liftEdge_fst_mem hfw with hw' | hw' <;>
    rw [Node.comparable, hu', hw']
  · left; rfl
  · right; left; exact hpre
  · right; right; exact hpre
  · left; rfl

theorem rising_base {F : FTS} {f : F.V → Node A κ × α}
    (e : Finset F.V) (he : (f '' (↑e : Set F.V)) ∈ (liftHG A κ).edges)
    {u w : F.V} (hu : u ∈ e) (hw : w ∈ e) (hpre : Node.pre A κ (f u).1 (f w).1) :
    ∃ x y : α, x ≠ y ∧
      ((f w).1.seq ⟨(f u).1.pos, hpre.1⟩ : Sym2 α) = s(x, y) ∧
      ((f u).1, x) ∈ (f '' (↑e : Set F.V)) ∧ ((f u).1, y) ∈ (f '' (↑e : Set F.V)) := by
  obtain ⟨ σ', τ', a, b, cc, hpre', hseq', hset ⟩ := he;

  have h_eq : (f u).1 = σ' ∧ (f w).1 = τ' := by
    have h_eq : (f u).1 ∈ ({σ', τ'} : Set (Node A κ)) ∧ (f w).1 ∈ ({σ', τ'} : Set (Node A κ)) := by
      exact ⟨ by simpa using liftEdge_fst_mem ( hset ▸ Set.mem_image_of_mem f hu ), by simpa using liftEdge_fst_mem ( hset ▸ Set.mem_image_of_mem f hw ) ⟩;
    cases h_eq.1 <;> cases h_eq.2 <;> simp_all +decide [ Node.pre ];
    exact absurd hpre.choose ( not_lt_of_gt hpre'.1 );
  have := ( τ'.seq ⟨ σ'.pos, hpre'.1 ⟩ ) |>.2; simp_all +decide [ SimpleGraph.mem_edgeSet ] ;
  exact ⟨ a, b, this.ne, by aesop ⟩

theorem Node.seqAt_Sym2_eq_of_comparable {p q : Node A κ} (hcomp : Node.comparable p q)
    {d : Idx κ} (hp : d < p.pos) (hq : d < q.pos) :
    ((p.seq ⟨d, hp⟩ : Sym2 α)) = ((q.seq ⟨d, hq⟩ : Sym2 α)) :=
  congrArg (fun e : A.edgeSet => (e : Sym2 α)) (Node.seqAt_eq_of_comparable hcomp hp hq)

theorem zmod_cyclic_induction {m : ℕ} [NeZero m] {P : ZMod m → Prop} (j0 : ZMod m)
    (hj0 : P j0) (hstep : ∀ i, P i → P (i + 1)) (i : ZMod m) : P i := by
  have h_ind : ∀ n : ℕ, P (j0 + n) := by
    intro n; induction n <;> simp_all +decide [ ← add_assoc ] ;
  convert h_ind ( i - j0 |> ZMod.val ) ; aesop;

theorem consecutive_comparable {F : FTS} {f : F.V → Node A κ × α}
    (hfe : ∀ e ∈ F.edges, (f '' (↑e : Set F.V)) ∈ (liftHG A κ).edges)
    (c : BergeCycle F) (i : ZMod c.m) :
    Node.comparable (f (c.v i)).1 (f (c.v (i + 1))).1 :=
  bergeEdge_nodes_comparable (c.e i).1 (hfe _ (c.e i).2) (c.mem_left i) (c.mem_right i)

theorem seqAt_const_along {m : ℕ} (g : ZMod m → Node A κ)
    (hcomp : ∀ i : ZMod m, Node.comparable (g i) (g (i + 1)))
    (σ : Node A κ) (start : ZMod m) (n : ℕ)
    (hpre : ∀ j : ℕ, j ≤ n → Node.pre A κ σ (g (start + (j : ZMod m)))) :
    ((g (start + (n : ZMod m))).seq ⟨σ.pos, (hpre n le_rfl).1⟩ : Sym2 α)
      = ((g (start + ((0 : ℕ) : ZMod m))).seq ⟨σ.pos, (hpre 0 (Nat.zero_le n)).1⟩ : Sym2 α) := by
  induction' n with n ih;
  · rfl;
  · convert ih ( fun j hj => hpre j ( Nat.le_succ_of_le hj ) ) using 1;
    convert Node.seqAt_Sym2_eq_of_comparable _ _ _ using 1;
    convert hcomp ( start + n ) |> fun h => h.symm using 1 ; push_cast ; ring;
    simp +decide [ add_comm, Node.comparable ];
    grind

theorem exists_first_return {m : ℕ} [NeZero m] (P : ZMod m → Prop)
    (start : ZMod m) (hstart : ¬ P start)
    (hex : ∃ t : ℕ, P (start + (t : ZMod m))) :
    ∃ n0 : ℕ, 1 ≤ n0 ∧ n0 ≤ m - 1 ∧ P (start + (n0 : ZMod m)) ∧
      ∀ j : ℕ, j < n0 → ¬ P (start + (j : ZMod m)) := by
  obtain ⟨t, ht⟩ := hex
  have ht_lt : t % m < m := by
    exact Nat.mod_lt _ ( NeZero.pos m );
  have h_exists_n0 : ∃ n0, 1 ≤ n0 ∧ n0 ≤ m - 1 ∧ P (start + (n0 : ZMod m)) := by
    refine' ⟨ t % m, Nat.pos_of_ne_zero _, Nat.le_sub_one_of_lt ht_lt, _ ⟩;
    · contrapose! hstart; simp_all ;
      rw [ ← Nat.dvd_iff_mod_eq_zero ] at hstart; obtain ⟨ k, hk ⟩ := hstart; simp_all ;
    · simpa [ ZMod.natCast_mod ] using ht;
  obtain ⟨n0, hn0⟩ : ∃ n0, n0 ∈ {n | 1 ≤ n ∧ n ≤ m - 1 ∧ P (start + (n : ZMod m))} ∧ ∀ n ∈ {n | 1 ≤ n ∧ n ≤ m - 1 ∧ P (start + (n : ZMod m))}, n0 ≤ n := by
    apply_rules [ Set.exists_min_image ];
    exact Set.finite_iff_bddAbove.mpr ⟨ m - 1, fun n hn => hn.2.1 ⟩;
  exact ⟨ n0, hn0.1.1, hn0.1.2.1, hn0.1.2.2, fun j hj hj' => not_lt_of_ge ( hn0.2 j ⟨ Nat.pos_of_ne_zero fun h => by aesop, Nat.le_trans ( Nat.le_of_lt hj ) hn0.1.2.1, hj' ⟩ ) hj ⟩

theorem base_adj {F : FTS} {f : F.V → Node A κ × α} (hf : Function.Injective f)
    (e : Finset F.V) (he : (f '' (↑e : Set F.V)) ∈ (liftHG A κ).edges)
    {u w : F.V} (hu : u ∈ e) (hw : w ∈ e) (huw : u ≠ w)
    (hnode : (f u).1 = (f w).1) :
    A.Adj (f u).2 (f w).2 := by
  obtain ⟨ σ, τ, x, y, z, hpre, hseq, hset ⟩ := he;

  have hfu : f u ∈ ({(σ, x), (σ, y), (τ, z)} : Set (Node A κ × α)) := by
    exact hset ▸ Set.mem_image_of_mem _ hu
  have hfw : f w ∈ ({(σ, x), (σ, y), (τ, z)} : Set (Node A κ × α)) := by
    grind;
  by_cases h : ( f u ).1 = τ <;> simp_all +decide [ Function.Injective.eq_iff hf ];
  · grind only;
  · rcases hfu with ( hfu | hfu | hfu ) <;> rcases hfw with ( hfw | hfw | hfw ) <;> simp_all +decide;
    · exact False.elim ( huw ( hf ( hfu.trans hfw.symm ) ) );
    · replace hseq := congr_arg ( fun s => s ∈ SimpleGraph.edgeSet A ) hseq ; simp_all +decide [ SimpleGraph.mem_edgeSet ];
    · convert A.adj_symm ( show A.Adj x y from ?_ ) using 1;
      convert ( τ.seq ⟨ σ.pos, hpre.1 ⟩ ).2 using 1;
      simp +decide [ hseq, SimpleGraph.mem_edgeSet ];
    · exact False.elim ( huw ( hf ( hfu.trans hfw.symm ) ) )

theorem cycle_collapse {F : FTS} (hlin : F.Linear) (f : F.V → Node A κ × α)
    (hf : Function.Injective f)
    (hfe : ∀ e ∈ F.edges, (f '' (↑e : Set F.V)) ∈ (liftHG A κ).edges)
    (c : BergeCycle F) (i j : ZMod c.m) :
    (f (c.v i)).1 = (f (c.v j)).1 := by
  haveI : NeZero c.m := ⟨by have := c.hm; omega⟩

  obtain ⟨j0, -, hj0min⟩ := Finset.exists_min_image Finset.univ
    (fun t => (f (c.v t)).1.pos) ⟨i, Finset.mem_univ i⟩
  simp only [Finset.mem_univ, forall_true_left] at hj0min
  set σ := (f (c.v j0)).1 with hσdef

  have hwpre : ∀ t, Node.wpre σ (f (c.v t)).1 := fun t =>
    zmod_cyclic_induction j0 (Or.inl rfl)
      (fun i hi => Node.wpre_of_comparable hi (consecutive_comparable hfe c i) (hj0min (i+1))) t
  suffices hall : ∀ t, (f (c.v t)).1 = σ by rw [hall i, hall j]
  intro t
  by_contra hne

  obtain ⟨k, hk, hk1⟩ : ∃ k, (f (c.v k)).1 = σ ∧ (f (c.v (k+1))).1 ≠ σ := by
    by_contra hall2
    push_neg at hall2
    exact hne (zmod_cyclic_induction (P := fun s => (f (c.v s)).1 = σ) j0 rfl
      (fun s hs => hall2 s hs) t)
  have hkpre : Node.pre A κ σ (f (c.v (k+1))).1 :=
    (hwpre (k+1)).resolve_left (fun h => hk1 h.symm)

  have hex : ∃ n : ℕ, (f (c.v (k+1+(n:ZMod c.m)))).1 = σ := by
    refine ⟨(j0-(k+1)).val, ?_⟩
    have he : k+1+(((j0-(k+1)).val : ℕ):ZMod c.m) = j0 := by
      rw [ZMod.natCast_zmod_val]; ring
    rw [he]
  obtain ⟨n0, h1n0, hn0m, hPn0, hbefore⟩ :=
    exists_first_return (fun s => (f (c.v s)).1 = σ) (k+1) hk1 hex

  have hrunpre : ∀ jj : ℕ, jj < n0 → Node.pre A κ σ (f (c.v (k+1+(jj:ZMod c.m)))).1 :=
    fun jj hjj => (hwpre _).resolve_left (fun h => hbefore jj hjj h.symm)
  set kf := k+1+((n0-1:ℕ):ZMod c.m) with hkfdef
  have hcast : (n0 : ZMod c.m) = ((n0 - 1 : ℕ) : ZMod c.m) + 1 := by
    have h1 : ((n0 - 1 : ℕ) : ZMod c.m) + 1 = (((n0 - 1) + 1 : ℕ) : ZMod c.m) := by norm_cast
    rw [h1, Nat.sub_add_cancel h1n0]
  have hkf1_eq : kf + 1 = k+1+(n0:ZMod c.m) := by rw [hkfdef, hcast]; ring
  have hνkf1 : (f (c.v (kf+1))).1 = σ := by rw [hkf1_eq]; exact hPn0
  have hνkf_pre : Node.pre A κ σ (f (c.v kf)).1 := by
    rw [hkfdef]; exact hrunpre (n0-1) (by omega)

  obtain ⟨x1, y1, hxy1, hval1, hmx1, hmy1⟩ :=
    rising_base (c.e k).1 (hfe _ (c.e k).2) (c.mem_left k) (c.mem_right k) (hk.symm ▸ hkpre)
  obtain ⟨x2, y2, hxy2, hval2, hmx2, hmy2⟩ :=
    rising_base (c.e kf).1 (hfe _ (c.e kf).2) (c.mem_right kf) (c.mem_left kf) (hνkf1.symm ▸ hνkf_pre)

  simp only [hk] at hval1 hmx1 hmy1
  simp only [hνkf1] at hval2 hmx2 hmy2

  have hpre' : ∀ jj : ℕ, jj ≤ n0 - 1 →
      Node.pre A κ σ ((fun s => (f (c.v s)).1) (k+1+(jj:ZMod c.m))) :=
    fun jj hjj => hrunpre jj (by omega)
  have hca := seqAt_const_along (fun s => (f (c.v s)).1)
    (consecutive_comparable hfe c) σ (k+1) (n0-1) hpre'
  have hnode_val : ∀ {p q : Node A κ} {hp : σ.pos < p.pos} {hq : σ.pos < q.pos},
      p = q → ((p.seq ⟨σ.pos, hp⟩ : Sym2 α)) = ((q.seq ⟨σ.pos, hq⟩ : Sym2 α)) := by
    rintro p q hp hq rfl; rfl
  have hsym2 : s(x1, y1) = s(x2, y2) := by
    rw [← hval1, ← hval2]
    refine (hnode_val (p := (f (c.v (k+1))).1) (q := (f (c.v (k+1+((0:ℕ):ZMod c.m)))).1)
      (hq := (hpre' 0 (Nat.zero_le _)).1) (by simp)).trans ?_
    exact hca.symm.trans (hnode_val (p := (f (c.v (k+1+((n0-1:ℕ):ZMod c.m)))).1)
      (q := (f (c.v kf)).1) (hp := (hpre' (n0-1) le_rfl).1) (by rw [hkfdef]))

  have hmemx1kf : (σ, x1) ∈ (f '' (↑(c.e kf).1 : Set F.V)) := by
    rw [Sym2.eq_iff] at hsym2
    rcases hsym2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hmx2
    · exact hmy2
  have hmemy1kf : (σ, y1) ∈ (f '' (↑(c.e kf).1 : Set F.V)) := by
    rw [Sym2.eq_iff] at hsym2
    rcases hsym2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hmy2
    · exact hmx2

  obtain ⟨ux, huxk, hfux⟩ := hmx1
  obtain ⟨ux', huxkf, hfux'⟩ := hmemx1kf
  obtain ⟨uy, huyk, hfuy⟩ := hmy1
  obtain ⟨uy', huykf, hfuy'⟩ := hmemy1kf
  have huxeq : ux = ux' := hf (by rw [hfux, hfux'])
  have huyeq : uy = uy' := hf (by rw [hfuy, hfuy'])
  have huxy : ux ≠ uy := by
    intro h; apply hxy1
    have hfeq : f ux = f uy := by rw [h]
    rw [hfux, hfuy] at hfeq
    exact (Prod.ext_iff.mp hfeq).2
  have hkne : k ≠ kf := by
    intro h
    rw [hkfdef] at h
    have hz : (n0 : ZMod c.m) = 0 := by rw [hcast]; linear_combination -h
    have hdvd : c.m ∣ n0 := (ZMod.natCast_eq_zero_iff _ _).mp hz
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hedgene : (c.e k).1 ≠ (c.e kf).1 := by
    intro h
    exact hkne (c.einj (Subtype.ext h))
  have hcard : 1 < ((c.e k).1 ∩ (c.e kf).1).card := by
    refine Finset.one_lt_card.mpr ⟨ux, ?_, uy, ?_, huxy⟩
    · exact Finset.mem_inter.mpr ⟨huxk, huxeq ▸ huxkf⟩
    · exact Finset.mem_inter.mpr ⟨huyk, huyeq ▸ huykf⟩
  have hle := hlin (c.e k).1 (c.e k).2 (c.e kf).1 (c.e kf).2 hedgene
  omega

theorem exists_bridge_incidence {F : FTS} (hlin : F.Linear) (f : F.V → Node A κ × α)
    (hf : Function.Injective f)
    (hfe : ∀ e ∈ F.edges, (f '' (↑e : Set F.V)) ∈ (liftHG A κ).edges)
    (ed : {e : Finset F.V // e ∈ F.edges}) :
    ∃ w ∈ ed.1, IsBridgeInc F w ed := by
  obtain ⟨σ, τ, x, y, z, hpre, hseq, hset⟩ := hfe ed.1 ed.2

  have hmem : ((τ, z) : Node A κ × α) ∈ f '' (↑ed.1 : Set F.V) := by
    rw [hset]; right; right; rfl
  obtain ⟨w, hw, hfw⟩ := hmem
  refine ⟨w, hw, hw, ?_⟩
  rintro ⟨c, i, hei, hvi⟩
  haveI : Fact (1 < c.m) := ⟨by have := c.hm; omega⟩

  have hcc := cycle_collapse hlin f hf hfe c i (i + 1)
  have hvne : c.v i ≠ c.v (i + 1) := by
    intro h
    have hii : i = i + 1 := c.vinj h
    exact zero_ne_one (by linear_combination hii : (0 : ZMod c.m) = 1)

  have hwnode : (f w).1 = τ := by rw [hfw]

  have hbase : ∀ v : F.V, v ∈ ed.1 → v ≠ w → (f v).1 = σ := by
    intro v hv hvw
    have hfv : f v ∈ f '' (↑ed.1 : Set F.V) := ⟨v, hv, rfl⟩
    rw [hset] at hfv
    rcases hfv with h | h | h
    · rw [h]
    · rw [h]
    · exact absurd (hf (by rw [h, hfw])) hvw

  have hi_mem : c.v i ∈ ed.1 := by rw [← hei]; exact c.mem_left i
  have hi1_mem : c.v (i + 1) ∈ ed.1 := by rw [← hei]; exact c.mem_right i

  have hστ : σ = τ := by
    rcases hvi with hvi | hvi
    ·
      have hw' : (f (c.v (i + 1))).1 = σ :=
        hbase _ hi1_mem (fun h => hvne (hvi.trans h.symm))
      rw [← hw', ← hcc, hvi, hwnode]
    ·
      have hw' : (f (c.v i)).1 = σ :=
        hbase _ hi_mem (fun h => hvne (h.trans hvi.symm))
      rw [← hw', hcc, hvi, hwnode]
  exact absurd hpre.1 (by rw [hστ]; exact lt_irrefl _)

theorem lift_bergeCycle_graphCycle {F : FTS} (hlin : F.Linear) (f : F.V → Node A κ × α)
    (hf : Function.Injective f)
    (hfe : ∀ e ∈ F.edges, (f '' (↑e : Set F.V)) ∈ (liftHG A κ).edges)
    (c : BergeCycle F) :
    ∃ v : ZMod c.m → α, Function.Injective v ∧ ∀ i, A.Adj (v i) (v (i + 1)) := by

  have hv_inj : Function.Injective (fun i => (f (c.v i)).2) := by
    intro i j hij
    have hnode : (f (c.v i)).1 = (f (c.v j)).1 := by
      convert cycle_collapse hlin f hf hfe c i j using 1;
    have := hf ( Prod.ext hnode hij ) ; simp_all +decide [ c.vinj.eq_iff ] ;
  refine' ⟨ _, hv_inj, _ ⟩;
  intro i
  have h_edge : (f '' (↑(c.e i).1 : Set F.V)) ∈ (liftHG A κ).edges := by
    exact hfe _ ( c.e i |>.2 )
  have h_nodes : (f (c.v i)).1 = (f (c.v (i + 1))).1 := by
    exact cycle_collapse hlin f hf hfe c i ( i + 1 )
  exact base_adj hf (c.e i).1 h_edge (c.mem_left i) (c.mem_right i) (by
  intro h_eq
  have h_contra : i = i + 1 := by
    exact c.vinj h_eq
  have h_contra' : (0 : ZMod c.m) = 1 := by
    linear_combination' h_contra
  have h_contra'' : ¬(0 : ZMod c.m) = 1 := by
    haveI : Fact (1 < c.m) := ⟨by linarith [c.hm]⟩; exact zero_ne_one;
  exact h_contra'' h_contra') h_nodes

theorem bridgeSelector_of_embeds_lift {F : FTS} (hlin : F.Linear)
    (h : F.Embeds (liftHG A κ)) : Nonempty (BridgeSelector F) := by
  obtain ⟨f, hf, hfe⟩ := h
  refine ⟨⟨fun ed => (exists_bridge_incidence hlin f hf hfe ed).choose, fun ed => ?_⟩⟩
  exact (exists_bridge_incidence hlin f hf hfe ed).choose_spec.2

theorem lift_omits_of_no_bridgeSelector {F : FTS} (hlin : F.Linear)
    (hns : ¬ Nonempty (BridgeSelector F)) : ¬ F.Embeds (liftHG A κ) :=
  fun h => hns (bridgeSelector_of_embeds_lift hlin h)

theorem lift_omits_of_bergeCycle {F : FTS} (hlin : F.Linear) (c : BergeCycle F)
    (hA : ¬ ∃ v : ZMod c.m → α, Function.Injective v ∧ ∀ i, A.Adj (v i) (v (i + 1))) :
    ¬ F.Embeds (liftHG A κ) := by
  rintro ⟨f, hf, hfe⟩
  exact hA (lift_bergeCycle_graphCycle hlin f hf hfe c)

end Erdos593
end

-- NegativeDirection
section
open Cardinal Ordinal

namespace Erdos593

universe u

theorem completeGraph_hasChromatic (lam : Cardinal.{u}) :
    (SimpleGraph.toHG (⊤ : SimpleGraph lam.out)).HasChromatic lam := by
  constructor;
  · refine' ⟨ id, _ ⟩;
    intro e he; simp_all +decide [ SimpleGraph.toHG ] ;
    rcases he with ⟨ x, y, hxy, rfl ⟩ ; exact ⟨ x, by simp +decide, y, by simp +decide, hxy ⟩ ;
  · intro θ hθ hcolorable
    obtain ⟨c, hc⟩ := hcolorable
    have hinjective : Function.Injective c := by
      intro x y; have := hc; simp_all +decide [ SimpleGraph.toHG ] ;
      have := hc { x, y } ; by_cases h : x = y <;> simp_all +decide ;
      specialize this x y h rfl; tauto;
    exact hθ.not_ge ( by simpa [ Cardinal.mk_out ] using Cardinal.mk_le_of_injective hinjective )

theorem liftHG_tripleSystem {α : Type u} (A : SimpleGraph α) (κ : Cardinal.{u}) :
    (liftHG A κ).IsTripleSystem := by
  intro e he;
  convert Set.ncard_eq_three.mpr ( Erdos593.liftHG_isTripleSystem A κ e he )

theorem nonlinear_not_embeds_linear {F : FTS} (hF : ¬ F.Linear)
    {W : Type u} {H : Hypergraph W} (hH : H.Linear) : ¬ F.Embeds H := by
  contrapose! hF; rcases hF with ⟨ f, hf, hfe ⟩ ;
  intro e₁ he₁ e₂ he₂ hne;
  have := hH ( f '' ↑e₁ ) ( hfe e₁ he₁ ) ( f '' ↑e₂ ) ( hfe e₂ he₂ ) ?_;
  · exact Finset.card_le_one.mpr fun x hx y hy => hf <| this ( Set.mem_inter ( Set.mem_image_of_mem _ <| Finset.mem_coe.mpr <| Finset.mem_inter.mp hx |>.1 ) ( Set.mem_image_of_mem _ <| Finset.mem_coe.mpr <| Finset.mem_inter.mp hx |>.2 ) ) ( Set.mem_inter ( Set.mem_image_of_mem _ <| Finset.mem_coe.mpr <| Finset.mem_inter.mp hy |>.1 ) ( Set.mem_image_of_mem _ <| Finset.mem_coe.mpr <| Finset.mem_inter.mp hy |>.2 ) );
  · exact fun h => hne <| Finset.coe_injective <| Set.image_injective.mpr hf h

def AllLinearExists : Prop :=
  ∀ (kappa : Cardinal.{u}), ℵ₀ < kappa →
    ∃ (W : Type u) (H : Hypergraph W), H.IsTripleSystem ∧ H.Linear ∧ H.HasChromatic kappa

theorem no_bridgeSelector_of {F : FTS}
    (h : ∃ ed : {e : Finset F.V // e ∈ F.edges}, ∀ w ∈ ed.1, ¬ IsBridgeInc F w ed) :
    ¬ Nonempty (BridgeSelector F) := by
  rintro ⟨bs⟩
  obtain ⟨ed, hed⟩ := h
  exact hed (bs.p ed) (bs.isBridge ed).1 (bs.isBridge ed)

theorem negativeCore_of (hlin6 : AllLinearExists.{u}) (hE2 : E2_EH_oddgirth.{u}) :
    NegativeCore.{u} := by
  intro F lam hnb hlam
  have hni : ¬ F.reduce.IntrinsicObligatory :=
    fun h => hnb ((finiteDecomposition_holds F).mpr h)
  by_cases hLin : F.reduce.Linear
  · by_cases hBr : ∀ ed : {e : Finset F.reduce.V // e ∈ F.reduce.edges},
        ∃ w ∈ ed.1, IsBridgeInc F.reduce w ed
    ·
      have hEx : ∃ c : BergeCycle F.reduce, ¬ Even c.m := by
        by_contra he; push_neg at he; exact hni ⟨hLin, hBr, he⟩
      obtain ⟨c, hcOdd⟩ := hEx
      have hodd : Odd c.m := (Nat.even_or_odd c.m).resolve_left hcOdd
      have hm3 : 3 ≤ c.m := by
        have := c.hm; rcases hodd with ⟨k, hk⟩; omega
      obtain ⟨V, A, hcard, hAchr, hAgirth⟩ := hE2 lam hlam c.m
      refine ⟨Node A lam × V, liftHG A lam, liftHG_tripleSystem _ _,
        lift_hasChromatic A lam hAchr, ?_⟩
      intro hemb
      exact lift_omits_of_bergeCycle hLin c
        (hAgirth c.m hodd hm3 (by omega)) (F.reduce_embeds_of_embeds hemb)
    ·
      push_neg at hBr
      have hns : ¬ Nonempty (BridgeSelector F.reduce) := no_bridgeSelector_of hBr
      refine ⟨Node (⊤ : SimpleGraph lam.out) lam × lam.out, liftHG (⊤) lam,
        liftHG_tripleSystem _ _,
        lift_hasChromatic (⊤) lam (completeGraph_hasChromatic lam), ?_⟩
      intro hemb
      exact lift_omits_of_no_bridgeSelector hLin hns (F.reduce_embeds_of_embeds hemb)
  ·
    obtain ⟨W, H, htri, hHlin, hchr⟩ := hlin6 lam hlam
    refine ⟨W, H, htri, hchr, ?_⟩
    intro hemb
    exact nonlinear_not_embeds_linear hLin hHlin (F.reduce_embeds_of_embeds hemb)

theorem classification_of (hexp : ReiherExpansion.{u}) (hlin6 : AllLinearExists.{u})
    (hE2 : E2_EH_oddgirth.{u}) (F : FTS) :
    (FTS.Obligatory.{u} F ↔ Bclass F) ∧ (Bclass F ↔ F.reduce.IntrinsicObligatory) :=
  classification hexp (negativeCore_of hlin6 hE2) F

theorem spectrum_dichotomy_of (hexp : ReiherExpansion.{u}) (hlin6 : AllLinearExists.{u})
    (hE2 : E2_EH_oddgirth.{u}) (F : FTS) (lam : Cardinal.{u}) :
    F.InSpec lam ↔ (¬ Bclass F ∧ ℵ₀ < lam) :=
  spectrum_dichotomy hexp (negativeCore_of hlin6 hE2) F lam

theorem problem_1177_part3_of (hexp : ReiherExpansion.{u}) (hlin6 : AllLinearExists.{u})
    (hE2 : E2_EH_oddgirth.{u}) (G : FTS) (kappa : Cardinal.{u}) (hk : ℵ₀ < kappa)
    (h : G.FGnonempty kappa) (lam : Cardinal.{u}) (hlam : ℵ₀ < lam) :
    G.FGnonempty lam :=
  problem_1177_part3 hexp (negativeCore_of hlin6 hE2) G kappa hk h lam hlam

end Erdos593
end

-- Reservoir
section
open Cardinal Ordinal

namespace Erdos593

universe u

def Hypergraph.sigma {J : Type u} {W : J → Type u} (H : ∀ j, Hypergraph (W j)) :
    Hypergraph (Σ j, W j) :=
  ⟨{e | ∃ (j : J) (t : Set (W j)), t ∈ (H j).edges ∧ e = Sigma.mk j '' t}⟩

theorem Hypergraph.sigma_isTripleSystem {J : Type u} {W : J → Type u}
    (H : ∀ j, Hypergraph (W j)) (h : ∀ j, (H j).IsTripleSystem) :
    (Hypergraph.sigma H).IsTripleSystem := by
  intro e he; obtain ⟨j, t, ht, rfl⟩ := he
  rw [Set.ncard_image_of_injective _ sigma_mk_injective]
  exact h j t ht

theorem Hypergraph.sigma_linear {J : Type u} {W : J → Type u}
    (H : ∀ j, Hypergraph (W j)) (h : ∀ j, (H j).Linear) :
    (Hypergraph.sigma H).Linear := by
  intro e₁ he₁ e₂ he₂ hne;
  obtain ⟨ j₁, t₁, ht₁, rfl ⟩ := he₁
  obtain ⟨ j₂, t₂, ht₂, rfl ⟩ := he₂;
  by_cases h : j₁ = j₂ <;> simp_all +decide [ Set.Subsingleton ];
  · subst h;
    intro a ha x hx hax b hb y hy hay; have := h j₁ t₁ ht₁ t₂ ht₂; simp_all +decide [ Set.Subsingleton ] ;
    exact this ( by aesop ) ha hx hb hy;
  · aesop

theorem Hypergraph.sigma_hasChromatic {J : Type u} {W : J → Type u}
    (H : ∀ j, Hypergraph (W j)) (κ : Cardinal.{u}) (κs : J → Cardinal.{u})
    (hchr : ∀ j, (H j).HasChromatic (κs j)) (hle : ∀ j, κs j ≤ κ)
    (hcof : ∀ θ, θ < κ → ∃ j, θ < κs j) :
    (Hypergraph.sigma H).HasChromatic κ := by
  constructor;
  · obtain ⟨c, hc⟩ : ∃ c : (Σ j, W j) → κ.out, (Hypergraph.sigma H).ProperColoring c := by
      obtain ⟨c, hc⟩ : ∃ c : (Σ j, W j) → κ.out, ∀ j, ∀ e ∈ (H j).edges, ∃ u ∈ e, ∃ v ∈ e, c ⟨j, u⟩ ≠ c ⟨j, v⟩ := by
        have h_coloring : ∀ j, ∃ c : W j → κ.out, ∀ e ∈ (H j).edges, ∃ u ∈ e, ∃ v ∈ e, c u ≠ c v := by
          intro j
          obtain ⟨c, hc⟩ := (hchr j).left
          have h_colorable : (H j).ColorableBy κ := by
            exact Erdos593.colorableBy_of_proper_le c hc (by rw [Cardinal.mk_out]; exact hle j)
          generalize_proofs at *; (
          obtain ⟨ c, hc ⟩ := h_colorable; use c; aesop;);
        choose c hc using h_coloring;
        exact ⟨ fun ⟨ j, u ⟩ => c j u, fun j e he => hc j e he ⟩;
      use c;
      intro e he; obtain ⟨ j, t, ht, rfl ⟩ := he; specialize hc j t ht; aesop;
    exact ⟨ c, hc ⟩;
  · intro θ hθ hcolorable
    obtain ⟨j, hj⟩ := hcof θ hθ
    have hcolorable_j : (H j).ColorableBy θ := by
      obtain ⟨ c, hc ⟩ := hcolorable;
      use fun w => c ⟨j, w⟩;
      intro e he; specialize hc ( Sigma.mk j '' e ) ; simp_all +decide [ Set.image ] ;
      exact hc ⟨ j, e, he, by aesop ⟩
    exact (hchr j).right θ hj hcolorable_j

theorem successor_linear (h3 : E3_EGH_P.{u}) (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) :
    ∃ (W : Type u) (H : Hypergraph W),
      H.IsTripleSystem ∧ H.Linear ∧ H.HasChromatic (Order.succ μ) := by
  obtain ⟨D⟩ := exists_calibData h3 μ hμ
  exact ⟨_, D.L, D.L_isTripleSystem, D.L_linear, D.L_colorable, D.L_lower⟩

theorem allLinearExists_of_E3 (h3 : E3_EGH_P.{u}) : AllLinearExists.{u} := by
  intro κ hκ
  by_cases hsucc : ∃ ν : Cardinal.{u}, κ = Order.succ ν
  ·
    obtain ⟨ν, rfl⟩ := hsucc
    have hν : ℵ₀ ≤ ν := by
      by_contra h
      push_neg at h
      exact absurd (Order.succ_le_of_lt h) (not_le.mpr hκ)
    obtain ⟨W, H, htri, hlin, hchr⟩ := successor_linear h3 ν hν
    exact ⟨W, H, htri, hlin, hchr⟩
  ·
    push_neg at hsucc

    have hpick : ∀ a : κ.ord.ToType,
        ∃ ν : Cardinal.{u}, ℵ₀ ≤ ν ∧ Order.succ ν < κ ∧
          Ordinal.typein (α := κ.ord.ToType) (· < ·) a < (Order.succ ν).ord := by
      intro a
      exact successors_cofinal κ hκ hsucc _ (Ordinal.typein_lt_self a)
    choose ν hνℵ hνlt hνrk using hpick

    have hcomp : ∀ a : κ.ord.ToType, ∃ (W : Type u) (H : Hypergraph W),
        H.IsTripleSystem ∧ H.Linear ∧ H.HasChromatic (Order.succ (ν a)) :=
      fun a => successor_linear h3 (ν a) (hνℵ a)
    choose W H htri hlin hchr using hcomp
    refine ⟨Σ a : κ.ord.ToType, W a, Hypergraph.sigma H,
      Hypergraph.sigma_isTripleSystem H htri, Hypergraph.sigma_linear H hlin,
      Hypergraph.sigma_hasChromatic H κ (fun a => Order.succ (ν a)) hchr
        (fun a => le_of_lt (hνlt a)) ?_⟩

    intro θ hθ
    have hθord : θ.ord < κ.ord := (Cardinal.ord_lt_ord).mpr hθ
    refine ⟨Ordinal.enum (α := κ.ord.ToType) (· < ·)
      ⟨θ.ord, by rw [Ordinal.type_toType]; exact hθord ⟩, ?_⟩
    have hrk := hνrk (Ordinal.enum (α := κ.ord.ToType) (· < ·)
      ⟨θ.ord, by rw [Ordinal.type_toType]; exact hθord⟩)
    have hte : Ordinal.typein (α := κ.ord.ToType) (· < ·) (Ordinal.enum (α := κ.ord.ToType) (· < ·)
        ⟨θ.ord, by rw [Ordinal.type_toType]; exact hθord⟩) = θ.ord := Ordinal.typein_enum _ _
    rw [hte] at hrk
    exact (Cardinal.ord_lt_ord).mp hrk

theorem classification_of_E3 (hexp : ReiherExpansion.{u}) (h3 : E3_EGH_P.{u})
    (hE2 : E2_EH_oddgirth.{u}) (F : FTS) :
    (FTS.Obligatory.{u} F ↔ Bclass F) ∧ (Bclass F ↔ F.reduce.IntrinsicObligatory) :=
  classification_of hexp (allLinearExists_of_E3 h3) hE2 F

theorem spectrum_dichotomy_of_E3 (hexp : ReiherExpansion.{u}) (h3 : E3_EGH_P.{u})
    (hE2 : E2_EH_oddgirth.{u}) (F : FTS) (lam : Cardinal.{u}) :
    F.InSpec lam ↔ (¬ Bclass F ∧ ℵ₀ < lam) :=
  spectrum_dichotomy_of hexp (allLinearExists_of_E3 h3) hE2 F lam

theorem problem_1177_part3_of_E3 (hexp : ReiherExpansion.{u}) (h3 : E3_EGH_P.{u})
    (hE2 : E2_EH_oddgirth.{u}) (G : FTS) (kappa : Cardinal.{u}) (hk : ℵ₀ < kappa)
    (h : G.FGnonempty kappa) (lam : Cardinal.{u}) (hlam : ℵ₀ < lam) :
    G.FGnonempty lam :=
  problem_1177_part3_of hexp (allLinearExists_of_E3 h3) hE2 G kappa hk h lam hlam

end Erdos593
end

-- Calibration
section
open Cardinal Ordinal

namespace Erdos593

universe u

theorem Vtx_card (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) :
    #(Vtx (rhoC μ)) = (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ μ) := by
  have hρ : ℵ₀ ≤ (2 : Cardinal.{u}) ^ μ := le_trans hμ (le_of_lt (Cardinal.cantor μ))
  have h1 : Order.succ ((2 : Cardinal.{u}) ^ μ) ≤ (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ μ) :=
    Order.succ_le_of_lt (Cardinal.cantor _)
  have h2 : ℵ₀ ≤ (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ μ) :=
    le_trans hρ (le_of_lt (Cardinal.cantor _))
  have h3 : Order.succ ((2 : Cardinal.{u}) ^ μ) ≠ 0 :=
    (lt_of_le_of_lt zero_le (Order.lt_succ _)).ne'
  show #((Rord (rhoC μ)).ToType × ((2 : Cardinal.{u}) ^ (rhoC μ)).out) = _
  rw [Cardinal.mk_prod, Cardinal.mk_out]
  show Cardinal.lift.{u,u} (#(((Order.succ (rhoC μ)).ord).ToType)) * _ = _
  rw [mk_ord_toType, Cardinal.lift_id, Cardinal.lift_id]
  show Order.succ ((2 : Cardinal.{u}) ^ μ) * (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ μ) = _
  rw [Cardinal.mul_eq_right h2 h1 h3]

theorem successor_linear_bounded (h3 : E3_EGH_P.{u}) (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) :
    ∃ (W : Type u) (H : Hypergraph W),
      H.IsTripleSystem ∧ H.Linear ∧ H.HasChromatic (Order.succ μ) ∧
        #W ≤ (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ μ) := by
  obtain ⟨D⟩ := exists_calibData h3 μ hμ
  exact ⟨_, D.L, D.L_isTripleSystem, D.L_linear, ⟨D.L_colorable, D.L_lower⟩,
    le_of_eq (Vtx_card μ hμ)⟩

theorem lift_card_le {α : Type u} (A : SimpleGraph α) (κ : Cardinal.{u})
    (hκ : ℵ₀ ≤ κ) (hα : #α ≤ κ) :
    #(Node A κ × α) ≤ (2 : Cardinal.{u}) ^ κ := by

  have h_node_card : #(Node A κ) ≤ κ * κ ^ κ := by
    have h_node_card : #(Node A κ) ≤ κ * κ ^ κ := by
      have h_card_seq : ∀ pos : Idx κ, #( {q : Idx κ // q < pos} → A.edgeSet ) ≤ κ ^ κ := by
        intro pos
        have h_seq_card : #({q : Idx κ // q < pos} → A.edgeSet) ≤ κ ^ #( {q : Idx κ // q < pos} ) := by
          refine' le_trans ( Cardinal.mk_le_of_injective _ ) _;
          exact ( { q : Idx κ // q < pos } → α × α );
          exact fun f q => f q |>.1.out;
          · intro f g hfg;
            funext q;
            have h : (f q).1.out = (g q).1.out := congr_fun hfg q;
            apply Subtype.ext;
            calc (f q).1 = Quot.mk _ (f q).1.out := (Quot.out_eq _).symm
              _ = Quot.mk _ (g q).1.out := by rw [h]
              _ = (g q).1 := Quot.out_eq _;
          · simp +decide [ Cardinal.mk_pi, Cardinal.mk_prod ];
            exact Cardinal.power_le_power_right ( by simpa using mul_le_mul' hα hα |> le_trans <| by simp +decide [ Cardinal.mul_eq_self hκ ] );
        refine' le_trans h_seq_card ( Cardinal.power_le_power_left _ _ );
        · exact ne_of_gt ( lt_of_lt_of_le ( Cardinal.aleph0_pos ) hκ );
        · refine' le_trans ( Cardinal.mk_le_mk_of_subset _ ) _;
          exact Set.univ;
          · exact Set.subset_univ _;
          · simp +decide [ Cardinal.mk_univ ]
      have h_card_node : #(Node A κ) ≤ Cardinal.mk (Σ pos : Idx κ, {q : Idx κ // q < pos} → A.edgeSet) := by
        refine' ⟨ fun x => ⟨ x.pos, x.seq ⟩, fun x y hxy => _ ⟩ ; cases x ; cases y ; aesop;
      refine' le_trans h_card_node _;
      refine le_trans (le_of_eq (Cardinal.mk_sigma _))
        ((Cardinal.sum_le_sum _ _ h_card_seq).trans (le_of_eq ?_));
      simp +decide [ Cardinal.mk_ord_toType ];
    exact h_node_card;
  refine' le_trans ( Cardinal.mk_prod _ _ |> le_of_eq ) _;
  refine' le_trans ( mul_le_mul' ( Cardinal.lift_le.mpr h_node_card ) ( Cardinal.lift_le.mpr hα ) ) _;
  simp +decide [ Cardinal.power_self_eq hκ ];
  rw [ mul_right_comm, Cardinal.mul_eq_max ];
  · simp +decide [ Cardinal.mul_eq_self hκ ];
    exact le_of_lt ( Cardinal.cantor _ );
  · exact le_trans hκ ( le_mul_of_one_le_right' ( Cardinal.one_le_iff_ne_zero.mpr ( ne_of_gt ( lt_of_lt_of_le ( Cardinal.aleph0_pos ) hκ ) ) ) );
  · exact le_trans hκ ( le_of_lt ( Cardinal.cantor _ ) )

theorem lift_card_le_aleph1 {α : Type u} (A : SimpleGraph α)
    (hα : #α ≤ Order.succ (ℵ₀ : Cardinal.{u})) :
    #(Node A (Order.succ (ℵ₀ : Cardinal.{u})) × α) ≤
      (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ (ℵ₀ : Cardinal.{u})) := by
  have hℵ₁ : ℵ₀ ≤ Order.succ (ℵ₀ : Cardinal.{u}) := le_of_lt (Order.lt_succ _)
  have hbound : #(Node A (Order.succ (ℵ₀ : Cardinal.{u})) × α) ≤
      (2 : Cardinal.{u}) ^ (Order.succ (ℵ₀ : Cardinal.{u})) :=
    lift_card_le A (Order.succ ℵ₀) hℵ₁ hα
  refine le_trans hbound ?_
  apply Cardinal.power_le_power_left (by norm_num)
  exact Order.succ_le_of_lt (Cardinal.cantor _)

theorem negativeCore_bounded_aleph1 (h3 : E3_EGH_P.{u}) (hE2 : E2_EH_oddgirth.{u})
    (F : FTS) (hnb : ¬ Bclass F) :
    ∃ (W : Type u) (H : Hypergraph W),
      H.IsTripleSystem ∧ H.HasChromatic (Order.succ (ℵ₀ : Cardinal.{u})) ∧
        ¬ F.Embeds H ∧ #W ≤ (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ (ℵ₀ : Cardinal.{u})) := by
  by_cases hLin : F.reduce.Linear;
  · have hni : ¬ F.reduce.IntrinsicObligatory := by
      contrapose! hnb; exact (finiteDecomposition_holds F).mpr hnb;
    by_cases hBr : ∀ ed : {e : Finset F.reduce.V // e ∈ F.reduce.edges}, ∃ w ∈ ed.1, IsBridgeInc F.reduce w ed;
    · obtain ⟨c, hc_odd, hc_cycle⟩ : ∃ c : BergeCycle F.reduce, Odd c.m := by
        contrapose! hni;
        exact ⟨ hLin, fun ed => hBr ed, fun c => by simpa using hni c ⟩;
      obtain ⟨V, A, hcard, hAchr, hAgirth⟩ := hE2 (Order.succ (ℵ₀ : Cardinal)) (Order.lt_succ _) (2 * hc_odd + 1);
      have h_lift_omits : ¬ F.reduce.Embeds (liftHG A (Order.succ ℵ₀)) := by
        apply lift_omits_of_bergeCycle;
        exact hLin;
        convert hAgirth ( 2 * hc_odd + 1 ) _ _ _ using 1;
        any_goals tauto;
        · rw [ hc_cycle ];
        · rcases hc_odd with ( _ | _ | hc_odd ) <;> simp_all +arith +decide;
          exact absurd hc_cycle ( by linarith [ c.hm ] );
        · omega;
      exact ⟨_, liftHG A (Order.succ ℵ₀), Erdos593.liftHG_tripleSystem A _,
        Erdos593.lift_hasChromatic A _ hAchr,
        fun h => h_lift_omits (FTS.reduce_embeds_of_embeds F h),
        lift_card_le_aleph1 A hcard.le⟩;
    · have hno_bridgeSelector : ¬ Nonempty (BridgeSelector F.reduce) := by
        exact no_bridgeSelector_of ( by push_neg at hBr; exact hBr );
      refine' ⟨ Node ( ⊤ : SimpleGraph ( Order.succ ℵ₀ ).out ) ( Order.succ ℵ₀ ) × ( Order.succ ℵ₀ ).out, liftHG ( ⊤ : SimpleGraph ( Order.succ ℵ₀ ).out ) ( Order.succ ℵ₀ ), _, _, _, _ ⟩;
      · exact Erdos593.liftHG_tripleSystem _ _;
      · convert Erdos593.lift_hasChromatic ( ⊤ : SimpleGraph ( Order.succ ℵ₀ ).out ) ( Order.succ ℵ₀ ) ( Erdos593.completeGraph_hasChromatic ( Order.succ ℵ₀ ) ) using 1;
      · intro h;
        apply hno_bridgeSelector;
        apply bridgeSelector_of_embeds_lift;
        exact hLin;
        exact F.reduce_embeds_of_embeds h;
      · convert lift_card_le_aleph1 _ _;
        simp +decide [ Cardinal.mk_out ];
  · obtain ⟨W, H, htri, hHlin, hchr, hcard⟩ := successor_linear_bounded h3 ℵ₀ le_rfl
    use W, H
    refine ⟨ htri, hchr, ?_, hcard ⟩
    intro hF
    have hFreduce : F.reduce.Embeds H := by
      exact F.reduce_embeds_of_embeds hF
    exact absurd (nonlinear_not_embeds_linear hLin hHlin hFreduce) (by
    grind)

theorem problem_1177_part1 (hexp : ReiherExpansion.{u}) (h3 : E3_EGH_P.{u})
    (hE2 : E2_EH_oddgirth.{u}) (G : FTS) (h : G.FGnonempty (Order.succ (ℵ₀ : Cardinal.{u}))) :
    ∃ (W : Type u) (H : Hypergraph W),
      H.IsTripleSystem ∧ H.HasChromatic (Order.succ (ℵ₀ : Cardinal.{u})) ∧
        ¬ G.Embeds H ∧ #W ≤ (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ (ℵ₀ : Cardinal.{u})) := by
  have hnb : ¬ Bclass G :=
    ((spectrum_dichotomy_of_E3 hexp h3 hE2 G (Order.succ ℵ₀)).mp
      ⟨Order.lt_succ _, h⟩).1
  exact negativeCore_bounded_aleph1 h3 hE2 G hnb

end Erdos593
end

-- Consequences
section
open Cardinal

namespace Erdos593

universe u

def twoTriplesSharingPair : FTS where
  V := Fin 4
  edges := {{0, 1, 2}, {0, 1, 3}}
  card3 := by decide

theorem twoTriples_not_linear : ¬ twoTriplesSharingPair.Linear := by
  unfold FTS.Linear twoTriplesSharingPair
  decide

theorem not_bclass_twoTriples : ¬ Bclass twoTriplesSharingPair :=
  fun h => twoTriples_not_linear (bclass_intrinsic h).1

theorem ncard_three_exists_third {W : Type u} {s : Set W} (hs : s.ncard = 3) {a b : W}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) : ∃ c ∈ s, c ≠ a ∧ c ≠ b := by
  by_contra hc
  push_neg at hc
  have hsub : s ⊆ {a, b} := by
    intro x hx
    by_cases hxa : x = a
    · exact Or.inl hxa
    · exact Or.inr (hc x hx hxa)
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_pair hab] at this
  omega

theorem ncard_three_eq_of_mem {W : Type u} {s : Set W} (hs : s.ncard = 3) {a b c : W}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    s = {a, b, c} := by
  have h3 : ({a, b, c} : Set W).ncard = 3 := Set.ncard_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
  have hsub : ({a, b, c} : Set W) ⊆ s := by
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  exact (Set.eq_of_subset_of_ncard_le hsub (by omega)
    (Set.finite_of_ncard_ne_zero (by omega))).symm

theorem twoTriples_embeds_of_not_linear {W : Type u} (K : Hypergraph W)
    (htri : K.IsTripleSystem) (hnl : ¬ K.Linear) :
    twoTriplesSharingPair.Embeds K := by
  unfold Hypergraph.Linear at hnl
  push_neg at hnl
  obtain ⟨e₁, he₁, e₂, he₂, hne, hcap⟩ := hnl
  obtain ⟨a, ha, b, hb, hab⟩ := hcap
  have h1 : e₁.ncard = 3 := htri e₁ he₁
  have h2 : e₂.ncard = 3 := htri e₂ he₂
  obtain ⟨c, hc, hca, hcb⟩ := ncard_three_exists_third h1 ha.1 hb.1 hab
  obtain ⟨d, hd, hda, hdb⟩ := ncard_three_exists_third h2 ha.2 hb.2 hab
  have he1 : e₁ = {a, b, c} := ncard_three_eq_of_mem h1 ha.1 hb.1 hc hab (Ne.symm hca) (Ne.symm hcb)
  have he2 : e₂ = {a, b, d} := ncard_three_eq_of_mem h2 ha.2 hb.2 hd hab (Ne.symm hda) (Ne.symm hdb)
  have hcd : c ≠ d := by
    intro hcd
    subst hcd
    exact hne (he1.trans he2.symm)
  have hcases : ∀ e : Finset (Fin 4), e ∈ ({{0, 1, 2}, {0, 1, 3}} : Finset (Finset (Fin 4))) →
      e = {0, 1, 2} ∨ e = {0, 1, 3} := by decide
  refine ⟨(![a, b, c, d] : Fin 4 → W), ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; simp at hij; simp_all)
  · have k1 : (![a, b, c, d] : Fin 4 → W) '' ((({0, 1, 2} : Finset (Fin 4)) : Set (Fin 4))) =
        {a, b, c} := by
      ext x; simp [Fin.exists_fin_succ]; tauto
    have k2 : (![a, b, c, d] : Fin 4 → W) '' ((({0, 1, 3} : Finset (Fin 4)) : Set (Fin 4))) =
        {a, b, d} := by
      ext x; simp [Fin.exists_fin_succ]; tauto
    intro e he
    rcases hcases e he with rfl | rfl
    · rw [he1] at he₁
      convert he₁ using 1
      exact k1
    · rw [he2] at he₂
      convert he₂ using 1
      exact k2

theorem loose7_edge_inj (a b : Fin 7)
    (h : ({Sum.inl a, Sum.inl (a + 1), Sum.inr a} : Finset (Fin 7 ⊕ Fin 7)) =
      {Sum.inl b, Sum.inl (b + 1), Sum.inr b}) : a = b := by
  have hmem : (Sum.inr a : Fin 7 ⊕ Fin 7) ∈
      ({Sum.inl b, Sum.inl (b + 1), Sum.inr b} : Finset (Fin 7 ⊕ Fin 7)) := by
    rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, false_or] at hmem
  exact Sum.inr_injective hmem

noncomputable def looseCycle7_bergeCycle : BergeCycle looseCycle7 where
  m := 7
  hm := by norm_num
  v := fun i => Sum.inl i
  e := fun i => ⟨{Sum.inl i, Sum.inl (i + 1), Sum.inr i},
    Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩
  vinj := fun a b h => Sum.inl_injective h
  einj := by
    intro a b h
    exact loose7_edge_inj a b (congrArg Subtype.val h)
  mem_left := fun i => Finset.mem_insert_self _ _
  mem_right := fun i => Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

theorem not_bclass_looseCycle7 : ¬ Bclass looseCycle7 := by
  intro h
  have : Even (looseCycle7_bergeCycle).m := (bclass_intrinsic h).2.2 looseCycle7_bergeCycle
  exact (by decide : ¬ Even 7) this

theorem problem_1177_part2 (hexp : ReiherExpansion.{u}) (h3 : E3_EGH_P.{u})
    (hE2 : E2_EH_oddgirth.{u}) (hE5 : E5_HK_loose7.{u}) :
    ∃ (G H : FTS),
      G.FGnonempty (Order.succ (ℵ₀ : Cardinal.{u})) ∧
      H.FGnonempty (Order.succ (ℵ₀ : Cardinal.{u})) ∧
      ¬ ∃ (W : Type u) (K : Hypergraph W),
          K.IsTripleSystem ∧ K.HasChromatic (Order.succ (ℵ₀ : Cardinal.{u})) ∧
          ¬ G.Embeds K ∧ ¬ H.Embeds K := by
  refine ⟨twoTriplesSharingPair, looseCycle7, ?_, ?_, ?_⟩
  · exact ((spectrum_dichotomy_of_E3 hexp h3 hE2 twoTriplesSharingPair
      (Order.succ ℵ₀)).mpr ⟨not_bclass_twoTriples, Order.lt_succ _⟩).2
  · exact ((spectrum_dichotomy_of_E3 hexp h3 hE2 looseCycle7
      (Order.succ ℵ₀)).mpr ⟨not_bclass_looseCycle7, Order.lt_succ _⟩).2
  · rintro ⟨W, K, htri, hchr, hGf, hHf⟩
    have huc : K.UncountablyChromatic := hchr.2 ℵ₀ (Order.lt_succ _)
    by_cases hlin : K.Linear
    · exact hHf (hE5 K htri hlin huc)
    · exact hGf (twoTriples_embeds_of_not_linear K htri hlin)

theorem obstruction_trichotomy (F : FTS) :
    ¬ Bclass F ↔
      (¬ F.reduce.Linear) ∨
      (F.reduce.Linear ∧ ∃ ed : {e : Finset F.reduce.V // e ∈ F.reduce.edges},
          ∀ w ∈ ed.1, ¬ IsBridgeInc F.reduce w ed) ∨
      (F.reduce.Linear ∧
          (∀ ed : {e : Finset F.reduce.V // e ∈ F.reduce.edges},
            ∃ w ∈ ed.1, IsBridgeInc F.reduce w ed) ∧
          ∃ c : BergeCycle F.reduce, ¬ Even c.m) := by
  rw [not_congr (finiteDecomposition_holds F), FTS.IntrinsicObligatory]
  constructor
  · intro h
    by_cases hL : F.reduce.Linear
    · by_cases hB : ∀ ed : {e : Finset F.reduce.V // e ∈ F.reduce.edges},
          ∃ w ∈ ed.1, IsBridgeInc F.reduce w ed
      · refine Or.inr (Or.inr ⟨hL, hB, ?_⟩)
        by_contra hc; push_neg at hc; exact h ⟨hL, hB, hc⟩
      · push_neg at hB; exact Or.inr (Or.inl ⟨hL, hB⟩)
    · exact Or.inl hL
  · rintro (h | ⟨hL, ed, hed⟩ | ⟨hL, _, c, hc⟩) ⟨hLin, hBr, hEv⟩
    · exact h hLin
    · obtain ⟨w, hw, hb⟩ := hBr ed; exact hed w hw hb
    · exact hc (hEv c)

def FTS.StronglyTripartite (F : FTS) : Prop :=
  ∃ col : F.V → Fin 3, ∀ e ∈ F.edges, ∀ i : Fin 3, (e.filter (fun v => col v = i)).card = 1

theorem stronglyTripartite_edgeless {F : FTS} (h : F.edges = ∅) : F.StronglyTripartite := by
  refine ⟨fun _ => 0, ?_⟩
  intro e he; rw [h] at he; exact absurd he (Finset.notMem_empty e)

theorem stronglyTripartite_iso {F G : FTS} (h : FTS.Iso F G)
    (hF : F.StronglyTripartite) : G.StronglyTripartite := by
  rcases h with ⟨ φ, hφ ⟩;
  obtain ⟨ colF, hcolF ⟩ := hF;
  refine' ⟨ fun w => colF ( φ.symm w ), fun e he => _ ⟩;
  intro i; specialize hcolF ( Finset.map φ.symm.toEmbedding e ) ; simp_all +decide [ Finset.filter_map ] ;
  convert hcolF _ i using 1;
  convert he using 1 ; ext ; aesop

theorem card_filter_tri {α β : Type} [DecidableEq α] [DecidableEq β] (g : α → Fin 2)
    (x y : α) (z : β) (hne : g x ≠ g y) (i : Fin 3) :
    (({Sum.inl x, Sum.inl y, Sum.inr z} : Finset (α ⊕ β)).filter
      (fun v => Sum.elim (fun w => Fin.castSucc (g w)) (fun _ => (2 : Fin 3)) v = i)).card = 1 := by
  have hxy : x ≠ y := fun h => hne (h ▸ rfl)
  rw [Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton]
  simp only [Sum.elim_inl, Sum.elim_inr]
  have h01 : ∀ p : Fin 2, p = 0 ∨ p = 1 := by decide
  rcases h01 (g x) with hx | hx <;> rcases h01 (g y) with hy | hy <;>
    simp only [hx, hy] at hne ⊢ <;> fin_cases i <;> simp_all

theorem stronglyTripartite_expansion {VJ : Type} [Fintype VJ] [DecidableEq VJ]
    (J : SimpleGraph VJ) [DecidableRel J.Adj] (hJ : J.Colorable 2) :
    (graphExpansion J).StronglyTripartite := by
  obtain ⟨C⟩ := hJ
  refine ⟨fun v => Sum.elim (fun x => Fin.castSucc (C x)) (fun _ => (2 : Fin 3)) v, ?_⟩
  intro e he i
  obtain ⟨a, rfl⟩ := expansion_edge_cases J he
  exact card_filter_tri (α := VJ) (β := {x : Sym2 VJ // x ∈ J.edgeFinset}) C _ _ a
    (C.valid (expansion_endpoints_adj J a)) i

theorem FTS.mem_disjUnion_edges (F G : FTS) (e : Finset (F.disjUnion G).V) :
    e ∈ (F.disjUnion G).edges ↔
      (∃ a ∈ F.edges, Finset.map Function.Embedding.inl a = e) ∨
      (∃ a ∈ G.edges, Finset.map Function.Embedding.inr a = e) := by
  constructor
  · intro h
    rcases Finset.mem_union.1 h with h | h
    · exact Or.inl (Finset.mem_image.1 h)
    · exact Or.inr (Finset.mem_image.1 h)
  · rintro (h | h)
    · exact Finset.mem_union.2 (Or.inl (Finset.mem_image.2 h))
    · exact Finset.mem_union.2 (Or.inr (Finset.mem_image.2 h))

theorem card_filter_map_eq {α β : Type} [DecidableEq β] (f : α ↪ β) (s : Finset α)
    (p : β → Prop) [DecidablePred p] :
    ((s.map f).filter p).card = (s.filter (fun a => p (f a))).card := by
  rw [Finset.filter_map, Finset.card_map]
  rfl

theorem stronglyTripartite_disjUnion {F G : FTS}
    (hF : F.StronglyTripartite) (hG : G.StronglyTripartite) :
    (F.disjUnion G).StronglyTripartite := by
  obtain ⟨colF, hcolF⟩ := hF
  obtain ⟨colG, hcolG⟩ := hG
  refine ⟨fun v => Sum.elim colF colG v, ?_⟩
  intro e he i
  rcases (FTS.mem_disjUnion_edges F G e).1 he with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · exact (card_filter_map_eq (β := F.V ⊕ G.V) Function.Embedding.inl a _).trans (hcolF a ha i)
  · exact (card_filter_map_eq (β := F.V ⊕ G.V) Function.Embedding.inr a _).trans (hcolG a ha i)

theorem stronglyTripartite_amalgamate {F G : FTS} (x : F.V) (y : G.V)
    (hF : F.StronglyTripartite) (hG : G.StronglyTripartite) :
    (F.amalgamate G x y).StronglyTripartite := by
  obtain ⟨colF, hcolF⟩ := hF
  obtain ⟨colG, hcolG⟩ := hG
  obtain ⟨π, hπ⟩ : ∃ π : Equiv.Perm (Fin 3), π (colG y) = colF x :=
    ⟨Equiv.swap (colG y) (colF x), Equiv.swap_apply_left _ _⟩
  refine ⟨fun v => Sum.elim (fun a => colF a) (fun b => π (colG b.1)) v, ?_⟩
  intro e he i
  rcases (FTS.mem_amalgamate_edges F G x y e).1 he with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · exact (card_filter_map_eq (β := F.V ⊕ {b : G.V // b ≠ y}) Function.Embedding.inl a _).trans
      (hcolF a ha i)
  · refine (card_filter_map_eq (β := F.V ⊕ {b : G.V // b ≠ y}) _ a _).trans ?_
    rw [← hcolG a ha (π.symm i)]
    congr 1
    apply Finset.filter_congr
    intro b _
    have key : Sum.elim (fun a => colF a) (fun b => π (colG b.1))
        ((if h : b = y then Sum.inl x else Sum.inr ⟨b, h⟩ : F.V ⊕ {b : G.V // b ≠ y})) =
          π (colG b) := by
      by_cases hb : b = y
      · subst hb; rw [dif_pos rfl]; exact hπ.symm
      · rw [dif_neg hb]; rfl
    rw [Equiv.eq_symm_apply]
    exact Iff.of_eq (congrArg (· = i) key)

theorem bclass_stronglyTripartite {F : FTS} (h : Bclass F) : F.StronglyTripartite := by
  induction h with
  | edgeless F hF => exact stronglyTripartite_edgeless hF
  | expansion J hJ => exact stronglyTripartite_expansion J hJ
  | iso hiso _ ih => exact stronglyTripartite_iso hiso ih
  | union _ _ ihF ihG => exact stronglyTripartite_disjUnion ihF ihG
  | amalg x y _ _ ihF ihG => exact stronglyTripartite_amalgamate x y ihF ihG

theorem obligatory_stronglyTripartite (hexp : ReiherExpansion.{u}) (h3 : E3_EGH_P.{u})
    (hE2 : E2_EH_oddgirth.{u}) (F : FTS) (hobl : FTS.Obligatory.{u} F) :
    F.StronglyTripartite :=
  bclass_stronglyTripartite ((classification_of_E3 hexp h3 hE2 F).1.mp hobl)

theorem C7_linearlyObligatory_not_obligatory (hexp : ReiherExpansion.{u})
    (h3 : E3_EGH_P.{u}) (hE2 : E2_EH_oddgirth.{u}) (hE5 : E5_HK_loose7.{u}) :
    FTS.LinearlyObligatory.{u} looseCycle7 ∧ ¬ FTS.Obligatory.{u} looseCycle7 := by
  refine ⟨hE5, fun hobl => ?_⟩
  exact not_bclass_looseCycle7 ((classification_of_E3 hexp h3 hE2 looseCycle7).1.mp hobl)

theorem tri_inr_eq {α β : Type} [DecidableEq α] [DecidableEq β] {x y x' y' : α} {z z' : β}
    (h : ({Sum.inl x, Sum.inl y, Sum.inr z} : Finset (α ⊕ β)) =
      {Sum.inl x', Sum.inl y', Sum.inr z'}) : z = z' := by
  have hmem : (Sum.inr z : α ⊕ β) ∈ ({Sum.inl x', Sum.inl y', Sum.inr z'} : Finset (α ⊕ β)) := by
    rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, false_or] at hmem
  exact Sum.inr_injective hmem

theorem tri_mem_inl {α β : Type} [DecidableEq α] [DecidableEq β] (x y : α) (z : β) (a : α)
    (h : a = x ∨ a = y) : (Sum.inl a : α ⊕ β) ∈ ({Sum.inl x, Sum.inl y, Sum.inr z} : Finset (α ⊕ β)) := by
  rcases h with rfl | rfl <;> simp

theorem sym2_mem_out {α : Type} (z : Sym2 α) (a : α) (h : a ∈ z) :
    a = (Quot.out z).1 ∨ a = (Quot.out z).2 := by
  have hz : Quot.mk (Sym2.Rel α) (Quot.out z) = z := Quot.out_eq z
  rcases hp : Quot.out z with ⟨p, q⟩
  rw [hp] at hz
  have h' : a ∈ s(p, q) := by
    have hz' : s(p, q) = z := hz
    rw [hz']; exact h
  exact Sym2.mem_iff.1 h'

theorem expansion_bergeCycle_of_cycle {VJ : Type} [Fintype VJ] [DecidableEq VJ]
    (J : SimpleGraph VJ) [DecidableRel J.Adj] (m : ℕ) (hm : 3 ≤ m) (w : ZMod m → VJ)
    (hw : Function.Injective w) (hadj : ∀ i, J.Adj (w i) (w (i + 1))) :
    ∃ c : BergeCycle (graphExpansion J), c.m = m := by
  have hE : ∀ i, s(w i, w (i + 1)) ∈ J.edgeFinset := fun i =>
    SimpleGraph.mem_edgeFinset.mpr (hadj i)
  have h2 : (2 : ZMod m) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod m) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  refine ⟨{
    m := m
    hm := by omega
    v := fun i => Sum.inl (w i)
    e := fun i => ⟨{Sum.inl (Quot.out (s(w i, w (i + 1)))).1,
        Sum.inl (Quot.out (s(w i, w (i + 1)))).2, Sum.inr ⟨s(w i, w (i + 1)), hE i⟩},
      Finset.mem_image_of_mem _ (Finset.mem_attach _ ⟨s(w i, w (i + 1)), hE i⟩)⟩
    vinj := fun a b h => hw (Sum.inl_injective h)
    einj := ?_
    mem_left := fun i => tri_mem_inl _ _ _ _ (sym2_mem_out _ _ (Sym2.mem_mk_left _ _))
    mem_right := fun i => tri_mem_inl _ _ _ _ (sym2_mem_out _ _ (Sym2.mem_mk_right _ _)) }, rfl⟩
  intro i j h
  have h' := Subtype.ext_iff.1 (tri_inr_eq (congrArg Subtype.val h))
  rcases Sym2.eq_iff.1 h' with ⟨h1, _⟩ | ⟨h1, h3⟩
  · exact hw h1
  · have e1 := hw h1
    have e3 := hw h3
    exfalso
    apply h2
    have : i + 1 + 1 = i := by rw [e3, e1]
    calc (2 : ZMod m) = (i + 1 + 1) - i := by ring
      _ = 0 := by rw [this, sub_self]

theorem cycleGraph_adj_succ (k : ℕ) (i : Fin (k + 3)) :
    (SimpleGraph.cycleGraph (k + 3)).Adj i (i + 1) :=
  Or.inr (add_sub_cancel_left i 1)

theorem cycleExpansion_oddBergeCycle (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) :
    ∃ c : BergeCycle (graphExpansion (SimpleGraph.cycleGraph n)), ¬ Even c.m := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  obtain ⟨c, hc⟩ := expansion_bergeCycle_of_cycle (SimpleGraph.cycleGraph (k + 3)) (k + 3)
    (by omega) (fun i => (i : Fin (k + 3))) (fun _ _ h => h) (fun i => cycleGraph_adj_succ k i)
  exact ⟨c, by rw [hc]; exact Nat.not_even_iff_odd.mpr hodd⟩

theorem cycleExpansion_obligatory_iff (hexp : ReiherExpansion.{u}) (h3 : E3_EGH_P.{u})
    (hE2 : E2_EH_oddgirth.{u}) (n : ℕ) (hn : 3 ≤ n) :
    FTS.Obligatory.{u} (graphExpansion (SimpleGraph.cycleGraph n)) ↔ Even n := by
  constructor
  · intro hobl
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    obtain ⟨c, hc⟩ := cycleExpansion_oddBergeCycle n hn hodd
    have hB : Bclass (graphExpansion (SimpleGraph.cycleGraph n)) :=
      (classification_of_E3 hexp h3 hE2 _).1.mp hobl
    exact hc ((bclass_intrinsic hB).2.2 c)
  · intro heven
    have hcol : (SimpleGraph.cycleGraph n).Colorable 2 := by
      have := (SimpleGraph.cycleGraph.bicoloring_of_even n heven).colorable
      simpa using this.mono (by norm_num)
    have hB : Bclass (graphExpansion (SimpleGraph.cycleGraph n)) :=
      Bclass.expansion (SimpleGraph.cycleGraph n) hcol
    intro W H htri huc
    exact bclass_obligatory hexp _ hB H htri huc

def lowerRankUnion (F : FTS) (rank : {e : Finset F.V // e ∈ F.edges} → ℕ)
    (ed : {e : Finset F.V // e ∈ F.edges}) : Finset F.V :=
  (Finset.univ.filter (fun ed' : {e : Finset F.V // e ∈ F.edges} => rank ed' < rank ed)).sup
    (fun ed' => ed'.1)

def FTS.Forest (F : FTS) : Prop :=
  ∃ rank : {e : Finset F.V // e ∈ F.edges} → ℕ, Function.Injective rank ∧
    ∀ ed : {e : Finset F.V // e ∈ F.edges}, (ed.1 ∩ lowerRankUnion F rank ed).card ≤ 1

theorem forest_linear {F : FTS} (h : F.Forest) : F.Linear := by
  obtain ⟨ rank, hrank₁, hrank₂ ⟩ := h; intro e₁ he₁ e₂ he₂ hne; have := hrank₁; simp_all +decide [ FTS.Linear ] ;

  wlog hlt : rank ⟨e₁, he₁⟩ < rank ⟨e₂, he₂⟩ generalizing e₁ e₂;
  · grind only [Finset.card_inter, Finset.card_le_one, Finset.card_le_one_iff];
  · refine' le_trans _ ( hrank₂ e₂ he₂ );
    refine' Finset.card_le_card _;
    simp +decide [ Finset.subset_iff, lowerRankUnion ];
    exact fun x hx₁ hx₂ => ⟨ hx₂, e₁, ⟨ he₁, hlt ⟩, hx₁ ⟩

theorem forest_no_bergeCycle {F : FTS} (h : F.Forest) (c : BergeCycle F) : False := by
  obtain ⟨ rank, hrank₁, hrank₂ ⟩ := h;

  obtain ⟨a, ha⟩ : ∃ a : ZMod c.m, ∀ i : ZMod c.m, rank (c.e i) ≤ rank (c.e a) := by
    haveI := Fact.mk ( show 1 < c.m from by linarith [ c.hm ] );
    simpa using Finset.exists_max_image Finset.univ ( fun i => rank ( c.e i ) ) ⟨ 0, Finset.mem_univ 0 ⟩;

  have h_neighbours : rank (c.e (a - 1)) < rank (c.e a) ∧ rank (c.e (a + 1)) < rank (c.e a) := by
    have h_neighbours : c.e (a - 1) ≠ c.e a ∧ c.e (a + 1) ≠ c.e a := by
      haveI := Fact.mk ( show 1 < c.m from by linarith [ c.hm ] ) ; simp +decide [ sub_eq_iff_eq_add, add_eq_zero_iff_eq_neg, c.einj.eq_iff ] ;
    exact ⟨ lt_of_le_of_ne ( ha _ ) ( hrank₁.ne h_neighbours.1 ), lt_of_le_of_ne ( ha _ ) ( hrank₁.ne h_neighbours.2 ) ⟩;

  have h_subset : (c.e (a - 1)).1 ⊆ lowerRankUnion F rank (c.e a) ∧ (c.e (a + 1)).1 ⊆ lowerRankUnion F rank (c.e a) := by
    exact ⟨ Finset.subset_iff.mpr fun x hx => Finset.mem_sup.mpr ⟨ _, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, h_neighbours.1 ⟩, hx ⟩, Finset.subset_iff.mpr fun x hx => Finset.mem_sup.mpr ⟨ _, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, h_neighbours.2 ⟩, hx ⟩ ⟩;
  have h_card : 2 ≤ ( ( c.e a ).1 ∩ lowerRankUnion F rank ( c.e a ) ).card := by
    refine' Finset.one_lt_card.mpr ⟨ c.v a, _, c.v ( a + 1 ), _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
    · exact ⟨ c.mem_left a, h_subset.1 ( by simpa using c.mem_right ( a - 1 ) ) ⟩;
    · exact ⟨ c.mem_right a, h_subset.2 ( c.mem_left _ ) ⟩;
    · haveI := Fact.mk ( show 1 < c.m from by linarith [ c.hm ] ) ; exact c.vinj.ne ( by simp +decide [ ZMod.natCast_eq_natCast_iff' ] ) ;
  linarith [ hrank₂ ( c.e a ) ]

theorem forest_intrinsic {F : FTS} (h : F.Forest) : F.IntrinsicObligatory := by
  refine ⟨forest_linear h, ?_, ?_⟩
  · intro ed
    have hcard : ed.1.card = 3 := F.card3 ed.1 ed.2
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 < ed.1.card)
    exact ⟨w, hw, hw, fun hcyc => forest_no_bergeCycle h hcyc.choose⟩
  · intro c; exact (forest_no_bergeCycle h c).elim

theorem forest_obligatory (hexp : ReiherExpansion.{u}) {F : FTS} (h : F.Forest) :
    FTS.Obligatory.{u} F := by
  have hB : Bclass F := intrinsic_bclass F (forest_intrinsic h)
  intro W H htri huc
  exact bclass_obligatory hexp _ hB H htri huc

end Erdos593
end

-- ReiherPassage
section
open Cardinal Classical

namespace Erdos593

universe u

def FTS.Sub (F G : FTS) : Prop :=
  ∃ g : F.V → G.V, Function.Injective g ∧ ∀ e ∈ F.edges, e.image g ∈ G.edges

theorem obligatory_of_sub {F G : FTS} (h : F.Sub G) (hG : FTS.Obligatory.{u} G) :
    FTS.Obligatory.{u} F := by
  obtain ⟨g, hg, hge⟩ := h
  intro W H htri huc
  obtain ⟨f, hf, hfe⟩ := hG H htri huc
  refine ⟨f ∘ g, hf.comp hg, ?_⟩
  intro e he
  have hcoe : (f ∘ g) '' (↑e : Set F.V) = f '' (↑(e.image g) : Set G.V) := by
    rw [Finset.coe_image, Set.image_comp]
  rw [hcoe]
  exact hfe _ (hge e he)

theorem sym2map_mem_edgeFinset {VJ VK : Type} [Fintype VJ] [DecidableEq VJ]
    [Fintype VK] [DecidableEq VK] (J : SimpleGraph VJ) [DecidableRel J.Adj]
    (K : SimpleGraph VK) [DecidableRel K.Adj]
    (φ : VJ → VK) (hadj : ∀ a b, J.Adj a b → K.Adj (φ a) (φ b))
    (e : Sym2 VJ) (he : e ∈ J.edgeFinset) : Sym2.map φ e ∈ K.edgeFinset := by
  rw [SimpleGraph.mem_edgeFinset] at *
  induction e with
  | h a b => rw [SimpleGraph.mem_edgeSet] at *; exact hadj a b he

theorem tri_eq_of_sym2 {α β : Type} [DecidableEq α] [DecidableEq β] {x y x' y' : α} (z : β)
    (h : s(x, y) = s(x', y')) :
    ({Sum.inl x, Sum.inl y, Sum.inr z} : Finset (α ⊕ β)) = {Sum.inl x', Sum.inl y', Sum.inr z} := by
  rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact Finset.insert_comm _ _ _

theorem image_tri {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β) (a b c : α) :
    Finset.image f ({a, b, c} : Finset α) = {f a, f b, f c} := by
  simp [Finset.image_insert]

theorem graphExpansion_sub_of_embedding {VJ VK : Type} [Fintype VJ] [DecidableEq VJ]
    [Fintype VK] [DecidableEq VK] (J : SimpleGraph VJ) [DecidableRel J.Adj]
    (K : SimpleGraph VK) [DecidableRel K.Adj]
    (φ : VJ → VK) (hφ : Function.Injective φ)
    (hadj : ∀ a b, J.Adj a b → K.Adj (φ a) (φ b)) :
    (graphExpansion J).Sub (graphExpansion K) := by
  let g : VJ ⊕ {e : Sym2 VJ // e ∈ J.edgeFinset} → VK ⊕ {e : Sym2 VK // e ∈ K.edgeFinset} :=
    Sum.elim (fun x => Sum.inl (φ x))
      (fun e => Sum.inr ⟨Sym2.map φ e.1, sym2map_mem_edgeFinset J K φ hadj e.1 e.2⟩)
  have hinj : Function.Injective g := by
    refine Function.Injective.sumElim (fun a b h => hφ (Sum.inl_injective h)) ?_ ?_
    · intro a b h
      exact Subtype.ext (Sym2.map.injective hφ (Subtype.ext_iff.1 (Sum.inr_injective h)))
    · intro a b h
      exact Sum.inl_ne_inr h
  refine ⟨g, hinj, ?_⟩
  intro e he
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 he
  have h1 : s((Quot.out (Sym2.map φ a.1)).1, (Quot.out (Sym2.map φ a.1)).2) = Sym2.map φ a.1 :=
    Quot.out_eq _
  have h2 : s((Quot.out a.1).1, (Quot.out a.1).2) = a.1 := Quot.out_eq _
  have key : s((Quot.out (Sym2.map φ a.1)).1, (Quot.out (Sym2.map φ a.1)).2) =
      s(φ (Quot.out a.1).1, φ (Quot.out a.1).2) := by
    rw [h1]
    conv_lhs => rw [← h2]
    rfl
  refine Finset.mem_image.2 ⟨⟨Sym2.map φ a.1, sym2map_mem_edgeFinset J K φ hadj a.1 a.2⟩,
    Finset.mem_attach _ _, ?_⟩
  refine (tri_eq_of_sym2 (α := VK) (β := {e : Sym2 VK // e ∈ K.edgeFinset}) _ key).trans ?_
  exact (image_tri g (Sum.inl (Quot.out a.1).1) (Sum.inl (Quot.out a.1).2) (Sum.inr a)).symm

theorem colorable_two_embeds_completeBipartite {VJ : Type} [Fintype VJ] [DecidableEq VJ]
    (J : SimpleGraph VJ) [DecidableRel J.Adj] (hJ : J.Colorable 2) :
    ∃ (n : ℕ) (φ : VJ → (Fin n ⊕ Fin n)), Function.Injective φ ∧
      ∀ a b, J.Adj a b → (completeBipartiteGraph (Fin n) (Fin n)).Adj (φ a) (φ b) := by
  obtain ⟨C⟩ := hJ;
  refine' ⟨ Fintype.card VJ, fun v => if C v = 0 then Sum.inl ( Fintype.equivFin VJ v ) else Sum.inr ( Fintype.equivFin VJ v ), _, _ ⟩;
  · intro v w h; by_cases hv : C v = 0 <;> by_cases hw : C w = 0 <;> simp_all +decide ;
  · intro a b hab; have := C.valid hab; simp_all +decide ;
    grind

theorem reiherExpansion_of_E4 (hE4 : E4_Reiher.{u}) : ReiherExpansion.{u} := by
  intro VJ _ _ J _ hJ
  obtain ⟨n, φ, hφ, hadj⟩ := colorable_two_embeds_completeBipartite J hJ
  exact obligatory_of_sub
    (graphExpansion_sub_of_embedding J (completeBipartiteGraph (Fin n) (Fin n)) φ hφ hadj)
    (hE4 n)

theorem reiherExpansion_iff_E4 : ReiherExpansion.{u} ↔ E4_Reiher.{u} :=
  ⟨E4_Reiher_of_reiherExpansion, reiherExpansion_of_E4⟩

end Erdos593
end

-- FinalResults
section
open Cardinal

namespace Erdos593

universe u

theorem classification_final (hE4 : E4_Reiher.{u}) (h3 : E3_EGH_P.{u})
    (hE2 : E2_EH_oddgirth.{u}) (F : FTS) :
    (FTS.Obligatory.{u} F ↔ Bclass F) ∧ (Bclass F ↔ F.reduce.IntrinsicObligatory) :=
  classification_of_E3 (reiherExpansion_of_E4 hE4) h3 hE2 F

theorem obligatory_iff_bclass_final (hE4 : E4_Reiher.{u}) (h3 : E3_EGH_P.{u})
    (hE2 : E2_EH_oddgirth.{u}) (F : FTS) :
    FTS.Obligatory.{u} F ↔ Bclass F :=
  (classification_final hE4 h3 hE2 F).1

theorem spectrum_dichotomy_final (hE4 : E4_Reiher.{u}) (h3 : E3_EGH_P.{u})
    (hE2 : E2_EH_oddgirth.{u}) (F : FTS) (lam : Cardinal.{u}) :
    F.InSpec lam ↔ (¬ Bclass F ∧ ℵ₀ < lam) :=
  spectrum_dichotomy_of_E3 (reiherExpansion_of_E4 hE4) h3 hE2 F lam

theorem problem_1177_part3_final (hE4 : E4_Reiher.{u}) (h3 : E3_EGH_P.{u})
    (hE2 : E2_EH_oddgirth.{u}) (G : FTS) (kappa : Cardinal.{u}) (hk : ℵ₀ < kappa)
    (h : G.FGnonempty kappa) (lam : Cardinal.{u}) (hlam : ℵ₀ < lam) :
    G.FGnonempty lam :=
  problem_1177_part3_of_E3 (reiherExpansion_of_E4 hE4) h3 hE2 G kappa hk h lam hlam

theorem problem_1177_part2_final (hE4 : E4_Reiher.{u}) (h3 : E3_EGH_P.{u})
    (hE2 : E2_EH_oddgirth.{u}) (hE5 : E5_HK_loose7.{u}) :
    ∃ (G H : FTS),
      G.FGnonempty (Order.succ (ℵ₀ : Cardinal.{u})) ∧
      H.FGnonempty (Order.succ (ℵ₀ : Cardinal.{u})) ∧
      ¬ ∃ (W : Type u) (K : Hypergraph W),
          K.IsTripleSystem ∧ K.HasChromatic (Order.succ (ℵ₀ : Cardinal.{u})) ∧
          ¬ G.Embeds K ∧ ¬ H.Embeds K :=
  problem_1177_part2 (reiherExpansion_of_E4 hE4) h3 hE2 hE5

theorem obligatory_stronglyTripartite_final (hE4 : E4_Reiher.{u}) (h3 : E3_EGH_P.{u})
    (hE2 : E2_EH_oddgirth.{u}) (F : FTS) (hobl : FTS.Obligatory.{u} F) :
    F.StronglyTripartite :=
  obligatory_stronglyTripartite (reiherExpansion_of_E4 hE4) h3 hE2 F hobl

theorem forest_obligatory_final (hE4 : E4_Reiher.{u}) {F : FTS} (h : F.Forest) :
    FTS.Obligatory.{u} F :=
  forest_obligatory (reiherExpansion_of_E4 hE4) h

theorem cycleExpansion_obligatory_iff_final (hE4 : E4_Reiher.{u}) (h3 : E3_EGH_P.{u})
    (hE2 : E2_EH_oddgirth.{u}) (n : ℕ) (hn : 3 ≤ n) :
    FTS.Obligatory.{u} (graphExpansion (SimpleGraph.cycleGraph n)) ↔ Even n :=
  cycleExpansion_obligatory_iff (reiherExpansion_of_E4 hE4) h3 hE2 n hn

theorem C7_linearlyObligatory_not_obligatory_final (hE4 : E4_Reiher.{u})
    (h3 : E3_EGH_P.{u}) (hE2 : E2_EH_oddgirth.{u}) (hE5 : E5_HK_loose7.{u}) :
    FTS.LinearlyObligatory.{u} looseCycle7 ∧ ¬ FTS.Obligatory.{u} looseCycle7 :=
  C7_linearlyObligatory_not_obligatory (reiherExpansion_of_E4 hE4) h3 hE2 hE5

end Erdos593
end

-- EHBase
section
open Cardinal

namespace Erdos593

universe u

variable {V : Type u}

def GCountColorable (G : SimpleGraph V) : Prop :=
  ∃ c : V → ℕ, ∀ x y, G.Adj x y → c x ≠ c y

theorem gCountColorable_iff_colorableBy (G : SimpleGraph V) :
    GCountColorable G ↔ (SimpleGraph.toHG G).ColorableBy ℵ₀ := by
  constructor;
  · rintro ⟨ c, hc ⟩;
    refine' ⟨ _, _ ⟩;
    convert ( nonempty_equiv_of_countable ( α := ℕ ) ( β := Quotient.out ℵ₀ ) ).some ∘ c;
    convert Cardinal.mk_le_aleph0_iff.mp _;
    convert Cardinal.mk_out ℵ₀ |> le_of_eq;
    exact Cardinal.infinite_iff.2 ( by simp +decide );
    intro e he; obtain ⟨ x, y, hxy, rfl ⟩ := he; specialize hc x y hxy; aesop;
  · rintro ⟨ c, hc ⟩;
    obtain ⟨ f, hf ⟩ := Cardinal.eq.1 ( Cardinal.mk_out ℵ₀ );
    use fun x => ( f ( c x ) ).down;
    intro x y hxy; have := hc _ ( by exact ⟨ x, y, hxy, rfl ⟩ ) ; simp_all +decide [ Function.LeftInverse, Function.RightInverse ] ;
    grind

def HasKnAleph1 (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ (a : Fin n → V) (B : Set V), Function.Injective a ∧ ℵ₁ ≤ #B ∧
    (∀ i, a i ∉ B) ∧ (∀ i, ∀ b ∈ B, G.Adj (a i) b)

def nbhdIn (G : SimpleGraph V) (x : V) (M : Set V) : Set V := {y | y ∈ M ∧ G.Adj x y}

def NClosed (G : SimpleGraph V) (n : ℕ) (M : Set V) : Prop :=
  ∀ x, x ∉ M → #(nbhdIn G x M) < (n : Cardinal)

def closeStep (G : SimpleGraph V) (n : ℕ) (X : Set V) : Set V :=
  X ∪ {x | (n : Cardinal) ≤ #(nbhdIn G x X)}

def closeIter (G : SimpleGraph V) (n : ℕ) (X : Set V) : ℕ → Set V
  | 0 => X
  | k + 1 => closeStep G n (closeIter G n X k)

def cl (G : SimpleGraph V) (n : ℕ) (X : Set V) : Set V := ⋃ k, closeIter G n X k

theorem commonNbhd_le_aleph0 (G : SimpleGraph V) (n : ℕ) (hfree : ¬ HasKnAleph1 G n)
    (a : Fin n → V) (ha : Function.Injective a) :
    #({v | (∀ i, v ≠ a i) ∧ ∀ i, G.Adj (a i) v}) ≤ ℵ₀ := by
  contrapose! hfree;

  have h_card_ge_aleph1 : ℵ₁ ≤ #(↥{v : V | (∀ i, v ≠ a i) ∧ ∀ i, G.Adj (a i) v}) := by
    rw [← Cardinal.succ_aleph0]
    exact Order.succ_le_of_lt hfree
  exact ⟨ a, _, ha, h_card_ge_aleph1, fun i => by aesop, fun i => by aesop ⟩

theorem closeStep_card_le (G : SimpleGraph V) (n : ℕ) (hfree : ¬ HasKnAleph1 G n)
    (X : Set V) : #(closeStep G n X) ≤ #X + ℵ₀ := by

  have h_closure_step : {x | (n : Cardinal) ≤ #(nbhdIn G x X)} ⊆ ⋃ (a : {a : Fin n → V // Function.Injective a ∧ ∀ i, a i ∈ X}), {v | (∀ i, v ≠ a.1 i) ∧ ∀ i, G.Adj (a.1 i) v} := by
    intro x hx; simp_all +decide [ Set.subset_def ] ;

    obtain ⟨a, ha⟩ : ∃ a : Fin n → V, Function.Injective a ∧ ∀ i, a i ∈ X ∧ G.Adj x (a i) := by
      obtain ⟨ s, hs ⟩ := Cardinal.le_mk_iff_exists_subset.mp hx;
      have := Cardinal.eq.1 hs.2;
      obtain ⟨ e ⟩ := this;
      exact ⟨ fun i => e.symm ⟨ i ⟩ |>.1, fun i j hij => by simpa [ Fin.ext_iff ] using e.symm.injective ( Subtype.ext hij ), fun i => ⟨ hs.1 ( e.symm ⟨ i ⟩ |>.2 ) |>.1, hs.1 ( e.symm ⟨ i ⟩ |>.2 ) |>.2 ⟩ ⟩;
    exact ⟨ a, fun i => by intro hi; have := ha.2 i; simp_all +decide [ SimpleGraph.adj_comm ], ⟨ ha.1, fun i => ha.2 i |>.1 ⟩, fun i => ha.2 i |>.2.symm ⟩;

  have h_index_card : #( {a : Fin n → V // Function.Injective a ∧ ∀ i, a i ∈ X} ) ≤ #(X : Set V) + ℵ₀ := by
    have h_index_card : #( {a : Fin n → V // Function.Injective a ∧ ∀ i, a i ∈ X} ) ≤ #(Fin n → X) := by
      fapply Cardinal.mk_le_of_injective;
      exacts [ fun a => fun i => ⟨ a.val i, a.property.2 i ⟩, fun a b h => Subtype.ext <| funext fun i => by simpa using congr_fun h i ];
    refine le_trans h_index_card ?_
    by_cases hX : Finite X
    · exact (Cardinal.lt_aleph0_of_finite _).le.trans le_add_self
    · rw [not_finite_iff_infinite] at hX
      have h0 : ℵ₀ ≤ #X := Cardinal.infinite_iff.mp hX
      rw [Cardinal.mk_arrow, Cardinal.lift_uzero, Cardinal.mk_fin, Cardinal.lift_natCast,
        Cardinal.power_natCast]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [pow_zero]; exact Cardinal.one_le_aleph0.trans le_add_self
      · exact (Cardinal.power_nat_le h0).trans le_self_add

  have h_common_nbhd_card : ∀ a : {a : Fin n → V // Function.Injective a ∧ ∀ i, a i ∈ X}, #( {v | (∀ i, v ≠ a.1 i) ∧ ∀ i, G.Adj (a.1 i) v} : Set V ) ≤ ℵ₀ := by
    exact fun a => commonNbhd_le_aleph0 G n hfree a.1 a.2.1;

  have h_closure_step_card : #( {x | (n : Cardinal) ≤ #(nbhdIn G x X)} : Set V ) ≤ (#(X : Set V) + ℵ₀) * ℵ₀ := by
    refine' le_trans ( Cardinal.mk_le_mk_of_subset h_closure_step ) _;
    refine' le_trans ( Cardinal.mk_iUnion_le _ ) _;
    gcongr;
    exact ciSup_le' fun a => h_common_nbhd_card a;
  have hc : ℵ₀ ≤ #X + ℵ₀ := le_add_self
  calc #(closeStep G n X) ≤ #X + #({x | (n : Cardinal) ≤ #(nbhdIn G x X)} : Set V) :=
        Cardinal.mk_union_le _ _
    _ ≤ #X + (#X + ℵ₀) * ℵ₀ := by gcongr
    _ = #X + ℵ₀ := by
        rw [Cardinal.mul_eq_left hc le_add_self Cardinal.aleph0_ne_zero,
          Cardinal.add_eq_right hc le_self_add]

theorem subset_closeIter (G : SimpleGraph V) (n : ℕ) (X : Set V) (k : ℕ) :
    X ⊆ closeIter G n X k := by
  induction' k with k ih;
  · rfl;
  · exact Set.Subset.trans ih ( Set.subset_union_left )

theorem closeIter_mono_index (G : SimpleGraph V) (n : ℕ) (X : Set V) {k l : ℕ}
    (h : k ≤ l) : closeIter G n X k ⊆ closeIter G n X l := by
  induction h <;> simp_all +decide [ closeIter ];
  exact Set.Subset.trans ‹_› ( Set.subset_union_left )

theorem subset_cl (G : SimpleGraph V) (n : ℕ) (X : Set V) : X ⊆ cl G n X := by
  exact Set.subset_iUnion_of_subset 0 ( by rfl )

theorem cl_mono (G : SimpleGraph V) (n : ℕ) {X Y : Set V} (h : X ⊆ Y) :
    cl G n X ⊆ cl G n Y := by
  refine Set.iUnion_subset fun k => ?_;
  refine' Set.Subset.trans _ ( Set.subset_iUnion _ ( k + 1 ) );
  induction' k with k ih;
  · exact Set.Subset.trans h ( Set.subset_union_left );
  · refine' Set.union_subset_union ih _;
    exact fun x hx => le_trans hx.out ( Cardinal.mk_le_mk_of_subset <| by exact fun y hy => by exact ⟨ ih hy.1, hy.2 ⟩ )

theorem nclosed_cl (G : SimpleGraph V) (n : ℕ) (hn : 1 ≤ n) (X : Set V) :
    NClosed G n (cl G n X) := by
  intro x hx;
  contrapose! hx;
  obtain ⟨ s, hs ⟩ := Cardinal.le_mk_iff_exists_subset.mp hx;

  obtain ⟨ k, hk ⟩ : ∃ k, s ⊆ closeIter G n X k := by
    have h_finite : ∀ y ∈ s, ∃ k, y ∈ closeIter G n X k := by
      exact fun y hy => Set.mem_iUnion.mp ( hs.1 hy |>.1 );
    choose! k hk using h_finite;
    have h_finite : Set.Finite s := by
      exact Set.finite_coe_iff.mp ( Cardinal.lt_aleph0_iff_finite.mp ( hs.2.symm ▸ Cardinal.nat_lt_aleph0 n ) );
    exact ⟨ h_finite.toFinset.sup k, fun y hy => closeIter_mono_index G n X ( Finset.le_sup ( f := k ) ( h_finite.mem_toFinset.mpr hy ) ) ( hk y hy ) ⟩;

  have h_card : n ≤ #(nbhdIn G x (closeIter G n X k)) := by
    refine' hs.2 ▸ Cardinal.mk_le_mk_of_subset _;
    exact fun y hy => ⟨ hk hy, hs.1 hy |>.2 ⟩;
  exact Set.mem_iUnion.mpr ⟨ k + 1, by exact Set.mem_union_right _ h_card ⟩

theorem cl_card_le (G : SimpleGraph V) (n : ℕ) (hfree : ¬ HasKnAleph1 G n)
    (X : Set V) : #(cl G n X) ≤ #X + ℵ₀ := by

  have h_ind : ∀ k, #(closeIter G n X k) ≤ #X + ℵ₀ := by
    intro k
    induction k with
    | zero => exact le_self_add
    | succ k ih =>
      calc #(closeIter G n X (k + 1)) ≤ #(closeIter G n X k) + ℵ₀ := closeStep_card_le G n hfree _
        _ ≤ (#X + ℵ₀) + ℵ₀ := by gcongr
        _ = #X + ℵ₀ := by rw [add_assoc, Cardinal.aleph0_add_aleph0]
  have hU : cl G n X = ⋃ k : ULift.{u} ℕ, closeIter G n X k.down := by
    ext x
    simp only [cl, Set.mem_iUnion]
    exact ⟨fun ⟨k, hk⟩ => ⟨⟨k⟩, hk⟩, fun ⟨k, hk⟩ => ⟨k.down, hk⟩⟩
  have hc : ℵ₀ ≤ #X + ℵ₀ := le_add_self
  rw [hU]
  calc #(⋃ k : ULift.{u} ℕ, closeIter G n X k.down)
      ≤ #(ULift.{u} ℕ) * ⨆ k : ULift.{u} ℕ, #(closeIter G n X k.down) := Cardinal.mk_iUnion_le _
    _ ≤ ℵ₀ * (#X + ℵ₀) := by
        rw [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0]
        gcongr
        exact ciSup_le' fun k => h_ind k.down
    _ = #X + ℵ₀ := Cardinal.mul_eq_right hc hc Cardinal.aleph0_ne_zero

theorem nclosed_biUnion_lt {σ : Type u} [LinearOrder σ] (G : SimpleGraph V) (n : ℕ)
    (hn : 1 ≤ n) (M : σ → Set V) (hmono : Monotone M) (hcl : ∀ b, NClosed G n (M b))
    (a : σ) : NClosed G n (⋃ b ∈ {b : σ | b < a}, M b) := by
  intro x hx;
  by_contra h_contra;
  obtain ⟨s, hs⟩ : ∃ s : Finset V, s.card = n ∧ ∀ y ∈ s, y ∈ nbhdIn G x (⋃ b ∈ {b | b < a}, M b) := by
    obtain ⟨ s, hs ⟩ := Cardinal.le_mk_iff_exists_subset.mp ( le_of_not_gt h_contra );
    cases' Set.Finite.exists_finset_coe ( show Set.Finite s from Set.finite_coe_iff.mp ( Cardinal.lt_aleph0_iff_finite.mp ( by rw [ hs.2 ] ; exact Cardinal.nat_lt_aleph0 _ ) ) ) ; aesop;

  obtain ⟨b, hb⟩ : ∃ b < a, ∀ y ∈ s, y ∈ M b := by
    have h_exists_b : ∀ y ∈ s, ∃ b < a, y ∈ M b := by
      intro y hy; specialize hs; have := hs.2 y hy; unfold nbhdIn at this; aesop;
    choose! b hb₁ hb₂ using h_exists_b;
    use Finset.max' (Finset.image (fun y => b y.1 y.2) (Finset.attach s)) (by
    exact ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_attach _ ⟨ Classical.choose ( Finset.card_pos.mp ( by linarith ) ), Classical.choose_spec ( Finset.card_pos.mp ( by linarith ) ) ⟩ ) ⟩)
    generalize_proofs at *;
    refine' ⟨ _, _ ⟩;
    · simp +decide [ Finset.max' ];
      exact fun y hy => hb₁ y hy;
    · intro y hy; exact hmono ( Finset.le_max' _ _ <| Finset.mem_image_of_mem _ <| Finset.mem_attach _ ⟨ y, hy ⟩ ) <| hb₂ _ _;
  have h_card : #(nbhdIn G x (M b)) ≥ n := by
    refine' le_trans _ ( Cardinal.mk_le_mk_of_subset <| show ( s : Set V ) ⊆ nbhdIn G x ( M b ) from _ );
    · simp +decide [ hs.1 ];
    · exact fun y hy => ⟨ hb.2 y hy, hs.2 y hy |>.2 ⟩;
  exact not_lt_of_ge h_card ( hcl b x ( by aesop ) )

theorem nat_block_inj {m a b c d : ℕ} (hb : b < m) (hd : d < m)
    (h : m * a + b = m * c + d) : a = c ∧ b = d := by
  have hac : a = c := by
    rcases lt_trichotomy a c with hlt | heq | hlt
    · exfalso
      have : m * (a + 1) ≤ m * c := Nat.mul_le_mul_left m hlt
      rw [Nat.mul_succ] at this
      linarith
    · exact heq
    · exfalso
      have : m * (c + 1) ≤ m * a := Nat.mul_le_mul_left m hlt
      rw [Nat.mul_succ] at this
      linarith
  subst hac
  exact ⟨rfl, Nat.add_left_cancel h⟩

theorem countColorable_of_rank {σ : Type u} [LinearOrder σ] [WellFoundedLT σ]
    (G : SimpleGraph V) (n : ℕ) (hn : 1 ≤ n) (rank : V → σ)
    (hback : ∀ x, #({y | G.Adj x y ∧ rank y < rank x}) < (n : Cardinal))
    (hlevel : ∀ a : σ, ∃ g : V → ℕ,
      ∀ x y, rank x = a → rank y = a → G.Adj x y → g x ≠ g y) :
    GCountColorable G := by
  choose g hg using hlevel;
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : V → Fin (2 * n + 1), ∀ a b, G.Adj a b → rank a ≠ rank b → c₂ a ≠ c₂ b := by
    have h_colorable : ∀ x : V, ∃ fs : Finset V,
        {y | G.Adj x y ∧ rank y < rank x} = (fs : Set V) ∧ fs.card ≤ n := by
      intro x
      have h_finite : Set.Finite {y | G.Adj x y ∧ rank y < rank x} :=
        Set.finite_coe_iff.mp (Cardinal.lt_aleph0_iff_finite.mp
          (lt_of_lt_of_le (hback x) (Cardinal.natCast_lt_aleph0 |>.le)))
      refine ⟨h_finite.toFinset, h_finite.coe_toFinset.symm, ?_⟩
      have hb := hback x
      have hcard : #((h_finite.toFinset : Finset V) : Set V) = h_finite.toFinset.card :=
        Cardinal.mk_coe_finset
      rw [← h_finite.coe_toFinset, hcard] at hb
      exact_mod_cast hb.le
    choose fs hfs using h_colorable
    let D : SimpleGraph V := SimpleGraph.mk (fun x y => G.Adj x y ∧ rank x ≠ rank y)
      ⟨fun x y h => ⟨h.1.symm, Ne.symm h.2⟩⟩ ⟨fun x hx => hx.1.ne rfl⟩
    classical
    obtain ⟨c, hc⟩ := colorable_of_out D n fs (fun x => (hfs x).2) (by
      intro v w hvw
      rcases lt_or_gt_of_ne hvw.2 with hlt | hlt
      · right
        have hmem : v ∈ ({y | G.Adj w y ∧ rank y < rank w} : Set V) := ⟨hvw.1.symm, hlt⟩
        rw [(hfs w).1] at hmem
        exact Finset.mem_coe.1 hmem
      · left
        have hmem : w ∈ ({y | G.Adj v y ∧ rank y < rank v} : Set V) := ⟨hvw.1, hlt⟩
        rw [(hfs v).1] at hmem
        exact Finset.mem_coe.1 hmem)
    exact ⟨c, fun a b hab hr => hc a b ⟨hab, hr⟩⟩
  refine ⟨fun x => (2 * n + 1) * g (rank x) x + (c₂ x : ℕ), ?_⟩
  intro x y hxy heq
  obtain ⟨h1, h2⟩ := nat_block_inj (c₂ x).isLt (c₂ y).isLt heq
  by_cases h : rank x = rank y
  · apply hg (rank x) x y rfl h.symm hxy
    rw [h1, h]
  · exact hc₂ x y hxy h (Fin.ext h2)

theorem hasKnAleph1_of_induce (G : SimpleGraph V) (n : ℕ) (M : Set V)
    (h : HasKnAleph1 (G.induce M) n) : HasKnAleph1 G n := by
  obtain ⟨ a, B, ha, hB, hB', hB'' ⟩ := h;
  refine' ⟨ fun i => a i, Subtype.val '' B, _, _, _, _ ⟩;
  · exact Subtype.coe_injective.comp ha;
  · rw [ Cardinal.mk_image_eq ] ; aesop;
    exact Subtype.coe_injective;
  · grind;
  · aesop

theorem gCountColorable_of_le_aleph0 (G : SimpleGraph V) (h : #V ≤ ℵ₀) :
    GCountColorable G := by
  have h_countable : Infinite V → Nonempty (V ↪ ℕ) := by
    exact fun _ => Cardinal.lift_mk_le'.mp ( by simpa using h );
  by_cases hV : Infinite V;
  · obtain ⟨ c ⟩ := h_countable hV; exact ⟨ c, fun x y hxy => by simpa using c.injective.ne hxy.ne ⟩ ;
  · simp_all +decide [ Infinite ];
    obtain ⟨c, hc⟩ : ∃ c : V → Fin (Nat.card V), Function.Injective c := by
      haveI := Fintype.ofFinite V;
      exact ⟨ fun x => Fintype.equivFinOfCardEq ( by simp +decide [ Nat.card_eq_fintype_card ] ) x, by simp +decide [ Function.Injective ] ⟩;
    exact ⟨ fun x => c x, fun x y hxy => by simpa [ Fin.ext_iff ] using hc.ne hxy.ne ⟩

theorem countColorable_of_smaller (G : SimpleGraph V) (n : ℕ) (hn : 1 ≤ n)
    (hfree : ¬ HasKnAleph1 G n) (hbig : ℵ₀ < #V)
    (IH : ∀ (W : Type u) (GW : SimpleGraph W), #W < #V → ¬ HasKnAleph1 GW n →
      GCountColorable GW) :
    GCountColorable G := by
  classical
  obtain ⟨e⟩ : Nonempty ((#V).ord.ToType ≃ V) :=
    Cardinal.eq.1 (by simp)
  set Idx := (#V).ord.ToType
  set M : Idx → Set V := fun a => cl G n (e '' {b | b ≤ a}) with hM
  have hmono : Monotone M := by
    intro a b hab
    exact cl_mono _ _ (Set.image_mono (fun x hx => le_trans hx.out hab))
  have hcl : ∀ a, NClosed G n (M a) := fun a => nclosed_cl G n hn _
  have hsmall : ∀ a, #(M a) < #V := by
    intro a
    have h1 : #(M a) ≤ #(e '' {b : Idx | b ≤ a}) + ℵ₀ := cl_card_le G n hfree _
    have h2 : #(e '' {b : Idx | b ≤ a}) ≤ #(Set.Iio a) + 1 := by
      refine le_trans Cardinal.mk_image_le ?_
      refine le_trans (Cardinal.mk_le_mk_of_subset
        (show {b : Idx | b ≤ a} ⊆ insert a (Set.Iio a) from ?_)) Cardinal.mk_insert_le
      intro x hx
      have hx' : x ≤ a := hx
      rcases lt_or_eq_of_le hx' with h | h
      · exact Or.inr h
      · exact Or.inl h
    have h3 : #(Set.Iio a) < #V := Cardinal.mk_Iio_ord_toType a
    have haleph : ℵ₀ ≤ #V := le_of_lt hbig
    have h4 : #(Set.Iio a) + 1 < #V :=
      Cardinal.add_lt_of_lt haleph h3 (lt_of_lt_of_le Cardinal.one_lt_aleph0 haleph)
    calc #(M a) ≤ #(e '' {b : Idx | b ≤ a}) + ℵ₀ := h1
      _ ≤ (#(Set.Iio a) + 1) + ℵ₀ := by gcongr
      _ < #V := Cardinal.add_lt_of_lt haleph h4 hbig
  have hcov : ∀ x, x ∈ M (e.symm x) :=
    fun x => by
      have h : e (e.symm x) ∈ e '' {b | b ≤ e.symm x} :=
        Set.mem_image_of_mem e (Set.mem_setOf.mpr (le_refl (e.symm x)))
      rw [e.apply_symm_apply] at h
      exact Set.mem_of_mem_of_subset h (subset_cl G n _)
  set rank : V → Idx :=
    fun x => (wellFounded_lt (α := Idx)).min {a | x ∈ M a} ⟨e.symm x, hcov x⟩ with hrank
  have hmemR : ∀ x, x ∈ M (rank x) :=
    fun x => (wellFounded_lt (α := Idx)).min_mem {a | x ∈ M a} ⟨e.symm x, hcov x⟩
  have hleast : ∀ x b, b < rank x → x ∉ M b := by
    intro x b hb hmem
    exact (wellFounded_lt (α := Idx)).not_lt_min {a | x ∈ M a} hmem hb
  apply countColorable_of_rank G n hn rank
  · intro x
    set a := rank x
    set U := ⋃ b ∈ {b : Idx | b < a}, M b with hU
    have hUcl : NClosed G n U := nclosed_biUnion_lt G n hn M hmono hcl a
    have hxU : x ∉ U := by
      intro hx
      obtain ⟨b, hb₁, hb₂⟩ := Set.mem_iUnion₂.mp hx
      exact hleast x b hb₁ hb₂
    have hback : #(nbhdIn G x U) < n := hUcl x hxU
    have hsubset : {y | G.Adj x y ∧ rank y < rank x} ⊆ nbhdIn G x U :=
      fun y hy => ⟨Set.mem_iUnion₂.mpr ⟨rank y, hy.2, hmemR y⟩, hy.1⟩
    exact lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset hsubset) hback
  · intro a
    have h_induce : ¬ HasKnAleph1 (G.induce (M a)) n :=
      fun hh => hfree (hasKnAleph1_of_induce G n (M a) hh)
    obtain ⟨c, hc⟩ := IH (↥(M a)) (SimpleGraph.induce (M a) G) (hsmall a) h_induce
    refine ⟨fun x => if hx : x ∈ M a then c ⟨x, hx⟩ else 0, ?_⟩
    intro x y hrx hry hadj
    have hx : x ∈ M a := hrx ▸ hmemR x
    have hy : y ∈ M a := hry ▸ hmemR y
    simp only [dif_pos hx, dif_pos hy]
    exact hc ⟨x, hx⟩ ⟨y, hy⟩ hadj

theorem eh_hasKnAleph1 (G : SimpleGraph V)
    (h : ¬ (SimpleGraph.toHG G).ColorableBy ℵ₀) (n : ℕ) : HasKnAleph1 G n := by
  rw [← gCountColorable_iff_colorableBy] at h
  have key : ∀ κ : Cardinal.{u}, ∀ (W : Type u) (GW : SimpleGraph W),
      #W = κ → ¬ GCountColorable GW → HasKnAleph1 GW n := by
    refine fun κ => Cardinal.lt_wf.induction
      (C := fun κ => ∀ (W : Type u) (GW : SimpleGraph W),
        #W = κ → ¬ GCountColorable GW → HasKnAleph1 GW n) κ ?_
    intro κ IH W GW hcard hncc
    have hbig : ℵ₀ < #W := by
      by_contra hle
      exact hncc (gCountColorable_of_le_aleph0 GW (not_lt.mp hle))
    by_cases hn0 : n = 0
    · subst hn0
      refine ⟨Fin.elim0, Set.univ, ?_, ?_, ?_, ?_⟩
      · intro a; exact a.elim0
      · rw [Cardinal.mk_univ]; exact Cardinal.succ_aleph0 ▸ Order.succ_le_of_lt hbig
      · intro a; exact a.elim0
      · intro a; exact a.elim0
    · by_contra hfree
      refine hncc (countColorable_of_smaller GW n (Nat.one_le_iff_ne_zero.mpr hn0)
        hfree hbig ?_)
      intro W' GW' hlt hfree'
      by_contra hncc'
      exact hfree' (IH (#W') (hcard ▸ hlt) W' GW' rfl hncc')
  exact key (#V) V G rfl h

def HasKmm (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ a b : Fin m → V, Function.Injective a ∧ Function.Injective b ∧
    (∀ i j, a i ≠ b j) ∧ (∀ i j, G.Adj (a i) (b j))

theorem eh_hasKmm (G : SimpleGraph V)
    (h : ¬ (SimpleGraph.toHG G).ColorableBy ℵ₀) (m : ℕ) : HasKmm G m := by
  obtain ⟨a, B, ha, hB, hB', hB''⟩ : ∃ (a : Fin m → V) (B : Set V), Function.Injective a ∧ ℵ₁ ≤ #B ∧ (∀ i, a i ∉ B) ∧ (∀ i, ∀ b ∈ B, G.Adj (a i) b) := by
    exact eh_hasKnAleph1 G h m
  obtain ⟨b, hb⟩ : ∃ b : Fin m → V, Function.Injective b ∧ ∀ i, b i ∈ B := by
    have hB_inf : Infinite B := by
      contrapose! hB;
      exact lt_of_le_of_lt ( Cardinal.mk_le_aleph0 ) ( Cardinal.aleph0_lt_aleph_one );
    have := hB_inf.natEmbedding;
    exact ⟨ fun i => this i, fun i j hij => by simpa [ Fin.ext_iff ] using this.injective ( Subtype.ext hij ), fun i => this i |>.2 ⟩;
  exact ⟨ a, b, ha, hb.1, fun i j => by intro H; have := hB' i; have := hb.2 j; aesop, fun i j => hB'' i _ ( hb.2 j ) ⟩

end Erdos593
end

-- E4Proof
section
open Cardinal

namespace Erdos593

universe u

variable {W : Type u}

def HasK3nn (H : Hypergraph W) (n : ℕ) : Prop :=
  ∃ f : (Fin n ⊕ Fin n) ⊕ (Fin n × Fin n) → W, Function.Injective f ∧
    ∀ i j : Fin n,
      ({f (Sum.inl (Sum.inl i)), f (Sum.inl (Sum.inr j)), f (Sum.inr (i, j))} : Set W)
        ∈ H.edges

open Classical in
theorem cb_edge_exists {n : ℕ} (e : Sym2 (Fin n ⊕ Fin n))
    (he : e ∈ (completeBipartiteGraph (Fin n) (Fin n)).edgeFinset) :
    ∃ i j : Fin n, e = s(Sum.inl i, Sum.inr j) := by
  revert he
  refine Sym2.ind (fun a b he => ?_) e
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
  rcases a with a | a <;> rcases b with b | b
  · simp [completeBipartiteGraph] at he
  · exact ⟨a, b, rfl⟩
  · exact ⟨b, a, Sym2.eq_swap⟩
  · simp [completeBipartiteGraph] at he

open Classical in

theorem hasK3nn_embeds (H : Hypergraph W) (n : ℕ) (h : HasK3nn H n) :
    (graphExpansion (completeBipartiteGraph (Fin n) (Fin n))).Embeds H := by
  unfold FTS.Embeds graphExpansion
  dsimp only
  obtain ⟨f, hf, hedge⟩ := h
  have hex : ∀ x : Sym2 (Fin n ⊕ Fin n),
      x ∈ (completeBipartiteGraph (Fin n) (Fin n)).edgeSet →
      ∃ p : Fin n × Fin n, x = s(Sum.inl p.1, Sum.inr p.2) := by
    intro x hx
    obtain ⟨i, j, hij⟩ := cb_edge_exists x (SimpleGraph.mem_edgeFinset.mpr hx)
    exact ⟨(i, j), hij⟩
  refine ⟨fun v => Sum.elim (Sum.elim (fun i => f (Sum.inl (Sum.inl i)))
      (fun j => f (Sum.inl (Sum.inr j))))
      (fun x => f (Sum.inr (hex x.1 (SimpleGraph.mem_edgeFinset.mp x.2)).choose)) v, ?_, ?_⟩
  · intro a b hab
    rcases a with (a | a) | a <;> rcases b with (b | b) | b <;>
      simp only [Sum.elim_inl, Sum.elim_inr] at hab <;>
      have := hf hab <;> simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at this
    · rw [this]
    · rw [this]
    · apply congrArg Sum.inr
      apply Subtype.ext
      rw [(hex a.1 (SimpleGraph.mem_edgeFinset.mp a.2)).choose_spec,
        (hex b.1 (SimpleGraph.mem_edgeFinset.mp b.2)).choose_spec, this]
  · intro e he
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 he
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq,
      Set.image_singleton, Sum.elim_inl, Sum.elim_inr]
    have hp := (hex x.1 (SimpleGraph.mem_edgeFinset.mp x.2)).choose_spec
    generalize (hex x.1 (SimpleGraph.mem_edgeFinset.mp x.2)).choose = p at hp ⊢
    have hq : s((Quot.out x.1).1, (Quot.out x.1).2) = s(Sum.inl p.1, Sum.inr p.2) := by
      rw [← hp]; exact Quot.out_eq x.1
    rcases Sym2.eq_iff.1 hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      simp only [Sum.elim_inl, Sum.elim_inr]
      exact hedge p.1 p.2
    · rw [h1, h2, Set.insert_comm]
      simp only [Sum.elim_inl, Sum.elim_inr]
      exact hedge p.1 p.2

def HGCountColorable (H : Hypergraph W) : Prop :=
  ∃ c : W → ℕ, H.ProperColoring c

theorem hgCountColorable_iff (H : Hypergraph W) :
    HGCountColorable H ↔ H.ColorableBy ℵ₀ := by
  constructor;
  · intro h;
    convert colorableBy_aleph0_of_countable H _ _;
    exact ULift ℕ;
    exact Cardinal.mk_le_aleph0;
    exact fun x => ⟨ h.choose x ⟩;
    intro e he; obtain ⟨ u, hu, v, hv, huv ⟩ := h.choose_spec e he; use u, hu, v, hv; aesop;
  · intro h;
    convert h using 1;
    constructor <;> intro h <;> rcases h with ⟨ c, hc ⟩;
    · grind;
    · obtain ⟨ f, hf ⟩ := Cardinal.eq.1 ( Cardinal.mk_out ℵ₀ );
      use fun x => ( f ( c x ) ).down;
      intro e he; obtain ⟨ u, hu, v, hv, huv ⟩ := hc e he; use u, hu, v, hv; simp_all +decide [ Function.LeftInverse, Function.RightInverse ] ;
      grind

def IsDeltaRoot (H : Hypergraph W) (t : ℕ) (f : Set W) : Prop :=
  ∃ D : Set (Set W), D ⊆ H.edges ∧ (t : Cardinal) ≤ #D ∧ (∀ e ∈ D, f ⊆ e) ∧
    (∀ e₁ ∈ D, ∀ e₂ ∈ D, e₁ ≠ e₂ → e₁ ∩ e₂ = f)

def rootsGraph (H : Hypergraph W) (t : ℕ) : SimpleGraph W :=
  SimpleGraph.fromRel (fun x y => IsDeltaRoot H t ({x, y} : Set W))

theorem deltaRoot_extend (H : Hypergraph W) (t : ℕ) (f g : Set W)
    (hf : IsDeltaRoot H t f) (hg : #g < (t : Cardinal)) (hfg : f ⊆ g) :
    ∃ e ∈ H.edges, f ⊆ e ∧ e ∩ g = f := by
  obtain ⟨ D, hDsub, hDcard, hDf, hDpair ⟩ := hf;
  contrapose! hg;

  have hv : ∀ e ∈ D, ∃ v : W, v ∈ (e ∩ g) \ f := by
    exact fun e he => Set.exists_of_ssubset ( lt_of_le_of_ne ( by aesop_cat ) ( Ne.symm ( hg e ( hDsub he ) ( hDf e he ) ) ) );
  choose! v hv₁ hv₂ using hv;
  refine' le_trans hDcard _;
  refine' ⟨ fun x => ⟨ v x.1 x.2, _ ⟩, fun x y hxy => _ ⟩;
  grind;
  grind +extAll

set_option maxHeartbeats 2000000 in
theorem exists_private_assignment (H : Hypergraph W) (hts : H.IsTripleSystem) (n : ℕ)
    (a b : Fin n → W) (Core : Finset W)
    (hCa : ∀ i, a i ∈ Core) (hCb : ∀ j, b j ∈ Core) (hCard : Core.card ≤ 2 * n)
    (hab : ∀ i j, a i ≠ b j)
    (hroot : ∀ i j, IsDeltaRoot H (3 * n ^ 2 + 1) ({a i, b j} : Set W)) :
    ∃ P : Fin n × Fin n → W, Function.Injective P ∧ (∀ p, P p ∉ Core) ∧
      ∀ p, ({a p.1, b p.2, P p} : Set W) ∈ H.edges := by
  rcases n with ( _ | n ) <;> simp_all +decide [ Set.InjOn ];
  · exact ⟨ fun _ => by aesop, by aesop_cat ⟩;
  · have hkey : ∀ s : Finset (Fin (n + 1) × Fin (n + 1)), ∃ P : Fin (n + 1) × Fin (n + 1) → W, Set.InjOn P s ∧ (∀ p ∈ s, P p ∉ Core) ∧ (∀ p ∈ s, ({a p.1, b p.2, P p} : Set W) ∈ H.edges) := by
      intro s
      induction' s using Finset.induction with p s ih;
      · exact ⟨ fun _ => a 0, by simp +decide [ Set.InjOn ] ⟩;
      · obtain ⟨ P, hP₁, hP₂, hP₃ ⟩ := ‹_›;

        obtain ⟨w, hw⟩ : ∃ w : W, w ∉ Core ∧ w ∉ Set.image P s ∧ ({a p.1, b p.2, w} : Set W) ∈ H.edges := by
          have := deltaRoot_extend H ( 3 * ( n + 1 ) ^ 2 + 1 ) { a p.1, b p.2 } ( Core ∪ P '' s ) ( hroot p.1 p.2 ) ?_ ?_ <;> simp_all +decide [ Set.subset_def ];
          · obtain ⟨ e, he₁, he₂, he₃ ⟩ := this; simp_all +decide [ Set.Subset.antisymm_iff, Set.subset_def ] ;
            obtain ⟨w, hw⟩ : ∃ w : W, w ∈ e ∧ w ≠ a p.1 ∧ w ≠ b p.2 := by
              have := hts e he₁; simp_all +decide [ Set.ncard_eq_toFinset_card' ] ;
              contrapose! this;
              rw [ show e = { a p.1, b p.2 } from Set.ext fun x => by by_cases hx : x = a p.1 <;> specialize this x <;> aesop ] ; simp +decide [ Set.ncard_pair, hab ];
            refine' ⟨ w, _, _, _ ⟩;
            · grind;
            · grind +ring;
            · convert he₁ using 1;
              have := hts e he₁; simp_all +decide [ Set.ncard_eq_toFinset_card' ] ;
              rw [ Set.ncard_eq_three ] at this;
              grind;
          · refine' lt_of_le_of_lt ( Cardinal.mk_le_mk_of_subset _ ) _;
            exact ↑Core ∪ P '' ↑s;
            · exact Set.Subset.rfl;
            · refine' lt_of_le_of_lt ( Cardinal.mk_le_mk_of_subset _ ) _;
              exact Set.range ( fun x : Core ⊕ s => x.elim ( fun x => x.val ) fun x => P x.val );
              · rintro x ( hx | ⟨ y, hy, rfl ⟩ ) <;> [ exact ⟨ Sum.inl ⟨ x, hx ⟩, rfl ⟩ ; exact ⟨ Sum.inr ⟨ y, hy ⟩, rfl ⟩ ];
              · refine' lt_of_le_of_lt ( Cardinal.mk_range_le ) _;
                simp +decide [ Cardinal.mk_sum ];
                norm_cast ; nlinarith [ show s.card ≤ ( n + 1 ) * ( n + 1 ) - 1 from Nat.le_sub_one_of_lt ( lt_of_lt_of_le ( Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.subset_univ _, by aesop_cat ⟩ ) ) ( by simp +decide [ Finset.card_univ ] ) ), Nat.sub_add_cancel ( show 1 ≤ ( n + 1 ) * ( n + 1 ) from Nat.mul_pos ( Nat.succ_pos _ ) ( Nat.succ_pos _ ) ) ];
        use fun q => if q = p then w else P q;
        simp_all +decide [ Set.InjOn ];
        grind +splitImp;
    specialize hkey Finset.univ ; aesop;

theorem hasK3nn_of_rootsKmm (H : Hypergraph W) (hts : H.IsTripleSystem) (n : ℕ)
    (hK : HasKmm (rootsGraph H (3 * n ^ 2 + 1)) n) : HasK3nn H n := by
  classical
  obtain ⟨a, b, ha, hb, hab, hadj⟩ := hK
  have hroot : ∀ i j, IsDeltaRoot H (3 * n ^ 2 + 1) ({a i, b j} : Set W) := by
    intro i j
    have h := hadj i j
    rw [rootsGraph, SimpleGraph.fromRel_adj] at h
    rcases h.2 with h' | h'
    · exact h'
    · rwa [Set.pair_comm] at h'
  set Core : Finset W := Finset.univ.image a ∪ Finset.univ.image b with hCoreDef
  have hCa : ∀ i, a i ∈ Core :=
    fun i => Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
  have hCb : ∀ j, b j ∈ Core :=
    fun j => Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩))
  have hCard : Core.card ≤ 2 * n := by
    have h0 : Core.card ≤ (Finset.univ.image a).card + (Finset.univ.image b).card :=
      Finset.card_union_le _ _
    have h1 := Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := a)
    have h2 := Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := b)
    simp only [Finset.card_univ, Fintype.card_fin] at h1 h2
    omega
  obtain ⟨P, hPinj, hPcore, hPedge⟩ :=
    exists_private_assignment H hts n a b Core hCa hCb hCard hab hroot
  have hPa : ∀ p i, P p ≠ a i := fun p i h => hPcore p (h ▸ hCa i)
  have hPb : ∀ p j, P p ≠ b j := fun p j h => hPcore p (h ▸ hCb j)
  refine ⟨Sum.elim (Sum.elim a b) P, ?_, fun i j => hPedge (i, j)⟩
  rintro ((i | i) | p) ((j | j) | q) hxy <;>
    simp only [Sum.elim_inl, Sum.elim_inr] at hxy <;>
    first
      | rw [ha hxy] | rw [hb hxy] | rw [hPinj hxy]
      | exact absurd hxy (hab _ _) | exact absurd hxy.symm (hab _ _)
      | exact absurd hxy (hPa _ _) | exact absurd hxy.symm (hPa _ _)
      | exact absurd hxy (hPb _ _) | exact absurd hxy.symm (hPb _ _)

theorem rootsGraph_countColorable (H : Hypergraph W) (hts : H.IsTripleSystem) (n : ℕ)
    (hfree : ¬ HasK3nn H n) : GCountColorable (rootsGraph H (3 * n ^ 2 + 1)) := by
  by_contra hnc
  rw [gCountColorable_iff_colorableBy] at hnc
  exact hfree (hasK3nn_of_rootsKmm H hts n (eh_hasKmm (rootsGraph H (3 * n ^ 2 + 1)) hnc n))

def IsRootDS (H : Hypergraph W) (f : Set W) (D : Finset (Set W)) : Prop :=
  (∀ e ∈ D, e ∈ H.edges ∧ f ⊆ e) ∧
    (∀ e₁ ∈ D, ∀ e₂ ∈ D, e₁ ≠ e₂ → e₁ ∩ e₂ = f)

theorem rootDS_card_lt (H : Hypergraph W) (t : ℕ) (f : Set W)
    (hf : ¬ IsDeltaRoot H t f) (D : Finset (Set W)) (hD : IsRootDS H f D) :
    D.card < t := by
  contrapose! hf;
  use D;
  simp_all +decide [ IsRootDS ];
  exact fun x hx => hD.1 x hx |>.1

open Classical in

theorem IsRootDS_insert (H : Hypergraph W) (f : Set W) (D : Finset (Set W))
    (hD : IsRootDS H f D) (e : Set W) (he : e ∈ H.edges) (hfe : f ⊆ e)
    (hint : ∀ e' ∈ D, e ∩ e' = f) (hnew : e ∉ D) :
    IsRootDS H f (insert e D) := by
  refine ⟨?_, ?_⟩
  · intro e'' he''
    rcases Finset.mem_insert.mp he'' with h | h
    · subst h; exact ⟨he, hfe⟩
    · exact hD.1 e'' h
  · intro e₁ h₁ e₂ h₂ hne
    rcases Finset.mem_insert.mp h₁ with h₁' | h₁' <;>
      rcases Finset.mem_insert.mp h₂ with h₂' | h₂'
    · exact absurd (h₁'.trans h₂'.symm) hne
    · subst h₁'; exact hint e₂ h₂'
    · subst h₂'; rw [Set.inter_comm]; exact hint e₁ h₁'
    · exact hD.2 e₁ h₁' e₂ h₂' hne

open Classical in

theorem exists_maximal_rootDS (H : Hypergraph W) (t : ℕ) (f : Set W)
    (hf : ¬ IsDeltaRoot H t f) :
    ∃ D : Finset (Set W), IsRootDS H f D ∧
      ∀ e ∈ H.edges, f ⊆ e → (∀ e' ∈ D, e ∩ e' = f) → e ∈ D := by
  obtain ⟨D, hD⟩ : ∃ D : Finset (Set W), IsRootDS H f D ∧
      ∀ D' : Finset (Set W), IsRootDS H f D' → D'.card ≤ D.card := by
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (∃ D : Finset (Set W), IsRootDS H f D ∧ D.card = m) ∧
        ∀ k, (∃ D : Finset (Set W), IsRootDS H f D ∧ D.card = k) → k ≤ m := by
      apply_rules [Set.exists_max_image]
      · exact Set.finite_iff_bddAbove.mpr ⟨t, fun n hn => by
          obtain ⟨D, hD₁, rfl⟩ := hn; exact le_of_lt (rootDS_card_lt H t f hf D hD₁)⟩
      · exact ⟨0, ⟨∅, by simp +decide [IsRootDS]⟩⟩
    obtain ⟨⟨D, hD₁, hD₂⟩, hD₃⟩ := hm
    exact ⟨D, hD₁, fun D' hD' => by linarith [hD₃ _ ⟨D', hD', rfl⟩]⟩
  refine ⟨D, hD.1, fun e he hfe hint => ?_⟩
  by_contra hnew
  have hins : IsRootDS H f (insert e D) := IsRootDS_insert H f D hD.1 e he hfe hint hnew
  have hcard : (insert e D).card = D.card + 1 := Finset.card_insert_of_notMem hnew
  have := hD.2 _ hins
  omega

open Classical in

noncomputable def maxDS (H : Hypergraph W) (t : ℕ) (f : Set W) : Finset (Set W) :=
  if h : ¬ IsDeltaRoot H t f then (exists_maximal_rootDS H t f h).choose else ∅

def witnessVerts (H : Hypergraph W) (t : ℕ) (f : Set W) : Set W :=
  ⋃ e ∈ maxDS H t f, e

theorem maxDS_spec (H : Hypergraph W) (t : ℕ) (f : Set W) (hf : ¬ IsDeltaRoot H t f) :
    IsRootDS H f (maxDS H t f) ∧
      ∀ e ∈ H.edges, f ⊆ e → (∀ e' ∈ maxDS H t f, e ∩ e' = f) →
        e ∈ maxDS H t f := by
  rw [maxDS, dif_pos hf]
  exact (exists_maximal_rootDS H t f hf).choose_spec

theorem witnessVerts_finite (H : Hypergraph W) (hts : H.IsTripleSystem) (t : ℕ)
    (f : Set W) : (witnessVerts H t f).Finite := by
  by_cases h : IsDeltaRoot H t f;
  · unfold witnessVerts maxDS; aesop;
  · have hspec := maxDS_spec H t f h
    have hfin : ∀ e ∈ maxDS H t f, (e : Set W).Finite := fun e he =>
      Set.finite_of_ncard_pos (by rw [hts e (hspec.1.1 e he |>.1)]; norm_num)
    have := Set.Finite.biUnion (Finset.finite_toSet (maxDS H t f)) (fun e he => hfin e he)
    simpa only [witnessVerts, Finset.mem_coe] using this

theorem witnessVerts_card_le (H : Hypergraph W) (hts : H.IsTripleSystem) (t : ℕ)
    (f : Set W) : #(witnessVerts H t f) ≤ ℵ₀ := by
  have h := (witnessVerts_finite H hts t f)
  exact le_of_lt h.lt_aleph0

def DCloseStep (H : Hypergraph W) (t : ℕ) (X : Set W) : Set W :=
  X ∪ {v | ∃ x ∈ X, ∃ y ∈ X, x ≠ y ∧ v ∈ witnessVerts H t {x, y}}

def DCloseIter (H : Hypergraph W) (t : ℕ) (X : Set W) : ℕ → Set W
  | 0 => X
  | k + 1 => DCloseStep H t (DCloseIter H t X k)

def Dcl (H : Hypergraph W) (t : ℕ) (X : Set W) : Set W := ⋃ k, DCloseIter H t X k

def DClosed (H : Hypergraph W) (t : ℕ) (X : Set W) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≠ y → witnessVerts H t {x, y} ⊆ X

theorem subset_DCloseIter (H : Hypergraph W) (t : ℕ) (X : Set W) (k : ℕ) :
    X ⊆ DCloseIter H t X k := by
  induction' k with k ih
  · rfl
  · exact Set.Subset.trans ih Set.subset_union_left

theorem DCloseIter_mono_index (H : Hypergraph W) (t : ℕ) (X : Set W) {k l : ℕ}
    (h : k ≤ l) : DCloseIter H t X k ⊆ DCloseIter H t X l := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact Set.Subset.trans ih Set.subset_union_left

theorem subset_Dcl (H : Hypergraph W) (t : ℕ) (X : Set W) : X ⊆ Dcl H t X :=
  Set.subset_iUnion_of_subset 0 (by rfl)

theorem Dcl_mono (H : Hypergraph W) (t : ℕ) {X Y : Set W} (h : X ⊆ Y) :
    Dcl H t X ⊆ Dcl H t Y := by
  apply Set.iUnion_mono;
  intro k;
  induction' k with k ih;
  · exact h;
  · refine' Set.union_subset_union ih _;
    exact fun v hv => by obtain ⟨ x, hx, y, hy, hxy, hv ⟩ := hv; exact ⟨ x, ih hx, y, ih hy, hxy, hv ⟩ ;

theorem DClosed_Dcl (H : Hypergraph W) (t : ℕ) (X : Set W) :
    DClosed H t (Dcl H t X) := by
  intro x hx y hy hxy v hv; simp_all +decide [ DClosed, Dcl ] ;
  obtain ⟨ kx, hkx ⟩ := hx; obtain ⟨ ky, hky ⟩ := hy; use Max.max kx ky + 1; simp_all +decide [ DCloseIter ] ;
  exact Set.mem_union_right _ ⟨ x, DCloseIter_mono_index _ _ _ ( le_max_left _ _ ) hkx, y, DCloseIter_mono_index _ _ _ ( le_max_right _ _ ) hky, hxy, hv ⟩

theorem DCloseStep_card_le (H : Hypergraph W) (hts : H.IsTripleSystem) (t : ℕ)
    (X : Set W) : #(DCloseStep H t X) ≤ #X + ℵ₀ := by

  set A := {v : W | ∃ x ∈ X, ∃ y ∈ X, x ≠ y ∧ v ∈ witnessVerts H t {x, y}} with hA_def
  have hDCloseStep : DCloseStep H t X = X ∪ A := by
    grind +locals
  generalize_proofs at *; (

  suffices hA_card : #(A) ≤ #(X × X) * Cardinal.aleph0 by
    by_cases hX : Infinite X <;> simp_all +decide [ Cardinal.mk_prod, Cardinal.mul_eq_max ];
    · refine' le_trans ( Cardinal.mk_union_le _ _ ) _ ; aesop;
    · refine' le_trans ( Cardinal.mk_union_le _ _ ) _;
      refine' add_le_add le_rfl _;
      exact Cardinal.mk_le_aleph0_iff.mpr ( Set.Finite.countable <| Set.Finite.subset ( Set.Finite.biUnion ( Set.finite_coe_iff.mp hX ) fun x hx => Set.Finite.biUnion ( Set.finite_coe_iff.mp hX ) fun y hy => Set.Finite.subset ( witnessVerts_finite H hts t { x, y } ) fun z => by aesop ) fun x hx => by aesop );

  have hA_subset : A ⊆ ⋃ p : ↥X × ↥X, witnessVerts H t {(p.1 : W), (p.2 : W)} := by
    intro v hv; obtain ⟨ x, hx, y, hy, hxy, hv ⟩ := hv; exact Set.mem_iUnion.2 ⟨ ⟨ ⟨ x, hx ⟩, ⟨ y, hy ⟩ ⟩, hv ⟩ ;
  refine' le_trans ( Cardinal.mk_le_mk_of_subset hA_subset ) _;
  refine' le_trans ( Cardinal.mk_iUnion_le _ ) _;
  exact mul_le_mul_right (ciSup_le' fun p => witnessVerts_card_le H hts t _) _)

theorem Dcl_card_le (H : Hypergraph W) (hts : H.IsTripleSystem) (t : ℕ)
    (X : Set W) : #(Dcl H t X) ≤ #X + ℵ₀ := by
  have hk : ∀ k, #(DCloseIter H t X k) ≤ #X + ℵ₀ := by
    intro k
    induction k with
    | zero => exact self_le_add_right _ _
    | succ k ih =>
      refine le_trans (DCloseStep_card_le H hts t _) ?_
      calc #(DCloseIter H t X k) + ℵ₀ ≤ (#X + ℵ₀) + ℵ₀ := add_le_add ih le_rfl
        _ = #X + ℵ₀ := by rw [add_assoc, Cardinal.aleph0_add_aleph0]
  have heq : Dcl H t X = ⋃ i : ULift.{u} ℕ, DCloseIter H t X i.down := by
    ext v
    simp only [Dcl, Set.mem_iUnion]
    exact ⟨fun ⟨k, hk⟩ => ⟨⟨k⟩, hk⟩, fun ⟨k, hk⟩ => ⟨k.down, hk⟩⟩
  rw [heq]
  refine le_trans (Cardinal.mk_iUnion_le _) ?_
  have h1 : #(ULift.{u} ℕ) = ℵ₀ := Cardinal.mk_eq_aleph0 _
  rw [h1]
  have h3 : (⨆ i : ULift.{u} ℕ, #(DCloseIter H t X i.down)) ≤ #X + ℵ₀ :=
    ciSup_le' fun i => hk i.down
  have h2 : ℵ₀ ≤ #X + ℵ₀ := self_le_add_left _ _
  calc ℵ₀ * (⨆ i : ULift.{u} ℕ, #(DCloseIter H t X i.down)) ≤ ℵ₀ * (#X + ℵ₀) := by gcongr
    _ = #X + ℵ₀ := by rw [Cardinal.mul_eq_max le_rfl h2, max_eq_right h2]

theorem DClosed_biUnion_lt {σ : Type u} [LinearOrder σ] (H : Hypergraph W) (t : ℕ)
    (M : σ → Set W) (hmono : Monotone M) (hcl : ∀ b, DClosed H t (M b)) (a : σ) :
    DClosed H t (⋃ b ∈ {b : σ | b < a}, M b) := by
  intro x hx y hy hxy;
  simp_all +decide [ Set.subset_def ];
  obtain ⟨ i, hi, hx ⟩ := hx; obtain ⟨ j, hj, hy ⟩ := hy; use fun z hz => ⟨ Max.max i j, max_lt hi hj, hcl ( Max.max i j ) _ ( hmono ( le_max_left _ _ ) hx ) _ ( hmono ( le_max_right _ _ ) hy ) hxy hz ⟩ ;

def hasRoot (H : Hypergraph W) (t : ℕ) (e : Set W) : Prop :=
  ∃ u v, u ≠ v ∧ ({u, v} : Set W) ⊆ e ∧ IsDeltaRoot H t {u, v}

theorem claim22_abstract (H : Hypergraph W) (hts : H.IsTripleSystem) (t : ℕ)
    (U : Set W) (hU : DClosed H t U) (x y z : W)
    (hxU : x ∈ U) (hyU : y ∈ U) (hzU : z ∉ U)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (e : Set W) (he : e ∈ H.edges) (hxe : x ∈ e) (hye : y ∈ e) (hze : z ∈ e)
    (hnr : ¬ IsDeltaRoot H t ({x, y} : Set W)) : False := by

  have h_e_in_maxDS : e ∈ maxDS H t {x, y} := by
    obtain ⟨hDS, hmax⟩ := maxDS_spec H t {x, y} hnr;
    refine' hmax e he ( by aesop_cat ) _;
    intro e' he';
    apply Set.Subset.antisymm;
    · intro w hw;
      have h_w_in_U : w ∈ U := by
        have h_w_in_U : e' ⊆ U := by
          exact Set.subset_biUnion_of_mem he' |> Set.Subset.trans <| hU x hxU y hyU hxy;
        exact h_w_in_U hw.2;
      have := hts e he;
      rw [ Set.ncard_eq_three ] at this;
      grind;
    · simp_all +decide [ Set.subset_def ];
      have := hDS.1 e' he'; aesop;
  exact hzU ( hU x hxU y hyU hxy |> fun h => h ( Set.mem_iUnion₂.mpr ⟨ e, h_e_in_maxDS, hze ⟩ ) )

theorem colorable_combine {Idx : Type*} (rank : W → Idx) (E₀ : Set (Set W))
    (d : Idx → W → ℕ)
    (hsep : ∀ e ∈ E₀, ∃ a, ∃ u ∈ e, ∃ w ∈ e, rank u = a ∧ rank w = a ∧ d a u ≠ d a w) :
    (⟨E₀⟩ : Hypergraph W).ColorableBy ℵ₀ := by
  convert colorableBy_aleph0_of_countable _ _ _ using 1;
  exact ULift ℕ;
  exact Cardinal.mk_le_aleph0;
  exact fun v => ⟨ d ( rank v ) v ⟩;
  intro e he; obtain ⟨ a, u, hu, w, hw, hru, hrw, hne ⟩ := hsep e he; use u, hu, w, hw; aesop;

theorem E'_colorable (H : Hypergraph W) (hts : H.IsTripleSystem) (n : ℕ)
    (hfree : ¬ HasK3nn H n) :
    (⟨{e | e ∈ H.edges ∧ hasRoot H (3 * n ^ 2 + 1) e}⟩ : Hypergraph W).ColorableBy ℵ₀ := by
  obtain ⟨c, hc⟩ := rootsGraph_countColorable H hts n hfree;
  convert colorableBy_aleph0_of_countable _ _ _ using 1;
  exact ULift ℕ;
  exact Cardinal.mk_le_aleph0;
  exact fun x => ⟨ c x ⟩;
  intro e he; obtain ⟨ u, v, huv, huv', huv'' ⟩ := he.2; simp_all +decide [ rootsGraph ] ;
  exact ⟨ u, huv' ( Set.mem_insert _ _ ), v, huv' ( Set.mem_insert_of_mem _ ( Set.mem_singleton _ ) ), hc u v huv ( Or.inl huv'' ) ⟩

def Hsub (H : Hypergraph W) (S : Set W) : Hypergraph ↑S :=
  ⟨{s | Subtype.val '' s ∈ H.edges}⟩

theorem Hsub_isTripleSystem (H : Hypergraph W) (hts : H.IsTripleSystem) (S : Set W) :
    (Hsub H S).IsTripleSystem := by
  intro s hs
  have h := hts _ hs
  rw [Set.ncard_image_of_injective _ Subtype.val_injective] at h
  exact h

theorem Hsub_hasK3nn (H : Hypergraph W) (S : Set W) (n : ℕ)
    (h : HasK3nn (Hsub H S) n) : HasK3nn H n := by
  obtain ⟨ g, hg_inj, hg_edge ⟩ := h;
  refine' ⟨ fun x => g x, _, _ ⟩;
  · exact Subtype.coe_injective.comp hg_inj;
  · convert hg_edge using 1;
    simp +decide [ Hsub, Set.image_insert_eq, Set.image_singleton ]

theorem Hsub_edge_of_subset (H : Hypergraph W) (S : Set W) (e : Set W)
    (he : e ∈ H.edges) (hsub : e ⊆ S) :
    ∃ s : Set ↑S, Subtype.val '' s = e ∧ s ∈ (Hsub H S).edges := by

  use {x : S | x.val ∈ e};

  unfold Hsub;
  aesop

theorem sub_colorable_gives (H : Hypergraph W) (hts : H.IsTripleSystem) (n : ℕ)
    (hfree : ¬ HasK3nn H n)
    (minim : ∀ (W' : Type u) (H' : Hypergraph W'), #W' < #W → H'.IsTripleSystem →
       ¬ HasK3nn H' n → H'.ColorableBy ℵ₀)
    (S : Set W) (hS : #S < #W) :
    ∃ d : W → ℕ, ∀ e ∈ H.edges, e ⊆ S → ∃ u ∈ e, ∃ w ∈ e, d u ≠ d w := by
  classical
  have htri : (Hsub H S).IsTripleSystem := Hsub_isTripleSystem H hts S
  have hfree' : ¬ HasK3nn (Hsub H S) n := fun h => hfree (Hsub_hasK3nn H S n h)
  obtain ⟨c, hc⟩ := minim (↑S) (Hsub H S) hS htri hfree'
  have hcnt : Countable (ℵ₀ : Cardinal.{u}).out :=
    Cardinal.mk_le_aleph0_iff.mp (le_of_eq (Cardinal.mk_out _))
  obtain ⟨g, hg⟩ : ∃ g : (ℵ₀ : Cardinal.{u}).out → ℕ, Function.Injective g :=
    ⟨_, (exists_injective_nat _).choose_spec⟩
  set d : W → ℕ := fun v => if h : v ∈ S then g (c ⟨v, h⟩) else 0 with hd
  have hval : ∀ a : ↑S, d (a : W) = g (c a) := by
    intro a; simp only [hd, dif_pos a.2, Subtype.coe_eta]
  refine ⟨d, fun e he hsub => ?_⟩
  obtain ⟨s, hsimg, hsedge⟩ := Hsub_edge_of_subset H S e he hsub
  obtain ⟨u, hu, w, hw, huw⟩ := hc s hsedge
  refine ⟨(u : W), by rw [← hsimg]; exact ⟨u, hu, rfl⟩, (w : W),
    by rw [← hsimg]; exact ⟨w, hw, rfl⟩, ?_⟩
  rw [hval u, hval w]
  exact fun h => huw (hg h)

theorem tripleSystem_colorable_of_le_aleph0 (H : Hypergraph W)
    (hts : H.IsTripleSystem) (h : #W ≤ ℵ₀) : H.ColorableBy ℵ₀ := by
  obtain ⟨c, hc⟩ : ∃ c : W → ℕ, ∀ e ∈ H.edges, ∃ u ∈ e, ∃ v ∈ e, c u ≠ c v := by
    cases' Cardinal.le_mk_iff_exists_set.mp h with S hS;
    cases' Cardinal.eq.1 hS.symm with f hf;
    use fun w => (f w).val.down;
    intro e he; have := hts e he; rw [ Set.ncard_eq_three ] at this; obtain ⟨ a, b, c, hab, hac, hbc, rfl ⟩ := this; use a, by simp +decide, b, by simp +decide; ; simp +decide [ hab ] ;
    exact fun h => hab <| f.injective <| Subtype.ext h;
  exact hgCountColorable_iff H |>.1 ⟨ c, hc ⟩

theorem hasK3nn_from_grid (H : Hypergraph W) (n : ℕ) (X Y : Fin n → W)
    (P : Fin n → Fin n → W)
    (hInj : Function.Injective
      (Sum.elim (Sum.elim X Y) (fun p : Fin n × Fin n => P p.1 p.2)))
    (hedge : ∀ i j, ({X i, Y j, P i j} : Set W) ∈ H.edges) : HasK3nn H n := by
  use Sum.elim (Sum.elim X Y) (fun p => P p.1 p.2);
  grind

theorem exists_finset_pairwise {α : Type*} [Fintype α] [DecidableEq α]
    (Q : α → Prop) (R : α → α → Prop) (n : ℕ)
    (hstep : ∀ D : Finset α, D.card < n → (∀ x ∈ D, Q x) →
      ∃ z, z ∉ D ∧ Q z ∧ ∀ x ∈ D, R x z ∧ R z x) :
    ∃ C : Finset α, C.card = n ∧ (∀ x ∈ C, Q x) ∧
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y → R x y := by
  induction' n with n ih;
  · exact ⟨ ∅, rfl, by simp +decide ⟩;
  ·
    obtain ⟨C, hC⟩ := ih (fun D hD hQ => hstep D (Nat.lt_succ_of_lt hD) hQ);
    obtain ⟨z, hz⟩ := hstep C (by linarith) hC.2.1;
    use Insert.insert z C;
    grind

open Classical in

theorem sum_agree_le {V : Type*} (t q : ℕ) (P : Fin q → Fin q → V)
    (hrow : ∀ (a : Fin q) (v : V), (Finset.univ.filter (fun b => P a b = v)).card < t)
    (b : Fin q) :
    ∑ z : Fin q, (Finset.univ.filter (fun a => P a b = P a z)).card ≤ q * (t - 1) := by

  have h_fubini : ∑ z : Fin q, (Finset.univ.filter (fun a => P a b = P a z)).card = ∑ a : Fin q, (Finset.univ.filter (fun z => P a b = P a z)).card := by
    simp +decide only [Finset.card_filter];
    exact Finset.sum_comm;
  exact h_fubini.symm ▸ le_trans ( Finset.sum_le_sum fun i _ => show Finset.card ( Finset.filter ( fun z => P i b = P i z ) Finset.univ ) ≤ t - 1 from Nat.le_sub_one_of_lt ( by simpa [ eq_comm ] using hrow i ( P i b ) ) ) ( by simp +decide [ mul_comm ] ) ;

open Classical in

theorem cols_step {V : Type*} (n t q : ℕ) (ht : 1 ≤ t) (hn : 1 ≤ n) (hq : n ^ 2 * t ≤ q)
    (P : Fin q → Fin q → V)
    (hrow : ∀ (a : Fin q) (v : V), (Finset.univ.filter (fun b => P a b = v)).card < t)
    (D : Finset (Fin q)) (hD : D.card < n) :
    ∃ z, z ∉ D ∧ ∀ x ∈ D,
      (Finset.univ.filter (fun a => P a x = P a z)).card < n * t := by

  have h_bad_card : ∑ x ∈ D, ∑ z : Fin q, (Finset.univ.filter (fun a => P a x = P a z)).card ≤ D.card * q * (t - 1) := by
    calc _ ≤ ∑ x ∈ D, q * (t - 1) := Finset.sum_le_sum fun x _ => sum_agree_le t q P hrow x
      _ = D.card * q * (t - 1) := by rw [Finset.sum_const, _root_.smul_eq_mul, mul_assoc]

  have h_bad_card : ∑ z : Fin q, ∑ x ∈ D, (Finset.univ.filter (fun a => P a x = P a z)).card < (q - D.card) * n * t := by
    rw [ Finset.sum_comm ];
    nlinarith [ Nat.sub_add_cancel ( show 1 ≤ t from ht ), Nat.sub_add_cancel ( show D.card ≤ q from le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ), mul_le_mul_right hD.le q, mul_le_mul_right hn q, mul_le_mul_right ht q, mul_le_mul_right hD.le t, mul_le_mul_right hn t, mul_le_mul_right ht t ];
  contrapose! h_bad_card;
  have h_bad_card : ∑ z ∈ Finset.univ \ D, ∑ x ∈ D, (Finset.univ.filter (fun a => P a x = P a z)).card ≥ (q - D.card) * n * t := by
    have h_bad_card : ∀ z ∈ Finset.univ \ D, ∑ x ∈ D, (Finset.univ.filter (fun a => P a x = P a z)).card ≥ n * t := by
      exact fun z hz => by obtain ⟨ x, hx, hx' ⟩ := h_bad_card z ( Finset.mem_sdiff.mp hz |>.2 ) ; exact le_trans hx' ( Finset.single_le_sum ( fun x _ => Nat.zero_le ( Finset.card ( Finset.filter ( fun a => P a x = P a z ) Finset.univ ) ) ) hx ) ;
    simpa [ mul_assoc, Finset.card_sdiff ] using Finset.sum_le_sum h_bad_card;
  exact h_bad_card.trans ( Finset.sum_le_sum_of_subset ( Finset.sdiff_subset ) )

open Classical in

theorem rows_step {V : Type*} (n t q : ℕ) (ht : 1 ≤ t) (hn : 1 ≤ n)
    (hq : 3 * n ^ 3 * t + n ≤ q) (P : Fin q → Fin q → V) (B : Fin n → Fin q)
    (hcol : ∀ (b : Fin q) (v : V), (Finset.univ.filter (fun a => P a b = v)).card < t)
    (hpair : ∀ i i' : Fin n, i ≠ i' →
      (Finset.univ.filter (fun a => P a (B i) = P a (B i'))).card < n * t)
    (D : Finset (Fin q)) (hD : D.card < n)
    (hDQ : ∀ x ∈ D, ∀ k l : Fin n, k ≠ l → P x (B k) ≠ P x (B l)) :
    ∃ z, z ∉ D ∧ (∀ k l : Fin n, k ≠ l → P z (B k) ≠ P z (B l)) ∧
      ∀ x ∈ D, (∀ k l : Fin n, P x (B k) ≠ P z (B l)) ∧
        (∀ k l : Fin n, P z (B k) ≠ P x (B l)) := by

  set I := Finset.biUnion (Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2)) (fun p => Finset.univ.filter (fun z => P z (B p.1) = P z (B p.2)))
  set C := Finset.biUnion D (fun x => Finset.biUnion (Finset.univ ×ˢ Finset.univ) (fun p : Fin n × Fin n => Finset.univ.filter (fun z => P z (B p.2) = P x (B p.1)) ∪ Finset.univ.filter (fun z => P z (B p.1) = P x (B p.2))));

  have hI : I.card ≤ n ^ 3 * t := by
    refine' le_trans ( Finset.card_biUnion_le ) _;
    refine' le_trans ( Finset.sum_le_sum fun x hx => Nat.le_of_lt ( hpair _ _ <| Finset.mem_filter.mp hx |>.2 ) ) _;
    rw [ show ( Finset.univ.filter fun p : Fin n × Fin n => ¬p.1 = p.2 ) = Finset.univ \ Finset.diag ( Finset.univ : Finset ( Fin n ) ) by ext ⟨ i, j ⟩ ; simp +decide [ Finset.mem_sdiff, Finset.mem_diag ] ] ; simp +decide [ Finset.card_sdiff, Finset.card_singleton, Finset.card_univ ] ; ring_nf;
    exact Nat.mul_le_mul_right _ ( by nlinarith only [ Nat.sub_le ( n ^ 2 ) n ] )
  have hC : C.card ≤ 2 * n ^ 3 * t := by
    refine' le_trans ( Finset.card_biUnion_le ) ( le_trans ( Finset.sum_le_sum fun x hx => Finset.card_biUnion_le ) _ );
    refine' le_trans ( Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => Finset.card_union_le _ _ ) _;
    refine' le_trans ( Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => add_le_add ( Nat.le_of_lt ( hcol _ _ ) ) ( Nat.le_of_lt ( hcol _ _ ) ) ) _ ; norm_num ; ring_nf ; norm_num;
    nlinarith [ mul_le_mul_right hn t ];

  have hBad : (D ∪ I ∪ C).card < q := by
    grind +qlia;
  obtain ⟨ z, hz ⟩ := Finset.exists_of_ssubset ( Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.subset_univ ( D ∪ I ∪ C ), by aesop_cat ⟩ );
  simp +zetaDelta at *;
  exact ⟨ z, hz.1, hz.2.1, fun x hx => ⟨ fun k l => Ne.symm ( hz.2.2 x hx k l |>.1 ), fun k l => hz.2.2 x hx k l |>.2 ⟩ ⟩

open Classical in

theorem greedy_rainbow {V : Type*} (n t q : ℕ) (ht : 1 ≤ t)
    (hq : 4 * t * n ^ 3 + n ^ 2 + n ≤ q) (P : Fin q → Fin q → V)
    (hrow : ∀ (a : Fin q) (v : V), (Finset.univ.filter (fun b => P a b = v)).card < t)
    (hcol : ∀ (b : Fin q) (v : V), (Finset.univ.filter (fun a => P a b = v)).card < t) :
    ∃ A B : Fin n → Fin q, Function.Injective A ∧ Function.Injective B ∧
      ∀ i j i' j', P (A i) (B j) = P (A i') (B j') → i = i' ∧ j = j' := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩

  obtain ⟨Ccol, hCcard, -, hCpair⟩ :=
    exists_finset_pairwise (α := Fin q) (fun _ => True)
      (fun b b' => (Finset.univ.filter (fun a => P a b = P a b')).card < n * t) n
      (fun D hD _ => by
        obtain ⟨z, hz, hzD⟩ := cols_step n t q ht hn (by nlinarith [hq]) P hrow D hD
        refine ⟨z, hz, trivial, fun x hx => ⟨hzD x hx, ?_⟩⟩
        show (Finset.univ.filter (fun a => P a z = P a x)).card < n * t
        rw [show (Finset.univ.filter (fun a => P a z = P a x)) =
            (Finset.univ.filter (fun a => P a x = P a z)) from
          Finset.filter_congr (fun a _ => by rw [eq_comm])]
        exact hzD x hx)

  set B : Fin n → Fin q := ⇑(Ccol.orderEmbOfFin hCcard) with hBdef
  have hBinj : Function.Injective B := (Ccol.orderEmbOfFin hCcard).injective
  have hBmem : ∀ i, B i ∈ Ccol := fun i => Ccol.orderEmbOfFin_mem hCcard i
  have hpairB : ∀ i i' : Fin n, i ≠ i' →
      (Finset.univ.filter (fun a => P a (B i) = P a (B i'))).card < n * t :=
    fun i i' hii => hCpair (B i) (hBmem i) (B i') (hBmem i') (fun h => hii (hBinj h))

  obtain ⟨Crow, hRcard, hRQ, hRpair⟩ :=
    exists_finset_pairwise (α := Fin q)
      (fun a => ∀ k l : Fin n, k ≠ l → P a (B k) ≠ P a (B l))
      (fun a a' => ∀ k l : Fin n, P a (B k) ≠ P a' (B l)) n
      (fun D hD hDQ => by
        obtain ⟨z, hz, hzQ, hzcross⟩ := rows_step n t q ht hn (by nlinarith [hq]) P B hcol hpairB D hD hDQ
        exact ⟨z, hz, hzQ, fun x hx => ⟨(hzcross x hx).1, (hzcross x hx).2⟩⟩)
  set A : Fin n → Fin q := ⇑(Crow.orderEmbOfFin hRcard) with hAdef
  have hAinj : Function.Injective A := (Crow.orderEmbOfFin hRcard).injective
  have hAmem : ∀ i, A i ∈ Crow := fun i => Crow.orderEmbOfFin_mem hRcard i
  refine ⟨A, B, hAinj, hBinj, fun i j i' j' hgrid => ?_⟩
  by_cases hAA : A i = A i'
  · refine ⟨hAinj hAA, ?_⟩
    by_contra hjj
    have hcol' : P (A i) (B j) = P (A i) (B j') := by rw [hgrid, hAA]
    exact hRQ (A i) (hAmem i) j j' hjj hcol'
  · exact absurd hgrid (hRpair (A i) (hAmem i) (A i') (hAmem i') hAA j j')

def layerGraph {Idx : Type*} [LT Idx] (H : Hypergraph W) (t : ℕ) (rank : W → Idx)
    (i : Idx) : SimpleGraph W :=
  SimpleGraph.fromRel (fun x y =>
    rank x = i ∧ rank y = i ∧ ∃ z, rank z < i ∧ ({x, y, z} : Set W) ∈ H.edges ∧
      ¬ hasRoot H t ({x, y, z} : Set W))

theorem exists_delta_filtration (H : Hypergraph W) (hts : H.IsTripleSystem) (t : ℕ)
    (hbig : ℵ₀ < #W) :
    ∃ (Idx : Type u) (_ : LinearOrder Idx) (_ : WellFoundedLT Idx) (rank : W → Idx),
      (∀ a : Idx, #({v | rank v = a} : Set W) < #W) ∧
      (∀ (x y z : W), rank x < rank z → rank y < rank z → x ≠ y →
        ¬ IsDeltaRoot H t ({x, y} : Set W) →
        ∀ e ∈ H.edges, x ∈ e → y ∈ e → z ∈ e → False) := by

  set Idx := (#W).ord.ToType;

  obtain ⟨e, he⟩ : ∃ e : Idx ≃ W, True := by
    refine' ⟨ _, trivial ⟩;
    exact Classical.choice ( Cardinal.eq.1 <| by simp +decide [ Idx ] )
  set M : Idx → Set W := fun a => Dcl H t (Set.image e {b | b ≤ a});

  have hM_mono : Monotone M := by
    intro a b hab; apply Dcl_mono; exact Set.image_mono (fun x hx => le_trans hx.out hab) ;
  have hM_DClosed : ∀ a, DClosed H t (M a) := by
    exact fun a => DClosed_Dcl H t _
  have hM_small : ∀ a, #(M a) < #W := by
    intro a
    have h_card_image : #(Set.image e {b | b ≤ a}) ≤ Cardinal.mk (Set.Iic a) := by
      exact Cardinal.mk_image_le.trans ( by simp +decide [ Set.Iic_def ] )
    have h_card_Iic : Cardinal.mk (Set.Iic a) < #W := by
      have h_card_Iic : Cardinal.mk (Set.Iio a) < #W := by
        convert Cardinal.mk_Iio_ord_toType a using 1;
      have h_card_Iic : Cardinal.mk (Set.Iic a) = Cardinal.mk (Set.Iio a) + 1 := by
        rw [ ← Cardinal.mk_singleton ( a : Idx ), ← Cardinal.mk_union_of_disjoint ];
        · congr with x ; simp +decide [ le_iff_lt_or_eq, eq_comm ];
        · exact Set.disjoint_singleton_right.2 (lt_irrefl a)
      convert Cardinal.add_lt_of_lt _ ‹_› _ using 1;
      · exact le_of_lt hbig;
      · exact lt_of_le_of_lt ( by norm_num ) hbig
    have h_card_M : #(M a) ≤ #(Set.image e {b | b ≤ a}) + ℵ₀ := by
      convert Dcl_card_le H hts t ( Set.image e { b | b ≤ a } ) using 1
    have h_card_M_lt : #(M a) < #W := by
      refine' lt_of_le_of_lt h_card_M _;
      refine' lt_of_le_of_lt ( add_le_add h_card_image le_rfl ) _;
      convert Cardinal.add_lt_of_lt _ _ _ using 1;
      · exact le_of_lt hbig;
      · exact h_card_Iic;
      · exact hbig
    exact h_card_M_lt
  have hM_cover : ∀ x, x ∈ M (e.symm x) := by
    intro x
    simp [M, subset_Dcl];
    exact subset_Dcl _ _ _ ⟨ e.symm x, by simp +decide, by simp +decide ⟩;

  obtain ⟨rank, hrank⟩ : ∃ rank : W → Idx, ∀ x, x ∈ M (rank x) ∧ ∀ b, b < rank x → x ∉ M b := by
    have h_wellFounded : WellFounded (fun x y : Idx => x < y) := by
      exact wellFounded_lt;
    have h_least : ∀ x, ∃ a, x ∈ M a ∧ ∀ b, b < a → x ∉ M b := by
      intro x;
      have := h_wellFounded.has_min { a | x ∈ M a } ⟨ e.symm x, hM_cover x ⟩;
      exact ⟨ this.choose, this.choose_spec.1, fun b hb hb' => this.choose_spec.2 b hb' hb ⟩;
    exact ⟨ fun x => Classical.choose ( h_least x ), fun x => Classical.choose_spec ( h_least x ) ⟩;
  refine' ⟨ Idx, inferInstance, inferInstance, rank, _, _ ⟩;
  · intro a
    have h_subset : {v | rank v = a} ⊆ M a := by
      intro v hv; specialize hrank v; aesop;
    exact lt_of_le_of_lt ( Cardinal.mk_le_mk_of_subset h_subset ) ( hM_small a );
  · intros x y z hxz hyz hxy hnr e he hx hy hz;
    apply claim22_abstract H hts t (⋃ b ∈ {b | b < rank z}, M b) (DClosed_biUnion_lt H t M hM_mono hM_DClosed (rank z)) x y z (by
    exact Set.mem_iUnion₂.mpr ⟨ rank x, hxz, hrank x |>.1 ⟩) (by
    exact Set.mem_iUnion₂.mpr ⟨ rank y, hyz, hrank y |>.1 ⟩) (by
    simp +zetaDelta at *;
    exact fun x hx => hrank z |>.2 x hx) hxy (by
    exact fun h => hxz.ne <| h ▸ rfl) (by
    exact fun h => by have := hrank z; aesop;) e he hx hy hz hnr

theorem delta_root_contra (H : Hypergraph W) (t : ℕ) (ht : 0 < t) (u w : W) (huw : u ≠ w)
    (S : Finset W) (hScard : t ≤ S.card) (hSne : ∀ x ∈ S, x ≠ u ∧ x ≠ w)
    (hedge : ∀ x ∈ S, ({x, u, w} : Set W) ∈ H.edges)
    (hnr : ∀ x ∈ S, ¬ hasRoot H t ({x, u, w} : Set W)) : False := by

  have h_delta_root : IsDeltaRoot H t ({u, w} : Set W) := by

    use { {x, u, w} | x ∈ S };
    refine' ⟨ _, _, _, _ ⟩;
    · exact fun x hx => by obtain ⟨ y, hy, rfl ⟩ := hx; exact hedge y hy;
    · refine' le_trans _ ( show _ ≤ _ from Cardinal.mk_le_mk_of_subset _ );
      rotate_left;
      exact Set.image ( fun x => { x, u, w } ) S;
      · exact Set.image_subset_iff.mpr fun x hx => ⟨ x, hx, rfl ⟩;
      · rw [ Set.image_eq_range ];
        rw [ Cardinal.mk_range_eq ];
        · simp +decide [ Cardinal.mk_coe_finset, hScard ];
        · intro x y; simp +decide [ Finset.ext_iff, Set.ext_iff ] ;
          intro h; specialize h x; aesop;
    · aesop_cat;
    · grind;
  obtain ⟨ x, hx ⟩ := Finset.card_pos.mp ( pos_of_gt ( lt_of_lt_of_le ht hScard ) ) ; specialize hnr x hx; unfold hasRoot at hnr; simp_all +decide ;

theorem Ess_adj {Idx : Type u} [LinearOrder Idx] (H : Hypergraph W)
    (hts : H.IsTripleSystem) (t : ℕ) (rank : W → Idx)
    (hclaim : ∀ (x y z : W), rank x < rank z → rank y < rank z → x ≠ y →
        ¬ IsDeltaRoot H t ({x, y} : Set W) →
        ∀ e ∈ H.edges, x ∈ e → y ∈ e → z ∈ e → False)
    (e : Set W) (heE : e ∈ H.edges) (hnr : ¬ hasRoot H t e)
    (hne : ¬ ∃ a, ∀ v ∈ e, rank v = a) :
    ∃ (i : Idx) (x y : W), x ∈ e ∧ y ∈ e ∧ rank x = i ∧ rank y = i ∧
      (layerGraph H t rank i).Adj x y := by
  obtain ⟨ p, q, r, hpq, hpr, hqr, he ⟩ := Set.ncard_eq_three.mp ( hts e heE );

  have h_no_max : ¬(rank p > rank q ∧ rank p > rank r) ∧ ¬(rank q > rank p ∧ rank q > rank r) ∧ ¬(rank r > rank p ∧ rank r > rank q) := by
    refine' ⟨ _, _, _ ⟩ <;> intro h <;> simp_all +decide [ hasRoot ];
    · exact hclaim q r p h.1 h.2 ( by tauto ) ( hnr q r ( by tauto ) ( by simp +decide [ Set.insert_subset_iff ] ) ) _ heE ( by simp +decide ) ( by simp +decide ) ( by simp +decide );
    · exact hclaim p r q h.1 h.2 ( by tauto ) ( hnr p r ( by tauto ) ( by simp +decide [ Set.insert_subset_iff ] ) ) _ heE ( by simp +decide ) ( by simp +decide ) ( by simp +decide );
    · exact hclaim p q r h.1 h.2 ( by tauto ) ( hnr p q ( by tauto ) ( by simp +decide [ Set.insert_subset_iff ] ) ) _ heE ( by simp +decide ) ( by simp +decide ) ( by simp +decide );

  obtain ⟨i, hi⟩ : ∃ i : Idx, (rank p = i ∧ rank q = i ∧ rank r ≠ i) ∨ (rank p = i ∧ rank r = i ∧ rank q ≠ i) ∨ (rank q = i ∧ rank r = i ∧ rank p ≠ i) := by
    contrapose! hne; simp_all +decide ;
    grind +splitImp;
  rcases hi with ( ⟨ hp, hq, hr ⟩ | ⟨ hp, hr, hq ⟩ | ⟨ hq, hr, hp ⟩ ) <;> simp_all +decide [ layerGraph ];
  · grind +splitImp;
  · refine' Or.inl ( Or.inl ⟨ q, lt_of_le_of_ne h_no_max hq, _, _ ⟩ );
    · convert heE using 1 ; ext ; simp +decide [ *, or_comm, or_left_comm, or_assoc ];
    · convert hnr using 1;
      simp +decide [ Set.insert_comm, Set.pair_comm ];
  · refine' Or.inr ⟨ Ne.symm hqr, Or.inl ⟨ p, lt_of_le_of_ne h_no_max hp, _, _ ⟩ ⟩;
    · convert heE using 1 ; ext ; simp +decide [ *, or_comm, or_left_comm, or_assoc ];
    · convert hnr using 1;
      simp +decide [ Set.Subset.antisymm_iff, Set.subset_def, hasRoot ];
      grind

theorem grid_injective {Idx : Type u} [LinearOrder Idx] (rank : W → Idx) (n q : ℕ)
    (i₀ : Idx) (a b : Fin q → W) (A B : Fin n → Fin q) (P : Fin q → Fin q → W)
    (hainj : Function.Injective a) (hbinj : Function.Injective b)
    (hAinj : Function.Injective A) (hBinj : Function.Injective B)
    (hab : ∀ i j, a i ≠ b j)
    (hgrid : ∀ i j i' j', P (A i) (B j) = P (A i') (B j') → i = i' ∧ j = j')
    (hra : ∀ k, rank (a k) = i₀) (hrb : ∀ k, rank (b k) = i₀)
    (hrP : ∀ i j, rank (P (A i) (B j)) < i₀) :
    Function.Injective
      (Sum.elim (Sum.elim (fun i => a (A i)) (fun j => b (B j)))
        (fun p : Fin n × Fin n => P (A p.1) (B p.2))) := by
  intro x y hxy;
  grind +revert

theorem hasK3nn_zero (H : Hypergraph W) : HasK3nn H 0 := by
  refine ⟨fun x => (by rcases x with (i | i) | ⟨i, _⟩ <;> exact i.elim0), ?_, ?_⟩
  · rintro ((i | i) | ⟨i, _⟩) _ _ <;> exact i.elim0
  · rintro i; exact i.elim0

theorem hasK3nn_step (H : Hypergraph W) (hts : H.IsTripleSystem) (n : ℕ)
    (hbig : ℵ₀ < #W) (huc : H.UncountablyChromatic) (hfree : ¬ HasK3nn H n)
    (minim : ∀ (W' : Type u) (H' : Hypergraph W'), #W' < #W → H'.IsTripleSystem →
       ¬ HasK3nn H' n → H'.ColorableBy ℵ₀) : False := by
  classical
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact absurd (hasK3nn_zero H) hfree
    · exact hn

  have hE'col := E'_colorable H hts n hfree
  have hE''uc := uncountablyChromatic_diff H.edges
      {e | e ∈ H.edges ∧ hasRoot H (3 * n ^ 2 + 1) e} huc hE'col
  obtain ⟨Idx, instLO, instWF, rank, hlevel, hclaim⟩ :=
    exists_delta_filtration H hts (3 * n ^ 2 + 1) hbig
  letI := instLO
  letI := instWF

  have hlc : ∀ a : Idx, ∃ d : W → ℕ, ∀ e ∈ H.edges, e ⊆ {v | rank v = a} →
      ∃ u ∈ e, ∃ w ∈ e, d u ≠ d w :=
    fun a => sub_colorable_gives H hts n hfree minim {v | rank v = a} (hlevel a)
  choose dstar hdstar using hlc
  set E'' : Set (Set W) := {e | e ∈ H.edges ∧ ¬ hasRoot H (3 * n ^ 2 + 1) e} with hE''def
  have hE''eq :
      (H.edges \ {e | e ∈ H.edges ∧ hasRoot H (3 * n ^ 2 + 1) e}) = E'' := by
    ext e; constructor
    · rintro ⟨he, hne⟩; exact ⟨he, fun hr => hne ⟨he, hr⟩⟩
    · rintro ⟨he, hnr⟩; exact ⟨he, fun h => hnr h.2⟩
  rw [hE''eq] at hE''uc

  have hEstarcol :
      (⟨{e | e ∈ E'' ∧ ∃ a, ∀ v ∈ e, rank v = a}⟩ : Hypergraph W).ColorableBy ℵ₀ := by
    apply colorable_combine rank _ dstar
    rintro e ⟨heE'', a, ha⟩
    obtain ⟨u, hu, w, hw, huw⟩ := hdstar a e heE''.1 (fun v hv => ha v hv)
    exact ⟨a, u, hu, w, hw, ha u hu, ha w hw, huw⟩

  have hExists : ∃ i₀ : Idx,
      ¬ (SimpleGraph.toHG (layerGraph H (3 * n ^ 2 + 1) rank i₀)).ColorableBy ℵ₀ := by
    by_contra hall
    push_neg at hall
    have hlayerc : ∀ i : Idx, ∃ c : W → ℕ,
        ∀ x y, (layerGraph H (3 * n ^ 2 + 1) rank i).Adj x y → c x ≠ c y :=
      fun i => (gCountColorable_iff_colorableBy _).2 (hall i)
    choose dlayer hdlayer using hlayerc
    have hEsscol :
        (⟨E'' \ {e | e ∈ E'' ∧ ∃ a, ∀ v ∈ e, rank v = a}⟩ : Hypergraph W).ColorableBy ℵ₀ := by
      apply colorable_combine rank _ dlayer
      rintro e ⟨heE'', hne⟩
      have hne' : ¬ ∃ a, ∀ v ∈ e, rank v = a := fun h => hne ⟨heE'', h⟩
      obtain ⟨i, x, y, hxe, hye, hrx, hry, hadj⟩ :=
        Ess_adj H hts (3 * n ^ 2 + 1) rank hclaim e heE''.1 heE''.2 hne'
      exact ⟨i, x, hxe, y, hye, hrx, hry, hdlayer i x y hadj⟩
    have hunion := colorableBy_aleph0_union
      {e | e ∈ E'' ∧ ∃ a, ∀ v ∈ e, rank v = a}
      (E'' \ {e | e ∈ E'' ∧ ∃ a, ∀ v ∈ e, rank v = a}) hEstarcol hEsscol
    have hcov : {e | e ∈ E'' ∧ ∃ a, ∀ v ∈ e, rank v = a} ∪
        (E'' \ {e | e ∈ E'' ∧ ∃ a, ∀ v ∈ e, rank v = a}) = E'' := by
      rw [Set.union_diff_cancel]; intro e he; exact he.1
    rw [hcov] at hunion
    exact hE''uc hunion
  obtain ⟨i₀, hi₀⟩ := hExists

  set q := 4 * (3 * n ^ 2 + 1) * n ^ 3 + n ^ 2 + n with hqdef
  obtain ⟨a, b, hainj, hbinj, hab, hadj⟩ :=
    eh_hasKmm (layerGraph H (3 * n ^ 2 + 1) rank i₀) hi₀ q
  have hqpos : 0 < q := by positivity

  have hP : ∀ i j : Fin q, ∃ z, rank (a i) = i₀ ∧ rank (b j) = i₀ ∧ rank z < i₀ ∧
      ({a i, b j, z} : Set W) ∈ H.edges ∧
      ¬ hasRoot H (3 * n ^ 2 + 1) ({a i, b j, z} : Set W) := by
    intro i j
    have hh := hadj i j
    rw [layerGraph, SimpleGraph.fromRel_adj] at hh
    obtain ⟨_, hr⟩ := hh
    rcases hr with ⟨r1, r2, z, hz1, hz2, hz3⟩ | ⟨r1, r2, z, hz1, hz2, hz3⟩
    · exact ⟨z, r1, r2, hz1, hz2, hz3⟩
    · refine ⟨z, r2, r1, hz1, ?_, ?_⟩
      · rw [Set.insert_comm]; exact hz2
      · rw [Set.insert_comm]; exact hz3
  choose P hPra hPrb hPrz hPedge hPnr using hP

  have hcol : ∀ (j : Fin q) (v : W),
      (Finset.univ.filter (fun i => P i j = v)).card < (3 * n ^ 2 + 1) := by
    intro j v
    by_contra hge
    push_neg at hge
    have hpos : 0 < (Finset.univ.filter (fun i => P i j = v)).card :=
      lt_of_lt_of_le (by positivity) hge
    obtain ⟨i0, hi0⟩ := Finset.card_pos.mp hpos
    have hi0v : P i0 j = v := (Finset.mem_filter.mp hi0).2
    have hbv : b j ≠ v := by
      intro h; have := hPrz i0 j; rw [hi0v, ← h, hPrb i0 j] at this; exact lt_irrefl _ this
    refine delta_root_contra H (3 * n ^ 2 + 1) (by positivity) (b j) v hbv
      ((Finset.univ.filter (fun i => P i j = v)).image a) ?_ ?_ ?_ ?_
    · rw [Finset.card_image_of_injective _ hainj]; exact hge
    · rintro x hx
      simp only [Finset.mem_image, Finset.mem_filter] at hx
      obtain ⟨i, ⟨_, hiv⟩, rfl⟩ := hx
      refine ⟨hab i j, ?_⟩
      intro h; have := hPrz i j; rw [hiv, ← h, hPra i j] at this; exact lt_irrefl _ this
    · rintro x hx
      simp only [Finset.mem_image, Finset.mem_filter] at hx
      obtain ⟨i, ⟨_, hiv⟩, rfl⟩ := hx
      have := hPedge i j; rw [hiv] at this; exact this
    · rintro x hx
      simp only [Finset.mem_image, Finset.mem_filter] at hx
      obtain ⟨i, ⟨_, hiv⟩, rfl⟩ := hx
      have := hPnr i j; rw [hiv] at this; exact this

  have hrow : ∀ (i : Fin q) (v : W),
      (Finset.univ.filter (fun j => P i j = v)).card < (3 * n ^ 2 + 1) := by
    intro i v
    by_contra hge
    push_neg at hge
    have hpos : 0 < (Finset.univ.filter (fun j => P i j = v)).card :=
      lt_of_lt_of_le (by positivity) hge
    obtain ⟨j0, hj0⟩ := Finset.card_pos.mp hpos
    have hj0v : P i j0 = v := (Finset.mem_filter.mp hj0).2
    have hav : a i ≠ v := by
      intro h; have := hPrz i j0; rw [hj0v, ← h, hPra i j0] at this; exact lt_irrefl _ this
    refine delta_root_contra H (3 * n ^ 2 + 1) (by positivity) (a i) v hav
      ((Finset.univ.filter (fun j => P i j = v)).image b) ?_ ?_ ?_ ?_
    · rw [Finset.card_image_of_injective _ hbinj]; exact hge
    · rintro x hx
      simp only [Finset.mem_image, Finset.mem_filter] at hx
      obtain ⟨j, ⟨_, hjv⟩, rfl⟩ := hx
      refine ⟨(hab i j).symm, ?_⟩
      intro h; have := hPrz i j; rw [hjv, ← h, hPrb i j] at this; exact lt_irrefl _ this
    · rintro x hx
      simp only [Finset.mem_image, Finset.mem_filter] at hx
      obtain ⟨j, ⟨_, hjv⟩, rfl⟩ := hx
      have := hPedge i j; rw [hjv] at this
      rw [Set.insert_comm]; exact this
    · rintro x hx
      simp only [Finset.mem_image, Finset.mem_filter] at hx
      obtain ⟨j, ⟨_, hjv⟩, rfl⟩ := hx
      have := hPnr i j; rw [hjv] at this
      rw [Set.insert_comm]; exact this

  obtain ⟨A, B, hAinj, hBinj, hgrid⟩ :=
    greedy_rainbow n (3 * n ^ 2 + 1) q (by omega) (le_of_eq hqdef.symm) P hrow hcol

  refine hfree (hasK3nn_from_grid H n (fun i => a (A i)) (fun j => b (B j))
    (fun i j => P (A i) (B j)) ?_ ?_)
  · exact grid_injective rank n q i₀ a b A B P hainj hbinj hAinj hBinj hab hgrid
      (fun k => hPra k ⟨0, hqpos⟩) (fun k => hPrb ⟨0, hqpos⟩ k)
      (fun i j => hPrz (A i) (B j))
  · intro i j; exact hPedge (A i) (B j)

theorem hasK3nn_of_uncountable (H : Hypergraph W) (hts : H.IsTripleSystem)
    (huc : H.UncountablyChromatic) (n : ℕ) : HasK3nn H n := by
  have key : ∀ κ : Cardinal.{u}, ∀ (W : Type u) (H : Hypergraph W),
      #W = κ → H.IsTripleSystem → H.UncountablyChromatic → HasK3nn H n := by
    refine fun κ => Cardinal.lt_wf.induction
      (C := fun κ => ∀ (W : Type u) (H : Hypergraph W),
        #W = κ → H.IsTripleSystem → H.UncountablyChromatic → HasK3nn H n) κ ?_
    intro κ IH W H hcard hts huc
    by_contra hfree
    have hbig : ℵ₀ < #W := by
      by_contra hle
      exact huc (tripleSystem_colorable_of_le_aleph0 H hts (not_lt.mp hle))
    refine hasK3nn_step H hts n hbig huc hfree (fun W' H' hlt hts' hfree' => ?_)
    by_contra hcc'
    exact hfree' (IH (#W') (hcard ▸ hlt) W' H' rfl hts' hcc')
  exact key (#W) W H rfl hts huc

open Classical in

theorem e4_Reiher : E4_Reiher.{u} := by
  intro n W H hts huc
  exact hasK3nn_embeds H n (hasK3nn_of_uncountable H hts huc n)

end Erdos593
end

-- E4Discharged
section
open Cardinal

namespace Erdos593

universe u

theorem reiherExpansion_proved : ReiherExpansion.{u} :=
  reiherExpansion_of_E4 e4_Reiher

theorem classification_no_E4 (h3 : E3_EGH_P.{u}) (hE2 : E2_EH_oddgirth.{u}) (F : FTS) :
    (FTS.Obligatory.{u} F ↔ Bclass F) ∧ (Bclass F ↔ F.reduce.IntrinsicObligatory) :=
  classification_final e4_Reiher h3 hE2 F

theorem obligatory_iff_bclass_no_E4 (h3 : E3_EGH_P.{u}) (hE2 : E2_EH_oddgirth.{u})
    (F : FTS) : FTS.Obligatory.{u} F ↔ Bclass F :=
  obligatory_iff_bclass_final e4_Reiher h3 hE2 F

theorem spectrum_dichotomy_no_E4 (h3 : E3_EGH_P.{u}) (hE2 : E2_EH_oddgirth.{u})
    (F : FTS) (lam : Cardinal.{u}) :
    F.InSpec lam ↔ (¬ Bclass F ∧ ℵ₀ < lam) :=
  spectrum_dichotomy_final e4_Reiher h3 hE2 F lam

theorem problem_1177_part3_no_E4 (h3 : E3_EGH_P.{u}) (hE2 : E2_EH_oddgirth.{u})
    (G : FTS) (kappa : Cardinal.{u}) (hk : ℵ₀ < kappa) (h : G.FGnonempty kappa)
    (lam : Cardinal.{u}) (hlam : ℵ₀ < lam) :
    G.FGnonempty lam :=
  problem_1177_part3_final e4_Reiher h3 hE2 G kappa hk h lam hlam

theorem problem_1177_part2_no_E4 (h3 : E3_EGH_P.{u}) (hE2 : E2_EH_oddgirth.{u})
    (hE5 : E5_HK_loose7.{u}) :
    ∃ (G H : FTS),
      G.FGnonempty (Order.succ (ℵ₀ : Cardinal.{u})) ∧
      H.FGnonempty (Order.succ (ℵ₀ : Cardinal.{u})) ∧
      ¬ ∃ (W : Type u) (K : Hypergraph W),
          K.IsTripleSystem ∧ K.HasChromatic (Order.succ (ℵ₀ : Cardinal.{u})) ∧
          ¬ G.Embeds K ∧ ¬ H.Embeds K :=
  problem_1177_part2_final e4_Reiher h3 hE2 hE5

theorem obligatory_stronglyTripartite_no_E4 (h3 : E3_EGH_P.{u})
    (hE2 : E2_EH_oddgirth.{u}) (F : FTS) (hobl : FTS.Obligatory.{u} F) :
    F.StronglyTripartite :=
  obligatory_stronglyTripartite_final e4_Reiher h3 hE2 F hobl

theorem forest_obligatory_no_E4 {F : FTS} (h : F.Forest) : FTS.Obligatory.{u} F :=
  forest_obligatory_final e4_Reiher h

theorem cycleExpansion_obligatory_iff_no_E4 (h3 : E3_EGH_P.{u})
    (hE2 : E2_EH_oddgirth.{u}) (n : ℕ) (hn : 3 ≤ n) :
    FTS.Obligatory.{u} (graphExpansion (SimpleGraph.cycleGraph n)) ↔ Even n :=
  cycleExpansion_obligatory_iff_final e4_Reiher h3 hE2 n hn

theorem C7_linearlyObligatory_not_obligatory_no_E4 (h3 : E3_EGH_P.{u})
    (hE2 : E2_EH_oddgirth.{u}) (hE5 : E5_HK_loose7.{u}) :
    FTS.LinearlyObligatory.{u} looseCycle7 ∧ ¬ FTS.Obligatory.{u} looseCycle7 :=
  C7_linearlyObligatory_not_obligatory_final e4_Reiher h3 hE2 hE5

end Erdos593
end

-- E3Facts
section
open Cardinal Ordinal

namespace Erdos593

variable {ρ : Cardinal.{u}}

theorem lt_pow_deltaRho (hρ : ℵ₀ ≤ ρ) : ρ < ρ ^ (deltaRho ρ) := by
  have hne : ({δ | ρ < ρ ^ δ} : Set Cardinal).Nonempty := ⟨ρ, deltaRho_mem hρ⟩
  have hmem := csInf_mem hne
  simpa [deltaRho] using hmem

theorem deltaRho_pow_le {θ : Cardinal} (hθ : θ < deltaRho ρ) :
    ρ ^ θ ≤ ρ := by
  by_contra h
  push_neg at h
  have : deltaRho ρ ≤ θ := csInf_le (OrderBot.bddBelow _) h
  exact absurd hθ (not_lt.mpr this)

theorem aleph0_le_deltaRho (hρ : ℵ₀ ≤ ρ) : ℵ₀ ≤ deltaRho ρ := by
  rw [deltaRho]
  refine le_csInf ⟨ρ, deltaRho_mem hρ⟩ ?_
  intro d hd
  by_contra h
  push_neg at h
  exact absurd (Cardinal.pow_le hρ h) (not_le.mpr hd)

theorem deltaRho_le_cof (hρ : ℵ₀ ≤ ρ) : deltaRho ρ ≤ (ρ.ord).cof := by
  have : (ρ.ord).cof ∈ {δ | ρ < ρ ^ δ} := Cardinal.lt_power_cof hρ
  exact csInf_le (OrderBot.bddBelow _) this

theorem deltaRho_le (hρ : ℵ₀ ≤ ρ) : deltaRho ρ ≤ ρ :=
  le_trans (deltaRho_le_cof hρ) (Ordinal.cof_ord_le ρ)

theorem deltaRho_regular (hρ : ℵ₀ ≤ ρ) : (deltaRho ρ).ord.cof = deltaRho ρ := by
  set δ := deltaRho ρ with hδdef
  haveI hwo : IsWellOrder δ.ord.ToType (· < ·) := inferInstance
  refine le_antisymm (Ordinal.cof_ord_le δ) ?_
  by_contra hcon
  push_neg at hcon
  have hδinf : ℵ₀ ≤ δ := aleph0_le_deltaRho hρ
  have hIioLt : ∀ s : δ.ord.ToType, #(Set.Iio s) < δ := by
    intro s
    simpa using Cardinal.mk_Iio_lt s (by simp)
  have hIicLt : ∀ s : δ.ord.ToType, #(Set.Iic s) < δ := by
    intro s
    have hu : (Set.Iic s : Set δ.ord.ToType) = (Set.Iio s ∪ {s} : Set δ.ord.ToType) := by
      ext x; simp [le_iff_lt_or_eq]
    rw [hu]
    calc #((Set.Iio s ∪ {s} : Set δ.ord.ToType)) ≤ #(Set.Iio s) + #({s} : Set δ.ord.ToType) :=
            Cardinal.mk_union_le _ _
      _ = #(Set.Iio s) + 1 := by rw [Cardinal.mk_singleton]
      _ < δ := Cardinal.add_lt_of_lt hδinf (hIioLt s) (lt_of_lt_of_le one_lt_aleph0 hδinf)
  obtain ⟨S, hSub, hScard⟩ := Order.exists_cof_eq δ.ord.ToType
  rw [Ordinal.cof_toType] at hScard
  have hScardδ : #S < δ := by rw [hScard]; exact hcon
  have hcover : (⋃ (s : S), Set.Iic (s : δ.ord.ToType)) = (Set.univ : Set δ.ord.ToType) := by
    ext x; simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_univ, iff_true]
    obtain ⟨s, hs, hxs⟩ := hSub x
    exact ⟨⟨s, hs⟩, hxs⟩
  have hδcard : #(δ.ord.ToType) = δ := by rw [Cardinal.mk_toType, Cardinal.card_ord]
  have hle : δ ≤ Cardinal.sum (fun s : S => #(Set.Iic (s : δ.ord.ToType))) := by
    calc δ = #(δ.ord.ToType) := hδcard.symm
      _ = #(⋃ (s : S), Set.Iic (s : δ.ord.ToType)) := by rw [hcover, Cardinal.mk_univ]
      _ ≤ Cardinal.sum (fun s : S => #(Set.Iic (s : δ.ord.ToType))) := Cardinal.mk_iUnion_le_sum_mk
  have hpow : ρ ^ δ ≤ ρ := by
    calc ρ ^ δ ≤ ρ ^ (Cardinal.sum (fun s : S => #(Set.Iic (s : δ.ord.ToType)))) :=
          Cardinal.power_le_power_left ((lt_of_lt_of_le Cardinal.aleph0_pos hρ).ne') hle
      _ = Cardinal.prod (fun s : S => ρ ^ #(Set.Iic (s : δ.ord.ToType))) := Cardinal.power_sum ..
      _ ≤ Cardinal.prod (fun _ : S => ρ) :=
          Cardinal.prod_le_prod _ _ (fun s => deltaRho_pow_le (hIicLt s))
      _ = ρ ^ #S := by rw [Cardinal.prod_const, Cardinal.lift_id, Cardinal.lift_id]
      _ ≤ ρ := deltaRho_pow_le hScardδ
  exact absurd (lt_pow_deltaRho hρ) (not_lt.mpr hpow)

theorem deltaRho_isRegular (hρ : ℵ₀ ≤ ρ) : (deltaRho ρ).IsRegular :=
  ⟨aleph0_le_deltaRho hρ, (deltaRho_regular hρ).symm.le⟩

end Erdos593
end

-- E3Proof
section
open Cardinal Ordinal Classical

namespace Erdos593
namespace E3

noncomputable section

variable (ρ : Cardinal.{u})

abbrev Lv : Type u := (deltaRho ρ).ord.ToType

abbrev Vx : Type u := Lv ρ × ρ.out

def lvl : Vx ρ → Lv ρ := Prod.fst

def IsTypeAt (ξ : Lv ρ) (t : Vx ρ → Option ρ.out) : Prop :=
  (∀ w, (t w).isSome → lvl ρ w < ξ) ∧ #({w | (t w).isSome}) < deltaRho ρ

def Types (ξ : Lv ρ) : Type u := {t : Vx ρ → Option ρ.out // IsTypeAt ρ ξ t}

theorem mk_Lv : #(Lv ρ) = deltaRho ρ := by
  rw [Lv, Cardinal.mk_toType, Cardinal.card_ord]

theorem mk_level (ξ : Lv ρ) : #({x : Vx ρ // lvl ρ x = ξ}) = ρ := by
  have e : {x : Vx ρ // lvl ρ x = ξ} ≃ ρ.out := by
    refine ⟨fun x => x.1.2, fun r => ⟨(ξ, r), rfl⟩, ?_, ?_⟩
    · rintro ⟨⟨a, b⟩, h⟩; simp only [lvl] at h; subst h; rfl
    · intro r; rfl
  rw [Cardinal.mk_congr e, Cardinal.mk_out]

theorem mk_Vx (hρ : ℵ₀ ≤ ρ) : #(Vx ρ) = ρ := by
  rw [Vx, Cardinal.mk_prod, Cardinal.mk_out, Cardinal.lift_id, Cardinal.lift_id, mk_Lv]
  exact Cardinal.mul_eq_right hρ (deltaRho_le hρ)
    ((lt_of_lt_of_le Cardinal.aleph0_pos (aleph0_le_deltaRho hρ)).ne')

theorem mk_below_le (hρ : ℵ₀ ≤ ρ) (ξ : Lv ρ) :
    #({w : Vx ρ // lvl ρ w < ξ}) ≤ ρ :=
  le_trans (Cardinal.mk_subtype_le _) (le_of_eq (mk_Vx ρ hρ))

theorem mk_small_subsets_le (hρ : ℵ₀ ≤ ρ) {α : Type u} (hα : #α ≤ ρ) :
    #({S : Set α | #S < deltaRho ρ}) ≤ ρ := by
  haveI hwo : IsWellOrder (deltaRho ρ).ord.ToType (· < ·) := inferInstance
  set δ := deltaRho ρ with hδ
  set f : δ.ord.ToType → Set (Set α) :=
    fun o => {S : Set α | #S ≤ ((Ordinal.typein (r := (· < ·)) ).toRelEmbedding o).card} with hf
  have hcover : {S : Set α | #S < δ} ⊆ ⋃ (o : δ.ord.ToType), f o := by
    intro S hS
    simp only [Set.mem_setOf_eq] at hS
    rw [Set.mem_iUnion]
    have hlt' : (#S).ord < Ordinal.type (α := δ.ord.ToType) (· < ·) := by
      rw [Ordinal.type_toType]; exact (Cardinal.ord_lt_ord).mpr hS
    refine ⟨Ordinal.enum (· < ·) ⟨(#S).ord, hlt'⟩, ?_⟩
    rw [hf]; simp only [Set.mem_setOf_eq]
    rw [Ordinal.typein_enum, Cardinal.card_ord]
  have hterm : ∀ o : δ.ord.ToType, #(f o) ≤ ρ := by
    intro o
    have hc : ((Ordinal.typein (r := (· < ·)) ).toRelEmbedding o).card < δ :=
      Cardinal.lt_ord.mp (Ordinal.typein_lt_self (o := δ.ord) o)
    calc #(f o) ≤ max #α ℵ₀ ^ ((Ordinal.typein (r := (· < ·)) ).toRelEmbedding o).card :=
          Cardinal.mk_bounded_set_le α _
      _ ≤ ρ ^ ((Ordinal.typein (r := (· < ·)) ).toRelEmbedding o).card :=
          Cardinal.power_le_power_right (max_le hα hρ)
      _ ≤ ρ := deltaRho_pow_le hc
  calc #({S : Set α | #S < δ}) ≤ #(⋃ (o : δ.ord.ToType), f o) :=
        Cardinal.mk_le_mk_of_subset hcover
    _ ≤ Cardinal.sum (fun o => #(f o)) := Cardinal.mk_iUnion_le_sum_mk
    _ ≤ Cardinal.sum (fun _ : δ.ord.ToType => ρ) := Cardinal.sum_le_sum _ _ hterm
    _ = #(δ.ord.ToType) * ρ := by rw [Cardinal.sum_const, Cardinal.lift_id, Cardinal.lift_id]
    _ = δ * ρ := by rw [Cardinal.mk_toType, Cardinal.card_ord]
    _ = ρ := Cardinal.mul_eq_right hρ (deltaRho_le hρ)
              ((lt_of_lt_of_le Cardinal.aleph0_pos (aleph0_le_deltaRho hρ)).ne')

theorem types_card_le (hρ : ℵ₀ ≤ ρ) (ξ : Lv ρ) : #(Types ρ ξ) ≤ ρ := by
  classical
  set δ := deltaRho ρ with hδ
  set W : Set (Vx ρ) := {w | lvl ρ w < ξ} with hW
  set Idx := {S : Set (Vx ρ) // #S < δ ∧ S ⊆ W} with hIdx
  have hsurj : Function.Surjective
      (fun p : (Σ S : Idx, (↥S.1 → ρ.out)) =>
        (⟨fun w => if h : w ∈ p.1.1 then some (p.2 ⟨w, h⟩) else none, by
            refine ⟨?_, ?_⟩
            · intro w hw
              by_cases h : w ∈ p.1.1
              · exact p.1.2.2 h
              · simp [h] at hw
            · apply lt_of_le_of_lt _ p.1.2.1
              apply Cardinal.mk_le_mk_of_subset
              intro w hw
              by_cases h : w ∈ p.1.1
              · exact h
              · simp [h] at hw⟩ : Types ρ ξ)) := by
    intro t
    refine ⟨⟨⟨{w | (t.1 w).isSome}, ⟨t.2.2, fun w hw => t.2.1 w hw⟩⟩,
      fun w => (t.1 w.1).get w.2⟩, ?_⟩
    apply Subtype.ext
    funext w
    by_cases h : (t.1 w).isSome
    · simp only [Set.mem_setOf_eq, h, dif_pos]
      exact Option.some_get h
    · simp only [Set.mem_setOf_eq, h]
      exact (Option.not_isSome_iff_eq_none.mp h).symm
  calc #(Types ρ ξ) ≤ #(Σ S : Idx, (↥S.1 → ρ.out)) := Cardinal.mk_le_of_surjective hsurj
    _ = Cardinal.sum (fun S : Idx => #(↥S.1 → ρ.out)) := Cardinal.mk_sigma _
    _ ≤ Cardinal.sum (fun _ : Idx => ρ) := by
        apply Cardinal.sum_le_sum
        intro S
        rw [Cardinal.mk_arrow, Cardinal.mk_out, Cardinal.lift_id, Cardinal.lift_id]
        exact deltaRho_pow_le S.2.1
    _ = #Idx * ρ := by rw [Cardinal.sum_const, Cardinal.lift_id, Cardinal.lift_id]
    _ ≤ ρ * ρ := by
        gcongr
        refine le_trans (Cardinal.mk_subtype_mono (fun S (h : #S < δ ∧ S ⊆ W) => h.1)) ?_
        exact mk_small_subsets_le ρ hρ (le_of_eq (mk_Vx ρ hρ))
    _ = ρ := Cardinal.mul_eq_self hρ

theorem types_nonempty (hρ : ℵ₀ ≤ ρ) (ξ : Lv ρ) : Nonempty (Types ρ ξ) :=
  ⟨⟨fun _ => none, by
    refine ⟨?_, ?_⟩
    · intro w h; simp at h
    · have : ({w | (Option.none : Option ρ.out).isSome}) = (∅ : Set (Vx ρ)) := by
        ext w; simp
      rw [this]
      simpa using lt_of_lt_of_le Cardinal.aleph0_pos (aleph0_le_deltaRho hρ)⟩⟩

theorem out_nonempty (hρ : ℵ₀ ≤ ρ) : Nonempty ρ.out := by
  rw [← Cardinal.mk_ne_zero_iff, Cardinal.mk_out]
  exact (lt_of_lt_of_le Cardinal.aleph0_pos hρ).ne'

theorem fiber_partition {B : Type u} (hB1 : Nonempty B) (hB : #B ≤ ρ) (hρ : ℵ₀ ≤ ρ) :
    ∃ s : ρ.out → B, ∀ b : B, #({a : ρ.out // s a = b}) = ρ := by
  have hBne : #B ≠ 0 := by rw [Cardinal.mk_ne_zero_iff]; exact hB1
  have hmul : #(B × ρ.out) = ρ := by
    rw [Cardinal.mk_prod, Cardinal.mk_out, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.mul_eq_right hρ hB hBne
  obtain ⟨e⟩ : Nonempty (ρ.out ≃ B × ρ.out) := by
    rw [← Cardinal.eq, Cardinal.mk_out, hmul]
  refine ⟨fun a => (e a).1, fun b => ?_⟩
  have e2 : {a : ρ.out // (e a).1 = b} ≃ {p : B × ρ.out // p.1 = b} :=
    Equiv.subtypeEquiv e (fun a => Iff.rfl)
  rw [Cardinal.mk_congr e2]
  have e3 : {p : B × ρ.out // p.1 = b} ≃ ρ.out := by
    refine ⟨fun p => p.1.2, fun r => ⟨(b, r), rfl⟩, ?_, ?_⟩
    · rintro ⟨⟨x, y⟩, h⟩; simp only at h; subst h; rfl
    · intro r; rfl
  rw [Cardinal.mk_congr e3, Cardinal.mk_out]

def chosenSurj (hρ : ℵ₀ ≤ ρ) (ξ : Lv ρ) : ρ.out → Types ρ ξ :=
  Classical.choose (fiber_partition ρ (types_nonempty ρ hρ ξ) (types_card_le ρ hρ ξ) hρ)

theorem chosenSurj_fiber (hρ : ℵ₀ ≤ ρ) (ξ : Lv ρ) (t : Types ρ ξ) :
    #({r : ρ.out // chosenSurj ρ hρ ξ r = t}) = ρ :=
  Classical.choose_spec (fiber_partition ρ (types_nonempty ρ hρ ξ) (types_card_le ρ hρ ξ) hρ) t

def typeOf (hρ : ℵ₀ ≤ ρ) (v : Vx ρ) : Vx ρ → Option ρ.out :=
  (chosenSurj ρ hρ (lvl ρ v) v.2).1

theorem typeOf_supp (hρ : ℵ₀ ≤ ρ) (v w : Vx ρ) (h : (typeOf ρ hρ v w).isSome) :
    lvl ρ w < lvl ρ v :=
  (chosenSurj ρ hρ (lvl ρ v) v.2).2.1 w h

theorem not_both_some (hρ : ℵ₀ ≤ ρ) (u w : Vx ρ) :
    ¬ ((typeOf ρ hρ u w).isSome ∧ (typeOf ρ hρ w u).isSome) := by
  rintro ⟨h1, h2⟩
  exact absurd (typeOf_supp ρ hρ u w h1) (not_lt.mpr (le_of_lt (typeOf_supp ρ hρ w u h2)))

theorem realize (hρ : ℵ₀ ≤ ρ) (ξ : Lv ρ) (t : Types ρ ξ) :
    #({x : Vx ρ // lvl ρ x = ξ ∧ ∀ w, typeOf ρ hρ x w = t.1 w}) = ρ := by
  refine Eq.trans (Cardinal.mk_congr ?_) (chosenSurj_fiber ρ hρ ξ t)
  refine ⟨fun x => ⟨x.1.2, ?_⟩, fun r => ⟨(ξ, r.1), rfl, ?_⟩, ?_, ?_⟩
  · obtain ⟨⟨a, b⟩, hlv, hfun⟩ := x
    simp only [lvl] at hlv; subst hlv
    apply Subtype.ext; funext w; exact hfun w
  · obtain ⟨b, hb⟩ := r
    intro w
    show typeOf ρ hρ (ξ, b) w = t.1 w
    have h1 : typeOf ρ hρ (ξ, b) = (chosenSurj ρ hρ ξ b).1 := rfl
    rw [h1, hb]
  · rintro ⟨⟨a, b⟩, hlv, hfun⟩
    simp only [lvl] at hlv; subst hlv; rfl
  · rintro ⟨b, hb⟩; rfl

def Grel (hρ : ℵ₀ ≤ ρ) (u w : Vx ρ) : Prop :=
  (typeOf ρ hρ u w).isSome ∨ (typeOf ρ hρ w u).isSome

theorem Grel_symm (hρ : ℵ₀ ≤ ρ) : Symmetric (Grel ρ hρ) := by
  intro u w h; exact h.symm

theorem Grel_irrefl (hρ : ℵ₀ ≤ ρ) : ∀ v, ¬ Grel ρ hρ v v := by
  intro v h
  rcases h with h | h <;> exact (lt_irrefl _ (typeOf_supp ρ hρ v v h))

def G (hρ : ℵ₀ ≤ ρ) : SimpleGraph (Vx ρ) :=
  { Adj := Grel ρ hρ, symm := ⟨fun _ _ h => Grel_symm ρ hρ h⟩, loopless := ⟨Grel_irrefl ρ hρ⟩ }

def labPair (hρ : ℵ₀ ≤ ρ) (u w : Vx ρ) : ρ.out :=
  haveI : Nonempty ρ.out := out_nonempty ρ hρ
  (typeOf ρ hρ u w).getD ((typeOf ρ hρ w u).getD (Classical.arbitrary ρ.out))

theorem labPair_symm (hρ : ℵ₀ ≤ ρ) (u w : Vx ρ) :
    labPair ρ hρ u w = labPair ρ hρ w u := by
  have hnb := not_both_some ρ hρ u w
  unfold labPair
  cases hu : typeOf ρ hρ u w <;> cases hw : typeOf ρ hρ w u <;>
    simp_all [Option.isSome]

def edgeLabel (hρ : ℵ₀ ≤ ρ) : (G ρ hρ).edgeSet → ρ.out :=
  fun e => Sym2.lift ⟨labPair ρ hρ, labPair_symm ρ hρ⟩ e.1

theorem edgeLabel_eq (hρ : ℵ₀ ≤ ρ) (x y : Vx ρ) (h : (G ρ hρ).Adj x y) :
    edgeLabel ρ hρ ⟨s(x, y), h⟩ = labPair ρ hρ x y := by
  simp [edgeLabel, Sym2.lift_mk]

theorem labPair_of_some (hρ : ℵ₀ ≤ ρ) (x y : Vx ρ) (l : ρ.out)
    (h : typeOf ρ hρ x y = some l) : labPair ρ hρ x y = l := by
  simp [labPair, h]

theorem exists_ub_Lv (hρ : ℵ₀ ≤ ρ) (S : Set (Lv ρ)) (hS : #S < deltaRho ρ) :
    ∃ ξ : Lv ρ, ∀ b ∈ S, b < ξ := by
  have hcof : Order.cof (Lv ρ) = deltaRho ρ := by
    rw [Ordinal.cof_toType]
    exact deltaRho_regular hρ
  by_contra hcon
  have hcf : IsCofinal S := by
    intro x
    by_contra hx
    apply hcon
    refine ⟨x, fun b hb => ?_⟩
    by_contra hbx
    exact hx ⟨b, hb, not_lt.mp hbx⟩
  have := Order.cof_le hcf
  rw [hcof] at this
  exact absurd hS (not_lt.mpr this)

theorem small_union_lt_rho {ι α : Type u} (hρ : ℵ₀ ≤ ρ) (hι : #ι < (ρ.ord).cof)
    (t : ι → Set α) (ht : ∀ i, #(t i) < ρ) : #(⋃ i, t i) < ρ := by
  have hsup : ⨆ i, #(t i) < ρ := Ordinal.iSup_lt hι ht
  have hιρ : #ι < ρ := lt_of_lt_of_le hι (Ordinal.cof_ord_le ρ)
  calc #(⋃ i, t i) ≤ Cardinal.sum (fun i => #(t i)) := Cardinal.mk_iUnion_le_sum_mk
    _ ≤ #ι * ⨆ i, #(t i) := Cardinal.sum_le_mk_mul_iSup _
    _ < ρ := Cardinal.mul_lt_of_lt hρ hιρ hsup

theorem propertyP (hρ : ℵ₀ ≤ ρ) :
    SimpleGraph.PropertyP (G ρ hρ) (edgeLabel ρ hρ) (deltaRho ρ) := by
  classical
  intro θ hθ c
  by_contra hcon
  push_neg at hcon
  choose q hq using hcon
  haveI hLvne : Nonempty (Lv ρ) := by
    have hpos : (0:Cardinal) < deltaRho ρ :=
      lt_of_lt_of_le Cardinal.aleph0_pos (aleph0_le_deltaRho hρ)
    exact Ordinal.toType_nonempty_iff_ne_zero.mpr (fun hh => hpos.ne' (Cardinal.ord_eq_zero.mp hh))
  haveI hρne : Nonempty ρ.out := out_nonempty ρ hρ
  set full : θ.out → Lv ρ → Prop :=
    fun a ξ => ρ ≤ #{x : Vx ρ // lvl ρ x = ξ ∧ c x = a} with hfulldef
  set isM : θ.out → Prop := fun a => #({ξ : Lv ρ | full a ξ}) < deltaRho ρ with hisMdef
  have hθδ : #(θ.out) < deltaRho ρ := by rw [Cardinal.mk_out]; exact hθ
  have hθcof : #(θ.out) < (ρ.ord).cof := lt_of_lt_of_le hθδ (deltaRho_le_cof hρ)
  have hyy : ∀ a : θ.out, ¬ isM a → ∃ w : Vx ρ, c w = a ∧ full a (lvl ρ w) := by
    intro a ha
    rw [hisMdef] at ha; simp only [not_lt] at ha
    have hFne : Nonempty {ξ : Lv ρ // ξ ∈ {ξ | full a ξ}} := by
      rw [← Cardinal.mk_ne_zero_iff]
      have h0 : (0:Cardinal) < deltaRho ρ :=
        lt_of_lt_of_le Cardinal.aleph0_pos (aleph0_le_deltaRho hρ)
      exact (lt_of_lt_of_le h0 ha).ne'
    obtain ⟨⟨ξ, hξ⟩⟩ := hFne
    simp only [Set.mem_setOf_eq] at hξ
    rw [hfulldef] at hξ
    have hxne : Nonempty {x : Vx ρ // lvl ρ x = ξ ∧ c x = a} := by
      rw [← Cardinal.mk_ne_zero_iff]
      have h0 : (0:Cardinal) < ρ := lt_of_lt_of_le Cardinal.aleph0_pos hρ
      exact (lt_of_lt_of_le h0 hξ).ne'
    obtain ⟨⟨x, hx1, hx2⟩⟩ := hxne
    exact ⟨x, hx2, by rw [hfulldef, hx1]; exact hξ⟩
  set yy : θ.out → Vx ρ := fun a =>
    if h : ¬ isM a then (hyy a h).choose else Classical.arbitrary _ with hyydef
  have hyy_spec : ∀ a, ¬ isM a → c (yy a) = a ∧ full a (lvl ρ (yy a)) := by
    intro a ha
    have he : yy a = (hyy a ha).choose := by rw [hyydef]; simp [ha]
    rw [he]; exact (hyy a ha).choose_spec
  set t : Vx ρ → Option ρ.out :=
    fun w => if (¬ isM (c w) ∧ yy (c w) = w) then some (q (c w)) else none with htdef
  have ht_some_iff : ∀ w, (t w).isSome ↔ (¬ isM (c w) ∧ yy (c w) = w) := by
    intro w; rw [htdef]; by_cases h : (¬ isM (c w) ∧ yy (c w) = w) <;> simp [h]
  have hsupp_inj : #({w : Vx ρ | (t w).isSome}) < deltaRho ρ := by
    apply lt_of_le_of_lt _ hθδ
    apply Cardinal.mk_le_of_injective (f := fun w : {w : Vx ρ // (t w).isSome} => c w.1)
    rintro ⟨w, hw⟩ ⟨w', hw'⟩ hcc
    simp only at hcc
    rw [ht_some_iff] at hw hw'
    have hww : w = w' := by rw [← hw.2, ← hw'.2, hcc]
    exact Subtype.ext hww
  set Bad : Set (Lv ρ) :=
    {ξ | (∃ a, ¬ isM a ∧ lvl ρ (yy a) = ξ) ∨ (∃ a, isM a ∧ full a ξ)} with hBaddef
  have hBadlt : #Bad < deltaRho ρ := by
    have hP1 : #({ξ : Lv ρ | ∃ a, ¬ isM a ∧ lvl ρ (yy a) = ξ}) < deltaRho ρ := by
      have hsub : {ξ : Lv ρ | ∃ a, ¬ isM a ∧ lvl ρ (yy a) = ξ} ⊆
          Set.range (fun a : θ.out => lvl ρ (yy a)) := by
        rintro ξ ⟨a, _, heq⟩; exact ⟨a, heq⟩
      exact lt_of_le_of_lt (le_trans (Cardinal.mk_le_mk_of_subset hsub)
        (le_trans Cardinal.mk_range_le (le_of_eq (Cardinal.mk_out θ)))) hθ
    have hP2 : #({ξ : Lv ρ | ∃ a, isM a ∧ full a ξ}) < deltaRho ρ := by
      have hEq : {ξ : Lv ρ | ∃ a, isM a ∧ full a ξ}
          = ⋃ (a : {a : θ.out // isM a}), {ξ | full a.1 ξ} := by
        ext ξ; simp only [Set.mem_setOf_eq, Set.mem_iUnion]
        constructor
        · rintro ⟨a, hM, hf⟩; exact ⟨⟨a, hM⟩, hf⟩
        · rintro ⟨⟨a, hM⟩, hf⟩; exact ⟨a, hM, hf⟩
      rw [hEq, card_iUnion_lt_iff_forall_of_isRegular (deltaRho_isRegular hρ)
        (lt_of_le_of_lt (Cardinal.mk_subtype_le _) hθδ)]
      rintro ⟨a, hM⟩; exact hM
    have hsub : Bad ⊆ {ξ : Lv ρ | ∃ a, ¬ isM a ∧ lvl ρ (yy a) = ξ} ∪
        {ξ : Lv ρ | ∃ a, isM a ∧ full a ξ} := by
      rw [hBaddef]; intro ξ h; rcases h with h | h
      · exact Or.inl h
      · exact Or.inr h
    exact lt_of_le_of_lt (le_trans (Cardinal.mk_le_mk_of_subset hsub) (Cardinal.mk_union_le _ _))
      (Cardinal.add_lt_of_lt (aleph0_le_deltaRho hρ) hP1 hP2)
  obtain ⟨ξstar, hξstar⟩ := exists_ub_Lv ρ hρ Bad hBadlt
  have hsupp_below : ∀ w, (t w).isSome → lvl ρ w < ξstar := by
    intro w hw
    rw [ht_some_iff] at hw
    obtain ⟨hnM, hyw⟩ := hw
    have hin : lvl ρ (yy (c w)) ∈ Bad := by rw [hBaddef]; left; exact ⟨c w, hnM, rfl⟩
    have := hξstar _ hin
    rwa [hyw] at this
  have htype : IsTypeAt ρ ξstar t := ⟨hsupp_below, hsupp_inj⟩
  have hD : #({x : Vx ρ // lvl ρ x = ξstar ∧ ∀ w, typeOf ρ hρ x w = t w}) = ρ :=
    realize ρ hρ ξstar ⟨t, htype⟩
  have hDcard : #({x : Vx ρ | lvl ρ x = ξstar ∧ ∀ w, typeOf ρ hρ x w = t w}) = ρ := hD
  have hMpart :
      #({x : Vx ρ | (lvl ρ x = ξstar ∧ ∀ w, typeOf ρ hρ x w = t w) ∧ isM (c x)}) < ρ := by
    apply lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset
      (t := ⋃ (a : {a : θ.out // isM a}), {x : Vx ρ | lvl ρ x = ξstar ∧ c x = a.1}) ?_)
      (small_union_lt_rho ρ hρ ?_ _ ?_)
    · rintro x ⟨⟨hlv, _⟩, hM⟩
      rw [Set.mem_iUnion]; exact ⟨⟨c x, hM⟩, hlv, rfl⟩
    · exact lt_of_le_of_lt (Cardinal.mk_subtype_le _) hθcof
    · rintro ⟨a, hM⟩
      have hnfull : ¬ full a ξstar := by
        intro hf
        exact absurd (hξstar ξstar (by rw [hBaddef]; right; exact ⟨a, hM, hf⟩)) (lt_irrefl _)
      rw [hfulldef] at hnfull; simp only [not_le] at hnfull
      exact hnfull
  have hexists : ∃ x, (lvl ρ x = ξstar ∧ ∀ w, typeOf ρ hρ x w = t w) ∧ ¬ isM (c x) := by
    by_contra hall
    push_neg at hall
    have hsub : {x : Vx ρ | lvl ρ x = ξstar ∧ ∀ w, typeOf ρ hρ x w = t w} ⊆
        {x : Vx ρ | (lvl ρ x = ξstar ∧ ∀ w, typeOf ρ hρ x w = t w) ∧ isM (c x)} :=
      fun x hx => ⟨hx, hall x hx⟩
    have hle := Cardinal.mk_le_mk_of_subset hsub
    rw [hDcard] at hle
    exact absurd (lt_of_le_of_lt hle hMpart) (lt_irrefl _)
  obtain ⟨x, ⟨hxlv, hxtype⟩, hxnM⟩ := hexists
  have hyya' := hyy_spec (c x) hxnM
  have htval : t (yy (c x)) = some (q (c x)) := by
    have h1 : c (yy (c x)) = c x := hyya'.1
    have hbeta : t (yy (c x))
        = if (¬ isM (c (yy (c x))) ∧ yy (c (yy (c x))) = yy (c x))
          then some (q (c (yy (c x)))) else none := rfl
    rw [hbeta, if_pos ⟨by rw [h1]; exact hxnM, by rw [h1]⟩, h1]
  have htypeof : typeOf ρ hρ x (yy (c x)) = some (q (c x)) := by rw [hxtype, htval]
  have hadj : (G ρ hρ).Adj x (yy (c x)) := by
    show Grel ρ hρ x (yy (c x)); left; rw [htypeof]; rfl
  have hlabel : edgeLabel ρ hρ ⟨s(x, yy (c x)), hadj⟩ = q (c x) := by
    rw [edgeLabel_eq]; exact labPair_of_some ρ hρ x (yy (c x)) (q (c x)) htypeof
  exact hq (c x) x (yy (c x)) hadj hlabel rfl hyya'.1

end

end E3

theorem e3_EGH_P : E3_EGH_P.{u} := by
  intro ρ hρ
  refine ⟨E3.Vx ρ, E3.G ρ hρ, ρ.out, ?_, Cardinal.mk_out ρ, E3.edgeLabel ρ hρ, ?_⟩
  · exact E3.mk_Vx ρ hρ
  · exact E3.propertyP ρ hρ

end Erdos593
end

-- E3Discharged
section
open Cardinal

namespace Erdos593

universe u

theorem classification_no_E34 (hE2 : E2_EH_oddgirth.{u}) (F : FTS) :
    (FTS.Obligatory.{u} F ↔ Bclass F) ∧ (Bclass F ↔ F.reduce.IntrinsicObligatory) :=
  classification_final e4_Reiher e3_EGH_P hE2 F

theorem obligatory_iff_bclass_no_E34 (hE2 : E2_EH_oddgirth.{u}) (F : FTS) :
    FTS.Obligatory.{u} F ↔ Bclass F :=
  obligatory_iff_bclass_final e4_Reiher e3_EGH_P hE2 F

theorem spectrum_dichotomy_no_E34 (hE2 : E2_EH_oddgirth.{u}) (F : FTS)
    (lam : Cardinal.{u}) :
    F.InSpec lam ↔ (¬ Bclass F ∧ ℵ₀ < lam) :=
  spectrum_dichotomy_final e4_Reiher e3_EGH_P hE2 F lam

theorem problem_1177_part3_no_E34 (hE2 : E2_EH_oddgirth.{u})
    (G : FTS) (kappa : Cardinal.{u}) (hk : ℵ₀ < kappa) (h : G.FGnonempty kappa)
    (lam : Cardinal.{u}) (hlam : ℵ₀ < lam) :
    G.FGnonempty lam :=
  problem_1177_part3_final e4_Reiher e3_EGH_P hE2 G kappa hk h lam hlam

theorem problem_1177_part2_no_E34 (hE2 : E2_EH_oddgirth.{u}) (hE5 : E5_HK_loose7.{u}) :
    ∃ (G H : FTS),
      G.FGnonempty (Order.succ (ℵ₀ : Cardinal.{u})) ∧
      H.FGnonempty (Order.succ (ℵ₀ : Cardinal.{u})) ∧
      ¬ ∃ (W : Type u) (K : Hypergraph W),
          K.IsTripleSystem ∧ K.HasChromatic (Order.succ (ℵ₀ : Cardinal.{u})) ∧
          ¬ G.Embeds K ∧ ¬ H.Embeds K :=
  problem_1177_part2_final e4_Reiher e3_EGH_P hE2 hE5

theorem obligatory_stronglyTripartite_no_E34 (hE2 : E2_EH_oddgirth.{u}) (F : FTS)
    (hobl : FTS.Obligatory.{u} F) :
    F.StronglyTripartite :=
  obligatory_stronglyTripartite_final e4_Reiher e3_EGH_P hE2 F hobl

theorem cycleExpansion_obligatory_iff_no_E34 (hE2 : E2_EH_oddgirth.{u}) (n : ℕ)
    (hn : 3 ≤ n) :
    FTS.Obligatory.{u} (graphExpansion (SimpleGraph.cycleGraph n)) ↔ Even n :=
  cycleExpansion_obligatory_iff_final e4_Reiher e3_EGH_P hE2 n hn

theorem C7_linearlyObligatory_not_obligatory_no_E34 (hE2 : E2_EH_oddgirth.{u})
    (hE5 : E5_HK_loose7.{u}) :
    FTS.LinearlyObligatory.{u} looseCycle7 ∧ ¬ FTS.Obligatory.{u} looseCycle7 :=
  C7_linearlyObligatory_not_obligatory_final e4_Reiher e3_EGH_P hE2 hE5

end Erdos593
end

-- E2Construction
section
open Cardinal

namespace Erdos593

universe u

theorem colorableBy_of_mk_eq {V : Type u} (A : SimpleGraph V) {κ : Cardinal.{u}}
    (h : Cardinal.mk V = κ) : (SimpleGraph.toHG A).ColorableBy κ := by
  have e : V ≃ κ.out := by
    apply Cardinal.outMkEquiv.symm.trans
    rw [h]
  refine ⟨e, ?_⟩
  intro edge he
  obtain ⟨x, y, hxy, rfl⟩ := he
  exact ⟨x, by simp, y, by simp, fun hc => (A.ne_of_adj hxy) (e.injective hc)⟩

def E2Core : Prop :=
  ∀ (κ : Cardinal.{u}), ℵ₀ < κ → ∀ (s : ℕ),
    ∃ (W : Type u) (G : SimpleGraph W),
      Cardinal.mk W ≤ κ ∧
      (∀ θ, θ < κ → ¬ (SimpleGraph.toHG G).ColorableBy θ) ∧
      NoShortOddCycle G s

def paddedGraph {W : Type u} (G : SimpleGraph W) (κ : Cardinal.{u}) :
    SimpleGraph (W ⊕ κ.out) where
  Adj a b :=
    match a, b with
    | Sum.inl x, Sum.inl y => G.Adj x y
    | _, _ => False
  symm := ⟨by
    rintro (x | x) (y | y) h <;> simp_all [G.adj_comm]⟩
  loopless := ⟨by rintro (x | x) h <;> simp_all⟩

theorem E2_of_core (h : E2Core.{u}) : E2_EH_oddgirth.{u} := by
  intro κ hκ s;
  obtain ⟨ W, G, hW, hG, hgirth ⟩ := h κ hκ s;
  refine' ⟨ W ⊕ κ.out, paddedGraph G κ, _, _, _ ⟩;
  · simp +decide [ Cardinal.mk_sum, Cardinal.mk_out ];
    exact Cardinal.add_eq_right (le_of_lt hκ) hW;
  · refine' ⟨ _, _ ⟩;
    · convert colorableBy_of_mk_eq ( paddedGraph G κ ) _;
      simp +decide [ Cardinal.mk_sum, Cardinal.mk_out ];
      rw [ Cardinal.add_eq_right ];
      · exact le_of_lt hκ;
      · exact hW;
    · intro θ hθ hcolorable
      obtain ⟨c, hc⟩ := hcolorable
      have hcolorable_G : (SimpleGraph.toHG G).ColorableBy θ := by
        use fun w => c (Sum.inl w);
        intro e he; obtain ⟨ x, y, hxy, rfl ⟩ := he; specialize hc ( { Sum.inl x, Sum.inl y } : Set ( W ⊕ Quotient.out κ ) ) ; simp_all +decide [ SimpleGraph.toHG ] ;
        exact hc <| Or.inl ⟨ x, Or.inl ⟨ y, by simpa [ paddedGraph ] using hxy, by simp +decide [ Set.pair_comm ] ⟩ ⟩
      exact hG θ hθ hcolorable_G;
  · intro m hm₁ hm₂ hm₃ ⟨ v, hv₁, hv₂ ⟩;

    have hvW : ∀ i : ZMod m, ∃ w : W, v i = Sum.inl w := by
      intro i; specialize hv₂ i; rcases v_i : v i with ( _ | _ ) <;> simp_all +decide [ paddedGraph ] ;
    choose w hw using hvW;
    exact hgirth m hm₁ hm₂ hm₃ ⟨ w, fun i j hij => by have := hv₁ ( by aesop : v i = v j ) ; aesop, fun i => by have := hv₂ i; aesop ⟩

theorem completeGraph_not_colorableBy {W : Type u} {κ : Cardinal.{u}}
    (h : Cardinal.mk W = κ) {θ : Cardinal.{u}} (hθ : θ < κ) :
    ¬ (SimpleGraph.toHG (⊤ : SimpleGraph W)).ColorableBy θ := by
  rintro ⟨c, hc⟩
  have hinj : Function.Injective c := by
    intro x y hxy
    by_contra hne
    obtain ⟨u, hu, v, hv, huv⟩ := hc ({x, y} : Set W) ⟨x, y, by simpa using hne, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp_all
  have : κ ≤ θ := by
    rw [← h]
    calc Cardinal.mk W ≤ Cardinal.mk θ.out := Cardinal.mk_le_of_injective hinj
      _ = θ := Cardinal.mk_out θ
  exact absurd this (not_le.mpr hθ)

theorem E2Core_zero (κ : Cardinal.{u}) :
    ∃ (W : Type u) (G : SimpleGraph W),
      Cardinal.mk W ≤ κ ∧
      (∀ θ, θ < κ → ¬ (SimpleGraph.toHG G).ColorableBy θ) ∧
      NoShortOddCycle G 0 := by
  refine ⟨κ.out, ⊤, le_of_eq (Cardinal.mk_out κ), ?_, ?_⟩
  · intro θ hθ
    exact completeGraph_not_colorableBy (Cardinal.mk_out κ) hθ
  ·
    intro m _ hm3 hm1
    omega

end Erdos593
end

-- ErdosHajnalGirth
section
open Cardinal Ordinal

namespace Erdos593
namespace ER60

universe u

abbrev Pt (κ : Cardinal.{u}) : Type u := κ.ord.ToType

abbrev Vtx (κ : Cardinal.{u}) : Type u := {t : Fin 3 → Pt κ // StrictMono t}

variable {κ : Cardinal.{u}}

def IsEdge (a b : Fin 3 → Pt κ) : Prop :=
  a 0 < a 1 ∧ a 1 < b 0 ∧ b 0 < a 2 ∧ a 2 < b 1 ∧ b 1 < b 2

def Adjr (a b : Vtx κ) : Prop := IsEdge a.1 b.1 ∨ IsEdge b.1 a.1

theorem isEdge_irrefl (a : Fin 3 → Pt κ) : ¬ IsEdge a a := by
  rintro ⟨h01, h1, -, -, -⟩
  exact absurd (lt_trans h01 h1) (lt_irrefl _)

def graph (κ : Cardinal.{u}) : SimpleGraph (Vtx κ) where
  Adj a b := Adjr a b
  symm := ⟨by intro a b h; exact h.symm⟩
  loopless := ⟨by rintro a (h | h) <;> exact isEdge_irrefl _ h⟩

theorem card_le (hκ : ℵ₀ ≤ κ) : Cardinal.mk (Vtx κ) ≤ κ := by

  have h_card : #(Fin 3 → Pt κ) = κ ^ (3 : ℕ) := by
    simp +decide [ Cardinal.mk_toType, Cardinal.card_ord ];
    norm_cast;
  refine' le_trans ( Cardinal.mk_subtype_le _ ) _;
  rw [ h_card, Cardinal.power_nat_eq ];
  · exact hκ;
  · norm_num

theorem isEdge_fst_lt {a b : Fin 3 → Pt κ} (h : IsEdge a b) : a 0 < b 0 :=
  lt_trans h.1 h.2.1

theorem triangleFree :
    ∀ a b c : Vtx κ, (graph κ).Adj a b → (graph κ).Adj b c → (graph κ).Adj a c → False := by
  intro a b c hab hbc hac
  simp only [graph, Adjr, IsEdge] at hab hbc hac
  rcases hab with h1 | h1 <;> rcases hbc with h2 | h2 <;> rcases hac with h3 | h3 <;> order

theorem noShortOddCycle_one : NoShortOddCycle (graph κ) 1 := by
  intro m hm₁ hm₂ hm₃;
  interval_cases m ; simp_all +decide;
  intro x hx_inj
  by_contra h_contra
  push_neg at h_contra;
  convert triangleFree _ _ _ ( h_contra 0 ) ( h_contra 1 ) ( h_contra 2 |> SimpleGraph.Adj.symm ) using 1

def Cofinal (S : Set (Pt κ)) : Prop := ∀ x : Pt κ, ∃ y ∈ S, x < y

theorem cofinal_univ (hκ : ℵ₀ ≤ κ) : Cofinal (Set.univ : Set (Pt κ)) := by
  intro x
  obtain ⟨y, hy⟩ : ∃ y : Pt κ, x < y := by
    convert exists_gt x;
    have h_no_max : NoMaxOrder (κ.ord.ToType) := by
      have h_limit : Order.IsSuccLimit κ.ord := by
        apply_rules [ Cardinal.isSuccLimit_ord, hκ ]
      exact Cardinal.noMaxOrder hκ;
    exact h_no_max
  use y
  simp [hy]

theorem cofinal_Ioi (hκ : ℵ₀ ≤ κ) (y : Pt κ) : Cofinal {z | y < z} := by
  intro x
  obtain ⟨z, -, hz⟩ := cofinal_univ hκ (max x y)
  exact ⟨z, lt_of_le_of_lt (le_max_right _ _) hz, lt_of_le_of_lt (le_max_left _ _) hz⟩

theorem exists_ub (hreg : κ.IsRegular) {θ : Cardinal.{u}} (hθ : θ < κ)
    (b : θ.out → Pt κ) : ∃ B : Pt κ, ∀ v, b v < B := by
      obtain ⟨c, hc⟩ : ∃ c : Ordinal, c < κ.ord ∧ ∀ v : Cardinal.ord κ |> Ordinal.ToType, (∃ w : (Quotient.out θ), b w = v) → v < c := by
        use Ordinal.lsub (fun w : (Quotient.out θ) => (b w).toOrd);
        refine' ⟨ _, _ ⟩;
        · convert Ordinal.lsub_lt_ord_lift _ _;
          · simp +decide [ Cardinal.mk_out ];
            exact hθ.trans_le hreg.cof_eq.ge;
          · exact fun w => (b w).toOrd.2;
        · rintro v ⟨ w, rfl ⟩;
          exact Ordinal.lt_lsub ( fun w => ToType.toOrd ( b w ) ) w;
      have h_enum : ∃ w : Ordinal.ToType κ.ord, w.toOrd = c := by
        obtain ⟨w, hw⟩ : ∃ w : Ordinal.ToType κ.ord, w.toOrd = c := by
          have h_enum : ∀ x : Ordinal, x < κ.ord → ∃ w : Ordinal.ToType κ.ord, w.toOrd = x := by
            intro x hx;
            obtain ⟨w, hw⟩ : ∃ w : Ordinal.ToType κ.ord, w.toOrd = x := by
              have h_enum : ∀ x : Ordinal, x < κ.ord → ∃ w : Ordinal.ToType κ.ord, w.toOrd = x := by
                intro x hx
                have h_enum : x < Ordinal.type (· < · : Ordinal.ToType κ.ord → Ordinal.ToType κ.ord → Prop) := by
                  convert hx using 1;
                  convert Ordinal.type_toType κ.ord using 1
                obtain ⟨ w, hw ⟩ := typein_surj ( fun x1 x2 : Ordinal.ToType κ.ord => x1 < x2 ) h_enum; use w; aesop;
              exact h_enum x hx;
            use w
          exact h_enum c hc.1;
        use w;
      cases' h_enum with w hw; use w; intro v; specialize hc; have := hc.2 ( b v ) ⟨ v, rfl ⟩ ; aesop;

theorem cofinal_fiber (hreg : κ.IsRegular) {θ : Cardinal.{u}} (hθ : θ < κ)
    {S : Set (Pt κ)} (hS : Cofinal S) (f : Pt κ → θ.out) :
    ∃ v : θ.out, Cofinal {y | y ∈ S ∧ f y = v} := by
      contrapose! hS; simp_all +decide [ Cofinal ] ;
      choose b hb using hS; have := exists_ub hreg hθ b; obtain ⟨ B, hB ⟩ := this; use B; intros x hx; specialize hb ( f x ) x hx rfl; exact le_trans hb ( le_of_lt ( hB _ ) ) ;

def mk3 (a b c : Pt κ) (h1 : a < b) (h2 : b < c) : Vtx κ :=
  ⟨![a, b, c], by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all +decide [lt_trans h1 h2]⟩

@[simp] theorem mk3_zero (a b c : Pt κ) (h1 : a < b) (h2 : b < c) :
    (mk3 a b c h1 h2).1 0 = a := rfl
@[simp] theorem mk3_one (a b c : Pt κ) (h1 : a < b) (h2 : b < c) :
    (mk3 a b c h1 h2).1 1 = b := rfl
@[simp] theorem mk3_two (a b c : Pt κ) (h1 : a < b) (h2 : b < c) :
    (mk3 a b c h1 h2).1 2 = c := rfl

theorem adj_of_chain {a0 a1 a2 a3 a4 a5 : Pt κ}
    (h01 : a0 < a1) (h12 : a1 < a2) (h23 : a2 < a3) (h34 : a3 < a4) (h45 : a4 < a5) :
    (graph κ).Adj (mk3 a0 a1 a3 h01 (lt_trans h12 h23))
      (mk3 a2 a4 a5 (lt_trans h23 h34) h45) :=
  Or.inl ⟨h01, h12, h23, h34, h45⟩

theorem not_colorableBy_regular (hreg : κ.IsRegular) {θ : Cardinal.{u}} (hθ : θ < κ) :
    ¬ (SimpleGraph.toHG (graph κ)).ColorableBy θ := by
  have h_card : ∃ v0 v1 v2 : Pt κ, v0 < v1 ∧ v1 < v2 := by
    have := cofinal_univ hreg.1;
    by_cases h : Nonempty ( Pt κ ) <;> simp_all +decide [ Cofinal ];
  obtain ⟨ v0, v1, v2, hv0, hv1 ⟩ := h_card;
  intro h
  obtain ⟨c, hc⟩ := h
  have hadj : ∀ a b, (graph κ).Adj a b → c a ≠ c b :=
    fun a b hab => (toHG_proper_iff _ c).1 hc a b hab

  set F1 : Pt κ → Pt κ → (Pt κ → θ.out) := fun x y z => if h : x < y ∧ y < z then c (mk3 x y z h.1 h.2) else c (mk3 v0 v1 v2 hv0 hv1);

  obtain ⟨g, hg⟩ : ∃ g : Pt κ → Pt κ → θ.out, ∀ x y, x < y → Cofinal {z | z ∈ {z | y < z} ∧ F1 x y z = g x y} := by
    have h_cofinal_fiber : ∀ x y, x < y → ∃ v : θ.out, Cofinal {z | z ∈ {z | y < z} ∧ F1 x y z = v} := by
      intros x y hxy
      apply cofinal_fiber hreg hθ (cofinal_Ioi hreg.1 y) (F1 x y);
    exact ⟨ fun x y => if h : x < y then Classical.choose ( h_cofinal_fiber x y h ) else c ( mk3 v0 v1 v2 hv0 hv1 ), fun x y hxy => by simpa [ hxy ] using Classical.choose_spec ( h_cofinal_fiber x y hxy ) ⟩;

  set F2 : Pt κ → (Pt κ → θ.out) := fun x y => if h : x < y then g x y else c (mk3 v0 v1 v2 hv0 hv1);

  obtain ⟨hcol, hhcol⟩ : ∃ hcol : Pt κ → θ.out, ∀ x, Cofinal {y | y ∈ {y | x < y} ∧ F2 x y = hcol x} := by
    have h_cofinal_fiber : ∀ x : Pt κ, ∃ v : θ.out, Cofinal {y | y ∈ {y | x < y} ∧ F2 x y = v} := by
      intro x
      apply cofinal_fiber hreg hθ (cofinal_Ioi hreg.1 x) (F2 x);
    exact ⟨ fun x => Classical.choose ( h_cofinal_fiber x ), fun x => Classical.choose_spec ( h_cofinal_fiber x ) ⟩;

  obtain ⟨star, hstar⟩ : ∃ star : θ.out, Cofinal {x | hcol x = star} := by
    have := cofinal_fiber hreg hθ ( cofinal_univ hreg.1 ) hcol; aesop;
  obtain ⟨ α0, hα0 ⟩ := hstar v0;
  obtain ⟨ α1, hα1 ⟩ := hhcol α0 α0;
  obtain ⟨ α2, hα2 ⟩ := hstar α1;
  obtain ⟨ α3, hα3 ⟩ := hg α0 α1 hα1.2 α2;
  obtain ⟨ α4, hα4 ⟩ := hhcol α2 α3;
  obtain ⟨ α5, hα5 ⟩ := hg α2 α4 ( by
    exact hα4.1.1 ) α4;
  have h13 : α1 < α3 := lt_trans hα2.2 hα3.2
  have e1 : c (mk3 α0 α1 α3 hα1.2 h13) = star := by
    have h3 : F1 α0 α1 α3 = g α0 α1 := hα3.1.2
    have h2 : F2 α0 α1 = hcol α0 := hα1.1.2
    rw [show F1 α0 α1 α3 = c (mk3 α0 α1 α3 hα1.2 h13) from dif_pos ⟨hα1.2, h13⟩] at h3
    rw [show F2 α0 α1 = g α0 α1 from dif_pos hα1.2] at h2
    rw [h3, h2]
    exact hα0.1
  have h24 : α2 < α4 := lt_trans hα3.2 hα4.2
  have e2 : c (mk3 α2 α4 α5 h24 hα5.2) = star := by
    have h3 : F1 α2 α4 α5 = g α2 α4 := hα5.1.2
    have h2 : F2 α2 α4 = hcol α2 := hα4.1.2
    rw [show F1 α2 α4 α5 = c (mk3 α2 α4 α5 h24 hα5.2) from dif_pos ⟨h24, hα5.2⟩] at h3
    rw [show F2 α2 α4 = g α2 α4 from dif_pos h24] at h2
    rw [h3, h2]
    exact hα2.1
  exact hadj _ _ (adj_of_chain hα1.2 hα2.2 hα3.2 hα4.2 hα5.2) (e1.trans e2.symm)

theorem exists_pt_orderEmbedding {μ : Cardinal.{u}} (hμκ : μ ≤ κ) :
    Nonempty (Pt μ ↪o Pt κ) := by
      convert Nonempty.intro ?_;
      convert OrderEmbedding.ofStrictMono ( fun x => Ordinal.enum ( fun x1 x2 : κ.ord.ToType => x1 < x2 ) ⟨ Ordinal.typein ( fun x1 x2 : μ.ord.ToType => x1 < x2 ) x, ?_ ⟩ ) fun x y hxy => ?_;
      all_goals norm_num [ typein_lt_type ];
      all_goals norm_num [ typein_lt_type, enum_lt_enum ];
      · exact lt_of_lt_of_le ( Ordinal.typein_lt_self x ) ( Cardinal.ord_le_ord.mpr hμκ );
      · exact hxy

theorem colorableBy_of_le {μ : Cardinal.{u}} (hμκ : μ ≤ κ) {θ : Cardinal.{u}}
    (h : (SimpleGraph.toHG (graph κ)).ColorableBy θ) :
    (SimpleGraph.toHG (graph μ)).ColorableBy θ := by
      revert h;
      intro h
      obtain ⟨e, he⟩ : ∃ e : Pt μ ↪o Pt κ, True := by
        exact ⟨ Classical.choice ( exists_pt_orderEmbedding hμκ ), trivial ⟩;
      obtain ⟨c, hc⟩ := h
      have hadjκ : ∀ a b, (graph κ).Adj a b → c a ≠ c b :=
        fun a b hab => (toHG_proper_iff _ c).1 hc a b hab
      refine' ⟨ fun a => c ⟨ fun i => e ( a.1 i ), _ ⟩, _ ⟩;
      exact e.strictMono.comp a.2;
      convert toHG_proper_iff ( graph μ ) _ |>.2 _;
      intro x y hxy; specialize hadjκ ⟨ fun i => e ( x.1 i ), e.strictMono.comp x.2 ⟩ ⟨ fun i => e ( y.1 i ), e.strictMono.comp y.2 ⟩ ; simp_all +decide [ graph, Adjr, IsEdge ] ;

theorem not_colorableBy (hκ : ℵ₀ < κ) {θ : Cardinal.{u}} (hθ : θ < κ) :
    ¬ (SimpleGraph.toHG (graph κ)).ColorableBy θ := by
  intro h
  have hνκ : max θ ℵ₀ < κ := max_lt hθ hκ
  have hμκ : Order.succ (max θ ℵ₀) ≤ κ := Order.succ_le_of_lt hνκ
  have hμreg : (Order.succ (max θ ℵ₀)).IsRegular := Cardinal.isRegular_succ (le_max_right _ _)
  have hθμ : θ < Order.succ (max θ ℵ₀) := lt_of_le_of_lt (le_max_left _ _) (Order.lt_succ _)
  exact not_colorableBy_regular hμreg hθμ (colorableBy_of_le hμκ h)

theorem e2Core_oddGirth_one (hκ : ℵ₀ < κ) :
    ∃ (W : Type u) (G : SimpleGraph W),
      Cardinal.mk W ≤ κ ∧
      (∀ θ, θ < κ → ¬ (SimpleGraph.toHG G).ColorableBy θ) ∧
      NoShortOddCycle G 1 :=
  ⟨Vtx κ, graph κ, card_le hκ.le, fun _ hθ => not_colorableBy hκ hθ, noShortOddCycle_one⟩

end ER60
end Erdos593
end

-- GSn
section
open Cardinal Ordinal

namespace Erdos593
namespace GSn

open ER60 (Pt)

universe u

variable {κ : Cardinal.{u}} {n : ℕ}

abbrev L (n : ℕ) : ℕ := n * n + n + 1

theorem L_pos (n : ℕ) : 0 < L n := by positivity

theorem nt_lt (n : ℕ) {t : ℕ} (h : t ≤ n * n) : n + t < L n := by
  simp only [L]; omega

theorem t_lt (n : ℕ) {t : ℕ} (h : t ≤ n * n) : t < L n := by
  simp only [L]; omega

abbrev Vtx (n : ℕ) (κ : Cardinal.{u}) : Type u := {t : Fin (L n) → Pt κ // StrictMono t}

def IsEdge (u v : Fin (L n) → Pt κ) : Prop :=
  (∀ t : ℕ, (h : t ≤ n * n) → u ⟨n + t, nt_lt n h⟩ < v ⟨t, t_lt n h⟩) ∧
  (∀ t : ℕ, (h : t < n * n) → v ⟨t, t_lt n (le_of_lt h)⟩ < u ⟨n + t + 1, by simp only [L]; omega⟩)

def Adjr (u v : Vtx n κ) : Prop := IsEdge u.1 v.1 ∨ IsEdge v.1 u.1

theorem isEdge_irrefl (a : Fin (L n) → Pt κ) (ha : StrictMono a) : ¬ IsEdge a a := by
  rintro ⟨h1, -⟩
  have h := h1 0 (Nat.zero_le _)
  simp only [Nat.add_zero] at h
  have hle : a ⟨0, t_lt n (Nat.zero_le _)⟩ ≤ a ⟨n, nt_lt n (Nat.zero_le _)⟩ :=
    ha.monotone (by simp only [Fin.le_def]; omega)
  exact absurd (lt_of_lt_of_le h hle) (lt_irrefl _)

def graph (n : ℕ) (κ : Cardinal.{u}) : SimpleGraph (Vtx n κ) where
  Adj u v := Adjr u v
  symm := ⟨by intro a b h; exact h.symm⟩
  loopless := ⟨by rintro a (h | h) <;> exact isEdge_irrefl _ a.2 h⟩

theorem card_le (hκ : ℵ₀ ≤ κ) : Cardinal.mk (Vtx n κ) ≤ κ := by
  have h_card : #(Fin (L n) → Pt κ) = κ ^ (L n : ℕ) := by
    simp +decide [Cardinal.mk_toType, Cardinal.card_ord]
    norm_cast
  refine le_trans (Cardinal.mk_subtype_le _) ?_
  rw [h_card, Cardinal.power_nat_eq]
  · exact hκ
  · exact L_pos n

theorem edge_lt_of_index_le {u v : Fin (L n) → Pt κ}
    (hu : StrictMono u) (hv : StrictMono v) (h : IsEdge u v)
    {a b : ℕ} (ha : a < L n) (hb : b < L n) (hab : a ≤ b + n) :
    u ⟨a, ha⟩ < v ⟨b, hb⟩ := by
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t ≤ n * n ∧ a ≤ n + t ∧ t ≤ b := by
    exact ⟨ Min.min ( a - n ) b, le_trans ( min_le_left _ _ ) ( Nat.sub_le_of_le_add <| by linarith [ show L n = n * n + n + 1 from rfl ] ), by omega, min_le_right _ _ ⟩;
  exact lt_of_le_of_lt ( hu.monotone ( by exact Nat.le_trans ( Nat.le_refl _ ) ht.2.1 ) ) ( lt_of_lt_of_le ( h.1 t ht.1 ) ( hv.monotone ( by exact Nat.le_trans ht.2.2 ( Nat.le_refl _ ) ) ) )

theorem edge_gt_of_index_ge {u v : Fin (L n) → Pt κ}
    (hu : StrictMono u) (h : IsEdge u v)
    {a b : ℕ} (ha : a < L n) (hb : b < L n) (hab : b + n + 1 ≤ a) :
    v ⟨b, hb⟩ < u ⟨a, ha⟩ := by
  exact lt_of_lt_of_le ( h.2 b ( by unfold L at *; omega ) ) ( hu.monotone ( by exact Nat.le_trans ( by simp +arith +decide ) hab ) )

theorem isEdge_fst_lt {u v : Fin (L n) → Pt κ}
    (hu : StrictMono u) (hv : StrictMono v) (h : IsEdge u v) :
    u ⟨0, L_pos n⟩ < v ⟨0, L_pos n⟩ :=
  edge_lt_of_index_le hu hv h (L_pos n) (L_pos n) (by omega)

theorem not_isEdge_both {u v : Fin (L n) → Pt κ}
    (hu : StrictMono u) (hv : StrictMono v) (h : IsEdge u v) : ¬ IsEdge v u := by
  intro h'
  have h1 := isEdge_fst_lt hu hv h
  have h2 := isEdge_fst_lt hv hu h'
  exact absurd (lt_trans h1 h2) (lt_irrefl _)

end GSn
end Erdos593
end

-- GSnPotential
section
open Finset

namespace Erdos593
namespace GSn

theorem sum_range_zmod (m : ℕ) [NeZero m] (f : ZMod m → ℤ) :
    ∑ t ∈ Finset.range m, f (t : ZMod m) = ∑ e : ZMod m, f e := by
  apply Finset.sum_bij (fun (t : ℕ) (_ : t ∈ Finset.range m) => (t : ZMod m))
  · intro a ha; exact Finset.mem_univ _
  · intro a ha b hb hab
    simp only [Finset.mem_range] at ha hb
    have := (ZMod.natCast_eq_natCast_iff' a b m).mp hab
    rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this; exact this
  · intro e he
    exact ⟨e.val, Finset.mem_range.mpr (ZMod.val_lt e), by simp⟩
  · intro a ha; rfl

def backSum (m : ℕ) (c : ZMod m → ℤ) (j : ZMod m) (r : ℕ) : ℤ :=
  ∑ t ∈ Finset.range r, c (j - 1 - t)

@[simp] theorem backSum_zero (m : ℕ) (c : ZMod m → ℤ) (j : ZMod m) :
    backSum m c j 0 = 0 := by simp [backSum]

theorem backSum_shift (m : ℕ) (c : ZMod m → ℤ) (j : ZMod m) (r : ℕ) :
    backSum m c (j + 1) (r + 1) = c j + backSum m c j r := by
  unfold backSum
  rw [Finset.sum_range_succ']
  push_cast
  have e2 : c (j + 1 - 1 - 0) = c j := by congr 1; ring
  rw [e2, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht; congr 1; ring

theorem backSum_full (m : ℕ) [NeZero m] (c : ZMod m → ℤ) (j : ZMod m) :
    backSum m c (j + 1) m = ∑ e : ZMod m, c e := by
  unfold backSum
  have := sum_range_zmod m (fun e => c (j + 1 - 1 - e))
  rw [this]
  exact Fintype.sum_equiv (Equiv.subLeft (j + 1 - 1)) _ _ (fun e => rfl)

noncomputable def pot (m : ℕ) (hm : 0 < m) (c : ZMod m → ℤ) (j : ZMod m) : ℤ :=
  (Finset.range m).sup' (Finset.nonempty_range_iff.mpr hm.ne') (fun r => backSum m c j r)

theorem pot_nonneg (m : ℕ) (hm : 0 < m) (c : ZMod m → ℤ) (j : ZMod m) :
    0 ≤ pot m hm c j := by
  have : backSum m c j 0 ≤ pot m hm c j := Finset.le_sup' _ (Finset.mem_range.mpr hm)
  simpa using this

theorem backSum_le_posSum (m : ℕ) [NeZero m] (c : ZMod m → ℤ) (j : ZMod m)
    {r : ℕ} (hr : r ≤ m) :
    backSum m c j r ≤ ∑ e : ZMod m, max (c e) 0 := by
  refine' le_trans ( Finset.sum_le_sum fun x hx => show c ( j - 1 - x ) ≤ max ( c ( j - 1 - x ) ) 0 from le_max_left _ _ ) _;

  have h_sum_range : ∑ x ∈ Finset.range m, max (c (j - 1 - x)) 0 = ∑ e : ZMod m, max (c e) 0 := by
    convert sum_range_zmod m ( fun e => max ( c ( j - 1 - e ) ) 0 ) using 1;
    rw [ ← Equiv.sum_comp ( Equiv.subLeft ( j - 1 ) ) ] ; aesop;
  exact h_sum_range ▸ Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono hr ) fun _ _ _ => le_max_right _ _

theorem pot_le_posSum (m : ℕ) (hm : 0 < m) [NeZero m] (c : ZMod m → ℤ) (j : ZMod m) :
    pot m hm c j ≤ ∑ e : ZMod m, max (c e) 0 := by
  apply Finset.sup'_le
  intro r hr
  exact backSum_le_posSum m c j (le_of_lt (Finset.mem_range.mp hr))

theorem pot_step (m : ℕ) (hm : 0 < m) [NeZero m] (c : ZMod m → ℤ)
    (hsum : ∑ e : ZMod m, c e ≤ 0) (j : ZMod m) :
    pot m hm c j + c j ≤ pot m hm c (j + 1) := by
  have h_sup_le : ∀ r ∈ Finset.range m, backSum m c j r + c j ≤ pot m hm c (j + 1) := by
    intros r hr
    by_cases hr_lt : r + 1 < m;
    · have hp : backSum m c (j + 1) (r + 1) ≤ pot m hm c (j + 1) :=
        Finset.le_sup' (fun r => backSum m c (j + 1) r) (Finset.mem_range.mpr hr_lt)
      linarith [backSum_shift m c j r]
    · have h_eq : backSum m c (j + 1) (r + 1) = ∑ e : ZMod m, c e := by
        rw [ show r + 1 = m by linarith [ Finset.mem_range.mp hr ] ] ; exact backSum_full m c j;
      linarith [ backSum_shift m c j r, pot_nonneg m hm c ( j + 1 ) ];
  obtain ⟨ r, hr ⟩ := Finset.exists_max_image ( Finset.range m ) ( fun r => backSum m c j r ) ⟨ _, Finset.mem_range.mpr hm ⟩;
  linarith [ hr.2 r hr.1, h_sup_le r hr.1, show pot m hm c j = backSum m c j r from le_antisymm ( Finset.sup'_le _ _ fun x hx => hr.2 x hx ) ( Finset.le_sup' ( fun r => backSum m c j r ) hr.1 ) ]

end GSn
end Erdos593
end

-- GSnOddGirth
section
open Cardinal Finset

namespace Erdos593
namespace GSn

open ER60 (Pt)

universe u

variable {κ : Cardinal.{u}} {n : ℕ}

theorem no_cyclic_strictMono {α : Type*} [Preorder α] (m : ℕ) (hm : 0 < m)
    (f : ZMod m → α) (h : ∀ j : ZMod m, f j < f (j + 1)) : False := by
  haveI : NeZero m := ⟨hm.ne'⟩
  have hg : StrictMono (fun k : ℕ => f (k : ZMod m)) := by
    apply strictMono_nat_of_lt_succ
    intro k; have := h (k : ZMod m); simpa [Nat.cast_succ] using this
  have := hg hm; simp only [Nat.cast_zero, ZMod.natCast_self] at this
  exact lt_irrefl _ this

section Cycle

variable {m : ℕ} (A : ZMod m → Vtx n κ)

open Classical in

noncomputable def incr (j : ZMod m) : ℤ :=
  if IsEdge (A j).1 (A (j + 1)).1 then -(n : ℤ) else (n + 1)

open Classical in

noncomputable def descCount [NeZero m] : ℕ :=
  (Finset.univ.filter (fun j : ZMod m => ¬ IsEdge (A j).1 (A (j + 1)).1)).card

theorem cycle_false (hm : 0 < m) [NeZero m]
    (hAadj : ∀ j : ZMod m, (graph n κ).Adj (A j) (A (j + 1)))
    (hsum : ∑ e : ZMod m, incr A e ≤ 0)
    (hpos : ∑ e : ZMod m, max (incr A e) 0 ≤ (n * n + n : ℤ)) : False := by
  classical
  set k : ZMod m → ℕ := fun j => (pot m hm (incr A) j).toNat with hk_def
  have hpot_nn : ∀ j, 0 ≤ pot m hm (incr A) j := fun j => pot_nonneg m hm _ j
  have hk_eq : ∀ j, (k j : ℤ) = pot m hm (incr A) j := by
    intro j; rw [hk_def]; simp only; rw [Int.toNat_of_nonneg (hpot_nn j)]
  have hk_lt : ∀ j, k j < L n := by
    intro j
    have h1 : pot m hm (incr A) j ≤ (n * n + n : ℤ) :=
      le_trans (pot_le_posSum m hm (incr A) j) hpos
    have h2 : (k j : ℤ) ≤ (n * n + n : ℤ) := by rw [hk_eq]; exact h1
    have h3 : k j ≤ n * n + n := by exact_mod_cast h2
    simp only [L]; omega
  set f : ZMod m → Pt κ := fun j => (A j).1 ⟨k j, hk_lt j⟩ with hf_def
  apply no_cyclic_strictMono m hm f
  intro j
  have hstep : (k j : ℤ) + incr A j ≤ (k (j + 1) : ℤ) := by
    have := pot_step m hm (incr A) hsum j; rw [hk_eq, hk_eq]; exact this
  by_cases hasc : IsEdge (A j).1 (A (j + 1)).1
  · have hincr : incr A j = -(n : ℤ) := by rw [incr]; simp [hasc]
    rw [hincr] at hstep
    have hle : k j ≤ k (j + 1) + n := by
      have : (k j : ℤ) ≤ (k (j + 1) : ℤ) + n := by linarith
      exact_mod_cast this
    exact edge_lt_of_index_le (A j).2 (A (j + 1)).2 hasc (hk_lt j) (hk_lt (j + 1)) hle
  · have hincr : incr A j = (n + 1 : ℤ) := by rw [incr]; simp [hasc]
    rw [hincr] at hstep
    have hedge : IsEdge (A (j + 1)).1 (A j).1 := by
      rcases hAadj j with h | h
      · exact absurd h hasc
      · exact h
    have hge : k j + n + 1 ≤ k (j + 1) := by
      have : (k j : ℤ) + n + 1 ≤ (k (j + 1) : ℤ) := by linarith
      exact_mod_cast this
    exact edge_gt_of_index_ge (A (j + 1)).2 hedge (hk_lt (j + 1)) (hk_lt j) hge

theorem sum_incr_eq [NeZero m] :
    ∑ e : ZMod m, incr A e = -(n : ℤ) * m + (2 * n + 1) * descCount A := by
  unfold incr;
  simp +decide [ Finset.sum_ite, Finset.filter_not, Finset.card_sdiff, Finset.card_univ, ZMod.card, descCount ];
  rw [ Nat.cast_sub ( show _ ≤ _ from le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ) ] ; ring

theorem sum_max_incr_eq [NeZero m] :
    ∑ e : ZMod m, max (incr A e) 0 = (n + 1 : ℤ) * descCount A := by
  classical
  have h : ∀ e : ZMod m, max (incr A e) 0 =
      if ¬ IsEdge (A e).1 (A (e + 1)).1 then (n + 1 : ℤ) else 0 := by
    intro e
    unfold incr
    by_cases he : IsEdge (A e).1 (A (e + 1)).1
    · simp only [he, if_true, not_true_eq_false, if_false]
      exact max_eq_right (by omega)
    · simp only [he, if_false, not_false_eq_true, if_true]
      exact max_eq_left (by omega)
  rw [Finset.sum_congr rfl (fun e _ => h e), ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, mul_comm, descCount]

theorem cycle_false' (hm : 0 < m) [NeZero m]
    (hAadj : ∀ j : ZMod m, (graph n κ).Adj (A j) (A (j + 1)))
    (hmle : m ≤ 2 * n + 1)
    (hD : (2 * n + 1) * descCount A ≤ n * m) : False := by
  have hDn : descCount A ≤ n := by
    have h2 : n * m ≤ n * (2 * n + 1) := by gcongr
    nlinarith [hD, h2]
  refine cycle_false A hm hAadj ?_ ?_
  · rw [sum_incr_eq]
    have hz : (2 * n + 1 : ℤ) * descCount A ≤ (n : ℤ) * m := by exact_mod_cast hD
    have hmz : (m : ℤ) ≤ 2 * n + 1 := by exact_mod_cast hmle
    nlinarith [hz, hmz]
  · rw [sum_max_incr_eq]
    have hz : (descCount A : ℤ) ≤ n := by exact_mod_cast hDn
    nlinarith [hz]

def reverseCycle : ZMod m → Vtx n κ := fun j => A (-j)

theorem reverseCycle_adj [NeZero m]
    (hAadj : ∀ j : ZMod m, (graph n κ).Adj (A j) (A (j + 1))) :
    ∀ j : ZMod m, (graph n κ).Adj (reverseCycle A j) (reverseCycle A (j + 1)) := by
  intro j
  have := hAadj (-j - 1)
  simp [reverseCycle] at this ⊢
  ring_nf at this ⊢
  exact this.symm

theorem descCount_reverse [NeZero m]
    (hAadj : ∀ j : ZMod m, (graph n κ).Adj (A j) (A (j + 1))) :
    descCount (reverseCycle A) = m - descCount A := by
  refine' eq_tsub_of_add_eq _;
  convert Finset.card_add_card_compl ( Finset.filter ( fun j => ¬ IsEdge ( A ( -j ) ).1 ( A ( -j - 1 ) ).1 ) Finset.univ ) using 1;
  congr! 1;
  all_goals try exact Classical.decPred _;
  · unfold descCount reverseCycle
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [neg_add']
  · refine' Finset.card_bij ( fun j _ => -j - 1 ) _ _ _ <;> simp +decide [ Finset.mem_filter, Finset.mem_univ ];
    · intro a ha; specialize hAadj a; simp_all +decide [ add_comm, graph ] ;
      exact hAadj.resolve_left ha;
    · intro b hb;
      use -b - 1;
      have := not_isEdge_both ( A ( -b - 1 ) |>.2 ) ( A ( -b ) |>.2 ) ; simp_all +decide [ sub_eq_add_neg, add_assoc ];
  · cases m <;> aesop

end Cycle

theorem arith_minority (n D m : ℕ) (h1 : 2 * D + 1 ≤ m) (h2 : m ≤ 2 * n + 1) :
    (2 * n + 1) * D ≤ n * m := by
  have hDn : D ≤ n := by omega
  nlinarith [h1, h2, hDn, Nat.mul_le_mul_left n h1]

theorem noShortOddCycle_n : NoShortOddCycle (graph n κ) n := by
  intro m hodd hm3 hmle ⟨A, hAinj, hAadj⟩
  classical
  haveI : NeZero m := ⟨by omega⟩
  have hm0 : 0 < m := by omega

  set D := descCount A with hD_def
  have hDle : D ≤ m := by
    rw [hD_def, descCount]
    exact le_trans (Finset.card_filter_le _ _) (by rw [Finset.card_univ, ZMod.card])

  have hodd2 : 2 * D ≠ m := by
    rintro he
    have hme : ¬ Even m := Nat.not_even_iff_odd.mpr hodd
    exact hme ⟨D, by omega⟩
  rcases Nat.lt_or_ge (2 * D) m with hcase | hcase
  ·
    have h2D : 2 * D + 1 ≤ m := by omega
    exact cycle_false' A hm0 hAadj hmle (arith_minority n D m h2D hmle)
  ·
    have h2Dgt : m < 2 * D := by omega
    have hA'adj := reverseCycle_adj A hAadj
    have hD' : descCount (reverseCycle A) = m - D := descCount_reverse A hAadj
    have hRlt : 2 * descCount (reverseCycle A) + 1 ≤ m := by rw [hD']; omega
    exact cycle_false' (reverseCycle A) hm0 hA'adj hmle
      (arith_minority n (descCount (reverseCycle A)) m hRlt hmle)

end GSn
end Erdos593
end

-- ErdosHajnalGirthGeneral
section
open Cardinal Ordinal

namespace Erdos593
namespace EHG

open ER60 (Pt)

universe u

variable {κ : Cardinal.{u}} {k : ℕ}

abbrev Vtx (k : ℕ) (κ : Cardinal.{u}) : Type u := {t : Fin k → Pt κ // StrictMono t}

def IsEdge (a b : Fin k → Pt κ) : Prop :=
  (∀ i : ℕ, (h : i + 1 < k) → a ⟨i + 1, h⟩ < b ⟨i, by omega⟩) ∧
  (∀ i : ℕ, (h : i + 2 < k) → b ⟨i, by omega⟩ < a ⟨i + 2, h⟩)

def Adjr (a b : Vtx k κ) : Prop := IsEdge a.1 b.1 ∨ IsEdge b.1 a.1

theorem isEdge_irrefl (hk : 2 ≤ k) (a : Fin k → Pt κ) (ha : StrictMono a) :
    ¬ IsEdge a a := by
  rintro ⟨h1, -⟩
  have := h1 0 (by omega)
  have hmono := ha (show (⟨0, by omega⟩ : Fin k) < ⟨1, by omega⟩ by
    simp [Fin.lt_def])
  exact absurd this (not_lt.mpr (le_of_lt hmono))

def graph (k : ℕ) (κ : Cardinal.{u}) (hk : 2 ≤ k) : SimpleGraph (Vtx k κ) where
  Adj a b := Adjr a b
  symm := ⟨by intro a b h; exact h.symm⟩
  loopless := ⟨by
    rintro a (h | h) <;> exact isEdge_irrefl hk _ a.2 h⟩

theorem card_le (hk : 1 ≤ k) (hκ : ℵ₀ ≤ κ) : Cardinal.mk (Vtx k κ) ≤ κ := by
  have h_card : #(Fin k → Pt κ) = κ ^ (k : ℕ) := by
    simp [Cardinal.mk_toType, Cardinal.card_ord]
  refine le_trans (Cardinal.mk_subtype_le _) ?_
  rw [h_card, Cardinal.power_nat_eq hκ]
  omega

theorem isEdge_coord_lt (hk : 2 ≤ k) {a b : Fin k → Pt κ} (ha : StrictMono a)
    (hb : StrictMono b) (h : IsEdge a b) (j : Fin k) : a j < b j := by
  obtain ⟨h1, _⟩ := h
  have hjk : (j : ℕ) < k := j.2
  rcases Nat.eq_zero_or_pos (j : ℕ) with hj0 | hjpos
  · have e1 : a j < a ⟨1, by omega⟩ := ha (by simp [Fin.lt_def, hj0])
    have e2 := h1 0 (by omega)
    have hb0 : (⟨0, by omega⟩ : Fin k) = j := by ext; simp [hj0]
    rw [hb0] at e2
    exact lt_trans e1 e2
  · have e1 := h1 (j - 1) (by omega)
    have e2 : b ⟨j - 1, by omega⟩ < b j := hb (by simp [Fin.lt_def]; omega)
    have hj1 : (⟨(j-1)+1, by omega⟩ : Fin k) = j := by ext; simp; omega
    rw [hj1] at e1
    exact lt_trans e1 e2

theorem isEdge_gap {a b : Fin k → Pt κ} (h : IsEdge a b) (l : ℕ) (hl : l + 2 < k) :
    b ⟨l, by omega⟩ < a ⟨l + 2, hl⟩ := h.2 l hl

def proj3 (hk : 3 ≤ k) (a : Vtx k κ) : ER60.Vtx κ :=
  ⟨fun i : Fin 3 => a.1 ⟨i, by omega⟩, by
    intro i j hij
    have hij' : (i : ℕ) < (j : ℕ) := hij
    exact a.2 (Fin.mk_lt_mk.mpr hij')⟩

theorem isEdge_proj3 (hk : 3 ≤ k) {a b : Fin k → Pt κ}
    (ha : StrictMono a) (hb : StrictMono b) (h : IsEdge a b) :
    ER60.IsEdge (fun i : Fin 3 => a ⟨i, by omega⟩) (fun i : Fin 3 => b ⟨i, by omega⟩) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ha (by simp [Fin.lt_def])
  · exact h1 0 (by omega)
  · exact h2 0 (by omega)
  · exact h1 1 (by omega)
  · exact hb (by simp [Fin.lt_def])

theorem proj3_adj (hk : 3 ≤ k) {a b : Vtx k κ}
    (h : (graph k κ (by omega)).Adj a b) :
    (ER60.graph κ).Adj (proj3 hk a) (proj3 hk b) := by
  rcases h with h | h
  · exact Or.inl (isEdge_proj3 hk a.2 b.2 h)
  · exact Or.inr (isEdge_proj3 hk b.2 a.2 h)

theorem triangleFree (hk : 3 ≤ k) (a b c : Vtx k κ)
    (hab : (graph k κ (by omega)).Adj a b)
    (hbc : (graph k κ (by omega)).Adj b c)
    (hac : (graph k κ (by omega)).Adj a c) : False :=
  ER60.triangleFree _ _ _ (proj3_adj hk hab) (proj3_adj hk hbc) (proj3_adj hk hac)

theorem noShortOddCycle_one (hk : 3 ≤ k) :
    NoShortOddCycle (graph k κ (by omega)) 1 := by
  intro m hm₁ hm₂ hm₃
  interval_cases m
  simp_all
  rintro x hx_inj
  by_contra h_contra
  push_neg at h_contra
  exact triangleFree hk _ _ _ (h_contra 0) (h_contra 1)
    ((h_contra 2).symm)

theorem colorableBy_of_le (hk : 2 ≤ k) {μ : Cardinal.{u}} (hμκ : μ ≤ κ)
    {θ : Cardinal.{u}}
    (h : (SimpleGraph.toHG (graph k κ hk)).ColorableBy θ) :
    (SimpleGraph.toHG (graph k μ hk)).ColorableBy θ := by
  obtain ⟨e, -⟩ : ∃ _ : Pt μ ↪o Pt κ, True :=
    ⟨Classical.choice (ER60.exists_pt_orderEmbedding hμκ), trivial⟩
  obtain ⟨c, hc⟩ := h
  have hadjκ : ∀ a b : Vtx k κ, (graph k κ hk).Adj a b → c a ≠ c b := by
    intro a b hab
    exact (toHG_proper_iff _ c).1 hc a b hab
  refine ⟨fun a => c ⟨fun i => e (a.1 i), e.strictMono.comp a.2⟩, ?_⟩
  rw [toHG_proper_iff]
  intro x y hxy
  refine hadjκ ⟨fun i => e (x.1 i), e.strictMono.comp x.2⟩
    ⟨fun i => e (y.1 i), e.strictMono.comp y.2⟩ ?_
  rcases hxy with h | h
  · refine Or.inl ⟨fun i hi => ?_, fun i hi => ?_⟩
    · exact e.strictMono (h.1 i hi)
    · exact e.strictMono (h.2 i hi)
  · refine Or.inr ⟨fun i hi => ?_, fun i hi => ?_⟩
    · exact e.strictMono (h.1 i hi)
    · exact e.strictMono (h.2 i hi)

end EHG
end Erdos593
end

-- EHGirthChromatic
section
open Cardinal Erdos593.ER60

namespace Erdos593
namespace EHG

open ER60 (Pt Cofinal cofinal_fiber cofinal_Ioi cofinal_univ)

universe u

variable {κ : Cardinal.{u}} {k : ℕ} {θ : Cardinal.{u}}

def tailSet (w : ℕ → Pt κ) (j : ℕ) : Set (Pt κ) :=
  if j = 0 then Set.univ else {z | w (j - 1) < z}

theorem tailSet_cofinal (hκ : ℵ₀ ≤ κ) (w : ℕ → Pt κ) (j : ℕ) :
    Cofinal (tailSet w j) := by
  unfold tailSet
  split
  · exact cofinal_univ hκ
  · exact cofinal_Ioi hκ _

noncomputable def stab (hreg : κ.IsRegular) (hθ : θ < κ) (c : (ℕ → Pt κ) → θ.out) :
    ℕ → ℕ → (ℕ → Pt κ) → θ.out
  | 0, _, w => c w
  | (fuel + 1), j, w =>
      Classical.choose (cofinal_fiber hreg hθ (tailSet_cofinal hreg.1 w j)
        (fun z => stab hreg hθ c fuel (j + 1) (Function.update w j z)))

theorem stab_spec (hreg : κ.IsRegular) (hθ : θ < κ) (c : (ℕ → Pt κ) → θ.out)
    (fuel j : ℕ) (w : ℕ → Pt κ) :
    Cofinal {z | z ∈ tailSet w j ∧
      stab hreg hθ c fuel (j + 1) (Function.update w j z)
        = stab hreg hθ c (fuel + 1) j w} := by
  exact Classical.choose_spec (cofinal_fiber hreg hθ (tailSet_cofinal hreg.1 w j)
    (fun z => stab hreg hθ c fuel (j + 1) (Function.update w j z)))

theorem stab_congr (hreg : κ.IsRegular) (hθ : θ < κ) (c : (ℕ → Pt κ) → θ.out)
    (hc : ∀ w w' : ℕ → Pt κ, (∀ i < k, w i = w' i) → c w = c w') :
    ∀ (fuel j : ℕ), k ≤ j + fuel → ∀ (w w' : ℕ → Pt κ), (∀ i < j, w i = w' i) →
      stab hreg hθ c fuel j w = stab hreg hθ c fuel j w' := by
  intro fuel j hj w w' hw;
  induction' fuel with fuel ih generalizing j w w' <;> simp_all +decide [ stab ];
  · exact hc _ _ fun i hi => hw i ( by linarith );
  · congr! 1;
    ext x;
    congr! 1;
    ext y;
    simp +decide [ tailSet ];
    grind

theorem exists_next_star (hreg : κ.IsRegular) (hθ : θ < κ) (c : (ℕ → Pt κ) → θ.out)
    (fuel j : ℕ) (w : ℕ → Pt κ) (B : Pt κ) :
    ∃ z, B < z ∧ z ∈ tailSet w j ∧
      stab hreg hθ c fuel (j + 1) (Function.update w j z)
        = stab hreg hθ c (fuel + 1) j w := by
  obtain ⟨z, hzS, hBz⟩ := stab_spec hreg hθ c fuel j w B
  exact ⟨z, hBz, hzS.1, hzS.2⟩

noncomputable def toTotal (k : ℕ) (c0 : Vtx k κ → θ.out) (junk : θ.out) :
    (ℕ → Pt κ) → θ.out :=
  fun w => if h : StrictMono (fun i : Fin k => w i) then c0 ⟨_, h⟩ else junk

theorem toTotal_prefix (k : ℕ) (c0 : Vtx k κ → θ.out) (junk : θ.out)
    (w w' : ℕ → Pt κ) (h : ∀ i < k, w i = w' i) :
    toTotal k c0 junk w = toTotal k c0 junk w' := by
  unfold toTotal
  have he : (fun i : Fin k => w i) = (fun i : Fin k => w' i) := funext (fun i => h i i.2)
  simp only [he]

theorem toTotal_mono (k : ℕ) (c0 : Vtx k κ → θ.out) (junk : θ.out)
    (w : ℕ → Pt κ) (h : StrictMono (fun i : Fin k => w i)) :
    toTotal k c0 junk w = c0 ⟨fun i : Fin k => w i, h⟩ := dif_pos h

set_option maxHeartbeats 1200000 in
theorem extract_aux (hreg : κ.IsRegular) (hθ : θ < κ) (c : (ℕ → Pt κ) → θ.out)
    (star : θ.out) (hstar : ∀ w, stab hreg hθ c k 0 w = star) (hk : 2 ≤ k) :
    ∀ cb, cb ≤ k - 2 → ∃ (wa wb : ℕ → Pt κ),
      StrictMonoOn wa (Set.Iio (cb + 2)) ∧ StrictMonoOn wb (Set.Iio cb) ∧
      stab hreg hθ c (k - (cb + 2)) (cb + 2) wa = star ∧
      stab hreg hθ c (k - cb) cb wb = star ∧
      (∀ i < cb, wa (i + 1) < wb i) ∧
      (∀ i < cb, wb i < wa (i + 2)) ∧
      (∀ i < cb, wb i < wa (cb + 1)) := by
  intro cb hcb;
  induction' cb with cb ih generalizing k;
  · rcases k with ( _ | _ | k ) <;> simp_all +decide [ StrictMonoOn ];
    obtain ⟨ z₀, hz₀ ⟩ := exists_next_star hreg hθ c ( k + 1 ) 0 ( fun _ => Classical.choose ( show ∃ p : Pt κ, True from by
                                                                                                cases isEmpty_or_nonempty ( Pt κ ) <;> aesop ) ) ( Classical.choose ( show ∃ p : Pt κ, True from by
                                                                                                                                                              cases hreg ; aesop ) )
    generalize_proofs at *;
    obtain ⟨ z₁, hz₁ ⟩ := exists_next_star hreg hθ c k 1 ( Function.update ( fun _ => Classical.choose ‹∃ p : Pt κ, True› ) 0 z₀ ) z₀
    generalize_proofs at *;
    use Function.update (Function.update (fun _ => Classical.choose ‹∃ p : Pt κ, True›) 0 z₀) 1 z₁;
    simp_all +decide [ Function.update_apply ];
    exact ⟨ fun a ha b hb hab => by interval_cases a <;> interval_cases b ; tauto, by rintro rfl; exact absurd hθ ( by simp +decide ) ⟩;
  · obtain ⟨wa, wb, hwa_mono, hwb_mono, hwa_star, hwb_star, hwa_lt_hwb, hwb_lt_hwa, hwb_lt_hwa_last⟩ := ih hstar hk (by omega);

    obtain ⟨zb, hzb_gt, hzb_tail, hzb_star⟩ : ∃ zb, wa (cb + 1) < zb ∧ zb ∈ tailSet wb cb ∧ stab hreg hθ c (k - cb - 1) (cb + 1) (Function.update wb cb zb) = star := by
      convert exists_next_star hreg hθ c ( k - cb - 1 ) cb wb ( wa ( cb + 1 ) ) using 1;
      grind +revert;

    obtain ⟨za, hza_gt, hza_tail, hza_star⟩ : ∃ za, zb < za ∧ za ∈ tailSet wa (cb + 2) ∧ stab hreg hθ c (k - (cb + 2) - 1) (cb + 3) (Function.update wa (cb + 2) za) = star := by
      convert exists_next_star hreg hθ c ( k - ( cb + 2 ) - 1 ) ( cb + 2 ) wa zb using 1;
      grind +qlia;
    refine' ⟨ Function.update wa ( cb + 2 ) za, Function.update wb cb zb, _, _, _, _, _ ⟩;
    · intro x hx y hy hxy; simp_all +decide [ StrictMonoOn, Function.update_apply ] ;
      split_ifs <;> try linarith;
      · by_cases hx' : x < cb + 1;
        · exact lt_trans ( hwa_mono ( by linarith ) ( by linarith ) ( by linarith ) ) ( lt_trans hzb_gt hza_gt );
        · grind;
      · exact hwa_mono ( by omega ) ( by omega ) hxy;
    · intro i hi j hj hij; simp_all +decide [ StrictMonoOn ] ;
      grind +splitImp;
    · exact hza_star;
    · grind;
    · grind +locals

end EHG
end Erdos593
end

-- GSnChromatic
section
open Cardinal

namespace Erdos593
namespace GSn

open ER60 (Pt Cofinal cofinal_fiber cofinal_Ioi cofinal_univ)

universe u

variable {κ : Cardinal.{u}} {n : ℕ} {θ : Cardinal.{u}}

theorem isEdge_map {μ : Cardinal.{u}} (e : Pt μ ↪o Pt κ) {u v : Fin (L n) → Pt μ}
    (h : IsEdge u v) : IsEdge (fun i => e (u i)) (fun i => e (v i)) := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨fun t ht => e.strictMono (h1 t ht), fun t ht => e.strictMono (h2 t ht)⟩

theorem colorableBy_of_le {μ : Cardinal.{u}} (hμκ : μ ≤ κ)
    (h : (SimpleGraph.toHG (graph n κ)).ColorableBy θ) :
    (SimpleGraph.toHG (graph n μ)).ColorableBy θ := by
  obtain ⟨e, -⟩ : ∃ _ : Pt μ ↪o Pt κ, True :=
    ⟨Classical.choice (ER60.exists_pt_orderEmbedding hμκ), trivial⟩
  obtain ⟨c, hc⟩ := h
  have hadjκ : ∀ a b : Vtx n κ, (graph n κ).Adj a b → c a ≠ c b := by
    intro a b hab
    exact (toHG_proper_iff _ c).1 hc a b hab
  refine ⟨fun a => c ⟨fun i => e (a.1 i), e.strictMono.comp a.2⟩, ?_⟩
  rw [toHG_proper_iff]
  intro x y hxy
  refine hadjκ ⟨fun i => e (x.1 i), e.strictMono.comp x.2⟩
    ⟨fun i => e (y.1 i), e.strictMono.comp y.2⟩ ?_
  rcases hxy with h | h
  · exact Or.inl (isEdge_map e h)
  · exact Or.inr (isEdge_map e h)

theorem grow (hreg : κ.IsRegular) (hθ : θ < κ) (c : (ℕ → Pt κ) → θ.out) (star : θ.out)
    (w : ℕ → Pt κ) (q r : ℕ) (B : Pt κ) (hqr : q + r ≤ L n)
    (hstar : EHG.stab hreg hθ c (L n - q) q w = star)
    (hwB : ∀ i, i < q → w i ≤ B)
    (hmono : StrictMonoOn w (Set.Iio q)) :
    ∃ (w' : ℕ → Pt κ) (B' : Pt κ),
      B ≤ B' ∧
      (∀ i, i < q → w' i = w i) ∧
      (∀ i, i < q + r → w' i ≤ B') ∧
      (∀ i, q ≤ i → i < q + r → B < w' i) ∧
      StrictMonoOn w' (Set.Iio (q + r)) ∧
      EHG.stab hreg hθ c (L n - (q + r)) (q + r) w' = star := by
  induction' r with r ih;
  · exact ⟨ w, B, le_rfl, fun i hi => rfl, fun i hi => hwB i hi, fun i hi₁ hi₂ => by linarith, hmono, hstar ⟩;
  · obtain ⟨ w', B', hB', hw', hB'', hB''', hB'''' ⟩ := ih ( by linarith );
    obtain ⟨ z, hz₁, hz₂, hz₃ ⟩ := EHG.exists_next_star hreg hθ c ( L n - ( q + r ) - 1 ) ( q + r ) w' B';
    refine' ⟨ Function.update w' ( q + r ) z, z, _, _, _, _, _ ⟩;
    · exact le_trans hB' hz₁.le;
    · grind;
    · intro i hi; by_cases hi' : i = q + r <;> simp_all +decide [ Function.update_apply ] ;
      exact le_trans ( hB'' i ( by omega ) ) ( le_of_lt hz₁ );
    · grind +revert;
    · refine' ⟨ _, _ ⟩;
      · intro i hi j hj hij; simp_all +decide [ Function.update_apply ] ;
        split_ifs <;> try linarith;
        · exact lt_of_le_of_lt ( hB'' i ( by omega ) ) hz₁;
        · exact hB'''' |>.1 ( show i < q + r from by omega ) ( show j < q + r from by omega ) hij;
      · grind +qlia

theorem mid (hreg : κ.IsRegular) (hθ : θ < κ) (c : (ℕ → Pt κ) → θ.out) (star : θ.out)
    (wu wv : ℕ → Pt κ) (t0 s : ℕ) (B : Pt κ)
    (hs : n + t0 + s ≤ L n)
    (hstaru : EHG.stab hreg hθ c (L n - (n + t0)) (n + t0) wu = star)
    (hstarv : EHG.stab hreg hθ c (L n - t0) t0 wv = star)
    (hwuB : ∀ i, i < n + t0 → wu i ≤ B)
    (hwvB : ∀ i, i < t0 → wv i ≤ B)
    (hmonou : StrictMonoOn wu (Set.Iio (n + t0)))
    (hmonov : StrictMonoOn wv (Set.Iio t0)) :
    ∃ (wu' wv' : ℕ → Pt κ) (B' : Pt κ),
      B ≤ B' ∧
      (∀ i, i < n + t0 → wu' i = wu i) ∧
      (∀ i, i < t0 → wv' i = wv i) ∧
      (∀ i, i < n + t0 + s → wu' i ≤ B') ∧
      (∀ i, i < t0 + s → wv' i ≤ B') ∧
      StrictMonoOn wu' (Set.Iio (n + t0 + s)) ∧
      StrictMonoOn wv' (Set.Iio (t0 + s)) ∧
      EHG.stab hreg hθ c (L n - (n + t0 + s)) (n + t0 + s) wu' = star ∧
      EHG.stab hreg hθ c (L n - (t0 + s)) (t0 + s) wv' = star ∧
      (∀ t, t0 ≤ t → t < t0 + s → wu' (n + t) < wv' t) ∧
      (∀ t, t0 ≤ t → t + 1 < t0 + s → wv' t < wu' (n + t + 1)) := by
  induction' s with s ih generalizing t0 wu wv B;
  · exact ⟨ wu, wv, B, le_rfl, fun i hi => rfl, fun i hi => rfl, hwuB, hwvB, hmonou, hmonov, hstaru, hstarv, by intros; linarith, by intros; linarith ⟩;
  · obtain ⟨ wu', wv', B', hB', hwu', hwv', hwuB', hwvB', hmonou', hmonov', hstaru', hstarv', hlow', hhigh' ⟩ := ih wu wv t0 B ( by linarith ) hstaru hstarv hwuB hwvB hmonou hmonov;
    obtain ⟨ zu, hzu₁, hzu₂, hzu₃ ⟩ := EHG.exists_next_star hreg hθ c ( L n - ( n + t0 + s ) - 1 ) ( n + t0 + s ) wu' B';
    obtain ⟨ zv, hzv₁, hzv₂, hzv₃ ⟩ := EHG.exists_next_star hreg hθ c ( L n - ( t0 + s ) - 1 ) ( t0 + s ) wv' zu;
    refine' ⟨ Function.update wu' ( n + t0 + s ) zu, Function.update wv' ( t0 + s ) zv, zv, _, _, _, _, _ ⟩;
    · exact le_trans hB' ( le_trans hzu₁.le hzv₁.le );
    · grind +qlia;
    · grind;
    · grind +splitImp;
    · refine' ⟨ _, _, _, _, _ ⟩;
      · grind;
      · intro i hi j hj hij;
        by_cases hi' : i = n + t0 + s <;> by_cases hj' : j = n + t0 + s <;> simp +decide [ *, Function.update_apply ] at hij ⊢;
        · linarith [ Set.mem_Iio.mp hi, Set.mem_Iio.mp hj ];
        · exact lt_of_le_of_lt ( hwuB' i hij ) hzu₁;
        · exact hmonou' ( show i < n + t0 + s from lt_of_le_of_ne ( Nat.le_of_lt_succ hi ) hi' ) ( show j < n + t0 + s from lt_of_le_of_ne ( Nat.le_of_lt_succ hj ) hj' ) hij;
      · intro i hi j hj hij; simp_all +decide [ Function.update_apply ] ;
        split_ifs <;> try linarith;
        · exact lt_of_le_of_lt ( hwvB' i ( by omega ) ) ( lt_of_lt_of_le hzu₁ ( le_of_lt hzv₁ ) );
        · exact hmonov' ( show i < t0 + s from by omega ) ( show j < t0 + s from by omega ) hij;
      · grind;
      · grind

theorem extract_gsn (hreg : κ.IsRegular) (hθ : θ < κ)
    (c : (ℕ → Pt κ) → θ.out) (star : θ.out)
    (hstar : ∀ w, EHG.stab hreg hθ c (L n) 0 w = star) :
    ∃ (wu wv : ℕ → Pt κ),
      StrictMono (fun i : Fin (L n) => wu i) ∧
      StrictMono (fun i : Fin (L n) => wv i) ∧
      c wu = star ∧ c wv = star ∧
      IsEdge (fun i : Fin (L n) => wu i) (fun i : Fin (L n) => wv i) := by
  classical
  haveI hInf : Infinite (Pt κ) := Cardinal.infinite_iff.2 (by simpa using hreg.1)
  obtain ⟨p0⟩ : Nonempty (Pt κ) := inferInstance

  obtain ⟨wu1, B1, -, -, hwu1le, -, hwu1mono, hwu1stab⟩ :=
    grow (n := n) hreg hθ c star (fun _ => p0) 0 n p0
      (by simp only [L]; omega) (by simpa using hstar (fun _ => p0))
      (by intro i hi; omega) (by intro a ha b hb hab; simp only [Set.mem_Iio] at ha; omega)
  simp only [Nat.zero_add] at hwu1le hwu1mono hwu1stab

  obtain ⟨wu2, wv2, B2, -, -, -, hwu2le, hwv2le, hwu2mono, hwv2mono,
      hwu2stab, hwv2stab, hlow, hhigh⟩ :=
    mid (n := n) hreg hθ c star wu1 (fun _ => p0) 0 (n * n + 1) B1
      (by simp only [L]; omega) (by simpa using hwu1stab)
      (by simpa using hstar (fun _ => p0)) (by simpa using hwu1le)
      (by intro i hi; omega) (by simpa using hwu1mono)
      (by intro a ha b hb hab; simp only [Set.mem_Iio] at ha; omega)

  obtain ⟨wv3, B3, -, hwv3agree, -, -, hwv3mono, hwv3stab⟩ :=
    grow (n := n) hreg hθ c star wv2 (n * n + 1) n B2
      (by simp only [L]; omega) (by simpa using hwv2stab)
      (by simpa using hwv2le) (by simpa using hwv2mono)

  have hidxu : n + 0 + (n * n + 1) = L n := by simp only [L]; ring
  have hidxv : n * n + 1 + n = L n := by simp only [L]; ring
  refine ⟨wu2, wv3, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hm := hwu2mono; rw [hidxu] at hm
    intro a b hab
    exact hm (Set.mem_Iio.mpr a.2) (Set.mem_Iio.mpr b.2) hab
  ·
    have hm := hwv3mono; rw [hidxv] at hm
    intro a b hab
    exact hm (Set.mem_Iio.mpr a.2) (Set.mem_Iio.mpr b.2) hab
  ·
    have h := hwu2stab; rw [hidxu, Nat.sub_self] at h
    exact h
  ·
    have h := hwv3stab; rw [hidxv, Nat.sub_self] at h
    exact h
  ·
    refine ⟨?_, ?_⟩
    · intro t ht
      show wu2 (n + t) < wv3 t
      rw [hwv3agree t (by omega)]
      exact hlow t (Nat.zero_le _) (by omega)
    · intro t ht
      show wv3 t < wu2 (n + t + 1)
      rw [hwv3agree t (by omega)]
      exact hhigh t (Nat.zero_le _) (by omega)

theorem not_colorableBy_regular (hreg : κ.IsRegular) (hθ : θ < κ) :
    ¬ (SimpleGraph.toHG (graph n κ)).ColorableBy θ := by
  by_contra h_contra
  obtain ⟨c0, hc0'⟩ := h_contra
  have hproper : ∀ a b : Vtx n κ, (graph n κ).Adj a b → c0 a ≠ c0 b :=
    fun a b hab => (toHG_proper_iff _ c0).1 hc0' a b hab
  obtain ⟨x0, -⟩ : ∃ _ : Vtx n κ, True := by
    have h_inf : Infinite (Pt κ) := Cardinal.infinite_iff.2 (by simpa using hreg.1)
    obtain ⟨s, hs⟩ : ∃ s : Finset (Pt κ), s.card = L n := by
      have hemb := h_inf.natEmbedding
      exact ⟨Finset.image (fun i : Fin (L n) => hemb i) Finset.univ, by
        rw [Finset.card_image_of_injective _ fun i j hij => by
          simpa [Fin.ext_iff] using hemb.injective hij]; simp⟩
    exact ⟨⟨fun i => s.orderEmbOfFin (by aesop) i, by aesop_cat⟩, trivial⟩
  set junk := c0 x0 with hjunk
  set c := EHG.toTotal (L n) c0 junk with hc_def
  have hc : ∀ w w' : ℕ → Pt κ, (∀ i < L n, w i = w' i) → c w = c w' :=
    EHG.toTotal_prefix (L n) c0 junk
  obtain ⟨star, hstar⟩ : ∃ star : θ.out, ∀ w : ℕ → Pt κ,
      EHG.stab hreg hθ c (L n) 0 w = star := by
    refine ⟨EHG.stab hreg hθ c (L n) 0 (fun _ => x0.1 ⟨0, L_pos n⟩), fun w => ?_⟩
    exact EHG.stab_congr hreg hθ c hc (L n) 0 (by omega) w _ (fun i hi => by omega)
  obtain ⟨wu, wv, hwu_mono, hwv_mono, hcu, hcv, hedge⟩ := extract_gsn hreg hθ c star hstar
  set au : Vtx n κ := ⟨fun i => wu i, hwu_mono⟩ with hau
  set av : Vtx n κ := ⟨fun i => wv i, hwv_mono⟩ with hav
  have e1 : c wu = c0 au := EHG.toTotal_mono (L n) c0 junk wu hwu_mono
  have e2 : c wv = c0 av := EHG.toTotal_mono (L n) c0 junk wv hwv_mono
  have hne : c0 au ≠ c0 av := hproper au av (Or.inl hedge)
  apply hne
  rw [← e1, ← e2, hcu, hcv]

theorem not_colorableBy (hκ : ℵ₀ < κ) (hθ : θ < κ) :
    ¬ (SimpleGraph.toHG (graph n κ)).ColorableBy θ := by
  intro h
  have hνκ : max θ ℵ₀ < κ := max_lt hθ hκ
  have hμκ : Order.succ (max θ ℵ₀) ≤ κ := Order.succ_le_of_lt hνκ
  have hμreg : (Order.succ (max θ ℵ₀)).IsRegular := Cardinal.isRegular_succ (le_max_right _ _)
  have hθμ : θ < Order.succ (max θ ℵ₀) := lt_of_le_of_lt (le_max_left _ _) (Order.lt_succ _)
  exact not_colorableBy_regular hμreg hθμ (colorableBy_of_le hμκ h)

end GSn
end Erdos593
end

-- E2Genuine
section
open Cardinal

namespace Erdos593

universe u

theorem e2Core_genuine : E2Core.{u} := by
  intro κ hκ s
  exact ⟨GSn.Vtx s κ, GSn.graph s κ, GSn.card_le hκ.le,
    fun _ hθ => GSn.not_colorableBy hκ hθ, GSn.noShortOddCycle_n⟩

theorem e2_EH_oddgirth : E2_EH_oddgirth.{u} := E2_of_core e2Core_genuine

end Erdos593
end

-- E5Proof
section
open Cardinal

namespace Erdos593

universe u

variable {W : Type u}

def shadowGraph (H : Hypergraph W) : SimpleGraph W :=
  SimpleGraph.fromRel (fun u v => ∃ e ∈ H.edges, u ∈ e ∧ v ∈ e)

structure Loose7Witness (H : Hypergraph W) where
  core : Fin 7 → W
  priv : Fin 7 → W
  injective : Function.Injective (Sum.elim core priv)
  edge_mem : ∀ i : Fin 7,
    ({core i, core (i + 1), priv i} : Set W) ∈ H.edges

def edgesMeeting (H : Hypergraph W) (S : Set W) : Set (Set W) :=
  {e | e ∈ H.edges ∧ (e ∩ S).Nonempty}

structure CleanLoose7EdgeCycle (H : Hypergraph W) where
  core : Fin 7 → W
  edge : Fin 7 → Set W
  core_injective : Function.Injective core
  edge_mem : ∀ i, edge i ∈ H.edges
  left_mem : ∀ i, core i ∈ edge i
  right_mem : ∀ i, core (i + 1) ∈ edge i
  core_mem_iff : ∀ i j, core j ∈ edge i ↔ j = i ∨ j = i + 1
  inter_subset_core : ∀ ⦃i j⦄, i ≠ j → edge i ∩ edge j ⊆ Set.range core

theorem cleanEdgeCycle_edge_injective (H : Hypergraph W)
    (c : CleanLoose7EdgeCycle H) : Function.Injective c.edge := by
  intro i j hij
  have hl := (c.core_mem_iff j i).mp (hij ▸ c.left_mem i)
  have hr := (c.core_mem_iff j (i + 1)).mp (hij ▸ c.right_mem i)
  rcases hl with h | h
  · exact h
  · subst i
    fin_cases j <;> simp at hr

end Erdos593
end

-- E5Obstructions
section
open Cardinal

namespace Erdos593

universe u

variable {W : Type u}

def finiteEdgeSupport (D : Finset (Set W)) : Set W := ⋃ e ∈ D, e

end Erdos593
end

-- E5IntersectionCycle
section
namespace Erdos593

universe u

variable {W : Type u}

def edgeIntersectionGraph (H : Hypergraph W) : SimpleGraph H.edges :=
  SimpleGraph.fromRel (fun e f => (e.1 ∩ f.1).Nonempty)

theorem edgeIntersectionGraph_adj_iff (H : Hypergraph W) (e f : H.edges) :
    (edgeIntersectionGraph H).Adj e f ↔ e ≠ f ∧ (e.1 ∩ f.1).Nonempty := by
  constructor;
  · intro h;
    cases h.2 <;> simp_all +decide [ edgeIntersectionGraph ];
    rwa [ Set.inter_comm ];
  · simp +contextual [ edgeIntersectionGraph ]

structure InducedEdgeIntersectionSevenCycle (H : Hypergraph W) where
  edge : Fin 7 → H.edges
  injective : Function.Injective edge
  consecutive : ∀ i, (edgeIntersectionGraph H).Adj (edge i) (edge (i + 1))
  induced : ∀ i j, (edgeIntersectionGraph H).Adj (edge i) (edge j) →
    j = i + 1 ∨ i = j + 1

noncomputable def InducedEdgeIntersectionSevenCycle.core
    {H : Hypergraph W} (c : InducedEdgeIntersectionSevenCycle H) (i : Fin 7) : W :=
  Classical.choose ((edgeIntersectionGraph_adj_iff H (c.edge (i - 1)) (c.edge i)).mp
    (by simpa using c.consecutive (i - 1))).2

theorem InducedEdgeIntersectionSevenCycle.core_mem_right
    {H : Hypergraph W} (c : InducedEdgeIntersectionSevenCycle H) (i : Fin 7) :
    c.core i ∈ (c.edge i).1 := by
  exact Classical.choose_spec ( _ : ∃ x, x ∈ ( c.edge ( i - 1 ) ).1 ∩ ( c.edge i ).1 ) |>.2

theorem InducedEdgeIntersectionSevenCycle.core_mem_left
    {H : Hypergraph W} (c : InducedEdgeIntersectionSevenCycle H) (i : Fin 7) :
    c.core (i + 1) ∈ (c.edge i).1 := by
  convert Classical.choose_spec ( ( edgeIntersectionGraph_adj_iff H ( c.edge i ) ( c.edge ( i + 1 ) ) ).mp ( by simpa using c.consecutive i ) |>.2 ) |>.1 using 1;
  fin_cases i <;> rfl

set_option maxHeartbeats 800000 in
theorem InducedEdgeIntersectionSevenCycle.core_injective
    (H : Hypergraph W)
    (c : InducedEdgeIntersectionSevenCycle H) :
    Function.Injective c.core := by
  intro i j hij
  by_contra h_neq;
  
  have h_core_i : c.core i ∈ (c.edge (i - 1)).1 ∧ c.core i ∈ (c.edge i).1 := by
    exact ⟨ Classical.choose_spec ( ( edgeIntersectionGraph_adj_iff H ( c.edge ( i - 1 ) ) ( c.edge i ) ).mp ( by simpa using c.consecutive ( i - 1 ) ) |>.2 ) |>.1, c.core_mem_right i ⟩
  have h_core_j : c.core j ∈ (c.edge (j - 1)).1 ∧ c.core j ∈ (c.edge j).1 := by
    exact ⟨ by simpa using c.core_mem_left ( j - 1 ), by simpa using c.core_mem_right j ⟩;
  have := c.induced ( i - 1 ) j; simp_all +decide [ Fin.ext_iff ] ;
  have := c.induced i ( j - 1 ) ; simp_all +decide [ edgeIntersectionGraph ] ;
  by_cases hi : c.edge ( i - 1 ) = c.edge j <;> by_cases hj : c.edge i = c.edge ( j - 1 ) <;> simp_all +decide [ Set.Nonempty ];
  · have := c.injective hi; have := c.injective hj; fin_cases i <;> fin_cases j <;> trivial;
  · fin_cases i <;> fin_cases j <;> simp +decide at h_neq this ⊢;
    all_goals have := c.injective hi; simp_all +decide ;
  · have := c.injective hj; simp_all +decide [ Fin.ext_iff ] ;
    fin_cases j <;> simp_all +decide;
  · fin_cases i <;> fin_cases j <;> simp +decide at h_neq hi hj this ⊢;
    all_goals simp_all +decide

theorem InducedEdgeIntersectionSevenCycle.core_mem_iff
    (H : Hypergraph W)
    (c : InducedEdgeIntersectionSevenCycle H) (i j : Fin 7) :
    c.core j ∈ (c.edge i).1 ↔ j = i ∨ j = i + 1 := by
  constructor;
  · intro hj
    by_cases h_eq : j = i ∨ j = i + 1;
    · exact h_eq;
    · have h_adj : (edgeIntersectionGraph H).Adj (c.edge i) (c.edge j) := by
        have h_adj : (c.edge i).1 ∩ (c.edge j).1 ≠ ∅ := by
          exact Set.Nonempty.ne_empty ⟨ c.core j, hj, c.core_mem_right j ⟩;
        simp_all +decide [ Set.ext_iff, edgeIntersectionGraph ];
        exact ⟨ by intro h; have := c.injective h; aesop, Or.inl ⟨ _, h_adj.choose_spec.1, h_adj.choose_spec.2 ⟩ ⟩;
      have := c.induced i j h_adj; simp_all +decide [ Fin.ext_iff ] ;
      have h_adj : (edgeIntersectionGraph H).Adj (c.edge i) (c.edge (j - 1)) := by
        have h_adj : c.core j ∈ (c.edge i).1 ∧ c.core j ∈ (c.edge (j - 1)).1 := by
          exact ⟨ hj, by simpa using c.core_mem_left ( j - 1 ) ⟩;
        exact ⟨ by
          intro h; have := c.injective h; fin_cases i <;> fin_cases j <;> trivial;, by
          exact Or.inl ⟨ c.core j, h_adj.1, h_adj.2 ⟩ ⟩;
      fin_cases i <;> fin_cases j <;> simp +decide at this h_adj ⊢;
      all_goals have := c.induced _ _ h_adj; simp_all +decide;
  · rintro ( rfl | rfl ) <;> simp +decide [ InducedEdgeIntersectionSevenCycle.core_mem_right, InducedEdgeIntersectionSevenCycle.core_mem_left ]

theorem InducedEdgeIntersectionSevenCycle.inter_subset_core
    (H : Hypergraph W) (hlin : H.Linear)
    (c : InducedEdgeIntersectionSevenCycle H)
    {i j : Fin 7} (hij : i ≠ j) :
    (c.edge i).1 ∩ (c.edge j).1 ⊆ Set.range c.core := by
  intro x hx; by_cases h_cases : j = i + 1 ∨ i = j + 1 <;> simp_all +decide;
  · cases' h_cases with h_cases h_cases;
    · use i + 1;
      apply hlin;
      exact c.edge i |>.2;
      exact c.edge ( i + 1 ) |>.2;
      · exact fun h => by have := c.injective ( Subtype.ext h ) ; fin_cases i <;> trivial;
      · exact ⟨ c.core_mem_left i, c.core_mem_right ( i + 1 ) ⟩;
      · aesop;
    · have h_core_eq : x = c.core (j + 1) := by
        apply hlin;
        exact c.edge i |>.2;
        exact c.edge j |>.2;
        · exact fun h => hij <| c.injective <| Subtype.ext h;
        · exact ⟨ hx.1, hx.2 ⟩;
        · simp +decide [ *, InducedEdgeIntersectionSevenCycle.core_mem_left, InducedEdgeIntersectionSevenCycle.core_mem_right ];
      exact ⟨ _, h_core_eq.symm ⟩;
  · have := c.induced i j; simp_all +decide [ edgeIntersectionGraph ] ;
    exact False.elim ( this ( by intro h; have := c.injective h; fin_cases i <;> fin_cases j <;> trivial ) |>.1 ⟨ x, hx ⟩ )

noncomputable def InducedEdgeIntersectionSevenCycle.toClean
    (H : Hypergraph W) (hlin : H.Linear)
    (c : InducedEdgeIntersectionSevenCycle H) : CleanLoose7EdgeCycle H where
  core := c.core
  edge := fun i => (c.edge i).1
  core_injective := c.core_injective H
  edge_mem := fun i => (c.edge i).2
  left_mem := c.core_mem_right
  right_mem := c.core_mem_left
  core_mem_iff := c.core_mem_iff H
  inter_subset_core := fun {i j} hij =>
    InducedEdgeIntersectionSevenCycle.inter_subset_core H hlin c (i := i) (j := j) hij

noncomputable def CleanLoose7EdgeCycle.toInduced
    (H : Hypergraph W) (c : CleanLoose7EdgeCycle H) :
    InducedEdgeIntersectionSevenCycle H where
  edge := fun i => ⟨c.edge i, c.edge_mem i⟩
  injective := fun i j h => cleanEdgeCycle_edge_injective H c (Subtype.ext_iff.mp h)
  consecutive := by
    intro i
    rw [edgeIntersectionGraph_adj_iff]
    refine ⟨?_, ⟨c.core (i + 1), c.right_mem i, c.left_mem (i + 1)⟩⟩
    intro h
    have hi : i = i + 1 :=
      cleanEdgeCycle_edge_injective H c (Subtype.ext_iff.mp h)
    have hne : i ≠ i + 1 := by
      fin_cases i <;> decide
    exact hne hi
  induced := by
    intro i j hij
    rw [edgeIntersectionGraph_adj_iff] at hij
    obtain ⟨x, hxi, hxj⟩ := hij.2
    obtain ⟨k, rfl⟩ := c.inter_subset_core
      (fun h => hij.1 (congrArg (fun k => (⟨c.edge k, c.edge_mem k⟩ : H.edges)) h))
      ⟨hxi, hxj⟩
    have hi := (c.core_mem_iff i k).mp hxi
    have hj := (c.core_mem_iff j k).mp hxj
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all

end Erdos593
end

-- E5IntersectionStructure
section
namespace Erdos593

universe u

variable {W : Type u}

theorem linear_intersection_subsingleton (H : Hypergraph W) (hlin : H.Linear)
    {e f : Set W} (he : e ∈ H.edges) (hf : f ∈ H.edges) (hef : e ≠ f) :
    (e ∩ f).Subsingleton := by
  exact fun x hx y hy => by have := hlin e he f hf hef; aesop;

theorem existsUnique_common_vertex (H : Hypergraph W) (hlin : H.Linear)
    {e f : Set W} (he : e ∈ H.edges) (hf : f ∈ H.edges) (hef : e ≠ f)
    (hmeet : (e ∩ f).Nonempty) :
    ∃! x, x ∈ e ∩ f := by
  obtain ⟨ x, hx ⟩ := hmeet;
  exact ⟨ x, hx, fun y hy => by have := linear_intersection_subsingleton H hlin he hf hef; exact this hy hx ⟩

end Erdos593
end

-- E5StarDecomposition
section
namespace Erdos593

universe u

variable {W : Type u}

def edgeStar (H : Hypergraph W) (x : W) : Set H.edges :=
  {e | x ∈ e.1}

theorem unique_contact_vertex (H : Hypergraph W) (hlin : H.Linear)
    {e f : H.edges} (hadj : (edgeIntersectionGraph H).Adj e f) :
    ∃! x, x ∈ e.1 ∧ x ∈ f.1 := by
  exact existsUnique_common_vertex H hlin e.property f.property
    (fun h => hadj.1 (Subtype.ext h))
    (hadj.2.elim id (fun h => by simpa only [Set.inter_comm] using h))

noncomputable def contactVertex (H : Hypergraph W) (hlin : H.Linear)
    {e f : H.edges} (hadj : (edgeIntersectionGraph H).Adj e f) : W :=
  Classical.choose (unique_contact_vertex H hlin hadj)

def neighbourStar (H : Hypergraph W) (center : H.edges) (x : W) : Set H.edges :=
  {leaf | (edgeIntersectionGraph H).Adj center leaf ∧ leaf ∈ edgeStar H x}

end Erdos593
end

-- E5ObstructionGrid
section
open Cardinal

namespace Erdos593

universe u

variable {W : Type u}

end Erdos593
end

-- E5CountableReduction
section
open Cardinal

namespace Erdos593

universe u

variable {W : Type u}

def CleanLoose7EdgeCycle.ofEdgesSubset (H : Hypergraph W) (A : Set (Set W))
    (hA : A ⊆ H.edges) (c : CleanLoose7EdgeCycle (⟨A⟩ : Hypergraph W)) :
    CleanLoose7EdgeCycle H where
  core := c.core
  edge := c.edge
  core_injective := c.core_injective
  edge_mem := fun i => hA (c.edge_mem i)
  left_mem := c.left_mem
  right_mem := c.right_mem
  core_mem_iff := c.core_mem_iff
  inter_subset_core := c.inter_subset_core

def E5CountableEmbeddingPrinciple : Prop :=
  ∀ {W : Type u} (H : Hypergraph W) (A : Set (Set W)),
    H.IsTripleSystem → H.Linear → A.Countable → A ⊆ H.edges →
    (∀ k : ℕ, 0 < k →
      ¬ ∃ c : W → Fin k, (⟨A⟩ : Hypergraph W).ProperColoring c) →
    looseCycle7.Embeds (⟨A⟩ : Hypergraph W)

def E5CountableCleanCyclePrinciple : Prop :=
  ∀ {W : Type u} (H : Hypergraph W) (A : Set (Set W)),
    H.IsTripleSystem → H.Linear → A.Countable → A ⊆ H.edges →
    (∀ k : ℕ, 0 < k →
      ¬ ∃ c : W → Fin k, (⟨A⟩ : Hypergraph W).ProperColoring c) →
    Nonempty (CleanLoose7EdgeCycle (⟨A⟩ : Hypergraph W))

def E5CountableIntersectionCyclePrinciple : Prop :=
  ∀ {W : Type u} (H : Hypergraph W) (A : Set (Set W)),
    H.IsTripleSystem → H.Linear → A.Countable → A ⊆ H.edges →
    (∀ k : ℕ, 0 < k →
      ¬ ∃ c : W → Fin k, (⟨A⟩ : Hypergraph W).ProperColoring c) →
    Nonempty (InducedEdgeIntersectionSevenCycle (⟨A⟩ : Hypergraph W))

end Erdos593
end

-- E5FiniteBound
section
open Cardinal

namespace Erdos593

universe u

def Loose7FreeFinitelyColorable : Prop :=
  ∀ {W : Type u} (H : Hypergraph W), H.IsTripleSystem → H.Linear →
    ¬ looseCycle7.Embeds H →
    ∃ k : ℕ, 0 < k ∧ ∃ c : W → Fin k, H.ProperColoring c

def Loose7FreeUniformFiniteBound : Prop :=
  ∃ k : ℕ, 0 < k ∧ ∀ {W : Type u} (H : Hypergraph W),
    H.IsTripleSystem → H.Linear → ¬ looseCycle7.Embeds H →
    ∃ c : W → Fin k, H.ProperColoring c

end Erdos593
end

-- E5IntersectionColoring
section
open Cardinal

namespace Erdos593

universe u v

variable {W : Type u}

def EdgeIntersectionColoring (H : Hypergraph W) (C : Type v) (c : H.edges → C) : Prop :=
  ∀ ⦃e f : H.edges⦄, (edgeIntersectionGraph H).Adj e f → c e ≠ c f

def EdgeIntersectionColorable (H : Hypergraph W) (C : Type v) : Prop :=
  ∃ c : H.edges → C, EdgeIntersectionColoring H C c

noncomputable def edgeMark (H : Hypergraph W) (htri : H.IsTripleSystem) : H.edges → W :=
  fun e => Classical.choose (Set.nonempty_of_ncard_ne_zero (by
    rw [htri e.1 e.2]
    norm_num))

end Erdos593
end

-- E5HK
section
open Cardinal

namespace Erdos593

universe u

noncomputable def hkMn (n : ℕ) : FTS where
  V := Fin 3 × Fin n × Fin n
  edges := ((Finset.univ : Finset (Fin n × Fin n × Fin n)).image fun p =>
    ({(0, p.1, p.2.1), (1, p.1, p.2.2), (2, p.2.1, p.2.2)} :
      Finset (Fin 3 × Fin n × Fin n)))
  card3 := by
    intro e he
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at he
    obtain ⟨p, rfl⟩ := he
    simp +decide

theorem looseCycle7_sub_hkMn3 : looseCycle7.Sub (hkMn 3) := by
  unfold FTS.Sub;
  by_contra h;
  push_neg at h;
  exact absurd ( h ( fun (x : Fin 7 ⊕ Fin 7) => if x = Sum.inl 0 then ( 0, 0, 0 ) else if x = Sum.inl 1 then ( 1, 0, 0 ) else if x = Sum.inl 2 then ( 2, 1, 0 ) else if x = Sum.inl 3 then ( 0, 1, 1 ) else if x = Sum.inl 4 then ( 1, 1, 1 ) else if x = Sum.inl 5 then ( 2, 2, 1 ) else if x = Sum.inl 6 then ( 1, 0, 1 ) else if x = Sum.inr 0 then ( 2, 0, 0 ) else if x = Sum.inr 1 then ( 0, 0, 1 ) else if x = Sum.inr 2 then ( 1, 1, 0 ) else if x = Sum.inr 3 then ( 2, 1, 1 ) else if x = Sum.inr 4 then ( 0, 1, 2 ) else if x = Sum.inr 5 then ( 0, 0, 2 ) else ( 2, 0, 1 ) ) (by unfold Function.Injective; decide) ) (by decide)

def HKRealizes (H : Hypergraph W) (Z : Fin 3 → Fin 3 → W)
    (X Y : Fin 3 → W) : Prop :=
  Function.Injective X ∧ Function.Injective Y ∧
  (∀ i j, X i ≠ Y j) ∧
  (∀ i k l, X i ≠ Z k l) ∧ (∀ i k l, Y i ≠ Z k l) ∧
  ∀ j k, ({X j, Y k, Z j k} : Set W) ∈ H.edges

theorem hkMn3_embeds_of_realizations (H : Hypergraph W)
    (Z : Fin 3 → Fin 3 → W)
    (hZ : ∀ i j i' j', Z i j = Z i' j' → i = i' ∧ j = j')
    (X Y : Fin 3 → Fin 3 → W)
    (hreal : ∀ a, HKRealizes H Z (X a) (Y a))
    (hdisjX : ∀ a b i j, a ≠ b → X a i ≠ X b j)
    (hdisjY : ∀ a b i j, a ≠ b → Y a i ≠ Y b j)
    (hdisjXY : ∀ a b i j, a ≠ b → X a i ≠ Y b j) :
    (hkMn 3).Embeds H := by
  simp +decide [ HKRealizes ] at hreal;
  refine' ⟨ fun x => _, _, _ ⟩;
  exact if x.1 = 0 then X x.2.1 x.2.2 else if x.1 = 1 then Y x.2.1 x.2.2 else Z x.2.1 x.2.2;
  · intro x y hxy;
    rcases x with ⟨ x₁, x₂, x₃ ⟩ ; rcases y with ⟨ y₁, y₂, y₃ ⟩ ; simp +decide at hxy ⊢;
    grind;
  · intro e he
    change e ∈ Finset.image _ _ at he
    obtain ⟨⟨a, b, c⟩, -, rfl⟩ := Finset.mem_image.mp he
    change (fun x : Fin 3 × Fin 3 × Fin 3 =>
      if x.1 = 0 then X x.2.1 x.2.2 else if x.1 = 1 then Y x.2.1 x.2.2 else Z x.2.1 x.2.2) ''
      (↑({(0, a, b), (1, a, c), (2, b, c)} : Finset (Fin 3 × Fin 3 × Fin 3)) :
        Set (Fin 3 × Fin 3 × Fin 3)) ∈ H.edges
    simpa [Set.image_insert_eq, Set.image_singleton] using (hreal a).2.2.2.2.2 b c

noncomputable def hkRealizationSupport (X Y : Fin 3 → W) : Finset W := by
  classical
  exact Finset.univ.image X ∪ Finset.univ.image Y

lemma hkRealizationSupport_card_le (X Y : Fin 3 → W) :
    (hkRealizationSupport X Y).card ≤ 6 := by
  classical
  unfold hkRealizationSupport
  refine (Finset.card_union_le _ _).trans ?_
  have hx : (Finset.univ.image X).card ≤ 3 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (Finset.card_image_le (f := X) (s := (Finset.univ : Finset (Fin 3))))
  have hy : (Finset.univ.image Y).card ≤ 3 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (Finset.card_image_le (f := Y) (s := (Finset.univ : Finset (Fin 3))))
  exact Nat.add_le_add hx hy

lemma hk_support_disjoint_cross
    (X Y X' Y' : Fin 3 → W)
    (hd : Disjoint (hkRealizationSupport X Y) (hkRealizationSupport X' Y')) :
    (∀ i j, X i ≠ X' j) ∧ (∀ i j, Y i ≠ Y' j) ∧
      (∀ i j, X i ≠ Y' j) ∧ (∀ i j, X' i ≠ Y j) := by
  simp_all +decide [ Finset.disjoint_left, hkRealizationSupport ];
  exact ⟨ fun i j => fun h => hd ( Or.inl ⟨ i, rfl ⟩ ) |>.1 j h.symm, fun i j => fun h => hd ( Or.inr ⟨ i, rfl ⟩ ) |>.2 j h.symm, fun i j => fun h => hd ( Or.inl ⟨ i, rfl ⟩ ) |>.2 j h.symm ⟩

lemma hk_support_disjoint_of_avoids
    (X Y X' Y' : Fin 3 → W)
    (hX : ∀ i, X' i ∉ hkRealizationSupport X Y)
    (hY : ∀ i, Y' i ∉ hkRealizationSupport X Y) :
    Disjoint (hkRealizationSupport X Y) (hkRealizationSupport X' Y') := by
  simp_all +decide [ Finset.disjoint_left, hkRealizationSupport ];
  grind

lemma hk_avoid_support (H : Hypergraph W)
    (Z : Fin 3 → Fin 3 → W)
    (havoid : ∀ S : Finset W, S.card ≤ 18 →
      ∃ X Y : Fin 3 → W, HKRealizes H Z X Y ∧
        (∀ i, X i ∉ S) ∧ (∀ i, Y i ∉ S))
    (X0 Y0 : Fin 3 → W) :
    ∃ X1 Y1 : Fin 3 → W, HKRealizes H Z X1 Y1 ∧
      Disjoint (hkRealizationSupport X0 Y0) (hkRealizationSupport X1 Y1) := by
  obtain ⟨ X1, Y1, h1, h2, h3 ⟩ := havoid ( hkRealizationSupport X0 Y0 ) ( by exact le_trans ( hkRealizationSupport_card_le X0 Y0 ) ( by decide ) );
  exact ⟨ X1, Y1, h1, hk_support_disjoint_of_avoids X0 Y0 X1 Y1 h2 h3 ⟩

lemma hk_avoid_two_supports (H : Hypergraph W)
    (Z : Fin 3 → Fin 3 → W)
    (havoid : ∀ S : Finset W, S.card ≤ 18 →
      ∃ X Y : Fin 3 → W, HKRealizes H Z X Y ∧
        (∀ i, X i ∉ S) ∧ (∀ i, Y i ∉ S))
    (X0 Y0 X1 Y1 : Fin 3 → W) :
    ∃ X2 Y2 : Fin 3 → W, HKRealizes H Z X2 Y2 ∧
      Disjoint (hkRealizationSupport X0 Y0) (hkRealizationSupport X2 Y2) ∧
      Disjoint (hkRealizationSupport X1 Y1) (hkRealizationSupport X2 Y2) := by
  classical
  let S0 := hkRealizationSupport X0 Y0
  let S1 := hkRealizationSupport X1 Y1
  have hc : (S0 ∪ S1).card ≤ 18 := by
    calc
      (S0 ∪ S1).card ≤ S0.card + S1.card := Finset.card_union_le _ _
      _ ≤ 6 + 6 := Nat.add_le_add (hkRealizationSupport_card_le X0 Y0)
        (hkRealizationSupport_card_le X1 Y1)
      _ ≤ 18 := by omega
  obtain ⟨X2, Y2, hr, hx, hy⟩ := havoid (S0 ∪ S1) hc
  have hx0 : ∀ i, X2 i ∉ S0 := by
    intro i hi
    exact hx i (Finset.mem_union.mpr (Or.inl hi))
  have hy0 : ∀ i, Y2 i ∉ S0 := by
    intro i hi
    exact hy i (Finset.mem_union.mpr (Or.inl hi))
  have hx1 : ∀ i, X2 i ∉ S1 := by
    intro i hi
    exact hx i (Finset.mem_union.mpr (Or.inr hi))
  have hy1 : ∀ i, Y2 i ∉ S1 := by
    intro i hi
    exact hy i (Finset.mem_union.mpr (Or.inr hi))
  exact ⟨X2, Y2, hr,
    hk_support_disjoint_of_avoids X0 Y0 X2 Y2 hx0 hy0,
    hk_support_disjoint_of_avoids X1 Y1 X2 Y2 hx1 hy1⟩

lemma hk_select_three (H : Hypergraph W)
    (Z : Fin 3 → Fin 3 → W)
    (havoid : ∀ S : Finset W, S.card ≤ 18 →
      ∃ X Y : Fin 3 → W, HKRealizes H Z X Y ∧
        (∀ i, X i ∉ S) ∧ (∀ i, Y i ∉ S)) :
    ∃ X0 Y0 X1 Y1 X2 Y2 : Fin 3 → W,
      HKRealizes H Z X0 Y0 ∧ HKRealizes H Z X1 Y1 ∧ HKRealizes H Z X2 Y2 ∧
      Disjoint (hkRealizationSupport X0 Y0) (hkRealizationSupport X1 Y1) ∧
      Disjoint (hkRealizationSupport X0 Y0) (hkRealizationSupport X2 Y2) ∧
      Disjoint (hkRealizationSupport X1 Y1) (hkRealizationSupport X2 Y2) := by
  obtain ⟨X0, Y0, hR0⟩ : ∃ X0 Y0 : Fin 3 → W, HKRealizes H Z X0 Y0 := by
    exact Exists.elim ( havoid ∅ ( by simp +decide ) ) fun X hX => Exists.elim hX fun Y hY => ⟨ X, Y, hY.1 ⟩;
  obtain ⟨ X1, Y1, hR1, h01 ⟩ := hk_avoid_support H Z havoid X0 Y0;
  obtain ⟨ X2, Y2, hR2, h02, h12 ⟩ := hk_avoid_two_supports H Z havoid X0 Y0 X1 Y1;
  exact ⟨ X0, Y0, X1, Y1, X2, Y2, hR0, hR1, hR2, h01, h02, h12 ⟩

lemma hk_three_disjoint_realizations (H : Hypergraph W)
    (Z : Fin 3 → Fin 3 → W)
    (havoid : ∀ S : Finset W, S.card ≤ 18 →
      ∃ X Y : Fin 3 → W, HKRealizes H Z X Y ∧
        (∀ i, X i ∉ S) ∧ (∀ i, Y i ∉ S)) :
    ∃ X Y : Fin 3 → Fin 3 → W,
      (∀ a, HKRealizes H Z (X a) (Y a)) ∧
      ∀ a b, a ≠ b →
        Disjoint (hkRealizationSupport (X a) (Y a))
          (hkRealizationSupport (X b) (Y b)) := by
  obtain ⟨ X0, Y0, X1, Y1, X2, Y2, hR0, hR1, hR2, d01, d02, d12 ⟩ := hk_select_three H Z havoid;
  refine' ⟨ fun a => if a = 0 then X0 else if a = 1 then X1 else X2, fun a => if a = 0 then Y0 else if a = 1 then Y1 else Y2, _, _ ⟩ <;> simp +decide [ Fin.forall_fin_succ ];
  · exact ⟨ hR0, hR1, hR2 ⟩;
  · exact ⟨ ⟨ d01, d02 ⟩, ⟨ d01.symm, d12 ⟩, d02.symm, d12.symm ⟩

theorem hkMn3_embeds_of_avoidance (H : Hypergraph W)
    (Z : Fin 3 → Fin 3 → W)
    (hZ : ∀ i j i' j', Z i j = Z i' j' → i = i' ∧ j = j')
    (havoid : ∀ S : Finset W, S.card ≤ 18 →
      ∃ X Y : Fin 3 → W, HKRealizes H Z X Y ∧
        (∀ i, X i ∉ S) ∧ (∀ i, Y i ∉ S)) :
    (hkMn 3).Embeds H := by
  convert hkMn3_embeds_of_realizations H Z hZ _ _ _ _ _ _ using 1;
  exact fun a i => ( hk_three_disjoint_realizations H Z havoid |> Classical.choose ) a i;
  exact fun a i => ( hk_three_disjoint_realizations H Z havoid |> Classical.choose_spec |> Classical.choose ) a i;
  · exact Classical.choose_spec ( hk_three_disjoint_realizations H Z havoid ) |> Classical.choose_spec |> And.left;
  · intro a b i j hab;
    have := Classical.choose_spec ( hk_three_disjoint_realizations H Z havoid ) |> Classical.choose_spec;
    exact hk_support_disjoint_cross _ _ _ _ ( this.2 a b hab ) |>.1 i j;
  · intro a b i j hab;
    have := Classical.choose_spec ( hk_three_disjoint_realizations H Z havoid ) |> Classical.choose_spec;
    have := hk_support_disjoint_cross _ _ _ _ ( this.2 a b hab );
    grind;
  · intro a b i j hab
    generalize_proofs at *;
    rename_i h₁ h₂;
    have := Classical.choose_spec h₂ |>.2 a b hab; simp_all +decide [ Finset.disjoint_left, hkRealizationSupport ] ;
    exact fun h => this ( Or.inl ⟨ i, rfl ⟩ ) |>.2 j h.symm

def HKBlocks (H : Hypergraph W) (Z : Fin 3 → Fin 3 → W) (S : Finset W) : Prop :=
  S.card ≤ 18 ∧ ∀ X Y : Fin 3 → W, HKRealizes H Z X Y →
    (∃ i, X i ∈ S) ∨ ∃ i, Y i ∈ S

noncomputable def hkBlocker (H : Hypergraph W) (Z : Fin 3 → Fin 3 → W) : Finset W := by
  classical
  exact if h : ∃ S : Finset W, HKBlocks H Z S then h.choose else ∅

lemma hkBlocker_spec (H : Hypergraph W) (Z : Fin 3 → Fin 3 → W)
    (h : ∃ S : Finset W, HKBlocks H Z S) :
    HKBlocks H Z (hkBlocker H Z) := by
  have := Classical.choose_spec h;
  unfold hkBlocker; aesop;

def HKCloseStep (H : Hypergraph W) (X : Set W) : Set W :=
  DCloseStep H 2 X ∪
    {v | ∃ Z : Fin 3 → Fin 3 → W, (∀ i j, Z i j ∈ X) ∧ v ∈ hkBlocker H Z}

def HKCloseIter (H : Hypergraph W) (X : Set W) : ℕ → Set W
  | 0 => X
  | k + 1 => HKCloseStep H (HKCloseIter H X k)

def HKcl (H : Hypergraph W) (X : Set W) : Set W := ⋃ k, HKCloseIter H X k

lemma subset_HKCloseIter (H : Hypergraph W) (X : Set W) (k : ℕ) :
    X ⊆ HKCloseIter H X k := by
  induction' k with k ih <;> simp_all +decide [ Set.subset_def, HKCloseIter ];
  exact fun x hx => Set.mem_union_left _ ( Set.mem_union_left _ ( ih x hx ) )

lemma HKCloseIter_mono_index (H : Hypergraph W) (X : Set W) {k l : ℕ}
    (h : k ≤ l) : HKCloseIter H X k ⊆ HKCloseIter H X l := by
  refine' Nat.le_induction _ _ l h <;> intro l _ <;> simp_all +decide [ Set.subset_def, HKCloseIter ];
  exact fun h x hx => Set.mem_union_left _ ( Set.mem_union_left _ ( h x hx ) )

lemma subset_HKcl (H : Hypergraph W) (X : Set W) : X ⊆ HKcl H X := by
  exact Set.subset_iUnion ( fun k => HKCloseIter H X k ) 0 |> Set.Subset.trans ( subset_HKCloseIter H X 0 )

lemma HKcl_mono (H : Hypergraph W) {X Y : Set W} (h : X ⊆ Y) :
    HKcl H X ⊆ HKcl H Y := by
  
  have h_ind : ∀ k, HKCloseIter H X k ⊆ HKCloseIter H Y k := by
    intro k;
    induction' k with k ih;
    · exact h;
    · refine' Set.union_subset_union ( Set.union_subset_union _ _ ) _;
      · exact ih;
      · exact fun v hv => by obtain ⟨ x, hx, y, hy, hxy, hv ⟩ := hv; exact ⟨ x, ih hx, y, ih hy, hxy, hv ⟩ ;
      · exact fun v hv => by obtain ⟨ Z, hZ₁, hZ₂ ⟩ := hv; exact ⟨ Z, fun i j => ih ( hZ₁ i j ), hZ₂ ⟩ ;
  exact Set.iUnion_mono h_ind

lemma HKcl_pairClosed (H : Hypergraph W) (X : Set W) :
    DClosed H 2 (HKcl H X) := by
  intro x hx; simp_all +decide [ DClosed ] ;
  intro y hy hxy; simp_all +decide [ Set.subset_def, HKcl ] ;
  obtain ⟨ kx, hkx ⟩ := hx; obtain ⟨ ky, hky ⟩ := hy; use fun z hz => ⟨ kx + ky + 1, ?_ ⟩ ; simp_all +decide [ Set.subset_def, HKCloseIter ] ;
  refine' Set.mem_union_left _ ( Set.mem_union_right _ _ );
  exact ⟨ x, HKCloseIter_mono_index H X ( by linarith ) hkx, y, HKCloseIter_mono_index H X ( by linarith ) hky, hxy, hz ⟩

lemma HKcl_blockerClosed (H : Hypergraph W) (X : Set W)
    (Z : Fin 3 → Fin 3 → W) (hZ : ∀ i j, Z i j ∈ HKcl H X) :
    (hkBlocker H Z : Set W) ⊆ HKcl H X := by
  by_contra h_false;
  obtain ⟨ v, hv ⟩ := Set.not_subset.mp h_false;
  obtain ⟨ k, hk ⟩ : ∃ k, ∀ i j, Z i j ∈ HKCloseIter H X k := by
    choose k hk using fun i j => Set.mem_iUnion.mp ( hZ i j );
    exact ⟨ Finset.univ.sup ( fun p : Fin 3 × Fin 3 => k p.1 p.2 ), fun i j => HKCloseIter_mono_index H X ( Finset.le_sup ( f := fun p : Fin 3 × Fin 3 => k p.1 p.2 ) ( Finset.mem_univ ( i, j ) ) ) ( hk i j ) ⟩;
  refine' hv.2 ( Set.mem_iUnion.2 ⟨ k + 1, Set.mem_union_right _ _ ⟩ );
  exact ⟨ Z, hk, hv.1 ⟩

lemma HKCloseStep_card_le (H : Hypergraph W) (htri : H.IsTripleSystem)
    (X : Set W) : #(HKCloseStep H X) ≤ #X + ℵ₀ := by
  let K : Cardinal := #X + ℵ₀
  have hK : ℵ₀ ≤ K := le_add_left le_rfl
  have hX : #X ≤ K := le_add_right le_rfl
  let B := fun Z : Fin 3 → Fin 3 → X => (hkBlocker H (fun i j => Z i j) : Set W)
  have hB : ∀ Z, #(B Z) ≤ 18 := by
    intro Z
    by_cases h : ∃ S : Finset W, HKBlocks H (fun i j => (Z i j : W)) S
    · simpa [B, hkBlocker, h] using h.choose_spec.1
    · simp [B, hkBlocker, h]
  have hI : #(Fin 3 → Fin 3 → X) ≤ K := by
    simp only [Cardinal.mk_arrow, Cardinal.mk_fin, Cardinal.lift_uzero, Cardinal.lift_natCast,
      Cardinal.power_natCast]
    calc
      (#X ^ 3) ^ 3 ≤ (K ^ 3) ^ 3 := by gcongr
      _ = K := by simp only [Cardinal.power_nat_eq hK (by decide : 1 ≤ 3)]
  have hUnion : #(⋃ Z, B Z) ≤ K := by
    refine (Cardinal.mk_iUnion_le B).trans ?_
    calc
      _ ≤ K * K := mul_le_mul' hI (ciSup_le' fun Z =>
        (hB Z).trans ((Cardinal.nat_lt_aleph0 18).le.trans hK))
      _ = K := Cardinal.mul_eq_self hK
  have hEq : HKCloseStep H X = DCloseStep H 2 X ∪ ⋃ Z, B Z := by
    ext v
    simp only [HKCloseStep, Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion]
    apply or_congr_right
    constructor
    · rintro ⟨Z, hZ, hv⟩
      exact ⟨fun i j => ⟨Z i j, hZ i j⟩, hv⟩
    · rintro ⟨Z, hv⟩
      exact ⟨fun i j => Z i j, fun i j => (Z i j).property, hv⟩
  rw [hEq]
  exact (Cardinal.mk_union_le _ _).trans ((add_le_add (DCloseStep_card_le H htri 2 X) hUnion).trans_eq
    (Cardinal.add_eq_left hK le_rfl))

lemma HKcl_card_le (H : Hypergraph W) (htri : H.IsTripleSystem) (X : Set W) :
    #(HKcl H X) ≤ #X + ℵ₀ := by
  let K : Cardinal := #X + ℵ₀
  have hK : ℵ₀ ≤ K := le_add_left le_rfl
  have hIter : ∀ n, #(HKCloseIter H X n) ≤ K := by
    intro n
    induction n with
    | zero => exact le_add_right le_rfl
    | succ n ih =>
      calc
        #(HKCloseIter H X (n + 1)) ≤ #(HKCloseIter H X n) + ℵ₀ := HKCloseStep_card_le H htri _
        _ ≤ K + ℵ₀ := add_le_add ih le_rfl
        _ = K := Cardinal.add_eq_left hK hK
  unfold HKcl
  have hUnion := Cardinal.mk_iUnion_le_lift (HKCloseIter H X)
  simp only [Cardinal.lift_uzero, Cardinal.mk_nat, Cardinal.lift_aleph0] at hUnion
  refine hUnion.trans ?_
  calc
    _ ≤ K * K := mul_le_mul' hK (ciSup_le' hIter)
    _ = K := Cardinal.mul_eq_self hK

structure HKFiltration (H : Hypergraph W) where
  Idx : Type u
  linearOrder : LinearOrder Idx
  wellFounded : WellFoundedLT Idx
  rank : W → Idx
  levelColorable : ∀ a, ∃ c : W → ℕ,
    ∀ e ∈ H.edges, e ⊆ {v | rank v = a} →
      ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y
  noUniqueTop : ∀ (x y z : W), rank x < rank z → rank y < rank z → x ≠ y →
    ∀ e ∈ H.edges, x ∈ e → y ∈ e → z ∈ e → False
  reflectBlocker : ∀ (a : Idx) (Z : Fin 3 → Fin 3 → W),
    (∀ i j, rank (Z i j) < a) →
    (∃ S : Finset W, HKBlocks H Z S) →
    ∃ S : Finset W, HKBlocks H Z S ∧ ∀ x ∈ S, rank x < a

lemma Hsub_linear_of_linear (H : Hypergraph W) (hlin : H.Linear) (S : Set W) :
    (Hsub H S).Linear := by
  
  intro e' f' h_inter
  simp_all +decide [ Hsub, Hypergraph.Linear ];
  intro g' hne;
  contrapose! hlin;
  refine' ⟨ _, f', _, g', _, _ ⟩;
  · exact fun h => hne <| Set.ext fun x => by simpa using Set.ext_iff.mp h x;
  · obtain ⟨ x, hx, y, hy, hxy ⟩ := hlin; use x, by aesop, y, by aesop;
    exact fun h => hxy <| Subtype.ext h

lemma hkMn_embeds_of_Hsub (H : Hypergraph W) (S : Set W)
    (h : (hkMn 3).Embeds (Hsub H S)) : (hkMn 3).Embeds H := by
  obtain ⟨ f, hf₁, hf₂ ⟩ := h;
  refine' ⟨ fun x => f x, _, _ ⟩;
  · exact Subtype.coe_injective.comp hf₁;
  · intro e he; specialize hf₂ e he; simp_all +decide [ Set.ext_iff, Hsub ] ;
    convert hf₂ using 1;
    ext; simp [Set.mem_image]

lemma hk_level_colorable (H : Hypergraph W) (htri : H.IsTripleSystem)
    (hlin : H.Linear) (hfree : ¬ (hkMn 3).Embeds H)
    (minimal : ∀ (W' : Type u) (H' : Hypergraph W'), #W' < #W →
      H'.IsTripleSystem → H'.Linear → ¬ (hkMn 3).Embeds H' →
      H'.ColorableBy ℵ₀)
    (S : Set W) (hS : #S < #W) :
    ∃ c : W → ℕ, ∀ e ∈ H.edges, e ⊆ S →
      ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y := by
  classical
  have htriS : (Hsub H S).IsTripleSystem := Hsub_isTripleSystem H htri S
  have hlinS : (Hsub H S).Linear := Hsub_linear_of_linear H hlin S
  have hfreeS : ¬ (hkMn 3).Embeds (Hsub H S) :=
    fun h => hfree (hkMn_embeds_of_Hsub H S h)
  obtain ⟨c, hc⟩ := minimal (↑S) (Hsub H S) hS htriS hlinS hfreeS
  have hcnt : Countable (ℵ₀ : Cardinal.{u}).out :=
    Cardinal.mk_le_aleph0_iff.mp (le_of_eq (Cardinal.mk_out _))
  obtain ⟨g, hg⟩ : ∃ g : (ℵ₀ : Cardinal.{u}).out → ℕ, Function.Injective g :=
    ⟨_, (exists_injective_nat _).choose_spec⟩
  set d : W → ℕ := fun v => if h : v ∈ S then g (c ⟨v, h⟩) else 0 with hd
  have hval : ∀ a : ↑S, d (a : W) = g (c a) := by
    intro a
    simp only [hd, dif_pos a.2, Subtype.coe_eta]
  refine ⟨d, fun e he hsub => ?_⟩
  obtain ⟨s, hsimg, hsedge⟩ := Hsub_edge_of_subset H S e he hsub
  obtain ⟨x, hx, y, hy, hxy⟩ := hc s hsedge
  refine ⟨(x : W), by rw [← hsimg]; exact ⟨x, hx, rfl⟩,
    (y : W), by rw [← hsimg]; exact ⟨y, hy, rfl⟩, ?_⟩
  rw [hval x, hval y]
  exact fun h => hxy (hg h)

lemma linear_not_deltaRoot_two (H : Hypergraph W) (hlin : H.Linear)
    (x y : W) (hxy : x ≠ y) : ¬ IsDeltaRoot H 2 ({x, y} : Set W) := by
  rintro ⟨D, hDH, hcard, hroot, hinter⟩
  have hcard' : (2 : Cardinal) ≤ #D := by exact_mod_cast hcard
  rw [Cardinal.two_le_iff] at hcard'
  obtain ⟨e₁, e₂, hne⟩ := hcard'
  have hs := hlin e₁ (hDH e₁.2) e₂ (hDH e₂.2)
    (fun h => hne (Subtype.ext h))
  have hx : x ∈ (e₁.1 ∩ e₂.1) :=
    ⟨hroot e₁ e₁.2 (by simp), hroot e₂ e₂.2 (by simp)⟩
  have hy : y ∈ (e₁.1 ∩ e₂.1) :=
    ⟨hroot e₁ e₁.2 (by simp), hroot e₂ e₂.2 (by simp)⟩
  exact hxy (hs hx hy)

lemma HKpairClosed_biUnion_lt {σ : Type u} [LinearOrder σ]
    (H : Hypergraph W) (M : σ → Set W) (hmono : Monotone M)
    (hclosed : ∀ a, DClosed H 2 (M a)) (a : σ) :
    DClosed H 2 (⋃ b ∈ {b | b < a}, M b) := by
  intro x hx y hy hxy
  simp only [Set.mem_iUnion] at hx hy ⊢
  obtain ⟨i, hia, hxM⟩ := hx
  obtain ⟨j, hja, hyM⟩ := hy
  intro v hv
  refine Set.mem_iUnion₂.mpr ⟨max i j, max_lt hia hja, ?_⟩
  exact hclosed (max i j) x (hmono (le_max_left _ _) hxM)
    y (hmono (le_max_right _ _) hyM) hxy hv

theorem exists_hk_filtration (H : Hypergraph W)
    (htri : H.IsTripleSystem) (hlin : H.Linear)
    (huc : H.UncountablyChromatic) (hfree : ¬ (hkMn 3).Embeds H)
    (minimal : ∀ (W' : Type u) (H' : Hypergraph W'), #W' < #W →
      H'.IsTripleSystem → H'.Linear → ¬ (hkMn 3).Embeds H' →
      H'.ColorableBy ℵ₀) :
    Nonempty (HKFiltration.{u, u} H) := by
  classical
  have hbig : ℵ₀ < #W := by
    by_contra hle
    exact huc (tripleSystem_colorable_of_le_aleph0 H htri (not_lt.mp hle))
  let Idx := (#W).ord.ToType
  let e : Idx ≃ W := Classical.choice (Cardinal.eq.1 (by simp [Idx]))
  let M : Idx → Set W := fun a => HKcl H (e '' {b | b ≤ a})
  have hMmono : Monotone M := by
    intro a b hab
    apply HKcl_mono
    exact Set.image_mono (fun x hx => le_trans hx hab)
  have hMclosed : ∀ a, DClosed H 2 (M a) := fun a => HKcl_pairClosed H _
  have hMblock : ∀ a Z, (∀ i j, Z i j ∈ M a) →
      (hkBlocker H Z : Set W) ⊆ M a := by
    intro a Z hZ
    exact HKcl_blockerClosed H _ Z hZ
  have hMsmall : ∀ a, #(M a) < #W := by
    intro a
    have himg : #(e '' {b | b ≤ a}) ≤ Cardinal.mk (Set.Iic a) :=
      Cardinal.mk_image_le.trans (by simp [Set.Iic_def])
    have hiio : Cardinal.mk (Set.Iio a) < #W := by
      convert Cardinal.mk_Iio_ord_toType a using 1
    have hiic : Cardinal.mk (Set.Iic a) < #W := by
      have heq : Cardinal.mk (Set.Iic a) = Cardinal.mk (Set.Iio a) + 1 := by
        rw [← Cardinal.mk_singleton (a : Idx), ← Cardinal.mk_union_of_disjoint]
        · congr with x; simp [le_iff_lt_or_eq, eq_comm]
        · exact Set.disjoint_left.mpr (by intro x hx hx'; exact (ne_of_lt hx) (Set.mem_singleton_iff.mp hx'))
      rw [heq]
      exact Cardinal.add_lt_of_lt (le_of_lt hbig) hiio
        (lt_of_le_of_lt (Cardinal.nat_lt_aleph0 1 |>.le) hbig)
    refine lt_of_le_of_lt (HKcl_card_le H htri _) ?_
    refine lt_of_le_of_lt (add_le_add himg le_rfl) ?_
    exact Cardinal.add_lt_of_lt (le_of_lt hbig) hiic hbig
  have hcover : ∀ x, x ∈ M (e.symm x) := by
    intro x
    apply subset_HKcl H _
    exact ⟨e.symm x, by simp, by simp⟩
  obtain ⟨rank, hrank⟩ : ∃ rank : W → Idx,
      ∀ x, x ∈ M (rank x) ∧ ∀ b, b < rank x → x ∉ M b := by
    have hwf : WellFounded (fun x y : Idx => x < y) := wellFounded_lt
    have hleast : ∀ x, ∃ a, x ∈ M a ∧ ∀ b, b < a → x ∉ M b := by
      intro x
      have hm := hwf.has_min {a | x ∈ M a} ⟨e.symm x, hcover x⟩
      exact ⟨hm.choose, hm.choose_spec.1,
        fun b hb hbM => hm.choose_spec.2 b hbM hb⟩
    exact ⟨fun x => (hleast x).choose, fun x => (hleast x).choose_spec⟩
  letI : LinearOrder Idx := inferInstance
  letI : WellFoundedLT Idx := inferInstance
  refine ⟨⟨Idx, inferInstance, inferInstance, rank, ?_, ?_, ?_⟩⟩
  · intro a
    have hsub : {v | rank v = a} ⊆ M a := by
      intro v hv
      rw [← hv]
      exact (hrank v).1
    apply hk_level_colorable H htri hlin hfree minimal
    exact lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset hsub) (hMsmall a)
  · intro x y z hxz hyz hxy ed hed hxe hye hze
    let U := ⋃ b ∈ {b : Idx | b < rank z}, M b
    have hxU : x ∈ U := Set.mem_iUnion₂.mpr ⟨rank x, hxz, (hrank x).1⟩
    have hyU : y ∈ U := Set.mem_iUnion₂.mpr ⟨rank y, hyz, (hrank y).1⟩
    have hzU : z ∉ U := by
      intro hz
      obtain ⟨b, hb, hzb⟩ := Set.mem_iUnion₂.mp hz
      exact (hrank z).2 b hb hzb
    have hclosedU : DClosed H 2 U :=
      HKpairClosed_biUnion_lt H M hMmono hMclosed (rank z)
    have hxz' : x ≠ z := fun h => hxz.ne (h ▸ rfl)
    have hyz' : y ≠ z := fun h => hyz.ne (h ▸ rfl)
    exact claim22_abstract H htri 2 U hclosedU x y z hxU hyU hzU hxy
      hxz' hyz' ed hed hxe hye hze (linear_not_deltaRoot_two H hlin x y hxy)
  · intro a Z hZa hblock
    choose k hk using fun i j => Set.mem_iUnion₂.mp
      (show Z i j ∈ (⋃ b ∈ {b : Idx | b < a}, M b) from
        Set.mem_iUnion₂.mpr ⟨rank (Z i j), hZa i j, (hrank (Z i j)).1⟩)
    let K : Finset Idx := Finset.univ.image (fun p : Fin 3 × Fin 3 => k p.1 p.2)
    have hK : K.Nonempty := ⟨k 0 0, by simp [K]⟩
    let b : Idx := K.max' hK
    have hbmem : b ∈ K := K.max'_mem hK
    obtain ⟨p, -, hbp⟩ := Finset.mem_image.mp hbmem
    have hba : b < a := by simpa [b, ← hbp] using (hk p.1 p.2).1
    have hkb : ∀ i j, k i j ≤ b := by
      intro i j
      exact Finset.le_max' K (k i j) (by simp [K])
    have hZM : ∀ i j, Z i j ∈ M b := by
      intro i j
      exact hMmono (hkb i j) (hk i j).2
    refine ⟨hkBlocker H Z, hkBlocker_spec H Z hblock, ?_⟩
    intro x hx
    have hxb : x ∈ M b := hMblock b Z hZM hx
    have hrle : rank x ≤ b := by
      by_contra hn
      exact (hrank x).2 b (lt_of_not_ge hn) hxb
    exact lt_of_le_of_lt hrle hba

def hkLinkGraph (H : Hypergraph W) (F : HKFiltration H) (a : F.Idx) :
    SimpleGraph W := by
  letI := F.linearOrder
  exact SimpleGraph.fromRel (fun x y =>
    F.rank x = a ∧ F.rank y = a ∧ ∃ z, F.rank z < a ∧
      ({x, y, z} : Set W) ∈ H.edges)

lemma hk_edge_flat_or_link (H : Hypergraph W) (htri : H.IsTripleSystem)
    (F : HKFiltration H) (e : Set W) (he : e ∈ H.edges) :
    (∃ a, ∀ v ∈ e, F.rank v = a) ∨
      ∃ a x y, x ∈ e ∧ y ∈ e ∧ F.rank x = a ∧ F.rank y = a ∧
        (hkLinkGraph H F a).Adj x y := by
  letI := F.linearOrder
  by_cases hflat : ∃ a, ∀ v ∈ e, F.rank v = a
  · exact Or.inl hflat
  right
  obtain ⟨p, q, r, hpq, hpr, hqr, hedge⟩ := Set.ncard_eq_three.mp (htri e he)
  have hnomax :
      ¬ (F.rank p > F.rank q ∧ F.rank p > F.rank r) ∧
      ¬ (F.rank q > F.rank p ∧ F.rank q > F.rank r) ∧
      ¬ (F.rank r > F.rank p ∧ F.rank r > F.rank q) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨hpq', hpr'⟩
      exact F.noUniqueTop q r p hpq' hpr' hqr e he
        (by simp [hedge]) (by simp [hedge]) (by simp [hedge])
    · rintro ⟨hqp', hqr'⟩
      exact F.noUniqueTop p r q hqp' hqr' hpr e he
        (by simp [hedge]) (by simp [hedge]) (by simp [hedge])
    · rintro ⟨hrp', hrq'⟩
      exact F.noUniqueTop p q r hrp' hrq' hpq e he
        (by simp [hedge]) (by simp [hedge]) (by simp [hedge])
  have hpairs :
      (F.rank p = F.rank q ∧ F.rank r < F.rank p) ∨
      (F.rank p = F.rank r ∧ F.rank q < F.rank p) ∨
      (F.rank q = F.rank r ∧ F.rank p < F.rank q) := by
    have hnall : ¬ (F.rank p = F.rank q ∧ F.rank q = F.rank r) := by
      intro hall
      apply hflat
      refine ⟨F.rank p, ?_⟩
      intro v hv
      rw [hedge] at hv
      rcases hv with (rfl | rfl | rfl)
      · rfl
      · exact hall.1.symm
      · exact (hall.1.trans hall.2).symm
    grind
  rcases hpairs with hp | hp | hp
  · refine ⟨F.rank p, p, q, by simp [hedge], by simp [hedge], rfl, hp.1.symm, ?_⟩
    rw [hkLinkGraph, SimpleGraph.fromRel_adj]
    exact ⟨hpq, Or.inl ⟨rfl, hp.1.symm, r, hp.2,
      by simpa [hedge] using he⟩⟩
  · refine ⟨F.rank p, p, r, by simp [hedge], by simp [hedge], rfl, hp.1.symm, ?_⟩
    rw [hkLinkGraph, SimpleGraph.fromRel_adj]
    exact ⟨hpr, Or.inl ⟨rfl, hp.1.symm, q, hp.2,
      by simpa [hedge, Set.pair_comm] using he⟩⟩
  · refine ⟨F.rank q, q, r, by simp [hedge], by simp [hedge], rfl, hp.1.symm, ?_⟩
    rw [hkLinkGraph, SimpleGraph.fromRel_adj]
    exact ⟨hqr, Or.inl ⟨rfl, hp.1.symm, p, hp.2,
      by
        convert he using 1
        ext v
        simp [hedge, or_comm, or_left_comm, or_assoc]⟩⟩

lemma exists_uncountable_hkLinkGraph (H : Hypergraph W)
    (htri : H.IsTripleSystem) (huc : H.UncountablyChromatic)
    (F : HKFiltration H) :
    ∃ a : F.Idx, ¬ (SimpleGraph.toHG (hkLinkGraph H F a)).ColorableBy ℵ₀ := by
  letI := F.linearOrder
  by_contra hall
  push_neg at hall
  choose dlevel hdlevel using F.levelColorable
  have hflat :
      (⟨{e | e ∈ H.edges ∧ ∃ a, ∀ v ∈ e, F.rank v = a}⟩ : Hypergraph W).ColorableBy ℵ₀ := by
    apply colorable_combine F.rank _ dlevel
    rintro e ⟨he, a, ha⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := hdlevel a e he (fun v hv => ha v hv)
    exact ⟨a, x, hx, y, hy, ha x hx, ha y hy, hxy⟩
  have hlinkcols : ∀ a : F.Idx, ∃ c : W → ℕ,
      ∀ x y, (hkLinkGraph H F a).Adj x y → c x ≠ c y :=
    fun a => (gCountColorable_iff_colorableBy _).2 (hall a)
  choose dlink hdlink using hlinkcols
  have hnonflat :
      (⟨H.edges \ {e | e ∈ H.edges ∧ ∃ a, ∀ v ∈ e, F.rank v = a}⟩ :
        Hypergraph W).ColorableBy ℵ₀ := by
    apply colorable_combine F.rank _ dlink
    rintro e ⟨he, hn⟩
    rcases hk_edge_flat_or_link H htri F e he with hf | ⟨a,x,y,hx,hy,hrx,hry,hadj⟩
    · exact False.elim (hn ⟨he, hf⟩)
    · exact ⟨a, x, hx, y, hy, hrx, hry, hdlink a x y hadj⟩
  have hu := colorableBy_aleph0_union
    {e | e ∈ H.edges ∧ ∃ a, ∀ v ∈ e, F.rank v = a}
    (H.edges \ {e | e ∈ H.edges ∧ ∃ a, ∀ v ∈ e, F.rank v = a})
    hflat hnonflat
  have hcov : {e | e ∈ H.edges ∧ ∃ a, ∀ v ∈ e, F.rank v = a} ∪
      (H.edges \ {e | e ∈ H.edges ∧ ∃ a, ∀ v ∈ e, F.rank v = a}) = H.edges := by
    rw [Set.union_diff_cancel]
    intro e he
    exact he.1
  rw [hcov] at hu
  exact huc hu

lemma hk_link_private_unique_row (H : Hypergraph W) (htri : H.IsTripleSystem)
    (hlin : H.Linear) {a b₁ b₂ z : W} (hab₁ : a ≠ b₁) (hab₂ : a ≠ b₂)
    (hb : b₁ ≠ b₂)
    (he₁ : ({a,b₁,z} : Set W) ∈ H.edges)
    (he₂ : ({a,b₂,z} : Set W) ∈ H.edges) : False := by
  have haz : a ≠ z := by
    intro h
    have hc := htri _ he₁
    subst z
    have : ({a, b₁, a} : Set W) = {a, b₁} := by ext; simp [or_comm]
    rw [this] at hc
    rw [Set.ncard_pair hab₁] at hc
    omega
  have hne : ({a,b₁,z} : Set W) ≠ ({a,b₂,z} : Set W) := by
    intro heq
    have hbmem : b₁ ∈ ({a,b₂,z} : Set W) := by
      rw [← heq]
      simp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hbmem
    rcases hbmem with h | h | h
    · exact hab₁ h.symm
    · exact hb h
    · have hc := htri _ he₁
      rw [h] at hc
      have : ({a, z, z} : Set W) = {a, z} := by ext; simp [or_comm]
      rw [this] at hc
      rw [Set.ncard_pair haz] at hc
      omega
  have hs := hlin _ he₁ _ he₂ hne
  exact haz (hs (by simp) (by simp))

lemma hk_link_value_row_bound [DecidableEq W] (H : Hypergraph W)
    (htri : H.IsTripleSystem) (hlin : H.Linear)
    {q : ℕ} (A B : Fin q → W) (P : Fin q → Fin q → W)
    (hAinj : Function.Injective A) (hBinj : Function.Injective B)
    (hAB : ∀ i j, A i ≠ B j)
    (hedge : ∀ i j, ({A i, B j, P i j} : Set W) ∈ H.edges) :
    (∀ i v, (Finset.univ.filter (fun j => P i j = v)).card < 2) ∧
    (∀ j v, (Finset.univ.filter (fun i => P i j = v)).card < 2) := by
  classical
  constructor
  · intro i v
    by_contra hn
    have htwo : 2 ≤ (Finset.univ.filter (fun j => P i j = v)).card := by omega
    have hone : 1 < (Finset.univ.filter (fun j => P i j = v)).card := by omega
    rw [Finset.one_lt_card] at hone
    obtain ⟨j₁, hj₁, j₂, hj₂, hjne⟩ := hone
    have hp₁ := (Finset.mem_filter.mp hj₁).2
    have hp₂ := (Finset.mem_filter.mp hj₂).2
    exact hk_link_private_unique_row H htri hlin (hAB i j₁) (hAB i j₂)
      (fun h => hjne (hBinj h)) (by simpa [hp₁] using hedge i j₁)
      (by simpa [hp₂] using hedge i j₂)
  · intro j v
    by_contra hn
    have hone : 1 < (Finset.univ.filter (fun i => P i j = v)).card := by omega
    rw [Finset.one_lt_card] at hone
    obtain ⟨i₁, hi₁, i₂, hi₂, hine⟩ := hone
    have hp₁ := (Finset.mem_filter.mp hi₁).2
    have hp₂ := (Finset.mem_filter.mp hi₂).2
    exact hk_link_private_unique_row H htri hlin (hAB i₁ j).symm (hAB i₂ j).symm
      (fun h => hine (hAinj h)) (by simpa [hp₁, Set.insert_comm] using hedge i₁ j)
      (by simpa [hp₂, Set.insert_comm] using hedge i₂ j)

lemma hk_rainbow_realization_from_link (H : Hypergraph W)
    (htri : H.IsTripleSystem) (hlin : H.Linear)
    (F : HKFiltration H) (a : F.Idx)
    (huc : ¬ (SimpleGraph.toHG (hkLinkGraph H F a)).ColorableBy ℵ₀) :
    ∃ Z X Y,
      (∀ i j i' j', Z i j = Z i' j' → i = i' ∧ j = j') ∧
      HKRealizes H Z X Y ∧
      (∀ i, F.rank (X i) = a) ∧ (∀ i, F.rank (Y i) = a) ∧
      ∀ i j, F.linearOrder.lt (F.rank (Z i j)) a := by
  letI := F.linearOrder
  classical
  let q := 228
  obtain ⟨A, B, hAinj, hBinj, hAB, hadj⟩ :=
    eh_hasKmm (hkLinkGraph H F a) huc q
  have hP : ∀ i j : Fin q, ∃ z, F.rank z < a ∧
      ({A i, B j, z} : Set W) ∈ H.edges := by
    intro i j
    have hh := hadj i j
    rw [hkLinkGraph, SimpleGraph.fromRel_adj] at hh
    rcases hh with ⟨_, hrel | hrel⟩
    · exact ⟨hrel.2.2.choose, hrel.2.2.choose_spec.1,
        hrel.2.2.choose_spec.2⟩
    · have hz := hrel.2.2.choose_spec
      exact ⟨hrel.2.2.choose, hz.1, by simpa [Set.insert_comm] using hz.2⟩
  choose P hPrank hPedge using hP
  have hb := hk_link_value_row_bound H htri hlin A B P hAinj hBinj hAB hPedge
  obtain ⟨I, J, hI, hJ, hrainbow⟩ :=
    greedy_rainbow 3 2 q (by omega) (by norm_num [q]) P hb.1 hb.2
  refine ⟨fun i j => P (I i) (J j), fun i => A (I i), fun j => B (J j),
    hrainbow, ?_, fun i => ?_, fun j => ?_, fun i j => hPrank (I i) (J j)⟩
  · refine ⟨hAinj.comp hI, hBinj.comp hJ, ?_, ?_, ?_, ?_⟩
    · exact fun i j => hAB (I i) (J j)
    · intro i k l h
      have hri := show F.rank (A (I i)) = a from by
        have hh := hadj (I i) (J k)
        rw [hkLinkGraph, SimpleGraph.fromRel_adj] at hh
        rcases hh with ⟨_, hh | hh⟩ <;> simp_all
      have hrz := hPrank (I k) (J l)
      have hrEq := congrArg F.rank h
      apply (lt_irrefl a)
      calc
        a = F.rank (A (I i)) := hri.symm
        _ = F.rank (P (I k) (J l)) := hrEq
        _ < a := hrz
    · intro i k l h
      have hri := show F.rank (B (J i)) = a from by
        have hh := hadj (I k) (J i)
        rw [hkLinkGraph, SimpleGraph.fromRel_adj] at hh
        rcases hh with ⟨_, hh | hh⟩ <;> simp_all
      have hrz := hPrank (I k) (J l)
      have hrEq := congrArg F.rank h
      apply (lt_irrefl a)
      calc
        a = F.rank (B (J i)) := hri.symm
        _ = F.rank (P (I k) (J l)) := hrEq
        _ < a := hrz
    · exact fun j k => hPedge (I j) (J k)
  · have hh := hadj (I i) (J 0)
    rw [hkLinkGraph, SimpleGraph.fromRel_adj] at hh
    rcases hh with ⟨_, hh | hh⟩ <;> simp_all
  · have hh := hadj (I 0) (J j)
    rw [hkLinkGraph, SimpleGraph.fromRel_adj] at hh
    rcases hh with ⟨_, hh | hh⟩ <;> simp_all

theorem hk_unblocked_grid_of_filtration (H : Hypergraph W)
    (htri : H.IsTripleSystem) (hlin : H.Linear)
    (huc : H.UncountablyChromatic) (F : HKFiltration H) :
    ∃ Z : Fin 3 → Fin 3 → W,
      (∀ i j i' j', Z i j = Z i' j' → i = i' ∧ j = j') ∧
      ∀ S : Finset W, S.card ≤ 18 →
        ∃ X Y : Fin 3 → W, HKRealizes H Z X Y ∧
          (∀ i, X i ∉ S) ∧ (∀ i, Y i ∉ S) := by
  letI := F.linearOrder
  obtain ⟨a, ha⟩ := exists_uncountable_hkLinkGraph H htri huc F
  obtain ⟨Z, X0, Y0, hZ, hreal0, hrX, hrY, hrZ⟩ :=
    hk_rainbow_realization_from_link H htri hlin F a ha
  refine ⟨Z, hZ, ?_⟩
  intro S hScard
  by_contra hno
  push_neg at hno
  have hblocks : HKBlocks H Z S := by
    refine ⟨hScard, ?_⟩
    intro X Y hreal
    by_cases hx : ∃ i, X i ∈ S
    · exact Or.inl hx
    · right
      exact hno X Y hreal (by simpa only [not_exists] using hx)
  obtain ⟨T, hTblock, hrT⟩ := F.reflectBlocker a Z hrZ ⟨S, hblocks⟩
  have hhit := hTblock.2 X0 Y0 hreal0
  rcases hhit with ⟨i, hi⟩ | ⟨i, hi⟩
  · exact (lt_irrefl a) (by
      calc a = F.rank (X0 i) := (hrX i).symm
           _ < a := hrT _ hi)
  · exact (lt_irrefl a) (by
      calc a = F.rank (Y0 i) := (hrY i).symm
           _ < a := hrT _ hi)

theorem hk_theorem1_three_step {W : Type u} (H : Hypergraph W)
    (htri : H.IsTripleSystem) (hlin : H.Linear)
    (huc : H.UncountablyChromatic) (hfree : ¬ (hkMn 3).Embeds H)
    (minimal : ∀ (W' : Type u) (H' : Hypergraph W'), #W' < #W →
      H'.IsTripleSystem → H'.Linear → ¬ (hkMn 3).Embeds H' →
      H'.ColorableBy ℵ₀) : False := by
  obtain ⟨F : HKFiltration.{u, u} H⟩ :=
    exists_hk_filtration (W := W) H htri hlin huc hfree minimal
  obtain ⟨Z, hZ, havoid⟩ := hk_unblocked_grid_of_filtration H htri hlin huc F
  exact hfree (hkMn3_embeds_of_avoidance H Z hZ havoid)

theorem hk_theorem1_three {W : Type u} (H : Hypergraph W)
    (htri : H.IsTripleSystem) (hlin : H.Linear)
    (huc : H.UncountablyChromatic) :
    (hkMn 3).Embeds H := by
  have key : ∀ κ : Cardinal.{u}, ∀ (W : Type u) (H : Hypergraph W),
      #W = κ → H.IsTripleSystem → H.Linear → H.UncountablyChromatic →
      (hkMn 3).Embeds H := by
    refine fun κ => Cardinal.lt_wf.induction
      (C := fun κ => ∀ (W : Type u) (H : Hypergraph W),
        #W = κ → H.IsTripleSystem → H.Linear → H.UncountablyChromatic →
        (hkMn 3).Embeds H) κ ?_
    intro κ IH W H hcard htri hlin huc
    by_contra hfree
    exact hk_theorem1_three_step H htri hlin huc hfree (fun W' H' hlt htri' hlin' hfree' => by
      by_contra hcol
      exact hfree' (IH (#W') (hcard ▸ hlt) W' H' rfl htri' hlin' hcol))
  exact key (#W) W H rfl htri hlin huc

theorem e5_HK_loose7 : E5_HK_loose7.{u} := by
  intro W H htri hlin huc
  obtain ⟨g, hg, hge⟩ := looseCycle7_sub_hkMn3
  obtain ⟨f, hf, hfe⟩ := hk_theorem1_three H htri hlin huc
  refine ⟨f ∘ g, hf.comp hg, ?_⟩
  intro e he
  rw [show (f ∘ g) '' (↑e : Set looseCycle7.V) =
    f '' (↑(e.image g) : Set (hkMn 3).V) by
      rw [Finset.coe_image, Set.image_comp]]
  exact hfe _ (hge e he)

end Erdos593
end

namespace OMA1177Bridge

open Cardinal

private def raw {V : Type} (H : UniformHypergraph V 3) : Erdos593.Hypergraph V :=
  ⟨H.edgeSet⟩

private theorem raw_isTriple {V : Type} (H : UniformHypergraph V 3) : (raw H).IsTripleSystem := by
  intro e he
  have hcard := H.uniform e he
  have hfinite := Set.finite_of_encard_eq_coe hcard
  have h := hfinite.cast_ncard_eq
  rw [hcard] at h
  exact_mod_cast h

private def uniform {V : Type} (H : Erdos593.Hypergraph V) (h : H.IsTripleSystem) :
    UniformHypergraph V 3 where
  toHypergraph := ⟨Set.univ, H.edges, fun _ _ => Set.subset_univ _⟩
  vertexSet_eq_univ := rfl
  uniform e he := by
    have hcard := h e he
    have hf : e.Finite := Set.finite_of_ncard_ne_zero (by rw [hcard]; decide)
    rw [← hf.cast_ncard_eq, hcard]

private theorem colorable_iff {V : Type} (H : UniformHypergraph V 3) (θ : Cardinal) :
    (raw H).ColorableBy θ ↔
      θ ∈ {α : Cardinal | ∃ (C : Type), #C = α ∧ ∃ f : V → C, H.IsProperColoring f} := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨θ.out, mk_out θ, f, hf⟩
  · rintro ⟨C, hC, f, hf⟩
    obtain ⟨equiv⟩ := Cardinal.eq.mp (hC.trans (mk_out θ).symm)
    refine ⟨equiv ∘ f, ?_⟩
    intro e he
    obtain ⟨x, hx, y, hy, hxy⟩ := hf e he
    exact ⟨x, hx, y, hy, equiv.injective.ne hxy⟩

private theorem chromatic_iff {V : Type} (H : UniformHypergraph V 3) {κ : Cardinal} :
    H.chromaticCardinal = κ ↔ (raw H).HasChromatic κ := by
  let colorSizes : Set Cardinal :=
    {α | ∃ (C : Type), #C = α ∧ ∃ f : V → C, H.IsProperColoring f}
  change sInf colorSizes = κ ↔ _
  constructor
  · intro heq
    have hne : colorSizes.Nonempty :=
      ⟨#V, V, rfl, id, H.isProperColoring_of_injective (by decide) Function.injective_id⟩
    have hmem : κ ∈ colorSizes := by
      rw [← heq]
      exact csInf_mem hne
    refine ⟨(colorable_iff H κ).mpr hmem, ?_⟩
    intro θ hlt hcol
    obtain ⟨C, hC, f, hf⟩ := (colorable_iff H θ).mp hcol
    have hle : sInf colorSizes ≤ #C := H.chromaticCardinal_le hf
    rw [heq, hC] at hle
    exact hlt.not_ge hle
  · rintro ⟨hcol, hmin⟩
    have hmem : κ ∈ colorSizes := (colorable_iff H κ).mp hcol
    refine le_antisymm (csInf_le' hmem) (le_csInf ⟨κ, hmem⟩ ?_)
    intro θ hθ
    exact le_of_not_gt (fun hlt => hmin θ hlt ((colorable_iff H θ).mpr hθ))

private def fromFinite (F : Erdos593.FTS) : UniformHypergraph F.V 3 :=
  uniform ⟨{e | ∃ s ∈ F.edges, (s : Set F.V) = e}⟩ (by
    rintro _ ⟨s, hs, rfl⟩
    simpa using F.card3 s hs)

private theorem edge_iff (F : Erdos593.FTS) (e : Finset F.V) :
    e ∈ F.edges ↔ (e : Set F.V) ∈ (fromFinite F).edgeSet := by
  change _ ↔ ∃ s ∈ F.edges, (s : Set F.V) = (e : Set F.V)
  exact ⟨fun h => ⟨e, h, rfl⟩, fun ⟨_, hs, he⟩ => Finset.coe_injective he ▸ hs⟩

private theorem appears_iff (F : Erdos593.FTS) {V : Type} (H : UniformHypergraph V 3) :
    (fromFinite F).Appears H ↔ F.Embeds (raw H) := by
  classical
  constructor
  · rintro ⟨f, hinj, hmem⟩
    exact ⟨f, hinj, fun e he => hmem (Hypergraph.image_mem_edgeSet_image ((edge_iff F e).mp he))⟩
  · rintro ⟨f, hinj, hmem⟩
    refine ⟨f, hinj, ?_⟩
    intro imageEdge himage
    obtain ⟨e, he, rfl⟩ := Hypergraph.mem_edgeSet_image.mp himage
    obtain ⟨s, hs, rfl⟩ : ∃ s ∈ F.edges, (s : Set F.V) = e := he
    exact hmem s hs

private theorem avoidance (F : Erdos593.FTS) {κ : Cardinal} (h : F.FGnonempty κ) :
    (fromFinite F).HasAvoidingChromaticCardinal κ := by
  obtain ⟨V, H, hT, hχ, havoid⟩ := h
  let U := uniform H hT
  exact ⟨V, Classical.decEq V, U, (chromatic_iff U).mpr hχ,
    fun he => havoid ((appears_iff F U).mp he)⟩

end OMA1177Bridge

open Cardinal OMA1177Bridge in
theorem OMA.solution : type_of% @Erdos1177.erdos_1177.parts.ii := by
  classical
  intro hAll
  obtain ⟨G, H, hG, hH, hbad⟩ := Erdos593.problem_1177_part2_no_E34
    Erdos593.e2_EH_oddgirth Erdos593.e5_HK_loose7
  rw [Cardinal.succ_aleph0] at hG hH hbad
  obtain ⟨V, _, K, hχ, hKG, hKH⟩ := hAll G.V H.V (fromFinite G) (fromFinite H)
    (avoidance G hG) (avoidance H hH)
  exact hbad ⟨V, raw K, raw_isTriple K, (chromatic_iff K).mp hχ,
    fun hG' => hKG ((appears_iff G K).mpr hG'),
    fun hH' => hKH ((appears_iff H K).mpr hH')⟩
