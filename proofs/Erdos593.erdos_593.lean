import FormalConjectures.ErdosProblems.«593»
import Mathlib

/-!
# Erdős problem 593

After removing isolated vertices, a finite triple system is obligatory exactly
when it is linear, each triple is incident to a bridge of the incidence graph,
and every Berge cycle has even length. Berge length counts triples.

Classification and proof adapted from Eric Li, arXiv:2606.24882, and the
Apache-2.0 licensed Lean development by Eric Li with Aristotle (Harmonic),
https://github.com/ericlisg/erdos-593-1177-lean, revision
5dcb6e4906df03f2e4294b21be73b55db7736f5a. Adapted to the Formal Conjectures
hypergraph API and Lean 4.33.1. The nonlinear obstruction uses the triangle
system from Matt Dorman’s accepted proof in this project (pull request 735).

SPDX-License-Identifier: Apache-2.0. The license of the adapted development
is reproduced at the end of this file.
-/

section

open Cardinal Ordinal

namespace TripleSystem593

universe u

structure TripleHost (V : Type u) where
  edges : Set (Set V)

def TripleHost.ProperColoring {V : Type u} {C : Type*} (H : TripleHost V)
    (c : V → C) : Prop :=
  ∀ e ∈ H.edges, ∃ u ∈ e, ∃ v ∈ e, c u ≠ c v

def TripleHost.ColorableBy {V : Type u} (H : TripleHost V) (θ : Cardinal.{u}) :
    Prop :=
  ∃ c : V → θ.out, H.ProperColoring c

def TripleHost.HasChromatic {V : Type u} (H : TripleHost V) (κ : Cardinal.{u}) :
    Prop :=
  H.ColorableBy κ ∧ ∀ θ, θ < κ → ¬ H.ColorableBy θ

def SimpleGraph.toHG {α : Type u} (A : SimpleGraph α) : TripleHost α :=
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

def liftHG : TripleHost (Node A κ × α) :=
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
  · intro h; exact (hpre.1.ne (congrArg Node.pos h)).elim;
  · rintro rfl; exact absurd hpre.1 ( lt_irrefl _ ) ;

end Lift

theorem toHG_proper_iff {α : Type u} (A : SimpleGraph α) {C : Type*}
    (c : α → C) :
    (SimpleGraph.toHG A).ProperColoring c ↔ ∀ x y, A.Adj x y → c x ≠ c y := by
  simp [SimpleGraph.toHG, TripleHost.ProperColoring];
  grind

theorem exists_mono_edge {α : Type u} {A : SimpleGraph α} {θ : Cardinal.{u}}
    (hA : ¬ (SimpleGraph.toHG A).ColorableBy θ) (g : α → θ.out) :
    ∃ x y, A.Adj x y ∧ g x = g y := by
  contrapose! hA;
  exact ⟨ g, fun e he => by rcases he with ⟨ x, y, hxy, rfl ⟩ ; exact ⟨ x, by simp, y, by simp, hA x y hxy ⟩ ⟩

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
  rw [ branch_eq ];
  convert! Classical.choose_spec ( Classical.choose_spec ( exists_mono_edge hA ( fun x => c ( branchNode A κ c hA a, x ) ) ) ) |>.2

theorem branchNode_seq (a b : Idx κ) (hab : a < b) :
    ((branchNode A κ c hA b).seq ⟨a, hab⟩ : Sym2 α)
      = s((branch A κ c hA a).1.1, (branch A κ c hA a).1.2) := by
  rfl

theorem lift_not_colorableBy (hA : ¬ (SimpleGraph.toHG A).ColorableBy θ)
    (hθ : θ < κ) :
    ¬ (liftHG A κ).ColorableBy θ := by
  intro hLift;
  -- Define the "stage colour" `d : Idx κ → θ.out` by `d a := c (branchNode A κ c hA a, (branch A κ c hA a).1.1)`.
  obtain ⟨c, hc⟩ := hLift
  set d : Idx κ → θ.out := fun a => c (branchNode A κ c hA a, (branch A κ c hA a).1.1);
  -- By `lt_trichotomy a b`, and by symmetry of the roles of `a,b` (since `d a = d b`), assume `a < b` (the case `b < a` is identical with `a,b` swapped; `a = b` is excluded).
  obtain ⟨a, b, hab, hd⟩ : ∃ a b : Idx κ, a < b ∧ d a = d b := by
    by_contra! h;
    have h_card : Cardinal.mk (Idx κ) ≤ Cardinal.mk (Quotient.out θ) := by
      exact Cardinal.mk_le_of_injective ( show Function.Injective d from fun a b hab => le_antisymm ( le_of_not_gt fun h' => h _ _ h' hab.symm ) ( le_of_not_gt fun h' => h _ _ h' hab ) );
    simp_all +decide [ Cardinal.mk_toType ];
    exact not_lt_of_ge h_card hθ;
  obtain ⟨ u, hu, v, hv, huv ⟩ := hc { ( branchNode A κ c hA a, ( branch A κ c hA a ).1.1 ), ( branchNode A κ c hA a, ( branch A κ c hA a ).1.2 ), ( branchNode A κ c hA b, ( branch A κ c hA b ).1.1 ) } ⟨ branchNode A κ c hA a, branchNode A κ c hA b, ( branch A κ c hA a ).1.1, ( branch A κ c hA a ).1.2, ( branch A κ c hA b ).1.1, ⟨ hab, fun q hq => rfl ⟩, by
    convert! branchNode_seq A κ c hA a b hab, rfl ⟩ ; simp_all +decide [ Set.mem_insert_iff, Set.mem_singleton_iff ];
  rcases hu with ( rfl | rfl | rfl ) <;> rcases hv with ( rfl | rfl | rfl ) <;> simp_all +decide [ branch_mono ]; all_goals have := branch_mono A κ c hA a; have := branch_mono A κ c hA b; aesop;

end LowerBound
end TripleSystem593

end

section

/-!
# Definitional infrastructure for arXiv:2606.24882

This file sets up the structural definitions needed to state and prove the
results of

  Eric Li, *A Resolution of Erdős Problems 593 and 1177: Obligatory Triple
  Systems and Exact Spectra*, arXiv:2606.24882.

We reuse the `TripleHost` framework from `RequestProject.Lift` for *hosts*
(large, possibly infinite triple systems), and introduce a bundled type
`FTS` of *finite triple systems* for the sources of embeddings.

## Main definitions

* `TripleHost.IsTripleSystem` — every edge has exactly three vertices.
* `TripleHost.UncountablyChromatic` — not colourable with `ℵ₀` colours.
* `FTS` — a finite triple system (bundled finite vertex type + edge finset).
* `FTS.Embeds` — an injective, non-induced embedding of a finite triple
  system into a host hypergraph.
* `FTS.Obligatory` — occurs in every triple system of uncountable chromatic
  number.
* `FTS.Linear` — any two distinct edges meet in at most one vertex.
* `FTS.InSpec` / `FTS.FGnonempty` — the exact spectrum and the family
  `F_G(κ)`.
-/

open Cardinal Ordinal

namespace TripleSystem593

universe u v

/-- A host hypergraph is a *triple system* if every edge has exactly three
vertices. -/
def TripleHost.IsTripleSystem {V : Type*} (H : TripleHost V) : Prop :=
  ∀ e ∈ H.edges, e.ncard = 3

/-- A host hypergraph is *uncountably chromatic* if it admits no proper
colouring by `ℵ₀` colours. -/
def TripleHost.UncountablyChromatic {V : Type u} (H : TripleHost V) : Prop :=
  ¬ H.ColorableBy ℵ₀

/-! ### Finite triple systems -/

/-- A *finite triple system*: a finite vertex type together with a finite set
of three-element edges. -/
structure FTS where
  /-- The (finite) vertex type. -/
  V : Type
  [finV : Fintype V]
  [decV : DecidableEq V]
  /-- The edges, each a three-element finset. -/
  edges : Finset (Finset V)
  /-- Every edge has exactly three vertices. -/
  card3 : ∀ e ∈ edges, e.card = 3

instance (F : FTS) : Fintype F.V := F.finV
instance (F : FTS) : DecidableEq F.V := F.decV

/-- A vertex of a finite triple system is *isolated* if it lies on no edge. -/
def FTS.Isolated (F : FTS) (x : F.V) : Prop :=
  ∀ e ∈ F.edges, x ∉ e

/-- `F` is *linear* if any two distinct edges meet in at most one vertex. -/
def FTS.Linear (F : FTS) : Prop :=
  ∀ e₁ ∈ F.edges, ∀ e₂ ∈ F.edges, e₁ ≠ e₂ → (e₁ ∩ e₂).card ≤ 1

/-- An injective, non-induced embedding of a finite triple system `F` into a
host hypergraph `H`: an injective vertex map sending every edge of `F` to an
edge of `H`. -/
def FTS.Embeds (F : FTS) {W : Type u} (H : TripleHost W) : Prop :=
  ∃ f : F.V → W, Function.Injective f ∧
    ∀ e ∈ F.edges, (f '' (↑e : Set F.V)) ∈ H.edges

/-- `F` is *obligatory* if it occurs in every triple system of uncountable
chromatic number. -/
def FTS.Obligatory (F : FTS) : Prop :=
  ∀ {W : Type u} (H : TripleHost W),
    H.IsTripleSystem → H.UncountablyChromatic → F.Embeds H

/-- The exact spectrum membership: `λ ∈ Spec(F)` iff `λ` is uncountable and
there is an exact-`λ`-chromatic `F`-free triple system. -/
def FTS.InSpec (F : FTS) (lam : Cardinal.{u}) : Prop :=
  ℵ₀ < lam ∧ ∃ (W : Type u) (H : TripleHost W),
    H.IsTripleSystem ∧ H.HasChromatic lam ∧ ¬ F.Embeds H

/-- The family `F_G(κ)` is nonempty: there is an exact-`κ`-chromatic triple
system omitting `G`. -/
def FTS.FGnonempty (G : FTS) (kappa : Cardinal.{u}) : Prop :=
  ∃ (W : Type u) (H : TripleHost W),
    H.IsTripleSystem ∧ H.HasChromatic kappa ∧ ¬ G.Embeds H

end TripleSystem593

end

section

open Cardinal Function

namespace TripleSystem593

universe u

open Classical in

noncomputable abbrev FTS.reduce (F : FTS) : FTS where
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

theorem TripleHost.UncountablyChromatic.infinite {W : Type u} {H : TripleHost W}
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

/-- Forward direction of the reduction: an embedding of `F` restricts to one of
`F°`. -/
theorem FTS.reduce_embeds_of_embeds (F : FTS) {W : Type u} {H : TripleHost W}
    (h : F.Embeds H) : F.reduce.Embeds H := by
  obtain ⟨f, hf₁, hf₂⟩ := h
  refine ⟨fun x => f x.val, hf₁.comp Subtype.coe_injective, ?_⟩
  simp only [FTS.reduce, Finset.mem_image, Finset.mem_attach, true_and, forall_exists_index]
  rintro e d rfl
  convert hf₂ d.1 d.2 using 1
  ext w
  simp only [Set.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.val, by simpa [Finset.mem_subtype] using ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    have hna : ¬ F.Isolated a := fun hiso => hiso d.1 d.2 ha
    exact ⟨⟨a, hna⟩, by simpa [Finset.mem_subtype] using ha, rfl⟩

/-- An injection from a finite type into an infinite type avoiding the range of
a given map (used to place isolated vertices on fresh host vertices). -/
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

/-- Backward direction of the reduction, for an infinite host. -/
theorem FTS.embeds_of_reduce_embeds (F : FTS) {W : Type u} [Infinite W]
    {H : TripleHost W} (h : F.reduce.Embeds H) : F.Embeds H := by
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
      simp only [FTS.reduce, Finset.mem_image, Finset.mem_attach, true_and]; exact ⟨⟨e, he⟩, rfl⟩
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
      simp only [hf]; rw [dif_pos a.2]

/-- **Isolated-vertex reduction** (`lem:isolated-reduction`, embedding form).
For an infinite host `H`, `F` embeds iff its reduction `F°` embeds. -/
theorem FTS.embeds_reduce_iff (F : FTS) {W : Type u} [Infinite W] (H : TripleHost W) :
    F.Embeds H ↔ F.reduce.Embeds H :=
  ⟨F.reduce_embeds_of_embeds, F.embeds_of_reduce_embeds⟩

/-- Obligatoriness is unaffected by isolated vertices. -/
theorem FTS.obligatory_reduce_iff (F : FTS) :
    FTS.Obligatory.{u} F ↔ FTS.Obligatory.{u} F.reduce := by
  constructor
  · intro hF W H htri huc
    exact F.reduce_embeds_of_embeds (hF H htri huc)
  · intro hF W H htri huc
    have : Infinite W := huc.infinite htri
    exact F.embeds_of_reduce_embeds (hF H htri huc)


end TripleSystem593

end

section

/-!
# Structural infrastructure: Berge cycles, bridges, the class `B`, expansions

This file provides the definitional infrastructure of the paper needed to state
the classification of obligatory triple systems and the exact-spectrum results:
Berge cycles, Levi bridges and bridge selectors, the intrinsic obligatoriness
condition, the private-vertex expansion `J⁺`, disjoint union and one-point
amalgamation of finite triple systems, and the target class `B`.
-/

open Cardinal

namespace TripleSystem593

universe u

/-! ### Berge cycles and bridges -/

/-- A *Berge cycle* of length `m ≥ 2` in a triple system: an alternating cyclic
sequence of distinct point-nodes and hyperedge-nodes with consecutive
incidences (`v i, v (i+1) ∈ e i`). -/
structure BergeCycle (F : FTS) where
  m : ℕ
  hm : 2 ≤ m
  v : ZMod m → F.V
  e : ZMod m → {e : Finset F.V // e ∈ F.edges}
  vinj : Function.Injective v
  einj : Function.Injective e
  mem_left : ∀ i, v i ∈ (e i).1
  mem_right : ∀ i, v (i + 1) ∈ (e i).1

/-- The Levi incidence `(w, ed)` (with `w ∈ ed`) lies on a Berge cycle. -/
def OnBergeCycle (F : FTS) (w : F.V) (ed : {e : Finset F.V // e ∈ F.edges}) : Prop :=
  ∃ (c : BergeCycle F) (i : ZMod c.m), c.e i = ed ∧ (c.v i = w ∨ c.v (i + 1) = w)

/-- A Levi incidence `(w, ed)` is a *bridge* if `w ∈ ed` and it lies on no Berge
cycle.  (A finite-graph edge is a bridge iff it lies on no cycle; this is the
characterization the paper uses.) -/
def IsBridgeInc (F : FTS) (w : F.V) (ed : {e : Finset F.V // e ∈ F.edges}) : Prop :=
  w ∈ ed.1 ∧ ¬ OnBergeCycle F w ed

/-- A *bridge selector*: a choice at each edge of an incident bridge point. -/
structure BridgeSelector (F : FTS) where
  p : {e : Finset F.V // e ∈ F.edges} → F.V
  isBridge : ∀ ed, IsBridgeInc F (p ed) ed

/-- The intrinsic condition (iii) of the classification: linear, every
hyperedge-node incident with a bridge, and every Berge cycle of even length.
(These three properties are unaffected by isolated vertices, so we phrase them on
`F` directly.) -/
def FTS.IntrinsicObligatory (F : FTS) : Prop :=
  F.Linear ∧
  (∀ ed : {e : Finset F.V // e ∈ F.edges}, ∃ w ∈ ed.1, IsBridgeInc F w ed) ∧
  (∀ c : BergeCycle F, Even c.m)

/-! ### The class `B` -/

/-- Disjoint union of two finite triple systems. -/
abbrev FTS.disjUnion (F G : FTS) : FTS where
  V := F.V ⊕ G.V
  edges := F.edges.image (Finset.map Function.Embedding.inl) ∪
           G.edges.image (Finset.map Function.Embedding.inr)
  card3 := by
    intro e he
    simp only [Finset.mem_union, Finset.mem_image] at he
    rcases he with ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩ <;>
      rw [Finset.card_map] <;> [exact F.card3 d hd; exact G.card3 d hd]

/-- One-point amalgamation identifying `x ∈ V(F)` with `y ∈ V(G)`.  Realized on
the glue type `F.V ⊕ {b : G.V // b ≠ y}`, sending `y` to `x`. -/
noncomputable abbrev FTS.amalgamate (F G : FTS) (x : F.V) (y : G.V) : FTS where
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

/-- The private-vertex expansion `J⁺` of a finite graph `J`: core vertices of `J`
plus one private vertex per edge, with edges `{x, y, p_{xy}}`. -/
noncomputable abbrev graphExpansion {VJ : Type} [Fintype VJ] [DecidableEq VJ]
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
      push Not
      exact ⟨fun h => hne (Sum.inl_injective h), fun h => Sum.inl_ne_inr h⟩

/-- Isomorphism of finite triple systems: a vertex bijection preserving edges. -/
def FTS.Iso (F G : FTS) : Prop :=
  ∃ φ : F.V ≃ G.V, ∀ e : Finset F.V, e ∈ F.edges ↔ e.map φ.toEmbedding ∈ G.edges

/-- **The class `B`** (`Bclass`): the smallest class of finite triple systems
containing every private-vertex expansion `J⁺` of a finite bipartite graph `J`,
containing every edgeless system, and closed under isomorphism, disjoint union
and one-point amalgamation. -/
inductive Bclass : FTS → Prop
  | edgeless (F : FTS) (h : F.edges = ∅) : Bclass F
  | expansion {VJ : Type} [Fintype VJ] [DecidableEq VJ] (J : SimpleGraph VJ)
      [DecidableRel J.Adj] (hJ : J.Colorable 2) : Bclass (graphExpansion J)
  | iso {F G : FTS} (h : FTS.Iso F G) : Bclass F → Bclass G
  | union {F G : FTS} : Bclass F → Bclass G → Bclass (F.disjUnion G)
  | amalg {F G : FTS} (x : F.V) (y : G.V) : Bclass F → Bclass G → Bclass (F.amalgamate G x y)

/-! ### Linearity for hosts -/

/-- A host hypergraph is *linear* if any two distinct edges meet in at most one
vertex. -/
def TripleHost.Linear {W : Type*} (H : TripleHost W) : Prop :=
  ∀ e₁ ∈ H.edges, ∀ e₂ ∈ H.edges, e₁ ≠ e₂ → (e₁ ∩ e₂).Subsingleton

/-! ### Obligatoriness transfers across isomorphism -/

/-- Obligatoriness transfers across isomorphism. -/
theorem obligatory_iso {F G : FTS} (h : FTS.Iso F G) (ih : FTS.Obligatory.{u} F) :
    FTS.Obligatory.{u} G := by
  intro W H htri huc;
  obtain ⟨ φ, hφ ⟩ := h;
  obtain ⟨ f, hf, hfe ⟩ := ih H htri huc;
  use fun x => f ( φ.symm x );
  refine' ⟨ hf.comp φ.symm.injective, _ ⟩;
  intro e he; specialize hφ ( Finset.map φ.symm.toEmbedding e ) ; simp_all +decide [ Finset.map_map ] ;
  convert! hfe _ hφ using 1 ; ext ; aesop

end TripleSystem593

end

section

/-!
# de Bruijn–Erdős compactness for graph colourings

If every finite subset of the vertex set of a simple graph admits a proper
`k`-colouring, then the whole graph is `k`-colourable.  This is the compactness
theorem used in the proof of closure of obligatory triple systems under
one-point amalgamation (`lem:obligatory-closure`).
-/

open SimpleGraph

namespace TripleSystem593

/-- **de Bruijn–Erdős compactness.**  If for every finite set `s` of vertices
there is a total colouring `V → Fin k` that is proper on `s`, then there is a
total colouring proper on all adjacent pairs. -/
theorem colorable_of_forall_finite {V : Type*} (G : SimpleGraph V) (k : ℕ) [NeZero k]
    (h : ∀ s : Finset V, ∃ c : V → Fin k, ∀ a ∈ s, ∀ b ∈ s, G.Adj a b → c a ≠ c b) :
    ∃ c : V → Fin k, ∀ a b, G.Adj a b → c a ≠ c b := by
  classical
  by_contra h_contra
  push Not at h_contra
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
  -- The finite set of vertices appearing in the pairs of `s`.
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

end TripleSystem593

end

section

/-!
# Helper lemmas for closure of obligatory triple systems under amalgamation

Reusable framework lemmas used in the proof of `lem:obligatory-closure`
(closure of the obligatory finite triple systems under one-point amalgamation).
-/

open Cardinal SimpleGraph

namespace TripleSystem593

universe u

/-- The restriction of a host hypergraph to a vertex subset `S`. -/
def TripleHost.restrict {W : Type u} (H : TripleHost W) (S : Set W) : TripleHost W :=
  ⟨{e | e ∈ H.edges ∧ e ⊆ S}⟩

/-
A proper colouring into any countable colour type witnesses `ℵ₀`-colourability.
-/
theorem colorableBy_aleph0_of_countable {W : Type u} (H : TripleHost W) {T : Type u}
    (hT : #T ≤ ℵ₀) {c : W → T} (hc : H.ProperColoring c) : H.ColorableBy ℵ₀ := by
  obtain ⟨ f, hf ⟩ := Cardinal.mk_le_aleph0_iff.mp hT;
  obtain ⟨ g, hg ⟩ := Cardinal.eq.1 ( Cardinal.mk_out ℵ₀ );
  refine' ⟨ fun w => hg ⟨ f ( c w ) ⟩, _ ⟩;
  intro e he; obtain ⟨ u, hu, v, hv, huv ⟩ := hc e he; use u, hu, v, hv; simp +decide [ * ] ;
  grind +qlia

/-
Any type of cardinality `≤ ℵ₀` embeds into `(ℵ₀).out`; a `Countable` product
of finite by `(ℵ₀).out` is countable.
-/
theorem countable_prod_out {I : Type} [Fintype I] : #(I × (ℵ₀ : Cardinal.{u}).out) ≤ ℵ₀ := by
  convert! Cardinal.mk_le_aleph0;
  convert! instCountableProd;
  · infer_instance;
  · convert! Cardinal.mk_le_aleph0_iff.mp ( le_of_eq ( Cardinal.mk_out ℵ₀ ) )

/-
If `F` is obligatory and does not embed into the restriction of a triple
system `H` to `S`, then that restriction is `ℵ₀`-colourable.
-/
theorem restrict_colorable_of_obligatory {W : Type u} {H : TripleHost W}
    (htri : H.IsTripleSystem) {F : FTS} (hF : FTS.Obligatory.{u} F)
    {S : Set W} (hfree : ¬ F.Embeds (H.restrict S)) :
    (H.restrict S).ColorableBy ℵ₀ := by
  contrapose! hfree;
  apply hF;
  · exact fun e he => htri e he.1;
  · exact hfree

/-
If the vertex set is partitioned into finitely many parts, each inducing an
`ℵ₀`-colourable restriction, then the whole host is `ℵ₀`-colourable.
-/
theorem colorableBy_of_finite_parts {W : Type u} (H : TripleHost W) {I : Type}
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

/-- Averaging / degeneracy: in a graph with an out-orientation of out-degree
`≤ d`, every nonempty finite vertex set contains a vertex of degree `≤ 2d`
inside the set. -/
theorem exists_low_degree_vertex {B : Type u} (D : SimpleGraph B) (d : ℕ)
    (out : B → Finset B) (hout : ∀ v, (out v).card ≤ d)
    (hcov : ∀ v w, D.Adj v w → w ∈ out v ∨ v ∈ out w) [DecidableRel D.Adj]
    (s : Finset B) (hs : s.Nonempty) :
    ∃ v₀ ∈ s, (s.filter (fun w => D.Adj v₀ w)).card ≤ 2 * d := by
  classical
  by_contra h_contra
  push Not at h_contra
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

/-- A finite-graph degeneracy colouring: if `D` has an orientation `out` with all
out-degrees `≤ d`, then any finite vertex set admits a proper `(2d+1)`-colouring
(restricted to that set). -/
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
        push Not at hcon
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

/-- **Degeneracy colouring via de Bruijn–Erdős.**  If `D` has an orientation with
all out-degrees `≤ d`, then `D` is `(2d+1)`-colourable. -/
theorem colorable_of_out {B : Type u} (D : SimpleGraph B) (d : ℕ)
    (out : B → Finset B) (hout : ∀ v, (out v).card ≤ d)
    (hcov : ∀ v w, D.Adj v w → w ∈ out v ∨ v ∈ out w) [DecidableRel D.Adj] :
    ∃ c : B → Fin (2 * d + 1), ∀ a b, D.Adj a b → c a ≠ c b := by
  have : NeZero (2 * d + 1) := ⟨by omega⟩
  exact colorable_of_forall_finite D (2 * d + 1)
    (finite_degenerate_coloring D d out hout hcov)

/-- Restricting an uncountably chromatic triple system to the complement of a
finite vertex set stays uncountably chromatic (and a triple system): recolour the
finitely many deleted vertices with a disjoint copy of the countable palette. -/
theorem restrict_uc {W : Type u} {H : TripleHost W} (htri : H.IsTripleSystem)
    (huc : H.UncountablyChromatic) {S : Set W} (hS : S.Finite) :
    (⟨{e | e ∈ H.edges ∧ e ⊆ Sᶜ}⟩ : TripleHost W).UncountablyChromatic := by
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

end TripleSystem593

end

section

/-!
# Closure of obligatory triple systems under one-point amalgamation

This file proves `lem:obligatory-closure` (the one-point amalgamation part):
if `F` and `G` are obligatory finite triple systems, then so is their one-point
amalgamation `F.amalgamate G x y`.

The proof is elementary apart from the de Bruijn–Erdős compactness theorem
(`TripleSystem593.colorable_of_forall_finite`) and the finite-graph degeneracy
colouring toolkit in `RequestProject.AmalgHelpers`.
-/

open Cardinal SimpleGraph

namespace TripleSystem593

universe u

/-
**Amalgam embedding from two copies meeting only at the glue point.**  If a
copy `f` of `F` and a copy `g` of `G` in a host `H` satisfy `f x = g y` and their
images meet *only* at that point, then the amalgamation `F.amalgamate G x y`
embeds into `H`.
-/
theorem amalgamate_embeds_of_copies {W : Type u} {H : TripleHost W} {F G : FTS}
    (x : F.V) (y : G.V)
    (f : F.V → W) (hf : Function.Injective f) (hfe : ∀ e ∈ F.edges, f '' (↑e : Set F.V) ∈ H.edges)
    (g : G.V → W) (hg : Function.Injective g) (hge : ∀ e ∈ G.edges, g '' (↑e : Set G.V) ∈ H.edges)
    (hglue : f x = g y)
    (hmeet : ∀ a b, f a = g b → a = x ∧ b = y) :
    (F.amalgamate G x y).Embeds H := by
  refine' ⟨ fun v => Sum.elim f ( fun b => g b.1 ) v, _, _ ⟩;
  · intro a b hab;
    cases a <;> cases b <;> simp_all +decide [ hf.eq_iff, hg.eq_iff ]; all_goals grind;
  · -- By definition of amalgamation, we can split the goal into two cases: when the edge is from F and when it is from G.
    intro e he
    simp [FTS.amalgamate] at he;
    rcases he with ( ⟨ a, ha, rfl ⟩ | ⟨ a, ha, rfl ⟩ ) <;> simp +decide [ *, Finset.map_eq_image ];
    · convert! hfe a ha using 1 ; ext ; aesop;
    · convert! hge a ha using 1;
      grind

/-- **Rerouting isolated vertices.**  Any copy `g` of `G` can be modified, keeping
its values on non-isolated vertices (hence on all edges), so that the images of
the isolated vertices avoid a prescribed finite set `Avoid` and the non-isolated
images, while remaining injective. -/
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

/-- The set of host vertices that can serve as the image of the root `x` in a
copy of `F` (the set `B` of the paper's proof). -/
def RootSetF {W : Type u} (H : TripleHost W) (F : FTS) (x : F.V) : Set W :=
  {v | ∃ f : F.V → W, Function.Injective f ∧
    (∀ e ∈ F.edges, f '' (↑e : Set F.V) ∈ H.edges) ∧ f x = v}

/-- If the root `x` is non-isolated, the complement of the root set carries no
copy of `F`. -/
theorem rootSetF_compl_Ffree {W : Type u} (H : TripleHost W) {F : FTS} (x : F.V)
    (hx : ¬ F.Isolated x) : ¬ F.Embeds (H.restrict (RootSetF H F x)ᶜ) := by
  rintro ⟨g, hg_inj, hg_e⟩
  obtain ⟨e0, he0, hxe0⟩ : ∃ e ∈ F.edges, x ∈ e := by
    by_contra hc; push Not at hc; exact hx hc
  have hmem := hg_e e0 he0
  have hsub : g '' (↑e0 : Set F.V) ⊆ (RootSetF H F x)ᶜ := hmem.2
  have hgx : g x ∈ g '' (↑e0 : Set F.V) := ⟨x, Finset.mem_coe.mpr hxe0, rfl⟩
  have hgxB : g x ∈ RootSetF H F x := ⟨g, hg_inj, fun e he => (hg_e e he).1, rfl⟩
  exact (hsub hgx) hgxB

/-
**Each colour class is `G`-free.**  If the glue root `y` is non-isolated, `C`
is contained in the root set `B`, each `v ∈ C` carries a chosen copy `K v` of `F`
rooted at `v`, and no non-root vertex of `K v` lies in `C`, then a copy of `G`
in `C` combined with `K v` would produce a copy of the amalgam — impossible when
`H` is amalgam-free.  Hence `C` carries no copy of `G`.
-/
theorem class_Gfree {W : Type u} [Infinite W] {H : TripleHost W}
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
    simp_all +decide [ TripleHost.restrict ];
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
  grind +suggestions)

/-- **Amalgamation closure, main case.**  If the two glue roots are non-isolated,
the one-point amalgamation of obligatory systems is obligatory. -/
theorem amalgamate_obligatory_of_nonisolated {F G : FTS} (x : F.V) (y : G.V)
    (hx : ¬ F.Isolated x) (hy : ¬ G.Isolated y)
    (hF : FTS.Obligatory.{u} F) (hG : FTS.Obligatory.{u} G) :
    FTS.Obligatory.{u} (F.amalgamate G x y) := by
  intro W H htri huc
  by_contra hcon
  haveI : Infinite W := huc.infinite htri
  classical
  refine huc ?_
  -- Chosen copies of `F` rooted at each vertex of the root set.
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
  -- Auxiliary graph and its out-orientation.
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
  -- Partition the host into the complement of the root set and the colour classes.
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

/-
**Symmetry of one-point amalgamation.**
-/
theorem amalgamate_symm_iso {F G : FTS} (x : F.V) (y : G.V) :
    FTS.Iso (F.amalgamate G x y) (G.amalgamate F y x) := by
  -- Construct the equivalence map `φ : (F.amalgamate G x y).V ≃ (G.amalgamate F y x).V` by swapping the roles of `F` and `G`.
  let φ : (F.V ⊕ {b : G.V // b ≠ y}) ≃ (G.V ⊕ {a : F.V // a ≠ x}) :=
    { toFun := fun v => match v with
      | Sum.inl a => if h : a = x then Sum.inl y else Sum.inr ⟨a, h⟩
      | Sum.inr ⟨b, hb⟩ => Sum.inl b,
      invFun := fun v => match v with
      | Sum.inl b => if h : b = y then Sum.inl x else Sum.inr ⟨b, h⟩
      | Sum.inr ⟨a, ha⟩ => Sum.inl a,
      left_inv := by
        grind,
      right_inv := by
        grind +qlia };
  all_goals generalize_proofs at *;
  refine' ⟨ φ, fun e => _ ⟩;
  constructor <;> intro he <;> simp_all +decide [ FTS.amalgamate ];
  · rcases he with ( ⟨ a, ha, rfl ⟩ | ⟨ a, ha, rfl ⟩ );
    · right;
      simp +decide [ Finset.map_map, Function.Embedding.inl ];
      grind +suggestions;
    · left;
      use a;
      simp +decide [ Finset.map_map ];
      refine' ⟨ ha, Finset.map_injective _ _ ⟩;
      exact F.V ⊕ { b : G.V // ¬b = y };
      exact ⟨ fun v => φ.symm v, φ.symm.injective ⟩;
      ext; simp [φ];
      congr! 2;
      split_ifs <;> simp +decide [ * ];
  · rcases he with ( ⟨ a, ha, he ⟩ | ⟨ a, ha, he ⟩ );
    · refine' Or.inr ⟨ a, ha, _ ⟩;
      convert! congr_arg ( Finset.map ( show ( G.V ⊕ { a // a ≠ x } ) ↪ ( F.V ⊕ { b // b ≠ y } ) from ⟨ φ.symm, by
                                        exact φ.symm.injective ⟩ ) ) he using 1
      generalize_proofs at *;
      · ext; simp [φ];
      · simp +decide [ Finset.map_map ];
        try simp +decide [ Function.Embedding.trans ];
    · left;
      use a;
      simp +decide [ Finset.ext_iff ] at he ⊢;
      refine' ⟨ ha, _, _ ⟩;
      · intro b; specialize he; have := he.2 b; by_cases hb : b = x <;> simp_all +decide ;
        · convert! he.1 y using 1;
          · grind;
          · simp +decide [ φ ];
        · convert! he.2 b hb using 1;
          grind;
      · intro b hb; specialize he; have := he.1 b; simp_all +decide [ φ ] ;
        specialize he ; replace he := he.1 b ; aesop

/-
**Amalgamation closure, isolated-root case.**  If the root `x` is isolated in
`F`, the amalgamation of obligatory systems is obligatory.
-/
theorem amalgamate_obligatory_of_isolated {F G : FTS} (x : F.V) (y : G.V)
    (hx : F.Isolated x) (hF : FTS.Obligatory.{u} F) (hG : FTS.Obligatory.{u} G) :
    FTS.Obligatory.{u} (F.amalgamate G x y) := by
  intro W H htri huc;
  obtain ⟨g, hg_inj, hg_e⟩ := hG H htri huc;
  haveI : Infinite W := huc.infinite htri
  set v := g y
  set S := Set.range g
  have hS : S.Finite := Set.finite_range g;
  -- Restriction of H off `S`: The hypergraph `H1 := ⟨{e | e ∈ H.edges ∧ e ⊆ Sᶜ}⟩` is uncountably chromatic by `restrict_uc htri huc hS` (this lemma is now available), and a triple system by `fun e he => htri e he.1`.
  set H1 : TripleHost W := ⟨{e | e ∈ H.edges ∧ e ⊆ Sᶜ}⟩
  have hH1_uc : H1.UncountablyChromatic := by
    convert! restrict_uc htri huc hS using 1
  have hH1_tri : H1.IsTripleSystem := by
    exact fun e he => htri e he.1;
  -- Copy of F in H1: `obtain ⟨f0, hf0_inj, hf0_e⟩ := hF H1 hH1_tri hH1_uc`; for `e ∈ F.edges`, `hf0_e e he` gives `f0 '' ↑e ∈ H.edges` (`.1`) and `f0 '' ↑e ⊆ Sᶜ` (`.2`).
  obtain ⟨f0, hf0_inj, hf0_e⟩ := hF H1 hH1_tri hH1_uc;
  -- Reroute isolated vertices of `f0` off `S`: `obtain ⟨f1, hf1_inj, hf1_0, hf1_1⟩ := reroute_isolated f0 hf0_inj S hS`, where `hf1_0 : ∀ a, ¬ F.Isolated a → f1 a = f0 a` and `hf1_1 : ∀ a, F.Isolated a → f1 a ∉ S ∧ f1 a ∉ f0 '' {a' | ¬ F.Isolated a'}`.
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

/-- **Closure of obligatory triple systems under one-point amalgamation**
(`lem:obligatory-closure`). -/
theorem amalgamate_obligatory {F G : FTS} (x : F.V) (y : G.V)
    (hF : FTS.Obligatory.{u} F) (hG : FTS.Obligatory.{u} G) :
    FTS.Obligatory.{u} (F.amalgamate G x y) := by
  by_cases hx : F.Isolated x
  · exact amalgamate_obligatory_of_isolated x y hx hF hG
  · by_cases hy : G.Isolated y
    · exact obligatory_iso (amalgamate_symm_iso y x)
        (amalgamate_obligatory_of_isolated y x hy hG hF)
    · exact amalgamate_obligatory_of_nonisolated x y hx hy hF hG

end TripleSystem593

end

section

open Cardinal

namespace TripleSystem593

universe u

theorem edgeless_obligatory (F : FTS) (h : F.edges = ∅) : FTS.Obligatory.{u} F := by
  intro W H htri huc
  have hinf : Infinite W := huc.infinite htri
  let f : F.V ↪ W := (Fintype.equivFin F.V).toEmbedding.trans (Fin.valEmbedding.trans hinf.natEmbedding)
  exact ⟨f, f.injective, fun e he => absurd he (by rw [h]; simp)⟩

theorem obligatory_disjUnion {F G : FTS} (ihF : FTS.Obligatory.{u} F)
    (ihG : FTS.Obligatory.{u} G) : FTS.Obligatory.{u} (F.disjUnion G) := by
  intro W H htri huc
  obtain ⟨fF, hfF, hfFe⟩ := ihF H htri huc
  obtain ⟨gG, hgG, hgGe⟩ := ihG H htri huc
  have hS : Set.Finite (Set.range fF) := by
    exact Set.toFinite _
  generalize_proofs at *; (
  obtain ⟨g0, hg0, hg0e⟩ : ∃ g0 : G.V → W, Function.Injective g0 ∧ ∀ e ∈ G.edges, g0 '' (e : Set G.V) ∈ {e | e ∈ H.edges ∧ e ⊆ (Set.range fF)ᶜ} := by
    obtain ⟨g0, hg0, hg0e⟩ : ∃ g0 : G.V → W, Function.Injective g0 ∧ ∀ e ∈ G.edges, g0 '' (e : Set G.V) ∈ {e | e ∈ H.edges ∧ e ⊆ (Set.range fF)ᶜ} := by
      have hHR : (⟨{e | e ∈ H.edges ∧ e ⊆ (Set.range fF)ᶜ}⟩ : TripleHost W).UncountablyChromatic := by
        exact restrict_uc htri huc hS
      convert! ihG _ _ hHR using 1
      generalize_proofs at *; (
      exact fun e he => htri e he.1)
    generalize_proofs at *; (
    use g0)
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
          apply TripleHost.UncountablyChromatic.infinite htri huc
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
  refine' ⟨ Sum.elim fF g, _, _ ⟩;
  · intro a b hab
    cases a <;> cases b <;> simp_all [Function.Injective]
    all_goals grind
  · intro e he
    rcases Finset.mem_union.mp he with he | he <;>
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    · simpa [Set.image_image] using hfFe a ha
    · simpa [Set.image_image] using hg'.1 a ha)))


def ReiherExpansion : Prop :=
  ∀ {VJ : Type} [Fintype VJ] [DecidableEq VJ] (J : SimpleGraph VJ) [DecidableRel J.Adj],
    J.Colorable 2 → FTS.Obligatory.{u} (graphExpansion J)

def AmalgClosure : Prop :=
  ∀ {F G : FTS} (x : F.V) (y : G.V), FTS.Obligatory.{u} F → FTS.Obligatory.{u} G →
    FTS.Obligatory.{u} (F.amalgamate G x y)

theorem amalgClosure_holds : AmalgClosure.{u} :=
  fun x y hF hG => amalgamate_obligatory x y hF hG

theorem bclass_obligatory (hexp : ReiherExpansion.{u})
    (F : FTS) (h : Bclass F) : FTS.Obligatory.{u} F := by
  induction h with
  | edgeless F hF => exact edgeless_obligatory F hF
  | expansion J hJ => exact hexp J hJ
  | iso hiso _ ih => exact obligatory_iso hiso ih
  | union _ _ ihF ihG => exact obligatory_disjUnion ihF ihG
  | amalg x y _ _ ihF ihG => exact amalgClosure_holds x y ihF ihG

end TripleSystem593

end

section

open Cardinal

namespace TripleSystem593

universe u

def NoShortOddCycle {V : Type u} (A : SimpleGraph V) (s : ℕ) : Prop :=
  ∀ m : ℕ, Odd m → 3 ≤ m → m ≤ 2 * s + 1 →
    ¬ ∃ v : ZMod m → V, Function.Injective v ∧ ∀ i : ZMod m, A.Adj (v i) (v (i + 1))

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
    {θ : Cardinal.{u}} (h : (⟨F⟩ : TripleHost V).ColorableBy θ) :
    (⟨E⟩ : TripleHost V).ColorableBy θ := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun e he => hc e (hEF he)⟩

theorem colorableBy_aleph0_union {V : Type u} (E' E'' : Set (Set V))
    (h' : (⟨E'⟩ : TripleHost V).ColorableBy ℵ₀)
    (h'' : (⟨E''⟩ : TripleHost V).ColorableBy ℵ₀) :
    (⟨E' ∪ E''⟩ : TripleHost V).ColorableBy ℵ₀ := by
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
    (hE : (⟨E⟩ : TripleHost V).UncountablyChromatic)
    (hE' : (⟨E'⟩ : TripleHost V).ColorableBy ℵ₀) :
    (⟨E \ E'⟩ : TripleHost V).UncountablyChromatic := by
  intro hdiff
  exact hE (colorableBy_mono
    (by intro x hx; by_cases h : x ∈ E' <;> [left; right] <;> simp_all)
    (colorableBy_aleph0_union E' (E \ E') hE' hdiff))
end TripleSystem593

end

section

/-!
# The subhypergraph passage: `E4_Reiher ⟹ ReiherExpansion`

The headline resolutions are assembled from the *carried* hypothesis
`ReiherExpansion` — every private-vertex expansion `J⁺` of a finite bipartite
graph `J` is obligatory.  The paper's literature input **E4** (Reiher) is the
single instance that the complete bipartite expansion `K_{n,n}⁺` is obligatory.
This file discharges the *subhypergraph passage* of `lem:obligatory-closure`
that upgrades E4 to `ReiherExpansion`: a `2`-colourable graph `J` embeds into
`K_{n,n}` (`n = |V(J)|`), so `J⁺` is a sub–triple-system of `K_{n,n}⁺`, and
obligatoriness passes to sub–triple-systems.  Consequently every headline result
depends only on the literature interfaces E1–E5, not on the strengthened
`ReiherExpansion`. -/

open Cardinal Classical

namespace TripleSystem593

universe u

/-- `F` is a **sub–triple-system** of `G`: an injective vertex map sending every
edge of `F` to an edge of `G`. -/
def FTS.Sub (F G : FTS) : Prop :=
  ∃ g : F.V → G.V, Function.Injective g ∧ ∀ e ∈ F.edges, e.image g ∈ G.edges

/-- **Obligatoriness passes to sub–triple-systems.**  If `F` embeds into `G` as a
sub–triple-system and `G` is obligatory, then `F` is obligatory. -/
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

/-
**Expansion is monotone under graph embeddings.**  An injective,
adjacency-preserving vertex map `φ : J → K` induces a sub–triple-system embedding
`J⁺ ↪ K⁺`.
-/
/-- An adjacency-preserving map sends `J`-edges to `K`-edges (as `Sym2` values). -/
theorem sym2map_mem_edgeFinset {VJ VK : Type} [Fintype VJ] [DecidableEq VJ]
    [Fintype VK] [DecidableEq VK] (J : SimpleGraph VJ) [DecidableRel J.Adj]
    (K : SimpleGraph VK) [DecidableRel K.Adj]
    (φ : VJ → VK) (hadj : ∀ a b, J.Adj a b → K.Adj (φ a) (φ b))
    (e : Sym2 VJ) (he : e ∈ J.edgeFinset) : Sym2.map φ e ∈ K.edgeFinset := by
  rw [SimpleGraph.mem_edgeFinset] at *
  induction e with
  | h a b => rw [SimpleGraph.mem_edgeSet] at *; exact hadj a b he

theorem graphExpansion_sub_of_embedding {VJ VK : Type} [Fintype VJ] [DecidableEq VJ]
    [Fintype VK] [DecidableEq VK] (J : SimpleGraph VJ) [DecidableRel J.Adj]
    (K : SimpleGraph VK) [DecidableRel K.Adj]
    (φ : VJ → VK) (hφ : Function.Injective φ)
    (hadj : ∀ a b, J.Adj a b → K.Adj (φ a) (φ b)) :
    (graphExpansion J).Sub (graphExpansion K) := by
  refine' ⟨ _, _, _ ⟩;
  exact fun x => x.elim ( fun x => Sum.inl ( φ x ) ) fun e => Sum.inr ⟨ Sym2.map φ e.1, by
    rcases e with ⟨ e, he ⟩ ; simp_all +decide [ SimpleGraph.mem_edgeFinset ] ;
    rcases e with ⟨ a, b ⟩ ; simp_all +decide [ SimpleGraph.mem_edgeSet ] ; ⟩;
  · intro x y hxy; cases x <;> cases y <;> simp_all +decide [ hφ.eq_iff ] ;
    exact Subtype.ext (Sym2.map.injective hφ hxy)
  · all_goals generalize_proofs at *;
    intro e he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    let t := Sym2.map φ d.val
    let dt : K.edgeFinset := ⟨t, sym2map_mem_edgeFinset J K φ hadj d.val d.property⟩
    apply Finset.mem_image.mpr
    refine ⟨dt, Finset.mem_attach _ _, ?_⟩
    simp only [Finset.map_insert, Finset.map_singleton]
    have hs : s((Quot.out t).1, (Quot.out t).2) =
        s(φ (Quot.out d.val).1, φ (Quot.out d.val).2) := by
      calc
        _ = t := Quot.out_eq t
        _ = _ := by
          have hd' : s((Quot.out d.val).1, (Quot.out d.val).2) = d.val := Quot.out_eq _
          exact (congrArg (Sym2.map φ) hd').symm
    rcases Sym2.eq_iff.mp hs with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · change {Sum.inl (Quot.out t).1, Sum.inl (Quot.out t).2, Sum.inr dt} = _
      rw [h1,h2]; simp [dt,t]
    · change {Sum.inl (Quot.out t).1, Sum.inl (Quot.out t).2, Sum.inr dt} = _
      rw [h1,h2, Finset.insert_comm]; simp [dt,t]

/-- **A `2`-colourable graph embeds into a complete bipartite graph.**  If `J` is
`2`-colourable then there is an `n` and an injective adjacency-preserving map
`J → K_{n,n}`. -/
theorem colorable_two_embeds_completeBipartite {VJ : Type} [Fintype VJ] [DecidableEq VJ]
    (J : SimpleGraph VJ) [DecidableRel J.Adj] (hJ : J.Colorable 2) :
    ∃ (n : ℕ) (φ : VJ → (Fin n ⊕ Fin n)), Function.Injective φ ∧
      ∀ a b, J.Adj a b → (completeBipartiteGraph (Fin n) (Fin n)).Adj (φ a) (φ b) := by
  obtain ⟨C⟩ := hJ;
  refine' ⟨ Fintype.card VJ, fun v => if C v = 0 then Sum.inl ( Fintype.equivFin VJ v ) else Sum.inr ( Fintype.equivFin VJ v ), _, _ ⟩;
  · intro v w h; by_cases hv : C v = 0 <;> by_cases hw : C w = 0 <;> simp_all +decide ;
  · intro a b hab; have := C.valid hab; simp_all +decide ;
    grind

/-- **The subhypergraph passage** (`lem:obligatory-closure`): the literature input
E4 (Reiher's theorem that `K_{n,n}⁺` is obligatory) implies the strengthened
`ReiherExpansion` (every bipartite expansion `J⁺` is obligatory). -/
theorem reiherExpansion_of_E4 (hE4 : E4_Reiher.{u}) : ReiherExpansion.{u} := by
  intro VJ _ _ J _ hJ
  obtain ⟨n, φ, hφ, hadj⟩ := colorable_two_embeds_completeBipartite J hJ
  exact obligatory_of_sub
    (graphExpansion_sub_of_embedding J (completeBipartiteGraph (Fin n) (Fin n)) φ hφ hadj)
    (hE4 n)

/-- **`ReiherExpansion` is exactly the literature input E4.**  Combined with
`E4_Reiher_of_reiherExpansion`, this shows the carried hypothesis
`ReiherExpansion` is *equivalent* to Reiher's published Theorem 1.2. -/
theorem reiherExpansion_iff_E4 : ReiherExpansion.{u} ↔ E4_Reiher.{u} :=
  ⟨E4_Reiher_of_reiherExpansion, reiherExpansion_of_E4⟩

end TripleSystem593

end

section

/-!
# The Erdős–Hajnal base case: uncountably chromatic graphs contain `K_{n,ℵ₁}`

This file formalizes the graph-theoretic base case underlying Reiher's
Theorem 1.2 (our `E4_Reiher`).  The statement is:

> For every natural number `n`, every graph `G` of uncountable chromatic number
> contains the complete bipartite graph `K_{n, ℵ₁}` (and hence `K_{n,n}`).

Reference: C. Reiher, *Graphs of large girth*, arXiv:2403.13571, §3.6,
Theorem (Erdős & Hajnal); originally Erdős–Hajnal, Acta Math. Hungar. 17 (1966),
Corollary 5.6.

## Proof outline (a transfinite-recursion-free rendering of the survey proof)

Fix `n`.  Argue by strong induction on the cardinal `κ = #V`.  Assume `G` is not
countably colourable but `K_{n,ℵ₁}`-free; we derive a contradiction by producing
a countable colouring.

* Call `M ⊆ V` *`n`-closed* (`NClosed`) if every `x ∉ M` has fewer than `n`
  neighbours in `M`.  Because `G` is `K_{n,ℵ₁}`-free, every `n`-set has countable
  common neighbourhood, so the finitary closure `cl X` (iterate "add vertices
  with `≥ n` neighbours") is `n`-closed with `#(cl X) ≤ #X + ℵ₀`.
* Enumerate `V` by `Idx = κ.ord.ToType`; set `M a = cl (e '' {b ≤ a})`.  This is
  monotone, each `M a` is `n`-closed with `#(M a) < κ`, and the sets cover `V`.
* `rank x := least a with x ∈ M a`.  Then the "back-neighbours"
  `{y | G.Adj x y ∧ rank y < rank x}` lie in `M_{<rank x} = ⋃_{b<rank x} M b`,
  which is `n`-closed (a monotone union of `n`-closed sets stays `n`-closed
  because `n` is finite), so there are `< n` of them.  Each level
  `{x | rank x = a} ⊆ M a` has size `< κ`, hence is countably colourable by the
  induction hypothesis.
* From a rank function with `< n` back-neighbours and countably-colourable
  levels one builds a countable colouring by well-founded recursion on `rank`:
  colour `x` inside the `n`-block `[n·g(x), n·g(x)+n)` (where `g` is a level
  colouring) avoiding the `< n` colours of its back-neighbours.
-/

open Cardinal

namespace TripleSystem593

universe u

variable {V : Type u}

/-- A graph `G` is *countably colourable* if its vertices can be properly
coloured by `ℕ`. -/
def GCountColorable (G : SimpleGraph V) : Prop :=
  ∃ c : V → ℕ, ∀ x y, G.Adj x y → c x ≠ c y

/-- `GCountColorable` is exactly `ℵ₀`-colourability of the associated hypergraph. -/
theorem gCountColorable_iff_colorableBy (G : SimpleGraph V) :
    GCountColorable G ↔ (SimpleGraph.toHG G).ColorableBy ℵ₀ := by
  constructor;
  · rintro ⟨ c, hc ⟩;
    refine' ⟨ _, _ ⟩;
    convert! ( nonempty_equiv_of_countable ( α := ℕ ) ( β := Quotient.out ℵ₀ ) ).some ∘ c;
    convert! Cardinal.mk_le_aleph0_iff.mp _;
    convert! Cardinal.mk_out ℵ₀ |> le_of_eq;
    exact Cardinal.infinite_iff.2 ( by simp +decide );
    intro e he; obtain ⟨ x, y, hxy, rfl ⟩ := he; specialize hc x y hxy; aesop;
  · rintro ⟨ c, hc ⟩;
    obtain ⟨ f, hf ⟩ := Cardinal.eq.1 ( Cardinal.mk_out ℵ₀ );
    use fun x => ( f ( c x ) ).down;
    intro x y hxy; have := hc _ ( by exact ⟨ x, y, hxy, rfl ⟩ ) ; simp_all +decide [ Function.LeftInverse, Function.RightInverse ] ;
    grind

/-- `G` contains `K_{n, ℵ₁}`: `n` distinct vertices with a common neighbourhood of
size at least `ℵ₁`, disjoint from the `n` vertices. -/
def HasKnAleph1 (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ (a : Fin n → V) (B : Set V), Function.Injective a ∧ ℵ₁ ≤ #B ∧
    (∀ i, a i ∉ B) ∧ (∀ i, ∀ b ∈ B, G.Adj (a i) b)

/-! ### Closed sets and the finitary closure operator -/

/-- The neighbours of `x` lying in `M`. -/
def nbhdIn (G : SimpleGraph V) (x : V) (M : Set V) : Set V := {y | y ∈ M ∧ G.Adj x y}

/-- `M` is *`n`-closed* if no vertex outside `M` has `n` or more neighbours in `M`. -/
def NClosed (G : SimpleGraph V) (n : ℕ) (M : Set V) : Prop :=
  ∀ x, x ∉ M → #(nbhdIn G x M) < (n : Cardinal)

/-- One closure step: add every vertex having `≥ n` neighbours in `X`. -/
def closeStep (G : SimpleGraph V) (n : ℕ) (X : Set V) : Set V :=
  X ∪ {x | (n : Cardinal) ≤ #(nbhdIn G x X)}

/-- The `k`-fold closure step. -/
def closeIter (G : SimpleGraph V) (n : ℕ) (X : Set V) : ℕ → Set V
  | 0 => X
  | k + 1 => closeStep G n (closeIter G n X k)

/-- The finitary `n`-closure of `X`. -/
def cl (G : SimpleGraph V) (n : ℕ) (X : Set V) : Set V := ⋃ k, closeIter G n X k

/-! ### Countable common neighbourhoods (from `K_{n,ℵ₁}`-freeness) -/

/-
If `G` is `K_{n,ℵ₁}`-free then any injective `n`-tuple has countable common
neighbourhood (excluding the tuple itself).
-/
theorem commonNbhd_le_aleph0 (G : SimpleGraph V) (n : ℕ) (hfree : ¬ HasKnAleph1 G n)
    (a : Fin n → V) (ha : Function.Injective a) :
    #({v | (∀ i, v ≠ a i) ∧ ∀ i, G.Adj (a i) v}) ≤ ℵ₀ := by
  contrapose! hfree;
  -- Since the cardinality of the set is greater than ℵ₀, it must be at least ℵ₁.
  have h_card_ge_aleph1 : ℵ₁ ≤ #(↥{v : V | (∀ i, v ≠ a i) ∧ ∀ i, G.Adj (a i) v}) := by
    convert! Order.succ_le_of_lt hfree using 1;
    simp +zetaDelta at *;
  exact ⟨ a, _, ha, h_card_ge_aleph1, fun i => by aesop, fun i => by aesop ⟩

/-
The set of vertices with `≥ n` neighbours in `X` has cardinality at most
`#X + ℵ₀`, when `G` is `K_{n,ℵ₁}`-free.
-/
theorem closeStep_card_le (G : SimpleGraph V) (n : ℕ) (hfree : ¬ HasKnAleph1 G n)
    (X : Set V) : #(closeStep G n X) ≤ #X + ℵ₀ := by
  -- Every vertex in the closure step has at least `n` neighbours in `X`.
  have h_closure_step : {x | (n : Cardinal) ≤ #(nbhdIn G x X)} ⊆ ⋃ (a : {a : Fin n → V // Function.Injective a ∧ ∀ i, a i ∈ X}), {v | (∀ i, v ≠ a.1 i) ∧ ∀ i, G.Adj (a.1 i) v} := by
    intro x hx; simp_all +decide [ Set.subset_def ] ;
    -- Since $x$ has at least $n$ neighbors in $X$, we can choose $n$ distinct neighbors from $X$.
    obtain ⟨a, ha⟩ : ∃ a : Fin n → V, Function.Injective a ∧ ∀ i, a i ∈ X ∧ G.Adj x (a i) := by
      obtain ⟨ s, hs ⟩ := Cardinal.le_mk_iff_exists_subset.mp hx;
      have := Cardinal.eq.1 hs.2;
      obtain ⟨ e ⟩ := this;
      exact ⟨ fun i => e.symm ⟨ i ⟩ |>.1, fun i j hij => by simpa [ Fin.ext_iff ] using e.symm.injective ( Subtype.ext hij ), fun i => ⟨ hs.1 ( e.symm ⟨ i ⟩ |>.2 ) |>.1, hs.1 ( e.symm ⟨ i ⟩ |>.2 ) |>.2 ⟩ ⟩;
    exact ⟨ a, fun i => by intro hi; have := ha.2 i; simp_all +decide [ SimpleGraph.adj_comm ], ⟨ ha.1, fun i => ha.2 i |>.1 ⟩, fun i => ha.2 i |>.2.symm ⟩;
  -- The index set has cardinality at most `#X + ℵ₀`.
  have h_index_card : #( {a : Fin n → V // Function.Injective a ∧ ∀ i, a i ∈ X} ) ≤ #(X : Set V) + ℵ₀ := by
    have h_index_card : #( {a : Fin n → V // Function.Injective a ∧ ∀ i, a i ∈ X} ) ≤ #(Fin n → X) := by
      fapply Cardinal.mk_le_of_injective;
      exacts [ fun a => fun i => ⟨ a.val i, a.property.2 i ⟩, fun a b h => Subtype.ext <| funext fun i => by simpa using congr_fun h i ];
    by_cases hX : Infinite X <;> simp_all +decide [ Cardinal.mk_fintype ];
    · refine' le_trans h_index_card _;
      rcases n with ( _ | n ) <;> simp_all +decide [ Cardinal.power_nat_eq ];
      exact le_add_of_nonneg_of_le ( zero_le ) ( by simp +decide );
    · exact le_trans h_index_card ( le_add_of_nonneg_of_le ( by positivity ) ( by exact le_of_lt ( Cardinal.lt_aleph0_of_finite _ ) ) );
  -- Each common-neighbourhood set has cardinality at most `ℵ₀`.
  have h_common_nbhd_card : ∀ a : {a : Fin n → V // Function.Injective a ∧ ∀ i, a i ∈ X}, #( {v | (∀ i, v ≠ a.1 i) ∧ ∀ i, G.Adj (a.1 i) v} : Set V ) ≤ ℵ₀ := by
    exact fun a => commonNbhd_le_aleph0 G n hfree a.1 a.2.1;
  -- Therefore, the cardinality of the closure step is at most `#X + ℵ₀`.
  have h_closure_step_card : #( {x | (n : Cardinal) ≤ #(nbhdIn G x X)} : Set V ) ≤ (#(X : Set V) + ℵ₀) * ℵ₀ := by
    refine' le_trans ( Cardinal.mk_le_mk_of_subset h_closure_step ) _;
    refine' le_trans ( Cardinal.mk_iUnion_le _ ) _;
    gcongr;
    exact ciSup_le' fun a => h_common_nbhd_card a;
  convert! Cardinal.mk_union_le _ _ |> le_trans <| add_le_add_left h_closure_step_card _ using 1;
  any_goals exact X;
  · grind +locals;
  · simp +decide [ add_comm, add_left_comm, add_assoc ];
    rw [ ← add_assoc, Cardinal.add_eq_max ];
    · rw [ Cardinal.add_eq_max ];
      · simp +decide [ max_assoc ];
      · exact le_max_left _ _;
    · norm_num

/-! ### Basic closure properties -/

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

/-
`cl` is monotone in its set argument.
-/
theorem cl_mono (G : SimpleGraph V) (n : ℕ) {X Y : Set V} (h : X ⊆ Y) :
    cl G n X ⊆ cl G n Y := by
  refine Set.iUnion_subset fun k => ?_;
  refine' Set.Subset.trans _ ( Set.subset_iUnion _ ( k + 1 ) );
  induction' k with k ih;
  · exact Set.Subset.trans h ( Set.subset_union_left );
  · refine' Set.union_subset_union ih _;
    exact fun x hx => le_trans hx.out ( Cardinal.mk_le_mk_of_subset <| by exact fun y hy => by exact ⟨ ih hy.1, hy.2 ⟩ )

/-
The closure is `n`-closed.
-/
theorem nclosed_cl (G : SimpleGraph V) (n : ℕ) (hn : 1 ≤ n) (X : Set V) :
    NClosed G n (cl G n X) := by
  intro x hx;
  contrapose! hx;
  obtain ⟨ s, hs ⟩ := Cardinal.le_mk_iff_exists_subset.mp hx;
  -- Since $s$ is a subset of $nbhdIn G x (cl G n X)$ and $s$ has cardinality $n$, there exists some $k$ such that $s \subseteq closeIter G n X k$.
  obtain ⟨ k, hk ⟩ : ∃ k, s ⊆ closeIter G n X k := by
    have h_finite : ∀ y ∈ s, ∃ k, y ∈ closeIter G n X k := by
      exact fun y hy => Set.mem_iUnion.mp ( hs.1 hy |>.1 );
    choose! k hk using h_finite;
    have h_finite : Set.Finite s := by
      exact Set.finite_coe_iff.mp ( Cardinal.lt_aleph0_iff_finite.mp ( hs.2.symm ▸ Cardinal.nat_lt_aleph0 n ) );
    exact ⟨ h_finite.toFinset.sup k, fun y hy => closeIter_mono_index G n X ( Finset.le_sup ( f := k ) ( h_finite.mem_toFinset.mpr hy ) ) ( hk y hy ) ⟩;
  -- Since $s$ is a subset of $closeIter G n X k$ and $s$ has cardinality $n$, we have $n \leq #(nbhdIn G x (closeIter G n X k))$.
  have h_card : n ≤ #(nbhdIn G x (closeIter G n X k)) := by
    refine' hs.2 ▸ Cardinal.mk_le_mk_of_subset _;
    exact fun y hy => ⟨ hk hy, hs.1 hy |>.2 ⟩;
  exact Set.mem_iUnion.mpr ⟨ k + 1, by exact Set.mem_union_right _ h_card ⟩

/-
The closure has size at most `#X + ℵ₀`.
-/
theorem cl_card_le (G : SimpleGraph V) (n : ℕ) (hfree : ¬ HasKnAleph1 G n)
    (X : Set V) : #(cl G n X) ≤ #X + ℵ₀ := by
  -- By induction on $k$, we show that $|closeIter G n X k| \leq |X| + \aleph_0$ for all $k$.
  have h_ind : ∀ k, #(closeIter G n X k) ≤ #X + ℵ₀ := by
    intro k;
    induction' k with k ih;
    · exact le_add_right le_rfl;
    · convert! le_trans ( closeStep_card_le G n hfree _ ) _ using 1;
      convert! add_le_add_right ih ℵ₀ using 1;
      · rw [ add_comm ];
      · rw [ add_comm, Cardinal.add_eq_max ];
        · rw [ Cardinal.add_eq_right ]; all_goals exact le_max_left _ _;
        · norm_num;
  convert! Cardinal.mk_iUnion_le _ |> le_trans <| ?_;
  rotate_left;
  exact ULift ℕ;
  use fun k => closeIter G n X k.down;
  · simp +decide [ Cardinal.mk_nat ];
    refine' le_trans ( mul_le_mul_right ( ciSup_le h_ind ) _ ) _;
    simp +decide [ Cardinal.aleph0_le_add_iff ];
  · ext; simp [cl]

/-
A monotone union of `n`-closed sets over an initial segment stays `n`-closed
(because `n` is finite).
-/
theorem nclosed_biUnion_lt {σ : Type u} [LinearOrder σ] (G : SimpleGraph V) (n : ℕ)
    (hn : 1 ≤ n) (M : σ → Set V) (hmono : Monotone M) (hcl : ∀ b, NClosed G n (M b))
    (a : σ) : NClosed G n (⋃ b ∈ {b : σ | b < a}, M b) := by
  intro x hx;
  by_contra h_contra;
  obtain ⟨s, hs⟩ : ∃ s : Finset V, s.card = n ∧ ∀ y ∈ s, y ∈ nbhdIn G x (⋃ b ∈ {b | b < a}, M b) := by
    obtain ⟨ s, hs ⟩ := Cardinal.le_mk_iff_exists_subset.mp ( le_of_not_gt h_contra );
    cases' Set.Finite.exists_finset_coe ( show Set.Finite s from Set.finite_coe_iff.mp ( Cardinal.lt_aleph0_iff_finite.mp ( by rw [ hs.2 ] ; exact Cardinal.nat_lt_aleph0 _ ) ) ) ; aesop;
  -- For each `y ∈ s`, there exists `b < a` such that `y ∈ M b`.
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

/-! ### The core: a rank function with few back-neighbours gives a colouring -/

/-
**Core colouring lemma.**  Suppose there is a `rank : V → σ` (into a
well-order) such that every vertex has fewer than `n` neighbours of strictly
smaller rank, and each rank level is countably colourable.  Then `G` is countably
colourable.
-/
theorem countColorable_of_rank {σ : Type u} [LinearOrder σ] [WellFoundedLT σ]
    (G : SimpleGraph V) (n : ℕ) (hn : 1 ≤ n) (rank : V → σ)
    (hback : ∀ x, #({y | G.Adj x y ∧ rank y < rank x}) < (n : Cardinal))
    (hlevel : ∀ a : σ, ∃ g : V → ℕ,
      ∀ x y, rank x = a → rank y = a → G.Adj x y → g x ≠ g y) :
    GCountColorable G := by
  choose g hg using hlevel;
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : V → Fin (2 * n + 1), ∀ a b, G.Adj a b → rank a ≠ rank b → c₂ a ≠ c₂ b := by
    have h_colorable : ∀ x : V, ∃ finset : Finset V, {y | G.Adj x y ∧ rank y < rank x} = (finset : Set V) ∧ finset.card ≤ n := by
      intro x
      obtain ⟨s, hs⟩ : ∃ s : Finset V, {y | G.Adj x y ∧ rank y < rank x} = (s : Set V) := by
        have h_finite : Set.Finite {y | G.Adj x y ∧ rank y < rank x} := by
          exact Set.finite_coe_iff.mp ( Cardinal.lt_aleph0_iff_finite.mp ( lt_of_lt_of_le ( hback x ) ( Cardinal.nat_lt_aleph0 _ |> le_of_lt ) ) );
        exact ⟨ h_finite.toFinset, by simpa ⟩;
      specialize hback x; rw [ hs ] at hback; simp_all +decide [ Cardinal.mk_fintype ] ;
      linarith;
    choose finset hfinset using h_colorable;
    convert! colorable_of_out ( SimpleGraph.mk ( fun x y => G.Adj x y ∧ rank x ≠ rank y ) ( by
      exact ⟨fun _ _ h => ⟨ h.1.symm, Ne.symm h.2 ⟩⟩ ) ( by
      exact ⟨ fun x hx => hx.1.ne rfl ⟩ ) ) n finset ( fun x => ( hfinset x ).2 ) ( fun x y hxy => by
      cases lt_or_gt_of_ne hxy.2 <;> simp_all +decide [ Set.ext_iff ];
      · exact Or.inr ( hfinset y |>.1 x |>.1 ⟨ hxy.1.symm, by tauto ⟩ );
      · exact Or.inl ( hfinset x |>.1 y |>.1 ⟨ hxy.1, by assumption ⟩ ) ) using 1;
    · grind +splitImp;
    · exact Classical.decRel _;
  use fun x => (2 * n + 1) * g (rank x) x + c₂ x |> Nat.cast;
  intro x y hxy; by_cases h : rank x = rank y <;> simp_all +decide [ Fin.ext_iff ] ;
  · exact fun h' => hg ( rank y ) x y ( by aesop ) ( by aesop ) hxy ( by nlinarith [ Fin.is_lt ( c₂ x ), Fin.is_lt ( c₂ y ) ] );
  · exact fun h' => hc₂ x y hxy h <| by nlinarith [ show g ( rank x ) x = g ( rank y ) y from by nlinarith [ Fin.is_lt ( c₂ x ), Fin.is_lt ( c₂ y ) ] ] ;

/-! ### Induced subgraphs preserve `K_{n,ℵ₁}`-freeness -/

/-
A `K_{n,ℵ₁}` in an induced subgraph lifts to `G`; hence `K_{n,ℵ₁}`-freeness
passes to induced subgraphs.
-/
theorem hasKnAleph1_of_induce (G : SimpleGraph V) (n : ℕ) (M : Set V)
    (h : HasKnAleph1 (G.induce M) n) : HasKnAleph1 G n := by
  obtain ⟨ a, B, ha, hB, hB', hB'' ⟩ := h;
  refine' ⟨ fun i => a i, Subtype.val '' B, _, _, _, _ ⟩;
  · exact Subtype.coe_injective.comp ha;
  · rw [ Cardinal.mk_image_eq ] ; aesop;
    exact Subtype.coe_injective;
  · grind;
  · aesop

/-! ### The main base-case theorem -/

/-
A graph on a countable vertex type is countably colourable (colour injectively).
-/
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

/-- **The core reduction.**  If `G` is `K_{n,ℵ₁}`-free (`n ≥ 1`), its vertex type
is uncountable, and every strictly smaller `K_{n,ℵ₁}`-free graph is countably
colourable, then `G` itself is countably colourable.  This is the closed-set
filtration argument: build `M a = cl (e '' {b ≤ a})` over an enumeration
`e : κ.ord.ToType ≃ V`, take `rank x` = least `a` with `x ∈ M a`, and apply
`countColorable_of_rank` (back-neighbours are `< n` by closedness; each level lies
in some `M a` of size `< κ`, hence is countably colourable by the hypothesis). -/
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
    fun x => subset_cl _ _ _ ⟨e.symm x, by simp, by simp⟩
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

/-- **Erdős–Hajnal base case.**  Every graph of uncountable chromatic number
contains `K_{n, ℵ₁}` for every `n`. -/
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

/-- `G` contains a (finite) complete bipartite graph `K_{m,m}`: two disjoint
`m`-element vertex sets, complete between them. -/
def HasKmm (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ a b : Fin m → V, Function.Injective a ∧ Function.Injective b ∧
    (∀ i j, a i ≠ b j) ∧ (∀ i j, G.Adj (a i) (b j))

/-- **Erdős–Hajnal, finite form.**  Every graph of uncountable chromatic number
contains `K_{m,m}` for every `m`. -/
theorem eh_hasKmm (G : SimpleGraph V)
    (h : ¬ (SimpleGraph.toHG G).ColorableBy ℵ₀) (m : ℕ) : HasKmm G m := by
  obtain ⟨a, B, ha, hB, hB', hB''⟩ : ∃ (a : Fin m → V) (B : Set V), Function.Injective a ∧ ℵ₁ ≤ #B ∧ (∀ i, a i ∉ B) ∧ (∀ i, ∀ b ∈ B, G.Adj (a i) b) := by
    convert! eh_hasKnAleph1 G h m;
  obtain ⟨b, hb⟩ : ∃ b : Fin m → V, Function.Injective b ∧ ∀ i, b i ∈ B := by
    have hB_inf : Infinite B := by
      contrapose! hB;
      exact lt_of_le_of_lt ( Cardinal.mk_le_aleph0 ) ( Cardinal.aleph0_lt_aleph_one );
    have := hB_inf.natEmbedding;
    exact ⟨ fun i => this i, fun i j hij => by simpa [ Fin.ext_iff ] using this.injective ( Subtype.ext hij ), fun i => this i |>.2 ⟩;
  exact ⟨ a, b, ha, hb.1, fun i j => by intro H; have := hB' i; have := hb.2 j; aesop, fun i j => hB'' i _ ( hb.2 j ) ⟩

end TripleSystem593

end

section

/-!
# E4 (Reiher's Theorem 1.2, case `k = 3`): `K^{(3)}_{n,n}` is obligatory

This file discharges the literature input `E4_Reiher`: for every `n`, the
private-vertex expansion `K^{(3)}_{n,n}` of the complete bipartite graph is
obligatory, i.e. it occurs in every triple system of uncountable chromatic
number.

Reference: C. Reiher, *Obligatory hypergraphs*, arXiv:2403.11223, Theorem 1.2
(the `k = 3` case, whose `k = 2` base case `K_{n,n}` is the Erdős–Hajnal theorem
proved in `RequestProject.EHBase` as `eh_hasKmm`).

## Strategy

`HasK3nn H n` records a copy of `K^{(3)}_{n,n}` inside a host `H` (left cores
`L`, right cores `R`, private vertices `P`, all distinct, with each triple
`{L i, R j, P i j}` an edge).  We prove:

* `hasK3nn_embeds` : `HasK3nn H n → (graphExpansion K_{n,n}).Embeds H` (bookkeeping).
* `hasK3nn_of_uncountable` : every uncountably-chromatic triple system has a
  `K^{(3)}_{n,n}` (Reiher's delta-system argument, using `eh_hasKmm`).
* `e4_Reiher` : hence `E4_Reiher`.
-/

open Cardinal

namespace TripleSystem593

universe u

variable {W : Type u}

/-- A copy of `K^{(3)}_{n,n}` inside a host hypergraph `H`: `n` left cores, `n`
right cores, and `n²` private vertices, all distinct, with each triple
`{L i, R j, P i j}` an edge of `H`. -/
def HasK3nn (H : TripleHost W) (n : ℕ) : Prop :=
  ∃ f : (Fin n ⊕ Fin n) ⊕ (Fin n × Fin n) → W, Function.Injective f ∧
    ∀ i j : Fin n,
      ({f (Sum.inl (Sum.inl i)), f (Sum.inl (Sum.inr j)), f (Sum.inr (i, j))} : Set W)
        ∈ H.edges

/-
Every edge of `K_{n,n} = completeBipartiteGraph (Fin n) (Fin n)` joins a
left vertex `Sum.inl i` to a right vertex `Sum.inr j`.
-/
open Classical in
theorem cb_edge_exists {n : ℕ} (e : Sym2 (Fin n ⊕ Fin n))
    (he : e ∈ (completeBipartiteGraph (Fin n) (Fin n)).edgeFinset) :
    ∃ i j : Fin n, e = s(Sum.inl i, Sum.inr j) := by
  rw [SimpleGraph.mem_edgeFinset] at he
  rcases e with ⟨ ⟨ a, b ⟩ ⟩;
  cases a <;> cases b <;> simp_all +decide [ completeBipartiteGraph ]

open Classical in
/-- **Packaging.**  A `K^{(3)}_{n,n}` copy yields an embedding of the graph
expansion `graphExpansion K_{n,n}` into `H`. -/
theorem hasK3nn_embeds (H : TripleHost W) (n : ℕ) (h : HasK3nn H n) :
    (graphExpansion (completeBipartiteGraph (Fin n) (Fin n))).Embeds H := by
  obtain ⟨f, hf, hedge⟩ := h
  let coord (e : (completeBipartiteGraph (Fin n) (Fin n)).edgeFinset) : Fin n × Fin n :=
    let h := cb_edge_exists e.1 e.2
    (h.choose, h.choose_spec.choose)
  have spec (e : (completeBipartiteGraph (Fin n) (Fin n)).edgeFinset) :
      e.1 = s(Sum.inl (coord e).1, Sum.inr (coord e).2) :=
    (cb_edge_exists e.1 e.2).choose_spec.choose_spec
  have inj : Function.Injective coord := by
    intro a b hab
    apply Subtype.ext
    rw [spec a, spec b, hab]
  let g := Sum.map (id : Fin n ⊕ Fin n → _) coord
  refine ⟨f ∘ g, hf.comp (Sum.map_injective.mpr ⟨Function.injective_id, inj⟩), ?_⟩
  intro e he
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
  have hpair : s((Quot.out d.val).1, (Quot.out d.val).2) =
      s(Sum.inl (coord d).1, Sum.inr (coord d).2) := (Quot.out_eq d.val).trans (spec d)
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton]
  rcases Sym2.eq_iff.mp hpair with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · rw [h1,h2]; exact hedge _ _
  · rw [h1,h2, Set.insert_comm]; exact hedge _ _

/-! ### Colourability bridge for hypergraphs -/

/-- A hypergraph is *countably colourable* if it has a proper `ℕ`-colouring. -/
def HGCountColorable (H : TripleHost W) : Prop :=
  ∃ c : W → ℕ, H.ProperColoring c

/-
`HGCountColorable` is exactly `ℵ₀`-colourability.
-/
theorem hgCountColorable_iff (H : TripleHost W) :
    HGCountColorable H ↔ H.ColorableBy ℵ₀ := by
  constructor;
  · intro h;
    convert! colorableBy_aleph0_of_countable H _ _;
    exact ULift ℕ;
    exact Cardinal.mk_le_aleph0;
    exact fun x => ⟨ h.choose x ⟩;
    intro e he; obtain ⟨ u, hu, v, hv, huv ⟩ := h.choose_spec e he; use u, hu, v, hv; aesop;
  · intro h;
    convert! h using 1;
    constructor <;> intro h <;> rcases h with ⟨ c, hc ⟩;
    · grind;
    · obtain ⟨ f, hf ⟩ := Cardinal.eq.1 ( Cardinal.mk_out ℵ₀ );
      use fun x => ( f ( c x ) ).down;
      intro e he; obtain ⟨ u, hu, v, hv, huv ⟩ := hc e he; use u, hu, v, hv; simp_all +decide [ Function.LeftInverse, Function.RightInverse ] ;
      grind

/-! ### Delta systems -/

/-- `f` is the *root* of a delta system of size `≥ t`: there are `≥ t` edges, all
containing `f`, pairwise meeting exactly in `f`. -/
def IsDeltaRoot (H : TripleHost W) (t : ℕ) (f : Set W) : Prop :=
  ∃ D : Set (Set W), D ⊆ H.edges ∧ (t : Cardinal) ≤ #D ∧ (∀ e ∈ D, f ⊆ e) ∧
    (∀ e₁ ∈ D, ∀ e₂ ∈ D, e₁ ≠ e₂ → e₁ ∩ e₂ = f)

/-- The *roots graph* `H^{(2)}`: `x, y` are adjacent iff `{x, y}` is a delta-system
root. -/
def rootsGraph (H : TripleHost W) (t : ℕ) : SimpleGraph W :=
  SimpleGraph.fromRel (fun x y => IsDeltaRoot H t ({x, y} : Set W))

/-
**Single delta-root extension.**  If `f` is a delta-system root (size `≥ t`)
and `g` is a set with fewer than `t` elements containing `f`, then some edge `e`
contains `f` and meets `g` exactly in `f`.
-/
theorem deltaRoot_extend (H : TripleHost W) (t : ℕ) (f g : Set W)
    (hf : IsDeltaRoot H t f) (hg : #g < (t : Cardinal)) (hfg : f ⊆ g) :
    ∃ e ∈ H.edges, f ⊆ e ∧ e ∩ g = f := by
  obtain ⟨ D, hDsub, hDcard, hDf, hDpair ⟩ := hf;
  contrapose! hg;
  -- For each edge `e ∈ D`, define a vertex `v e ∈ (e ∩ g) \ f`.
  have hv : ∀ e ∈ D, ∃ v : W, v ∈ (e ∩ g) \ f := by
    exact fun e he => Set.exists_of_ssubset ( lt_of_le_of_ne ( by aesop_cat ) ( Ne.symm ( hg e ( hDsub he ) ( hDf e he ) ) ) );
  choose! v hv₁ hv₂ using hv;
  refine' le_trans hDcard _;
  refine' ⟨ fun x => ⟨ v x.1 x.2, _ ⟩, fun x y hxy => _ ⟩;
  grind;
  grind +extAll

/-
**Greedy private-vertex assignment.**  Given cores `a, b` inside a small
`Core` set, all of whose `n²` pairs are delta roots of size `≥ 3n²+1`, one can
choose an injective family of private vertices `P`, avoiding `Core`, so that each
`{a i, b j, P (i,j)}` is an edge.  Proof: greedily extend one pair at a time by
`deltaRoot_extend`; the accumulated used set always has `< 3n²+1` elements.
-/
set_option maxHeartbeats 2000000 in
theorem exists_private_assignment (H : TripleHost W) (hts : H.IsTripleSystem) (n : ℕ)
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
        -- Let's choose a new vertex $w$ for $p$ that is not in $Core$ and not in the image of $P$ on $s$.
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
            · convert! he₁ using 1;
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

/-- **Claim 2.1 (extension step).**  If the roots graph `H^{(2)}` (with
`t = 3n²+1`) contains `K_{n,n}`, then `H` contains a copy of `K^{(3)}_{n,n}`. -/
theorem hasK3nn_of_rootsKmm (H : TripleHost W) (hts : H.IsTripleSystem) (n : ℕ)
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

/-- **Claim 2.1.**  If `H` has no `K^{(3)}_{n,n}`, then its roots graph `H^{(2)}`
is countably colourable.  (Otherwise, by Erdős–Hajnal `eh_hasKmm` the roots graph
would contain `K_{n,n}`, and `hasK3nn_of_rootsKmm` would build a `K^{(3)}_{n,n}`.) -/
theorem rootsGraph_countColorable (H : TripleHost W) (hts : H.IsTripleSystem) (n : ℕ)
    (hfree : ¬ HasK3nn H n) : GCountColorable (rootsGraph H (3 * n ^ 2 + 1)) := by
  by_contra hnc
  rw [gCountColorable_iff_colorableBy] at hnc
  exact hfree (hasK3nn_of_rootsKmm H hts n (eh_hasKmm (rootsGraph H (3 * n ^ 2 + 1)) hnc n))

/-! ### Part A: maximal delta systems and the finitary delta-closure

The remainder of the file discharges Reiher's `k = 3` delta-system reduction
(`hasK3nn_of_uncountable`).  For each pair `{x,y}` that is *not* a size-`t`
delta-root we build a *maximal* finite delta system with root `{x,y}`; its
vertex set `witnessVerts` is finite.  Closing a set under all these witness
sets produces a *delta-closed* set, replacing the elementary submodels of
Reiher's proof.  This mirrors the finitary-closure filtration proved in
`EHBase` (`cl`, `nclosed_cl`, `cl_card_le`, `countColorable_of_smaller`). -/

/-- A finite delta system with prescribed root `f`: all edges of `H`, each
containing `f`, pairwise meeting exactly in `f`. -/
def IsRootDS (H : TripleHost W) (f : Set W) (D : Finset (Set W)) : Prop :=
  (∀ e ∈ D, e ∈ H.edges ∧ f ⊆ e) ∧
    (∀ e₁ ∈ D, ∀ e₂ ∈ D, e₁ ≠ e₂ → e₁ ∩ e₂ = f)

/-
If `f` is not the root of a size-`t` delta system, every finite delta system
with root `f` has fewer than `t` edges.
-/
theorem rootDS_card_lt (H : TripleHost W) (t : ℕ) (f : Set W)
    (hf : ¬ IsDeltaRoot H t f) (D : Finset (Set W)) (hD : IsRootDS H f D) :
    D.card < t := by
  contrapose! hf;
  use D;
  simp_all +decide [ IsRootDS ];
  exact fun x hx => hD.1 x hx |>.1

open Classical in
/-- Inserting an edge that meets every member of a root-`f` delta system exactly
in `f` yields another root-`f` delta system. -/
theorem IsRootDS_insert (H : TripleHost W) (f : Set W) (D : Finset (Set W))
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
/-- A *maximal* finite delta system with root `f` exists when `f` is not a
size-`t` root: one that no further edge of `H` can extend. -/
theorem exists_maximal_rootDS (H : TripleHost W) (t : ℕ) (f : Set W)
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
/-- A chosen maximal delta system with root `f` (junk `∅` when `f` is a root). -/
noncomputable def maxDS (H : TripleHost W) (t : ℕ) (f : Set W) : Finset (Set W) :=
  if h : ¬ IsDeltaRoot H t f then (exists_maximal_rootDS H t f h).choose else ∅

/-- The vertex set of the chosen maximal delta system with root `f`. -/
def witnessVerts (H : TripleHost W) (t : ℕ) (f : Set W) : Set W :=
  ⋃ e ∈ maxDS H t f, e

/-- Specification of `maxDS` when `f` is not a root. -/
theorem maxDS_spec (H : TripleHost W) (t : ℕ) (f : Set W) (hf : ¬ IsDeltaRoot H t f) :
    IsRootDS H f (maxDS H t f) ∧
      ∀ e ∈ H.edges, f ⊆ e → (∀ e' ∈ maxDS H t f, e ∩ e' = f) →
        e ∈ maxDS H t f := by
  rw [maxDS, dif_pos hf]
  exact (exists_maximal_rootDS H t f hf).choose_spec

/-
The witness vertex set is finite (a maximal delta system has `< t` edges,
each a triple).
-/
theorem witnessVerts_finite (H : TripleHost W) (hts : H.IsTripleSystem) (t : ℕ)
    (f : Set W) : (witnessVerts H t f).Finite := by
  by_cases h : IsDeltaRoot H t f;
  · unfold witnessVerts maxDS; aesop;
  · convert! Set.Finite.biUnion ( Finset.finite_toSet ( maxDS H t f ) ) ( fun e he => ?_ ) using 1;
    have := maxDS_spec H t f h;
    exact Set.finite_of_ncard_pos ( by rw [ hts e ( this.1.1 e he |>.1 ) ] ; norm_num )

/-- The witness vertex set is at most countable. -/
theorem witnessVerts_card_le (H : TripleHost W) (hts : H.IsTripleSystem) (t : ℕ)
    (f : Set W) : #(witnessVerts H t f) ≤ ℵ₀ := by
  have h := (witnessVerts_finite H hts t f)
  exact le_of_lt h.lt_aleph0

/-- One delta-closure step: add the witness vertices of every pair in `X`. -/
def DCloseStep (H : TripleHost W) (t : ℕ) (X : Set W) : Set W :=
  X ∪ {v | ∃ x ∈ X, ∃ y ∈ X, x ≠ y ∧ v ∈ witnessVerts H t {x, y}}

/-- The `k`-fold delta-closure step. -/
def DCloseIter (H : TripleHost W) (t : ℕ) (X : Set W) : ℕ → Set W
  | 0 => X
  | k + 1 => DCloseStep H t (DCloseIter H t X k)

/-- The finitary delta-closure of `X`. -/
def Dcl (H : TripleHost W) (t : ℕ) (X : Set W) : Set W := ⋃ k, DCloseIter H t X k

/-- `X` is *delta-closed*: it contains the witness vertices of each of its
pairs. -/
def DClosed (H : TripleHost W) (t : ℕ) (X : Set W) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≠ y → witnessVerts H t {x, y} ⊆ X

theorem subset_DCloseIter (H : TripleHost W) (t : ℕ) (X : Set W) (k : ℕ) :
    X ⊆ DCloseIter H t X k := by
  induction' k with k ih
  · rfl
  · exact Set.Subset.trans ih Set.subset_union_left

theorem DCloseIter_mono_index (H : TripleHost W) (t : ℕ) (X : Set W) {k l : ℕ}
    (h : k ≤ l) : DCloseIter H t X k ⊆ DCloseIter H t X l := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact Set.Subset.trans ih Set.subset_union_left

theorem subset_Dcl (H : TripleHost W) (t : ℕ) (X : Set W) : X ⊆ Dcl H t X :=
  Set.subset_iUnion_of_subset 0 (by rfl)

theorem Dcl_mono (H : TripleHost W) (t : ℕ) {X Y : Set W} (h : X ⊆ Y) :
    Dcl H t X ⊆ Dcl H t Y := by
  apply Set.iUnion_mono;
  intro k;
  induction' k with k ih;
  · exact h;
  · refine' Set.union_subset_union ih _;
    exact fun v hv => by obtain ⟨ x, hx, y, hy, hxy, hv ⟩ := hv; exact ⟨ x, ih hx, y, ih hy, hxy, hv ⟩ ;

/-
The delta-closure is delta-closed.
-/
theorem DClosed_Dcl (H : TripleHost W) (t : ℕ) (X : Set W) :
    DClosed H t (Dcl H t X) := by
  intro x hx y hy hxy v hv; simp_all +decide [ DClosed, Dcl ] ;
  obtain ⟨ kx, hkx ⟩ := hx; obtain ⟨ ky, hky ⟩ := hy; use Max.max kx ky + 1; simp_all +decide [ DCloseIter ] ;
  exact Set.mem_union_right _ ⟨ x, DCloseIter_mono_index _ _ _ ( le_max_left _ _ ) hkx, y, DCloseIter_mono_index _ _ _ ( le_max_right _ _ ) hky, hxy, hv ⟩

/-
The delta-closure step increases cardinality by at most `ℵ₀`.
-/
theorem DCloseStep_card_le (H : TripleHost W) (hts : H.IsTripleSystem) (t : ℕ)
    (X : Set W) : #(DCloseStep H t X) ≤ #X + ℵ₀ := by
  -- By definition of `DCloseStep`, we have `DCloseStep H t X = X ∪ {v | ∃ x ∈ X, ∃ y ∈ X, x ≠ y ∧ v ∈ witnessVerts H t {x, y}}`.
  set A := {v : W | ∃ x ∈ X, ∃ y ∈ X, x ≠ y ∧ v ∈ witnessVerts H t {x, y}} with hA_def
  have hDCloseStep : DCloseStep H t X = X ∪ A := by
    grind +locals
  generalize_proofs at *; (
  -- It suffices to show that $|A| \leq |X|^2 \cdot \aleph_0$.
  suffices hA_card : #(A) ≤ #(X × X) * Cardinal.aleph0 by
    by_cases hX : Infinite X <;> simp_all +decide [ Cardinal.mk_prod, Cardinal.mul_eq_max ];
    · refine' le_trans ( Cardinal.mk_union_le _ _ ) _ ; aesop;
    · refine' le_trans ( Cardinal.mk_union_le _ _ ) _;
      refine' add_le_add le_rfl _;
      exact Cardinal.mk_le_aleph0_iff.mpr ( Set.Finite.countable <| Set.Finite.subset ( Set.Finite.biUnion ( Set.finite_coe_iff.mp hX ) fun x hx => Set.Finite.biUnion ( Set.finite_coe_iff.mp hX ) fun y hy => Set.Finite.subset ( witnessVerts_finite H hts t { x, y } ) fun z => by aesop ) fun x hx => by aesop );
  -- By definition of $A$, we have $A \subseteq \bigcup_{p : ↥X × ↥X} witnessVerts H t {(p.1 : W), (p.2 : W)}$.
  have hA_subset : A ⊆ ⋃ p : ↥X × ↥X, witnessVerts H t {(p.1 : W), (p.2 : W)} := by
    intro v hv; obtain ⟨ x, hx, y, hy, hxy, hv ⟩ := hv; exact Set.mem_iUnion.2 ⟨ ⟨ ⟨ x, hx ⟩, ⟨ y, hy ⟩ ⟩, hv ⟩ ;
  refine' le_trans ( Cardinal.mk_le_mk_of_subset hA_subset ) _;
  refine' le_trans ( Cardinal.mk_iUnion_le _ ) _;
  refine' mul_le_mul_right _ _;
  exact ciSup_le' fun p => witnessVerts_card_le H hts t _)

/-
The delta-closure has size at most `#X + ℵ₀`.
-/
theorem Dcl_card_le (H : TripleHost W) (hts : H.IsTripleSystem) (t : ℕ)
    (X : Set W) : #(Dcl H t X) ≤ #X + ℵ₀ := by
  convert! Cardinal.mk_iUnion_le _ |> le_trans <| _;
  rotate_left;
  exact ULift ℕ;
  exact fun i => DCloseIter H t X i.down;
  · refine' le_trans ( mul_le_mul_right ( ciSup_le _ ) _ ) _;
    exact #X + ℵ₀;
    · intro x; induction' x.down with k ih <;> simp_all +decide [ DCloseIter ] ;
      refine' le_trans ( DCloseStep_card_le H hts t _ ) _;
      convert! add_le_add_right ih ℵ₀ using 1;
      · rw [ add_comm ];
      · rw [ add_comm, Cardinal.add_eq_max ];
        · rw [ Cardinal.add_eq_max ];
          · grind;
          · norm_num;
        · norm_num;
    · simp +decide [ Cardinal.mk_nat ];
  · ext; simp [Dcl]

/-
A monotone union of delta-closed sets over an initial segment stays
delta-closed.
-/
theorem DClosed_biUnion_lt {σ : Type u} [LinearOrder σ] (H : TripleHost W) (t : ℕ)
    (M : σ → Set W) (hmono : Monotone M) (hcl : ∀ b, DClosed H t (M b)) (a : σ) :
    DClosed H t (⋃ b ∈ {b : σ | b < a}, M b) := by
  intro x hx y hy hxy;
  simp_all +decide [ Set.subset_def ];
  obtain ⟨ i, hi, hx ⟩ := hx; obtain ⟨ j, hj, hy ⟩ := hy; use fun z hz => ⟨ Max.max i j, max_lt hi hj, hcl ( Max.max i j ) _ ( hmono ( le_max_left _ _ ) hx ) _ ( hmono ( le_max_right _ _ ) hy ) hxy hz ⟩ ;

/-! ### Part B: Claim 2.2 and the colourability ingredients -/

/-- An edge `e` *contains a delta-root*: two distinct vertices `u, v` with
`{u,v} ⊆ e` that form a size-`t` delta-root.  `E'` is the set of edges with a
root; `E''` its complement inside `H.edges`. -/
def hasRoot (H : TripleHost W) (t : ℕ) (e : Set W) : Prop :=
  ∃ u v, u ≠ v ∧ ({u, v} : Set W) ⊆ e ∧ IsDeltaRoot H t {u, v}

/-
**Claim 2.2 (core step).**  Let `U` be delta-closed, `x, y ∈ U`, `z ∉ U`, and
`e = {x,y,z}` an edge whose lower pair `{x,y}` is not a delta-root.  This is
impossible: the maximal delta system with root `{x,y}` lives inside `U` (by
delta-closedness), yet `e` extends it (since `z ∉ U`), contradicting maximality.
-/
theorem claim22_abstract (H : TripleHost W) (hts : H.IsTripleSystem) (t : ℕ)
    (U : Set W) (hU : DClosed H t U) (x y z : W)
    (hxU : x ∈ U) (hyU : y ∈ U) (hzU : z ∉ U)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (e : Set W) (he : e ∈ H.edges) (hxe : x ∈ e) (hye : y ∈ e) (hze : z ∈ e)
    (hnr : ¬ IsDeltaRoot H t ({x, y} : Set W)) : False := by
  -- Apply the maximality condition hmax to e.
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

/-
**Combining per-level colourings.**  If every edge of `E₀` has two vertices of
a common `rank` value `a` that a level-`a` colouring `d a` separates, then
`(W, E₀)` is `ℵ₀`-colourable (colour `v` by `d (rank v) v`).
-/
theorem colorable_combine {Idx : Type*} (rank : W → Idx) (E₀ : Set (Set W))
    (d : Idx → W → ℕ)
    (hsep : ∀ e ∈ E₀, ∃ a, ∃ u ∈ e, ∃ w ∈ e, rank u = a ∧ rank w = a ∧ d a u ≠ d a w) :
    (⟨E₀⟩ : TripleHost W).ColorableBy ℵ₀ := by
  convert! colorableBy_aleph0_of_countable _ _ _ using 1;
  exact ULift ℕ;
  exact Cardinal.mk_le_aleph0;
  exact fun v => ⟨ d ( rank v ) v ⟩;
  intro e he; obtain ⟨ a, u, hu, w, hw, hru, hrw, hne ⟩ := hsep e he; use u, hu, w, hw; aesop;

/-
**`E'` is `ℵ₀`-colourable.**  A proper `ℕ`-colouring of the roots graph
`H^{(2)}` (which exists by `rootsGraph_countColorable`) is proper for `(W, E')`,
since each `e ∈ E'` contains an adjacent pair `{u,v}` of the roots graph.
-/
theorem E'_colorable (H : TripleHost W) (hts : H.IsTripleSystem) (n : ℕ)
    (hfree : ¬ HasK3nn H n) :
    (⟨{e | e ∈ H.edges ∧ hasRoot H (3 * n ^ 2 + 1) e}⟩ : TripleHost W).ColorableBy ℵ₀ := by
  obtain ⟨c, hc⟩ := rootsGraph_countColorable H hts n hfree;
  convert! colorableBy_aleph0_of_countable _ _ _ using 1;
  exact ULift ℕ;
  exact Cardinal.mk_le_aleph0;
  exact fun x => ⟨ c x ⟩;
  intro e he; obtain ⟨ u, v, huv, huv', huv'' ⟩ := he.2; simp_all +decide [ rootsGraph ] ;
  exact ⟨ u, huv' ( Set.mem_insert _ _ ), v, huv' ( Set.mem_insert_of_mem _ ( Set.mem_singleton _ ) ), hc u v huv ( Or.inl huv'' ) ⟩

/-- The triple system induced by `H` on a subset `S`, living on the subtype `↑S`. -/
def Hsub (H : TripleHost W) (S : Set W) : TripleHost ↑S :=
  ⟨{s | Subtype.val '' s ∈ H.edges}⟩

/-
The induced system on `S` is a triple system.
-/
theorem Hsub_isTripleSystem (H : TripleHost W) (hts : H.IsTripleSystem) (S : Set W) :
    (Hsub H S).IsTripleSystem := by
  intro s hs
  simpa only [Set.ncard_image_of_injective _ Subtype.val_injective] using hts (Subtype.val '' s) hs

/-
A `K^{(3)}_{n,n}` in the induced system on `S` lifts to one in `H`.
-/
theorem Hsub_hasK3nn (H : TripleHost W) (S : Set W) (n : ℕ)
    (h : HasK3nn (Hsub H S) n) : HasK3nn H n := by
  obtain ⟨ g, hg_inj, hg_edge ⟩ := h;
  refine' ⟨ fun x => g x, _, _ ⟩;
  · exact Subtype.coe_injective.comp hg_inj;
  · convert! hg_edge using 1;
    simp +decide [ Hsub, Set.image_insert_eq, Set.image_singleton ]

/-
For an edge `e ⊆ S`, its preimage in `↑S` is an edge of the induced system
with image `e`.
-/
theorem Hsub_edge_of_subset (H : TripleHost W) (S : Set W) (e : Set W)
    (he : e ∈ H.edges) (hsub : e ⊆ S) :
    ∃ s : Set ↑S, Subtype.val '' s = e ∧ s ∈ (Hsub H S).edges := by
  -- Let $s$ be the preimage of $e$ under the inclusion map from $S$ to $W$.
  use {x : S | x.val ∈ e};
  -- By definition of `Hsub`, we know that `{x | x.val ∈ e}` is an edge in `Hsub H S` if and only if `e` is an edge in `H`.
  unfold Hsub;
  aesop

/-- **Minimality gives level colourings.**  Any subset `S` of size `< #W` carries
a `ℕ`-colouring proper for the edges of `H` contained in `S` (the induced triple
system on `S` is `K^{(3)}_{n,n}`-free and smaller, hence `ℵ₀`-colourable). -/
theorem sub_colorable_gives (H : TripleHost W) (hts : H.IsTripleSystem) (n : ℕ)
    (hfree : ¬ HasK3nn H n)
    (minim : ∀ (W' : Type u) (H' : TripleHost W'), #W' < #W → H'.IsTripleSystem →
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

/-
A triple system on an at-most-countable vertex type is `ℵ₀`-colourable
(colour vertices injectively).
-/
theorem tripleSystem_colorable_of_le_aleph0 (H : TripleHost W)
    (hts : H.IsTripleSystem) (h : #W ≤ ℵ₀) : H.ColorableBy ℵ₀ := by
  obtain ⟨c, hc⟩ : ∃ c : W → ℕ, ∀ e ∈ H.edges, ∃ u ∈ e, ∃ v ∈ e, c u ≠ c v := by
    cases' Cardinal.le_mk_iff_exists_set.mp h with S hS;
    cases' Cardinal.eq.1 hS.symm with f hf;
    use fun w => (f w).val.down;
    intro e he; have := hts e he; rw [ Set.ncard_eq_three ] at this; obtain ⟨ a, b, c, hab, hac, hbc, rfl ⟩ := this; use a, by simp +decide, b, by simp +decide; ; simp +decide [ hab ] ;
    exact fun h => hab <| f.injective <| Subtype.ext h;
  exact hgCountColorable_iff H |>.1 ⟨ c, hc ⟩

/-! ### Part C: the rainbow grid and grid-to-`K^{(3)}_{n,n}` -/

/-
Assembling a `K^{(3)}_{n,n}` from an injective grid of left cores `X`, right
cores `Y`, and private vertices `P`.
-/
theorem hasK3nn_from_grid (H : TripleHost W) (n : ℕ) (X Y : Fin n → W)
    (P : Fin n → Fin n → W)
    (hInj : Function.Injective
      (Sum.elim (Sum.elim X Y) (fun p : Fin n × Fin n => P p.1 p.2)))
    (hedge : ∀ i j, ({X i, Y j, P i j} : Set W) ∈ H.edges) : HasK3nn H n := by
  use Sum.elim (Sum.elim X Y) (fun p => P p.1 p.2);
  grind

/-
**Generic greedy selection.**  Build `n` distinct elements, each satisfying a
unary predicate `Q` and pairwise related by `R`, from a one-step extension
property.
-/
theorem exists_finset_pairwise {α : Type*} [Fintype α] [DecidableEq α]
    (Q : α → Prop) (R : α → α → Prop) (n : ℕ)
    (hstep : ∀ D : Finset α, D.card < n → (∀ x ∈ D, Q x) →
      ∃ z, z ∉ D ∧ Q z ∧ ∀ x ∈ D, R x z ∧ R z x) :
    ∃ C : Finset α, C.card = n ∧ (∀ x ∈ C, Q x) ∧
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y → R x y := by
  induction' n with n ih;
  · exact ⟨ ∅, rfl, by simp +decide ⟩;
  · -- Apply the induction hypothesis with hstep modified to use n instead of n+1.
    obtain ⟨C, hC⟩ := ih (fun D hD hQ => hstep D (Nat.lt_succ_of_lt hD) hQ);
    obtain ⟨z, hz⟩ := hstep C (by linarith) hC.2.1;
    use Insert.insert z C;
    grind

open Classical in
/-- **Double counting of column agreement.**  For a fixed column `b`, the total
number of `(a, z)` with `P a b = P a z` is `≤ q*(t-1)` (each row `a` has `< t`
columns of any given value). -/
theorem sum_agree_le {V : Type*} (t q : ℕ) (P : Fin q → Fin q → V)
    (hrow : ∀ (a : Fin q) (v : V), (Finset.univ.filter (fun b => P a b = v)).card < t)
    (b : Fin q) :
    ∑ z : Fin q, (Finset.univ.filter (fun a => P a b = P a z)).card ≤ q * (t - 1) := by
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ z : Fin q, (Finset.univ.filter (fun a => P a b = P a z)).card = ∑ a : Fin q, (Finset.univ.filter (fun z => P a b = P a z)).card := by
    simp +decide only [Finset.card_filter];
    exact Finset.sum_comm;
  exact h_fubini.symm ▸ le_trans ( Finset.sum_le_sum fun i _ => show Finset.card ( Finset.filter ( fun z => P i b = P i z ) Finset.univ ) ≤ t - 1 from Nat.le_sub_one_of_lt ( by simpa [ eq_comm ] using hrow i ( P i b ) ) ) ( by simp +decide [ mul_comm ] ) ;

open Classical in
/-- **Column step.**  Given `< n` chosen columns, there is a new column agreeing
with each on `< n*t` rows (few columns are `n*t`-twins of any fixed column, by
`sum_agree_le`). -/
theorem cols_step {V : Type*} (n t q : ℕ) (ht : 1 ≤ t) (hn : 1 ≤ n) (hq : n ^ 2 * t ≤ q)
    (P : Fin q → Fin q → V)
    (hrow : ∀ (a : Fin q) (v : V), (Finset.univ.filter (fun b => P a b = v)).card < t)
    (D : Finset (Fin q)) (hD : D.card < n) :
    ∃ z, z ∉ D ∧ ∀ x ∈ D,
      (Finset.univ.filter (fun a => P a x = P a z)).card < n * t := by
  -- By `sum_agree_le` and `bad union bound`, we can find such a $z$.
  have h_bad_card : ∑ x ∈ D, ∑ z : Fin q, (Finset.univ.filter (fun a => P a x = P a z)).card ≤ D.card * q * (t - 1) := by
    convert! Finset.sum_le_sum fun x hx => sum_agree_le t q P hrow x using 1;
    simp +decide [ mul_assoc ];
  -- By `bad union bound`, we can find such a $z$.
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
/-- **Row step.**  Given `< n` chosen rows, all internally rainbow on the fixed
columns `B` and pairwise non-crossing, there is a new such row (internal
collisions bounded by `hpair`, cross collisions by the column bound). -/
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
  -- Define the "bad" rows: `I := Finset.univ.filter (fun z => ∃ k l : Fin n, k ≠ l ∧ P z (B k) = P z (B l))` (internally non-rainbow), `C := Finset.univ.filter (fun z => ∃ x ∈ D, ∃ k l : Fin n, P x (B k) = P z (B l) ∨ P z (B k) = P x (B l))` (crossing some chosen row)
  set I := Finset.biUnion (Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2)) (fun p => Finset.univ.filter (fun z => P z (B p.1) = P z (B p.2)))
  set C := Finset.biUnion D (fun x => Finset.biUnion (Finset.univ ×ˢ Finset.univ) (fun p : Fin n × Fin n => Finset.univ.filter (fun z => P z (B p.2) = P x (B p.1)) ∪ Finset.univ.filter (fun z => P z (B p.1) = P x (B p.2))));
  -- Bound `I.card ≤ n ^ 3 * t` and `C.card ≤ 2 * n ^ 3 * t`.
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
  -- Then `Bad.card ≤ D.card + I.card + C.card ≤ (n-1) + n^3*t + 2*n^3*t < 3*n^3*t + n ≤ q`.
  have hBad : (D ∪ I ∪ C).card < q := by
    grind +qlia;
  obtain ⟨ z, hz ⟩ := Finset.exists_of_ssubset ( Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.subset_univ ( D ∪ I ∪ C ), by aesop_cat ⟩ );
  simp +zetaDelta at *;
  exact ⟨ z, hz.1, hz.2.1, fun x hx => ⟨ fun k l => Ne.symm ( hz.2.2 x hx k l |>.1 ), fun k l => hz.2.2 x hx k l |>.2 ⟩ ⟩

open Classical in
/-- **Rainbow grid lemma.**  A `q × q` matrix `P` in which every value occurs
fewer than `t` times in each row and in each column contains an `n × n` rainbow
subgrid (an injective `A × B` block).  Proof: choose `n` columns pairwise
agreeing on `< n*t` rows (possible by the row bound), then greedily choose `n`
rows keeping all grid entries distinct (possible by the column bound and the
small column-agreement). -/
theorem greedy_rainbow {V : Type*} (n t q : ℕ) (ht : 1 ≤ t)
    (hq : 4 * t * n ^ 3 + n ^ 2 + n ≤ q) (P : Fin q → Fin q → V)
    (hrow : ∀ (a : Fin q) (v : V), (Finset.univ.filter (fun b => P a b = v)).card < t)
    (hcol : ∀ (b : Fin q) (v : V), (Finset.univ.filter (fun a => P a b = v)).card < t) :
    ∃ A B : Fin n → Fin q, Function.Injective A ∧ Function.Injective B ∧
      ∀ i j i' j', P (A i) (B j) = P (A i') (B j') → i = i' ∧ j = j' := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  -- Stage 1: choose `n` pairwise-`< n*t`-agreeing columns.
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
  -- Extract the injective column map `B`.
  set B : Fin n → Fin q := ⇑(Ccol.orderEmbOfFin hCcard) with hBdef
  have hBinj : Function.Injective B := (Ccol.orderEmbOfFin hCcard).injective
  have hBmem : ∀ i, B i ∈ Ccol := fun i => Ccol.orderEmbOfFin_mem hCcard i
  have hpairB : ∀ i i' : Fin n, i ≠ i' →
      (Finset.univ.filter (fun a => P a (B i) = P a (B i'))).card < n * t :=
    fun i i' hii => hCpair (B i) (hBmem i) (B i') (hBmem i') (fun h => hii (hBinj h))
  -- Stage 2: choose `n` rows, internally rainbow on `B` and pairwise non-crossing.
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

/-- The *layer graph* at level `i`: `x ~ y` iff both have rank `i` and there is a
lower vertex `z` with `{x,y,z}` an `E''`-edge. -/
def layerGraph {Idx : Type*} [LT Idx] (H : TripleHost W) (t : ℕ) (rank : W → Idx)
    (i : Idx) : SimpleGraph W :=
  SimpleGraph.fromRel (fun x y =>
    rank x = i ∧ rank y = i ∧ ∃ z, rank z < i ∧ ({x, y, z} : Set W) ∈ H.edges ∧
      ¬ hasRoot H t ({x, y, z} : Set W))

/-
**The delta-closed filtration and Claim 2.2, packaged.**  For an uncountable
triple system there is a rank function into a well-order such that (A) every rank
level is smaller than the whole, and (B) no `E''`-edge has a unique top vertex:
if `x, y` both have rank `< rank z`, `x ≠ y`, `{x,y}` is not a delta-root, and
`{x,y,z}` is an edge, that is impossible (Claim 2.2).
-/
theorem exists_delta_filtration (H : TripleHost W) (hts : H.IsTripleSystem) (t : ℕ)
    (hbig : ℵ₀ < #W) :
    ∃ (Idx : Type u) (_ : LinearOrder Idx) (_ : WellFoundedLT Idx) (rank : W → Idx),
      (∀ a : Idx, #({v | rank v = a} : Set W) < #W) ∧
      (∀ (x y z : W), rank x < rank z → rank y < rank z → x ≠ y →
        ¬ IsDeltaRoot H t ({x, y} : Set W) →
        ∀ e ∈ H.edges, x ∈ e → y ∈ e → z ∈ e → False) := by
  -- Let `Idx := (#W).ord.ToType`.
  set Idx := (#W).ord.ToType;
  -- Set `M : Idx → Set W := fun a => Dcl H t (e '' {b | b ≤ a})`.
  obtain ⟨e, he⟩ : ∃ e : Idx ≃ W, True := by
    refine' ⟨ _, trivial ⟩;
    exact Classical.choice ( Cardinal.eq.1 <| by simp +decide [ Idx ] )
  set M : Idx → Set W := fun a => Dcl H t (Set.image e {b | b ≤ a});
  -- Show that `M` satisfies the required properties.
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
        convert! Cardinal.mk_Iio_ord_toType a using 1;
      have h_card_Iic : Cardinal.mk (Set.Iic a) = Cardinal.mk (Set.Iio a) + 1 := by
        rw [ ← Cardinal.mk_singleton ( a : Idx ), ← Cardinal.mk_union_of_disjoint ];
        · congr with x ; simp +decide [ le_iff_lt_or_eq, eq_comm ];
        · exact Set.disjoint_singleton_right.mpr (by simp)
      convert! Cardinal.add_lt_of_lt _ ‹_› _ using 1;
      · exact le_of_lt hbig;
      · exact lt_of_le_of_lt ( by norm_num ) hbig
    have h_card_M : #(M a) ≤ #(Set.image e {b | b ≤ a}) + ℵ₀ := by
      convert! Dcl_card_le H hts t ( Set.image e { b | b ≤ a } ) using 1
    have h_card_M_lt : #(M a) < #W := by
      refine' lt_of_le_of_lt h_card_M _;
      refine' lt_of_le_of_lt ( add_le_add h_card_image le_rfl ) _;
      convert! Cardinal.add_lt_of_lt _ _ _ using 1;
      · exact le_of_lt hbig;
      · exact h_card_Iic;
      · exact hbig
    exact h_card_M_lt
  have hM_cover : ∀ x, x ∈ M (e.symm x) := by
    intro x
    simp [M, subset_Dcl];
    exact subset_Dcl _ _ _ ⟨ e.symm x, by simp +decide, by simp +decide ⟩;
  -- Define `rank : W → Idx` as the least index such that `x ∈ M a`.
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

/-
**A monochromatic column/row of size `t` is a delta-root.**  If `t` distinct
vertices `x` all form an edge `{x, u, w}` (with `u ≠ w`, `x ∉ {u,w}`), then
`{u,w}` is a size-`t` delta-root, so each such edge `hasRoot` — contradicting the
assumption that none does.
-/
theorem delta_root_contra (H : TripleHost W) (t : ℕ) (ht : 0 < t) (u w : W) (huw : u ≠ w)
    (S : Finset W) (hScard : t ≤ S.card) (hSne : ∀ x ∈ S, x ≠ u ∧ x ≠ w)
    (hedge : ∀ x ∈ S, ({x, u, w} : Set W) ∈ H.edges)
    (hnr : ∀ x ∈ S, ¬ hasRoot H t ({x, u, w} : Set W)) : False := by
  -- By assumption, $D := \{e \mid e \in H.edges \land \{u, w\} \subseteq e\}$ has size at least $t$, so $\{u, w\}$ is a delta-root.
  have h_delta_root : IsDeltaRoot H t ({u, w} : Set W) := by
    -- By assumption, $D := \{ {x, u, w} \mid x \in S \}$ has size at least $t$, so $\{u, w\}$ is a delta-root.
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

/-
**Layer adjacency for an `E''`-edge that is not level-flat.**  An `E''`-edge
whose vertices do not all share a rank has (by Claim 2.2) exactly two top vertices
`x, y` of some rank `i`, adjacent in the layer graph `layerGraph .. i`.
-/
theorem Ess_adj {Idx : Type u} [LinearOrder Idx] (H : TripleHost W)
    (hts : H.IsTripleSystem) (t : ℕ) (rank : W → Idx)
    (hclaim : ∀ (x y z : W), rank x < rank z → rank y < rank z → x ≠ y →
        ¬ IsDeltaRoot H t ({x, y} : Set W) →
        ∀ e ∈ H.edges, x ∈ e → y ∈ e → z ∈ e → False)
    (e : Set W) (heE : e ∈ H.edges) (hnr : ¬ hasRoot H t e)
    (hne : ¬ ∃ a, ∀ v ∈ e, rank v = a) :
    ∃ (i : Idx) (x y : W), x ∈ e ∧ y ∈ e ∧ rank x = i ∧ rank y = i ∧
      (layerGraph H t rank i).Adj x y := by
  obtain ⟨ p, q, r, hpq, hpr, hqr, he ⟩ := Set.ncard_eq_three.mp ( hts e heE );
  -- By `key`, no vertex is a strict maximum over the other two.
  have h_no_max : ¬(rank p > rank q ∧ rank p > rank r) ∧ ¬(rank q > rank p ∧ rank q > rank r) ∧ ¬(rank r > rank p ∧ rank r > rank q) := by
    refine' ⟨ _, _, _ ⟩ <;> intro h <;> simp_all +decide [ hasRoot ];
    · exact hclaim q r p h.1 h.2 ( by tauto ) ( hnr q r ( by tauto ) ( by simp +decide [ Set.insert_subset_iff ] ) ) _ heE ( by simp +decide ) ( by simp +decide ) ( by simp +decide );
    · exact hclaim p r q h.1 h.2 ( by tauto ) ( hnr p r ( by tauto ) ( by simp +decide [ Set.insert_subset_iff ] ) ) _ heE ( by simp +decide ) ( by simp +decide ) ( by simp +decide );
    · exact hclaim p q r h.1 h.2 ( by tauto ) ( hnr p q ( by tauto ) ( by simp +decide [ Set.insert_subset_iff ] ) ) _ heE ( by simp +decide ) ( by simp +decide ) ( by simp +decide );
  -- By `hne`, the ranks are not all equal.
  obtain ⟨i, hi⟩ : ∃ i : Idx, (rank p = i ∧ rank q = i ∧ rank r ≠ i) ∨ (rank p = i ∧ rank r = i ∧ rank q ≠ i) ∨ (rank q = i ∧ rank r = i ∧ rank p ≠ i) := by
    contrapose! hne; simp_all +decide ;
    grind +splitImp;
  rcases hi with ( ⟨ hp, hq, hr ⟩ | ⟨ hp, hr, hq ⟩ | ⟨ hq, hr, hp ⟩ ) <;> simp_all +decide [ layerGraph ];
  · grind +splitImp;
  · refine' Or.inl ( Or.inl ⟨ q, lt_of_le_of_ne h_no_max hq, _, _ ⟩ );
    · convert! heE using 1 ; ext ; simp +decide [ *, or_comm, or_left_comm, or_assoc ];
    · convert! hnr using 1;
      simp +decide [ Set.insert_comm, Set.pair_comm ];
  · refine' Or.inr ⟨ Ne.symm hqr, Or.inl ⟨ p, lt_of_le_of_ne h_no_max hp, _, _ ⟩ ⟩;
    · convert! heE using 1 ; ext ; simp +decide [ *, or_comm, or_left_comm, or_assoc ];
    · convert! hnr using 1;
      simp +decide [ Set.Subset.antisymm_iff, Set.subset_def, hasRoot ];
      grind

/-
Injectivity of the assembled `K^{(3)}_{n,n}` grid: cores have rank `i₀`,
privates have rank `< i₀`, and the grid privates are distinct.
-/
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

/-- `K^{(3)}_{n,n}` is trivially present for `n = 0`. -/
theorem hasK3nn_zero (H : TripleHost W) : HasK3nn H 0 := by
  refine ⟨fun x => (by rcases x with (i | i) | ⟨i, _⟩ <;> exact i.elim0), ?_, ?_⟩
  · rintro ((i | i) | ⟨i, _⟩) _ _ <;> exact i.elim0
  · rintro i; exact i.elim0

/-! ### Part D: the delta-system reduction and E4 -/

/-- **The inductive step of Reiher's `k = 3` argument.**  A `K^{(3)}_{n,n}`-free
triple system of uncountable chromatic number, minimal in cardinality, yields a
contradiction.  This is the delta-closed filtration (Part A), Claim 2.2, and the
final rainbow counting. -/
theorem hasK3nn_step (H : TripleHost W) (hts : H.IsTripleSystem) (n : ℕ)
    (hbig : ℵ₀ < #W) (huc : H.UncountablyChromatic) (hfree : ¬ HasK3nn H n)
    (minim : ∀ (W' : Type u) (H' : TripleHost W'), #W' < #W → H'.IsTripleSystem →
       ¬ HasK3nn H' n → H'.ColorableBy ℵ₀) : False := by
  classical
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact absurd (hasK3nn_zero H) hfree
    · exact hn
  -- E' colourable, E'' uncountably chromatic
  have hE'col := E'_colorable H hts n hfree
  have hE''uc := uncountablyChromatic_diff H.edges
      {e | e ∈ H.edges ∧ hasRoot H (3 * n ^ 2 + 1) e} huc hE'col
  obtain ⟨Idx, instLO, instWF, rank, hlevel, hclaim⟩ :=
    exists_delta_filtration H hts (3 * n ^ 2 + 1) hbig
  letI := instLO
  letI := instWF
  -- level colourings
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
  -- level-flat part is colourable
  have hEstarcol :
      (⟨{e | e ∈ E'' ∧ ∃ a, ∀ v ∈ e, rank v = a}⟩ : TripleHost W).ColorableBy ℵ₀ := by
    apply colorable_combine rank _ dstar
    rintro e ⟨heE'', a, ha⟩
    obtain ⟨u, hu, w, hw, huw⟩ := hdstar a e heE''.1 (fun v hv => ha v hv)
    exact ⟨a, u, hu, w, hw, ha u hu, ha w hw, huw⟩
  -- some layer is uncountably chromatic
  have hExists : ∃ i₀ : Idx,
      ¬ (SimpleGraph.toHG (layerGraph H (3 * n ^ 2 + 1) rank i₀)).ColorableBy ℵ₀ := by
    by_contra hall
    push Not at hall
    have hlayerc : ∀ i : Idx, ∃ c : W → ℕ,
        ∀ x y, (layerGraph H (3 * n ^ 2 + 1) rank i).Adj x y → c x ≠ c y :=
      fun i => (gCountColorable_iff_colorableBy _).2 (hall i)
    choose dlayer hdlayer using hlayerc
    have hEsscol :
        (⟨E'' \ {e | e ∈ E'' ∧ ∃ a, ∀ v ∈ e, rank v = a}⟩ : TripleHost W).ColorableBy ℵ₀ := by
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
  -- Erdős–Hajnal: the layer graph contains `K_{q,q}`
  set q := 4 * (3 * n ^ 2 + 1) * n ^ 3 + n ^ 2 + n with hqdef
  obtain ⟨a, b, hainj, hbinj, hab, hadj⟩ :=
    eh_hasKmm (layerGraph H (3 * n ^ 2 + 1) rank i₀) hi₀ q
  have hqpos : 0 < q := by positivity
  -- extract private vertices
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
  -- column bound
  have hcol : ∀ (j : Fin q) (v : W),
      (Finset.univ.filter (fun i => P i j = v)).card < (3 * n ^ 2 + 1) := by
    intro j v
    by_contra hge
    push Not at hge
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
  -- row bound
  have hrow : ∀ (i : Fin q) (v : W),
      (Finset.univ.filter (fun j => P i j = v)).card < (3 * n ^ 2 + 1) := by
    intro i v
    by_contra hge
    push Not at hge
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
  -- rainbow grid
  obtain ⟨A, B, hAinj, hBinj, hgrid⟩ :=
    greedy_rainbow n (3 * n ^ 2 + 1) q (by omega) (le_of_eq hqdef.symm) P hrow hcol
  -- assemble `K^{(3)}_{n,n}`, contradiction
  refine hfree (hasK3nn_from_grid H n (fun i => a (A i)) (fun j => b (B j))
    (fun i j => P (A i) (B j)) ?_ ?_)
  · exact grid_injective rank n q i₀ a b A B P hainj hbinj hAinj hBinj hab hgrid
      (fun k => hPra k ⟨0, hqpos⟩) (fun k => hPrb ⟨0, hqpos⟩ k)
      (fun i j => hPrz (A i) (B j))
  · intro i j; exact hPedge (A i) (B j)

/-- **The delta-system theorem.**  Every triple system of uncountable chromatic
number contains a copy of `K^{(3)}_{n,n}` (Reiher's Theorem 1.2, `k = 3`). -/
theorem hasK3nn_of_uncountable (H : TripleHost W) (hts : H.IsTripleSystem)
    (huc : H.UncountablyChromatic) (n : ℕ) : HasK3nn H n := by
  have key : ∀ κ : Cardinal.{u}, ∀ (W : Type u) (H : TripleHost W),
      #W = κ → H.IsTripleSystem → H.UncountablyChromatic → HasK3nn H n := by
    refine fun κ => Cardinal.lt_wf.induction
      (C := fun κ => ∀ (W : Type u) (H : TripleHost W),
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
/-- **E4 (Reiher, `k = 3`).**  `K^{(3)}_{n,n}` is obligatory for every `n`. -/
theorem e4_Reiher : E4_Reiher.{u} := by
  intro n W H hts huc
  exact hasK3nn_embeds H n (hasK3nn_of_uncountable H hts huc n)

end TripleSystem593

end

section

open Cardinal

namespace TripleSystem593

open Classical

universe u

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
  simp_all +decide [ FTS.reduce ];
  grind +suggestions

theorem expansion_edge_cases {VJ : Type} [Fintype VJ] [DecidableEq VJ] (J : SimpleGraph VJ)
    [DecidableRel J.Adj] {s : Finset ((graphExpansion J).V)}
    (hs : s ∈ (graphExpansion J).edges) :
    ∃ e : {x : Sym2 VJ // x ∈ J.edgeFinset},
      s = {Sum.inl (Quot.out e.1).1, Sum.inl (Quot.out e.1).2, Sum.inr e} := by
  unfold graphExpansion at hs; aesop;

abbrev amalgEmbG (F G : FTS) (x : F.V) (y : G.V) : G.V ↪ (F.amalgamate G x y).V :=
  ⟨fun b => if h : b = y then Sum.inl x else Sum.inr ⟨b, h⟩, by
    intro a b hab
    simp only at hab
    by_cases ha : a = y <;> by_cases hb : b = y
    · rw [ha, hb]
    · rw [dif_pos ha, dif_neg hb] at hab; exact absurd hab Sum.inl_ne_inr
    · rw [dif_neg ha, dif_pos hb] at hab; exact absurd hab Sum.inr_ne_inl
    · rw [dif_neg ha, dif_neg hb] at hab; exact congrArg Subtype.val (Sum.inr_injective hab)⟩

end TripleSystem593

end

section

/-!
# Sub-systems on a subset of edges

For the reconstruction step of the finite bridge decomposition we need to split
a finite triple system along its edges.  Given a finite triple system `F` and a
set `S` of its edges, `FTS.restrict F S` is the sub-triple-system with edge set
`S` and vertex set the vertices incident to some edge of `S`.

This file develops `FTS.restrict` and the reconstruction isomorphisms:

* a partition of the edges into two parts with no shared vertex gives a disjoint
  union;
* a partition whose only shared vertex is a single glue point gives a one-point
  amalgamation.
-/

open Cardinal

namespace TripleSystem593

open Classical

universe u

/-- The intrinsic conditions together with the absence of isolated vertices;
this is the predicate maintained by the reconstruction induction. -/
def ReconOK (F : FTS) : Prop :=
  F.Linear ∧ (∀ x : F.V, ¬ F.Isolated x) ∧
  (∀ ed : {e : Finset F.V // e ∈ F.edges}, ∃ w ∈ ed.1, IsBridgeInc F w ed) ∧
  (∀ c : BergeCycle F, Even c.m)

/-- The sub-triple-system on a set `S` of edges of `F`: vertices are those
incident to some edge of `S`. -/
noncomputable abbrev FTS.restrict (F : FTS) (S : Finset {e : Finset F.V // e ∈ F.edges}) : FTS where
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

/-
Membership of an edge of `F.restrict S`.
-/
theorem FTS.mem_restrict_edges {F : FTS} {S : Finset {e : Finset F.V // e ∈ F.edges}}
    {s : Finset (F.restrict S).V} :
    s ∈ (F.restrict S).edges ↔
      ∃ e ∈ S, s = Finset.subtype (fun v => ∃ e' ∈ S, v ∈ e'.1) e.1 := by
  simp [FTS.restrict, Finset.mem_image, Finset.mem_attach];
  grind

/-
The number of edges of `F.restrict S` is `S.card`.
-/
theorem FTS.restrict_edges_card {F : FTS} (S : Finset {e : Finset F.V // e ∈ F.edges}) :
    (F.restrict S).edges.card = S.card := by
  rw [ FTS.restrict, Finset.card_image_of_injOn ];
  · exact Finset.card_attach;
  · intro e₁ he₁ e₂ he₂ h_eq; simp_all +decide [ Finset.ext_iff ] ;
    grind +suggestions

/-
Restriction is linear when `F` is.
-/
theorem FTS.restrict_linear {F : FTS} (S : Finset {e : Finset F.V // e ∈ F.edges})
    (hlin : F.Linear) : (F.restrict S).Linear := by
  intro s₁ hs₁ s₂ hs₂ hne;
  convert! hlin _ _ _ _ _;
  rotate_left;
  exact s₁.map ( Function.Embedding.subtype fun v => ∃ e' ∈ S, v ∈ e'.1 );
  rotate_left;
  exact s₂.map ( Function.Embedding.subtype fun v => ∃ e' ∈ S, v ∈ e'.1 );
  · obtain ⟨ e, he, rfl ⟩ := FTS.mem_restrict_edges.mp hs₂;
    grind +suggestions;
  · exact fun h => hne <| Finset.map_injective ( Function.Embedding.subtype _ ) h;
  · rw [ ← Finset.map_inter ];
    rw [ Finset.card_map ];
  · obtain ⟨ e₁, he₁, rfl ⟩ := FTS.mem_restrict_edges.mp hs₁;
    convert! e₁.2 using 1;
    ext; simp [Finset.mem_map, Finset.mem_subtype];
    exact fun h => ⟨ e₁.1, ⟨ e₁.2, he₁ ⟩, h ⟩

/-
Restriction has no isolated vertices (its vertices are incident by
construction).
-/
theorem FTS.restrict_no_isolated {F : FTS} (S : Finset {e : Finset F.V // e ∈ F.edges})
    (v : (F.restrict S).V) : ¬ (F.restrict S).Isolated v := by
  have h_isolated : ¬(F.restrict S).Isolated v := by
    -- v.2 : ∃ e ∈ S, v.1 ∈ e.1; take s := Finset.subtype (fun v => ∃ e' ∈ S, v ∈ e'.1) e.1.
    obtain ⟨e, heS, hev⟩ := v.2
    let s := Finset.subtype (fun v => ∃ e' ∈ S, v ∈ e'.1) e.1
    -- s ∈ (F.restrict S).edges by FTS.mem_restrict_edges (witness e ∈ S)
    have hs : s ∈ (F.restrict S).edges := by
      exact FTS.mem_restrict_edges.mpr ⟨ e, heS, rfl ⟩
    -- s ≤ v.1, so v ∈ s (Finset.mem_subtype)
    have hv_s : v ∈ s := by
      exact Finset.mem_subtype.mpr ( by aesop )
    -- unfold FTS.Isolated and use hs,hv_s
    -- FTS.Isolated G v := ∀ e ∈ G.edges, v ∉ e
    unfold FTS.Isolated
    push Not
    exact ⟨s, hs, hv_s⟩;
  grind

/-
The subtype-inclusion image of a `restrict`-edge is an `F`-edge (in fact one
of `S`).
-/
theorem FTS.restrict_edge_map_mem {F : FTS} {S : Finset {e : Finset F.V // e ∈ F.edges}}
    {d : Finset (F.restrict S).V} (hd : d ∈ (F.restrict S).edges) :
    d.map (Function.Embedding.subtype (fun v => ∃ e' ∈ S, v ∈ e'.1)) ∈ F.edges := by
  obtain ⟨ e, heS, rfl ⟩ := FTS.mem_restrict_edges.mp hd;
  grind +suggestions

/-- Transport a Berge cycle of a restriction up to `F` (same length). -/
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

/-- Restriction has only even Berge cycles when `F` does. -/
theorem FTS.restrict_even {F : FTS} (S : Finset {e : Finset F.V // e ∈ F.edges})
    (hev : ∀ c : BergeCycle F, Even c.m) (c : BergeCycle (F.restrict S)) : Even c.m :=
  hev (BergeCycle.ofRestrict c)

/-
Each hyperedge-node of a restriction is incident with a bridge, when `F` is
bridge-incident.
-/
theorem FTS.restrict_bridge {F : FTS} (S : Finset {e : Finset F.V // e ∈ F.edges})
    (hbr : ∀ ed : {e : Finset F.V // e ∈ F.edges}, ∃ w ∈ ed.1, IsBridgeInc F w ed)
    (ed : {e : Finset (F.restrict S).V // e ∈ (F.restrict S).edges}) :
    ∃ w ∈ ed.1, IsBridgeInc (F.restrict S) w ed := by
  let incl : (F.restrict S).V ↪ F.V := Function.Embedding.subtype _
  let E : F.edges := ⟨ed.1.map incl, FTS.restrict_edge_map_mem ed.2⟩
  obtain ⟨w, hw, hbridge⟩ := hbr E
  obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hw
  refine ⟨v, hv, hv, ?_⟩
  rintro ⟨c, i, hi, hpt⟩
  apply hbridge.2
  refine ⟨BergeCycle.ofRestrict c, i, ?_, ?_⟩
  · exact Subtype.ext (congrArg (fun d : (F.restrict S).edges => d.val.map incl) hi)
  · exact hpt.imp (congrArg incl) (congrArg incl)

/-- The restriction of a `ReconOK`-input system is `ReconOK`. -/
theorem FTS.restrict_reconOK {F : FTS} (S : Finset {e : Finset F.V // e ∈ F.edges})
    (hlin : F.Linear)
    (hbr : ∀ ed : {e : Finset F.V // e ∈ F.edges}, ∃ w ∈ ed.1, IsBridgeInc F w ed)
    (hev : ∀ c : BergeCycle F, Even c.m) : ReconOK (F.restrict S) :=
  ⟨FTS.restrict_linear S hlin, FTS.restrict_no_isolated S,
    FTS.restrict_bridge S hbr, FTS.restrict_even S hev⟩

end TripleSystem593

end

section

/-!
# Reconstruction from a separation

Given a finite triple system `F` and a partition of its edges into `S` and its
complement, we reconstruct `F` (up to isomorphism) as a disjoint union or a
one-point amalgamation of the two restrictions, according to whether the two
sides share `0` or exactly `1` vertex.
-/

open Cardinal

namespace TripleSystem593

open Classical

universe u

variable {F : FTS} (S : Finset {e : Finset F.V // e ∈ F.edges})

/-- The vertex predicate "incident to an edge of `S`". -/
abbrev IncS (v : F.V) : Prop := ∃ e ∈ S, v ∈ e.1

variable (g : F.V)

/-- The amalgamation equivalence: classify each vertex by side, sending the glue
vertex `g` to the left copy. -/
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
    intro v; by_cases hv : IncS S v <;> simp [hv]
  right_inv := by
    rintro (⟨v, hv⟩ | ⟨⟨v, hv⟩, hne⟩)
    · change (if h : IncS S v then _ else _) = _
      exact dif_pos (show IncS S v from hv)
    · change (if h : IncS S v then _ else _) = _
      apply dif_neg
      exact fun h => hne (Subtype.ext (hsep v h hv))

@[simp] theorem amalgEquiv_inl {hcov hsep hgS hgT} {v : F.V} (hv : IncS S v) :
    amalgEquiv S g hcov hsep hgS hgT v = Sum.inl ⟨v, hv⟩ := by
  simp only [amalgEquiv, Equiv.coe_fn_mk]; rw [dif_pos hv]

theorem amalgEquiv_inr {hcov hsep hgS hgT} {v : F.V} (hv : ¬ IncS S v)
    (hv' : ∃ e ∈ Sᶜ, v ∈ e.1) (hne : v ≠ g) :
    amalgEquiv S g hcov hsep hgS hgT v = Sum.inr ⟨⟨v, hv'⟩, by
      intro heq; exact hne (congrArg Subtype.val heq)⟩ := by
  simp only [amalgEquiv, Equiv.coe_fn_mk]; rw [dif_neg hv]

/-- Mapping a finite edge through a subtype only requires agreement on that edge. -/
theorem map_via_subtype {A B : Type*} {P : A → Prop} [DecidablePred P]
    (e : Finset A) (f : A ↪ B) (g : {a // P a} ↪ B)
    (he : ∀ a ∈ e, P a) (hag : ∀ a (ha : P a), f a = g ⟨a, ha⟩) :
    e.map f = (e.subtype P).map g := by
  apply Finset.ext
  intro b
  constructor
  · intro hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hb
    exact Finset.mem_map.mpr ⟨⟨a, he a ha⟩, Finset.mem_subtype.mpr ha, (hag _ _).symm⟩
  · intro hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hb
    exact Finset.mem_map.mpr ⟨a.1, Finset.mem_subtype.mp ha, hag _ _⟩

/-
An `S`-edge maps to a left restricted edge under `amalgEquiv`.
-/
theorem amalgEquiv_map_left {hcov hsep hgS hgT} {e : Finset F.V} (he : ∀ v ∈ e, IncS S v) :
    e.map (amalgEquiv S g hcov hsep hgS hgT).toEmbedding =
      (Finset.subtype (fun v => IncS S v) e).map Function.Embedding.inl := by
  apply map_via_subtype _ _ _ he
  exact fun _ hv => amalgEquiv_inl S g hv

/-
A `Sᶜ`-edge maps to a right restricted edge under `amalgEquiv`, via the
amalgamation embedding `amalgEmbG`.
-/
set_option maxHeartbeats 1000000 in
theorem amalgEquiv_map_amalg {hcov hsep hgS hgT} {e : Finset F.V}
    (he' : ∀ v ∈ e, ∃ e' ∈ Sᶜ, v ∈ e'.1) :
    e.map (amalgEquiv S g hcov hsep hgS hgT).toEmbedding =
      (Finset.subtype (fun v => ∃ e' ∈ Sᶜ, v ∈ e'.1) e).map
        (amalgEmbG (F.restrict S) (F.restrict Sᶜ) ⟨g, hgS⟩ ⟨g, hgT⟩) := by
  apply map_via_subtype _ _ _ he'
  intro v hv
  by_cases h : v = g
  · subst v
    rw [Equiv.coe_toEmbedding, amalgEquiv_inl S g hgS]
    simp [amalgEmbG]
  · have hS : ¬IncS S v := fun hS => h (hsep v hS hv)
    rw [Equiv.coe_toEmbedding, amalgEquiv_inr S g hS hv h]
    simp [amalgEmbG, Subtype.ext_iff, h]

/-
**Amalgamation reconstruction.**  If the edges split into two parts `S` and
`Sᶜ` whose only shared vertex is the glue vertex `g` (and covering all vertices),
then `F` is the one-point amalgamation of the two restrictions at `g`.
-/
theorem recon_amalg
    (hcov : ∀ v : F.V, IncS S v ∨ (∃ e ∈ Sᶜ, v ∈ e.1))
    (hsep : ∀ v : F.V, IncS S v → (∃ e ∈ Sᶜ, v ∈ e.1) → v = g)
    (hgS : IncS S g) (hgT : ∃ e ∈ Sᶜ, g ∈ e.1) :
    FTS.Iso F (FTS.amalgamate (F.restrict S) (F.restrict Sᶜ) ⟨g, hgS⟩ ⟨g, hgT⟩) := by
  refine' ⟨ _, _ ⟩;
  exact ( amalgEquiv S g hcov hsep hgS hgT );
  intro e;
  constructor;
  · intro he
    by_cases h : ⟨ e, he ⟩ ∈ S;
    · refine' Finset.mem_union_left _ ( Finset.mem_image.mpr ⟨ _, _, _ ⟩ );
      exact Finset.subtype ( fun v => IncS S v ) e;
      · exact FTS.mem_restrict_edges.mpr ⟨ ⟨ e, he ⟩, h, rfl ⟩;
      · convert! amalgEquiv_map_left S g ( fun v hv => ⟨ _, h, hv ⟩ ) |> Eq.symm using 1;
    · refine' Finset.mem_union_right _ ( Finset.mem_image.mpr ⟨ Finset.subtype ( fun v => ∃ e' ∈ Sᶜ, v ∈ e'.1 ) e, _, _ ⟩ );
      · exact FTS.mem_restrict_edges.mpr ⟨ ⟨ e, he ⟩, Finset.mem_compl.mpr h, rfl ⟩;
      · convert! amalgEquiv_map_amalg S g ( fun v hv => ⟨ ⟨ e, he ⟩, Finset.mem_compl.mpr h, hv ⟩ ) |> Eq.symm using 1;
  · intro he
    let φ := amalgEquiv S g hcov hsep hgS hgT
    rcases Finset.mem_union.mp he with h | h
    · obtain ⟨a, ha, hmap⟩ := Finset.mem_image.mp h
      obtain ⟨d, hd, rfl⟩ := FTS.mem_restrict_edges.mp ha
      have hh := amalgEquiv_map_left S g (hcov := hcov) (hsep := hsep)
        (hgS := hgS) (hgT := hgT) (e := d.val) (fun v hv => ⟨d, hd, hv⟩)
      exact Finset.map_injective φ.toEmbedding (hh.trans hmap) ▸ d.property
    · obtain ⟨a, ha, hmap⟩ := Finset.mem_image.mp h
      obtain ⟨d, hd, rfl⟩ := FTS.mem_restrict_edges.mp ha
      have hh := amalgEquiv_map_amalg S g (hcov := hcov) (hsep := hsep)
        (hgS := hgS) (hgT := hgT) (e := d.val) (fun v hv => ⟨d, hd, hv⟩)
      exact Finset.map_injective φ.toEmbedding (hh.trans hmap) ▸ d.property

end TripleSystem593

end

section

/-!
# The separation dichotomy

For the reconstruction step we must, given a `ReconOK` finite triple system with
at least one edge, either exhibit a separation (a partition of the edges sharing
at most one vertex) or recognise the system as a bipartite expansion.

The key geometric input is that a bridge incidence blocks edge-connectivity: if
`(w, e₀)` lies on no Berge cycle, then no edge containing `w` (other than `e₀`)
is reachable from `e₀` through vertices other than `w`.
-/

open Cardinal

namespace TripleSystem593

open Classical

universe u

variable {F : FTS}

/- Two edges share a vertex different from `w`. -/
set_option maxHeartbeats 2000000 in
def ShareOff (w : F.V) (a b : {e : Finset F.V // e ∈ F.edges}) : Prop :=
  ∃ v, v ≠ w ∧ v ∈ a.1 ∧ v ∈ b.1

/- Edge-reachability avoiding the vertex `w`. -/
set_option maxHeartbeats 2000000 in
def EReach (w : F.V) : {e : Finset F.V // e ∈ F.edges} → {e : Finset F.V // e ∈ F.edges} → Prop :=
  Relation.ReflTransGen (ShareOff w)

/-
**Generic chain shortcut.**  If two entries `L[i]`, `L[j]` (`i < j`) of an
`R`-chain are themselves `R`-related, then splicing the list at those positions
yields an `R`-chain with the same endpoints and length `i + 1 + (L.length - j)`.
-/
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

/-
A reachability witness as a chain-list of edges.
-/
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

/- **Assembling a Berge cycle from cyclic incidence data.**  Injective cyclic
sequences of vertices `v` and edges `g` (indexed by `ZMod m`, `m ≥ 2`) with the
two incidence conditions form a Berge cycle; if moreover `g 0 = e0` and `v 0 = w`
then `(w, e0)` lies on a Berge cycle. -/
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

/-
**A minimal reachability walk.**  A shortest chain-list from `e0` to `f`
(avoiding `w`) has length `≥ 2`, is nodup, and has no "chord": two entries at
list-distance `≥ 2` never share a vertex `≠ w`.
-/
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
  -- Let's choose the shortest such chain `L`.
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
      grind;
  · intro i j hi hj hij hR
    obtain ⟨L', hh, ht, hc, hlen⟩ := chain_shortcut L hL.2.2.1 i j hi hj (by omega) hR
    have hmin := hL.2.2.2 L' ⟨hh.trans hL.1, ht.trans hL.2.1, hc⟩
    omega

/- Consecutive entries of an `IsChain (ShareOff w)` list share a vertex `≠ w`. -/
set_option maxHeartbeats 2000000 in
theorem chain_get_shareoff {w : F.V} {L : List {e : Finset F.V // e ∈ F.edges}}
    (hchain : List.IsChain (ShareOff w) L) {k : ℕ} (h : k + 1 < L.length) :
    ShareOff w (L.get ⟨k, by omega⟩) (L.get ⟨k + 1, h⟩) :=
  List.isChain_iff_getElem.mp hchain k h

/-
In `ZMod m` (`m ≠ 0`), the `val` of `i - 1` for `i ≠ 0` is `i.val - 1`.
-/
set_option maxHeartbeats 2000000 in
theorem zmod_val_sub_one {m : ℕ} [NeZero m] (i : ZMod m) (h : i ≠ 0) :
    (i - 1).val = i.val - 1 := by
  by_cases hi : i.val = 0;
  · exact False.elim <| h <| by rw [ ← ZMod.natCast_zmod_val i, hi ] ; norm_num;
  · have h_val : (i - 1 : ZMod m) = (i.val - 1 : ℕ) := by
      simp +decide [ Nat.cast_sub ( Nat.one_le_iff_ne_zero.mpr hi ) ];
    rw [ h_val, ZMod.val_cast_of_lt ];
    exact lt_of_le_of_lt ( Nat.pred_le _ ) ( ZMod.val_lt i )

/-
**Extraction of cyclic incidence data.**  If `w ∈ e0`, `w ∈ f`, `e0 ≠ f`,
and `f` is reachable from `e0` avoiding `w`, then there is injective cyclic
incidence data (`m ≥ 2`) closing up the reachability walk through `w`, with the
`0`-th edge equal to `e0` and the `0`-th vertex equal to `w`.
-/
set_option maxHeartbeats 2000000 in
theorem cycle_data_of_ereach (hlin : F.Linear) (w : F.V)
    (e0 f : {e : Finset F.V // e ∈ F.edges}) (hwe0 : w ∈ e0.1) (hwf : w ∈ f.1)
    (hne : e0 ≠ f) (hreach : EReach w e0 f) :
    ∃ (m : ℕ) (_ : 2 ≤ m)
      (g : ZMod m → {e : Finset F.V // e ∈ F.edges}) (v : ZMod m → F.V),
      Function.Injective g ∧ Function.Injective v ∧
      (∀ i, v i ∈ (g i).1) ∧ (∀ i, v (i + 1) ∈ (g i).1) ∧
      g 0 = e0 ∧ v 0 = w := by
  -- Set `m := L.length`, `haveI : NeZero m := ⟨by omega⟩`.
  obtain ⟨L, hhead, hlast, hchain, h2, hnodup, hnochord⟩ := exists_minimal_chain w e0 f hne hreach
  set m := L.length
  haveI : NeZero m := ⟨by omega⟩;
  -- Define `g : ZMod m → _ := fun i => L.get ⟨i.val, ZMod.val_lt i⟩`.
  set g : ZMod m → {e : Finset F.V // e ∈ F.edges} := fun i => L.get ⟨i.val, ZMod.val_lt i⟩
  have hg0 : g 0 = e0 := by
    cases L <;> aesop
  have g_last : g (0 - 1) = f := by
    convert! hlast using 1;
    rw [ List.getLast?_eq_getElem? ];
    simp +zetaDelta at *;
    rcases L with ( _ | ⟨ _, _ | L ⟩ ) <;> norm_num at *
  have hg_inj : Function.Injective g := by
    intro i j hij; have := List.nodup_iff_injective_get.mp hnodup; simp_all +decide ;
    exact ZMod.val_injective m <| by have := List.nodup_iff_injective_get.mp hnodup; have := @this ⟨ i.val, ZMod.val_lt i ⟩ ⟨ j.val, ZMod.val_lt j ⟩ ; aesop;
  -- Shared-vertex existence `hshare : ∀ i, ∃ x, x ∈ (g (i-1)).1 ∧ x ∈ (g i).1`.
  have hshare : ∀ i : ZMod m, ∃ x : F.V, x ∈ (g (i - 1)).1 ∧ x ∈ (g i).1 := by
    intro i
    by_cases hi : i = 0;
    · grind;
    · have hcons : ShareOff w (g (i - 1)) (g i) := by
        convert! chain_get_shareoff hchain _;
        · rw [ zmod_val_sub_one ];
          · rw [ Nat.sub_add_cancel ( Nat.pos_of_ne_zero ( by simpa [ ZMod.val_eq_zero ] using hi ) ) ];
          · exact hi;
        · rw [ zmod_val_sub_one ];
          · rw [ Nat.sub_add_cancel ( Nat.pos_of_ne_zero ( by simpa [ ZMod.val_eq_zero ] using hi ) ) ] ; exact ZMod.val_lt i;
          · exact hi;
      exact ⟨ hcons.choose, hcons.choose_spec.2.1, hcons.choose_spec.2.2 ⟩;
  choose v hv_prev hv_cur using hshare;
  -- Uniqueness `huniq i y : y ∈ (g (i-1)).1 → y ∈ (g i).1 → y = v i`.
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
  · -- Let `p := v i`.
    intro i j hij
    by_cases hp : v i = w;
    · -- If `v k = w`, then `k = 0` (as `v · = w` only at `0`, shown above).
      have hk_zero : ∀ k : ZMod m, v k = w → k = 0 := by
        intro k hk
        by_contra hk_ne_zero;
        obtain ⟨ x, hx ⟩ := chain_get_shareoff hchain ( show k.val - 1 + 1 < L.length from by
                                                          rw [ Nat.sub_add_cancel ];
                                                          · exact ZMod.val_lt k;
                                                          · exact Nat.pos_of_ne_zero ( by simpa [ ZMod.val_eq_zero ] using hk_ne_zero ) );
        specialize huniq k x ; simp_all +decide [ Nat.sub_add_cancel ( show 1 ≤ k.val from Nat.pos_of_ne_zero ( by simpa [ ZMod.val_eq_zero ] using hk_ne_zero ) ) ];
        grind +suggestions;
      rw [ hk_zero i hp, hk_zero j ( hij ▸ hp ) ];
    · -- WLOG `i.val < j.val` (else symmetric; `i.val = j.val → i = j` by `ZMod.val_injective`).
      wlog hij' : i.val < j.val generalizing i j;
      · by_cases hij'' : j.val < i.val;
        · exact Eq.symm ( this ( hij.symm ) ( by simpa [ hij ] using hp ) hij'' );
        · exact ZMod.val_injective m ( le_antisymm ( le_of_not_gt hij'' ) ( le_of_not_gt hij' ) );
      · -- Set `a := i.val - 1`, `b := j.val`; `a + 2 ≤ b` (from `i.val < j.val`, `i.val ≥ 1`).
        set a := i.val - 1
        set b := j.val
        have hab : a + 2 ≤ b := by
          by_cases hi : i = 0;
          · grind +revert;
          · linarith [ Nat.sub_add_cancel ( show 1 ≤ i.val from Nat.pos_of_ne_zero ( by simpa [ ZMod.val_eq_zero ] using hi ) ) ];
        -- `p ∈ g (i-1) = L.get ⟨a,_⟩` (`hv_prev i`, `zmod_val_sub_one`) and `p ∈ g j = L.get ⟨b,_⟩` (`hv_cur j`).
        have hp_a : v i ∈ (L.get ⟨a, by
          exact lt_of_le_of_lt ( Nat.sub_le _ _ ) ( ZMod.val_lt i )⟩).1 := by
          convert! hv_prev i using 1;
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
  · grind +suggestions

/- **Bridge blocks reachability.**  If the incidence `(w, e₀)` lies on no Berge
cycle, then no other edge `f` containing `w` is reachable from `e₀` avoiding `w`. -/
set_option maxHeartbeats 2000000 in
theorem bridge_ereach_false (hlin : F.Linear) (w : F.V)
    (e0 f : {e : Finset F.V // e ∈ F.edges}) (hwe0 : w ∈ e0.1) (hwf : w ∈ f.1)
    (hne : e0 ≠ f) (hbr : ¬ OnBergeCycle F w e0) : ¬ EReach w e0 f := by
  intro hreach
  obtain ⟨m, hm, g, v, hg, hv, hmem1, hmem2, hg0, hv0⟩ :=
    cycle_data_of_ereach hlin w e0 f hwe0 hwf hne hreach
  exact hbr (onBergeCycle_of_cycle_data w hm g v hg hv hmem1 hmem2 e0 hg0 hv0)

end TripleSystem593

end

section

/-!
# The reconstruction step (§5): amalgamation and expansion cases

`decomp_step` (in `DecompReverse`) needs, for a `ReconOK` system with at least one
edge, to either split it at a one-point separation or recognise it as a bipartite
expansion.  This file provides the two geometric halves:

* `decomp_amalg` — if some edge has a bridge incidence at a vertex `w` that lies
  on another edge too, then cutting the edges into "reachable from `ed` avoiding
  `w`" and its complement is a one-point separation at `w`, exhibiting `F` as a
  one-point amalgamation of two strictly smaller `ReconOK` systems.  The
  separation property uses `bridge_ereach_false`.
* `exists_expansion_of_private` — if every edge has a private vertex, `F` is a
  bipartite expansion.
-/

open Cardinal

namespace TripleSystem593

open Classical

universe u

variable {F : FTS}

/-
Split a walk at index `k`: `w = (prefix of length k) ++ (rest)`.
-/
set_option maxHeartbeats 2000000 in
theorem walk_split_at {V : Type*} {G : SimpleGraph V} {u v : V} (w : G.Walk u v)
    (k : ℕ) (hk : k ≤ w.length) :
    ∃ (w1 : G.Walk u (w.getVert k)) (w2 : G.Walk (w.getVert k) v),
      w = w1.append w2 ∧ w1.length = k := by
  exact ⟨w.take k, w.drop k, (w.append_take_drop_eq k).symm, by simp [hk]⟩

/-
A non-cycle closed walk of length `≥ 3` has a repeated vertex at two indices
`i < j < length`.
-/
set_option maxHeartbeats 2000000 in
theorem walk_vertex_repeat {V : Type*} {G : SimpleGraph V} {v : V} (w : G.Walk v v)
    (hcyc : ¬ w.IsCycle) (hlen : 3 ≤ w.length) :
    ∃ i j, i < j ∧ j < w.length ∧ w.getVert i = w.getVert j := by
  have h_not_path : ¬ w.tail.IsPath := by
    grind +suggestions;
  -- Since `w.tail` is not a path, there exist indices `a` and `b` such that `1 ≤ a < b ≤ w.length` and `w.getVert a = w.getVert b`.
  obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, 1 ≤ a ∧ a < b ∧ b ≤ w.length ∧ w.getVert a = w.getVert b := by
    contrapose! h_not_path;
    have h_tail_nodup : List.Nodup (List.tail (w.support)) := by
      rw [ List.nodup_iff_getElem?_ne_getElem? ];
      grind +suggestions;
    convert! h_tail_nodup using 1;
    simp +decide [ SimpleGraph.Walk.isPath_def ];
    cases w <;> simp +decide [ SimpleGraph.Walk.support ];
  by_cases hb : b = w.length;
  · aesop;
  · exact ⟨ a, b, hab.2.1, lt_of_le_of_ne hab.2.2.1 hb, hab.2.2.2 ⟩

/-
**Odd closed walks contain odd cycles.**  From a closed walk of odd length
one can extract a cycle of odd length.
-/
set_option maxHeartbeats 2000000 in
theorem exists_odd_cycle_aux {V : Type*} (G : SimpleGraph V) (n : ℕ) :
    ∀ (v : V) (w : G.Walk v v), w.length = n → Odd n →
      ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ Odd c.length := by
  intro v w hw hn_odd
  induction' n using Nat.strong_induction_on with n ih generalizing v w;
  by_cases hw_cycle : w.IsCycle;
  · exact ⟨ v, w, hw_cycle, hw ▸ hn_odd ⟩;
  · -- Apply `walk_vertex_repeat` to find indices `i` and `j` such that `i < j < n` and `w.getVert i = w.getVert j =: x`.
    obtain ⟨i, j, hij, hjn, hx⟩ : ∃ i j, i < j ∧ j < n ∧ w.getVert i = w.getVert j := by
      convert! walk_vertex_repeat w hw_cycle _;
      · exact hw.symm;
      · rcases w with ( _ | ⟨ _, _, w ⟩ ) <;> simp_all +decide;
        · grind +extAll;
        · exact absurd ‹G.Adj v v› ( by simp +decide );
        · rcases n with ( _ | _ | _ | n ) <;> simp_all +arith +decide;
    -- Split `w` into three parts: `w1`, `c₁`, and `w3`.
    obtain ⟨w1, w2, hw1, hw2⟩ : ∃ w1 : G.Walk v (w.getVert i), ∃ w2 : G.Walk (w.getVert i) v, w = w1.append w2 ∧ w1.length = i := by
      exact walk_split_at w i ( by linarith )
    obtain ⟨c₁, w3, hc₁, hw3⟩ : ∃ c₁ : G.Walk (w.getVert i) (w.getVert i), ∃ w3 : G.Walk (w.getVert i) v, w2 = c₁.append w3 ∧ c₁.length = j - i := by
      have := walk_split_at w2 ( j - i ) ( by
        have := congr_arg SimpleGraph.Walk.length hw1; norm_num at this; omega; );
      grind +suggestions;
    -- Consider the two closed walks `c₁` and `c₂ = w3.append w1`.
    set c₂ : G.Walk (w.getVert i) (w.getVert i) := w3.append w1
    have hc₂ : c₂.length = n - (j - i) := by
      simp +zetaDelta at *;
      simp_all +decide [ SimpleGraph.Walk.length_append ];
      omega
    have hc₁_odd : Odd c₁.length ∨ Odd c₂.length := by
      grind +qlia
    generalize_proofs at *;
    grind

/- **No odd cycle implies 2-colorable.**  A simple graph in which every cycle
has even length is 2-colorable. -/
set_option maxHeartbeats 2000000 in
theorem colorable_two_of_cycle_even {V : Type*} (G : SimpleGraph V)
    (h : ∀ (v : V) (c : G.Walk v v), c.IsCycle → Even c.length) : G.Colorable 2 := by
  rw [SimpleGraph.two_colorable_iff_forall_loop_even]
  intro u w
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  obtain ⟨x, c, hc, hcodd⟩ := exists_odd_cycle_aux G w.length u w rfl hodd
  exact (Nat.not_odd_iff_even.mpr (h x c hc)) hcodd

/-
**Amalgamation case of the reconstruction step.**  If `(w, ed)` is a bridge
incidence and `w` also lies on another edge `f`, then `F` is a one-point
amalgamation of two strictly smaller `ReconOK` systems.
-/
set_option maxHeartbeats 2000000 in
theorem decomp_amalg (h : ReconOK F)
    (ed : {e : Finset F.V // e ∈ F.edges}) (w : F.V) (hbrid : IsBridgeInc F w ed)
    (f : {e : Finset F.V // e ∈ F.edges}) (hfne : f ≠ ed) (hwf : w ∈ f.1) :
    ∃ (F₁ F₂ : FTS) (x : F₁.V) (y : F₂.V),
        F₁.edges.card < F.edges.card ∧ F₂.edges.card < F.edges.card ∧
        ReconOK F₁ ∧ ReconOK F₂ ∧ FTS.Iso F (F₁.amalgamate F₂ x y) := by
  obtain ⟨hlin, hno_iso, hbrEx, hev⟩ := h;
  -- Let `S := Finset.univ.filter (fun e' => EReach w ed e')`.
  set S : Finset {e : Finset F.V // e ∈ F.edges} := Finset.univ.filter (fun e' => EReach w ed e');
  -- We need to show that `S` satisfies the conditions for `recon_amalg`.
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

/-! ### The core graph of a private-vertex selection -/

/- Core vertices for a private-vertex selection `pr`: vertices that are not the
chosen private vertex of any edge. -/
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

/- The core graph: two core vertices are adjacent when they are distinct and both
lie on a common edge of `F`. -/
set_option maxHeartbeats 2000000 in
abbrev coreGraph (F : FTS) (pr : {e : Finset F.V // e ∈ F.edges} → F.V) :
    SimpleGraph (CoreV F pr) where
  Adj a b := (a : F.V) ≠ (b : F.V) ∧
    ∃ ed : {e : Finset F.V // e ∈ F.edges}, (a : F.V) ∈ ed.1 ∧ (b : F.V) ∈ ed.1
  symm := ⟨fun _ _ ⟨h1, ed, h2, h3⟩ => ⟨h1.symm, ed, h3, h2⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

set_option maxHeartbeats 2000000 in
noncomputable instance instDecRelCoreGraph (F : FTS)
    (pr : {e : Finset F.V // e ∈ F.edges} → F.V) :
    DecidableRel (coreGraph F pr).Adj :=
  fun _ _ => Classical.dec _

/-
In a cycle, `getVert` is injective on `[0, length)`.
-/
set_option maxHeartbeats 2000000 in
theorem cycle_getVert_inj {V : Type*} {G : SimpleGraph V} {x : V} {c : G.Walk x x}
    (hc : c.IsCycle) {i j : ℕ} (hi : i < c.length) (hj : j < c.length)
    (h : c.getVert i = c.getVert j) : i = j := by
  exact hc.getVert_injOn' (Nat.le_sub_one_of_lt hi) (Nat.le_sub_one_of_lt hj) h

/-
The core graph is 2-colorable, because a cycle of the core graph lifts to a
Berge cycle of `F` of the same length, which is even.
-/
set_option maxHeartbeats 2000000 in
theorem coreGraph_colorable (F : FTS) (pr : {e : Finset F.V // e ∈ F.edges} → F.V)
    (hpm : ∀ ed, pr ed ∈ ed.1)
    (hev : ∀ c : BergeCycle F, Even c.m) : (coreGraph F pr).Colorable 2 := by
  apply colorable_two_of_cycle_even;
  intro v c hc
  set m := c.length with hm
  have hm3 : 3 ≤ m := by
    exact hc.three_le_length
  haveI : NeZero m := ⟨by omega⟩
  generalize_proofs at *;
  -- Build a Berge cycle of length `m` in `F`.
  obtain ⟨v', e', hv', he'⟩ : ∃ (v' : ZMod m → F.V) (e' : ZMod m → {e : Finset F.V // e ∈ F.edges}),
    (∀ i, v' i = (c.getVert i.val : F.V)) ∧
    (∀ i, v' i ∈ (e' i).1 ∧ v' (i + 1) ∈ (e' i).1) := by
      have h_adj : ∀ i : ZMod m, (coreGraph F pr).Adj (c.getVert i.val) (c.getVert ((i.val + 1) % m)) := by
        intro i
        have h_adj : (coreGraph F pr).Adj (c.getVert i.val) (c.getVert (i.val + 1)) := by
          convert! c.adj_getVert_succ _ using 1
          generalize_proofs at *;
          exact i.val_lt
        generalize_proofs at *;
        cases eq_or_ne ( i.val + 1 ) m <;> simp_all +decide;
        rwa [ Nat.mod_eq_of_lt ( lt_of_le_of_ne ( Nat.succ_le_of_lt ( show i.val < c.length from i.val_lt ) ) ‹_› ) ];
      choose e' he' using fun i => h_adj i |>.2;
      refine ⟨fun i => (c.getVert i.val : F.V), e', fun _ => rfl, ?_⟩
      intro i
      haveI : Fact (1 < m) := ⟨by omega⟩
      simpa only [ZMod.val_add, ZMod.val_one] using he' i
  -- Show that `v'` and `e'` satisfy the conditions of a Berge cycle.
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
    · grind +suggestions;
    · grind;
    · have h_contra : (i + 1 + 1 : ZMod m) = i := by
        grind +suggestions;
      norm_num [ add_assoc ] at h_contra;
      erw [ ZMod.natCast_eq_zero_iff ] at h_contra ; have := Nat.le_of_dvd ( by linarith ) h_contra ; linarith;
    · grind +suggestions;
  exact hev ⟨ m, by linarith, v', e', hv'_inj, he'_inj, fun i => he' i |>.1, fun i => he' i |>.2 ⟩

/-
Structure of an edge: it consists of two distinct core vertices and its
private vertex.
-/
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

/-
The private-vertex map is injective.
-/
set_option maxHeartbeats 2000000 in
theorem pr_injective (F : FTS) (pr : {e : Finset F.V // e ∈ F.edges} → F.V)
    (hpm : ∀ ed, pr ed ∈ ed.1)
    (hpu : ∀ ed, ∀ g ∈ F.edges, pr ed ∈ g → g = ed.1) :
    Function.Injective pr := by
  intro ed1 ed2 h_eq;
  grind +suggestions

/-
Two distinct core vertices lying on a common edge are adjacent in the core
graph, so their `Sym2` is an edge of the core graph.
-/
set_option maxHeartbeats 2000000 in
theorem core_edge_mem (F : FTS) (pr : {e : Finset F.V // e ∈ F.edges} → F.V)
    (a b : CoreV F pr) (ed : {e : Finset F.V // e ∈ F.edges})
    (hab : a ≠ b) (hae : (a : F.V) ∈ ed.1) (hbe : (b : F.V) ∈ ed.1) :
    s(a, b) ∈ (coreGraph F pr).edgeFinset := by
  simp +decide [ SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, coreGraph ];
  exact ⟨ Subtype.coe_injective.ne hab, ed.1, hae, ed.2, hbe ⟩

/-
An edge is determined by any two of its distinct vertices (linearity).
-/
set_option maxHeartbeats 2000000 in
theorem edge_unique_of_two (F : FTS) (hlin : F.Linear)
    {ed ed' : {e : Finset F.V // e ∈ F.edges}} {a b : F.V} (hab : a ≠ b)
    (h1 : a ∈ ed.1) (h2 : b ∈ ed.1) (h3 : a ∈ ed'.1) (h4 : b ∈ ed'.1) : ed = ed' := by
  exact Subtype.ext <| Classical.not_not.1 fun h => absurd ( hlin _ ed.2 _ ed'.2 h ) ( by exact Nat.not_le_of_gt ( Finset.one_lt_card.2 ⟨ a, by aesop, b, by aesop ⟩ ) )

/-
From an edge of the core graph, recover an `F`-edge containing both endpoints.
-/
set_option maxHeartbeats 2000000 in
theorem jedge_exists_edge (F : FTS) (pr : {e : Finset F.V // e ∈ F.edges} → F.V)
    (a b : CoreV F pr) (hx : s(a, b) ∈ (coreGraph F pr).edgeFinset) :
    ∃ ed : {e : Finset F.V // e ∈ F.edges}, (a : F.V) ∈ ed.1 ∧ (b : F.V) ∈ ed.1 := by
  simp_all +decide [ coreGraph ]

/- The vertex bijection `F.V ≃ (graphExpansion (coreGraph F pr)).V` with its
computation rules: core vertices go to `Sum.inl`, and the private vertex of an
edge goes to `Sum.inr` of the core-pair edge. -/
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
  set f : F.V → (graphExpansion (coreGraph F pr)).V :=
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
  · intro v hv; rw [Equiv.ofBijective_apply]; exact hf_core v hv
  · intro ed; refine ⟨jE ed, ?_, hjE ed⟩; rw [Equiv.ofBijective_apply]; exact hf_priv ed
  · intro x; obtain ⟨ed, hed⟩ := hjE_surj x
    exact ⟨ed, by rw [Equiv.ofBijective_apply, hf_priv ed, hed]⟩

/- `F` is isomorphic to the private-vertex expansion of its core graph. -/
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
    · rw [h1, h2]
    · rw [h1, h2, Finset.insert_comm]
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

/- **Expansion recognition.**  A linear finite triple system with no isolated
vertices, only even Berge cycles, and a private vertex on every edge, is
isomorphic to the private-vertex expansion of a finite bipartite graph. -/
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

end TripleSystem593

end

section

open Cardinal

namespace TripleSystem593

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
  · -- Amalgamation case.
    obtain ⟨ed, w, hbrid, f, hfne, hwf⟩ := hA
    exact Or.inr (Or.inr
      (decomp_amalg ⟨hlin, hno_iso, hbr, hev⟩ ed w hbrid f hfne hwf))
  · -- Expansion case: every edge has a private vertex.
    push Not at hA
    refine Or.inl (exists_expansion_of_private hlin ?_ hev)
    intro ed
    obtain ⟨w, hw_mem, hw_bridge⟩ := hbr ed
    refine ⟨w, hw_mem, ?_⟩
    intro g hg hwg
    by_contra hgne
    exact hA ed w hw_bridge ⟨g, hg⟩ (fun hcontra => hgne (congrArg Subtype.val hcontra)) hwg

theorem bclass_of_reconOK (F : FTS) (h : ReconOK F) : Bclass F := by
  -- strong induction on the number of edges
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

end TripleSystem593

end

section

open Cardinal Ordinal

namespace TripleSystem593
namespace ER60

universe u

abbrev Pt (κ : Cardinal.{u}) : Type u := κ.ord.ToType
variable {κ : Cardinal.{u}}
def Cofinal (S : Set (Pt κ)) : Prop := ∀ x : Pt κ, ∃ y ∈ S, x < y

theorem cofinal_univ (hκ : ℵ₀ ≤ κ) : Cofinal (Set.univ : Set (Pt κ)) := by
  intro x
  obtain ⟨y, hy⟩ : ∃ y : Pt κ, x < y := by
    convert! exists_gt x;
    have h_no_max : NoMaxOrder (κ.ord.ToType) := by
      have h_limit : Order.IsSuccLimit κ.ord := by
        apply_rules [ Cardinal.isSuccLimit_ord, hκ ]
      grind +suggestions;
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
        · convert! Ordinal.lsub_lt_ord_lift _ _;
          · simp +decide [ Cardinal.mk_out ];
            exact hθ.trans_le hreg.cof_eq.ge;
          · grind +suggestions;
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
                  convert! hx using 1;
                  convert! Ordinal.type_toType κ.ord using 1
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
end ER60
end TripleSystem593

end

section

open Cardinal Ordinal

namespace TripleSystem593
namespace EHG

open ER60 (Pt)

universe u

variable {κ : Cardinal.{u}} {k : ℕ}

abbrev Vtx (k : ℕ) (κ : Cardinal.{u}) : Type u := {t : Fin k → Pt κ // StrictMono t}
end EHG
end TripleSystem593

end

section

open Cardinal TripleSystem593.ER60

namespace TripleSystem593
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
end EHG
end TripleSystem593

end

section

/-!
# The genuine Erdős–Hajnal / generalized Specker high-odd-girth graph `GS_n(κ)`

This file develops the **correct** Erdős–Hajnal high-odd-girth construction, the
generalized Specker graph `GS_n(κ)` of Erdős–Galvin–Hajnal (Bolyai 10, 1975,
Definition 8.2), on top of the `n = 1` (triangle-free) base case
`RequestProject.ErdosHajnalGirth`.

**Construction (Def. 8.2).**  Fix `κ` and a parameter `n ≥ 1`.  Let
`Pt = κ.ord.ToType` (so `|Pt| = κ`).  Put `L = L n = n² + n + 1`.  The vertices
are the strictly increasing `L`-tuples `u = (u₀ < u₁ < ⋯ < u_{L-1})` of `Pt`.
Two tuples `u`, `v` are joined when the coordinates interleave as the chain
```
  u_n < v_0 < u_{n+1} < v_1 < u_{n+2} < v_2 < ⋯ < u_{n²+n} < v_{n²}
```
(or symmetrically with `u`, `v` swapped).  Concretely the oriented edge
`IsEdge u v` (with `u` "below") is
```
  (∀ t ≤ n²,   u_{n+t} < v_t)   ∧   (∀ t < n²,   v_t < u_{n+t+1}).
```

For `n = 1` (so `L = 3`) this is exactly the Erdős–Rado graph of
`ErdosHajnalGirth` (the chain `u₁ < v₀ < u₂ < v₁`, with `u₀ < u₁` and `v₁ < v₂`
supplied by monotonicity).

The key facts (Lemma 8.3) are:
* `card_le` — `|V| ≤ κ`;
* no odd cycle `C_{2i+1}` for `1 ≤ i ≤ n` (`NoShortOddCycle (graph n κ) n`);
* the chromatic lower bound `χ(GS_n(κ)) = κ`.

This file establishes the construction, the cardinality bound, and the two
"index comparison" workhorse lemmas `edge_lt_of_index_le` and
`edge_gt_of_index_ge` that drive the odd-girth argument.  The odd-girth theorem
itself is in `RequestProject.GSnOddGirth` and the chromatic bound in
`RequestProject.GSnChromatic`.
-/

open Cardinal Ordinal

namespace TripleSystem593
namespace GSn

open ER60 (Pt)

universe u

variable {κ : Cardinal.{u}} {n : ℕ}

/-- The tuple length `L n = n² + n + 1`. -/
abbrev L (n : ℕ) : ℕ := n * n + n + 1

theorem L_pos (n : ℕ) : 0 < L n := by positivity

/-- `n + t < L n` when `t ≤ n²`. -/
theorem nt_lt (n : ℕ) {t : ℕ} (h : t ≤ n * n) : n + t < L n := by
  simp only [L]; omega

/-- `t < L n` when `t ≤ n²`. -/
theorem t_lt (n : ℕ) {t : ℕ} (h : t ≤ n * n) : t < L n := by
  simp only [L]; omega

/-- Vertices: strictly increasing `L n`-tuples of `Pt κ`. -/
abbrev Vtx (n : ℕ) (κ : Cardinal.{u}) : Type u := {t : Fin (L n) → Pt κ // StrictMono t}

/-- The oriented interleaving edge relation `IsEdge u v` (`u` below):
`u_n < v_0 < u_{n+1} < v_1 < ⋯ < u_{n²+n} < v_{n²}`, expressed via the two
families of cross conditions. -/
def IsEdge (u v : Fin (L n) → Pt κ) : Prop :=
  (∀ t : ℕ, (h : t ≤ n * n) → u ⟨n + t, nt_lt n h⟩ < v ⟨t, t_lt n h⟩) ∧
  (∀ t : ℕ, (h : t < n * n) → v ⟨t, t_lt n (le_of_lt h)⟩ < u ⟨n + t + 1, by simp only [L]; omega⟩)

/-- Symmetric adjacency. -/
def Adjr (u v : Vtx n κ) : Prop := IsEdge u.1 v.1 ∨ IsEdge v.1 u.1

theorem isEdge_irrefl (a : Fin (L n) → Pt κ) (ha : StrictMono a) : ¬ IsEdge a a := by
  rintro ⟨h1, -⟩
  have h := h1 0 (Nat.zero_le _)
  simp only [Nat.add_zero] at h
  have hle : a ⟨0, t_lt n (Nat.zero_le _)⟩ ≤ a ⟨n, nt_lt n (Nat.zero_le _)⟩ :=
    ha.monotone (by simp only [Fin.le_def]; omega)
  exact absurd (lt_of_lt_of_le h hle) (lt_irrefl _)

/-- The generalized Specker / Erdős–Hajnal graph `GS_n(κ)` on increasing
`L n`-tuples. -/
def graph (n : ℕ) (κ : Cardinal.{u}) : SimpleGraph (Vtx n κ) where
  Adj u v := Adjr u v
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by rintro a (h | h) <;> exact isEdge_irrefl _ a.2 h⟩

/-! ### Cardinality -/

theorem card_le (hκ : ℵ₀ ≤ κ) : Cardinal.mk (Vtx n κ) ≤ κ := by
  have h_card : #(Fin (L n) → Pt κ) = κ ^ (L n : ℕ) := by
    simp +decide [Cardinal.mk_toType, Cardinal.card_ord]
    norm_cast
  refine le_trans (Cardinal.mk_subtype_le _) ?_
  rw [h_card, Cardinal.power_nat_eq]
  · exact hκ
  · exact L_pos n

/-! ### The index-comparison workhorse lemmas

In an oriented edge `IsEdge u v` (`u` below, both strictly increasing), the order
between a coordinate `u_a` and a coordinate `v_b` is decided entirely by comparing
the indices `a` and `b + n`:
* `u_a < v_b` whenever `a ≤ b + n`   (`edge_lt_of_index_le`);
* `v_b < u_a` whenever `a ≥ b + n + 1` (`edge_gt_of_index_ge`).
These two are complementary and capture every cross-relation of an edge. -/

/-
If `IsEdge u v` and `a ≤ b + n` (with `a, b` valid indices), then
`u_a < v_b`.  Proof: pick `t = a - n` (or `t = 0` if `a ≤ n`); then
`u_a ≤ u_{n+t} < v_t ≤ v_b`.
-/
theorem edge_lt_of_index_le {u v : Fin (L n) → Pt κ}
    (hu : StrictMono u) (hv : StrictMono v) (h : IsEdge u v)
    {a b : ℕ} (ha : a < L n) (hb : b < L n) (hab : a ≤ b + n) :
    u ⟨a, ha⟩ < v ⟨b, hb⟩ := by
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t ≤ n * n ∧ a ≤ n + t ∧ t ≤ b := by
    exact ⟨ Min.min ( a - n ) b, le_trans ( min_le_left _ _ ) ( Nat.sub_le_of_le_add <| by linarith [ show L n = n * n + n + 1 from rfl ] ), by omega, min_le_right _ _ ⟩;
  exact lt_of_le_of_lt ( hu.monotone ( by exact Nat.le_trans ( Nat.le_refl _ ) ht.2.1 ) ) ( lt_of_lt_of_le ( h.1 t ht.1 ) ( hv.monotone ( by exact Nat.le_trans ht.2.2 ( Nat.le_refl _ ) ) ) )

/-
If `IsEdge u v` and `a ≥ b + n + 1` (with `a, b` valid indices), then
`v_b < u_a`.  Proof: pick `t = b`; then `v_b < u_{n+b+1} ≤ u_a` (the hypothesis
`a ≥ b + n + 1` together with `a < L n` forces `b < n²`, so `v_b < u_{n+b+1}`
is a valid edge inequality).
-/
theorem edge_gt_of_index_ge {u v : Fin (L n) → Pt κ}
    (hu : StrictMono u) (h : IsEdge u v)
    {a b : ℕ} (ha : a < L n) (hb : b < L n) (hab : b + n + 1 ≤ a) :
    v ⟨b, hb⟩ < u ⟨a, ha⟩ := by
  exact lt_of_lt_of_le ( h.2 b ( by unfold L at *; omega ) ) ( hu.monotone ( by exact Nat.le_trans ( by simp +arith +decide ) hab ) )

/-- An oriented edge dominates in the `0`-coordinate: `IsEdge u v ⟹ u₀ < v₀`. -/
theorem isEdge_fst_lt {u v : Fin (L n) → Pt κ}
    (hu : StrictMono u) (hv : StrictMono v) (h : IsEdge u v) :
    u ⟨0, L_pos n⟩ < v ⟨0, L_pos n⟩ :=
  edge_lt_of_index_le hu hv h (L_pos n) (L_pos n) (by omega)

/-- The two orientations of an edge are mutually exclusive. -/
theorem not_isEdge_both {u v : Fin (L n) → Pt κ}
    (hu : StrictMono u) (hv : StrictMono v) (h : IsEdge u v) : ¬ IsEdge v u := by
  intro h'
  have h1 := isEdge_fst_lt hu hv h
  have h2 := isEdge_fst_lt hv hu h'
  exact absurd (lt_trans h1 h2) (lt_irrefl _)

end GSn
end TripleSystem593

end

section

/-!
# The cyclic difference-constraint potential (delta lemma core)

This file is the pure combinatorial engine behind the odd-girth argument for the
generalized Specker graph `GS_n(κ)` (Erdős–Galvin–Hajnal, Lemma 8.3(A)).  It is
entirely graph-independent.

Given a cycle `ℤ/m` with an integer "increment" `c j` on each edge `j → j+1`,
we build the **max-window potential**
```
  pot j = max_{0 ≤ r < m} backSum j r,   backSum j r = ∑_{t<r} c (j-1-t),
```
and prove its two decisive properties:
* `pot_step` — if the total increment `∑_e c e ≤ 0`, then `pot (j+1) ≥ pot j + c j`
  (so the potential "absorbs" every edge constraint);
* `pot_le_posSum` — `pot j ≤ ∑_e (c e)⁺` (the potential never exceeds the total of
  the positive increments), together with `pot_nonneg` (`0 ≤ pot j`).

Applied with `c j = -n` on "ascent" edges and `c j = n+1` on "descent" edges of a
would-be short odd cycle in `GS_n(κ)`, these give an index assignment
`k j = pot j ∈ [0, n²+n]` for which the corresponding coordinates strictly
increase around the cycle — an impossibility (`GSnOddGirth`).
-/

open Finset

namespace TripleSystem593
namespace GSn

/-- Reindexing a sum over `range m` (via `ℕ`-cast) as a sum over `ZMod m`. -/
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

/-- Backward window sum: the sum of the `r` increments on the edges ending at
node `j` (i.e. edges `j-1, j-2, …, j-r`). -/
def backSum (m : ℕ) (c : ZMod m → ℤ) (j : ZMod m) (r : ℕ) : ℤ :=
  ∑ t ∈ Finset.range r, c (j - 1 - t)

@[simp] theorem backSum_zero (m : ℕ) (c : ZMod m → ℤ) (j : ZMod m) :
    backSum m c j 0 = 0 := by simp [backSum]

/-- Shift identity: prepending edge `j` to a window ending at `j`. -/
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

/-- A full-length window sums all increments once. -/
theorem backSum_full (m : ℕ) [NeZero m] (c : ZMod m → ℤ) (j : ZMod m) :
    backSum m c (j + 1) m = ∑ e : ZMod m, c e := by
  unfold backSum
  have := sum_range_zmod m (fun e => c (j + 1 - 1 - e))
  rw [this]
  exact Fintype.sum_equiv (Equiv.subLeft (j + 1 - 1)) _ _ (fun e => rfl)

/-- The max-window potential. -/
noncomputable def pot (m : ℕ) (hm : 0 < m) (c : ZMod m → ℤ) (j : ZMod m) : ℤ :=
  (Finset.range m).sup' (Finset.nonempty_range_iff.mpr hm.ne') (fun r => backSum m c j r)

theorem pot_nonneg (m : ℕ) (hm : 0 < m) (c : ZMod m → ℤ) (j : ZMod m) :
    0 ≤ pot m hm c j := by
  have : backSum m c j 0 ≤ pot m hm c j := Finset.le_sup' _ (Finset.mem_range.mpr hm)
  simpa using this

/-
A window sum is at most the total of the positive increments.
-/
theorem backSum_le_posSum (m : ℕ) [NeZero m] (c : ZMod m → ℤ) (j : ZMod m)
    {r : ℕ} (hr : r ≤ m) :
    backSum m c j r ≤ ∑ e : ZMod m, max (c e) 0 := by
  refine' le_trans ( Finset.sum_le_sum fun x hx => show c ( j - 1 - x ) ≤ max ( c ( j - 1 - x ) ) 0 from le_max_left _ _ ) _;
  -- By definition of summation, we can rewrite the right-hand side as a sum over all elements in the range.
  have h_sum_range : ∑ x ∈ Finset.range m, max (c (j - 1 - x)) 0 = ∑ e : ZMod m, max (c e) 0 := by
    convert! sum_range_zmod m ( fun e => max ( c ( j - 1 - e ) ) 0 ) using 1;
    rw [ ← Equiv.sum_comp ( Equiv.subLeft ( j - 1 ) ) ] ; aesop;
  exact h_sum_range ▸ Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono hr ) fun _ _ _ => le_max_right _ _

/-- **The potential never exceeds the total of the positive increments.** -/
theorem pot_le_posSum (m : ℕ) (hm : 0 < m) [NeZero m] (c : ZMod m → ℤ) (j : ZMod m) :
    pot m hm c j ≤ ∑ e : ZMod m, max (c e) 0 := by
  apply Finset.sup'_le
  intro r hr
  exact backSum_le_posSum m c j (le_of_lt (Finset.mem_range.mp hr))

/-
**The potential absorbs every edge constraint** when the total increment is
nonpositive: `pot (j+1) ≥ pot j + c j`.
-/
theorem pot_step (m : ℕ) (hm : 0 < m) [NeZero m] (c : ZMod m → ℤ)
    (hsum : ∑ e : ZMod m, c e ≤ 0) (j : ZMod m) :
    pot m hm c j + c j ≤ pot m hm c (j + 1) := by
  have h_sup_le : ∀ r ∈ Finset.range m, backSum m c j r + c j ≤ pot m hm c (j + 1) := by
    intros r hr
    by_cases hr_lt : r + 1 < m;
    · convert! Finset.le_sup' ( fun r => backSum m c ( j + 1 ) r ) ( Finset.mem_range.mpr hr_lt ) using 1 ; rw [ backSum_shift ] ; ring;
    · have h_eq : backSum m c (j + 1) (r + 1) = ∑ e : ZMod m, c e := by
        rw [ show r + 1 = m by linarith [ Finset.mem_range.mp hr ] ] ; exact backSum_full m c j;
      linarith [ backSum_shift m c j r, pot_nonneg m hm c ( j + 1 ) ];
  obtain ⟨ r, hr ⟩ := Finset.exists_max_image ( Finset.range m ) ( fun r => backSum m c j r ) ⟨ _, Finset.mem_range.mpr hm ⟩;
  linarith [ hr.2 r hr.1, h_sup_le r hr.1, show pot m hm c j = backSum m c j r from le_antisymm ( Finset.sup'_le _ _ fun x hx => hr.2 x hx ) ( Finset.le_sup' ( fun r => backSum m c j r ) hr.1 ) ]

end GSn
end TripleSystem593

end

section

/-!
# No short odd cycles in `GS_n(κ)` (Erdős–Galvin–Hajnal, Lemma 8.3(A))

This file proves that the generalized Specker graph `GS_n(κ)` of
`RequestProject.GSn` contains **no odd cycle of length `≤ 2n+1`**
(`noShortOddCycle_n : NoShortOddCycle (graph n κ) n`).

The proof is the delta-lemma argument.  Suppose `C_m` (`m = 2i+1`, `3 ≤ m ≤ 2n+1`)
sits in `GS_n(κ)` as an injective cyclic sequence `A : ℤ/m → Vtx`.  Orient each
edge `A j — A(j+1)`: it is an *ascent* if `IsEdge (A j) (A(j+1))` (the "below"
vertex is `A j`) and a *descent* otherwise.  Assign increments `incr j = -n`
(ascent) / `n+1` (descent).  When the descents are the minority
(`(2n+1)·#descents ≤ n·m`, achievable up to reversing the cycle since `m` is odd
and `m ≤ 2n+1`), the total increment is `≤ 0` and the positive increments total
`≤ n²+n`.  The max-window potential `pot` of `RequestProject.GSnPotential` then
produces an index assignment `k j ∈ [0, n²+n]` with
`(A j)_{k_j} < (A(j+1))_{k_{j+1}}` around the whole cycle — a strictly increasing
function on the cyclic group `ℤ/m`, which is impossible.
-/

open Cardinal Finset

namespace TripleSystem593
namespace GSn

open ER60 (Pt)

universe u

variable {κ : Cardinal.{u}} {n : ℕ}

/-- A strictly increasing function around a finite cycle `ℤ/m` cannot exist. -/
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
/-- The edge increment: `-n` on ascents (`IsEdge (A j) (A(j+1))`), `n+1` on
descents. -/
noncomputable def incr (j : ZMod m) : ℤ :=
  if IsEdge (A j).1 (A (j + 1)).1 then -(n : ℤ) else (n + 1)

open Classical in
/-- The number of descent edges. -/
noncomputable def descCount [NeZero m] : ℕ :=
  (Finset.univ.filter (fun j : ZMod m => ¬ IsEdge (A j).1 (A (j + 1)).1)).card

/-- **Core delta-lemma contradiction.**  Under the two sum bounds (total increment
`≤ 0`, positive increments `≤ n²+n`), a cyclic sequence of adjacent vertices is
impossible. -/
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

/-
Total increment in terms of the descent count: `∑ incr = -n·m + (2n+1)·D`.
-/
theorem sum_incr_eq [NeZero m] :
    ∑ e : ZMod m, incr A e = -(n : ℤ) * m + (2 * n + 1) * descCount A := by
  unfold incr;
  simp +decide [ Finset.sum_ite, Finset.filter_not, Finset.card_sdiff, Finset.card_univ, ZMod.card, descCount ];
  rw [ Nat.cast_sub ( show _ ≤ _ from le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ) ] ; ring

/-
Total of positive increments: `∑ max(incr,0) = (n+1)·D`.
-/
theorem sum_max_incr_eq [NeZero m] :
    ∑ e : ZMod m, max (incr A e) 0 = (n + 1 : ℤ) * descCount A := by
  convert! Finset.sum_congr rfl fun x hx => show max ( if IsEdge ( A x ).1 ( A ( x + 1 ) ).1 then - ( n : ℤ ) else ( n + 1 : ℤ ) ) 0 = if IsEdge ( A x ).1 ( A ( x + 1 ) ).1 then 0 else ( n + 1 : ℤ ) from ?_ using 1;
  all_goals norm_num [ Finset.sum_ite ];
  convert! mul_comm _ _ using 2;
  split_ifs <;> norm_num ; linarith

/-- **Core contradiction, in terms of the descent count.**  If the descents are a
"minority" in the sense `(2n+1)·D ≤ n·m`, and `m ≤ 2n+1`, a cycle is impossible. -/
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

/-- The reversed cycle `A ∘ neg`. -/
def reverseCycle : ZMod m → Vtx n κ := fun j => A (-j)

theorem reverseCycle_adj [NeZero m]
    (hAadj : ∀ j : ZMod m, (graph n κ).Adj (A j) (A (j + 1))) :
    ∀ j : ZMod m, (graph n κ).Adj (reverseCycle A j) (reverseCycle A (j + 1)) := by
  intro j
  have := hAadj (-j - 1)
  simp [reverseCycle] at this ⊢
  ring_nf at this ⊢
  exact this.symm

/-
The descent count of the reversed cycle is `m - D` (the ascent count of `A`).
-/
theorem descCount_reverse [NeZero m]
    (hAadj : ∀ j : ZMod m, (graph n κ).Adj (A j) (A (j + 1))) :
    descCount (reverseCycle A) = m - descCount A := by
  refine' eq_tsub_of_add_eq _;
  convert! Finset.card_add_card_compl ( Finset.filter ( fun j => ¬ IsEdge ( A ( -j ) ).1 ( A ( -j - 1 ) ).1 ) Finset.univ ) using 1;
  congr! 1;
  all_goals try exact Classical.decPred _;
  · unfold descCount reverseCycle;
    grind +suggestions;
  · refine' Finset.card_bij ( fun j _ => -j - 1 ) _ _ _ <;> simp +decide [ Finset.mem_filter, Finset.mem_univ ];
    · intro a ha; specialize hAadj a; simp_all +decide [ add_comm, graph ] ;
      exact hAadj.resolve_left ha;
    · intro b hb;
      use -b - 1;
      have := not_isEdge_both ( A ( -b - 1 ) |>.2 ) ( A ( -b ) |>.2 ) ; simp_all +decide [ sub_eq_add_neg, add_assoc ];
  · cases m <;> aesop

end Cycle

/-- Arithmetic core of the minority condition. -/
theorem arith_minority (n D m : ℕ) (h1 : 2 * D + 1 ≤ m) (h2 : m ≤ 2 * n + 1) :
    (2 * n + 1) * D ≤ n * m := by
  have hDn : D ≤ n := by omega
  nlinarith [h1, h2, hDn, Nat.mul_le_mul_left n h1]

/-- **Lemma 8.3(A): `GS_n(κ)` has no odd cycle of length `≤ 2n+1`.** -/
theorem noShortOddCycle_n : NoShortOddCycle (graph n κ) n := by
  intro m hodd hm3 hmle ⟨A, hAinj, hAadj⟩
  classical
  haveI : NeZero m := ⟨by omega⟩
  have hm0 : 0 < m := by omega
  -- descent count D of A; either A or its reversal has the minority condition
  set D := descCount A with hD_def
  have hDle : D ≤ m := by
    rw [hD_def, descCount]
    exact le_trans (Finset.card_filter_le _ _) (by rw [Finset.card_univ, ZMod.card])
  -- m is odd, so 2*D ≠ m
  have hodd2 : 2 * D ≠ m := by
    rintro he
    have hme : ¬ Even m := Nat.not_even_iff_odd.mpr hodd
    exact hme ⟨D, by omega⟩
  rcases Nat.lt_or_ge (2 * D) m with hcase | hcase
  · -- descents minority for A
    have h2D : 2 * D + 1 ≤ m := by omega
    exact cycle_false' A hm0 hAadj hmle (arith_minority n D m h2D hmle)
  · -- descents majority: reverse
    have h2Dgt : m < 2 * D := by omega
    have hA'adj := reverseCycle_adj A hAadj
    have hD' : descCount (reverseCycle A) = m - D := descCount_reverse A hAadj
    have hRlt : 2 * descCount (reverseCycle A) + 1 ≤ m := by rw [hD']; omega
    exact cycle_false' (reverseCycle A) hm0 hA'adj hmle
      (arith_minority n (descCount (reverseCycle A)) m hRlt hmle)

end GSn
end TripleSystem593

end

section

open Cardinal

namespace TripleSystem593
namespace GSn

open ER60 (Pt Cofinal cofinal_fiber cofinal_Ioi cofinal_univ)

universe u

variable {κ : Cardinal.{u}} {n : ℕ} {θ : Cardinal.{u}}

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
  -- Phase 1: place wu₀ … wu_{n-1}.
  obtain ⟨wu1, B1, -, -, hwu1le, -, hwu1mono, hwu1stab⟩ :=
    grow (n := n) hreg hθ c star (fun _ => p0) 0 n p0
      (by simp only [L]; omega) (by simpa using hstar (fun _ => p0))
      (by intro i hi; omega) (by intro a ha b hb hab; simp only [Set.mem_Iio] at ha; omega)
  simp only [Nat.zero_add] at hwu1le hwu1mono hwu1stab
  -- Phase 2: alternately place wu_{n+t}, wv_t for t = 0 … n².
  obtain ⟨wu2, wv2, B2, -, -, -, hwu2le, hwv2le, hwu2mono, hwv2mono,
      hwu2stab, hwv2stab, hlow, hhigh⟩ :=
    mid (n := n) hreg hθ c star wu1 (fun _ => p0) 0 (n * n + 1) B1
      (by simp only [L]; omega) (by simpa using hwu1stab)
      (by simpa using hstar (fun _ => p0)) (by simpa using hwu1le)
      (by intro i hi; omega) (by simpa using hwu1mono)
      (by intro a ha b hb hab; simp only [Set.mem_Iio] at ha; omega)
  -- Phase 3: place wv_{n²+1} … wv_{n²+n}.
  obtain ⟨wv3, B3, -, hwv3agree, -, -, hwv3mono, hwv3stab⟩ :=
    grow (n := n) hreg hθ c star wv2 (n * n + 1) n B2
      (by simp only [L]; omega) (by simpa using hwv2stab)
      (by simpa using hwv2le) (by simpa using hwv2mono)
  -- index normalizations
  have hidxu : n + 0 + (n * n + 1) = L n := by simp only [L]; ring
  have hidxv : n * n + 1 + n = L n := by simp only [L]; ring
  refine ⟨wu2, wv3, ?_, ?_, ?_, ?_, ?_⟩
  · -- StrictMono wu2
    have hm := hwu2mono; rw [hidxu] at hm
    intro a b hab
    exact hm (Set.mem_Iio.mpr a.2) (Set.mem_Iio.mpr b.2) hab
  · -- StrictMono wv3
    have hm := hwv3mono; rw [hidxv] at hm
    intro a b hab
    exact hm (Set.mem_Iio.mpr a.2) (Set.mem_Iio.mpr b.2) hab
  · -- c wu2 = star
    have h := hwu2stab; rw [hidxu, Nat.sub_self] at h
    exact h
  · -- c wv3 = star
    have h := hwv3stab; rw [hidxv, Nat.sub_self] at h
    exact h
  · -- IsEdge
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
end GSn
end TripleSystem593

end

section

/-!
# Cycle collapse (§4, `lem:cycle-collapse`)

This file formalizes the transfinite core of the paper's §4 "Finite linear
traces of the lift": the **cycle collapse** lemma.  If a finite linear triple
system `F` embeds into the lift `Lift(A,κ)` via `f`, and we write
`f v = (ν v, a v)` with `ν v : Node A κ` the *sequence node*, then on every
Berge cycle of `F` all sequence nodes `ν (c.v i)` are equal.

This is `lem:cycle-collapse` of arXiv:2606.24882, the linchpin of the necessity
direction of the bridge-trace theorem.
-/

open Cardinal Ordinal

namespace TripleSystem593

universe u

variable {α : Type u} {A : SimpleGraph α} {κ : Cardinal.{u}}

/-! ### The prefix order on nodes -/

/-- Two nodes are *comparable* in the initial-segment (prefix) order: equal, or
one is a proper prefix of the other. -/
def Node.comparable (σ τ : Node A κ) : Prop :=
  σ = τ ∨ Node.pre A κ σ τ ∨ Node.pre A κ τ σ

/-- Weak prefix: `σ = τ` or `σ` is a proper prefix of `τ`. -/
def Node.wpre (σ τ : Node A κ) : Prop :=
  σ = τ ∨ Node.pre A κ σ τ

theorem Node.pre.pos_lt {σ τ : Node A κ} (h : Node.pre A κ σ τ) : σ.pos < τ.pos :=
  h.1

theorem Node.pre.agree {σ τ : Node A κ} (h : Node.pre A κ σ τ)
    (q : Idx κ) (hq : q < σ.pos) :
    τ.seq ⟨q, lt_trans hq h.1⟩ = σ.seq ⟨q, hq⟩ :=
  h.2 q hq

/-- If two nodes agree below `σ.pos` and have equal `pos` (with `σ.pos ≤ τ.pos`
and, symmetrically, agreement), they are equal. Concretely: a weak prefix with
equal position is equality. -/
theorem Node.wpre_pos_eq {σ τ : Node A κ} (h : Node.wpre σ τ) (hpos : τ.pos ≤ σ.pos) :
    σ = τ := by
  rcases h with h | h
  · exact h
  · exact absurd h.1 (not_lt.mpr hpos)

/-- `Node.pre` is transitive. -/
theorem Node.pre.trans {ρ σ τ : Node A κ} (h1 : Node.pre A κ ρ σ)
    (h2 : Node.pre A κ σ τ) : Node.pre A κ ρ τ := by
  refine ⟨lt_trans h1.1 h2.1, ?_⟩
  intro q hq
  rw [h2.2 q (lt_trans hq h1.1), h1.2 q hq]

/-- Weak-prefix / proper-prefix composition. -/
theorem Node.wpre.trans_pre {ρ σ τ : Node A κ} (h1 : Node.wpre ρ σ)
    (h2 : Node.pre A κ σ τ) : Node.wpre ρ τ := by
  rcases h1 with rfl | h1
  · exact Or.inr h2
  · exact Or.inr (h1.trans h2)

/-
**Prefix nesting.**  If `ρ` is a weak prefix of `a`, `b` is comparable with
`a`, and `ρ.pos ≤ b.pos`, then `ρ` is a weak prefix of `b`.  (Prefixes of a
common node are nested by position.)
-/
theorem Node.wpre_of_comparable {ρ a b : Node A κ} (hρa : Node.wpre ρ a)
    (hcomp : Node.comparable a b) (hpos : ρ.pos ≤ b.pos) :
    Node.wpre ρ b := by
  rcases hρa with ( rfl | hρa ) <;> rcases hcomp with ( rfl | hcomp | hcomp ) <;> simp_all +decide [ Node.wpre ];
  · exact absurd hpos ( not_le_of_gt hcomp.1 );
  · exact Or.inr ( Node.pre.trans hρa hcomp );
  · cases lt_or_eq_of_le hpos <;> simp_all +decide [ pre ];
    · grind +suggestions;
    · cases ρ ; cases b ; aesop

/-
If `p` and `q` are comparable and both strictly longer than a coordinate `d`,
their entries at `d` agree.
-/
theorem Node.seqAt_eq_of_comparable {p q : Node A κ} (hcomp : Node.comparable p q)
    {d : Idx κ} (hp : d < p.pos) (hq : d < q.pos) :
    p.seq ⟨d, hp⟩ = q.seq ⟨d, hq⟩ := by
  rcases hcomp with ( rfl | hcomp | hcomp );
  · grind;
  · exact hcomp.agree d hp ▸ rfl;
  · exact hcomp.agree d hq ▸ rfl

/-! ### Lift-edge structure -/

/-- The three first-coordinates of a lift edge `{(σ,x),(σ,y),(τ,z)}` lie in
`{σ, τ}`. -/
theorem liftEdge_fst_mem {σ τ : Node A κ} {x y z : α}
    {p : Node A κ × α} (hp : p ∈ ({(σ, x), (σ, y), (τ, z)} : Set (Node A κ × α))) :
    p.1 = σ ∨ p.1 = τ := by
  rcases hp with rfl | rfl | rfl
  · left; rfl
  · left; rfl
  · right; rfl

/-- Any two vertices lying in a common edge of `F` whose `f`-image is a lift edge
have comparable sequence nodes. -/
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

/-
**Base pair of a rising edge.**  If an edge `e` of `F` has `f`-image a lift
edge, and `u, w ∈ e` with `(f u).1` a proper prefix of `(f w).1`, then the base
pair of the lift edge sits at node `(f u).1`: there are `x ≠ y` with
`(f w).1.seq ⟨(f u).1.pos, _⟩ = s(x, y)` and both `((f u).1, x)` and
`((f u).1, y)` lie in `f '' e`.
-/
theorem rising_base {F : FTS} {f : F.V → Node A κ × α}
    (e : Finset F.V) (he : (f '' (↑e : Set F.V)) ∈ (liftHG A κ).edges)
    {u w : F.V} (hu : u ∈ e) (hw : w ∈ e) (hpre : Node.pre A κ (f u).1 (f w).1) :
    ∃ x y : α, x ≠ y ∧
      ((f w).1.seq ⟨(f u).1.pos, hpre.1⟩ : Sym2 α) = s(x, y) ∧
      ((f u).1, x) ∈ (f '' (↑e : Set F.V)) ∧ ((f u).1, y) ∈ (f '' (↑e : Set F.V)) := by
  obtain ⟨ σ', τ', a, b, cc, hpre', hseq', hset ⟩ := he;
  -- From `hpre`, we have `(f u).1 = σ'` and `(f w).1 = τ'`.
  have h_eq : (f u).1 = σ' ∧ (f w).1 = τ' := by
    have h_eq : (f u).1 ∈ ({σ', τ'} : Set (Node A κ)) ∧ (f w).1 ∈ ({σ', τ'} : Set (Node A κ)) := by
      exact ⟨ by simpa using liftEdge_fst_mem ( hset ▸ Set.mem_image_of_mem f hu ), by simpa using liftEdge_fst_mem ( hset ▸ Set.mem_image_of_mem f hw ) ⟩;
    cases h_eq.1 <;> cases h_eq.2 <;> simp_all +decide [ Node.pre ];
    exact absurd hpre.choose ( not_lt_of_gt hpre'.1 );
  have := ( τ'.seq ⟨ σ'.pos, hpre'.1 ⟩ ) |>.2; simp_all +decide [ SimpleGraph.mem_edgeSet ] ;
  exact ⟨ a, b, this.ne, by aesop ⟩

/-- Sym2-level version of `seqAt_eq_of_comparable`. -/
theorem Node.seqAt_Sym2_eq_of_comparable {p q : Node A κ} (hcomp : Node.comparable p q)
    {d : Idx κ} (hp : d < p.pos) (hq : d < q.pos) :
    ((p.seq ⟨d, hp⟩ : Sym2 α)) = ((q.seq ⟨d, hq⟩ : Sym2 α)) :=
  congrArg (fun e : A.edgeSet => (e : Sym2 α)) (Node.seqAt_eq_of_comparable hcomp hp hq)

/-
**Cyclic induction on `ZMod m`.**  A predicate holding at one point and
closed under `i ↦ i + 1` holds everywhere.
-/
theorem zmod_cyclic_induction {m : ℕ} [NeZero m] {P : ZMod m → Prop} (j0 : ZMod m)
    (hj0 : P j0) (hstep : ∀ i, P i → P (i + 1)) (i : ZMod m) : P i := by
  have h_ind : ∀ n : ℕ, P (j0 + n) := by
    intro n; induction n <;> simp_all +decide [ ← add_assoc ] ;
  convert! h_ind ( i - j0 |> ZMod.val ) ; aesop;

/-- Consecutive vertices on a Berge cycle have comparable sequence nodes. -/
theorem consecutive_comparable {F : FTS} {f : F.V → Node A κ × α}
    (hfe : ∀ e ∈ F.edges, (f '' (↑e : Set F.V)) ∈ (liftHG A κ).edges)
    (c : BergeCycle F) (i : ZMod c.m) :
    Node.comparable (f (c.v i)).1 (f (c.v (i + 1))).1 :=
  bergeEdge_nodes_comparable (c.e i).1 (hfe _ (c.e i).2) (c.mem_left i) (c.mem_right i)

/-
**Value constant along a comparable walk.**  If consecutive nodes `g i, g (i+1)`
are comparable and every node `g (start + j)` (for `j ≤ n`) properly extends `σ`,
then the `Sym2`-value at coordinate `σ.pos` is the same at step `n` as at step
`0`.
-/
theorem seqAt_const_along {m : ℕ} (g : ZMod m → Node A κ)
    (hcomp : ∀ i : ZMod m, Node.comparable (g i) (g (i + 1)))
    (σ : Node A κ) (start : ZMod m) (n : ℕ)
    (hpre : ∀ j : ℕ, j ≤ n → Node.pre A κ σ (g (start + (j : ZMod m)))) :
    ((g (start + (n : ZMod m))).seq ⟨σ.pos, (hpre n le_rfl).1⟩ : Sym2 α)
      = ((g (start + ((0 : ℕ) : ZMod m))).seq ⟨σ.pos, (hpre 0 (Nat.zero_le n)).1⟩ : Sym2 α) := by
  induction' n with n ih;
  · rfl;
  · convert! ih ( fun j hj => hpre j ( Nat.le_succ_of_le hj ) ) using 1;
    convert! Node.seqAt_Sym2_eq_of_comparable _ _ _ using 1;
    convert! hcomp ( start + n ) |> fun h => h.symm using 1 ; push_cast ; ring;
    simp +decide [ add_comm, Node.comparable ];
    grind

/-
**First return.**  If `P` fails at `start` but holds at some `start + t`,
there is a least positive step `n0 ≤ m - 1` with `P (start + n0)` and `P` failing
at every earlier step.
-/
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

/-
**Base adjacency.**  If two distinct vertices `u, w` of an edge `e` of `F`
with `f`-image a lift edge have the *same* sequence node, then their second
coordinates are adjacent in `A` (they are the two base vertices of the lift
edge).
-/
theorem base_adj {F : FTS} {f : F.V → Node A κ × α} (hf : Function.Injective f)
    (e : Finset F.V) (he : (f '' (↑e : Set F.V)) ∈ (liftHG A κ).edges)
    {u w : F.V} (hu : u ∈ e) (hw : w ∈ e) (huw : u ≠ w)
    (hnode : (f u).1 = (f w).1) :
    A.Adj (f u).2 (f w).2 := by
  obtain ⟨ σ, τ, x, y, z, hpre, hseq, hset ⟩ := he;
  have hadj : A.Adj x y := by
    have hm := (τ.seq ⟨σ.pos, hpre.1⟩).2
    rw [hseq] at hm
    exact hm
  have hn : σ ≠ τ := fun h => hpre.1.ne (congrArg Node.pos h)
  have hfu := hset ▸ Set.mem_image_of_mem f hu
  have hfw := hset ▸ Set.mem_image_of_mem f hw
  rcases hfu with h1 | h1 | h1 <;> rcases hfw with h2 | h2 | h2 <;>
    rw [h1, h2] at hnode ⊢ <;> simp only at hnode ⊢
  all_goals first | exact hadj | exact hadj.symm | exact (hn hnode).elim |
    exact (hn hnode.symm).elim | exact (huw (hf (h1.trans h2.symm))).elim

/-! ### The collapse argument -/

/-- **Cycle collapse** (`lem:cycle-collapse`).  If a finite linear triple system
`F` embeds into `Lift(A,κ)` via an injective `f` sending each edge to a lift
edge, then on every Berge cycle all sequence nodes are equal. -/
theorem cycle_collapse {F : FTS} (hlin : F.Linear) (f : F.V → Node A κ × α)
    (hf : Function.Injective f)
    (hfe : ∀ e ∈ F.edges, (f '' (↑e : Set F.V)) ∈ (liftHG A κ).edges)
    (c : BergeCycle F) (i j : ZMod c.m) :
    (f (c.v i)).1 = (f (c.v j)).1 := by
  haveI : NeZero c.m := ⟨by have := c.hm; omega⟩
  -- Step 1: minimal node
  obtain ⟨j0, -, hj0min⟩ := Finset.exists_min_image Finset.univ
    (fun t => (f (c.v t)).1.pos) ⟨i, Finset.mem_univ i⟩
  simp only [Finset.mem_univ, forall_true_left] at hj0min
  set σ := (f (c.v j0)).1 with hσdef
  -- Step 2: all weak-prefix σ
  have hwpre : ∀ t, Node.wpre σ (f (c.v t)).1 := fun t =>
    zmod_cyclic_induction j0 (Or.inl rfl)
      (fun i hi => Node.wpre_of_comparable hi (consecutive_comparable hfe c i) (hj0min (i+1))) t
  suffices hall : ∀ t, (f (c.v t)).1 = σ by rw [hall i, hall j]
  intro t
  by_contra hne
  -- Step 3: rising index
  obtain ⟨k, hk, hk1⟩ : ∃ k, (f (c.v k)).1 = σ ∧ (f (c.v (k+1))).1 ≠ σ := by
    by_contra hall2
    push Not at hall2
    exact hne (zmod_cyclic_induction (P := fun s => (f (c.v s)).1 = σ) j0 rfl
      (fun s hs => hall2 s hs) t)
  have hkpre : Node.pre A κ σ (f (c.v (k+1))).1 :=
    (hwpre (k+1)).resolve_left (fun h => hk1 h.symm)
  -- Step 4: first return
  have hex : ∃ n : ℕ, (f (c.v (k+1+(n:ZMod c.m)))).1 = σ := by
    refine ⟨(j0-(k+1)).val, ?_⟩
    have he : k+1+(((j0-(k+1)).val : ℕ):ZMod c.m) = j0 := by
      rw [ZMod.natCast_zmod_val]; ring
    rw [he]
  obtain ⟨n0, h1n0, hn0m, hPn0, hbefore⟩ :=
    exists_first_return (fun s => (f (c.v s)).1 = σ) (k+1) hk1 hex
  -- Step 5: run pre and falling index
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
  -- Step 6: base pairs at the two boundary edges
  obtain ⟨x1, y1, hxy1, hval1, hmx1, hmy1⟩ :=
    rising_base (c.e k).1 (hfe _ (c.e k).2) (c.mem_left k) (c.mem_right k) (hk.symm ▸ hkpre)
  obtain ⟨x2, y2, hxy2, hval2, hmx2, hmy2⟩ :=
    rising_base (c.e kf).1 (hfe _ (c.e kf).2) (c.mem_right kf) (c.mem_left kf) (hνkf1.symm ▸ hνkf_pre)
  -- rewrite the memberships and base-pair values to base node σ
  simp only [hk] at hval1 hmx1 hmy1
  simp only [hνkf1] at hval2 hmx2 hmy2
  -- Step 7: the two base pairs are equal Sym2 values (constant along the run)
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
  -- Step 8: same base pair as a set
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
  -- Step 9: linearity contradiction
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

/-- **Bridge incidence from an embedding** (necessity part of the bridge-trace
theorem).  If a finite linear triple system `F` embeds into `Lift(A,κ)` via an
injective `f`, then every edge `ed` of `F` is incident with a *bridge*: the
incidence at the apex vertex (whose image is the apex `(τ,z)` of the lift edge)
lies on no Berge cycle.  This is one of the three intrinsic conditions of the
classification, and the key use of `cycle_collapse`. -/
theorem exists_bridge_incidence {F : FTS} (hlin : F.Linear) (f : F.V → Node A κ × α)
    (hf : Function.Injective f)
    (hfe : ∀ e ∈ F.edges, (f '' (↑e : Set F.V)) ∈ (liftHG A κ).edges)
    (ed : {e : Finset F.V // e ∈ F.edges}) :
    ∃ w ∈ ed.1, IsBridgeInc F w ed := by
  obtain ⟨σ, τ, x, y, z, hpre, hseq, hset⟩ := hfe ed.1 ed.2
  -- the apex host vertex (τ,z) has a preimage `w ∈ ed.1`
  have hmem : ((τ, z) : Node A κ × α) ∈ f '' (↑ed.1 : Set F.V) := by
    rw [hset]; right; right; rfl
  obtain ⟨w, hw, hfw⟩ := hmem
  refine ⟨w, hw, hw, ?_⟩
  rintro ⟨c, i, hei, hvi⟩
  haveI : Fact (1 < c.m) := ⟨by have := c.hm; omega⟩
  -- the other displayed vertex `w'` of the Berge cycle at edge `ed`
  have hcc := cycle_collapse hlin f hf hfe c i (i + 1)
  have hvne : c.v i ≠ c.v (i + 1) := by
    intro h
    have hii : i = i + 1 := c.vinj h
    exact zero_ne_one (by linear_combination hii : (0 : ZMod c.m) = 1)
  -- `w` has apex node `τ`
  have hwnode : (f w).1 = τ := by rw [hfw]
  -- identify the other vertex `w'` in `ed.1`, distinct from `w`, with base node `σ`
  have hbase : ∀ v : F.V, v ∈ ed.1 → v ≠ w → (f v).1 = σ := by
    intro v hv hvw
    have hfv : f v ∈ f '' (↑ed.1 : Set F.V) := ⟨v, hv, rfl⟩
    rw [hset] at hfv
    rcases hfv with h | h | h
    · rw [h]
    · rw [h]
    · exact absurd (hf (by rw [h, hfw])) hvw
  -- both displayed vertices lie in `ed.1` and one of them is `w`
  have hi_mem : c.v i ∈ ed.1 := by rw [← hei]; exact c.mem_left i
  have hi1_mem : c.v (i + 1) ∈ ed.1 := by rw [← hei]; exact c.mem_right i
  -- derive σ = τ, contradicting the strict prefix
  have hστ : σ = τ := by
    rcases hvi with hvi | hvi
    · -- w = c.v i, so w' = c.v (i+1)
      have hw' : (f (c.v (i + 1))).1 = σ :=
        hbase _ hi1_mem (fun h => hvne (hvi.trans h.symm))
      rw [← hw', ← hcc, hvi, hwnode]
    · -- w = c.v (i+1), so w' = c.v i
      have hw' : (f (c.v i)).1 = σ :=
        hbase _ hi_mem (fun h => hvne (h.trans hvi.symm))
      rw [← hw', hcc, hvi, hwnode]
  exact absurd hpre.1 (by rw [hστ]; exact lt_irrefl _)

/-
**Berge cycle to graph cycle** (`lem:cycle-selector`, host form).  If a finite
linear triple system `F` embeds into `Lift(A,κ)` and has a Berge cycle of length
`m`, then `A` contains an `m`-cycle: an injective `v : ZMod m → α` with consecutive
vertices adjacent.  (Follows from `cycle_collapse`: all cycle vertices share a
node `σ`, and each cycle edge's base pair is an actual edge of `A`.)  This is the
case-(iii) input of the spectrum construction.
-/
theorem lift_bergeCycle_graphCycle {F : FTS} (hlin : F.Linear) (f : F.V → Node A κ × α)
    (hf : Function.Injective f)
    (hfe : ∀ e ∈ F.edges, (f '' (↑e : Set F.V)) ∈ (liftHG A κ).edges)
    (c : BergeCycle F) :
    ∃ v : ZMod c.m → α, Function.Injective v ∧ ∀ i, A.Adj (v i) (v (i + 1)) := by
  -- Show that `v` is injective.
  have hv_inj : Function.Injective (fun i => (f (c.v i)).2) := by
    intro i j hij
    have hnode : (f (c.v i)).1 = (f (c.v j)).1 := by
      convert! cycle_collapse hlin f hf hfe c i j using 1;
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

/-- **A lift embedding yields a bridge selector.**  If a finite linear triple
system `F` embeds into `Lift(A,κ)`, then `F` has a bridge selector.  Hence, by
contraposition, a finite linear system with *no* bridge selector cannot embed
into any lift `Lift(A,κ)` — this is the case-(ii) input of the spectrum
construction (`thm:classification`, `thm:spectrum`). -/
theorem bridgeSelector_of_embeds_lift {F : FTS} (hlin : F.Linear)
    (h : F.Embeds (liftHG A κ)) : Nonempty (BridgeSelector F) := by
  obtain ⟨f, hf, hfe⟩ := h
  refine ⟨⟨fun ed => (exists_bridge_incidence hlin f hf hfe ed).choose, fun ed => ?_⟩⟩
  exact (exists_bridge_incidence hlin f hf hfe ed).choose_spec.2

/-- **Case (ii) omission** (`thm:classification`, `thm:spectrum`).  A finite
linear triple system with *no* bridge selector is omitted by every lift
`Lift(A,κ)`.  (Contrapositive of `bridgeSelector_of_embeds_lift`.) -/
theorem lift_omits_of_no_bridgeSelector {F : FTS} (hlin : F.Linear)
    (hns : ¬ Nonempty (BridgeSelector F)) : ¬ F.Embeds (liftHG A κ) :=
  fun h => hns (bridgeSelector_of_embeds_lift hlin h)

/-- **Case (iii) omission** (`thm:classification`, `thm:spectrum`).  If a finite
linear triple system `F` has a Berge cycle of length `m` and the graph `A`
contains no `m`-cycle, then `Lift(A,κ)` omits `F`.  Combined with a graph of
high odd girth (`E2`) this handles the odd-Berge-cycle case. -/
theorem lift_omits_of_bergeCycle {F : FTS} (hlin : F.Linear) (c : BergeCycle F)
    (hA : ¬ ∃ v : ZMod c.m → α, Function.Injective v ∧ ∀ i, A.Adj (v i) (v (i + 1))) :
    ¬ F.Embeds (liftHG A κ) := by
  rintro ⟨f, hf, hfe⟩
  exact hA (lift_bergeCycle_graphCycle hlin f hf hfe c)

end TripleSystem593

end

section

/-!
# Erdos Problem 593 — common pair not obligatory

We construct a linear 3-uniform hypergraph of uncountable chromatic cardinal whose vertices are the
non-diagonal unordered pairs on a base set `omaBase` and whose hyperedges are the triangles on three
distinct base elements. Because any two distinct edges share at most one vertex, `commonPair` cannot
appear in this hypergraph. Uncountable chromatic cardinal follows from a self-contained Cantor
diagonal / Erdos-Rado stepping argument showing that every countable coloring of pairs of `omaBase`
admits a monochromatic triangle.
-/

namespace OMAErdos593

open Cardinal Set

abbrev omaIdx : Type := (Order.succ ℵ₀).ord.ToType

abbrev omaHist : Type := Σ a : omaIdx, ({ b : omaIdx // b < a } → ℕ)

abbrev omaBase : Type := Set omaHist

abbrev omaVert : Type := { e : Sym2 omaBase // ¬ e.IsDiag }

lemma omaVert_mk_ne_diag {x y : omaBase} (hxy : x ≠ y) : ¬ (s(x, y)).IsDiag := by
  simpa [Sym2.mk_isDiag_iff] using hxy

def omaTriEdge (x y z : omaBase) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) : Set omaVert :=
  { ⟨s(x, y), omaVert_mk_ne_diag hxy⟩,
    ⟨s(y, z), omaVert_mk_ne_diag hyz⟩,
    ⟨s(x, z), omaVert_mk_ne_diag hxz⟩ }

lemma omaTriEdge_encard (x y z : omaBase) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    (omaTriEdge x y z hxy hyz hxz).encard = 3 := by
  let u₁ : omaVert := ⟨s(x, y), omaVert_mk_ne_diag hxy⟩
  let u₂ : omaVert := ⟨s(y, z), omaVert_mk_ne_diag hyz⟩
  let u₃ : omaVert := ⟨s(x, z), omaVert_mk_ne_diag hxz⟩
  have h12 : u₁ ≠ u₂ := by
    intro h
    have hs : s(x, y) = s(y, z) := congrArg Subtype.val h
    rcases Sym2.eq_iff.mp hs with ⟨_, _⟩ | ⟨rfl, _⟩
    · exact hxy ‹_›
    · exact hxz rfl
  have h13 : u₁ ≠ u₃ := by
    intro h
    have hs : s(x, y) = s(x, z) := congrArg Subtype.val h
    rcases Sym2.eq_iff.mp hs with ⟨_, hyz'⟩ | ⟨hxz', _⟩
    · exact hyz hyz'
    · exact hxz hxz'
  have h23 : u₂ ≠ u₃ := by
    intro h
    have hs : s(y, z) = s(x, z) := congrArg Subtype.val h
    rcases Sym2.eq_iff.mp hs with ⟨hyx, _⟩ | ⟨hyz', _⟩
    · exact hxy hyx.symm
    · exact hyz hyz'
  change ({u₁, u₂, u₃} : Set omaVert).encard = 3
  have hn1 : u₁ ∉ ({u₂, u₃} : Set omaVert) := by
    simp [Set.mem_insert_iff, Set.mem_singleton_iff, h12, h13]
  have hn2 : u₂ ∉ ({u₃} : Set omaVert) := by
    simp [Set.mem_singleton_iff, h23]
  rw [Set.encard_insert_of_notMem hn1, Set.encard_insert_of_notMem hn2, Set.encard_singleton]
  norm_num

lemma mem_omaTriEdge_iff (x y z : omaBase) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (p : omaVert) :
    p ∈ omaTriEdge x y z hxy hyz hxz ↔ ∀ w ∈ p.1, w ∈ ({x, y, z} : Set omaBase) := by
  constructor
  · intro hp w hw
    rcases hp with rfl | rfl | rfl
    · simp only [Sym2.mem_iff] at hw
      rcases hw with rfl | rfl <;> simp
    · simp only [Sym2.mem_iff] at hw
      rcases hw with rfl | rfl <;> simp
    · simp only [Sym2.mem_iff] at hw
      rcases hw with rfl | rfl <;> simp
  · obtain ⟨e, he⟩ := p
    induction e using Sym2.ind with
    | _ a b =>
      intro hsub
      have hab : a ≠ b := by simpa [Sym2.mk_isDiag_iff] using he
      have ha : a ∈ ({x, y, z} : Set omaBase) := hsub a (Sym2.mem_mk_left a b)
      have hb : b ∈ ({x, y, z} : Set omaBase) := hsub b (Sym2.mem_mk_right a b)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      unfold omaTriEdge
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Subtype.mk.injEq]
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
      · exact absurd rfl hab
      · left; rfl
      · right; right; rfl
      · left; exact Sym2.eq_swap
      · exact absurd rfl hab
      · right; left; rfl
      · right; right; exact Sym2.eq_swap
      · right; left; exact Sym2.eq_swap
      · exact absurd rfl hab

lemma two_edges_support (x y z : omaBase) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    {u v : omaVert} (hu : u ∈ omaTriEdge x y z hxy hyz hxz)
    (hv : v ∈ omaTriEdge x y z hxy hyz hxz) (huv : u ≠ v) (w : omaBase) :
    w ∈ ({x, y, z} : Set omaBase) ↔ w ∈ u.1 ∨ w ∈ v.1 := by
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  · exact absurd rfl huv
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.mem_iff]; tauto
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.mem_iff]; tauto
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.mem_iff]; tauto
  · exact absurd rfl huv
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.mem_iff]; tauto
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.mem_iff]; tauto
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.mem_iff]; tauto
  · exact absurd rfl huv

def omaHypergraph : UniformHypergraph omaVert 3 where
  vertexSet := Set.univ
  edgeSet := { E : Set omaVert |
    ∃ (x y z : omaBase) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z),
      E = omaTriEdge x y z hxy hyz hxz }
  subset_vertexSet_of_mem_edgeSet' := fun _ _ => Set.subset_univ _
  vertexSet_eq_univ := rfl
  uniform := by
    rintro E ⟨x, y, z, hxy, hyz, hxz, rfl⟩
    exact omaTriEdge_encard x y z hxy hyz hxz

lemma omaHypergraph_linear {E₁ E₂ : Set omaVert}
    (hE₁ : E₁ ∈ omaHypergraph.edgeSet) (hE₂ : E₂ ∈ omaHypergraph.edgeSet)
    {u v : omaVert} (hu₁ : u ∈ E₁) (hv₁ : v ∈ E₁) (hu₂ : u ∈ E₂) (hv₂ : v ∈ E₂) (huv : u ≠ v) :
    E₁ = E₂ := by
  rcases hE₁ with ⟨x₁, y₁, z₁, hxy₁, hyz₁, hxz₁, rfl⟩
  rcases hE₂ with ⟨x₂, y₂, z₂, hxy₂, hyz₂, hxz₂, rfl⟩
  have hsup : ({x₁, y₁, z₁} : Set omaBase) = {x₂, y₂, z₂} := by
    ext w
    rw [two_edges_support x₁ y₁ z₁ hxy₁ hyz₁ hxz₁ hu₁ hv₁ huv w,
      two_edges_support x₂ y₂ z₂ hxy₂ hyz₂ hxz₂ hu₂ hv₂ huv w]
  ext p
  rw [mem_omaTriEdge_iff, mem_omaTriEdge_iff, hsup]

lemma omaIdx_not_countable : ¬ Countable omaIdx := by
  intro hcount
  have hle : #omaIdx ≤ ℵ₀ := Cardinal.mk_le_aleph0
  have hmk : #omaIdx = Order.succ ℵ₀ := by
    simp [omaIdx]
  rw [hmk] at hle
  exact not_lt_of_ge hle (Order.lt_succ ℵ₀)

lemma exists_three_same_color_on_omaIdx (sz : omaIdx → ℕ) :
    ∃ a₀ a₁ a₂ : omaIdx, a₀ < a₁ ∧ a₁ < a₂ ∧ sz a₀ = sz a₁ := by
  classical
  by_contra hno
  let g : omaIdx → ℕ × Bool := fun a => (sz a, decide (∃ b : omaIdx, b < a ∧ sz b = sz a))
  have hginj : Function.Injective g := by
    intro a₁ a₂ hg
    have hsz : sz a₁ = sz a₂ := congrArg Prod.fst hg
    have hdec : decide (∃ b : omaIdx, b < a₁ ∧ sz b = sz a₁) =
        decide (∃ b : omaIdx, b < a₂ ∧ sz b = sz a₂) := congrArg Prod.snd hg
    rcases lt_trichotomy a₁ a₂ with hlt | rfl | hgt
    · have hex₂ : ∃ b : omaIdx, b < a₂ ∧ sz b = sz a₂ := ⟨a₁, hlt, hsz⟩
      have hex₁ : ∃ b : omaIdx, b < a₁ ∧ sz b = sz a₁ :=
        of_decide_eq_true (hdec.trans (decide_eq_true hex₂))
      rcases hex₁ with ⟨a₀, ha₀, hsz₀⟩
      exact False.elim (hno ⟨a₀, a₁, a₂, ha₀, hlt, hsz₀⟩)
    · rfl
    · have hex₁ : ∃ b : omaIdx, b < a₁ ∧ sz b = sz a₁ := ⟨a₂, hgt, hsz.symm⟩
      have hex₂ : ∃ b : omaIdx, b < a₂ ∧ sz b = sz a₂ :=
        of_decide_eq_true (hdec.symm.trans (decide_eq_true hex₁))
      rcases hex₂ with ⟨a₀, ha₀, hsz₀⟩
      exact False.elim (hno ⟨a₀, a₂, a₁, ha₀, hgt, hsz₀⟩)
  exact omaIdx_not_countable (Function.Injective.countable hginj)

open Classical in
noncomputable def omaStep (col : Sym2 omaBase → ℕ) (a : omaIdx)
    (rec : ∀ b : omaIdx, b < a → ({ d : omaIdx // d < b } → ℕ) → Option omaBase)
    (s : { b : omaIdx // b < a } → ℕ) : Option omaBase :=
  let good : omaBase → Prop := fun x =>
    ∀ (b : omaIdx) (hba : b < a),
      ∃ y : omaBase,
        rec b hba (fun ⟨d, hdb⟩ => s ⟨d, hdb.trans hba⟩) = some y ∧
        x ≠ y ∧ col s(y, x) = s ⟨b, hba⟩
  if h : ∃ x : omaBase, good x then some (Classical.choose h) else none

noncomputable def omaNode (col : Sym2 omaBase → ℕ) :
    (a : omaIdx) → ({ b : omaIdx // b < a } → ℕ) → Option omaBase :=
  WellFounded.fix (wellFounded_lt (α := omaIdx)) (omaStep col)

lemma omaNode_eq (col : Sym2 omaBase → ℕ) (a : omaIdx) (s : { b : omaIdx // b < a } → ℕ) :
    omaNode col a s = omaStep col a (fun b _ => omaNode col b) s :=
  congrFun (WellFounded.fix_eq (wellFounded_lt (α := omaIdx)) (omaStep col) a) s

lemma exists_mono_triangle (col : Sym2 omaBase → ℕ) :
    ∃ x y w : omaBase, x ≠ y ∧ y ≠ w ∧ x ≠ w ∧
      col s(x, y) = col s(y, w) ∧ col s(x, y) = col s(x, w) := by
  classical
  let f : omaHist → omaBase := fun p =>
    match omaNode col p.1 p.2 with
    | some x => x
    | none => ∅
  let z : omaBase := { p : omaHist | p ∉ f p }
  have hz_not_node : ∀ (a : omaIdx) (s : { b : omaIdx // b < a } → ℕ),
      omaNode col a s ≠ some z := by
    intro a s heq
    let p : omaHist := ⟨a, s⟩
    have hfp : f p = z := by simp [f, p, heq]
    have hmem : p ∈ z ↔ p ∉ z := by
      change p ∉ f p ↔ p ∉ z
      rw [hfp]
    exact iff_not_self hmem
  let szStep : ∀ a : omaIdx, (∀ b : omaIdx, b < a → ℕ) → ℕ := fun a rec =>
    match omaNode col a (fun ⟨b, hba⟩ => rec b hba) with
    | some y => col s(y, z)
    | none => 0
  let sz : omaIdx → ℕ := WellFounded.fix (wellFounded_lt (α := omaIdx)) szStep
  have hsz_eq : ∀ a : omaIdx,
      sz a = match omaNode col a (fun ⟨b, _⟩ => sz b) with
        | some y => col s(y, z)
        | none => 0 := fun a =>
    WellFounded.fix_eq (wellFounded_lt (α := omaIdx)) szStep a
  have hnode_some : ∀ a : omaIdx, ∃ y : omaBase, omaNode col a (fun ⟨b, _⟩ => sz b) = some y := by
    intro a
    induction a using WellFounded.induction (wellFounded_lt (α := omaIdx)) with
    | h a ih =>
      have hgood_z : ∀ (b : omaIdx) (hba : b < a),
          ∃ y : omaBase,
            omaNode col b (fun ⟨d, _⟩ => sz d) = some y ∧
            z ≠ y ∧ col s(y, z) = sz b := by
        intro b hba
        obtain ⟨y, hy⟩ := ih b hba
        refine ⟨y, hy, ?_, ?_⟩
        · intro hzy
          subst hzy
          exact hz_not_node b _ hy
        · rw [hsz_eq b, hy]
      have hex : ∃ x : omaBase, ∀ (b : omaIdx) (hba : b < a),
          ∃ y : omaBase,
            omaNode col b (fun ⟨d, _⟩ => sz d) = some y ∧
            x ≠ y ∧ col s(y, x) = sz b := ⟨z, hgood_z⟩
      refine ⟨Classical.choose hex, ?_⟩
      rw [omaNode_eq]
      dsimp only [omaStep]
      rw [dif_pos hex]
  let y : omaIdx → omaBase := fun a => Classical.choose (hnode_some a)
  have hy_eq : ∀ a : omaIdx, omaNode col a (fun ⟨b, _⟩ => sz b) = some (y a) :=
    fun a => Classical.choose_spec (hnode_some a)
  have hy_rel : ∀ {b a : omaIdx}, b < a → y a ≠ y b ∧ col s(y b, y a) = sz b := by
    intro b a hba
    have hstep := hy_eq a
    rw [omaNode_eq] at hstep
    dsimp only [omaStep] at hstep
    split_ifs at hstep with hex
    · have hya : Classical.choose hex = y a := Option.some.inj hstep
      have hspec := Classical.choose_spec hex b hba
      rw [hya] at hspec
      rcases hspec with ⟨y', hy', hne, hcol⟩
      have hy'eq : y' = y b := Option.some.inj (hy'.symm.trans (hy_eq b))
      subst hy'eq
      exact ⟨hne, hcol⟩
  obtain ⟨a₀, a₁, a₂, ha01, ha12, hsz01⟩ := exists_three_same_color_on_omaIdx sz
  have ha02 : a₀ < a₂ := ha01.trans ha12
  obtain ⟨hne01, hcol01⟩ := hy_rel ha01
  obtain ⟨hne12, hcol12⟩ := hy_rel ha12
  obtain ⟨hne02, hcol02⟩ := hy_rel ha02
  refine ⟨y a₀, y a₁, y a₂, hne01.symm, hne12.symm, hne02.symm, ?_, ?_⟩
  · rw [hcol01, hcol12, hsz01]
  · rw [hcol01, hcol02]

lemma aleph0_lt_omaHypergraph_chromatic : ℵ₀ < omaHypergraph.chromaticCardinal := by
  classical
  by_contra hle
  replace hle : omaHypergraph.chromaticCardinal ≤ ℵ₀ := not_lt.mp hle
  let S : Set Cardinal.{0} :=
    { κ : Cardinal.{0} | ∃ (C : Type), #C = κ ∧ ∃ f : omaVert → C, omaHypergraph.IsProperColoring f }
  have hS_ne : S.Nonempty :=
    ⟨#omaVert, omaVert, rfl, id,
      omaHypergraph.isProperColoring_of_injective (by decide) Function.injective_id⟩
  have hmem : omaHypergraph.chromaticCardinal ∈ S := csInf_mem hS_ne
  rcases hmem with ⟨C, hC_card, f, hf⟩
  have hC_le : #C ≤ ℵ₀ := by rwa [hC_card]
  have hC_count : Countable C := Cardinal.mk_le_aleph0_iff.mp hC_le
  obtain ⟨emb, hemb_inj⟩ := @Countable.exists_injective_nat C hC_count
  let col : Sym2 omaBase → ℕ := fun e =>
    if h : ¬ e.IsDiag then emb (f ⟨e, h⟩) else 0
  obtain ⟨x, y, z, hxy, hyz, hxz, hc1, hc2⟩ := exists_mono_triangle col
  let E := omaTriEdge x y z hxy hyz hxz
  have hE : E ∈ omaHypergraph.edgeSet := ⟨x, y, z, hxy, hyz, hxz, rfl⟩
  obtain ⟨u, hu, v, hv, hfuv⟩ := hf E hE
  have hcol_eq : ∀ p ∈ E, emb (f p) = col s(x, y) := by
    intro p hp
    have hp_val : emb (f p) = col p.1 := by
      dsimp [col]
      rw [dif_pos p.2]
    rw [hp_val]
    rcases hp with rfl | rfl | rfl
    · rfl
    · exact hc1.symm
    · exact hc2.symm
  have hemb_eq : emb (f u) = emb (f v) := (hcol_eq u hu).trans (hcol_eq v hv).symm
  exact hfuv (hemb_inj hemb_eq)

end OMAErdos593

end

namespace TripleSystem593

open Cardinal

/-- The finite system on the same labelled vertices, including isolated ones. -/
noncomputable def finiteSystem {n : ℕ} (F : UniformHypergraph (Fin n) 3) : FTS := by
  classical
  exact {
    V := Fin n
    edges := Finset.univ.filter (fun e : Finset (Fin n) => (e : Set (Fin n)) ∈ F.edgeSet)
    card3 := by
      intro e he
      have h := F.uniform _ (Finset.mem_filter.mp he).2
      have hcard : (e.card : ENat) = 3 := by simpa using h
      exact_mod_cast hcard
  }

theorem finiteSystem_mem {n : ℕ} (F : UniformHypergraph (Fin n) 3) (e : Finset (Fin n)) :
    e ∈ (finiteSystem F).edges ↔ (e : Set (Fin n)) ∈ F.edgeSet := by
  classical
  exact ⟨fun he => (Finset.mem_filter.mp he).2,
    fun he => Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩

def host {V : Type} (H : UniformHypergraph V 3) : TripleHost V := ⟨H.edgeSet⟩

theorem host_triple {V : Type} (H : UniformHypergraph V 3) : (host H).IsTripleSystem :=
  fun e he => Set.ncard_eq_three.mpr (Set.encard_eq_three.mp (H.uniform e he))

def uniformHost {V : Type} (H : TripleHost V) (h : H.IsTripleSystem) : UniformHypergraph V 3 where
  vertexSet := Set.univ
  edgeSet := H.edges
  subset_vertexSet_of_mem_edgeSet' := fun _ _ => Set.subset_univ _
  vertexSet_eq_univ := rfl
  uniform := fun e he => Set.encard_eq_three.mpr (Set.ncard_eq_three.mp (h e he))

theorem uncountable_iff {V : Type} (H : UniformHypergraph V 3) :
    ℵ₀ < H.chromaticCardinal ↔ (host H).UncountablyChromatic := by
  constructor
  · rintro h ⟨c, hc⟩
    exact h.not_ge (by simpa using H.chromaticCardinal_le (f := c) hc)
  · intro h
    by_contra! hle
    let S := {k : Cardinal | ∃ (C : Type), #C = k ∧ ∃ c : V → C, H.IsProperColoring c}
    have hne : S.Nonempty :=
      ⟨#V, V, rfl, id, H.isProperColoring_of_injective (by decide) Function.injective_id⟩
    have hmem : H.chromaticCardinal ∈ S := csInf_mem hne
    obtain ⟨C, hC, c, hc⟩ := hmem
    have hsize : #C ≤ #((ℵ₀ : Cardinal).out) := by simpa [hC] using hle
    obtain ⟨f⟩ := (Cardinal.le_def _ _).mp hsize
    apply h
    refine ⟨f ∘ c, ?_⟩
    intro e he
    obtain ⟨u, hu, v, hv, huv⟩ := hc e he
    exact ⟨u, hu, v, hv, f.injective.ne huv⟩

theorem appears_iff {n : ℕ} (F : UniformHypergraph (Fin n) 3) {V : Type}
    (H : UniformHypergraph V 3) : F.Appears H ↔ (finiteSystem F).Embeds (host H) := by
  classical
  constructor
  · rintro ⟨f, hf, h⟩
    exact ⟨f, hf, fun e he => h (Hypergraph.image_mem_edgeSet_image ((finiteSystem_mem F e).mp he))⟩
  · rintro ⟨f, hf, h⟩
    refine ⟨f, hf, ?_⟩
    rintro _ ⟨e, he, rfl⟩
    have he' : (e.toFinset : Set (Fin n)) = e := Set.coe_toFinset _
    exact he' ▸ h e.toFinset ((finiteSystem_mem F _).mpr (he'.symm ▸ he))

theorem obligatory_iff {n : ℕ} (F : UniformHypergraph (Fin n) 3) :
    F.IsObligatory ↔ FTS.Obligatory.{0} (finiteSystem F) := by
  classical
  constructor
  · intro h V H htri huc
    let U := uniformHost H htri
    exact (appears_iff F U).mp (h V U ((uncountable_iff U).mpr huc))
  · intro h V _ H hχ
    exact (appears_iff F H).mpr (h (host H) (host_triple H) ((uncountable_iff H).mp hχ))

/-- Dorman’s triangle host forces linearity in every finite obligatory system. -/
theorem linear_of_obligatory {F : FTS} (h : FTS.Obligatory.{0} F) : F.Linear := by
  let H := OMAErdos593.omaHypergraph
  obtain ⟨f, hf, hfe⟩ := h (host H) (host_triple H)
    ((uncountable_iff H).mp OMAErdos593.aleph0_lt_omaHypergraph_chromatic)
  intro a ha b hb hne
  apply Finset.card_le_one.mpr
  intro x hx y hy
  by_contra hxy
  obtain ⟨hxa, hxb⟩ := Finset.mem_inter.mp hx
  obtain ⟨hya, hyb⟩ := Finset.mem_inter.mp hy
  have hEq := OMAErdos593.omaHypergraph_linear (hfe a ha) (hfe b hb)
    (Set.mem_image_of_mem f hxa) (Set.mem_image_of_mem f hya)
    (Set.mem_image_of_mem f hxb) (Set.mem_image_of_mem f hyb) (hf.ne hxy)
  exact hne (Finset.coe_injective ((Set.image_injective.mpr hf) hEq))

/-- Li's lift of a generalized Specker graph forces the bridge and parity conditions. -/
theorem intrinsic_of_obligatory {F : FTS} (h : FTS.Obligatory.{0} F) : F.IntrinsicObligatory := by
  let κ : Cardinal := Order.succ ℵ₀
  have hκ : ℵ₀ < κ := Order.lt_succ _
  have hreg : κ.IsRegular := Cardinal.isRegular_succ le_rfl
  have hlin := linear_of_obligatory h
  have embeds (k : ℕ) : F.Embeds (liftHG (GSn.graph k κ) κ) := by
    let A := GSn.graph k κ
    apply h
    · exact fun e he => Set.ncard_eq_three.mpr (liftHG_isTripleSystem A κ e he)
    · exact lift_not_colorableBy A κ (GSn.not_colorableBy_regular hreg hκ) hκ
  refine ⟨hlin, ?_, ?_⟩
  · obtain ⟨b⟩ := bridgeSelector_of_embeds_lift hlin (embeds 0)
    exact fun ed => ⟨b.p ed, (b.isBridge ed).1, b.isBridge ed⟩
  · intro c
    rcases Nat.even_or_odd c.m with heven | hodd
    · exact heven
    · have hm : 3 ≤ c.m := by obtain ⟨j, hj⟩ := hodd; have := c.hm; omega
      have hn := GSn.noShortOddCycle_n (κ := κ) (n := c.m) c.m hodd hm (by omega)
      exact (lift_omits_of_bergeCycle hlin c hn (embeds c.m)).elim

/-- The classification on the project's own hypergraphs, with the answer written out. -/
theorem obligatory_iff_intrinsic {n : ℕ} (F : UniformHypergraph (Fin n) 3) :
    F.IsObligatory ↔ (finiteSystem F).reduce.IntrinsicObligatory := by
  rw [obligatory_iff, FTS.obligatory_reduce_iff]
  refine ⟨intrinsic_of_obligatory, fun hF => ?_⟩
  apply bclass_obligatory (reiherExpansion_of_E4 e4_Reiher)
  apply bclass_of_reconOK
  exact ⟨hF.1, FTS.reduce_no_isolated _, hF.2⟩

end TripleSystem593

/-- The finite test uses edge intersections, incidence bridges, and Berge-cycle parity. -/
noncomputable def OMA.answer : Set ((n : ℕ) × UniformHypergraph (Fin n) 3) :=
  {p | (TripleSystem593.finiteSystem p.2).reduce.IntrinsicObligatory}

theorem OMA.solution : Erdos593.erdos_593.answer = OMA.answer → type_of% @Erdos593.erdos_593 := by
  intro h
  rw [h]
  ext p
  exact TripleSystem593.obligatory_iff_intrinsic p.2

/-
Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
-/
