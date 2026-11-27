import FormalConjectures.ErdosProblems.«595»

/- Erdős–Hajnal Problem 595, also 1174(i). Credit: @TheWaler.
A triangle-Ramsey host may have four-cliques if a countable sequence of
continuum-codegree-bounded layers hits all of them. The layer condition is
internal to a layer. Deleting their edges recovers a K4-free Ramsey graph.
Harary, Hsu and Miller, The biparticity of a graph (1977), is a finite
precedent for binary cut covers, doi:10.1002/jgt.3190010208.
Shelah, Consistency of positive partition theorems for graphs and models (1989),
Lemma 5.1, gives a relative consistency result. See Komjáth, The Erdős–Hajnal
problem list (2025), Problem 53. The construction hypothesis remains open. -/
namespace OMA.R_Erdos595_erdos_595_R1
open SimpleGraph
variable {V : Type*}

universe u
open Relation SimpleGraph

theorem lts595_small_reach {X : Type*} (r : X → X → Prop)
    (h : ∀ x, Nonempty ({y : X | r x y} ↪ (ℕ → Bool))) (x : X) :
    Nonempty ({y : X | Relation.ReflTransGen r x y} ↪ (ℕ → Bool)) := by
  classical
  let C := ℕ → Bool
  let enc (a : X) : {y // r a y} ↪ C := (h a).some
  let step (a : X) (c : C) : X :=
    if e : ∃ z : {y // r a y}, enc a z = c then e.choose.val else a
  have follows {a b : X} (e : r a b) : step a (enc a ⟨b,e⟩) = b := by
    have hit : ∃ z : {y // r a y}, enc a z = enc a ⟨b,e⟩ := ⟨⟨b,e⟩,rfl⟩
    unfold step
    rw [dif_pos hit]
    exact congrArg Subtype.val ((enc a).injective hit.choose_spec)
  have reach {y : X} (hy : Relation.ReflTransGen r x y) :
      ∃ w : List C, w.foldl step x = y := by
    induction hy with
    | refl => exact ⟨[],rfl⟩
    | @tail b c _ e ih =>
      obtain ⟨w,hw⟩ := ih
      exact ⟨w ++ [enc b ⟨c,e⟩], by simpa [List.foldl_append, hw] using follows e⟩
  let path (y : {y // Relation.ReflTransGen r x y}) := (reach y.2).choose
  have inj : Function.Injective path := by
    intro y z hyz
    apply Subtype.ext
    calc
      (y:X) = (path y).foldl step x := (reach y.2).choose_spec.symm
      _ = (path z).foldl step x := congrArg (fun w : List C => w.foldl step x) hyz
      _ = (z:X) := (reach z.2).choose_spec
  have : Infinite C := by dsimp [C]; infer_instance
  obtain ⟨eqv⟩ := Cardinal.eq.mp (Cardinal.mk_list_eq_mk C)
  exact ⟨(Function.Embedding.mk path inj).trans eqv.toEmbedding⟩

/-- Binary coordinate cuts cover every edge whose endpoints have distinct codes. The
finite counterpart is the bipartite edge-cover construction of Harary, Hsu and Miller. -/
theorem lts595_code_cuts {V : Type*} (G : SimpleGraph V) (c : V → ℕ → Bool)
    (proper : ∀ {v w}, G.Adj v w → c v ≠ c w) : Erdos595.IsCountableUnionOfTriangleFree G := by
  let bitCut (G : SimpleGraph V) (c : V → ℕ → Bool) (i : ℕ) : SimpleGraph V := {
    Adj v w := G.Adj v w ∧ c v i ≠ c w i
    symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
    loopless := ⟨fun _ h => h.2 rfl⟩ }

  let bitCutColoring (G : SimpleGraph V) (c : V → ℕ → Bool) (i : ℕ) :
      (bitCut G c i).Coloring Bool :=
    SimpleGraph.Coloring.mk (fun v => c v i) fun h => h.2

  have bitCut_cliqueFree (G : SimpleGraph V) (c : V → ℕ → Bool) (i : ℕ) :
      (bitCut G c i).CliqueFree 3 :=
    (bitCutColoring G c i).colorable.cliqueFree (by decide)

  have iSup_bitCut (G : SimpleGraph V) (c : V → ℕ → Bool)
      (proper : ∀ {v w}, G.Adj v w → c v ≠ c w) : G = ⨆ i, bitCut G c i := by
    ext v w
    rw [SimpleGraph.iSup_adj]
    constructor
    · intro h
      obtain ⟨i, hi⟩ : ∃ i, c v i ≠ c w i := by
        by_contra! e
        exact proper h (funext e)
      exact ⟨i, h, hi⟩
    · rintro ⟨i, h, _⟩
      exact h
  exact ⟨bitCut G c, bitCut_cliqueFree G c, iSup_bitCut G c proper⟩

set_option maxHeartbeats 1600000 in
/-- A codable common neighbourhood at every edge gives a countable triangle-free cover. -/
theorem lts595_low_codebook_cover {V : Type u} (G : SimpleGraph V)
    (low : ∀ a b, G.Adj a b → Nonempty ({w : V | G.Adj a w ∧ G.Adj b w} ↪ (ℕ → Bool))) :
    Erdos595.IsCountableUnionOfTriangleFree G := by
  classical
  let Codes := ℕ → Bool
  let SmallSet {X : Type u} (s : Set X) := Nonempty (s ↪ Codes)

  let Step (G : SimpleGraph V) (e f : V × V) : Prop :=
    f = e.swap ∨ f.1 = e.1 ∧ G.Adj e.1 e.2 ∧ G.Adj e.1 f.2 ∧ G.Adj e.2 f.2

  have step_symm {G : SimpleGraph V} {e f : V × V} (h : Step G e f) : Step G f e := by
    rcases h with he | ⟨h₁,h₂,h₃,h₄⟩
    · left; simp [he]
    · right; exact ⟨h₁.symm, h₁ ▸ h₃, h₁ ▸ h₂, h₄.symm⟩

  let componentSetoid (G : SimpleGraph V) : Setoid (V × V) := {
    r := ReflTransGen (Step G)
    iseqv := ⟨fun _ => .refl, fun h => by
      induction h with
      | refl => exact .refl
      | tail _ h ih => exact (ReflTransGen.single (step_symm h)).trans ih,
      fun h h' => h.trans h'⟩ }

  let Component (G : SimpleGraph V) := Quotient (componentSetoid G)

  let tag (G : SimpleGraph V) (a b : V) : Component G := Quotient.mk _ (a,b)

  have tag_symm (G : SimpleGraph V) (a b : V) : tag G a b = tag G b a :=
    Quotient.sound (ReflTransGen.single (show Step G (a,b) (b,a) from Or.inl rfl))

  have tag_triangle {G : SimpleGraph V} {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c)
      (hca : G.Adj c a) : tag G a b = tag G b c := by
    apply (tag_symm G a b).trans
    exact Quotient.sound (ReflTransGen.single (show Step G (b,a) (b,c) from
      Or.inr ⟨rfl,hab.symm,hbc,hca.symm⟩))

  let pack (k : Option Codes) : Codes := fun
    | 0 => k.isSome
    | n+1 => match k with | none => false | some f => f n

  have pack_inj : Function.Injective pack := by
    intro a b h
    cases a <;> cases b
    · rfl
    · have := congrFun h 0; contradiction
    · have := congrFun h 0; contradiction
    · congr 1; funext i; exact congrFun h (i+1)

  have small_step {G : SimpleGraph V} (low : ∀ a b, G.Adj a b →
      SmallSet {w | G.Adj a w ∧ G.Adj b w}) (e : V × V) : SmallSet {f | Step G e f} := by
    classical
    let key (f : {f | Step G e f}) : Option Codes :=
      if h : f.val = e.swap then none else
      let hf := f.property.resolve_left h
      some ((low e.1 e.2 hf.2.1).some ⟨f.val.2,hf.2.2⟩)
    refine ⟨⟨fun f => pack (key f), fun a b h => ?_⟩⟩
    have eq := pack_inj h
    by_cases ha : a.val = e.swap <;> by_cases hb : b.val = e.swap
    · exact Subtype.ext (ha.trans hb.symm)
    · simp [key,ha,hb] at eq
    · simp [key,ha,hb] at eq
    · simp only [key, dif_neg ha, dif_neg hb, Option.some.injEq] at eq
      obtain ⟨a₁,a₂,a₃⟩ := a.property.resolve_left ha
      obtain ⟨b₁,b₂,b₃⟩ := b.property.resolve_left hb
      have val := (low e.1 e.2 a₂).some.injective eq
      apply Subtype.ext; exact Prod.ext (a₁.trans b₁.symm) (congrArg Subtype.val val)

  have component_codes (G : SimpleGraph V)
      (small : ∀ e, SmallSet {f | ReflTransGen (Step G) e f}) (q : Component G) :
      ∃ c : V → Codes, ∀ {v w}, G.Adj v w → tag G v w = q → c v ≠ c w := by
    classical
    induction q using Quotient.ind with | _ root =>
    let S (v : V) := ∃ w, tag G v w = Quotient.mk (componentSetoid G) root
    let lift (v : V) (h : S v) : {f | ReflTransGen (Step G) root f} :=
      ⟨(v, h.choose), Quotient.exact h.choose_spec.symm⟩
    let E := (small root).some
    let code (v : V) := if h : S v then E (lift v h) else fun _ => false
    refine ⟨code, ?_⟩
    intro v w adjacent hq hcodes
    have hv : S v := ⟨w,hq⟩
    have hw : S w := ⟨v,(tag_symm G w v).trans hq⟩
    simp only [code,dif_pos hv,dif_pos hw] at hcodes
    have eq := congrArg (fun x : {f | ReflTransGen (Step G) root f} => x.val.1) (E.injective hcodes)
    exact adjacent.ne eq
  let Q := Component G
  let part (G : SimpleGraph V) (tagQ : V → V → Q) (sym : ∀ a b, tagQ a b = tagQ b a)
      (q : Q) : SimpleGraph V := {
    Adj a b := G.Adj a b ∧ tagQ a b = q
    symm := ⟨fun a b h => ⟨h.1.symm, (sym a b).symm.trans h.2⟩⟩
    loopless := ⟨fun a h => G.loopless.irrefl a h.1⟩ }

  have cover_of_parts (G : SimpleGraph V) (tagQ : V → V → Q)
      (sym : ∀ a b, tagQ a b = tagQ b a)
      (tri : ∀ {a b c}, G.Adj a b → G.Adj b c → G.Adj c a → tagQ a b = tagQ b c)
      (covered : ∀ q, Erdos595.IsCountableUnionOfTriangleFree (part G tagQ sym q)) : Erdos595.IsCountableUnionOfTriangleFree G := by
    classical
    choose H hfree heq using covered
    have incl (q : Q) (n : ℕ) : H q n ≤ part G tagQ sym q := by
      rw [heq q]
      exact le_iSup (H q) n
    let K (n : ℕ) : SimpleGraph V := ⨆ q, H q n
    refine ⟨K,?_,?_⟩
    · intro n S h
      obtain ⟨a,b,c,hab,hac,hbc,_⟩ := is3Clique_iff.mp h
      obtain ⟨r,hr⟩ := iSup_adj.mp hab
      obtain ⟨s,hs⟩ := iSup_adj.mp hac
      obtain ⟨t,ht⟩ := iSup_adj.mp hbc
      obtain ⟨G_ab,T_ab⟩ := incl r n hr
      obtain ⟨G_ac,T_ac⟩ := incl s n hs
      obtain ⟨G_bc,T_bc⟩ := incl t n ht
      have rt : r=t := T_ab.symm.trans ((tri G_ab G_bc G_ac.symm).trans T_bc)
      have st : s=t := T_ac.symm.trans ((sym a c).trans
        ((tri G_bc G_ac.symm G_ab).symm.trans T_bc))
      rw [rt] at hr
      rw [st] at hs
      exact hfree t n {a,b,c} (is3Clique_triple_iff.mpr ⟨hr,hs,ht⟩)
    · ext a b
      constructor
      · intro hab
        have Hpart : (part G tagQ sym (tagQ a b)).Adj a b := ⟨hab,rfl⟩
        rw [heq (tagQ a b)] at Hpart
        obtain ⟨n,hn⟩ := iSup_adj.mp Hpart
        exact iSup_adj.mpr ⟨n,iSup_adj.mpr ⟨tagQ a b,hn⟩⟩
      · intro hab
        obtain ⟨n,hn⟩ := iSup_adj.mp hab
        obtain ⟨q,hq⟩ := iSup_adj.mp hn
        exact (incl q n hq).1
  apply cover_of_parts G (tag G) (tag_symm G) (fun h₁ h₂ h₃ => tag_triangle h₁ h₂ h₃)
  intro q
  obtain ⟨f,h⟩ := component_codes G (lts595_small_reach _ (small_step low)) q
  exact lts595_code_cuts _ f fun e => h e.1 e.2

private theorem cover_mono {H G : SimpleGraph V} (h : H ≤ G) (c : Erdos595.IsCountableUnionOfTriangleFree G) : Erdos595.IsCountableUnionOfTriangleFree H := by
  obtain ⟨f, hf, rfl⟩ := c
  refine ⟨fun n => H ⊓ f n, fun n => (hf n).anti inf_le_right, ?_⟩
  ext x y
  simp only [iSup_adj, inf_adj]
  constructor
  · intro hy
    obtain ⟨n, hn⟩ := iSup_adj.mp (h hy)
    exact ⟨n, hy, hn⟩
  · rintro ⟨_, hy, _⟩
    exact hy

private theorem cover_iSup {ι : Type*} [Countable ι] (F : ι → SimpleGraph V)
    (h : ∀ i, Erdos595.IsCountableUnionOfTriangleFree (F i)) : Erdos595.IsCountableUnionOfTriangleFree (⨆ i, F i) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hempty =>
    let := hempty
    refine ⟨fun _ => ⊥, fun _ => cliqueFree_bot (by decide : 2 ≤ 3), ?_⟩
    simp
  | inr hnonempty =>
    let := hnonempty
    obtain ⟨get, onto⟩ := exists_surjective_nat (ι × ℕ)
    choose f hf heq using h
    refine ⟨fun n => f (get n).1 (get n).2, fun n => hf _ _, ?_⟩
    apply le_antisymm
    · apply iSup_le
      intro i
      rw [heq i]
      apply iSup_le
      intro k
      obtain ⟨n, hn⟩ := onto (i,k)
      exact (by simpa only [hn] using le_iSup (fun n => f (get n).1 (get n).2) n)
    · apply iSup_le
      intro n
      exact le_trans (le_iSup (f _) _) (by rw [← heq]; exact le_iSup F _)

private theorem cover_sup {A B : SimpleGraph V} (ha : Erdos595.IsCountableUnionOfTriangleFree A) (hb : Erdos595.IsCountableUnionOfTriangleFree B) : Erdos595.IsCountableUnionOfTriangleFree (A ⊔ B) := by
  have h := cover_iSup (fun b : Bool => cond b A B) (fun b => by cases b <;> assumption)
  simpa [iSup_bool_eq, sup_comm] using h

private theorem cover_iff_sdiff {G L : SimpleGraph V} (hL : Erdos595.IsCountableUnionOfTriangleFree L) : Erdos595.IsCountableUnionOfTriangleFree G ↔ Erdos595.IsCountableUnionOfTriangleFree (G \ L) := by
  constructor
  · exact cover_mono sdiff_le
  · intro h
    apply cover_mono (G := (G \ L) ⊔ L) _ (cover_sup h hL)
    intro x y hxy
    by_cases hl : L.Adj x y
    · exact Or.inr hl
    · exact Or.inl ⟨hxy,hl⟩

/-- A universe lift preserves clique-freeness and failure of a countable cover. -/
private theorem lift_witness {V : Type} [Infinite V] (G : SimpleGraph V) (h4 : G.CliqueFree 4)
    (bad : ¬ Erdos595.IsCountableUnionOfTriangleFree G) :
    ∃ (W : Type u) (_ : Infinite W) (J : SimpleGraph W),
      J.CliqueFree 4 ∧ ¬ Erdos595.IsCountableUnionOfTriangleFree J := by
  let down : ULift.{u} V ↪ V := Equiv.ulift.toEmbedding
  let incl : V ↪ ULift.{u} V := Equiv.ulift.symm.toEmbedding
  refine ⟨ULift.{u} V, inferInstance, G.comap down,
    h4.comap (SimpleGraph.Embedding.comap down G).isContained, ?_⟩
  rintro ⟨H, hfree, heq⟩
  apply bad
  refine ⟨fun i => (H i).comap incl,
    fun i => (hfree i).comap (SimpleGraph.Embedding.comap incl (H i)).isContained, ?_⟩
  ext a b
  rw [SimpleGraph.iSup_adj]
  change G.Adj a b ↔ ∃ i, (H i).Adj (incl a) (incl b)
  rw [← SimpleGraph.iSup_adj, ← heq]; rfl


/-- In any graph, countable-colour Ramsey for a triangle forces a monochromatic
book with strictly more than continuum many pages in some colour. -/
theorem ramsey_iff_large_book {W : Type*} (G : SimpleGraph W) :
    ¬ Erdos595.IsCountableUnionOfTriangleFree G ↔ ∀ c : G.EdgeLabeling ℕ,
      ∃ n a b, (c.labelGraph n).Adj a b ∧ ¬ Nonempty
        ({w : W | (c.labelGraph n).Adj a w ∧ (c.labelGraph n).Adj b w} ↪ (ℕ → Bool)) := by
  classical
  let large (F : SimpleGraph W) : Prop := ∃ a b, F.Adj a b ∧ ¬ Nonempty
    ({w : W | F.Adj a w ∧ F.Adj b w} ↪ (ℕ → Bool))
  change _ ↔ ∀ c : G.EdgeLabeling ℕ, ∃ n, large (c.labelGraph n)
  constructor
  · intro bad c
    by_contra! no_book
    apply bad
    rw [← c.iSup_labelGraph]
    apply cover_iSup
    intro n
    apply lts595_low_codebook_cover
    intro a b adj
    by_contra big
    exact no_book n ⟨a,b,adj,big⟩
  · intro arrow hc
    obtain ⟨c,free⟩ := (Erdos595.erdos_595.variants.reformulation_edge_colouring G).mp hc
    let d : G.EdgeLabeling ℕ := c
    obtain ⟨n,a,b,ab,big⟩ := arrow d
    apply big
    have empty (x : {w : W | (d.labelGraph n).Adj a w ∧ (d.labelGraph n).Adj b w}) : False :=
      free n {a,b,x.val} (is3Clique_triple_iff.mpr ⟨ab,x.property.1,x.property.2⟩)
    exact ⟨⟨fun x => (empty x).elim, fun x => (empty x).elim⟩⟩

/-- Every graph of continuum-bounded edge codegree admits a countable cover by
triangle-free graphs. -/
def H1 : Prop := ∀ (V : Type) (G : SimpleGraph V),
  (∀ a b, G.Adj a b → Nonempty ({w : V | G.Adj a w ∧ G.Adj b w} ↪ (ℕ → Bool))) →
  Erdos595.IsCountableUnionOfTriangleFree G

/-- Construct an infinite triangle-Ramsey host. It may contain four-cliques,
provided that a countable list of continuum-codegree-bounded edge layers hits
all of them. The common neighbours are measured inside each individual layer. -/
def H2 : Prop := ∃ (V : Type) (_ : Infinite V) (X : SimpleGraph V),
  (∀ c : X.EdgeLabeling ℕ, ∃ n, ¬ (c.labelGraph n).CliqueFree 3) ∧
  ∃ F : ℕ → SimpleGraph V,
    (∀ n a b, (F n).Adj a b → Nonempty ({w : V | (F n).Adj a w ∧ (F n).Adj b w} ↪ (ℕ → Bool))) ∧
    ∀ s : Finset V, X.IsNClique 4 s → ∃ n, ∃ a ∈ s, ∃ b ∈ s, (F n).Adj a b

theorem main : H1 → H2 → type_of% @Erdos595.erdos_595 := by
  intro bounded host
  obtain ⟨V,hV,X,ramsey,F,layers,hit⟩ := host
  let D := ⨆ n,F n
  let : Infinite V := hV
  apply lift_witness (X \ D)
  · intro s hs
    obtain ⟨n,a,ha,b,hb,edge⟩ := hit s (hs.mono sdiff_le)
    exact (hs.isClique ha hb edge.ne).2 (iSup_adj.mpr ⟨n,edge⟩)
  · intro repaired
    have all : Erdos595.IsCountableUnionOfTriangleFree D := cover_iSup F (fun n => bounded V (F n) (layers n))
    have ambient := (cover_iff_sdiff (G := X) all).mpr repaired
    obtain ⟨c,free⟩ := (Erdos595.erdos_595.variants.reformulation_edge_colouring X).mp ambient
    obtain ⟨n,mono⟩ := ramsey c
    exact mono (free n)

/-- The first step is proved unconditionally by the triangle-component and binary-cut argument. -/
theorem bounded_step : H1 := fun _ G h => lts595_low_codebook_cover G h

end OMA.R_Erdos595_erdos_595_R1
