import OMAReductions.R_Erdos601_erdos_601_variants_erdos_hajnal_milner_1970_R1

/-!
# Proof of `Erdos601.erdos_601.variants.erdos_hajnal_milner_1970.R1.H3`

We prove that for every nonzero ordinal `γ` and countable limit ordinal `β < ω_ 1`, if
`HasPathOrIndepSetOfType (ω_ 1 * γ)` and `HasPathOrIndepSetOfType β` hold, then
`HasPathOrIndepSetOfType (ω_ 1 * γ + β)` holds.

Proof outline:
1. **Schmidt's rank decomposition (`HasRank`)**, **ordinal union & Cantor normal form lemmas**,
   and **pruned-tree BFS partition** (reused from the countable limit ordinal proof): yields
   `pruned_bfs_disjoint_split`, which splits any color-light countable block of type `ω ^ ξ`
   into `m` pairwise disjoint color classes each retaining order type `ω ^ ξ`.
2. **Rayless bipartite decoupling (`rayless_bipartite_decouple`)**: by induction on `HasRank G`,
   for any well-ordered `WL` of limit type `α` and `WR` of countable type `ω ^ ξ` (`1 ≤ ξ < ω_ 1`),
   there exist `IL ⊆ WL` (type `α`) and `IR ⊆ WR` (type `ω ^ ξ`) with no edges between them.
   - If some component `c₀` of `G - S` is heavy in `WR`, recurse on `c₀` for the left CNF blocks
     whose complement outside `c₀` drops in order type, and glue using `cnf_sum_rigid`.
   - If `WR` is component-light, apply `pruned_bfs_disjoint_split` with `m = L.length + 1` and
     pick a color class `D t₀` by pigeonhole so every left CNF block retains full order type
     outside `D t₀`.
3. **Cantor normal form iteration**: decompose `β = ∑ ω ^ ξ_j` (`1 ≤ ξ_j < ω_ 1`) and iterate
   `rayless_bipartite_decouple` to find `IL` of type `ω_ 1 * γ` and `IR` of type `β` with no
   edges between them, then apply the two hypotheses and take the union of the independent sets.
-/

-- Credit: @skhakim

namespace OMA.P_Erdos601_erdos_601_variants_erdos_hajnal_milner_1970_R1_H3

open Ordinal Cardinal SimpleGraph Erdos601
open scoped Classical

/- ### Part 1: Schmidt's rank theorem for rayless graphs -/

/-- A graph has an infinite path (ray). -/
private def HasInfPath {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ f : ℕ → V, Function.Injective f ∧ ∀ n, G.Adj (f n) (f (n + 1))

/-- Schmidt's inductive rank predicate for rayless graphs. -/
private inductive HasRank : ∀ {V : Type}, SimpleGraph V → Prop
  | finite {V : Type} (G : SimpleGraph V) (hfin : Finite V) : HasRank G
  | sep {V : Type} (G : SimpleGraph V) (S : Finset V)
      (hcomp : ∀ c : (G.induce {v : V | v ∉ S}).ConnectedComponent,
        HasRank (G.induce {v : V | ∃ hv : v ∉ S,
          (G.induce {w : V | w ∉ S}).connectedComponentMk ⟨v, hv⟩ = c})) :
      HasRank G

/-- `HasRank` is preserved under graph embeddings. -/
private lemma hasRank_of_emb {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : HasRank G) (e : H ↪g G) : HasRank H := by
  induction hG generalizing W with
  | finite G hfin =>
    exact HasRank.finite H (Finite.of_injective e e.injective)
  | sep G S hcomp ih =>
    let S' : Finset W := S.preimage e (fun x _ y _ h ↦ e.injective h)
    refine HasRank.sep H S' fun c ↦ ?_
    obtain ⟨⟨w0, hw0⟩, hc⟩ := c.exists_rep
    have hw0S : e w0 ∉ S := fun h ↦ hw0 (Finset.mem_preimage.mpr h)
    let cG : (G.induce {v | v ∉ S}).ConnectedComponent :=
      (G.induce {v | v ∉ S}).connectedComponentMk ⟨e w0, hw0S⟩
    refine ih cG (H := H.induce {w : W | ∃ hw : w ∉ S',
      (H.induce {u : W | u ∉ S'}).connectedComponentMk ⟨w, hw⟩ = c}) ?_
    refine ⟨⟨fun x ↦ ⟨e x.1, ?_⟩, ?_⟩, ?_⟩
    · obtain ⟨hw, hcw⟩ := x.2
      have hwS : e x.1 ∉ S := fun h ↦ hw (Finset.mem_preimage.mpr h)
      refine ⟨hwS, ?_⟩
      have hreachH : (H.induce {u : W | u ∉ S'}).Reachable ⟨x.1, hw⟩ ⟨w0, hw0⟩ :=
        SimpleGraph.ConnectedComponent.exact (hcw.trans hc.symm)
      obtain ⟨walk⟩ := hreachH
      let hom : (H.induce {u : W | u ∉ S'}) →g (G.induce {v | v ∉ S}) :=
        ⟨fun u ↦ ⟨e u.1, fun h ↦ u.2 (Finset.mem_preimage.mpr h)⟩,
         fun {a b} hab ↦ e.map_rel_iff.mpr hab⟩
      have hmap : (G.induce {v | v ∉ S}).Reachable ⟨e x.1, hwS⟩ ⟨e w0, hw0S⟩ :=
        ⟨walk.map hom⟩
      exact SimpleGraph.ConnectedComponent.sound hmap
    · intro x1 x2 h
      exact Subtype.ext (e.injective (congrArg Subtype.val h))
    · intro x1 x2
      exact e.map_rel_iff

/-- `HasRank` is hereditary on induced subgraphs. -/
private lemma hasRank_induce {V : Type} {G : SimpleGraph V} (hG : HasRank G) (U : Set V) :
    HasRank (G.induce U) :=
  hasRank_of_emb hG (SimpleGraph.Embedding.induce U)

/-- Every rayless graph satisfies `HasRank`. -/
private lemma rayless_hasRank {V : Type} (G : SimpleGraph V) (hray : ¬ HasInfPath G) :
    HasRank G := by
  by_contra hnot
  have hstep : ∀ (U : Set V), ¬ HasRank (G.induce U) → ∀ S : Finset V,
      ∃ C : Set V, C ⊆ U ∧ (∀ x ∈ C, x ∉ S) ∧
        (∀ x ∈ C, ∀ y ∈ U, y ∉ S → G.Adj x y → y ∈ C) ∧
        (G.induce C).Connected ∧ ¬ HasRank (G.induce C) := by
    intro U hU S
    let SU : Finset U := S.preimage Subtype.val (fun _ _ _ _ h ↦ Subtype.ext h)
    by_contra hall
    push Not at hall
    apply hU
    refine HasRank.sep (G.induce U) SU fun c ↦ ?_
    let C : Set V := {v : V | ∃ hvU : v ∈ U, ∃ hvS : (⟨v, hvU⟩ : U) ∉ SU,
      ((G.induce U).induce {u : U | u ∉ SU}).connectedComponentMk ⟨⟨v, hvU⟩, hvS⟩ = c}
    have hCU : C ⊆ U := fun _ h ↦ h.1
    have hCS : ∀ x ∈ C, x ∉ S := fun x ⟨_, hxS, _⟩ hmem ↦
      hxS (Finset.mem_preimage.mpr hmem)
    have hCmax : ∀ x ∈ C, ∀ y ∈ U, y ∉ S → G.Adj x y → y ∈ C := by
      intro x ⟨hxU, hxS, hcx⟩ y hyU hyS hxy
      have hySU : (⟨y, hyU⟩ : U) ∉ SU := fun h ↦ hyS (Finset.mem_preimage.mp h)
      refine ⟨hyU, hySU, ?_⟩
      have hadj : ((G.induce U).induce {u : U | u ∉ SU}).Adj ⟨⟨x, hxU⟩, hxS⟩ ⟨⟨y, hyU⟩, hySU⟩ := hxy
      exact (SimpleGraph.ConnectedComponent.sound hadj.reachable).symm.trans hcx
    have hCconn : (G.induce C).Connected := by
      obtain ⟨⟨⟨v0, hv0U⟩, hv0S⟩, hc0⟩ := c.exists_rep
      have : Nonempty C := ⟨⟨v0, hv0U, hv0S, hc0⟩⟩
      refine SimpleGraph.Connected.mk fun ⟨x, hxU, hxS, hcx⟩ ⟨y, hyU, hyS, hcy⟩ ↦ ?_
      have hreach : ((G.induce U).induce {u : U | u ∉ SU}).Reachable ⟨⟨x, hxU⟩, hxS⟩ ⟨⟨y, hyU⟩, hyS⟩ :=
        SimpleGraph.ConnectedComponent.exact (hcx.trans hcy.symm)
      obtain ⟨w⟩ := hreach
      have hmem_all : ∀ z ∈ w.support, z.1.1 ∈ C := by
        intro z hz
        have hrz : ((G.induce U).induce {u : U | u ∉ SU}).Reachable ⟨⟨x, hxU⟩, hxS⟩ z :=
          ⟨w.takeUntil z hz⟩
        exact ⟨z.1.2, z.2, (SimpleGraph.ConnectedComponent.sound hrz).symm.trans hcx⟩
      have hwalk_reach : ∀ {a b : {u : U | u ∉ SU}}
          (w' : ((G.induce U).induce {u : U | u ∉ SU}).Walk a b)
          (haC : a.1.1 ∈ C) (hbC : b.1.1 ∈ C),
          (∀ z ∈ w'.support, z.1.1 ∈ C) →
          (G.induce C).Reachable ⟨a.1.1, haC⟩ ⟨b.1.1, hbC⟩ := by
        intro a b w'
        induction w' with
        | nil => intro haC hbC _; exact SimpleGraph.Reachable.refl _
        | @cons a b d hab rest ih =>
          intro haC hdC hall_w
          have hbC : b.1.1 ∈ C := hall_w b (List.mem_cons_of_mem a rest.start_mem_support)
          have hadjC : (G.induce C).Adj ⟨a.1.1, haC⟩ ⟨b.1.1, hbC⟩ := hab
          exact hadjC.reachable.trans (ih hbC hdC (fun z hz ↦ hall_w z (List.mem_cons_of_mem a hz)))
      exact hwalk_reach w ⟨hxU, hxS, hcx⟩ ⟨hyU, hyS, hcy⟩ hmem_all
    have hCrank : HasRank (G.induce C) := hall C hCU hCS hCmax hCconn
    refine hasRank_of_emb hCrank ⟨⟨fun x ↦ ⟨x.1.1, x.1.2, x.2.1, x.2.2⟩, ?_⟩, ?_⟩
    · intro x1 x2 h
      exact Subtype.ext (Subtype.ext (congrArg (fun z : C ↦ z.1) h))
    · intro x1 x2
      rfl
  have htop : ¬ HasRank (G.induce Set.univ) := fun h ↦
    hnot (hasRank_of_emb h ⟨⟨fun v ↦ ⟨v, trivial⟩, fun _ _ h ↦ congrArg Subtype.val h⟩, fun {_ _} ↦ Iff.rfl⟩)
  obtain ⟨H0, _, _, _, hH0_conn, hH0_unrank⟩ := hstep Set.univ htop ∅
  obtain ⟨⟨v0, hv0⟩⟩ := hH0_conn.nonempty
  let State := {p : V × Set V // p.1 ∈ p.2 ∧ (G.induce p.2).Connected ∧ ¬ HasRank (G.induce p.2)}
  have hnext : ∀ p : State,
      ∃ q : State, q.1.2 ⊆ p.1.2 ∧ (∀ x ∈ q.1.2, x ≠ p.1.1) ∧ G.Adj p.1.1 q.1.1 := by
    rintro ⟨⟨v, H⟩, hvH, hHconn, hHunrank⟩
    obtain ⟨H', hH'sub, hH'notv, hH'max, hH'conn, hH'unrank⟩ := hstep H hHunrank {v}
    obtain ⟨⟨w, hwH'⟩⟩ := hH'conn.nonempty
    obtain ⟨walk⟩ := hHconn ⟨v, hvH⟩ ⟨w, hH'sub hwH'⟩
    have hex_adj : ∃ u ∈ H', G.Adj v u := by
      have hvnot : v ∉ H' := fun h ↦ hH'notv v h (Finset.mem_singleton_self v)
      have hwalk_cross : ∀ {a b : H} (p : (G.induce H).Walk a b),
          a.1 ∉ H' → b.1 ∈ H' → ∃ u ∈ H', G.Adj v u := by
        intro a b p
        induction p with
        | nil => intro ha hb; exact absurd hb ha
        | @cons x y z hxy rest ih =>
          intro hx hz
          by_cases hy : y.1 ∈ H'
          · by_cases hxv : x.1 = v
            · exact ⟨y.1, hy, hxv ▸ hxy⟩
            · exfalso
              exact hx (hH'max y.1 hy x.1 x.2 (by simp [hxv]) hxy.symm)
          · exact ih hy hz
      exact hwalk_cross walk hvnot hwH'
    obtain ⟨u, huH', hvu⟩ := hex_adj
    exact ⟨⟨⟨u, H'⟩, huH', hH'conn, hH'unrank⟩, hH'sub,
      fun x hx hxv ↦ hH'notv x hx (by simp [hxv]), hvu⟩
  choose step hsub hnotv hadj using hnext
  let seq : ℕ → State := Nat.rec ⟨⟨v0, H0⟩, hv0, hH0_conn, hH0_unrank⟩ (fun _ s ↦ step s)
  have hmono : ∀ {i j : ℕ}, i ≤ j → (seq j).1.2 ⊆ (seq i).1.2 := by
    intro i j hij
    induction hij with
    | refl => exact Set.Subset.rfl
    | @step k _ ih => exact (hsub (seq k)).trans ih
  have hlt_ne : ∀ {i j : ℕ}, i < j → (seq i).1.1 ≠ (seq j).1.1 := by
    intro i j hij heq
    have hmem : (seq j).1.1 ∈ (seq (i + 1)).1.2 := hmono hij (seq j).2.1
    exact hnotv (seq i) (seq j).1.1 hmem heq.symm
  apply hray
  refine ⟨fun n ↦ (seq n).1.1, ?_, fun n ↦ hadj (seq n)⟩
  intro i j hij
  rcases lt_trichotomy i j with h | rfl | h
  · exact absurd hij (hlt_ne h)
  · rfl
  · exact absurd hij.symm (hlt_ne h)

/- ### Part 2: Ordinal order-type, union, and Cantor normal form lemmas -/

/-- `typeLT` respects set equality. -/
private lemma typeLT_congr_set {V : Type} [LinearOrder V] [WellFoundedLT V] {A B : Set V}
    (h : A = B) : typeLT A = typeLT B := by
  subst h; rfl

/-- `typeLT` is invariant under order isomorphism. -/
private lemma typeLT_eq_of_orderIso {α β : Type} [LinearOrder α] [WellFoundedLT α]
    [LinearOrder β] [WellFoundedLT β] (e : α ≃o β) :
    typeLT α = typeLT β :=
  Ordinal.type_eq.mpr ⟨e.toRelIsoLT⟩

/-- Monotonicity of `typeLT` on subsets. -/
private lemma typeLT_mono {V : Type} [LinearOrder V] [WellFoundedLT V] {A B : Set V}
    (h : A ⊆ B) : typeLT A ≤ typeLT B := by
  let f : ((· < · : A → A → Prop) ↪r (· < · : B → B → Prop)) :=
    ⟨⟨fun x ↦ ⟨x.1, h x.2⟩, fun _ _ hx ↦ Subtype.ext (congrArg (fun z : B ↦ z.1) hx)⟩, Iff.rfl⟩
  exact Ordinal.type_le_iff'.mpr ⟨f⟩

/-- Order type of the empty set is `0`. -/
private lemma typeLT_empty {V : Type} [LinearOrder V] [WellFoundedLT V] :
    typeLT (∅ : Set V) = 0 := by
  rw [Ordinal.type_eq_zero_iff_isEmpty]
  exact ⟨fun ⟨_, h⟩ ↦ h⟩

/-- Order type of a singleton is `1`. -/
private lemma typeLT_singleton {V : Type} [LinearOrder V] [WellFoundedLT V] (x : V) :
    typeLT ({x} : Set V) = 1 := by
  have : Nonempty ({x} : Set V) := ⟨⟨x, rfl⟩⟩
  have : Subsingleton ({x} : Set V) := ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ ↦ Subtype.ext (ha.trans hb.symm)⟩
  exact Ordinal.type_eq_one_of_unique (· < ·)

/-- Order type of a subset `s` equals the sum of the order types of a downward-closed part and its
complement inside `s`. -/
private lemma typeLT_split_downward {V : Type} [LinearOrder V] [WellFoundedLT V]
    (s : Set V) (P : V → Prop) (hdown : ∀ x ∈ s, ∀ y ∈ s, P x → ¬ P y → x < y) :
    typeLT s = typeLT ({x ∈ s | P x} : Set V) + typeLT ({x ∈ s | ¬ P x} : Set V) := by
  let L := {x ∈ s | P x}
  let R := {x ∈ s | ¬ P x}
  let e : (Sum.Lex (· < · : L → L → Prop) (· < · : R → R → Prop) ≃r (· < · : s → s → Prop)) :=
    { toFun := fun u ↦ match u with
        | Sum.inl ⟨x, hx, _⟩ => ⟨x, hx⟩
        | Sum.inr ⟨y, hy, _⟩ => ⟨y, hy⟩
      invFun := fun ⟨x, hx⟩ ↦ if h : P x then Sum.inl ⟨x, hx, h⟩ else Sum.inr ⟨x, hx, h⟩
      left_inv := fun u ↦ by
        rcases u with ⟨x, hx, hP⟩ | ⟨y, hy, hnP⟩
        · simp only [hP, ↓reduceDIte]
        · simp only [hnP, ↓reduceDIte]
      right_inv := fun ⟨x, hx⟩ ↦ by
        by_cases hP : P x <;> simp [hP]
      map_rel_iff' := by
        intro u1 u2
        rcases u1 with ⟨x1, hx1, h1⟩ | ⟨x1, hx1, h1⟩ <;> rcases u2 with ⟨x2, hx2, h2⟩ | ⟨x2, hx2, h2⟩
        · simp only [Sum.lex_inl_inl]; exact Iff.rfl
        · constructor
          · intro _; exact Sum.Lex.sep _ _
          · intro _; exact hdown x1 hx1 x2 hx2 h1 h2
        · constructor
          · intro hlt
            exact absurd hlt (not_lt.mpr (le_of_lt (hdown x2 hx2 x1 hx1 h2 h1)))
          · intro hlex; cases hlex
        · simp only [Sum.lex_inr_inr]; exact Iff.rfl }
  have heq : typeLT s = Ordinal.type (Sum.Lex (· < · : L → L → Prop) (· < · : R → R → Prop)) :=
    (Ordinal.type_eq.mpr ⟨e⟩).symm
  rw [heq]
  exact Ordinal.type_sum_lex _ _

/-- Order type of two separated subsets `A < B` is `typeLT A + typeLT B`. -/
private lemma typeLT_union_of_lt {V : Type} [LinearOrder V] [WellFoundedLT V]
    {A B : Set V} (hAB : ∀ x ∈ A, ∀ y ∈ B, x < y) :
    typeLT (A ∪ B : Set V) = typeLT A + typeLT B := by
  have h := typeLT_split_downward (A ∪ B) (· ∈ A) (by
    intro x _ y hy hxA hyA
    have hyB : y ∈ B := hy.resolve_left hyA
    exact hAB x hxA y hyB)
  have h1 : ({x ∈ A ∪ B | x ∈ A} : Set V) = A := by ext x; simp
  have h2 : ({x ∈ A ∪ B | x ∉ A} : Set V) = B := by
    ext x; constructor
    · rintro ⟨hx, hnot⟩; exact hx.resolve_left hnot
    · intro hxB; refine ⟨Or.inr hxB, fun hxA ↦ lt_irrefl x (hAB x hxA x hxB)⟩
  rw [h1, h2] at h
  exact h

/-- If every proper initial segment `{x ∈ s | x < a}` of `s` has order type `< α`, then
`typeLT s ≤ α`. -/
private lemma typeLT_le_of_forall_Iio_lt {V : Type} [LinearOrder V] [WellFoundedLT V]
    {s : Set V} {α : Ordinal.{0}}
    (h : ∀ a ∈ s, typeLT ({x ∈ s | x < a} : Set V) < α) :
    typeLT s ≤ α := by
  by_contra hgt
  push Not at hgt
  let a : s := Ordinal.enum (· < · : s → s → Prop) ⟨α, hgt⟩
  have ha_lt : typeLT ({x ∈ s | x < a.1} : Set V) < α := h a.1 a.2
  have hiso : ({x ∈ s | x < a.1} : Set V) ≃o Set.Iio a :=
    { toFun := fun ⟨x, hx, hlt⟩ ↦ ⟨⟨x, hx⟩, hlt⟩
      invFun := fun ⟨⟨x, hx⟩, hlt⟩ ↦ ⟨x, hx, hlt⟩
      left_inv := fun ⟨_, _, _⟩ ↦ rfl
      right_inv := fun ⟨⟨_, _⟩, _⟩ ↦ rfl
      map_rel_iff' := by rintro ⟨_, _, _⟩ ⟨_, _, _⟩; exact Iff.rfl }
  have htype_eq : typeLT ({x ∈ s | x < a.1} : Set V) = α := by
    rw [typeLT_eq_of_orderIso hiso, Ordinal.type_Iio_lt]
    exact Ordinal.typein_enum (· < · : s → s → Prop) hgt
  exact lt_irrefl α (htype_eq ▸ ha_lt)

/-- If `typeLT s = α + β`, we can split `s` into a downward-closed subset `L` of type `α` and its
complement `R = s \ L` of type `β` with `∀ x ∈ L, ∀ y ∈ R, x < y`. -/
private lemma exists_split_of_typeLT_add {V : Type} [LinearOrder V] [WellFoundedLT V]
    {s : Set V} {α β : Ordinal.{0}} (hs : typeLT s = α + β) :
    ∃ L R : Set V, L ⊆ s ∧ R ⊆ s ∧ L ∪ R = s ∧ (∀ x ∈ L, ∀ y ∈ R, x < y) ∧
      typeLT L = α ∧ typeLT R = β := by
  have htype_eq : Ordinal.type (Sum.Lex (· < · : α.ToType → _ → Prop) (· < · : β.ToType → _ → Prop)) =
      typeLT s := by
    rw [Ordinal.type_sum_lex, Ordinal.type_toType, Ordinal.type_toType, hs]
  obtain ⟨e⟩ := Ordinal.type_eq.mp htype_eq
  let L : Set V := {x : V | ∃ a : α.ToType, (e (Sum.inl a)).1 = x}
  let R : Set V := {x : V | ∃ b : β.ToType, (e (Sum.inr b)).1 = x}
  refine ⟨L, R, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩; exact (e (Sum.inl a)).2
  · rintro _ ⟨b, rfl⟩; exact (e (Sum.inr b)).2
  · ext x; constructor
    · rintro (⟨a, rfl⟩ | ⟨b, rfl⟩)
      · exact (e (Sum.inl a)).2
      · exact (e (Sum.inr b)).2
    · intro hx
      rcases h : e.symm ⟨x, hx⟩ with a | b
      · left; refine ⟨a, ?_⟩
        have := congrArg e h; simp at this; exact congrArg Subtype.val this.symm
      · right; refine ⟨b, ?_⟩
        have := congrArg e h; simp at this; exact congrArg Subtype.val this.symm
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact e.map_rel_iff.mpr (Sum.Lex.sep a b)
  · have eL : ((· < · : α.ToType → _ → Prop) ≃r (· < · : L → _ → Prop)) :=
      { toFun := fun a ↦ ⟨(e (Sum.inl a)).1, a, rfl⟩
        invFun := fun ⟨x, h⟩ ↦ Classical.choose h
        left_inv := fun a ↦ by
          have hs := Classical.choose_spec (⟨a, rfl⟩ : ∃ a', (e (Sum.inl a')).1 = (e (Sum.inl a)).1)
          have hinj := e.injective (Subtype.ext hs)
          exact Sum.inl.inj hinj
        right_inv := fun ⟨x, h⟩ ↦ Subtype.ext (Classical.choose_spec h)
        map_rel_iff' := by
          intro a1 a2
          change (e (Sum.inl a1)).1 < (e (Sum.inl a2)).1 ↔ a1 < a2
          have := e.map_rel_iff (a := Sum.inl a1) (b := Sum.inl a2)
          simpa using this }
    rw [← Ordinal.type_eq.mpr ⟨eL⟩, Ordinal.type_toType]
  · have eR : ((· < · : β.ToType → _ → Prop) ≃r (· < · : R → _ → Prop)) :=
      { toFun := fun b ↦ ⟨(e (Sum.inr b)).1, b, rfl⟩
        invFun := fun ⟨x, h⟩ ↦ Classical.choose h
        left_inv := fun b ↦ by
          have hs := Classical.choose_spec (⟨b, rfl⟩ : ∃ b', (e (Sum.inr b')).1 = (e (Sum.inr b)).1)
          have hinj := e.injective (Subtype.ext hs)
          exact Sum.inr.inj hinj
        right_inv := fun ⟨x, h⟩ ↦ Subtype.ext (Classical.choose_spec h)
        map_rel_iff' := by
          intro b1 b2
          change (e (Sum.inr b1)).1 < (e (Sum.inr b2)).1 ↔ b1 < b2
          have := e.map_rel_iff (a := Sum.inr b1) (b := Sum.inr b2)
          simpa using this }
    rw [← Ordinal.type_eq.mpr ⟨eR⟩, Ordinal.type_toType]

/-- Key ordinal union theorem: if `typeLT A < ω ^ ξ` and `typeLT B < ω ^ ξ`, then
`typeLT (A ∪ B) < ω ^ ξ`. -/
private lemma typeLT_union_lt_omega0_opow :
    ∀ (ξ : Ordinal.{0}) {V : Type} [LinearOrder V] [WellFoundedLT V] {A B : Set V},
      typeLT A < ω ^ ξ → typeLT B < ω ^ ξ → typeLT (A ∪ B : Set V) < ω ^ ξ := by
  intro ξ
  induction ξ using Ordinal.limitRecOn with
  | zero =>
    intro V _ _ A B hA hB
    rw [Ordinal.opow_zero] at hA hB ⊢
    have hA0 : typeLT A = 0 := Order.lt_one_iff.mp hA
    have hB0 : typeLT B = 0 := Order.lt_one_iff.mp hB
    have hAe : A = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun x hx ↦
      (Ordinal.type_eq_zero_iff_isEmpty.mp hA0).false ⟨x, hx⟩
    have hBe : B = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun x hx ↦
      (Ordinal.type_eq_zero_iff_isEmpty.mp hB0).false ⟨x, hx⟩
    rw [hAe, hBe, Set.union_empty, typeLT_empty]
    exact zero_lt_one
  | add_one η ih =>
    intro V _ _ A B hA hB
    rw [Ordinal.opow_add_one] at hA hB ⊢
    -- Both typeLT A and typeLT B are < ω^η * ω, so bounded by ω^η * m and ω^η * n
    have hmul_lt : ∀ m : ℕ, ω ^ η * (m : Ordinal.{0}) < ω ^ η * ω := by
      intro m
      rw [← Ordinal.opow_add_one]
      induction m with
      | zero => simp only [Nat.cast_zero, mul_zero]; exact Ordinal.opow_pos (η + 1) Ordinal.omega0_pos
      | succ m ihm =>
        rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one]
        exact Ordinal.isPrincipal_add_omega0_opow (η + 1) ihm
          ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (Order.lt_succ η))
    have hAm : ∃ m : ℕ, typeLT A ≤ ω ^ η * m := by
      have hdiv : (typeLT A) / ω ^ η < ω := (Ordinal.lt_mul_iff_div_lt (Ordinal.opow_ne_zero η Ordinal.omega0_ne_zero)).mp hA
      obtain ⟨k, hk⟩ := Ordinal.lt_omega0.mp hdiv
      refine ⟨k + 1, ?_⟩
      have h1 : typeLT A < ω ^ η * ((typeLT A) / ω ^ η + 1) :=
        Ordinal.lt_mul_succ_div (typeLT A) (Ordinal.opow_ne_zero η Ordinal.omega0_ne_zero)
      rw [hk] at h1
      exact le_of_lt (by simpa [Nat.cast_add, Nat.cast_one] using h1)
    have hBn : ∃ n : ℕ, typeLT B ≤ ω ^ η * n := by
      have hdiv : (typeLT B) / ω ^ η < ω := (Ordinal.lt_mul_iff_div_lt (Ordinal.opow_ne_zero η Ordinal.omega0_ne_zero)).mp hB
      obtain ⟨k, hk⟩ := Ordinal.lt_omega0.mp hdiv
      refine ⟨k + 1, ?_⟩
      have h1 : typeLT B < ω ^ η * ((typeLT B) / ω ^ η + 1) :=
        Ordinal.lt_mul_succ_div (typeLT B) (Ordinal.opow_ne_zero η Ordinal.omega0_ne_zero)
      rw [hk] at h1
      exact le_of_lt (by simpa [Nat.cast_add, Nat.cast_one] using h1)
    obtain ⟨m, hm⟩ := hAm
    obtain ⟨n, hn⟩ := hBn
    -- Induction on m + n
    suffices hmn : ∀ (k : ℕ) (m n : ℕ), m + n = k →
        ∀ {A B : Set V}, typeLT A ≤ ω ^ η * m → typeLT B ≤ ω ^ η * n →
          typeLT (A ∪ B : Set V) < ω ^ η * ω by
      exact hmn (m + n) m n rfl hm hn
    intro k
    induction k with
    | zero =>
      intro m n hsum A B hm hn
      have hm0 : m = 0 := by omega
      have hn0 : n = 0 := by omega
      subst hm0; subst hn0
      simp only [Nat.cast_zero, mul_zero, nonpos_iff_eq_zero] at hm hn
      have hAe : A = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun x hx ↦
        (Ordinal.type_eq_zero_iff_isEmpty.mp hm).false ⟨x, hx⟩
      have hBe : B = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun x hx ↦
        (Ordinal.type_eq_zero_iff_isEmpty.mp hn).false ⟨x, hx⟩
      rw [hAe, hBe, Set.union_empty, typeLT_empty, ← Ordinal.opow_add_one]
      exact Ordinal.opow_pos (η + 1) Ordinal.omega0_pos
    | succ k ihk =>
      intro m n hsum A B hm hn
      by_cases hm0 : m = 0
      · subst hm0
        simp only [Nat.cast_zero, mul_zero, nonpos_iff_eq_zero] at hm
        have hAe : A = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun x hx ↦
          (Ordinal.type_eq_zero_iff_isEmpty.mp hm).false ⟨x, hx⟩
        rw [hAe, Set.empty_union]
        exact hn.trans_lt (hmul_lt n)
      · by_cases hn0 : n = 0
        · subst hn0
          simp only [Nat.cast_zero, mul_zero, nonpos_iff_eq_zero] at hn
          have hBe : B = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun x hx ↦
            (Ordinal.type_eq_zero_iff_isEmpty.mp hn).false ⟨x, hx⟩
          rw [hBe, Set.union_empty]
          exact hm.trans_lt (hmul_lt m)
        · -- Both m ≥ 1 and n ≥ 1. Let P x := typeLT (A ∩ Iio x) < ω^η ∧ typeLT (B ∩ Iio x) < ω^η.
          let P : V → Prop := fun x ↦
            typeLT ({a ∈ A | a < x} : Set V) < ω ^ η ∧ typeLT ({b ∈ B | b < x} : Set V) < ω ^ η
          have hP_down : ∀ x ∈ A ∪ B, ∀ y ∈ A ∪ B, P x → ¬ P y → x < y := by
            intro x _ y _ hPx hnPy
            by_contra hle; push Not at hle
            apply hnPy
            have hsubA : ({a ∈ A | a < y} : Set V) ⊆ {a ∈ A | a < x} :=
              fun z ⟨hzA, hzy⟩ ↦ ⟨hzA, hzy.trans_le hle⟩
            have hsubB : ({b ∈ B | b < y} : Set V) ⊆ {b ∈ B | b < x} :=
              fun z ⟨hzB, hzy⟩ ↦ ⟨hzB, hzy.trans_le hle⟩
            exact ⟨(typeLT_mono hsubA).trans_lt hPx.1, (typeLT_mono hsubB).trans_lt hPx.2⟩
          rw [typeLT_split_downward (A ∪ B) P hP_down]
          have hL_le : typeLT ({x ∈ A ∪ B | P x} : Set V) ≤ ω ^ η := by
            apply typeLT_le_of_forall_Iio_lt
            intro a ⟨_, hPa⟩
            have hsub : ({x ∈ {x ∈ A ∪ B | P x} | x < a} : Set V) ⊆
                ({x ∈ A | x < a} : Set V) ∪ ({x ∈ B | x < a} : Set V) := by
              intro x ⟨⟨hxAB, _⟩, hxa⟩
              rcases hxAB with hxA | hxB
              · exact Or.inl ⟨hxA, hxa⟩
              · exact Or.inr ⟨hxB, hxa⟩
            exact (typeLT_mono hsub).trans_lt (ih hPa.1 hPa.2)
          let R : Set V := {x ∈ A ∪ B | ¬ P x}
          have hR_lt : typeLT R < ω ^ η * ω := by
            by_cases hRe : R = ∅
            · rw [hRe, typeLT_empty, ← Ordinal.opow_add_one]
              exact Ordinal.opow_pos (η + 1) Ordinal.omega0_pos
            · have hRne : R.Nonempty := Set.nonempty_iff_ne_empty.mpr hRe
              let y0 : V := WellFounded.min (wellFounded_lt (α := V)) R hRne
              have hy0_mem : y0 ∈ R := WellFounded.min_mem _ R hRne
              have hy0_min : ∀ z ∈ R, y0 ≤ z := fun z hz ↦
                not_lt.mp (WellFounded.not_lt_min (wellFounded_lt (α := V)) R hz)
              have hR_sub : R ⊆ ({a ∈ A | y0 ≤ a} : Set V) ∪ ({b ∈ B | y0 ≤ b} : Set V) := by
                intro z hz
                rcases hz.1 with hzA | hzB
                · exact Or.inl ⟨hzA, hy0_min z hz⟩
                · exact Or.inr ⟨hzB, hy0_min z hz⟩
              have hnP0 : ¬ P y0 := hy0_mem.2
              dsimp only [P] at hnP0
              rw [not_and_or, not_lt, not_lt] at hnP0
              rcases hnP0 with hAge | hBge
              · -- typeLT {a ∈ A | a < y0} ≥ ω^η, so typeLT {a ∈ A | y0 ≤ a} ≤ ω^η * (m - 1)
                have hAsplit := typeLT_split_downward A (· < y0) (fun x _ y _ hx hy ↦ by
                  have : y0 ≤ y := not_lt.mp hy; exact hx.trans_le this)
                have hA2_le : typeLT ({a ∈ A | y0 ≤ a} : Set V) ≤ ω ^ η * (m - 1 : ℕ) := by
                  have hnot : ({a ∈ A | ¬ a < y0} : Set V) = {a ∈ A | y0 ≤ a} := by ext a; simp
                  rw [hnot] at hAsplit
                  have hm_eq : (m : Ordinal.{0}) = 1 + ((m - 1 : ℕ) : Ordinal.{0}) := by
                    have : m = 1 + (m - 1) := by omega
                    exact_mod_cast this
                  have h1 : ω ^ η + typeLT ({a ∈ A | y0 ≤ a} : Set V) ≤ ω ^ η + ω ^ η * (m - 1 : ℕ) := by
                    calc ω ^ η + typeLT ({a ∈ A | y0 ≤ a} : Set V)
                        ≤ typeLT ({a ∈ A | a < y0} : Set V) + typeLT ({a ∈ A | y0 ≤ a} : Set V) :=
                          add_le_add hAge le_rfl
                      _ = typeLT A := hAsplit.symm
                      _ ≤ ω ^ η * m := hm
                      _ = ω ^ η * (1 + ((m - 1 : ℕ) : Ordinal.{0})) := by rw [hm_eq]
                      _ = ω ^ η + ω ^ η * (m - 1 : ℕ) := by rw [mul_add, mul_one]
                  exact (add_le_add_iff_left (ω ^ η)).mp h1
                have hB2_le : typeLT ({b ∈ B | y0 ≤ b} : Set V) ≤ ω ^ η * n :=
                  (typeLT_mono fun _ h ↦ h.1).trans hn
                exact (typeLT_mono hR_sub).trans_lt (ihk (m - 1) n (by omega) hA2_le hB2_le)
              · -- typeLT {b ∈ B | b < y0} ≥ ω^η, so typeLT {b ∈ B | y0 ≤ b} ≤ ω^η * (n - 1)
                have hBsplit := typeLT_split_downward B (· < y0) (fun x _ y _ hx hy ↦ by
                  have : y0 ≤ y := not_lt.mp hy; exact hx.trans_le this)
                have hB2_le : typeLT ({b ∈ B | y0 ≤ b} : Set V) ≤ ω ^ η * (n - 1 : ℕ) := by
                  have hnot : ({b ∈ B | ¬ b < y0} : Set V) = {b ∈ B | y0 ≤ b} := by ext b; simp
                  rw [hnot] at hBsplit
                  have hn_eq : (n : Ordinal.{0}) = 1 + ((n - 1 : ℕ) : Ordinal.{0}) := by
                    have : n = 1 + (n - 1) := by omega
                    exact_mod_cast this
                  have h1 : ω ^ η + typeLT ({b ∈ B | y0 ≤ b} : Set V) ≤ ω ^ η + ω ^ η * (n - 1 : ℕ) := by
                    calc ω ^ η + typeLT ({b ∈ B | y0 ≤ b} : Set V)
                        ≤ typeLT ({b ∈ B | b < y0} : Set V) + typeLT ({b ∈ B | y0 ≤ b} : Set V) :=
                          add_le_add hBge le_rfl
                      _ = typeLT B := hBsplit.symm
                      _ ≤ ω ^ η * n := hn
                      _ = ω ^ η * (1 + ((n - 1 : ℕ) : Ordinal.{0})) := by rw [hn_eq]
                      _ = ω ^ η + ω ^ η * (n - 1 : ℕ) := by rw [mul_add, mul_one]
                  exact (add_le_add_iff_left (ω ^ η)).mp h1
                have hA2_le : typeLT ({a ∈ A | y0 ≤ a} : Set V) ≤ ω ^ η * m :=
                  (typeLT_mono fun _ h ↦ h.1).trans hm
                exact (typeLT_mono hR_sub).trans_lt (ihk m (n - 1) (by omega) hA2_le hB2_le)
          have hL_lt : typeLT ({x ∈ A ∪ B | P x} : Set V) < ω ^ (η + 1) :=
            hL_le.trans_lt ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (Order.lt_succ η))
          rw [← Ordinal.opow_add_one] at hR_lt ⊢
          exact Ordinal.isPrincipal_add_omega0_opow (η + 1) hL_lt hR_lt
  | limit ξ hlim ih =>
    intro V _ _ A B hA hB
    obtain ⟨η1, hη1, hA1⟩ := (Ordinal.lt_opow_of_isSuccLimit Ordinal.omega0_ne_zero hlim).mp hA
    obtain ⟨η2, hη2, hB2⟩ := (Ordinal.lt_opow_of_isSuccLimit Ordinal.omega0_ne_zero hlim).mp hB
    let η := max η1 η2
    have hη : η < ξ := max_lt hη1 hη2
    have hA' : typeLT A < ω ^ η :=
      hA1.trans_le (Ordinal.opow_le_opow_right Ordinal.omega0_pos (le_max_left _ _))
    have hB' : typeLT B < ω ^ η :=
      hB2.trans_le (Ordinal.opow_le_opow_right Ordinal.omega0_pos (le_max_right _ _))
    exact (ih η hη hA' hB').trans ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr hη)

/-- Deleting a subset of type `< ω ^ ξ` from a set of type `ω ^ ξ` preserves order type `ω ^ ξ`. -/
private lemma typeLT_sdiff_eq_of_lt_omega0_opow {V : Type} [LinearOrder V] [WellFoundedLT V]
    {ξ : Ordinal.{0}} {U A : Set V} (hU : typeLT U = ω ^ ξ) (hA : typeLT A < ω ^ ξ) :
    typeLT (U \ A : Set V) = ω ^ ξ := by
  apply le_antisymm
  · exact (typeLT_mono Set.sdiff_subset).trans hU.le
  · by_contra hlt; push Not at hlt
    have hcov : U ⊆ (U \ A) ∪ A := fun x hx ↦ by
      by_cases h : x ∈ A
      · exact Or.inr h
      · exact Or.inl ⟨hx, h⟩
    have := (typeLT_mono hcov).trans_lt (typeLT_union_lt_omega0_opow ξ hlt hA)
    exact lt_irrefl _ (hU ▸ this)

/-- Deleting a finite set from a set of order type `ω ^ ξ` (`1 ≤ ξ`) preserves order type `ω ^ ξ`. -/
private lemma typeLT_sdiff_finset_omega0_opow {V : Type} [LinearOrder V] [WellFoundedLT V]
    {ξ : Ordinal.{0}} (hξ : 1 ≤ ξ) {U : Set V} (hU : typeLT U = ω ^ ξ) (S : Finset V) :
    typeLT (U \ (S : Set V) : Set V) = ω ^ ξ := by
  apply typeLT_sdiff_eq_of_lt_omega0_opow hU
  have hfin : typeLT (S : Set V) < ω := by
    rw [Ordinal.lt_omega0]
    refine ⟨Fintype.card ↥(S : Set V), ?_⟩
    exact Ordinal.type_fintype (r := (· < · : ↥(S : Set V) → _ → Prop))
  exact hfin.trans_le (by
    calc ω = ω ^ (1 : Ordinal.{0}) := (Ordinal.opow_one ω).symm
      _ ≤ ω ^ ξ := Ordinal.opow_le_opow_right Ordinal.omega0_pos hξ)

/-- Cantor normal form decomposition for any limit ordinal `β`: a non-increasing list of exponents
`ξ_j ≥ 1` whose `ω ^ ξ_j` sum to `β`. -/
private lemma exists_cnf_limit : ∀ (β : Ordinal.{0}), Order.IsSuccLimit β →
    ∃ L : List Ordinal.{0}, L.Pairwise (· ≥ ·) ∧ (∀ ξ ∈ L, 1 ≤ ξ) ∧
      β = (L.map (fun ξ ↦ ω ^ ξ)).sum := by
  intro β
  induction β using WellFoundedLT.induction with
  | ind β ih =>
    intro hlim
    have hβ_pos : 0 < β := hlim.bot_lt
    have hω_le : ω ≤ β := Ordinal.omega0_le_of_isSuccLimit hlim
    let ξ := Ordinal.log ω β
    have hξ1 : 1 ≤ ξ := by
      rw [← Ordinal.opow_le_iff_le_log Ordinal.one_lt_omega0 hβ_pos.ne', Ordinal.opow_one]
      exact hω_le
    have hle : ω ^ ξ ≤ β := Ordinal.opow_log_le_self ω hβ_pos.ne'
    have hlt_succ : β < ω ^ (ξ + 1) := Ordinal.lt_opow_succ_log_self Ordinal.one_lt_omega0 β
    let r := β - ω ^ ξ
    have hadd : ω ^ ξ + r = β := Ordinal.add_sub_cancel_of_le hle
    have hr_lt : r < β := by
      by_contra hge; push Not at hge
      have hge' : ω ^ ξ + β ≤ β := (add_le_add le_rfl hge).trans hadd.le
      have hlt' : β < ω ^ ξ + β := by
        have hdiv : β / ω ^ ξ < ω := by
          rw [← Ordinal.lt_mul_iff_div_lt (Ordinal.opow_ne_zero ξ Ordinal.omega0_ne_zero), ← Ordinal.opow_add_one]
          exact hlt_succ
        obtain ⟨q, hq⟩ := Ordinal.lt_omega0.mp hdiv
        have hdm : ω ^ ξ * q + β % ω ^ ξ = β := by
          rw [← hq]; exact Ordinal.div_add_mod β (ω ^ ξ)
        have hmod : β % ω ^ ξ < ω ^ ξ :=
          Ordinal.mod_lt β (Ordinal.opow_ne_zero ξ Ordinal.omega0_ne_zero)
        have hstep : ω ^ ξ + β = ω ^ ξ * ((q + 1 : ℕ) : Ordinal.{0}) + β % ω ^ ξ := by
          have h1q : ω ^ ξ + ω ^ ξ * (q : Ordinal.{0}) = ω ^ ξ * ((1 + q : ℕ) : Ordinal.{0}) := by
            rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one]
          conv_lhs => rw [← hdm]
          rw [← add_assoc, h1q, show 1 + q = q + 1 by omega]
        rw [hstep]
        conv_lhs => rw [← hdm]
        have hlt1 : ω ^ ξ * (q : Ordinal.{0}) + β % ω ^ ξ < ω ^ ξ * ((q + 1 : ℕ) : Ordinal.{0}) := by
          rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one]
          exact (add_lt_add_iff_left (ω ^ ξ * (q : Ordinal.{0}))).mpr hmod
        exact hlt1.trans_le le_self_add
      exact not_lt_of_ge hge' hlt'
    by_cases hr0 : r = 0
    · refine ⟨[ξ], List.pairwise_singleton _ _, fun η hη ↦ by simp at hη; rw [hη]; exact hξ1, ?_⟩
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [← hadd, hr0, add_zero]
    · have hr_lim : Order.IsSuccLimit r := by
        rw [← hadd] at hlim
        exact (Ordinal.isSuccLimit_add_iff.mp hlim).resolve_right (fun h ↦ hr0 h.1)
      obtain ⟨Lr, hLr_pair, hLr_ge1, hLr_sum⟩ := ih r hr_lt hr_lim
      refine ⟨ξ :: Lr, ?_, ?_, ?_⟩
      · rw [List.pairwise_cons]
        refine ⟨fun η hη ↦ ?_, hLr_pair⟩
        -- ω ^ η ≤ r ≤ β < ω ^ (ξ + 1), so η ≤ ξ
        have hη_le_r : ω ^ η ≤ r := by
          rw [hLr_sum]
          have hmem : ω ^ η ∈ Lr.map (fun x ↦ ω ^ x) := List.mem_map.mpr ⟨η, hη, rfl⟩
          exact List.le_sum_of_mem hmem
        have hlt_pow : ω ^ η < ω ^ (ξ + 1) := hη_le_r.trans_lt (hr_lt.trans hlt_succ)
        have hlt_exp : η < ξ + 1 := (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mp hlt_pow
        exact Order.lt_add_one_iff.mp hlt_exp
      · intro η hη
        rw [List.mem_cons] at hη
        rcases hη with rfl | hη
        · exact hξ1
        · exact hLr_ge1 η hη
      · simp only [List.map_cons, List.sum_cons]
        rw [← hLr_sum, hadd]

/-- Strictly smaller head cannot be compensated by a non-increasing tail of `ω`-powers. -/
private lemma cnf_lt_of_head_lt :
    ∀ (L : List Ordinal.{0}), L.Pairwise (· ≥ ·) →
      ∀ (ξ α : Ordinal.{0}), (∀ η ∈ L, η ≤ ξ) → α < ω ^ ξ →
        α + (L.map (fun η ↦ ω ^ η)).sum < ω ^ ξ + (L.map (fun η ↦ ω ^ η)).sum := by
  intro L
  induction L with
  | nil =>
    intro _ ξ α _ hα
    simpa using hα
  | cons η rest ih =>
    intro hpair ξ α hle hα
    rw [List.pairwise_cons] at hpair
    have hη_le : η ≤ ξ := hle η (List.mem_cons_self ..)
    have hrest_le : ∀ ζ ∈ rest, ζ ≤ ξ := fun ζ hζ ↦ hle ζ (List.mem_cons_of_mem _ hζ)
    simp only [List.map_cons, List.sum_cons]
    rcases lt_or_eq_of_le hη_le with hlt | hη_eq
    · -- All elements of (η :: rest) are < ξ, so α + sum < ω ^ ξ ≤ ω ^ ξ + sum
      have hsum_lt : (rest.map (fun x ↦ ω ^ x)).sum < ω ^ ξ := by
        have : ∀ (M : List Ordinal.{0}), (∀ x ∈ M, x < ξ) → (M.map (fun x ↦ ω ^ x)).sum < ω ^ ξ := by
          intro M
          induction M with
          | nil => intro _; simpa using Ordinal.opow_pos ξ Ordinal.omega0_pos
          | cons a as ihas =>
            intro hM
            simp only [List.map_cons, List.sum_cons]
            exact Ordinal.isPrincipal_add_omega0_opow ξ
              ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (hM a (List.mem_cons_self ..)))
              (ihas fun x hx ↦ hM x (List.mem_cons_of_mem _ hx))
        exact this rest (fun ζ hζ ↦ (hpair.1 ζ hζ).trans_lt hlt)
      have hη_lt : ω ^ η < ω ^ ξ := (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr hlt
      have hrhs_lt : α + (ω ^ η + (rest.map (fun x ↦ ω ^ x)).sum) < ω ^ ξ :=
        Ordinal.isPrincipal_add_omega0_opow ξ hα
          (Ordinal.isPrincipal_add_omega0_opow ξ hη_lt hsum_lt)
      exact hrhs_lt.trans_le le_self_add
    · -- η = ξ: α + ω ^ ξ = ω ^ ξ, so LHS = ω ^ ξ + sum rest < ω ^ ξ + (ω ^ ξ + sum rest)
      subst hη_eq
      rw [← add_assoc, Ordinal.add_omega0_opow hα]
      rw [add_lt_add_iff_left]
      have hS_lt : ∀ (M : List Ordinal.{0}), M.Pairwise (· ≥ ·) → (∀ x ∈ M, x ≤ η) →
          (M.map (fun x ↦ ω ^ x)).sum < ω ^ η + (M.map (fun x ↦ ω ^ x)).sum := by
        intro M
        induction M with
        | nil => intro _ _; simpa using Ordinal.opow_pos η Ordinal.omega0_pos
        | cons b bs ihb =>
          intro hp hleM
          rw [List.pairwise_cons] at hp
          simp only [List.map_cons, List.sum_cons]
          rcases lt_or_eq_of_le (hleM b (List.mem_cons_self ..)) with hltb | hb_eq
          · have hbs : (bs.map (fun x ↦ ω ^ x)).sum < ω ^ η := by
              have : ∀ (N : List Ordinal.{0}), (∀ x ∈ N, x < η) → (N.map (fun x ↦ ω ^ x)).sum < ω ^ η := by
                intro N; induction N with
                | nil => intro _; simpa using Ordinal.opow_pos η Ordinal.omega0_pos
                | cons c cs ihc =>
                  intro hN; simp only [List.map_cons, List.sum_cons]
                  exact Ordinal.isPrincipal_add_omega0_opow η
                    ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (hN c (List.mem_cons_self ..)))
                    (ihc fun x hx ↦ hN x (List.mem_cons_of_mem _ hx))
              exact this bs (fun x hx ↦ (hp.1 x hx).trans_lt hltb)
            exact (Ordinal.isPrincipal_add_omega0_opow η
              ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr hltb) hbs).trans_le le_self_add
          · subst hb_eq
            rw [← add_assoc, add_assoc (ω ^ b)]
            exact (add_lt_add_iff_left (ω ^ b)).mpr (ihb hp.2 (fun x hx ↦ hleM x (List.mem_cons_of_mem _ hx)))
      exact hS_lt rest hpair.2 hrest_le

/-- Sum of order types of a list of consecutive subsets. -/
private lemma typeLT_biUnion_list {V : Type} [LinearOrder V] [WellFoundedLT V] :
    ∀ (As : List (Set V)),
      (∀ (i j : Fin As.length), i < j → ∀ x ∈ As.get i, ∀ y ∈ As.get j, x < y) →
      typeLT (⋃ i : Fin As.length, As.get i) = (As.map (fun A : Set V ↦ typeLT ↥A)).sum := by
  intro As
  induction As with
  | nil =>
    intro _
    have he : (⋃ i : Fin ([] : List (Set V)).length, ([] : List (Set V)).get i) = ∅ := by
      ext x; simp
    rw [he]
    simp only [List.map_nil, List.sum_nil]
    exact typeLT_empty (V := V)
  | cons A As' ih =>
    intro hord
    have hsplit : (⋃ i : Fin (A :: As').length, (A :: As').get i) =
        A ∪ (⋃ j : Fin As'.length, As'.get j) := by
      ext x; simp only [Set.mem_iUnion, Set.mem_union]
      constructor
      · rintro ⟨i, hi⟩
        cases i using Fin.cases with
        | zero => exact Or.inl hi
        | succ j => exact Or.inr ⟨j, hi⟩
      · rintro (hA | ⟨j, hj⟩)
        · exact ⟨0, hA⟩
        · exact ⟨j.succ, hj⟩
    rw [hsplit, typeLT_union_of_lt]
    · simp only [List.map_cons, List.sum_cons]
      congr 1
      exact ih (fun i j hij ↦ hord i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij))
    · intro x hxA y hy
      rw [Set.mem_iUnion] at hy
      obtain ⟨j, hj⟩ := hy
      exact hord 0 j.succ (Fin.succ_pos j) x hxA y hj

/-- Split a set of order type `(L.map (ω ^ ·)).sum` into consecutive subsets `A_i` of order type
`ω ^ L[i]`. -/
private lemma exists_split_list {V : Type} [LinearOrder V] [WellFoundedLT V] :
    ∀ (L : List Ordinal.{0}) (U : Set V),
      typeLT U = (L.map (fun ξ ↦ ω ^ ξ)).sum →
      ∃ As : Fin L.length → Set V,
        (∀ i, As i ⊆ U) ∧
        (⋃ i, As i) = U ∧
        (∀ i j, i < j → ∀ x ∈ As i, ∀ y ∈ As j, x < y) ∧
        (∀ i, typeLT (As i) = ω ^ L.get i) := by
  intro L
  induction L with
  | nil =>
    intro U hU
    simp only [List.map_nil, List.sum_nil] at hU
    have hUe : U = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun x hx ↦
      (Ordinal.type_eq_zero_iff_isEmpty.mp hU).false ⟨x, hx⟩
    exact ⟨Fin.elim0, fun i ↦ i.elim0, by simp [hUe], fun i ↦ i.elim0, fun i ↦ i.elim0⟩
  | cons ξ L' ih =>
    intro U hU
    simp only [List.map_cons, List.sum_cons] at hU
    obtain ⟨A0, U', hA0U, hU'U, hunion, hlt0, hA0_type, hU'_type⟩ := exists_split_of_typeLT_add hU
    obtain ⟨As', hAs'_sub, hAs'_uni, hAs'_ord, hAs'_type⟩ := ih U' hU'_type
    refine ⟨Fin.cases A0 As', ?_, ?_, ?_, ?_⟩
    · intro i
      cases i using Fin.cases with
      | zero => exact hA0U
      | succ j => exact (hAs'_sub j).trans hU'U
    · ext x; simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨i, hi⟩
        cases i using Fin.cases with
        | zero => exact hA0U hi
        | succ j => exact hU'U (hAs'_sub j hi)
      · intro hx
        rw [← hunion] at hx
        rcases hx with h0 | h1
        · exact ⟨0, h0⟩
        · rw [← hAs'_uni, Set.mem_iUnion] at h1
          obtain ⟨j, hj⟩ := h1
          exact ⟨j.succ, hj⟩
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact absurd hij (lt_irrefl _)
        | succ j' =>
          intro x hx y hy
          exact hlt0 x hx y (hAs'_sub j' hy)
      | succ i' =>
        cases j using Fin.cases with
        | zero => exact absurd hij (not_lt_of_ge (Fin.zero_le _))
        | succ j' =>
          exact hAs'_ord i' j' (Fin.succ_lt_succ_iff.mp hij)
    · intro i
      cases i using Fin.cases with
      | zero => exact hA0_type
      | succ j => exact hAs'_type j

/-- Rigidity of non-increasing Cantor sums: if `I ⊆ ⋃ i, As i` has order type
`(L.map (ω ^ ·)).sum` where `L` is non-increasing and `typeLT (As i) = ω ^ L[i]`, then
`typeLT (I ∩ As i) = ω ^ L[i]` for every `i`. -/
private lemma cnf_sum_rigid {V : Type} [LinearOrder V] [WellFoundedLT V] :
    ∀ (L : List Ordinal.{0}), L.Pairwise (· ≥ ·) →
      ∀ (As : Fin L.length → Set V),
        (∀ i j, i < j → ∀ x ∈ As i, ∀ y ∈ As j, x < y) →
        (∀ i, typeLT (As i) = ω ^ L.get i) →
        ∀ (I : Set V), I ⊆ (⋃ i, As i) →
          typeLT I = (L.map (fun ξ ↦ ω ^ ξ)).sum →
          ∀ i : Fin L.length, typeLT (I ∩ As i : Set V) = ω ^ L.get i := by
  intro L
  induction L with
  | nil => intro _ _ _ _ _ _ _ i; exact i.elim0
  | cons ξ L' ih =>
    intro hpair As hord htype I hIsub hItype
    rw [List.pairwise_cons] at hpair
    have hIeq : I = (I ∩ As 0) ∪ (I ∩ (⋃ j : Fin L'.length, As j.succ)) := by
      ext x; constructor
      · intro hx
        have hmem := hIsub hx
        rw [Set.mem_iUnion] at hmem
        obtain ⟨k, hk⟩ := hmem
        cases k using Fin.cases with
        | zero => exact Or.inl ⟨hx, hk⟩
        | succ j => exact Or.inr ⟨hx, Set.mem_iUnion.mpr ⟨j, hk⟩⟩
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    have hlt_LR : ∀ x ∈ I ∩ As 0, ∀ y ∈ I ∩ (⋃ j : Fin L'.length, As j.succ), x < y := by
      intro x hx y hy
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy.2
      exact hord 0 j.succ (Fin.succ_pos j) x hx.2 y hj
    have hIsplit : typeLT I = typeLT (I ∩ As 0 : Set V) + typeLT (I ∩ (⋃ j : Fin L'.length, As j.succ) : Set V) := by
      conv_lhs => rw [hIeq]
      exact typeLT_union_of_lt hlt_LR
    have hR_le : typeLT (I ∩ (⋃ j : Fin L'.length, As j.succ) : Set V) ≤ (L'.map (fun η ↦ ω ^ η)).sum := by
      have hU_type : typeLT (⋃ j : Fin L'.length, As j.succ) = (L'.map (fun η ↦ ω ^ η)).sum := by
        let Bs : List (Set V) := List.ofFn (fun j : Fin L'.length ↦ As j.succ)
        have hBs_len : Bs.length = L'.length := List.length_ofFn
        have h1 := typeLT_biUnion_list Bs (by
          intro i j hij
          have hi : i.val < L'.length := hBs_len ▸ i.isLt
          have hj : j.val < L'.length := hBs_len ▸ j.isLt
          have hget_i : Bs.get i = As (Fin.succ ⟨i.val, hi⟩) := by simp [Bs]
          have hget_j : Bs.get j = As (Fin.succ ⟨j.val, hj⟩) := by simp [Bs]
          rw [hget_i, hget_j]
          exact hord (Fin.succ ⟨i.val, hi⟩) (Fin.succ ⟨j.val, hj⟩)
            (Fin.succ_lt_succ_iff.mpr (Fin.mk_lt_mk.mpr (Fin.lt_def.mp hij))))
        have hUeq : (⋃ j : Fin L'.length, As j.succ) = ⋃ i : Fin Bs.length, Bs.get i := by
          ext x; simp only [Set.mem_iUnion]
          constructor
          · rintro ⟨j, hj⟩
            refine ⟨⟨j.val, hBs_len.symm ▸ j.isLt⟩, ?_⟩
            simpa [Bs] using hj
          · rintro ⟨i, hi⟩
            refine ⟨⟨i.val, hBs_len ▸ i.isLt⟩, ?_⟩
            simpa [Bs] using hi
        rw [hUeq, h1]
        congr 1
        apply List.ext_getElem (by simp [Bs])
        intro k hk1 hk2
        simp only [Bs, List.getElem_map]
        have hk' : k < L'.length := by rw [List.length_map] at hk2; exact hk2
        exact (typeLT_congr_set (List.getElem_ofFn _)).trans
          (by simpa only [List.get_eq_getElem, Fin.val_succ, List.getElem_cons_succ] using htype (Fin.succ ⟨k, hk'⟩))
      exact (typeLT_mono Set.inter_subset_right).trans hU_type.le
    have h0_le : typeLT (I ∩ As 0 : Set V) ≤ ω ^ ξ := (typeLT_mono Set.inter_subset_right).trans (htype 0).le
    simp only [List.map_cons, List.sum_cons] at hItype
    have h0_eq : typeLT (I ∩ As 0 : Set V) = ω ^ ξ := by
      apply le_antisymm h0_le
      by_contra hlt; push Not at hlt
      have hstrict := cnf_lt_of_head_lt L' hpair.2 ξ (typeLT (I ∩ As 0 : Set V)) hpair.1 hlt
      have hle' : typeLT (I ∩ As 0 : Set V) + typeLT (I ∩ (⋃ j : Fin L'.length, As j.succ) : Set V) ≤
          typeLT (I ∩ As 0 : Set V) + (L'.map (fun η ↦ ω ^ η)).sum :=
        add_le_add le_rfl hR_le
      rw [← hIsplit, hItype] at hle'
      exact not_lt_of_ge hle' hstrict
    have hR_eq : typeLT (I ∩ (⋃ j : Fin L'.length, As j.succ) : Set V) = (L'.map (fun η ↦ ω ^ η)).sum := by
      rw [hItype, h0_eq] at hIsplit
      exact (add_right_inj (ω ^ ξ)).mp hIsplit.symm
    intro i
    cases i using Fin.cases with
    | zero => exact h0_eq
    | succ j =>
      have hres := ih hpair.2 (fun k ↦ As k.succ)
        (fun a b hab ↦ hord a.succ b.succ (Fin.succ_lt_succ_iff.mpr hab))
        (fun k ↦ htype k.succ)
        (I ∩ (⋃ k : Fin L'.length, As k.succ)) Set.inter_subset_right hR_eq j
      have heq : (I ∩ (⋃ k : Fin L'.length, As k.succ)) ∩ As j.succ = I ∩ As j.succ := by
        ext x; constructor
        · rintro ⟨⟨hxI, _⟩, hxA⟩; exact ⟨hxI, hxA⟩
        · rintro ⟨hxI, hxA⟩; exact ⟨⟨hxI, Set.mem_iUnion.mpr ⟨j, hxA⟩⟩, hxA⟩
      rw [heq] at hres
      exact hres

/-- Fundamental sequence decomposition for any countable `0 < ξ < ω_ 1`: there exists
`f : ℕ → Ordinal.{0}` with `∀ n, f n < ξ` such that any set `U` of type `ω ^ ξ` splits into
consecutive subsets `W n` of type `ω ^ (f n)`, and ANY infinite subsequence of subsets
`Y k ⊆ W (g k)` of types `ω ^ (f (g k))` has union of type `ω ^ ξ`. -/
private lemma exists_omega0_opow_decomp (ξ : Ordinal.{0}) (hξpos : 0 < ξ) (hξcnt : ξ < ω_ 1) :
    ∃ f : ℕ → Ordinal.{0}, (∀ n, f n < ξ) ∧
      (∀ (g : ℕ → ℕ), StrictMono g →
        ∀ {V : Type} [LinearOrder V] [WellFoundedLT V] (Y : ℕ → Set V),
          (∀ i j, i < j → ∀ x ∈ Y i, ∀ y ∈ Y j, x < y) →
          (∀ k, typeLT (Y k) = ω ^ f (g k)) →
          ω ^ ξ ≤ typeLT (⋃ k, Y k)) ∧
      (∀ {V : Type} [LinearOrder V] [WellFoundedLT V] (U : Set V),
        typeLT U = ω ^ ξ →
        ∃ W : ℕ → Set V,
          (∀ n, W n ⊆ U) ∧
          (∀ i j, i < j → ∀ x ∈ W i, ∀ y ∈ W j, x < y) ∧
          (∀ n, typeLT (W n) = ω ^ f n)) := by
  by_cases hlim : Order.IsSuccLimit ξ
  · -- Countable limit ordinal ξ: enumerate ξ.ToType and take running max
    have hcnt : Countable ξ.ToType := by
      rw [← Cardinal.mk_le_aleph0_iff, Cardinal.mk_toType]
      have hcard : ξ.card < ℵ_ 1 := by
        rw [← Cardinal.lt_ord, Cardinal.ord_aleph]; exact hξcnt
      exact Cardinal.lt_aleph_one_iff.mp hcard
    have hne : Nonempty ξ.ToType := by
      have h0 : Cardinal.mk ξ.ToType ≠ 0 := by
        rw [Cardinal.mk_toType]
        exact fun h ↦ hξpos.ne' (Ordinal.card_eq_zero.mp h)
      exact Cardinal.mk_ne_zero_iff.mp h0
    obtain ⟨enum, hsurj⟩ := exists_surjective_nat ξ.ToType
    let val : ℕ → Ordinal.{0} := fun n ↦ Ordinal.typein (· < · : ξ.ToType → _ → Prop) (enum n)
    have hval_lt : ∀ n, val n < ξ := fun n ↦ by
      have := Ordinal.typein_lt_type (· < · : ξ.ToType → _ → Prop) (enum n)
      rwa [Ordinal.type_toType] at this
    let f : ℕ → Ordinal.{0} := Nat.rec (val 0) (fun n prev ↦ max prev (val (n + 1)))
    have hf_lt : ∀ n, f n < ξ := by
      intro n; induction n with
      | zero => exact hval_lt 0
      | succ n ih => exact max_lt ih (hval_lt (n + 1))
    have hf_mono : Monotone f := by
      apply monotone_nat_of_le_succ; intro n; exact le_max_left _ _
    have hf_cof : ∀ α < ξ, ∃ n, α ≤ f n := by
      intro α hα
      let x : ξ.ToType := Ordinal.enum (· < · : ξ.ToType → _ → Prop) ⟨α, by rw [Ordinal.type_toType]; exact hα⟩
      obtain ⟨n, hn⟩ := hsurj x
      refine ⟨n, ?_⟩
      have hval_eq : val n = α := by
        dsimp only [val]; rw [hn]
        exact Ordinal.typein_enum (· < · : ξ.ToType → _ → Prop) (by rw [Ordinal.type_toType]; exact hα)
      rw [← hval_eq]
      cases n with
      | zero => exact le_refl _
      | succ k => exact le_max_right _ _
    refine ⟨f, hf_lt, ?_, ?_⟩
    · intro g hg V _ _ Y _ hYtype
      rw [Ordinal.opow_le_of_isSuccLimit Ordinal.omega0_ne_zero hlim]
      intro α hα
      obtain ⟨n, hn⟩ := hf_cof α hα
      have hle : f n ≤ f (g n) := hf_mono (hg.id_le n)
      calc ω ^ α ≤ ω ^ f (g n) := Ordinal.opow_le_opow_right Ordinal.omega0_pos (hn.trans hle)
        _ = typeLT (Y n) := (hYtype n).symm
        _ ≤ typeLT (⋃ k, Y k) := typeLT_mono (Set.subset_iUnion Y n)
    · intro V _ _ U hU
      have hpeel : ∀ (R : Set V), typeLT R = ω ^ ξ → ∀ n : ℕ,
          ∃ W R' : Set V, W ⊆ R ∧ R' ⊆ R ∧ (∀ x ∈ W, ∀ y ∈ R', x < y) ∧
            typeLT W = ω ^ f n ∧ typeLT R' = ω ^ ξ := by
        intro R hR n
        have hadd : ω ^ f n + ω ^ ξ = ω ^ ξ :=
          Ordinal.add_omega0_opow ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (hf_lt n))
        obtain ⟨W, R', hWR, hR'R, _, hlt, hWt, hR't⟩ := exists_split_of_typeLT_add (hR.trans hadd.symm)
        exact ⟨W, R', hWR, hR'R, hlt, hWt, hR't⟩
      choose peelW peelR hWsub hRsub hWRlt hWtype hRtype using hpeel
      let rem : ℕ → {R : Set V // typeLT R = ω ^ ξ} :=
        Nat.rec ⟨U, hU⟩ (fun n prev ↦ ⟨peelR prev.1 prev.2 n, hRtype prev.1 prev.2 n⟩)
      let W : ℕ → Set V := fun n ↦ peelW (rem n).1 (rem n).2 n
      have hrem_sub : ∀ {i j : ℕ}, i ≤ j → (rem j).1 ⊆ (rem i).1 := by
        intro i j hij
        induction hij with
        | refl => exact Set.Subset.rfl
        | @step k _ ih => exact (hRsub (rem k).1 (rem k).2 k).trans ih
      refine ⟨W, fun n ↦ (hWsub (rem n).1 (rem n).2 n).trans (hrem_sub (Nat.zero_le n)), ?_,
        fun n ↦ hWtype (rem n).1 (rem n).2 n⟩
      intro i j hij x hx y hy
      have hy_rem : y ∈ (rem (i + 1)).1 := hrem_sub hij (hWsub (rem j).1 (rem j).2 j hy)
      exact hWRlt (rem i).1 (rem i).2 i x hx y hy_rem
  · -- Successor ordinal ξ = η + 1
    have hnotmin : ¬ IsMin ξ := not_isMin_of_lt hξpos
    have hex_pred : ∃ η : Ordinal.{0}, ξ = η + 1 := by
      have h1 : ¬ Order.IsSuccPrelimit ξ := fun h ↦ hlim ⟨hnotmin, h⟩
      rw [Order.isSuccPrelimit_iff_succ_lt] at h1
      push Not at h1
      obtain ⟨η, hηlt, hle⟩ := h1
      have hsucc_eq : ξ = Order.succ η := le_antisymm hle (Order.succ_le_of_lt hηlt)
      exact ⟨η, hsucc_eq.trans (Order.succ_eq_add_one η)⟩
    obtain ⟨η, rfl⟩ := hex_pred
    refine ⟨fun _ ↦ η, fun _ ↦ Order.lt_succ η, ?_, ?_⟩
    · intro g _ V _ _ Y hYord hYtype
      rw [Ordinal.opow_add_one]
      have hle_nat : ∀ m : ℕ, ω ^ η * m ≤ typeLT (⋃ k, Y k) := by
        intro m
        let Ys : List (Set V) := List.ofFn (fun i : Fin m ↦ Y i.val)
        have hYs_len : Ys.length = m := List.length_ofFn
        have hsum_rep : ∀ (n : ℕ) (a : Ordinal.{0}), (List.replicate n a).sum = a * n := by
          intro n a; induction n with
          | zero => simp
          | succ n ihn =>
            rw [List.replicate_succ, List.sum_cons, ihn]
            have h1 : (1 : Ordinal.{0}) + (n : Ordinal.{0}) = ((n + 1 : ℕ) : Ordinal.{0}) := by
              have : 1 + n = n + 1 := by omega
              exact_mod_cast this
            rw [← h1, mul_add, mul_one]
        have hYs_type : typeLT (⋃ i : Fin Ys.length, Ys.get i) = ω ^ η * m := by
          rw [typeLT_biUnion_list Ys]
          · have hmap : Ys.map (fun A : Set V ↦ typeLT ↥A) = List.replicate m (ω ^ η) := by
              apply List.ext_getElem (by simp [Ys])
              intro k hk1 hk2
              simp only [Ys, List.getElem_map, List.getElem_replicate]
              exact (typeLT_congr_set (List.getElem_ofFn _)).trans (hYtype k)
            rw [hmap, hsum_rep]
          · intro i j hij
            simp only [Ys, List.get_eq_getElem, List.getElem_ofFn]
            exact hYord i.val j.val (Fin.lt_def.mp hij)
        have hsub : (⋃ i : Fin Ys.length, Ys.get i) ⊆ ⋃ k, Y k := by
          intro x hx; rw [Set.mem_iUnion] at hx ⊢
          obtain ⟨i, hi⟩ := hx
          simp only [Ys, List.get_eq_getElem, List.getElem_ofFn] at hi
          exact ⟨i.val, hi⟩
        exact hYs_type.symm.le.trans (typeLT_mono hsub)
      by_contra hlt; push Not at hlt
      have hdiv : (typeLT (⋃ k, Y k)) / ω ^ η < ω :=
        (Ordinal.lt_mul_iff_div_lt (Ordinal.opow_ne_zero η Ordinal.omega0_ne_zero)).mp hlt
      obtain ⟨m, hm⟩ := Ordinal.lt_omega0.mp hdiv
      have h1 : typeLT (⋃ k, Y k) < ω ^ η * ((m + 1 : ℕ) : Ordinal.{0}) := by
        have hlt1 := Ordinal.lt_mul_succ_div (typeLT (⋃ k, Y k)) (Ordinal.opow_ne_zero η Ordinal.omega0_ne_zero)
        rw [hm] at hlt1
        simpa [Nat.cast_add, Nat.cast_one] using hlt1
      exact not_lt_of_ge (hle_nat (m + 1)) h1
    · intro V _ _ U hU
      have hpeel : ∀ (R : Set V), typeLT R = ω ^ (η + 1) →
          ∃ W R' : Set V, W ⊆ R ∧ R' ⊆ R ∧ (∀ x ∈ W, ∀ y ∈ R', x < y) ∧
            typeLT W = ω ^ η ∧ typeLT R' = ω ^ (η + 1) := by
        intro R hR
        have hadd : ω ^ η + ω ^ (η + 1) = ω ^ (η + 1) :=
          Ordinal.add_omega0_opow ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (Order.lt_succ η))
        obtain ⟨W, R', hWR, hR'R, _, hlt, hWt, hR't⟩ := exists_split_of_typeLT_add (hR.trans hadd.symm)
        exact ⟨W, R', hWR, hR'R, hlt, hWt, hR't⟩
      choose peelW peelR hWsub hRsub hWRlt hWtype hRtype using hpeel
      let rem : ℕ → {R : Set V // typeLT R = ω ^ (η + 1)} :=
        Nat.rec ⟨U, hU⟩ (fun _ prev ↦ ⟨peelR prev.1 prev.2, hRtype prev.1 prev.2⟩)
      let W : ℕ → Set V := fun n ↦ peelW (rem n).1 (rem n).2
      have hrem_sub : ∀ {i j : ℕ}, i ≤ j → (rem j).1 ⊆ (rem i).1 := by
        intro i j hij
        induction hij with
        | refl => exact Set.Subset.rfl
        | @step k _ ih => exact (hRsub (rem k).1 (rem k).2).trans ih
      refine ⟨W, fun n ↦ (hWsub (rem n).1 (rem n).2).trans (hrem_sub (Nat.zero_le n)), ?_,
        fun n ↦ hWtype (rem n).1 (rem n).2⟩
      intro i j hij x hx y hy
      have hy_rem : y ∈ (rem (i + 1)).1 := hrem_sub hij (hWsub (rem j).1 (rem j).2 hy)
      exact hWRlt (rem i).1 (rem i).2 x hx y hy_rem

/- ### Part 3: Multi-root pruned-tree BFS partition lemma -/

/-- Rank-respecting enumeration of `Fin k × List ℕ` (for `k ≥ 1`), so that every parent
`(j, p)` precedes every child `(j, p ++ [a])`, and left siblings `(j, p ++ [a₁])` precede right
siblings `(j, p ++ [a₂])` (`a₁ < a₂`). -/
private lemma exists_rank_enum (k : ℕ) (hk : 0 < k) :
    ∃ e : ℕ ≃ Fin k × List ℕ,
      ∀ i j : ℕ, (e i).2.length + (e i).2.sum < (e j).2.length + (e j).2.sum → i < j := by
  let rk : Fin k × List ℕ → ℕ := fun x ↦ x.2.length + x.2.sum
  have hfin_layer : ∀ r : ℕ, Set.Finite {x : Fin k × List ℕ | rk x = r} := by
    intro r
    let T := Fin k × (Σ len : Fin (r + 1), Fin len.val → Fin (r + 1))
    have hfinT : Finite T := inferInstance
    let toT : {x : Fin k × List ℕ // rk x = r} → T := fun ⟨⟨j, l⟩, hrl⟩ ↦
      ⟨j, ⟨⟨l.length, by dsimp [rk] at hrl; omega⟩, fun idx ↦ ⟨l.get idx, by
        have hle : l.get idx ≤ l.sum := List.le_sum_of_mem (List.get_mem l idx)
        dsimp [rk] at hrl; omega⟩⟩⟩
    have hinj : Function.Injective toT := by
      rintro ⟨⟨j1, l1⟩, h1⟩ ⟨⟨j2, l2⟩, h2⟩ heq
      have hj : j1 = j2 := congrArg Prod.fst heq
      have hsig : (⟨⟨l1.length, by dsimp [rk] at h1; omega⟩, fun idx ↦ ⟨l1.get idx, by
            have hle : l1.get idx ≤ l1.sum := List.le_sum_of_mem (List.get_mem l1 idx)
            dsimp [rk] at h1; omega⟩⟩ : Σ len : Fin (r + 1), Fin len.val → Fin (r + 1)) =
          ⟨⟨l2.length, by dsimp [rk] at h2; omega⟩, fun idx ↦ ⟨l2.get idx, by
            have hle : l2.get idx ≤ l2.sum := List.le_sum_of_mem (List.get_mem l2 idx)
            dsimp [rk] at h2; omega⟩⟩ := congrArg Prod.snd heq
      have hlen : l1.length = l2.length := congrArg (fun z : Fin (r + 1) ↦ z.val) (congrArg Sigma.fst hsig)
      have hl : l1 = l2 := by
        apply List.ext_getElem hlen
        intro idx hlt1 hlt2
        have hfun : HEq (fun i : Fin l1.length ↦ (⟨l1.get i, by
              have hle : l1.get i ≤ l1.sum := List.le_sum_of_mem (List.get_mem l1 i)
              dsimp [rk] at h1; omega⟩ : Fin (r + 1)))
            (fun i : Fin l2.length ↦ (⟨l2.get i, by
              have hle : l2.get i ≤ l2.sum := List.le_sum_of_mem (List.get_mem l2 i)
              dsimp [rk] at h2; omega⟩ : Fin (r + 1))) := (Sigma.mk.inj hsig).2
        have hpt : (⟨l1.get ⟨idx, hlt1⟩, by
              have hle : l1.get ⟨idx, hlt1⟩ ≤ l1.sum := List.le_sum_of_mem (List.get_mem l1 ⟨idx, hlt1⟩)
              dsimp [rk] at h1; omega⟩ : Fin (r + 1)) =
            ⟨l2.get ⟨idx, hlt2⟩, by
              have hle : l2.get ⟨idx, hlt2⟩ ≤ l2.sum := List.le_sum_of_mem (List.get_mem l2 ⟨idx, hlt2⟩)
              dsimp [rk] at h2; omega⟩ := by
          have : ∀ (n1 n2 : ℕ) (hn : n1 = n2) (f1 : Fin n1 → Fin (r + 1)) (f2 : Fin n2 → Fin (r + 1)),
              HEq f1 f2 → ∀ (i : ℕ) (hi1 : i < n1) (hi2 : i < n2), f1 ⟨i, hi1⟩ = f2 ⟨i, hi2⟩ := by
            intro n1 n2 hn f1 f2 hfeq i hi1 hi2; subst hn; cases eq_of_heq hfeq; rfl
          exact this l1.length l2.length hlen _ _ hfun idx hlt1 hlt2
        simpa [List.get_eq_getElem] using congrArg Fin.val hpt
      exact Subtype.ext (Prod.ext hj hl)
    exact Set.finite_coe_iff.mp (Finite.of_injective toT hinj)
  -- Layer finsets and cumulative sizes
  let L : ℕ → Finset (Fin k × List ℕ) := fun r ↦ (hfin_layer r).toFinset
  have hL_mem : ∀ r x, x ∈ L r ↔ rk x = r := fun r x ↦ Set.Finite.mem_toFinset _
  have hL_pos : ∀ r, 0 < (L r).card := by
    intro r
    refine Finset.card_pos.mpr ⟨(⟨0, hk⟩, List.replicate r 0), ?_⟩
    rw [hL_mem]; simp [rk]
  let pref : ℕ → ℕ := fun r ↦ ∑ i ∈ Finset.range r, (L i).card
  have hpref_strict : StrictMono pref := by
    apply strictMono_nat_of_lt_succ
    intro r
    dsimp only [pref]
    rw [Finset.sum_range_succ]
    have := hL_pos r; omega
  have hpref_zero : pref 0 = 0 := by simp [pref]
  have hpref_unb : ∀ n : ℕ, ∃ r : ℕ, n < pref (r + 1) := by
    intro n
    refine ⟨n, ?_⟩
    have hge : ∀ r : ℕ, r ≤ pref r := by
      intro r; induction r with
      | zero => simp [pref]
      | succ r ihr =>
        dsimp only [pref] at ihr ⊢
        rw [Finset.sum_range_succ]
        have := hL_pos r; omega
    have := hge (n + 1); omega
  -- Equiv each layer L r with Fin (L r).card
  let eL : ∀ r : ℕ, Fin (L r).card ≃ L r := fun r ↦
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, Fintype.card_coe])
  -- For any n : ℕ, let layer n be the unique r with pref r ≤ n < pref (r + 1)
  have hlayer_ex : ∀ n : ℕ, ∃ r : ℕ, pref r ≤ n ∧ n < pref (r + 1) := by
    intro n
    let r := Nat.find (hpref_unb n)
    have hlt : n < pref (r + 1) := Nat.find_spec (hpref_unb n)
    have hle : pref r ≤ n := by
      cases hr : r with
      | zero => rw [hpref_zero]; exact Nat.zero_le n
      | succ r' =>
        have := Nat.find_min (hpref_unb n) (show r' < r by omega)
        omega
    exact ⟨r, hle, hlt⟩
  let layer : ℕ → ℕ := fun n ↦ Classical.choose (hlayer_ex n)
  have hlayer_spec : ∀ n, pref (layer n) ≤ n ∧ n < pref (layer n + 1) :=
    fun n ↦ Classical.choose_spec (hlayer_ex n)
  have hlayer_uniq : ∀ n r, pref r ≤ n → n < pref (r + 1) → layer n = r := by
    intro n r h1 h2
    have ⟨s1, s2⟩ := hlayer_spec n
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : pref (layer n + 1) ≤ pref r := hpref_strict.monotone (by omega)
      omega
    · have : pref (r + 1) ≤ pref (layer n) := hpref_strict.monotone (by omega)
      omega
  have hpref_step : ∀ r, pref (r + 1) = pref r + (L r).card := fun r ↦ by
    dsimp only [pref]; rw [Finset.sum_range_succ]
  let toFun : ℕ → Fin k × List ℕ := fun n ↦
    (eL (layer n) ⟨n - pref (layer n), by have hsp := hlayer_spec n; have hst := hpref_step (layer n); omega⟩).1
  let invFun : Fin k × List ℕ → ℕ := fun x ↦
    let r := rk x
    pref r + ((eL r).symm ⟨x, (hL_mem r x).mpr rfl⟩).val
  have htoFun_rk : ∀ n, rk (toFun n) = layer n := fun n ↦
    (hL_mem (layer n) (toFun n)).mp (eL (layer n) _).2
  have hleft : Function.LeftInverse invFun toFun := by
    intro n
    dsimp only [invFun]
    have hrk : rk (toFun n) = layer n := htoFun_rk n
    have heq_idx : ∀ (r' : ℕ) (hr' : rk (toFun n) = r') (hm : toFun n ∈ L r'),
        ((eL r').symm ⟨toFun n, hm⟩).val = n - pref (layer n) := by
      intro r' hr' hm
      have hr'_eq : r' = layer n := hr'.symm.trans hrk
      subst hr'_eq
      have hval : (⟨toFun n, hm⟩ : L (layer n)) =
          eL (layer n) ⟨n - pref (layer n), by have hsp := hlayer_spec n; have hst := hpref_step (layer n); omega⟩ :=
        Subtype.ext rfl
      rw [hval, (eL (layer n)).symm_apply_apply]
    rw [heq_idx (rk (toFun n)) rfl _, hrk]
    have := (hlayer_spec n).1; omega
  have hright : Function.RightInverse invFun toFun := by
    intro x
    let r := rk x
    let idx := (eL r).symm ⟨x, (hL_mem r x).mpr rfl⟩
    have hlt : pref r + idx.val < pref (r + 1) := by
      rw [hpref_step]; have := idx.isLt; omega
    have hlay : layer (invFun x) = r := hlayer_uniq (invFun x) r (Nat.le_add_right _ _) hlt
    dsimp only [toFun]
    have harg : ∀ (r' : ℕ) (hr' : r' = r) (hbound : invFun x - pref r' < (L r').card),
        (eL r' ⟨invFun x - pref r', hbound⟩).1 = x := by
      intro r' hr' hbound; subst hr'
      have hsub : (⟨invFun x - pref r, hbound⟩ : Fin (L r).card) = idx :=
        Fin.ext (by
          change (pref r + idx.val) - pref r = idx.val
          omega)
      rw [hsub]
      exact congrArg Subtype.val ((eL r).apply_symm_apply ⟨x, (hL_mem r x).mpr rfl⟩)
    exact harg (layer (invFun x)) hlay _
  refine ⟨⟨toFun, invFun, hleft, hright⟩, ?_⟩
  intro i j hlt
  change rk (toFun i) < rk (toFun j) at hlt
  rw [htoFun_rk i, htoFun_rk j] at hlt
  have h1 := (hlayer_spec i).2
  have h2 := (hlayer_spec j).1
  have h3 : pref (layer i + 1) ≤ pref (layer j) := hpref_strict.monotone (by omega)
  omega

/-- Pruned-tree BFS disjoint color-class split: given a countable color-light block `U` of order
type `ω ^ ξ` (`1 ≤ ξ < ω_ 1`) and `0 < m`, there exist `m` pairwise disjoint sets of colors
`D : Fin m → Set ι` such that `{v ∈ U | comp v ∈ D t}` has order type `ω ^ ξ` for every `t`. -/
private lemma pruned_bfs_disjoint_split_aux {V ι : Type} [LinearOrder V] [WellFoundedLT V]
    (comp : V → ι) (ξ : Ordinal.{0}) (_hξ1 : 1 ≤ ξ) (hξcnt : ξ < ω_ 1)
    (roots : Fin 1 → Set V) (hroots_type : ∀ j : Fin 1, typeLT (roots j) = ω ^ ξ)
    (hlight_u : ∀ j c, typeLT ({v ∈ roots j | comp v = c} : Set V) < ω ^ ξ)
    (m : ℕ) (hm : 0 < m) :
    ∃ D : Fin m → Set ι,
      (∀ t1 t2 : Fin m, t1 ≠ t2 → Disjoint (D t1) (D t2)) ∧
      ∀ t : Fin m, typeLT ({v ∈ roots 0 | comp v ∈ D t} : Set V) = ω ^ ξ := by
  let k : ℕ := 1
  have hk : 0 < k := Nat.one_pos
  let exps : Fin k → Ordinal.{0} := fun _ ↦ ξ
  have hexp_cnt : ∀ j : Fin k, exps j < ω_ 1 := fun _ ↦ hξcnt
  have hlight : ∀ (j : Fin k) (c : ι), typeLT ({v ∈ roots j | comp v = c} : Set V) < ω ^ exps j :=
    fun j c ↦ hlight_u j c
  let F0 : Finset ι := ∅
  -- Step 1: Fix a fundamental sequence choice for every countable ordinal 0 < α < ω_ 1
  have hfs : ∀ α : Ordinal.{0}, 0 < α → α < ω_ 1 →
      ∃ f : ℕ → Ordinal.{0}, (∀ n, f n < α) ∧
        (∀ (g : ℕ → ℕ), StrictMono g →
          ∀ (Y : ℕ → Set V),
            (∀ i j, i < j → ∀ x ∈ Y i, ∀ y ∈ Y j, x < y) →
            (∀ m, typeLT (Y m) = ω ^ f (g m)) →
            ω ^ α ≤ typeLT (⋃ m, Y m)) ∧
        (∀ (U : Set V), typeLT U = ω ^ α →
          ∃ W : ℕ → Set V,
            (∀ n, W n ⊆ U) ∧
            (∀ i j, i < j → ∀ x ∈ W i, ∀ y ∈ W j, x < y) ∧
            (∀ n, typeLT (W n) = ω ^ f n)) :=
    fun α hpos hcnt ↦ by
      obtain ⟨f, h1, h2, h3⟩ := exists_omega0_opow_decomp α hpos hcnt
      exact ⟨f, h1, fun g hg Y hord hty ↦ h2 g hg Y hord hty, fun U hU ↦ h3 U hU⟩
  choose fSeq hf_lt hf_lim hf_split using hfs
  -- Step 2: Build the pruned tree (nodeSet r, nodeOrd r) on Fin k × List ℕ by recursion on r.2
  -- A node (U, α) is monochromatic-heavy if ∃ c, typeLT {v ∈ U | comp v = c} = ω ^ α
  let IsHeavy (U : Set V) (α : Ordinal.{0}) : Prop :=
    ∃ c : ι, typeLT ({v ∈ U | comp v = c} : Set V) = ω ^ α
  -- Package node data: (U : Set V, α : Ordinal, hcnt : α < ω_ 1, hU : typeLT U = ω ^ α, hsub : U ⊆ roots j)
  let NodeData (j : Fin k) :=
    {d : Set V × Ordinal.{0} // d.2 < ω_ 1 ∧ typeLT d.1 = ω ^ d.2 ∧ d.1 ⊆ roots j}
  -- Helper: given a non-heavy NodeData d, its exponent α is > 0 (since α = 0 means singleton -> heavy!)
  have hpos_of_not_heavy : ∀ {j : Fin k} (d : NodeData j), ¬ IsHeavy d.1.1 d.1.2 → 0 < d.1.2 := by
    intro j ⟨⟨U, α⟩, _, hU, _⟩ hnheavy
    dsimp only at hU hnheavy ⊢
    by_contra hle; push Not at hle
    have hα0 : α = 0 := nonpos_iff_eq_zero.mp hle
    subst hα0
    rw [Ordinal.opow_zero] at hU
    have hne : U.Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      rw [hempty, typeLT_empty] at hU
      exact zero_ne_one hU
    obtain ⟨v0, hv0⟩ := hne
    apply hnheavy
    refine ⟨comp v0, ?_⟩
    rw [Ordinal.opow_zero]
    apply le_antisymm
    · exact (typeLT_mono (fun _ h ↦ h.1)).trans hU.le
    · rw [← typeLT_singleton v0]
      exact typeLT_mono (fun x hx ↦ by rw [Set.mem_singleton_iff] at hx; subst hx; exact ⟨hv0, rfl⟩)
  -- Child step on NodeData
  let childOf {j : Fin k} (d : NodeData j) (n : ℕ) : NodeData j :=
    if h : IsHeavy d.1.1 d.1.2 then d
    else
      have hpos : 0 < d.1.2 := hpos_of_not_heavy d h
      let W := Classical.choose (hf_split d.1.2 hpos d.2.1 d.1.1 d.2.2.1)
      have hW := Classical.choose_spec (hf_split d.1.2 hpos d.2.1 d.1.1 d.2.2.1)
      ⟨(W n, fSeq d.1.2 hpos d.2.1 n),
        (hf_lt d.1.2 hpos d.2.1 n).trans d.2.1,
        hW.2.2 n,
        (hW.1 n).trans d.2.2.2⟩
  let tree : ∀ (j : Fin k), List ℕ → NodeData j := fun j l ↦
    l.foldl (fun d n ↦ childOf d n) ⟨(roots j, exps j), hexp_cnt j, hroots_type j, Set.Subset.rfl⟩
  have htree_nil : ∀ j, tree j [] = ⟨(roots j, exps j), hexp_cnt j, hroots_type j, Set.Subset.rfl⟩ :=
    fun _ ↦ rfl
  have htree_append : ∀ j p n, tree j (p ++ [n]) = childOf (tree j p) n := by
    intro j p n; simp [tree]
  have hchild_ord : ∀ {j : Fin k} (d : NodeData j) (h : ¬ IsHeavy d.1.1 d.1.2) (n : ℕ),
      (childOf d n).1.2 = fSeq d.1.2 (hpos_of_not_heavy d h) d.2.1 n := by
    intro j d h n; simp [childOf, h]
  have hchild_sub : ∀ {j : Fin k} (d : NodeData j) (n : ℕ), (childOf d n).1.1 ⊆ d.1.1 := by
    intro j d n
    by_cases h : IsHeavy d.1.1 d.1.2
    · simp [childOf, h]
    · simp only [childOf, h, ↓reduceDIte]
      exact (Classical.choose_spec (hf_split d.1.2 (hpos_of_not_heavy d h) d.2.1 d.1.1 d.2.2.1)).1 n
  have hchild_lt : ∀ {j : Fin k} (d : NodeData j) (h : ¬ IsHeavy d.1.1 d.1.2)
      {n1 n2 : ℕ}, n1 < n2 → ∀ x ∈ (childOf d n1).1.1, ∀ y ∈ (childOf d n2).1.1, x < y := by
    intro j d h n1 n2 hlt x hx y hy
    simp only [childOf, h, ↓reduceDIte] at hx hy
    exact (Classical.choose_spec (hf_split d.1.2 (hpos_of_not_heavy d h) d.2.1 d.1.1 d.2.2.1)).2.1 n1 n2 hlt x hx y hy
  have htree_prefix_sub : ∀ j p1 p2, (tree j (p1 ++ p2)).1.1 ⊆ (tree j p1).1.1 := by
    intro j p1 p2
    induction p2 using List.reverseRecOn with
    | nil => simp
    | append_singleton p2 n ih =>
      rw [← List.append_assoc, htree_append]
      exact (hchild_sub _ n).trans ih
  let heavyCol {j : Fin k} (d : NodeData j) (h : IsHeavy d.1.1 d.1.2) : ι := Classical.choose h
  have hheavyCol_spec : ∀ {j : Fin k} (d : NodeData j) (h : IsHeavy d.1.1 d.1.2),
      typeLT ({v ∈ d.1.1 | comp v = heavyCol d h} : Set V) = ω ^ d.1.2 :=
    fun d h ↦ Classical.choose_spec h
  have hex_fresh_child : ∀ {j : Fin k} (d : NodeData j) (hn : ¬ IsHeavy d.1.1 d.1.2)
      (F : Finset ι) (N : ℕ),
      ∃ n : ℕ, N ≤ n ∧ ∀ h : IsHeavy (childOf d n).1.1 (childOf d n).1.2,
        heavyCol (childOf d n) h ∉ F := by
    intro j d hn F N
    by_contra hall; push Not at hall
    let colOf : ℕ → F := fun m ↦
      ⟨heavyCol (childOf d (N + m)) (hall (N + m) (Nat.le_add_right N m)).1,
       (hall (N + m) (Nat.le_add_right N m)).2⟩
    have hfinF : Finite F := inferInstance
    obtain ⟨⟨c, hcF⟩, hinf⟩ := Finite.exists_infinite_fiber colOf
    have hinf_set : (colOf ⁻¹' {⟨c, hcF⟩}).Infinite := Set.infinite_coe_iff.mp hinf
    have hnext : ∀ M : ℕ, ∃ m : ℕ, M < m ∧ colOf m = ⟨c, hcF⟩ := by
      intro M
      obtain ⟨m, hm, hmnot⟩ := hinf_set.exists_notMem_finset (Finset.range (M + 1))
      rw [Finset.mem_range] at hmnot
      exact ⟨m, by omega, hm⟩
    choose nextM hnext_gt hnext_eq using hnext
    let mseq : ℕ → ℕ := Nat.rec (nextM 0) (fun _ prev ↦ nextM prev)
    have hm_strict : StrictMono mseq := strictMono_nat_of_lt_succ fun i ↦ hnext_gt (mseq i)
    have hm_col : ∀ i, colOf (mseq i) = ⟨c, hcF⟩ := by
      intro i; cases i with
      | zero => exact hnext_eq 0
      | succ i => exact hnext_eq (mseq i)
    let g : ℕ → ℕ := fun i ↦ N + mseq i
    have hg_strict : StrictMono g := fun a b hab ↦ Nat.add_lt_add_left (hm_strict hab) N
    let Y : ℕ → Set V := fun i ↦ {v ∈ (childOf d (g i)).1.1 | comp v = c}
    have hYord : ∀ i1 i2, i1 < i2 → ∀ x ∈ Y i1, ∀ y ∈ Y i2, x < y := fun i1 i2 hi x hx y hy ↦
      hchild_lt d hn (hg_strict hi) x hx.1 y hy.1
    have hYtype : ∀ i, typeLT (Y i) = ω ^ fSeq d.1.2 (hpos_of_not_heavy d hn) d.2.1 (g i) := by
      intro i
      have hheav := (hall (g i) (Nat.le_add_right N (mseq i))).1
      have hceq : heavyCol (childOf d (g i)) hheav = c := congrArg Subtype.val (hm_col i)
      have hty := hheavyCol_spec (childOf d (g i)) hheav
      rw [hceq, hchild_ord d hn (g i)] at hty
      exact hty
    have hge := hf_lim d.1.2 (hpos_of_not_heavy d hn) d.2.1 g hg_strict Y hYord hYtype
    have hsub : (⋃ i, Y i) ⊆ {v ∈ d.1.1 | comp v = c} := by
      intro v hv; rw [Set.mem_iUnion] at hv
      obtain ⟨i, hi⟩ := hv
      exact ⟨hchild_sub d (g i) hi.1, hi.2⟩
    have hle : typeLT ({v ∈ d.1.1 | comp v = c} : Set V) ≤ ω ^ d.1.2 :=
      (typeLT_mono fun _ h ↦ h.1).trans d.2.2.1.le
    exact hn ⟨c, le_antisymm hle (hge.trans (typeLT_mono hsub))⟩
  -- Step 4: Breadth-first embedding φ : ℕ → Option (List ℕ) × Finset ι along rank enum e
  obtain ⟨e, he_rank⟩ := exists_rank_enum k hk
  let BFSVal := Option (List ℕ) × Finset ι
  let bfsStep : ∀ t : ℕ, (∀ s < t, BFSVal) → BFSVal := fun t prev ↦
    let Fcur : Finset ι := if h0 : t = 0 then F0 else (prev (t - 1) (by omega)).2
    let q := e t
    if hq : q.2 = [] then (some [], Fcur)
    else
      let p := q.2.dropLast
      let a := q.2.getLast hq
      have hqp : q.2 = p ++ [a] := (List.dropLast_append_getLast hq).symm
      have hp_lt : e.symm (q.1, p) < t := by
        have hrk : (e (e.symm (q.1, p))).2.length + (e (e.symm (q.1, p))).2.sum <
            (e t).2.length + (e t).2.sum := by
          simp only [Equiv.apply_symm_apply]
          change p.length + p.sum < q.2.length + q.2.sum
          rw [hqp]; simp; omega
        exact he_rank (e.symm (q.1, p)) t hrk
      match (prev (e.symm (q.1, p)) hp_lt).1 with
      | none => (none, Fcur)
      | some rp =>
        let d := tree q.1 rp
        if hd : IsHeavy d.1.1 d.1.2 then (none, Fcur)
        else
          let N : ℕ := if ha : a = 0 then 0 else
            have hsib_lt : e.symm (q.1, p ++ [a - 1]) < t := by
              have hrk : (e (e.symm (q.1, p ++ [a - 1]))).2.length + (e (e.symm (q.1, p ++ [a - 1]))).2.sum <
                  (e t).2.length + (e t).2.sum := by
                simp only [Equiv.apply_symm_apply]
                change (p ++ [a - 1]).length + (p ++ [a - 1]).sum < q.2.length + q.2.sum
                rw [hqp]; simp; omega
              exact he_rank _ t hrk
            match (prev (e.symm (q.1, p ++ [a - 1])) hsib_lt).1 with
            | none => 0
            | some rsib => rsib.getLastD 0 + 1
          let n := Classical.choose (hex_fresh_child d hd Fcur N)
          let rnew := rp ++ [n]
          let dnew := tree q.1 rnew
          if hnew : IsHeavy dnew.1.1 dnew.1.2 then
            (some rnew, insert (heavyCol dnew hnew) Fcur)
          else
            (some rnew, Fcur)
  let bfs : ℕ → BFSVal := WellFounded.fix Nat.lt_wfRel.wf bfsStep
  have hbfs_eq : ∀ t, bfs t = bfsStep t (fun s _ ↦ bfs s) :=
    fun t ↦ WellFounded.fix_eq Nat.lt_wfRel.wf bfsStep t
  let φ : Fin k × List ℕ → Option (List ℕ) := fun q ↦ (bfs (e.symm q)).1
  let Fset : ℕ → Finset ι := fun t ↦ if t = 0 then F0 else (bfs (t - 1)).2
  have hF_step_sub : ∀ t, Fset t ⊆ (bfs t).2 := by
    intro t
    have hdite_sub : ∀ (P : Prop) [Decidable P] (a b : Option (List ℕ)) (f : P → ι) (F : Finset ι),
        F ⊆ (if h : P then (a, insert (f h) F) else (b, F)).2 := by
      intro P _ a b f F; by_cases hP : P <;> simp [hP, Finset.subset_insert]
    have hF_eq : Fset t = (if h0 : t = 0 then F0 else (bfs (t - 1)).2) := by
      dsimp only [Fset]; split_ifs <;> rfl
    rw [hF_eq, hbfs_eq t]
    dsimp only [bfsStep]
    generalize (if h0 : t = 0 then F0 else (bfs (t - 1)).2) = Fcur
    by_cases hq : (e t).2 = []
    · simp only [hq, ↓reduceDIte]; exact Finset.Subset.refl _
    · simp only [hq, ↓reduceDIte]
      cases (bfs (e.symm ((e t).1, (e t).2.dropLast))).1 with
      | none => exact Finset.Subset.refl _
      | some rp =>
        dsimp only
        by_cases hd : IsHeavy (tree (e t).1 rp).1.1 (tree (e t).1 rp).1.2
        · simp only [hd, ↓reduceDIte]; exact Finset.Subset.refl _
        · simp only [hd, ↓reduceDIte]
          exact hdite_sub _ _ _ _ Fcur
  have hF_mono : ∀ {s t : ℕ}, s ≤ t → Fset s ⊆ Fset t := by
    intro s t hst
    induction hst with
    | refl => exact Finset.Subset.refl _
    | @step m hsm ih =>
      have h1 : Fset m ⊆ (bfs m).2 := hF_step_sub m
      have h2 : Fset (m + 1) = (bfs m).2 := by simp [Fset]
      rw [h2]; exact ih.trans h1
  have hF0_sub : ∀ t, F0 ⊆ Fset t := fun t ↦ by
    have : Fset 0 = F0 := by simp [Fset]
    rw [← this]; exact hF_mono (Nat.zero_le t)
  have hφ_root : ∀ j : Fin k, φ (j, []) = some [] := by
    intro j
    dsimp only [φ]
    rw [hbfs_eq (e.symm (j, []))]
    simp [bfsStep]
  have hroot_not_heavy : ∀ j : Fin k, ¬ IsHeavy (tree j []).1.1 (tree j []).1.2 := by
    intro j ⟨c, hc⟩
    rw [htree_nil] at hc
    exact ne_of_lt (hlight j c) hc
  have hφ_child : ∀ (j : Fin k) (p : List ℕ) (a : ℕ) (rp : List ℕ),
      φ (j, p) = some rp → ¬ IsHeavy (tree j rp).1.1 (tree j rp).1.2 →
      ∃ n : ℕ, φ (j, p ++ [a]) = some (rp ++ [n]) ∧
        (∀ h : IsHeavy (tree j (rp ++ [n])).1.1 (tree j (rp ++ [n])).1.2,
          heavyCol (tree j (rp ++ [n])) h ∉ Fset (e.symm (j, p ++ [a])) ∧
          heavyCol (tree j (rp ++ [n])) h ∈ (bfs (e.symm (j, p ++ [a]))).2) ∧
        (∀ (a' : ℕ) (n' : ℕ), a = a' + 1 → φ (j, p ++ [a']) = some (rp ++ [n']) → n' < n) := by
    intro j p a rp hφp hnp
    let t := e.symm (j, p ++ [a])
    have het : e t = (j, p ++ [a]) := e.apply_symm_apply _
    have hne_nil : ¬ (e t).2 = [] := by rw [het]; simp
    have hdrop : (e t).2.dropLast = p := by rw [het]; simp
    have hlast : (e t).2.getLast hne_nil = a := by
      have : ∀ (x : Fin k × List ℕ) (hx : x = (j, p ++ [a])) (hne : x.2 ≠ []),
          x.2.getLast hne = a := by rintro _ rfl _; simp
      exact this (e t) het hne_nil
    have hfst : (e t).1 = j := by rw [het]
    have hbfs_t : bfs t = bfsStep t (fun s _ ↦ bfs s) := hbfs_eq t
    dsimp only [bfsStep] at hbfs_t
    simp only [hne_nil, ↓reduceDIte] at hbfs_t
    have hp_val : (bfs (e.symm ((e t).1, (e t).2.dropLast))).1 = some rp := by
      rw [hfst, hdrop]; exact hφp
    have hnp' : ¬ IsHeavy (tree (e t).1 rp).1.1 (tree (e t).1 rp).1.2 := by rw [hfst]; exact hnp
    rw [hp_val] at hbfs_t
    dsimp only at hbfs_t
    simp only [hnp', ↓reduceDIte] at hbfs_t
    let Fcur : Finset ι := if h0 : t = 0 then F0 else (bfs (t - 1)).2
    have hFcur_eq : Fcur = Fset t := by dsimp only [Fcur, Fset]; split_ifs <;> rfl
    let N : ℕ := if ha : (e t).2.getLast hne_nil = 0 then 0 else
      match (bfs (e.symm ((e t).1, (e t).2.dropLast ++ [(e t).2.getLast hne_nil - 1]))).1 with
      | none => 0
      | some rsib => rsib.getLastD 0 + 1
    let n := Classical.choose (hex_fresh_child (tree (e t).1 rp) hnp' Fcur N)
    have hn_spec := Classical.choose_spec (hex_fresh_child (tree (e t).1 rp) hnp' Fcur N)
    refine ⟨n, ?_, ?_, ?_⟩
    · change (bfs t).1 = some (rp ++ [n])
      rw [hbfs_t]
      change (if hnew : IsHeavy (tree (e t).1 (rp ++ [n])).1.1 (tree (e t).1 (rp ++ [n])).1.2 then
          (some (rp ++ [n]), insert (heavyCol (tree (e t).1 (rp ++ [n])) hnew) Fcur)
        else (some (rp ++ [n]), Fcur)).1 = some (rp ++ [n])
      split_ifs <;> rfl
    · intro hheav
      have hheav' : IsHeavy (tree (e t).1 (rp ++ [n])).1.1 (tree (e t).1 (rp ++ [n])).1.2 := by
        rw [hfst]; exact hheav
      have hnotF : heavyCol (tree j (rp ++ [n])) hheav ∉ Fset t := by
        rw [← hFcur_eq]
        have hheav_ch : IsHeavy (childOf (tree (e t).1 rp) n).1.1 (childOf (tree (e t).1 rp) n).1.2 := by
          rw [← htree_append]; exact hheav'
        have h1 : heavyCol (childOf (tree (e t).1 rp) n) hheav_ch ∉ Fcur := hn_spec.2 hheav_ch
        have hEq : heavyCol (tree j (rp ++ [n])) hheav = heavyCol (childOf (tree (e t).1 rp) n) hheav_ch := by
          have : ∀ (j1 : Fin k) (hj1 : j1 = j) (d1 : NodeData j1) (d2 : NodeData j)
              (hd : HEq d1 d2) (h1 : IsHeavy d1.1.1 d1.1.2) (h2 : IsHeavy d2.1.1 d2.1.2),
              heavyCol d1 h1 = heavyCol d2 h2 := by
            intro j1 hj1 d1 d2 hd h1 h2; subst hj1; cases eq_of_heq hd; rfl
          exact (this (e t).1 hfst (childOf (tree (e t).1 rp) n) (tree j (rp ++ [n]))
            (by rw [← htree_append, hfst]) hheav_ch hheav).symm
        rw [hEq]; exact h1
      have hinF : heavyCol (tree j (rp ++ [n])) hheav ∈ (bfs t).2 := by
        rw [hbfs_t]
        change heavyCol (tree j (rp ++ [n])) hheav ∈
          (if hnew : IsHeavy (tree (e t).1 (rp ++ [n])).1.1 (tree (e t).1 (rp ++ [n])).1.2 then
            (some (rp ++ [n]), insert (heavyCol (tree (e t).1 (rp ++ [n])) hnew) Fcur)
           else (some (rp ++ [n]), Fcur)).2
        simp only [hheav', ↓reduceDIte]
        have hEq : heavyCol (tree j (rp ++ [n])) hheav = heavyCol (tree (e t).1 (rp ++ [n])) hheav' := by
          have : ∀ (j1 : Fin k) (hj1 : j1 = j)
              (h1 : IsHeavy (tree j1 (rp ++ [n])).1.1 (tree j1 (rp ++ [n])).1.2)
              (h2 : IsHeavy (tree j (rp ++ [n])).1.1 (tree j (rp ++ [n])).1.2),
              heavyCol (tree j1 (rp ++ [n])) h1 = heavyCol (tree j (rp ++ [n])) h2 := by
            intro j1 hj1 h1 h2; subst hj1; rfl
          exact (this (e t).1 hfst hheav' hheav).symm
        rw [hEq]
        exact Finset.mem_insert_self _ _
      exact ⟨hnotF, hinF⟩
    · intro a' n' ha_eq hφprev
      have hne0 : ¬ (e t).2.getLast hne_nil = 0 := by rw [hlast]; omega
      have hgetLastD : ∀ (l : List ℕ) (x : ℕ), (l ++ [x]).getLastD 0 = x := by
        intro l x; induction l with
        | nil => rfl
        | cons y ys ihl =>
          cases ys with
          | nil => rfl
          | cons z zs => simp [List.getLastD]
      have hN_eq : N = n' + 1 := by
        dsimp only [N]
        simp only [hfst, hdrop, hlast, ha_eq, Nat.add_sub_cancel]
        rw [dif_neg (by omega)]
        change (match φ (j, p ++ [a']) with | none => 0 | some rsib => rsib.getLastD 0 + 1) = n' + 1
        rw [hφprev]
        dsimp only
        rw [hgetLastD rp n']
      have := hn_spec.1
      omega
  have hφ_dead : ∀ (j : Fin k) (p : List ℕ) (a : ℕ),
      (φ (j, p) = none ∨ ∃ rp, φ (j, p) = some rp ∧ IsHeavy (tree j rp).1.1 (tree j rp).1.2) →
      φ (j, p ++ [a]) = none := by
    intro j p a hdead
    let t := e.symm (j, p ++ [a])
    have het : e t = (j, p ++ [a]) := e.apply_symm_apply _
    have hne_nil : ¬ (e t).2 = [] := by rw [het]; simp
    have hdrop : (e t).2.dropLast = p := by rw [het]; simp
    have hfst : (e t).1 = j := by rw [het]
    change (bfs t).1 = none
    rw [hbfs_eq t]
    dsimp only [bfsStep]
    simp only [hne_nil, ↓reduceDIte]
    rcases hdead with hnone | ⟨rp, hsome, hheav⟩
    · have hp_val : (bfs (e.symm ((e t).1, (e t).2.dropLast))).1 = none := by
        rw [hfst, hdrop]; exact hnone
      rw [hp_val]
    · have hp_val : (bfs (e.symm ((e t).1, (e t).2.dropLast))).1 = some rp := by
        rw [hfst, hdrop]; exact hsome
      rw [hp_val]
      dsimp only
      have hheav' : IsHeavy (tree (e t).1 rp).1.1 (tree (e t).1 rp).1.2 := by rw [hfst]; exact hheav
      simp [hheav']
  -- Define Leaves, leafSet, leafOrd, leafCol
  let Leaves : Set (Fin k × List ℕ) :=
    {q | ∃ r, φ q = some r ∧ IsHeavy (tree q.1 r).1.1 (tree q.1 r).1.2}
  let leafPath (q : Fin k × List ℕ) : List ℕ :=
    if h : q ∈ Leaves then Classical.choose h else []
  have hleafPath : ∀ q (h : q ∈ Leaves), φ q = some (leafPath q) ∧
      IsHeavy (tree q.1 (leafPath q)).1.1 (tree q.1 (leafPath q)).1.2 := by
    intro q h; simp only [leafPath, h, ↓reduceDIte]; exact Classical.choose_spec h
  let leafCol : Fin k × List ℕ → ι := fun q ↦
    if h : q ∈ Leaves then heavyCol (tree q.1 (leafPath q)) (hleafPath q h).2
    else comp (Classical.choice (by
      have hne : (roots ⟨0, hk⟩).Nonempty := by
        by_contra hempty; rw [Set.not_nonempty_iff_eq_empty] at hempty
        have ht := hroots_type ⟨0, hk⟩; rw [hempty, typeLT_empty] at ht
        exact (Ordinal.opow_pos _ Ordinal.omega0_pos).ne ht
      exact ⟨hne.some⟩))
  let leafOrd : Fin k × List ℕ → Ordinal.{0} := fun q ↦ (tree q.1 (leafPath q)).1.2
  let leafSet : Fin k × List ℕ → Set V := fun q ↦
    {v ∈ (tree q.1 (leafPath q)).1.1 | comp v = leafCol q}
  have hleaf_ne_nil : ∀ q ∈ Leaves, q.2 ≠ [] := by
    intro ⟨j, l⟩ hq hnil
    subst hnil
    obtain ⟨hφq, hhq⟩ := hleafPath (j, []) hq
    rw [hφ_root j] at hφq
    have hr : leafPath (j, []) = [] := Option.some.inj hφq.symm
    rw [hr] at hhq
    exact hroot_not_heavy j hhq
  have hleaf_fresh : ∀ q ∈ Leaves, leafCol q ∉ Fset (e.symm q) ∧ leafCol q ∈ (bfs (e.symm q)).2 := by
    intro ⟨j, l⟩ hq
    have hne : l ≠ [] := hleaf_ne_nil (j, l) hq
    let p := l.dropLast
    let a := l.getLast hne
    have hl_eq : l = p ++ [a] := (List.dropLast_append_getLast hne).symm
    have hparent : ∃ rp, φ (j, p) = some rp ∧ ¬ IsHeavy (tree j rp).1.1 (tree j rp).1.2 := by
      by_contra hbad; push Not at hbad
      have hdead : φ (j, p) = none ∨ ∃ rp, φ (j, p) = some rp ∧ IsHeavy (tree j rp).1.1 (tree j rp).1.2 := by
        cases hp : φ (j, p) with
        | none => exact Or.inl rfl
        | some rp => exact Or.inr ⟨rp, rfl, hbad rp hp⟩
      have hnone := hφ_dead j p a hdead
      rw [← hl_eq] at hnone
      have := (hleafPath (j, l) hq).1
      rw [hnone] at this; cases this
    obtain ⟨rp, hφp, hnp⟩ := hparent
    obtain ⟨n, hφl, hcol_prop, _⟩ := hφ_child j p a rp hφp hnp
    rw [← hl_eq] at hφl hcol_prop
    have hlp : leafPath (j, l) = rp ++ [n] := Option.some.inj ((hleafPath (j, l) hq).1.symm.trans hφl)
    have hheav : IsHeavy (tree j (rp ++ [n])).1.1 (tree j (rp ++ [n])).1.2 := by
      rw [← hlp]; exact (hleafPath (j, l) hq).2
    have hcol_eq : leafCol (j, l) = heavyCol (tree j (rp ++ [n])) hheav := by
      simp only [leafCol, hq, ↓reduceDIte]
      have : ∀ (r1 r2 : List ℕ) (hr : r1 = r2) (h1 : IsHeavy (tree j r1).1.1 (tree j r1).1.2)
          (h2 : IsHeavy (tree j r2).1.1 (tree j r2).1.2),
          heavyCol (tree j r1) h1 = heavyCol (tree j r2) h2 := by
        intro r1 r2 hr h1 h2; subst hr; rfl
      exact this (leafPath (j, l)) (rp ++ [n]) hlp _ hheav
    rw [hcol_eq]
    exact hcol_prop hheav
  have hleaf_inj : ∀ q1 ∈ Leaves, ∀ q2 ∈ Leaves, q1 ≠ q2 → leafCol q1 ≠ leafCol q2 := by
    intro q1 hq1 q2 hq2 hne heq
    have htne : e.symm q1 ≠ e.symm q2 := fun h ↦ hne (e.symm.injective h)
    rcases lt_or_gt_of_ne htne with hlt | hgt
    · have h1 : leafCol q1 ∈ (bfs (e.symm q1)).2 := (hleaf_fresh q1 hq1).2
      have h2 : (bfs (e.symm q1)).2 = Fset (e.symm q1 + 1) := by simp [Fset]
      have h3 : leafCol q1 ∈ Fset (e.symm q2) := hF_mono (by omega) (h2 ▸ h1)
      exact (hleaf_fresh q2 hq2).1 (heq ▸ h3)
    · have h1 : leafCol q2 ∈ (bfs (e.symm q2)).2 := (hleaf_fresh q2 hq2).2
      have h2 : (bfs (e.symm q2)).2 = Fset (e.symm q2 + 1) := by simp [Fset]
      have h3 : leafCol q2 ∈ Fset (e.symm q1) := hF_mono (by omega) (h2 ▸ h1)
      exact (hleaf_fresh q1 hq1).1 (heq.symm ▸ h3)
  have hleaf_type : ∀ q ∈ Leaves, typeLT (leafSet q) = ω ^ leafOrd q := by
    intro q hq
    dsimp only [leafSet, leafOrd, leafCol]
    refine (typeLT_congr_set ?_).trans (hheavyCol_spec (tree q.1 (leafPath q)) (hleafPath q hq).2)
    ext v; simp only [Set.mem_ofPred_eq, dif_pos hq]
  -- Well-founded induction on α = (tree 0 r).1.2 for subtrees of leafSet
  have hind : ∀ (α : Ordinal.{0}), ∀ (p r : List ℕ),
      φ (0, p) = some r → (tree 0 r).1.2 = α →
      let SubU := ⋃ (q : Fin k × List ℕ) (_ : q ∈ Leaves ∧ q.1 = 0 ∧ p <+: q.2), leafSet q
      SubU ⊆ (tree 0 r).1.1 ∧ typeLT SubU = ω ^ α := by
    intro α
    induction α using WellFoundedLT.induction with
    | ind α ih =>
      intro p r hφp hrord
      have hpref_φ : ∀ (s : List ℕ) (r' : List ℕ), φ (0, p ++ s) = some r' → r <+: r' := by
        intro s
        induction s using List.reverseRecOn with
        | nil =>
          intro r' h; simp only [List.append_nil] at h; rw [hφp] at h; rw [Option.some.inj h]
        | append_singleton s a ihs =>
          intro r' h
          rw [← List.append_assoc] at h
          cases hprev : φ (0, p ++ s) with
          | none =>
            have := hφ_dead 0 (p ++ s) a (Or.inl hprev)
            rw [this] at h; cases h
          | some rp' =>
            by_cases hhv : IsHeavy (tree 0 rp').1.1 (tree 0 rp').1.2
            · have := hφ_dead 0 (p ++ s) a (Or.inr ⟨rp', hprev, hhv⟩)
              rw [this] at h; cases h
            · obtain ⟨n, hchild, _, _⟩ := hφ_child 0 (p ++ s) a rp' hprev hhv
              rw [hchild] at h
              have hr'eq : rp' ++ [n] = r' := Option.some.inj h
              rw [← hr'eq]
              exact (ihs rp' hprev).trans (List.prefix_append rp' [n])
      have hSub_sub : (⋃ (q : Fin k × List ℕ) (_ : q ∈ Leaves ∧ q.1 = 0 ∧ p <+: q.2), leafSet q) ⊆
          (tree 0 r).1.1 := by
        intro x hx
        simp only [Set.mem_iUnion] at hx
        obtain ⟨q, ⟨hqL, hqj, ⟨s, hs⟩⟩, hxleaf⟩ := hx
        have hxnode : x ∈ (tree q.1 (leafPath q)).1.1 := hxleaf.1
        rcases q with ⟨jq, lq⟩
        dsimp only at hqj hs hxnode
        subst jq; subst lq
        have hφq : φ (0, p ++ s) = some (leafPath (0, p ++ s)) := (hleafPath _ hqL).1
        obtain ⟨t, ht⟩ := hpref_φ s (leafPath (0, p ++ s)) hφq
        rw [← ht] at hxnode
        exact htree_prefix_sub 0 r t hxnode
      refine ⟨hSub_sub, ?_⟩
      apply le_antisymm
      · exact (typeLT_mono hSub_sub).trans (by rw [← hrord]; exact (tree 0 r).2.2.1.le)
      · by_cases hhv : IsHeavy (tree 0 r).1.1 (tree 0 r).1.2
        · have hqL : (0, p) ∈ Leaves := ⟨r, hφp, hhv⟩
          have hlp : leafPath (0, p) = r := Option.some.inj ((hleafPath (0, p) hqL).1.symm.trans hφp)
          have hItype : typeLT (leafSet (0, p)) = ω ^ α := by
            rw [hleaf_type (0, p) hqL]
            dsimp only [leafOrd]; rw [hlp, hrord]
          rw [← hItype]
          refine typeLT_mono (fun x hx ↦ ?_)
          simp only [Set.mem_iUnion]
          exact ⟨(0, p), ⟨hqL, rfl, List.prefix_refl p⟩, hx⟩
        · have hchild_ex : ∀ a : ℕ, ∃ n : ℕ, φ (0, p ++ [a]) = some (r ++ [n]) := fun a ↦ by
            obtain ⟨n, h1, _, _⟩ := hφ_child 0 p a r hφp hhv
            exact ⟨n, h1⟩
          choose g hg_eq using hchild_ex
          have hg_strict : StrictMono g := by
            apply strictMono_nat_of_lt_succ
            intro a
            obtain ⟨n, h1, _, hlt⟩ := hφ_child 0 p (a + 1) r hφp hhv
            have hn : n = g (a + 1) := by
              have := h1.symm.trans (hg_eq (a + 1))
              exact List.append_inj_right' (Option.some.inj this) rfl |> List.singleton_injective
            rw [← hn]
            exact hlt a (g a) rfl (hg_eq a)
          let Y : ℕ → Set V := fun a ↦
            ⋃ (q : Fin k × List ℕ) (_ : q ∈ Leaves ∧ q.1 = 0 ∧ (p ++ [a]) <+: q.2), leafSet q
          have hY_props : ∀ a, Y a ⊆ (tree 0 (r ++ [g a])).1.1 ∧
              typeLT (Y a) = ω ^ fSeq (tree 0 r).1.2 (hpos_of_not_heavy (tree 0 r) hhv) (tree 0 r).2.1 (g a) := by
            intro a
            have hord_a : (tree 0 (r ++ [g a])).1.2 =
                fSeq (tree 0 r).1.2 (hpos_of_not_heavy (tree 0 r) hhv) (tree 0 r).2.1 (g a) := by
              rw [htree_append, hchild_ord (tree 0 r) hhv (g a)]
            have hlt_a : (tree 0 (r ++ [g a])).1.2 < α := by
              rw [hord_a, ← hrord]
              exact hf_lt (tree 0 r).1.2 (hpos_of_not_heavy (tree 0 r) hhv) (tree 0 r).2.1 (g a)
            have hres := ih (tree 0 (r ++ [g a])).1.2 hlt_a (p ++ [a]) (r ++ [g a]) (hg_eq a) rfl
            rw [hord_a] at hres
            exact hres
          have hYord : ∀ a1 a2, a1 < a2 → ∀ x ∈ Y a1, ∀ y ∈ Y a2, x < y := by
            intro a1 a2 ha x hx y hy
            have hx' := (hY_props a1).1 hx
            have hy' := (hY_props a2).1 hy
            rw [htree_append] at hx' hy'
            exact hchild_lt (tree 0 r) hhv (hg_strict ha) x hx' y hy'
          have hge := hf_lim (tree 0 r).1.2 (hpos_of_not_heavy (tree 0 r) hhv) (tree 0 r).2.1
            g hg_strict Y hYord (fun a ↦ (hY_props a).2)
          rw [hrord] at hge
          have hUsub : (⋃ a, Y a) ⊆ ⋃ (q : Fin k × List ℕ) (_ : q ∈ Leaves ∧ q.1 = 0 ∧ p <+: q.2), leafSet q := by
            intro x hx
            rw [Set.mem_iUnion] at hx
            obtain ⟨a, ha⟩ := hx
            simp only [Y, Set.mem_iUnion] at ha ⊢
            obtain ⟨q, ⟨hqL, hqj, hpref⟩, hxI⟩ := ha
            exact ⟨q, ⟨hqL, hqj, (List.prefix_append p [a]).trans hpref⟩, hxI⟩
          exact hge.trans (typeLT_mono hUsub)
  -- Now split depth-1 children of the root (0, []) into m residue classes modulo m
  have hroot_nh : ¬ IsHeavy (tree 0 []).1.1 (tree 0 []).1.2 := hroot_not_heavy 0
  have hchild0_ex : ∀ a : ℕ, ∃ n : ℕ, φ (0, [a]) = some [n] := fun a ↦ by
    obtain ⟨n, h1, _, _⟩ := hφ_child 0 [] a [] (hφ_root 0) hroot_nh
    exact ⟨n, h1⟩
  choose g0 hg0_eq using hchild0_ex
  have hg0_strict : StrictMono g0 := by
    apply strictMono_nat_of_lt_succ
    intro a
    obtain ⟨n, h1, _, hlt⟩ := hφ_child 0 [] (a + 1) [] (hφ_root 0) hroot_nh
    have hn : n = g0 (a + 1) := by
      have := h1.symm.trans (hg0_eq (a + 1))
      exact List.singleton_injective (Option.some.inj this)
    rw [← hn]
    exact hlt a (g0 a) rfl (hg0_eq a)
  let Y0 : ℕ → Set V := fun a ↦
    ⋃ (q : Fin k × List ℕ) (_ : q ∈ Leaves ∧ q.1 = 0 ∧ [a] <+: q.2), leafSet q
  have hY0_props : ∀ a, Y0 a ⊆ (tree 0 [g0 a]).1.1 ∧
      typeLT (Y0 a) = ω ^ fSeq (tree 0 []).1.2 (hpos_of_not_heavy (tree 0 []) hroot_nh) (tree 0 []).2.1 (g0 a) := by
    intro a
    have hord_a : (tree 0 [g0 a]).1.2 =
        fSeq (tree 0 []).1.2 (hpos_of_not_heavy (tree 0 []) hroot_nh) (tree 0 []).2.1 (g0 a) := by
      have h1 := htree_append 0 [] (g0 a)
      simp only [List.nil_append] at h1
      rw [h1, hchild_ord (tree 0 []) hroot_nh (g0 a)]
    have hres := hind (tree 0 [g0 a]).1.2 [a] [g0 a] (hg0_eq a) rfl
    rw [hord_a] at hres
    exact hres
  let D : Fin m → Set ι := fun t ↦
    {c : ι | ∃ q ∈ Leaves, q.1 = 0 ∧ (∃ i : ℕ, [m * i + t.val] <+: q.2) ∧ leafCol q = c}
  refine ⟨D, ?_, ?_⟩
  · intro t1 t2 hne
    rw [Set.disjoint_left]
    rintro c ⟨q1, hq1, _, ⟨i1, hp1⟩, hc1⟩ ⟨q2, hq2, _, ⟨i2, hp2⟩, hc2⟩
    have hqeq : q1 = q2 := by
      by_contra hqne; exact hleaf_inj q1 hq1 q2 hq2 hqne (hc1.trans hc2.symm)
    subst hqeq
    obtain ⟨s1, hs1⟩ := hp1
    obtain ⟨s2, hs2⟩ := hp2
    have hcons : (m * i1 + t1.val) :: s1 = (m * i2 + t2.val) :: s2 := by
      simpa using hs1.trans hs2.symm
    have hhead : m * i1 + t1.val = m * i2 + t2.val := (List.cons.inj hcons).1
    have hmod1 : (m * i1 + t1.val) % m = t1.val := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt t1.isLt]
    have hmod2 : (m * i2 + t2.val) % m = t2.val := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt t2.isLt]
    exact hne (Fin.ext (hmod1.symm.trans (congrArg (· % m) hhead |>.trans hmod2)))
  · intro t
    apply le_antisymm
    · exact (typeLT_mono fun _ h ↦ h.1).trans (hroots_type 0).le
    · let gt : ℕ → ℕ := fun i ↦ g0 (m * i + t.val)
      have hgt_strict : StrictMono gt := fun i1 i2 hi ↦
        hg0_strict (by have := Nat.mul_lt_mul_of_pos_left hi hm; omega)
      let Yt : ℕ → Set V := fun i ↦ Y0 (m * i + t.val)
      have hYt_ord : ∀ i1 i2, i1 < i2 → ∀ x ∈ Yt i1, ∀ y ∈ Yt i2, x < y := by
        intro i1 i2 hi x hx y hy
        have hx' := (hY0_props (m * i1 + t.val)).1 hx
        have hy' := (hY0_props (m * i2 + t.val)).1 hy
        have h1 : tree 0 [gt i1] = childOf (tree 0 []) (gt i1) := by simpa using htree_append 0 [] (gt i1)
        have h2 : tree 0 [gt i2] = childOf (tree 0 []) (gt i2) := by simpa using htree_append 0 [] (gt i2)
        rw [h1] at hx'; rw [h2] at hy'
        exact hchild_lt (tree 0 []) hroot_nh (hgt_strict hi) x hx' y hy'
      have hge := hf_lim (tree 0 []).1.2 (hpos_of_not_heavy (tree 0 []) hroot_nh) (tree 0 []).2.1
        gt hgt_strict Yt hYt_ord (fun i ↦ (hY0_props (m * i + t.val)).2)
      have hroot_ord : (tree 0 []).1.2 = ξ := rfl
      rw [hroot_ord] at hge
      have hsub : (⋃ i, Yt i) ⊆ {v ∈ roots 0 | comp v ∈ D t} := by
        intro x hx
        rw [Set.mem_iUnion] at hx
        obtain ⟨i, hi⟩ := hx
        simp only [Yt, Y0, Set.mem_iUnion] at hi
        obtain ⟨q, ⟨hqL, hq0, hpref⟩, hxleaf⟩ := hi
        have hx0 : x ∈ roots 0 := by
          have := (tree q.1 (leafPath q)).2.2.2 hxleaf.1
          rwa [hq0] at this
        exact ⟨hx0, ⟨q, hqL, hq0, ⟨i, hpref⟩, hxleaf.2.symm⟩⟩
      exact hge.trans (typeLT_mono hsub)

private lemma pruned_bfs_disjoint_split {V ι : Type} [LinearOrder V] [WellFoundedLT V]
    (comp : V → ι) (ξ : Ordinal.{0}) (hξ1 : 1 ≤ ξ) (hξcnt : ξ < ω_ 1)
    (U : Set V) (hU_type : typeLT U = ω ^ ξ)
    (hlight_u : ∀ c, typeLT ({v ∈ U | comp v = c} : Set V) < ω ^ ξ)
    (m : ℕ) (hm : 0 < m) :
    ∃ D : Fin m → Set ι,
      (∀ t1 t2 : Fin m, t1 ≠ t2 → Disjoint (D t1) (D t2)) ∧
      ∀ t : Fin m, typeLT ({v ∈ U | comp v ∈ D t} : Set V) = ω ^ ξ :=
  pruned_bfs_disjoint_split_aux comp ξ hξ1 hξcnt (fun _ ↦ U) (fun _ ↦ hU_type) (fun _ c ↦ hlight_u c) m hm

/- ### Part 4: Rayless bipartite decoupling by induction on Schmidt rank -/

/-- Helper: sum of `ω ^ η` over a nonempty list of exponents `η ≥ 1` is a limit ordinal. -/
private lemma isSuccLimit_cnf_sum : ∀ (M : List Ordinal.{0}), M ≠ [] → (∀ η ∈ M, 1 ≤ η) →
    Order.IsSuccLimit (M.map (fun η ↦ ω ^ η)).sum := by
  intro M
  induction M with
  | nil => intro h; exact absurd rfl h
  | cons a as ih =>
    intro _ hge
    simp only [List.map_cons, List.sum_cons]
    have ha_lim : Order.IsSuccLimit (ω ^ a) :=
      Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0
        (zero_lt_one.trans_le (hge a (List.mem_cons_self ..))).ne'
    by_cases has : as = []
    · subst has; simpa using ha_lim
    · exact Ordinal.isSuccLimit_add (ω ^ a) (ih has fun x hx ↦ hge x (List.mem_cons_of_mem _ hx))

/-- Core bipartite decoupling lemma: if `G` has Schmidt rank (`HasRank G`), then for ANY
well-ordered `WL` of limit order type `α` and `WR` of countable order type `ω ^ ξ`
(`1 ≤ ξ < ω_ 1`) embedding into `V`, there exist `IL ⊆ WL` of order type `α` and `IR ⊆ WR` of
order type `ω ^ ξ` with no edges of `G` between `IL` and `IR`. -/
private lemma rayless_bipartite_decouple {V : Type} {G : SimpleGraph V} (hG : HasRank G) :
    ∀ {WL WR : Type} [LinearOrder WL] [WellFoundedLT WL] [LinearOrder WR] [WellFoundedLT WR]
      (eL : WL ↪ V) (eR : WR ↪ V) (α ξ : Ordinal.{0}),
      Order.IsSuccLimit α → 1 ≤ ξ → ξ < ω_ 1 →
      typeLT WL = α → typeLT WR = ω ^ ξ →
      ∃ (IL : Set WL) (IR : Set WR),
        typeLT IL = α ∧ typeLT IR = ω ^ ξ ∧
        ∀ x ∈ IL, ∀ y ∈ IR, ¬ G.Adj (eL x) (eR y) := by
  induction hG with
  | finite G hfin =>
    intro WL WR _ _ _ _ _ eR _ ξ _ hξ1 _ _ hWR
    exfalso
    have : Finite WR := Finite.of_injective eR eR.injective
    let _ : Fintype WR := Fintype.ofFinite WR
    have hlt : typeLT WR < ω := by
      rw [Ordinal.type_fintype]
      exact Ordinal.natCast_lt_omega0 (Fintype.card WR)
    have hge : ω ≤ typeLT WR := by
      rw [hWR]
      calc ω = ω ^ (1 : Ordinal.{0}) := (Ordinal.opow_one ω).symm
        _ ≤ ω ^ ξ := Ordinal.opow_le_opow_right Ordinal.omega0_pos hξ1
    exact not_lt_of_ge hge hlt
  | sep G S hcomp ih =>
    intro WL WR _ _ _ _ eL eR α ξ hα_lim hξ1 hξcnt hWL hWR
    -- Step 1: Decompose WL \ S into Cantor normal form blocks A_0 < ... < A_{m-1}
    obtain ⟨L, hL_pair, hL_ge1, hL_sum⟩ := exists_cnf_limit α hα_lim
    have hLne : 0 < L.length := by
      by_contra h0; push Not at h0
      have hnil : L = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero h0)
      rw [hnil] at hL_sum; simp at hL_sum
      exact hα_lim.bot_lt.ne' hL_sum
    have hunivL : typeLT (Set.univ : Set WL) = (L.map (fun η ↦ ω ^ η)).sum := by
      have eu : (Set.univ : Set WL) ≃o WL := OrderIso.Set.univ
      rw [typeLT_eq_of_orderIso eu, hWL, hL_sum]
    obtain ⟨A0, _, _, hA0_ord, hA0_type⟩ := exists_split_list L (Set.univ : Set WL) hunivL
    let SL : Finset WL := S.preimage eL (fun x _ y _ h ↦ eL.injective h)
    let A : Fin L.length → Set WL := fun i ↦ A0 i \ (SL : Set WL)
    have hA_ord : ∀ i j, i < j → ∀ x ∈ A i, ∀ y ∈ A j, x < y := fun i j hij x hx y hy ↦
      hA0_ord i j hij x hx.1 y hy.1
    have hA_notS : ∀ i, ∀ x ∈ A i, eL x ∉ S := fun i x hx hS ↦
      hx.2 (Finset.mem_preimage.mpr hS)
    have hA_type : ∀ i, typeLT (A i) = ω ^ L.get i := fun i ↦
      typeLT_sdiff_finset_omega0_opow (hL_ge1 _ (List.get_mem L i)) (hA0_type i) SL
    -- Step 2: Delete S from WR to get UR of type ω ^ ξ
    let SR : Finset WR := S.preimage eR (fun x _ y _ h ↦ eR.injective h)
    let UR : Set WR := (Set.univ : Set WR) \ (SR : Set WR)
    have hUR_type : typeLT UR = ω ^ ξ := by
      have hunivR : typeLT (Set.univ : Set WR) = ω ^ ξ := by
        have eu : (Set.univ : Set WR) ≃o WR := OrderIso.Set.univ
        rw [typeLT_eq_of_orderIso eu, hWR]
      exact typeLT_sdiff_finset_omega0_opow hξ1 hunivR SR
    have hUR_notS : ∀ y ∈ UR, eR y ∉ S := fun y hy hS ↦
      hy.2 (Finset.mem_preimage.mpr hS)
    -- Step 3: Connected components of G - S
    let G' := G.induce {v | v ∉ S}
    let Comp := G'.ConnectedComponent
    have hComp_ne : Nonempty Comp := by
      have hUR_ne : UR.Nonempty := by
        by_contra hempty; rw [Set.not_nonempty_iff_eq_empty] at hempty
        rw [hempty, typeLT_empty] at hUR_type
        exact (Ordinal.opow_pos ξ Ordinal.omega0_pos).ne hUR_type
      obtain ⟨y0, hy0⟩ := hUR_ne
      exact ⟨G'.connectedComponentMk ⟨eR y0, hUR_notS y0 hy0⟩⟩
    let compL : WL → Comp := fun x ↦
      if hx : eL x ∉ S then G'.connectedComponentMk ⟨eL x, hx⟩ else Classical.choice hComp_ne
    let compR : WR → Comp := fun y ↦
      if hy : eR y ∉ S then G'.connectedComponentMk ⟨eR y, hy⟩ else Classical.choice hComp_ne
    have hcomp_adj : ∀ x : WL, ∀ y : WR, eL x ∉ S → eR y ∉ S → G.Adj (eL x) (eR y) →
        compL x = compR y := by
      intro x y hx hy hxy
      simp only [compL, compR, hx, hy]
      exact SimpleGraph.ConnectedComponent.sound (SimpleGraph.Adj.reachable (G := G') hxy)
    -- Helper: turning per-block subsets of type ω ^ L[i] into a set of type α
    have hglue_L : ∀ (IL : Set WL),
        (∀ i : Fin L.length, typeLT (IL ∩ A i : Set WL) = ω ^ L.get i) → typeLT IL = α := by
      intro IL hblock
      apply le_antisymm
      · exact (Ordinal.type_set_le IL).trans hWL.le
      · let Is : List (Set WL) := List.ofFn (fun i : Fin L.length ↦ IL ∩ A i)
        have hIs_len : Is.length = L.length := List.length_ofFn
        have hIs_sub : (⋃ k : Fin Is.length, Is.get k) ⊆ IL := by
          intro x hx; rw [Set.mem_iUnion] at hx
          obtain ⟨k, hk⟩ := hx
          simp only [Is, List.get_eq_getElem, List.getElem_ofFn] at hk
          exact hk.1
        have hIs_type : typeLT (⋃ k : Fin Is.length, Is.get k) = α := by
          rw [typeLT_biUnion_list Is, hL_sum]
          · congr 1
            apply List.ext_getElem (by simp [hIs_len])
            intro m hm1 hm2
            simp only [List.getElem_map, Is]
            exact (typeLT_congr_set (List.getElem_ofFn _)).trans
              (by simpa only [List.get_eq_getElem] using hblock ⟨m, by rw [List.length_map, hIs_len] at hm1; exact hm1⟩)
          · intro k1 k2 hk x hx y hy
            have hk1 : k1.val < L.length := hIs_len ▸ k1.isLt
            have hk2 : k2.val < L.length := hIs_len ▸ k2.isLt
            simp only [Is, List.get_eq_getElem, List.getElem_ofFn] at hx hy
            exact hA_ord ⟨k1.val, hk1⟩ ⟨k2.val, hk2⟩ (Fin.mk_lt_mk.mpr (Fin.lt_def.mp hk)) x hx.2 y hy.2
        exact hIs_type.symm.le.trans (typeLT_mono hIs_sub)
    -- Case split: is some component c0 heavy in UR?
    by_cases hheavy : ∃ c0 : Comp, typeLT ({y ∈ UR | compR y = c0} : Set WR) = ω ^ ξ
    · -- CASE 1: c0 is heavy in UR
      obtain ⟨c0, hc0_type⟩ := hheavy
      let UR' : Set WR := {y ∈ UR | compR y = c0}
      let IsBad (i : Fin L.length) : Prop := typeLT ({x ∈ A i | compL x ≠ c0} : Set WL) < ω ^ L.get i
      have hbad_c0 : ∀ i, IsBad i → typeLT ({x ∈ A i | compL x = c0} : Set WL) = ω ^ L.get i := by
        intro i hbad
        have heq : ({x ∈ A i | compL x = c0} : Set WL) = A i \ {x ∈ A i | compL x ≠ c0} := by
          ext x; simp only [Set.mem_sdiff, Set.mem_ofPred_eq]; tauto
        rw [heq]
        exact typeLT_sdiff_eq_of_lt_omega0_opow (hA_type i) hbad
      have hgood_ne : ∀ i, ¬ IsBad i → typeLT ({x ∈ A i | compL x ≠ c0} : Set WL) = ω ^ L.get i := by
        intro i hgood
        apply le_antisymm
        · exact (typeLT_mono fun _ h ↦ h.1).trans (hA_type i).le
        · exact not_lt.mp hgood
      let idxs : List (Fin L.length) := (List.finRange L.length).filter (fun i ↦ decide (IsBad i))
      have hidxs_mem : ∀ i : Fin L.length, i ∈ idxs ↔ IsBad i := by
        intro i; simp [idxs]
      by_cases hidxs_nil : idxs = []
      · -- Subcase 1a: every left block has full type outside c0
        let IL : Set WL := ⋃ i : Fin L.length, {x ∈ A i | compL x ≠ c0}
        refine ⟨IL, UR', ?_, hc0_type, ?_⟩
        · apply hglue_L IL
          intro i
          have hgood : ¬ IsBad i := fun hb ↦ by
            have := (hidxs_mem i).mpr hb
            rw [hidxs_nil] at this; cases this
          apply le_antisymm
          · exact (typeLT_mono Set.inter_subset_right).trans (hA_type i).le
          · rw [← hgood_ne i hgood]
            exact typeLT_mono (fun x hx ↦ ⟨Set.mem_iUnion.mpr ⟨i, hx⟩, hx.1⟩)
        · intro x hx y hy hadj
          rw [Set.mem_iUnion] at hx
          obtain ⟨i, hxA, hxne⟩ := hx
          exact hxne ((hcomp_adj x y (hA_notS i x hxA) (hUR_notS y hy.1) hadj).trans hy.2)
      · -- Subcase 1b: recurse ih c0 on the union of bad left blocks in c0
        have hidxs_lt : idxs.Pairwise (· < ·) :=
          (List.pairwise_lt_finRange L.length).filter _
        let Lc : List Ordinal.{0} := idxs.map L.get
        have hLc_pair : Lc.Pairwise (· ≥ ·) := by
          have hL_anti : ∀ i j : Fin L.length, i < j → L.get i ≥ L.get j := by
            intro i j hij
            have := List.pairwise_iff_get.mp hL_pair
            exact this i j hij
          exact hidxs_lt.map L.get (fun a b hab ↦ hL_anti a b hab)
        have hLc_ge1 : ∀ η ∈ Lc, 1 ≤ η := by
          intro η hη; rw [List.mem_map] at hη
          obtain ⟨i, _, rfl⟩ := hη; exact hL_ge1 _ (List.get_mem L i)
        have hLc_ne : Lc ≠ [] := fun h ↦ hidxs_nil (List.map_eq_nil_iff.mp h)
        let αc : Ordinal.{0} := (Lc.map (fun η ↦ ω ^ η)).sum
        have hαc_lim : Order.IsSuccLimit αc := isSuccLimit_cnf_sum Lc hLc_ne hLc_ge1
        let Bc : Fin Lc.length → Set WL := fun k ↦
          {x ∈ A (idxs.get ⟨k.val, by simpa [Lc] using k.isLt⟩) | compL x = c0}
        have hBc_ord : ∀ k1 k2 : Fin Lc.length, k1 < k2 → ∀ x ∈ Bc k1, ∀ y ∈ Bc k2, x < y := by
          intro k1 k2 hk x hx y hy
          have hk1 : k1.val < idxs.length := by simpa [Lc] using k1.isLt
          have hk2 : k2.val < idxs.length := by simpa [Lc] using k2.isLt
          have hlt_i : idxs.get ⟨k1.val, hk1⟩ < idxs.get ⟨k2.val, hk2⟩ :=
            List.pairwise_iff_get.mp hidxs_lt ⟨k1.val, hk1⟩ ⟨k2.val, hk2⟩ (Fin.mk_lt_mk.mpr (Fin.lt_def.mp hk))
          exact hA_ord _ _ hlt_i x hx.1 y hy.1
        have hBc_type : ∀ k : Fin Lc.length, typeLT (Bc k) = ω ^ Lc.get k := by
          intro k
          have hk : k.val < idxs.length := by simpa [Lc] using k.isLt
          have hbad : IsBad (idxs.get ⟨k.val, hk⟩) := (hidxs_mem _).mp (List.get_mem idxs ⟨k.val, hk⟩)
          have hget : Lc.get k = L.get (idxs.get ⟨k.val, hk⟩) := by simp [Lc]
          rw [hget]
          exact hbad_c0 _ hbad
        let Uc : Set WL := ⋃ k : Fin Lc.length, Bc k
        have hUc_type : typeLT Uc = αc := by
          let Bs : List (Set WL) := List.ofFn Bc
          have hBs_len : Bs.length = Lc.length := List.length_ofFn
          have hUeq : Uc = ⋃ k : Fin Bs.length, Bs.get k := by
            ext x; simp only [Uc, Set.mem_iUnion]
            constructor
            · rintro ⟨k, hk⟩
              refine ⟨⟨k.val, hBs_len.symm ▸ k.isLt⟩, ?_⟩
              simpa [Bs] using hk
            · rintro ⟨k, hk⟩
              refine ⟨⟨k.val, hBs_len ▸ k.isLt⟩, ?_⟩
              simpa [Bs] using hk
          rw [hUeq, typeLT_biUnion_list Bs]
          · congr 1
            apply List.ext_getElem (by simp [hBs_len])
            intro m hm1 hm2
            simp only [List.getElem_map, Bs]
            exact (typeLT_congr_set (List.getElem_ofFn _)).trans
              (by simpa only [List.get_eq_getElem] using hBc_type ⟨m, by rw [List.length_map, hBs_len] at hm1; exact hm1⟩)
          · intro k1 k2 hk x hx y hy
            have hk1 : k1.val < Lc.length := hBs_len ▸ k1.isLt
            have hk2 : k2.val < Lc.length := hBs_len ▸ k2.isLt
            simp only [Bs, List.get_eq_getElem, List.getElem_ofFn] at hx hy
            exact hBc_ord ⟨k1.val, hk1⟩ ⟨k2.val, hk2⟩ (Fin.mk_lt_mk.mpr (Fin.lt_def.mp hk)) x hx y hy
        have hUc_in : ∀ x ∈ Uc, eL x ∉ S ∧ compL x = c0 := by
          intro x hx; rw [Set.mem_iUnion] at hx
          obtain ⟨k, hxA, hxc⟩ := hx
          exact ⟨hA_notS _ x hxA, hxc⟩
        let Vc := {v | ∃ hv : v ∉ S, G'.connectedComponentMk ⟨v, hv⟩ = c0}
        let eUc : Uc ↪ Vc :=
          ⟨fun x ↦ ⟨eL x.1, (hUc_in x.1 x.2).1, by
              have := (hUc_in x.1 x.2).2
              simpa [compL, (hUc_in x.1 x.2).1] using this⟩,
           fun _ _ h ↦ Subtype.ext (eL.injective (congrArg Subtype.val h))⟩
        let eUR' : UR' ↪ Vc :=
          ⟨fun y ↦ ⟨eR y.1, hUR_notS y.1 y.2.1, by
              have := y.2.2
              simpa [compR, hUR_notS y.1 y.2.1] using this⟩,
           fun _ _ h ↦ Subtype.ext (eR.injective (congrArg Subtype.val h))⟩
        obtain ⟨ILc_sub, IR_sub, hILc_sub_ty, hIR_sub_ty, hno_edge_c0⟩ :=
          ih c0 eUc eUR' αc ξ hαc_lim hξ1 hξcnt hUc_type hc0_type
        let ILc : Set WL := Subtype.val '' ILc_sub
        let IR : Set WR := Subtype.val '' IR_sub
        have hILc_ty : typeLT ILc = αc := by
          have hiso : ILc_sub ≃o ILc :=
            { toFun := fun x ↦ ⟨x.1.1, ⟨x.1, x.2, rfl⟩⟩
              invFun := fun y ↦ ⟨⟨y.1, by obtain ⟨a, _, ha⟩ := y.2; rw [← ha]; exact a.2⟩,
                by obtain ⟨a, haI, ha⟩ := y.2
                   have heq : (⟨y.1, by rw [← ha]; exact a.2⟩ : Uc) = a := Subtype.ext ha.symm
                   rw [heq]; exact haI⟩
              left_inv := fun ⟨⟨_, _⟩, _⟩ ↦ rfl
              right_inv := fun ⟨_, _⟩ ↦ rfl
              map_rel_iff' := by rintro ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩; exact Iff.rfl }
          rw [← typeLT_eq_of_orderIso hiso, hILc_sub_ty]
        have hIR_ty : typeLT IR = ω ^ ξ := by
          have hiso : IR_sub ≃o IR :=
            { toFun := fun y ↦ ⟨y.1.1, ⟨y.1, y.2, rfl⟩⟩
              invFun := fun z ↦ ⟨⟨z.1, by obtain ⟨a, _, ha⟩ := z.2; rw [← ha]; exact a.2⟩,
                by obtain ⟨a, haI, ha⟩ := z.2
                   have heq : (⟨z.1, by rw [← ha]; exact a.2⟩ : UR') = a := Subtype.ext ha.symm
                   rw [heq]; exact haI⟩
              left_inv := fun ⟨⟨_, _⟩, _⟩ ↦ rfl
              right_inv := fun ⟨_, _⟩ ↦ rfl
              map_rel_iff' := by rintro ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩; exact Iff.rfl }
          rw [← typeLT_eq_of_orderIso hiso, hIR_sub_ty]
        have hILc_sub_Uc : ILc ⊆ Uc := by rintro _ ⟨a, _, rfl⟩; exact a.2
        have hIR_sub_UR' : IR ⊆ UR' := by rintro _ ⟨b, _, rfl⟩; exact b.2
        let IL : Set WL := ILc ∪ (⋃ (i : Fin L.length) (_ : ¬ IsBad i), {x ∈ A i | compL x ≠ c0})
        refine ⟨IL, IR, ?_, hIR_ty, ?_⟩
        · apply hglue_L IL
          intro i
          apply le_antisymm
          · exact (typeLT_mono Set.inter_subset_right).trans (hA_type i).le
          · by_cases hbad : IsBad i
            · have hi_mem : i ∈ idxs := (hidxs_mem i).mpr hbad
              obtain ⟨k_idx, hk_eq⟩ := List.mem_iff_get.mp hi_mem
              let k : Fin Lc.length := ⟨k_idx.val, by simp [Lc]⟩
              have hrig := cnf_sum_rigid Lc hLc_pair Bc hBc_ord hBc_type ILc hILc_sub_Uc hILc_ty k
              have hLck : Lc.get k = L.get i := by
                simp only [Lc, List.get_eq_getElem, List.getElem_map]
                exact congrArg L.get hk_eq
              have hBck_sub : Bc k ⊆ A i := by
                intro x hx; dsimp only [Bc] at hx
                have : idxs.get ⟨k.val, _⟩ = i := hk_eq
                rw [this] at hx; exact hx.1
              rw [hLck] at hrig
              rw [← hrig]
              exact typeLT_mono (fun x ⟨hx1, hx2⟩ ↦ ⟨Or.inl hx1, hBck_sub hx2⟩)
            · rw [← hgood_ne i hbad]
              exact typeLT_mono (fun x hx ↦ ⟨Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hbad, hx⟩⟩), hx.1⟩)
        · intro x hx y hy hadj
          rcases hx with hxC | hxG
          · obtain ⟨a, haI, rfl⟩ := hxC
            obtain ⟨b, hbI, rfl⟩ := hy
            exact hno_edge_c0 a haI b hbI hadj
          · simp only [Set.mem_iUnion] at hxG
            obtain ⟨i, _, hxA, hxne⟩ := hxG
            have hy' : y ∈ UR' := hIR_sub_UR' hy
            exact hxne ((hcomp_adj x y (hA_notS i x hxA) (hUR_notS y hy'.1) hadj).trans hy'.2)
    · -- CASE 2: UR is component-light -> pruned_bfs_disjoint_split + pigeonhole
      have hlight : ∀ c : Comp, typeLT ({y ∈ UR | compR y = c} : Set WR) < ω ^ ξ := by
        intro c
        have hle : typeLT ({y ∈ UR | compR y = c} : Set WR) ≤ ω ^ ξ :=
          (typeLT_mono fun _ h ↦ h.1).trans hUR_type.le
        exact lt_of_le_of_ne hle (fun heq ↦ hheavy ⟨c, heq⟩)
      obtain ⟨D, hD_disj, hD_type⟩ :=
        pruned_bfs_disjoint_split compR ξ hξ1 hξcnt UR hUR_type hlight (L.length + 1) (Nat.succ_pos _)
      -- Each left block i has at most one t where {x ∈ A i | compL x ∉ D t} drops below ω ^ L[i]
      have hat_most_one : ∀ (i : Fin L.length) (t1 t2 : Fin (L.length + 1)),
          typeLT ({x ∈ A i | compL x ∉ D t1} : Set WL) < ω ^ L.get i →
          typeLT ({x ∈ A i | compL x ∉ D t2} : Set WL) < ω ^ L.get i →
          t1 = t2 := by
        intro i t1 t2 h1 h2
        by_contra hne
        have hcov : A i ⊆ ({x ∈ A i | compL x ∉ D t1} : Set WL) ∪ {x ∈ A i | compL x ∉ D t2} := by
          intro x hxA
          by_cases hmem : compL x ∈ D t1
          · exact Or.inr ⟨hxA, Set.disjoint_left.mp (hD_disj t1 t2 hne) hmem⟩
          · exact Or.inl ⟨hxA, hmem⟩
        have hlt := (typeLT_mono hcov).trans_lt (typeLT_union_lt_omega0_opow (L.get i) h1 h2)
        exact lt_irrefl _ ((hA_type i) ▸ hlt)
      let badT : Fin L.length → Fin (L.length + 1) := fun i ↦
        if h : ∃ t : Fin (L.length + 1), typeLT ({x ∈ A i | compL x ∉ D t} : Set WL) < ω ^ L.get i
        then Classical.choose h
        else 0
      have hex_good_t : ∃ t0 : Fin (L.length + 1), t0 ∉ Finset.univ.image badT := by
        have hcard : (Finset.univ.image badT).card < (Finset.univ : Finset (Fin (L.length + 1))).card := by
          calc (Finset.univ.image badT).card ≤ (Finset.univ : Finset (Fin L.length)).card := Finset.card_image_le
            _ = L.length := Finset.card_fin _
            _ < L.length + 1 := Nat.lt_succ_self _
            _ = (Finset.univ : Finset (Fin (L.length + 1))).card := (Finset.card_fin _).symm
        obtain ⟨t0, _, ht0⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
        exact ⟨t0, ht0⟩
      obtain ⟨t0, ht0_not⟩ := hex_good_t
      have hgood_t0 : ∀ i : Fin L.length, typeLT ({x ∈ A i | compL x ∉ D t0} : Set WL) = ω ^ L.get i := by
        intro i
        apply le_antisymm
        · exact (typeLT_mono fun _ h ↦ h.1).trans (hA_type i).le
        · by_contra hlt; push Not at hlt
          have hex : ∃ t : Fin (L.length + 1), typeLT ({x ∈ A i | compL x ∉ D t} : Set WL) < ω ^ L.get i :=
            ⟨t0, hlt⟩
          have hbad_eq : badT i = t0 := by
            have hspec : typeLT ({x ∈ A i | compL x ∉ D (Classical.choose hex)} : Set WL) < ω ^ L.get i :=
              Classical.choose_spec hex
            have heq := hat_most_one i (Classical.choose hex) t0 hspec hlt
            simpa only [badT, dif_pos hex] using heq
          exact ht0_not (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hbad_eq⟩)
      let IL : Set WL := ⋃ i : Fin L.length, {x ∈ A i | compL x ∉ D t0}
      let IR : Set WR := {y ∈ UR | compR y ∈ D t0}
      refine ⟨IL, IR, ?_, hD_type t0, ?_⟩
      · apply hglue_L IL
        intro i
        apply le_antisymm
        · exact (typeLT_mono Set.inter_subset_right).trans (hA_type i).le
        · rw [← hgood_t0 i]
          exact typeLT_mono (fun x hx ↦ ⟨Set.mem_iUnion.mpr ⟨i, hx⟩, hx.1⟩)
      · intro x hx y hy hadj
        rw [Set.mem_iUnion] at hx
        obtain ⟨i, hxA, hxnotD⟩ := hx
        exact hxnotD ((hcomp_adj x y (hA_notS i x hxA) (hUR_notS y hy.1) hadj) ▸ hy.2)

/-- Iterate `rayless_bipartite_decouple` over a finite list of consecutive countable right blocks. -/
private lemma rayless_bipartite_decouple_list {V : Type} [LinearOrder V] [WellFoundedLT V]
    {G : SimpleGraph V} (hG : HasRank G) (α : Ordinal.{0}) (hα_lim : Order.IsSuccLimit α) :
    ∀ (M : List Ordinal.{0}), (∀ ξ ∈ M, 1 ≤ ξ ∧ ξ < ω_ 1) →
      ∀ (WL : Set V) (Bs : Fin M.length → Set V),
        typeLT WL = α →
        (∀ j, typeLT (Bs j) = ω ^ M.get j) →
        ∃ (IL : Set V) (IRs : Fin M.length → Set V),
          IL ⊆ WL ∧ typeLT IL = α ∧
          (∀ j, IRs j ⊆ Bs j ∧ typeLT (IRs j) = ω ^ M.get j) ∧
          ∀ x ∈ IL, ∀ j, ∀ y ∈ IRs j, ¬ G.Adj x y := by
  intro M
  induction M with
  | nil =>
    intro _ WL _ hWL _
    exact ⟨WL, Fin.elim0, Set.Subset.rfl, hWL, fun j ↦ j.elim0, fun _ _ j ↦ j.elim0⟩
  | cons ξ M' ih =>
    intro hM WL Bs hWL hBs
    have hξ := hM ξ (List.mem_cons_self ..)
    obtain ⟨IL1_sub, IR0_sub, hIL1_ty, hIR0_ty, hno0⟩ :=
      rayless_bipartite_decouple hG (Function.Embedding.subtype (· ∈ WL))
        (Function.Embedding.subtype (· ∈ Bs 0)) α ξ hα_lim hξ.1 hξ.2 hWL (hBs 0)
    let IL1 : Set V := Subtype.val '' IL1_sub
    let IR0 : Set V := Subtype.val '' IR0_sub
    have hIL1_set_ty : typeLT IL1 = α := by
      have hiso : IL1_sub ≃o IL1 :=
        { toFun := fun x ↦ ⟨x.1.1, ⟨x.1, x.2, rfl⟩⟩
          invFun := fun y ↦ ⟨⟨y.1, by obtain ⟨a, _, ha⟩ := y.2; rw [← ha]; exact a.2⟩,
            by obtain ⟨a, haI, ha⟩ := y.2
               have heq : (⟨y.1, by rw [← ha]; exact a.2⟩ : WL) = a := Subtype.ext ha.symm
               rw [heq]; exact haI⟩
          left_inv := fun ⟨⟨_, _⟩, _⟩ ↦ rfl
          right_inv := fun ⟨_, _⟩ ↦ rfl
          map_rel_iff' := by rintro ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩; exact Iff.rfl }
      rw [← typeLT_eq_of_orderIso hiso, hIL1_ty]
    have hIR0_set_ty : typeLT IR0 = ω ^ ξ := by
      have hiso : IR0_sub ≃o IR0 :=
        { toFun := fun y ↦ ⟨y.1.1, ⟨y.1, y.2, rfl⟩⟩
          invFun := fun z ↦ ⟨⟨z.1, by obtain ⟨a, _, ha⟩ := z.2; rw [← ha]; exact a.2⟩,
            by obtain ⟨a, haI, ha⟩ := z.2
               have heq : (⟨z.1, by rw [← ha]; exact a.2⟩ : Bs 0) = a := Subtype.ext ha.symm
               rw [heq]; exact haI⟩
          left_inv := fun ⟨⟨_, _⟩, _⟩ ↦ rfl
          right_inv := fun ⟨_, _⟩ ↦ rfl
          map_rel_iff' := by rintro ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩; exact Iff.rfl }
      rw [← typeLT_eq_of_orderIso hiso, hIR0_ty]
    have hIL1_sub_WL : IL1 ⊆ WL := by rintro _ ⟨a, _, rfl⟩; exact a.2
    have hIR0_sub_B0 : IR0 ⊆ Bs 0 := by rintro _ ⟨b, _, rfl⟩; exact b.2
    obtain ⟨IL2, IRs', hIL2_sub, hIL2_ty, hIRs'_spec, hno'⟩ :=
      ih (fun η hη ↦ hM η (List.mem_cons_of_mem _ hη)) IL1 (fun j ↦ Bs j.succ) hIL1_set_ty (fun j ↦ hBs j.succ)
    refine ⟨IL2, Fin.cases IR0 IRs', hIL2_sub.trans hIL1_sub_WL, hIL2_ty, ?_, ?_⟩
    · intro j
      cases j using Fin.cases with
      | zero => exact ⟨hIR0_sub_B0, hIR0_set_ty⟩
      | succ k => exact hIRs'_spec k
    · intro x hx j
      cases j using Fin.cases with
      | zero =>
        intro y hy
        obtain ⟨a, haI, rfl⟩ := hIL2_sub hx
        obtain ⟨b, hbI, rfl⟩ := hy
        exact hno0 a haI b hbI
      | succ k => exact hno' x hx k

end OMA.P_Erdos601_erdos_601_variants_erdos_hajnal_milner_1970_R1_H3

open Ordinal Cardinal SimpleGraph Erdos601
open OMA.P_Erdos601_erdos_601_variants_erdos_hajnal_milner_1970_R1_H3

theorem OMA.solution : OMA.R_Erdos601_erdos_601_variants_erdos_hajnal_milner_1970_R1.H3 := by
  intro γ β hγ hβ_cnt hβ_lim _ hA hB G
  by_cases hray : HasInfPath G
  · exact Or.inl hray
  · right
    have hG : HasRank G := rayless_hasRank G hray
    let V := (ω_ 1 * γ + β).ToType
    have huniv : typeLT (Set.univ : Set V) = ω_ 1 * γ + β := by
      have eu : (Set.univ : Set V) ≃o V := OrderIso.Set.univ
      rw [typeLT_eq_of_orderIso eu, Ordinal.type_toType]
    obtain ⟨A, B, _, _, _, hAB_lt, hA_ty, hB_ty⟩ := exists_split_of_typeLT_add huniv
    obtain ⟨M, _, hM_ge1, hM_sum⟩ := exists_cnf_limit β hβ_lim
    have hM_cnt : ∀ ξ ∈ M, 1 ≤ ξ ∧ ξ < ω_ 1 := by
      intro ξ hξ
      refine ⟨hM_ge1 ξ hξ, ?_⟩
      have hpow_le : ω ^ ξ ≤ β := by
        rw [hM_sum]
        exact List.le_sum_of_mem (List.mem_map.mpr ⟨ξ, hξ, rfl⟩)
      exact (Ordinal.right_le_opow ξ Ordinal.one_lt_omega0).trans_lt (hpow_le.trans_lt hβ_cnt)
    obtain ⟨Bs, hBs_sub, _, hBs_ord, hBs_ty⟩ := exists_split_list M B (hB_ty.trans hM_sum)
    have hα_lim : Order.IsSuccLimit (ω_ 1 * γ) :=
      Ordinal.isSuccLimit_mul_left (Cardinal.isSuccLimit_omega 1) (pos_iff_ne_zero.mpr hγ)
    obtain ⟨IL, IRs, hIL_sub, hIL_ty, hIRs_spec, hno_edge⟩ :=
      rayless_bipartite_decouple_list hG (ω_ 1 * γ) hα_lim M hM_cnt A Bs hA_ty hBs_ty
    let IR : Set V := ⋃ j : Fin M.length, IRs j
    have hIR_sub : IR ⊆ B := by
      intro y hy; rw [Set.mem_iUnion] at hy
      obtain ⟨j, hj⟩ := hy
      exact hBs_sub j ((hIRs_spec j).1 hj)
    have hIR_ty : typeLT IR = β := by
      let Rs : List (Set V) := List.ofFn IRs
      have hRs_len : Rs.length = M.length := List.length_ofFn
      have hUeq : IR = ⋃ k : Fin Rs.length, Rs.get k := by
        ext y; simp only [IR, Set.mem_iUnion]
        constructor
        · rintro ⟨j, hj⟩
          refine ⟨⟨j.val, hRs_len.symm ▸ j.isLt⟩, ?_⟩
          simpa [Rs] using hj
        · rintro ⟨k, hk⟩
          refine ⟨⟨k.val, hRs_len ▸ k.isLt⟩, ?_⟩
          simpa [Rs] using hk
      rw [hUeq, typeLT_biUnion_list Rs]
      · conv_rhs => rw [hM_sum]
        congr 1
        apply List.ext_getElem (by simp [hRs_len])
        intro m hm1 hm2
        simp only [List.getElem_map, Rs]
        exact (typeLT_congr_set (List.getElem_ofFn _)).trans
          (by simpa only [List.get_eq_getElem] using (hIRs_spec ⟨m, by rw [List.length_map, hRs_len] at hm1; exact hm1⟩).2)
      · intro k1 k2 hk x hx y hy
        have hk1 : k1.val < M.length := hRs_len ▸ k1.isLt
        have hk2 : k2.val < M.length := hRs_len ▸ k2.isLt
        simp only [Rs, List.get_eq_getElem, List.getElem_ofFn] at hx hy
        exact hBs_ord ⟨k1.val, hk1⟩ ⟨k2.val, hk2⟩ (Fin.mk_lt_mk.mpr (Fin.lt_def.mp hk))
          x ((hIRs_spec _).1 hx) y ((hIRs_spec _).1 hy)
    -- Transport hA to IL and hB to IR
    have heqL : Ordinal.type (· < · : (ω_ 1 * γ).ToType → _ → Prop) = typeLT IL := by
      rw [Ordinal.type_toType, hIL_ty]
    obtain ⟨eL_rel⟩ := Ordinal.type_eq.mp heqL
    let eL_iso : (ω_ 1 * γ).ToType ≃o IL := OrderIso.ofRelIsoLT eL_rel
    let G_L : SimpleGraph (ω_ 1 * γ).ToType := G.comap (fun x ↦ (eL_iso x).1)
    have hG_L_no : ¬ HasInfPath G_L := by
      rintro ⟨f, hfinj, hfadj⟩
      exact hray ⟨fun n ↦ (eL_iso (f n)).1,
        fun i j h ↦ hfinj (eL_iso.injective (Subtype.ext h)), hfadj⟩
    rcases hA G_L with hpathL | ⟨S1, hS1_ind, hS1_ty⟩
    · exact absurd hpathL hG_L_no
    have heqR : Ordinal.type (· < · : β.ToType → _ → Prop) = typeLT IR := by
      rw [Ordinal.type_toType, hIR_ty]
    obtain ⟨eR_rel⟩ := Ordinal.type_eq.mp heqR
    let eR_iso : β.ToType ≃o IR := OrderIso.ofRelIsoLT eR_rel
    let G_R : SimpleGraph β.ToType := G.comap (fun y ↦ (eR_iso y).1)
    have hG_R_no : ¬ HasInfPath G_R := by
      rintro ⟨f, hfinj, hfadj⟩
      exact hray ⟨fun n ↦ (eR_iso (f n)).1,
        fun i j h ↦ hfinj (eR_iso.injective (Subtype.ext h)), hfadj⟩
    rcases hB G_R with hpathR | ⟨S2, hS2_ind, hS2_ty⟩
    · exact absurd hpathR hG_R_no
    let I1 : Set V := (fun x ↦ (eL_iso x).1) '' S1
    let I2 : Set V := (fun y ↦ (eR_iso y).1) '' S2
    have hI1_sub : I1 ⊆ IL := by rintro _ ⟨a, _, rfl⟩; exact (eL_iso a).2
    have hI2_sub : I2 ⊆ IR := by rintro _ ⟨b, _, rfl⟩; exact (eR_iso b).2
    have hI1_ty : typeLT I1 = ω_ 1 * γ := by
      have hiso : S1 ≃o I1 :=
        { toFun := fun a ↦ ⟨(eL_iso a.1).1, ⟨a.1, a.2, rfl⟩⟩
          invFun := fun x ↦ ⟨eL_iso.symm ⟨x.1, hI1_sub x.2⟩, by
            obtain ⟨a, ha, hax⟩ := x.2
            have heq : (⟨x.1, hI1_sub x.2⟩ : IL) = eL_iso a := Subtype.ext hax.symm
            rw [heq, eL_iso.symm_apply_apply]; exact ha⟩
          left_inv := fun ⟨a, _⟩ ↦ Subtype.ext (by simp)
          right_inv := fun ⟨x, hx⟩ ↦ Subtype.ext (by
            have := congrArg Subtype.val (eL_iso.apply_symm_apply ⟨x, hI1_sub hx⟩)
            exact this)
          map_rel_iff' := by
            rintro ⟨a1, _⟩ ⟨a2, _⟩
            exact eL_iso.le_iff_le }
      rw [← typeLT_eq_of_orderIso hiso, hS1_ty]
    have hI2_ty : typeLT I2 = β := by
      have hiso : S2 ≃o I2 :=
        { toFun := fun b ↦ ⟨(eR_iso b.1).1, ⟨b.1, b.2, rfl⟩⟩
          invFun := fun y ↦ ⟨eR_iso.symm ⟨y.1, hI2_sub y.2⟩, by
            obtain ⟨b, hb, hby⟩ := y.2
            have heq : (⟨y.1, hI2_sub y.2⟩ : IR) = eR_iso b := Subtype.ext hby.symm
            rw [heq, eR_iso.symm_apply_apply]; exact hb⟩
          left_inv := fun ⟨b, _⟩ ↦ Subtype.ext (by simp)
          right_inv := fun ⟨y, hy⟩ ↦ Subtype.ext (by
            have := congrArg Subtype.val (eR_iso.apply_symm_apply ⟨y, hI2_sub hy⟩)
            exact this)
          map_rel_iff' := by
            rintro ⟨b1, _⟩ ⟨b2, _⟩
            exact eR_iso.le_iff_le }
      rw [← typeLT_eq_of_orderIso hiso, hS2_ty]
    refine ⟨I1 ∪ I2, ?_, ?_⟩
    · rw [SimpleGraph.isIndepSet_iff]
      intro x hx y hy hne hadj
      rcases hx with hx1 | hx2 <;> rcases hy with hy1 | hy2
      · obtain ⟨a1, ha1, rfl⟩ := hx1
        obtain ⟨a2, ha2, rfl⟩ := hy1
        have hane : a1 ≠ a2 := fun h ↦ hne (congrArg (fun a ↦ (eL_iso a).1) h)
        exact (SimpleGraph.isIndepSet_iff _).mp hS1_ind ha1 ha2 hane hadj
      · have hxL : x ∈ IL := hI1_sub hx1
        have hyR : y ∈ IR := hI2_sub hy2
        rw [Set.mem_iUnion] at hyR
        obtain ⟨j, hj⟩ := hyR
        exact hno_edge x hxL j y hj hadj
      · have hyL : y ∈ IL := hI1_sub hy1
        have hxR : x ∈ IR := hI2_sub hx2
        rw [Set.mem_iUnion] at hxR
        obtain ⟨j, hj⟩ := hxR
        exact hno_edge y hyL j x hj hadj.symm
      · obtain ⟨b1, hb1, rfl⟩ := hx2
        obtain ⟨b2, hb2, rfl⟩ := hy2
        have hbne : b1 ≠ b2 := fun h ↦ hne (congrArg (fun b ↦ (eR_iso b).1) h)
        exact (SimpleGraph.isIndepSet_iff _).mp hS2_ind hb1 hb2 hbne hadj
    · rw [typeLT_union_of_lt (fun x hx y hy ↦ hAB_lt x (hIL_sub (hI1_sub hx)) y (hIR_sub (hI2_sub hy)))]
      rw [hI1_ty, hI2_ty]
