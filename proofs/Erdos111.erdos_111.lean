import FormalConjectures.ErdosProblems.«111»
import Mathlib

-- Erdos Problem 111: if G has chromatic number aleph one then h_G(n) / n tends to infinity.
--
-- The mathematics below is NOT the work of the submitter. It is the proof published by
-- Plasma AI, ported to the statement pinned on this site:
--
--   Source: https://github.com/plasma-ai/erdos-111
--   Commit: de72caf0e388c729697b6813f4ea90bfe1617c7b (registered in the Palomar registry as
--   PALOMAR-2026-10-19-000007)
--   Authors: Plasma AI, as credited in that repository (its README says the proof was found
--   by two AI models and formalised in Lean under human direction).
--   Licence: Apache License, Version 2.0, http://www.apache.org/licenses/LICENSE-2.0
--   Used here under the terms of that licence.
--
-- Changes made to the source: the modules reachable from Solution.lean are concatenated in
-- dependency order into this one file; the module, import and public section lines are
-- removed; the namespace Erdos111 of the source is renamed PlasmaE111, because the pinned
-- Formal Conjectures file already declares Erdos111.erdos_111; repeated universe lines are
-- dropped; and two lemma names of the newer Mathlib used by the source are replaced by their
-- names in the Mathlib pinned here (dite_eq_left by dif_pos, Measurable.of_eval by
-- measurable_pi_lambda), with the function of one measurable_from_top made explicit. Nothing
-- else is changed in that part.
--
-- New here (namespace OMA.E111Bridge and OMA.solution): the source states the theorem with
-- its own quantity h G n, a supremum over all subgraphs on n vertices of the number of edge
-- deletions that make the subgraph bipartite, and concludes for every graph without a
-- colouring by the natural numbers. The pinned statement uses hG G n, the supremum over
-- induced subgraphs on n vertices of bipartiteDistance. The bridge shows h G n <= hG G n
-- for n >= 1 (a subgraph needs no more deletions than the induced graph on its vertices),
-- and that chromatic cardinal aleph one excludes a colouring by the natural numbers.

-- ===== source module PlasmaE111.Greedy =====

/-!
# Greedy colorings along a well-founded order

If every edge joins comparable vertices of a well-founded relation and every vertex has
finitely many neighbours below it, coloring each vertex by the least natural number not
used by its neighbours below is a proper coloring by `ℕ`.
-/


namespace PlasmaE111

/-- Greedy coloring along a well-founded relation with finitely many earlier
neighbours. -/
theorem nonempty_coloring_of_wellFounded {V : Type*} (H : SimpleGraph V) {r : V → V → Prop}
    (hr : WellFounded r) (hcomp : ∀ u v, H.Adj u v → r u v ∨ r v u)
    (hfin : ∀ v, {u | r u v ∧ H.Adj u v}.Finite) : Nonempty (H.Coloring ℕ) := by
  -- color `v` by the least number not used by its neighbours below
  let c : V → ℕ := hr.fix fun v g => sInf {n | ∀ u (h : r u v), H.Adj u v → g u h ≠ n}
  have hc : ∀ v, c v = sInf {n | ∀ u, r u v → H.Adj u v → c u ≠ n} := fun v =>
    hr.fix_eq _ v
  -- the least unused number avoids every neighbour below
  have hne : ∀ u v, r u v → H.Adj u v → c u ≠ c v := by
    intro u v huv hadj
    have hmem : c v ∈ {n | ∀ u, r u v → H.Adj u v → c u ≠ n} := by
      rw [hc v]
      refine Nat.sInf_mem ?_
      obtain ⟨n, hn⟩ := ((hfin v).image c).infinite_compl.nonempty
      exact ⟨n, fun u hu hadj hcu => hn ⟨u, ⟨hu, hadj⟩, hcu⟩⟩
    exact hmem u huv hadj
  refine ⟨SimpleGraph.Coloring.mk c fun {u v} hadj => ?_⟩
  rcases hcomp u v hadj with huv | hvu
  · exact hne u v huv hadj
  · exact (hne v u hvu hadj.symm).symm

end PlasmaE111

-- ===== source module PlasmaE111.Basic =====

/-!
# Edge costs, linear graphs, rooted patterns

Signs are Boolean: a sign assignment is `τ : V → Bool`, and an edge is
monochromatic under `τ` when its two ends receive the same sign.

* `edgeCost E` is the least number of monochromatic edges of the finite edge set `E`
  over all sign assignments, the number of deletions that make `E` bipartite.
* `Linear G C` says that every finite edge set of `G` whose ends lie in `s` has
  `edgeCost` at most `C |s|`.
* A `Pattern` has roots `R`, new vertices `S` and edges `E`. Its extension cost
  `extCost P.S P.E τ` is the least number of monochromatic edges after the signs of
  `S` are chosen freely and the others are those of `τ`.
* `Rooted G C N ν` is the property `J` of the proof: every pattern over `N` has
  expected extension cost at most `C |S|` under the law `ν` of the signs.
* `SameOn A μ ν` says that `μ` and `ν` have the same finite-dimensional marginals on
  the coordinates in `A`.
* `TraceBound C ν v T` bounds the trace energy `∑ u ∈ T, ν (σ u = σ v)` by `C`.
-/


open MeasureTheory
open scoped ENNReal NNReal Classical

namespace PlasmaE111

variable {V : Type*}

/-- `mono τ e` holds when both ends of `e` receive the same sign under `τ`. -/
def mono (τ : V → Bool) : Sym2 V → Prop :=
  Sym2.lift ⟨fun a b => τ a = τ b, fun _ _ => propext eq_comm⟩

/-- The number of edges of `E` that are monochromatic under `τ`. -/
noncomputable def monoCount (E : Finset (Sym2 V)) (τ : V → Bool) : ℕ :=
  (E.filter (mono τ)).card

/-- The least number of monochromatic edges of `E` over all sign assignments. -/
noncomputable def edgeCost (E : Finset (Sym2 V)) : ℕ :=
  ⨅ τ : V → Bool, monoCount E τ

/-- The least number of monochromatic edges of `E` when the signs on `S` are chosen
freely and every other vertex keeps its sign under `τ`. -/
noncomputable def extCost (S : Finset V) (E : Finset (Sym2 V)) (τ : V → Bool) : ℕ :=
  ⨅ η : V → Bool, monoCount E (S.piecewise η τ)

/-- `G` is `C`-linear: every finite set of edges of `G` with ends in `s` can be made
bipartite by deleting at most `C |s|` of them. -/
def Linear (G : SimpleGraph V) (C : ℝ≥0) : Prop :=
  ∀ (s : Finset V) (E : Finset (Sym2 V)), ↑E ⊆ G.edgeSet → (∀ e ∈ E, ∀ v ∈ e, v ∈ s) →
    (edgeCost E : ℝ≥0) ≤ C * s.card

/-- A rooted pattern: roots `R`, new vertices `S` and edges `E`. -/
structure Pattern (V : Type*) where
  /-- The roots, whose signs are given. -/
  R : Finset V
  /-- The new vertices, whose signs are chosen. -/
  S : Finset V
  /-- The edges, each meeting `S` and lying inside `R ∪ S`. -/
  E : Finset (Sym2 V)

/-- `P` is a pattern of `G` over `N`: its roots lie in `N`, its new vertices lie outside
`N`, and its edges are edges of `G` that meet `S` and lie inside `R ∪ S`. -/
structure Pattern.IsOver (G : SimpleGraph V) (N : Set V) (P : Pattern V) : Prop where
  roots_subset : ↑P.R ⊆ N
  new_not_mem : ∀ v ∈ P.S, v ∉ N
  edges_subset : ↑P.E ⊆ G.edgeSet
  edges_meet : ∀ e ∈ P.E, ∃ v ∈ e, v ∈ P.S
  edges_inside : ∀ e ∈ P.E, ∀ v ∈ e, v ∈ P.R ∨ v ∈ P.S

/-- The property `J`: every pattern of `G` over `N` has expected extension cost at most
`C |S|` under `ν`. -/
def Rooted (G : SimpleGraph V) (C : ℝ≥0) (N : Set V) (ν : Measure (V → Bool)) : Prop :=
  ∀ P : Pattern V, P.IsOver G N →
    ∫⁻ τ, (extCost P.S P.E τ : ℝ≥0∞) ∂ν ≤ C * P.S.card

/-- `μ` and `ν` have the same finite-dimensional marginals on the coordinates in `A`. -/
def SameOn (A : Set V) (μ ν : Measure (V → Bool)) : Prop :=
  ∀ J : Finset V, ↑J ⊆ A → μ.map J.restrict = ν.map J.restrict

/-- The trace energy of `v` over `T` is at most `C`: every finite `B ⊆ T` has
`∑ u ∈ B, ν (σ u = σ v) ≤ C`. -/
def TraceBound (C : ℝ≥0) (ν : Measure (V → Bool)) (v : V) (T : Set V) : Prop :=
  ∀ B : Finset V, ↑B ⊆ T → ∑ u ∈ B, ν {ω | ω u = ω v} ≤ C

/-! ### Basic properties -/

/-- A function of finitely many coordinates factors through the restriction to them. -/
theorem DependsOn.eq_comp_restrict {β : Type*} {f : (V → Bool) → β} {J : Finset V}
    (hf : DependsOn f J) (ω : V → Bool) :
    f ω = f (fun v => if h : v ∈ J then J.restrict ω ⟨v, h⟩ else true) :=
  hf fun i hi => by simp [Finset.mem_coe.mp hi]

/-- A function of finitely many coordinates is measurable. -/
theorem measurable_of_dependsOn {β : Type*} [MeasurableSpace β] {f : (V → Bool) → β}
    {J : Finset V} (hf : DependsOn f J) : Measurable f := by
  have hg : Measurable fun x : J → Bool => f fun v => if h : v ∈ J then x ⟨v, h⟩ else true :=
    measurable_of_finite _
  convert hg.comp (Finset.measurable_restrict (X := fun _ : V => Bool) J) using 1
  exact funext (DependsOn.eq_comp_restrict hf)

/-- The monochromatic count depends only on the signs at the ends of the edges. -/
theorem monoCount_congr {E : Finset (Sym2 V)} {τ τ' : V → Bool}
    (h : ∀ e ∈ E, ∀ v ∈ e, τ v = τ' v) : monoCount E τ = monoCount E τ' := by
  unfold monoCount
  congr 1
  refine Finset.filter_congr fun e he => ?_
  induction e using Sym2.ind with
  | h a b => simp [mono, h _ he a (Sym2.mem_mk_left a b), h _ he b (Sym2.mem_mk_right a b)]

/-- The extension cost depends only on the signs off `S` at the ends of the edges. -/
theorem extCost_dependsOn {S : Finset V} {E : Finset (Sym2 V)} {R : Finset V}
    (hE : ∀ e ∈ E, ∀ v ∈ e, v ∈ R ∨ v ∈ S) : DependsOn (extCost S E) R := by
  intro τ τ' h
  refine congrArg iInf (funext fun η => monoCount_congr fun e he v hv => ?_)
  rcases hE e he v hv with hR | hS
  · by_cases hvS : v ∈ S
    · simp [hvS]
    · simp [hvS, h v hR]
  · simp [hS]

/-- Some sign assignment attains the edge cost. -/
theorem exists_monoCount_eq_edgeCost (E : Finset (Sym2 V)) :
    ∃ σ : V → Bool, monoCount E σ = edgeCost E :=
  Nat.sInf_mem (Set.range_nonempty fun σ : V → Bool => monoCount E σ)

/-- Every sign assignment costs at least the edge cost. -/
theorem edgeCost_le_monoCount (E : Finset (Sym2 V)) (σ : V → Bool) :
    edgeCost E ≤ monoCount E σ :=
  ciInf_le (OrderBot.bddBelow _) σ

/-- The extension cost is at most the number of edges. -/
theorem extCost_le_card (S : Finset V) (E : Finset (Sym2 V)) (τ : V → Bool) :
    extCost S E τ ≤ E.card :=
  (ciInf_le (OrderBot.bddBelow _) τ).trans (Finset.card_filter_le _ _)

/-- Some choice of the signs on `S` attains the extension cost. -/
theorem exists_extCost_eq (S : Finset V) (E : Finset (Sym2 V)) (τ : V → Bool) :
    ∃ η : V → Bool, monoCount E (S.piecewise η τ) = extCost S E τ :=
  Nat.sInf_mem (Set.range_nonempty _)

/-- Every choice of the signs on `S` costs at least the extension cost. -/
theorem extCost_le_monoCount (S : Finset V) (E : Finset (Sym2 V)) (τ η : V → Bool) :
    extCost S E τ ≤ monoCount E (S.piecewise η τ) :=
  ciInf_le (OrderBot.bddBelow _) η

/-- A linear graph satisfies `J` over the empty set, for every probability law: a pattern
with no roots costs at most `C |S|` whatever the signs. -/
theorem rooted_empty {G : SimpleGraph V} {C : ℝ≥0} (hG : Linear G C)
    (ν : Measure (V → Bool)) [IsProbabilityMeasure ν] : Rooted G C ∅ ν := by
  intro P hP
  have hS : ∀ e ∈ P.E, ∀ v ∈ e, v ∈ P.S := fun e he v hv =>
    (hP.edges_inside e he v hv).resolve_left fun hR => hP.roots_subset hR
  have hle : ∀ τ, extCost P.S P.E τ ≤ edgeCost P.E := fun τ =>
    le_ciInf fun σ => (extCost_le_monoCount P.S P.E τ σ).trans_eq
      (monoCount_congr fun e he v hv => by simp [hS e he v hv])
  have hC := hG P.S P.E hP.edges_subset hS
  calc ∫⁻ τ, (extCost P.S P.E τ : ℝ≥0∞) ∂ν ≤ ∫⁻ _, (edgeCost P.E : ℝ≥0∞) ∂ν :=
        lintegral_mono fun τ => Nat.mono_cast (hle τ)
    _ = edgeCost P.E := by simp
    _ ≤ C * P.S.card := by exact_mod_cast hC

/-- Laws with the same finite marginals on `A` integrate a function of finitely many
coordinates of `A` alike. -/
theorem SameOn.lintegral_eq {A : Set V} {μ ν : Measure (V → Bool)} (h : SameOn A μ ν)
    {f : (V → Bool) → ℝ≥0∞} {J : Finset V} (hf : DependsOn f J) (hJ : ↑J ⊆ A) :
    ∫⁻ ω, f ω ∂μ = ∫⁻ ω, f ω ∂ν := by
  obtain ⟨g, hg, e⟩ : ∃ g : (J → Bool) → ℝ≥0∞, Measurable g ∧ ∀ ω, f ω = g (J.restrict ω) :=
    ⟨fun x => f fun v => if h : v ∈ J then x ⟨v, h⟩ else true, measurable_of_finite _,
      DependsOn.eq_comp_restrict hf⟩
  have hJm := Finset.measurable_restrict (X := fun _ : V => Bool) J
  rw [lintegral_congr e, lintegral_congr e, ← lintegral_map hg hJm, ← lintegral_map hg hJm,
    h J hJ]

/-- `J` over `N` depends only on the finite marginals on `N`. -/
theorem Rooted.of_sameOn {G : SimpleGraph V} {C : ℝ≥0} {N : Set V}
    {μ ν : Measure (V → Bool)} (hμ : Rooted G C N μ) (h : SameOn N μ ν) :
    Rooted G C N ν := by
  intro P hP
  rw [← h.lintegral_eq (fun _ _ hxy => congrArg _ (extCost_dependsOn hP.edges_inside hxy))
    hP.roots_subset]
  exact hμ P hP

/-- A trace bound depends only on the finite marginals on the trace and the vertex. -/
theorem TraceBound.of_sameOn {C : ℝ≥0} {A T : Set V} {v : V}
    {μ ν : Measure (V → Bool)} (hμ : TraceBound C μ v T) (h : SameOn A μ ν)
    (hv : v ∈ A) (hT : T ⊆ A) : TraceBound C ν v T := by
  intro B hB
  have key : ∀ u ∈ B, ν {ω | ω u = ω v} = μ {ω | ω u = ω v} := by
    intro u hu
    have hJ : ↑({u, v} : Finset V) ⊆ A := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hT (hB hu)
      · rw [Finset.mem_singleton.mp hx]
        exact hv
    have hS : {ω : V → Bool | ω u = ω v} = ({u, v} : Finset V).restrict ⁻¹'
        {x | x ⟨u, by simp⟩ = x ⟨v, by simp⟩} := rfl
    rw [hS, ← Measure.map_apply (Finset.measurable_restrict _) (Set.toFinite _).measurableSet,
      ← Measure.map_apply (Finset.measurable_restrict _) (Set.toFinite _).measurableSet,
      h _ hJ]
  rw [Finset.sum_congr rfl key]
  exact hμ B hB

/-- Agreement of finite marginals is transitive. -/
theorem SameOn.trans {A : Set V} {μ ν ρ : Measure (V → Bool)} (h₁ : SameOn A μ ν)
    (h₂ : SameOn A ν ρ) : SameOn A μ ρ :=
  fun J hJ => (h₁ J hJ).trans (h₂ J hJ)

/-- Agreement of finite marginals on `A` gives agreement on every subset of `A`. -/
theorem SameOn.mono {A B : Set V} {μ ν : Measure (V → Bool)} (h : SameOn A μ ν)
    (hBA : B ⊆ A) : SameOn B μ ν :=
  fun J hJ => h J (hJ.trans hBA)

end PlasmaE111

-- ===== source module PlasmaE111.HilbertClasses =====

/-!
# Countably many classes of unit vectors (Proposition C)

The unit vectors of a real Hilbert space fall into countably many classes such that any
two vectors `x, y` of one class satisfy `1 + ⟪x, y⟫ ≥ η > 0` for a constant `η` of the
class. Choose a Hilbert basis. For rationals `0 < b < a`, a unit vector whose coordinates
of magnitude at least `a` form a nonempty set `S`, all others having magnitude at most
`b`, is classified by `(a, b)` and the sign of its coordinate at an element of `S` chosen
by `Classical.epsilon`, a choice that depends only on `S`. Two vectors of one class differ
in their supports, giving `‖x + y‖ ≥ a - b`, or share the sign of a coordinate of
magnitude at least `a`, giving `‖x + y‖ ≥ 2a`.

Applied to the signs `±1` of a law in `L²`, this gives countably many classes of vertices
within which any two signs agree with probability bounded below.
-/


open MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace PlasmaE111

/-- A vector whose coordinates in a Hilbert basis all vanish is zero. -/
theorem eq_zero_of_forall_inner_hilbertBasis_eq_zero {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (b : HilbertBasis ι ℝ E) {x : E}
    (h : ∀ i, ⟪b i, x⟫ = 0) : x = 0 := by
  have hx := b.hasSum_repr x
  simp only [b.repr_apply_apply, h, zero_smul] at hx
  exact hx.unique hasSum_zero

/-- Only finitely many coordinates of a vector in a Hilbert basis have magnitude at least a
positive `t`. -/
theorem finite_setOf_le_abs_inner {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (b : HilbertBasis ι ℝ E) (x : E) {t : ℝ} (ht : 0 < t) :
    {i | t ≤ |⟪b i, x⟫|}.Finite := by
  have h := (b.orthonormal.inner_products_summable (x := x)).tendsto_cofinite_zero.eventually
    (gt_mem_nhds (pow_pos ht 2))
  refine (Filter.eventually_cofinite.1 h).subset fun i hi => ?_
  simp only [Set.mem_ofPred_eq, Real.norm_eq_abs, not_lt] at hi ⊢
  exact pow_le_pow_left₀ ht.le hi 2

/-- A real family with a nonzero member, only finitely many of whose members exceed any
positive magnitude, has rationals `0 < b < a` such that some member has magnitude at least
`a` and every member of magnitude below `a` has magnitude at most `b`. -/
theorem exists_rat_gap {ι : Type*} (f : ι → ℝ) (hfin : ∀ t, 0 < t → {i | t ≤ |f i|}.Finite)
    {i₀ : ι} (hi₀ : f i₀ ≠ 0) :
    ∃ q : ℚ × ℚ, 0 < q.2 ∧ q.2 < q.1 ∧ (∃ i, (q.1 : ℝ) ≤ |f i|) ∧
      ∀ i, |f i| < q.1 → |f i| ≤ q.2 := by
  set m := |f i₀|
  have hm : 0 < m := abs_pos.2 hi₀
  have hT : {i | m / 2 ≤ |f i| ∧ |f i| < m}.Finite :=
    (hfin (m / 2) (half_pos hm)).subset fun i hi => hi.1
  obtain ⟨L, hL0, hLm, hL⟩ : ∃ L, 0 < L ∧ L < m ∧ ∀ i, |f i| < m → |f i| ≤ L := by
    rcases Set.eq_empty_or_nonempty {i | m / 2 ≤ |f i| ∧ |f i| < m} with hT' | hT'
    · refine ⟨m / 2, half_pos hm, half_lt_self hm, fun i hi => ?_⟩
      by_contra hc
      have hi' : i ∈ {i | m / 2 ≤ |f i| ∧ |f i| < m} := ⟨(not_le.1 hc).le, hi⟩
      rw [hT'] at hi'
      exact hi'
    · obtain ⟨a, ha, hmax⟩ := Set.exists_max_image _ (fun i => |f i|) hT hT'
      refine ⟨max (m / 2) |f a|, lt_max_of_lt_left (half_pos hm),
        max_lt (half_lt_self hm) ha.2, fun i hi => ?_⟩
      by_cases hi' : m / 2 ≤ |f i|
      · exact le_max_of_le_right (hmax i ⟨hi', hi⟩)
      · exact le_max_of_le_left (not_le.1 hi').le
  obtain ⟨q₂, hq₂L, hq₂m⟩ := exists_rat_btwn hLm
  obtain ⟨q₁, hq₁₂, hq₁m⟩ := exists_rat_btwn hq₂m
  refine ⟨(q₁, q₂), by exact_mod_cast hL0.trans hq₂L, by exact_mod_cast hq₁₂, ⟨i₀, hq₁m.le⟩,
    fun i hi => (hL i (hi.trans hq₁m)).trans hq₂L.le⟩

/-- Proposition C. -/
theorem exists_unitVector_classes (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] :
    ∃ (cls : E → ℕ) (η : ℕ → ℝ), (∀ n, 0 < η n) ∧
      ∀ x y : E, ‖x‖ = 1 → ‖y‖ = 1 → cls x = cls y → η (cls x) ≤ 1 + ⟪x, y⟫ := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℝ E
  rcases isEmpty_or_nonempty w with hw | hw
  · refine ⟨fun _ => 0, fun _ => 1, fun _ => one_pos, fun x y hx _ _ => ?_⟩
    rw [eq_zero_of_forall_inner_hilbertBasis_eq_zero (x := x) b fun i => (IsEmpty.false i).elim,
      norm_zero] at hx
    exact (zero_ne_one hx).elim
  have hgood : ∀ x : E, ∃ q : ℚ × ℚ, ‖x‖ = 1 → 0 < q.2 ∧ q.2 < q.1 ∧
      (∃ i, (q.1 : ℝ) ≤ |⟪b i, x⟫|) ∧ ∀ i, |⟪b i, x⟫| < q.1 → |⟪b i, x⟫| ≤ q.2 := by
    intro x
    by_cases hx : ‖x‖ = 1
    · obtain ⟨i₀, hi₀⟩ : ∃ i, ⟪b i, x⟫ ≠ 0 := by
        by_contra! h
        rw [eq_zero_of_forall_inner_hilbertBasis_eq_zero b h, norm_zero] at hx
        exact zero_ne_one hx
      obtain ⟨q, hq⟩ := exists_rat_gap (fun i => ⟪b i, x⟫)
        (fun t ht => finite_setOf_le_abs_inner b x ht) hi₀
      exact ⟨q, fun _ => hq⟩
    · exact ⟨0, fun h => (hx h).elim⟩
  choose q hq using hgood
  let g : (ℚ × ℚ) × Bool → ℝ := fun k =>
    if k.1.2 < k.1.1 then ((k.1.1 : ℝ) - k.1.2) ^ 2 / 2 else 1
  refine ⟨fun x => Encodable.encode
      (q x, decide (0 < ⟪b (Classical.epsilon fun i => ((q x).1 : ℝ) ≤ |⟪b i, x⟫|), x⟫)),
    fun n => (Encodable.decode n).elim 1 g, fun n => ?_, fun x y hx hy hxy => ?_⟩
  · change 0 < (Encodable.decode n).elim 1 g
    rcases Encodable.decode n with _ | k
    · exact one_pos
    · simp only [Option.elim, g]
      split_ifs with h
      · have : (k.1.2 : ℝ) < k.1.1 := by exact_mod_cast h
        have : (0 : ℝ) < (k.1.1 : ℝ) - k.1.2 := by linarith
        positivity
      · exact one_pos
  obtain ⟨hqxy, hsign⟩ := Prod.mk.inj (Encodable.encode_injective hxy)
  have hqy := hq y hy
  rw [← hqxy] at hqy hsign
  obtain ⟨h0, h12, ⟨i₁, hi₁⟩, hgap⟩ := hq x hx
  obtain ⟨-, -, -, hgapy⟩ := hqy
  simp only [Encodable.encodek, Option.elim, g, h12, ↓reduceIte]
  set p := q x
  have hp12 : (p.2 : ℝ) < p.1 := by exact_mod_cast h12
  have hp2 : (0 : ℝ) < p.2 := by exact_mod_cast h0
  -- some coordinate of `x + y` has magnitude at least `a - b`
  obtain ⟨i, hi⟩ : ∃ i, (p.1 : ℝ) - p.2 ≤ |⟪b i, x⟫ + ⟪b i, y⟫| := by
    by_cases hS : ∀ i, (p.1 : ℝ) ≤ |⟪b i, x⟫| ↔ (p.1 : ℝ) ≤ |⟪b i, y⟫|
    · have he : (fun i => (p.1 : ℝ) ≤ |⟪b i, x⟫|) = fun i => (p.1 : ℝ) ≤ |⟪b i, y⟫| :=
        funext fun i => propext (hS i)
      rw [← he] at hsign
      set i₀ := Classical.epsilon fun i => (p.1 : ℝ) ≤ |⟪b i, x⟫|
      have hx0 : (p.1 : ℝ) ≤ |⟪b i₀, x⟫| :=
        Classical.epsilon_spec (p := fun i => (p.1 : ℝ) ≤ |⟪b i, x⟫|) ⟨i₁, hi₁⟩
      have hy0 := (hS i₀).1 hx0
      refine ⟨i₀, ?_⟩
      by_cases hpos : 0 < ⟪b i₀, x⟫
      · have hpos' : 0 < ⟪b i₀, y⟫ := by simpa [hpos] using hsign
        rw [abs_of_pos hpos] at hx0
        rw [abs_of_pos hpos'] at hy0
        rw [abs_of_pos (by linarith)]
        linarith
      · have hpos' : ¬0 < ⟪b i₀, y⟫ := by simpa [hpos] using hsign
        rw [not_lt] at hpos hpos'
        rw [abs_of_nonpos hpos] at hx0
        rw [abs_of_nonpos hpos'] at hy0
        rw [abs_of_nonpos (by linarith)]
        linarith
    · obtain ⟨i, hi⟩ := not_forall.1 hS
      refine ⟨i, ?_⟩
      have tri₁ : |⟪b i, x⟫| - |⟪b i, y⟫| ≤ |⟪b i, x⟫ + ⟪b i, y⟫| := by
        have := abs_sub_abs_le_abs_sub ⟪b i, x⟫ (-⟪b i, y⟫)
        rwa [abs_neg, sub_neg_eq_add] at this
      have tri₂ : |⟪b i, y⟫| - |⟪b i, x⟫| ≤ |⟪b i, x⟫ + ⟪b i, y⟫| := by
        have := abs_sub_abs_le_abs_sub ⟪b i, y⟫ (-⟪b i, x⟫)
        rwa [abs_neg, sub_neg_eq_add, add_comm] at this
      by_cases hA : (p.1 : ℝ) ≤ |⟪b i, x⟫|
      · have hB : |⟪b i, y⟫| < p.1 := not_le.1 fun h => hi ⟨fun _ => h, fun _ => hA⟩
        have := hgapy i hB
        linarith
      · have hB : (p.1 : ℝ) ≤ |⟪b i, y⟫| := by
          by_contra h
          exact hi ⟨fun h' => (hA h').elim, fun h' => (h h').elim⟩
        have := hgap i (not_le.1 hA)
        linarith
  -- a single coordinate is bounded by the norm
  have hcoord : |⟪b i, x + y⟫| ≤ ‖x + y‖ := by
    have := abs_real_inner_le_norm (b i) (x + y)
    rwa [b.orthonormal.1 i, one_mul] at this
  rw [inner_add_right] at hcoord
  have hsq := pow_le_pow_left₀ (by linarith) (hi.trans hcoord) 2
  rw [norm_add_sq_real, hx, hy] at hsq
  linarith

/-- The vertices fall into countably many classes within which any two signs agree with
probability at least a positive constant of the class. -/
theorem exists_sign_classes {V : Type*} (ν : Measure (V → Bool)) [IsProbabilityMeasure ν] :
    ∃ (cls : V → ℕ) (η : ℕ → ℝ≥0), (∀ n, 0 < η n) ∧
      ∀ u v, cls u = cls v → (η (cls u) : ℝ≥0∞) ≤ ν {ω | ω u = ω v} := by
  obtain ⟨cls, η, hη, hcls⟩ := exists_unitVector_classes (Lp ℝ 2 ν)
  -- the sign `±1` of vertex `u`
  let f : V → (V → Bool) → ℝ := fun u ω => if ω u then 1 else -1
  have hfm : ∀ u, Measurable (f u) := fun u =>
    (measurable_of_countable (fun c : Bool => if c then (1 : ℝ) else -1)).comp
      (measurable_pi_apply u)
  have hfL : ∀ u, MemLp (f u) 2 ν := fun u =>
    MemLp.of_bound (hfm u).aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => by
      simp only [f]
      split_ifs <;> simp)
  have hinner : ∀ u v,
      1 + ⟪(hfL u).toLp (f u), (hfL v).toLp (f v)⟫ = 2 * ν.real {ω | ω u = ω v} := by
    intro u v
    have hA : MeasurableSet {ω : V → Bool | ω u = ω v} :=
      measurableSet_eq_fun (measurable_pi_apply u) (measurable_pi_apply v)
    have he : (fun ω => ⟪(hfL u).toLp (f u) ω, (hfL v).toLp (f v) ω⟫) =ᵐ[ν]
        fun ω => {ω | ω u = ω v}.indicator (fun _ => (2 : ℝ)) ω - 1 := by
      filter_upwards [(hfL u).coeFn_toLp, (hfL v).coeFn_toLp] with ω hu hv
      rw [hu, hv]
      simp only [f, Set.indicator, Set.mem_ofPred_eq]
      cases ω u <;> cases ω v <;> norm_num
    rw [L2.inner_def, integral_congr_ae he,
      integral_sub ((integrable_const 2).indicator hA) (integrable_const 1),
      integral_indicator_const _ hA, integral_const]
    simp only [probReal_univ, smul_eq_mul]
    ring
  have hunit : ∀ u, ‖(hfL u).toLp (f u)‖ = 1 := by
    intro u
    have h := hinner u u
    simp only [real_inner_self_eq_norm_sq, Set.ofPred_true, probReal_univ] at h
    have h2 : ‖(hfL u).toLp (f u)‖ ^ 2 = 1 := by linarith
    nlinarith [norm_nonneg ((hfL u).toLp (f u))]
  refine ⟨fun u => cls ((hfL u).toLp (f u)), fun n => (η n / 2).toNNReal,
    fun n => Real.toNNReal_pos.2 (half_pos (hη n)), fun u v huv => ?_⟩
  have h := hcls _ _ (hunit u) (hunit v) huv
  rw [hinner] at h
  change ENNReal.ofReal (η _ / 2) ≤ _
  rw [← ofReal_measureReal (measure_ne_top ν _)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

end PlasmaE111

-- ===== source module PlasmaE111.Closure =====

/-!
# Closure over a set: replication of finite extensions

The proof uses elementary submodels only through replication: a finite configuration
whose new vertices lie outside the previous model has a copy, with the same diagram over
its roots, inside the next model. `ClosedOver G M N` states exactly this property of the
next model `N` over the previous model `M`, with an additional finite set `D ⊆ N` to
avoid, so that copies can be chosen pairwise disjoint.

A closure of `M ∪ X` over `M` is built in `ω` rounds, adding one witness for each finite
diagram over finite sets of roots and avoided vertices, so its size is at most
`max (#M + #X) ℵ₀`.
-/


open Cardinal

namespace PlasmaE111

variable {V : Type*}

/-- `g` realizes over `R` the same finite diagram as `f`: the same adjacencies among the
new vertices and between the new vertices and the roots. -/
def SameDiagram (G : SimpleGraph V) (R : Finset V) {m : ℕ} (f g : Fin m → V) : Prop :=
  (∀ i j, G.Adj (f i) (f j) ↔ G.Adj (g i) (g j)) ∧
    ∀ i, ∀ r ∈ R, (G.Adj (f i) r ↔ G.Adj (g i) r)

/-- `N` is closed over `M`: it contains `M`, and every finite configuration with roots
`R ⊆ N` whose new vertices avoid `M`, a finite `D ⊆ N` and `R` has a copy with the same
diagram over `R` inside `N`, still avoiding `M`, `D` and `R`. -/
def ClosedOver (G : SimpleGraph V) (M N : Set V) : Prop :=
  M ⊆ N ∧ ∀ (R D : Finset V) (m : ℕ) (f : Fin m → V), ↑R ⊆ N → ↑D ⊆ N →
    Function.Injective f → (∀ i, f i ∉ M ∧ f i ∉ D ∧ f i ∉ R) →
    ∃ g : Fin m → V, Function.Injective g ∧ (∀ i, g i ∈ N ∧ g i ∉ M ∧ g i ∉ D ∧ g i ∉ R) ∧
      SameDiagram G R f g

namespace Closure

/-- A request over `S`: finite sets of roots and of avoided vertices in `S`, and the number
of new vertices. -/
abbrev Request (S : Set V) : Type _ :=
  Finset S × Finset S × ℕ

/-- A finite diagram for a request: the adjacencies among the new vertices and between the
new vertices and the roots. -/
abbrev Diagram {S : Set V} (p : Request S) : Type _ :=
  (Fin p.2.2 → Fin p.2.2 → Bool) × (Fin p.2.2 → p.1 → Bool)

/-- `g` realizes the diagram `d` of the request `p`, with new vertices avoiding `M`, the
avoided vertices and the roots. -/
def Realizes (G : SimpleGraph V) (M : Set V) {S : Set V} (p : Request S) (d : Diagram p)
    (g : Fin p.2.2 → V) : Prop :=
  Function.Injective g ∧
    (∀ i, g i ∉ M ∧ (∀ r ∈ p.2.1, g i ≠ r) ∧ ∀ r ∈ p.1, g i ≠ r) ∧
    (∀ i j, G.Adj (g i) (g j) ↔ d.1 i j = true) ∧
    ∀ i (r : p.1), G.Adj (g i) r.1 ↔ d.2 i r = true

open scoped Classical in
/-- The new vertices of one realization of the diagram `d`, when there is one. -/
noncomputable def witness (G : SimpleGraph V) (M : Set V) {S : Set V} (p : Request S)
    (d : Diagram p) : Set V :=
  if h : ∃ g, Realizes G M p d g then Set.range h.choose else ∅

/-- A witness is finite. -/
theorem witness_finite (G : SimpleGraph V) (M : Set V) {S : Set V} (p : Request S)
    (d : Diagram p) : (witness G M p d).Finite := by
  unfold witness
  split
  · exact Set.finite_range _
  · exact Set.finite_empty

/-- A realizable diagram has a realization inside its witness. -/
theorem exists_realizes_subset_witness {G : SimpleGraph V} {M S : Set V} {p : Request S}
    {d : Diagram p} (h : ∃ g, Realizes G M p d g) :
    ∃ g, Realizes G M p d g ∧ Set.range g ⊆ witness G M p d := by
  refine ⟨h.choose, h.choose_spec, ?_⟩
  simp [witness, h]

/-- One round over `S`: add a realization of every realizable diagram over `S`. -/
noncomputable def step (G : SimpleGraph V) (M S : Set V) : Set V :=
  S ∪ ⋃ (p : Request S) (d : Diagram p), witness G M p d

/-- The rounds of the closure of `M ∪ X` over `M`. -/
noncomputable def rounds (G : SimpleGraph V) (M X : Set V) : ℕ → Set V
  | 0 => M ∪ X
  | n + 1 => step G M (rounds G M X n)

/-- A round keeps a set of size at most an infinite `κ` of size at most `κ`. -/
theorem mk_step_le (G : SimpleGraph V) (M : Set V) {S : Set V} {κ : Cardinal} (hκ : ℵ₀ ≤ κ)
    (hS : #S ≤ κ) : #(step G M S) ≤ κ := by
  classical
  have hmul : ∀ {a b : Cardinal}, a ≤ κ → b ≤ κ → a * b ≤ κ := fun ha hb =>
    (mul_le_mul' ha hb).trans (mul_eq_self hκ).le
  have hfin : #(Finset S) ≤ κ := by
    refine (mk_le_of_surjective (f := fun l : List S => l.toFinset)
      fun s => ⟨s.toList, s.toList_toFinset⟩).trans ((mk_list_le_max S).trans (max_le hκ hS))
  have hreq : #(Request S) ≤ κ := by
    simp only [Request, mk_prod, lift_id, lift_uzero, mk_nat, lift_aleph0]
    exact hmul hfin (hmul hfin hκ)
  have hU : #(⋃ (p : Request S) (d : Diagram p), witness G M p d) ≤ κ := by
    refine (mk_iUnion_le _).trans (hmul hreq (ciSup_le' fun p => ?_))
    exact (Set.finite_iUnion fun d => witness_finite G M p d).lt_aleph0.le.trans hκ
  exact (mk_union_le _ _).trans ((add_le_add hS hU).trans (add_eq_self hκ).le)

end Closure

open Closure in
/-- Every `M ∪ X` lies in a set closed over `M` of size at most `max (#M + #X) ℵ₀`. -/
theorem exists_closedOver (G : SimpleGraph V) (M X : Set V) :
    ∃ N : Set V, M ∪ X ⊆ N ∧ ClosedOver G M N ∧ #N ≤ max (#M + #X) ℵ₀ := by
  classical
  have hκ : ℵ₀ ≤ max (#M + #X) ℵ₀ := le_max_right _ _
  set N := rounds G M X
  have hmono : Monotone N := monotone_nat_of_le_succ fun n => Set.subset_union_left
  have hcard : ∀ n, #(N n) ≤ max (#M + #X) ℵ₀ := by
    intro n
    induction n with
    | zero => exact (mk_union_le M X).trans (le_max_left _ _)
    | succ n ih => exact mk_step_le G M hκ ih
  refine ⟨⋃ n, N n, Set.subset_iUnion N 0,
    ⟨Set.subset_union_left.trans (Set.subset_iUnion N 0), ?_⟩, ?_⟩
  · intro R D m f hR hD hf hfa
    obtain ⟨n, hn⟩ := Directed.exists_mem_subset_of_finset_subset_biUnion hmono.directed_le
      (s := R ∪ D) (by simpa [Set.union_subset_iff] using And.intro hR hD)
    rw [Finset.coe_union, Set.union_subset_iff] at hn
    let R' : Finset (N n) := R.subtype (· ∈ N n)
    let D' : Finset (N n) := D.subtype (· ∈ N n)
    let p : Request (N n) := (R', D', m)
    let d : Diagram p := (fun i j => decide (G.Adj (f i) (f j)),
      fun i r => decide (G.Adj (f i) r.1.1))
    have hfr : Realizes G M p d f := by
      refine ⟨hf, fun i => ⟨(hfa i).1, ?_, ?_⟩, fun i j => by simp [d],
        fun i r => by simp [d]⟩
      · intro r hr h
        exact (hfa i).2.1 (h ▸ Finset.mem_subtype.1 hr)
      · intro r hr h
        exact (hfa i).2.2 (h ▸ Finset.mem_subtype.1 hr)
    obtain ⟨g, ⟨hg, hga, hgA, hgB⟩, hgW⟩ :=
      exists_realizes_subset_witness (G := G) (M := M) (p := p) (d := d) ⟨f, hfr⟩
    refine ⟨g, hg, fun i => ⟨?_, (hga i).1, ?_, ?_⟩, fun i j => ?_, fun i r hr => ?_⟩
    · refine Set.subset_iUnion N (n + 1) (Set.subset_union_right ?_)
      exact Set.mem_iUnion₂.2 ⟨p, d, hgW ⟨i, rfl⟩⟩
    · intro h
      exact (hga i).2.1 ⟨g i, hn.2 h⟩ (Finset.mem_subtype.2 h) rfl
    · intro h
      exact (hga i).2.2 ⟨g i, hn.1 h⟩ (Finset.mem_subtype.2 h) rfl
    · rw [hgA i j]
      simp [d]
    · have := hgB i ⟨⟨r, hn.1 hr⟩, Finset.mem_subtype.2 hr⟩
      rw [this]
      simp [d]
  · have h := mk_iUnion_le_lift N
    rw [lift_uzero, mk_nat, lift_aleph0] at h
    simp only [lift_uzero] at h
    exact h.trans ((mul_le_mul' hκ (ciSup_le' hcard)).trans (mul_eq_self hκ).le)

end PlasmaE111

-- ===== source module PlasmaE111.Chain =====

/-!
# Chains of closed sets, layers and traces

For a graph on an uncountable vertex type `V`, a chain is a continuous increasing family
`N ξ` of vertex sets indexed by ordinals, starting from `∅`, each successor closed over
its predecessor, each set of size below `#V` while `ξ < (#V).ord`, and covering `V` by
then. It replaces the chain of elementary submodels of the proof, with the first model
empty and with length `(#V).ord` in place of the cofinality of `#V`.

The layer of a vertex `v` is the ordinal `ξ` with `v ∈ N (ξ + 1) \ N ξ`, and its trace
is the set of its neighbours in `N ξ`, which contains every neighbour in an earlier layer.
-/


open Cardinal Order

universe u

namespace PlasmaE111

variable {V : Type u}

/-- A continuous chain of closed sets covering `V`, each of size below `#V` before
`(#V).ord`. -/
structure Chain (G : SimpleGraph V) where
  /-- The sets of the chain. -/
  N : Ordinal.{u} → Set V
  zero : N 0 = ∅
  mono : Monotone N
  succ : ∀ ξ, ClosedOver G (N ξ) (N (ξ + 1))
  limit : ∀ o, IsSuccLimit o → N o = ⋃ ζ < o, N ζ
  card_lt : ∀ ξ < (#V).ord, #(N ξ) < #V
  cover : ∀ v, ∃ ξ < (#V).ord, v ∈ N (ξ + 1)

namespace Chain

/-- A nonempty type is enumerated by the ordinals below `(#V).ord`. -/
theorem exists_enum [Nonempty V] :
    ∃ e : Ordinal.{u} → V, ∀ v, ∃ ξ < (#V).ord, e ξ = v := by
  classical
  obtain ⟨eqv⟩ : Nonempty ((#V).ord.ToType ≃ V) := Cardinal.eq.1 (mk_ord_toType _)
  refine ⟨fun ξ => if h : ξ < (#V).ord then eqv (Ordinal.ToType.mk ⟨ξ, h⟩)
    else Classical.arbitrary V, fun v => ?_⟩
  have h := (Ordinal.ToType.mk.symm (eqv.symm v)).2
  refine ⟨(Ordinal.ToType.mk.symm (eqv.symm v)).1, h, ?_⟩
  rw [Set.mem_Iio] at h
  simp only [h, dite_true]
  exact (congrArg eqv (Ordinal.ToType.mk.apply_symm_apply (eqv.symm v))).trans
    (eqv.apply_symm_apply v)

/-- A closure of `S ∪ {x}` over `S`. -/
noncomputable def closure (G : SimpleGraph V) (S : Set V) (x : V) : Set V :=
  (exists_closedOver G S {x}).choose

/-- The closure contains `S ∪ {x}`. -/
theorem subset_closure (G : SimpleGraph V) (S : Set V) (x : V) :
    S ∪ {x} ⊆ closure G S x :=
  (exists_closedOver G S {x}).choose_spec.1

/-- The closure is closed over `S`. -/
theorem closedOver_closure (G : SimpleGraph V) (S : Set V) (x : V) :
    ClosedOver G S (closure G S x) :=
  (exists_closedOver G S {x}).choose_spec.2.1

/-- The closure is small. -/
theorem mk_closure_le (G : SimpleGraph V) (S : Set V) (x : V) :
    #(closure G S x) ≤ max (#S + 1) ℵ₀ :=
  (exists_closedOver G S {x}).choose_spec.2.2.trans_eq (by rw [mk_singleton])

/-- The chain adding the vertices of an enumeration `e` one at a time. -/
noncomputable def build (G : SimpleGraph V) (e : Ordinal.{u} → V) (o : Ordinal.{u}) : Set V :=
  Ordinal.limitRecOn o ∅ (fun ξ S => closure G S (e ξ)) fun o _ IH =>
    ⋃ ζ, ⋃ h : ζ < o, IH ζ h

/-- The chain starts from `∅`. -/
theorem build_zero (G : SimpleGraph V) (e : Ordinal.{u} → V) : build G e 0 = ∅ := by
  simp [build]

/-- A successor set closes its predecessor with the next vertex. -/
theorem build_add_one (G : SimpleGraph V) (e : Ordinal.{u} → V) (ξ : Ordinal.{u}) :
    build G e (ξ + 1) = closure G (build G e ξ) (e ξ) := by
  simp [build]

/-- A limit set is the union of the earlier sets. -/
theorem build_limit (G : SimpleGraph V) (e : Ordinal.{u} → V) {o : Ordinal.{u}}
    (ho : IsSuccLimit o) : build G e o = ⋃ ζ < o, build G e ζ := by
  rw [build, Ordinal.limitRecOn_limit _ _ _ _ ho]
  rfl

/-- The chain is increasing. -/
theorem build_subset_build (G : SimpleGraph V) (e : Ordinal.{u} → V) (η : Ordinal.{u}) :
    ∀ ξ ≤ η, build G e ξ ⊆ build G e η := by
  induction η using Ordinal.limitRecOn with
  | zero =>
    intro ξ h
    rw [nonpos_iff_eq_zero.1 h]
  | add_one η ih =>
    intro ξ h
    rcases h.lt_or_eq with h | rfl
    · rw [build_add_one]
      exact Set.Subset.trans (ih ξ (Order.lt_add_one_iff.1 h))
        (Set.subset_union_left.trans (subset_closure G _ _))
    · exact Set.Subset.rfl
  | limit o ho ih =>
    intro ξ h
    rcases h.lt_or_eq with h | rfl
    · rw [build_limit G e ho]
      exact Set.subset_iUnion₂ (s := fun ζ _ => build G e ζ) ξ h
    · exact Set.Subset.rfl

/-- The chain is monotone. -/
theorem build_mono (G : SimpleGraph V) (e : Ordinal.{u} → V) : Monotone (build G e) :=
  fun ξ η h => build_subset_build G e η ξ h

/-- The `ξ`-th set has at most `max ξ.card ℵ₀` vertices. -/
theorem mk_build_le (G : SimpleGraph V) (e : Ordinal.{u} → V) (ξ : Ordinal.{u}) :
    #(build G e ξ) ≤ max ξ.card ℵ₀ := by
  induction ξ using Ordinal.limitRecOn with
  | zero => simp [build_zero]
  | add_one ξ ih =>
    rw [build_add_one]
    refine (mk_closure_le G _ _).trans (max_le ?_ (le_max_right _ _))
    refine (add_le_add_left ih 1).trans ?_
    rw [add_one_of_aleph0_le (le_max_right _ _)]
    exact max_le_max (Ordinal.card_le_card (Order.lt_add_one_iff.2 le_rfl).le) le_rfl
  | limit o ho ih =>
    rw [build_limit G e ho]
    exact mk_biUnion_le_of_le (le_max_left _ _) (le_max_right _ _) _ fun j hj =>
      (ih j hj).trans (max_le_max (Ordinal.card_le_card hj.le) le_rfl)

end Chain

/-- Every graph on an uncountable vertex type has a chain. -/
theorem exists_chain (G : SimpleGraph V) (hV : ℵ₀ < #V) : Nonempty (Chain G) := by
  have : Nonempty V := mk_ne_zero_iff.1 (aleph0_pos.trans hV).ne'
  obtain ⟨e, he⟩ := Chain.exists_enum (V := V)
  refine ⟨{
    N := Chain.build G e
    zero := Chain.build_zero G e
    mono := Chain.build_mono G e
    succ := fun ξ => by
      rw [Chain.build_add_one]
      exact Chain.closedOver_closure G _ _
    limit := fun o ho => Chain.build_limit G e ho
    card_lt := fun ξ hξ => (Chain.mk_build_le G e ξ).trans_lt (max_lt (lt_ord.1 hξ) hV)
    cover := fun v => ?_ }⟩
  obtain ⟨ξ, hξ, rfl⟩ := he v
  refine ⟨ξ, hξ, ?_⟩
  rw [Chain.build_add_one]
  exact Chain.subset_closure G _ _ (Or.inr rfl)

namespace Chain

variable {G : SimpleGraph V} (c : Chain G)

/-- The layer of `v`: the ordinal `ξ` with `v ∈ N (ξ + 1) \ N ξ`. -/
noncomputable def layer (v : V) : Ordinal.{u} :=
  sInf {ξ | v ∈ c.N (ξ + 1)}

/-- The trace of `v`: its neighbours in the set preceding its layer. -/
def trace (v : V) : Set V :=
  {u | G.Adj v u ∧ u ∈ c.N (c.layer v)}

/-- A vertex lies in `N ξ` exactly when its layer is below `ξ`. -/
theorem mem_N_iff {v : V} {ξ : Ordinal.{u}} : v ∈ c.N ξ ↔ c.layer v < ξ := by
  constructor
  · intro hv
    induction ξ using Ordinal.limitRecOn with
    | zero => simp [c.zero] at hv
    | add_one ξ ih =>
      exact Order.lt_add_one_iff.2 (csInf_le' (s := {ξ | v ∈ c.N (ξ + 1)}) hv)
    | limit o ho ih =>
      rw [c.limit o ho, Set.mem_iUnion₂] at hv
      obtain ⟨ζ, hζ, hv⟩ := hv
      exact (ih ζ hζ hv).trans hζ
  · intro h
    obtain ⟨ξ', -, hv⟩ := c.cover v
    exact c.mono (Order.add_one_le_of_lt h)
      (csInf_mem (s := {ξ | v ∈ c.N (ξ + 1)}) ⟨ξ', hv⟩)

/-- Every layer is below `(#V).ord`. -/
theorem layer_lt_ord (v : V) : c.layer v < (#V).ord := by
  obtain ⟨ξ, hξ, hv⟩ := c.cover v
  exact (csInf_le' (s := {ξ | v ∈ c.N (ξ + 1)}) hv).trans_lt hξ

/-- Every layer has fewer than `#V` vertices, when `V` is infinite. -/
theorem card_layer_lt (hV : ℵ₀ ≤ #V) (ξ : Ordinal.{u}) :
    #{v // c.layer v = ξ} < #V := by
  by_cases hξ : ξ < (#V).ord
  · refine (mk_subtype_le_of_subset fun v hv => c.mem_N_iff.2 ?_).trans_lt
      (c.card_lt _ ((isSuccLimit_ord hV).add_one_lt hξ))
    rw [hv]
    exact Order.lt_add_one_iff.2 le_rfl
  · have : IsEmpty {v // c.layer v = ξ} := ⟨fun v => hξ (v.2 ▸ c.layer_lt_ord v.1)⟩
    rw [mk_eq_zero]
    exact aleph0_pos.trans_le hV

/-- A neighbour in an earlier layer lies in the trace. -/
theorem mem_trace_of_layer_lt {u v : V} (h : G.Adj v u) (hl : c.layer u < c.layer v) :
    u ∈ c.trace v :=
  ⟨h, c.mem_N_iff.2 hl⟩

end Chain

end PlasmaE111

-- ===== source module PlasmaE111.Probability.Kolmogorov =====

/-!
# Kolmogorov extension for Boolean coordinates

A consistent family of probability laws on the finite coordinate sets of `ι → Bool`
has a projective limit, for an arbitrary index type `ι`. The cylinders of `ι → Bool`
are compact and clopen, so the content of the family is σ-additive on the cylinder
algebra, and Carathéodory's construction extends it.
-/


open MeasureTheory Filter
open scoped Topology

namespace PlasmaE111

/-- A measurable cylinder of `ι → Bool` is closed in the product topology. -/
theorem isClosed_of_mem_measurableCylinders {ι : Type*} {s : Set (ι → Bool)}
    (hs : s ∈ measurableCylinders (fun _ : ι => Bool)) : IsClosed s := by
  obtain ⟨J, S, -, rfl⟩ := (mem_measurableCylinders s).1 hs
  exact (isClosed_discrete S).preimage (continuous_pi fun i => continuous_apply _)

/-- Kolmogorov extension for Boolean coordinates. -/
theorem exists_isProjectiveLimit_bool {ι : Type*}
    (P : ∀ J : Finset ι, Measure (J → Bool)) [∀ J, IsProbabilityMeasure (P J)]
    (hP : IsProjectiveMeasureFamily (α := fun _ : ι => Bool) P) :
    ∃ μ : Measure (ι → Bool), IsProbabilityMeasure μ ∧
      IsProjectiveLimit (α := fun _ : ι => Bool) μ P := by
  -- the content vanishes along decreasing cylinders with empty intersection
  have h_tendsto : ∀ ⦃s : ℕ → Set (ι → Bool)⦄,
      (∀ n, s n ∈ measurableCylinders (fun _ : ι => Bool)) → Antitone s → (⋂ n, s n) = ∅ →
        Tendsto (fun n => projectiveFamilyContent hP (s n)) atTop (𝓝 0) := by
    intro s hs hanti hinter
    obtain ⟨N, hN⟩ : ∃ N, s N = ∅ := by
      by_contra! h
      have := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed s
        (fun n => hanti (Nat.le_succ n)) h
        (isClosed_of_mem_measurableCylinders (hs 0)).isCompact
        (fun n => isClosed_of_mem_measurableCylinders (hs n))
      rw [hinter] at this
      exact Set.not_nonempty_empty this
    refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => ?_
    have : s n = ∅ := Set.subset_empty_iff.1 (hN ▸ hanti hn)
    rw [this, addContent_empty]
  have hσ : (projectiveFamilyContent hP).IsSigmaSubadditive := by
    refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum
      isSetRing_measurableCylinders (fun f hf hf_Union hf' => ?_)
    exact addContent_iUnion_eq_sum_of_tendsto_zero isSetRing_measurableCylinders
      (projectiveFamilyContent hP) (fun s hs => projectiveFamilyContent_ne_top _)
      h_tendsto hf hf_Union hf'
  let μ := (projectiveFamilyContent hP).measure isSetSemiring_measurableCylinders
    generateFrom_measurableCylinders.ge hσ
  have hμ : IsProjectiveLimit (α := fun _ : ι => Bool) μ P := by
    intro I
    ext s hs
    rw [Measure.map_apply (Finset.measurable_restrict I) hs, AddContent.measure_eq,
      ← cylinder, projectiveFamilyContent_cylinder hP hs]
    · exact generateFrom_measurableCylinders.symm
    · exact cylinder_mem_measurableCylinders _ _ hs
  refine ⟨μ, ⟨?_⟩, hμ⟩
  rw [← Set.preimage_univ (f := (∅ : Finset ι).restrict),
    ← Measure.map_apply (Finset.measurable_restrict _) .univ, hμ, measure_univ]

end PlasmaE111

-- ===== source module PlasmaE111.Probability.Limit =====

/-!
# Limits of sign laws along an ultrafilter

Probability laws on `V → Bool` are compact in the following sense: along any ultrafilter,
the finite-dimensional marginals of a family of laws converge, and Kolmogorov extension
turns the limits into one law. Every property that is a closed condition on finitely many
coordinates, holding eventually along the ultrafilter, then holds for the limit. In
particular `Rooted`, `SameOn` and `TraceBound` pass to the limit.
-/


open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace PlasmaE111

variable {V : Type*}

/-- Along an ultrafilter, laws on a finite type converge setwise to a limit measure. -/
theorem exists_tendsto_measure_of_finite {α X : Type*} [Finite X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (F : Ultrafilter α) (π : α → Measure X) :
    ∃ ρ : Measure X, ∀ S : Set X, Tendsto (fun a => π a S) F (𝓝 (ρ S)) := by
  have := Fintype.ofFinite X
  have hlim : ∀ x : X, ∃ m, Tendsto (fun a => π a {x}) F (𝓝 m) := fun x => by
    obtain ⟨m, -, hm⟩ := isCompact_univ.ultrafilter_le_nhds (F.map fun a => π a {x}) (by simp)
    exact ⟨m, hm⟩
  choose m hm using hlim
  refine ⟨Measure.sum fun x => m x • Measure.dirac x, fun S => ?_⟩
  have hS : MeasurableSet S := S.toFinite.measurableSet
  have h : ∀ a, π a S = ∑ x, π a {x} * Measure.dirac x S := fun a => by
    conv_lhs => rw [← Measure.sum_smul_dirac (π a)]
    simp
  simp only [h, Measure.sum_apply _ hS, tsum_fintype, Measure.smul_apply, smul_eq_mul]
  exact tendsto_finsetSum _ fun x _ =>
    ENNReal.Tendsto.mul_const (hm x) (Or.inr (measure_ne_top _ _))

/-- Along an ultrafilter, sign laws have a limit law: the integral of every finite-valued
function of finitely many coordinates converges to its integral under the limit. -/
theorem exists_limit {α : Type*} (F : Ultrafilter α) (ν : α → Measure (V → Bool))
    [∀ a, IsProbabilityMeasure (ν a)] :
    ∃ μ : Measure (V → Bool), IsProbabilityMeasure μ ∧
      ∀ (J : Finset V) (f : (V → Bool) → ℝ≥0∞), DependsOn f J → (∀ ω, f ω ≠ ∞) →
        Tendsto (fun a => ∫⁻ ω, f ω ∂ν a) F (𝓝 (∫⁻ ω, f ω ∂μ)) := by
  classical
  choose P hP using fun J : Finset V =>
    exists_tendsto_measure_of_finite F (fun a => (ν a).map J.restrict)
  have hprob : ∀ J, IsProbabilityMeasure (P J) := fun J => by
    have h : ∀ a, (ν a).map J.restrict Set.univ = 1 := fun a => by
      rw [Measure.map_apply (Finset.measurable_restrict J) .univ, Set.preimage_univ, measure_univ]
    refine ⟨tendsto_nhds_unique (hP J Set.univ) ?_⟩
    simp only [h]
    exact tendsto_const_nhds
  have hproj : IsProjectiveMeasureFamily (α := fun _ : V => Bool) P := by
    intro I J hJI
    ext S hS
    rw [Measure.map_apply (Finset.measurable_restrict₂ (X := fun _ : V => Bool) hJI) hS]
    refine tendsto_nhds_unique (hP J S) ?_
    convert hP I (Finset.restrict₂ (π := fun _ : V => Bool) hJI ⁻¹' S) using 2 with a
    rw [Measure.map_apply (Finset.measurable_restrict _) hS,
      Measure.map_apply (Finset.measurable_restrict _)
        (Finset.measurable_restrict₂ (X := fun _ : V => Bool) hJI hS),
      ← Set.preimage_comp, Finset.restrict₂_comp_restrict]
  obtain ⟨μ, hμprob, hμ⟩ := exists_isProjectiveLimit_bool P hproj
  refine ⟨μ, hμprob, fun J f hf hfin => ?_⟩
  -- `f` factors through the coordinates in `J`
  obtain ⟨g, hg, hfg⟩ : ∃ g : (J → Bool) → ℝ≥0∞, (∀ y, g y ≠ ∞) ∧
      ∀ ω, f ω = g (J.restrict ω) :=
    ⟨fun y => f fun i => if h : i ∈ J then y ⟨i, h⟩ else false, fun _ => hfin _,
      fun ω => hf fun i hi => by simp [Finset.mem_coe.1 hi]⟩
  have hint : ∀ ρ : Measure (V → Bool), ∫⁻ ω, f ω ∂ρ = ∑ y, g y * ρ.map J.restrict {y} :=
    fun ρ => by
      simp only [hfg]
      rw [← lintegral_map (measurable_of_finite g) (Finset.measurable_restrict J),
        lintegral_fintype]
  simp only [hint, hμ J]
  exact tendsto_finsetSum _ fun y _ => ENNReal.Tendsto.const_mul (hP J {y}) (Or.inr (hg y))

/-- A bound on the integral of a finite-valued function of finitely many coordinates that
holds eventually along the ultrafilter holds for the limit law. -/
theorem lintegral_le_of_tendsto {α : Type*} {F : Ultrafilter α} {ν : α → Measure (V → Bool)}
    {μ : Measure (V → Bool)}
    (hμ : ∀ (J : Finset V) (f : (V → Bool) → ℝ≥0∞), DependsOn f J → (∀ ω, f ω ≠ ∞) →
      Tendsto (fun a => ∫⁻ ω, f ω ∂ν a) F (𝓝 (∫⁻ ω, f ω ∂μ)))
    {J : Finset V} {f : (V → Bool) → ℝ≥0∞} (hf : DependsOn f J) (hfin : ∀ ω, f ω ≠ ∞)
    {c : ℝ≥0∞} (h : ∀ᶠ a in F, ∫⁻ ω, f ω ∂ν a ≤ c) : ∫⁻ ω, f ω ∂μ ≤ c :=
  le_of_tendsto (hμ J f hf hfin) h

/-- `J` over `N` passes to the limit law. -/
theorem rooted_of_tendsto {α : Type*} {F : Ultrafilter α} {ν : α → Measure (V → Bool)}
    {μ : Measure (V → Bool)}
    (hμ : ∀ (J : Finset V) (f : (V → Bool) → ℝ≥0∞), DependsOn f J → (∀ ω, f ω ≠ ∞) →
      Tendsto (fun a => ∫⁻ ω, f ω ∂ν a) F (𝓝 (∫⁻ ω, f ω ∂μ)))
    {G : SimpleGraph V} {C : ℝ≥0} {N : Set V}
    (h : ∀ P : Pattern V, P.IsOver G N →
      ∀ᶠ a in F, ∫⁻ τ, (extCost P.S P.E τ : ℝ≥0∞) ∂ν a ≤ C * P.S.card) :
    Rooted G C N μ := fun P hP =>
  lintegral_le_of_tendsto hμ (J := P.R)
    (fun _ _ hxy => congrArg _ (extCost_dependsOn hP.edges_inside hxy))
    (fun _ => ENNReal.natCast_ne_top _) (h P hP)

/-- The mass of a measurable set determined by finitely many coordinates converges to its
mass under the limit law. -/
theorem tendsto_measure_of_dependsOn {α : Type*} {F : Ultrafilter α}
    {ν : α → Measure (V → Bool)} {μ : Measure (V → Bool)}
    (hμ : ∀ (J : Finset V) (f : (V → Bool) → ℝ≥0∞), DependsOn f J → (∀ ω, f ω ≠ ∞) →
      Tendsto (fun a => ∫⁻ ω, f ω ∂ν a) F (𝓝 (∫⁻ ω, f ω ∂μ)))
    {J : Finset V} {s : Set (V → Bool)} (hs : MeasurableSet s) (hsJ : DependsOn (· ∈ s) J) :
    Tendsto (fun a => ν a s) F (𝓝 (μ s)) := by
  classical
  have hf : DependsOn (s.indicator (1 : (V → Bool) → ℝ≥0∞)) J := fun x y hxy => by
    simp only [Set.indicator_apply, show x ∈ s ↔ y ∈ s from iff_of_eq (hsJ hxy), Pi.one_apply]
  have := hμ J _ hf fun ω => by by_cases hω : ω ∈ s <;> simp [hω]
  simpa only [lintegral_indicator_one hs] using this

/-- Agreement of finite marginals on `A` with a fixed law passes to the limit law. -/
theorem sameOn_of_tendsto {α : Type*} {F : Ultrafilter α} {ν : α → Measure (V → Bool)}
    {μ : Measure (V → Bool)}
    (hμ : ∀ (J : Finset V) (f : (V → Bool) → ℝ≥0∞), DependsOn f J → (∀ ω, f ω ≠ ∞) →
      Tendsto (fun a => ∫⁻ ω, f ω ∂ν a) F (𝓝 (∫⁻ ω, f ω ∂μ)))
    {A : Set V} {ρ : Measure (V → Bool)} (h : ∀ᶠ a in F, SameOn A ρ (ν a)) :
    SameOn A ρ μ := by
  intro J hJ
  ext S hS
  have hm : MeasurableSet (J.restrict ⁻¹' S) :=
    Finset.measurable_restrict (X := fun _ : V => Bool) J hS
  rw [Measure.map_apply (Finset.measurable_restrict J) hS,
    Measure.map_apply (Finset.measurable_restrict J) hS]
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_)
    (tendsto_measure_of_dependsOn hμ hm (J := J) fun x y hxy => ?_)
  · filter_upwards [h] with a ha
    rw [← Measure.map_apply (Finset.measurable_restrict J) hS, ha J hJ,
      Measure.map_apply (Finset.measurable_restrict J) hS]
  · have : J.restrict x = J.restrict y := funext fun i => hxy i i.2
    simp only [Set.mem_preimage, this]

/-- A trace bound that holds eventually along the ultrafilter holds for the limit law. -/
theorem traceBound_of_tendsto {α : Type*} {F : Ultrafilter α} {ν : α → Measure (V → Bool)}
    {μ : Measure (V → Bool)}
    (hμ : ∀ (J : Finset V) (f : (V → Bool) → ℝ≥0∞), DependsOn f J → (∀ ω, f ω ≠ ∞) →
      Tendsto (fun a => ∫⁻ ω, f ω ∂ν a) F (𝓝 (∫⁻ ω, f ω ∂μ)))
    {C : ℝ≥0} {v : V} {T : Set V} (h : ∀ᶠ a in F, TraceBound C (ν a) v T) :
    TraceBound C μ v T := by
  classical
  intro B hB
  refine le_of_tendsto (tendsto_finsetSum _ fun u _ =>
    tendsto_measure_of_dependsOn hμ (J := {u, v})
      (measurableSet_eq_fun (measurable_pi_apply u) (measurable_pi_apply v))
      fun x y hxy => ?_) ?_
  · change (x u = x v) = (y u = y v)
    rw [hxy u (by simp), hxy v (by simp)]
  · filter_upwards [h] with a ha using ha B hB

end PlasmaE111

-- ===== source module PlasmaE111.DerivedSign =====

/-!
# Derived signs of infinite traces (Lemma D)

Let `ν` satisfy `J` over `M`, and let `y ∉ M` have infinitely many neighbours in `M`.
Enumerate infinitely many of them as `a 0, a 1, …`. Stars from `y` to finite sets of
neighbours are patterns over `M`, so the expected minority count of the signs on any
finite set of neighbours is at most `C`. Hence almost surely one sign occurs only finitely
often along `a`; the other is the derived sign `s`, a measurable function of the
coordinates `a n`. For every finite set `B` of neighbours, the stars on `B` together with
`a 0, …, a (L - 1)` cost at least the disagreements with `s` on `B` once the derived sign
has recurred often enough along `a`, so monotone convergence in `L` bounds
`∑ u ∈ B, ν (σ u ≠ s)` by `C`.
-/


open MeasureTheory
open scoped ENNReal NNReal Classical

namespace PlasmaE111

variable {V : Type*}

/-- A star from `y` to the vertices of `D`, with `y ∉ D`, has extension cost equal to the
number of vertices of `D` carrying some sign `c`, the sign chosen for `y`. -/
theorem exists_extCost_star_eq {y : V} {D : Finset V} (hyD : y ∉ D) (τ : V → Bool) :
    ∃ c : Bool, extCost {y} (D.image fun b => s(y, b)) τ =
      (D.filter fun b => τ b = c).card := by
  obtain ⟨η, hη⟩ := exists_extCost_eq {y} (D.image fun b => s(y, b)) τ
  refine ⟨η y, hη.symm.trans ?_⟩
  unfold monoCount
  rw [Finset.filter_image, Finset.card_image_of_injective _ fun b b' h => Sym2.congr_right.1 h]
  congr 1
  refine Finset.filter_congr fun b hb => ?_
  have hby : b ≠ y := fun h => hyD (h ▸ hb)
  simp [mono, Finset.piecewise_eq_of_notMem _ _ _ (Finset.notMem_singleton.2 hby), eq_comm]

/-- A star from `y ∉ M` to finitely many of its neighbours in `M` is a pattern over `M`. -/
theorem isOver_star {G : SimpleGraph V} {M : Set V} {y : V} (hy : y ∉ M) {D : Finset V}
    (hD : ↑D ⊆ {u | G.Adj y u ∧ u ∈ M}) :
    (⟨D, {y}, D.image fun b => s(y, b)⟩ : Pattern V).IsOver G M where
  roots_subset u hu := (hD hu).2
  new_not_mem v hv := by
    rw [Finset.mem_singleton.1 hv]
    exact hy
  edges_subset e he := by
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 he
    exact (hD hb).1
  edges_meet e he := by
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 he
    exact ⟨y, Sym2.mem_mk_left y b, Finset.mem_singleton_self y⟩
  edges_inside e he v hv := by
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 he
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact Or.inr (Finset.mem_singleton_self v)
    · exact Or.inl hb

/-- An infinite set of naturals meets some initial segment in at least `K` elements. -/
theorem exists_le_card_filter_range {p : ℕ → Prop} [DecidablePred p] (h : {n | p n}.Infinite)
    (K : ℕ) : ∃ L, K ≤ ((Finset.range L).filter p).card := by
  obtain ⟨t, ht, rfl⟩ := h.exists_subset_card_eq K
  refine ⟨t.sup id + 1, Finset.card_le_card fun n hn => Finset.mem_filter.2 ⟨?_, ht hn⟩⟩
  exact Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn))

/-- The count of a property along an initial segment is monotone in its length. -/
theorem card_filter_range_mono (p : ℕ → Prop) [DecidablePred p] {L L' : ℕ} (h : L ≤ L') :
    ((Finset.range L).filter p).card ≤ ((Finset.range L').filter p).card :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.2 h))

/-- The number of indices with a measurable property is a measurable function. -/
theorem measurable_card_filter {ι : Type*} (B : Finset ι) (p : ι → (V → Bool) → Prop)
    [∀ i ω, Decidable (p i ω)] (hp : ∀ i, MeasurableSet {ω | p i ω}) :
    Measurable fun ω => (((B.filter fun i => p i ω).card : ℕ) : ℝ≥0∞) := by
  have : (fun ω => (((B.filter fun i => p i ω).card : ℕ) : ℝ≥0∞)) =
      fun ω => ∑ i ∈ B, Set.indicator {ω | p i ω} 1 ω := by
    funext ω
    rw [Finset.card_filter]
    push_cast
    simp [Set.indicator_apply]
  rw [this]
  exact Finset.measurable_sum _ fun i _ => measurable_const.indicator (hp i)

/-- The expected number of indices with a measurable property is the sum of their
probabilities. -/
theorem lintegral_card_filter {ι : Type*} (ν : Measure (V → Bool)) (B : Finset ι)
    (p : ι → (V → Bool) → Prop) [∀ i ω, Decidable (p i ω)]
    (hp : ∀ i, MeasurableSet {ω | p i ω}) :
    ∫⁻ ω, (((B.filter fun i => p i ω).card : ℕ) : ℝ≥0∞) ∂ν = ∑ i ∈ B, ν {ω | p i ω} := by
  have : (fun ω => (((B.filter fun i => p i ω).card : ℕ) : ℝ≥0∞)) =
      fun ω => ∑ i ∈ B, Set.indicator {ω | p i ω} 1 ω := by
    funext ω
    rw [Finset.card_filter]
    push_cast
    simp [Set.indicator_apply]
  rw [this, lintegral_finsetSum B (f := fun i => Set.indicator {ω | p i ω} 1)
    fun i _ => measurable_const.indicator (hp i)]
  exact Finset.sum_congr rfl fun i _ => lintegral_indicator_one (hp i)

/-- Lemma D: a vertex with infinitely many neighbours in `M` has a derived sign `s`,
determined by the signs along an enumeration `a` of some of those neighbours, from which
almost surely only finitely many signs along `a` differ, and whose expected disagreement
with the signs of the neighbours sums to at most `C`. -/
theorem exists_derivedSign {G : SimpleGraph V} {C : ℝ≥0} {M : Set V}
    {ν : Measure (V → Bool)} [IsProbabilityMeasure ν] (hν : Rooted G C M ν)
    {y : V} (hy : y ∉ M) (hT : {u | G.Adj y u ∧ u ∈ M}.Infinite) :
    ∃ (s : (V → Bool) → Bool) (a : ℕ → V),
      Function.Injective a ∧ (∀ n, G.Adj y (a n) ∧ a n ∈ M) ∧
      DependsOn s (Set.range a) ∧ Measurable s ∧
      (∀ᵐ ω ∂ν, {n | ω (a n) ≠ s ω}.Finite) ∧
      ∀ B : Finset V, ↑B ⊆ {u | G.Adj y u ∧ u ∈ M} →
        ∑ u ∈ B, ν {ω | ω u ≠ s ω} ≤ C := by
  classical
  set T := {u | G.Adj y u ∧ u ∈ M}
  -- An enumeration `a` of infinitely many neighbours in `M`.
  set a : ℕ → V := fun n => (hT.natEmbedding T n : V)
  have ha_inj : Function.Injective a :=
    Subtype.val_injective.comp (hT.natEmbedding T).injective
  have haT : ∀ n, a n ∈ T := fun n => (hT.natEmbedding T n).2
  have hyD : ∀ D : Finset V, ↑D ⊆ T → y ∉ D := fun D hD hyD => hy (hD hyD).2
  -- The derived sign: whether the sign `true` occurs infinitely often along `a`.
  set s : (V → Bool) → Bool := fun ω => decide {n | ω (a n) = true}.Infinite with hsdef
  have hs_meas : Measurable s := by
    refine measurable_to_bool ?_
    have : s ⁻¹' {true} = ⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_ : N ≤ n), {ω | ω (a n) = true} := by
      ext ω
      simp [hsdef, ← Nat.frequently_atTop_iff_infinite, Filter.frequently_atTop]
    rw [this]
    exact MeasurableSet.iInter fun N => MeasurableSet.iUnion fun n => MeasurableSet.iUnion
      fun _ => measurableSet_eq_fun (measurable_pi_apply (a n)) measurable_const
  have hs_dep : DependsOn s (Set.range a) := by
    intro ω ω' h
    have : ∀ n, ω (a n) = ω' (a n) := fun n => h (a n) ⟨n, rfl⟩
    simp only [hsdef, this]
  -- The derived sign occurs infinitely often along `a`.
  have hs_inf : ∀ ω, {n | ω (a n) = s ω}.Infinite := by
    intro ω
    by_cases h : {n | ω (a n) = true}.Infinite
    · simp [hsdef, h]
    · have : {n | ω (a n) = s ω} = {n | ω (a n) = true}ᶜ := by
        ext n
        simp [hsdef, h]
      rw [this]
      exact (Set.not_infinite.1 h).infinite_compl
  have hmeas_eq : ∀ (u : V) (c : (V → Bool) → Bool), Measurable c →
      MeasurableSet {ω : V → Bool | ω u = c ω} :=
    fun u c hc => measurableSet_eq_fun (measurable_pi_apply u) hc
  -- Stars from `y` cost at most `C` in expectation.
  have hstar : ∀ D : Finset V, ↑D ⊆ T →
      ∫⁻ ω, (extCost {y} (D.image fun b => s(y, b)) ω : ℝ≥0∞) ∂ν ≤ C := by
    intro D hD
    simpa using hν _ (isOver_star hy hD)
  have hcard_img : ∀ (L : ℕ) (ω : V → Bool) (c : Bool),
      (((Finset.range L).image a).filter fun u => ω u = c).card =
        ((Finset.range L).filter fun n => ω (a n) = c).card := by
    intro L ω c
    rw [Finset.filter_image, Finset.card_image_of_injective _ ha_inj]
  have himg_T : ∀ L, ↑((Finset.range L).image a) ⊆ T := by
    intro L u hu
    obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 hu
    exact haT n
  refine ⟨s, a, ha_inj, haT, hs_dep, hs_meas, ?_, ?_⟩
  · -- The minority count along `a 0, …, a (L - 1)`.
    set f : ℕ → (V → Bool) → ℝ≥0∞ := fun L ω =>
      min (((Finset.range L).filter fun n => ω (a n) = true).card : ℝ≥0∞)
        (((Finset.range L).filter fun n => ω (a n) = false).card : ℝ≥0∞)
    have hf_meas : ∀ L, Measurable (f L) := fun L =>
      (measurable_card_filter _ (fun n ω => ω (a n) = true)
        fun n => hmeas_eq _ _ measurable_const).min
      (measurable_card_filter _ (fun n ω => ω (a n) = false)
        fun n => hmeas_eq _ _ measurable_const)
    have hf_mono : Monotone f := fun L L' h ω =>
      min_le_min (Nat.cast_le.2 (card_filter_range_mono _ h))
        (Nat.cast_le.2 (card_filter_range_mono _ h))
    have hf_le : ∀ L ω, f L ω ≤
        extCost {y} (((Finset.range L).image a).image fun b => s(y, b)) ω := by
      intro L ω
      obtain ⟨c, hc⟩ := exists_extCost_star_eq (hyD _ (himg_T L)) ω
      rw [hc, hcard_img]
      cases c
      · exact min_le_right _ _
      · exact min_le_left _ _
    have hF : ∫⁻ ω, ⨆ L, f L ω ∂ν ≤ C := by
      rw [lintegral_iSup hf_meas hf_mono]
      exact iSup_le fun L => (lintegral_mono (hf_le L)).trans (hstar _ (himg_T L))
    filter_upwards [ae_lt_top (Measurable.iSup hf_meas)
      (hF.trans_lt ENNReal.coe_lt_top).ne] with ω hω
    by_contra hinf
    obtain ⟨K, hK⟩ := ENNReal.exists_nat_gt hω.ne
    have hboth : ∀ c, {n | ω (a n) = c}.Infinite := by
      intro c
      by_cases hc : c = s ω
      · rw [hc]
        exact hs_inf ω
      · have : {n | ω (a n) = c} = {n | ω (a n) ≠ s ω} := by
          ext n
          simp only [Set.mem_ofPred_eq, Bool.eq_not_iff.2 hc, Bool.eq_not_iff]
        rw [this]
        exact hinf
    obtain ⟨L₁, hL₁⟩ := exists_le_card_filter_range (hboth true) K
    obtain ⟨L₂, hL₂⟩ := exists_le_card_filter_range (hboth false) K
    refine (hK.trans_le (le_iSup_of_le (max L₁ L₂) ?_)).false
    exact le_min
      (Nat.cast_le.2 (hL₁.trans (card_filter_range_mono _ (le_max_left _ _))))
      (Nat.cast_le.2 (hL₂.trans (card_filter_range_mono _ (le_max_right _ _))))
  · intro B hB
    -- The disagreement count on `B`, capped by the agreement count along `a`.
    set h : ℕ → (V → Bool) → ℝ≥0∞ := fun L ω =>
      min ((B.filter fun u => ω u ≠ s ω).card : ℝ≥0∞)
        (((Finset.range L).filter fun n => ω (a n) = s ω).card : ℝ≥0∞)
    have hh_meas : ∀ L, Measurable (h L) := fun L =>
      (measurable_card_filter _ (fun u ω => ω u ≠ s ω)
        fun u => (hmeas_eq _ _ hs_meas).compl).min
      (measurable_card_filter _ (fun n ω => ω (a n) = s ω)
        fun n => hmeas_eq _ _ hs_meas)
    have hh_mono : Monotone h := fun L L' hLL' ω =>
      min_le_min le_rfl (Nat.cast_le.2 (card_filter_range_mono _ hLL'))
    have hDT : ∀ L, ↑(B ∪ (Finset.range L).image a) ⊆ T := by
      intro L
      rw [Finset.coe_union]
      exact Set.union_subset hB (himg_T L)
    have hh_le : ∀ L ω, h L ω ≤
        extCost {y} ((B ∪ (Finset.range L).image a).image fun b => s(y, b)) ω := by
      intro L ω
      obtain ⟨c, hc⟩ := exists_extCost_star_eq (hyD _ (hDT L)) ω
      rw [hc]
      by_cases hcs : c = s ω
      · refine (min_le_right _ _).trans (Nat.cast_le.2 ?_)
        rw [hcs, ← hcard_img]
        exact Finset.card_le_card (Finset.filter_subset_filter _ Finset.subset_union_right)
      · refine (min_le_left _ _).trans (Nat.cast_le.2 ?_)
        have : (B.filter fun u => ω u ≠ s ω) = B.filter fun u => ω u = c := by
          refine Finset.filter_congr fun u _ => ?_
          rw [Bool.eq_not_iff.2 hcs, Bool.eq_not_iff]
        rw [this]
        exact Finset.card_le_card (Finset.filter_subset_filter _ Finset.subset_union_left)
    calc ∑ u ∈ B, ν {ω | ω u ≠ s ω}
        = ∫⁻ ω, ((B.filter fun u => ω u ≠ s ω).card : ℝ≥0∞) ∂ν :=
          (lintegral_card_filter ν B (fun u ω => ω u ≠ s ω)
            fun u => (hmeas_eq _ _ hs_meas).compl).symm
      _ ≤ ∫⁻ ω, ⨆ L, h L ω ∂ν := by
          refine lintegral_mono fun ω => ?_
          obtain ⟨L, hL⟩ := exists_le_card_filter_range (hs_inf ω)
            (B.filter fun u => ω u ≠ s ω).card
          exact le_iSup_of_le L (le_min le_rfl (Nat.cast_le.2 hL))
      _ = ⨆ L, ∫⁻ ω, h L ω ∂ν := lintegral_iSup hh_meas hh_mono
      _ ≤ C := iSup_le fun L => (lintegral_mono (hh_le L)).trans (hstar _ (hDT L))

end PlasmaE111

-- ===== source module PlasmaE111.Successor.Forcing =====

/-!
# Forced signs

Over the previous set `M`, every vertex `y` of the set `X` of new vertices with infinite
trace carries derived-sign data from Lemma D. The forcing map replaces the sign of each
`y ∈ X` by the opposite of its derived sign and keeps every other sign. Under the law
`ν.map (forced X s)` the coordinates of `X` take exactly the forced values, the marginals
on `M` are those of `ν`, and every `y ∈ X` has trace energy at most `C`.
-/


open MeasureTheory
open scoped ENNReal NNReal Classical

namespace PlasmaE111

variable {V : Type*}

/-- Derived-sign data over `M` for the vertices of `X`, as given by Lemma D. -/
structure ForcingData (G : SimpleGraph V) (C : ℝ≥0) (M X : Set V)
    (ν : Measure (V → Bool)) where
  /-- The derived sign of each vertex. -/
  s : V → (V → Bool) → Bool
  /-- The enumerated neighbours in `M` that determine the derived sign. -/
  a : V → ℕ → V
  injective : ∀ y ∈ X, Function.Injective (a y)
  adj_mem : ∀ y ∈ X, ∀ n, G.Adj y (a y n) ∧ a y n ∈ M
  measurable : ∀ y ∈ X, Measurable (s y)
  ae_finite : ∀ y ∈ X, ∀ᵐ ω ∂ν, {n | ω (a y n) ≠ s y ω}.Finite
  sum_le : ∀ y ∈ X, ∀ B : Finset V, ↑B ⊆ {u | G.Adj y u ∧ u ∈ M} →
    ∑ u ∈ B, ν {ω | ω u ≠ s y ω} ≤ C

/-- Lemma D supplies forcing data for every set of vertices outside `M` with infinite
traces. -/
theorem exists_forcingData {G : SimpleGraph V} {C : ℝ≥0} {M X : Set V}
    {ν : Measure (V → Bool)} [IsProbabilityMeasure ν] (hν : Rooted G C M ν)
    (hX : ∀ y ∈ X, y ∉ M ∧ {u | G.Adj y u ∧ u ∈ M}.Infinite) :
    Nonempty (ForcingData G C M X ν) := by
  have hD : ∀ y ∈ X, ∃ (s : (V → Bool) → Bool) (a : ℕ → V),
      Function.Injective a ∧ (∀ n, G.Adj y (a n) ∧ a n ∈ M) ∧
      DependsOn s (Set.range a) ∧ Measurable s ∧
      (∀ᵐ ω ∂ν, {n | ω (a n) ≠ s ω}.Finite) ∧
      ∀ B : Finset V, ↑B ⊆ {u | G.Adj y u ∧ u ∈ M} →
        ∑ u ∈ B, ν {ω | ω u ≠ s ω} ≤ C :=
    fun y hy => exists_derivedSign hν (hX y hy).1 (hX y hy).2
  refine ⟨{
    s := fun y => if h : y ∈ X then (hD y h).choose else fun _ => false
    a := fun y => if h : y ∈ X then (hD y h).choose_spec.choose else fun _ => y
    injective := fun y hy => ?_
    adj_mem := fun y hy => ?_
    measurable := fun y hy => ?_
    ae_finite := fun y hy => ?_
    sum_le := fun y hy => ?_ }⟩ <;>
  simp only [dif_pos hy]
  exacts [(hD y hy).choose_spec.choose_spec.1, (hD y hy).choose_spec.choose_spec.2.1,
    (hD y hy).choose_spec.choose_spec.2.2.2.1, (hD y hy).choose_spec.choose_spec.2.2.2.2.1,
    (hD y hy).choose_spec.choose_spec.2.2.2.2.2]

/-- The forcing map: each `y ∈ X` takes the opposite of its derived sign. -/
noncomputable def forced (X : Set V) (s : V → (V → Bool) → Bool) (ω : V → Bool) :
    V → Bool :=
  fun v => if v ∈ X then !s v ω else ω v

/-- The forcing map is measurable. -/
theorem measurable_forced {G : SimpleGraph V} {C : ℝ≥0} {M X : Set V}
    {ν : Measure (V → Bool)} (d : ForcingData G C M X ν) : Measurable (forced X d.s) := by
  refine measurable_pi_lambda _ fun v => ?_
  by_cases hv : v ∈ X
  · simp only [forced, hv, ite_true]
    exact (measurable_from_top (f := fun b : Bool => !b)).comp (d.measurable v hv)
  · simp only [forced, hv, ite_false]
    exact measurable_pi_apply v

/-- The forced law has the marginals of `ν` on `M`. -/
theorem sameOn_map_forced {G : SimpleGraph V} {C : ℝ≥0} {M X : Set V}
    {ν : Measure (V → Bool)} (d : ForcingData G C M X ν) (hXM : Disjoint X M) :
    SameOn M ν (ν.map (forced X d.s)) := by
  intro J hJ
  rw [Measure.map_map (Finset.measurable_restrict J) (measurable_forced d)]
  congr 1
  funext ω j
  have hj : (j : V) ∉ X := hXM.notMem_of_mem_right (hJ j.2)
  simp [Finset.restrict, forced, hj]

/-- Under the forced law every `y ∈ X` has trace energy at most `C` over its
neighbours in `M`. -/
theorem traceBound_map_forced {G : SimpleGraph V} {C : ℝ≥0} {M X : Set V}
    {ν : Measure (V → Bool)} (d : ForcingData G C M X ν) (hXM : Disjoint X M)
    {y : V} (hy : y ∈ X) :
    TraceBound C (ν.map (forced X d.s)) y {u | G.Adj y u ∧ u ∈ M} := by
  intro B hB
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun u hu => ?_)) (d.sum_le y hy B hB)
  have hu : u ∉ X := hXM.notMem_of_mem_right (hB hu).2
  rw [Measure.map_apply (measurable_forced d)
    (measurableSet_eq_fun (measurable_pi_apply u) (measurable_pi_apply y))]
  congr 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, forced, hu, hy, ite_true, ite_false,
    Bool.eq_not_iff]

end PlasmaE111

-- ===== source module PlasmaE111.Successor.Key =====

/-!
# The key inequality of the successor step

Let `N` be closed over `M`, let `ν` satisfy `J` over `M`, and force the signs of the set
`X` of new vertices with infinite trace. For finitely many patterns `P i` over `N` and
nonnegative weights `ρ i`, the expected weighted cost, after choosing the signs of the
remaining roots `W` (new vertices with finite trace) jointly and optimally, is at most
`∑ ρ i C |S i|`.

*Proof.* Fix `k` and take `⌈k ρ i⌉` copies of each `S i` over its roots inside
`N \ M`, pairwise disjoint and avoiding all roots, by `ClosedOver`. Together with stars
from each root `y ∈ X` to `a y 0, …, a y (L - 1)` they form one pattern over `M`, to
which `J` applies. Almost surely, once `L` exceeds the number of disagreements along
`a y` plus the total copy weight, every cheap extension gives each `y` its forced sign,
so the pattern costs at least `k` times the left-hand integrand. Fatou's lemma in `L`,
division by `k`, and `k → ∞` give the bound.
-/


open MeasureTheory
open scoped ENNReal NNReal Classical

namespace PlasmaE111

variable {V : Type*}

/-! ### Monochromatic counts -/

/-- The monochromatic count is monotone in the edge set. -/
theorem monoCount_le_of_subset {E F : Finset (Sym2 V)} (h : E ⊆ F) (τ : V → Bool) :
    monoCount E τ ≤ monoCount F τ :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

/-- `Sym2.map φ` is injective on the edges inside a set on which `φ` is injective. -/
theorem injOn_sym2Map_of_injOn {φ : V → V} {A : Set V} (hφ : Set.InjOn φ A)
    {E : Finset (Sym2 V)} (hE : ∀ e ∈ E, ∀ v ∈ e, v ∈ A) : Set.InjOn (Sym2.map φ) E := by
  have key : ∀ e e' : Sym2 V, (∀ v ∈ e, v ∈ A) → (∀ v ∈ e', v ∈ A) →
      Sym2.map φ e = Sym2.map φ e' → e = e' := by
    intro e e'
    induction e using Sym2.ind with
    | _ a b =>
      induction e' using Sym2.ind with
      | _ c d =>
        intro h h' he
        have ha := h a (Sym2.mem_mk_left a b)
        have hb := h b (Sym2.mem_mk_right a b)
        have hc := h' c (Sym2.mem_mk_left c d)
        have hd := h' d (Sym2.mem_mk_right c d)
        rw [Sym2.map_mk, Sym2.map_mk, Sym2.eq_iff] at he
        rw [Sym2.eq_iff]
        rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨hφ ha hc h1, hφ hb hd h2⟩
        · exact Or.inr ⟨hφ ha hd h1, hφ hb hc h2⟩
  intro e he e' he' h
  exact key e e' (hE e he) (hE e' he') h

/-- Transport of the monochromatic count along a map injective on the edges. -/
theorem monoCount_image_sym2Map {E : Finset (Sym2 V)} {φ : V → V}
    (hφ : Set.InjOn (Sym2.map φ) E) (τ : V → Bool) :
    monoCount (E.image (Sym2.map φ)) τ = monoCount E (τ ∘ φ) := by
  unfold monoCount
  rw [Finset.filter_image,
    Finset.card_image_of_injOn (hφ.mono fun x hx => by
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, SetLike.mem_coe] at hx ⊢
      exact hx.1)]
  congr 1
  refine Finset.filter_congr fun e _ => ?_
  induction e using Sym2.ind with
  | _ a b => simp [mono]

/-! ### Copies of patterns -/

/-- `φ` copies the pattern `P` into `N`: it fixes every vertex off `P.S`, maps `P.S`
injectively into `N` away from `M` and `D`, and maps the edges of `P` to edges of `G`. -/
structure IsCopy (G : SimpleGraph V) (M N : Set V) (D : Finset V) (P : Pattern V)
    (φ : V → V) : Prop where
  /-- Every vertex off the new vertices is fixed. -/
  eq_self : ∀ v ∉ P.S, φ v = v
  /-- The new vertices are copied injectively. -/
  injOn : Set.InjOn φ P.S
  /-- The copied new vertices lie in `N`, outside `M` and `D`. -/
  mem : ∀ v ∈ P.S, φ v ∈ N ∧ φ v ∉ M ∧ φ v ∉ D
  /-- The copied edges are edges of `G`. -/
  edges : ∀ e ∈ P.E, Sym2.map φ e ∈ G.edgeSet

/-- A pattern over `N` has a copy in `N` avoiding `M` and a finite `D ⊆ N`. -/
theorem exists_copy {G : SimpleGraph V} {M N : Set V} (hMN : ClosedOver G M N)
    {P : Pattern V} (hP : P.IsOver G N) {D : Finset V} (hD : ↑D ⊆ N) :
    ∃ φ, IsCopy G M N D P φ := by
  let e := P.S.equivFin
  let f : Fin P.S.card → V := fun j => (e.symm j : V)
  have hf : Function.Injective f := Subtype.val_injective.comp e.symm.injective
  obtain ⟨g, hg, hgN, hgd⟩ := hMN.2 P.R D _ f hP.roots_subset hD hf fun j =>
    have h := hP.new_not_mem _ (e.symm j).2
    ⟨fun h' => h (hMN.1 h'), fun h' => h (hD h'), fun h' => h (hP.roots_subset h')⟩
  have key : ∀ v (hv : v ∈ P.S), f (e ⟨v, hv⟩) = v := fun v hv => by simp [f]
  refine ⟨fun v => if h : v ∈ P.S then g (e ⟨v, h⟩) else v, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro v hv
    simp [hv]
  · intro v hv w hw h
    simp only [Finset.mem_coe] at hv hw
    simp only [hv, hw, ↓reduceDIte] at h
    simpa using e.injective (hg h)
  · intro v hv
    simp only [hv, ↓reduceDIte]
    exact ⟨(hgN _).1, (hgN _).2.1, (hgN _).2.2.1⟩
  · intro x hx
    have hadj := hP.edges_subset hx
    have hin := hP.edges_inside x hx
    have hmeet := hP.edges_meet x hx
    clear hx
    induction x using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at hadj
      rw [Sym2.map_mk, SimpleGraph.mem_edgeSet]
      by_cases ha : a ∈ P.S <;> by_cases hb : b ∈ P.S
      · simp only [ha, hb, ↓reduceDIte]
        rw [← key a ha, ← key b hb] at hadj
        exact (hgd.1 _ _).1 hadj
      · simp only [ha, hb, ↓reduceDIte]
        have hbR := (hin b (Sym2.mem_mk_right a b)).resolve_right hb
        rw [← key a ha] at hadj
        exact (hgd.2 _ b hbR).1 hadj
      · simp only [ha, hb, ↓reduceDIte]
        have haR := (hin a (Sym2.mem_mk_left a b)).resolve_right ha
        rw [← key b hb] at hadj
        exact ((hgd.2 _ a haR).1 hadj.symm).symm
      · exfalso
        obtain ⟨v, hv, hvS⟩ := hmeet
        rcases Sym2.mem_iff.1 hv with rfl | rfl
        · exact ha hvS
        · exact hb hvS

/-- Finitely many patterns over `N` have copies in `N` avoiding `M` and a finite `D ⊆ N`,
with pairwise disjoint images of their new vertices. -/
theorem exists_copies {G : SimpleGraph V} {M N : Set V} (hMN : ClosedOver G M N)
    {ι : Type*} [Finite ι] (Q : ι → Pattern V) (hQ : ∀ j, (Q j).IsOver G N) {D : Finset V}
    (hD : ↑D ⊆ N) :
    ∃ φ : ι → V → V, (∀ j, IsCopy G M N D (Q j) (φ j)) ∧
      ∀ j j', j ≠ j' → ∀ v ∈ (Q j).S, ∀ v' ∈ (Q j').S, φ j v ≠ φ j' v' := by
  have := Fintype.ofFinite ι
  suffices h : ∀ T : Finset ι, ∃ φ : ι → V → V,
      (∀ j ∈ T, IsCopy G M N D (Q j) (φ j)) ∧
      ∀ j ∈ T, ∀ j' ∈ T, j ≠ j' →
        ∀ v ∈ (Q j).S, ∀ v' ∈ (Q j').S, φ j v ≠ φ j' v' by
    obtain ⟨φ, h1, h2⟩ := h Finset.univ
    exact ⟨φ, fun j => h1 j (Finset.mem_univ _),
      fun j j' hjj' => h2 j (Finset.mem_univ _) j' (Finset.mem_univ _) hjj'⟩
  intro T
  induction T using Finset.induction_on with
  | empty => exact ⟨fun _ => id, by simp, by simp⟩
  | insert a T ha ih =>
    obtain ⟨φ, h1, h2⟩ := ih
    let D' := D ∪ T.biUnion fun j => (Q j).S.image (φ j)
    have hD' : ↑D' ⊆ N := by
      intro x hx
      simp only [D', Finset.coe_union, Finset.coe_biUnion, Finset.coe_image, Set.mem_union,
        Set.mem_iUnion, Set.mem_image, Finset.mem_coe] at hx
      rcases hx with hx | ⟨j, hj, v, hv, rfl⟩
      · exact hD hx
      · exact ((h1 j hj).mem v hv).1
    obtain ⟨ψ, hψ⟩ := exists_copy hMN (hQ a) hD'
    have hψD : IsCopy G M N D (Q a) ψ :=
      ⟨hψ.eq_self, hψ.injOn, fun v hv =>
        ⟨(hψ.mem v hv).1, (hψ.mem v hv).2.1,
          fun h => (hψ.mem v hv).2.2 (Finset.mem_union_left _ h)⟩, hψ.edges⟩
    have hψT : ∀ j ∈ T, ∀ v ∈ (Q a).S, ∀ v' ∈ (Q j).S, ψ v ≠ φ j v' := by
      intro j hj v hv v' hv' h
      apply (hψ.mem v hv).2.2
      rw [h]
      exact Finset.mem_union_right _
        (Finset.mem_biUnion.2 ⟨j, hj, Finset.mem_image_of_mem _ hv'⟩)
    have hupd : ∀ j ∈ T, Function.update φ a ψ j = φ j := fun j hj =>
      Function.update_of_ne (by rintro rfl; exact ha hj) _ _
    refine ⟨Function.update φ a ψ, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.1 hj with rfl | hj
      · simpa using hψD
      · rw [hupd j hj]
        exact h1 j hj
    · intro j hj j' hj' hjj'
      rcases Finset.mem_insert.1 hj with rfl | hjT <;>
        rcases Finset.mem_insert.1 hj' with rfl | hjT'
      · exact absurd rfl hjj'
      · simpa [hupd j' hjT'] using hψT j' hjT'
      · intro v hv v' hv'
        simpa [hupd j hjT] using (hψT j hjT v' hv' v hv).symm
      · simpa [hupd j hjT, hupd j' hjT'] using h2 j hjT j' hjT' hjj'

/-- A copy fixes the roots and is injective on the roots and new vertices together. -/
theorem IsCopy.injOn_union {G : SimpleGraph V} {M N : Set V} {D : Finset V} {P : Pattern V}
    {φ : V → V} (h : IsCopy G M N D P φ) (hRD : P.R ⊆ D) (hRS : ∀ v ∈ P.R, v ∉ P.S) :
    Set.InjOn φ ↑(P.R ∪ P.S) := by
  intro v hv w hw hvw
  simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hv hw
  rcases hv with hv | hv <;> rcases hw with hw | hw
  · rwa [h.eq_self v (hRS v hv), h.eq_self w (hRS w hw)] at hvw
  · rw [h.eq_self v (hRS v hv)] at hvw
    exact absurd (hvw ▸ hRD hv) (h.mem w hw).2.2
  · rw [h.eq_self w (hRS w hw)] at hvw
    exact absurd (hvw ▸ hRD hw) (h.mem v hv).2.2
  · exact h.injOn hv hw hvw

/-- A copy of `P` costs at least the extension cost of `P` under any signs agreeing on the
roots. -/
theorem IsCopy.extCost_le_monoCount {G : SimpleGraph V} {M N : Set V} {D : Finset V}
    {P : Pattern V} {φ : V → V} (h : IsCopy G M N D P φ) (hRD : P.R ⊆ D)
    (hRS : ∀ v ∈ P.R, v ∉ P.S) (hE : ∀ e ∈ P.E, ∀ v ∈ e, v ∈ P.R ∨ v ∈ P.S)
    {τ τ₀ : V → Bool} (hτ : ∀ v ∈ P.R, τ v = τ₀ v) :
    extCost P.S P.E τ₀ ≤ monoCount (P.E.image (Sym2.map φ)) τ := by
  rw [monoCount_image_sym2Map (injOn_sym2Map_of_injOn (h.injOn_union hRD hRS)
    fun e he v hv => by simpa using hE e he v hv)]
  rw [monoCount_congr (τ' := P.S.piecewise (τ ∘ φ) τ₀)]
  · exact PlasmaE111.extCost_le_monoCount _ _ _ _
  · intro e he v hv
    rcases hE e he v hv with hR | hS
    · rw [Finset.piecewise_eq_of_notMem _ _ _ (hRS v hR), Function.comp_apply,
        h.eq_self v (hRS v hR), hτ v hR]
    · rw [Finset.piecewise_eq_of_mem _ _ _ hS]

/-- Copies with disjoint new vertices avoiding all roots have disjoint edge sets. -/
theorem IsCopy.disjoint_edges {G : SimpleGraph V} {M N : Set V} {D : Finset V}
    {P Q : Pattern V} {φ ψ : V → V} (hφ : IsCopy G M N D P φ) (hψ : IsCopy G M N D Q ψ)
    (hP : P.IsOver G N) (hQ : Q.IsOver G N) (hQD : Q.R ⊆ D)
    (h : ∀ v ∈ P.S, ∀ v' ∈ Q.S, φ v ≠ ψ v') :
    Disjoint (P.E.image (Sym2.map φ)) (Q.E.image (Sym2.map ψ)) := by
  rw [Finset.disjoint_left]
  intro e he he'
  obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_image.1 he
  obtain ⟨e₁, he₁, hee⟩ := Finset.mem_image.1 he'
  obtain ⟨v, hv, hvS⟩ := hP.edges_meet e₀ he₀
  have hmem : φ v ∈ Sym2.map ψ e₁ := hee ▸ Sym2.mem_map.2 ⟨v, hv, rfl⟩
  obtain ⟨w, hw, hwv⟩ := Sym2.mem_map.1 hmem
  rcases hQ.edges_inside e₁ he₁ w hw with hwR | hwS
  · have hwS : w ∉ Q.S := fun hwS => hQ.new_not_mem w hwS (hQ.roots_subset hwR)
    rw [hψ.eq_self w hwS] at hwv
    exact (hφ.mem v hvS).2.2 (hwv ▸ hQD hwR)
  · exact h v hvS w hwS hwv.symm

/-- The monochromatic count over a disjoint union of edge sets is the sum of the counts. -/
theorem monoCount_biUnion_of_pairwiseDisjoint {ι : Type*} {s : Finset ι}
    {t : ι → Finset (Sym2 V)} (h : (s : Set ι).PairwiseDisjoint t) (τ : V → Bool) :
    monoCount (s.biUnion t) τ = ∑ j ∈ s, monoCount (t j) τ := by
  unfold monoCount
  rw [Finset.filter_biUnion, Finset.card_biUnion]
  exact fun j hj j' hj' hne =>
    (h hj hj' hne).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

/-- A sum over the copies is a sum over the patterns weighted by the numbers of copies. -/
theorem sum_sigma_fin {r : ℕ} (m : Fin r → ℕ) (x : Fin r → ℝ≥0∞) :
    ∑ j : (Σ i, Fin (m i)), x j.1 = ∑ i, (m i : ℝ≥0∞) * x i := by
  rw [Fintype.sum_sigma]
  simp

/-- The natural-number version of `sum_sigma_fin`. -/
theorem sum_sigma_fin_nat {r : ℕ} (m : Fin r → ℕ) (x : Fin r → ℕ) :
    ∑ j : (Σ i, Fin (m i)), x j.1 = ∑ i, m i * x i := by
  rw [Fintype.sum_sigma]
  simp

/-- An inequality `k I ≤ k T + B` for all `k ≥ 1` with `B` finite gives `I ≤ T`. -/
theorem le_of_forall_nat_mul_le {I T B : ℝ≥0∞} (hB : B ≠ ⊤)
    (h : ∀ k : ℕ, 0 < k → (k : ℝ≥0∞) * I ≤ k * T + B) : I ≤ T := by
  have h' : ∀ k : ℕ, 1 ≤ k → I ≤ T + B * (k : ℝ≥0∞)⁻¹ := fun k hk => by
    have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hk)
    have hkt : (k : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top k
    rw [← ENNReal.mul_le_mul_iff_right hk0 hkt, mul_add, mul_comm B, ← mul_assoc,
      ENNReal.mul_inv_cancel hk0 hkt, one_mul]
    exact h k hk
  have ht : Filter.Tendsto (fun k : ℕ => T + B * (k : ℝ≥0∞)⁻¹) Filter.atTop
      (nhds (T + B * 0)) :=
    tendsto_const_nhds.add
      (ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hB))
  rw [mul_zero, add_zero] at ht
  exact ge_of_tendsto ht (Filter.eventually_atTop.2 ⟨1, h'⟩)

/-! ### The pattern of stars and copies -/

/-- The roots of the patterns `P i`. -/
noncomputable def allRoots {r : ℕ} (P : Fin r → Pattern V) : Finset V :=
  Finset.univ.biUnion fun i => (P i).R

/-- The pattern made of the stars from the roots `y ∈ X` to `a y 0, …, a y (L - 1)` and
the copies `φ j` of the patterns `P j.1`, with the roots in `X` and `W` as new vertices
and the roots in `M` as roots. -/
noncomputable def starCopy {r : ℕ} (P : Fin r → Pattern V) {m : Fin r → ℕ}
    (φ : (Σ i, Fin (m i)) → V → V) (M X : Set V) (W : Finset V) (a : V → ℕ → V)
    (L : ℕ) :
    Pattern V where
  R := (allRoots P).filter (· ∈ M) ∪
    ((allRoots P).filter (· ∈ X)).biUnion fun y => (Finset.range L).image (a y)
  S := (allRoots P).filter (· ∈ X) ∪ W ∪ Finset.univ.biUnion fun j => (P j.1).S.image (φ j)
  E := ((allRoots P).filter (· ∈ X)).biUnion
      (fun y => (Finset.range L).image fun n => s(y, a y n)) ∪
    Finset.univ.biUnion fun j => (P j.1).E.image (Sym2.map (φ j))

/-- The stars and copies form a pattern over `M`. -/
theorem starCopy_isOver {G : SimpleGraph V} {C : ℝ≥0} {M N X : Set V}
    {ν : Measure (V → Bool)} (hX : X ⊆ N \ M) (d : ForcingData G C M X ν) {r : ℕ}
    {P : Fin r → Pattern V} (hP : ∀ i, (P i).IsOver G N) {W : Finset V}
    (hW : ∀ i, ∀ v ∈ (P i).R, v ∈ M ∨ v ∈ X ∨ v ∈ W) (hWN : ↑W ⊆ N \ M)
    {m : Fin r → ℕ} {φ : (Σ i, Fin (m i)) → V → V} {D : Finset V}
    (hφ : ∀ j, IsCopy G M N D (P j.1) (φ j)) (L : ℕ) :
    (starCopy P φ M X W d.a L).IsOver G M where
  roots_subset := by
    intro v hv
    simp only [Finset.mem_coe, starCopy, Finset.mem_union, Finset.mem_biUnion,
      Finset.mem_filter, Finset.mem_image] at hv
    rcases hv with ⟨_, hv⟩ | ⟨y, ⟨_, hy⟩, n, _, rfl⟩
    · exact hv
    · exact (d.adj_mem y hy n).2
  new_not_mem := by
    intro v hv
    simp only [starCopy, Finset.mem_union, Finset.mem_filter, Finset.mem_biUnion,
      Finset.mem_univ, true_and, Finset.mem_image] at hv
    rcases hv with (⟨_, hv⟩ | hv) | ⟨j, u, hu, rfl⟩
    · exact (hX hv).2
    · exact (hWN hv).2
    · exact ((hφ j).mem u hu).2.1
  edges_subset := by
    intro e he
    simp only [Finset.mem_coe, starCopy, Finset.mem_union, Finset.mem_biUnion,
      Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at he
    rcases he with ⟨y, ⟨_, hy⟩, n, _, rfl⟩ | ⟨j, e₀, he₀, rfl⟩
    · exact (d.adj_mem y hy n).1
    · exact (hφ j).edges e₀ he₀
  edges_meet := by
    intro e he
    simp only [starCopy, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_image, Finset.mem_univ, true_and] at he
    rcases he with ⟨y, ⟨hyR, hy⟩, n, _, rfl⟩ | ⟨j, e₀, he₀, rfl⟩
    · refine ⟨y, Sym2.mem_mk_left _ _, ?_⟩
      simp only [starCopy, Finset.mem_union, Finset.mem_filter]
      exact Or.inl (Or.inl ⟨hyR, hy⟩)
    · obtain ⟨v, hv, hvS⟩ := (hP j.1).edges_meet e₀ he₀
      refine ⟨φ j v, Sym2.mem_map.2 ⟨v, hv, rfl⟩, ?_⟩
      simp only [starCopy, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_image]
      exact Or.inr ⟨j, v, hvS, rfl⟩
  edges_inside := by
    intro e he w hw
    simp only [starCopy, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range] at he ⊢
    rcases he with ⟨y, ⟨hyR, hy⟩, n, hn, rfl⟩ | ⟨j, e₀, he₀, rfl⟩
    · rcases Sym2.mem_iff.1 hw with rfl | rfl
      · exact Or.inr (Or.inl (Or.inl ⟨hyR, hy⟩))
      · exact Or.inl (Or.inr ⟨y, ⟨hyR, hy⟩, n, hn, rfl⟩)
    · obtain ⟨u, hu, rfl⟩ := Sym2.mem_map.1 hw
      rcases (hP j.1).edges_inside e₀ he₀ u hu with huR | huS
      · have huS : u ∉ (P j.1).S := fun huS =>
          (hP j.1).new_not_mem u huS ((hP j.1).roots_subset huR)
        rw [(hφ j).eq_self u huS]
        have hu' : u ∈ allRoots P := Finset.mem_biUnion.2 ⟨j.1, Finset.mem_univ _, huR⟩
        rcases hW j.1 u huR with huM | huX | huW
        · exact Or.inl (Or.inl ⟨hu', huM⟩)
        · exact Or.inr (Or.inl (Or.inl ⟨hu', huX⟩))
        · exact Or.inr (Or.inl (Or.inr huW))
      · exact Or.inr (Or.inr ⟨j, u, huS, rfl⟩)

/-- The stars and copies have at most `|R ∩ X| + |W| + ∑ m i |S i|` new vertices. -/
theorem card_starCopy_S_le {r : ℕ} (P : Fin r → Pattern V) {m : Fin r → ℕ}
    (φ : (Σ i, Fin (m i)) → V → V) (M X : Set V) (W : Finset V) (a : V → ℕ → V)
    (L : ℕ) :
    (starCopy P φ M X W a L).S.card ≤
      ((allRoots P).filter (· ∈ X)).card + W.card + ∑ i, m i * (P i).S.card := by
  calc (starCopy P φ M X W a L).S.card
      ≤ (((allRoots P).filter (· ∈ X)) ∪ W).card +
          (Finset.univ.biUnion fun j => (P j.1).S.image (φ j)).card :=
        Finset.card_union_le _ _
    _ ≤ ((allRoots P).filter (· ∈ X)).card + W.card +
          ∑ j : (Σ i, Fin (m i)), ((P j.1).S.image (φ j)).card :=
        add_le_add (Finset.card_union_le _ _) Finset.card_biUnion_le
    _ ≤ ((allRoots P).filter (· ∈ X)).card + W.card +
          ∑ j : (Σ i, Fin (m i)), (P j.1).S.card :=
        Nat.add_le_add_left (Finset.sum_le_sum fun j _ => Finset.card_image_le) _
    _ = _ := by rw [sum_sigma_fin_nat m fun i => (P i).S.card]

/-- The combinatorial lower bound: once `L` exceeds the disagreements along every `a y`
plus the total number of edges of the copies, the stars and copies cost at least `k` times
the optimal weighted cost of the patterns under the forced signs. -/
theorem le_extCost_starCopy {G : SimpleGraph V} {C : ℝ≥0} {M N X : Set V}
    {ν : Measure (V → Bool)} (hX : X ⊆ N \ M) (d : ForcingData G C M X ν) {r : ℕ}
    {P : Fin r → Pattern V} (hP : ∀ i, (P i).IsOver G N) {W : Finset V}
    (hW : ∀ i, ∀ v ∈ (P i).R, v ∈ M ∨ v ∈ X ∨ v ∈ W) (hWN : ↑W ⊆ N \ M)
    (ρ : Fin r → ℝ≥0) {k : ℝ≥0∞} {m : Fin r → ℕ}
    (hm : ∀ i, k * ρ i ≤ m i) {φ : (Σ i, Fin (m i)) → V → V} {D : Finset V}
    (hRD : allRoots P ⊆ D) (hφ : ∀ j, IsCopy G M N D (P j.1) (φ j))
    (hdisj : ∀ j j', j ≠ j' → ∀ v ∈ (P j.1).S, ∀ v' ∈ (P j'.1).S, φ j v ≠ φ j' v')
    {ω : V → Bool}
    (hfin : ∀ y ∈ (allRoots P).filter (· ∈ X), {n | ω (d.a y n) ≠ d.s y ω}.Finite)
    {L : ℕ}
    (hL : ∑ y ∈ (allRoots P).filter (· ∈ X), {n | ω (d.a y n) ≠ d.s y ω}.ncard +
      ∑ j : (Σ i, Fin (m i)), (P j.1).E.card ≤ L) :
    k * ⨅ η : V → Bool, ∑ i, (ρ i : ℝ≥0∞) *
        extCost (P i).S (P i).E (W.piecewise η (forced X d.s ω)) ≤
      extCost (starCopy P φ M X W d.a L).S (starCopy P φ M X W d.a L).E ω := by
  set Q := starCopy P φ M X W d.a L with hQ
  have hQo : Q.IsOver G M := starCopy_isOver hX d hP hW hWN hφ L
  have hRP : ∀ i, (P i).R ⊆ D := fun i v hv =>
    hRD (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hv⟩)
  have hRS : ∀ i, ∀ v ∈ (P i).R, v ∉ (P i).S := fun i v hv hvS =>
    (hP i).new_not_mem v hvS ((hP i).roots_subset hv)
  obtain ⟨η, hη⟩ := exists_extCost_eq Q.S Q.E ω
  rw [← hη]
  set τ := Q.S.piecewise η ω with hτ
  -- the edges of the copies
  have hcopy : ∑ j, monoCount ((P j.1).E.image (Sym2.map (φ j))) τ ≤ monoCount Q.E τ := by
    rw [← monoCount_biUnion_of_pairwiseDisjoint]
    · exact monoCount_le_of_subset Finset.subset_union_right τ
    · intro j _ j' _ hne
      exact (hφ j).disjoint_edges (hφ j') (hP j.1) (hP j'.1) (hRP j'.1) (hdisj j j' hne)
  -- the signs off the new vertices
  have hτM : ∀ v ∈ M, τ v = ω v := fun v hv =>
    Finset.piecewise_eq_of_notMem _ _ _ fun hvS => hQo.new_not_mem v hvS hv
  by_cases hA : ∀ y ∈ (allRoots P).filter (· ∈ X), τ y = !d.s y ω
  · set τ₀ := W.piecewise τ (forced X d.s ω)
    have hagree : ∀ i, ∀ v ∈ (P i).R, τ v = τ₀ v := by
      intro i v hv
      by_cases hvW : v ∈ W
      · exact (Finset.piecewise_eq_of_mem _ _ _ hvW).symm
      rw [show τ₀ v = forced X d.s ω v from Finset.piecewise_eq_of_notMem _ _ _ hvW]
      have hvR : v ∈ allRoots P := Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hv⟩
      by_cases hvX : v ∈ X
      · rw [hA v (Finset.mem_filter.2 ⟨hvR, hvX⟩)]
        simp [forced, hvX]
      · have hvM : v ∈ M := by
          rcases hW i v hv with h | h | h
          · exact h
          · exact absurd h hvX
          · exact absurd h hvW
        rw [hτM v hvM]
        simp [forced, hvX]
    calc k * ⨅ η : V → Bool, ∑ i, (ρ i : ℝ≥0∞) *
          extCost (P i).S (P i).E (W.piecewise η (forced X d.s ω))
        ≤ k * ∑ i, (ρ i : ℝ≥0∞) * extCost (P i).S (P i).E τ₀ := by
          gcongr
          exact iInf_le _ τ
      _ = ∑ i, k * ρ i * extCost (P i).S (P i).E τ₀ := by
          rw [Finset.mul_sum]
          simp_rw [mul_assoc]
      _ ≤ ∑ i, (m i : ℝ≥0∞) * extCost (P i).S (P i).E τ₀ := by
          gcongr with i
          exact hm i
      _ = ∑ j : (Σ i, Fin (m i)), (extCost (P j.1).S (P j.1).E τ₀ : ℝ≥0∞) :=
          (sum_sigma_fin m _).symm
      _ ≤ ∑ j : (Σ i, Fin (m i)),
          (monoCount ((P j.1).E.image (Sym2.map (φ j))) τ : ℝ≥0∞) := by
          gcongr with j
          exact_mod_cast (hφ j).extCost_le_monoCount (hRP j.1) (hRS j.1)
            (hP j.1).edges_inside (hagree j.1)
      _ ≤ monoCount Q.E τ := by exact_mod_cast hcopy
  · push Not at hA
    obtain ⟨y, hy, hyτ⟩ := hA
    have hyτ' : τ y = d.s y ω := by simpa using hyτ
    obtain ⟨hyR, hyX⟩ := Finset.mem_filter.1 hy
    -- the star of `y`
    let A := (Finset.range L).filter fun n => ω (d.a y n) = d.s y ω
    have hstar : A.card ≤ monoCount Q.E τ := by
      calc A.card = (A.image fun n => s(y, d.a y n)).card := by
            rw [Finset.card_image_of_injective]
            intro n n' h
            exact d.injective y hyX (Sym2.congr_right.1 h)
        _ ≤ monoCount Q.E τ := by
            unfold monoCount
            apply Finset.card_le_card
            intro e he
            obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 he
            obtain ⟨hnL, hn⟩ := Finset.mem_filter.1 hn
            refine Finset.mem_filter.2 ⟨?_, ?_⟩
            · simp only [hQ, starCopy, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image]
              exact Or.inl ⟨y, hy, n, hnL, rfl⟩
            · change τ y = τ (d.a y n)
              rw [hyτ', hτM _ (d.adj_mem y hyX n).2, hn]
    have hbad : ((Finset.range L).filter fun n => ¬ω (d.a y n) = d.s y ω).card ≤
        {n | ω (d.a y n) ≠ d.s y ω}.ncard := by
      rw [← Set.ncard_coe_finset]
      refine Set.ncard_le_ncard (fun n hn => ?_) (hfin y hy)
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hn
      exact hn.2
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := Finset.range L) (fun n => ω (d.a y n) = d.s y ω)
    rw [Finset.card_range] at hsplit
    have hle := Finset.single_le_sum (f := fun y => {n | ω (d.a y n) ≠ d.s y ω}.ncard)
      (fun _ _ => Nat.zero_le _) hy
    have hEA : ∑ j : (Σ i, Fin (m i)), (P j.1).E.card ≤ A.card := by
      change _ ≤ ((Finset.range L).filter fun n => ω (d.a y n) = d.s y ω).card
      omega
    calc k * ⨅ η : V → Bool, ∑ i, (ρ i : ℝ≥0∞) *
          extCost (P i).S (P i).E (W.piecewise η (forced X d.s ω))
        ≤ k * ∑ i, (ρ i : ℝ≥0∞) * (P i).E.card := by
          gcongr
          refine (iInf_le _ ω).trans ?_
          gcongr with i
          exact_mod_cast extCost_le_card _ _ _
      _ = ∑ i, k * ρ i * (P i).E.card := by
          rw [Finset.mul_sum]
          simp_rw [mul_assoc]
      _ ≤ ∑ i, (m i : ℝ≥0∞) * (P i).E.card := by
          gcongr with i
          exact hm i
      _ = ∑ j : (Σ i, Fin (m i)), ((P j.1).E.card : ℝ≥0∞) := (sum_sigma_fin m _).symm
      _ ≤ monoCount Q.E τ := by exact_mod_cast hEA.trans hstar

/-- The key inequality (S) of the successor step, for nonnegative real weights. -/
theorem key_inequality {G : SimpleGraph V} {C : ℝ≥0} {M N X : Set V}
    (hMN : ClosedOver G M N) {ν : Measure (V → Bool)} [IsProbabilityMeasure ν]
    (hν : Rooted G C M ν) (hX : X ⊆ N \ M) (d : ForcingData G C M X ν)
    {r : ℕ} (P : Fin r → Pattern V) (hP : ∀ i, (P i).IsOver G N) (W : Finset V)
    (hW : ∀ i, ∀ v ∈ (P i).R, v ∈ M ∨ v ∈ X ∨ v ∈ W) (hWN : ↑W ⊆ N \ M)
    (ρ : Fin r → ℝ≥0) :
    ∫⁻ ω, ⨅ η : V → Bool, ∑ i, (ρ i : ℝ≥0∞) *
        extCost (P i).S (P i).E (W.piecewise η (forced X d.s ω)) ∂ν ≤
      ∑ i, (ρ i : ℝ≥0∞) * (C * (P i).S.card) := by
  set Rx := (allRoots P).filter (· ∈ X)
  set F : (V → Bool) → ℝ≥0∞ := fun ω => ⨅ η : V → Bool, ∑ i, (ρ i : ℝ≥0∞) *
    extCost (P i).S (P i).E (W.piecewise η (forced X d.s ω))
  refine le_of_forall_nat_mul_le
    (B := (C : ℝ≥0∞) * ((Rx.card + W.card + ∑ i, (P i).S.card : ℕ) : ℝ≥0∞))
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.natCast_ne_top _)) fun k _ => ?_
  -- the numbers of copies
  let m : Fin r → ℕ := fun i => ⌈(k : ℝ≥0) * ρ i⌉₊
  have hm : ∀ i, (k : ℝ≥0∞) * ρ i ≤ m i := fun i => by
    have := Nat.le_ceil ((k : ℝ≥0) * ρ i)
    exact_mod_cast this
  have hm' : ∀ i, (m i : ℝ≥0∞) ≤ k * ρ i + 1 := fun i => by
    have := Nat.ceil_lt_add_one (zero_le (a := (k : ℝ≥0) * ρ i))
    exact_mod_cast this.le
  -- the copies, avoiding all roots
  obtain ⟨φ, hφ, hdisj⟩ := exists_copies hMN (fun j : (Σ i, Fin (m i)) => P j.1)
    (fun j => hP j.1) (D := allRoots P) (by
      intro v hv
      obtain ⟨i, _, hv⟩ := Finset.mem_biUnion.1 hv
      exact (hP i).roots_subset hv)
  have hQo := fun L => starCopy_isOver hX d hP hW hWN hφ L
  have hmeas : ∀ L, Measurable fun ω =>
      (extCost (starCopy P φ M X W d.a L).S (starCopy P φ M X W d.a L).E ω : ℝ≥0∞) :=
    fun L => measurable_from_nat.comp
      (measurable_of_dependsOn (extCost_dependsOn (hQo L).edges_inside))
  -- the pointwise lower bound, almost surely
  have hae : ∀ᵐ ω ∂ν, (k : ℝ≥0∞) * F ω ≤ Filter.liminf (fun L =>
      (extCost (starCopy P φ M X W d.a L).S (starCopy P φ M X W d.a L).E ω : ℝ≥0∞))
      Filter.atTop := by
    have hfin : ∀ᵐ ω ∂ν, ∀ y ∈ Rx, {n | ω (d.a y n) ≠ d.s y ω}.Finite :=
      (Filter.eventually_all_finset Rx).2 fun y hy => d.ae_finite y (Finset.mem_filter.1 hy).2
    filter_upwards [hfin] with ω hω
    exact Filter.le_liminf_of_le (by isBoundedDefault) (Filter.eventually_atTop.2
      ⟨_, fun L hL => le_extCost_starCopy hX d hP hW hWN ρ hm (Finset.Subset.refl _) hφ hdisj
        hω hL⟩)
  -- the size of the new vertices
  have hcard : ∀ L, (C : ℝ≥0∞) * (starCopy P φ M X W d.a L).S.card ≤
      C * ((Rx.card + W.card + ∑ i, m i * (P i).S.card : ℕ) : ℝ≥0∞) := fun L => by
    gcongr
    exact_mod_cast card_starCopy_S_le P φ M X W d.a L
  calc (k : ℝ≥0∞) * ∫⁻ ω, F ω ∂ν
      ≤ ∫⁻ ω, k * F ω ∂ν := lintegral_const_mul_le _ _
    _ ≤ ∫⁻ ω, Filter.liminf (fun L =>
          (extCost (starCopy P φ M X W d.a L).S (starCopy P φ M X W d.a L).E ω : ℝ≥0∞))
          Filter.atTop ∂ν := lintegral_mono_ae hae
    _ ≤ Filter.liminf (fun L => ∫⁻ ω, (extCost (starCopy P φ M X W d.a L).S
          (starCopy P φ M X W d.a L).E ω : ℝ≥0∞) ∂ν)
          Filter.atTop := lintegral_liminf_le hmeas
    _ ≤ C * ((Rx.card + W.card + ∑ i, m i * (P i).S.card : ℕ) : ℝ≥0∞) :=
        Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall fun L =>
          (hν _ (hQo L)).trans (hcard L))
    _ ≤ C * ((Rx.card + W.card : ℕ) + ∑ i, ((k : ℝ≥0∞) * ρ i + 1) * (P i).S.card) := by
        push_cast
        gcongr with i
        exact hm' i
    _ = k * ∑ i, (ρ i : ℝ≥0∞) * (C * (P i).S.card) +
          C * ((Rx.card + W.card + ∑ i, (P i).S.card : ℕ) : ℝ≥0∞) := by
        have h1 : ∑ i, ((k : ℝ≥0∞) * ρ i + 1) * (P i).S.card =
            k * ∑ i, (ρ i : ℝ≥0∞) * (P i).S.card + ∑ i, ((P i).S.card : ℝ≥0∞) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
        have h2 : ∑ i, (ρ i : ℝ≥0∞) * (C * (P i).S.card) =
            C * ∑ i, (ρ i : ℝ≥0∞) * (P i).S.card := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [h1, h2]
        push_cast
        ring

end PlasmaE111

-- ===== source module PlasmaE111.Probability.Minimax =====

/-!
# A finite minimax lemma

Let finitely many pure strategies `x` have payoffs `f i x` against finitely many
constraints `i`. If every nonnegative combination of the constraints is met by some
pure strategy, then one mixed strategy meets all the constraints at once. The proof
separates the convex hull of the payoff vectors from the closed lower orthant at `c`.
-/


namespace PlasmaE111

/-- If every nonnegative combination of the constraints `f i ≤ c i` is met by a pure
strategy, a single mixed strategy meets every constraint. -/
theorem exists_mixed_le {ι X : Type*} [Fintype ι] [Fintype X] [Nonempty X]
    (f : ι → X → ℝ) (c : ι → ℝ)
    (h : ∀ ρ : ι → ℝ, (∀ i, 0 ≤ ρ i) → ∃ x, ∑ i, ρ i * f i x ≤ ∑ i, ρ i * c i) :
    ∃ p : X → ℝ, (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1 ∧ ∀ i, ∑ x, p x * f i x ≤ c i := by
  classical
  -- the mixed strategies, and their payoff vectors
  let P : Set (X → ℝ) := convexHull ℝ (Set.range fun x => Pi.single x 1)
  let M : Matrix ι X ℝ := Matrix.of fun i x => f i x
  let K : Set (ι → ℝ) := M.mulVecLin '' P
  have hP : P ⊆ {p | (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1} := by
    refine convexHull_min ?_ ?_
    · rintro _ ⟨x, rfl⟩
      refine ⟨fun y => ?_, by simp⟩
      dsimp only
      rw [Pi.single_apply]
      split_ifs <;> norm_num
    · rintro p ⟨hp0, hp1⟩ q ⟨hq0, hq1⟩ a b ha hb hab
      refine ⟨fun x => ?_, ?_⟩
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have := hp0 x
        have := hq0 x
        positivity
      · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hp1, hq1, hab]
  by_cases hKO : (K ∩ Set.Iic c).Nonempty
  · obtain ⟨_, ⟨p, hp, rfl⟩, hpc⟩ := hKO
    refine ⟨p, (hP hp).1, (hP hp).2, fun i => ?_⟩
    have := hpc i
    rw [Matrix.mulVecLin_apply] at this
    simpa [M, Matrix.mulVec, dotProduct, mul_comm] using this
  rw [Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty] at hKO
  have hKv : Convex ℝ K := (convex_convexHull ℝ _).linear_image M.mulVecLin
  have hKc : IsCompact K := ((Set.finite_range _).isCompact_convexHull ℝ).image
    M.mulVecLin.continuous_of_finiteDimensional
  obtain ⟨φ, u, v, hφK, huv, hφO⟩ :=
    geometric_hahn_banach_compact_closed hKv hKc (convex_Iic c) isClosed_Iic hKO
  -- the separating functional in coordinates
  let ρ : ι → ℝ := fun i => -φ (Pi.single i 1)
  have hφ : ∀ z, φ z = -∑ i, ρ i * z i := by
    intro z
    conv_lhs => rw [← Finset.univ_sum_single z]
    simp only [map_sum, ρ, neg_mul, Finset.sum_neg_distrib, neg_neg]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : Pi.single i (z i) = z i • Pi.single i (1 : ℝ) := by
      ext j
      simp [Pi.single_apply]
    rw [this, map_smul, smul_eq_mul, mul_comm]
  have hc : v < φ c := hφO c (Set.mem_Iic.2 le_rfl)
  have hρ : ∀ i, 0 ≤ ρ i := by
    intro i
    by_contra hi
    have hpos : 0 < φ (Pi.single i 1) := by simp only [ρ] at hi; linarith
    set t := (φ c - v) / φ (Pi.single i 1)
    have ht : 0 ≤ t := div_nonneg (by linarith) hpos.le
    have hmem : c - t • Pi.single i 1 ∈ Set.Iic c := by
      intro j
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have : 0 ≤ (Pi.single i (1 : ℝ) : ι → ℝ) j := by
        rw [Pi.single_apply]; split_ifs <;> norm_num
      nlinarith
    have := hφO _ hmem
    rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hpos.ne'] at this
    linarith
  obtain ⟨x, hx⟩ := h ρ hρ
  have hxK : M.mulVecLin (Pi.single x 1) ∈ K :=
    ⟨_, subset_convexHull ℝ _ ⟨x, rfl⟩, rfl⟩
  have h1 := hφK _ hxK
  rw [hφ] at h1 hc
  have : ∀ i, (M.mulVecLin (Pi.single x 1) : ι → ℝ) i = f i x := by
    intro i
    rw [Matrix.mulVecLin_apply]
    simp [M, Matrix.mulVec_single]
  simp only [this] at h1
  linarith

end PlasmaE111

-- ===== source module PlasmaE111.Successor.Mixture =====

/-!
# Mixtures of couplings

Let `Λ` be a law, `A` a set of coordinates to keep, and `W` a finite set of coordinates
outside `A` to choose. A coupling chooses the signs on `W` as a function of the signs on
a finite set `U ⊆ A`. If every nonnegative combination of finitely many costs, each a
function of the coordinates in `U ∪ W`, has expected optimal value at most the same
combination of the bounds `c i`, then the finite minimax lemma gives a mixture of
couplings meeting every bound at once. The mixture keeps the marginals of `Λ` on `A`.
-/


open MeasureTheory
open scoped ENNReal NNReal Classical

namespace PlasmaE111

variable {V : Type*}

/-- A mixture of couplings that choose the signs on `W` meets finitely many expected-cost
bounds at once, if every nonnegative combination of them is met by optimal choices. -/
theorem exists_mixture {r : ℕ} (Λ : Measure (V → Bool)) [IsProbabilityMeasure Λ]
    (A : Set V) (U W : Finset V) (hW : ∀ w ∈ W, w ∉ A)
    (f : Fin r → (V → Bool) → ℕ) (hf : ∀ i, DependsOn (f i) (↑U ∪ ↑W))
    (c : Fin r → ℝ≥0)
    (hkey : ∀ ρ : Fin r → ℝ≥0,
      ∫⁻ τ, ⨅ η : V → Bool, ∑ i, (ρ i : ℝ≥0∞) * f i (W.piecewise η τ) ∂Λ ≤
        ∑ i, (ρ i : ℝ≥0∞) * c i) :
    ∃ μ : Measure (V → Bool), IsProbabilityMeasure μ ∧ SameOn A Λ μ ∧
      ∀ i, ∫⁻ τ, (f i τ : ℝ≥0∞) ∂μ ≤ c i := by
  -- a pure coupling `ψ` chooses the signs on `W` from the signs on `U`
  let ext : (W → Bool) → V → Bool := fun ζ v => if hv : v ∈ W then ζ ⟨v, hv⟩ else true
  let extU : (U → Bool) → V → Bool := fun σ v => if hv : v ∈ U then σ ⟨v, hv⟩ else true
  let Ψ : ((U → Bool) → (W → Bool)) → (V → Bool) → V → Bool :=
    fun ψ τ => W.piecewise (ext (ψ (U.restrict τ))) τ
  -- the costs see only the signs on `U` and the choices on `W`
  have hfeq : ∀ i (τ τ' η η' : V → Bool), (∀ u ∈ U, τ u = τ' u) →
      (∀ w ∈ W, η w = η' w) → f i (W.piecewise η τ) = f i (W.piecewise η' τ') := by
    intro i τ τ' η η' hτ hη
    refine hf i fun v hv => ?_
    by_cases hw : v ∈ W
    · simp only [Finset.piecewise_eq_of_mem _ _ _ hw, hη v hw]
    · have hu : v ∈ U := by
        rcases hv with hu | hw'
        · exact hu
        · exact absurd hw' hw
      simp only [Finset.piecewise_eq_of_notMem _ _ _ hw, hτ v hu]
  have hmf : ∀ i, Measurable fun τ => (f i τ : ℝ≥0∞) := fun i =>
    measurable_from_nat.comp (measurable_of_dependsOn (J := U ∪ W) (by simpa using hf i))
  have hΨ : ∀ ψ, Measurable (Ψ ψ) := by
    intro ψ
    refine measurable_pi_lambda _ fun v => ?_
    by_cases hw : v ∈ W
    · simp only [Ψ, Finset.piecewise_eq_of_mem _ _ _ hw, ext, dif_pos hw]
      refine measurable_of_dependsOn (J := U) fun τ τ' h => ?_
      rw [show U.restrict τ = U.restrict τ' from funext fun u => h u u.2]
    · simp only [Ψ, Finset.piecewise_eq_of_notMem _ _ _ hw]
      exact measurable_pi_apply v
  -- the expected cost of a pure coupling is finite
  let pay : Fin r → ((U → Bool) → (W → Bool)) → ℝ≥0∞ :=
    fun i ψ => ∫⁻ τ, (f i (Ψ ψ τ) : ℝ≥0∞) ∂Λ
  have hpay : ∀ i ψ, pay i ψ ≠ ∞ := by
    intro i ψ
    let e : (↥(U ∪ W) → Bool) → V → Bool :=
      fun σ v => if hv : v ∈ U ∪ W then σ ⟨v, hv⟩ else true
    have hB : ∀ τ, f i τ ≤ Finset.univ.sup fun σ => f i (e σ) := by
      intro τ
      have : f i τ = f i (e ((U ∪ W).restrict τ)) := hf i fun v hv => by
        have hv' : v ∈ U ∪ W := by simpa using hv
        rw [show e ((U ∪ W).restrict τ) v = τ v from dif_pos hv']
      rw [this]
      exact Finset.le_sup (f := fun σ => f i (e σ)) (Finset.mem_univ _)
    refine ne_top_of_le_ne_top (ENNReal.natCast_ne_top (Finset.univ.sup fun σ => f i (e σ))) ?_
    calc pay i ψ ≤ ∫⁻ _, ((Finset.univ.sup fun σ => f i (e σ) : ℕ) : ℝ≥0∞) ∂Λ :=
          lintegral_mono fun τ => Nat.cast_le.2 (hB _)
      _ = _ := by simp
  -- every nonnegative combination of the bounds is met by a pure coupling
  obtain ⟨p, hp0, hp1, hpc⟩ := exists_mixed_le (fun i ψ => (pay i ψ).toReal) (fun i => c i) (by
    intro ρ hρ
    let ρ' : Fin r → ℝ≥0 := fun i => (ρ i).toNNReal
    let G : (U → Bool) → (W → Bool) → ℝ≥0∞ :=
      fun σ ζ => ∑ i, (ρ' i : ℝ≥0∞) * f i (W.piecewise (ext ζ) (extU σ))
    let ψ : (U → Bool) → (W → Bool) := fun σ => (Finite.exists_min (G σ)).choose
    have hτU : ∀ τ : V → Bool, ∀ u ∈ U, τ u = extU (U.restrict τ) u := by
      intro τ u hu
      simp [extU, hu]
    have hopt : ∀ τ, ∑ i, (ρ' i : ℝ≥0∞) * f i (Ψ ψ τ) ≤
        ⨅ η : V → Bool, ∑ i, (ρ' i : ℝ≥0∞) * f i (W.piecewise η τ) := by
      intro τ
      refine le_iInf fun η => ?_
      calc ∑ i, (ρ' i : ℝ≥0∞) * f i (Ψ ψ τ) = G (U.restrict τ) (ψ (U.restrict τ)) :=
            Finset.sum_congr rfl fun i _ => by
              rw [hfeq i τ (extU (U.restrict τ)) _ _ (hτU τ) fun _ _ => rfl]
        _ ≤ G (U.restrict τ) (W.restrict η) := (Finite.exists_min _).choose_spec _
        _ = _ := Finset.sum_congr rfl fun i _ => by
              rw [hfeq i (extU (U.restrict τ)) τ (ext (W.restrict η)) η
                (fun u hu => (hτU τ u hu).symm) fun w hw => by simp [ext, hw]]
    have hsum : ∑ i, (ρ' i : ℝ≥0∞) * pay i ψ ≤ ∑ i, (ρ' i : ℝ≥0∞) * c i :=
      calc ∑ i, (ρ' i : ℝ≥0∞) * pay i ψ =
            ∫⁻ τ, ∑ i, (ρ' i : ℝ≥0∞) * f i (Ψ ψ τ) ∂Λ := by
            rw [lintegral_finsetSum (f := fun i τ => (ρ' i : ℝ≥0∞) * f i (Ψ ψ τ)) _
              fun i _ => ((hmf i).comp (hΨ ψ)).const_mul _]
            exact Finset.sum_congr rfl fun i _ =>
              (lintegral_const_mul _ ((hmf i).comp (hΨ ψ))).symm
        _ ≤ ∫⁻ τ, ⨅ η : V → Bool, ∑ i, (ρ' i : ℝ≥0∞) * f i (W.piecewise η τ) ∂Λ :=
            lintegral_mono hopt
        _ ≤ _ := hkey ρ'
    refine ⟨ψ, ?_⟩
    have hρ' : ∀ i, ρ i = ρ' i := fun i => (Real.coe_toNNReal _ (hρ i)).symm
    have h1 : ∑ i, ρ i * (pay i ψ).toReal = (∑ i, (ρ' i : ℝ≥0∞) * pay i ψ).toReal := by
      rw [ENNReal.toReal_sum fun i _ => ENNReal.mul_ne_top ENNReal.coe_ne_top (hpay i ψ)]
      simp [ENNReal.toReal_mul, hρ']
    have h2 : ∑ i, ρ i * (c i : ℝ) = (∑ i, (ρ' i : ℝ≥0∞) * c i).toReal := by
      rw [ENNReal.toReal_sum fun i _ => ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top]
      simp [ENNReal.toReal_mul, hρ']
    rw [h1, h2]
    exact ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun i _ =>
      ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top) hsum)
  -- the mixture of the pure couplings
  let μ : Measure (V → Bool) := ∑ ψ, ENNReal.ofReal (p ψ) • Λ.map (Ψ ψ)
  have hμ : ∀ s, MeasurableSet s → μ s = ∑ ψ, ENNReal.ofReal (p ψ) * Λ (Ψ ψ ⁻¹' s) := by
    intro s hs
    simp [μ, Measure.finsetSum_apply, Measure.map_apply (hΨ _) hs]
  have hp : ∑ ψ, ENNReal.ofReal (p ψ) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg fun ψ _ => hp0 ψ, hp1, ENNReal.ofReal_one]
  refine ⟨μ, ⟨by simp [hμ _ MeasurableSet.univ, hp]⟩, fun J hJ => ?_, fun i => ?_⟩
  · -- each pure coupling keeps the signs on `A`
    ext s hs
    have hJ' : Measurable (J.restrict (π := fun _ => Bool)) := Finset.measurable_restrict J
    rw [Measure.map_apply hJ' hs, Measure.map_apply hJ' hs, hμ _ (hJ' hs)]
    have : ∀ ψ, Ψ ψ ⁻¹' (J.restrict ⁻¹' s) = J.restrict ⁻¹' s := by
      intro ψ
      ext τ
      have : J.restrict (Ψ ψ τ) = J.restrict τ := by
        funext j
        exact Finset.piecewise_eq_of_notMem _ _ _ fun hw => hW _ hw (hJ j.2)
      simp only [Set.mem_preimage, this]
    simp only [this, ← Finset.sum_mul, hp, one_mul]
  · calc ∫⁻ τ, (f i τ : ℝ≥0∞) ∂μ = ∑ ψ, ENNReal.ofReal (p ψ) * pay i ψ := by
          simp only [μ, lintegral_finsetSum_measure, lintegral_smul_measure, smul_eq_mul]
          exact Finset.sum_congr rfl fun ψ _ => by rw [lintegral_map (hmf i) (hΨ ψ)]
      _ = ENNReal.ofReal (∑ ψ, p ψ * (pay i ψ).toReal) := by
          rw [ENNReal.ofReal_sum_of_nonneg fun ψ _ => mul_nonneg (hp0 ψ) ENNReal.toReal_nonneg]
          refine Finset.sum_congr rfl fun ψ _ => ?_
          rw [ENNReal.ofReal_mul (hp0 ψ), ENNReal.ofReal_toReal (hpay i ψ)]
      _ ≤ ENNReal.ofReal (c i) := ENNReal.ofReal_le_ofReal (hpc i)
      _ = c i := ENNReal.ofReal_coe_nnreal

end PlasmaE111

-- ===== source module PlasmaE111.Successor =====

/-!
# The successor step (Lemma S)

Let `N` be closed over `M` and let `ν` satisfy `J` over `M`. There is a law `ν'` with
the marginals of `ν` on `M`, satisfying `J` over `N`, under which every vertex of
`N \ M` with infinitely many neighbours in `M` has trace energy at most `C` over them.

*Proof.* Force the signs of the set `X` of such vertices, giving the law
`Λ = ν.map (forced X s)`. For each finite family of patterns over `N`, the key inequality
and the mixture lemma give a law with the marginals of `Λ` on `M ∪ X` meeting `J` for
those patterns. A limit along an ultrafilter finer than the filter of finite families
keeps the marginals on `M ∪ X` and meets `J` for every pattern over `N`.
-/


open MeasureTheory
open scoped ENNReal NNReal Classical

namespace PlasmaE111

variable {V : Type*}

/-- For one finite family of patterns over `N`, the mixture lemma gives a law with the
marginals of the forced law on `M ∪ X` meeting `J` for the patterns of the family. -/
theorem exists_law_of_finset {G : SimpleGraph V} {C : ℝ≥0} {M N X : Set V}
    (hMN : ClosedOver G M N) {ν : Measure (V → Bool)} [IsProbabilityMeasure ν]
    (hν : Rooted G C M ν) (hX : X ⊆ N \ M) (d : ForcingData G C M X ν)
    [IsProbabilityMeasure (ν.map (forced X d.s))] (F : Finset (Pattern V)) :
    ∃ μ : Measure (V → Bool), IsProbabilityMeasure μ ∧
      SameOn (M ∪ X) (ν.map (forced X d.s)) μ ∧
      ∀ P ∈ F, P.IsOver G N → ∫⁻ τ, (extCost P.S P.E τ : ℝ≥0∞) ∂μ ≤ C * P.S.card := by
  set L := F.filter (fun P => P.IsOver G N)
  let e := L.equivFin
  let P : Fin L.card → Pattern V := fun i => (e.symm i).1
  have hP : ∀ i, (P i).IsOver G N := fun i => (Finset.mem_filter.1 (e.symm i).2).2
  set roots := L.biUnion Pattern.R
  set U := roots.filter (· ∈ M ∪ X)
  set W := roots.filter (· ∉ M ∪ X)
  have hroots : ∀ i, ∀ v ∈ (P i).R, v ∈ roots := fun i v hv =>
    Finset.mem_biUnion.2 ⟨(e.symm i).1, (e.symm i).2, hv⟩
  have hW : ∀ w ∈ W, w ∉ M ∪ X := fun w hw => (Finset.mem_filter.1 hw).2
  have hWN : (↑W : Set V) ⊆ N \ M := by
    intro w hw
    obtain ⟨hw, hwMX⟩ := Finset.mem_filter.1 hw
    obtain ⟨Q, hQ, hwQ⟩ := Finset.mem_biUnion.1 hw
    exact ⟨(Finset.mem_filter.1 hQ).2.roots_subset hwQ, fun h => hwMX (Or.inl h)⟩
  have hf : ∀ i, DependsOn (extCost (P i).S (P i).E) (↑U ∪ ↑W) := by
    intro i
    rw [← Finset.coe_union]
    refine extCost_dependsOn fun e he v hv => ?_
    rcases (hP i).edges_inside e he v hv with h | h
    · left
      by_cases hv' : v ∈ M ∪ X
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hroots i v h, hv'⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hroots i v h, hv'⟩)
    · exact Or.inr h
  have hc : ∀ i, ((C * (P i).S.card : ℝ≥0) : ℝ≥0∞) = C * (P i).S.card := by
    intro i
    push_cast
    rfl
  obtain ⟨μ, hμ, hsame, hbound⟩ := exists_mixture (ν.map (forced X d.s)) (M ∪ X) U W hW
    (fun i => extCost (P i).S (P i).E) hf (fun i => C * (P i).S.card) (by
      intro ρ
      have hdep : DependsOn (fun τ => ⨅ η : V → Bool, ∑ i, (ρ i : ℝ≥0∞) *
          (extCost (P i).S (P i).E (W.piecewise η τ) : ℝ≥0∞)) ↑(U ∪ W) := by
        intro τ τ' h
        refine iInf_congr fun η => Finset.sum_congr rfl fun i _ => ?_
        have hτ : ∀ v ∈ (↑U ∪ ↑W : Set V), W.piecewise η τ v = W.piecewise η τ' v := by
          intro v hv
          by_cases hvW : v ∈ W
          · simp [Finset.piecewise_eq_of_mem _ _ _ hvW]
          · rw [Finset.piecewise_eq_of_notMem _ _ _ hvW,
              Finset.piecewise_eq_of_notMem _ _ _ hvW]
            exact h v (by simpa [Finset.coe_union] using hv)
        rw [hf i hτ]
      rw [lintegral_map (measurable_of_dependsOn hdep) (measurable_forced d)]
      simp only [hc]
      exact key_inequality hMN hν hX d P hP W
        (fun i v hv => by
          by_cases hv' : v ∈ M ∪ X
          · rcases hv' with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Finset.mem_filter.2 ⟨hroots i v hv, hv'⟩)))
        hWN ρ)
  refine ⟨μ, hμ, hsame, fun Q hQF hQ => ?_⟩
  have hQL : Q ∈ L := Finset.mem_filter.2 ⟨hQF, hQ⟩
  have h := hbound (e ⟨Q, hQL⟩)
  have hPQ : P (e ⟨Q, hQL⟩) = Q := by simp [P]
  rw [hc, hPQ] at h
  exact h

/-- Lemma S. -/
theorem exists_successor {G : SimpleGraph V} {C : ℝ≥0} {M N : Set V}
    (hMN : ClosedOver G M N) {ν : Measure (V → Bool)} [IsProbabilityMeasure ν]
    (hν : Rooted G C M ν) :
    ∃ ν' : Measure (V → Bool), IsProbabilityMeasure ν' ∧ SameOn M ν ν' ∧
      Rooted G C N ν' ∧
      ∀ y ∈ N \ M, {u | G.Adj y u ∧ u ∈ M}.Infinite →
        TraceBound C ν' y {u | G.Adj y u ∧ u ∈ M} := by
  set X : Set V := {y | y ∈ N \ M ∧ {u | G.Adj y u ∧ u ∈ M}.Infinite}
  have hXNM : X ⊆ N \ M := fun y hy => hy.1
  have hXM : Disjoint X M := Set.disjoint_left.2 fun y hy hyM => hy.1.2 hyM
  let d := (exists_forcingData hν (X := X) fun y hy => ⟨hy.1.2, hy.2⟩).some
  have : IsProbabilityMeasure (ν.map (forced X d.s)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_forced d).aemeasurable).2 inferInstance
  choose μ hμ hsame hbound using exists_law_of_finset hMN hν hXNM d
  have := hμ
  obtain ⟨ν', hν', hlim⟩ :=
    exists_limit (Ultrafilter.of (Filter.atTop : Filter (Finset (Pattern V)))) μ
  have := hν'
  have hΛ : SameOn (M ∪ X) (ν.map (forced X d.s)) ν' :=
    sameOn_of_tendsto hlim (Filter.Eventually.of_forall hsame)
  refine ⟨ν', hν', (sameOn_map_forced d hXM).trans (hΛ.mono Set.subset_union_left),
    rooted_of_tendsto hlim fun P hP => Ultrafilter.of_le _ ?_, fun y hy hinf => ?_⟩
  · exact (Filter.eventually_ge_atTop {P}).mono fun F hF =>
      hbound F P (hF (Finset.mem_singleton_self P)) hP
  · have hyX : y ∈ X := ⟨hy, hinf⟩
    exact (traceBound_map_forced d hXM hyX).of_sameOn hΛ (Or.inr hyX)
      fun u hu => Or.inl hu.2

end PlasmaE111

-- ===== source module PlasmaE111.LimitMeasure =====

/-!
# The limit law (Proposition L)

For a linear graph and a chain, there is one law of the signs under which every vertex
with infinite trace has trace energy at most `C`.

*Proof.* By induction on `ξ`, there is a law satisfying `J` over every `N ζ` with
`ζ ≤ ξ` and the trace bound at every vertex of layer below `ξ` with infinite trace. Any
law satisfies `J` over `N 0 = ∅`. The successor step applies Lemma S to `N ξ ⊆ N (ξ + 1)`;
the new law has the old marginals on `N ξ`, which carry `J` over each earlier `N ζ` and
the earlier trace bounds. At a limit, every condition is closed and finite-dimensional,
and holds from some stage on, so a limit along an ultrafilter keeps them all; a pattern
over the union has its finitely many roots in an earlier set. At `(#V).ord` every vertex
has its layer below.
-/


open MeasureTheory Cardinal
open scoped ENNReal NNReal


namespace PlasmaE111

variable {V : Type u}

/-- Proposition L: one law gives every vertex with infinite trace trace energy at most
`C`. -/
theorem exists_traceBound_law {G : SimpleGraph V} {C : ℝ≥0} (hG : Linear G C)
    (c : Chain G) :
    ∃ ν : Measure (V → Bool), IsProbabilityMeasure ν ∧
      ∀ v, (c.trace v).Infinite → TraceBound C ν v (c.trace v) := by
  have key : ∀ ξ, ∃ ν : Measure (V → Bool), IsProbabilityMeasure ν ∧
      (∀ ζ ≤ ξ, Rooted G C (c.N ζ) ν) ∧
      ∀ v, c.layer v < ξ → (c.trace v).Infinite → TraceBound C ν v (c.trace v) := by
    intro ξ
    induction ξ using WellFoundedLT.induction with | ind ξ IH
    rcases Ordinal.zero_or_succ_or_isSuccLimit ξ with rfl | ⟨o, rfl⟩ | hξ
    · refine ⟨Measure.dirac fun _ => true, inferInstance, fun ζ hζ => ?_,
        fun v hv => (not_lt_zero hv).elim⟩
      rw [nonpos_iff_eq_zero.1 hζ, c.zero]
      exact rooted_empty hG _
    · obtain ⟨ν, hν, hR, hT⟩ := IH o (Order.lt_succ o)
      have := hν
      obtain ⟨ν', hν', hsame, hR', hT'⟩ := exists_successor (c.succ o) (hR o le_rfl)
      refine ⟨ν', hν', fun ζ hζ => ?_, fun v hv hinf => ?_⟩
      · rcases hζ.lt_or_eq with hζ | rfl
        · exact (hR ζ (Order.lt_succ_iff.1 hζ)).of_sameOn
            (hsame.mono (c.mono (Order.lt_succ_iff.1 hζ)))
        · rwa [Order.succ_eq_add_one]
      · rcases (Order.lt_succ_iff.1 hv).lt_or_eq with hv | hv
        · exact (hT v hv hinf).of_sameOn hsame (c.mem_N_iff.2 hv) fun u hu => c.mono hv.le hu.2
        · have htr : c.trace v = {u | G.Adj v u ∧ u ∈ c.N o} := by rw [Chain.trace, hv]
          rw [htr] at hinf ⊢
          refine hT' v ⟨?_, ?_⟩ hinf
          · rw [← Order.succ_eq_add_one, c.mem_N_iff, hv]
            exact Order.lt_succ o
          · rw [c.mem_N_iff, hv]
            exact lt_irrefl o
    · choose ν hν hR hT using fun ζ : Set.Iio ξ => IH ζ.1 ζ.2
      have := hν
      have : Nonempty (Set.Iio ξ) := ⟨⟨0, hξ.pos⟩⟩
      obtain ⟨μ, hμ, hlim⟩ :=
        exists_limit (Ultrafilter.of (Filter.atTop : Filter (Set.Iio ξ))) ν
      refine ⟨μ, hμ, fun ζ' hζ' => rooted_of_tendsto hlim fun P hP => ?_,
        fun v hv hinf => traceBound_of_tendsto hlim (Ultrafilter.of_le _ ?_)⟩
      · set ζ₀ := P.R.sup fun v => Order.succ (c.layer v)
        have hR₀ : ∀ v ∈ P.R, c.layer v < ζ' := fun v hv => c.mem_N_iff.1 (hP.roots_subset hv)
        have h₀ : ζ₀ ≤ ζ' := Finset.sup_le fun v hv => Order.succ_le_of_lt (hR₀ v hv)
        have h₀ξ : ζ₀ < ξ := (Finset.sup_lt_iff hξ.bot_lt).2 fun v hv =>
          hξ.succ_lt ((hR₀ v hv).trans_le hζ')
        have hP₀ : P.IsOver G (c.N ζ₀) :=
          { hP with
            roots_subset := fun v hv => c.mem_N_iff.2 ((Order.lt_succ _).trans_le
              (Finset.le_sup (f := fun v => Order.succ (c.layer v)) hv))
            new_not_mem := fun v hv hv₀ => hP.new_not_mem v hv (c.mono h₀ hv₀) }
        exact Ultrafilter.of_le _ ((Filter.eventually_ge_atTop ⟨ζ₀, h₀ξ⟩).mono
          fun ζ hζ => hR ζ ζ₀ hζ P hP₀)
      · exact (Filter.eventually_ge_atTop ⟨Order.succ (c.layer v), hξ.succ_lt hv⟩).mono
          fun ζ hζ => hT ζ v ((Order.lt_succ _).trans_le hζ) hinf
  obtain ⟨ν, hν, -, hT⟩ := key (#V).ord
  exact ⟨ν, hν, fun v hinf => hT v (c.layer_lt_ord v) hinf⟩

end PlasmaE111

-- ===== source module PlasmaE111.Coloring =====

/-!
# Countable colorings of linear graphs

**Theorem.** For every `C`, every `C`-linear graph has a proper coloring by `ℕ`.

*Proof.* Induct on `#V`; countable graphs are colored injectively. For uncountable `V`,
take a chain. Each layer has fewer than `#V` vertices and induces a `C`-linear graph, so
it is countably colorable by induction. Proposition L gives a law under which every
vertex with infinite trace has trace energy at most `C`, and Proposition C splits the
vertices into countably many classes within which any two signs agree with probability at
least `η > 0`. Within a class, a vertex has only finitely many neighbours in earlier
layers: they lie in its trace, which is finite or has energy at most `C`. Greedy coloring
along the layers colors the edges between layers inside each class. The class, the
greedy color and the color within the layer together color `G`.
-/


open Cardinal
open scoped NNReal


namespace PlasmaE111

variable {V : Type u}

/-- Induced subgraphs of a `C`-linear graph are `C`-linear. -/
theorem Linear.induce {G : SimpleGraph V} {C : ℝ≥0} (hG : Linear G C) (s : Set V) :
    Linear (G.induce s) C := by
  classical
  intro t E hE hEt
  set f : Sym2 s ↪ Sym2 V := (Function.Embedding.subtype (· ∈ s)).sym2Map
  have hmono : ∀ τ : V → Bool, monoCount (E.map f) τ = monoCount E (τ ∘ Subtype.val) := by
    intro τ
    unfold monoCount
    rw [Finset.filter_map, Finset.card_map]
    congr 1
    refine Finset.filter_congr fun e _ => ?_
    induction e using Sym2.ind with
    | _ a b => simp [f, mono]
  have hcost : edgeCost E ≤ edgeCost (E.map f) :=
    le_ciInf fun τ => (hmono τ).symm ▸ ciInf_le (OrderBot.bddBelow _) _
  have hmap := hG (t.map (Function.Embedding.subtype (· ∈ s))) (E.map f) ?_ ?_
  · rw [Finset.card_map] at hmap
    exact le_trans (by exact_mod_cast hcost) hmap
  · intro e he
    obtain ⟨e, he', rfl⟩ := Finset.mem_map.1 he
    have := hE he'
    induction e using Sym2.ind with
    | _ a b => simpa [f] using this
  · intro e he v hv
    obtain ⟨e, he', rfl⟩ := Finset.mem_map.1 he
    obtain ⟨w, hw, rfl⟩ := Sym2.mem_map.1 hv
    exact Finset.mem_map_of_mem _ (hEt e he' w hw)

/-- Lemma T: the trace bounds of one law and countable colorings of the layers give a
countable coloring. -/
theorem nonempty_coloring_of_traceBound {G : SimpleGraph V} {C : ℝ≥0} (c : Chain G)
    {ν : MeasureTheory.Measure (V → Bool)} [MeasureTheory.IsProbabilityMeasure ν]
    (hν : ∀ v, (c.trace v).Infinite → TraceBound C ν v (c.trace v))
    (hlayer : ∀ ξ, Nonempty ((G.induce {v | c.layer v = ξ}).Coloring ℕ)) :
    Nonempty (G.Coloring ℕ) := by
  classical
  obtain ⟨cls, η, hη, hcls⟩ := exists_sign_classes ν
  -- The edges between layers inside each class.
  let H : SimpleGraph V :=
    { Adj := fun u v => G.Adj u v ∧ cls u = cls v ∧ c.layer u ≠ c.layer v
      symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩⟩
      loopless := ⟨fun _ h => h.2.2 rfl⟩ }
  have hfin : ∀ v, {u | c.layer u < c.layer v ∧ H.Adj u v}.Finite := by
    intro v
    have hsub : {u | c.layer u < c.layer v ∧ H.Adj u v} ⊆
        {u | u ∈ c.trace v ∧ cls u = cls v} :=
      fun u hu => ⟨c.mem_trace_of_layer_lt hu.2.1.symm hu.1, hu.2.2.1⟩
    refine Set.Finite.subset ?_ hsub
    by_cases ht : (c.trace v).Finite
    · exact ht.subset fun u hu => hu.1
    by_contra hT
    obtain ⟨n, hn⟩ := exists_nat_gt (C / η (cls v))
    have hCn : C < n * η (cls v) := (div_lt_iff₀ (hη _)).1 hn
    obtain ⟨B, hB, hBn⟩ := Set.Infinite.exists_subset_card_eq hT n
    have hsum := hν v ht B fun u hu => (hB hu).1
    have hle : B.card • (η (cls v) : ENNReal) ≤ ∑ u ∈ B, ν {ω | ω u = ω v} :=
      Finset.card_nsmul_le_sum _ _ _ fun u hu => (hB hu).2 ▸ hcls u v (hB hu).2
    rw [hBn, nsmul_eq_mul] at hle
    have : ((n * η (cls v) : ℝ≥0) : ENNReal) ≤ C := by
      push_cast
      exact hle.trans hsum
    exact absurd (ENNReal.coe_le_coe.1 this) (not_le.2 hCn)
  obtain ⟨hg⟩ := nonempty_coloring_of_wellFounded H (r := fun u v => c.layer u < c.layer v)
    (InvImage.wf c.layer wellFounded_lt) (fun u v h => lt_or_gt_of_ne h.2.2) hfin
  -- The color of each vertex within its layer.
  have hcol : ∀ {u v} (ξ : Ordinal.{u}) (hu : c.layer u = ξ) (hv : c.layer v = ξ),
      G.Adj u v → (hlayer ξ).some ⟨u, hu⟩ ≠ (hlayer ξ).some ⟨v, hv⟩ :=
    fun ξ hu hv h => (hlayer ξ).some.valid (SimpleGraph.induce_adj.2 h)
  have heq : ∀ {u} (ξ : Ordinal.{u}) (hu : c.layer u = ξ),
      (hlayer (c.layer u)).some ⟨u, rfl⟩ = (hlayer ξ).some ⟨u, hu⟩ := by
    intro u ξ hu
    subst hu
    rfl
  refine ⟨SimpleGraph.Coloring.mk
    (fun v => Nat.pair (cls v) (Nat.pair (hg v) ((hlayer (c.layer v)).some ⟨v, rfl⟩))) ?_⟩
  intro u v h huv
  simp only [Nat.pair_eq_pair] at huv
  obtain ⟨hc, hgc, hl⟩ := huv
  by_cases hξ : c.layer u = c.layer v
  · rw [heq (c.layer v) hξ] at hl
    exact hcol (c.layer v) hξ rfl h hl
  · exact hg.valid (show H.Adj u v from ⟨h, hc, hξ⟩) hgc

/-- Every `C`-linear graph has a proper coloring by `ℕ`. -/
theorem nonempty_coloring_of_linear (G : SimpleGraph V) {C : ℝ≥0} (hG : Linear G C) :
    Nonempty (G.Coloring ℕ) := by
  suffices h : ∀ κ : Cardinal.{u}, ∀ (W : Type u) (H : SimpleGraph W), #W = κ → Linear H C →
      Nonempty (H.Coloring ℕ) from h _ V G rfl hG
  intro κ
  induction κ using Cardinal.lt_wf.induction with
  | _ κ ih =>
  intro W H hW hH
  rcases le_or_gt #W ℵ₀ with hc | hc
  · -- Countable graphs are colored injectively.
    have : Countable W := Cardinal.mk_le_aleph0_iff.1 hc
    obtain ⟨f, hf⟩ := Countable.exists_injective_nat W
    exact ⟨SimpleGraph.Coloring.mk f fun h heq => H.ne_of_adj h (hf heq)⟩
  · obtain ⟨c⟩ := exists_chain H hc
    obtain ⟨ν, hν, htr⟩ := exists_traceBound_law hH c
    refine nonempty_coloring_of_traceBound c htr fun ξ => ?_
    exact ih _ (hW ▸ c.card_layer_lt hc.le ξ) _ (H.induce {v | c.layer v = ξ}) rfl (hH.induce _)

end PlasmaE111

-- ===== source module PlasmaE111.Statement =====

/-!
# Statement of Erdős Problem 111: bipartizing finite subgraphs of uncountably chromatic graphs

The definitions here repeat those of `Challenge.lean` for the proof
development; Comparator requires them to agree exactly.
-/



namespace PlasmaE111

/-- The least number of edges whose deletion leaves the subgraph `H` bipartite, for `H`
with finitely many vertices (the only case used below). -/
noncomputable def bipartizationNumber {V : Type*} {G : SimpleGraph V} (H : G.Subgraph) : ℕ :=
  sInf {k : ℕ | ∃ D ⊆ H.edgeSet, D.ncard = k ∧ (H.deleteEdges D).coe.IsBipartite}

/-- `h G n` is the least bound such that every subgraph of `G` on `n` vertices can be
made bipartite by deleting at most `h G n` edges. -/
noncomputable def h {V : Type*} (G : SimpleGraph V) (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ H : G.Subgraph, H.verts.Finite ∧ H.verts.ncard = n ∧
    bipartizationNumber H = k}

/-- The chromatic number of `G` as a cardinal: the least cardinality of a set of colors
that properly colors `G`. -/
noncomputable def chromaticCardinal {V : Type u} (G : SimpleGraph V) : Cardinal.{u} :=
  sInf {κ : Cardinal.{u} | ∃ α : Type u, Cardinal.mk α = κ ∧ Nonempty (G.Coloring α)}

end PlasmaE111

-- ===== source module PlasmaE111.Bridge =====

/-!
# The challenge definitions in terms of edge costs

`bipartizationNumber H` counts the deletions that make the subgraph `H` bipartite, while
`edgeCost` minimizes the monochromatic edges over sign assignments. Deleting the
monochromatic edges of a sign assignment leaves a bipartite graph, and a 2-coloring of
what remains after deleting `D` leaves every monochromatic edge in `D`, so the two
agree. Hence the hypothesis of the challenge is `C`-linearity, and every finite edge set
of `G` on `n` vertices bounds `h G n` from below.
-/


open scoped NNReal

namespace PlasmaE111

variable {V : Type*} {G : SimpleGraph V}

/-- A finite edge set of `G` with ends in `s` is the edge set of a subgraph on `s`. -/
private theorem exists_subgraph {s : Finset V} {E : Finset (Sym2 V)} (hE : ↑E ⊆ G.edgeSet)
    (hEs : ∀ e ∈ E, ∀ v ∈ e, v ∈ s) :
    ∃ H : G.Subgraph, H.verts = ↑s ∧ H.edgeSet = ↑E := by
  refine ⟨{ verts := ↑s
            Adj := fun a b => s(a, b) ∈ E
            adj_sub := fun h => hE h
            edge_vert := fun h => hEs _ h _ (Sym2.mem_mk_left _ _)
            symm := ⟨fun a b h => by rwa [Sym2.eq_swap]⟩ }, rfl, ?_⟩
  ext e
  induction e using Sym2.ind with
  | _ a b => exact Iff.rfl

/-- The number of deletions that make a finite subgraph bipartite is the edge cost of its
edge set. -/
theorem bipartizationNumber_eq_edgeCost (H : G.Subgraph) (E : Finset (Sym2 V))
    (hE : (E : Set (Sym2 V)) = H.edgeSet) :
    bipartizationNumber H = edgeCost E := by
  classical
  -- The monochromatic edges of a sign assignment are a feasible deletion.
  have hmem : ∀ σ : V → Bool, monoCount E σ ∈ {k : ℕ | ∃ D ⊆ H.edgeSet, D.ncard = k ∧
      (H.deleteEdges D).coe.IsBipartite} := by
    intro σ
    refine ⟨↑(E.filter (mono σ)), ?_, by rw [Set.ncard_coe_finset]; rfl, ?_⟩
    · rw [← hE]
      exact Finset.coe_subset.2 (Finset.filter_subset _ _)
    · have hc := (SimpleGraph.Coloring.mk (G := (H.deleteEdges (E.filter (mono σ) : Set _)).coe)
        (fun v => σ v) ?_).colorable
      · simpa using hc
      intro a b hab heq
      rw [SimpleGraph.Subgraph.coe_adj, SimpleGraph.Subgraph.deleteEdges_adj] at hab
      apply hab.2
      have he : s(a.1, b.1) ∈ E := by
        rw [← Finset.mem_coe, hE]
        exact hab.1
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨he, heq⟩
  apply le_antisymm
  · obtain ⟨σ, hσ⟩ := exists_monoCount_eq_edgeCost E
    rw [← hσ]
    exact Nat.sInf_le (hmem σ)
  · obtain ⟨D, hD, hDk, ⟨c⟩⟩ := Nat.sInf_mem ⟨_, hmem fun _ => false⟩
    rw [bipartizationNumber, ← hDk]
    -- A 2-coloring of the rest leaves every monochromatic edge in `D`.
    let σ : V → Bool := fun v => if hv : v ∈ H.verts then finTwoEquiv (c ⟨v, hv⟩) else false
    have hDfin : D.Finite := (Set.Finite.subset (E.finite_toSet) (hE ▸ hD))
    refine (edgeCost_le_monoCount E σ).trans ?_
    rw [monoCount, ← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard ?_ hDfin
    intro e he
    rw [Finset.coe_filter] at he
    obtain ⟨heE, hmono⟩ := he
    induction e using Sym2.ind with
    | _ a b =>
      have hadj : H.Adj a b := by
        rw [← SimpleGraph.Subgraph.mem_edgeSet, ← hE]
        exact heE
      have ha := H.edge_vert hadj
      have hb := H.edge_vert hadj.symm
      by_contra hnot
      have hadj' : (H.deleteEdges D).coe.Adj ⟨a, ha⟩ ⟨b, hb⟩ := by
        rw [SimpleGraph.Subgraph.coe_adj, SimpleGraph.Subgraph.deleteEdges_adj]
        exact ⟨hadj, hnot⟩
      apply c.valid hadj'
      have hab : σ a = σ b := hmono
      simpa [σ, ha, hb] using hab

/-- The hypothesis of the challenge is `C`-linearity. -/
theorem linear_of_bipartizationNumber_le {C : ℝ}
    (hC : ∀ H : G.Subgraph, H.verts.Finite →
      (bipartizationNumber H : ℝ) ≤ C * H.verts.ncard) :
    Linear G C.toNNReal := by
  intro s E hE hEs
  obtain ⟨H, hv, he⟩ := exists_subgraph hE hEs
  have hfin : H.verts.Finite := by
    rw [hv]
    exact s.finite_toSet
  have h1 := hC H hfin
  rw [bipartizationNumber_eq_edgeCost H E he.symm, hv, Set.ncard_coe_finset] at h1
  rw [← NNReal.coe_le_coe]
  push_cast
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
  rw [Real.coe_toNNReal']
  exact le_max_left _ _

/-- A finite edge set of `G` with ends in `s` bounds `h G s.card` from below. -/
theorem edgeCost_le_h {s : Finset V} {E : Finset (Sym2 V)} (hE : ↑E ⊆ G.edgeSet)
    (hEs : ∀ e ∈ E, ∀ v ∈ e, v ∈ s) : edgeCost E ≤ h G s.card := by
  classical
  obtain ⟨H, hv, he⟩ := exists_subgraph hE hEs
  have hfin : H.verts.Finite := by
    rw [hv]
    exact s.finite_toSet
  apply le_csSup
  · -- A subgraph on `n` vertices has at most `(n + 1).choose 2` edges.
    refine ⟨(s.card + 1).choose 2, ?_⟩
    rintro k ⟨H', hH', hn, rfl⟩
    rw [bipartizationNumber_eq_edgeCost H' (hH'.toFinset.sym2.filter (· ∈ H'.edgeSet))]
    · calc edgeCost _ ≤ monoCount _ fun _ => false := edgeCost_le_monoCount _ _
        _ ≤ (hH'.toFinset.sym2.filter (· ∈ H'.edgeSet)).card := Finset.card_filter_le _ _
        _ ≤ hH'.toFinset.sym2.card := Finset.card_filter_le _ _
        _ = (s.card + 1).choose 2 := by
          rw [Finset.card_sym2, ← Set.ncard_eq_toFinset_card _ hH', hn]
    · ext e
      simp only [Finset.coe_filter, Finset.mem_sym2_iff, Set.Finite.mem_toFinset,
        Set.mem_ofPred_eq]
      exact ⟨fun h => h.2, fun h => ⟨fun v hv => H'.mem_verts_of_mem_edge h hv, h⟩⟩
  · exact ⟨H, hfin, by rw [hv, Set.ncard_coe_finset],
      bipartizationNumber_eq_edgeCost H E he.symm⟩

end PlasmaE111

-- ===== source module PlasmaE111.Reduction =====

/-!
# Reduction of Erdős Problem 111 to countable colorings of linear graphs

* **Countable deletion.** If removing a countable set leaves a countably colorable
  graph, the graph is countably colorable: give the removed vertices fresh colors.
* **Packing.** Uncountably many pairwise disjoint finite witnesses with cost above
  `2 K` per vertex include infinitely many with the same size `v` and cost `b`, since
  these are natural numbers. Then `⌊n / v⌋` of them, padded to `n` vertices, cost at least
  `b ⌊n / v⌋ > K n` for `n ≥ 2 v`.
* **The limit.** If `G` is not countably colorable, fix `K` and take a maximal family of
  pairwise disjoint witnesses. If it were countable, the remainder would be `2 K`-linear
  by maximality, hence countably colorable, and so would `G`. So it is uncountable, and
  packing gives `h G n > K n` for all large `n`.
-/


open Filter Cardinal
open scoped NNReal


namespace PlasmaE111

variable {V : Type u}

/-- A witness costing more than `2 K` per vertex has a vertex. -/
private theorem card_pos_of_lt_edgeCost {K : ℝ} {s : Finset V} {E : Finset (Sym2 V)}
    (hEs : ∀ e ∈ E, ∀ v ∈ e, v ∈ s) (hcost : 2 * K * s.card < edgeCost E) : 0 < s.card := by
  by_contra hs
  have hs' : s = ∅ := Finset.card_eq_zero.1 (by omega)
  have hE : E = ∅ := Finset.eq_empty_of_forall_notMem fun e he => by
    simpa [hs'] using hEs e he _ e.out_fst_mem
  have h0 : edgeCost E = 0 := Nat.eq_zero_of_le_zero
    ((edgeCost_le_monoCount E fun _ => false).trans (by simp [monoCount, hE]))
  simp [hs', h0] at hcost

/-- Relabeling along an embedding does not lower the edge cost. -/
private theorem edgeCost_le_edgeCost_map {W : Type*} (f : W ↪ V) (E : Finset (Sym2 W)) :
    edgeCost E ≤ edgeCost (E.map f.sym2Map) := by
  classical
  refine le_ciInf fun σ => (edgeCost_le_monoCount E (σ ∘ f)).trans_eq ?_
  rw [monoCount, monoCount, Finset.filter_map, Finset.card_map]
  congr 1
  apply Finset.filter_congr
  intro e _
  induction e using Sym2.ind with
  | _ a b => exact Iff.rfl

/-- Edge sets with pairwise disjoint vertex sets cost at least the sum of their costs. -/
private theorem sum_edgeCost_le_edgeCost_biUnion [DecidableEq (Sym2 V)] {ι : Type*}
    (T : Finset ι) (s : ι → Finset V) (E : ι → Finset (Sym2 V))
    (hdisj : (T : Set ι).PairwiseDisjoint s) (hEs : ∀ i, ∀ e ∈ E i, ∀ v ∈ e, v ∈ s i) :
    ∑ i ∈ T, edgeCost (E i) ≤ edgeCost (T.biUnion E) := by
  classical
  refine le_ciInf fun σ => ?_
  rw [monoCount, Finset.filter_biUnion, Finset.card_biUnion]
  · exact Finset.sum_le_sum fun i _ => edgeCost_le_monoCount (E i) σ
  · intro i hi j hj hij
    rw [Function.onFun, Finset.disjoint_left]
    intro e hei hej
    exact Finset.disjoint_left.1 (hdisj hi hj hij)
      (hEs i e (Finset.mem_filter.1 hei).1 _ e.out_fst_mem)
      (hEs j e (Finset.mem_filter.1 hej).1 _ e.out_fst_mem)

/-- Countable deletion. -/
theorem nonempty_coloring_of_countable_compl {G : SimpleGraph V} {S : Set V}
    (hS : S.Countable) (h : Nonempty ((G.induce Sᶜ).Coloring ℕ)) :
    Nonempty (G.Coloring ℕ) := by
  classical
  obtain ⟨c⟩ := h
  have := hS.to_subtype
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat S
  -- Odd colors for the removed vertices, even colors for the rest.
  refine ⟨SimpleGraph.Coloring.mk
    (fun v => if hv : v ∈ S then 2 * f ⟨v, hv⟩ + 1 else 2 * c ⟨v, hv⟩) ?_⟩
  intro a b hab
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp only [ha, hb, ↓reduceDIte]
  · intro heq
    exact hab.ne (congrArg Subtype.val (hf (by omega : f ⟨a, ha⟩ = f ⟨b, hb⟩)))
  · omega
  · omega
  · intro heq
    exact c.valid (show (G.induce Sᶜ).Adj ⟨a, ha⟩ ⟨b, hb⟩ from hab) (by omega)

/-- Packing. -/
theorem eventually_lt_h_of_uncountable {G : SimpleGraph V} {ι : Type*} [Uncountable ι]
    (K : ℝ) (s : ι → Finset V) (E : ι → Finset (Sym2 V))
    (hdisj : Pairwise fun i j => Disjoint (s i) (s j)) (hE : ∀ i, ↑(E i) ⊆ G.edgeSet)
    (hEs : ∀ i, ∀ e ∈ E i, ∀ v ∈ e, v ∈ s i)
    (hcost : ∀ i, 2 * K * (s i).card < edgeCost (E i)) :
    ∀ᶠ n : ℕ in atTop, K * n < h G n := by
  classical
  -- Infinitely many witnesses share their size `v` and cost `b`.
  obtain ⟨⟨v, b⟩, hp⟩ : ∃ p : ℕ × ℕ, {i | ((s i).card, edgeCost (E i)) = p}.Infinite := by
    by_contra hfin
    simp only [not_exists, Set.not_infinite] at hfin
    apply not_countable (α := ι)
    rw [← Set.countable_univ_iff]
    have hU : (Set.univ : Set ι) = ⋃ p : ℕ × ℕ, {i | ((s i).card, edgeCost (E i)) = p} := by
      ext i
      simp
    rw [hU]
    exact Set.countable_iUnion fun p => (hfin p).countable
  have hfib : ∀ i ∈ {i | ((s i).card, edgeCost (E i)) = (v, b)}, (s i).card = v ∧
      edgeCost (E i) = b := fun i hi => by simpa using hi
  obtain ⟨i₀, hi₀⟩ := hp.nonempty
  have hv : 0 < v := (hfib i₀ hi₀).1 ▸ card_pos_of_lt_edgeCost (hEs i₀) (hcost i₀)
  have hb : 2 * K * v < b := by
    have := hcost i₀
    rwa [(hfib i₀ hi₀).1, (hfib i₀ hi₀).2] at this
  have hpd : ∀ T₀ : Finset ι, (T₀ : Set ι).PairwiseDisjoint s := fun T₀ i _ j _ hij => hdisj hij
  rw [Filter.eventually_atTop]
  refine ⟨2 * v, fun n hn => ?_⟩
  -- Take `q = n / v` of `n` such witnesses and pad their vertices to `n`.
  set q := n / v with hq
  obtain ⟨T', hT'F, hT'⟩ := hp.exists_subset_card_eq n
  obtain ⟨T, hTT', hT⟩ := Finset.exists_subset_card_eq (s := T') (n := q)
    (by rw [hT']; exact Nat.div_le_self n v)
  have hcardU : ∀ T₀ ⊆ T', (T₀.biUnion s).card = T₀.card * v := by
    intro T₀ hT₀
    rw [Finset.card_biUnion (hpd T₀), Finset.sum_const_nat fun i hi => (hfib i (hT'F (hT₀ hi))).1]
  obtain ⟨s', hUs', -, hs'⟩ := Finset.exists_subsuperset_card_eq (n := n)
    (Finset.biUnion_subset_biUnion_of_subset_left s hTT')
    (by rw [hcardU T hTT', hT]; exact Nat.div_mul_le_self n v)
    (by rw [hcardU T' le_rfl, hT']; exact Nat.le_mul_of_pos_right n hv)
  have hE' : ↑(T.biUnion E) ⊆ G.edgeSet := by
    simp only [Finset.coe_biUnion, Set.iUnion_subset_iff]
    exact fun i _ => hE i
  have hEs' : ∀ e ∈ T.biUnion E, ∀ u ∈ e, u ∈ s' := by
    intro e he u hu
    obtain ⟨i, hi, hei⟩ := Finset.mem_biUnion.1 he
    exact hUs' (Finset.mem_biUnion.2 ⟨i, hi, hEs i e hei u hu⟩)
  have hcostE' : q * b ≤ edgeCost (T.biUnion E) := by
    calc q * b = ∑ i ∈ T, edgeCost (E i) := by
          rw [Finset.sum_const_nat fun i hi => (hfib i (hT'F (hTT' hi))).2, hT]
      _ ≤ _ := sum_edgeCost_le_edgeCost_biUnion T s E (hpd T) hEs
  have hh := edgeCost_le_h hE' hEs'
  rw [hs'] at hh
  -- Then `n < 2 q v`, so `K n < q b`.
  have hq1 : 1 ≤ q := (Nat.le_div_iff_mul_le hv).2 (by omega)
  have hlt : n < v * q + v := by
    have h1 := Nat.div_add_mod n v
    rw [← hq] at h1
    have h2 := Nat.mod_lt n hv
    omega
  have hnR : (n : ℝ) ≤ 2 * q * v := by
    have h1 : (n : ℝ) < v * q + v := by exact_mod_cast hlt
    have h2 : (v : ℝ) ≤ v * q := by exact_mod_cast Nat.le_mul_of_pos_right v hq1
    linarith
  have hq1R : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hbig : K * n < q * b := by
    rcases le_or_gt 0 K with hK | hK
    · calc K * n ≤ K * (2 * q * v) := mul_le_mul_of_nonneg_left hnR hK
        _ = q * (2 * K * v) := by ring
        _ < q * b := mul_lt_mul_of_pos_left hb (by linarith)
    · have : (0 : ℝ) ≤ q * b := by positivity
      nlinarith
  calc K * n < q * b := hbig
    _ ≤ h G n := by exact_mod_cast hcostE'.trans hh

/-- If every linear graph is countably colorable, then `h G n / n → ∞` for every graph `G`
that is not countably colorable. -/
theorem tendsto_of_isEmpty_coloring
    (hmain : ∀ (W : Type u) (H : SimpleGraph W) (C : ℝ≥0), Linear H C →
      Nonempty (H.Coloring ℕ))
    (G : SimpleGraph V) (hG : IsEmpty (G.Coloring ℕ)) :
    Tendsto (fun n : ℕ => (h G n : ℝ) / n) atTop atTop := by
  classical
  suffices hK : ∀ K : ℝ, ∀ᶠ n : ℕ in atTop, K * n < h G n by
    rw [Filter.tendsto_atTop]
    intro K
    filter_upwards [hK K, Filter.eventually_gt_atTop 0] with n hn hn0
    rw [le_div_iff₀ (by exact_mod_cast hn0)]
    exact hn.le
  intro K
  -- The witnesses: edge sets of `G` with ends in `s` costing more than `2 K |s|`.
  let W : Set (Finset V × Finset (Sym2 V)) := {w | ↑w.2 ⊆ G.edgeSet ∧
    (∀ e ∈ w.2, ∀ v ∈ e, v ∈ w.1) ∧ 2 * K * w.1.card < edgeCost w.2}
  let 𝒮 : Set (Set (Finset V × Finset (Sym2 V))) :=
    {𝓕 | 𝓕 ⊆ W ∧ 𝓕.Pairwise fun x y => Disjoint x.1 y.1}
  -- A maximal family of witnesses with pairwise disjoint vertex sets.
  obtain ⟨𝓕, h𝓕⟩ := zorn_subset 𝒮 fun c hc hchain => by
    refine ⟨⋃₀ c, ⟨Set.sUnion_subset fun 𝓖 h𝓖 => (hc h𝓖).1, ?_⟩,
      fun 𝓖 h𝓖 => Set.subset_sUnion_of_mem h𝓖⟩
    rintro x ⟨𝓖, h𝓖, hx⟩ y ⟨𝓗, h𝓗, hy⟩ hxy
    rcases hchain.total h𝓖 h𝓗 with h | h
    · exact (hc h𝓗).2 (h hx) hy hxy
    · exact (hc h𝓖).2 hx (h hy) hxy
  -- If it were countable, the rest of `G` would be `2 K`-linear, so `G` would be
  -- countably colorable.
  have hF : ¬𝓕.Countable := by
    intro hcount
    set S : Set V := ⋃ x ∈ 𝓕, (x.1 : Set V) with hS
    have hScount : S.Countable := hcount.biUnion fun x _ => x.1.countable_toSet
    refine hG.false (nonempty_coloring_of_countable_compl hScount
      (hmain _ (G.induce Sᶜ) (2 * K).toNNReal ?_)).some
    intro s' E' hE' hEs'
    by_contra hlt
    rw [not_le] at hlt
    let f : ↥Sᶜ ↪ V := Function.Embedding.subtype _
    let w : Finset V × Finset (Sym2 V) := (s'.map f, E'.map f.sym2Map)
    have hw : w ∈ W := by
      refine ⟨?_, ?_, ?_⟩
      · intro e he
        obtain ⟨e', he', rfl⟩ := Finset.mem_map.1 (Finset.mem_coe.1 he)
        induction e' using Sym2.ind with
        | _ a b => exact hE' he'
      · intro e he u hu
        obtain ⟨e', he', rfl⟩ := Finset.mem_map.1 he
        rw [Function.Embedding.sym2Map_apply] at hu
        obtain ⟨a, ha, rfl⟩ := Sym2.mem_map.1 hu
        exact Finset.mem_map_of_mem f (hEs' e' he' a ha)
      · have h1 : ((2 * K).toNNReal * s'.card : ℝ) < edgeCost E' := by exact_mod_cast hlt
        have h2 : (edgeCost E' : ℝ) ≤ edgeCost (E'.map f.sym2Map) := by
          exact_mod_cast edgeCost_le_edgeCost_map f E'
        have h3 : 2 * K ≤ ((2 * K).toNNReal : ℝ) := by
          rw [Real.coe_toNNReal']
          exact le_max_left _ _
        simp only [w, Finset.card_map]
        calc 2 * K * s'.card ≤ (2 * K).toNNReal * s'.card :=
              mul_le_mul_of_nonneg_right h3 (Nat.cast_nonneg _)
          _ < edgeCost E' := h1
          _ ≤ edgeCost (E'.map f.sym2Map) := h2
    have hdisjw : ∀ x ∈ 𝓕, Disjoint x.1 w.1 := by
      intro x hx
      rw [Finset.disjoint_left]
      intro u hux huw
      obtain ⟨a, _, rfl⟩ := Finset.mem_map.1 huw
      exact a.2 (Set.mem_biUnion hx hux)
    have hins : insert w 𝓕 ∈ 𝒮 := by
      refine ⟨Set.insert_subset hw h𝓕.1.1, ?_⟩
      rw [Set.pairwise_insert]
      exact ⟨h𝓕.1.2, fun x hx _ => ⟨(hdisjw x hx).symm, hdisjw x hx⟩⟩
    have hw𝓕 : w ∈ 𝓕 :=
      (h𝓕.2 hins (Set.subset_insert _ _) : insert w 𝓕 ⊆ 𝓕) (Set.mem_insert _ _)
    have hpos := card_pos_of_lt_edgeCost hw.2.1 hw.2.2
    have hempty := hdisjw w hw𝓕
    rw [disjoint_self, Finset.bot_eq_empty] at hempty
    rw [hempty] at hpos
    simp at hpos
  have : Uncountable 𝓕 := ⟨hF⟩
  exact eventually_lt_h_of_uncountable K (fun x : 𝓕 => x.1.1) (fun x => x.1.2)
    (fun x y hxy => h𝓕.1.2 x.2 y.2 (Subtype.coe_ne_coe.2 hxy)) (fun x => (h𝓕.1.1 x.2).1)
    (fun x => (h𝓕.1.1 x.2).2.1) (fun x => (h𝓕.1.1 x.2).2.2)

/-- A graph of chromatic number `ℵ₁` is not countably colorable. -/
theorem isEmpty_coloring_of_chromaticCardinal {G : SimpleGraph V}
    (hG : chromaticCardinal G = ℵ₁) : IsEmpty (G.Coloring ℕ) := by
  refine ⟨fun c => ?_⟩
  let c' : G.Coloring (ULift.{u} ℕ) := SimpleGraph.Coloring.mk (fun v => ULift.up (c v))
    fun hab heq => c.valid hab (congrArg ULift.down heq)
  have hle : chromaticCardinal G ≤ ℵ₀ := csInf_le' ⟨ULift.{u} ℕ, by simp, ⟨c'⟩⟩
  rw [hG] at hle
  exact lt_irrefl _ (aleph0_lt_aleph_one.trans_le hle)

end PlasmaE111

-- ===== source module PlasmaE111.FinalAssembly =====

/-!
# Assembly of Erdős Problem 111: bipartizing finite subgraphs of uncountably chromatic graphs

The hypothesis of `countably_colorable_of_linear_proved` is `C`-linearity
(`linear_of_bipartizationNumber_le`), so the theorem is `nonempty_coloring_of_linear`.
The reduction (`tendsto_of_isEmpty_coloring`) turns it into the limit for every graph
that is not countably colorable, and a graph of chromatic number `ℵ₁` is one of them.
-/


open Filter
open scoped Cardinal


namespace PlasmaE111

/-- A graph in which every finite subgraph on `m` vertices can be made bipartite by
deleting at most `C m` edges has countable chromatic number. -/
theorem countably_colorable_of_linear_proved {V : Type u} (G : SimpleGraph V) (C : ℝ)
    (hC : ∀ H : G.Subgraph, H.verts.Finite →
      (bipartizationNumber H : ℝ) ≤ C * H.verts.ncard) :
    Nonempty (G.Coloring ℕ) :=
  nonempty_coloring_of_linear G (linear_of_bipartizationNumber_le hC)

/-- `h G n / n → ∞` for every graph `G` that is not countably colorable. -/
theorem tendsto_of_not_countably_colorable_proved {V : Type u} (G : SimpleGraph V)
    (hG : IsEmpty (G.Coloring ℕ)) :
    Tendsto (fun n : ℕ => (h G n : ℝ) / n) atTop atTop :=
  tendsto_of_isEmpty_coloring (fun _ H _ hH => nonempty_coloring_of_linear H hH) G hG

/-- Erdős Problem 111: `h G n / n → ∞` for every graph `G` of chromatic number `ℵ₁`. -/
theorem erdos_111_proved {V : Type u} (G : SimpleGraph V) (hG : chromaticCardinal G = ℵ₁) :
    Tendsto (fun n : ℕ => (h G n : ℝ) / n) atTop atTop :=
  tendsto_of_not_countably_colorable_proved G (isEmpty_coloring_of_chromaticCardinal hG)

end PlasmaE111

-- ===== source module Solution =====

/-!
# Proof of Erdős Problem 111: bipartizing finite subgraphs of uncountably chromatic graphs

Comparator checks the three theorems in this module against the Mathlib-only
statements in `Challenge.lean`.
-/


open Filter
open scoped Cardinal


namespace PlasmaE111

/-- A graph in which every finite subgraph on `m` vertices can be made bipartite by
deleting at most `C m` edges has countable chromatic number. -/
theorem countably_colorable_of_linear {V : Type u} (G : SimpleGraph V) (C : ℝ)
    (hC : ∀ H : G.Subgraph, H.verts.Finite →
      (bipartizationNumber H : ℝ) ≤ C * H.verts.ncard) :
    Nonempty (G.Coloring ℕ) :=
  countably_colorable_of_linear_proved G C hC

/-- `h G n / n → ∞` for every graph `G` that is not countably colorable. -/
theorem tendsto_of_not_countably_colorable {V : Type u} (G : SimpleGraph V)
    (hG : IsEmpty (G.Coloring ℕ)) :
    Tendsto (fun n : ℕ => (h G n : ℝ) / n) atTop atTop :=
  tendsto_of_not_countably_colorable_proved G hG

/-- Erdős Problem 111: `h G n / n → ∞` for every graph `G` of chromatic number `ℵ₁`. -/
theorem erdos_111 {V : Type u} (G : SimpleGraph V) (hG : chromaticCardinal G = ℵ₁) :
    Tendsto (fun n : ℕ => (h G n : ℝ) / n) atTop atTop :=
  erdos_111_proved G hG

end PlasmaE111

namespace OMA.E111Bridge

open SimpleGraph

/-- A graph of chromatic cardinal aleph one has no colouring by the natural numbers. -/
theorem isEmpty_coloring_nat {V : Type} (G : SimpleGraph V)
    (hG : G.chromaticCardinal = Cardinal.aleph 1) : IsEmpty (G.Coloring ℕ) := by
  by_contra hne
  rw [not_isEmpty_iff] at hne
  have hle : G.chromaticCardinal ≤ Cardinal.aleph0 := by
    unfold SimpleGraph.chromaticCardinal
    exact csInf_le' ⟨ℕ, Cardinal.mk_nat, hne⟩
  rw [hG] at hle
  exact absurd hle (not_le.mpr Cardinal.aleph0_lt_aleph_one)

/-- The empty graph is bipartite. -/
theorem bot_isBipartite {W : Type*} : (⊥ : SimpleGraph W).IsBipartite :=
  ⟨SimpleGraph.Coloring.mk (fun _ => 0) (fun h => h.elim)⟩

/-- The bipartite distance of an induced subgraph on a finite set is attained. -/
theorem exists_bipartite_attaining {V : Type*} (G : SimpleGraph V) (S : Set V) :
    ∃ H' : SimpleGraph S, H' ≤ G.induce S ∧ H'.IsBipartite ∧
      Set.ncard ((G.induce S).edgeSet \ H'.edgeSet) = Erdos111.bipartiteDistance (G.induce S) := by
  have hne : {k : ℕ | ∃ H : SimpleGraph S, H ≤ G.induce S ∧ H.IsBipartite ∧
      Set.ncard ((G.induce S).edgeSet \ H.edgeSet) = k}.Nonempty :=
    ⟨_, ⊥, bot_le, bot_isBipartite, rfl⟩
  exact Nat.sInf_mem hne

/-- Deleting from a subgraph what a bipartite spanning subgraph of the induced graph misses
costs no more than the bipartite distance of the induced graph. -/
theorem bipartizationNumber_le {V : Type*} (G : SimpleGraph V) (H : G.Subgraph)
    (hfin : H.verts.Finite) :
    PlasmaE111.bipartizationNumber H ≤ Erdos111.bipartiteDistance (G.induce H.verts) := by
  classical
  obtain ⟨H', hle, ⟨c⟩, hcard⟩ := exists_bipartite_attaining G H.verts
  let D : Set (Sym2 V) := {e | e ∈ H.edgeSet ∧
    ¬ ∃ a b : H.verts, s(a.1, b.1) = e ∧ H'.Adj a b}
  have hDsub : D ⊆ H.edgeSet := fun e he => he.1
  have hbip : (H.deleteEdges D).coe.IsBipartite := by
    refine ⟨SimpleGraph.Coloring.mk (fun x => c ⟨x.1, x.2⟩) ?_⟩
    intro x y hxy
    have hxy' : (H.deleteEdges D).Adj x.1 y.1 := hxy
    rw [SimpleGraph.Subgraph.deleteEdges_adj] at hxy'
    obtain ⟨hH, hnD⟩ := hxy'
    have hin : ∃ a b : H.verts, s(a.1, b.1) = s(x.1, y.1) ∧ H'.Adj a b := by
      by_contra hcon
      exact hnD ⟨hH, hcon⟩
    obtain ⟨a, b, hab, hadj⟩ := hin
    rw [Sym2.eq_iff] at hab
    rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have ha : a = ⟨x.1, x.2⟩ := Subtype.ext h1
      have hb : b = ⟨y.1, y.2⟩ := Subtype.ext h2
      rw [ha, hb] at hadj
      exact c.valid hadj
    · have ha : a = ⟨y.1, y.2⟩ := Subtype.ext h1
      have hb : b = ⟨x.1, x.2⟩ := Subtype.ext h2
      rw [ha, hb] at hadj
      exact (c.valid hadj).symm
  have hfinT : ((G.induce H.verts).edgeSet \ H'.edgeSet).Finite := by
    have : Finite H.verts := hfin
    exact Set.toFinite _
  have himg : D ⊆ (Sym2.map Subtype.val) '' ((G.induce H.verts).edgeSet \ H'.edgeSet) := by
    intro e he
    obtain ⟨heH, hno⟩ := he
    induction e using Sym2.ind with
    | _ x y =>
      have hadj : H.Adj x y := heH
      have hx : x ∈ H.verts := H.edge_vert hadj
      have hy : y ∈ H.verts := H.edge_vert hadj.symm
      refine ⟨s(⟨x, hx⟩, ⟨y, hy⟩), ⟨?_, ?_⟩, rfl⟩
      · exact H.adj_sub hadj
      · intro hH'
        exact hno ⟨⟨x, hx⟩, ⟨y, hy⟩, rfl, hH'⟩
  have h1 : D.ncard ≤ ((G.induce H.verts).edgeSet \ H'.edgeSet).ncard :=
    (Set.ncard_le_ncard himg (hfinT.image _)).trans (Set.ncard_image_le hfinT)
  have h2 : PlasmaE111.bipartizationNumber H ≤ D.ncard :=
    Nat.sInf_le ⟨D, hDsub, rfl, hbip⟩
  omega

/-- For a set of `n` vertices the bipartite distance of the induced graph is at most
`n.choose 2`. -/
theorem bipartiteDistance_le_choose {V : Type*} (G : SimpleGraph V) (S : Set V) (n : ℕ)
    (hn : 1 ≤ n) (hS : S.ncard = n) :
    Erdos111.bipartiteDistance (G.induce S) ≤ n.choose 2 := by
  classical
  have hfin : S.Finite := Set.finite_of_ncard_pos (by omega)
  have : Fintype S := hfin.fintype
  have h1 : Erdos111.bipartiteDistance (G.induce S) ≤
      Set.ncard ((G.induce S).edgeSet \ (⊥ : SimpleGraph S).edgeSet) :=
    Nat.sInf_le ⟨⊥, bot_le, bot_isBipartite, rfl⟩
  have h2 : Set.ncard ((G.induce S).edgeSet \ (⊥ : SimpleGraph S).edgeSet) ≤
      (G.induce S).edgeSet.ncard := Set.ncard_le_ncard Set.diff_subset (Set.toFinite _)
  have h3 : (G.induce S).edgeSet.ncard = (G.induce S).edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card']
    rfl
  have h4 := (G.induce S).card_edgeFinset_le_card_choose_two
  have h5 : Fintype.card S = n := by
    rw [← hS, Set.ncard_eq_toFinset_card', Set.toFinset_card]
  rw [h5] at h4
  omega

/-- The quantity of the source proof is at most the quantity of the Formal Conjectures
statement. -/
theorem h_le_hG {V : Type*} (G : SimpleGraph V) (n : ℕ) (hn : 1 ≤ n) :
    PlasmaE111.h G n ≤ Erdos111.hG G n := by
  unfold PlasmaE111.h
  apply csSup_le'
  rintro k ⟨H, hfin, hcard, rfl⟩
  refine (bipartizationNumber_le G H hfin).trans ?_
  unfold Erdos111.hG
  apply le_csSup
  · refine ⟨n.choose 2, ?_⟩
    rintro k ⟨S, hS, rfl⟩
    exact bipartiteDistance_le_choose G S n hn hS
  · exact ⟨H.verts, hcard, rfl⟩

end OMA.E111Bridge

theorem OMA.solution : type_of% @Erdos111.erdos_111 := by
  intro V G hG
  have hempty := OMA.E111Bridge.isEmpty_coloring_nat G hG
  have ht := PlasmaE111.tendsto_of_not_countably_colorable G hempty
  refine Filter.tendsto_atTop_mono' Filter.atTop ?_ ht
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hle := OMA.E111Bridge.h_le_hG G n hn
  have hle' : (PlasmaE111.h G n : ℝ) ≤ (Erdos111.hG G n : ℝ) := by exact_mod_cast hle
  exact div_le_div_of_nonneg_right hle' (by positivity)
