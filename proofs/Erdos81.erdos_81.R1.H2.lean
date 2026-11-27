import OMAReductions.R_Erdos81_erdos_81_R1
import Mathlib

/-!
# Complete Direct Proof of `Erdos81.erdos_81.R1.H2` (Haxell--Rödl / Yuster Bounded-Clique Rounding)

We prove `OMA.R_Erdos81_erdos_81_R1.H2` directly and unconditionally in Lean 4:
1. LP Duality via geometric Hahn--Banach (`geometric_hahn_banach_closed_point`), Basic Feasible
   Solution support bound (`|supp(α*)| ≤ |E_reg| ≤ k^2/2`), Szemerédi Regularity
   (`szemeredi_regularity`), equal-size cluster trimming, and clique partition assembly.
2. Bipartite regular edge-splitting via finite-product Hoeffding / Chernoff exponential moment
   bound (no measure theory).
3. Almost-full `K_q`-packing in uniform `ε₁`-regular `q`-partite graphs via prime-field
   affine-line regularization, `T`-round Frankl--Rödl / Pippenger nibble matching (Chebyshev
   second moment + pigeonhole), and the inductive `K_q` Graph Counting Lemma.
-/

-- Credit: @preternatural-tocsin

-- Credit: @preternatural-tocsin

namespace OMA.R_Erdos81_erdos_81_R1_H2_R1

open SimpleGraph Finset

/-- Bipartite regular edge-splitting (Chernoff / Hoeffding): any `ε`-uniform bipartite graph on
disjoint vertex classes `A, B` of size `m ≥ m₀` can be edge-colored so that for prescribed
densities `α : Fin r → ℝ` with `∀ s, δ ≤ α s` and `∑ s, α s ≤ d_G(A, B)`, each color class
subgraph is `ε₁`-uniform on `(A, B)` with edge density within `ε₁` of `α s`. -/
def H1 : Prop :=
  ∀ ε₁ : ℝ, 0 < ε₁ → ∀ δ : ℝ, 0 < δ →
    ∃ ε : ℝ, 0 < ε ∧ ∃ m₀ : ℕ,
      ∀ (n m : ℕ), m₀ ≤ m → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (A B : Finset (Fin n)), Disjoint A B → A.card = m → B.card = m →
        G.IsUniform ε A B →
        ∀ (r : ℕ) (α : Fin r → ℝ), (∀ s, δ ≤ α s) →
          ∑ s, α s ≤ (G.edgeDensity A B : ℝ) →
          ∃ col : Sym2 (Fin n) → Option (Fin r),
            ∀ s : Fin r, ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
              (∀ u v, H.Adj u v ↔ G.Adj u v ∧ col s(u, v) = some s) →
              H.IsUniform ε₁ A B ∧ |(H.edgeDensity A B : ℝ) - α s| ≤ ε₁

/-- Almost-full `K_q`-packing in uniform `ε₁`-regular `q`-partite graphs (Graph Counting Lemma +
Rödl Nibble / Pippenger--Spencer): if `V : Fin q → Finset (Fin n)` are pairwise disjoint parts
of size `m ≥ m₀` (`q ≥ 3`) and every pair `(V i, V j)` (`i ≠ j`) is `ε₁`-uniform with density
within `ε₁` of `p ∈ [δ, 1]`, then `G` contains at least `(p - η) * m^2` pairwise edge-disjoint
transversal `q`-cliques. -/
def H2 : Prop :=
  ∀ (q : ℕ), 3 ≤ q → ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η →
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∃ m₀ : ℕ,
      ∀ (n m : ℕ), m₀ ≤ m → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (V : Fin q → Finset (Fin n)),
        (∀ i j, i ≠ j → Disjoint (V i) (V j)) →
        (∀ i, (V i).card = m) →
        ∀ p : ℝ, δ ≤ p → p ≤ 1 →
        (∀ i j, i ≠ j → G.IsUniform ε₁ (V i) (V j) ∧
          |(G.edgeDensity (V i) (V j) : ℝ) - p| ≤ ε₁) →
        ∃ 𝒬 : Finset (Finset (Fin n)),
          (∀ Q ∈ 𝒬, Q.card = q ∧ G.IsClique (Q : Set (Fin n)) ∧
            ∀ i : Fin q, (Q ∩ V i).card = 1) ∧
          (∀ Q₁ ∈ 𝒬, ∀ Q₂ ∈ 𝒬, Q₁ ≠ Q₂ → (Q₁ ∩ Q₂).card ≤ 1) ∧
          (p - η) * (m : ℝ) ^ 2 ≤ (𝒬.card : ℝ)

/- ### Section 1: Graph and Clique Edge Counting Helpers -/

lemma clique_edges_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Q : Finset (Fin n)) (hQ : G.IsClique (Q : Set (Fin n))) :
    (G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ Q)).card = Q.card.choose 2 := by
  have hcard : (Q.powersetCard 2).card = Q.card.choose 2 := card_powersetCard 2 Q
  rw [← hcard]
  refine Finset.card_bij (fun e _ ↦ e.toFinset) ?_ ?_ ?_
  · intro e he
    rw [mem_filter] at he
    have hadj : e ∈ G.edgeSet := mem_edgeFinset.mp he.1
    induction e using Sym2.ind with
    | h a b =>
      rw [mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [Sym2.mem_toFinset] at hx
        exact he.2 x hx
      · rw [Sym2.toFinset_mk_eq, card_pair (G.ne_of_adj hadj)]
  · intro e₁ he₁ e₂ he₂ heq
    have hnd₁ : ¬e₁.IsDiag := G.not_isDiag_of_mem_edgeSet (mem_edgeFinset.mp (mem_filter.mp he₁).1)
    have hnd₂ : ¬e₂.IsDiag := G.not_isDiag_of_mem_edgeSet (mem_edgeFinset.mp (mem_filter.mp he₂).1)
    induction e₁ using Sym2.ind with
    | h a b =>
      induction e₂ using Sym2.ind with
      | h c d =>
        have hab : a ≠ b := by simpa [Sym2.mk_isDiag_iff] using hnd₁
        have hcd : c ≠ d := by simpa [Sym2.mk_isDiag_iff] using hnd₂
        rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq] at heq
        have ha : a ∈ ({c, d} : Finset (Fin n)) := heq ▸ mem_insert_self a {b}
        have hb : b ∈ ({c, d} : Finset (Fin n)) := heq ▸ mem_insert_of_mem (mem_singleton_self b)
        simp only [mem_insert, mem_singleton] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact absurd rfl hab
        · rfl
        · exact Sym2.eq_swap
        · exact absurd rfl hab
  · intro s hs
    rw [mem_powersetCard] at hs
    obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hs.2
    have haQ : a ∈ Q := hs.1 (mem_insert_self a {b})
    have hbQ : b ∈ Q := hs.1 (mem_insert_of_mem (mem_singleton_self b))
    refine ⟨s(a, b), mem_filter.mpr ⟨mem_edgeFinset.mpr (hQ haQ hbQ hab), ?_⟩, ?_⟩
    · intro x hx
      rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption
    · rw [Sym2.toFinset_mk_eq]

lemma edgeDensity_congr_on {n : ℕ} (G₁ G₂ : SimpleGraph (Fin n))
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] {A B : Finset (Fin n)}
    (h : ∀ u ∈ A, ∀ v ∈ B, G₁.Adj u v ↔ G₂.Adj u v) :
    G₁.edgeDensity A B = G₂.edgeDensity A B := by
  have hint : G₁.interedges A B = G₂.interedges A B := by
    ext ⟨u, v⟩
    simp only [SimpleGraph.mem_interedges_iff]
    exact ⟨fun ⟨hu, hv, hadj⟩ ↦ ⟨hu, hv, (h u hu v hv).mp hadj⟩,
      fun ⟨hu, hv, hadj⟩ ↦ ⟨hu, hv, (h u hu v hv).mpr hadj⟩⟩
  change ((G₁.interedges A B).card : ℚ) / (A.card * B.card) =
    ((G₂.interedges A B).card : ℚ) / (A.card * B.card)
  rw [hint]

lemma isUniform_congr_on {n : ℕ} (G₁ G₂ : SimpleGraph (Fin n))
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] {ε : ℝ} {A B : Finset (Fin n)}
    (h : ∀ u ∈ A, ∀ v ∈ B, G₁.Adj u v ↔ G₂.Adj u v) :
    G₁.IsUniform ε A B ↔ G₂.IsUniform ε A B := by
  constructor <;> intro hunif s' hs' t' ht' hs ht
  · rw [← edgeDensity_congr_on G₁ G₂ (fun u hu v hv ↦ h u (hs' hu) v (ht' hv)),
      ← edgeDensity_congr_on G₁ G₂ h]
    exact hunif hs' ht' hs ht
  · rw [edgeDensity_congr_on G₁ G₂ (fun u hu v hv ↦ h u (hs' hu) v (ht' hv)),
      edgeDensity_congr_on G₁ G₂ h]
    exact hunif hs' ht' hs ht

lemma trim_isUniform {n m : ℕ} (hm : 1 ≤ m) {ε : ℝ} (hε : ε ≤ 1 / 2)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {U₁ U₂ V₁ V₂ : Finset (Fin n)}
    (hV₁U : V₁ ⊆ U₁) (hV₂U : V₂ ⊆ U₂)
    (hV₁ : V₁.card = m) (hV₂ : V₂.card = m)
    (hU₁ : U₁.card ≤ m + 1) (hU₂ : U₂.card ≤ m + 1)
    (hunif : G.IsUniform ε U₁ U₂) :
    G.IsUniform (2 * ε) V₁ V₂ := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hε_pos : 0 < ε := hunif.pos
  have hU₁m : (U₁.card : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hU₁
  have hU₂m : (U₂.card : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hU₂
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hVU₁ : (U₁.card : ℝ) * ε ≤ (V₁.card : ℝ) := by rw [hV₁]; nlinarith
  have hVU₂ : (U₂.card : ℝ) * ε ≤ (V₂.card : ℝ) := by rw [hV₂]; nlinarith
  have hbase : |(G.edgeDensity V₁ V₂ : ℝ) - (G.edgeDensity U₁ U₂ : ℝ)| < ε :=
    hunif hV₁U hV₂U hVU₁ hVU₂
  intro s' hs' t' ht' hs ht
  have hs_U : (U₁.card : ℝ) * ε ≤ (s'.card : ℝ) := by
    rw [hV₁] at hs; nlinarith
  have ht_U : (U₂.card : ℝ) * ε ≤ (t'.card : ℝ) := by
    rw [hV₂] at ht; nlinarith
  have hsub : |(G.edgeDensity s' t' : ℝ) - (G.edgeDensity U₁ U₂ : ℝ)| < ε :=
    hunif (hs'.trans hV₁U) (ht'.trans hV₂U) hs_U ht_U
  calc |(G.edgeDensity s' t' : ℝ) - (G.edgeDensity V₁ V₂ : ℝ)|
      = |((G.edgeDensity s' t' : ℝ) - (G.edgeDensity U₁ U₂ : ℝ)) -
          ((G.edgeDensity V₁ V₂ : ℝ) - (G.edgeDensity U₁ U₂ : ℝ))| := by ring_nf
    _ ≤ |(G.edgeDensity s' t' : ℝ) - (G.edgeDensity U₁ U₂ : ℝ)| +
        |(G.edgeDensity V₁ V₂ : ℝ) - (G.edgeDensity U₁ U₂ : ℝ)| := abs_sub _ _
    _ < ε + ε := add_lt_add hsub hbase
    _ = 2 * ε := by ring

/- ### Section 2: LP Duality for Bounded-Clique Packing (Hahn--Banach) -/

lemma lp_duality_cliques {n L : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (M : ℝ)
    (hdual : ∀ z : Sym2 (Fin n) → ℝ,
      (∀ Q : Finset (Fin n), 2 ≤ Q.card → Q.card ≤ L → G.IsClique (Q : Set (Fin n)) →
        ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ Q), z e ≤ 1) →
      ∑ e ∈ G.edgeFinset, z e ≤ M) :
    ∃ w : Finset (Fin n) → ℝ,
      (∀ Q, 0 ≤ w Q) ∧
      (∀ e ∈ G.edgeFinset,
        ∑ Q ∈ (Finset.univ : Finset (Finset (Fin n))).filter
          (fun (Q : Finset (Fin n)) ↦ 3 ≤ Q.card ∧ Q.card ≤ L ∧ G.IsClique (Q : Set (Fin n)) ∧ ∀ x ∈ e, x ∈ Q),
          w Q ≤ 1) ∧
      (G.edgeFinset.card : ℝ) -
        ∑ Q ∈ (Finset.univ : Finset (Finset (Fin n))).filter
          (fun (Q : Finset (Fin n)) ↦ 3 ≤ Q.card ∧ Q.card ≤ L ∧ G.IsClique (Q : Set (Fin n))),
          ((Q.card.choose 2 : ℝ) - 1) * w Q ≤ M := by
  classical
  have hM_nonneg : 0 ≤ M := by
    have h0 := hdual (fun _ ↦ 0) (fun _ _ _ _ ↦ by simp)
    simpa using h0
  -- Handle `M = 0` separately: then `G.edgeFinset = ∅`.
  rcases eq_or_lt_of_le hM_nonneg with rfl | hM_pos
  · have hE_empty : G.edgeFinset = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro e₀ he₀
      let z : Sym2 (Fin n) → ℝ := fun e ↦ if e = e₀ then 1 else 0
      have hz : ∀ Q : Finset (Fin n), 2 ≤ Q.card → Q.card ≤ L → G.IsClique (Q : Set (Fin n)) →
          ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ Q), z e ≤ 1 := by
        intro Q _ _ _
        simp only [z, sum_ite_eq']
        split_ifs <;> norm_num
      have h1 := hdual z hz
      simp only [z, sum_ite_eq', if_pos he₀] at h1
      linarith
    refine ⟨fun _ ↦ 0, fun _ ↦ le_rfl, fun _ _ ↦ by simp, ?_⟩
    simp [hE_empty]
  -- Now `0 < M`. Set up the finite-dimensional simplex and its image in `(E → ℝ)`.
  let E : Finset (Sym2 (Fin n)) := G.edgeFinset
  let 𝒬 : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun Q ↦ 2 ≤ Q.card ∧ Q.card ≤ L ∧ G.IsClique (Q : Set (Fin n)))
  let S : Set ({ Q // Q ∈ 𝒬 } → ℝ) :=
    { w | (∀ Q, 0 ≤ w Q) ∧ ∑ Q, w Q ≤ M }
  let Φ : ({ Q // Q ∈ 𝒬 } → ℝ) →ₗ[ℝ] ({ e // e ∈ E } → ℝ) :=
    { toFun := fun w e ↦ ∑ Q : { Q // Q ∈ 𝒬 }, if (∀ x ∈ e.1, x ∈ Q.1) then w Q else 0
      map_add' := fun w₁ w₂ ↦ by
        ext e
        simp only [Pi.add_apply, ← sum_add_distrib]
        refine sum_congr rfl fun Q _ ↦ ?_
        split_ifs <;> ring
      map_smul' := fun r w ↦ by
        ext e
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
        refine sum_congr rfl fun Q _ ↦ ?_
        split_ifs <;> ring }
  have hS_closed : IsClosed S := by
    have h1 : IsClosed { w : { Q // Q ∈ 𝒬 } → ℝ | ∀ Q, 0 ≤ w Q } := by
      have : { w : { Q // Q ∈ 𝒬 } → ℝ | ∀ Q, 0 ≤ w Q } =
          ⋂ Q : { Q // Q ∈ 𝒬 }, { w | 0 ≤ w Q } := by ext; simp
      rw [this]
      exact isClosed_iInter fun Q ↦ isClosed_le continuous_const (continuous_apply Q)
    have h2 : IsClosed { w : { Q // Q ∈ 𝒬 } → ℝ | ∑ Q, w Q ≤ M } :=
      isClosed_le (continuous_finsetSum _ fun Q _ ↦ continuous_apply Q) continuous_const
    exact h1.inter h2
  have hS_sub : S ⊆ Set.pi Set.univ (fun _ ↦ Set.Icc (0 : ℝ) M) := by
    intro w hw Q _
    refine ⟨hw.1 Q, ?_⟩
    calc w Q ≤ ∑ Q' : { Q // Q ∈ 𝒬 }, w Q' :=
          single_le_sum (fun Q' _ ↦ hw.1 Q') (mem_univ Q)
      _ ≤ M := hw.2
  have hS_compact : IsCompact S :=
    (isCompact_univ_pi fun _ ↦ isCompact_Icc).of_isClosed_subset hS_closed hS_sub
  have hS_convex : Convex ℝ S := by
    intro w₁ hw₁ w₂ hw₂ a b ha hb hab
    refine ⟨fun Q ↦ add_nonneg (mul_nonneg ha (hw₁.1 Q)) (mul_nonneg hb (hw₂.1 Q)), ?_⟩
    calc ∑ Q, (a * w₁ Q + b * w₂ Q)
        = a * ∑ Q, w₁ Q + b * ∑ Q, w₂ Q := by
          rw [sum_add_distrib, ← mul_sum, ← mul_sum]
      _ ≤ a * M + b * M := add_le_add (mul_le_mul_of_nonneg_left hw₁.2 ha)
          (mul_le_mul_of_nonneg_left hw₂.2 hb)
      _ = (a + b) * M := by ring
      _ = M := by rw [hab, one_mul]
  have hΦ_cont : Continuous Φ := Φ.continuous_of_finiteDimensional
  let K : Set ({ e // e ∈ E } → ℝ) := Φ '' S
  have hK_closed : IsClosed K := (hS_compact.image hΦ_cont).isClosed
  have hK_convex : Convex ℝ K := hS_convex.linear_image Φ
  have h0_mem : (0 : { e // e ∈ E } → ℝ) ∈ K :=
    ⟨0, ⟨fun _ ↦ le_rfl, by simpa using hM_nonneg⟩, map_zero Φ⟩
  let one_E : { e // e ∈ E } → ℝ := fun _ ↦ 1
  have hone_mem : one_E ∈ K := by
    by_contra hnot
    obtain ⟨f, u, hK_lt, hu_lt⟩ := geometric_hahn_banach_closed_point hK_convex hK_closed hnot
    have hu_pos : 0 < u := by
      have h0 := hK_lt 0 h0_mem
      rwa [map_zero] at h0
    -- Represent `f` on basis vectors `Pi.single e 1`.
    have hf_repr : ∀ v : { e // e ∈ E } → ℝ,
        f v = ∑ e : { e // e ∈ E }, v e * f (Pi.single e 1) := by
      intro v
      have hv : v = ∑ e : { e // e ∈ E }, v e • Pi.single e (1 : ℝ) := by
        ext e
        simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [hv]
      rw [map_sum]
      refine sum_congr rfl fun e _ ↦ ?_
      rw [map_smul, smul_eq_mul]
    let z : Sym2 (Fin n) → ℝ := fun e ↦
      if he : e ∈ E then (M / u) * f (Pi.single ⟨e, he⟩ 1) else 0
    have hz_dual : ∀ Q : Finset (Fin n), 2 ≤ Q.card → Q.card ≤ L →
        G.IsClique (Q : Set (Fin n)) →
        ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ Q), z e ≤ 1 := by
      intro Q hQ2 hQL hQcl
      have hQmem : Q ∈ 𝒬 := mem_filter.mpr ⟨mem_univ Q, hQ2, hQL, hQcl⟩
      let wQ : { Q // Q ∈ 𝒬 } → ℝ := Pi.single ⟨Q, hQmem⟩ M
      have hwQ_mem : wQ ∈ S := by
        refine ⟨fun Q' ↦ ?_, ?_⟩
        · by_cases h : Q' = ⟨Q, hQmem⟩
          · subst h; simp [wQ, hM_nonneg]
          · simp [wQ, Pi.single_eq_of_ne h]
        · simp [wQ, Pi.single_apply]
      have hΦwQ : f (Φ wQ) < u := hK_lt (Φ wQ) ⟨wQ, hwQ_mem, rfl⟩
      have hΦ_eval : ∀ e : { e // e ∈ E },
          Φ wQ e = if (∀ x ∈ e.1, x ∈ Q) then M else 0 := by
        intro e
        simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, wQ, Pi.single_apply]
        rw [Finset.sum_eq_single ⟨Q, hQmem⟩]
        · simp
        · intro Q' _ hne; simp [hne]
        · intro h; exact absurd (mem_univ _) h
      have hfΦ : f (Φ wQ) = M * ∑ e : { e // e ∈ E },
          if (∀ x ∈ e.1, x ∈ Q) then f (Pi.single e 1) else 0 := by
        rw [hf_repr (Φ wQ), mul_sum]
        refine sum_congr rfl fun e _ ↦ ?_
        rw [hΦ_eval e]
        split_ifs <;> ring
      have hsum_eq : ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ Q), z e =
          f (Φ wQ) / u := by
        rw [hfΦ, mul_div_assoc]
        have hlhs : ∑ e ∈ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ Q), z e =
            ∑ e : { e // e ∈ E }, if (∀ x ∈ e.1, x ∈ Q) then z e.1 else 0 := by
          change ∑ e ∈ E.filter (fun e ↦ ∀ x ∈ e, x ∈ Q), z e = _
          rw [Finset.sum_filter, ← Finset.sum_coe_sort E]
        rw [hlhs, sum_div, mul_sum]
        refine sum_congr rfl fun e _ ↦ ?_
        split_ifs
        · simp only [z, dif_pos e.2]; ring
        · simp
      rw [hsum_eq]
      exact (div_lt_one hu_pos).mpr hΦwQ |>.le
    have hbound := hdual z hz_dual
    have htotal : ∑ e ∈ G.edgeFinset, z e = (M / u) * f one_E := by
      rw [hf_repr one_E, mul_sum]
      have hlhs : ∑ e ∈ G.edgeFinset, z e = ∑ e : { e // e ∈ E }, z e.1 := by
        simpa [E] using (Finset.sum_coe_sort E z).symm
      rw [hlhs]
      refine sum_congr rfl fun e _ ↦ ?_
      simp [z, one_E, dif_pos e.2]
    rw [htotal] at hbound
    have hgt : M < (M / u) * f one_E := by
      have h1 : (M / u) * u < (M / u) * f one_E :=
        mul_lt_mul_of_pos_left hu_lt (div_pos hM_pos hu_pos)
      rwa [div_mul_cancel₀ M hu_pos.ne'] at h1
    linarith
  -- Extract `w ∈ S` with `Φ w = one_E`.
  obtain ⟨w_sub, hw_mem, hw_eq⟩ := hone_mem
  let w : Finset (Fin n) → ℝ := fun Q ↦ if hQ : Q ∈ 𝒬 then w_sub ⟨Q, hQ⟩ else 0
  have hw_nonneg : ∀ Q, 0 ≤ w Q := by
    intro Q; simp only [w]; split_ifs with h
    · exact hw_mem.1 ⟨Q, h⟩
    · exact le_rfl
  have hw_cover : ∀ e ∈ E, ∑ Q ∈ 𝒬.filter (fun Q ↦ ∀ x ∈ e, x ∈ Q), w Q = 1 := by
    intro e he
    have h1 := congr_fun hw_eq ⟨e, he⟩
    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, one_E] at h1
    rw [← h1, Finset.sum_filter, ← Finset.sum_coe_sort 𝒬]
    refine sum_congr rfl fun Q _ ↦ ?_
    simp [w, dif_pos Q.2]
  -- Double count edges covered by `𝒬`.
  have hdouble : (E.card : ℝ) = ∑ Q ∈ 𝒬, (Q.card.choose 2 : ℝ) * w Q := by
    calc (E.card : ℝ)
        = ∑ e ∈ E, (1 : ℝ) := by simp
      _ = ∑ e ∈ E, ∑ Q ∈ 𝒬.filter (fun Q ↦ ∀ x ∈ e, x ∈ Q), w Q :=
          sum_congr rfl fun e he ↦ (hw_cover e he).symm
      _ = ∑ e ∈ E, ∑ Q ∈ 𝒬, if (∀ x ∈ e, x ∈ Q) then w Q else 0 := by
          refine sum_congr rfl fun e _ ↦ Finset.sum_filter _ _
      _ = ∑ Q ∈ 𝒬, ∑ e ∈ E, if (∀ x ∈ e, x ∈ Q) then w Q else 0 := Finset.sum_comm
      _ = ∑ Q ∈ 𝒬, (Q.card.choose 2 : ℝ) * w Q := by
          refine sum_congr rfl fun Q hQ ↦ ?_
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          have hQcl : G.IsClique (Q : Set (Fin n)) := (mem_filter.mp hQ).2.2.2
          rw [clique_edges_card G Q hQcl]
  have hw_sum_le : ∑ Q ∈ 𝒬, w Q ≤ M := by
    calc ∑ Q ∈ 𝒬, w Q = ∑ Q : { Q // Q ∈ 𝒬 }, w_sub Q := by
          rw [← Finset.sum_coe_sort 𝒬]
          refine sum_congr rfl fun Q _ ↦ by simp [w, dif_pos Q.2]
      _ ≤ M := hw_mem.2
  let 𝒬3 : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun Q ↦ 3 ≤ Q.card ∧ Q.card ≤ L ∧ G.IsClique (Q : Set (Fin n)))
  have h𝒬3_sub : 𝒬3 ⊆ 𝒬 := by
    intro Q hQ
    simp only [𝒬3, 𝒬, mem_filter, mem_univ, true_and] at hQ ⊢
    exact ⟨by omega, hQ.2.1, hQ.2.2⟩
  refine ⟨w, hw_nonneg, ?_, ?_⟩
  · intro e he
    have hsub : ((Finset.univ : Finset (Finset (Fin n))).filter (fun (Q : Finset (Fin n)) ↦
        3 ≤ Q.card ∧ Q.card ≤ L ∧ G.IsClique (Q : Set (Fin n)) ∧ ∀ x ∈ e, x ∈ Q)) ⊆
        𝒬.filter (fun Q ↦ ∀ x ∈ e, x ∈ Q) := by
      intro Q hQ
      simp only [𝒬, mem_filter, mem_univ, true_and] at hQ ⊢
      exact ⟨⟨by omega, hQ.2.1, hQ.2.2.1⟩, hQ.2.2.2⟩
    calc ∑ Q ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun (Q : Finset (Fin n)) ↦
            3 ≤ Q.card ∧ Q.card ≤ L ∧ G.IsClique (Q : Set (Fin n)) ∧ ∀ x ∈ e, x ∈ Q), w Q
        ≤ ∑ Q ∈ 𝒬.filter (fun Q ↦ ∀ x ∈ e, x ∈ Q), w Q :=
          sum_le_sum_of_subset_of_nonneg hsub (fun Q _ _ ↦ hw_nonneg Q)
      _ = 1 := hw_cover e he
  · have hsplit : ∑ Q ∈ 𝒬, ((Q.card.choose 2 : ℝ) - 1) * w Q =
        ∑ Q ∈ 𝒬3, ((Q.card.choose 2 : ℝ) - 1) * w Q := by
      symm
      refine sum_subset h𝒬3_sub fun Q hQ hQ3 ↦ ?_
      simp only [𝒬, mem_filter, mem_univ, true_and] at hQ
      simp only [𝒬3, mem_filter, mem_univ, true_and] at hQ3
      have hnot3 : ¬(3 ≤ Q.card) := fun h3 ↦ hQ3 ⟨h3, hQ.2.1, hQ.2.2⟩
      have hcard2 : Q.card = 2 := by omega
      simp [hcard2]
    have hident : (E.card : ℝ) - ∑ Q ∈ 𝒬, ((Q.card.choose 2 : ℝ) - 1) * w Q =
        ∑ Q ∈ 𝒬, w Q := by
      rw [hdouble]
      have : ∑ Q ∈ 𝒬, ((Q.card.choose 2 : ℝ) - 1) * w Q =
          ∑ Q ∈ 𝒬, (Q.card.choose 2 : ℝ) * w Q - ∑ Q ∈ 𝒬, w Q := by
        rw [← sum_sub_distrib]
        refine sum_congr rfl fun Q _ ↦ by ring
      linarith
    have : (E.card : ℝ) - ∑ Q ∈ 𝒬3, ((Q.card.choose 2 : ℝ) - 1) * w Q = ∑ Q ∈ 𝒬, w Q := by
      rw [← hsplit, hident]
    linarith

/- ### Section 3: Basic Feasible Solution Support Bound -/

lemma bfs_support_bound {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : κ → ι → ℝ) (b : κ → ℝ) (c : ι → ℝ) (B : ℝ)
    (x₀ : ι → ℝ)
    (hx₀_nonneg : ∀ i, 0 ≤ x₀ i)
    (hx₀_le : ∀ j, ∑ i, A j i * x₀ i ≤ b j)
    (hbounded : ∀ x : ι → ℝ, (∀ i, 0 ≤ x i) → (∀ j, ∑ i, A j i * x i ≤ b j) → ∀ i, x i ≤ B) :
    ∃ x : ι → ℝ,
      (∀ i, 0 ≤ x i) ∧
      (∀ j, ∑ i, A j i * x i ≤ b j) ∧
      ∑ i, c i * x₀ i ≤ ∑ i, c i * x i ∧
      (Finset.univ.filter (fun i ↦ x i ≠ 0)).card ≤ Fintype.card κ := by
  classical
  let P : Set (ι → ℝ) := { x | (∀ i, 0 ≤ x i) ∧ ∀ j, ∑ i, A j i * x i ≤ b j }
  have hx₀P : x₀ ∈ P := ⟨hx₀_nonneg, hx₀_le⟩
  have hP_closed : IsClosed P := by
    have h1 : IsClosed { x : ι → ℝ | ∀ i, 0 ≤ x i } := by
      have : { x : ι → ℝ | ∀ i, 0 ≤ x i } = ⋂ i : ι, { x | 0 ≤ x i } := by ext; simp
      rw [this]
      exact isClosed_iInter fun i ↦ isClosed_le continuous_const (continuous_apply i)
    have h2 : IsClosed { x : ι → ℝ | ∀ j, ∑ i, A j i * x i ≤ b j } := by
      have : { x : ι → ℝ | ∀ j, ∑ i, A j i * x i ≤ b j } =
          ⋂ j : κ, { x | ∑ i, A j i * x i ≤ b j } := by ext; simp
      rw [this]
      exact isClosed_iInter fun j ↦
        isClosed_le (continuous_finsetSum _ fun i _ ↦ continuous_const.mul (continuous_apply i))
          continuous_const
    exact h1.inter h2
  have hP_sub : P ⊆ Set.pi Set.univ (fun _ ↦ Set.Icc (0 : ℝ) B) :=
    fun x hx i _ ↦ ⟨hx.1 i, hbounded x hx.1 hx.2 i⟩
  have hP_compact : IsCompact P :=
    (isCompact_univ_pi fun _ ↦ isCompact_Icc).of_isClosed_subset hP_closed hP_sub
  let obj : (ι → ℝ) → ℝ := fun x ↦ ∑ i, c i * x i
  have hobj_cont : Continuous obj :=
    continuous_finsetSum _ fun i _ ↦ continuous_const.mul (continuous_apply i)
  obtain ⟨x_init, hx_initP, hx_init_max⟩ :=
    hP_compact.exists_isMaxOn ⟨x₀, hx₀P⟩ hobj_cont.continuousOn
  let P_opt : Set (ι → ℝ) := { x ∈ P | ∀ y ∈ P, obj y ≤ obj x }
  have hP_opt_ne : ∃ s : ℕ, ∃ x ∈ P_opt, (Finset.univ.filter (fun i ↦ x i ≠ 0)).card = s :=
    ⟨(Finset.univ.filter (fun i ↦ x_init i ≠ 0)).card, x_init,
      ⟨hx_initP, fun y hy ↦ hx_init_max hy⟩, rfl⟩
  let s_min := Nat.find hP_opt_ne
  obtain ⟨x, hx_opt, hx_card⟩ := Nat.find_spec hP_opt_ne
  refine ⟨x, hx_opt.1.1, hx_opt.1.2, hx_opt.2 x₀ hx₀P, ?_⟩
  rw [hx_card]
  by_contra hlt
  push Not at hlt
  -- `Fintype.card κ < supp.card`
  let supp : Finset ι := Finset.univ.filter (fun i ↦ x i ≠ 0)
  have hsupp_gt : Fintype.card κ < supp.card := by simpa [supp, hx_card] using hlt
  let Lmap : ({ i // i ∈ supp } → ℝ) →ₗ[ℝ] (κ → ℝ) :=
    { toFun := fun d j ↦ ∑ i : { i // i ∈ supp }, A j i.1 * d i
      map_add' := fun d₁ d₂ ↦ by
        ext j; simp only [Pi.add_apply, mul_add, sum_add_distrib]
      map_smul' := fun r d ↦ by
        ext j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
        refine sum_congr rfl fun i _ ↦ by ring }
  have hrank : Module.finrank ℝ (LinearMap.range Lmap) + Module.finrank ℝ (LinearMap.ker Lmap) =
      Module.finrank ℝ ({ i // i ∈ supp } → ℝ) :=
    LinearMap.finrank_range_add_finrank_ker Lmap
  have hrange_le : Module.finrank ℝ (LinearMap.range Lmap) ≤ Fintype.card κ := by
    calc Module.finrank ℝ (LinearMap.range Lmap)
        ≤ Module.finrank ℝ (κ → ℝ) := Submodule.finrank_le _
      _ = Fintype.card κ := Module.finrank_pi ℝ
  have hdom : Module.finrank ℝ ({ i // i ∈ supp } → ℝ) = supp.card := by
    rw [Module.finrank_pi ℝ, Fintype.card_coe]
  have hker_pos : 0 < Module.finrank ℝ (LinearMap.ker Lmap) := by omega
  have hker_ne : LinearMap.ker Lmap ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hker_pos
    omega
  obtain ⟨d_sub, hd_ker, hd_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
  let d0 : ι → ℝ := fun i ↦ if hi : i ∈ supp then d_sub ⟨i, hi⟩ else 0
  have hd0_ne : ∃ i ∈ supp, d0 i ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hd_ne
    ext ⟨i, hi⟩
    have := hall i hi
    simpa [d0, dif_pos hi] using this
  have hd0_out : ∀ i, i ∉ supp → d0 i = 0 := fun i hi ↦ dif_neg hi
  have hd0_ker : ∀ j : κ, ∑ i : ι, A j i * d0 i = 0 := by
    intro j
    have hj : Lmap d_sub j = 0 := congr_fun (LinearMap.mem_ker.mp hd_ker) j
    have hsum : ∑ i : ι, A j i * d0 i = ∑ i ∈ supp, A j i * d0 i := by
      symm
      refine sum_subset (subset_univ supp) fun i _ hi ↦ by simp [hd0_out i hi]
    rw [hsum, ← Finset.sum_coe_sort supp]
    simpa [Lmap, d0] using hj
  -- Prove `obj d0 = 0` by small perturbations `x ± t₀ • d0 ∈ P`.
  have hsupp_pos : ∀ i ∈ supp, 0 < x i := fun i hi ↦
    lt_of_le_of_ne (hx_opt.1.1 i) (Ne.symm (mem_filter.mp hi).2)
  have hsupp_ne : supp.Nonempty := by
    obtain ⟨i, hi, _⟩ := hd0_ne; exact ⟨i, hi⟩
  obtain ⟨i_min, hi_min, hmin_le⟩ :=
    Finset.exists_min_image supp (fun i ↦ x i / (|d0 i| + 1)) hsupp_ne
  let t₀ : ℝ := x i_min / (|d0 i_min| + 1)
  have ht₀_pos : 0 < t₀ := div_pos (hsupp_pos i_min hi_min) (by positivity)
  have hpert : ∀ t : ℝ, |t| ≤ t₀ → (fun i ↦ x i + t * d0 i) ∈ P := by
    intro t ht
    refine ⟨fun i ↦ ?_, fun j ↦ ?_⟩
    · by_cases hi : i ∈ supp
      · have hle : t₀ ≤ x i / (|d0 i| + 1) := hmin_le i hi
        have h1 : |t| * (|d0 i| + 1) ≤ x i := by
          have hpos : (0 : ℝ) < |d0 i| + 1 := by positivity
          calc |t| * (|d0 i| + 1) ≤ t₀ * (|d0 i| + 1) :=
                mul_le_mul_of_nonneg_right ht hpos.le
            _ ≤ (x i / (|d0 i| + 1)) * (|d0 i| + 1) :=
                mul_le_mul_of_nonneg_right hle hpos.le
            _ = x i := div_mul_cancel₀ _ hpos.ne'
        have h2 : -(t * d0 i) ≤ |t| * |d0 i| := by
          calc -(t * d0 i) ≤ |t * d0 i| := neg_le_abs _
            _ = |t| * |d0 i| := abs_mul _ _
        nlinarith [abs_nonneg t]
      · simp [hd0_out i hi, hx_opt.1.1 i]
    · calc ∑ i, A j i * (x i + t * d0 i)
          = ∑ i, A j i * x i + t * ∑ i, A j i * d0 i := by
            rw [mul_sum, ← sum_add_distrib]
            refine sum_congr rfl fun i _ ↦ by ring
        _ = ∑ i, A j i * x i := by rw [hd0_ker j, mul_zero, add_zero]
        _ ≤ b j := hx_opt.1.2 j
  have hobj_d0 : obj d0 = 0 := by
    have hplus := hx_opt.2 (fun i ↦ x i + t₀ * d0 i) (hpert t₀ (by rw [abs_of_pos ht₀_pos]))
    have hminus := hx_opt.2 (fun i ↦ x i + (-t₀) * d0 i)
      (hpert (-t₀) (by rw [abs_neg, abs_of_pos ht₀_pos]))
    have heq1 : obj (fun i ↦ x i + t₀ * d0 i) = obj x + t₀ * obj d0 := by
      simp only [obj, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun i _ ↦ by ring
    have heq2 : obj (fun i ↦ x i + (-t₀) * d0 i) = obj x - t₀ * obj d0 := by
      simp only [obj, mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun i _ ↦ by ring
    rw [heq1] at hplus
    rw [heq2] at hminus
    nlinarith
  -- Orient `d` so that some coordinate in `supp` is strictly negative.
  obtain ⟨i_nz, hi_nz, hnz⟩ := hd0_ne
  let d : ι → ℝ := if d0 i_nz < 0 then d0 else fun i ↦ -d0 i
  have hd_out : ∀ i, i ∉ supp → d i = 0 := by
    intro i hi; simp only [d]; split_ifs <;> simp [hd0_out i hi]
  have hd_ker_eq : ∀ j : κ, ∑ i : ι, A j i * d i = 0 := by
    intro j; simp only [d]; split_ifs
    · exact hd0_ker j
    · simp only [mul_neg, sum_neg_distrib, hd0_ker j, neg_zero]
  have hd_obj : obj d = 0 := by
    simp only [d]; split_ifs
    · exact hobj_d0
    · simp only [obj, mul_neg, sum_neg_distrib]
      have : ∑ i, c i * d0 i = 0 := hobj_d0
      linarith
  have hd_has_neg : ∃ i ∈ supp, d i < 0 := by
    refine ⟨i_nz, hi_nz, ?_⟩
    simp only [d]; split_ifs with h
    · exact h
    · push Not at h
      have : 0 < d0 i_nz := lt_of_le_of_ne h (Ne.symm hnz)
      linarith
  let S_neg : Finset ι := supp.filter (fun i ↦ d i < 0)
  have hS_neg : S_neg.Nonempty := by
    obtain ⟨i, hi, hdi⟩ := hd_has_neg
    exact ⟨i, mem_filter.mpr ⟨hi, hdi⟩⟩
  obtain ⟨i_hit, hi_hit, hhit_min⟩ :=
    Finset.exists_min_image S_neg (fun i ↦ x i / (-d i)) hS_neg
  have hi_hit_supp : i_hit ∈ supp := (mem_filter.mp hi_hit).1
  have hdi_hit_neg : d i_hit < 0 := (mem_filter.mp hi_hit).2
  let t_star : ℝ := x i_hit / (-d i_hit)
  have ht_star_pos : 0 < t_star :=
    div_pos (hsupp_pos i_hit hi_hit_supp) (by linarith)
  let x_new : ι → ℝ := fun i ↦ x i + t_star * d i
  have hx_newP : x_new ∈ P := by
    refine ⟨fun i ↦ ?_, fun j ↦ ?_⟩
    · by_cases hi : i ∈ supp
      · by_cases hdi : d i < 0
        · have hi_neg : i ∈ S_neg := mem_filter.mpr ⟨hi, hdi⟩
          have hle : t_star ≤ x i / (-d i) := hhit_min i hi_neg
          have hpos : 0 < -d i := by linarith
          have hmul : t_star * (-d i) ≤ x i := (le_div_iff₀ hpos).mp hle
          simp only [x_new]; linarith
        · push Not at hdi
          simp only [x_new]
          exact add_nonneg (hx_opt.1.1 i) (mul_nonneg ht_star_pos.le hdi)
      · simp [x_new, hd_out i hi, hx_opt.1.1 i]
    · calc ∑ i, A j i * x_new i
          = ∑ i, A j i * x i + t_star * ∑ i, A j i * d i := by
            simp only [x_new, mul_sum, ← sum_add_distrib]
            refine sum_congr rfl fun i _ ↦ by ring
        _ = ∑ i, A j i * x i := by rw [hd_ker_eq j, mul_zero, add_zero]
        _ ≤ b j := hx_opt.1.2 j
  have hx_new_obj : obj x_new = obj x := by
    have : obj x_new = obj x + t_star * obj d := by
      simp only [obj, x_new, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun i _ ↦ by ring
    rw [this, hd_obj, mul_zero, add_zero]
  have hx_new_opt : x_new ∈ P_opt :=
    ⟨hx_newP, fun y hy ↦ hx_new_obj.symm ▸ hx_opt.2 y hy⟩
  have hx_hit_zero : x_new i_hit = 0 := by
    have hne : -d i_hit ≠ 0 := by linarith
    have hmul : x i_hit / (-d i_hit) * d i_hit = -x i_hit := by
      rw [div_mul_eq_mul_div, div_eq_iff hne]
      ring
    simp only [x_new, t_star]
    linarith
  have hsub_supp : Finset.univ.filter (fun i ↦ x_new i ≠ 0) ⊆ supp.erase i_hit := by
    intro i hi
    have hne : x_new i ≠ 0 := (mem_filter.mp hi).2
    have hi_ne : i ≠ i_hit := fun heq ↦ hne (heq ▸ hx_hit_zero)
    have hi_supp : i ∈ supp := by
      by_contra hnot
      have hxi : x i = 0 := by
        by_contra hxne
        exact hnot (mem_filter.mpr ⟨mem_univ i, hxne⟩)
      exact hne (by simp [x_new, hxi, hd_out i hnot])
    exact mem_erase.mpr ⟨hi_ne, hi_supp⟩
  have hcard_lt : (Finset.univ.filter (fun i ↦ x_new i ≠ 0)).card < s_min := by
    have h1 := Finset.card_le_card hsub_supp
    have h2 : (supp.erase i_hit).card < supp.card := card_erase_lt_of_mem hi_hit_supp
    have hsupp_eq : supp.card = s_min := hx_card
    omega
  exact Nat.find_min hP_opt_ne hcard_lt ⟨x_new, hx_new_opt, rfl⟩

/- ### Section 4: Simultaneous `H2` Parameters Across `3 ≤ q ≤ L` -/

lemma h2_uniform_params (h2 : H2) (L : ℕ) (hL : 3 ≤ L) (δ : ℝ) (hδ : 0 < δ)
    (η : ℝ) (hη : 0 < η) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∃ m₀ : ℕ,
      ∀ q : ℕ, 3 ≤ q → q ≤ L →
        ∀ (n m : ℕ), m₀ ≤ m → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
          (V : Fin q → Finset (Fin n)),
          (∀ i j, i ≠ j → Disjoint (V i) (V j)) →
          (∀ i, (V i).card = m) →
          ∀ p : ℝ, δ ≤ p → p ≤ 1 →
          (∀ i j, i ≠ j → G.IsUniform ε₁ (V i) (V j) ∧
            |(G.edgeDensity (V i) (V j) : ℝ) - p| ≤ ε₁) →
          ∃ 𝒬 : Finset (Finset (Fin n)),
            (∀ Q ∈ 𝒬, Q.card = q ∧ G.IsClique (Q : Set (Fin n)) ∧
              ∀ i : Fin q, (Q ∩ V i).card = 1) ∧
            (∀ Q₁ ∈ 𝒬, ∀ Q₂ ∈ 𝒬, Q₁ ≠ Q₂ → (Q₁ ∩ Q₂).card ≤ 1) ∧
            (p - η) * (m : ℝ) ^ 2 ≤ (𝒬.card : ℝ) := by
  induction L, hL using Nat.le_induction with
  | base =>
    obtain ⟨ε₁, hε₁, m₀, hspec⟩ := h2 3 le_rfl δ hδ η hη
    refine ⟨ε₁, hε₁, m₀, fun q hq3 hqL ↦ ?_⟩
    have hq : q = 3 := by omega
    subst hq
    exact hspec
  | succ k hk ih =>
    obtain ⟨ε_ih, hε_ih, m_ih, hspec_ih⟩ := ih
    obtain ⟨ε_k, hε_k, m_k, hspec_k⟩ := h2 (k + 1) (by omega) δ hδ η hη
    refine ⟨min ε_ih ε_k, lt_min hε_ih hε_k, max m_ih m_k, ?_⟩
    intro q hq3 hqk n m hm G _ V hdisj hcard p hpδ hp1 hunif
    rcases lt_or_eq_of_le hqk with hlt | rfl
    · exact hspec_ih q hq3 (by omega) n m (le_trans (le_max_left _ _) hm) G V hdisj hcard
        p hpδ hp1 (fun i j hij ↦
          ⟨(hunif i j hij).1.mono (min_le_left _ _),
            (hunif i j hij).2.trans (min_le_left _ _)⟩)
    · exact hspec_k n m (le_trans (le_max_right _ _) hm) G V hdisj hcard
        p hpδ hp1 (fun i j hij ↦
          ⟨(hunif i j hij).1.mono (min_le_right _ _),
            (hunif i j hij).2.trans (min_le_right _ _)⟩)

/- ### Section 5: Main Reduction Theorem -/

set_option maxHeartbeats 1600000 in
theorem main : H1 → H2 → OMA.R_Erdos81_erdos_81_R1.H2 := by
  intro h1 h2 L hL ζ hζ
  classical
  have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hL2_pos : (0 : ℝ) < (L : ℝ) ^ 2 := sq_pos_of_pos hL_pos
  -- Step 1: Choose all constants in non-circular order.
  let δ : ℝ := ζ / (16 * (L : ℝ) ^ 2)
  let η : ℝ := ζ / (16 * (L : ℝ) ^ 2)
  have hδ_pos : 0 < δ := div_pos hζ (by positivity)
  have hη_pos : 0 < η := div_pos hζ (by positivity)
  obtain ⟨ε₁, hε₁_pos, m₀_pack, hpack⟩ := h2_uniform_params h2 L hL δ hδ_pos η hη_pos
  obtain ⟨ε_split, hε_split_pos, m₀_split, hsplit⟩ := h1 ε₁ hε₁_pos δ hδ_pos
  let ε_reg : ℝ := min (min (ε_split / 2) (1 / 2)) (ζ / (16 * (L : ℝ) ^ 2))
  have hε_reg_pos : 0 < ε_reg :=
    lt_min (lt_min (half_pos hε_split_pos) (by norm_num)) (div_pos hζ (by positivity))
  have hε_reg_split : 2 * ε_reg ≤ ε_split := by
    have : ε_reg ≤ ε_split / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have hε_reg_half : ε_reg ≤ 1 / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hε_reg_ζ : ε_reg ≤ ζ / (16 * (L : ℝ) ^ 2) := min_le_right _ _
  let l : ℕ := max 1 (Nat.ceil (16 * (L : ℝ) ^ 2 / ζ))
  have hl_pos : 1 ≤ l := le_max_left _ _
  have hl_bound : 16 * (L : ℝ) ^ 2 / ζ ≤ (l : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right 1 _))
  let K_max : ℕ := SzemerediRegularity.bound ε_reg l
  let m_req : ℕ := max 1 (max m₀_split m₀_pack)
  let n₀ : ℕ := max (max l (K_max * m_req))
    (Nat.ceil (16 * (L : ℝ) ^ 2 * (K_max : ℝ) / ζ))
  refine ⟨n₀, fun n hn G _ M hdual ↦ ?_⟩
  -- Handle `n = 0` (cannot happen since `1 ≤ l ≤ n₀ ≤ n`, so `0 < n`).
  have hn_l : l ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn_pos : 0 < n := lt_of_lt_of_le (by omega) hn_l
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  -- Step 2: LP Duality gives fractional packing `w` on cliques of size `3..L`.
  obtain ⟨w, hw_nonneg, hw_edge, hw_val⟩ := lp_duality_cliques G M hdual
  let 𝒬3 : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun Q ↦ 3 ≤ Q.card ∧ Q.card ≤ L ∧ G.IsClique (Q : Set (Fin n)))
  -- Step 3: Apply Szemerédi Regularity Lemma to `G`.
  have hl_card : l ≤ Fintype.card (Fin n) := by simpa using hn_l
  obtain ⟨P, hP_eq, hl_k, hk_max, hP_unif⟩ := szemeredi_regularity G hε_reg_pos hl_card
  let k : ℕ := P.parts.card
  have hk_pos : 0 < k := lt_of_lt_of_le (by omega) hl_k
  have hk_real_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos
  -- Enumerate parts of `P` as `U : Fin k → Finset (Fin n)`.
  let eParts : P.parts ≃ Fin k := P.parts.equivFin
  let U : Fin k → Finset (Fin n) := fun i ↦ (eParts.symm i).1
  have hU_mem : ∀ i : Fin k, U i ∈ P.parts := fun i ↦ (eParts.symm i).2
  have hU_inj : Function.Injective U := fun i j hij ↦ by
    apply eParts.symm.injective
    exact Subtype.ext hij
  have hU_disj : ∀ i j : Fin k, i ≠ j → Disjoint (U i) (U j) := fun i j hij ↦
    P.disjoint (hU_mem i) (hU_mem j) (fun h ↦ hij (hU_inj h))
  -- Trim each part `U i` to exact size `m = n / k`.
  let m : ℕ := n / k
  have hU_card_lo : ∀ i : Fin k, m ≤ (U i).card := by
    intro i
    have := hP_eq.average_le_card_part (hU_mem i)
    simpa [m, k] using this
  have hU_card_hi : ∀ i : Fin k, (U i).card ≤ m + 1 := by
    intro i
    have := hP_eq.card_part_le_average_add_one (hU_mem i)
    simpa [m, k] using this
  have hm_req : m_req ≤ m := by
    have hn_Km : K_max * m_req ≤ n :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hkm : k * m_req ≤ n := le_trans (Nat.mul_le_mul_right m_req hk_max) hn_Km
    exact (Nat.le_div_iff_mul_le hk_pos).mpr (by rwa [mul_comm])
  have hm_one : 1 ≤ m := le_trans (le_max_left _ _) hm_req
  have hm_split : m₀_split ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm_req
  have hm_pack : m₀_pack ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm_req
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hkm_le_n : k * m ≤ n := Nat.mul_div_le n k
  have hkm_le_n_real : (k : ℝ) * (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkm_le_n
  -- Choose trimmed clusters `V i ⊆ U i` with `(V i).card = m`.
  have hV_ex : ∀ i : Fin k, ∃ s : Finset (Fin n), s ⊆ U i ∧ s.card = m :=
    fun i ↦ Finset.exists_subset_card_eq (hU_card_lo i)
  let V : Fin k → Finset (Fin n) := fun i ↦ (hV_ex i).choose
  have hV_sub : ∀ i : Fin k, V i ⊆ U i := fun i ↦ (hV_ex i).choose_spec.1
  have hV_card : ∀ i : Fin k, (V i).card = m := fun i ↦ (hV_ex i).choose_spec.2
  have hV_disj : ∀ i j : Fin k, i ≠ j → Disjoint (V i) (V j) := fun i j hij ↦
    (hU_disj i j hij).mono (hV_sub i) (hV_sub j)
  -- Step 4: Regular cluster pairs `E_reg` and good/bad edges of `G`.
  let E_reg : Finset (Sym2 (Fin k)) :=
    Finset.univ.filter (fun e ↦ ¬e.IsDiag ∧ ∀ i j : Fin k, e = s(i, j) →
      G.IsUniform ε_reg (U i) (U j))
  have hE_reg_mem : ∀ i j : Fin k, s(i, j) ∈ E_reg ↔ i ≠ j ∧ G.IsUniform ε_reg (U i) (U j) := by
    intro i j
    simp only [E_reg, mem_filter, mem_univ, true_and, Sym2.mk_isDiag_iff]
    constructor
    · rintro ⟨hij, h⟩; exact ⟨hij, h i j rfl⟩
    · rintro ⟨hij, h⟩
      refine ⟨hij, fun a b hab ↦ ?_⟩
      rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h
      · exact h.symm
  have hE_reg_unif_split : ∀ i j : Fin k, s(i, j) ∈ E_reg → G.IsUniform ε_split (V i) (V j) := by
    intro i j hij
    have hu := (hE_reg_mem i j).mp hij |>.2
    exact (trim_isUniform hm_one hε_reg_half G (hV_sub i) (hV_sub j)
      (hV_card i) (hV_card j) (hU_card_hi i) (hU_card_hi j) hu).mono hε_reg_split
  -- Bound `E_reg.card ≤ k^2 / 2`.
  have hE_reg_card : (E_reg.card : ℝ) ≤ (k : ℝ) ^ 2 / 2 := by
    have h2 : 2 * E_reg.card ≤ k * k := by
      let S_ord : Finset (Fin k × Fin k) :=
        Finset.univ.filter (fun p ↦ s(p.1, p.2) ∈ E_reg)
      have hS_le : S_ord.card ≤ k * k := by
        calc S_ord.card ≤ (Finset.univ : Finset (Fin k × Fin k)).card := card_le_card (subset_univ _)
          _ = k * k := by simp
      have hfib : S_ord.card = 2 * E_reg.card := by
        have hmap : S_ord.card = ∑ e ∈ E_reg, (S_ord.filter (fun p ↦ s(p.1, p.2) = e)).card := by
          rw [← Finset.card_biUnion]
          · congr 1; ext p; simp [S_ord]
          · intro e₁ _ e₂ _ hne
            dsimp only [Function.onFun]
            rw [Finset.disjoint_left]
            intro p hp₁ hp₂
            exact hne ((mem_filter.mp hp₁).2.symm.trans (mem_filter.mp hp₂).2)
        rw [hmap]
        have h2e : ∀ e ∈ E_reg, (S_ord.filter (fun p ↦ s(p.1, p.2) = e)).card = 2 := by
          intro e he
          induction e using Sym2.ind with
          | h a b =>
            have hab : a ≠ b := ((hE_reg_mem a b).mp he).1
            have hset : S_ord.filter (fun p ↦ s(p.1, p.2) = s(a, b)) = {(a, b), (b, a)} := by
              ext ⟨x, y⟩
              simp only [S_ord, mem_filter, mem_univ, true_and, mem_insert, mem_singleton,
                Prod.mk.injEq, Sym2.eq_iff]
              constructor
              · rintro ⟨_, h⟩; exact h
              · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
                · exact ⟨he, Or.inl ⟨rfl, rfl⟩⟩
                · exact ⟨by rwa [Sym2.eq_swap], Or.inr ⟨rfl, rfl⟩⟩
            rw [hset, card_pair]
            intro h; exact hab (Prod.mk.inj h).1
        rw [Finset.sum_congr rfl h2e, Finset.sum_const, smul_eq_mul, mul_comm]
      omega
    have h2r : 2 * (E_reg.card : ℝ) ≤ (k : ℝ) ^ 2 := by
      have : (2 * E_reg.card : ℝ) ≤ ((k * k : ℕ) : ℝ) := by exact_mod_cast h2
      push_cast at this; linarith
    linarith
  -- Good edges and bad edges of `G`.
  let E_good : Finset (Sym2 (Fin n)) :=
    G.edgeFinset.filter (fun e ↦ ∃ i j : Fin k, s(i, j) ∈ E_reg ∧
      ∃ u ∈ V i, ∃ v ∈ V j, e = s(u, v))
  let E_bad : Finset (Sym2 (Fin n)) := G.edgeFinset \ E_good
  -- Bound `E_bad.card ≤ (3 * ζ / (16 * L^2)) * n^2`.
  let V_union : Finset (Fin n) := Finset.univ.biUnion V
  let D_trim : Finset (Fin n) := Finset.univ \ V_union
  have hV_union_card : V_union.card = k * m := by
    rw [Finset.card_biUnion (fun i _ j _ hij ↦ hV_disj i j hij)]
    simp [hV_card]
  have hD_trim_card : D_trim.card ≤ k := by
    have hsub : V_union ⊆ Finset.univ := subset_univ _
    rw [Finset.card_sdiff_of_subset hsub, Finset.card_univ, Fintype.card_fin, hV_union_card]
    have hmod : n = k * m + n % k := (Nat.div_add_mod n k).symm
    have hlt : n % k < k := Nat.mod_lt n hk_pos
    omega
  let B_trim : Finset (Sym2 (Fin n)) :=
    D_trim.biUnion (fun x ↦ (Finset.univ : Finset (Fin n)).image (fun y ↦ s(x, y)))
  let B_intra : Finset (Sym2 (Fin n)) :=
    (Finset.univ : Finset (Fin k)).biUnion (fun i ↦
      (V i ×ˢ V i).image (fun p ↦ s(p.1, p.2)))
  let badPairs : Finset (Fin k × Fin k) :=
    Finset.univ.filter (fun p ↦ p.1 ≠ p.2 ∧ ¬ G.IsUniform ε_reg (U p.1) (U p.2))
  let B_nonunif : Finset (Sym2 (Fin n)) :=
    badPairs.biUnion (fun p ↦ (V p.1 ×ˢ V p.2).image (fun q ↦ s(q.1, q.2)))
  have hE_bad_sub : E_bad ⊆ B_trim ∪ (B_intra ∪ B_nonunif) := by
    intro e he
    rw [mem_sdiff] at he
    obtain ⟨heG, he_not_good⟩ := he
    induction e using Sym2.ind with
    | h u v =>
      by_cases hu : u ∈ V_union
      · by_cases hv : v ∈ V_union
        · obtain ⟨i, _, hui⟩ := mem_biUnion.mp hu
          obtain ⟨j, _, hvj⟩ := mem_biUnion.mp hv
          by_cases hij : i = j
          · subst hij
            refine mem_union_right _ (mem_union_left _ ?_)
            exact mem_biUnion.mpr ⟨i, mem_univ i,
              mem_image.mpr ⟨(u, v), mem_product.mpr ⟨hui, hvj⟩, rfl⟩⟩
          · have hnotreg : s(i, j) ∉ E_reg := fun hreg ↦
              he_not_good (mem_filter.mpr ⟨heG, i, j, hreg, u, hui, v, hvj, rfl⟩)
            have hnotunif : ¬ G.IsUniform ε_reg (U i) (U j) := fun hunif ↦
              hnotreg ((hE_reg_mem i j).mpr ⟨hij, hunif⟩)
            refine mem_union_right _ (mem_union_right _ ?_)
            exact mem_biUnion.mpr ⟨(i, j), mem_filter.mpr ⟨mem_univ _, hij, hnotunif⟩,
              mem_image.mpr ⟨(u, v), mem_product.mpr ⟨hui, hvj⟩, rfl⟩⟩
        · refine mem_union_left _ (mem_biUnion.mpr ⟨v, mem_sdiff.mpr ⟨mem_univ v, hv⟩,
            mem_image.mpr ⟨u, mem_univ u, Sym2.eq_swap⟩⟩)
      · refine mem_union_left _ (mem_biUnion.mpr ⟨u, mem_sdiff.mpr ⟨mem_univ u, hu⟩,
          mem_image.mpr ⟨v, mem_univ v, rfl⟩⟩)
  have hB_trim_card : (B_trim.card : ℝ) ≤ (K_max : ℝ) * (n : ℝ) := by
    have h1 : B_trim.card ≤ D_trim.card * n := by
      calc B_trim.card
          ≤ ∑ x ∈ D_trim, ((Finset.univ : Finset (Fin n)).image (fun y ↦ s(x, y))).card :=
            card_biUnion_le
        _ ≤ ∑ _x ∈ D_trim, n := sum_le_sum fun x _ ↦
            card_image_le.trans (by simp)
        _ = D_trim.card * n := by simp
    have h2 : B_trim.card ≤ K_max * n :=
      h1.trans (Nat.mul_le_mul_right n (hD_trim_card.trans hk_max))
    exact_mod_cast h2
  have hB_intra_card : (B_intra.card : ℝ) ≤ (ζ / (16 * (L : ℝ) ^ 2)) * (n : ℝ) ^ 2 := by
    have h1 : B_intra.card ≤ k * (m * m) := by
      calc B_intra.card
          ≤ ∑ i : Fin k, ((V i ×ˢ V i).image (fun p ↦ s(p.1, p.2))).card := card_biUnion_le
        _ ≤ ∑ i : Fin k, (m * m) := sum_le_sum fun i _ ↦
            card_image_le.trans (by rw [card_product, hV_card i])
        _ = k * (m * m) := by simp
    have h1r : (B_intra.card : ℝ) ≤ (k : ℝ) * (m : ℝ) ^ 2 := by
      have : (B_intra.card : ℝ) ≤ ((k * (m * m) : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at this; linarith
    have hl_le_k : (l : ℝ) ≤ (k : ℝ) := by exact_mod_cast hl_k
    have hkm2 : (k : ℝ) * (m : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 / (k : ℝ) := by
      rw [le_div_iff₀ hk_real_pos]
      have : ((k : ℝ) * (m : ℝ)) ^ 2 ≤ (n : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hkm_le_n_real 2
      nlinarith
    have hdiv : (n : ℝ) ^ 2 / (k : ℝ) ≤ (ζ / (16 * (L : ℝ) ^ 2)) * (n : ℝ) ^ 2 := by
      have h16 : (16 * (L : ℝ) ^ 2) / ζ ≤ (k : ℝ) := hl_bound.trans hl_le_k
      have hinv : 1 / (k : ℝ) ≤ ζ / (16 * (L : ℝ) ^ 2) := by
        rw [div_le_div_iff₀ hk_real_pos (by positivity)]
        have := (div_le_iff₀ hζ).mp h16
        linarith
      calc (n : ℝ) ^ 2 / (k : ℝ) = (1 / (k : ℝ)) * (n : ℝ) ^ 2 := by ring
        _ ≤ (ζ / (16 * (L : ℝ) ^ 2)) * (n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hinv (sq_nonneg _)
    exact h1r.trans (hkm2.trans hdiv)
  have hB_nonunif_card : (B_nonunif.card : ℝ) ≤ (ζ / (16 * (L : ℝ) ^ 2)) * (n : ℝ) ^ 2 := by
    have hbad_le : badPairs.card ≤ (P.nonUniforms G ε_reg).card := by
      refine Finset.card_le_card_of_injOn (fun p ↦ (U p.1, U p.2)) ?_ ?_
      · intro p hp
        simp only [mem_coe, badPairs, mem_filter, mem_univ, true_and] at hp
        rw [mem_coe, Finpartition.mk_mem_nonUniforms]
        exact ⟨hU_mem p.1, hU_mem p.2, fun h ↦ hp.1 (hU_inj h), hp.2⟩
      · intro p₁ _ p₂ _ h
        have h1 : U p₁.1 = U p₂.1 := (Prod.mk.inj h).1
        have h2 : U p₁.2 = U p₂.2 := (Prod.mk.inj h).2
        exact Prod.ext (hU_inj h1) (hU_inj h2)
    have h1 : B_nonunif.card ≤ badPairs.card * (m * m) := by
      calc B_nonunif.card
          ≤ ∑ p ∈ badPairs, ((V p.1 ×ˢ V p.2).image (fun q ↦ s(q.1, q.2))).card :=
            card_biUnion_le
        _ ≤ ∑ _p ∈ badPairs, (m * m) := sum_le_sum fun p _ ↦
            card_image_le.trans (by rw [card_product, hV_card p.1, hV_card p.2])
        _ = badPairs.card * (m * m) := by simp
    have h1r : (B_nonunif.card : ℝ) ≤ (badPairs.card : ℝ) * (m : ℝ) ^ 2 := by
      have : (B_nonunif.card : ℝ) ≤ ((badPairs.card * (m * m) : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at this; linarith
    have hbad_r : (badPairs.card : ℝ) ≤ (k : ℝ) ^ 2 * ε_reg := by
      have hnu : ((P.nonUniforms G ε_reg).card : ℝ) ≤ ((k * (k - 1) : ℕ) : ℝ) * ε_reg := hP_unif
      have hkk : ((k * (k - 1) : ℕ) : ℝ) ≤ (k : ℝ) ^ 2 := by
        have : k * (k - 1) ≤ k * k := Nat.mul_le_mul_left k (Nat.sub_le k 1)
        rw [sq]
        exact_mod_cast this
      calc (badPairs.card : ℝ) ≤ ((P.nonUniforms G ε_reg).card : ℝ) := by exact_mod_cast hbad_le
        _ ≤ ((k * (k - 1) : ℕ) : ℝ) * ε_reg := hnu
        _ ≤ (k : ℝ) ^ 2 * ε_reg := mul_le_mul_of_nonneg_right hkk hε_reg_pos.le
    calc (B_nonunif.card : ℝ)
        ≤ ((k : ℝ) ^ 2 * ε_reg) * (m : ℝ) ^ 2 :=
          h1r.trans (mul_le_mul_of_nonneg_right hbad_r (sq_nonneg _))
      _ = ε_reg * ((k : ℝ) * (m : ℝ)) ^ 2 := by ring
      _ ≤ ε_reg * (n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hkm_le_n_real 2) hε_reg_pos.le
      _ ≤ (ζ / (16 * (L : ℝ) ^ 2)) * (n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hε_reg_ζ (sq_nonneg _)
  have htrim_n : (K_max : ℝ) * (n : ℝ) ≤ (ζ / (16 * (L : ℝ) ^ 2)) * (n : ℝ) ^ 2 := by
    have hn_ceil : 16 * (L : ℝ) ^ 2 * (K_max : ℝ) / ζ ≤ (n : ℝ) := by
      have h1 : Nat.ceil (16 * (L : ℝ) ^ 2 * (K_max : ℝ) / ζ) ≤ n :=
        le_trans (le_max_right _ _) hn
      exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
    have hmul : 16 * (L : ℝ) ^ 2 * (K_max : ℝ) ≤ (n : ℝ) * ζ := (div_le_iff₀ hζ).mp hn_ceil
    have hdiv : (K_max : ℝ) ≤ (ζ / (16 * (L : ℝ) ^ 2)) * (n : ℝ) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      linarith
    calc (K_max : ℝ) * (n : ℝ) ≤ ((ζ / (16 * (L : ℝ) ^ 2)) * (n : ℝ)) * (n : ℝ) :=
          mul_le_mul_of_nonneg_right hdiv hn_real_pos.le
      _ = (ζ / (16 * (L : ℝ) ^ 2)) * (n : ℝ) ^ 2 := by ring
  have hE_bad_card : (E_bad.card : ℝ) ≤ (3 * ζ / (16 * (L : ℝ) ^ 2)) * (n : ℝ) ^ 2 := by
    have hcard : E_bad.card ≤ B_trim.card + (B_intra.card + B_nonunif.card) :=
      (card_le_card hE_bad_sub).trans
        ((card_union_le _ _).trans (Nat.add_le_add_left (card_union_le _ _) _))
    have hcard_r : (E_bad.card : ℝ) ≤ (B_trim.card : ℝ) + (B_intra.card : ℝ) + (B_nonunif.card : ℝ) := by
      have : (E_bad.card : ℝ) ≤ ((B_trim.card + (B_intra.card + B_nonunif.card) : ℕ) : ℝ) := by
        exact_mod_cast hcard
      push_cast at this; linarith
    calc (E_bad.card : ℝ)
        ≤ (B_trim.card : ℝ) + (B_intra.card : ℝ) + (B_nonunif.card : ℝ) := hcard_r
      _ ≤ (ζ / (16 * (L : ℝ) ^ 2)) * (n : ℝ) ^ 2 + (ζ / (16 * (L : ℝ) ^ 2)) * (n : ℝ) ^ 2 +
          (ζ / (16 * (L : ℝ) ^ 2)) * (n : ℝ) ^ 2 :=
        add_le_add (add_le_add (hB_trim_card.trans htrim_n) hB_intra_card) hB_nonunif_card
      _ = (3 * ζ / (16 * (L : ℝ) ^ 2)) * (n : ℝ) ^ 2 := by ring
  -- Step 5: Restrict `w` to good cliques `𝒬_good` and aggregate onto regular cluster tuples `𝒯`.
  let 𝒬_good : Finset (Finset (Fin n)) :=
    𝒬3.filter (fun Q ↦ ∀ e ∈ G.edgeFinset, (∀ x ∈ e, x ∈ Q) → e ∈ E_good)
  -- Helper: cluster index of a vertex `u ∈ V_union`.
  let clSet : Finset (Fin n) → Finset (Fin k) :=
    fun Q ↦ Finset.univ.filter (fun i ↦ (Q ∩ V i).Nonempty)
  let 𝒯 : Finset (Finset (Fin k)) :=
    Finset.univ.filter (fun T ↦ 3 ≤ T.card ∧ T.card ≤ L ∧
      ∀ i ∈ T, ∀ j ∈ T, i ≠ j → s(i, j) ∈ E_reg)
  have hQgood_props : ∀ Q ∈ 𝒬_good,
      clSet Q ∈ 𝒯 ∧ (clSet Q).card = Q.card ∧
      (∀ i ∈ clSet Q, (Q ∩ V i).card = 1) ∧
      (∀ u ∈ Q, ∃ i ∈ clSet Q, u ∈ V i) := by
    intro Q hQ
    have hQ3 : Q ∈ 𝒬3 := (mem_filter.mp hQ).1
    have hQedge_good : ∀ e ∈ G.edgeFinset, (∀ x ∈ e, x ∈ Q) → e ∈ E_good :=
      (mem_filter.mp hQ).2
    simp only [𝒬3, mem_filter, mem_univ, true_and] at hQ3
    obtain ⟨hQ_lo, hQ_hi, hQ_cl⟩ := hQ3
    -- Every vertex of `Q` lies in some `V i`.
    have hv_in_V : ∀ u ∈ Q, ∃ i : Fin k, u ∈ V i := by
      intro u hu
      have hne : (Q.erase u).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hemp
        have := card_erase_of_mem hu
        rw [hemp, card_empty] at this
        omega
      obtain ⟨v, hv⟩ := hne
      have huv : u ≠ v := (mem_erase.mp hv).1.symm
      have hvQ : v ∈ Q := (mem_erase.mp hv).2
      have hadj : G.Adj u v := hQ_cl hu hvQ huv
      have hgood := hQedge_good s(u, v) (mem_edgeFinset.mpr hadj) (fun x hx ↦ by
        rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption)
      obtain ⟨i, j, _, a, ha, b, hb, heq⟩ := (mem_filter.mp hgood).2
      rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨i, ha⟩
      · exact ⟨j, hb⟩
    -- No two distinct vertices of `Q` lie in the same `V i`.
    have huniq_in_V : ∀ i : Fin k, ∀ u ∈ Q, ∀ v ∈ Q, u ∈ V i → v ∈ V i → u = v := by
      intro i u hu v hv hui hvi
      by_contra huv
      have hadj : G.Adj u v := hQ_cl hu hv huv
      have hgood := hQedge_good s(u, v) (mem_edgeFinset.mpr hadj) (fun x hx ↦ by
        rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption)
      obtain ⟨a, b, hab_reg, x, hxa, y, hyb, heq⟩ := (mem_filter.mp hgood).2
      have hab_ne : a ≠ b := ((hE_reg_mem a b).mp hab_reg).1
      rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hia : i = a := by
          by_contra h; exact Finset.disjoint_left.mp (hV_disj i a h) hui hxa
        have hib : i = b := by
          by_contra h; exact Finset.disjoint_left.mp (hV_disj i b h) hvi hyb
        exact hab_ne (hia.symm.trans hib)
      · have hib : i = b := by
          by_contra h; exact Finset.disjoint_left.mp (hV_disj i b h) hui hyb
        have hia : i = a := by
          by_contra h; exact Finset.disjoint_left.mp (hV_disj i a h) hvi hxa
        exact hab_ne (hia.symm.trans hib)
    have hcard_one : ∀ i ∈ clSet Q, (Q ∩ V i).card = 1 := by
      intro i hi
      obtain ⟨u, hu⟩ := (mem_filter.mp hi).2
      rw [Finset.card_eq_one]
      refine ⟨u, ?_⟩
      ext v
      simp only [mem_inter, mem_singleton]
      constructor
      · rintro ⟨hvQ, hvi⟩
        exact huniq_in_V i v hvQ u (mem_inter.mp hu).1 hvi (mem_inter.mp hu).2
      · rintro rfl; exact mem_inter.mp hu
    have hv_cl : ∀ u ∈ Q, ∃ i ∈ clSet Q, u ∈ V i := by
      intro u hu
      obtain ⟨i, hui⟩ := hv_in_V u hu
      exact ⟨i, mem_filter.mpr ⟨mem_univ i, ⟨u, mem_inter.mpr ⟨hu, hui⟩⟩⟩, hui⟩
    have hcard_eq : (clSet Q).card = Q.card := by
      symm
      refine Finset.card_bij (fun u hu ↦ (hv_cl u hu).choose) ?_ ?_ ?_
      · intro u hu; exact (hv_cl u hu).choose_spec.1
      · intro u₁ hu₁ u₂ hu₂ heq
        have h1 : u₁ ∈ V ((hv_cl u₁ hu₁).choose) := (hv_cl u₁ hu₁).choose_spec.2
        have h2 : u₂ ∈ V ((hv_cl u₁ hu₁).choose) := heq ▸ (hv_cl u₂ hu₂).choose_spec.2
        exact huniq_in_V _ u₁ hu₁ u₂ hu₂ h1 h2
      · intro i hi
        obtain ⟨u, hu⟩ := (mem_filter.mp hi).2
        have huQ : u ∈ Q := (mem_inter.mp hu).1
        have hui : u ∈ V i := (mem_inter.mp hu).2
        refine ⟨u, huQ, ?_⟩
        by_contra hne
        exact Finset.disjoint_left.mp (hV_disj _ i hne) (hv_cl u huQ).choose_spec.2 hui
    have hreg_pairs : ∀ i ∈ clSet Q, ∀ j ∈ clSet Q, i ≠ j → s(i, j) ∈ E_reg := by
      intro i hi j hj hij
      obtain ⟨u, hu⟩ := (mem_filter.mp hi).2
      obtain ⟨v, hv⟩ := (mem_filter.mp hj).2
      have huQ : u ∈ Q := (mem_inter.mp hu).1
      have hui : u ∈ V i := (mem_inter.mp hu).2
      have hvQ : v ∈ Q := (mem_inter.mp hv).1
      have hvj : v ∈ V j := (mem_inter.mp hv).2
      have huv : u ≠ v := fun heq ↦ Finset.disjoint_left.mp (hV_disj i j hij) hui (heq ▸ hvj)
      have hgood := hQedge_good s(u, v) (mem_edgeFinset.mpr (hQ_cl huQ hvQ huv)) (fun x hx ↦ by
        rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption)
      obtain ⟨a, b, hab_reg, x, hxa, y, hyb, heq⟩ := (mem_filter.mp hgood).2
      rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hia : i = a := by
          by_contra h; exact Finset.disjoint_left.mp (hV_disj i a h) hui hxa
        have hjb : j = b := by
          by_contra h; exact Finset.disjoint_left.mp (hV_disj j b h) hvj hyb
        rwa [hia, hjb]
      · have hib : i = b := by
          by_contra h; exact Finset.disjoint_left.mp (hV_disj i b h) hui hyb
        have hja : j = a := by
          by_contra h; exact Finset.disjoint_left.mp (hV_disj j a h) hvj hxa
        rw [hib, hja, Sym2.eq_swap]; exact hab_reg
    refine ⟨mem_filter.mpr ⟨mem_univ _, hcard_eq ▸ hQ_lo, hcard_eq ▸ hQ_hi, hreg_pairs⟩,
      hcard_eq, hcard_one, hv_cl⟩
  -- Bound weight lost by dropping `𝒬3 \ 𝒬_good`.
  have hdrop_bad :
      ∑ Q ∈ 𝒬3 \ 𝒬_good, ((Q.card.choose 2 : ℝ) - 1) * w Q ≤
        (L : ℝ) ^ 2 * (E_bad.card : ℝ) := by
    have hstep1 : ∑ Q ∈ 𝒬3 \ 𝒬_good, ((Q.card.choose 2 : ℝ) - 1) * w Q ≤
        (L : ℝ) ^ 2 * ∑ Q ∈ 𝒬3 \ 𝒬_good, w Q := by
      rw [mul_sum]
      refine sum_le_sum fun Q hQ ↦ ?_
      have hQ3 : Q ∈ 𝒬3 := (mem_sdiff.mp hQ).1
      have hQL : Q.card ≤ L := (mem_filter.mp hQ3).2.2.1
      have hch : (Q.card.choose 2 : ℝ) - 1 ≤ (L : ℝ) ^ 2 := by
        have h1 : Q.card.choose 2 ≤ Q.card * Q.card := by
          rw [Nat.choose_two_right]
          exact Nat.div_le_self _ 2 |>.trans (Nat.mul_le_mul_left _ (Nat.sub_le _ 1))
        have h2 : Q.card * Q.card ≤ L * L := Nat.mul_le_mul hQL hQL
        have h3 : (Q.card.choose 2 : ℝ) ≤ (L : ℝ) ^ 2 := by
          have : (Q.card.choose 2 : ℝ) ≤ ((L * L : ℕ) : ℝ) := by
            exact_mod_cast h1.trans h2
          push_cast at this; linarith
        linarith
      exact mul_le_mul_of_nonneg_right hch (hw_nonneg Q)
    have hstep2 : ∑ Q ∈ 𝒬3 \ 𝒬_good, w Q ≤ (E_bad.card : ℝ) := by
      have hhas_bad : ∀ Q ∈ 𝒬3 \ 𝒬_good,
          ∃ e ∈ E_bad, ∀ x ∈ e, x ∈ Q := by
        intro Q hQ
        obtain ⟨hQ3, hnot⟩ := mem_sdiff.mp hQ
        simp only [𝒬_good, mem_filter, hQ3, true_and, not_forall] at hnot
        obtain ⟨e, heG, heQ, hnotg⟩ := hnot
        exact ⟨e, mem_sdiff.mpr ⟨heG, hnotg⟩, heQ⟩
      calc ∑ Q ∈ 𝒬3 \ 𝒬_good, w Q
          ≤ ∑ Q ∈ 𝒬3 \ 𝒬_good, ∑ e ∈ E_bad, if (∀ x ∈ e, x ∈ Q) then w Q else 0 := by
            refine sum_le_sum fun Q hQ ↦ ?_
            obtain ⟨e₀, he₀, he₀Q⟩ := hhas_bad Q hQ
            calc w Q = (if (∀ x ∈ e₀, x ∈ Q) then w Q else 0) := (if_pos he₀Q).symm
              _ ≤ ∑ e ∈ E_bad, if (∀ x ∈ e, x ∈ Q) then w Q else 0 :=
                single_le_sum (f := fun e ↦ if (∀ x ∈ e, x ∈ Q) then w Q else 0)
                  (fun e _ ↦ by split_ifs <;> [exact hw_nonneg Q; exact le_rfl]) he₀
        _ = ∑ e ∈ E_bad, ∑ Q ∈ 𝒬3 \ 𝒬_good, if (∀ x ∈ e, x ∈ Q) then w Q else 0 := Finset.sum_comm
        _ ≤ ∑ e ∈ E_bad, (1 : ℝ) := by
            refine sum_le_sum fun e he ↦ ?_
            rw [← Finset.sum_filter]
            have hsub : (𝒬3 \ 𝒬_good).filter (fun Q ↦ ∀ x ∈ e, x ∈ Q) ⊆
                Finset.univ.filter (fun Q ↦ 3 ≤ Q.card ∧ Q.card ≤ L ∧
                  G.IsClique (Q : Set (Fin n)) ∧ ∀ x ∈ e, x ∈ Q) := by
              intro Q hQ
              obtain ⟨hQs, heQ⟩ := mem_filter.mp hQ
              have hQ3 := (mem_sdiff.mp hQs).1
              simp only [𝒬3, mem_filter, mem_univ, true_and] at hQ3 ⊢
              exact ⟨hQ3.1, hQ3.2.1, hQ3.2.2, heQ⟩
            exact (sum_le_sum_of_subset_of_nonneg hsub (fun Q _ _ ↦ hw_nonneg Q)).trans
              (hw_edge e (mem_sdiff.mp he).1)
        _ = (E_bad.card : ℝ) := by simp
    exact hstep1.trans (mul_le_mul_of_nonneg_left hstep2 hL2_pos.le)
  -- Define aggregated cluster weights `α₀ : { T // T ∈ 𝒯 } → ℝ`.
  let α₀ : { T // T ∈ 𝒯 } → ℝ := fun T ↦
    (1 / (m : ℝ) ^ 2) * ∑ Q ∈ 𝒬_good.filter (fun Q ↦ clSet Q = T.1), w Q
  have hα₀_nonneg : ∀ T, 0 ≤ α₀ T := fun T ↦
    mul_nonneg (by positivity) (sum_nonneg fun Q _ ↦ hw_nonneg Q)
  -- For each `e ∈ E_reg`, pick canonical endpoints `ep1 e, ep2 e : Fin k`.
  have hep_ex : ∀ e ∈ E_reg, ∃ i j : Fin k, i ≠ j ∧ e = s(i, j) := by
    intro e he
    induction e using Sym2.ind with
    | h i j => exact ⟨i, j, ((hE_reg_mem i j).mp he).1, rfl⟩
  let ep1 : { e // e ∈ E_reg } → Fin k := fun e ↦ (hep_ex e.1 e.2).choose
  let ep2 : { e // e ∈ E_reg } → Fin k := fun e ↦ (hep_ex e.1 e.2).choose_spec.choose
  have hep_ne : ∀ e : { e // e ∈ E_reg }, ep1 e ≠ ep2 e :=
    fun e ↦ (hep_ex e.1 e.2).choose_spec.choose_spec.1
  have hep_eq : ∀ e : { e // e ∈ E_reg }, e.1 = s(ep1 e, ep2 e) :=
    fun e ↦ (hep_ex e.1 e.2).choose_spec.choose_spec.2
  -- Incidence matrix `A`, RHS `b`, objective `c` for cluster LP.
  let A : { e // e ∈ E_reg } → { T // T ∈ 𝒯 } → ℝ :=
    fun e T ↦ if (∀ i ∈ e.1, i ∈ T.1) then 1 else 0
  let b : { e // e ∈ E_reg } → ℝ :=
    fun e ↦ (G.edgeDensity (V (ep1 e)) (V (ep2 e)) : ℝ)
  let c : { T // T ∈ 𝒯 } → ℝ :=
    fun T ↦ (T.1.card.choose 2 : ℝ) - 1
  -- Verify `α₀` satisfies the cluster edge capacity constraints.
  have hα₀_le : ∀ e : { e // e ∈ E_reg }, ∑ T : { T // T ∈ 𝒯 }, A e T * α₀ T ≤ b e := by
    intro e
    let i := ep1 e
    let j := ep2 e
    have hij : i ≠ j := hep_ne e
    have he_eq : e.1 = s(i, j) := hep_eq e
    have hcond : ∀ T : Finset (Fin k), (∀ x ∈ e.1, x ∈ T) ↔ (i ∈ T ∧ j ∈ T) := by
      intro T; rw [he_eq]
      exact ⟨fun h ↦ ⟨h i (Sym2.mem_mk_left i j), h j (Sym2.mem_mk_right i j)⟩,
        fun ⟨hi, hj⟩ x hx ↦ by rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption⟩
    have hsum_lhs : ∑ T : { T // T ∈ 𝒯 }, A e T * α₀ T =
        (1 / (m : ℝ) ^ 2) * ∑ Q ∈ 𝒬_good.filter (fun Q ↦ i ∈ clSet Q ∧ j ∈ clSet Q), w Q := by
      have h1 : ∑ T : { T // T ∈ 𝒯 }, A e T * α₀ T =
          (1 / (m : ℝ) ^ 2) * ∑ T ∈ 𝒯.filter (fun T ↦ i ∈ T ∧ j ∈ T),
            ∑ Q ∈ 𝒬_good.filter (fun Q ↦ clSet Q = T), w Q := by
        rw [mul_sum, Finset.sum_filter, ← Finset.sum_coe_sort 𝒯]
        refine sum_congr rfl fun T _ ↦ ?_
        simp only [A, hcond T.1, α₀]
        split_ifs <;> ring
      rw [h1]
      congr 1
      rw [← Finset.sum_biUnion]
      · congr 1
        ext Q
        simp only [mem_biUnion, mem_filter]
        constructor
        · rintro ⟨T, ⟨_, hiT, hjT⟩, hQg, rfl⟩; exact ⟨hQg, hiT, hjT⟩
        · rintro ⟨hQg, hiQ, hjQ⟩
          exact ⟨clSet Q, ⟨(hQgood_props Q hQg).1, hiQ, hjQ⟩, hQg, rfl⟩
      · intro T₁ _ T₂ _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro Q h1 h2
        exact hne ((mem_filter.mp h1).2.symm.trans (mem_filter.mp h2).2)
    rw [hsum_lhs]
    -- Double count over `(u, v) ∈ G.interedges (V i) (V j)`.
    have hsum_inter : ∑ Q ∈ 𝒬_good.filter (fun Q ↦ i ∈ clSet Q ∧ j ∈ clSet Q), w Q ≤
        ((G.interedges (V i) (V j)).card : ℝ) := by
      have hpair_ex : ∀ Q ∈ 𝒬_good.filter (fun Q ↦ i ∈ clSet Q ∧ j ∈ clSet Q),
          ∃ p ∈ G.interedges (V i) (V j), p.1 ∈ Q ∧ p.2 ∈ Q := by
        intro Q hQ
        obtain ⟨hQg, hiQ, hjQ⟩ := mem_filter.mp hQ
        obtain ⟨u, hu⟩ := (mem_filter.mp hiQ).2
        obtain ⟨v, hv⟩ := (mem_filter.mp hjQ).2
        have huQ : u ∈ Q := (mem_inter.mp hu).1
        have hui : u ∈ V i := (mem_inter.mp hu).2
        have hvQ : v ∈ Q := (mem_inter.mp hv).1
        have hvj : v ∈ V j := (mem_inter.mp hv).2
        have huv : u ≠ v := fun h ↦ Finset.disjoint_left.mp (hV_disj i j hij) hui (h ▸ hvj)
        have hQcl : G.IsClique (Q : Set (Fin n)) := (mem_filter.mp (mem_filter.mp hQg).1).2.2.2
        exact ⟨(u, v), (SimpleGraph.mem_interedges_iff G).mpr ⟨hui, hvj, hQcl huQ hvQ huv⟩, huQ, hvQ⟩
      calc ∑ Q ∈ 𝒬_good.filter (fun Q ↦ i ∈ clSet Q ∧ j ∈ clSet Q), w Q
          ≤ ∑ Q ∈ 𝒬_good.filter (fun Q ↦ i ∈ clSet Q ∧ j ∈ clSet Q),
              ∑ p ∈ G.interedges (V i) (V j), if (p.1 ∈ Q ∧ p.2 ∈ Q) then w Q else 0 := by
            refine sum_le_sum fun Q hQ ↦ ?_
            obtain ⟨p₀, hp₀, hp₀Q⟩ := hpair_ex Q hQ
            calc w Q = (if (p₀.1 ∈ Q ∧ p₀.2 ∈ Q) then w Q else 0) := (if_pos hp₀Q).symm
              _ ≤ ∑ p ∈ G.interedges (V i) (V j), if (p.1 ∈ Q ∧ p.2 ∈ Q) then w Q else 0 :=
                single_le_sum (f := fun p ↦ if (p.1 ∈ Q ∧ p.2 ∈ Q) then w Q else 0)
                  (fun p _ ↦ by split_ifs <;> [exact hw_nonneg Q; exact le_rfl]) hp₀
        _ = ∑ p ∈ G.interedges (V i) (V j),
              ∑ Q ∈ 𝒬_good.filter (fun Q ↦ i ∈ clSet Q ∧ j ∈ clSet Q),
                if (p.1 ∈ Q ∧ p.2 ∈ Q) then w Q else 0 := Finset.sum_comm
        _ ≤ ∑ p ∈ G.interedges (V i) (V j), (1 : ℝ) := by
            refine sum_le_sum fun p hp ↦ ?_
            rw [← Finset.sum_filter]
            have hadj : G.Adj p.1 p.2 := ((SimpleGraph.mem_interedges_iff G).mp hp).2.2
            have hsub : (𝒬_good.filter (fun Q ↦ i ∈ clSet Q ∧ j ∈ clSet Q)).filter
                (fun Q ↦ p.1 ∈ Q ∧ p.2 ∈ Q) ⊆
                Finset.univ.filter (fun Q ↦ 3 ≤ Q.card ∧ Q.card ≤ L ∧
                  G.IsClique (Q : Set (Fin n)) ∧ ∀ x ∈ s(p.1, p.2), x ∈ Q) := by
              intro Q hQ
              obtain ⟨hQ1, hp1, hp2⟩ := mem_filter.mp hQ
              have hQ3 := (mem_filter.mp (mem_filter.mp hQ1).1).1
              simp only [𝒬3, mem_filter, mem_univ, true_and] at hQ3 ⊢
              refine ⟨hQ3.1, hQ3.2.1, hQ3.2.2, fun x hx ↦ ?_⟩
              rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption
            exact (sum_le_sum_of_subset_of_nonneg hsub (fun Q _ _ ↦ hw_nonneg Q)).trans
              (hw_edge s(p.1, p.2) (mem_edgeFinset.mpr hadj))
        _ = ((G.interedges (V i) (V j)).card : ℝ) := by simp
    have hbd : b e = (1 / (m : ℝ) ^ 2) * ((G.interedges (V i) (V j)).card : ℝ) := by
      simp only [b, i, j, SimpleGraph.edgeDensity, Rel.edgeDensity, SimpleGraph.interedges]
      push_cast
      rw [hV_card (ep1 e), hV_card (ep2 e)]
      ring
    rw [hbd]
    exact mul_le_mul_of_nonneg_left hsum_inter (by positivity)
  -- Every feasible `α` is bounded by `1` (since each `T ∈ 𝒯` has `T.card ≥ 3`, hence contains some `e ∈ E_reg`).
  have hbounded : ∀ x : { T // T ∈ 𝒯 } → ℝ,
      (∀ T, 0 ≤ x T) → (∀ e, ∑ T, A e T * x T ≤ b e) → ∀ T, x T ≤ 1 := by
    intro x hx_nn hx_le T
    have hT := (mem_filter.mp T.2).2
    have h2 : 2 ≤ T.1.card := by omega
    obtain ⟨a, ha, b', hb', hab⟩ := Finset.one_lt_card.mp (by omega : 1 < T.1.card)
    have he_mem : s(a, b') ∈ E_reg := hT.2.2 a ha b' hb' hab
    let e : { e // e ∈ E_reg } := ⟨s(a, b'), he_mem⟩
    have hAeT : A e T = 1 := by
      simp only [A, e]
      rw [if_pos]
      intro u hu
      rcases Sym2.mem_iff.mp hu with rfl | rfl <;> assumption
    have hbe_le : b e ≤ 1 := by
      have h1 : G.edgeDensity (V (ep1 e)) (V (ep2 e)) ≤ 1 :=
        SimpleGraph.edgeDensity_le_one G _ _
      change (G.edgeDensity (V (ep1 e)) (V (ep2 e)) : ℝ) ≤ 1
      exact_mod_cast h1
    calc x T = A e T * x T := by rw [hAeT, one_mul]
      _ ≤ ∑ T' : { T // T ∈ 𝒯 }, A e T' * x T' :=
        single_le_sum (fun T' _ ↦ mul_nonneg (by simp only [A]; split_ifs <;> norm_num) (hx_nn T'))
          (mem_univ T)
      _ ≤ b e := hx_le e
      _ ≤ 1 := hbe_le
  -- Step 6: Apply Basic Feasible Solution support bound!
  obtain ⟨α_star, hα_nn, hα_le, hα_opt, hα_supp_card⟩ :=
    bfs_support_bound A b c 1 α₀ hα₀_nonneg hα₀_le hbounded
  -- Objective of `α₀` equals `𝒬_good` weight divided by `m^2`.
  have hα₀_obj : (∑ T : { T // T ∈ 𝒯 }, c T * α₀ T) * (m : ℝ) ^ 2 =
      ∑ Q ∈ 𝒬_good, ((Q.card.choose 2 : ℝ) - 1) * w Q := by
    rw [sum_mul]
    have h1 : ∑ T : { T // T ∈ 𝒯 }, c T * α₀ T * (m : ℝ) ^ 2 =
        ∑ T ∈ 𝒯, ∑ Q ∈ 𝒬_good.filter (fun Q ↦ clSet Q = T),
          ((Q.card.choose 2 : ℝ) - 1) * w Q := by
      rw [← Finset.sum_coe_sort 𝒯]
      refine sum_congr rfl fun T _ ↦ ?_
      have hm2_ne : (m : ℝ) ^ 2 ≠ 0 := by positivity
      calc c T * α₀ T * (m : ℝ) ^ 2
          = c T * ∑ Q ∈ 𝒬_good.filter (fun Q ↦ clSet Q = T.1), w Q := by
            simp only [α₀]; field_simp
        _ = ∑ Q ∈ 𝒬_good.filter (fun Q ↦ clSet Q = T.1), c T * w Q := mul_sum _ _ _
        _ = ∑ Q ∈ 𝒬_good.filter (fun Q ↦ clSet Q = T.1),
            ((Q.card.choose 2 : ℝ) - 1) * w Q := by
          refine sum_congr rfl fun Q hQ ↦ ?_
          have hQg : Q ∈ 𝒬_good := (mem_filter.mp hQ).1
          have hcl : clSet Q = T.1 := (mem_filter.mp hQ).2
          have hcard := (hQgood_props Q hQg).2.1
          simp only [c, ← hcl, hcard]
    rw [h1, ← Finset.sum_biUnion]
    · congr 1
      ext Q
      simp only [mem_biUnion, mem_filter]
      exact ⟨fun ⟨_, _, hQg, _⟩ ↦ hQg,
        fun hQg ↦ ⟨clSet Q, (hQgood_props Q hQg).1, hQg, rfl⟩⟩
    · intro T₁ _ T₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro Q h1 h2
      exact hne ((mem_filter.mp h1).2.symm.trans (mem_filter.mp h2).2)
  -- Step 7: Drop small `α_star T < δ` to form `𝒯_big`.
  let 𝒯_big : Finset { T // T ∈ 𝒯 } := Finset.univ.filter (fun T ↦ δ ≤ α_star T)
  let supp_α : Finset { T // T ∈ 𝒯 } := Finset.univ.filter (fun T ↦ α_star T ≠ 0)
  have h𝒯_big_sub : 𝒯_big ⊆ supp_α := by
    intro T hT
    exact mem_filter.mpr ⟨mem_univ T, ne_of_gt (lt_of_lt_of_le hδ_pos (mem_filter.mp hT).2)⟩
  have hsupp_le_k2 : (supp_α.card : ℝ) ≤ (k : ℝ) ^ 2 / 2 := by
    have h1 : (supp_α.card : ℝ) ≤ (Fintype.card { e // e ∈ E_reg } : ℝ) := by
      exact_mod_cast hα_supp_card
    rw [Fintype.card_coe] at h1
    exact h1.trans hE_reg_card
  have hc_le_L2 : ∀ T : { T // T ∈ 𝒯 }, c T ≤ (L : ℝ) ^ 2 := by
    intro T
    have hTL : T.1.card ≤ L := (mem_filter.mp T.2).2.2.1
    have h1 : T.1.card.choose 2 ≤ T.1.card * T.1.card := by
      rw [Nat.choose_two_right]
      exact (Nat.div_le_self _ 2).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ 1))
    have h2 : T.1.card * T.1.card ≤ L * L := Nat.mul_le_mul hTL hTL
    have h3 : (T.1.card.choose 2 : ℝ) ≤ (L : ℝ) ^ 2 := by
      have : (T.1.card.choose 2 : ℝ) ≤ ((L * L : ℕ) : ℝ) := by exact_mod_cast h1.trans h2
      push_cast at this; linarith
    simp only [c]; linarith
  have hc_nonneg : ∀ T : { T // T ∈ 𝒯 }, 0 ≤ c T := by
    intro T
    have hT3 : 3 ≤ T.1.card := (mem_filter.mp T.2).2.1
    have h1 : 1 ≤ T.1.card.choose 2 := by
      rw [Nat.choose_two_right]
      have h32 : 3 * (3 - 1) ≤ T.1.card * (T.1.card - 1) := Nat.mul_le_mul hT3 (by omega)
      omega
    have h1r : (1 : ℝ) ≤ (T.1.card.choose 2 : ℝ) := by exact_mod_cast h1
    simp only [c]; linarith
  have hdrop_small :
      (∑ T : { T // T ∈ 𝒯 }, c T * α_star T - ∑ T ∈ 𝒯_big, c T * α_star T) * (m : ℝ) ^ 2 ≤
        (ζ / 32) * (n : ℝ) ^ 2 := by
    have hdiff : ∑ T : { T // T ∈ 𝒯 }, c T * α_star T - ∑ T ∈ 𝒯_big, c T * α_star T =
        ∑ T ∈ supp_α \ 𝒯_big, c T * α_star T := by
      have hsub1 : 𝒯_big ⊆ supp_α := h𝒯_big_sub
      have htot : ∑ T : { T // T ∈ 𝒯 }, c T * α_star T = ∑ T ∈ supp_α, c T * α_star T := by
        symm
        refine sum_subset (subset_univ supp_α) fun T _ hT ↦ ?_
        have h0 : α_star T = 0 := by
          by_contra hne; exact hT (mem_filter.mpr ⟨mem_univ T, hne⟩)
        simp [h0]
      rw [htot, ← Finset.sum_sdiff hsub1]
      ring
    rw [hdiff]
    have h1 : ∑ T ∈ supp_α \ 𝒯_big, c T * α_star T ≤ (supp_α.card : ℝ) * ((L : ℝ) ^ 2 * δ) := by
      calc ∑ T ∈ supp_α \ 𝒯_big, c T * α_star T
          ≤ ∑ _T ∈ supp_α \ 𝒯_big, ((L : ℝ) ^ 2 * δ) := by
            refine sum_le_sum fun T hT ↦ ?_
            have hlt : α_star T < δ := by
              have hnot := (mem_sdiff.mp hT).2
              simp only [𝒯_big, mem_filter, mem_univ, true_and, not_le] at hnot
              exact hnot
            exact mul_le_mul (hc_le_L2 T) hlt.le (hα_nn T) hL2_pos.le
        _ = ((supp_α \ 𝒯_big).card : ℝ) * ((L : ℝ) ^ 2 * δ) := by simp
        _ ≤ (supp_α.card : ℝ) * ((L : ℝ) ^ 2 * δ) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_card sdiff_subset) (by positivity)
    calc (∑ T ∈ supp_α \ 𝒯_big, c T * α_star T) * (m : ℝ) ^ 2
        ≤ ((supp_α.card : ℝ) * ((L : ℝ) ^ 2 * δ)) * (m : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ ≤ (((k : ℝ) ^ 2 / 2) * ((L : ℝ) ^ 2 * δ)) * (m : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hsupp_le_k2 (by positivity)) (sq_nonneg _)
      _ = ((L : ℝ) ^ 2 * δ / 2) * ((k : ℝ) * (m : ℝ)) ^ 2 := by ring
      _ ≤ ((L : ℝ) ^ 2 * δ / 2) * (n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (mul_nonneg hk_real_pos.le hm_pos.le) hkm_le_n_real 2)
            (div_nonneg (mul_nonneg hL2_pos.le hδ_pos.le) (by norm_num))
      _ = (ζ / 32) * (n : ℝ) ^ 2 := by
          simp only [δ]; field_simp; ring
  -- Step 8: Apply `H1` on each regular cluster pair `e ∈ E_reg`.
  have hcol_ex : ∀ e : { e // e ∈ E_reg },
      ∃ col : Sym2 (Fin n) → Option (Finset (Fin k)),
        ∀ T ∈ 𝒯_big, (∀ x ∈ e.1, x ∈ T.1) →
          ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
            (∀ u v, H.Adj u v ↔ G.Adj u v ∧ col s(u, v) = some T.1) →
            H.IsUniform ε₁ (V (ep1 e)) (V (ep2 e)) ∧
            |(H.edgeDensity (V (ep1 e)) (V (ep2 e)) : ℝ) - α_star T| ≤ ε₁ := by
    intro e
    let 𝒯_e : Finset { T // T ∈ 𝒯 } := 𝒯_big.filter (fun T ↦ ∀ x ∈ e.1, x ∈ T.1)
    let r : ℕ := 𝒯_e.card
    let equiv_e : 𝒯_e ≃ Fin r := 𝒯_e.equivFin
    let α_e : Fin r → ℝ := fun s ↦ α_star (equiv_e.symm s).1
    have hα_e_δ : ∀ s : Fin r, δ ≤ α_e s := fun s ↦
      (mem_filter.mp (mem_filter.mp (equiv_e.symm s).2).1).2
    have hα_e_sum : ∑ s : Fin r, α_e s ≤ (G.edgeDensity (V (ep1 e)) (V (ep2 e)) : ℝ) := by
      have h1 : ∑ s : Fin r, α_e s = ∑ T ∈ 𝒯_e, α_star T := by
        rw [← Finset.sum_coe_sort 𝒯_e]
        exact Fintype.sum_equiv equiv_e.symm _ _ (fun _ ↦ rfl)
      rw [h1]
      calc ∑ T ∈ 𝒯_e, α_star T
          = ∑ T ∈ 𝒯_e, A e T * α_star T := by
            refine sum_congr rfl fun T hT ↦ ?_
            have hTe : ∀ x ∈ e.1, x ∈ T.1 := (mem_filter.mp hT).2
            simp only [A, if_pos hTe, one_mul]
        _ ≤ ∑ T : { T // T ∈ 𝒯 }, A e T * α_star T :=
            sum_le_sum_of_subset_of_nonneg (subset_univ _) fun T _ _ ↦
              mul_nonneg (by simp only [A]; split_ifs <;> norm_num) (hα_nn T)
        _ ≤ b e := hα_le e
    have he_unif : G.IsUniform ε_split (V (ep1 e)) (V (ep2 e)) :=
      hE_reg_unif_split (ep1 e) (ep2 e) (hep_eq e ▸ e.2)
    obtain ⟨col_raw, hcol_raw⟩ := hsplit n m hm_split G (V (ep1 e)) (V (ep2 e))
      (hV_disj (ep1 e) (ep2 e) (hep_ne e)) (hV_card (ep1 e)) (hV_card (ep2 e))
      he_unif r α_e hα_e_δ hα_e_sum
    refine ⟨fun f ↦ (col_raw f).map (fun s ↦ (equiv_e.symm s).1.1), ?_⟩
    intro T hT hTe H _ hH
    have hT_mem : T ∈ 𝒯_e := mem_filter.mpr ⟨hT, hTe⟩
    let s : Fin r := equiv_e ⟨T, hT_mem⟩
    have hs_eq : (equiv_e.symm s).1 = T := by simp [s]
    have hcol_iff : ∀ f : Sym2 (Fin n),
        (col_raw f).map (fun s' ↦ (equiv_e.symm s').1.1) = some T.1 ↔ col_raw f = some s := by
      intro f
      cases hc : col_raw f with
      | none => simp
      | some s' =>
        simp only [Option.map_some, Option.some.injEq]
        constructor
        · intro heq
          have h1 : (equiv_e.symm s').1 = (equiv_e.symm s).1 := Subtype.ext (heq.trans (by rw [hs_eq]))
          have h2 : equiv_e.symm s' = equiv_e.symm s := Subtype.ext h1
          exact equiv_e.symm.injective h2
        · rintro rfl; rw [hs_eq]
    have hH' : ∀ u v, H.Adj u v ↔ G.Adj u v ∧ col_raw s(u, v) = some s := fun u v ↦ by
      rw [hH u v, hcol_iff s(u, v)]
    have hres := hcol_raw s H hH'
    simpa [α_e, hs_eq] using hres
  let owner : Sym2 (Fin k) → Sym2 (Fin n) → Option (Finset (Fin k)) :=
    fun e f ↦ if he : e ∈ E_reg then (hcol_ex ⟨e, he⟩).choose f else none
  -- Step 9: For each `T ∈ 𝒯_big`, apply `H2` to the color-`T` subgraph `G_T` to get `𝒬_T`.
  have hQT_ex : ∀ T ∈ 𝒯_big,
      ∃ 𝒬 : Finset (Finset (Fin n)),
        (∀ Q ∈ 𝒬, Q.card = T.1.card ∧ G.IsClique (Q : Set (Fin n)) ∧
          (∀ i ∈ T.1, (Q ∩ V i).card = 1) ∧
          (∀ u ∈ Q, ∀ v ∈ Q, u ≠ v →
            ∃ i ∈ T.1, ∃ j ∈ T.1, i ≠ j ∧ u ∈ V i ∧ v ∈ V j ∧
              owner s(i, j) s(u, v) = some T.1)) ∧
        (∀ Q₁ ∈ 𝒬, ∀ Q₂ ∈ 𝒬, Q₁ ≠ Q₂ → (Q₁ ∩ Q₂).card ≤ 1) ∧
        (α_star T - η) * (m : ℝ) ^ 2 ≤ (𝒬.card : ℝ) := by
    intro T hT
    have hT_props := (mem_filter.mp T.2).2
    let q : ℕ := T.1.card
    have hq3 : 3 ≤ q := hT_props.1
    have hqL : q ≤ L := hT_props.2.1
    let τ : T.1 ≃ Fin q := T.1.equivFin
    let W : Fin q → Finset (Fin n) := fun a ↦ V (τ.symm a).1
    have hW_disj : ∀ a b : Fin q, a ≠ b → Disjoint (W a) (W b) := fun a b hab ↦
      hV_disj _ _ (fun h ↦ hab (τ.symm.injective (Subtype.ext h)))
    have hW_card : ∀ a : Fin q, (W a).card = m := fun a ↦ hV_card _
    -- Define the color-`T` subgraph `G_T` of `G`.
    let G_T : SimpleGraph (Fin n) :=
      { Adj := fun u v ↦ G.Adj u v ∧
          ∃ i ∈ T.1, ∃ j ∈ T.1, i ≠ j ∧ u ∈ V i ∧ v ∈ V j ∧
            owner s(i, j) s(u, v) = some T.1
        symm := ⟨fun u v ⟨hadj, i, hi, j, hj, hij, hui, hvj, hown⟩ ↦
          ⟨hadj.symm, j, hj, i, hi, hij.symm, hvj, hui, by
            rw [Sym2.eq_swap (a := j) (b := i), Sym2.eq_swap (a := v) (b := u)]
            exact hown⟩⟩
        loopless := ⟨fun u ⟨hadj, _⟩ ↦ hadj.ne rfl⟩ }
    have hGT_unif : ∀ a b : Fin q, a ≠ b →
        G_T.IsUniform ε₁ (W a) (W b) ∧
        |(G_T.edgeDensity (W a) (W b) : ℝ) - α_star T| ≤ ε₁ := by
      intro a b hab
      let i := (τ.symm a).1
      let j := (τ.symm b).1
      have hiT : i ∈ T.1 := (τ.symm a).2
      have hjT : j ∈ T.1 := (τ.symm b).2
      have hij : i ≠ j := fun h ↦ hab (τ.symm.injective (Subtype.ext h))
      have he_mem : s(i, j) ∈ E_reg := hT_props.2.2 i hiT j hjT hij
      let e : { e // e ∈ E_reg } := ⟨s(i, j), he_mem⟩
      let H_e : SimpleGraph (Fin n) :=
        { Adj := fun u v ↦ G.Adj u v ∧ (hcol_ex e).choose s(u, v) = some T.1
          symm := ⟨fun u v ⟨h, hc⟩ ↦ ⟨h.symm, by rwa [Sym2.eq_swap]⟩⟩
          loopless := ⟨fun u ⟨h, _⟩ ↦ h.ne rfl⟩ }
      have hHe_spec := (hcol_ex e).choose_spec T hT (fun x hx ↦ by
        rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption) H_e (fun _ _ ↦ Iff.rfl)
      -- Match `(ep1 e, ep2 e)` with `(i, j)` (up to symmetry).
      have hHe_ij : H_e.IsUniform ε₁ (V i) (V j) ∧
          |(H_e.edgeDensity (V i) (V j) : ℝ) - α_star T| ≤ ε₁ := by
        rcases Sym2.eq_iff.mp (hep_eq e) with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]
          exact hHe_spec
        · rw [h1, h2]
          exact ⟨hHe_spec.1.symm, by rw [SimpleGraph.edgeDensity_comm]; exact hHe_spec.2⟩
      -- On `V i × V j`, `G_T.Adj` agrees with `H_e.Adj`.
      have hcongr : ∀ u ∈ V i, ∀ v ∈ V j, G_T.Adj u v ↔ H_e.Adj u v := by
        intro u hui v hvj
        constructor
        · rintro ⟨hadj, i', _, j', _, _, hui', hvj', hown⟩
          have hii' : i = i' := by
            by_contra h; exact Finset.disjoint_left.mp (hV_disj i i' h) hui hui'
          have hjj' : j = j' := by
            by_contra h; exact Finset.disjoint_left.mp (hV_disj j j' h) hvj hvj'
          subst hii' hjj'
          refine ⟨hadj, ?_⟩
          simpa [owner, dif_pos he_mem, e] using hown
        · rintro ⟨hadj, hc⟩
          refine ⟨hadj, i, hiT, j, hjT, hij, hui, hvj, ?_⟩
          simpa [owner, dif_pos he_mem, e] using hc
      change G_T.IsUniform ε₁ (V i) (V j) ∧ |(G_T.edgeDensity (V i) (V j) : ℝ) - α_star T| ≤ ε₁
      rw [isUniform_congr_on G_T H_e hcongr, edgeDensity_congr_on G_T H_e hcongr]
      exact hHe_ij
    have hα_δ : δ ≤ α_star T := (mem_filter.mp hT).2
    have hα_1 : α_star T ≤ 1 := hbounded α_star hα_nn hα_le T
    obtain ⟨𝒬, hQ_cl, hQ_disj, hQ_card⟩ :=
      hpack q hq3 hqL n m hm_pack G_T W hW_disj hW_card (α_star T) hα_δ hα_1 hGT_unif
    refine ⟨𝒬, ?_, hQ_disj, hQ_card⟩
    intro Q hQ
    obtain ⟨hQc, hQ_GT_cl, hQ_trans⟩ := hQ_cl Q hQ
    refine ⟨hQc, fun u hu v hv huv ↦ (hQ_GT_cl hu hv huv).1, ?_, ?_⟩
    · intro i hiT
      simpa [W] using hQ_trans (τ ⟨i, hiT⟩)
    · intro u hu v hv huv
      exact (hQ_GT_cl hu hv huv).2
  -- Step 10: Assemble all packed cliques `𝒬_pack` and complete to a clique edge partition `P_out`.
  let 𝒬_of : { T // T ∈ 𝒯_big } → Finset (Finset (Fin n)) :=
    fun T ↦ (hQT_ex T.1 T.2).choose
  have hQof_spec : ∀ T : { T // T ∈ 𝒯_big },
      (∀ Q ∈ 𝒬_of T, Q.card = T.1.1.card ∧ G.IsClique (Q : Set (Fin n)) ∧
        (∀ i ∈ T.1.1, (Q ∩ V i).card = 1) ∧
        (∀ u ∈ Q, ∀ v ∈ Q, u ≠ v →
          ∃ i ∈ T.1.1, ∃ j ∈ T.1.1, i ≠ j ∧ u ∈ V i ∧ v ∈ V j ∧
            owner s(i, j) s(u, v) = some T.1.1)) ∧
      (∀ Q₁ ∈ 𝒬_of T, ∀ Q₂ ∈ 𝒬_of T, Q₁ ≠ Q₂ → (Q₁ ∩ Q₂).card ≤ 1) ∧
      (α_star T.1 - η) * (m : ℝ) ^ 2 ≤ ((𝒬_of T).card : ℝ) :=
    fun T ↦ (hQT_ex T.1 T.2).choose_spec
  -- Cliques from different `T₁ ≠ T₂` cannot share an edge (and in particular are distinct!).
  have hcross_disj : ∀ T₁ T₂ : { T // T ∈ 𝒯_big }, ∀ Q₁ ∈ 𝒬_of T₁, ∀ Q₂ ∈ 𝒬_of T₂,
      ∀ u v : Fin n, u ≠ v → u ∈ Q₁ → v ∈ Q₁ → u ∈ Q₂ → v ∈ Q₂ → T₁ = T₂ := by
    intro T₁ T₂ Q₁ hQ₁ Q₂ hQ₂ u v huv hu₁ hv₁ hu₂ hv₂
    obtain ⟨i₁, _, j₁, _, _, hui₁, hvj₁, hown₁⟩ := (hQof_spec T₁).1 Q₁ hQ₁ |>.2.2.2 u hu₁ v hv₁ huv
    obtain ⟨i₂, _, j₂, _, _, hui₂, hvj₂, hown₂⟩ := (hQof_spec T₂).1 Q₂ hQ₂ |>.2.2.2 u hu₂ v hv₂ huv
    have hi : i₁ = i₂ := by
      by_contra h; exact Finset.disjoint_left.mp (hV_disj i₁ i₂ h) hui₁ hui₂
    have hj : j₁ = j₂ := by
      by_contra h; exact Finset.disjoint_left.mp (hV_disj j₁ j₂ h) hvj₁ hvj₂
    subst hi hj
    have heq : some T₁.1.1 = some T₂.1.1 := hown₁.symm.trans hown₂
    exact Subtype.ext (Subtype.ext (Option.some.inj heq))
  have hQof_pairwise_disj :
      Set.PairwiseDisjoint (Finset.univ : Finset { T // T ∈ 𝒯_big }) 𝒬_of := by
    intro T₁ _ T₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro Q hQ₁ hQ₂
    have hQcard : 3 ≤ Q.card := by
      rw [((hQof_spec T₁).1 Q hQ₁).1]
      exact (mem_filter.mp T₁.1.2).2.1
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (by omega : 1 < Q.card)
    exact hne (hcross_disj T₁ T₂ Q hQ₁ Q hQ₂ u v huv hu hv hu hv)
  let 𝒬_pack : Finset (Finset (Fin n)) := Finset.univ.biUnion 𝒬_of
  have hpack_clique : ∀ Q ∈ 𝒬_pack, 3 ≤ Q.card ∧ G.IsClique (Q : Set (Fin n)) := by
    intro Q hQ
    obtain ⟨T, _, hQT⟩ := mem_biUnion.mp hQ
    have hs := (hQof_spec T).1 Q hQT
    exact ⟨hs.1 ▸ (mem_filter.mp T.1.2).2.1, hs.2.1⟩
  have hpack_edge_uniq : ∀ Q₁ ∈ 𝒬_pack, ∀ Q₂ ∈ 𝒬_pack,
      ∀ u v : Fin n, u ≠ v → u ∈ Q₁ → v ∈ Q₁ → u ∈ Q₂ → v ∈ Q₂ → Q₁ = Q₂ := by
    intro Q₁ hQ₁ Q₂ hQ₂ u v huv hu₁ hv₁ hu₂ hv₂
    obtain ⟨T₁, _, hQT₁⟩ := mem_biUnion.mp hQ₁
    obtain ⟨T₂, _, hQT₂⟩ := mem_biUnion.mp hQ₂
    have hT : T₁ = T₂ := hcross_disj T₁ T₂ Q₁ hQT₁ Q₂ hQT₂ u v huv hu₁ hv₁ hu₂ hv₂
    subst hT
    by_contra hne
    have hle := (hQof_spec T₁).2.1 Q₁ hQT₁ Q₂ hQT₂ hne
    have hge : 2 ≤ (Q₁ ∩ Q₂).card := by
      have hsub : ({u, v} : Finset (Fin n)) ⊆ Q₁ ∩ Q₂ := by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl <;> exact mem_inter.mpr ⟨by assumption, by assumption⟩
      exact (card_pair huv).symm.le.trans (card_le_card hsub)
    omega
  -- Complete `𝒬_pack` with uncovered edges as `K_2`s.
  let E_cov : Finset (Sym2 (Fin n)) :=
    G.edgeFinset.filter (fun e ↦ ∃ Q ∈ 𝒬_pack, ∀ x ∈ e, x ∈ Q)
  let P_rem : Finset (Finset (Fin n)) := (G.edgeFinset \ E_cov).image Sym2.toFinset
  let P_out : Finset (Finset (Fin n)) := 𝒬_pack ∪ P_rem
  -- Verify `G.IsCliqueEdgePartition P_out`.
  have hP_part : G.IsCliqueEdgePartition P_out := by
    constructor
    · intro Q hQ
      rcases mem_union.mp hQ with h1 | h2
      · obtain ⟨hc, hcl⟩ := hpack_clique Q h1
        exact ⟨by omega, hcl⟩
      · obtain ⟨e, he, rfl⟩ := mem_image.mp h2
        have hadj : e ∈ G.edgeSet := mem_edgeFinset.mp (mem_sdiff.mp he).1
        induction e using Sym2.ind with
        | h a b =>
          rw [Sym2.toFinset_mk_eq, card_pair (G.ne_of_adj hadj), coe_pair]
          exact ⟨le_rfl, isClique_pair.mpr (fun _ ↦ hadj)⟩
    · intro a b hab
      by_cases hcov : s(a, b) ∈ E_cov
      · obtain ⟨Q, hQ, hQab⟩ := (mem_filter.mp hcov).2
        refine ⟨Q, ⟨mem_union_left _ hQ, hQab a (by simp), hQab b (by simp)⟩, ?_⟩
        rintro Q' ⟨hQ'P, haQ', hbQ'⟩
        rcases mem_union.mp hQ'P with h1 | h2
        · exact hpack_edge_uniq Q' h1 Q hQ a b hab.ne haQ' hbQ'
            (hQab a (by simp)) (hQab b (by simp))
        · obtain ⟨e, he, rfl⟩ := mem_image.mp h2
          have heq : e = s(a, b) := (Sym2.mem_and_mem_iff hab.ne).mp
            ⟨Sym2.mem_toFinset.mp haQ', Sym2.mem_toFinset.mp hbQ'⟩
          exact absurd (heq ▸ hcov) (mem_sdiff.mp he).2
      · have hmem : s(a, b).toFinset ∈ P_rem :=
          mem_image.mpr ⟨s(a, b), mem_sdiff.mpr ⟨mem_edgeFinset.mpr hab, hcov⟩, rfl⟩
        refine ⟨s(a, b).toFinset, ⟨mem_union_right _ hmem, by simp, by simp⟩, ?_⟩
        rintro Q' ⟨hQ'P, haQ', hbQ'⟩
        rcases mem_union.mp hQ'P with h1 | h2
        · exfalso
          exact hcov (mem_filter.mpr ⟨mem_edgeFinset.mpr hab, Q', h1, fun x hx ↦ by
            rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption⟩)
        · obtain ⟨e, _, rfl⟩ := mem_image.mp h2
          have heq : e = s(a, b) := (Sym2.mem_and_mem_iff hab.ne).mp
            ⟨Sym2.mem_toFinset.mp haQ', Sym2.mem_toFinset.mp hbQ'⟩
          rw [heq]
  -- Count `E_cov.card = ∑ Q ∈ 𝒬_pack, Q.card.choose 2`.
  have hE_cov_card : E_cov.card = ∑ Q ∈ 𝒬_pack, Q.card.choose 2 := by
    have hbi : E_cov = 𝒬_pack.biUnion (fun Q ↦ G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ Q)) := by
      ext e
      simp only [E_cov, mem_filter, mem_biUnion]
      exact ⟨fun ⟨he, Q, hQ, hQe⟩ ↦ ⟨Q, hQ, he, hQe⟩,
        fun ⟨Q, hQ, he, hQe⟩ ↦ ⟨he, Q, hQ, hQe⟩⟩
    rw [hbi, Finset.card_biUnion]
    · exact sum_congr rfl fun Q hQ ↦ clique_edges_card G Q (hpack_clique Q hQ).2
    · intro Q₁ hQ₁ Q₂ hQ₂ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro e he₁ he₂
      have hadj : e ∈ G.edgeSet := mem_edgeFinset.mp (mem_filter.mp he₁).1
      induction e using Sym2.ind with
      | h u v =>
        exact hne (hpack_edge_uniq Q₁ hQ₁ Q₂ hQ₂ u v (G.ne_of_adj hadj)
          ((mem_filter.mp he₁).2 u (by simp)) ((mem_filter.mp he₁).2 v (by simp))
          ((mem_filter.mp he₂).2 u (by simp)) ((mem_filter.mp he₂).2 v (by simp)))
  -- Final cardinality bound on `P_out`!
  have hP_card_le : (P_out.card : ℝ) ≤
      (G.edgeFinset.card : ℝ) - ∑ Q ∈ 𝒬_pack, ((Q.card.choose 2 : ℝ) - 1) := by
    have h1 : P_out.card ≤ 𝒬_pack.card + P_rem.card := card_union_le _ _
    have h2 : P_rem.card ≤ (G.edgeFinset \ E_cov).card := card_image_le
    have h3 : (G.edgeFinset \ E_cov).card + E_cov.card = G.edgeFinset.card :=
      card_sdiff_add_card_eq_card (filter_subset _ _)
    have h4 : P_out.card + E_cov.card ≤ G.edgeFinset.card + 𝒬_pack.card := by omega
    have h4r : (P_out.card : ℝ) + (E_cov.card : ℝ) ≤ (G.edgeFinset.card : ℝ) + (𝒬_pack.card : ℝ) := by
      exact_mod_cast h4
    have h5 : ∑ Q ∈ 𝒬_pack, ((Q.card.choose 2 : ℝ) - 1) =
        (E_cov.card : ℝ) - (𝒬_pack.card : ℝ) := by
      rw [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one, hE_cov_card]
      push_cast; rfl
    linarith
  -- Lower bound `∑ Q ∈ 𝒬_pack, ((Q.card.choose 2 : ℝ) - 1)`.
  have hpack_gain :
      ∑ Q ∈ 𝒬_pack, ((Q.card.choose 2 : ℝ) - 1) ≥
        (∑ T ∈ 𝒯_big, c T * α_star T) * (m : ℝ) ^ 2 - (ζ / 32) * (n : ℝ) ^ 2 := by
    rw [Finset.sum_biUnion hQof_pairwise_disj]
    have hterm : ∀ T : { T // T ∈ 𝒯_big },
        ∑ Q ∈ 𝒬_of T, ((Q.card.choose 2 : ℝ) - 1) ≥
          c T.1 * (α_star T.1 - η) * (m : ℝ) ^ 2 := by
      intro T
      have heq : ∑ Q ∈ 𝒬_of T, ((Q.card.choose 2 : ℝ) - 1) =
          c T.1 * ((𝒬_of T).card : ℝ) := by
        calc ∑ Q ∈ 𝒬_of T, ((Q.card.choose 2 : ℝ) - 1)
            = ∑ _Q ∈ 𝒬_of T, c T.1 := by
              refine sum_congr rfl fun Q hQ ↦ ?_
              simp [c, ((hQof_spec T).1 Q hQ).1]
          _ = ((𝒬_of T).card : ℝ) * c T.1 := by simp
          _ = c T.1 * ((𝒬_of T).card : ℝ) := mul_comm _ _
      rw [heq, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hQof_spec T).2.2 (hc_nonneg T.1)
    have hsum1 : ∑ T : { T // T ∈ 𝒯_big }, ∑ Q ∈ 𝒬_of T, ((Q.card.choose 2 : ℝ) - 1) ≥
        ∑ T ∈ 𝒯_big, c T * (α_star T - η) * (m : ℝ) ^ 2 := by
      rw [← Finset.sum_coe_sort 𝒯_big]
      exact sum_le_sum fun T _ ↦ hterm T
    have hη_err : (∑ T ∈ 𝒯_big, c T * η) * (m : ℝ) ^ 2 ≤ (ζ / 32) * (n : ℝ) ^ 2 := by
      have h1 : ∑ T ∈ 𝒯_big, c T * η ≤ (supp_α.card : ℝ) * ((L : ℝ) ^ 2 * η) := by
        calc ∑ T ∈ 𝒯_big, c T * η
            ≤ ∑ _T ∈ 𝒯_big, ((L : ℝ) ^ 2 * η) :=
              sum_le_sum fun T _ ↦ mul_le_mul_of_nonneg_right (hc_le_L2 T) hη_pos.le
          _ = (𝒯_big.card : ℝ) * ((L : ℝ) ^ 2 * η) := by simp
          _ ≤ (supp_α.card : ℝ) * ((L : ℝ) ^ 2 * η) :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_card h𝒯_big_sub) (by positivity)
      calc (∑ T ∈ 𝒯_big, c T * η) * (m : ℝ) ^ 2
          ≤ ((supp_α.card : ℝ) * ((L : ℝ) ^ 2 * η)) * (m : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
        _ ≤ (((k : ℝ) ^ 2 / 2) * ((L : ℝ) ^ 2 * η)) * (m : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hsupp_le_k2 (by positivity)) (sq_nonneg _)
        _ = ((L : ℝ) ^ 2 * η / 2) * ((k : ℝ) * (m : ℝ)) ^ 2 := by ring
        _ ≤ ((L : ℝ) ^ 2 * η / 2) * (n : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hkm_le_n_real 2)
              (by positivity)
        _ = (ζ / 32) * (n : ℝ) ^ 2 := by
            simp only [η]; field_simp; ring
    have halg : ∑ T ∈ 𝒯_big, c T * (α_star T - η) * (m : ℝ) ^ 2 =
        (∑ T ∈ 𝒯_big, c T * α_star T) * (m : ℝ) ^ 2 - (∑ T ∈ 𝒯_big, c T * η) * (m : ℝ) ^ 2 := by
      rw [sum_mul, sum_mul, ← sum_sub_distrib]
      refine sum_congr rfl fun T _ ↦ by ring
    linarith
  -- Combine all bounds!
  have h𝒬3_split : ∑ Q ∈ 𝒬3, ((Q.card.choose 2 : ℝ) - 1) * w Q =
      ∑ Q ∈ 𝒬_good, ((Q.card.choose 2 : ℝ) - 1) * w Q +
      ∑ Q ∈ 𝒬3 \ 𝒬_good, ((Q.card.choose 2 : ℝ) - 1) * w Q := by
    rw [add_comm, Finset.sum_sdiff (filter_subset _ _)]
  have hbad_L2 : (L : ℝ) ^ 2 * (E_bad.card : ℝ) ≤ (3 * ζ / 16) * (n : ℝ) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hE_bad_card hL2_pos.le
    have h2 : (L : ℝ) ^ 2 * ((3 * ζ / (16 * (L : ℝ) ^ 2)) * (n : ℝ) ^ 2) =
        (3 * ζ / 16) * (n : ℝ) ^ 2 := by field_simp
    linarith
  have hα_opt_m2 : (∑ T : { T // T ∈ 𝒯 }, c T * α₀ T) * (m : ℝ) ^ 2 ≤
      (∑ T : { T // T ∈ 𝒯 }, c T * α_star T) * (m : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right hα_opt (sq_nonneg _)
  have hζ_pos_n2 : 0 ≤ ζ * (n : ℝ) ^ 2 := by positivity
  refine ⟨P_out, hP_part, ?_⟩
  linarith

end OMA.R_Erdos81_erdos_81_R1_H2_R1

-- Credit: @preternatural-tocsin

namespace OMA.Erdos81_erdos_81_R1_H2_R1_H1

open SimpleGraph Finset

lemma sum_union_le_of_nonneg {α : Type*} [DecidableEq α]
    {s₁ s₂ : Finset α} {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) :
    ∑ a ∈ s₁ ∪ s₂, f a ≤ ∑ a ∈ s₁, f a + ∑ a ∈ s₂, f a := by
  have h := Finset.sum_union_inter (s₁ := s₁) (s₂ := s₂) (f := f)
  have hnn : 0 ≤ ∑ a ∈ s₁ ∩ s₂, f a := Finset.sum_nonneg fun a _ ↦ hf a
  linarith

lemma sum_biUnion_le_of_nonneg {α β : Type*} [DecidableEq β]
    {s : Finset α} {t : α → Finset β} {f : β → ℝ} (hf : ∀ b, 0 ≤ f b) :
    ∑ b ∈ s.biUnion t, f b ≤ ∑ a ∈ s, ∑ b ∈ t a, f b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    exact (sum_union_le_of_nonneg hf).trans (by linarith)

lemma exp_le_one_add_add_sq {x : ℝ} (hx : |x| ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 := by
  have h := Real.exp_bound hx (n := 2) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one, Nat.factorial_one,
    Nat.succ_eq_add_one, Nat.factorial_two, Nat.cast_ofNat] at h
  push_cast at h
  have h1 : Real.exp x - (1 + x) ≤ |x| ^ 2 * ((3 : ℝ) / (2 * 2)) :=
    (abs_le.mp h).2
  rw [sq_abs] at h1
  nlinarith [sq_nonneg x]

lemma bernoulli_mgf_le {p t : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ht : |t| ≤ 1) :
    p * Real.exp (t * (1 - p)) + (1 - p) * Real.exp (-t * p) ≤ Real.exp (t ^ 2 / 4) := by
  have h1 : |t * (1 - p)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (show 0 ≤ 1 - p by linarith)]
    calc |t| * (1 - p) ≤ 1 * 1 := mul_le_mul ht (by linarith) (by linarith) zero_le_one
      _ = 1 := one_mul 1
  have h2 : |-t * p| ≤ 1 := by
    rw [abs_mul, abs_neg, abs_of_nonneg hp0]
    calc |t| * p ≤ 1 * 1 := mul_le_mul ht hp1 hp0 zero_le_one
      _ = 1 := one_mul 1
  have he1 := exp_le_one_add_add_sq h1
  have he2 := exp_le_one_add_add_sq h2
  have hcomb : p * Real.exp (t * (1 - p)) + (1 - p) * Real.exp (-t * p) ≤
      1 + t ^ 2 * (p * (1 - p)) := by
    have ha := mul_le_mul_of_nonneg_left he1 hp0
    have hb := mul_le_mul_of_nonneg_left he2 (by linarith : 0 ≤ 1 - p)
    linarith
  have hpq : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
  have hle : 1 + t ^ 2 * (p * (1 - p)) ≤ 1 + t ^ 2 / 4 := by
    nlinarith [sq_nonneg t]
  exact hcomb.trans (hle.trans (by linarith [Real.add_one_le_exp (t ^ 2 / 4)]))

lemma prod_hoeffding_tail {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (w : κ → ℝ) (hw_nn : ∀ c, 0 ≤ w c) (hw_sum : ∑ c : κ, w c = 1)
    (c₀ : κ) (S : Finset ι) (t Δ : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (_hΔ : 0 ≤ Δ) :
    ∑ ω ∈ (Finset.univ : Finset (ι → κ)).filter
        (fun ω ↦ Δ ≤ |((S.filter (fun e ↦ ω e = c₀)).card : ℝ) - (S.card : ℝ) * w c₀|),
        (∏ e : ι, w (ω e)) ≤
      2 * Real.exp (-t * Δ + (S.card : ℝ) * (t ^ 2 / 4)) := by
  classical
  let p : ℝ := w c₀
  have hp0 : 0 ≤ p := hw_nn c₀
  have hp1 : p ≤ 1 := by
    calc w c₀ ≤ ∑ c : κ, w c := single_le_sum (fun c _ ↦ hw_nn c) (mem_univ c₀)
      _ = 1 := hw_sum
  -- Moment generating function identity for any `lam` with `|lam| ≤ 1`.
  have hmgf : ∀ lam : ℝ, |lam| ≤ 1 →
      ∑ ω : ι → κ, (∏ e : ι, w (ω e)) *
          Real.exp (lam * (((S.filter (fun e ↦ ω e = c₀)).card : ℝ) - (S.card : ℝ) * p)) ≤
        Real.exp ((S.card : ℝ) * (lam ^ 2 / 4)) := by
    intro lam hlam
    let g : ι → κ → ℝ := fun e c ↦
      if e ∈ S then (if c = c₀ then Real.exp (lam * (1 - p)) else Real.exp (-lam * p)) else 1
    have hprod_eq : ∀ ω : ι → κ,
        Real.exp (lam * (((S.filter (fun e ↦ ω e = c₀)).card : ℝ) - (S.card : ℝ) * p)) =
          ∏ e : ι, g e (ω e) := by
      intro ω
      have h1 : ∏ e : ι, g e (ω e) =
          ∏ e ∈ S, (if ω e = c₀ then Real.exp (lam * (1 - p)) else Real.exp (-lam * p)) := by
        calc ∏ e : ι, g e (ω e)
            = ∏ e ∈ S, g e (ω e) :=
              (Finset.prod_subset (subset_univ S) fun e _ he ↦ by simp [g, he]).symm
          _ = ∏ e ∈ S, (if ω e = c₀ then Real.exp (lam * (1 - p)) else Real.exp (-lam * p)) :=
              Finset.prod_congr rfl fun e he ↦ by simp [g, he]
      rw [h1]
      have h2 : ∏ e ∈ S, (if ω e = c₀ then Real.exp (lam * (1 - p)) else Real.exp (-lam * p)) =
          ∏ e ∈ S, Real.exp (if ω e = c₀ then lam * (1 - p) else -lam * p) := by
        refine Finset.prod_congr rfl fun e _ ↦ by split_ifs <;> rfl
      rw [h2, ← Real.exp_sum]
      congr 1
      have hsum : ∑ e ∈ S, (if ω e = c₀ then lam * (1 - p) else -lam * p) =
          ∑ e ∈ S, ((if ω e = c₀ then lam else 0) - lam * p) := by
        refine Finset.sum_congr rfl fun e _ ↦ ?_
        split_ifs <;> ring
      rw [hsum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
        ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      ring
    have hfactor : ∑ ω : ι → κ, (∏ e : ι, w (ω e)) *
          Real.exp (lam * (((S.filter (fun e ↦ ω e = c₀)).card : ℝ) - (S.card : ℝ) * p)) =
        ∏ e : ι, ∑ c : κ, w c * g e c := by
      have h1 : ∀ ω : ι → κ,
          (∏ e : ι, w (ω e)) *
            Real.exp (lam * (((S.filter (fun e ↦ ω e = c₀)).card : ℝ) - (S.card : ℝ) * p)) =
            ∏ e : ι, (w (ω e) * g e (ω e)) := by
        intro ω; rw [hprod_eq ω, Finset.prod_mul_distrib]
      simp_rw [h1]
      exact (Fintype.prod_sum (fun e c ↦ w c * g e c)).symm
    rw [hfactor]
    have hterm_out : ∀ e : ι, e ∉ S → ∑ c : κ, w c * g e c = 1 := by
      intro e he
      simp [g, he, hw_sum]
    have hterm_in : ∀ e : ι, e ∈ S →
        ∑ c : κ, w c * g e c ≤ Real.exp (lam ^ 2 / 4) := by
      intro e he
      have hsplit : ∑ c : κ, w c * g e c =
          p * Real.exp (lam * (1 - p)) + (1 - p) * Real.exp (-lam * p) := by
        have h1 : ∑ c : κ, w c * g e c =
            w c₀ * Real.exp (lam * (1 - p)) +
            ∑ c ∈ Finset.univ.erase c₀, w c * Real.exp (-lam * p) := by
          rw [← Finset.add_sum_erase _ _ (mem_univ c₀)]
          congr 1
          · simp [g, he]
          · refine Finset.sum_congr rfl fun c hc ↦ ?_
            simp [g, he, (mem_erase.mp hc).1]
        have h2 : ∑ c ∈ Finset.univ.erase c₀, w c = 1 - p := by
          have := Finset.add_sum_erase (Finset.univ : Finset κ) w (mem_univ c₀)
          linarith
        rw [h1, ← Finset.sum_mul, h2]
      rw [hsplit]
      exact bernoulli_mgf_le hp0 hp1 hlam
    have hprod_S : ∏ e : ι, ∑ c : κ, w c * g e c = ∏ e ∈ S, ∑ c : κ, w c * g e c := by
      symm
      refine Finset.prod_subset (subset_univ S) fun e _ he ↦ hterm_out e he
    rw [hprod_S]
    calc ∏ e ∈ S, ∑ c : κ, w c * g e c
        ≤ ∏ _e ∈ S, Real.exp (lam ^ 2 / 4) := by
          refine Finset.prod_le_prod (fun e _ ↦ Finset.sum_nonneg fun c _ ↦ ?_) hterm_in
          exact mul_nonneg (hw_nn c) (by simp only [g]; split_ifs <;> positivity)
      _ = Real.exp (lam ^ 2 / 4) ^ S.card := by simp
      _ = Real.exp ((S.card : ℝ) * (lam ^ 2 / 4)) := by
          rw [← Real.exp_nat_mul]
  -- Apply Markov to upper tail (`lam = t`) and lower tail (`lam = -t`).
  have hP_nn : ∀ ω : ι → κ, 0 ≤ ∏ e : ι, w (ω e) :=
    fun ω ↦ Finset.prod_nonneg fun e _ ↦ hw_nn (ω e)
  have hupper :
      ∑ ω ∈ (Finset.univ : Finset (ι → κ)).filter
          (fun ω ↦ Δ ≤ ((S.filter (fun e ↦ ω e = c₀)).card : ℝ) - (S.card : ℝ) * p),
          (∏ e : ι, w (ω e)) ≤
        Real.exp (-t * Δ + (S.card : ℝ) * (t ^ 2 / 4)) := by
    have h1 : Real.exp (t * Δ) *
        ∑ ω ∈ (Finset.univ : Finset (ι → κ)).filter
            (fun ω ↦ Δ ≤ ((S.filter (fun e ↦ ω e = c₀)).card : ℝ) - (S.card : ℝ) * p),
            (∏ e : ι, w (ω e)) ≤
        Real.exp ((S.card : ℝ) * (t ^ 2 / 4)) := by
      rw [Finset.mul_sum]
      calc ∑ ω ∈ (Finset.univ : Finset (ι → κ)).filter
              (fun ω ↦ Δ ≤ ((S.filter (fun e ↦ ω e = c₀)).card : ℝ) - (S.card : ℝ) * p),
              Real.exp (t * Δ) * (∏ e : ι, w (ω e))
          ≤ ∑ ω ∈ (Finset.univ : Finset (ι → κ)).filter
              (fun ω ↦ Δ ≤ ((S.filter (fun e ↦ ω e = c₀)).card : ℝ) - (S.card : ℝ) * p),
              (∏ e : ι, w (ω e)) *
                Real.exp (t * (((S.filter (fun e ↦ ω e = c₀)).card : ℝ) - (S.card : ℝ) * p)) := by
            refine Finset.sum_le_sum fun ω hω ↦ ?_
            rw [mul_comm (Real.exp (t * Δ))]
            refine mul_le_mul_of_nonneg_left ?_ (hP_nn ω)
            exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (mem_filter.mp hω).2 ht)
        _ ≤ ∑ ω : ι → κ, (∏ e : ι, w (ω e)) *
              Real.exp (t * (((S.filter (fun e ↦ ω e = c₀)).card : ℝ) - (S.card : ℝ) * p)) :=
            Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _)
              (fun ω _ _ ↦ mul_nonneg (hP_nn ω) (Real.exp_pos _).le)
        _ ≤ Real.exp ((S.card : ℝ) * (t ^ 2 / 4)) := hmgf t (by rw [abs_of_nonneg ht]; exact ht1)
    have hpos := Real.exp_pos (t * Δ)
    calc _ ≤ Real.exp ((S.card : ℝ) * (t ^ 2 / 4)) / Real.exp (t * Δ) :=
          (le_div_iff₀' hpos).mpr h1
      _ = Real.exp (-t * Δ + (S.card : ℝ) * (t ^ 2 / 4)) := by
          rw [← Real.exp_sub]; congr 1; ring
  have hlower :
      ∑ ω ∈ (Finset.univ : Finset (ι → κ)).filter
          (fun ω ↦ Δ ≤ (S.card : ℝ) * p - ((S.filter (fun e ↦ ω e = c₀)).card : ℝ)),
          (∏ e : ι, w (ω e)) ≤
        Real.exp (-t * Δ + (S.card : ℝ) * (t ^ 2 / 4)) := by
    have h1 : Real.exp (t * Δ) *
        ∑ ω ∈ (Finset.univ : Finset (ι → κ)).filter
            (fun ω ↦ Δ ≤ (S.card : ℝ) * p - ((S.filter (fun e ↦ ω e = c₀)).card : ℝ)),
            (∏ e : ι, w (ω e)) ≤
        Real.exp ((S.card : ℝ) * ((-t) ^ 2 / 4)) := by
      rw [Finset.mul_sum]
      calc ∑ ω ∈ (Finset.univ : Finset (ι → κ)).filter
              (fun ω ↦ Δ ≤ (S.card : ℝ) * p - ((S.filter (fun e ↦ ω e = c₀)).card : ℝ)),
              Real.exp (t * Δ) * (∏ e : ι, w (ω e))
          ≤ ∑ ω ∈ (Finset.univ : Finset (ι → κ)).filter
              (fun ω ↦ Δ ≤ (S.card : ℝ) * p - ((S.filter (fun e ↦ ω e = c₀)).card : ℝ)),
              (∏ e : ι, w (ω e)) *
                Real.exp ((-t) * (((S.filter (fun e ↦ ω e = c₀)).card : ℝ) - (S.card : ℝ) * p)) := by
            refine Finset.sum_le_sum fun ω hω ↦ ?_
            rw [mul_comm (Real.exp (t * Δ))]
            refine mul_le_mul_of_nonneg_left ?_ (hP_nn ω)
            apply Real.exp_le_exp.mpr
            have hle : Δ ≤ (S.card : ℝ) * p - ((S.filter (fun e ↦ ω e = c₀)).card : ℝ) :=
              (mem_filter.mp hω).2
            nlinarith
        _ ≤ ∑ ω : ι → κ, (∏ e : ι, w (ω e)) *
              Real.exp ((-t) * (((S.filter (fun e ↦ ω e = c₀)).card : ℝ) - (S.card : ℝ) * p)) :=
            Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _)
              (fun ω _ _ ↦ mul_nonneg (hP_nn ω) (Real.exp_pos _).le)
        _ ≤ Real.exp ((S.card : ℝ) * ((-t) ^ 2 / 4)) :=
            hmgf (-t) (by rw [abs_neg, abs_of_nonneg ht]; exact ht1)
    have hpos := Real.exp_pos (t * Δ)
    have hsq : (-t) ^ 2 = t ^ 2 := neg_sq t
    rw [hsq] at h1
    calc _ ≤ Real.exp ((S.card : ℝ) * (t ^ 2 / 4)) / Real.exp (t * Δ) :=
          (le_div_iff₀' hpos).mpr h1
      _ = Real.exp (-t * Δ + (S.card : ℝ) * (t ^ 2 / 4)) := by
          rw [← Real.exp_sub]; congr 1; ring
  have hsub :
      (Finset.univ : Finset (ι → κ)).filter
          (fun ω ↦ Δ ≤ |((S.filter (fun e ↦ ω e = c₀)).card : ℝ) - (S.card : ℝ) * p|) ⊆
        (Finset.univ : Finset (ι → κ)).filter
          (fun ω ↦ Δ ≤ ((S.filter (fun e ↦ ω e = c₀)).card : ℝ) - (S.card : ℝ) * p) ∪
        (Finset.univ : Finset (ι → κ)).filter
          (fun ω ↦ Δ ≤ (S.card : ℝ) * p - ((S.filter (fun e ↦ ω e = c₀)).card : ℝ)) := by
    intro ω hω
    have hge := (mem_filter.mp hω).2
    rcases le_abs.mp hge with h | h
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, by linarith⟩)
  calc ∑ ω ∈ (Finset.univ : Finset (ι → κ)).filter
          (fun ω ↦ Δ ≤ |((S.filter (fun e ↦ ω e = c₀)).card : ℝ) - (S.card : ℝ) * p|),
          (∏ e : ι, w (ω e))
      ≤ ∑ ω ∈ (Finset.univ : Finset (ι → κ)).filter
            (fun ω ↦ Δ ≤ ((S.filter (fun e ↦ ω e = c₀)).card : ℝ) - (S.card : ℝ) * p) ∪
          (Finset.univ : Finset (ι → κ)).filter
            (fun ω ↦ Δ ≤ (S.card : ℝ) * p - ((S.filter (fun e ↦ ω e = c₀)).card : ℝ)),
          (∏ e : ι, w (ω e)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ω _ _ ↦ hP_nn ω)
    _ ≤ ∑ ω ∈ (Finset.univ : Finset (ι → κ)).filter
            (fun ω ↦ Δ ≤ ((S.filter (fun e ↦ ω e = c₀)).card : ℝ) - (S.card : ℝ) * p),
            (∏ e : ι, w (ω e)) +
        ∑ ω ∈ (Finset.univ : Finset (ι → κ)).filter
            (fun ω ↦ Δ ≤ (S.card : ℝ) * p - ((S.filter (fun e ↦ ω e = c₀)).card : ℝ)),
            (∏ e : ι, w (ω e)) :=
        sum_union_le_of_nonneg hP_nn
    _ ≤ Real.exp (-t * Δ + (S.card : ℝ) * (t ^ 2 / 4)) +
        Real.exp (-t * Δ + (S.card : ℝ) * (t ^ 2 / 4)) := add_le_add hupper hlower
    _ = 2 * Real.exp (-t * Δ + (S.card : ℝ) * (t ^ 2 / 4)) := by ring

theorem main_aux : OMA.R_Erdos81_erdos_81_R1_H2_R1.H1 := by
  intro ε₁ hε₁ δ hδ
  classical
  -- Case 1: `1 ≤ ε₁` is trivial with `col := fun _ ↦ none`.
  by_cases hε₁_ge : 1 ≤ ε₁
  · refine ⟨1, zero_lt_one, 1, fun n m _ G _ A B _ _ _ _ r α hα_δ hα_sum ↦ ?_⟩
    refine ⟨fun _ ↦ none, fun s H _ hH ↦ ?_⟩
    refine ⟨H.isUniform_one.mono hε₁_ge, ?_⟩
    have hH_empty : H.interedges A B = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro ⟨u, v⟩ hp
      have hadj : H.Adj u v := ((SimpleGraph.mem_interedges_iff H).mp hp).2.2
      have hnone := ((hH u v).mp hadj).2
      simp at hnone
    have hH_dens : (H.edgeDensity A B : ℝ) = 0 := by
      have hint : Rel.interedges H.Adj A B = ∅ := hH_empty
      simp [SimpleGraph.edgeDensity, Rel.edgeDensity, hint]
    have hα_nn : 0 ≤ α s := hδ.le.trans (hα_δ s)
    have hα_le1 : α s ≤ 1 := by
      have hd1 : (G.edgeDensity A B : ℝ) ≤ 1 := by
        exact_mod_cast SimpleGraph.edgeDensity_le_one G A B
      calc α s ≤ ∑ s' : Fin r, α s' :=
            single_le_sum (fun s' _ ↦ hδ.le.trans (hα_δ s')) (mem_univ s)
        _ ≤ (G.edgeDensity A B : ℝ) := hα_sum
        _ ≤ 1 := hd1
    rw [hH_dens, zero_sub, abs_neg, abs_of_nonneg hα_nn]
    exact hα_le1.trans hε₁_ge
  -- Case 2: `0 < ε₁ < 1`.
  push Not at hε₁_ge
  let ε : ℝ := ε₁ / 4
  have hε_pos : 0 < ε := by positivity
  let t_dev : ℝ := ε₁ / 4
  let lam : ℝ := 2 * t_dev
  have hlam_nn : 0 ≤ lam := by positivity
  have hlam_le1 : lam ≤ 1 := by simp only [lam, t_dev]; linarith
  let c₀ : ℝ := t_dev ^ 2 * ε₁ ^ 2
  have hc₀_pos : 0 < c₀ := by positivity
  let m₀ : ℕ := max 1 (max (Nat.ceil (3 / c₀)) (Nat.ceil (2 / δ)))
  refine ⟨ε, hε_pos, m₀, fun n m hm G _ A B hdisj hA hB hunif r α hα_δ hα_sum ↦ ?_⟩
  -- Handle `r = 0` vacuously.
  by_cases hr0 : r = 0
  · subst hr0
    exact ⟨fun _ ↦ none, fun s ↦ Fin.elim0 s⟩
  have hr_pos : 0 < r := Nat.pos_of_ne_zero hr0
  have hm_one : 1 ≤ m := le_trans (le_max_left _ _) hm
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  let d : ℝ := (G.edgeDensity A B : ℝ)
  have hd_ge_δ : δ ≤ d := by
    let s0 : Fin r := ⟨0, hr_pos⟩
    calc δ ≤ α s0 := hα_δ s0
      _ ≤ ∑ s : Fin r, α s := single_le_sum (fun s _ ↦ hδ.le.trans (hα_δ s)) (mem_univ s0)
      _ ≤ d := hα_sum
  have hd_pos : 0 < d := lt_of_lt_of_le hδ hd_ge_δ
  have hd_le1 : d ≤ 1 := by
    change (G.edgeDensity A B : ℝ) ≤ 1
    exact_mod_cast SimpleGraph.edgeDensity_le_one G A B
  have hr_le : (r : ℝ) ≤ 1 / δ := by
    have h1 : (r : ℝ) * δ ≤ d := by
      calc (r : ℝ) * δ = ∑ _s : Fin r, δ := by simp
        _ ≤ ∑ s : Fin r, α s := sum_le_sum fun s _ ↦ hα_δ s
        _ ≤ d := hα_sum
    exact (le_div_iff₀ hδ).mpr (h1.trans hd_le1)
  -- Probability weights `w : Option (Fin r) → ℝ`.
  let w : Option (Fin r) → ℝ := fun c ↦
    match c with
    | some s => α s / d
    | none => 1 - (∑ s : Fin r, α s) / d
  have hw_nn : ∀ c : Option (Fin r), 0 ≤ w c := by
    intro c
    cases c with
    | none =>
      simp only [w]
      have : (∑ s : Fin r, α s) / d ≤ 1 := (div_le_one hd_pos).mpr hα_sum
      linarith
    | some s =>
      simp only [w]
      exact div_nonneg (hδ.le.trans (hα_δ s)) hd_pos.le
  have hw_sum : ∑ c : Option (Fin r), w c = 1 := by
    rw [Fintype.sum_option]
    simp only [w, ← Finset.sum_div]
    ring
  -- Edge set `E` of `G` between `A` and `B`.
  let E : Finset (Sym2 (Fin n)) := (G.interedges A B).image (fun p ↦ s(p.1, p.2))
  have hpair_inj : ∀ A' ⊆ A, ∀ B' ⊆ B,
      Set.InjOn (fun p : Fin n × Fin n ↦ s(p.1, p.2)) (G.interedges A' B' : Set (Fin n × Fin n)) := by
    intro A' hA' B' hB' p₁ hp₁ p₂ hp₂ heq
    have hp₁' := (SimpleGraph.mem_interedges_iff G).mp (mem_coe.mp hp₁)
    have hp₂' := (SimpleGraph.mem_interedges_iff G).mp (mem_coe.mp hp₂)
    rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exfalso
      exact Finset.disjoint_left.mp hdisj (hA' hp₁'.1) (h1 ▸ hB' hp₂'.2.1)
  -- For any `A' ⊆ A, B' ⊆ B`, the corresponding subset of `{ e // e ∈ E }`.
  let S_of : Finset (Fin n) → Finset (Fin n) → Finset { e // e ∈ E } := fun A' B' ↦
    Finset.univ.filter (fun e ↦ e.1 ∈ (G.interedges A' B').image (fun p ↦ s(p.1, p.2)))
  have hS_card : ∀ A' ⊆ A, ∀ B' ⊆ B, (S_of A' B').card = (G.interedges A' B').card := by
    intro A' hA' B' hB'
    have hsub : (G.interedges A' B').image (fun p ↦ s(p.1, p.2)) ⊆ E :=
      image_subset_image (Rel.interedges_mono hA' hB')
    have h1 : (S_of A' B').card = ((G.interedges A' B').image (fun p ↦ s(p.1, p.2))).card := by
      refine Finset.card_bij (fun e _ ↦ e.1) ?_ ?_ ?_
      · intro e he; exact (mem_filter.mp he).2
      · intro e₁ _ e₂ _ h; exact Subtype.ext h
      · intro f hf; exact ⟨⟨f, hsub hf⟩, mem_filter.mpr ⟨mem_univ _, hf⟩, rfl⟩
    rw [h1, Finset.card_image_of_injOn (hpair_inj A' hA' B' hB')]
  -- Bad event set in `Ω := { e // e ∈ E } → Option (Fin r)`.
  let bigA : Finset (Finset (Fin n)) := A.powerset.filter (fun A' ↦ (m : ℝ) * ε₁ ≤ (A'.card : ℝ))
  let bigB : Finset (Finset (Fin n)) := B.powerset.filter (fun B' ↦ (m : ℝ) * ε₁ ≤ (B'.card : ℝ))
  let badEv : Fin r → Finset (Fin n) → Finset (Fin n) → Finset ({ e // e ∈ E } → Option (Fin r)) :=
    fun s A' B' ↦
      Finset.univ.filter (fun ω ↦
        t_dev * (A'.card : ℝ) * (B'.card : ℝ) ≤
          |(((S_of A' B').filter (fun e ↦ ω e = some s)).card : ℝ) -
            ((S_of A' B').card : ℝ) * w (some s)|)
  let Ω_bad : Finset ({ e // e ∈ E } → Option (Fin r)) :=
    (Finset.univ : Finset (Fin r)).biUnion (fun s ↦
      (bigA ×ˢ bigB).biUnion (fun AB ↦ badEv s AB.1 AB.2))
  have hP_nn : ∀ ω : { e // e ∈ E } → Option (Fin r), 0 ≤ ∏ e : { e // e ∈ E }, w (ω e) :=
    fun ω ↦ Finset.prod_nonneg fun e _ ↦ hw_nn (ω e)
  have hP_total : ∑ ω : { e // e ∈ E } → Option (Fin r), (∏ e : { e // e ∈ E }, w (ω e)) = 1 := by
    rw [← Fintype.prod_sum (fun (_ : { e // e ∈ E }) c ↦ w c)]
    simp [hw_sum]
  -- Bound each individual bad event probability using `prod_hoeffding_tail`.
  have hbad_single : ∀ s : Fin r, ∀ A' ∈ bigA, ∀ B' ∈ bigB,
      ∑ ω ∈ badEv s A' B', (∏ e : { e // e ∈ E }, w (ω e)) ≤
        2 * Real.exp (-c₀ * (m : ℝ) ^ 2) := by
    intro s A' hA' B' hB'
    have hA'_sub : A' ⊆ A := mem_powerset.mp (mem_filter.mp hA').1
    have hB'_sub : B' ⊆ B := mem_powerset.mp (mem_filter.mp hB').1
    have hA'_sz : (m : ℝ) * ε₁ ≤ (A'.card : ℝ) := (mem_filter.mp hA').2
    have hB'_sz : (m : ℝ) * ε₁ ≤ (B'.card : ℝ) := (mem_filter.mp hB').2
    have hΔ_nn : 0 ≤ t_dev * (A'.card : ℝ) * (B'.card : ℝ) := by positivity
    have htail := prod_hoeffding_tail w hw_nn hw_sum (some s) (S_of A' B')
      lam (t_dev * (A'.card : ℝ) * (B'.card : ℝ)) hlam_nn hlam_le1 hΔ_nn
    have hS_le : ((S_of A' B').card : ℝ) ≤ (A'.card : ℝ) * (B'.card : ℝ) := by
      rw [hS_card A' hA'_sub B' hB'_sub]
      exact_mod_cast Rel.card_interedges_le_mul G.Adj A' B'
    have hexp_le : -lam * (t_dev * (A'.card : ℝ) * (B'.card : ℝ)) +
        ((S_of A' B').card : ℝ) * (lam ^ 2 / 4) ≤ -c₀ * (m : ℝ) ^ 2 := by
      have h1 : ((S_of A' B').card : ℝ) * (lam ^ 2 / 4) ≤
          (A'.card : ℝ) * (B'.card : ℝ) * (lam ^ 2 / 4) :=
        mul_le_mul_of_nonneg_right hS_le (by positivity)
      have h2 : -lam * (t_dev * (A'.card : ℝ) * (B'.card : ℝ)) +
          (A'.card : ℝ) * (B'.card : ℝ) * (lam ^ 2 / 4) =
          -(t_dev ^ 2) * ((A'.card : ℝ) * (B'.card : ℝ)) := by
        simp only [lam]; ring
      have h3 : (m : ℝ) ^ 2 * ε₁ ^ 2 ≤ (A'.card : ℝ) * (B'.card : ℝ) := by
        have := mul_le_mul hA'_sz hB'_sz (by positivity) (by positivity)
        linarith
      have h4 : c₀ * (m : ℝ) ^ 2 ≤ t_dev ^ 2 * ((A'.card : ℝ) * (B'.card : ℝ)) := by
        have := mul_le_mul_of_nonneg_left h3 (sq_nonneg t_dev)
        simp only [c₀]; linarith
      linarith
    exact htail.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_le) (by norm_num))
  -- Union bound over all `s ∈ Fin r`, `(A', B') ∈ bigA ×ˢ bigB`: total bad mass `< 1`.
  have hbad_lt_one : ∑ ω ∈ Ω_bad, (∏ e : { e // e ∈ E }, w (ω e)) < 1 := by
    have hstep1 : ∑ ω ∈ Ω_bad, (∏ e : { e // e ∈ E }, w (ω e)) ≤
        (r : ℝ) * ((bigA.card : ℝ) * (bigB.card : ℝ)) * (2 * Real.exp (-c₀ * (m : ℝ) ^ 2)) := by
      calc ∑ ω ∈ Ω_bad, (∏ e : { e // e ∈ E }, w (ω e))
          ≤ ∑ s : Fin r, ∑ ω ∈ (bigA ×ˢ bigB).biUnion (fun AB ↦ badEv s AB.1 AB.2),
              (∏ e : { e // e ∈ E }, w (ω e)) :=
            sum_biUnion_le_of_nonneg hP_nn
        _ ≤ ∑ s : Fin r, ∑ AB ∈ bigA ×ˢ bigB, ∑ ω ∈ badEv s AB.1 AB.2,
              (∏ e : { e // e ∈ E }, w (ω e)) :=
            Finset.sum_le_sum fun s _ ↦ sum_biUnion_le_of_nonneg hP_nn
        _ ≤ ∑ _s : Fin r, ∑ _AB ∈ bigA ×ˢ bigB, (2 * Real.exp (-c₀ * (m : ℝ) ^ 2)) := by
            refine Finset.sum_le_sum fun s _ ↦ Finset.sum_le_sum fun AB hAB ↦ ?_
            exact hbad_single s AB.1 (mem_product.mp hAB).1 AB.2 (mem_product.mp hAB).2
        _ = (r : ℝ) * ((bigA.card : ℝ) * (bigB.card : ℝ)) * (2 * Real.exp (-c₀ * (m : ℝ) ^ 2)) := by
            simp [card_product, mul_assoc]
    have hbigA_le : (bigA.card : ℝ) ≤ (2 : ℝ) ^ m := by
      have h1 : bigA.card ≤ 2 ^ m :=
        (card_le_card (filter_subset _ _)).trans (by rw [card_powerset, hA])
      exact_mod_cast h1
    have hbigB_le : (bigB.card : ℝ) ≤ (2 : ℝ) ^ m := by
      have h1 : bigB.card ≤ 2 ^ m :=
        (card_le_card (filter_subset _ _)).trans (by rw [card_powerset, hB])
      exact_mod_cast h1
    have h4m_le : (2 : ℝ) ^ m * (2 : ℝ) ^ m ≤ Real.exp (2 * (m : ℝ)) := by
      have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have h4e : (4 : ℝ) ≤ Real.exp 2 := by
        have hsq : (2 : ℝ) ^ 2 ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ zero_le_two h2e 2
        rw [← Real.exp_nat_mul] at hsq
        norm_num at hsq
        exact hsq
      have hpow : (4 : ℝ) ^ m ≤ (Real.exp 2) ^ m := pow_le_pow_left₀ (by norm_num) h4e m
      rw [← Real.exp_nat_mul] at hpow
      have hlhs : (2 : ℝ) ^ m * (2 : ℝ) ^ m = (4 : ℝ) ^ m := by
        rw [← mul_pow]; norm_num
      rw [hlhs]
      simpa [mul_comm] using hpow
    have hm_c0 : 3 / c₀ ≤ (m : ℝ) := by
      have h1 : Nat.ceil (3 / c₀) ≤ m :=
        le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm
      exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
    have hm_δ : 2 / δ ≤ (m : ℝ) := by
      have h1 : Nat.ceil (2 / δ) ≤ m :=
        le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm
      exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
    have hexp_comb : 2 * (m : ℝ) + (-c₀ * (m : ℝ) ^ 2) ≤ -(m : ℝ) := by
      have h1 : 3 ≤ c₀ * (m : ℝ) := by
        have := (div_le_iff₀ hc₀_pos).mp hm_c0
        linarith
      nlinarith
    have hlt_exp : 2 / δ < Real.exp (m : ℝ) := by
      linarith [Real.add_one_le_exp (m : ℝ)]
    calc ∑ ω ∈ Ω_bad, (∏ e : { e // e ∈ E }, w (ω e))
        ≤ (r : ℝ) * ((bigA.card : ℝ) * (bigB.card : ℝ)) * (2 * Real.exp (-c₀ * (m : ℝ) ^ 2)) :=
          hstep1
      _ ≤ (1 / δ) * ((2 : ℝ) ^ m * (2 : ℝ) ^ m) * (2 * Real.exp (-c₀ * (m : ℝ) ^ 2)) := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul hr_le (mul_le_mul hbigA_le hbigB_le (by positivity) (by positivity))
              (by positivity) (by positivity)) (by positivity)
      _ ≤ (1 / δ) * Real.exp (2 * (m : ℝ)) * (2 * Real.exp (-c₀ * (m : ℝ) ^ 2)) := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h4m_le (by positivity)) (by positivity)
      _ = (2 / δ) * Real.exp (2 * (m : ℝ) + (-c₀ * (m : ℝ) ^ 2)) := by
          rw [Real.exp_add]; ring
      _ ≤ (2 / δ) * Real.exp (-(m : ℝ)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_comb) (by positivity)
      _ = (2 / δ) / Real.exp (m : ℝ) := by rw [Real.exp_neg]; ring
      _ < 1 := (div_lt_one (Real.exp_pos _)).mpr hlt_exp
  -- Therefore some `ω₀ ∉ Ω_bad` exists!
  have hex_good : ∃ ω₀ : { e // e ∈ E } → Option (Fin r), ω₀ ∉ Ω_bad := by
    by_contra hall
    push Not at hall
    have hEq : Ω_bad = Finset.univ := eq_univ_of_forall hall
    rw [hEq, hP_total] at hbad_lt_one
    linarith
  obtain ⟨ω₀, hω₀_good⟩ := hex_good
  let col : Sym2 (Fin n) → Option (Fin r) := fun e ↦ if he : e ∈ E then ω₀ ⟨e, he⟩ else none
  refine ⟨col, fun s H _ hH ↦ ?_⟩
  -- For any `A' ∈ bigA, B' ∈ bigB`, relate `H.edgeDensity A' B'` to `G.edgeDensity A' B' * (α s / d)`.
  have hdev : ∀ A' ∈ bigA, ∀ B' ∈ bigB,
      |(H.edgeDensity A' B' : ℝ) - (G.edgeDensity A' B' : ℝ) * (α s / d)| < t_dev := by
    intro A' hA' B' hB'
    have hA'_sub : A' ⊆ A := mem_powerset.mp (mem_filter.mp hA').1
    have hB'_sub : B' ⊆ B := mem_powerset.mp (mem_filter.mp hB').1
    have hA'_pos : (0 : ℝ) < (A'.card : ℝ) := lt_of_lt_of_le (by positivity) (mem_filter.mp hA').2
    have hB'_pos : (0 : ℝ) < (B'.card : ℝ) := lt_of_lt_of_le (by positivity) (mem_filter.mp hB').2
    have hnot : ω₀ ∉ badEv s A' B' := by
      intro hmem
      exact hω₀_good (mem_biUnion.mpr ⟨s, mem_univ s,
        mem_biUnion.mpr ⟨(A', B'), mem_product.mpr ⟨hA', hB'⟩, hmem⟩⟩)
    have hlt : |(((S_of A' B').filter (fun e ↦ ω₀ e = some s)).card : ℝ) -
        ((S_of A' B').card : ℝ) * (α s / d)| < t_dev * (A'.card : ℝ) * (B'.card : ℝ) := by
      simp only [badEv, mem_filter, mem_univ, true_and, not_le, w] at hnot
      exact hnot
    -- Show `#(H.interedges A' B') = #((S_of A' B').filter (fun e ↦ ω₀ e = some s))`.
    have hH_card : (H.interedges A' B').card = ((S_of A' B').filter (fun e ↦ ω₀ e = some s)).card := by
      have hsubE : (G.interedges A' B').image (fun p ↦ s(p.1, p.2)) ⊆ E :=
        image_subset_image (Rel.interedges_mono hA'_sub hB'_sub)
      refine Finset.card_bij
        (fun p hp ↦ ⟨s(p.1, p.2), hsubE (mem_image_of_mem _ (by
          have hp' := (SimpleGraph.mem_interedges_iff H).mp hp
          exact (SimpleGraph.mem_interedges_iff G).mpr ⟨hp'.1, hp'.2.1, ((hH p.1 p.2).mp hp'.2.2).1⟩))⟩)
        ?_ ?_ ?_
      · intro p hp
        have hp' := (SimpleGraph.mem_interedges_iff H).mp hp
        have hG := ((hH p.1 p.2).mp hp'.2.2).1
        have hc := ((hH p.1 p.2).mp hp'.2.2).2
        have hmem_im : s(p.1, p.2) ∈ (G.interedges A' B').image (fun q ↦ s(q.1, q.2)) :=
          mem_image_of_mem _ ((SimpleGraph.mem_interedges_iff G).mpr ⟨hp'.1, hp'.2.1, hG⟩)
        refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hmem_im⟩, ?_⟩
        simpa [col, dif_pos (hsubE hmem_im)] using hc
      · intro p₁ hp₁ p₂ hp₂ heq
        have hp₁' := (SimpleGraph.mem_interedges_iff H).mp hp₁
        have hp₂' := (SimpleGraph.mem_interedges_iff H).mp hp₂
        have hp₁G := (SimpleGraph.mem_interedges_iff G).mpr
          ⟨hp₁'.1, hp₁'.2.1, ((hH p₁.1 p₁.2).mp hp₁'.2.2).1⟩
        have hp₂G := (SimpleGraph.mem_interedges_iff G).mpr
          ⟨hp₂'.1, hp₂'.2.1, ((hH p₂.1 p₂.2).mp hp₂'.2.2).1⟩
        exact hpair_inj A' hA'_sub B' hB'_sub hp₁G hp₂G (congrArg Subtype.val heq)
      · intro e he
        obtain ⟨heS, hωe⟩ := mem_filter.mp he
        obtain ⟨p, hpG, hp_eq⟩ := mem_image.mp (mem_filter.mp heS).2
        have hp' := (SimpleGraph.mem_interedges_iff G).mp hpG
        have hc : col s(p.1, p.2) = some s := by
          simp only [col, dif_pos (hp_eq ▸ e.2)]
          convert hωe using 2
          exact Subtype.ext hp_eq
        refine ⟨p, (SimpleGraph.mem_interedges_iff H).mpr
          ⟨hp'.1, hp'.2.1, (hH p.1 p.2).mpr ⟨hp'.2.2, hc⟩⟩, Subtype.ext hp_eq⟩
    rw [← hH_card, hS_card A' hA'_sub B' hB'_sub] at hlt
    have hAB_pos : (0 : ℝ) < (A'.card : ℝ) * (B'.card : ℝ) := mul_pos hA'_pos hB'_pos
    have hdiv := (div_lt_iff₀ hAB_pos).mpr (by simpa [mul_assoc] using hlt)
    have hrew : |(H.edgeDensity A' B' : ℝ) - (G.edgeDensity A' B' : ℝ) * (α s / d)| =
        |((H.interedges A' B').card : ℝ) - ((G.interedges A' B').card : ℝ) * (α s / d)| /
          ((A'.card : ℝ) * (B'.card : ℝ)) := by
      rw [← abs_of_pos hAB_pos, ← abs_div]
      congr 1
      simp only [SimpleGraph.edgeDensity, Rel.edgeDensity, SimpleGraph.interedges]
      push_cast
      ring
    rwa [hrew]
  -- Apply `hdev` to `(A, B)` (which belongs to `bigA × bigB` since `ε₁ < 1`).
  have hA_big : A ∈ bigA := mem_filter.mpr ⟨mem_powerset.mpr Subset.rfl, by rw [hA]; nlinarith⟩
  have hB_big : B ∈ bigB := mem_filter.mpr ⟨mem_powerset.mpr Subset.rfl, by rw [hB]; nlinarith⟩
  have hbase : |(H.edgeDensity A B : ℝ) - α s| < t_dev := by
    have h1 := hdev A hA_big B hB_big
    have hmul : (G.edgeDensity A B : ℝ) * (α s / d) = α s := by
      change d * (α s / d) = α s
      exact mul_div_cancel₀ (α s) hd_pos.ne'
    rwa [hmul] at h1
  refine ⟨?_, hbase.le.trans (by simp only [t_dev]; linarith)⟩
  -- Verify `H.IsUniform ε₁ A B`.
  intro A' hA' B' hB' hA'_sz hB'_sz
  have hA'_big : A' ∈ bigA := mem_filter.mpr ⟨mem_powerset.mpr hA', by rwa [← hA]⟩
  have hB'_big : B' ∈ bigB := mem_filter.mpr ⟨mem_powerset.mpr hB', by rwa [← hB]⟩
  have h1 := hdev A' hA'_big B' hB'_big
  have hG_unif : |(G.edgeDensity A' B' : ℝ) - d| < ε := by
    refine hunif hA' hB' ?_ ?_
    · calc (A.card : ℝ) * ε ≤ (A.card : ℝ) * ε₁ :=
            mul_le_mul_of_nonneg_left (by simp only [ε]; linarith) (Nat.cast_nonneg _)
        _ ≤ (A'.card : ℝ) := hA'_sz
    · calc (B.card : ℝ) * ε ≤ (B.card : ℝ) * ε₁ :=
            mul_le_mul_of_nonneg_left (by simp only [ε]; linarith) (Nat.cast_nonneg _)
        _ ≤ (B'.card : ℝ) := hB'_sz
  have hαd_nn : 0 ≤ α s / d := div_nonneg (hδ.le.trans (hα_δ s)) hd_pos.le
  have hαd_le1 : α s / d ≤ 1 := (div_le_one hd_pos).mpr (by
    calc α s ≤ ∑ s' : Fin r, α s' :=
          single_le_sum (fun s' _ ↦ hδ.le.trans (hα_δ s')) (mem_univ s)
      _ ≤ d := hα_sum)
  have h2 : |(G.edgeDensity A' B' : ℝ) * (α s / d) - α s| < ε := by
    have heq : (G.edgeDensity A' B' : ℝ) * (α s / d) - α s =
        ((G.edgeDensity A' B' : ℝ) - d) * (α s / d) := by
      have : d * (α s / d) = α s := mul_div_cancel₀ (α s) hd_pos.ne'
      linarith
    rw [heq, abs_mul, abs_of_nonneg hαd_nn]
    calc |(G.edgeDensity A' B' : ℝ) - d| * (α s / d)
        ≤ |(G.edgeDensity A' B' : ℝ) - d| * 1 :=
          mul_le_mul_of_nonneg_left hαd_le1 (abs_nonneg _)
      _ = |(G.edgeDensity A' B' : ℝ) - d| := mul_one _
      _ < ε := hG_unif
  have htri : |(H.edgeDensity A' B' : ℝ) - (H.edgeDensity A B : ℝ)| ≤
      |(H.edgeDensity A' B' : ℝ) - (G.edgeDensity A' B' : ℝ) * (α s / d)| +
      |(G.edgeDensity A' B' : ℝ) * (α s / d) - α s| +
      |(H.edgeDensity A B : ℝ) - α s| := by
    calc |(H.edgeDensity A' B' : ℝ) - (H.edgeDensity A B : ℝ)|
        = |((H.edgeDensity A' B' : ℝ) - (G.edgeDensity A' B' : ℝ) * (α s / d)) +
            ((G.edgeDensity A' B' : ℝ) * (α s / d) - α s) -
            ((H.edgeDensity A B : ℝ) - α s)| := by ring_nf
      _ ≤ |((H.edgeDensity A' B' : ℝ) - (G.edgeDensity A' B' : ℝ) * (α s / d)) +
            ((G.edgeDensity A' B' : ℝ) * (α s / d) - α s)| +
            |(H.edgeDensity A B : ℝ) - α s| := abs_sub _ _
      _ ≤ |(H.edgeDensity A' B' : ℝ) - (G.edgeDensity A' B' : ℝ) * (α s / d)| +
            |(G.edgeDensity A' B' : ℝ) * (α s / d) - α s| +
            |(H.edgeDensity A B : ℝ) - α s| := add_le_add (abs_add_le _ _) le_rfl
  have hsum : t_dev + ε + t_dev < ε₁ := by simp only [t_dev, ε]; linarith
  linarith

end OMA.Erdos81_erdos_81_R1_H2_R1_H1

-- Credit: @preternatural-tocsin

namespace OMA.Erdos81_erdos_81_R1_H2_R1_H2

open SimpleGraph Finset

/- ### Section 1: Elementary Inequalities & Finite Bernoulli Product Identities -/

lemma one_sub_mul_le_pow {p : ℝ} (_hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    1 - (k : ℝ) * p ≤ (1 - p) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.cast_succ]
    have h1 : (1 - (k : ℝ) * p) * (1 - p) ≤ (1 - p) ^ k * (1 - p) :=
      mul_le_mul_of_nonneg_right ih (by linarith)
    nlinarith [mul_nonneg (Nat.cast_nonneg k) (sq_nonneg p)]

lemma pow_mul_one_add_le_one {ε : ℝ} (_hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (T : ℕ) :
    (1 - ε) ^ T * (1 + (T : ℝ) * ε) ≤ 1 := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [pow_succ, Nat.cast_succ]
    have h1 : (1 - ε) * (1 + ((T : ℝ) + 1) * ε) ≤ 1 + (T : ℝ) * ε := by
      nlinarith [mul_nonneg (Nat.cast_nonneg T) (sq_nonneg ε), sq_nonneg ε]
    have h2 : (1 - ε) ^ T * ((1 - ε) * (1 + ((T : ℝ) + 1) * ε)) ≤
        (1 - ε) ^ T * (1 + (T : ℝ) * ε) :=
      mul_le_mul_of_nonneg_left h1 (pow_nonneg (by linarith) T)
    linarith

lemma exp_le_one_add_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤ 1 + 2 * x := by
  have hx : |x| ≤ 1 := by rwa [abs_of_nonneg hx0]
  have h := Real.exp_bound hx (n := 2) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one, Nat.factorial_one,
    Nat.succ_eq_add_one, Nat.factorial_two, Nat.cast_ofNat] at h
  push_cast at h
  have h1 : Real.exp x - (1 + x) ≤ |x| ^ 2 * ((3 : ℝ) / (2 * 2)) := (abs_le.mp h).2
  rw [sq_abs] at h1
  nlinarith

lemma inv_one_sub_pow_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) (k : ℕ)
    (hk : 2 * (k : ℝ) * p ≤ 1) :
    ((1 - p) ^ k)⁻¹ ≤ 1 + 4 * (k : ℝ) * p := by
  have h1p : 0 < 1 - p := by linarith
  have hinv : (1 - p)⁻¹ ≤ Real.exp (2 * p) := by
    have h1 : (1 - p)⁻¹ ≤ 1 + 2 * p := by
      rw [inv_le_iff_one_le_mul₀ h1p]
      nlinarith
    exact h1.trans (by linarith [Real.add_one_le_exp (2 * p)])
  calc ((1 - p) ^ k)⁻¹ = ((1 - p)⁻¹) ^ k := (inv_pow (1 - p) k).symm
    _ ≤ (Real.exp (2 * p)) ^ k := pow_le_pow_left₀ (inv_nonneg.mpr h1p.le) hinv k
    _ = Real.exp ((k : ℝ) * (2 * p)) := by rw [← Real.exp_nat_mul]
    _ = Real.exp (2 * (k : ℝ) * p) := by congr 1; ring
    _ ≤ 1 + 2 * (2 * (k : ℝ) * p) := exp_le_one_add_two_mul (by positivity) hk
    _ = 1 + 4 * (k : ℝ) * p := by ring

lemma abs_pow_sub_pow_le {a b : ℝ} (ha0 : 0 ≤ a) (ha2 : a ≤ 2) (hb0 : 0 ≤ b) (hb2 : b ≤ 2)
    (k : ℕ) : |a ^ k - b ^ k| ≤ (k : ℝ) * (2 : ℝ) ^ k * |a - b| := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, pow_succ, Nat.cast_succ]
    have hsplit : a ^ k * a - b ^ k * b = (a ^ k - b ^ k) * a + b ^ k * (a - b) := by ring
    rw [hsplit]
    have hbk : b ^ k ≤ (2 : ℝ) ^ k := pow_le_pow_left₀ hb0 hb2 k
    calc |(a ^ k - b ^ k) * a + b ^ k * (a - b)|
        ≤ |(a ^ k - b ^ k) * a| + |b ^ k * (a - b)| := abs_add_le _ _
      _ = |a ^ k - b ^ k| * a + b ^ k * |a - b| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_nonneg (pow_nonneg hb0 k)]
      _ ≤ ((k : ℝ) * (2 : ℝ) ^ k * |a - b|) * 2 + (2 : ℝ) ^ k * |a - b| :=
          add_le_add (mul_le_mul ih ha2 ha0 (by positivity))
            (mul_le_mul_of_nonneg_right hbk (abs_nonneg _))
      _ ≤ ((k : ℝ) + 1) * ((2 : ℝ) ^ k * 2) * |a - b| := by
          nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k, abs_nonneg (a - b)]

lemma bern_sum_one {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℝ) :
    ∑ ω : ι → Bool, (∏ e : ι, if ω e then p else 1 - p) = 1 := by
  rw [← Fintype.prod_sum (fun (_ : ι) (b : Bool) ↦ if b then p else 1 - p)]
  simp

lemma bern_sum_all_false {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℝ) (A : Finset ι) :
    ∑ ω ∈ (Finset.univ : Finset (ι → Bool)).filter (fun ω ↦ ∀ e ∈ A, ω e = false),
      (∏ e : ι, if ω e then p else 1 - p) = (1 - p) ^ A.card := by
  let g : ι → Bool → ℝ := fun e b ↦ if e ∈ A then (if b = false then 1 else 0) else 1
  have hrew : ∀ ω : ι → Bool,
      (if (∀ e ∈ A, ω e = false) then (∏ e : ι, if ω e then p else 1 - p) else 0) =
        ∏ e : ι, ((if ω e then p else 1 - p) * g e (ω e)) := by
    intro ω
    rw [Finset.prod_mul_distrib]
    by_cases h : ∀ e ∈ A, ω e = false
    · rw [if_pos h]
      have hg : ∏ e : ι, g e (ω e) = 1 := Finset.prod_eq_one fun e _ ↦ by
        simp only [g]; split_ifs with he hb
        · rfl
        · exact absurd (h e he) hb
        · rfl
      rw [hg, mul_one]
    · rw [if_neg h]
      push Not at h
      obtain ⟨e₀, he₀A, he₀⟩ := h
      have hg : ∏ e : ι, g e (ω e) = 0 :=
        Finset.prod_eq_zero (mem_univ e₀) (by simp [g, he₀A, he₀])
      rw [hg, mul_zero]
  rw [Finset.sum_filter]
  simp_rw [hrew]
  rw [← Fintype.prod_sum (fun e b ↦ (if b then p else 1 - p) * g e b)]
  have hterm : ∀ e : ι, ∑ b : Bool, (if b then p else 1 - p) * g e b =
      if e ∈ A then 1 - p else 1 := by
    intro e
    by_cases he : e ∈ A <;> simp [g, he]
  simp_rw [hterm]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  congr 2
  ext e; simp

lemma bern_sum_one_true_rest_false {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ) (e₀ : ι) (A : Finset ι) (he₀ : e₀ ∉ A) :
    ∑ ω ∈ (Finset.univ : Finset (ι → Bool)).filter
        (fun ω ↦ ω e₀ = true ∧ ∀ e ∈ A, ω e = false),
      (∏ e : ι, if ω e then p else 1 - p) = p * (1 - p) ^ A.card := by
  let g : ι → Bool → ℝ := fun e b ↦
    if e = e₀ then (if b = true then 1 else 0)
    else if e ∈ A then (if b = false then 1 else 0) else 1
  have hrew : ∀ ω : ι → Bool,
      (if (ω e₀ = true ∧ ∀ e ∈ A, ω e = false) then (∏ e : ι, if ω e then p else 1 - p) else 0) =
        ∏ e : ι, ((if ω e then p else 1 - p) * g e (ω e)) := by
    intro ω
    rw [Finset.prod_mul_distrib]
    by_cases h : ω e₀ = true ∧ ∀ e ∈ A, ω e = false
    · rw [if_pos h]
      have hg : ∏ e : ι, g e (ω e) = 1 := Finset.prod_eq_one fun e _ ↦ by
        simp only [g]; split_ifs with h1 h2 h3 h4
        · rfl
        · subst h1; exact absurd h.1 h2
        · rfl
        · exact absurd (h.2 e h3) h4
        · rfl
      rw [hg, mul_one]
    · rw [if_neg h]
      by_cases h0 : ω e₀ = true
      · have hnot : ¬(∀ e ∈ A, ω e = false) := fun ha ↦ h ⟨h0, ha⟩
        push Not at hnot
        obtain ⟨e₁, he₁A, he₁⟩ := hnot
        have hne : e₁ ≠ e₀ := fun heq ↦ he₀ (heq ▸ he₁A)
        have hg : ∏ e : ι, g e (ω e) = 0 :=
          Finset.prod_eq_zero (mem_univ e₁) (by simp [g, hne, he₁A, he₁])
        rw [hg, mul_zero]
      · have hg : ∏ e : ι, g e (ω e) = 0 :=
          Finset.prod_eq_zero (mem_univ e₀) (by simp [g, h0])
        rw [hg, mul_zero]
  rw [Finset.sum_filter]
  simp_rw [hrew]
  rw [← Fintype.prod_sum (fun e b ↦ (if b then p else 1 - p) * g e b)]
  have hterm : ∀ e : ι, ∑ b : Bool, (if b then p else 1 - p) * g e b =
      if e = e₀ then p else if e ∈ A then 1 - p else 1 := by
    intro e
    by_cases h1 : e = e₀
    · simp [g, h1]
    · by_cases h2 : e ∈ A <;> simp [g, h1, h2]
  simp_rw [hterm]
  rw [← Finset.mul_prod_erase Finset.univ _ (mem_univ e₀), if_pos rfl]
  congr 1
  have hrest : ∀ e ∈ Finset.univ.erase e₀,
      (if e = e₀ then p else if e ∈ A then 1 - p else 1) = if e ∈ A then 1 - p else 1 := by
    intro e he; rw [if_neg (mem_erase.mp he).1]
  rw [Finset.prod_congr rfl hrest, Finset.prod_ite, Finset.prod_const_one, mul_one,
    Finset.prod_const]
  congr 2
  ext e
  simp only [mem_filter, mem_erase, mem_univ, and_true]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨fun heq ↦ he₀ (heq ▸ h), h⟩⟩

/- ### Section 2: Prime-Field Affine-Line Hypergraph Regularization -/

lemma regularize_hypergraph {α : Type*} [DecidableEq α]
    (U : Finset α) (ℰ : Finset (Finset α)) (r D Δ₂ : ℕ)
    (hr : 2 ≤ r) (_hD : 1 ≤ D)
    (hunif : ∀ e ∈ ℰ, e ⊆ U ∧ e.card = r)
    (hdeg : ∀ x ∈ U, (ℰ.filter (fun e ↦ x ∈ e)).card ≤ D)
    (hcodeg : ∀ x ∈ U, ∀ y ∈ U, x ≠ y → (ℰ.filter (fun e ↦ x ∈ e ∧ y ∈ e)).card ≤ Δ₂) :
    ∃ (p_prime : ℕ) (_ : Fact p_prime.Prime),
      let W : Finset (Fin r × ZMod p_prime) := Finset.univ
      ∃ (ℰ_orig ℰ_reg : Finset (Finset ((Fin r × ZMod p_prime) × α))),
        ℰ_orig ⊆ ℰ_reg ∧
        (∀ e ∈ ℰ_reg, e ⊆ W ×ˢ U ∧ e.card = r) ∧
        (∀ v ∈ W ×ˢ U, (ℰ_reg.filter (fun e ↦ v ∈ e)).card = D) ∧
        (∀ v₁ ∈ W ×ˢ U, ∀ v₂ ∈ W ×ˢ U, v₁ ≠ v₂ →
          (ℰ_reg.filter (fun e ↦ v₁ ∈ e ∧ v₂ ∈ e)).card ≤ max Δ₂ 1) ∧
        ℰ_orig.card = W.card * ℰ.card ∧
        (∀ ℳ : Finset (Finset ((Fin r × ZMod p_prime) × α)),
          ℳ ⊆ ℰ_orig →
          (∀ e₁ ∈ ℳ, ∀ e₂ ∈ ℳ, e₁ ≠ e₂ → Disjoint e₁ e₂) →
          ∃ ℳ_orig : Finset (Finset α), ℳ_orig ⊆ ℰ ∧
            (∀ e₁ ∈ ℳ_orig, ∀ e₂ ∈ ℳ_orig, e₁ ≠ e₂ → Disjoint e₁ e₂) ∧
            (ℳ.card : ℝ) ≤ (W.card : ℝ) * (ℳ_orig.card : ℝ)) := by
  classical
  obtain ⟨p_prime, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes (max D r)
  have : Fact p_prime.Prime := ⟨hp_prime⟩
  have hp_D : D ≤ p_prime := le_trans (le_max_left _ _) hp_ge
  have hp_r : r ≤ p_prime := le_trans (le_max_right _ _) hp_ge
  let W : Finset (Fin r × ZMod p_prime) := Finset.univ
  -- Original edges lifted to each copy `w ∈ W`.
  let liftOrig : (Fin r × ZMod p_prime) → Finset α → Finset ((Fin r × ZMod p_prime) × α) :=
    fun w e ↦ e.image (fun x ↦ (w, x))
  let ℰ_orig : Finset (Finset ((Fin r × ZMod p_prime) × α)) :=
    (W ×ˢ ℰ).image (fun p ↦ liftOrig p.1 p.2)
  -- Padding affine lines on `W × {x}` for slopes `a < D - deg(x)`.
  let lineOf : ZMod p_prime → ZMod p_prime → α → Finset ((Fin r × ZMod p_prime) × α) :=
    fun a b x ↦ (Finset.univ : Finset (Fin r)).image (fun i ↦ ((i, a * (i.1 : ZMod p_prime) + b), x))
  let defOf : α → ℕ := fun x ↦ D - (ℰ.filter (fun e ↦ x ∈ e)).card
  let padTriples : Finset (α × Fin p_prime × ZMod p_prime) :=
    (U ×ˢ ((Finset.univ : Finset (Fin p_prime)) ×ˢ (Finset.univ : Finset (ZMod p_prime)))).filter
      (fun t ↦ t.2.1.1 < defOf t.1)
  let ℰ_pad : Finset (Finset ((Fin r × ZMod p_prime) × α)) :=
    padTriples.image (fun t ↦ lineOf (t.2.1.1 : ZMod p_prime) t.2.2 t.1)
  let ℰ_reg : Finset (Finset ((Fin r × ZMod p_prime) × α)) := ℰ_orig ∪ ℰ_pad
  -- Helper: injectivity of `Fin r → ZMod p_prime`.
  have hfin_inj : ∀ i j : Fin r, ((i.1 : ZMod p_prime) = (j.1 : ZMod p_prime)) → i = j := by
    intro i j hij
    have hi : i.1 < p_prime := lt_of_lt_of_le i.2 hp_r
    have hj : j.1 < p_prime := lt_of_lt_of_le j.2 hp_r
    have hval : i.1 % p_prime = j.1 % p_prime := by
      have := (ZMod.natCast_eq_natCast_iff' i.1 j.1 p_prime).mp hij
      exact this
    rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hval
    exact Fin.ext hval
  -- Helper: `ℰ_orig` and `ℰ_pad` are disjoint (orig has ≥ 2 distinct `x`, pad has constant `x`).
  have hdisj_op : Disjoint ℰ_orig ℰ_pad := by
    rw [Finset.disjoint_left]
    intro E hEo hEp
    obtain ⟨⟨w, e⟩, hwe, rfl⟩ := mem_image.mp hEo
    obtain ⟨⟨x, a, b⟩, _, heq⟩ := mem_image.mp hEp
    have he_card : e.card = r := (hunif e (mem_product.mp hwe).2).2
    obtain ⟨x₁, hx₁, x₂, hx₂, hxne⟩ := Finset.one_lt_card.mp (by omega : 1 < e.card)
    have h1 : (w, x₁) ∈ lineOf (a.1 : ZMod p_prime) b x := heq ▸ mem_image_of_mem _ hx₁
    have h2 : (w, x₂) ∈ lineOf (a.1 : ZMod p_prime) b x := heq ▸ mem_image_of_mem _ hx₂
    obtain ⟨_, _, h1'⟩ := mem_image.mp h1
    obtain ⟨_, _, h2'⟩ := mem_image.mp h2
    have hx1 : x₁ = x := (Prod.mk.inj h1').2.symm
    have hx2 : x₂ = x := (Prod.mk.inj h2').2.symm
    exact hxne (hx1.trans hx2.symm)
  -- Helper: `liftOrig` is injective on `W ×ˢ ℰ`.
  have hlift_inj : Set.InjOn (fun p : (Fin r × ZMod p_prime) × Finset α ↦ liftOrig p.1 p.2)
      ((W ×ˢ ℰ : Finset ((Fin r × ZMod p_prime) × Finset α)) : Set ((Fin r × ZMod p_prime) × Finset α)) := by
    intro ⟨w₁, e₁⟩ h₁ ⟨w₂, e₂⟩ h₂ heq
    dsimp only at heq
    have he₁_mem : e₁ ∈ ℰ := (mem_product.mp (mem_coe.mp h₁)).2
    have he₁_ne : e₁.Nonempty := card_pos.mp (by have := (hunif e₁ he₁_mem).2; omega)
    obtain ⟨x₀, hx₀⟩ := he₁_ne
    have hmem : (w₁, x₀) ∈ liftOrig w₂ e₂ := by
      rw [← heq]; exact mem_image_of_mem _ hx₀
    obtain ⟨_, _, hw⟩ := mem_image.mp hmem
    have hweq : w₁ = w₂ := (Prod.mk.inj hw).1.symm
    subst hweq
    have heeq : e₁ = e₂ := by
      ext x
      constructor
      · intro hx
        have h1 : (w₁, x) ∈ liftOrig w₁ e₂ := by rw [← heq]; exact mem_image_of_mem _ hx
        obtain ⟨y, hy, hxy⟩ := mem_image.mp h1
        exact (Prod.mk.inj hxy).2 ▸ hy
      · intro hx
        have h1 : (w₁, x) ∈ liftOrig w₁ e₁ := by rw [heq]; exact mem_image_of_mem _ hx
        obtain ⟨y, hy, hxy⟩ := mem_image.mp h1
        exact (Prod.mk.inj hxy).2 ▸ hy
    exact Prod.ext rfl heeq
  -- Helper: `lineOf` is injective on `padTriples`.
  have hline_inj : ∀ a₁ a₂ : Fin p_prime, ∀ b₁ b₂ : ZMod p_prime, ∀ x₁ x₂ : α,
      lineOf (a₁.1 : ZMod p_prime) b₁ x₁ = lineOf (a₂.1 : ZMod p_prime) b₂ x₂ →
      x₁ = x₂ ∧ a₁ = a₂ ∧ b₁ = b₂ := by
    intro a₁ a₂ b₁ b₂ x₁ x₂ heq
    let i0 : Fin r := ⟨0, by omega⟩
    let i1 : Fin r := ⟨1, by omega⟩
    have h0 : ((i0, (a₁.1 : ZMod p_prime) * (i0.1 : ZMod p_prime) + b₁), x₁) ∈
        lineOf (a₂.1 : ZMod p_prime) b₂ x₂ := heq ▸ mem_image_of_mem _ (mem_univ i0)
    have h1 : ((i1, (a₁.1 : ZMod p_prime) * (i1.1 : ZMod p_prime) + b₁), x₁) ∈
        lineOf (a₂.1 : ZMod p_prime) b₂ x₂ := heq ▸ mem_image_of_mem _ (mem_univ i1)
    obtain ⟨j0, _, hj0⟩ := mem_image.mp h0
    obtain ⟨j1, _, hj1⟩ := mem_image.mp h1
    have hx : x₁ = x₂ := (Prod.mk.inj hj0).2.symm
    have hj0_eq : j0 = i0 := (Prod.mk.inj (Prod.mk.inj hj0).1).1
    have hj1_eq : j1 = i1 := (Prod.mk.inj (Prod.mk.inj hj1).1).1
    have hb_eq : b₁ = b₂ := by
      have hy := (Prod.mk.inj (Prod.mk.inj hj0).1).2
      rw [hj0_eq] at hy
      simpa [i0] using hy.symm
    have ha_zmod : (a₁.1 : ZMod p_prime) = (a₂.1 : ZMod p_prime) := by
      have hy := (Prod.mk.inj (Prod.mk.inj hj1).1).2
      rw [hj1_eq, hb_eq] at hy
      simpa [i1] using hy.symm
    have ha_eq : a₁ = a₂ := by
      have hmod := (ZMod.natCast_eq_natCast_iff' a₁.1 a₂.1 p_prime).mp ha_zmod
      rw [Nat.mod_eq_of_lt a₁.2, Nat.mod_eq_of_lt a₂.2] at hmod
      exact Fin.ext hmod
    exact ⟨hx, ha_eq, hb_eq⟩
  refine ⟨p_prime, ⟨hp_prime⟩, ℰ_orig, ℰ_reg, subset_union_left, ?_, ?_, ?_, ?_, ?_⟩
  · -- Uniformity: every `E ∈ ℰ_reg` has `E ⊆ W ×ˢ U` and `E.card = r`.
    intro E hE
    rcases mem_union.mp hE with hEo | hEp
    · obtain ⟨⟨w, e⟩, hwe, rfl⟩ := mem_image.mp hEo
      have he_sub := (hunif e (mem_product.mp hwe).2).1
      have he_card := (hunif e (mem_product.mp hwe).2).2
      refine ⟨fun p hp ↦ ?_, ?_⟩
      · obtain ⟨x, hx, rfl⟩ := mem_image.mp hp
        exact mem_product.mpr ⟨mem_univ w, he_sub hx⟩
      · rw [Finset.card_image_of_injective _ (fun _ _ h ↦ (Prod.mk.inj h).2), he_card]
    · obtain ⟨⟨x, a, b⟩, ht, rfl⟩ := mem_image.mp hEp
      have hxU : x ∈ U := (mem_product.mp (mem_filter.mp ht).1).1
      refine ⟨fun p hp ↦ ?_, ?_⟩
      · obtain ⟨i, _, rfl⟩ := mem_image.mp hp
        exact mem_product.mpr ⟨mem_univ _, hxU⟩
      · rw [Finset.card_image_of_injective _ (fun _ _ h ↦ (Prod.mk.inj (Prod.mk.inj h).1).1)]
        simp
  · -- Exact `D`-regularity: every `(w, x) ∈ W ×ˢ U` has degree `D` in `ℰ_reg`.
    intro ⟨w, x⟩ hv
    have hxU : x ∈ U := (mem_product.mp hv).2
    have hsplit : (ℰ_reg.filter (fun E ↦ (w, x) ∈ E)).card =
        (ℰ_orig.filter (fun E ↦ (w, x) ∈ E)).card + (ℰ_pad.filter (fun E ↦ (w, x) ∈ E)).card := by
      rw [Finset.filter_union, Finset.card_union_of_disjoint
        (hdisj_op.mono (filter_subset _ _) (filter_subset _ _))]
    rw [hsplit]
    have hdeg_orig : (ℰ_orig.filter (fun E ↦ (w, x) ∈ E)).card =
        (ℰ.filter (fun e ↦ x ∈ e)).card := by
      refine Finset.card_bij (fun E _ ↦ E.image Prod.snd) ?_ ?_ ?_
      · intro E hE
        obtain ⟨hEo, hwx⟩ := mem_filter.mp hE
        obtain ⟨⟨w', e⟩, hwe, rfl⟩ := mem_image.mp hEo
        obtain ⟨x', hx', hwx'⟩ := mem_image.mp hwx
        have hx_eq : x' = x := (Prod.mk.inj hwx').2
        have him : (liftOrig w' e).image Prod.snd = e := by
          ext y; simp [liftOrig]
        rw [him]
        exact mem_filter.mpr ⟨(mem_product.mp hwe).2, hx_eq ▸ hx'⟩
      · intro E₁ hE₁ E₂ hE₂ heq
        obtain ⟨hEo₁, hwx₁⟩ := mem_filter.mp hE₁
        obtain ⟨hEo₂, hwx₂⟩ := mem_filter.mp hE₂
        obtain ⟨⟨w₁, e₁⟩, _, rfl⟩ := mem_image.mp hEo₁
        obtain ⟨⟨w₂, e₂⟩, _, rfl⟩ := mem_image.mp hEo₂
        obtain ⟨_, _, h1⟩ := mem_image.mp hwx₁
        obtain ⟨_, _, h2⟩ := mem_image.mp hwx₂
        have hw1 : w₁ = w := (Prod.mk.inj h1).1
        have hw2 : w₂ = w := (Prod.mk.inj h2).1
        have him1 : (liftOrig w₁ e₁).image Prod.snd = e₁ := by ext y; simp [liftOrig]
        have him2 : (liftOrig w₂ e₂).image Prod.snd = e₂ := by ext y; simp [liftOrig]
        rw [him1, him2] at heq
        rw [hw1, hw2, heq]
      · intro e he
        obtain ⟨heℰ, hxe⟩ := mem_filter.mp he
        refine ⟨liftOrig w e, mem_filter.mpr
          ⟨mem_image.mpr ⟨(w, e), mem_product.mpr ⟨mem_univ w, heℰ⟩, rfl⟩,
            mem_image_of_mem _ hxe⟩, ?_⟩
        ext y; simp [liftOrig]
    have hdeg_pad : (ℰ_pad.filter (fun E ↦ (w, x) ∈ E)).card = defOf x := by
      have hdef_le : defOf x ≤ p_prime := (Nat.sub_le D _).trans hp_D
      have hcard_fin : (Finset.univ.filter (fun a : Fin p_prime ↦ a.1 < defOf x)).card = defOf x := by
        have hbij : (Finset.univ.filter (fun a : Fin p_prime ↦ a.1 < defOf x)).card =
            (Finset.range (defOf x)).card := by
          refine Finset.card_bij (fun a _ ↦ a.1) ?_ ?_ ?_
          · intro a ha; exact mem_range.mpr (mem_filter.mp ha).2
          · intro a₁ _ a₂ _ h; exact Fin.ext h
          · intro k hk; exact ⟨⟨k, lt_of_lt_of_le (mem_range.mp hk) hdef_le⟩,
              mem_filter.mpr ⟨mem_univ _, mem_range.mp hk⟩, rfl⟩
        rw [hbij, card_range]
      rw [← hcard_fin]
      symm
      refine Finset.card_bij
        (fun a _ ↦ lineOf (a.1 : ZMod p_prime) (w.2 - (a.1 : ZMod p_prime) * (w.1.1 : ZMod p_prime)) x)
        ?_ ?_ ?_
      · intro a ha
        refine mem_filter.mpr ⟨mem_image.mpr ⟨(x, a, w.2 - (a.1 : ZMod p_prime) * (w.1.1 : ZMod p_prime)),
          mem_filter.mpr ⟨mem_product.mpr ⟨hxU, mem_product.mpr ⟨mem_univ _, mem_univ _⟩⟩,
            (mem_filter.mp ha).2⟩, rfl⟩, ?_⟩
        exact mem_image.mpr ⟨w.1, mem_univ w.1, by ext <;> simp⟩
      · intro a₁ _ a₂ _ heq
        exact (hline_inj a₁ a₂ _ _ x x heq).2.1
      · intro E hE
        obtain ⟨hEp, hwx⟩ := mem_filter.mp hE
        obtain ⟨⟨x', a, b⟩, ht, rfl⟩ := mem_image.mp hEp
        obtain ⟨i, _, hi_eq⟩ := mem_image.mp hwx
        have hx_eq : x' = x := (Prod.mk.inj hi_eq).2
        have hi_w1 : i = w.1 := (Prod.mk.inj (Prod.mk.inj hi_eq).1).1
        have hy_w2 : (a.1 : ZMod p_prime) * (i.1 : ZMod p_prime) + b = w.2 :=
          (Prod.mk.inj (Prod.mk.inj hi_eq).1).2
        have hb_eq : b = w.2 - (a.1 : ZMod p_prime) * (w.1.1 : ZMod p_prime) := by
          rw [hi_w1] at hy_w2; exact eq_sub_of_add_eq' hy_w2
        subst hx_eq
        refine ⟨a, mem_filter.mpr ⟨mem_univ a, (mem_filter.mp ht).2⟩, by rw [hb_eq]⟩
    rw [hdeg_orig, hdeg_pad]
    have hle := hdeg x hxU
    simp only [defOf]
    omega
  · -- Codegree bound: `codeg ≤ max Δ₂ 1`.
    intro ⟨w₁, x₁⟩ hv₁ ⟨w₂, x₂⟩ hv₂ hne
    have hx₁U : x₁ ∈ U := (mem_product.mp hv₁).2
    have hx₂U : x₂ ∈ U := (mem_product.mp hv₂).2
    have hsplit : (ℰ_reg.filter (fun E ↦ (w₁, x₁) ∈ E ∧ (w₂, x₂) ∈ E)).card =
        (ℰ_orig.filter (fun E ↦ (w₁, x₁) ∈ E ∧ (w₂, x₂) ∈ E)).card +
        (ℰ_pad.filter (fun E ↦ (w₁, x₁) ∈ E ∧ (w₂, x₂) ∈ E)).card := by
      rw [Finset.filter_union, Finset.card_union_of_disjoint
        (hdisj_op.mono (filter_subset _ _) (filter_subset _ _))]
    rw [hsplit]
    by_cases hw : w₁ = w₂
    · subst hw
      have hxne : x₁ ≠ x₂ := fun h ↦ hne (Prod.ext rfl h)
      have hpad0 : (ℰ_pad.filter (fun E ↦ (w₁, x₁) ∈ E ∧ (w₁, x₂) ∈ E)).card = 0 := by
        rw [card_eq_zero, eq_empty_iff_forall_notMem]
        intro E hE
        obtain ⟨hEp, h1, h2⟩ := mem_filter.mp hE
        obtain ⟨⟨x, a, b⟩, _, rfl⟩ := mem_image.mp hEp
        obtain ⟨_, _, h1'⟩ := mem_image.mp h1
        obtain ⟨_, _, h2'⟩ := mem_image.mp h2
        exact hxne ((Prod.mk.inj h1').2.symm.trans (Prod.mk.inj h2').2)
      have horig_le : (ℰ_orig.filter (fun E ↦ (w₁, x₁) ∈ E ∧ (w₁, x₂) ∈ E)).card ≤ Δ₂ := by
        refine (Finset.card_le_card_of_injOn (fun E ↦ E.image Prod.snd) ?_ ?_).trans
          (hcodeg x₁ hx₁U x₂ hx₂U hxne)
        · intro E hE
          obtain ⟨hEo, h1, h2⟩ := mem_filter.mp (mem_coe.mp hE)
          obtain ⟨⟨w', e⟩, hwe, rfl⟩ := mem_image.mp hEo
          obtain ⟨y₁, hy₁, h1'⟩ := mem_image.mp h1
          obtain ⟨y₂, hy₂, h2'⟩ := mem_image.mp h2
          have him : (liftOrig w' e).image Prod.snd = e := by ext y; simp [liftOrig]
          dsimp only
          rw [mem_coe, him]
          exact mem_filter.mpr ⟨(mem_product.mp hwe).2,
            (Prod.mk.inj h1').2 ▸ hy₁, (Prod.mk.inj h2').2 ▸ hy₂⟩
        · intro E₁ hE₁ E₂ hE₂ heq
          obtain ⟨hEo₁, h1₁, _⟩ := mem_filter.mp (mem_coe.mp hE₁)
          obtain ⟨hEo₂, h1₂, _⟩ := mem_filter.mp (mem_coe.mp hE₂)
          obtain ⟨⟨w₁', e₁⟩, _, rfl⟩ := mem_image.mp hEo₁
          obtain ⟨⟨w₂', e₂⟩, _, rfl⟩ := mem_image.mp hEo₂
          obtain ⟨_, _, hw1'⟩ := mem_image.mp h1₁
          obtain ⟨_, _, hw2'⟩ := mem_image.mp h1₂
          have him1 : (liftOrig w₁' e₁).image Prod.snd = e₁ := by ext y; simp [liftOrig]
          have him2 : (liftOrig w₂' e₂).image Prod.snd = e₂ := by ext y; simp [liftOrig]
          dsimp only at heq
          rw [him1, him2] at heq
          rw [(Prod.mk.inj hw1').1, (Prod.mk.inj hw2').1, heq]
      rw [hpad0, add_zero]
      exact horig_le.trans (le_max_left _ _)
    · -- `w₁ ≠ w₂`: no original edge contains both; at most 1 padding line contains both.
      have horig0 : (ℰ_orig.filter (fun E ↦ (w₁, x₁) ∈ E ∧ (w₂, x₂) ∈ E)).card = 0 := by
        rw [card_eq_zero, eq_empty_iff_forall_notMem]
        intro E hE
        obtain ⟨hEo, h1, h2⟩ := mem_filter.mp hE
        obtain ⟨⟨w', e⟩, _, rfl⟩ := mem_image.mp hEo
        obtain ⟨_, _, h1'⟩ := mem_image.mp h1
        obtain ⟨_, _, h2'⟩ := mem_image.mp h2
        exact hw ((Prod.mk.inj h1').1.symm.trans (Prod.mk.inj h2').1)
      have hpad_le1 : (ℰ_pad.filter (fun E ↦ (w₁, x₁) ∈ E ∧ (w₂, x₂) ∈ E)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro E₁ hE₁ E₂ hE₂
        obtain ⟨hEp₁, h1₁, h2₁⟩ := mem_filter.mp hE₁
        obtain ⟨hEp₂, h1₂, h2₂⟩ := mem_filter.mp hE₂
        obtain ⟨⟨x, a₁, b₁⟩, _, rfl⟩ := mem_image.mp hEp₁
        obtain ⟨⟨x', a₂, b₂⟩, _, rfl⟩ := mem_image.mp hEp₂
        obtain ⟨i₁, _, hi₁⟩ := mem_image.mp h1₁
        obtain ⟨j₁, _, hj₁⟩ := mem_image.mp h2₁
        obtain ⟨i₂, _, hi₂⟩ := mem_image.mp h1₂
        obtain ⟨j₂, _, hj₂⟩ := mem_image.mp h2₂
        have hx_eq : x = x' := (Prod.mk.inj hi₁).2.trans (Prod.mk.inj hi₂).2.symm
        have hi1 : i₁ = w₁.1 := (Prod.mk.inj (Prod.mk.inj hi₁).1).1
        have hj1 : j₁ = w₂.1 := (Prod.mk.inj (Prod.mk.inj hj₁).1).1
        have hi2 : i₂ = w₁.1 := (Prod.mk.inj (Prod.mk.inj hi₂).1).1
        have hj2 : j₂ = w₂.1 := (Prod.mk.inj (Prod.mk.inj hj₂).1).1
        have hy1_1 : (a₁.1 : ZMod p_prime) * (w₁.1.1 : ZMod p_prime) + b₁ = w₁.2 :=
          hi1 ▸ (Prod.mk.inj (Prod.mk.inj hi₁).1).2
        have hy2_1 : (a₁.1 : ZMod p_prime) * (w₂.1.1 : ZMod p_prime) + b₁ = w₂.2 :=
          hj1 ▸ (Prod.mk.inj (Prod.mk.inj hj₁).1).2
        have hy1_2 : (a₂.1 : ZMod p_prime) * (w₁.1.1 : ZMod p_prime) + b₂ = w₁.2 :=
          hi2 ▸ (Prod.mk.inj (Prod.mk.inj hi₂).1).2
        have hy2_2 : (a₂.1 : ZMod p_prime) * (w₂.1.1 : ZMod p_prime) + b₂ = w₂.2 :=
          hj2 ▸ (Prod.mk.inj (Prod.mk.inj hj₂).1).2
        have hw12_ne : w₁.1 ≠ w₂.1 := by
          intro hsame
          have : w₁.2 = w₂.2 := by rw [← hy1_1, ← hy2_1, hsame]
          exact hw (Prod.ext hsame this)
        have hdiff_ne : (w₁.1.1 : ZMod p_prime) - (w₂.1.1 : ZMod p_prime) ≠ 0 := by
          intro h0
          exact hw12_ne (hfin_inj w₁.1 w₂.1 (sub_eq_zero.mp h0))
        have ha_eq : (a₁.1 : ZMod p_prime) = (a₂.1 : ZMod p_prime) := by
          have hsub : ((a₁.1 : ZMod p_prime) - (a₂.1 : ZMod p_prime)) *
              ((w₁.1.1 : ZMod p_prime) - (w₂.1.1 : ZMod p_prime)) = 0 := by
            linear_combination (hy1_1 - hy2_1) - (hy1_2 - hy2_2)
          exact sub_eq_zero.mp ((mul_eq_zero.mp hsub).resolve_right hdiff_ne)
        have hb_eq : b₁ = b₂ := by
          linear_combination hy1_1 - hy1_2 - (w₁.1.1 : ZMod p_prime) * ha_eq
        rw [hx_eq, ha_eq, hb_eq]
      rw [horig0, zero_add]
      exact hpad_le1.trans (le_max_right _ _)
  · -- `ℰ_orig.card = W.card * ℰ.card`.
    rw [Finset.card_image_of_injOn hlift_inj, Finset.card_product]
  · -- Pigeonhole extraction of a matching in `ℰ` from a matching `ℳ ⊆ ℰ_orig`.
    intro ℳ hℳ_sub hℳ_disj
    let slice : (Fin r × ZMod p_prime) → Finset (Finset α) := fun w ↦
      ℰ.filter (fun e ↦ liftOrig w e ∈ ℳ)
    have hsum_slice : ∑ w ∈ W, (slice w).card = ℳ.card := by
      have hbi : ℳ = W.biUnion (fun w ↦ (slice w).image (liftOrig w)) := by
        ext E
        simp only [mem_biUnion, mem_image, slice, mem_filter]
        constructor
        · intro hE
          obtain ⟨⟨w, e⟩, hwe, rfl⟩ := mem_image.mp (hℳ_sub hE)
          exact ⟨w, mem_univ w, e, ⟨(mem_product.mp hwe).2, hE⟩, rfl⟩
        · rintro ⟨w, _, e, ⟨_, hE⟩, rfl⟩; exact hE
      conv_rhs => rw [hbi]
      rw [Finset.card_biUnion]
      · refine sum_congr rfl fun w _ ↦ ?_
        rw [Finset.card_image_of_injOn]
        intro e₁ he₁ e₂ he₂ heq
        have h1 := hlift_inj
          (x₁ := (w, e₁)) (mem_coe.mpr (mem_product.mpr ⟨mem_univ w, (mem_filter.mp (mem_coe.mp he₁)).1⟩))
          (x₂ := (w, e₂)) (mem_coe.mpr (mem_product.mpr ⟨mem_univ w, (mem_filter.mp (mem_coe.mp he₂)).1⟩))
          heq
        exact (Prod.mk.inj h1).2
      · intro w₁ _ w₂ _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro E h1 h2
        obtain ⟨e₁, he₁, rfl⟩ := mem_image.mp h1
        obtain ⟨e₂, he₂, heq⟩ := mem_image.mp h2
        have hpair := hlift_inj
          (x₁ := (w₂, e₂)) (mem_coe.mpr (mem_product.mpr ⟨mem_univ w₂, (mem_filter.mp he₂).1⟩))
          (x₂ := (w₁, e₁)) (mem_coe.mpr (mem_product.mpr ⟨mem_univ w₁, (mem_filter.mp he₁).1⟩))
          heq
        exact hne (Prod.mk.inj hpair).1.symm
    have hW_ne : W.Nonempty := ⟨(⟨0, by omega⟩, 0), mem_univ _⟩
    obtain ⟨w₀, _, hw₀_max⟩ := Finset.exists_max_image W (fun w ↦ (slice w).card) hW_ne
    refine ⟨slice w₀, filter_subset _ _, ?_, ?_⟩
    · intro e₁ he₁ e₂ he₂ hne
      have h1 : liftOrig w₀ e₁ ∈ ℳ := (mem_filter.mp he₁).2
      have h2 : liftOrig w₀ e₂ ∈ ℳ := (mem_filter.mp he₂).2
      have hne' : liftOrig w₀ e₁ ≠ liftOrig w₀ e₂ := fun heq ↦
        hne (Prod.mk.inj (hlift_inj
          (x₁ := (w₀, e₁)) (mem_coe.mpr (mem_product.mpr ⟨mem_univ w₀, (mem_filter.mp he₁).1⟩))
          (x₂ := (w₀, e₂)) (mem_coe.mpr (mem_product.mpr ⟨mem_univ w₀, (mem_filter.mp he₂).1⟩))
          heq)).2
      have hd := hℳ_disj _ h1 _ h2 hne'
      rw [Finset.disjoint_left] at hd ⊢
      intro x hx₁ hx₂
      exact hd (mem_image_of_mem _ hx₁) (mem_image_of_mem _ hx₂)
    · have hle : ℳ.card ≤ W.card * (slice w₀).card := by
        calc ℳ.card = ∑ w ∈ W, (slice w).card := hsum_slice.symm
          _ ≤ ∑ _w ∈ W, (slice w₀).card := sum_le_sum fun w hw ↦ hw₀_max w hw
          _ = W.card * (slice w₀).card := by simp
      exact_mod_cast hle

/- ### Section 3: One-Step Nibble & `T`-Round Frankl--Rödl / Pippenger Matching Theorem -/

set_option maxHeartbeats 1200000 in
lemma nibble_one_step {α : Type*} [DecidableEq α]
    (U : Finset α) (ℰ_orig ℰ_reg : Finset (Finset α)) (r D Δ₂ : ℕ)
    (ε η₁ c_next : ℝ)
    (hr : 2 ≤ r) (hD : 1 ≤ D)
    (hε0 : 0 < ε) (hε_small : 4 * (r : ℝ) * ε ≤ 1)
    (hη₁0 : 0 < η₁) (hη₁_le : η₁ ≤ 1 / 4)
    (hc_nn : 0 ≤ c_next)
    (hβ_small : 4 * (r : ℝ) ^ 2 * ((Δ₂ : ℝ) / (D : ℝ)) ≤ η₁)
    (hβ_cheb : 32 * ((r : ℝ) + (r : ℝ) ^ 2) * ((Δ₂ : ℝ) / (D : ℝ)) * (r : ℝ) ≤ η₁ ^ 3)
    (hD_η : 2 ≤ η₁ * (D : ℝ))
    (hsub : ℰ_orig ⊆ ℰ_reg)
    (hunif : ∀ e ∈ ℰ_reg, e ⊆ U ∧ e.card = r)
    (hreg : ∀ v ∈ U, (ℰ_reg.filter (fun e ↦ v ∈ e)).card = D)
    (hcodeg : ∀ v₁ ∈ U, ∀ v₂ ∈ U, v₁ ≠ v₂ →
      (ℰ_reg.filter (fun e ↦ v₁ ∈ e ∧ v₂ ∈ e)).card ≤ Δ₂) :
    let p : ℝ := ε / (D : ℝ)
    let D' : ℕ := Nat.ceil ((1 + η₁) * (1 - p) ^ ((r - 1) * D) * (D : ℝ))
    ∃ (ℳ₁ ℰ_rem : Finset (Finset α)),
      ℳ₁ ⊆ ℰ_orig ∧ ℰ_rem ⊆ ℰ_orig ∧
      (∀ e₁ ∈ ℳ₁, ∀ e₂ ∈ ℳ₁, e₁ ≠ e₂ → Disjoint e₁ e₂) ∧
      (∀ e₁ ∈ ℳ₁, ∀ e₂ ∈ ℰ_rem, Disjoint e₁ e₂) ∧
      (∀ v ∈ U, (ℰ_rem.filter (fun e ↦ v ∈ e)).card ≤ D') ∧
      (D : ℝ) / 2 ≤ (D' : ℝ) ∧
      (ε * (1 - (r : ℝ) * ε) + c_next * (1 - ε - 4 * η₁)) * ((ℰ_orig.card : ℝ) / (D : ℝ)) ≤
        (ℳ₁.card : ℝ) + c_next * ((ℰ_rem.card : ℝ) / (D' : ℝ)) := by
  classical
  have hD_pos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (show 0 < D by omega)
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  let p : ℝ := ε / (D : ℝ)
  have hp0 : 0 ≤ p := by positivity
  have hp_half : p ≤ 1 / 2 := by
    have : ε ≤ (D : ℝ) / 2 := by
      have h1 : 1 ≤ (D : ℝ) := by exact_mod_cast hD
      have h2 : 2 ≤ (r : ℝ) := by exact_mod_cast hr
      nlinarith
    exact (div_le_iff₀ hD_pos).mpr (by linarith)
  have hp1 : p ≤ 1 := hp_half.trans (by norm_num)
  let D_exp : ℝ := (1 - p) ^ ((r - 1) * D) * (D : ℝ)
  let D' : ℕ := Nat.ceil ((1 + η₁) * (1 - p) ^ ((r - 1) * D) * (D : ℝ))
  have hD'_arg : (1 + η₁) * (1 - p) ^ ((r - 1) * D) * (D : ℝ) = (1 + η₁) * D_exp := by
    simp only [D_exp]; ring
  have hpow_r1 : 1 / 2 ≤ (1 - p) ^ ((r - 1) * D) := by
    have h1 := one_sub_mul_le_pow hp0 hp1 ((r - 1) * D)
    have h2 : (((r - 1) * D : ℕ) : ℝ) * p = ((r : ℝ) - 1) * ε := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
      simp only [p]; field_simp
    rw [h2] at h1
    nlinarith
  have hD_exp_ge : (D : ℝ) / 2 ≤ D_exp := by
    simp only [D_exp]; nlinarith
  have hD'_ge : (D : ℝ) / 2 ≤ (D' : ℝ) := by
    have h1 : (1 + η₁) * D_exp ≤ (D' : ℝ) := hD'_arg ▸ Nat.le_ceil _
    nlinarith
  have hD'_pos : (0 : ℝ) < (D' : ℝ) := by linarith
  have hD'_le : (D' : ℝ) ≤ (1 + 2 * η₁) * D_exp := by
    have h1 : (D' : ℝ) < (1 + η₁) * D_exp + 1 := by
      rw [← hD'_arg]; exact Nat.ceil_lt_add_one (by positivity)
    have h2 : 1 ≤ η₁ * D_exp := by nlinarith
    linarith
  -- Probability space `Ω := { e // e ∈ ℰ_reg } → Bool` with Bernoulli(`p`) weight `P ω`.
  let P : ({ e // e ∈ ℰ_reg } → Bool) → ℝ := fun ω ↦ ∏ e : { e // e ∈ ℰ_reg }, if ω e then p else 1 - p
  have hP_nn : ∀ ω, 0 ≤ P ω := fun ω ↦ Finset.prod_nonneg fun _ _ ↦ by split_ifs <;> linarith
  have hP_sum : ∑ ω : { e // e ∈ ℰ_reg } → Bool, P ω = 1 :=
    bern_sum_one (ι := { e // e ∈ ℰ_reg }) p
  -- Helper: neighbor edges of `e` in `ℰ_reg`.
  let N_all : Finset α → Finset { e // e ∈ ℰ_reg } := fun s ↦
    Finset.univ.filter (fun f ↦ (f.1 ∩ s).Nonempty)
  have hN_card_le : ∀ s ⊆ U, (N_all s).card ≤ s.card * D := by
    intro s hs
    have hsubN : (N_all s).image Subtype.val ⊆ s.biUnion (fun v ↦ ℰ_reg.filter (fun f ↦ v ∈ f)) := by
      intro f hf
      obtain ⟨f', hf', rfl⟩ := mem_image.mp hf
      obtain ⟨v, hv⟩ := (mem_filter.mp hf').2
      exact mem_biUnion.mpr ⟨v, (mem_inter.mp hv).2, mem_filter.mpr ⟨f'.2, (mem_inter.mp hv).1⟩⟩
    calc (N_all s).card
        = ((N_all s).image Subtype.val).card :=
          (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ ≤ (s.biUnion (fun v ↦ ℰ_reg.filter (fun f ↦ v ∈ f))).card := card_le_card hsubN
      _ ≤ ∑ v ∈ s, (ℰ_reg.filter (fun f ↦ v ∈ f)).card := card_biUnion_le
      _ = ∑ _v ∈ s, D := sum_congr rfl fun v hv ↦ hreg v (hs hv)
      _ = s.card * D := by simp
  -- Inclusion-exclusion lower bound on `(N_all s).card` for `s ⊆ U`.
  have hN_card_ge : ∀ s ⊆ U, s.card * D ≤ (N_all s).card + s.card * s.card * Δ₂ := by
    intro s hs
    have h1 : s.card * D = ∑ v ∈ s, (ℰ_reg.filter (fun f ↦ v ∈ f)).card := by
      rw [sum_congr rfl fun v hv ↦ hreg v (hs hv)]; simp
    have h2 : ∑ v ∈ s, (ℰ_reg.filter (fun f ↦ v ∈ f)).card =
        ∑ f ∈ N_all s, (f.1 ∩ s).card := by
      have hlhs : ∑ v ∈ s, (ℰ_reg.filter (fun f ↦ v ∈ f)).card =
          ∑ v ∈ s, ∑ f : { e // e ∈ ℰ_reg }, if v ∈ f.1 then 1 else 0 := by
        refine sum_congr rfl fun v _ ↦ ?_
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
        refine Finset.card_bij (fun f _ ↦ ⟨f, (mem_filter.mp ‹_›).1⟩) ?_ ?_ ?_
        · intro f hf; exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hf).2⟩
        · intro _ _ _ _ h; exact congrArg Subtype.val h
        · intro f hf; exact ⟨f.1, mem_filter.mpr ⟨f.2, (mem_filter.mp hf).2⟩, rfl⟩
      rw [hlhs, Finset.sum_comm]
      have hsub2 : ∑ f : { e // e ∈ ℰ_reg }, ∑ v ∈ s, (if v ∈ f.1 then 1 else 0) =
          ∑ f ∈ N_all s, ∑ v ∈ s, (if v ∈ f.1 then 1 else 0) := by
        symm
        refine sum_subset (subset_univ _) fun f _ hf ↦ ?_
        have hemp : f.1 ∩ s = ∅ := by
          rw [← Finset.not_nonempty_iff_eq_empty]
          exact fun hne ↦ hf (mem_filter.mpr ⟨mem_univ f, hne⟩)
        refine sum_eq_zero fun v hv ↦ ?_
        rw [if_neg]
        intro hvf
        have : v ∈ f.1 ∩ s := mem_inter.mpr ⟨hvf, hv⟩
        rw [hemp] at this; exact notMem_empty v this
      rw [hsub2]
      refine sum_congr rfl fun f _ ↦ ?_
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
      congr 1; ext v; simp [and_comm]
    have h3 : ∑ f ∈ N_all s, ((f.1 ∩ s).card * ((f.1 ∩ s).card - 1)) ≤ s.card * s.card * Δ₂ := by
      have hpair : ∑ f ∈ N_all s, ((f.1 ∩ s).card * ((f.1 ∩ s).card - 1)) =
          ∑ p ∈ s.offDiag, (ℰ_reg.filter (fun f ↦ p.1 ∈ f ∧ p.2 ∈ f)).card := by
        have hl : ∀ f ∈ N_all s, (f.1 ∩ s).card * ((f.1 ∩ s).card - 1) =
            ((f.1 ∩ s).offDiag).card := fun f _ ↦ by
          rw [Finset.offDiag_card, Nat.mul_sub_left_distrib, mul_one]
        rw [sum_congr rfl hl]
        calc ∑ f ∈ N_all s, ((f.1 ∩ s).offDiag).card
            = ∑ f ∈ N_all s, ∑ p ∈ s.offDiag, if (p.1 ∈ f.1 ∧ p.2 ∈ f.1) then 1 else 0 := by
              refine sum_congr rfl fun f _ ↦ ?_
              rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
              congr 1; ext ⟨u, v⟩; simp [mem_offDiag]; tauto
          _ = ∑ p ∈ s.offDiag, ∑ f ∈ N_all s, if (p.1 ∈ f.1 ∧ p.2 ∈ f.1) then 1 else 0 :=
              Finset.sum_comm
          _ = ∑ p ∈ s.offDiag, (ℰ_reg.filter (fun f ↦ p.1 ∈ f ∧ p.2 ∈ f)).card := by
              refine sum_congr rfl fun p hp ↦ ?_
              rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
              refine Finset.card_bij (fun f _ ↦ f.1) ?_ ?_ ?_
              · intro f hf; exact mem_filter.mpr ⟨f.2, (mem_filter.mp hf).2⟩
              · intro _ _ _ _ h; exact Subtype.ext h
              · intro f hf
                obtain ⟨hfℰ, h1, h2⟩ := mem_filter.mp hf
                exact ⟨⟨f, hfℰ⟩, mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,
                  ⟨p.1, mem_inter.mpr ⟨h1, (mem_offDiag.mp hp).1⟩⟩⟩, h1, h2⟩, rfl⟩
      rw [hpair]
      calc ∑ p ∈ s.offDiag, (ℰ_reg.filter (fun f ↦ p.1 ∈ f ∧ p.2 ∈ f)).card
          ≤ ∑ _p ∈ s.offDiag, Δ₂ := sum_le_sum fun p hp ↦
            hcodeg p.1 (hs (mem_offDiag.mp hp).1) p.2 (hs (mem_offDiag.mp hp).2.1)
              (mem_offDiag.mp hp).2.2
        _ = s.offDiag.card * Δ₂ := by simp
        _ ≤ s.card * s.card * Δ₂ := by
            rw [Finset.offDiag_card]
            exact Nat.mul_le_mul_right Δ₂ (Nat.sub_le _ _)
    have h4 : ∑ f ∈ N_all s, (f.1 ∩ s).card ≤
        (N_all s).card + ∑ f ∈ N_all s, ((f.1 ∩ s).card * ((f.1 ∩ s).card - 1)) := by
      have : (N_all s).card + ∑ f ∈ N_all s, ((f.1 ∩ s).card * ((f.1 ∩ s).card - 1)) =
          ∑ f ∈ N_all s, (1 + (f.1 ∩ s).card * ((f.1 ∩ s).card - 1)) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
      rw [this]
      refine sum_le_sum fun f _ ↦ ?_
      cases hk : (f.1 ∩ s).card with
      | zero => omega
      | succ m =>
        cases m with
        | zero => simp
        | succ m' =>
          have hsub1 : m' + 1 + 1 - 1 = m' + 1 := by omega
          rw [hsub1]
          have hmul : m' + 1 + 1 ≤ (m' + 1 + 1) * (m' + 1) := Nat.le_mul_of_pos_right _ (by omega)
          omega
    omega
  -- Define random outcomes for each `ω : { e // e ∈ ℰ_reg } → Bool`.
  let ℳ₁_of : ({ e // e ∈ ℰ_reg } → Bool) → Finset (Finset α) := fun ω ↦
    ℰ_orig.filter (fun e ↦ ∃ he : e ∈ ℰ_reg, ω ⟨e, he⟩ = true ∧
      ∀ f ∈ (N_all e).erase ⟨e, he⟩, ω f = false)
  let ℰ'_of : ({ e // e ∈ ℰ_reg } → Bool) → Finset (Finset α) := fun ω ↦
    ℰ_orig.filter (fun e ↦ ∀ f ∈ N_all e, ω f = false)
  let X_of : α → ({ e // e ∈ ℰ_reg } → Bool) → ℕ := fun v ω ↦
    (ℰ_reg.filter (fun e ↦ v ∈ e ∧ ∀ f ∈ N_all (e.erase v), ω f = false)).card
  let B_of : ({ e // e ∈ ℰ_reg } → Bool) → Finset α := fun ω ↦
    U.filter (fun v ↦ D' < X_of v ω)
  let ℰ_rem_of : ({ e // e ∈ ℰ_reg } → Bool) → Finset (Finset α) := fun ω ↦
    (ℰ'_of ω).filter (fun e ↦ Disjoint e (B_of ω))
  -- Expectation of `ℳ₁_of`.
  have hE_M1 : ε * (1 - (r : ℝ) * ε) * ((ℰ_orig.card : ℝ) / (D : ℝ)) ≤
      ∑ ω, P ω * ((ℳ₁_of ω).card : ℝ) := by
    have hsw : ∑ ω, P ω * ((ℳ₁_of ω).card : ℝ) =
        ∑ e ∈ ℰ_orig, ∑ ω ∈ Finset.univ.filter (fun ω ↦
          ∃ he : e ∈ ℰ_reg, ω ⟨e, he⟩ = true ∧ ∀ f ∈ (N_all e).erase ⟨e, he⟩, ω f = false), P ω := by
      have h1 : ∀ ω, P ω * ((ℳ₁_of ω).card : ℝ) =
          ∑ e ∈ ℰ_orig, if (∃ he : e ∈ ℰ_reg, ω ⟨e, he⟩ = true ∧
            ∀ f ∈ (N_all e).erase ⟨e, he⟩, ω f = false) then P ω else 0 := by
        intro ω; rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
      simp_rw [h1]
      rw [Finset.sum_comm]
      refine sum_congr rfl fun e _ ↦ (Finset.sum_filter _ _).symm
    rw [hsw]
    calc ε * (1 - (r : ℝ) * ε) * ((ℰ_orig.card : ℝ) / (D : ℝ))
        = ∑ _e ∈ ℰ_orig, (p * (1 - (r : ℝ) * ε)) := by
          simp only [p, Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ e ∈ ℰ_orig, ∑ ω ∈ Finset.univ.filter (fun ω ↦
            ∃ he : e ∈ ℰ_reg, ω ⟨e, he⟩ = true ∧ ∀ f ∈ (N_all e).erase ⟨e, he⟩, ω f = false),
            P ω := by
          refine sum_le_sum fun e he ↦ ?_
          have he_reg : e ∈ ℰ_reg := hsub he
          have hfilt : Finset.univ.filter (fun ω : { e // e ∈ ℰ_reg } → Bool ↦
              ∃ he' : e ∈ ℰ_reg, ω ⟨e, he'⟩ = true ∧ ∀ f ∈ (N_all e).erase ⟨e, he'⟩, ω f = false) =
              Finset.univ.filter (fun ω : { e // e ∈ ℰ_reg } → Bool ↦
                ω ⟨e, he_reg⟩ = true ∧ ∀ f ∈ (N_all e).erase ⟨e, he_reg⟩, ω f = false) := by
            ext ω; simp [he_reg]
          rw [hfilt]
          have hbern_eq : ∑ ω ∈ Finset.univ.filter (fun ω : { e // e ∈ ℰ_reg } → Bool ↦
                ω ⟨e, he_reg⟩ = true ∧ ∀ f ∈ (N_all e).erase ⟨e, he_reg⟩, ω f = false), P ω =
              p * (1 - p) ^ ((N_all e).erase ⟨e, he_reg⟩).card := by
            convert bern_sum_one_true_rest_false p ⟨e, he_reg⟩ ((N_all e).erase ⟨e, he_reg⟩)
              (notMem_erase _ _) using 1
          rw [hbern_eq]
          have hcard : ((N_all e).erase ⟨e, he_reg⟩).card ≤ r * D :=
            (card_erase_le).trans ((hunif e he_reg).2 ▸ hN_card_le e (hunif e he_reg).1)
          have hpow : (1 - p) ^ (r * D) ≤ (1 - p) ^ ((N_all e).erase ⟨e, he_reg⟩).card :=
            pow_le_pow_of_le_one (by linarith) (by linarith) hcard
          have hbern : 1 - (r : ℝ) * ε ≤ (1 - p) ^ (r * D) := by
            have := one_sub_mul_le_pow hp0 hp1 (r * D)
            have hmul : ((r * D : ℕ) : ℝ) * p = (r : ℝ) * ε := by
              rw [Nat.cast_mul]; simp only [p]; field_simp
            rwa [hmul] at this
          exact mul_le_mul_of_nonneg_left (hbern.trans hpow) hp0
  -- Expectation of `ℰ'_of`.
  have hE_E' : (1 - p) ^ (r * D) * (ℰ_orig.card : ℝ) ≤ ∑ ω, P ω * ((ℰ'_of ω).card : ℝ) := by
    have hsw : ∑ ω, P ω * ((ℰ'_of ω).card : ℝ) =
        ∑ e ∈ ℰ_orig, ∑ ω ∈ Finset.univ.filter (fun ω ↦ ∀ f ∈ N_all e, ω f = false), P ω := by
      have h1 : ∀ ω, P ω * ((ℰ'_of ω).card : ℝ) =
          ∑ e ∈ ℰ_orig, if (∀ f ∈ N_all e, ω f = false) then P ω else 0 := by
        intro ω; rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
      simp_rw [h1]
      rw [Finset.sum_comm]
      refine sum_congr rfl fun e _ ↦ (Finset.sum_filter _ _).symm
    rw [hsw]
    calc (1 - p) ^ (r * D) * (ℰ_orig.card : ℝ)
        = ∑ _e ∈ ℰ_orig, (1 - p) ^ (r * D) := by simp [mul_comm]
      _ ≤ ∑ e ∈ ℰ_orig, ∑ ω ∈ Finset.univ.filter (fun ω ↦ ∀ f ∈ N_all e, ω f = false), P ω := by
          refine sum_le_sum fun e he ↦ ?_
          rw [bern_sum_all_false p (N_all e)]
          have hcard : (N_all e).card ≤ r * D :=
            (hunif e (hsub he)).2 ▸ hN_card_le e (hunif e (hsub he)).1
          exact pow_le_pow_of_le_one (by linarith) (by linarith) hcard
  -- Chebyshev bound on `Pr[D' < X_of v ω]` for every fixed `v ∈ U`.
  have hbad_prob : ∀ v ∈ U,
      ∑ ω ∈ Finset.univ.filter (fun ω ↦ D' < X_of v ω), P ω ≤ η₁ / (r : ℝ) := by
    intro v hv
    let Ev : Finset (Finset α) := ℰ_reg.filter (fun e ↦ v ∈ e)
    have hEv_card : Ev.card = D := hreg v hv
    let μ : ℝ := ∑ ω, P ω * (X_of v ω : ℝ)
    -- Exact formula for `μ = ∑ e ∈ Ev, (1 - p) ^ (N_all (e.erase v)).card`.
    have hμ_eq : μ = ∑ e ∈ Ev, (1 - p) ^ (N_all (e.erase v)).card := by
      have h1 : ∀ ω, P ω * (X_of v ω : ℝ) =
          ∑ e ∈ Ev, if (∀ f ∈ N_all (e.erase v), ω f = false) then P ω else 0 := by
        intro ω
        have hcard_eq : X_of v ω = (Ev.filter (fun e ↦ ∀ f ∈ N_all (e.erase v), ω f = false)).card := by
          simp only [X_of, Ev, Finset.filter_filter]
        rw [hcard_eq, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
      simp only [μ]
      simp_rw [h1]
      rw [Finset.sum_comm]
      refine sum_congr rfl fun e _ ↦ ?_
      rw [← Finset.sum_filter, bern_sum_all_false p (N_all (e.erase v))]
    -- Factor `inv_c := ((1 - p) ^ (r * r * Δ₂))⁻¹ ≤ 1 + η₁ / 2` (actually `1 + 4 * r^2 * ε * Δ₂ / D`).
    have hε_half : ε ≤ 1 / 2 := by
      have : 2 ≤ (r : ℝ) := by exact_mod_cast hr
      nlinarith
    have hk_small : 2 * ((r * r * Δ₂ : ℕ) : ℝ) * p ≤ 1 := by
      have h1 : 2 * ((r * r * Δ₂ : ℕ) : ℝ) * p = 2 * ε * (r : ℝ) ^ 2 * ((Δ₂ : ℝ) / (D : ℝ)) := by
        push_cast; simp only [p]; ring
      rw [h1]
      have h2 : 4 * (r : ℝ) ^ 2 * ((Δ₂ : ℝ) / (D : ℝ)) ≤ 1 / 4 := hβ_small.trans hη₁_le
      have h3 := mul_le_mul_of_nonneg_left h2 hε0.le
      have h4 : 2 * ε * (r : ℝ) ^ 2 * ((Δ₂ : ℝ) / (D : ℝ)) ≤ (1 / 8) * ε := by linarith
      linarith
    have hinv_le : ((1 - p) ^ (r * r * Δ₂))⁻¹ ≤ 1 + 4 * ε * (r : ℝ) ^ 2 * ((Δ₂ : ℝ) / (D : ℝ)) := by
      have h := inv_one_sub_pow_le hp0 hp_half (r * r * Δ₂) hk_small
      have h1 : 4 * ((r * r * Δ₂ : ℕ) : ℝ) * p = 4 * ε * (r : ℝ) ^ 2 * ((Δ₂ : ℝ) / (D : ℝ)) := by
        push_cast; simp only [p]; ring
      rwa [h1] at h
    -- Upper bound `μ ≤ (1 + η₁ / 2) * D_exp`.
    have hμ_le : μ ≤ (1 + η₁ / 2) * D_exp := by
      have hterm : ∀ e ∈ Ev, (1 - p) ^ (N_all (e.erase v)).card ≤
          ((1 - p) ^ (r * r * Δ₂))⁻¹ * (1 - p) ^ ((r - 1) * D) := by
        intro e he
        have he_reg : e ∈ ℰ_reg := (mem_filter.mp he).1
        have hve : v ∈ e := (mem_filter.mp he).2
        have herase_sub : e.erase v ⊆ U := (erase_subset v e).trans (hunif e he_reg).1
        have herase_card : (e.erase v).card = r - 1 := by
          rw [card_erase_of_mem hve, (hunif e he_reg).2]
        have hge := hN_card_ge (e.erase v) herase_sub
        rw [herase_card] at hge
        have hle2 : (r - 1) * D ≤ (N_all (e.erase v)).card + r * r * Δ₂ := by
          have : (r - 1) * (r - 1) ≤ r * r := Nat.mul_le_mul (Nat.sub_le r 1) (Nat.sub_le r 1)
          have : (r - 1) * (r - 1) * Δ₂ ≤ r * r * Δ₂ := Nat.mul_le_mul_right Δ₂ this
          omega
        have hpow_le : (1 - p) ^ ((N_all (e.erase v)).card + r * r * Δ₂) ≤
            (1 - p) ^ ((r - 1) * D) :=
          pow_le_pow_of_le_one (by linarith) (by linarith) hle2
        rw [pow_add] at hpow_le
        have hpos_f : 0 < (1 - p) ^ (r * r * Δ₂) := pow_pos (by linarith) _
        calc (1 - p) ^ (N_all (e.erase v)).card
            = ((1 - p) ^ (r * r * Δ₂))⁻¹ * ((1 - p) ^ (N_all (e.erase v)).card *
                (1 - p) ^ (r * r * Δ₂)) := by field_simp
          _ ≤ ((1 - p) ^ (r * r * Δ₂))⁻¹ * (1 - p) ^ ((r - 1) * D) :=
              mul_le_mul_of_nonneg_left hpow_le (inv_nonneg.mpr hpos_f.le)
      have h1 : μ ≤ ((1 - p) ^ (r * r * Δ₂))⁻¹ * D_exp := by
        rw [hμ_eq]
        calc ∑ e ∈ Ev, (1 - p) ^ (N_all (e.erase v)).card
            ≤ ∑ _e ∈ Ev, (((1 - p) ^ (r * r * Δ₂))⁻¹ * (1 - p) ^ ((r - 1) * D)) :=
              sum_le_sum hterm
          _ = (D : ℝ) * (((1 - p) ^ (r * r * Δ₂))⁻¹ * (1 - p) ^ ((r - 1) * D)) := by
              rw [Finset.sum_const, nsmul_eq_mul, hEv_card]
          _ = ((1 - p) ^ (r * r * Δ₂))⁻¹ * D_exp := by simp only [D_exp]; ring
      have hinv2 : ((1 - p) ^ (r * r * Δ₂))⁻¹ ≤ 1 + η₁ / 2 := by
        have hmul : 4 * ε * (r : ℝ) ^ 2 * ((Δ₂ : ℝ) / (D : ℝ)) ≤
            2 * (r : ℝ) ^ 2 * ((Δ₂ : ℝ) / (D : ℝ)) := by
          have hnn : 0 ≤ (r : ℝ) ^ 2 * ((Δ₂ : ℝ) / (D : ℝ)) := by positivity
          have := mul_le_mul_of_nonneg_right hε_half hnn
          linarith
        linarith
      exact h1.trans (mul_le_mul_of_nonneg_right hinv2 (by positivity))
    -- Upper bound `E[X_v^2]`.
    have hE_X2 : ∑ ω, P ω * (X_of v ω : ℝ) ^ 2 ≤
        (r : ℝ) * (Δ₂ : ℝ) * (D : ℝ) + ((1 - p) ^ (r * r * Δ₂))⁻¹ * μ ^ 2 := by
      have hexp : ∑ ω, P ω * (X_of v ω : ℝ) ^ 2 =
          ∑ e₁ ∈ Ev, ∑ e₂ ∈ Ev,
            (1 - p) ^ (N_all (e₁.erase v) ∪ N_all (e₂.erase v)).card := by
        have h1 : ∀ ω, P ω * (X_of v ω : ℝ) ^ 2 =
            ∑ e₁ ∈ Ev, ∑ e₂ ∈ Ev,
              if (∀ f ∈ N_all (e₁.erase v) ∪ N_all (e₂.erase v), ω f = false) then P ω else 0 := by
          intro ω
          have hcard : (X_of v ω : ℝ) = ∑ e ∈ Ev, if (∀ f ∈ N_all (e.erase v), ω f = false) then (1 : ℝ) else 0 := by
            have hce : X_of v ω = (Ev.filter (fun e ↦ ∀ f ∈ N_all (e.erase v), ω f = false)).card := by
              simp only [X_of, Ev, Finset.filter_filter]
            rw [hce, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
          rw [sq, hcard, Finset.sum_mul, Finset.mul_sum]
          refine sum_congr rfl fun e₁ _ ↦ ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          refine sum_congr rfl fun e₂ _ ↦ ?_
          by_cases h1 : ∀ f ∈ N_all (e₁.erase v), ω f = false
          · by_cases h2 : ∀ f ∈ N_all (e₂.erase v), ω f = false
            · have hu : ∀ f ∈ N_all (e₁.erase v) ∪ N_all (e₂.erase v), ω f = false := fun f hf ↦ by
                rcases mem_union.mp hf with hf1 | hf2
                · exact h1 f hf1
                · exact h2 f hf2
              rw [if_pos h1, if_pos h2, if_pos hu]; ring
            · have hu : ¬(∀ f ∈ N_all (e₁.erase v) ∪ N_all (e₂.erase v), ω f = false) := fun ha ↦
                h2 fun f hf ↦ ha f (mem_union_right _ hf)
              rw [if_pos h1, if_neg h2, if_neg hu]; ring
          · have hu : ¬(∀ f ∈ N_all (e₁.erase v) ∪ N_all (e₂.erase v), ω f = false) := fun ha ↦
              h1 fun f hf ↦ ha f (mem_union_left _ hf)
            rw [if_neg h1, if_neg hu]; ring
        simp_rw [h1]
        rw [Finset.sum_comm]
        refine sum_congr rfl fun e₁ _ ↦ ?_
        rw [Finset.sum_comm]
        refine sum_congr rfl fun e₂ _ ↦ ?_
        rw [← Finset.sum_filter, bern_sum_all_false p _]
      rw [hexp]
      -- Split each inner sum into overlapping (`(e₁.erase v ∩ e₂.erase v).Nonempty`) and disjoint.
      have hterm_split : ∀ e₁ ∈ Ev,
          ∑ e₂ ∈ Ev, (1 - p) ^ (N_all (e₁.erase v) ∪ N_all (e₂.erase v)).card ≤
            (r : ℝ) * (Δ₂ : ℝ) +
            ((1 - p) ^ (r * r * Δ₂))⁻¹ * (1 - p) ^ (N_all (e₁.erase v)).card * μ := by
        intro e₁ he₁
        let Ev_ov : Finset (Finset α) := Ev.filter (fun e₂ ↦ (e₁.erase v ∩ e₂.erase v).Nonempty)
        let Ev_dj : Finset (Finset α) := Ev.filter (fun e₂ ↦ ¬(e₁.erase v ∩ e₂.erase v).Nonempty)
        have hpart : ∑ e₂ ∈ Ev, (1 - p) ^ (N_all (e₁.erase v) ∪ N_all (e₂.erase v)).card =
            ∑ e₂ ∈ Ev_ov, (1 - p) ^ (N_all (e₁.erase v) ∪ N_all (e₂.erase v)).card +
            ∑ e₂ ∈ Ev_dj, (1 - p) ^ (N_all (e₁.erase v) ∪ N_all (e₂.erase v)).card :=
          (Finset.sum_filter_add_sum_filter_not Ev _ _).symm
        rw [hpart]
        -- Bound overlapping part by `r * Δ₂`.
        have hov_le : ∑ e₂ ∈ Ev_ov, (1 - p) ^ (N_all (e₁.erase v) ∪ N_all (e₂.erase v)).card ≤
            (r : ℝ) * (Δ₂ : ℝ) := by
          have hov_card : Ev_ov.card ≤ r * Δ₂ := by
            have hsub_ov : Ev_ov ⊆ (e₁.erase v).biUnion (fun u ↦ ℰ_reg.filter (fun f ↦ v ∈ f ∧ u ∈ f)) := by
              intro e₂ he₂
              obtain ⟨he₂Ev, ⟨u, hu⟩⟩ := mem_filter.mp he₂
              exact mem_biUnion.mpr ⟨u, (mem_inter.mp hu).1,
                mem_filter.mpr ⟨(mem_filter.mp he₂Ev).1, (mem_filter.mp he₂Ev).2,
                  (mem_erase.mp (mem_inter.mp hu).2).2⟩⟩
            calc Ev_ov.card
                ≤ ((e₁.erase v).biUnion (fun u ↦ ℰ_reg.filter (fun f ↦ v ∈ f ∧ u ∈ f))).card :=
                  card_le_card hsub_ov
              _ ≤ ∑ u ∈ e₁.erase v, (ℰ_reg.filter (fun f ↦ v ∈ f ∧ u ∈ f)).card := card_biUnion_le
              _ ≤ ∑ _u ∈ e₁.erase v, Δ₂ := sum_le_sum fun u hu ↦
                  hcodeg v hv u ((hunif e₁ (mem_filter.mp he₁).1).1 (mem_erase.mp hu).2)
                    (mem_erase.mp hu).1.symm
              _ = (e₁.erase v).card * Δ₂ := by simp
              _ ≤ r * Δ₂ := Nat.mul_le_mul_right Δ₂
                  ((card_erase_le).trans (hunif e₁ (mem_filter.mp he₁).1).2.le)
          calc ∑ e₂ ∈ Ev_ov, (1 - p) ^ (N_all (e₁.erase v) ∪ N_all (e₂.erase v)).card
              ≤ ∑ _e₂ ∈ Ev_ov, (1 : ℝ) := sum_le_sum fun _ _ ↦ pow_le_one₀ (by linarith) (by linarith)
            _ = (Ev_ov.card : ℝ) := by simp
            _ ≤ (r : ℝ) * (Δ₂ : ℝ) := by exact_mod_cast hov_card
        -- Bound disjoint part by `((1 - p) ^ (r * r * Δ₂))⁻¹ * (1 - p)^(N_all (e₁.erase v)) * μ`.
        have hdj_le : ∑ e₂ ∈ Ev_dj, (1 - p) ^ (N_all (e₁.erase v) ∪ N_all (e₂.erase v)).card ≤
            ((1 - p) ^ (r * r * Δ₂))⁻¹ * (1 - p) ^ (N_all (e₁.erase v)).card * μ := by
          have hterm_dj : ∀ e₂ ∈ Ev_dj,
              (1 - p) ^ (N_all (e₁.erase v) ∪ N_all (e₂.erase v)).card ≤
                ((1 - p) ^ (r * r * Δ₂))⁻¹ * (1 - p) ^ (N_all (e₁.erase v)).card *
                  (1 - p) ^ (N_all (e₂.erase v)).card := by
            intro e₂ he₂
            have he₂Ev : e₂ ∈ Ev := (mem_filter.mp he₂).1
            have hdisj12 : Disjoint (e₁.erase v) (e₂.erase v) :=
              Finset.disjoint_iff_inter_eq_empty.mpr
                (Finset.not_nonempty_iff_eq_empty.mp (mem_filter.mp he₂).2)
            have hinter_le : (N_all (e₁.erase v) ∩ N_all (e₂.erase v)).card ≤ r * r * Δ₂ := by
              have hsubI : (N_all (e₁.erase v) ∩ N_all (e₂.erase v)).image Subtype.val ⊆
                  ((e₁.erase v) ×ˢ (e₂.erase v)).biUnion
                    (fun q ↦ ℰ_reg.filter (fun f ↦ q.1 ∈ f ∧ q.2 ∈ f)) := by
                intro f hf
                obtain ⟨f', hf', rfl⟩ := mem_image.mp hf
                obtain ⟨hf1, hf2⟩ := mem_inter.mp hf'
                obtain ⟨u₁, hu₁⟩ := (mem_filter.mp hf1).2
                obtain ⟨u₂, hu₂⟩ := (mem_filter.mp hf2).2
                exact mem_biUnion.mpr ⟨(u₁, u₂), mem_product.mpr ⟨(mem_inter.mp hu₁).2, (mem_inter.mp hu₂).2⟩,
                  mem_filter.mpr ⟨f'.2, (mem_inter.mp hu₁).1, (mem_inter.mp hu₂).1⟩⟩
              calc (N_all (e₁.erase v) ∩ N_all (e₂.erase v)).card
                  = ((N_all (e₁.erase v) ∩ N_all (e₂.erase v)).image Subtype.val).card :=
                    (Finset.card_image_of_injective _ Subtype.val_injective).symm
                _ ≤ (((e₁.erase v) ×ˢ (e₂.erase v)).biUnion
                      (fun q ↦ ℰ_reg.filter (fun f ↦ q.1 ∈ f ∧ q.2 ∈ f))).card := card_le_card hsubI
                _ ≤ ∑ q ∈ (e₁.erase v) ×ˢ (e₂.erase v),
                      (ℰ_reg.filter (fun f ↦ q.1 ∈ f ∧ q.2 ∈ f)).card := card_biUnion_le
                _ ≤ ∑ _q ∈ (e₁.erase v) ×ˢ (e₂.erase v), Δ₂ := by
                    refine sum_le_sum fun q hq ↦ ?_
                    have hq1 := (mem_product.mp hq).1
                    have hq2 := (mem_product.mp hq).2
                    have hqne : q.1 ≠ q.2 := fun h ↦ Finset.disjoint_left.mp hdisj12 hq1 (h ▸ hq2)
                    exact hcodeg q.1 ((hunif e₁ (mem_filter.mp he₁).1).1 (mem_erase.mp hq1).2)
                      q.2 ((hunif e₂ (mem_filter.mp he₂Ev).1).1 (mem_erase.mp hq2).2) hqne
                _ = (e₁.erase v).card * (e₂.erase v).card * Δ₂ := by simp [card_product]
                _ ≤ r * r * Δ₂ := Nat.mul_le_mul_right Δ₂ (Nat.mul_le_mul
                    ((card_erase_le).trans (hunif e₁ (mem_filter.mp he₁).1).2.le)
                    ((card_erase_le).trans (hunif e₂ (mem_filter.mp he₂Ev).1).2.le))
            have hcard_u : (N_all (e₁.erase v)).card + (N_all (e₂.erase v)).card ≤
                (N_all (e₁.erase v) ∪ N_all (e₂.erase v)).card + r * r * Δ₂ := by
              have := Finset.card_union_add_card_inter (N_all (e₁.erase v)) (N_all (e₂.erase v))
              omega
            have hpow_le : (1 - p) ^ ((N_all (e₁.erase v) ∪ N_all (e₂.erase v)).card + r * r * Δ₂) ≤
                (1 - p) ^ ((N_all (e₁.erase v)).card + (N_all (e₂.erase v)).card) :=
              pow_le_pow_of_le_one (by linarith) (by linarith) hcard_u
            rw [pow_add, pow_add] at hpow_le
            have hpos_f : 0 < (1 - p) ^ (r * r * Δ₂) := pow_pos (by linarith) _
            calc (1 - p) ^ (N_all (e₁.erase v) ∪ N_all (e₂.erase v)).card
                = ((1 - p) ^ (r * r * Δ₂))⁻¹ *
                    ((1 - p) ^ (N_all (e₁.erase v) ∪ N_all (e₂.erase v)).card *
                      (1 - p) ^ (r * r * Δ₂)) := by field_simp
              _ ≤ ((1 - p) ^ (r * r * Δ₂))⁻¹ *
                    ((1 - p) ^ (N_all (e₁.erase v)).card * (1 - p) ^ (N_all (e₂.erase v)).card) :=
                  mul_le_mul_of_nonneg_left hpow_le (inv_nonneg.mpr hpos_f.le)
              _ = _ := by ring
          calc ∑ e₂ ∈ Ev_dj, (1 - p) ^ (N_all (e₁.erase v) ∪ N_all (e₂.erase v)).card
              ≤ ∑ e₂ ∈ Ev_dj, (((1 - p) ^ (r * r * Δ₂))⁻¹ * (1 - p) ^ (N_all (e₁.erase v)).card *
                  (1 - p) ^ (N_all (e₂.erase v)).card) := sum_le_sum hterm_dj
            _ ≤ ∑ e₂ ∈ Ev, (((1 - p) ^ (r * r * Δ₂))⁻¹ * (1 - p) ^ (N_all (e₁.erase v)).card *
                  (1 - p) ^ (N_all (e₂.erase v)).card) :=
                sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
                  (fun _ _ _ ↦ by positivity)
            _ = ((1 - p) ^ (r * r * Δ₂))⁻¹ * (1 - p) ^ (N_all (e₁.erase v)).card * μ := by
                rw [← Finset.mul_sum, ← hμ_eq]
        exact add_le_add hov_le hdj_le
      calc ∑ e₁ ∈ Ev, ∑ e₂ ∈ Ev, (1 - p) ^ (N_all (e₁.erase v) ∪ N_all (e₂.erase v)).card
          ≤ ∑ e₁ ∈ Ev, ((r : ℝ) * (Δ₂ : ℝ) +
              ((1 - p) ^ (r * r * Δ₂))⁻¹ * (1 - p) ^ (N_all (e₁.erase v)).card * μ) :=
            sum_le_sum hterm_split
        _ = (D : ℝ) * ((r : ℝ) * (Δ₂ : ℝ)) +
            ((1 - p) ^ (r * r * Δ₂))⁻¹ * (∑ e₁ ∈ Ev, (1 - p) ^ (N_all (e₁.erase v)).card) * μ := by
            rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hEv_card,
              ← Finset.sum_mul, ← Finset.mul_sum]
        _ = (r : ℝ) * (Δ₂ : ℝ) * (D : ℝ) + ((1 - p) ^ (r * r * Δ₂))⁻¹ * μ ^ 2 := by
            rw [← hμ_eq]; ring
    -- Apply Chebyshev to `X_of v`.
    have hμ_le_D : μ ≤ (D : ℝ) := by
      rw [hμ_eq]
      calc ∑ e ∈ Ev, (1 - p) ^ (N_all (e.erase v)).card
          ≤ ∑ _e ∈ Ev, (1 : ℝ) := sum_le_sum fun _ _ ↦ pow_le_one₀ (by linarith) (by linarith)
        _ = (D : ℝ) := by simp [hEv_card]
    have hμ_nn : 0 ≤ μ := by
      rw [hμ_eq]; exact sum_nonneg fun _ _ ↦ pow_nonneg (by linarith) _
    have hvar : ∑ ω, P ω * ((X_of v ω : ℝ) - μ) ^ 2 ≤
        ((r : ℝ) + (r : ℝ) ^ 2) * ((Δ₂ : ℝ) / (D : ℝ)) * (D : ℝ) ^ 2 := by
      have hid : ∑ ω, P ω * ((X_of v ω : ℝ) - μ) ^ 2 =
          ∑ ω, P ω * (X_of v ω : ℝ) ^ 2 - μ ^ 2 := by
        have h1 : ∀ ω, P ω * ((X_of v ω : ℝ) - μ) ^ 2 =
            P ω * (X_of v ω : ℝ) ^ 2 - 2 * μ * (P ω * (X_of v ω : ℝ)) + μ ^ 2 * P ω := fun ω ↦ by ring
        simp_rw [h1]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          hP_sum]
        change ∑ ω, P ω * (X_of v ω : ℝ) ^ 2 - 2 * μ * μ + μ ^ 2 * 1 = _
        ring
      rw [hid]
      have hε_q : 4 * ε ≤ 1 := by
        have : 2 ≤ (r : ℝ) := by exact_mod_cast hr
        nlinarith
      have hdiff_inv : ((1 - p) ^ (r * r * Δ₂))⁻¹ - 1 ≤ (r : ℝ) ^ 2 * ((Δ₂ : ℝ) / (D : ℝ)) := by
        have : 0 ≤ (r : ℝ) ^ 2 * ((Δ₂ : ℝ) / (D : ℝ)) := by positivity
        nlinarith
      have hμ2 : μ ^ 2 ≤ (D : ℝ) ^ 2 := pow_le_pow_left₀ hμ_nn hμ_le_D 2
      have h1 : (((1 - p) ^ (r * r * Δ₂))⁻¹ - 1) * μ ^ 2 ≤
          ((r : ℝ) ^ 2 * ((Δ₂ : ℝ) / (D : ℝ))) * (D : ℝ) ^ 2 :=
        mul_le_mul hdiff_inv hμ2 (sq_nonneg μ) (by positivity)
      have h2 : (r : ℝ) * (Δ₂ : ℝ) * (D : ℝ) = (r : ℝ) * ((Δ₂ : ℝ) / (D : ℝ)) * (D : ℝ) ^ 2 := by
        field_simp
      linarith
    have hgap : (η₁ / 4) * (D : ℝ) ≤ (D' : ℝ) - μ := by
      have hD'_lo : (1 + η₁) * D_exp ≤ (D' : ℝ) := hD'_arg ▸ Nat.le_ceil _
      nlinarith
    have hcheb : ((η₁ / 4) * (D : ℝ)) ^ 2 *
        ∑ ω ∈ Finset.univ.filter (fun ω ↦ D' < X_of v ω), P ω ≤
        ∑ ω, P ω * ((X_of v ω : ℝ) - μ) ^ 2 := by
      rw [Finset.mul_sum]
      calc ∑ ω ∈ Finset.univ.filter (fun ω ↦ D' < X_of v ω), ((η₁ / 4) * (D : ℝ)) ^ 2 * P ω
          ≤ ∑ ω ∈ Finset.univ.filter (fun ω ↦ D' < X_of v ω), P ω * ((X_of v ω : ℝ) - μ) ^ 2 := by
            refine sum_le_sum fun ω hω ↦ ?_
            have hlt : (D' : ℝ) < (X_of v ω : ℝ) := by exact_mod_cast (mem_filter.mp hω).2
            have hle_sq : ((η₁ / 4) * (D : ℝ)) ^ 2 ≤ ((X_of v ω : ℝ) - μ) ^ 2 :=
              pow_le_pow_left₀ (by positivity) (by linarith) 2
            rw [mul_comm (P ω)]
            exact mul_le_mul_of_nonneg_right hle_sq (hP_nn ω)
        _ ≤ ∑ ω, P ω * ((X_of v ω : ℝ) - μ) ^ 2 :=
            sum_le_sum_of_subset_of_nonneg (subset_univ _)
              (fun ω _ _ ↦ mul_nonneg (hP_nn ω) (sq_nonneg _))
    have hcomb := hcheb.trans hvar
    have hpos_den : 0 < ((η₁ / 4) * (D : ℝ)) ^ 2 := by positivity
    have hdiv : ∑ ω ∈ Finset.univ.filter (fun ω ↦ D' < X_of v ω), P ω ≤
        (((r : ℝ) + (r : ℝ) ^ 2) * ((Δ₂ : ℝ) / (D : ℝ)) * (D : ℝ) ^ 2) /
          (((η₁ / 4) * (D : ℝ)) ^ 2) := (le_div_iff₀' hpos_den).mpr hcomb
    have hsimp : (((r : ℝ) + (r : ℝ) ^ 2) * ((Δ₂ : ℝ) / (D : ℝ)) * (D : ℝ) ^ 2) /
        (((η₁ / 4) * (D : ℝ)) ^ 2) =
        16 * ((r : ℝ) + (r : ℝ) ^ 2) * ((Δ₂ : ℝ) / (D : ℝ)) / η₁ ^ 2 := by
      field_simp; ring
    rw [hsimp] at hdiv
    refine hdiv.trans ?_
    rw [div_le_div_iff₀ (sq_pos_of_pos hη₁0) hr_pos]
    nlinarith
  -- Expectation of deleted edges `ℰ'_of ω \ ℰ_rem_of ω`.
  have hE_lost : ∑ ω, P ω * ((ℰ'_of ω \ ℰ_rem_of ω).card : ℝ) ≤ η₁ * (ℰ_orig.card : ℝ) := by
    have hdet : ∀ ω, ((ℰ'_of ω \ ℰ_rem_of ω).card : ℝ) ≤
        ∑ v ∈ U, if D' < X_of v ω then ((ℰ_orig.filter (fun e ↦ v ∈ e)).card : ℝ) else 0 := by
      intro ω
      have hsub_l : ℰ'_of ω \ ℰ_rem_of ω ⊆
          (B_of ω).biUnion (fun v ↦ ℰ_orig.filter (fun e ↦ v ∈ e)) := by
        intro e he
        obtain ⟨he', hnot⟩ := mem_sdiff.mp he
        have he_orig : e ∈ ℰ_orig := (mem_filter.mp he').1
        have hnd : ¬Disjoint e (B_of ω) := fun hd ↦ hnot (mem_filter.mpr ⟨he', hd⟩)
        rw [Finset.not_disjoint_iff] at hnd
        obtain ⟨v, hve, hvB⟩ := hnd
        exact mem_biUnion.mpr ⟨v, hvB, mem_filter.mpr ⟨he_orig, hve⟩⟩
      have hcard_l : (ℰ'_of ω \ ℰ_rem_of ω).card ≤
          ∑ v ∈ B_of ω, (ℰ_orig.filter (fun e ↦ v ∈ e)).card :=
        (card_le_card hsub_l).trans card_biUnion_le
      have hcard_r : ((ℰ'_of ω \ ℰ_rem_of ω).card : ℝ) ≤
          ∑ v ∈ B_of ω, ((ℰ_orig.filter (fun e ↦ v ∈ e)).card : ℝ) := by exact_mod_cast hcard_l
      rwa [Finset.sum_filter] at hcard_r
    calc ∑ ω, P ω * ((ℰ'_of ω \ ℰ_rem_of ω).card : ℝ)
        ≤ ∑ ω, P ω * (∑ v ∈ U, if D' < X_of v ω then ((ℰ_orig.filter (fun e ↦ v ∈ e)).card : ℝ) else 0) :=
          sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left (hdet ω) (hP_nn ω)
      _ = ∑ v ∈ U, ((ℰ_orig.filter (fun e ↦ v ∈ e)).card : ℝ) *
            ∑ ω ∈ Finset.univ.filter (fun ω ↦ D' < X_of v ω), P ω := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine sum_congr rfl fun v _ ↦ ?_
          rw [Finset.sum_filter]
          refine sum_congr rfl fun ω _ ↦ by split_ifs <;> ring
      _ ≤ ∑ v ∈ U, ((ℰ_orig.filter (fun e ↦ v ∈ e)).card : ℝ) * (η₁ / (r : ℝ)) :=
          sum_le_sum fun v hv ↦ mul_le_mul_of_nonneg_left (hbad_prob v hv) (Nat.cast_nonneg _)
      _ = (η₁ / (r : ℝ)) * ∑ v ∈ U, ((ℰ_orig.filter (fun e ↦ v ∈ e)).card : ℝ) := by
          rw [← Finset.sum_mul, mul_comm]
      _ = (η₁ / (r : ℝ)) * ((r : ℝ) * (ℰ_orig.card : ℝ)) := by
          congr 1
          have hdc : ∑ v ∈ U, (ℰ_orig.filter (fun e ↦ v ∈ e)).card = r * ℰ_orig.card := by
            calc ∑ v ∈ U, (ℰ_orig.filter (fun e ↦ v ∈ e)).card
                = ∑ v ∈ U, ∑ e ∈ ℰ_orig, if v ∈ e then 1 else 0 := by
                  refine sum_congr rfl fun v _ ↦ by
                    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
              _ = ∑ e ∈ ℰ_orig, ∑ v ∈ U, if v ∈ e then 1 else 0 := Finset.sum_comm
              _ = ∑ e ∈ ℰ_orig, r := by
                  refine sum_congr rfl fun e he ↦ ?_
                  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
                  have hesub := (hunif e (hsub he)).1
                  have heq : U.filter (fun v ↦ v ∈ e) = e := by
                    ext v; simp only [mem_filter]; exact ⟨fun h ↦ h.2, fun h ↦ ⟨hesub h, h⟩⟩
                  rw [heq, (hunif e (hsub he)).2]
              _ = r * ℰ_orig.card := by simp [mul_comm]
          exact_mod_cast hdc
      _ = η₁ * (ℰ_orig.card : ℝ) := by field_simp
  -- Combine expectations for `ℰ_rem_of` and `ℳ₁_of`.
  have hE_rem : ((1 - p) ^ (r * D) - η₁) * (ℰ_orig.card : ℝ) ≤
      ∑ ω, P ω * ((ℰ_rem_of ω).card : ℝ) := by
    have hcard_diff : ∀ ω, ((ℰ'_of ω).card : ℝ) - ((ℰ'_of ω \ ℰ_rem_of ω).card : ℝ) =
        ((ℰ_rem_of ω).card : ℝ) := by
      intro ω
      have := Finset.card_sdiff_add_card_eq_card (filter_subset (fun e ↦ Disjoint e (B_of ω)) (ℰ'_of ω))
      have : ((ℰ'_of ω \ ℰ_rem_of ω).card : ℝ) + ((ℰ_rem_of ω).card : ℝ) = ((ℰ'_of ω).card : ℝ) := by
        exact_mod_cast this
      linarith
    have hsum_eq : ∑ ω, P ω * ((ℰ_rem_of ω).card : ℝ) =
        ∑ ω, P ω * ((ℰ'_of ω).card : ℝ) - ∑ ω, P ω * ((ℰ'_of ω \ ℰ_rem_of ω).card : ℝ) := by
      rw [← Finset.sum_sub_distrib]
      refine sum_congr rfl fun ω _ ↦ by rw [← hcard_diff ω]; ring
    linarith
  have hratio : 1 - ε - 4 * η₁ ≤ ((1 - p) ^ (r * D) - η₁) * (D : ℝ) / (D' : ℝ) := by
    have hsplit_pow : (1 - p) ^ (r * D) = (1 - p) ^ D * (1 - p) ^ ((r - 1) * D) := by
      rw [← pow_add]; congr 1
      have : D + (r - 1) * D = (1 + (r - 1)) * D := by ring
      rw [this, Nat.add_sub_cancel' (by omega : 1 ≤ r)]
    have h1pD : 1 - ε ≤ (1 - p) ^ D := by
      have := one_sub_mul_le_pow hp0 hp1 D
      have hmul : (D : ℝ) * p = ε := by simp only [p]; field_simp
      rwa [hmul] at this
    have hnum : (1 - ε - 2 * η₁) * D_exp ≤ ((1 - p) ^ (r * D) - η₁) * (D : ℝ) := by
      rw [hsplit_pow]
      have h1 : (1 - p) ^ D * (1 - p) ^ ((r - 1) * D) * (D : ℝ) - η₁ * (D : ℝ) =
          (1 - p) ^ D * D_exp - η₁ * (D : ℝ) := by simp only [D_exp]; ring
      have h2 : η₁ * (D : ℝ) ≤ 2 * η₁ * D_exp := by nlinarith
      nlinarith
    have h3 : (1 - ε - 4 * η₁) * (1 + 2 * η₁) ≤ 1 - ε - 2 * η₁ := by
      have : ε ≤ 1 / 4 := by
        have : 2 ≤ (r : ℝ) := by exact_mod_cast hr
        nlinarith
      nlinarith
    rw [le_div_iff₀ hD'_pos]
    by_cases hneg : 0 ≤ 1 - ε - 4 * η₁
    · calc (1 - ε - 4 * η₁) * (D' : ℝ)
          ≤ (1 - ε - 4 * η₁) * ((1 + 2 * η₁) * D_exp) := mul_le_mul_of_nonneg_left hD'_le hneg
        _ = ((1 - ε - 4 * η₁) * (1 + 2 * η₁)) * D_exp := by ring
        _ ≤ (1 - ε - 2 * η₁) * D_exp := mul_le_mul_of_nonneg_right h3 (by positivity)
        _ ≤ ((1 - p) ^ (r * D) - η₁) * (D : ℝ) := hnum
    · push Not at hneg
      have hle1 : (1 - ε - 4 * η₁) * (D' : ℝ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hneg.le hD'_pos.le
      have h1prD : 1 - (r : ℝ) * ε ≤ (1 - p) ^ (r * D) := by
        have := one_sub_mul_le_pow hp0 hp1 (r * D)
        have hmul : ((r * D : ℕ) : ℝ) * p = (r : ℝ) * ε := by
          rw [Nat.cast_mul]; simp only [p]; field_simp
        rwa [hmul] at this
      have hrhs_nn : 0 ≤ ((1 - p) ^ (r * D) - η₁) * (D : ℝ) :=
        mul_nonneg (by linarith) hD_pos.le
      exact hle1.trans hrhs_nn
  -- Linearity of expectation gives an outcome `ω₀` attaining at least the mean!
  let target : ℝ :=
    (ε * (1 - (r : ℝ) * ε) + c_next * (1 - ε - 4 * η₁)) * ((ℰ_orig.card : ℝ) / (D : ℝ))
  have hE_total : target ≤
      ∑ ω, P ω * (((ℳ₁_of ω).card : ℝ) + c_next * (((ℰ_rem_of ω).card : ℝ) / (D' : ℝ))) := by
    have h1 : ∑ ω, P ω * (((ℳ₁_of ω).card : ℝ) + c_next * (((ℰ_rem_of ω).card : ℝ) / (D' : ℝ))) =
        ∑ ω, P ω * ((ℳ₁_of ω).card : ℝ) +
        (c_next / (D' : ℝ)) * ∑ ω, P ω * ((ℰ_rem_of ω).card : ℝ) := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum]
      refine sum_congr rfl fun ω _ ↦ by ring
    rw [h1]
    have h2 : c_next * (1 - ε - 4 * η₁) * ((ℰ_orig.card : ℝ) / (D : ℝ)) ≤
        (c_next / (D' : ℝ)) * (((1 - p) ^ (r * D) - η₁) * (ℰ_orig.card : ℝ)) := by
      have hmul := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hratio (div_nonneg (Nat.cast_nonneg ℰ_orig.card) hD_pos.le)) hc_nn
      have hrew : c_next * (((1 - p) ^ (r * D) - η₁) * (D : ℝ) / (D' : ℝ) *
          ((ℰ_orig.card : ℝ) / (D : ℝ))) =
          (c_next / (D' : ℝ)) * (((1 - p) ^ (r * D) - η₁) * (ℰ_orig.card : ℝ)) := by
        field_simp
      linarith
    have h3 : (c_next / (D' : ℝ)) * (((1 - p) ^ (r * D) - η₁) * (ℰ_orig.card : ℝ)) ≤
        (c_next / (D' : ℝ)) * ∑ ω, P ω * ((ℰ_rem_of ω).card : ℝ) :=
      mul_le_mul_of_nonneg_left hE_rem (div_nonneg hc_nn hD'_pos.le)
    simp only [target]
    linarith
  have hex_ω : ∃ ω, target ≤
      ((ℳ₁_of ω).card : ℝ) + c_next * (((ℰ_rem_of ω).card : ℝ) / (D' : ℝ)) := by
    by_contra hall
    push Not at hall
    have hlt : ∑ ω, P ω * (((ℳ₁_of ω).card : ℝ) + c_next * (((ℰ_rem_of ω).card : ℝ) / (D' : ℝ))) <
        target := by
      have hle_t : ∑ ω, P ω * (((ℳ₁_of ω).card : ℝ) + c_next * (((ℰ_rem_of ω).card : ℝ) / (D' : ℝ))) ≤
          ∑ ω, P ω * target := sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left (hall ω).le (hP_nn ω)
      have hstrict : ∃ ω, 0 < P ω := by
        by_contra h0
        push Not at h0
        have : ∑ ω, P ω ≤ 0 := sum_nonpos fun ω _ ↦ h0 ω
        linarith
      obtain ⟨ω₁, hω₁⟩ := hstrict
      have hlt_s : ∑ ω, P ω * (((ℳ₁_of ω).card : ℝ) + c_next * (((ℰ_rem_of ω).card : ℝ) / (D' : ℝ))) <
          ∑ ω, P ω * target :=
        Finset.sum_lt_sum (fun ω _ ↦ mul_le_mul_of_nonneg_left (hall ω).le (hP_nn ω))
          ⟨ω₁, mem_univ ω₁, mul_lt_mul_of_pos_left (hall ω₁) hω₁⟩
      rwa [← Finset.sum_mul, hP_sum, one_mul] at hlt_s
    linarith
  obtain ⟨ω₀, hω₀⟩ := hex_ω
  refine ⟨ℳ₁_of ω₀, ℰ_rem_of ω₀, filter_subset _ _, (filter_subset _ _).trans (filter_subset _ _),
    ?_, ?_, ?_, hD'_ge, hω₀⟩
  · -- `ℳ₁_of ω₀` is a matching!
    intro e₁ he₁ e₂ he₂ hne
    obtain ⟨he₁_reg, hω₁, hiso₁⟩ := (mem_filter.mp he₁).2
    obtain ⟨he₂_reg, hω₂, _⟩ := (mem_filter.mp he₂).2
    rw [Finset.disjoint_left]
    intro v hv₁ hv₂
    have hf_mem : (⟨e₂, he₂_reg⟩ : { e // e ∈ ℰ_reg }) ∈ (N_all e₁).erase ⟨e₁, he₁_reg⟩ :=
      mem_erase.mpr ⟨fun h ↦ hne (congrArg Subtype.val h).symm,
        mem_filter.mpr ⟨mem_univ _, ⟨v, mem_inter.mpr ⟨hv₂, hv₁⟩⟩⟩⟩
    have := hiso₁ ⟨e₂, he₂_reg⟩ hf_mem
    rw [hω₂] at this
    exact Bool.noConfusion this
  · -- `ℳ₁_of ω₀` and `ℰ_rem_of ω₀` are vertex-disjoint!
    intro e₁ he₁ e₂ he₂
    obtain ⟨he₁_reg, hω₁, _⟩ := (mem_filter.mp he₁).2
    have hrem2 := (mem_filter.mp (mem_filter.mp he₂).1).2
    rw [Finset.disjoint_left]
    intro v hv₁ hv₂
    have hf_mem : (⟨e₁, he₁_reg⟩ : { e // e ∈ ℰ_reg }) ∈ N_all e₂ :=
      mem_filter.mpr ⟨mem_univ _, ⟨v, mem_inter.mpr ⟨hv₁, hv₂⟩⟩⟩
    have := hrem2 ⟨e₁, he₁_reg⟩ hf_mem
    rw [hω₁] at this
    exact Bool.noConfusion this
  · -- Max degree of `ℰ_rem_of ω₀` is `≤ D'`!
    intro v hv
    by_cases hvB : v ∈ B_of ω₀
    · have hemp : (ℰ_rem_of ω₀).filter (fun e ↦ v ∈ e) = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        intro e he
        obtain ⟨her, hve⟩ := mem_filter.mp he
        exact Finset.disjoint_left.mp (mem_filter.mp her).2 hve hvB
      simp [hemp]
    · have hle_X : X_of v ω₀ ≤ D' := by
        by_contra hgt; push Not at hgt
        exact hvB (mem_filter.mpr ⟨hv, hgt⟩)
      have hsub_X : (ℰ_rem_of ω₀).filter (fun e ↦ v ∈ e) ⊆
          ℰ_reg.filter (fun e ↦ v ∈ e ∧ ∀ f ∈ N_all (e.erase v), ω₀ f = false) := by
        intro e he
        obtain ⟨her, hve⟩ := mem_filter.mp he
        have he' := (mem_filter.mp her).1
        refine mem_filter.mpr ⟨hsub (mem_filter.mp he').1, hve, fun f hf ↦ ?_⟩
        apply (mem_filter.mp he').2 f
        obtain ⟨u, hu⟩ := (mem_filter.mp hf).2
        exact mem_filter.mpr ⟨mem_univ f, ⟨u, mem_inter.mpr ⟨(mem_inter.mp hu).1,
          (mem_erase.mp (mem_inter.mp hu).2).2⟩⟩⟩
      exact (card_le_card hsub_X).trans hle_X

lemma nibble_T_rounds (r : ℕ) (hr : 2 ≤ r) (ε : ℝ) (hε0 : 0 < ε) (hε_small : 4 * (r : ℝ) * ε ≤ 1)
    (T : ℕ) :
    let η₁ : ℝ := ε ^ 2
    let c_T : ℝ := (ε * (1 - (r : ℝ) * ε)) / (ε + 4 * η₁) * (1 - (1 - ε - 4 * η₁) ^ T)
    ∃ β : ℝ, 0 < β ∧ ∃ D₀ : ℕ, 1 ≤ D₀ ∧
      ∀ {α : Type*} [DecidableEq α] (U : Finset α) (ℰ : Finset (Finset α)) (D : ℕ),
        D₀ ≤ D →
        (∀ e ∈ ℰ, e ⊆ U ∧ e.card = r) →
        (∀ x ∈ U, (ℰ.filter (fun e ↦ x ∈ e)).card ≤ D) →
        (∀ x ∈ U, ∀ y ∈ U, x ≠ y → ((ℰ.filter (fun e ↦ x ∈ e ∧ y ∈ e)).card : ℝ) ≤ β * (D : ℝ)) →
        ∃ ℳ : Finset (Finset α), ℳ ⊆ ℰ ∧
          (∀ e₁ ∈ ℳ, ∀ e₂ ∈ ℳ, e₁ ≠ e₂ → Disjoint e₁ e₂) ∧
          c_T * ((ℰ.card : ℝ) / (D : ℝ)) ≤ (ℳ.card : ℝ) := by
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hε_le_q : ε ≤ 1 / 8 := by
    have : 2 ≤ (r : ℝ) := by exact_mod_cast hr
    nlinarith
  let η₁ : ℝ := ε ^ 2
  have hη₁0 : 0 < η₁ := sq_pos_of_pos hε0
  have hη₁_le : η₁ ≤ 1 / 4 := by simp only [η₁]; nlinarith
  induction T with
  | zero =>
    refine ⟨1, zero_lt_one, 1, le_rfl, fun U ℰ D _ _ _ _ ↦ ⟨∅, empty_subset _, by simp, by simp⟩⟩
  | succ T ih =>
    obtain ⟨β_T, hβ_T0, D_T, hD_T1, hIH⟩ := ih
    let c_T : ℝ := (ε * (1 - (r : ℝ) * ε)) / (ε + 4 * η₁) * (1 - (1 - ε - 4 * η₁) ^ T)
    have hc_T_nn : 0 ≤ c_T := by
      have h1 : 0 ≤ 1 - (r : ℝ) * ε := by nlinarith
      have h2 : (1 - ε - 4 * η₁) ^ T ≤ 1 := pow_le_one₀ (by simp only [η₁]; nlinarith)
        (by simp only [η₁]; nlinarith)
      exact mul_nonneg (div_nonneg (mul_nonneg hε0.le h1) (by positivity)) (by linarith)
    let β_raw : ℝ := min (β_T / 4) (min (η₁ / (8 * (r : ℝ) ^ 2))
      (η₁ ^ 3 / (64 * ((r : ℝ) + (r : ℝ) ^ 2) * (r : ℝ))))
    have hβ0 : 0 < β_raw := lt_min (by positivity) (lt_min (by positivity) (by positivity))
    let D₀ : ℕ := max (max (2 * D_T) (Nat.ceil (2 / η₁))) (Nat.ceil (1 / β_raw))
    have hD₀1 : 1 ≤ D₀ := le_trans (by omega : 1 ≤ 2 * D_T)
      (le_trans (le_max_left _ _) (le_max_left _ _))
    refine ⟨β_raw, hβ0, D₀, hD₀1, fun {α} _ U ℰ D hD hunif hdeg hcodeg ↦ ?_⟩
    have hD1 : 1 ≤ D := hD₀1.trans hD
    have hD_pos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (show 0 < D by omega)
    let Δ₂ : ℕ := Nat.floor (β_raw * (D : ℝ))
    have hΔ₂_le : (Δ₂ : ℝ) ≤ β_raw * (D : ℝ) := Nat.floor_le (by positivity)
    have hcodeg_nat : ∀ x ∈ U, ∀ y ∈ U, x ≠ y → (ℰ.filter (fun e ↦ x ∈ e ∧ y ∈ e)).card ≤ Δ₂ :=
      fun x hx y hy hxy ↦ Nat.le_floor (hcodeg x hx y hy hxy)
    -- Step A: Regularize `ℋ` via affine lines over `ZMod p_prime`.
    obtain ⟨p_prime, hp_fact, ℰ_orig, ℰ_reg, hsub_or, hunif_reg, hreg_deg, hreg_codeg,
      hcard_orig, hpigeon⟩ := regularize_hypergraph U ℰ r D Δ₂ hr hD1 hunif hdeg hcodeg_nat
    let W : Finset (Fin r × ZMod p_prime) := Finset.univ
    -- Note `max Δ₂ 1 ≤ 2 * β_raw * D` since `D ≥ 1 / β_raw`.
    have h1_le_βD : 1 ≤ β_raw * (D : ℝ) := by
      have h1 : 1 / β_raw ≤ (D : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hD)
      have := (div_le_iff₀ hβ0).mp h1
      linarith
    have hΔ₂_reg_le : ((max Δ₂ 1 : ℕ) : ℝ) / (D : ℝ) ≤ 2 * β_raw := by
      have hmax : ((max Δ₂ 1 : ℕ) : ℝ) ≤ 2 * β_raw * (D : ℝ) := by
        rw [Nat.cast_max]; simp only [Nat.cast_one]
        exact max_le (by linarith) (by linarith)
      exact (div_le_iff₀ hD_pos).mpr hmax
    have hβ_small' : 4 * (r : ℝ) ^ 2 * (((max Δ₂ 1 : ℕ) : ℝ) / (D : ℝ)) ≤ η₁ := by
      have h1 : β_raw ≤ η₁ / (8 * (r : ℝ) ^ 2) := (min_le_right _ _).trans (min_le_left _ _)
      have h2 : 8 * (r : ℝ) ^ 2 * β_raw ≤ η₁ := by
        have := (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * (r : ℝ) ^ 2)).mp h1
        linarith
      have h3 := mul_le_mul_of_nonneg_left hΔ₂_reg_le (by positivity : (0 : ℝ) ≤ 4 * (r : ℝ) ^ 2)
      linarith
    have hβ_cheb' : 32 * ((r : ℝ) + (r : ℝ) ^ 2) * (((max Δ₂ 1 : ℕ) : ℝ) / (D : ℝ)) * (r : ℝ) ≤ η₁ ^ 3 := by
      have h1 : β_raw ≤ η₁ ^ 3 / (64 * ((r : ℝ) + (r : ℝ) ^ 2) * (r : ℝ)) :=
        (min_le_right _ _).trans (min_le_right _ _)
      have h2 : 64 * ((r : ℝ) + (r : ℝ) ^ 2) * (r : ℝ) * β_raw ≤ η₁ ^ 3 := by
        have := (le_div_iff₀ (by positivity : (0 : ℝ) < 64 * ((r : ℝ) + (r : ℝ) ^ 2) * (r : ℝ))).mp h1
        linarith
      have h3 := mul_le_mul_of_nonneg_left hΔ₂_reg_le
        (by positivity : (0 : ℝ) ≤ 32 * ((r : ℝ) + (r : ℝ) ^ 2) * (r : ℝ))
      linarith
    have hD_η' : 2 ≤ η₁ * (D : ℝ) := by
      have h1 : 2 / η₁ ≤ (D : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast ((le_max_right _ _).trans (le_max_left _ _)).trans hD)
      have := (div_le_iff₀ hη₁0).mp h1
      linarith
    -- Step B: Apply one nibble step to `(ℰ_orig, ℰ_reg)`.
    obtain ⟨ℳ₁, ℰ_rem, hℳ₁_sub, hℰ_rem_sub, hℳ₁_disj, hdisj_12, hdeg_rem, hD'_ge, hgain⟩ :=
      nibble_one_step (W ×ˢ U) ℰ_orig ℰ_reg r D (max Δ₂ 1) ε η₁ c_T hr hD1 hε0 hε_small
        hη₁0 hη₁_le hc_T_nn hβ_small' hβ_cheb' hD_η' hsub_or hunif_reg hreg_deg hreg_codeg
    let D' : ℕ := Nat.ceil ((1 + η₁) * (1 - ε / (D : ℝ)) ^ ((r - 1) * D) * (D : ℝ))
    -- Step C: Apply induction hypothesis for `T` rounds to `ℰ_rem`!
    have hD'_ge_DT : D_T ≤ D' := by
      have h2DT : 2 * D_T ≤ D := ((le_max_left _ _).trans (le_max_left _ _)).trans hD
      have h2DT_r : (D_T : ℝ) ≤ (D : ℝ) / 2 := by
        have : (2 * D_T : ℝ) ≤ (D : ℝ) := by exact_mod_cast h2DT
        linarith
      exact_mod_cast h2DT_r.trans hD'_ge
    have hcodeg_rem : ∀ v₁ ∈ W ×ˢ U, ∀ v₂ ∈ W ×ˢ U, v₁ ≠ v₂ →
        ((ℰ_rem.filter (fun e ↦ v₁ ∈ e ∧ v₂ ∈ e)).card : ℝ) ≤ β_T * (D' : ℝ) := by
      intro v₁ hv₁ v₂ hv₂ hne
      have h1 : (ℰ_rem.filter (fun e ↦ v₁ ∈ e ∧ v₂ ∈ e)).card ≤ max Δ₂ 1 :=
        (card_le_card (filter_subset_filter _ (hℰ_rem_sub.trans hsub_or))).trans
          (hreg_codeg v₁ hv₁ v₂ hv₂ hne)
      have h2 : ((max Δ₂ 1 : ℕ) : ℝ) ≤ 2 * β_raw * (D : ℝ) := (div_le_iff₀ hD_pos).mp hΔ₂_reg_le
      have h3 : 2 * β_raw * (D : ℝ) ≤ β_T * (D' : ℝ) := by
        have hβ_le : β_raw ≤ β_T / 4 := min_le_left _ _
        nlinarith
      exact (by exact_mod_cast h1 : ((ℰ_rem.filter _).card : ℝ) ≤ ((max Δ₂ 1 : ℕ) : ℝ)).trans
        (h2.trans h3)
    obtain ⟨ℳ₂, hℳ₂_sub, hℳ₂_disj, hℳ₂_card⟩ :=
      hIH (W ×ˢ U) ℰ_rem D' hD'_ge_DT
        (fun e he ↦ hunif_reg e (hsub_or (hℰ_rem_sub he))) hdeg_rem hcodeg_rem
    -- Step D: Combine `ℳ₁ ∪ ℳ₂ ⊆ ℰ_orig` and apply pigeonhole over `W`!
    have hdisj_M12 : Disjoint ℳ₁ ℳ₂ := by
      rw [Finset.disjoint_left]
      intro e he₁ he₂
      have hd := hdisj_12 e he₁ e (hℳ₂_sub he₂)
      have hne : e.Nonempty := card_pos.mp (by have := (hunif_reg e (hsub_or (hℳ₁_sub he₁))).2; omega)
      obtain ⟨v, hv⟩ := hne
      exact Finset.disjoint_left.mp hd hv hv
    have hM12_disj : ∀ e₁ ∈ ℳ₁ ∪ ℳ₂, ∀ e₂ ∈ ℳ₁ ∪ ℳ₂, e₁ ≠ e₂ → Disjoint e₁ e₂ := by
      intro e₁ h1 e₂ h2 hne
      rcases mem_union.mp h1 with h1a | h1b <;> rcases mem_union.mp h2 with h2a | h2b
      · exact hℳ₁_disj e₁ h1a e₂ h2a hne
      · exact hdisj_12 e₁ h1a e₂ (hℳ₂_sub h2b)
      · exact (hdisj_12 e₂ h2a e₁ (hℳ₂_sub h1b)).symm
      · exact hℳ₂_disj e₁ h1b e₂ h2b hne
    obtain ⟨ℳ_out, hℳ_out_sub, hℳ_out_disj, hℳ_out_card⟩ :=
      hpigeon (ℳ₁ ∪ ℳ₂) (union_subset hℳ₁_sub (hℳ₂_sub.trans hℰ_rem_sub)) hM12_disj
    refine ⟨ℳ_out, hℳ_out_sub, hℳ_out_disj, ?_⟩
    have hcard_u : ((ℳ₁ ∪ ℳ₂).card : ℝ) = (ℳ₁.card : ℝ) + (ℳ₂.card : ℝ) := by
      exact_mod_cast Finset.card_union_of_disjoint hdisj_M12
    have hrec : (ε * (1 - (r : ℝ) * ε)) / (ε + 4 * η₁) * (1 - (1 - ε - 4 * η₁) ^ (T + 1)) =
        ε * (1 - (r : ℝ) * ε) + c_T * (1 - ε - 4 * η₁) := by
      simp only [c_T, pow_succ]
      have hden : ε + 4 * η₁ ≠ 0 := by positivity
      field_simp; ring
    have hbig : (ε * (1 - (r : ℝ) * ε) + c_T * (1 - ε - 4 * η₁)) *
        ((W.card : ℝ) * ((ℰ.card : ℝ) / (D : ℝ))) ≤ (W.card : ℝ) * (ℳ_out.card : ℝ) := by
      have hcard_r : (ℰ_orig.card : ℝ) = (W.card : ℝ) * (ℰ.card : ℝ) := by exact_mod_cast hcard_orig
      have hrew : (W.card : ℝ) * ((ℰ.card : ℝ) / (D : ℝ)) = (ℰ_orig.card : ℝ) / (D : ℝ) := by
        rw [hcard_r]; ring
      rw [hrew]
      linarith
    have hW_pos : (0 : ℝ) < (W.card : ℝ) := by
      have : 0 < W.card := card_pos.mpr ⟨(⟨0, by omega⟩, 0), mem_univ _⟩
      exact_mod_cast this
    rw [hrec]
    nlinarith

lemma rodl_nibble_matching (r : ℕ) (hr : 2 ≤ r) (γ : ℝ) (hγ : 0 < γ) :
    ∃ β : ℝ, 0 < β ∧ ∃ D₀ : ℕ, 1 ≤ D₀ ∧
      ∀ {α : Type*} [DecidableEq α] (U : Finset α) (ℰ : Finset (Finset α)) (D : ℕ),
        D₀ ≤ D →
        (∀ e ∈ ℰ, e ⊆ U ∧ e.card = r) →
        (∀ x ∈ U, (ℰ.filter (fun e ↦ x ∈ e)).card ≤ D) →
        (∀ x ∈ U, ∀ y ∈ U, x ≠ y → ((ℰ.filter (fun e ↦ x ∈ e ∧ y ∈ e)).card : ℝ) ≤ β * (D : ℝ)) →
        ∃ ℳ : Finset (Finset α), ℳ ⊆ ℰ ∧
          (∀ e₁ ∈ ℳ, ∀ e₂ ∈ ℳ, e₁ ≠ e₂ → Disjoint e₁ e₂) ∧
          (1 - γ) * ((ℰ.card : ℝ) / (D : ℝ)) ≤ (ℳ.card : ℝ) := by
  let γ' : ℝ := min γ (1 / 2)
  have hγ'0 : 0 < γ' := lt_min hγ (by norm_num)
  have hγ'_le : γ' ≤ γ := min_le_left _ _
  let ε : ℝ := min (1 / (8 * (r : ℝ))) (γ' / (4 * ((r : ℝ) + 4)))
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hε0 : 0 < ε := lt_min (by positivity) (by positivity)
  have hε_small : 4 * (r : ℝ) * ε ≤ 1 := by
    have : ε ≤ 1 / (8 * (r : ℝ)) := min_le_left _ _
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * (r : ℝ))).mp this
    linarith
  have hε_γ : ((r : ℝ) + 4) * ε ≤ γ' / 4 := by
    have : ε ≤ γ' / (4 * ((r : ℝ) + 4)) := min_le_right _ _
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * ((r : ℝ) + 4))).mp this
    linarith
  let T : ℕ := Nat.ceil (2 / (γ' * ε))
  obtain ⟨β, hβ0, D₀, hD₀1, hspec⟩ := nibble_T_rounds r hr ε hε0 hε_small T
  refine ⟨β, hβ0, D₀, hD₀1, fun U ℰ D hD hunif hdeg hcodeg ↦ ?_⟩
  obtain ⟨ℳ, hℳ_sub, hℳ_disj, hℳ_card⟩ := hspec U ℰ D hD hunif hdeg hcodeg
  refine ⟨ℳ, hℳ_sub, hℳ_disj, ?_⟩
  let η₁ : ℝ := ε ^ 2
  have hε_le1 : ε ≤ 1 / 8 := by
    have : 2 ≤ (r : ℝ) := by exact_mod_cast hr
    nlinarith
  have hfrac : 1 - γ' / 4 ≤ (ε * (1 - (r : ℝ) * ε)) / (ε + 4 * η₁) := by
    rw [le_div_iff₀ (by positivity)]
    simp only [η₁]
    have : γ' / 4 * (4 * ε) ≥ 0 := by positivity
    nlinarith
  have hpow_le : (1 - ε - 4 * η₁) ^ T ≤ γ' / 2 := by
    have h1 : (1 - ε - 4 * η₁) ^ T ≤ (1 - ε) ^ T :=
      pow_le_pow_left₀ (by simp only [η₁]; nlinarith) (by simp only [η₁]; nlinarith) T
    have h2 : (1 - ε) ^ T * (1 + (T : ℝ) * ε) ≤ 1 :=
      pow_mul_one_add_le_one hε0.le (by linarith) T
    have hT : 2 / (γ' * ε) ≤ (T : ℝ) := Nat.le_ceil _
    have h3 : 2 / γ' ≤ 1 + (T : ℝ) * ε := by
      have : 2 ≤ (T : ℝ) * (γ' * ε) := (div_le_iff₀ (by positivity)).mp hT
      have : 2 / γ' ≤ (T : ℝ) * ε := (div_le_iff₀ hγ'0).mpr (by linarith)
      linarith
    have h4 : (1 - ε) ^ T * (2 / γ') ≤ 1 := by
      calc (1 - ε) ^ T * (2 / γ') ≤ (1 - ε) ^ T * (1 + (T : ℝ) * ε) :=
            mul_le_mul_of_nonneg_left h3 (pow_nonneg (by linarith) T)
        _ ≤ 1 := h2
    have h5 : (1 - ε) ^ T ≤ γ' / 2 := by
      have hpos : 0 < 2 / γ' := by positivity
      calc (1 - ε) ^ T ≤ 1 / (2 / γ') := (le_div_iff₀ hpos).mpr h4
        _ = γ' / 2 := by field_simp
    exact h1.trans h5
  have hc_ge : 1 - γ ≤ (ε * (1 - (r : ℝ) * ε)) / (ε + 4 * η₁) * (1 - (1 - ε - 4 * η₁) ^ T) := by
    have hprod : (1 - γ' / 4) * (1 - γ' / 2) ≤
        (ε * (1 - (r : ℝ) * ε)) / (ε + 4 * η₁) * (1 - (1 - ε - 4 * η₁) ^ T) :=
      mul_le_mul hfrac (by linarith) (by have : γ' ≤ 1 / 2 := min_le_right _ _; linarith)
        (div_nonneg (mul_nonneg hε0.le (by linarith)) (by positivity))
    have : 1 - γ' ≤ (1 - γ' / 4) * (1 - γ' / 2) := by nlinarith
    linarith
  exact (mul_le_mul_of_nonneg_right hc_ge
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))).trans hℳ_card

/- ### Section 4: Inductive `K_q` Graph Counting Lemma & Main Proof -/

lemma atypical_deg_card_lt {n m : ℕ} (hm : 1 ≤ m) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {ε p : ℝ} (hε : 0 < ε)
    {U V A B : Finset (Fin n)} (hU : U.card = m) (hV : V.card = m)
    (hA : A ⊆ U) (hB : B ⊆ V) (hB_sz : (m : ℝ) * ε ≤ (B.card : ℝ))
    (hunif : G.IsUniform ε U V) (hdens : |(G.edgeDensity U V : ℝ) - p| ≤ ε) :
    ((A.filter (fun u ↦ ((B.filter (G.Adj u)).card : ℝ) < (p - 2 * ε) * (B.card : ℝ))).card : ℝ) <
      (m : ℝ) * ε ∧
    ((A.filter (fun u ↦ (p + 2 * ε) * (B.card : ℝ) < ((B.filter (G.Adj u)).card : ℝ))).card : ℝ) <
      (m : ℝ) * ε := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hB_pos : (0 : ℝ) < (B.card : ℝ) := lt_of_lt_of_le (mul_pos hm_pos hε) hB_sz
  constructor <;> by_contra hge <;> push Not at hge
  · let S := A.filter (fun u ↦ ((B.filter (G.Adj u)).card : ℝ) < (p - 2 * ε) * (B.card : ℝ))
    have hS_pos : (0 : ℝ) < (S.card : ℝ) := lt_of_lt_of_le (mul_pos hm_pos hε) hge
    have hSB := hunif ((filter_subset _ _).trans hA) hB (hU.symm ▸ hge) (hV.symm ▸ hB_sz)
    have hd_gt : p - 2 * ε < (G.edgeDensity S B : ℝ) := by
      have h1 := (abs_lt.mp hSB).1
      have h2 := (abs_le.mp hdens).1
      linarith
    have hint_eq : ((G.interedges S B).card : ℝ) = ∑ u ∈ S, ((B.filter (G.Adj u)).card : ℝ) := by
      have hnat : (G.interedges S B).card = ∑ u ∈ S, (B.filter (G.Adj u)).card := by
        rw [SimpleGraph.interedges, Rel.interedges_eq_biUnion, Finset.card_biUnion]
        · refine sum_congr rfl fun u _ ↦ by rw [card_map]
        · intro u₁ _ u₂ _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro p hp₁ hp₂
          simp only [mem_map, Function.Embedding.coeFn_mk] at hp₁ hp₂
          obtain ⟨_, _, h1⟩ := hp₁; obtain ⟨_, _, h2⟩ := hp₂
          exact hne ((Prod.mk.inj (h1.trans h2.symm)).1)
      exact_mod_cast hnat
    have hint_lt : ((G.interedges S B).card : ℝ) < (p - 2 * ε) * ((S.card : ℝ) * (B.card : ℝ)) := by
      rw [hint_eq]
      have hSne : S.Nonempty := card_pos.mp (by exact_mod_cast hS_pos)
      calc ∑ u ∈ S, ((B.filter (G.Adj u)).card : ℝ)
          < ∑ _u ∈ S, ((p - 2 * ε) * (B.card : ℝ)) :=
            Finset.sum_lt_sum_of_nonempty hSne fun u hu ↦ (mem_filter.mp hu).2
        _ = (p - 2 * ε) * ((S.card : ℝ) * (B.card : ℝ)) := by simp; ring
    have hd_lt : (G.edgeDensity S B : ℝ) < p - 2 * ε := by
      have hrew : (G.edgeDensity S B : ℝ) =
          ((G.interedges S B).card : ℝ) / ((S.card : ℝ) * (B.card : ℝ)) := by
        simp only [SimpleGraph.edgeDensity, Rel.edgeDensity, SimpleGraph.interedges]
        push_cast; rfl
      rw [hrew, div_lt_iff₀ (mul_pos hS_pos hB_pos)]
      linarith
    linarith
  · let S := A.filter (fun u ↦ (p + 2 * ε) * (B.card : ℝ) < ((B.filter (G.Adj u)).card : ℝ))
    have hS_pos : (0 : ℝ) < (S.card : ℝ) := lt_of_lt_of_le (mul_pos hm_pos hε) hge
    have hSB := hunif ((filter_subset _ _).trans hA) hB (hU.symm ▸ hge) (hV.symm ▸ hB_sz)
    have hd_lt : (G.edgeDensity S B : ℝ) < p + 2 * ε := by
      have h1 := (abs_lt.mp hSB).2
      have h2 := (abs_le.mp hdens).2
      linarith
    have hint_eq : ((G.interedges S B).card : ℝ) = ∑ u ∈ S, ((B.filter (G.Adj u)).card : ℝ) := by
      have hnat : (G.interedges S B).card = ∑ u ∈ S, (B.filter (G.Adj u)).card := by
        rw [SimpleGraph.interedges, Rel.interedges_eq_biUnion, Finset.card_biUnion]
        · refine sum_congr rfl fun u _ ↦ by rw [card_map]
        · intro u₁ _ u₂ _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro p hp₁ hp₂
          simp only [mem_map, Function.Embedding.coeFn_mk] at hp₁ hp₂
          obtain ⟨_, _, h1⟩ := hp₁; obtain ⟨_, _, h2⟩ := hp₂
          exact hne ((Prod.mk.inj (h1.trans h2.symm)).1)
      exact_mod_cast hnat
    have hint_gt : (p + 2 * ε) * ((S.card : ℝ) * (B.card : ℝ)) < ((G.interedges S B).card : ℝ) := by
      rw [hint_eq]
      have hSne : S.Nonempty := card_pos.mp (by exact_mod_cast hS_pos)
      calc (p + 2 * ε) * ((S.card : ℝ) * (B.card : ℝ))
          = ∑ _u ∈ S, ((p + 2 * ε) * (B.card : ℝ)) := by simp; ring
        _ < ∑ u ∈ S, ((B.filter (G.Adj u)).card : ℝ) :=
            Finset.sum_lt_sum_of_nonempty hSne fun u hu ↦ (mem_filter.mp hu).2
    have hd_gt : p + 2 * ε < (G.edgeDensity S B : ℝ) := by
      have hrew : (G.edgeDensity S B : ℝ) =
          ((G.interedges S B).card : ℝ) / ((S.card : ℝ) * (B.card : ℝ)) := by
        simp only [SimpleGraph.edgeDensity, Rel.edgeDensity, SimpleGraph.interedges]
        push_cast; rfl
      rw [hrew, lt_div_iff₀ (mul_pos hS_pos hB_pos)]
      linarith
    linarith

set_option maxHeartbeats 800000 in
lemma clique_counting_lemma (k : ℕ) :
    ∀ (δ α γ : ℝ), 0 < δ → 0 < α → 0 < γ →
      ∃ ε : ℝ, 0 < ε ∧
        ∀ (n m : ℕ), 1 ≤ m → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
          (V A : Fin k → Finset (Fin n)) (p : ℝ),
          δ ≤ p → p ≤ 1 →
          (∀ i, (V i).card = m) →
          (∀ i, A i ⊆ V i) →
          (∀ i, α * (m : ℝ) ≤ ((A i).card : ℝ)) →
          (∀ i j, i ≠ j → G.IsUniform ε (V i) (V j) ∧
            |(G.edgeDensity (V i) (V j) : ℝ) - p| ≤ ε) →
          |(((Finset.univ : Finset (Fin k → Fin n)).filter
              (fun f ↦ (∀ i, f i ∈ A i) ∧ ∀ i j, i ≠ j → G.Adj (f i) (f j))).card : ℝ) -
            p ^ (k.choose 2) * ∏ i : Fin k, ((A i).card : ℝ)| ≤
            γ * ∏ i : Fin k, ((A i).card : ℝ) := by
  induction k with
  | zero =>
    intro δ α γ _ _ hγ
    refine ⟨1, zero_lt_one, fun n m _ G _ V A p _ _ _ _ _ _ ↦ ?_⟩
    have h1 : (Finset.univ : Finset (Fin 0 → Fin n)).filter
        (fun f ↦ (∀ i, f i ∈ A i) ∧ ∀ i j, i ≠ j → G.Adj (f i) (f j)) = Finset.univ := by
      ext f; simp
    rw [h1, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
    simp [hγ.le]
  | succ k ih =>
    intro δ α γ hδ hα hγ
    let γ' : ℝ := min γ 1 / 8
    have hγ'0 : 0 < γ' := by positivity
    let α' : ℝ := (δ / 2) * α
    have hα'0 : 0 < α' := by positivity
    obtain ⟨ε_ih, hε_ih0, hspec_ih⟩ := ih δ α' γ' hδ hα'0 hγ'0
    let ε : ℝ := min (min ε_ih (min (δ / 4) α))
      (min (γ' / (2 * ((k : ℝ) + 1) * (2 : ℝ) ^ k)) (γ' * α / (2 * ((k : ℝ) + 1))))
    have hε0 : 0 < ε := lt_min (lt_min hε_ih0 (lt_min (by positivity) hα))
      (lt_min (by positivity) (by positivity))
    refine ⟨ε, hε0, fun n m hm G _ V A p hpδ hp1 hVcard hAV hAsz hunif ↦ ?_⟩
    classical
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    have hε_ih : ε ≤ ε_ih := (min_le_left _ _).trans (min_le_left _ _)
    have hε_δ : ε ≤ δ / 4 := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hε_α : ε ≤ α := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hε_pow : 2 * ((k : ℝ) + 1) * (2 : ℝ) ^ k * ε ≤ γ' := by
      have h1 : ε ≤ γ' / (2 * ((k : ℝ) + 1) * (2 : ℝ) ^ k) :=
        (min_le_right _ _).trans (min_le_left _ _)
      have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ((k : ℝ) + 1) * (2 : ℝ) ^ k)).mp h1
      linarith
    have hε_bad : 2 * (k : ℝ) * ε / α ≤ γ' := by
      have h1 : ε ≤ γ' * α / (2 * ((k : ℝ) + 1)) :=
        (min_le_right _ _).trans (min_le_right _ _)
      have h2 : 2 * ((k : ℝ) + 1) * ε ≤ γ' * α := by
        have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ((k : ℝ) + 1))).mp h1
        linarith
      rw [div_le_iff₀ hα]; nlinarith
    -- Partition `transK` by `f 0 ∈ A 0`.
    let totK := (Finset.univ : Finset (Fin (k + 1) → Fin n)).filter
      (fun f ↦ (∀ i, f i ∈ A i) ∧ ∀ i j, i ≠ j → G.Adj (f i) (f j))
    let extK : Fin n → Finset (Fin k → Fin n) := fun v ↦
      (Finset.univ : Finset (Fin k → Fin n)).filter
        (fun g ↦ (∀ j, g j ∈ (A j.succ).filter (G.Adj v)) ∧ ∀ i j, i ≠ j → G.Adj (g i) (g j))
    have htot_sum : totK.card = ∑ v ∈ A 0, (extK v).card := by
      have hbi : totK.card = ((A 0).biUnion (fun v ↦
          (extK v).image (fun g ↦ Fin.cons (α := fun _ ↦ Fin n) v g))).card := by
        congr 1; ext f
        simp only [totK, mem_filter, mem_univ, true_and, mem_biUnion, mem_image, extK]
        constructor
        · rintro ⟨hfA, hfAdj⟩
          refine ⟨f 0, hfA 0, fun j ↦ f j.succ, ⟨fun j ↦ ⟨hfA j.succ,
            hfAdj 0 j.succ (Fin.succ_ne_zero j).symm⟩,
            fun i j hij ↦ hfAdj i.succ j.succ (fun h ↦ hij (Fin.succ_injective _ h))⟩, ?_⟩
          funext i; cases i using Fin.cases with
          | zero => simp
          | succ j => simp
        · rintro ⟨v, hvA, g, ⟨hg1, hg2⟩, rfl⟩
          refine ⟨fun i ↦ ?_, fun i j hij ↦ ?_⟩
          · cases i using Fin.cases with
            | zero => simpa using hvA
            | succ j => simpa using (hg1 j).1
          · cases i using Fin.cases with
            | zero =>
              cases j using Fin.cases with
              | zero => exact absurd rfl hij
              | succ j' => simpa using (hg1 j').2
            | succ i' =>
              cases j using Fin.cases with
              | zero => simpa using (hg1 i').2.symm
              | succ j' => simpa using hg2 i' j' (fun h ↦ hij (congrArg Fin.succ h))
      rw [hbi, Finset.card_biUnion]
      · refine sum_congr rfl fun v _ ↦ Finset.card_image_of_injective _ (fun g₁ g₂ h ↦ by
          funext j; have := congr_fun h j.succ; simpa using this)
      · intro v₁ _ v₂ _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro f h1 h2
        obtain ⟨g₁, _, rfl⟩ := mem_image.mp h1
        obtain ⟨g₂, _, heq⟩ := mem_image.mp h2
        have := congr_fun heq 0
        simpa using hne this.symm
    -- Good vertices `Good ⊆ A 0`.
    let Good : Finset (Fin n) := (A 0).filter (fun v ↦ ∀ j : Fin k,
      (p - 2 * ε) * ((A j.succ).card : ℝ) ≤ (((A j.succ).filter (G.Adj v)).card : ℝ) ∧
      (((A j.succ).filter (G.Adj v)).card : ℝ) ≤ (p + 2 * ε) * ((A j.succ).card : ℝ))
    let Bad : Finset (Fin n) := (A 0) \ Good
    have hBad_card : (Bad.card : ℝ) ≤ 2 * (k : ℝ) * ε * (m : ℝ) := by
      have hsubB : Bad ⊆ (Finset.univ : Finset (Fin k)).biUnion (fun j ↦
          (A 0).filter (fun v ↦ (((A j.succ).filter (G.Adj v)).card : ℝ) <
            (p - 2 * ε) * ((A j.succ).card : ℝ)) ∪
          (A 0).filter (fun v ↦ (p + 2 * ε) * ((A j.succ).card : ℝ) <
            (((A j.succ).filter (G.Adj v)).card : ℝ))) := by
        intro v hv
        obtain ⟨hvA, hnotG⟩ := mem_sdiff.mp hv
        simp only [Good, mem_filter, hvA, true_and, not_forall, not_and_or, not_le] at hnotG
        obtain ⟨j, hj | hj⟩ := hnotG
        · exact mem_biUnion.mpr ⟨j, mem_univ j, mem_union_left _ (mem_filter.mpr ⟨hvA, hj⟩)⟩
        · exact mem_biUnion.mpr ⟨j, mem_univ j, mem_union_right _ (mem_filter.mpr ⟨hvA, hj⟩)⟩
      have h1 : (Bad.card : ℝ) ≤ ∑ j : Fin k,
          ((((A 0).filter (fun v ↦ (((A j.succ).filter (G.Adj v)).card : ℝ) <
              (p - 2 * ε) * ((A j.succ).card : ℝ))).card : ℝ) +
          (((A 0).filter (fun v ↦ (p + 2 * ε) * ((A j.succ).card : ℝ) <
              (((A j.succ).filter (G.Adj v)).card : ℝ))).card : ℝ)) := by
        have hnat : Bad.card ≤ ∑ j : Fin k,
            (((A 0).filter (fun v ↦ (((A j.succ).filter (G.Adj v)).card : ℝ) <
                (p - 2 * ε) * ((A j.succ).card : ℝ))).card +
            ((A 0).filter (fun v ↦ (p + 2 * ε) * ((A j.succ).card : ℝ) <
                (((A j.succ).filter (G.Adj v)).card : ℝ))).card) :=
          (card_le_card hsubB).trans (card_biUnion_le.trans (sum_le_sum fun j _ ↦ card_union_le _ _))
        exact_mod_cast hnat
      calc (Bad.card : ℝ) ≤ ∑ _j : Fin k, (2 * ε * (m : ℝ)) := h1.trans (sum_le_sum fun j _ ↦ by
            have hBsz : (m : ℝ) * ε ≤ ((A j.succ).card : ℝ) :=
              (mul_le_mul_of_nonneg_left hε_α hm_pos.le).trans (by rw [mul_comm]; exact hAsz j.succ)
            have hat := atypical_deg_card_lt hm G hε0 (hVcard 0) (hVcard j.succ) (hAV 0) (hAV j.succ)
              hBsz (hunif 0 j.succ (Fin.succ_ne_zero j).symm).1
              (hunif 0 j.succ (Fin.succ_ne_zero j).symm).2
            linarith)
        _ = 2 * (k : ℝ) * ε * (m : ℝ) := by simp; ring
    have hBad_frac : (Bad.card : ℝ) ≤ γ' * ((A 0).card : ℝ) := by
      have h1 : (m : ℝ) ≤ ((A 0).card : ℝ) / α := (le_div_iff₀ hα).mpr (by linarith [hAsz 0])
      calc (Bad.card : ℝ) ≤ 2 * (k : ℝ) * ε * (m : ℝ) := hBad_card
        _ ≤ 2 * (k : ℝ) * ε * (((A 0).card : ℝ) / α) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (2 * (k : ℝ) * ε / α) * ((A 0).card : ℝ) := by ring
        _ ≤ γ' * ((A 0).card : ℝ) := mul_le_mul_of_nonneg_right hε_bad (Nat.cast_nonneg _)
    -- Apply IH to every `v ∈ Good`!
    let P_rest : ℝ := ∏ j : Fin k, ((A j.succ).card : ℝ)
    have hP_tot : ∏ i : Fin (k + 1), ((A i).card : ℝ) = ((A 0).card : ℝ) * P_rest :=
      Fin.prod_univ_succ _
    have hP_rest_nn : 0 ≤ P_rest := Finset.prod_nonneg fun _ _ ↦ Nat.cast_nonneg _
    have hp_sub_nn : 0 ≤ p - 2 * ε := by linarith
    have hp_add_le2 : p + 2 * ε ≤ 2 := by
      have : ε ≤ 1 / 4 := hε_δ.trans (by linarith)
      linarith
    have hpow_lo : p ^ k - γ' ≤ (p - 2 * ε) ^ k := by
      have habs := abs_pow_sub_pow_le (a := p) (b := p - 2 * ε)
        (by linarith) (by linarith) hp_sub_nn (by linarith) k
      have h1 : |p - (p - 2 * ε)| = 2 * ε := by rw [show p - (p - 2 * ε) = 2 * ε by ring, abs_of_pos (by positivity)]
      rw [h1] at habs
      have h2 : (k : ℝ) * (2 : ℝ) ^ k * (2 * ε) ≤ γ' := by
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k]
      linarith [(abs_le.mp habs).2]
    have hpow_hi : (p + 2 * ε) ^ k ≤ p ^ k + γ' := by
      have habs := abs_pow_sub_pow_le (a := p + 2 * ε) (b := p)
        (by linarith) hp_add_le2 (by linarith) (by linarith) k
      have h1 : |p + 2 * ε - p| = 2 * ε := by rw [show p + 2 * ε - p = 2 * ε by ring, abs_of_pos (by positivity)]
      rw [h1] at habs
      have h2 : (k : ℝ) * (2 : ℝ) ^ k * (2 * ε) ≤ γ' := by
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k]
      linarith [(abs_le.mp habs).2]
    have hGood_est : ∀ v ∈ Good,
        (p ^ (k.choose 2) - γ') * (p - 2 * ε) ^ k * P_rest ≤ ((extK v).card : ℝ) ∧
        ((extK v).card : ℝ) ≤ (p ^ (k.choose 2) + γ') * (p + 2 * ε) ^ k * P_rest := by
      intro v hv
      have hv_deg := (mem_filter.mp hv).2
      let A_v : Fin k → Finset (Fin n) := fun j ↦ (A j.succ).filter (G.Adj v)
      have hAv_sub : ∀ j : Fin k, A_v j ⊆ V j.succ := fun j ↦ (filter_subset _ _).trans (hAV j.succ)
      have hAv_sz : ∀ j : Fin k, α' * (m : ℝ) ≤ ((A_v j).card : ℝ) := by
        intro j
        have h1 : δ / 2 ≤ p - 2 * ε := by linarith
        calc α' * (m : ℝ) = (δ / 2) * (α * (m : ℝ)) := by simp only [α']; ring
          _ ≤ (p - 2 * ε) * ((A j.succ).card : ℝ) :=
              mul_le_mul h1 (hAsz j.succ) (by positivity) hp_sub_nn
          _ ≤ ((A_v j).card : ℝ) := (hv_deg j).1
      have hIH_v := hspec_ih n m hm G (fun j ↦ V j.succ) A_v p hpδ hp1
        (fun j ↦ hVcard j.succ) hAv_sub hAv_sz (fun i j hij ↦
          let h := hunif i.succ j.succ (fun h ↦ hij (Fin.succ_injective _ h))
          ⟨h.1.mono hε_ih, h.2.trans hε_ih⟩)
      have hprod_lo : (p - 2 * ε) ^ k * P_rest ≤ ∏ j : Fin k, ((A_v j).card : ℝ) := by
        calc (p - 2 * ε) ^ k * P_rest
            = ∏ j : Fin k, ((p - 2 * ε) * ((A j.succ).card : ℝ)) := by
              rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          _ ≤ ∏ j : Fin k, ((A_v j).card : ℝ) :=
              Finset.prod_le_prod (fun j _ ↦ by positivity) (fun j _ ↦ (hv_deg j).1)
      have hprod_hi : ∏ j : Fin k, ((A_v j).card : ℝ) ≤ (p + 2 * ε) ^ k * P_rest := by
        calc ∏ j : Fin k, ((A_v j).card : ℝ)
            ≤ ∏ j : Fin k, ((p + 2 * ε) * ((A j.succ).card : ℝ)) :=
              Finset.prod_le_prod (fun j _ ↦ Nat.cast_nonneg _) (fun j _ ↦ (hv_deg j).2)
          _ = (p + 2 * ε) ^ k * P_rest := by
              rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have hlo := (abs_le.mp hIH_v).1
      have hhi := (abs_le.mp hIH_v).2
      constructor
      · by_cases hpos : 0 ≤ p ^ (k.choose 2) - γ'
        · calc (p ^ (k.choose 2) - γ') * (p - 2 * ε) ^ k * P_rest
              = (p ^ (k.choose 2) - γ') * ((p - 2 * ε) ^ k * P_rest) := by ring
            _ ≤ (p ^ (k.choose 2) - γ') * ∏ j : Fin k, ((A_v j).card : ℝ) :=
                mul_le_mul_of_nonneg_left hprod_lo hpos
            _ ≤ ((extK v).card : ℝ) := by linarith
        · push Not at hpos
          have h1 : (p ^ (k.choose 2) - γ') * (p - 2 * ε) ^ k * P_rest ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg
              (mul_nonpos_of_nonpos_of_nonneg hpos.le (pow_nonneg hp_sub_nn k)) hP_rest_nn
          exact h1.trans (Nat.cast_nonneg _)
      · calc ((extK v).card : ℝ)
            ≤ (p ^ (k.choose 2) + γ') * ∏ j : Fin k, ((A_v j).card : ℝ) := by linarith
          _ ≤ (p ^ (k.choose 2) + γ') * ((p + 2 * ε) ^ k * P_rest) :=
              mul_le_mul_of_nonneg_left hprod_hi (add_nonneg (pow_nonneg (by linarith) _) hγ'0.le)
          _ = (p ^ (k.choose 2) + γ') * (p + 2 * ε) ^ k * P_rest := by ring
    -- Trivial upper bound `((extK v).card : ℝ) ≤ P_rest` for `v ∈ Bad`.
    have hBad_est : ∀ v ∈ Bad, ((extK v).card : ℝ) ≤ P_rest := by
      intro v _
      have hsub_triv : extK v ⊆ Fintype.piFinset (fun j : Fin k ↦ A j.succ) := by
        intro g hg
        rw [Fintype.mem_piFinset]
        intro j
        exact (mem_filter.mp ((mem_filter.mp hg).2.1 j)).1
      have hcard_le : (extK v).card ≤ ∏ j : Fin k, (A j.succ).card :=
        (card_le_card hsub_triv).trans (Fintype.card_piFinset _).le
      change ((extK v).card : ℝ) ≤ ∏ j : Fin k, ((A j.succ).card : ℝ)
      exact_mod_cast hcard_le
    -- Combine `Good` and `Bad` sums!
    have hchoose : (k + 1).choose 2 = k.choose 2 + k := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
    have hpow_succ : p ^ ((k + 1).choose 2) = p ^ (k.choose 2) * p ^ k := by
      rw [hchoose, pow_add]
    have hGood_sub : Good ⊆ A 0 := filter_subset _ (A 0)
    have hGood_card : ((A 0).card : ℝ) - (Bad.card : ℝ) = (Good.card : ℝ) := by
      have := Finset.card_sdiff_add_card_eq_card hGood_sub
      have : (Bad.card : ℝ) + (Good.card : ℝ) = ((A 0).card : ℝ) := by exact_mod_cast this
      linarith
    have hsum_split : (totK.card : ℝ) =
        ∑ v ∈ Good, ((extK v).card : ℝ) + ∑ v ∈ Bad, ((extK v).card : ℝ) := by
      have : totK.card = ∑ v ∈ Good, (extK v).card + ∑ v ∈ Bad, (extK v).card := by
        rw [htot_sum, ← Finset.sum_sdiff hGood_sub, add_comm]
      exact_mod_cast this
    have hγ'_le1 : γ' ≤ 1 / 8 := by
      have : min γ 1 ≤ 1 := min_le_right _ _
      simp only [γ']; linarith
    have h8γ' : 8 * γ' ≤ γ := by
      have : min γ 1 ≤ γ := min_le_left _ _
      simp only [γ']; linarith
    have hp_pow_le1 : p ^ (k.choose 2) ≤ 1 := pow_le_one₀ (by linarith) hp1
    have hp_k_le1 : p ^ k ≤ 1 := pow_le_one₀ (by linarith) hp1
    rw [hP_tot, abs_le]
    constructor
    · -- Lower bound: `totK.card ≥ (p^{C(k+1,2)} - γ) * P_tot`.
      have hlo1 : (Good.card : ℝ) * ((p ^ (k.choose 2) - γ') * (p - 2 * ε) ^ k * P_rest) ≤
          (totK.card : ℝ) := by
        rw [hsum_split]
        have h1 : (Good.card : ℝ) * ((p ^ (k.choose 2) - γ') * (p - 2 * ε) ^ k * P_rest) ≤
            ∑ v ∈ Good, ((extK v).card : ℝ) := by
          calc _ = ∑ _v ∈ Good, ((p ^ (k.choose 2) - γ') * (p - 2 * ε) ^ k * P_rest) := by simp
            _ ≤ ∑ v ∈ Good, ((extK v).card : ℝ) := sum_le_sum fun v hv ↦ (hGood_est v hv).1
        have h2 : 0 ≤ ∑ v ∈ Bad, ((extK v).card : ℝ) := sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
        linarith
      have hcoeff : p ^ ((k + 1).choose 2) - 4 * γ' ≤
          (1 - γ') * ((p ^ (k.choose 2) - γ') * (p - 2 * ε) ^ k) := by
        rw [hpow_succ]
        have h1 : p ^ (k.choose 2) * p ^ k - 2 * γ' ≤ (p ^ (k.choose 2) - γ') * (p - 2 * ε) ^ k := by
          have : (p - 2 * ε) ^ k ≤ 1 := pow_le_one₀ hp_sub_nn (by linarith)
          nlinarith [pow_nonneg (show 0 ≤ p by linarith) (k.choose 2),
            pow_nonneg (show 0 ≤ p by linarith) k]
        have h2 : (1 - γ') * (p ^ (k.choose 2) * p ^ k - 2 * γ') ≤
            (1 - γ') * ((p ^ (k.choose 2) - γ') * (p - 2 * ε) ^ k) :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
        have : p ^ (k.choose 2) * p ^ k ≤ 1 :=
          mul_le_one₀ hp_pow_le1 (pow_nonneg (by linarith) _) hp_k_le1
        nlinarith
      have hG_ge : (1 - γ') * ((A 0).card : ℝ) ≤ (Good.card : ℝ) := by linarith
      by_cases hnn : 0 ≤ (p ^ (k.choose 2) - γ') * (p - 2 * ε) ^ k
      · have hA0_prod : (p ^ ((k + 1).choose 2) - γ) * (((A 0).card : ℝ) * P_rest) ≤
            (Good.card : ℝ) * ((p ^ (k.choose 2) - γ') * (p - 2 * ε) ^ k * P_rest) := by
          calc (p ^ ((k + 1).choose 2) - γ) * (((A 0).card : ℝ) * P_rest)
              ≤ (p ^ ((k + 1).choose 2) - 4 * γ') * (((A 0).card : ℝ) * P_rest) :=
                mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (Nat.cast_nonneg _) hP_rest_nn)
            _ ≤ ((1 - γ') * ((p ^ (k.choose 2) - γ') * (p - 2 * ε) ^ k)) *
                  (((A 0).card : ℝ) * P_rest) :=
                mul_le_mul_of_nonneg_right hcoeff (mul_nonneg (Nat.cast_nonneg _) hP_rest_nn)
            _ = ((1 - γ') * ((A 0).card : ℝ)) *
                  ((p ^ (k.choose 2) - γ') * (p - 2 * ε) ^ k * P_rest) := by ring
            _ ≤ (Good.card : ℝ) * ((p ^ (k.choose 2) - γ') * (p - 2 * ε) ^ k * P_rest) :=
                mul_le_mul_of_nonneg_right hG_ge (mul_nonneg hnn hP_rest_nn)
        linarith
      · push Not at hnn
        have hneg1 : (1 - γ') * ((p ^ (k.choose 2) - γ') * (p - 2 * ε) ^ k) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by linarith) hnn.le
        have hlt0 : p ^ ((k + 1).choose 2) - γ ≤ 0 := by linarith
        have h1 : (p ^ ((k + 1).choose 2) - γ) * (((A 0).card : ℝ) * P_rest) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hlt0 (mul_nonneg (Nat.cast_nonneg _) hP_rest_nn)
        linarith [Nat.cast_nonneg (α := ℝ) totK.card]
    · -- Upper bound: `totK.card ≤ (p^{C(k+1,2)} + γ) * P_tot`.
      have hhi1 : (totK.card : ℝ) ≤
          ((A 0).card : ℝ) * ((p ^ (k.choose 2) + γ') * (p + 2 * ε) ^ k * P_rest) +
          (Bad.card : ℝ) * P_rest := by
        rw [hsum_split]
        have h1 : ∑ v ∈ Good, ((extK v).card : ℝ) ≤
            (Good.card : ℝ) * ((p ^ (k.choose 2) + γ') * (p + 2 * ε) ^ k * P_rest) := by
          calc ∑ v ∈ Good, ((extK v).card : ℝ)
              ≤ ∑ _v ∈ Good, ((p ^ (k.choose 2) + γ') * (p + 2 * ε) ^ k * P_rest) :=
                sum_le_sum fun v hv ↦ (hGood_est v hv).2
            _ = _ := by simp
        have h1' : (Good.card : ℝ) * ((p ^ (k.choose 2) + γ') * (p + 2 * ε) ^ k * P_rest) ≤
            ((A 0).card : ℝ) * ((p ^ (k.choose 2) + γ') * (p + 2 * ε) ^ k * P_rest) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_card (filter_subset _ _))
            (mul_nonneg (mul_nonneg (add_nonneg (pow_nonneg (by linarith) _) hγ'0.le)
              (pow_nonneg (by linarith) _)) hP_rest_nn)
        have h2 : ∑ v ∈ Bad, ((extK v).card : ℝ) ≤ (Bad.card : ℝ) * P_rest := by
          calc ∑ v ∈ Bad, ((extK v).card : ℝ)
              ≤ ∑ _v ∈ Bad, P_rest := sum_le_sum hBad_est
            _ = (Bad.card : ℝ) * P_rest := by simp
        linarith
      have hcoeff : (p ^ (k.choose 2) + γ') * (p + 2 * ε) ^ k + γ' ≤ p ^ ((k + 1).choose 2) + 4 * γ' := by
        rw [hpow_succ]
        have h1 : (p ^ (k.choose 2) + γ') * (p + 2 * ε) ^ k ≤
            (p ^ (k.choose 2) + γ') * (p ^ k + γ') :=
          mul_le_mul_of_nonneg_left hpow_hi (add_nonneg (pow_nonneg (by linarith) _) hγ'0.le)
        nlinarith
      have hbad_p : (Bad.card : ℝ) * P_rest ≤ γ' * (((A 0).card : ℝ) * P_rest) := by
        have := mul_le_mul_of_nonneg_right hBad_frac hP_rest_nn
        linarith
      calc (totK.card : ℝ) - p ^ ((k + 1).choose 2) * (((A 0).card : ℝ) * P_rest)
          ≤ (((p ^ (k.choose 2) + γ') * (p + 2 * ε) ^ k + γ') - p ^ ((k + 1).choose 2)) *
              (((A 0).card : ℝ) * P_rest) := by linarith
        _ ≤ (4 * γ') * (((A 0).card : ℝ) * P_rest) :=
            mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (Nat.cast_nonneg _) hP_rest_nn)
        _ ≤ γ * (((A 0).card : ℝ) * P_rest) :=
            mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (Nat.cast_nonneg _) hP_rest_nn)

set_option maxHeartbeats 1600000 in
theorem main_aux : OMA.R_Erdos81_erdos_81_R1_H2_R1.H2 := by
  intro q hq δ hδ η hη
  classical
  -- Handle `1 ≤ η` or `1 < δ` trivially (`𝒬 = ∅`).
  by_cases htriv : 1 ≤ η ∨ 1 < δ
  · refine ⟨1, zero_lt_one, 1, fun n m _ G _ V _ _ p hpδ hp1 _ ↦ ⟨∅, by simp, by simp, ?_⟩⟩
    rcases htriv with hη1 | hδ1
    · have : p - η ≤ 0 := by linarith
      simpa using mul_nonpos_of_nonpos_of_nonneg this (sq_nonneg (m : ℝ))
    · linarith
  push Not at htriv
  obtain ⟨hη1, hδ1⟩ := htriv
  let r : ℕ := q.choose 2
  have hr3 : 3 ≤ r := by
    simp only [r, Nat.choose_two_right]
    have : 3 * (3 - 1) ≤ q * (q - 1) := Nat.mul_le_mul hq (by omega)
    omega
  have hr2 : 2 ≤ r := by omega
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  -- Step 1: Choose parameters from `rodl_nibble_matching` and `clique_counting_lemma`.
  let γ_nib : ℝ := η / 4
  have hγ_nib0 : 0 < γ_nib := by positivity
  obtain ⟨β, hβ0, D₀, hD₀1, hnibble⟩ := rodl_nibble_matching r hr2 γ_nib hγ_nib0
  let γ_D : ℝ := η * δ ^ (r - 1) / 16
  have hγ_D0 : 0 < γ_D := by positivity
  let γ_cnt : ℝ := min (η * δ ^ r / 16) (γ_D / 4)
  have hγ_cnt0 : 0 < γ_cnt := lt_min (by positivity) (by positivity)
  obtain ⟨ε_q, hε_q0, hcnt_q⟩ := clique_counting_lemma q δ 1 γ_cnt hδ zero_lt_one hγ_cnt0
  let α_q2 : ℝ := δ ^ 2 / 4
  have hα_q20 : 0 < α_q2 := by positivity
  obtain ⟨ε_q2, hε_q20, hcnt_q2⟩ := clique_counting_lemma (q - 2) δ α_q2 γ_cnt hδ hα_q20 hγ_cnt0
  -- Choose `ε₁ > 0` small enough for both counting lemmas and atypical edge count.
  let ε₁ : ℝ := min (min ε_q ε_q2)
    (min (min (δ / 4) (γ_cnt / (8 * (q : ℝ) * (r : ℝ) + 1)))
      (γ_D / (16 * (q : ℝ) * (2 : ℝ) ^ (2 * q) + 1)))
  have hε₁0 : 0 < ε₁ := lt_min (lt_min hε_q0 hε_q20)
    (lt_min (lt_min (by positivity) (by positivity)) (by positivity))
  have hε₁_q : ε₁ ≤ ε_q := (min_le_left _ _).trans (min_le_left _ _)
  have hε₁_q2 : ε₁ ≤ ε_q2 := (min_le_left _ _).trans (min_le_right _ _)
  have hε₁_δ : ε₁ ≤ δ / 4 := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hε₁_bad : 4 * (q : ℝ) * (r : ℝ) * ε₁ ≤ γ_cnt := by
    have h1 : ε₁ ≤ γ_cnt / (8 * (q : ℝ) * (r : ℝ) + 1) :=
      (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * (q : ℝ) * (r : ℝ) + 1)).mp h1
    nlinarith
  have hε₁_pow : 4 * (q : ℝ) * (2 : ℝ) ^ (2 * (q - 2)) * ε₁ ≤ γ_D / 4 := by
    have h1 : ε₁ ≤ γ_D / (16 * (q : ℝ) * (2 : ℝ) ^ (2 * q) + 1) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have h2 : (16 * (q : ℝ) * (2 : ℝ) ^ (2 * q) + 1) * ε₁ ≤ γ_D := by
      have := (le_div_iff₀ (by positivity : (0 : ℝ) < 16 * (q : ℝ) * (2 : ℝ) ^ (2 * q) + 1)).mp h1
      linarith
    have h2pow : (2 : ℝ) ^ (2 * (q - 2)) ≤ (2 : ℝ) ^ (2 * q) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h3 : 4 * (q : ℝ) * (2 : ℝ) ^ (2 * (q - 2)) * ε₁ ≤
        4 * (q : ℝ) * (2 : ℝ) ^ (2 * q) * ε₁ := by
      have hmul := mul_le_mul_of_nonneg_left h2pow (by positivity : (0 : ℝ) ≤ 4 * (q : ℝ))
      exact mul_le_mul_of_nonneg_right hmul hε₁0.le
    linarith
  -- Choose `m₀ : ℕ`.
  let m₀ : ℕ := max (max 1 (Nat.ceil ((D₀ : ℝ) / δ ^ (r - 1))))
    (max (Nat.ceil (1 / (β * δ ^ (r - 1)))) (Nat.ceil (1 / γ_D)))
  refine ⟨ε₁, hε₁0, m₀, fun n m hm G _ V hV_disj hV_card p hpδ hp1 hunif ↦ ?_⟩
  have hm1 : 1 ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hp0 : 0 < p := lt_of_lt_of_le hδ hpδ
  have hq2_ge1 : 1 ≤ q - 2 := by omega
  have hm_ge_q2 : (m : ℝ) ≤ (m : ℝ) ^ (q - 2) := by
    calc (m : ℝ) = (m : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (m : ℝ) ^ (q - 2) := pow_le_pow_right₀ (by exact_mod_cast hm1) hq2_ge1
  -- Step 2: Define transversal edges `U` and transversal `q`-cliques `allK`.
  let U : Finset (Sym2 (Fin n)) :=
    G.edgeFinset.filter (fun e ↦ ∃ i j : Fin q, i ≠ j ∧ ∃ u ∈ V i, ∃ v ∈ V j, e = s(u, v))
  let transF : Finset (Fin q → Fin n) :=
    Finset.univ.filter (fun f ↦ (∀ i, f i ∈ V i) ∧ ∀ i j, i ≠ j → G.Adj (f i) (f j))
  let cliqueOf : (Fin q → Fin n) → Finset (Fin n) := fun f ↦ Finset.univ.image f
  let edgesOf : Finset (Fin n) → Finset (Sym2 (Fin n)) := fun Q ↦
    G.edgeFinset.filter (fun e ↦ ∀ x ∈ e, x ∈ Q)
  have hf_inj : ∀ f ∈ transF, Function.Injective f := by
    intro f hf i j hij
    by_contra hne
    exact Finset.disjoint_left.mp (hV_disj i j hne) ((mem_filter.mp hf).2.1 i)
      (hij ▸ (mem_filter.mp hf).2.1 j)
  have hcl_props : ∀ f ∈ transF,
      (cliqueOf f).card = q ∧ G.IsClique ((cliqueOf f) : Set (Fin n)) ∧
      (∀ i : Fin q, (cliqueOf f ∩ V i).card = 1) ∧
      edgesOf (cliqueOf f) ⊆ U ∧ (edgesOf (cliqueOf f)).card = r := by
    intro f hf
    have hf1 := (mem_filter.mp hf).2.1
    have hf2 := (mem_filter.mp hf).2.2
    have hcard : (cliqueOf f).card = q := by
      rw [Finset.card_image_of_injective _ (hf_inj f hf), card_univ, Fintype.card_fin]
    have hcl : G.IsClique ((cliqueOf f) : Set (Fin n)) := by
      intro u hu v hv huv
      obtain ⟨i, _, rfl⟩ := mem_image.mp (mem_coe.mp hu)
      obtain ⟨j, _, rfl⟩ := mem_image.mp (mem_coe.mp hv)
      exact hf2 i j (fun h ↦ huv (congrArg f h))
    have htrans : ∀ i : Fin q, (cliqueOf f ∩ V i).card = 1 := by
      intro i
      rw [Finset.card_eq_one]
      refine ⟨f i, ?_⟩
      ext x
      simp only [mem_inter, mem_singleton, cliqueOf, mem_image, mem_univ, true_and]
      constructor
      · rintro ⟨⟨j, rfl⟩, hxi⟩
        have hij : j = i := by
          by_contra hne
          exact Finset.disjoint_left.mp (hV_disj j i hne) (hf1 j) hxi
        rw [hij]
      · rintro rfl; exact ⟨⟨i, rfl⟩, hf1 i⟩
    have hesub : edgesOf (cliqueOf f) ⊆ U := by
      intro e he
      obtain ⟨heG, heQ⟩ := mem_filter.mp he
      have hadj : e ∈ G.edgeSet := mem_edgeFinset.mp heG
      induction e using Sym2.ind with
      | h u v =>
        obtain ⟨i, _, rfl⟩ := mem_image.mp (heQ u (by simp))
        obtain ⟨j, _, rfl⟩ := mem_image.mp (heQ v (by simp))
        exact mem_filter.mpr ⟨heG, i, j, fun h ↦ G.ne_of_adj hadj (congrArg f h),
          f i, hf1 i, f j, hf1 j, rfl⟩
    have hecard : (edgesOf (cliqueOf f)).card = r := by
      have hbij : (edgesOf (cliqueOf f)).card = ((cliqueOf f).powersetCard 2).card := by
        refine Finset.card_bij (fun e _ ↦ e.toFinset) ?_ ?_ ?_
        · intro e he
          obtain ⟨heG, heQ⟩ := mem_filter.mp he
          have hadj : e ∈ G.edgeSet := mem_edgeFinset.mp heG
          induction e using Sym2.ind with
          | h a b =>
            rw [mem_powersetCard, Sym2.toFinset_mk_eq, card_pair (G.ne_of_adj hadj)]
            refine ⟨fun x hx ↦ heQ x (by simpa [Sym2.mem_iff] using hx), rfl⟩
        · intro e₁ he₁ e₂ he₂ heq
          have h1 := G.not_isDiag_of_mem_edgeSet (mem_edgeFinset.mp (mem_filter.mp he₁).1)
          have h2 := G.not_isDiag_of_mem_edgeSet (mem_edgeFinset.mp (mem_filter.mp he₂).1)
          induction e₁ using Sym2.ind with
          | h a b =>
            induction e₂ using Sym2.ind with
            | h c d =>
              have hab : a ≠ b := by simpa [Sym2.mk_isDiag_iff] using h1
              rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq] at heq
              have ha : a ∈ ({c, d} : Finset (Fin n)) := heq ▸ mem_insert_self a {b}
              have hb : b ∈ ({c, d} : Finset (Fin n)) := heq ▸ mem_insert_of_mem (mem_singleton_self b)
              simp only [mem_insert, mem_singleton] at ha hb
              rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
              · exact absurd rfl hab
              · rfl
              · exact Sym2.eq_swap
              · exact absurd rfl hab
        · intro s hs
          rw [mem_powersetCard] at hs
          obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hs.2
          have ha := hs.1 (mem_insert_self a {b})
          have hb := hs.1 (mem_insert_of_mem (mem_singleton_self b))
          refine ⟨s(a, b), mem_filter.mpr ⟨mem_edgeFinset.mpr (hcl ha hb hab),
            fun x hx ↦ by rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption⟩,
            Sym2.toFinset_mk_eq⟩
      rw [hbij, card_powersetCard, hcard]
    exact ⟨hcard, hcl, htrans, hesub, hecard⟩
  -- `f ↦ edgesOf (cliqueOf f)` is injective on `transF`!
  have hedges_inj : Set.InjOn (fun f ↦ edgesOf (cliqueOf f)) (transF : Set (Fin q → Fin n)) := by
    intro f₁ hf₁ f₂ hf₂ heq
    dsimp only at heq
    ext i
    have hne : (Finset.univ.erase i).Nonempty :=
      card_pos.mp (by rw [card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]; omega)
    obtain ⟨j, hj⟩ := hne
    have hij : i ≠ j := (mem_erase.mp hj).1.symm
    have hmem : s(f₁ i, f₁ j) ∈ edgesOf (cliqueOf f₂) := by
      rw [← heq]
      refine mem_filter.mpr ⟨mem_edgeFinset.mpr ((mem_filter.mp (mem_coe.mp hf₁)).2.2 i j hij),
        fun x hx ↦ ?_⟩
      rcases Sym2.mem_iff.mp hx with rfl | rfl
      · exact mem_image_of_mem _ (mem_univ i)
      · exact mem_image_of_mem _ (mem_univ j)
    have hfi_in : f₁ i ∈ cliqueOf f₂ := (mem_filter.mp hmem).2 (f₁ i) (by simp)
    obtain ⟨i', _, hi'⟩ := mem_image.mp hfi_in
    have hii' : i' = i := by
      by_contra hne'
      exact Finset.disjoint_left.mp (hV_disj i' i hne')
        ((mem_filter.mp (mem_coe.mp hf₂)).2.1 i') (hi' ▸ (mem_filter.mp (mem_coe.mp hf₁)).2.1 i)
    rw [← hi', hii']
  -- Step 3: Set degree cap `D` and filter edges `E_good ⊆ U` of degree `≤ D`.
  let D : ℕ := Nat.ceil ((p ^ (r - 1) + γ_D) * (m : ℝ) ^ (q - 2))
  have hD_ge_real : (p ^ (r - 1) + γ_D) * (m : ℝ) ^ (q - 2) ≤ (D : ℝ) := Nat.le_ceil _
  have hD_le_real : (D : ℝ) ≤ (p ^ (r - 1) + 2 * γ_D) * (m : ℝ) ^ (q - 2) := by
    have h1 : (D : ℝ) < (p ^ (r - 1) + γ_D) * (m : ℝ) ^ (q - 2) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hm_γ : 1 / γ_D ≤ (m : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast ((le_max_right _ _).trans (le_max_right _ _)).trans hm)
    have h2 : 1 ≤ γ_D * (m : ℝ) ^ (q - 2) := by
      have : 1 ≤ γ_D * (m : ℝ) := (div_le_iff₀ hγ_D0).mp hm_γ |>.trans_eq (mul_comm _ _)
      calc (1 : ℝ) ≤ γ_D * (m : ℝ) := this
        _ ≤ γ_D * (m : ℝ) ^ (q - 2) := mul_le_mul_of_nonneg_left hm_ge_q2 hγ_D0.le
    linarith
  have hD_ge_D0 : D₀ ≤ D := by
    have hm_D0 : (D₀ : ℝ) / δ ^ (r - 1) ≤ (m : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast ((le_max_right _ _).trans (le_max_left _ _)).trans hm)
    have h1 : (D₀ : ℝ) ≤ δ ^ (r - 1) * (m : ℝ) := by
      have := (div_le_iff₀ (pow_pos hδ (r - 1))).mp hm_D0
      linarith
    have h2 : δ ^ (r - 1) * (m : ℝ) ≤ (p ^ (r - 1) + γ_D) * (m : ℝ) ^ (q - 2) := by
      have hpow : δ ^ (r - 1) ≤ p ^ (r - 1) := pow_le_pow_left₀ hδ.le hpδ (r - 1)
      have : δ ^ (r - 1) * (m : ℝ) ≤ p ^ (r - 1) * (m : ℝ) ^ (q - 2) :=
        mul_le_mul hpow hm_ge_q2 hm_pos.le (pow_nonneg hp0.le _)
      nlinarith [pow_nonneg hm_pos.le (q - 2)]
    exact_mod_cast h1.trans (h2.trans hD_ge_real)
  let E_good : Finset (Sym2 (Fin n)) :=
    U.filter (fun e ↦ (transF.filter (fun f ↦ e ∈ edgesOf (cliqueOf f))).card ≤ D)
  let transF_good : Finset (Fin q → Fin n) :=
    transF.filter (fun f ↦ edgesOf (cliqueOf f) ⊆ E_good)
  let ℰ : Finset (Finset (Sym2 (Fin n))) := transF_good.image (fun f ↦ edgesOf (cliqueOf f))
  -- Step 4: Bound `(U \ E_good).card ≤ 4 * q * r * ε₁ * m^2` via `clique_counting_lemma (q - 2)`.
  have hbad_edges_card : ((U \ E_good).card : ℝ) ≤ 4 * (q : ℝ) * (r : ℝ) * ε₁ * (m : ℝ) ^ 2 := by
    -- For each distinct pair `(i, j)`, count edges between `V i, V j` that fail typical common neighborhoods.
    let typV : Fin q → Finset (Fin n) := fun i ↦
      (V i).filter (fun u ↦ ∀ ℓ : Fin q, ℓ ≠ i →
        (p - 2 * ε₁) * (m : ℝ) ≤ (((V ℓ).filter (G.Adj u)).card : ℝ) ∧
        (((V ℓ).filter (G.Adj u)).card : ℝ) ≤ (p + 2 * ε₁) * (m : ℝ))
    let badPairE : Fin q → Fin q → Finset (Sym2 (Fin n)) := fun i j ↦
      ((G.interedges (V i) (V j)).filter (fun uv ↦
        ¬(uv.1 ∈ typV i ∧ ∀ ℓ : Fin q, ℓ ≠ i → ℓ ≠ j →
          (p - 2 * ε₁) ^ 2 * (m : ℝ) ≤
            ((((V ℓ).filter (G.Adj uv.1)).filter (G.Adj uv.2)).card : ℝ) ∧
          ((((V ℓ).filter (G.Adj uv.1)).filter (G.Adj uv.2)).card : ℝ) ≤
            (p + 2 * ε₁) ^ 2 * (m : ℝ)))).image (fun uv ↦ s(uv.1, uv.2))
    -- Any edge `e = s(u, v) ∈ U` that IS typical has `K_q`-count `≤ D`!
    have htyp_in_good : ∀ i j : Fin q, i ≠ j → ∀ u ∈ V i, ∀ v ∈ V j, G.Adj u v →
        u ∈ typV i →
        (∀ ℓ : Fin q, ℓ ≠ i → ℓ ≠ j →
          (p - 2 * ε₁) ^ 2 * (m : ℝ) ≤
            ((((V ℓ).filter (G.Adj u)).filter (G.Adj v)).card : ℝ) ∧
          ((((V ℓ).filter (G.Adj u)).filter (G.Adj v)).card : ℝ) ≤
            (p + 2 * ε₁) ^ 2 * (m : ℝ)) →
        s(u, v) ∈ E_good := by
      intro i j hij u hui v hvj hadj _ hcn
      have heU : s(u, v) ∈ U :=
        mem_filter.mpr ⟨mem_edgeFinset.mpr hadj, i, j, hij, u, hui, v, hvj, rfl⟩
      refine mem_filter.mpr ⟨heU, ?_⟩
      -- Map `f ∈ transF` with `s(u, v) ∈ edgesOf (cliqueOf f)` into `Fin (q - 2) → Fin n`.
      let rest : Finset (Fin q) := (Finset.univ.erase i).erase j
      have hrest_card : rest.card = q - 2 := by
        rw [card_erase_of_mem (mem_erase.mpr ⟨hij.symm, mem_univ j⟩),
          card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
        omega
      let τ' : Fin (q - 2) ≃ rest := (Fin.castOrderIso hrest_card.symm).toEquiv.trans rest.equivFin.symm
      let V' : Fin (q - 2) → Finset (Fin n) := fun a ↦ V (τ' a).1
      let A' : Fin (q - 2) → Finset (Fin n) := fun a ↦ ((V' a).filter (G.Adj u)).filter (G.Adj v)
      have hτ'_ne_i : ∀ a : Fin (q - 2), (τ' a).1 ≠ i := fun a ↦
        (mem_erase.mp (mem_erase.mp (τ' a).2).2).1
      have hτ'_ne_j : ∀ a : Fin (q - 2), (τ' a).1 ≠ j := fun a ↦
        (mem_erase.mp (τ' a).2).1
      have hA'_sz : ∀ a : Fin (q - 2), α_q2 * (m : ℝ) ≤ ((A' a).card : ℝ) := by
        intro a
        have h1 := (hcn (τ' a).1 (hτ'_ne_i a) (hτ'_ne_j a)).1
        have h2 : δ / 2 ≤ p - 2 * ε₁ := by linarith
        have h3 : α_q2 ≤ (p - 2 * ε₁) ^ 2 := by
          have : (δ / 2) ^ 2 ≤ (p - 2 * ε₁) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
          simp only [α_q2]; linarith
        exact (mul_le_mul_of_nonneg_right h3 hm_pos.le).trans h1
      have hcnt_uv := hcnt_q2 n m hm1 G V' A' p hpδ hp1
        (fun a ↦ hV_card _) (fun a ↦ (filter_subset _ _).trans (filter_subset _ _)) hA'_sz
        (fun a b hab ↦
          let h := hunif (τ' a).1 (τ' b).1 (fun h ↦ hab (τ'.injective (Subtype.ext h)))
          ⟨h.1.mono hε₁_q2, h.2.trans hε₁_q2⟩)
      -- Inject `transF.filter (s(u, v) ∈ edgesOf (cliqueOf f))` into `transK G A'`.
      have hinj_ext : (transF.filter (fun f ↦ s(u, v) ∈ edgesOf (cliqueOf f))).card ≤
          ((Finset.univ : Finset (Fin (q - 2) → Fin n)).filter
            (fun g ↦ (∀ a, g a ∈ A' a) ∧ ∀ a b, a ≠ b → G.Adj (g a) (g b))).card := by
        refine Finset.card_le_card_of_injOn (fun f a ↦ f (τ' a).1) ?_ ?_
        · intro f hf
          obtain ⟨hfT, hfe⟩ := mem_filter.mp (mem_coe.mp hf)
          have hf1 := (mem_filter.mp hfT).2.1
          have hf2 := (mem_filter.mp hfT).2.2
          have hu_in : u ∈ cliqueOf f := (mem_filter.mp hfe).2 u (by simp)
          have hv_in : v ∈ cliqueOf f := (mem_filter.mp hfe).2 v (by simp)
          have hfi : f i = u := by
            obtain ⟨i', _, hi'⟩ := mem_image.mp hu_in
            have heq : i' = i := by
              by_contra hne; exact Finset.disjoint_left.mp (hV_disj i' i hne) (hf1 i') (hi' ▸ hui)
            exact heq ▸ hi'
          have hfj : f j = v := by
            obtain ⟨j', _, hj'⟩ := mem_image.mp hv_in
            have heq : j' = j := by
              by_contra hne; exact Finset.disjoint_left.mp (hV_disj j' j hne) (hf1 j') (hj' ▸ hvj)
            exact heq ▸ hj'
          rw [mem_coe, mem_filter]
          refine ⟨mem_univ _, fun a ↦ mem_filter.mpr ⟨mem_filter.mpr ⟨hf1 _,
            hfi ▸ hf2 i (τ' a).1 (hτ'_ne_i a).symm⟩, hfj ▸ hf2 j (τ' a).1 (hτ'_ne_j a).symm⟩,
            fun a b hab ↦ hf2 _ _ (fun h ↦ hab (τ'.injective (Subtype.ext h)))⟩
        · intro f₁ hf₁ f₂ hf₂ heq
          obtain ⟨hfT₁, hfe₁⟩ := mem_filter.mp (mem_coe.mp hf₁)
          obtain ⟨hfT₂, hfe₂⟩ := mem_filter.mp (mem_coe.mp hf₂)
          have hfi1 : f₁ i = u := by
            obtain ⟨i', _, hi'⟩ := mem_image.mp ((mem_filter.mp hfe₁).2 u (by simp))
            have : i' = i := by by_contra h; exact Finset.disjoint_left.mp (hV_disj i' i h) ((mem_filter.mp hfT₁).2.1 i') (hi' ▸ hui)
            exact this ▸ hi'
          have hfj1 : f₁ j = v := by
            obtain ⟨j', _, hj'⟩ := mem_image.mp ((mem_filter.mp hfe₁).2 v (by simp))
            have : j' = j := by by_contra h; exact Finset.disjoint_left.mp (hV_disj j' j h) ((mem_filter.mp hfT₁).2.1 j') (hj' ▸ hvj)
            exact this ▸ hj'
          have hfi2 : f₂ i = u := by
            obtain ⟨i', _, hi'⟩ := mem_image.mp ((mem_filter.mp hfe₂).2 u (by simp))
            have : i' = i := by by_contra h; exact Finset.disjoint_left.mp (hV_disj i' i h) ((mem_filter.mp hfT₂).2.1 i') (hi' ▸ hui)
            exact this ▸ hi'
          have hfj2 : f₂ j = v := by
            obtain ⟨j', _, hj'⟩ := mem_image.mp ((mem_filter.mp hfe₂).2 v (by simp))
            have : j' = j := by by_contra h; exact Finset.disjoint_left.mp (hV_disj j' j h) ((mem_filter.mp hfT₂).2.1 j') (hj' ▸ hvj)
            exact this ▸ hj'
          funext ℓ
          by_cases h1 : ℓ = i
          · rw [h1, hfi1, hfi2]
          · by_cases h2 : ℓ = j
            · rw [h2, hfj1, hfj2]
            · have hmem : ℓ ∈ rest := mem_erase.mpr ⟨h2, mem_erase.mpr ⟨h1, mem_univ ℓ⟩⟩
              have := congr_fun heq (τ'.symm ⟨ℓ, hmem⟩)
              simpa using this
      -- Bound `((transK G A').card : ℝ) ≤ (p^(r-1) + γ_D) * m^(q-2) ≤ D`!
      have hprodA : ∏ a : Fin (q - 2), ((A' a).card : ℝ) ≤
          (p + 2 * ε₁) ^ (2 * (q - 2)) * (m : ℝ) ^ (q - 2) := by
        calc ∏ a : Fin (q - 2), ((A' a).card : ℝ)
            ≤ ∏ _a : Fin (q - 2), ((p + 2 * ε₁) ^ 2 * (m : ℝ)) :=
              Finset.prod_le_prod (fun _ _ ↦ Nat.cast_nonneg _)
                (fun a _ ↦ (hcn (τ' a).1 (hτ'_ne_i a) (hτ'_ne_j a)).2)
          _ = ((p + 2 * ε₁) ^ 2 * (m : ℝ)) ^ (q - 2) := by simp
          _ = (p + 2 * ε₁) ^ (2 * (q - 2)) * (m : ℝ) ^ (q - 2) := by rw [mul_pow, ← pow_mul]
      have hexp_eq : (q - 2).choose 2 + 2 * (q - 2) = r - 1 := by
        obtain ⟨t, rfl⟩ : ∃ t, q = t + 3 := ⟨q - 3, by omega⟩
        simp only [r, Nat.choose_two_right]
        have ha : t + 3 - 2 = t + 1 := by omega
        have hb : t + 1 - 1 = t := by omega
        have hc : t + 3 - 1 = t + 2 := by omega
        rw [ha, hb, hc]
        have hd : (t + 3) * (t + 2) = (t + 1) * t + 4 * (t + 1) + 2 := by ring
        rw [hd]
        omega
      have hpow_diff : (p + 2 * ε₁) ^ (2 * (q - 2)) ≤ p ^ (2 * (q - 2)) + γ_D / 4 := by
        have habs := abs_pow_sub_pow_le (by linarith) (by linarith : p + 2 * ε₁ ≤ 2)
          hp0.le (by linarith) (2 * (q - 2))
        have h1 : |p + 2 * ε₁ - p| = 2 * ε₁ := by
          rw [show p + 2 * ε₁ - p = 2 * ε₁ by ring, abs_of_pos (by positivity)]
        rw [h1] at habs
        have h2 : ((2 * (q - 2) : ℕ) : ℝ) * (2 : ℝ) ^ (2 * (q - 2)) * (2 * ε₁) ≤ γ_D / 4 := by
          have hqle : ((2 * (q - 2) : ℕ) : ℝ) ≤ 2 * (q : ℝ) := by
            have : 2 * (q - 2) ≤ 2 * q := by omega
            exact_mod_cast this
          have := mul_le_mul_of_nonneg_right hqle (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * (q - 2)) * (2 * ε₁))
          linarith
        linarith [(abs_le.mp habs).2]
      have hle_D_real : ((transF.filter (fun f ↦ s(u, v) ∈ edgesOf (cliqueOf f))).card : ℝ) ≤
          (p ^ (r - 1) + γ_D) * (m : ℝ) ^ (q - 2) := by
        have h1 : ((transF.filter (fun f ↦ s(u, v) ∈ edgesOf (cliqueOf f))).card : ℝ) ≤
            (p ^ ((q - 2).choose 2) + γ_cnt) * ∏ a : Fin (q - 2), ((A' a).card : ℝ) := by
          have hhi := (abs_le.mp hcnt_uv).2
          have hcast : ((transF.filter (fun f ↦ s(u, v) ∈ edgesOf (cliqueOf f))).card : ℝ) ≤
              (((Finset.univ : Finset (Fin (q - 2) → Fin n)).filter
                (fun g ↦ (∀ a, g a ∈ A' a) ∧ ∀ a b, a ≠ b → G.Adj (g a) (g b))).card : ℝ) := by
            exact_mod_cast hinj_ext
          linarith
        have h2 : (p ^ ((q - 2).choose 2) + γ_cnt) * (p + 2 * ε₁) ^ (2 * (q - 2)) ≤
            p ^ (r - 1) + γ_D := by
          have hA : p ^ ((q - 2).choose 2) * p ^ (2 * (q - 2)) = p ^ (r - 1) := by
            rw [← pow_add, hexp_eq]
          have hB : (p ^ ((q - 2).choose 2) + γ_cnt) * (p + 2 * ε₁) ^ (2 * (q - 2)) ≤
              (p ^ ((q - 2).choose 2) + γ_cnt) * (p ^ (2 * (q - 2)) + γ_D / 4) :=
            mul_le_mul_of_nonneg_left hpow_diff (by positivity)
          have hC : p ^ ((q - 2).choose 2) ≤ 1 := pow_le_one₀ hp0.le hp1
          have hD' : p ^ (2 * (q - 2)) ≤ 1 := pow_le_one₀ hp0.le hp1
          have hγcnt_le : γ_cnt ≤ γ_D / 4 := min_le_right _ _
          have hγD_le1 : γ_D ≤ 1 := by
            have : δ ^ (r - 1) ≤ 1 := pow_le_one₀ hδ.le hδ1
            simp only [γ_D]; nlinarith
          nlinarith
        calc ((transF.filter (fun f ↦ s(u, v) ∈ edgesOf (cliqueOf f))).card : ℝ)
            ≤ (p ^ ((q - 2).choose 2) + γ_cnt) * ((p + 2 * ε₁) ^ (2 * (q - 2)) * (m : ℝ) ^ (q - 2)) :=
              h1.trans (mul_le_mul_of_nonneg_left hprodA (by positivity))
          _ = ((p ^ ((q - 2).choose 2) + γ_cnt) * (p + 2 * ε₁) ^ (2 * (q - 2))) * (m : ℝ) ^ (q - 2) := by ring
          _ ≤ (p ^ (r - 1) + γ_D) * (m : ℝ) ^ (q - 2) :=
              mul_le_mul_of_nonneg_right h2 (pow_nonneg hm_pos.le _)
      exact_mod_cast hle_D_real.trans hD_ge_real
    -- Now bound `(U \ E_good).card` by summing `badPairE i j` over unordered pairs `i < j`.
    let pairsLT : Finset (Fin q × Fin q) := Finset.univ.filter (fun p ↦ p.1 < p.2)
    have hpairsLT_card : pairsLT.card = r := by
      have h2 : 2 * pairsLT.card = q * (q - 1) := by
        have hdisj : Disjoint pairsLT (Finset.univ.filter (fun p : Fin q × Fin q ↦ p.2 < p.1)) := by
          rw [Finset.disjoint_left]; intro p h1 h2
          exact lt_asymm (mem_filter.mp h1).2 (mem_filter.mp h2).2
        have hu : pairsLT ∪ Finset.univ.filter (fun p : Fin q × Fin q ↦ p.2 < p.1) =
            (Finset.univ : Finset (Fin q)).offDiag := by
          ext ⟨a, b⟩
          simp only [pairsLT, mem_union, mem_filter, mem_univ, true_and, mem_offDiag]
          rcases lt_trichotomy a b with h | rfl | h
          · simp [h, h.ne, h.asymm]
          · simp
          · simp [h, h.ne', h.asymm]
        have hsym : (Finset.univ.filter (fun p : Fin q × Fin q ↦ p.2 < p.1)).card = pairsLT.card := by
          refine Finset.card_bij (fun p _ ↦ (p.2, p.1)) ?_ ?_ ?_
          · intro p hp; exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hp).2⟩
          · intro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h; exact Prod.ext (Prod.mk.inj h).2 (Prod.mk.inj h).1
          · intro ⟨a, b⟩ hp; exact ⟨(b, a), mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hp).2⟩, rfl⟩
        have hcard := Finset.card_union_of_disjoint hdisj
        rw [hu, Finset.offDiag_card, card_univ, Fintype.card_fin, hsym] at hcard
        have hmul : q * (q - 1) = q * q - q := by rw [Nat.mul_sub_left_distrib, mul_one]
        omega
      simp only [r, Nat.choose_two_right]; omega
    have hUbad_sub : U \ E_good ⊆ pairsLT.biUnion (fun ij ↦ badPairE ij.1 ij.2) := by
      intro e he
      obtain ⟨heU, hnotG⟩ := mem_sdiff.mp he
      obtain ⟨heG, i, j, hij, u, hui, v, hvj, rfl⟩ := mem_filter.mp heU
      have hadj : G.Adj u v := mem_edgeFinset.mp heG
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · refine mem_biUnion.mpr ⟨(i, j), mem_filter.mpr ⟨mem_univ _, hlt⟩,
          mem_image.mpr ⟨(u, v), mem_filter.mpr ⟨(SimpleGraph.mem_interedges_iff G).mpr
            ⟨hui, hvj, hadj⟩, fun ⟨ht, hc⟩ ↦ hnotG (htyp_in_good i j hij u hui v hvj hadj ht hc)⟩, rfl⟩⟩
      · refine mem_biUnion.mpr ⟨(j, i), mem_filter.mpr ⟨mem_univ _, hgt⟩,
          mem_image.mpr ⟨(v, u), mem_filter.mpr ⟨(SimpleGraph.mem_interedges_iff G).mpr
            ⟨hvj, hui, hadj.symm⟩, fun ⟨ht, hc⟩ ↦ hnotG (by
              rw [Sym2.eq_swap]; exact htyp_in_good j i hij.symm v hvj u hui hadj.symm ht hc)⟩,
            Sym2.eq_swap⟩⟩
    have hbadPair_le : ∀ i j : Fin q, i ≠ j →
        ((badPairE i j).card : ℝ) ≤ 4 * (q : ℝ) * ε₁ * (m : ℝ) ^ 2 := by
      intro i j hij
      -- Count atypical `u ∈ V i \ typV i` (`≤ 2 * q * ε₁ * m`) + atypical `v ∈ V j` for each typical `u` (`≤ 2 * q * ε₁ * m`).
      have hatyp_i : (((V i) \ typV i).card : ℝ) ≤ 2 * (q : ℝ) * ε₁ * (m : ℝ) := by
        have hsub : (V i) \ typV i ⊆ (Finset.univ.erase i).biUnion (fun ℓ ↦
            (V i).filter (fun u ↦ (((V ℓ).filter (G.Adj u)).card : ℝ) < (p - 2 * ε₁) * (m : ℝ)) ∪
            (V i).filter (fun u ↦ (p + 2 * ε₁) * (m : ℝ) < (((V ℓ).filter (G.Adj u)).card : ℝ))) := by
          intro u hu
          obtain ⟨hui, hnot⟩ := mem_sdiff.mp hu
          simp only [typV, mem_filter, hui, true_and, not_forall, not_and_or, not_le] at hnot
          obtain ⟨ℓ, hℓi, h | h⟩ := hnot
          · exact mem_biUnion.mpr ⟨ℓ, mem_erase.mpr ⟨hℓi, mem_univ _⟩,
              mem_union_left _ (mem_filter.mpr ⟨hui, h⟩)⟩
          · exact mem_biUnion.mpr ⟨ℓ, mem_erase.mpr ⟨hℓi, mem_univ _⟩,
              mem_union_right _ (mem_filter.mpr ⟨hui, h⟩)⟩
        have h1 : (((V i) \ typV i).card : ℝ) ≤ ∑ ℓ ∈ Finset.univ.erase i,
            ((((V i).filter (fun u ↦ (((V ℓ).filter (G.Adj u)).card : ℝ) < (p - 2 * ε₁) * (m : ℝ))).card : ℝ) +
             (((V i).filter (fun u ↦ (p + 2 * ε₁) * (m : ℝ) < (((V ℓ).filter (G.Adj u)).card : ℝ))).card : ℝ)) := by
          have hnat : ((V i) \ typV i).card ≤ ∑ ℓ ∈ Finset.univ.erase i,
              (((V i).filter (fun u ↦ (((V ℓ).filter (G.Adj u)).card : ℝ) < (p - 2 * ε₁) * (m : ℝ))).card +
               ((V i).filter (fun u ↦ (p + 2 * ε₁) * (m : ℝ) < (((V ℓ).filter (G.Adj u)).card : ℝ))).card) :=
            (card_le_card hsub).trans (card_biUnion_le.trans (sum_le_sum fun _ _ ↦ card_union_le _ _))
          exact_mod_cast hnat
        calc (((V i) \ typV i).card : ℝ)
            ≤ ∑ _ℓ ∈ Finset.univ.erase i, (2 * ε₁ * (m : ℝ)) := h1.trans (sum_le_sum fun ℓ hℓ ↦ by
              have hℓi : i ≠ ℓ := (mem_erase.mp hℓ).1.symm
              have hBsz : (m : ℝ) * ε₁ ≤ ((V ℓ).card : ℝ) := by
                rw [hV_card ℓ]; nlinarith
              have hat := atypical_deg_card_lt hm1 G hε₁0 (hV_card i) (hV_card ℓ) Subset.rfl Subset.rfl
                hBsz (hunif i ℓ hℓi).1 (hunif i ℓ hℓi).2
              rw [hV_card ℓ] at hat
              linarith)
          _ = ((Finset.univ.erase i).card : ℝ) * (2 * ε₁ * (m : ℝ)) := by simp
          _ ≤ (q : ℝ) * (2 * ε₁ * (m : ℝ)) := mul_le_mul_of_nonneg_right
              (by exact_mod_cast (card_erase_le.trans (by simp : (Finset.univ : Finset (Fin q)).card ≤ q)))
              (by positivity)
          _ = 2 * (q : ℝ) * ε₁ * (m : ℝ) := by ring
      have hatyp_v : ∀ u ∈ typV i,
          (((V j).filter (fun v ↦ ¬(∀ ℓ : Fin q, ℓ ≠ i → ℓ ≠ j →
            (p - 2 * ε₁) ^ 2 * (m : ℝ) ≤ ((((V ℓ).filter (G.Adj u)).filter (G.Adj v)).card : ℝ) ∧
            ((((V ℓ).filter (G.Adj u)).filter (G.Adj v)).card : ℝ) ≤
              (p + 2 * ε₁) ^ 2 * (m : ℝ)))).card : ℝ) ≤ 2 * (q : ℝ) * ε₁ * (m : ℝ) := by
        intro u hu
        have hu_deg := (mem_filter.mp hu).2
        let S_bad_v := (V j).filter (fun v ↦ ¬(∀ ℓ : Fin q, ℓ ≠ i → ℓ ≠ j →
          (p - 2 * ε₁) ^ 2 * (m : ℝ) ≤ ((((V ℓ).filter (G.Adj u)).filter (G.Adj v)).card : ℝ) ∧
          ((((V ℓ).filter (G.Adj u)).filter (G.Adj v)).card : ℝ) ≤ (p + 2 * ε₁) ^ 2 * (m : ℝ)))
        have hsub : S_bad_v ⊆ ((Finset.univ.erase i).erase j).biUnion (fun ℓ ↦
            (V j).filter (fun v ↦ ((((V ℓ).filter (G.Adj u)).filter (G.Adj v)).card : ℝ) <
              (p - 2 * ε₁) * (((V ℓ).filter (G.Adj u)).card : ℝ)) ∪
            (V j).filter (fun v ↦ (p + 2 * ε₁) * (((V ℓ).filter (G.Adj u)).card : ℝ) <
              ((((V ℓ).filter (G.Adj u)).filter (G.Adj v)).card : ℝ))) := by
          intro v hv
          obtain ⟨hvj, hnot⟩ := mem_filter.mp hv
          push Not at hnot
          obtain ⟨ℓ, hℓi, hℓj, hfail⟩ := hnot
          have hℓ_mem : ℓ ∈ (Finset.univ.erase i).erase j :=
            mem_erase.mpr ⟨hℓj, mem_erase.mpr ⟨hℓi, mem_univ ℓ⟩⟩
          have huℓ := hu_deg ℓ hℓi
          refine mem_biUnion.mpr ⟨ℓ, hℓ_mem, ?_⟩
          by_cases hlo : ((((V ℓ).filter (G.Adj u)).filter (G.Adj v)).card : ℝ) <
              (p - 2 * ε₁) * (((V ℓ).filter (G.Adj u)).card : ℝ)
          · exact mem_union_left _ (mem_filter.mpr ⟨hvj, hlo⟩)
          · push Not at hlo
            have hlo2 : (p - 2 * ε₁) ^ 2 * (m : ℝ) ≤
                ((((V ℓ).filter (G.Adj u)).filter (G.Adj v)).card : ℝ) := by
              have hpos : 0 ≤ p - 2 * ε₁ := by linarith
              have := mul_le_mul_of_nonneg_left huℓ.1 hpos
              nlinarith
            have hhi2 := hfail hlo2
            have hhi : (p + 2 * ε₁) * (((V ℓ).filter (G.Adj u)).card : ℝ) <
                ((((V ℓ).filter (G.Adj u)).filter (G.Adj v)).card : ℝ) := by
              have := mul_le_mul_of_nonneg_left huℓ.2 (by positivity : 0 ≤ p + 2 * ε₁)
              nlinarith
            exact mem_union_right _ (mem_filter.mpr ⟨hvj, hhi⟩)
        have h1 : (S_bad_v.card : ℝ) ≤ ∑ ℓ ∈ (Finset.univ.erase i).erase j,
            ((((V j).filter (fun v ↦ ((((V ℓ).filter (G.Adj u)).filter (G.Adj v)).card : ℝ) <
                (p - 2 * ε₁) * (((V ℓ).filter (G.Adj u)).card : ℝ))).card : ℝ) +
             (((V j).filter (fun v ↦ (p + 2 * ε₁) * (((V ℓ).filter (G.Adj u)).card : ℝ) <
                ((((V ℓ).filter (G.Adj u)).filter (G.Adj v)).card : ℝ))).card : ℝ)) := by
          have hnat : S_bad_v.card ≤ ∑ ℓ ∈ (Finset.univ.erase i).erase j,
              (((V j).filter (fun v ↦ ((((V ℓ).filter (G.Adj u)).filter (G.Adj v)).card : ℝ) <
                  (p - 2 * ε₁) * (((V ℓ).filter (G.Adj u)).card : ℝ))).card +
               ((V j).filter (fun v ↦ (p + 2 * ε₁) * (((V ℓ).filter (G.Adj u)).card : ℝ) <
                  ((((V ℓ).filter (G.Adj u)).filter (G.Adj v)).card : ℝ))).card) :=
            (card_le_card hsub).trans (card_biUnion_le.trans (sum_le_sum fun _ _ ↦ card_union_le _ _))
          exact_mod_cast hnat
        calc (S_bad_v.card : ℝ)
            ≤ ∑ _ℓ ∈ (Finset.univ.erase i).erase j, (2 * ε₁ * (m : ℝ)) := h1.trans (sum_le_sum fun ℓ hℓ ↦ by
              have hℓj : j ≠ ℓ := (mem_erase.mp hℓ).1.symm
              have hℓi : ℓ ≠ i := (mem_erase.mp (mem_erase.mp hℓ).2).1
              have hBsz : (m : ℝ) * ε₁ ≤ (((V ℓ).filter (G.Adj u)).card : ℝ) := by
                have := (hu_deg ℓ hℓi).1
                nlinarith
              have hat := atypical_deg_card_lt hm1 G hε₁0 (hV_card j) (hV_card ℓ) Subset.rfl
                (filter_subset _ _) hBsz (hunif j ℓ hℓj).1 (hunif j ℓ hℓj).2
              linarith)
          _ = (((Finset.univ.erase i).erase j).card : ℝ) * (2 * ε₁ * (m : ℝ)) := by simp
          _ ≤ (q : ℝ) * (2 * ε₁ * (m : ℝ)) := mul_le_mul_of_nonneg_right
              (by exact_mod_cast (card_erase_le.trans (card_erase_le.trans (by simp : (Finset.univ : Finset (Fin q)).card ≤ q))))
              (by positivity)
          _ = 2 * (q : ℝ) * ε₁ * (m : ℝ) := by ring
      let badV : Fin n → Finset (Fin n) := fun u ↦
        (V j).filter (fun v ↦ ¬(∀ ℓ : Fin q, ℓ ≠ i → ℓ ≠ j →
          (p - 2 * ε₁) ^ 2 * (m : ℝ) ≤ ((((V ℓ).filter (G.Adj u)).filter (G.Adj v)).card : ℝ) ∧
          ((((V ℓ).filter (G.Adj u)).filter (G.Adj v)).card : ℝ) ≤ (p + 2 * ε₁) ^ 2 * (m : ℝ)))
      have hbad_pair_sub :
          (G.interedges (V i) (V j)).filter (fun uv ↦
            ¬(uv.1 ∈ typV i ∧ ∀ ℓ : Fin q, ℓ ≠ i → ℓ ≠ j →
              (p - 2 * ε₁) ^ 2 * (m : ℝ) ≤ ((((V ℓ).filter (G.Adj uv.1)).filter (G.Adj uv.2)).card : ℝ) ∧
              ((((V ℓ).filter (G.Adj uv.1)).filter (G.Adj uv.2)).card : ℝ) ≤ (p + 2 * ε₁) ^ 2 * (m : ℝ))) ⊆
          (((V i) \ typV i) ×ˢ V j) ∪
          (typV i).biUnion (fun u ↦ (badV u).image (fun v ↦ (u, v))) := by
        intro ⟨u, v⟩ huv
        obtain ⟨hint, hnot⟩ := mem_filter.mp huv
        have hui := ((SimpleGraph.mem_interedges_iff G).mp hint).1
        have hvj := ((SimpleGraph.mem_interedges_iff G).mp hint).2.1
        by_cases hu : u ∈ typV i
        · refine mem_union_right _ (mem_biUnion.mpr ⟨u, hu, mem_image.mpr ⟨v, mem_filter.mpr
            ⟨hvj, fun h ↦ hnot ⟨hu, h⟩⟩, rfl⟩⟩)
        · exact mem_union_left _ (mem_product.mpr ⟨mem_sdiff.mpr ⟨hui, hu⟩, hvj⟩)
      have hcard_nat : (badPairE i j).card ≤
          ((V i) \ typV i).card * m + ∑ u ∈ typV i, (badV u).card := by
        calc (badPairE i j).card
            ≤ ((G.interedges (V i) (V j)).filter _).card := card_image_le
          _ ≤ ((((V i) \ typV i) ×ˢ V j) ∪ (typV i).biUnion (fun u ↦ (badV u).image (fun v ↦ (u, v)))).card :=
              card_le_card hbad_pair_sub
          _ ≤ (((V i) \ typV i) ×ˢ V j).card +
                ((typV i).biUnion (fun u ↦ (badV u).image (fun v ↦ (u, v)))).card := card_union_le _ _
          _ ≤ ((V i) \ typV i).card * m + ∑ u ∈ typV i, ((badV u).image (fun v ↦ (u, v))).card :=
              Nat.add_le_add (by rw [card_product, hV_card j]) card_biUnion_le
          _ ≤ ((V i) \ typV i).card * m + ∑ u ∈ typV i, (badV u).card :=
              Nat.add_le_add_left (sum_le_sum fun _ _ ↦ card_image_le) _
      have hcard_r : ((badPairE i j).card : ℝ) ≤
          (((V i) \ typV i).card : ℝ) * (m : ℝ) + ∑ u ∈ typV i, ((badV u).card : ℝ) := by
        exact_mod_cast hcard_nat
      have hterm1 : (((V i) \ typV i).card : ℝ) * (m : ℝ) ≤ 2 * (q : ℝ) * ε₁ * (m : ℝ) ^ 2 := by
        have := mul_le_mul_of_nonneg_right hatyp_i hm_pos.le
        linarith
      have hterm2 : ∑ u ∈ typV i, ((badV u).card : ℝ) ≤ 2 * (q : ℝ) * ε₁ * (m : ℝ) ^ 2 := by
        calc _ ≤ ∑ _u ∈ typV i, (2 * (q : ℝ) * ε₁ * (m : ℝ)) := sum_le_sum hatyp_v
          _ = ((typV i).card : ℝ) * (2 * (q : ℝ) * ε₁ * (m : ℝ)) := by simp
          _ ≤ (m : ℝ) * (2 * (q : ℝ) * ε₁ * (m : ℝ)) := mul_le_mul_of_nonneg_right
              (by exact_mod_cast (card_le_card (filter_subset _ _)).trans (hV_card i).le) (by positivity)
          _ = 2 * (q : ℝ) * ε₁ * (m : ℝ) ^ 2 := by ring
      linarith
    have hsum_bad : ((U \ E_good).card : ℝ) ≤ ∑ ij ∈ pairsLT, ((badPairE ij.1 ij.2).card : ℝ) := by
      have hnat : (U \ E_good).card ≤ ∑ ij ∈ pairsLT, (badPairE ij.1 ij.2).card :=
        (card_le_card hUbad_sub).trans card_biUnion_le
      exact_mod_cast hnat
    calc ((U \ E_good).card : ℝ)
        ≤ ∑ ij ∈ pairsLT, (4 * (q : ℝ) * ε₁ * (m : ℝ) ^ 2) := hsum_bad.trans (sum_le_sum fun ij hij ↦
          hbadPair_le ij.1 ij.2 (ne_of_lt (mem_filter.mp hij).2))
      _ = (pairsLT.card : ℝ) * (4 * (q : ℝ) * ε₁ * (m : ℝ) ^ 2) := by simp
      _ = 4 * (q : ℝ) * (r : ℝ) * ε₁ * (m : ℝ) ^ 2 := by rw [hpairsLT_card]; ring
  -- Step 5: Bound `ℰ.card ≥ (p^r - 2 * γ_cnt) * m^q` and verify `Δ(ℰ) ≤ D`, `Δ₂(ℰ) ≤ β * D`.
  have hℰ_card : (p ^ r - 2 * γ_cnt) * (m : ℝ) ^ q ≤ (ℰ.card : ℝ) := by
    have hcnt_all := hcnt_q n m hm1 G V V p hpδ hp1 hV_card (fun _ ↦ Subset.rfl)
      (fun i ↦ by rw [hV_card i, one_mul]) (fun i j hij ↦
        ⟨(hunif i j hij).1.mono hε₁_q, (hunif i j hij).2.trans hε₁_q⟩)
    have hprodV : ∏ i : Fin q, ((V i).card : ℝ) = (m : ℝ) ^ q := by
      simp [hV_card]
    rw [hprodV] at hcnt_all
    have htot_lo : (p ^ r - γ_cnt) * (m : ℝ) ^ q ≤ (transF.card : ℝ) := by
      have := (abs_le.mp hcnt_all).1
      simp only [r]; linarith
    -- Each bad edge `e ∈ U \ E_good` lies in at most `m ^ (q - 2)` cliques of `transF`.
    have hbad_edge_deg : ∀ e ∈ U \ E_good,
        (transF.filter (fun f ↦ e ∈ edgesOf (cliqueOf f))).card ≤ m ^ (q - 2) := by
      intro e he
      have heU := (mem_sdiff.mp he).1
      obtain ⟨_, i, j, hij, u, hui, v, hvj, rfl⟩ := mem_filter.mp heU
      let rest : Finset (Fin q) := (Finset.univ.erase i).erase j
      have hrest_card : rest.card = q - 2 := by
        rw [card_erase_of_mem (mem_erase.mpr ⟨hij.symm, mem_univ j⟩),
          card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
        omega
      refine (Finset.card_le_card_of_injOn (fun f (x : rest) ↦ f x.1) (t := Fintype.piFinset (fun x : rest ↦ V x.1)) ?_ ?_).trans ?_
      · intro f hf
        rw [mem_coe, Fintype.mem_piFinset]
        intro x
        exact (mem_filter.mp (mem_filter.mp (mem_coe.mp hf)).1).2.1 x.1
      · intro f₁ hf₁ f₂ hf₂ heq
        obtain ⟨hfT₁, hfe₁⟩ := mem_filter.mp (mem_coe.mp hf₁)
        obtain ⟨hfT₂, hfe₂⟩ := mem_filter.mp (mem_coe.mp hf₂)
        have hfi1 : f₁ i = u := by
          obtain ⟨i', _, hi'⟩ := mem_image.mp ((mem_filter.mp hfe₁).2 u (by simp))
          have : i' = i := by by_contra h; exact Finset.disjoint_left.mp (hV_disj i' i h) ((mem_filter.mp hfT₁).2.1 i') (hi' ▸ hui)
          exact this ▸ hi'
        have hfj1 : f₁ j = v := by
          obtain ⟨j', _, hj'⟩ := mem_image.mp ((mem_filter.mp hfe₁).2 v (by simp))
          have : j' = j := by by_contra h; exact Finset.disjoint_left.mp (hV_disj j' j h) ((mem_filter.mp hfT₁).2.1 j') (hj' ▸ hvj)
          exact this ▸ hj'
        have hfi2 : f₂ i = u := by
          obtain ⟨i', _, hi'⟩ := mem_image.mp ((mem_filter.mp hfe₂).2 u (by simp))
          have : i' = i := by by_contra h; exact Finset.disjoint_left.mp (hV_disj i' i h) ((mem_filter.mp hfT₂).2.1 i') (hi' ▸ hui)
          exact this ▸ hi'
        have hfj2 : f₂ j = v := by
          obtain ⟨j', _, hj'⟩ := mem_image.mp ((mem_filter.mp hfe₂).2 v (by simp))
          have : j' = j := by by_contra h; exact Finset.disjoint_left.mp (hV_disj j' j h) ((mem_filter.mp hfT₂).2.1 j') (hj' ▸ hvj)
          exact this ▸ hj'
        funext ℓ
        by_cases h1 : ℓ = i
        · rw [h1, hfi1, hfi2]
        · by_cases h2 : ℓ = j
          · rw [h2, hfj1, hfj2]
          · exact congr_fun heq ⟨ℓ, mem_erase.mpr ⟨h2, mem_erase.mpr ⟨h1, mem_univ ℓ⟩⟩⟩
      · rw [Fintype.card_piFinset]
        simp [hV_card, hrest_card]
    have hlost_cliques : ((transF \ transF_good).card : ℝ) ≤ γ_cnt * (m : ℝ) ^ q := by
      have hsub : transF \ transF_good ⊆
          (U \ E_good).biUnion (fun e ↦ transF.filter (fun f ↦ e ∈ edgesOf (cliqueOf f))) := by
        intro f hf
        obtain ⟨hfT, hnot⟩ := mem_sdiff.mp hf
        simp only [transF_good, mem_filter, hfT, true_and] at hnot
        rw [Finset.not_subset] at hnot
        obtain ⟨e, heF, heNot⟩ := hnot
        exact mem_biUnion.mpr ⟨e, mem_sdiff.mpr ⟨(hcl_props f hfT).2.2.2.1 heF, heNot⟩,
          mem_filter.mpr ⟨hfT, heF⟩⟩
      have hnat : (transF \ transF_good).card ≤ (U \ E_good).card * m ^ (q - 2) :=
        (card_le_card hsub).trans (card_biUnion_le.trans (by
          calc ∑ e ∈ U \ E_good, (transF.filter (fun f ↦ e ∈ edgesOf (cliqueOf f))).card
              ≤ ∑ _e ∈ U \ E_good, m ^ (q - 2) := sum_le_sum hbad_edge_deg
            _ = (U \ E_good).card * m ^ (q - 2) := by simp))
      have hr_le : ((transF \ transF_good).card : ℝ) ≤ ((U \ E_good).card : ℝ) * (m : ℝ) ^ (q - 2) := by
        exact_mod_cast hnat
      have hpow_q : (m : ℝ) ^ 2 * (m : ℝ) ^ (q - 2) = (m : ℝ) ^ q := by
        rw [← pow_add, show 2 + (q - 2) = q by omega]
      calc ((transF \ transF_good).card : ℝ)
          ≤ (4 * (q : ℝ) * (r : ℝ) * ε₁ * (m : ℝ) ^ 2) * (m : ℝ) ^ (q - 2) :=
            hr_le.trans (mul_le_mul_of_nonneg_right hbad_edges_card (pow_nonneg hm_pos.le _))
        _ = (4 * (q : ℝ) * (r : ℝ) * ε₁) * (m : ℝ) ^ q := by rw [mul_assoc, hpow_q]
        _ ≤ γ_cnt * (m : ℝ) ^ q := mul_le_mul_of_nonneg_right hε₁_bad (pow_nonneg hm_pos.le _)
    have hℰ_eq : ℰ.card = transF_good.card :=
      Finset.card_image_of_injOn (hedges_inj.mono (filter_subset _ _))
    have hdiff : ((transF \ transF_good).card : ℝ) + (transF_good.card : ℝ) = (transF.card : ℝ) := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card (filter_subset _ transF)
    rw [hℰ_eq]
    linarith
  -- Verify `ℰ` is `r`-uniform on `U`, has `Δ(ℰ) ≤ D`, and `Δ₂(ℰ) ≤ β * D`.
  have hℰ_unif : ∀ F ∈ ℰ, F ⊆ U ∧ F.card = r := by
    intro F hF
    obtain ⟨f, hf, rfl⟩ := mem_image.mp hF
    have hp := hcl_props f (mem_filter.mp hf).1
    exact ⟨hp.2.2.2.1, hp.2.2.2.2⟩
  have hℰ_deg : ∀ e ∈ U, (ℰ.filter (fun F ↦ e ∈ F)).card ≤ D := by
    intro e _
    by_cases he : e ∈ E_good
    · have h1 : (ℰ.filter (fun F ↦ e ∈ F)).card ≤
          (transF.filter (fun f ↦ e ∈ edgesOf (cliqueOf f))).card := by
        have hsub : ℰ.filter (fun F ↦ e ∈ F) ⊆
            (transF.filter (fun f ↦ e ∈ edgesOf (cliqueOf f))).image (fun f ↦ edgesOf (cliqueOf f)) := by
          intro F hF
          obtain ⟨hFℰ, heF⟩ := mem_filter.mp hF
          obtain ⟨f, hf, rfl⟩ := mem_image.mp hFℰ
          exact mem_image.mpr ⟨f, mem_filter.mpr ⟨(mem_filter.mp hf).1, heF⟩, rfl⟩
        exact (card_le_card hsub).trans card_image_le
      exact h1.trans (mem_filter.mp he).2
    · have hemp : ℰ.filter (fun F ↦ e ∈ F) = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        intro F hF
        obtain ⟨hFℰ, heF⟩ := mem_filter.mp hF
        obtain ⟨f, hf, rfl⟩ := mem_image.mp hFℰ
        exact he ((mem_filter.mp hf).2 heF)
      simp [hemp]
  have hℰ_codeg : ∀ e₁ ∈ U, ∀ e₂ ∈ U, e₁ ≠ e₂ →
      ((ℰ.filter (fun F ↦ e₁ ∈ F ∧ e₂ ∈ F)).card : ℝ) ≤ β * (D : ℝ) := by
    intro e₁ he₁ e₂ he₂ hne
    -- Two distinct edges `e₁, e₂ ∈ U` span at least 3 distinct vertices, hence fix 3 coordinates of `f`!
    obtain ⟨_, i₁, j₁, hij₁, u₁, hu₁, v₁, hv₁, rfl⟩ := mem_filter.mp he₁
    obtain ⟨_, i₂, j₂, hij₂, u₂, hu₂, v₂, hv₂, rfl⟩ := mem_filter.mp he₂
    have hnat : (ℰ.filter (fun F ↦ s(u₁, v₁) ∈ F ∧ s(u₂, v₂) ∈ F)).card ≤ m ^ (q - 3) := by
      -- Map `F ↦ f ∈ transF` via image; if `f` contains both `s(u₁, v₁)` and `s(u₂, v₂)`, then
      -- `f` is uniquely determined on `{i₁, j₁, i₂, j₂}`, which has cardinality `≥ 3`!
      have hcard3 : 3 ≤ ({i₁, j₁, i₂, j₂} : Finset (Fin q)).card ∨
          (ℰ.filter (fun F ↦ s(u₁, v₁) ∈ F ∧ s(u₂, v₂) ∈ F)) = ∅ := by
        by_cases hsub : ({i₂, j₂} : Finset (Fin q)) ⊆ {i₁, j₁}
        · -- If `{i₂, j₂} ⊆ {i₁, j₁}`, then since `s(u₁, v₁) ≠ s(u₂, v₂)`, no single `f ∈ transF` can contain both!
          right
          rw [eq_empty_iff_forall_notMem]
          intro F hF
          obtain ⟨hFℰ, h1F, h2F⟩ := mem_filter.mp hF
          obtain ⟨f, hf, rfl⟩ := mem_image.mp hFℰ
          have hf1 := (mem_filter.mp (mem_filter.mp hf).1).2.1
          have hfi1 : f i₁ = u₁ := by
            obtain ⟨a, _, ha⟩ := mem_image.mp ((mem_filter.mp h1F).2 u₁ (by simp))
            have : a = i₁ := by by_contra h; exact Finset.disjoint_left.mp (hV_disj a i₁ h) (hf1 a) (ha ▸ hu₁)
            exact this ▸ ha
          have hfj1 : f j₁ = v₁ := by
            obtain ⟨a, _, ha⟩ := mem_image.mp ((mem_filter.mp h1F).2 v₁ (by simp))
            have : a = j₁ := by by_contra h; exact Finset.disjoint_left.mp (hV_disj a j₁ h) (hf1 a) (ha ▸ hv₁)
            exact this ▸ ha
          have hfi2 : f i₂ = u₂ := by
            obtain ⟨a, _, ha⟩ := mem_image.mp ((mem_filter.mp h2F).2 u₂ (by simp))
            have : a = i₂ := by by_contra h; exact Finset.disjoint_left.mp (hV_disj a i₂ h) (hf1 a) (ha ▸ hu₂)
            exact this ▸ ha
          have hfj2 : f j₂ = v₂ := by
            obtain ⟨a, _, ha⟩ := mem_image.mp ((mem_filter.mp h2F).2 v₂ (by simp))
            have : a = j₂ := by by_contra h; exact Finset.disjoint_left.mp (hV_disj a j₂ h) (hf1 a) (ha ▸ hv₂)
            exact this ▸ ha
          have hi2m : i₂ ∈ ({i₁, j₁} : Finset (Fin q)) := hsub (by simp)
          have hj2m : j₂ ∈ ({i₁, j₁} : Finset (Fin q)) := hsub (by simp)
          simp only [mem_insert, mem_singleton] at hi2m hj2m
          rcases hi2m with rfl | rfl <;> rcases hj2m with rfl | rfl
          · exact hij₂ rfl
          · exact hne (by rw [← hfi1, ← hfj1, ← hfi2, ← hfj2])
          · exact hne (by rw [← hfi1, ← hfj1, ← hfi2, ← hfj2, Sym2.eq_swap])
          · exact hij₂ rfl
        · left
          rw [Finset.not_subset] at hsub
          obtain ⟨k₀, hk₀_in, hk₀_not⟩ := hsub
          have hsub3 : insert k₀ ({i₁, j₁} : Finset (Fin q)) ⊆ {i₁, j₁, i₂, j₂} := by
            intro x hx
            simp only [mem_insert, mem_singleton] at hx hk₀_in ⊢
            rcases hx with rfl | rfl | rfl
            · rcases hk₀_in with rfl | rfl <;> simp
            · simp
            · simp
          have h3 : (insert k₀ ({i₁, j₁} : Finset (Fin q))).card = 3 := by
            rw [card_insert_of_notMem hk₀_not, card_pair hij₁]
          exact h3 ▸ card_le_card hsub3
      rcases hcard3 with h3 | hemp
      · let fixed : Finset (Fin q) := {i₁, j₁, i₂, j₂}
        let free : Finset (Fin q) := Finset.univ \ fixed
        have hfree_le : free.card ≤ q - 3 := by
          rw [Finset.card_sdiff_of_subset (subset_univ fixed), card_univ, Fintype.card_fin]
          have hfixed3 : 3 ≤ fixed.card := h3
          omega
        have hstep1 : (ℰ.filter (fun F ↦ s(u₁, v₁) ∈ F ∧ s(u₂, v₂) ∈ F)).card ≤
            (transF.filter (fun f ↦ s(u₁, v₁) ∈ edgesOf (cliqueOf f) ∧
              s(u₂, v₂) ∈ edgesOf (cliqueOf f))).card := by
          have hsub : ℰ.filter (fun F ↦ s(u₁, v₁) ∈ F ∧ s(u₂, v₂) ∈ F) ⊆
              (transF.filter (fun f ↦ s(u₁, v₁) ∈ edgesOf (cliqueOf f) ∧
                s(u₂, v₂) ∈ edgesOf (cliqueOf f))).image (fun f ↦ edgesOf (cliqueOf f)) := by
            intro F hF
            obtain ⟨hFℰ, h1F, h2F⟩ := mem_filter.mp hF
            obtain ⟨f, hf, rfl⟩ := mem_image.mp hFℰ
            exact mem_image.mpr ⟨f, mem_filter.mpr ⟨(mem_filter.mp hf).1, h1F, h2F⟩, rfl⟩
          exact (card_le_card hsub).trans card_image_le
        refine hstep1.trans ?_
        refine (Finset.card_le_card_of_injOn (fun f (x : free) ↦ f x.1)
          (t := Fintype.piFinset (fun x : free ↦ V x.1)) ?_ ?_).trans ?_
        · intro f hf
          rw [mem_coe, Fintype.mem_piFinset]
          intro x; exact (mem_filter.mp (mem_filter.mp (mem_coe.mp hf)).1).2.1 x.1
        · intro f₁ hf₁ f₂ hf₂ heq
          obtain ⟨hfT₁, h1₁, h2₁⟩ := mem_filter.mp (mem_coe.mp hf₁)
          obtain ⟨hfT₂, h1₂, h2₂⟩ := mem_filter.mp (mem_coe.mp hf₂)
          have hfix : ∀ f ∈ transF, s(u₁, v₁) ∈ edgesOf (cliqueOf f) →
              s(u₂, v₂) ∈ edgesOf (cliqueOf f) →
              f i₁ = u₁ ∧ f j₁ = v₁ ∧ f i₂ = u₂ ∧ f j₂ = v₂ := by
            intro f hfT h1F h2F
            have hf1 := (mem_filter.mp hfT).2.1
            refine ⟨?_, ?_, ?_, ?_⟩
            · obtain ⟨a, _, ha⟩ := mem_image.mp ((mem_filter.mp h1F).2 u₁ (by simp))
              have : a = i₁ := by by_contra h; exact Finset.disjoint_left.mp (hV_disj a i₁ h) (hf1 a) (ha ▸ hu₁)
              exact this ▸ ha
            · obtain ⟨a, _, ha⟩ := mem_image.mp ((mem_filter.mp h1F).2 v₁ (by simp))
              have : a = j₁ := by by_contra h; exact Finset.disjoint_left.mp (hV_disj a j₁ h) (hf1 a) (ha ▸ hv₁)
              exact this ▸ ha
            · obtain ⟨a, _, ha⟩ := mem_image.mp ((mem_filter.mp h2F).2 u₂ (by simp))
              have : a = i₂ := by by_contra h; exact Finset.disjoint_left.mp (hV_disj a i₂ h) (hf1 a) (ha ▸ hu₂)
              exact this ▸ ha
            · obtain ⟨a, _, ha⟩ := mem_image.mp ((mem_filter.mp h2F).2 v₂ (by simp))
              have : a = j₂ := by by_contra h; exact Finset.disjoint_left.mp (hV_disj a j₂ h) (hf1 a) (ha ▸ hv₂)
              exact this ▸ ha
          have hf1_eq := hfix f₁ hfT₁ h1₁ h2₁
          have hf2_eq := hfix f₂ hfT₂ h1₂ h2₂
          funext ℓ
          by_cases hℓ : ℓ ∈ fixed
          · simp only [fixed, mem_insert, mem_singleton] at hℓ
            rcases hℓ with rfl | rfl | rfl | rfl
            · exact hf1_eq.1.trans hf2_eq.1.symm
            · exact hf1_eq.2.1.trans hf2_eq.2.1.symm
            · exact hf1_eq.2.2.1.trans hf2_eq.2.2.1.symm
            · exact hf1_eq.2.2.2.trans hf2_eq.2.2.2.symm
          · exact congr_fun heq ⟨ℓ, mem_sdiff.mpr ⟨mem_univ ℓ, hℓ⟩⟩
        · rw [Fintype.card_piFinset]
          simp only [hV_card, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
          exact Nat.pow_le_pow_right (by omega) hfree_le
      · rw [hemp, card_empty]; exact Nat.zero_le _
    have hm_β : 1 / (β * δ ^ (r - 1)) ≤ (m : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast ((le_max_left _ _).trans (le_max_right _ _)).trans hm)
    have h1 : 1 ≤ β * δ ^ (r - 1) * (m : ℝ) := by
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < β * δ ^ (r - 1))).mp hm_β
      linarith
    have h2 : (m : ℝ) ^ (q - 3) ≤ β * (D : ℝ) := by
      have hpow_m : (m : ℝ) ^ (q - 3) * (m : ℝ) = (m : ℝ) ^ (q - 2) := by
        rw [← pow_succ, show q - 3 + 1 = q - 2 by omega]
      have hpow_p : δ ^ (r - 1) ≤ p ^ (r - 1) := pow_le_pow_left₀ hδ.le hpδ (r - 1)
      have hD_lo : δ ^ (r - 1) * (m : ℝ) ^ (q - 2) ≤ (D : ℝ) := by
        have : δ ^ (r - 1) * (m : ℝ) ^ (q - 2) ≤ (p ^ (r - 1) + γ_D) * (m : ℝ) ^ (q - 2) :=
          mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hm_pos.le _)
        exact this.trans hD_ge_real
      calc (m : ℝ) ^ (q - 3)
          ≤ (m : ℝ) ^ (q - 3) * (β * δ ^ (r - 1) * (m : ℝ)) :=
            le_mul_of_one_le_right (pow_nonneg hm_pos.le _) h1
        _ = β * (δ ^ (r - 1) * ((m : ℝ) ^ (q - 3) * (m : ℝ))) := by ring
        _ = β * (δ ^ (r - 1) * (m : ℝ) ^ (q - 2)) := by rw [hpow_m]
        _ ≤ β * (D : ℝ) := mul_le_mul_of_nonneg_left hD_lo hβ0.le
    exact (by exact_mod_cast hnat : ((ℰ.filter _).card : ℝ) ≤ (m : ℝ) ^ (q - 3)).trans h2
  -- Step 6: Apply `rodl_nibble_matching` to `ℰ` and extract the edge-disjoint `q`-cliques `𝒬`!
  obtain ⟨ℳ, hℳ_sub, hℳ_disj, hℳ_card⟩ :=
    hnibble U ℰ D hD_ge_D0 hℰ_unif hℰ_deg hℰ_codeg
  -- Recover the unique `f ∈ transF_good` for each `F ∈ ℳ`.
  have hrec_ex : ∀ F ∈ ℳ, ∃ f ∈ transF_good, edgesOf (cliqueOf f) = F :=
    fun F hF ↦ mem_image.mp (hℳ_sub hF)
  let 𝒬 : Finset (Finset (Fin n)) := ℳ.attach.image (fun F ↦ cliqueOf (hrec_ex F.1 F.2).choose)
  have hQ_inj : Function.Injective (fun F : { F // F ∈ ℳ } ↦ cliqueOf (hrec_ex F.1 F.2).choose) := by
    intro F₁ F₂ heq
    dsimp only at heq
    have h1 := (hrec_ex F₁.1 F₁.2).choose_spec.2
    have h2 := (hrec_ex F₂.1 F₂.2).choose_spec.2
    exact Subtype.ext (by rw [← h1, heq, h2])
  have hQ_card : 𝒬.card = ℳ.card := by
    rw [Finset.card_image_of_injective _ hQ_inj, Finset.card_attach]
  refine ⟨𝒬, ?_, ?_, ?_⟩
  · intro Q hQ
    obtain ⟨F, _, rfl⟩ := mem_image.mp hQ
    have hfT := (mem_filter.mp (hrec_ex F.1 F.2).choose_spec.1).1
    have hp := hcl_props _ hfT
    exact ⟨hp.1, hp.2.1, hp.2.2.1⟩
  · intro Q₁ hQ₁ Q₂ hQ₂ hne
    obtain ⟨F₁, _, rfl⟩ := mem_image.mp hQ₁
    obtain ⟨F₂, _, rfl⟩ := mem_image.mp hQ₂
    have hFne : F₁.1 ≠ F₂.1 := fun heq ↦ hne (by have h := Subtype.ext heq; rw [h])
    have hdisjF := hℳ_disj F₁.1 F₁.2 F₂.1 F₂.2 hFne
    rw [← (hrec_ex F₁.1 F₁.2).choose_spec.2, ← (hrec_ex F₂.1 F₂.2).choose_spec.2] at hdisjF
    by_contra hgt
    push Not at hgt
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hgt
    have hcl1 := (hcl_props _ (mem_filter.mp (hrec_ex F₁.1 F₁.2).choose_spec.1).1).2.1
    have hadj : G.Adj u v := hcl1 (mem_inter.mp hu).1 (mem_inter.mp hv).1 huv
    have h1 : s(u, v) ∈ edgesOf (cliqueOf (hrec_ex F₁.1 F₁.2).choose) :=
      mem_filter.mpr ⟨mem_edgeFinset.mpr hadj, fun x hx ↦ by
        rcases Sym2.mem_iff.mp hx with rfl | rfl
        · exact (mem_inter.mp hu).1
        · exact (mem_inter.mp hv).1⟩
    have h2 : s(u, v) ∈ edgesOf (cliqueOf (hrec_ex F₂.1 F₂.2).choose) :=
      mem_filter.mpr ⟨mem_edgeFinset.mpr hadj, fun x hx ↦ by
        rcases Sym2.mem_iff.mp hx with rfl | rfl
        · exact (mem_inter.mp hu).2
        · exact (mem_inter.mp hv).2⟩
    exact Finset.disjoint_left.mp hdisjF h1 h2
  · -- Final arithmetic bound: `(p - η) * m^2 ≤ 𝒬.card`.
    rw [hQ_card]
    have hD_pos : (0 : ℝ) < (D : ℝ) := by
      have : 0 < D := lt_of_lt_of_le (by omega) hD_ge_D0
      exact_mod_cast this
    have hpow_r : p ^ r = p * p ^ (r - 1) := by
      rw [← pow_succ', show r - 1 + 1 = r by omega]
    have hpow_q : (m : ℝ) ^ q = (m : ℝ) ^ 2 * (m : ℝ) ^ (q - 2) := by
      rw [← pow_add, show 2 + (q - 2) = q by omega]
    have h2γ_cnt : 2 * γ_cnt ≤ (η / 4) * p ^ r := by
      have h1 : γ_cnt ≤ η * δ ^ r / 16 := min_le_left _ _
      have h2 : δ ^ r ≤ p ^ r := pow_le_pow_left₀ hδ.le hpδ r
      nlinarith
    have h2γ_D : 2 * γ_D ≤ (η / 4) * p ^ (r - 1) := by
      have h2 : δ ^ (r - 1) ≤ p ^ (r - 1) := pow_le_pow_left₀ hδ.le hpδ (r - 1)
      have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ η / 8)
      have h4 : 0 ≤ η * p ^ (r - 1) := mul_nonneg hη.le (pow_nonneg hp0.le _)
      simp only [γ_D]; linarith
    have hℰ_lo : (1 - η / 4) * p ^ r * (m : ℝ) ^ q ≤ (ℰ.card : ℝ) := by
      have h1 : (1 - η / 4) * p ^ r ≤ p ^ r - 2 * γ_cnt := by linarith
      exact (mul_le_mul_of_nonneg_right h1 (pow_nonneg hm_pos.le _)).trans hℰ_card
    have hD_hi : (D : ℝ) ≤ (1 + η / 4) * p ^ (r - 1) * (m : ℝ) ^ (q - 2) := by
      have h1 : p ^ (r - 1) + 2 * γ_D ≤ (1 + η / 4) * p ^ (r - 1) := by linarith
      exact hD_le_real.trans (mul_le_mul_of_nonneg_right h1 (pow_nonneg hm_pos.le _))
    have hnum_frac : (p - η) * (m : ℝ) ^ 2 ≤ (1 - γ_nib) * ((ℰ.card : ℝ) / (D : ℝ)) := by
      by_cases hpη : 0 ≤ p - η
      · rw [mul_div_assoc', le_div_iff₀ hD_pos]
        have h1 : (p - η) * (m : ℝ) ^ 2 * (D : ℝ) ≤
            (p - η) * (1 + η / 4) * p ^ (r - 1) * (m : ℝ) ^ q := by
          calc (p - η) * (m : ℝ) ^ 2 * (D : ℝ)
              ≤ (p - η) * (m : ℝ) ^ 2 * ((1 + η / 4) * p ^ (r - 1) * (m : ℝ) ^ (q - 2)) :=
                mul_le_mul_of_nonneg_left hD_hi (mul_nonneg hpη (sq_nonneg _))
            _ = (p - η) * (1 + η / 4) * p ^ (r - 1) * ((m : ℝ) ^ 2 * (m : ℝ) ^ (q - 2)) := by ring
            _ = (p - η) * (1 + η / 4) * p ^ (r - 1) * (m : ℝ) ^ q := by rw [hpow_q]
        have halg : (p - η) * (1 + η / 4) ≤ (1 - η / 4) * (1 - η / 4) * p := by
          have hpη_le : p * η ≤ η := mul_le_of_le_one_left hη.le hp1
          nlinarith [mul_nonneg hp0.le (sq_nonneg η), sq_nonneg η]
        calc (p - η) * (m : ℝ) ^ 2 * (D : ℝ)
            ≤ (p - η) * (1 + η / 4) * p ^ (r - 1) * (m : ℝ) ^ q := h1
          _ ≤ ((1 - η / 4) * (1 - η / 4) * p) * p ^ (r - 1) * (m : ℝ) ^ q :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right halg (pow_nonneg hp0.le _)) (pow_nonneg hm_pos.le _)
          _ = (1 - γ_nib) * ((1 - η / 4) * p ^ r * (m : ℝ) ^ q) := by
              simp only [γ_nib, hpow_r]; ring
          _ ≤ (1 - γ_nib) * (ℰ.card : ℝ) :=
              mul_le_mul_of_nonneg_left hℰ_lo (by simp only [γ_nib]; linarith)
      · push Not at hpη
        have hl : (p - η) * (m : ℝ) ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hpη.le (sq_nonneg _)
        have hr' : 0 ≤ (1 - γ_nib) * ((ℰ.card : ℝ) / (D : ℝ)) :=
          mul_nonneg (by simp only [γ_nib]; linarith) (div_nonneg (Nat.cast_nonneg _) hD_pos.le)
        exact hl.trans hr'
    exact hnum_frac.trans hℳ_card

end OMA.Erdos81_erdos_81_R1_H2_R1_H2

theorem OMA.solution : OMA.R_Erdos81_erdos_81_R1.H2 :=
  OMA.R_Erdos81_erdos_81_R1_H2_R1.main
    OMA.Erdos81_erdos_81_R1_H2_R1_H1.main_aux
    OMA.Erdos81_erdos_81_R1_H2_R1_H2.main_aux
