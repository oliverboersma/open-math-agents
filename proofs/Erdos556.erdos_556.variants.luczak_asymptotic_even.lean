import FormalConjectures.ErdosProblems.«556»

section R1Section
-- Reduction Erdos556.erdos_556.variants.luczak_asymptotic_even.R1 of Erdős Problem 556 — luczak asymptotic even
-- Credit: @green-notes
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-
# Łuczak's asymptotic bound for even cycles via Szemerédi regularity and connected matchings

We reduce `Erdos556.erdos_556.variants.luczak_asymptotic_even` (`R(C_n; 3) ≤ (3 + ε)n` for large
even `n`) to two independent combinatorial pillars, while discharging the pigeonhole edge-counting
and Szemerédi regularity cluster-graph extraction directly inside this reduction:

* `H1`: Connected matching density lemma — any graph on `t` vertices with strictly more than
  `(k - 1) * t` edges contains a matching of size at least `k` inside a single connected
  component (Erdős–Gallai / Tutte–Berge).
* `H2`: Łuczak's blow-up / cycle-embedding lemma — a connected matching of `k` edges in an
  `η`-uniform, `d`-dense cluster graph with equipartite parts of size `m` embeds `C_n` for every
  even `4 ≤ n ≤ (1 - δ) * 2 * k * m` once `m` is sufficiently large relative to `(d, δ, t)`.
-/

namespace OMA.Erdos556R1

open Filter SimpleGraph Finset

/-- Connected matching density lemma: any graph on `t` vertices with strictly more than
`(k - 1) * t` edges contains a matching covering at least `2 * k` vertices within a single
connected component. -/
def H1 : Prop :=
  ∀ (t k : ℕ) (R : SimpleGraph (Fin t)) [DecidableRel R.Adj],
    1 ≤ k → (k - 1) * t < R.edgeFinset.card →
    ∃ M : R.Subgraph, M.IsMatching ∧ 2 * k ≤ M.verts.ncard ∧
      ∀ u ∈ M.verts, ∀ v ∈ M.verts, R.Reachable u v

/-- Łuczak's connected-matching blow-up lemma for even cycles: given density `d > 0` and slack
`δ ∈ (0, 1)`, there exists regularity parameter `η > 0` such that for any number of clusters `t`
and sufficiently large equipartite part size `m ≥ m₀`, any `η`-uniform `d`-dense cluster graph `R`
with a connected matching `M` covering at least `2 * k` clusters embeds `C_n` in `G` for all even
`4 ≤ n ≤ (1 - δ) * (2 * k * m)`. -/
def H2 : Prop :=
  ∀ (d δ : ℝ), 0 < d → 0 < δ → δ < 1 →
    ∃ η > (0 : ℝ), ∀ (t : ℕ), ∃ m₀ : ℕ,
      ∀ (N n m k : ℕ) (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
        (parts : Fin t → Finset (Fin N)) (R : SimpleGraph (Fin t)) (M : R.Subgraph),
        Even n → 4 ≤ n → 1 ≤ k → m₀ ≤ m → (n : ℝ) ≤ (1 - δ) * (2 * (k : ℝ) * (m : ℝ)) →
        Pairwise (fun i j => Disjoint (parts i) (parts j)) →
        (∀ i : Fin t, m ≤ (parts i).card ∧ (parts i).card ≤ m + 1) →
        (∀ u v : Fin t, R.Adj u v →
          G.IsUniform η (parts u) (parts v) ∧ (d : ℝ) ≤ (G.edgeDensity (parts u) (parts v) : ℝ)) →
        M.IsMatching → 2 * k ≤ M.verts.ncard →
        (∀ u ∈ M.verts, ∀ v ∈ M.verts, R.Reachable u v) →
        (cycleGraph n).IsContained G

lemma dense_color_of_three_colouring (N : ℕ) (c : Fin 3 → SimpleGraph (Fin N))
    [∀ i, DecidableRel (c i).Adj]
    (hc : (⊤ : SimpleGraph (Fin N)).IsEdgeColouring c) :
    ∃ i : Fin 3, N * (N - 1) ≤ 6 * (c i).edgeFinset.card := by
  have hcov : (⊤ : SimpleGraph (Fin N)).edgeFinset ⊆
      (Finset.univ : Finset (Fin 3)).biUnion (fun i => (c i).edgeFinset) := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      rw [mem_edgeFinset, mem_edgeSet, top_adj] at he
      have hi : (⨆ i, c i).Adj x y := by rw [← hc.1]; exact (top_adj x y).mpr he
      rw [iSup_adj] at hi
      obtain ⟨i, hi⟩ := hi
      exact mem_biUnion.mpr ⟨i, mem_univ i, mem_edgeFinset.mpr hi⟩
  have hcard : (⊤ : SimpleGraph (Fin N)).edgeFinset.card ≤
      ∑ i : Fin 3, (c i).edgeFinset.card :=
    (Finset.card_le_card hcov).trans Finset.card_biUnion_le
  have htop : (⊤ : SimpleGraph (Fin N)).edgeFinset.card = Nat.choose N 2 := by
    convert SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin N)
    simp
  have hchoose : 2 * Nat.choose N 2 = N * (N - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_cancel' (Nat.even_mul_pred_self N).two_dvd
  rw [htop] at hcard
  have hsum : ∑ i : Fin 3, (c i).edgeFinset.card =
      (c 0).edgeFinset.card + (c 1).edgeFinset.card + (c 2).edgeFinset.card := by
    simp [Fin.sum_univ_three, add_assoc]
  have hmax : ∃ i : Fin 3, Nat.choose N 2 ≤ 3 * (c i).edgeFinset.card := by
    by_contra! h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    omega
  obtain ⟨i, hi⟩ := hmax
  exact ⟨i, by omega⟩

lemma regularity_cluster_graph (N : ℕ) (hN : 0 < N)
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (hG : N * (N - 1) ≤ 6 * G.edgeFinset.card)
    (η d : ℝ) (hη : 0 < η) (hd : 0 ≤ d) (l : ℕ) (hl : l ≤ N) (hl_pos : 0 < l) :
    ∃ (t : ℕ) (parts : Fin t → Finset (Fin N)) (R : SimpleGraph (Fin t))
      (_ : DecidableRel R.Adj),
      l ≤ t ∧ t ≤ SzemerediRegularity.bound η l ∧
      Pairwise (fun i j => Disjoint (parts i) (parts j)) ∧
      (∀ i : Fin t, N / t ≤ (parts i).card ∧ (parts i).card ≤ N / t + 1) ∧
      (∀ u v : Fin t, R.Adj u v →
        G.IsUniform η (parts u) (parts v) ∧ d ≤ (G.edgeDensity (parts u) (parts v) : ℝ)) ∧
      (N : ℝ) * (N - 1) / 3 ≤
        (N : ℝ) * (N + t) / t + η * (N + t) ^ 2 + d * (N + t) ^ 2 +
          2 * (R.edgeFinset.card : ℝ) * ((N / t : ℕ) + 1 : ℝ) ^ 2 := by
  classical
  have hl_card : l ≤ Fintype.card (Fin N) := by simpa using hl
  obtain ⟨P, hP₁, hP₂, hP₃, hP₄⟩ := szemeredi_regularity G hη hl_card
  set t := P.parts.card
  have ht_pos : 0 < t := lt_of_lt_of_le hl_pos hP₂
  let e : Fin t ≃ P.parts := (Finset.equivFin P.parts).symm
  let parts : Fin t → Finset (Fin N) := fun i => (e i).1
  let R : SimpleGraph (Fin t) :=
    { Adj := fun u v => u ≠ v ∧ G.IsUniform η (parts u) (parts v) ∧
        d ≤ (G.edgeDensity (parts u) (parts v) : ℝ)
      symm := ⟨fun u v ⟨hne, hu, hd_uv⟩ =>
        ⟨hne.symm, hu.symm, by rwa [SimpleGraph.edgeDensity_comm]⟩⟩
      loopless := ⟨fun u ⟨hne, _⟩ => hne rfl⟩ }
  letI : DecidableRel R.Adj := Classical.decRel R.Adj
  refine ⟨t, parts, R, inferInstance, hP₂, hP₃, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact P.disjoint (e i).2 (e j).2 (fun h => hij (e.injective (Subtype.ext h)))
  · intro i
    have hmem : parts i ∈ P.parts := (e i).2
    have h1 := hP₁.average_le_card_part hmem
    have h2 := hP₁.card_part_le_average_add_one hmem
    simp only [Finset.card_univ, Fintype.card_fin] at h1 h2
    exact ⟨h1, h2⟩
  · intro u v huv
    exact ⟨huv.2.1, huv.2.2⟩
  · have hA : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, hN⟩, Finset.mem_univ _⟩
    let densePairs : Finset (Finset (Fin N) × Finset (Fin N)) :=
      P.parts.offDiag.filter (fun uv => G.IsUniform η uv.1 uv.2 ∧
        d ≤ (G.edgeDensity uv.1 uv.2 : ℝ))
    have hsub : (Finset.univ ×ˢ Finset.univ).filter (fun xy : Fin N × Fin N => G.Adj xy.1 xy.2) ⊆
        (P.nonUniforms G η).biUnion (fun uv => uv.1 ×ˢ uv.2) ∪
          P.parts.biUnion Finset.offDiag ∪
          (P.sparsePairs G d).biUnion (fun uv => G.interedges uv.1 uv.2) ∪
          densePairs.biUnion (fun uv => G.interedges uv.1 uv.2) := by
      rintro ⟨x, y⟩ hxy
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hxy
      obtain ⟨U, hU, hx⟩ := P.exists_mem (Finset.mem_univ x)
      obtain ⟨V, hV, hy⟩ := P.exists_mem (Finset.mem_univ y)
      by_cases hUV : U = V
      · subst hUV
        refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
        exact Finset.mem_biUnion.mpr ⟨U, hU, Finset.mem_offDiag.mpr ⟨hx, hy, G.ne_of_adj hxy⟩⟩
      · by_cases huni : G.IsUniform η U V
        · by_cases hd_uv : d ≤ (G.edgeDensity U V : ℝ)
          · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨(U, V), ?_, ?_⟩)
            · exact Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨hU, hV, hUV⟩, huni, hd_uv⟩
            · exact G.mk_mem_interedges_iff.mpr ⟨hx, hy, hxy⟩
          · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
            refine Finset.mem_biUnion.mpr ⟨(U, V), ?_, G.mk_mem_interedges_iff.mpr ⟨hx, hy, hxy⟩⟩
            exact (P.mk_mem_sparsePairs G U V d).mpr ⟨hU, hV, hUV, not_le.mp hd_uv⟩
        · refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ ?_))
          refine Finset.mem_biUnion.mpr ⟨(U, V), ?_, Finset.mem_product.mpr ⟨hx, hy⟩⟩
          exact (P.mk_mem_nonUniforms G).mpr ⟨hU, hV, hUV, huni⟩
    have hcard_edges : 2 * G.edgeFinset.card ≤
        ((P.nonUniforms G η).biUnion (fun uv => uv.1 ×ˢ uv.2)).card +
        (P.parts.biUnion Finset.offDiag).card +
        ((P.sparsePairs G d).biUnion (fun uv => G.interedges uv.1 uv.2)).card +
        (densePairs.biUnion (fun uv => G.interedges uv.1 uv.2)).card := by
      have h2 := G.two_mul_card_edgeFinset
      rw [Finset.univ_product_univ] at hsub
      have hc := Finset.card_le_card hsub
      rw [← h2] at hc
      exact hc.trans (by
        refine (Finset.card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
        refine (Finset.card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
        exact Finset.card_union_le _ _)
    have h_dense_card : densePairs.card = 2 * R.edgeFinset.card := by
      have h2R := R.two_mul_card_edgeFinset
      rw [← Finset.univ_product_univ] at h2R
      rw [h2R]
      symm
      refine Finset.card_bij (fun uv _ => (parts uv.1, parts uv.2)) ?_ ?_ ?_
      · intro ⟨u, v⟩ huv
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at huv
        refine Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨(e u).2, (e v).2, ?_⟩, huv.2.1, huv.2.2⟩
        exact fun h => huv.1 (e.injective (Subtype.ext h))
      · intro ⟨u₁, v₁⟩ _ ⟨u₂, v₂⟩ _ heq
        simp only [Prod.mk.injEq] at heq
        exact Prod.ext (e.injective (Subtype.ext heq.1)) (e.injective (Subtype.ext heq.2))
      · intro ⟨U, V⟩ hUV
        simp only [densePairs, Finset.mem_filter, Finset.mem_offDiag] at hUV
        obtain ⟨⟨hU, hV, hne⟩, huni, hd_uv⟩ := hUV
        refine ⟨(e.symm ⟨U, hU⟩, e.symm ⟨V, hV⟩), ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
          refine ⟨fun h => hne ?_, ?_, ?_⟩
          · exact congrArg Subtype.val (e.symm.injective h)
          · simpa [parts] using huni
          · simpa [parts] using hd_uv
        · simp [parts]
    have h_dense_inter : ((densePairs.biUnion (fun uv => G.interedges uv.1 uv.2)).card : ℝ) ≤
        2 * (R.edgeFinset.card : ℝ) * ((N / t : ℕ) + 1 : ℝ) ^ 2 := by
      have h1 : (densePairs.biUnion (fun uv => G.interedges uv.1 uv.2)).card ≤
          ∑ uv ∈ densePairs, (G.interedges uv.1 uv.2).card := Finset.card_biUnion_le
      have h2 : ∑ uv ∈ densePairs, (G.interedges uv.1 uv.2).card ≤
          densePairs.card * (N / t + 1) ^ 2 := by
        calc ∑ uv ∈ densePairs, (G.interedges uv.1 uv.2).card
            ≤ ∑ _uv ∈ densePairs, (N / t + 1) ^ 2 := by
              refine Finset.sum_le_sum fun uv huv => ?_
              have hmem := Finset.mem_offDiag.mp (Finset.mem_filter.mp huv).1
              have hu := hP₁.card_part_le_average_add_one hmem.1
              have hv := hP₁.card_part_le_average_add_one hmem.2.1
              simp only [Finset.card_univ, Fintype.card_fin] at hu hv
              rw [sq]
              exact (G.card_interedges_le_mul uv.1 uv.2).trans (Nat.mul_le_mul hu hv)
          _ = densePairs.card * (N / t + 1) ^ 2 := by simp
      have h3 : (densePairs.biUnion (fun uv => G.interedges uv.1 uv.2)).card ≤
          2 * R.edgeFinset.card * (N / t + 1) ^ 2 := by
        rw [← h_dense_card]
        exact h1.trans h2
      exact_mod_cast h3
    have h_nonuni : (((P.nonUniforms G η).biUnion (fun uv => uv.1 ×ˢ uv.2)).card : ℝ) ≤
        η * ((N : ℝ) + t) ^ 2 := by
      have h1 : ((P.nonUniforms G η).biUnion (fun uv => uv.1 ×ˢ uv.2)).card ≤
          ∑ uv ∈ P.nonUniforms G η, uv.1.card * uv.2.card := by
        calc ((P.nonUniforms G η).biUnion (fun uv => uv.1 ×ˢ uv.2)).card
            ≤ ∑ uv ∈ P.nonUniforms G η, (uv.1 ×ˢ uv.2).card := Finset.card_biUnion_le
          _ = ∑ uv ∈ P.nonUniforms G η, uv.1.card * uv.2.card := by
              refine Finset.sum_congr rfl fun uv _ => Finset.card_product _ _
      have h2 := hP₁.sum_nonUniforms_lt' (𝕜 := ℝ) hA hη hP₄
      simp only [Finset.card_univ, Fintype.card_fin] at h2
      have h2le : (∑ uv ∈ P.nonUniforms G η, (#uv.1 : ℝ) * (#uv.2 : ℝ)) ≤ η * ((N : ℝ) + t) ^ 2 := by
        simpa [t] using h2.le
      calc (((P.nonUniforms G η).biUnion (fun uv => uv.1 ×ˢ uv.2)).card : ℝ)
          ≤ ((∑ uv ∈ P.nonUniforms G η, uv.1.card * uv.2.card : ℕ) : ℝ) := Nat.cast_le.mpr h1
        _ = ∑ uv ∈ P.nonUniforms G η, (#uv.1 : ℝ) * (#uv.2 : ℝ) := by push_cast; rfl
        _ ≤ η * ((N : ℝ) + t) ^ 2 := h2le
    have h_off : ((P.parts.biUnion Finset.offDiag).card : ℝ) ≤ (N : ℝ) * ((N : ℝ) + t) / t := by
      have h := hP₁.card_biUnion_offDiag_le' (𝕜 := ℝ)
      simpa [t] using h
    have h_sparse : (((P.sparsePairs G d).biUnion (fun uv => G.interedges uv.1 uv.2)).card : ℝ) ≤
        d * ((N : ℝ) + t) ^ 2 := by
      have h := hP₁.card_interedges_sparsePairs_le' (G := G) (ε := d) hd
      simpa [t] using h
    have hG_real : (N : ℝ) * ((N : ℝ) - 1) / 3 ≤ 2 * (G.edgeFinset.card : ℝ) := by
      have hG' : (N : ℝ) * ((N : ℝ) - 1) ≤ 6 * (G.edgeFinset.card : ℝ) := by
        have hcast : ((N * (N - 1) : ℕ) : ℝ) ≤ ((6 * G.edgeFinset.card : ℕ) : ℝ) :=
          Nat.cast_le.mpr hG
        rw [Nat.cast_mul, Nat.cast_sub hN, Nat.cast_one] at hcast
        push_cast at hcast
        exact hcast
      linarith
    have hcard_real : 2 * (G.edgeFinset.card : ℝ) ≤
        (((P.nonUniforms G η).biUnion (fun uv => uv.1 ×ˢ uv.2)).card : ℝ) +
        ((P.parts.biUnion Finset.offDiag).card : ℝ) +
        (((P.sparsePairs G d).biUnion (fun uv => G.interedges uv.1 uv.2)).card : ℝ) +
        ((densePairs.biUnion (fun uv => G.interedges uv.1 uv.2)).card : ℝ) := by
      exact_mod_cast hcard_edges
    linarith

lemma cluster_edge_bound (ε' η d : ℝ) (N t k eR : ℕ)
    (hε' : 0 < ε') (hε'1 : ε' ≤ 1)
    (hη_le : η ≤ ε' / 1000) (hd_le : d ≤ ε' / 1000)
    (ht_pos : 0 < t) (hN_pos : 0 < N)
    (ht_ge : 1000 / ε' ≤ (t : ℝ))
    (ht_leN : (t : ℝ) ≤ ε' / 10000 * (N : ℝ))
    (hk_le : (k : ℝ) ≤ (t : ℝ) / (6 + ε' / 2))
    (hR_ineq : (N : ℝ) * ((N : ℝ) - 1) / 3 ≤
      (N : ℝ) * ((N : ℝ) + (t : ℝ)) / (t : ℝ) +
      η * ((N : ℝ) + (t : ℝ)) ^ 2 + d * ((N : ℝ) + (t : ℝ)) ^ 2 +
      2 * (eR : ℝ) * ((↑(N / t) : ℝ) + 1) ^ 2) :
    (k - 1) * t < eR := by
  have ht_real_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht_pos
  have hN_real_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
  have hN_ge_inv : (10000 : ℝ) / ε' ≤ (N : ℝ) / (t : ℝ) := by
    rw [div_le_div_iff₀ hε' ht_real_pos]
    have h1 := (le_div_iff₀ (by norm_num : (0 : ℝ) < 10000)).mp
      (by linarith : (t : ℝ) ≤ ε' * (N : ℝ) / 10000)
    linarith
  have h_one_le_Nt : (1 : ℝ) ≤ ε' / 10000 * ((N : ℝ) / (t : ℝ)) := by
    have h1 := (div_le_iff₀ hε').mp hN_ge_inv
    linarith
  have ht_ge1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht_pos
  have h_one_le_N : (1 : ℝ) ≤ ε' / 10000 * (N : ℝ) := by
    have hNt1 : (N : ℝ) / (t : ℝ) ≤ (N : ℝ) := div_le_self hN_real_pos.le ht_ge1
    nlinarith
  have h_m_cast_le : (↑(N / t) : ℝ) ≤ (N : ℝ) / (t : ℝ) :=
    (le_div_iff₀ ht_real_pos).mpr (by exact_mod_cast Nat.div_mul_le_self N t)
  have h_N_add_t : (N : ℝ) + (t : ℝ) ≤ (1 + ε' / 10000) * (N : ℝ) := by linarith
  have h_N_sub_1 : (1 - ε' / 10000) * (N : ℝ) ≤ (N : ℝ) - 1 := by linarith
  have h_m_add_1 : (↑(N / t) : ℝ) + 1 ≤ (1 + ε' / 10000) * ((N : ℝ) / (t : ℝ)) := by linarith
  have h_inv_t : (1 : ℝ) / (t : ℝ) ≤ ε' / 1000 := by
    rw [div_le_div_iff₀ ht_real_pos (by norm_num), one_mul]
    linarith only [(div_le_iff₀ hε').mp ht_ge]
  have hLHS : (1 - ε' / 10000) / 3 * (N : ℝ) ^ 2 ≤ (N : ℝ) * ((N : ℝ) - 1) / 3 := by
    have hmul := mul_le_mul_of_nonneg_left h_N_sub_1 hN_real_pos.le
    linarith
  have h_off_term : (N : ℝ) * ((N : ℝ) + (t : ℝ)) / (t : ℝ) ≤
      (ε' / 1000) * (1 + ε' / 10000) * (N : ℝ) ^ 2 := by
    have h1 : (N : ℝ) * ((N : ℝ) + (t : ℝ)) / (t : ℝ) =
        ((N : ℝ) * ((N : ℝ) + (t : ℝ))) * (1 / (t : ℝ)) := by ring
    rw [h1]
    have h2 : (N : ℝ) * ((N : ℝ) + (t : ℝ)) ≤ (N : ℝ) * ((1 + ε' / 10000) * (N : ℝ)) := by
      gcongr
    calc ((N : ℝ) * ((N : ℝ) + (t : ℝ))) * (1 / (t : ℝ))
        ≤ ((N : ℝ) * ((1 + ε' / 10000) * (N : ℝ))) * (ε' / 1000) := by
          gcongr
      _ = (ε' / 1000) * (1 + ε' / 10000) * (N : ℝ) ^ 2 := by ring
  have h_sq_term : (η + d) * ((N : ℝ) + (t : ℝ)) ^ 2 ≤
      (ε' / 500) * (1 + ε' / 10000) ^ 2 * (N : ℝ) ^ 2 := by
    have hsq : ((N : ℝ) + (t : ℝ)) ^ 2 ≤ ((1 + ε' / 10000) * (N : ℝ)) ^ 2 := by gcongr
    have hhd : η + d ≤ ε' / 500 := by linarith
    calc (η + d) * ((N : ℝ) + (t : ℝ)) ^ 2
        ≤ (ε' / 500) * ((1 + ε' / 10000) * (N : ℝ)) ^ 2 := by gcongr
      _ = (ε' / 500) * (1 + ε' / 10000) ^ 2 * (N : ℝ) ^ 2 := by ring
  have h_edge_term : 2 * (eR : ℝ) * ((↑(N / t) : ℝ) + 1) ^ 2 ≤
      2 * (eR : ℝ) * ((1 + ε' / 10000) ^ 2 * (N : ℝ) ^ 2 / (t : ℝ) ^ 2) := by
    have hsq : ((↑(N / t) : ℝ) + 1) ^ 2 ≤ ((1 + ε' / 10000) * ((N : ℝ) / (t : ℝ))) ^ 2 := by
      gcongr
    have hsq' : ((1 + ε' / 10000) * ((N : ℝ) / (t : ℝ))) ^ 2 =
        (1 + ε' / 10000) ^ 2 * (N : ℝ) ^ 2 / (t : ℝ) ^ 2 := by ring
    rw [← hsq']
    gcongr
  have hN2_pos : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have h_comb : (1 / 3 - 0.0034 * ε') * (N : ℝ) ^ 2 ≤
      2 * (eR : ℝ) * ((1 + ε' / 10000) ^ 2 * (N : ℝ) ^ 2 / (t : ℝ) ^ 2) := by
    have h_num1 : (ε' / 1000) * (1 + ε' / 10000) ≤ 0.0011 * ε' := by nlinarith only [hε', hε'1]
    have hsq_bnd : (1 + ε' / 10000) ^ 2 ≤ 1.05 := by nlinarith only [hε', hε'1]
    have h_num2 : (ε' / 500) * (1 + ε' / 10000) ^ 2 ≤ 0.0021 * ε' := by
      nlinarith only [hε', hsq_bnd]
    have h_num3 : 1 / 3 - 0.0001 * ε' ≤ (1 - ε' / 10000) / 3 := by linarith
    have h1 : (1 / 3 - 0.0001 * ε') * (N : ℝ) ^ 2 ≤ (N : ℝ) * ((N : ℝ) - 1) / 3 := by
      nlinarith only [h_num3, hLHS, hN2_pos]
    have h2 : (N : ℝ) * ((N : ℝ) + (t : ℝ)) / (t : ℝ) ≤ 0.0011 * ε' * (N : ℝ) ^ 2 := by
      nlinarith only [h_num1, h_off_term, hN2_pos]
    have h3 : (η + d) * ((N : ℝ) + (t : ℝ)) ^ 2 ≤ 0.0021 * ε' * (N : ℝ) ^ 2 := by
      nlinarith only [h_num2, h_sq_term, hN2_pos]
    have h3' : η * ((N : ℝ) + (t : ℝ)) ^ 2 + d * ((N : ℝ) + (t : ℝ)) ^ 2 ≤
        0.0021 * ε' * (N : ℝ) ^ 2 := by
      linarith only [h3, show (η + d) * ((N : ℝ) + (t : ℝ)) ^ 2 =
        η * ((N : ℝ) + (t : ℝ)) ^ 2 + d * ((N : ℝ) + (t : ℝ)) ^ 2 by ring]
    have h_epsN2 : 0 ≤ ε' * (N : ℝ) ^ 2 := by positivity
    linarith only [hR_ineq, h1, h2, h3', h_edge_term, h_epsN2]
  have h_divN : (1 / 3 - 0.0034 * ε') ≤
      2 * (eR : ℝ) * (1 + ε' / 10000) ^ 2 / (t : ℝ) ^ 2 := by
    have h_eq : 2 * (eR : ℝ) * ((1 + ε' / 10000) ^ 2 * (N : ℝ) ^ 2 / (t : ℝ) ^ 2) =
        (2 * (eR : ℝ) * (1 + ε' / 10000) ^ 2 / (t : ℝ) ^ 2) * (N : ℝ) ^ 2 := by ring
    rw [h_eq] at h_comb
    exact le_of_mul_le_mul_right h_comb hN2_pos
  have h_mul_t : (1 / 3 - 0.0034 * ε') * (t : ℝ) ^ 2 ≤
      2 * (eR : ℝ) * (1 + ε' / 10000) ^ 2 :=
    (le_div_iff₀ (by positivity)).mp h_divN
  have h_k_le : ((k - 1 : ℕ) : ℝ) * (t : ℝ) ≤ (t : ℝ) ^ 2 / (6 + ε' / 2) := by
    have hkm1 : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.sub_le k 1
    calc ((k - 1 : ℕ) : ℝ) * (t : ℝ)
        ≤ (k : ℝ) * (t : ℝ) := by gcongr
      _ ≤ ((t : ℝ) / (6 + ε' / 2)) * (t : ℝ) := by gcongr
      _ = (t : ℝ) ^ 2 / (6 + ε' / 2) := by ring
  have h_strict : 2 * ((t : ℝ) ^ 2 / (6 + ε' / 2)) * (1 + ε' / 10000) ^ 2 <
      (1 / 3 - 0.0034 * ε') * (t : ℝ) ^ 2 := by
    have h6 : 0 < 6 + ε' / 2 := by linarith
    have ht2 : (0 : ℝ) < (t : ℝ) ^ 2 := by positivity
    suffices hcoef : 2 * (1 + ε' / 10000) ^ 2 < (1 / 3 - 0.0034 * ε') * (6 + ε' / 2) by
      have hmul : 2 * ((t : ℝ) ^ 2 / (6 + ε' / 2)) * (1 + ε' / 10000) ^ 2 =
          (2 * (1 + ε' / 10000) ^ 2 / (6 + ε' / 2)) * (t : ℝ) ^ 2 := by ring
      rw [hmul]
      exact mul_lt_mul_of_pos_right ((div_lt_iff₀ h6).mpr hcoef) ht2
    nlinarith only [hε', hε'1]
  have h_final_real : ((k - 1 : ℕ) : ℝ) * (t : ℝ) < (eR : ℝ) := by
    have hpos_c : (0 : ℝ) < 2 * (1 + ε' / 10000) ^ 2 := by positivity
    have h1 : 2 * (((k - 1 : ℕ) : ℝ) * (t : ℝ)) * (1 + ε' / 10000) ^ 2 ≤
        2 * ((t : ℝ) ^ 2 / (6 + ε' / 2)) * (1 + ε' / 10000) ^ 2 := by
      gcongr
    have h2 : 2 * (((k - 1 : ℕ) : ℝ) * (t : ℝ)) * (1 + ε' / 10000) ^ 2 <
        2 * (eR : ℝ) * (1 + ε' / 10000) ^ 2 := by
      linarith only [h1, h_strict, h_mul_t]
    nlinarith only [h2, hpos_c]
  exact_mod_cast h_final_real

lemma blowup_size_bound (ε' δ : ℝ) (N n t m k : ℕ)
    (hε' : 0 < ε') (hε'1 : ε' ≤ 1) (hδ : δ = ε' / 20)
    (ht_pos : 0 < t) (hn_pos : (0 : ℝ) < (n : ℝ))
    (ht_ge : 1000 / ε' ≤ (t : ℝ))
    (ht_leN : (t : ℝ) ≤ ε' / 10000 * (N : ℝ))
    (hN_ge : (3 + ε') * (n : ℝ) - 1 < (N : ℝ))
    (h_n_big : 10000 / ε' ≤ 3 * (n : ℝ))
    (hk_gt : (t : ℝ) / (6 + ε' / 2) - 1 < (k : ℝ))
    (hm_gt : (N : ℝ) / (t : ℝ) - 1 < (m : ℝ)) :
    (n : ℝ) ≤ (1 - δ) * (2 * (k : ℝ) * (m : ℝ)) := by
  have ht_real_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht_pos
  have h_one_lt_tk : (1 : ℝ) < (ε' / 100) * ((t : ℝ) / (6 + ε' / 2)) := by
    rw [div_mul_div_comm, lt_div_iff₀ (by positivity)]
    have h1 : (1000 : ℝ) ≤ ε' * (t : ℝ) := by linarith only [(div_le_iff₀ hε').mp ht_ge]
    linarith
  have hk_lower : (1 - ε' / 100) * ((t : ℝ) / (6 + ε' / 2)) < (k : ℝ) := by linarith
  have hN_ge_inv : (10000 : ℝ) / ε' ≤ (N : ℝ) / (t : ℝ) := by
    rw [div_le_div_iff₀ hε' ht_real_pos]
    have h1 := (le_div_iff₀ (by norm_num : (0 : ℝ) < 10000)).mp
      (by linarith : (t : ℝ) ≤ ε' * (N : ℝ) / 10000)
    linarith
  have h_one_le_Nt : (1 : ℝ) ≤ ε' / 10000 * ((N : ℝ) / (t : ℝ)) := by
    have h1 := (div_le_iff₀ hε').mp hN_ge_inv
    linarith
  have hm_lower : (1 - ε' / 10000) * ((N : ℝ) / (t : ℝ)) < (m : ℝ) := by linarith
  have hN_lower : (3 + 0.99 * ε') * (n : ℝ) ≤ (N : ℝ) := by
    have h1 : (1 : ℝ) ≤ 0.01 * ε' * (n : ℝ) := by
      have h2 := (div_le_iff₀ hε').mp h_n_big
      linarith
    linarith
  have hm_lower2 : (1 - ε' / 10000) * ((3 + 0.99 * ε') * (n : ℝ) / (t : ℝ)) ≤ (m : ℝ) := by
    have h1 : (3 + 0.99 * ε') * (n : ℝ) / (t : ℝ) ≤ (N : ℝ) / (t : ℝ) := by gcongr
    have h2 : 0 ≤ (1 - ε' / 10000) := by linarith
    nlinarith only [h1, h2, hm_lower]
  have h_prod : (1 - ε' / 20) * (2 * ((1 - ε' / 100) * ((t : ℝ) / (6 + ε' / 2))) *
      ((1 - ε' / 10000) * ((3 + 0.99 * ε') * (n : ℝ) / (t : ℝ)))) ≤
      (1 - δ) * (2 * (k : ℝ) * (m : ℝ)) := by
    rw [hδ]
    have hk0 : 0 ≤ (1 - ε' / 100) * ((t : ℝ) / (6 + ε' / 2)) :=
      mul_nonneg (by linarith) (by positivity)
    have hm0 : 0 ≤ (1 - ε' / 10000) * ((3 + 0.99 * ε') * (n : ℝ) / (t : ℝ)) :=
      mul_nonneg (by linarith) (by positivity)
    have hd0 : 0 ≤ 1 - ε' / 20 := by linarith
    gcongr
  have h_simp : (1 - ε' / 20) * (2 * ((1 - ε' / 100) * ((t : ℝ) / (6 + ε' / 2))) *
      ((1 - ε' / 10000) * ((3 + 0.99 * ε') * (n : ℝ) / (t : ℝ)))) =
      (2 * (1 - ε' / 20) * (1 - ε' / 100) * (1 - ε' / 10000) * (3 + 0.99 * ε') / (6 + ε' / 2)) *
        (n : ℝ) := by
    field_simp
  have h_ge_one : (1 : ℝ) ≤ 2 * (1 - ε' / 20) * (1 - ε' / 100) * (1 - ε' / 10000) *
      (3 + 0.99 * ε') / (6 + ε' / 2) := by
    rw [le_div_iff₀ (by linarith)]
    have hp1 : 1 - 0.061 * ε' ≤ (1 - ε' / 20) * (1 - ε' / 100) := by nlinarith only [hε', hε'1]
    have hp2 : 1 - 0.062 * ε' ≤ (1 - ε' / 20) * (1 - ε' / 100) * (1 - ε' / 10000) := by
      nlinarith only [hε', hε'1, hp1]
    have hp3 : 6 + ε' / 2 ≤ 2 * (1 - 0.062 * ε') * (3 + 0.99 * ε') := by
      nlinarith only [hε', hε'1]
    have hp4 : 2 * (1 - 0.062 * ε') * (3 + 0.99 * ε') ≤
        2 * (1 - ε' / 20) * (1 - ε' / 100) * (1 - ε' / 10000) * (3 + 0.99 * ε') := by
      nlinarith only [hε', hε'1, hp2]
    linarith only [hp3, hp4]
  have h_n_prod : (n : ℝ) ≤ (2 * (1 - ε' / 20) * (1 - ε' / 100) * (1 - ε' / 10000) *
      (3 + 0.99 * ε') / (6 + ε' / 2)) * (n : ℝ) := by
    nlinarith only [h_ge_one, hn_pos]
  linarith only [h_prod, h_simp, h_n_prod]

theorem main : H1 → H2 → type_of% @Erdos556.erdos_556.variants.luczak_asymptotic_even := by
  intro h1 h2 ε hε
  classical
  set ε' : ℝ := min ε 1
  have hε' : 0 < ε' := lt_min hε zero_lt_one
  have hε'1 : ε' ≤ 1 := min_le_right ε 1
  have hε'ε : ε' ≤ ε := min_le_left ε 1
  set d : ℝ := ε' / 1000
  set δ : ℝ := ε' / 20
  have hd : 0 < d := by positivity
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ < 1 := by dsimp [δ]; linarith
  obtain ⟨η₀, hη₀, hm₀_all⟩ := h2 d δ hd hδ0 hδ1
  set η : ℝ := min η₀ (ε' / 1000)
  have hη : 0 < η := lt_min hη₀ (by positivity)
  have hη_le0 : η ≤ η₀ := min_le_left _ _
  have hη_le : η ≤ ε' / 1000 := min_le_right _ _
  set l : ℕ := Nat.ceil (1000 / ε')
  have hl_real : 1000 / ε' ≤ (l : ℝ) := Nat.le_ceil _
  have hl_ge : 1000 ≤ l := by
    have : (1000 : ℝ) ≤ 1000 / ε' := by rw [le_div_iff₀ hε']; nlinarith
    exact_mod_cast this.trans hl_real
  have hl_pos : 0 < l := by omega
  obtain ⟨M_bound, hM_eq⟩ : ∃ M, M = SzemerediRegularity.bound η l := ⟨_, rfl⟩
  have hM_pos : 0 < M_bound := hM_eq ▸ SzemerediRegularity.bound_pos η l
  have hl_le_M : l ≤ M_bound := hM_eq ▸ SzemerediRegularity.le_bound η l
  obtain ⟨m_req, hm_req_eq⟩ : ∃ mr, mr = (Finset.range (M_bound + 1)).sup (fun t => (hm₀_all t).choose) :=
    ⟨_, rfl⟩
  obtain ⟨N₀, hN₀_eq⟩ : ∃ n0, n0 = Nat.ceil ((10000 * (M_bound : ℝ) / ε' + (m_req : ℝ) * M_bound + 100) / 3) + 4 :=
    ⟨_, rfl⟩
  rw [Filter.eventually_atTop]
  refine ⟨N₀, fun n hn heven => ?_⟩
  have hN₀_ge4 : 4 ≤ N₀ := by rw [hN₀_eq]; exact Nat.le_add_left 4 _
  have hn4 : 4 ≤ n := hN₀_ge4.trans hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  obtain ⟨N, hN_eq⟩ : ∃ N, N = Nat.floor ((3 + ε') * (n : ℝ)) := ⟨_, rfl⟩
  have hN_le : (N : ℝ) ≤ (3 + ε') * (n : ℝ) := hN_eq ▸ Nat.floor_le (by positivity)
  have hN_gt : (3 + ε') * (n : ℝ) - 1 < (N : ℝ) := hN_eq ▸ Nat.sub_one_lt_floor _
  have hn_bound : (10000 * (M_bound : ℝ) / ε' + (m_req : ℝ) * M_bound + 100) / 3 ≤ (n : ℝ) := by
    have h1n : (N₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h2n : (10000 * (M_bound : ℝ) / ε' + (m_req : ℝ) * M_bound + 100) / 3 ≤
        (Nat.ceil ((10000 * (M_bound : ℝ) / ε' + (m_req : ℝ) * M_bound + 100) / 3) : ℝ) :=
      Nat.le_ceil _
    have h3n : ((Nat.ceil ((10000 * (M_bound : ℝ) / ε' + (m_req : ℝ) * M_bound + 100) / 3) : ℕ) : ℝ) ≤ (N₀ : ℝ) := by
      rw [hN₀_eq]; exact_mod_cast Nat.le_add_right _ 4
    linarith
  have hN_big : 10000 * (M_bound : ℝ) / ε' + (m_req : ℝ) * M_bound + 99 ≤ (N : ℝ) := by
    have h3n : (3 + ε') * (n : ℝ) - 1 ≥ 3 * (n : ℝ) - 1 := by nlinarith
    linarith
  have hN_pos : 0 < N := by
    have : (1 : ℝ) ≤ (N : ℝ) := by
      have : (0 : ℝ) < 10000 * (M_bound : ℝ) / ε' + (m_req : ℝ) * M_bound := by positivity
      linarith
    exact_mod_cast this
  have hRamsey_le : multicolourRamsey (cycleGraph n) 3 ≤ N := by
    apply Nat.sInf_le
    intro c hc
    obtain ⟨ic, hic⟩ := dense_color_of_three_colouring N c hc
    let G := c ic
    have hlN : l ≤ N := by
      have h1 : (l : ℝ) ≤ (M_bound : ℝ) := by exact_mod_cast hl_le_M
      have h2 : (M_bound : ℝ) ≤ 10000 * (M_bound : ℝ) / ε' := by
        rw [le_div_iff₀ hε']; nlinarith only [hε', hε'1]
      have h3 : (10000 * (M_bound : ℝ) / ε' : ℝ) ≤ (N : ℝ) := by
        linarith [show (0 : ℝ) ≤ (m_req : ℝ) * M_bound + 99 by positivity]
      exact Nat.cast_le.mp (h1.trans (h2.trans h3))
    obtain ⟨t, parts, R, _, htl, htM, hdisj, hparts_card, hR_prop, hR_ineq⟩ :=
      regularity_cluster_graph N hN_pos G hic η d hη hd.le l hlN hl_pos
    rw [← hM_eq] at htM
    have ht_pos : 0 < t := lt_of_lt_of_le hl_pos htl
    have ht_ge_1000 : (1000 : ℝ) / ε' ≤ (t : ℝ) := hl_real.trans (by exact_mod_cast htl)
    have ht_1000 : (1000 : ℝ) ≤ (t : ℝ) := by
      have : (1000 : ℝ) ≤ 1000 / ε' := by rw [le_div_iff₀ hε']; nlinarith only [hε', hε'1]
      exact this.trans ht_ge_1000
    obtain ⟨m, hm_eq⟩ : ∃ m, m = N / t := ⟨_, rfl⟩
    obtain ⟨k, hk_eq⟩ : ∃ k, k = Nat.floor ((t : ℝ) / (6 + ε' / 2)) := ⟨_, rfl⟩
    have hk_pos_real : (1 : ℝ) ≤ (t : ℝ) / (6 + ε' / 2) := by
      rw [le_div_iff₀ (by linarith)]; linarith
    have hk1 : 1 ≤ k := by rw [hk_eq]; exact Nat.le_floor (by simpa using hk_pos_real)
    have hm_ge : (hm₀_all t).choose ≤ m := by
      have hsup : (hm₀_all t).choose ≤ m_req := by
        rw [hm_req_eq]
        exact Finset.le_sup (f := fun s => (hm₀_all s).choose)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le htM))
      have hmul : m_req * t ≤ N := by
        have h1 : (m_req : ℝ) * (t : ℝ) ≤ (m_req : ℝ) * (M_bound : ℝ) := by gcongr
        have h2 : (m_req : ℝ) * (M_bound : ℝ) ≤ (N : ℝ) := by
          have : (0 : ℝ) ≤ 10000 * (M_bound : ℝ) / ε' + 99 := by positivity
          linarith
        exact_mod_cast h1.trans h2
      rw [hm_eq]
      exact hsup.trans ((Nat.le_div_iff_mul_le ht_pos).mpr hmul)
    have ht_le_epsN : (t : ℝ) ≤ ε' / 10000 * (N : ℝ) := by
      have h1 : (t : ℝ) ≤ (M_bound : ℝ) := by exact_mod_cast htM
      have h2 : 10000 * (M_bound : ℝ) / ε' ≤ (N : ℝ) := by
        have : (0 : ℝ) ≤ (m_req : ℝ) * M_bound + 99 := by positivity
        linarith
      have h3 : (M_bound : ℝ) ≤ ε' / 10000 * (N : ℝ) := by
        rw [div_le_iff₀ hε'] at h2; linarith
      exact h1.trans h3
    have hk_le : (k : ℝ) ≤ (t : ℝ) / (6 + ε' / 2) := hk_eq ▸ Nat.floor_le (by positivity)
    have hR_gt : (k - 1) * t < R.edgeFinset.card :=
      cluster_edge_bound ε' η d N t k R.edgeFinset.card hε' hε'1 hη_le le_rfl
        ht_pos hN_pos ht_ge_1000 ht_le_epsN hk_le hR_ineq
    obtain ⟨M, hM_match, hM_card, hM_reach⟩ := h1 t k R hk1 hR_gt
    have hn_big3 : 10000 / ε' ≤ 3 * (n : ℝ) := by
      have hM1 : (1 : ℝ) ≤ (M_bound : ℝ) := by exact_mod_cast hM_pos
      have h1 : (10000 : ℝ) ≤ 10000 * (M_bound : ℝ) := by linarith
      have h1' : (10000 : ℝ) / ε' ≤ 10000 * (M_bound : ℝ) / ε' := div_le_div_of_nonneg_right h1 hε'.le
      have h2 : (0 : ℝ) ≤ (m_req : ℝ) * M_bound + 100 := by positivity
      linarith
    have hk_gt : (t : ℝ) / (6 + ε' / 2) - 1 < (k : ℝ) := hk_eq ▸ Nat.sub_one_lt_floor _
    have hm_gt : (N : ℝ) / (t : ℝ) - 1 < (m : ℝ) := by
      rw [hm_eq, sub_lt_iff_lt_add, div_lt_iff₀ (by exact_mod_cast ht_pos)]
      calc (N : ℝ) < (↑(N / t * t + t) : ℝ) := by exact_mod_cast Nat.lt_div_mul_add ht_pos
        _ = (↑(N / t) + 1) * ↑t := by push_cast; ring
    have h_n_le : (n : ℝ) ≤ (1 - δ) * (2 * (k : ℝ) * (m : ℝ)) :=
      blowup_size_bound ε' δ N n t m k hε' hε'1 rfl ht_pos hn_pos ht_ge_1000 ht_le_epsN
        hN_gt hn_big3 hk_gt hm_gt
    have hparts_card' : ∀ i : Fin t, m ≤ (parts i).card ∧ (parts i).card ≤ m + 1 := by
      rw [hm_eq]; exact hparts_card
    exact ⟨ic, (hm₀_all t).choose_spec N n m k G parts R M heven hn4 hk1 hm_ge h_n_le
      hdisj hparts_card' (fun u v huv => ⟨(hR_prop u v huv).1.mono hη_le0, (hR_prop u v huv).2⟩)
      hM_match hM_card hM_reach⟩
  have h_final : (multicolourRamsey (cycleGraph n) 3 : ℝ) ≤ (3 + ε) * (n : ℝ) := by
    calc (multicolourRamsey (cycleGraph n) 3 : ℝ)
        ≤ (N : ℝ) := by exact_mod_cast hRamsey_le
      _ ≤ (3 + ε') * (n : ℝ) := hN_le
      _ ≤ (3 + ε) * (n : ℝ) := by gcongr
  exact h_final

end OMA.Erdos556R1
end R1Section

section H1Section
/- A dense component yields a matching by coloring each edge with the sum of its endpoint labels. -/

open SimpleGraph Finset
open scoped SimpleGraph

-- Credit: @MrSeizy
theorem h1_proof : OMA.Erdos556R1.H1 := by
  intro t k R _ hk hd
  classical
  let S (c : R.ConnectedComponent) := univ.filter (fun x => R.connectedComponentMk x = c)
  let comp (e : Sym2 (Fin t)) := R.connectedComponentMk e.out.1
  let E (c : R.ConnectedComponent) := R.edgeFinset.filter (fun e => comp e = c)
  have hS : ∑ c, (S c).card = t := by
    simpa [S] using sum_card_fiberwise_eq_card_filter (univ : Finset (Fin t)) univ
      R.connectedComponentMk
  have hE : ∑ c, (E c).card = R.edgeFinset.card := by
    simpa [E] using sum_card_fiberwise_eq_card_filter R.edgeFinset univ comp
  obtain ⟨c, hc⟩ : ∃ c, (k - 1) * (S c).card < (E c).card := by
    by_contra! h
    have hle := sum_le_sum (fun c (_ : c ∈ univ) => h c)
    rw [← mul_sum, hS, hE] at hle
    omega
  have hmem (x : Fin t) : x ∈ S c ↔ x ∈ c.supp := by simp [S]
  have hends {x y : Fin t} (he : s(x,y) ∈ E c) : x ∈ S c ∧ y ∈ S c := by
    obtain ⟨hR, hcomp⟩ := mem_filter.mp he
    have hadj : R.Adj x y := mem_edgeFinset.mp hR
    have hout : (s(x,y) : Sym2 (Fin t)).out.1 ∈ c.supp := hcomp
    have hxy := c.mem_supp_congr_adj hadj
    rcases Sym2.mem_iff.mp (Sym2.out_fst_mem s(x,y)) with hx | hy
    · rw [hx] at hout
      exact ⟨(hmem _).mpr hout, (hmem _).mpr (hxy.mp hout)⟩
    · rw [hy] at hout
      exact ⟨(hmem _).mpr (hxy.mpr hout), (hmem _).mpr hout⟩
  have hspos : 0 < (S c).card := by
    obtain ⟨x, hx⟩ := c.nonempty_supp
    exact card_pos.mpr ⟨x, (hmem _).mpr hx⟩
  let : NeZero (S c).card := ⟨hspos.ne'⟩
  -- The finite-set labeling follows the odd_lower_bound sibling proof.
  let equiv : S c ≃ Fin (S c).card := Finset.equivFinOfCardEq rfl
  let label (x : Fin t) : Fin (S c).card := if hx : x ∈ S c then equiv ⟨x, hx⟩ else 0
  have hinj {x y} (hx : x ∈ S c) (hy : y ∈ S c) (h : label x = label y) : x = y := by
    simp only [label, dif_pos hx, dif_pos hy] at h
    exact congrArg Subtype.val (equiv.injective h)
  let color : Sym2 (Fin t) → Fin (S c).card :=
    Sym2.lift ⟨fun x y => label x + label y, fun x y => add_comm _ _⟩
  obtain ⟨a, _, ha⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := E c) (t := univ) (f := color) (fun _ _ => mem_univ _)
    (by simpa [Nat.mul_comm] using hc)
  let F := (E c).filter (fun e => color e = a)
  have hsize : k ≤ F.card := by
    change k - 1 < F.card at ha
    omega
  have uniqueNbr {x y z : Fin t} (hy : s(x,y) ∈ F) (hz : s(x,z) ∈ F) : y = z := by
    obtain ⟨he, hy'⟩ := mem_filter.mp hy
    obtain ⟨hf, hz'⟩ := mem_filter.mp hz
    have h : label x + label y = label x + label z := hy'.trans hz'.symm
    exact hinj (hends he).2 (hends hf).2 (add_left_cancel h)
  let M : R.Subgraph := {
    verts := ↑(F.biUnion Sym2.toFinset)
    Adj := fun x y => s(x,y) ∈ F
    adj_sub := fun h => mem_edgeFinset.mp (mem_filter.mp (mem_filter.mp h).1).1
    edge_vert := fun {x y} h => mem_biUnion.mpr ⟨_, h, Sym2.mem_toFinset.mpr (Sym2.mem_mk_left x y)⟩
    symm := ⟨fun x y h => by rwa [Sym2.eq_swap]⟩ }
  have incident {x : Fin t} (hx : x ∈ M.verts) : ∃ y, s(x,y) ∈ F := by
    obtain ⟨e, he, hx'⟩ := mem_biUnion.mp hx
    obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp (Sym2.mem_toFinset.mp hx')
    exact ⟨y, he⟩
  have disj : (F : Set (Sym2 (Fin t))).PairwiseDisjoint Sym2.toFinset := by
    intro e he f hf hne
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp (Sym2.mem_toFinset.mp hx)
    obtain ⟨z, rfl⟩ := Sym2.mem_iff_exists.mp (Sym2.mem_toFinset.mp hx')
    exact hne (congrArg (fun w => s(x,w)) (uniqueNbr he hf))
  have inside {x : Fin t} (hx : x ∈ M.verts) : x ∈ c.supp := by
    obtain ⟨y, hy⟩ := incident hx
    exact (hmem x).mp (hends (mem_filter.mp hy).1).1
  refine ⟨M, ?_, ?_, fun _ hu _ hv => c.reachable_of_mem_supp (inside hu) (inside hv)⟩
  · intro x hx
    obtain ⟨y, hy⟩ := incident hx
    exact ⟨y, hy, fun _ hz => uniqueNbr hz hy⟩
  · have hcard (e) (he : e ∈ F) : e.toFinset.card = 2 :=
      e.card_toFinset_of_not_isDiag (R.not_isDiag_of_mem_edgeFinset
        (mem_filter.mp (mem_filter.mp he).1).1)
    change 2 * k ≤ (↑(F.biUnion Sym2.toFinset) : Set (Fin t)).ncard
    rw [Set.ncard_coe_finset, card_biUnion disj, sum_const_nat hcard, Nat.mul_comm F.card]
    omega
end H1Section

section H2Section
open SimpleGraph Finset

namespace H2Proof

/- ### Uniformity and typical-degree helpers -/

private lemma card_bad_lt {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    {d η : ℝ} (hη : 0 < η) {U V V' : Finset (Fin N)}
    (huni : G.IsUniform η U V) (hd : d ≤ (G.edgeDensity U V : ℝ))
    (hU : 0 < U.card) (hV : 0 < V.card) (hV' : V' ⊆ V)
    (hV'card : (V.card : ℝ) * η ≤ (V'.card : ℝ)) :
    ((U.filter (fun u => ((G.neighborFinset u ∩ V').card : ℝ) ≤ (d - η) * (V'.card : ℝ))).card : ℝ) <
      (U.card : ℝ) * η := by
  set B := U.filter (fun u => ((G.neighborFinset u ∩ V').card : ℝ) ≤ (d - η) * (V'.card : ℝ))
  by_contra! hle
  have hB_pos : 0 < B.card := by
    have h1 : (0 : ℝ) < (U.card : ℝ) * η := by positivity
    exact_mod_cast h1.trans_le hle
  have hV'_pos : 0 < V'.card := by
    have h1 : (0 : ℝ) < (V.card : ℝ) * η := by positivity
    exact_mod_cast h1.trans_le hV'card
  have hdiff := huni (Finset.filter_subset _ _) hV' hle hV'card
  have hgt : d - η < (G.edgeDensity B V' : ℝ) := by
    rw [abs_sub_lt_iff] at hdiff
    linarith
  have hsub : G.interedges B V' ⊆
      B.biUnion (fun u => (G.neighborFinset u ∩ V').image (fun v => (u, v))) := by
    intro ⟨u, v⟩ huv
    rw [SimpleGraph.mk_mem_interedges_iff] at huv
    exact Finset.mem_biUnion.mpr ⟨u, huv.1,
      Finset.mem_image.mpr ⟨v, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset u v).mpr huv.2.2, huv.2.1⟩, rfl⟩⟩
  have hcard_ie : (G.interedges B V').card ≤ ∑ u ∈ B, (G.neighborFinset u ∩ V').card := by
    calc (G.interedges B V').card
        ≤ (B.biUnion (fun u => (G.neighborFinset u ∩ V').image (fun v => (u, v)))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ u ∈ B, ((G.neighborFinset u ∩ V').image (fun v => (u, v))).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ u ∈ B, (G.neighborFinset u ∩ V').card :=
          Finset.sum_le_sum fun _ _ => Finset.card_image_le
  have hcard_real : ((G.interedges B V').card : ℝ) ≤ (B.card : ℝ) * ((d - η) * (V'.card : ℝ)) := by
    calc ((G.interedges B V').card : ℝ)
        ≤ ((∑ u ∈ B, (G.neighborFinset u ∩ V').card : ℕ) : ℝ) := Nat.cast_le.mpr hcard_ie
      _ = ∑ u ∈ B, ((G.neighborFinset u ∩ V').card : ℝ) := by push_cast; rfl
      _ ≤ ∑ _u ∈ B, (d - η) * (V'.card : ℝ) := by
          refine Finset.sum_le_sum fun u hu => ?_
          exact (Finset.mem_filter.mp hu).2
      _ = (B.card : ℝ) * ((d - η) * (V'.card : ℝ)) := by simp [Finset.sum_const, nsmul_eq_mul]
  have hden_pos : (0 : ℝ) < (B.card : ℝ) * (V'.card : ℝ) := by positivity
  have hle_den : (G.edgeDensity B V' : ℝ) ≤ d - η := by
    rw [SimpleGraph.edgeDensity_def]
    push_cast
    rw [div_le_iff₀ hden_pos]
    linarith
  linarith

private lemma exists_good_two {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    {d η : ℝ} (hη : 0 < η) {U P avoid V₁ T₁ V₂ T₂ : Finset (Fin N)}
    (hPU : P ⊆ U) (hU : 0 < U.card)
    (huni₁ : G.IsUniform η U V₁) (hd₁ : d ≤ (G.edgeDensity U V₁ : ℝ))
    (hV₁ : 0 < V₁.card) (hT₁ : T₁ ⊆ V₁) (hT₁c : (V₁.card : ℝ) * η ≤ (T₁.card : ℝ))
    (huni₂ : G.IsUniform η U V₂) (hd₂ : d ≤ (G.edgeDensity U V₂ : ℝ))
    (hV₂ : 0 < V₂.card) (hT₂ : T₂ ⊆ V₂) (hT₂c : (V₂.card : ℝ) * η ≤ (T₂.card : ℝ))
    (hP : (avoid.card : ℝ) + 2 * (U.card : ℝ) * η ≤ (P.card : ℝ)) :
    ∃ u ∈ P, u ∉ avoid ∧
      (d - η) * (T₁.card : ℝ) < ((G.neighborFinset u ∩ T₁).card : ℝ) ∧
      (d - η) * (T₂.card : ℝ) < ((G.neighborFinset u ∩ T₂).card : ℝ) := by
  set B₁ := U.filter (fun u => ((G.neighborFinset u ∩ T₁).card : ℝ) ≤ (d - η) * (T₁.card : ℝ))
  set B₂ := U.filter (fun u => ((G.neighborFinset u ∩ T₂).card : ℝ) ≤ (d - η) * (T₂.card : ℝ))
  have hB₁ : (B₁.card : ℝ) < (U.card : ℝ) * η := card_bad_lt G hη huni₁ hd₁ hU hV₁ hT₁ hT₁c
  have hB₂ : (B₂.card : ℝ) < (U.card : ℝ) * η := card_bad_lt G hη huni₂ hd₂ hU hV₂ hT₂ hT₂c
  set rem := P \ (avoid ∪ B₁ ∪ B₂)
  have hrem_pos : 0 < rem.card := by
    have h1 : P.card ≤ rem.card + (avoid ∪ B₁ ∪ B₂).card := by
      calc P.card ≤ (rem ∪ (avoid ∪ B₁ ∪ B₂)).card := Finset.card_le_card (fun x hx => by
            by_cases h : x ∈ avoid ∪ B₁ ∪ B₂
            · exact Finset.mem_union_right _ h
            · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, h⟩))
        _ ≤ rem.card + (avoid ∪ B₁ ∪ B₂).card := Finset.card_union_le _ _
    have h2 : (avoid ∪ B₁ ∪ B₂).card ≤ avoid.card + B₁.card + B₂.card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    have h12 : P.card ≤ rem.card + avoid.card + B₁.card + B₂.card := by omega
    have h3 : ((P.card : ℝ)) ≤ (rem.card : ℝ) + (avoid.card : ℝ) + (B₁.card : ℝ) + (B₂.card : ℝ) := by
      exact_mod_cast h12
    have h4 : (0 : ℝ) < (rem.card : ℝ) := by linarith
    exact_mod_cast h4
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hrem_pos
  rw [Finset.mem_sdiff, Finset.mem_union, Finset.mem_union] at hu
  have huU : u ∈ U := hPU hu.1
  have hnotB₁ : u ∉ B₁ := fun h => hu.2 (Or.inl (Or.inr h))
  have hnotB₂ : u ∉ B₂ := fun h => hu.2 (Or.inr h)
  refine ⟨u, hu.1, fun h => hu.2 (Or.inl (Or.inl h)), ?_, ?_⟩
  · by_contra! hle
    exact hnotB₁ (Finset.mem_filter.mpr ⟨huU, hle⟩)
  · by_contra! hle
    exact hnotB₂ (Finset.mem_filter.mpr ⟨huU, hle⟩)

private lemma no_empty_pair_of_uniform {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    {d η : ℝ} (hd_gt : η < d) {U V A' B' : Finset (Fin N)}
    (huni : G.IsUniform η U V) (hd : d ≤ (G.edgeDensity U V : ℝ))
    (hA' : A' ⊆ U) (hB' : B' ⊆ V) {cA cB : ℕ}
    (hcA : (U.card : ℝ) * η ≤ (cA : ℝ)) (hcB : (V.card : ℝ) * η ≤ (cB : ℝ)) :
    ∀ X ⊆ A', ∀ Y ⊆ B', cA ≤ X.card → cB ≤ Y.card → ∃ x ∈ X, ∃ y ∈ Y, G.Adj x y := by
  intro X hX Y hY hXc hYc
  have hX' : (U.card : ℝ) * η ≤ (X.card : ℝ) := hcA.trans (Nat.cast_le.mpr hXc)
  have hY' : (V.card : ℝ) * η ≤ (Y.card : ℝ) := hcB.trans (Nat.cast_le.mpr hYc)
  have hdiff := huni (hX.trans hA') (hY.trans hB') hX' hY'
  have hpos : (0 : ℝ) < (G.edgeDensity X Y : ℝ) := by
    rw [abs_sub_lt_iff] at hdiff
    linarith
  have hne : (G.interedges X Y).Nonempty := by
    rw [SimpleGraph.edgeDensity_def] at hpos
    push_cast at hpos
    by_contra! hem
    simp [hem] at hpos
  obtain ⟨⟨x, y⟩, hxy⟩ := hne
  rw [SimpleGraph.mk_mem_interedges_iff] at hxy
  exact ⟨x, hxy.1, y, hxy.2.1, hxy.2.2⟩

/- ### Splitting a cluster into disjoint Res, Cap, Body -/

private lemma split_cluster {N : ℕ} (S : Finset (Fin N)) (q : ℕ) (hq : 2 * q ≤ S.card) :
    ∃ Res Cap Body : Finset (Fin N),
      Res ⊆ S ∧ Cap ⊆ S ∧ Body ⊆ S ∧
      Disjoint Res Cap ∧ Disjoint Res Body ∧ Disjoint Cap Body ∧
      Res.card = q ∧ Cap.card = q ∧ Body.card = S.card - 2 * q := by
  classical
  set L := S.toList
  have hnodup : L.Nodup := S.nodup_toList
  have hlen : L.length = S.card := S.length_toList
  set L1 := L.take q
  set L2 := (L.drop q).take q
  set L3 := L.drop (2 * q)
  have hcat : L1 ++ L2 ++ L3 = L := by
    have h1 : L2 ++ L3 = L.drop q := by
      simp only [L2, L3]
      rw [show 2 * q = q + q by omega, ← List.drop_drop]
      exact List.take_append_drop q (L.drop q)
    rw [List.append_assoc, h1]
    exact List.take_append_drop q L
  have hnodup_cat : (L1 ++ L2 ++ L3).Nodup := hcat.symm ▸ hnodup
  have hn12 : (L1 ++ L2).Nodup := (List.nodup_append.mp hnodup_cat).1
  have hn1 : L1.Nodup := (List.nodup_append.mp hn12).1
  have hn2 : L2.Nodup := (List.nodup_append.mp hn12).2.1
  have hn3 : L3.Nodup := (List.nodup_append.mp hnodup_cat).2.1
  refine ⟨L1.toFinset, L2.toFinset, L3.toFinset, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [List.mem_toFinset] at hx
    exact S.mem_toList.mp (by show x ∈ L; rw [← hcat]; exact List.mem_append_left _ (List.mem_append_left _ hx))
  · intro x hx
    rw [List.mem_toFinset] at hx
    exact S.mem_toList.mp (by show x ∈ L; rw [← hcat]; exact List.mem_append_left _ (List.mem_append_right _ hx))
  · intro x hx
    rw [List.mem_toFinset] at hx
    exact S.mem_toList.mp (by show x ∈ L; rw [← hcat]; exact List.mem_append_right _ hx)
  · rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [List.mem_toFinset] at hx1 hx2
    exact (List.nodup_append.mp hn12).2.2 x hx1 x hx2 rfl
  · rw [Finset.disjoint_left]
    intro x hx1 hx3
    rw [List.mem_toFinset] at hx1 hx3
    exact (List.nodup_append.mp hnodup_cat).2.2 x (List.mem_append_left _ hx1) x hx3 rfl
  · rw [Finset.disjoint_left]
    intro x hx2 hx3
    rw [List.mem_toFinset] at hx2 hx3
    exact (List.nodup_append.mp hnodup_cat).2.2 x (List.mem_append_right _ hx2) x hx3 rfl
  · rw [List.toFinset_card_of_nodup hn1, List.length_take, hlen]
    omega
  · rw [List.toFinset_card_of_nodup hn2, List.length_take, List.length_drop, hlen]
    omega
  · rw [List.toFinset_card_of_nodup hn3, List.length_drop, hlen]

/- ### DFS long alternating path lemma -/

private noncomputable def bipartAdj {N : ℕ} (G : SimpleGraph (Fin N))
    (A' B' : Finset (Fin N)) (x y : Fin N) : Prop :=
  ((x ∈ A' ∧ y ∈ B') ∨ (x ∈ B' ∧ y ∈ A')) ∧ G.Adj x y

private lemma bipartAdj_symm {N : ℕ} {G : SimpleGraph (Fin N)} {A' B' : Finset (Fin N)}
    {x y : Fin N} (h : bipartAdj G A' B' x y) : bipartAdj G A' B' y x :=
  ⟨by rcases h.1 with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> [exact Or.inr ⟨hy, hx⟩; exact Or.inl ⟨hy, hx⟩],
    h.2.symm⟩

open Classical in
private noncomputable def dfsStep {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A' B' : Finset (Fin N)) (cA cB : ℕ)
    (P : List (Fin N)) (D W : Finset (Fin N)) :
    List (Fin N) × Finset (Fin N) × Finset (Fin N) :=
  if _ : cA ≤ (D ∩ A').card ∨ cB ≤ (D ∩ B').card then (P, D, W)
  else match P with
  | [] => ([], D, W)
  | v :: rest =>
    if hex : ∃ w ∈ W, bipartAdj G A' B' v w then
      dfsStep G A' B' cA cB (hex.choose :: v :: rest) D (W.erase hex.choose)
    else
      dfsStep G A' B' cA cB rest (insert v D) W
termination_by 2 * W.card + P.length
decreasing_by
  · have hc : (W.erase hex.choose).card < W.card := Finset.card_erase_lt_of_mem hex.choose_spec.1
    simp only [List.length_cons]
    omega
  · simp only [List.length_cons]
    omega

open Classical in
private lemma dfsStep_spec {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A' B' : Finset (Fin N)) (hdisj : Disjoint A' B') (cA cB : ℕ)
    (a₀ : Fin N) (ha₀ : a₀ ∈ A') (hdeg₀ : cB ≤ (G.neighborFinset a₀ ∩ B').card) :
    ∀ n : ℕ, ∀ (P : List (Fin N)) (D W : Finset (Fin N)),
      2 * W.card + P.length = n →
      P ≠ [] →
      P.getLast? = some a₀ →
      P.Nodup →
      P.IsChain (bipartAdj G A' B') →
      P.toFinset ⊆ A' ∪ B' →
      D ⊆ A' ∪ B' →
      W ⊆ A' ∪ B' →
      A' ∪ B' ⊆ P.toFinset ∪ D ∪ W →
      Disjoint D W →
      Disjoint D P.toFinset →
      Disjoint W P.toFinset →
      (∀ d ∈ D, ∀ w ∈ W, ¬ bipartAdj G A' B' d w) →
      (D ∩ A').card ≤ cA →
      (D ∩ B').card ≤ cB →
      let res := dfsStep G A' B' cA cB P D W
      res.1 ≠ [] ∧
      res.1.getLast? = some a₀ ∧
      res.1.Nodup ∧
      res.1.IsChain (bipartAdj G A' B') ∧
      res.1.toFinset ⊆ A' ∪ B' ∧
      res.2.1 ⊆ A' ∪ B' ∧
      res.2.2 ⊆ A' ∪ B' ∧
      A' ∪ B' ⊆ res.1.toFinset ∪ res.2.1 ∪ res.2.2 ∧
      (∀ d ∈ res.2.1, ∀ w ∈ res.2.2, ¬ bipartAdj G A' B' d w) ∧
      (res.2.1 ∩ A').card ≤ cA ∧
      (res.2.1 ∩ B').card ≤ cB ∧
      (cA ≤ (res.2.1 ∩ A').card ∨ cB ≤ (res.2.1 ∩ B').card) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro P D W hn hPne hPlast hPnodup hPchain hPsub hDsub hWsub hcov
      hDW hDP hWP hnoEdge hDA hDB
    unfold dfsStep
    by_cases hstop : cA ≤ (D ∩ A').card ∨ cB ≤ (D ∩ B').card
    · simp only [dif_pos hstop]
      exact ⟨hPne, hPlast, hPnodup, hPchain, hPsub, hDsub, hWsub, hcov, hnoEdge, hDA, hDB, hstop⟩
    · simp only [dif_neg hstop]
      rcases P with _ | ⟨v, rest⟩
      · exact (hPne rfl).elim
      · by_cases hex : ∃ w ∈ W, bipartAdj G A' B' v w
        · simp only [dif_pos hex]
          set w := hex.choose
          have hwW : w ∈ W := hex.choose_spec.1
          have hvw : bipartAdj G A' B' v w := hex.choose_spec.2
          have hwsub : w ∈ A' ∪ B' := hWsub hwW
          have hwnP : w ∉ (v :: rest).toFinset := Finset.disjoint_left.mp hWP hwW
          have hwnD : w ∉ D := Finset.disjoint_right.mp hDW hwW
          have hlt : 2 * (W.erase w).card + (w :: v :: rest).length < n := by
            have hc := Finset.card_erase_lt_of_mem hwW
            simp only [List.length_cons] at hn ⊢
            omega
          refine ih _ hlt (w :: v :: rest) D (W.erase w) rfl (by simp) ?_ ?_ ?_ ?_ hDsub ?_ ?_ ?_ ?_ ?_ ?_ hDA hDB
          · simpa using hPlast
          · exact List.nodup_cons.mpr ⟨by simpa [List.mem_toFinset] using hwnP, hPnodup⟩
          · exact List.IsChain.cons_cons (bipartAdj_symm hvw) hPchain
          · intro x hx
            rw [List.toFinset_cons, Finset.mem_insert] at hx
            rcases hx with rfl | hx
            · exact hwsub
            · exact hPsub hx
          · exact (Finset.erase_subset w W).trans hWsub
          · intro x hx
            rcases Finset.mem_union.mp (hcov hx) with hPD | hW
            · rcases Finset.mem_union.mp hPD with hP | hD
              · rw [List.toFinset_cons, Finset.mem_union, Finset.mem_union, Finset.mem_insert]
                exact Or.inl (Or.inl (Or.inr hP))
              · exact Finset.mem_union_left _ (Finset.mem_union_right _ hD)
            · by_cases hxw : x = w
              · subst hxw
                rw [List.toFinset_cons, Finset.mem_union, Finset.mem_union, Finset.mem_insert]
                exact Or.inl (Or.inl (Or.inl rfl))
              · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hxw, hW⟩)
          · exact Finset.disjoint_of_subset_right (Finset.erase_subset w W) hDW
          · rw [List.toFinset_cons, Finset.disjoint_insert_right]
            exact ⟨hwnD, hDP⟩
          · rw [List.toFinset_cons, Finset.disjoint_insert_right]
            exact ⟨Finset.notMem_erase w W, Finset.disjoint_of_subset_left (Finset.erase_subset w W) hWP⟩
          · intro d hd x hx
            exact hnoEdge d hd x (Finset.mem_of_mem_erase hx)
        · simp only [dif_neg hex]
          have hvP : v ∈ (v :: rest).toFinset := by simp
          have hvsub : v ∈ A' ∪ B' := hPsub hvP
          have hvnD : v ∉ D := Finset.disjoint_right.mp hDP hvP
          have hvnW : v ∉ W := Finset.disjoint_right.mp hWP hvP
          have hvnR : v ∉ rest.toFinset := by
            intro h
            have : v ∈ rest := List.mem_toFinset.mp h
            exact (List.nodup_cons.mp hPnodup).1 this
          have hrest_ne : rest ≠ [] := by
            intro hnil
            subst hnil
            simp only [List.getLast?_singleton, Option.some.injEq] at hPlast
            subst hPlast
            have hsubB : G.neighborFinset v ∩ B' ⊆ D ∩ B' := by
              intro b hb
              rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hb
              have hbAB : b ∈ A' ∪ B' := Finset.mem_union_right _ hb.2
              rcases Finset.mem_union.mp (hcov hbAB) with hPD | hW
              · rcases Finset.mem_union.mp hPD with hP | hD
                · rw [List.mem_toFinset, List.mem_singleton] at hP
                  subst hP
                  exact (Finset.disjoint_left.mp hdisj ha₀ hb.2).elim
                · exact Finset.mem_inter.mpr ⟨hD, hb.2⟩
              · exact (hex ⟨b, hW, Or.inl ⟨ha₀, hb.2⟩, hb.1⟩).elim
            have hle : cB ≤ (D ∩ B').card := hdeg₀.trans (Finset.card_le_card hsubB)
            exact hstop (Or.inr hle)
          have hlt : 2 * W.card + rest.length < n := by
            simp only [List.length_cons] at hn
            omega
          have hDA' : ((insert v D) ∩ A').card ≤ cA := by
            by_cases hvA : v ∈ A'
            · have : insert v D ∩ A' = insert v (D ∩ A') := by
                ext x; simp only [Finset.mem_inter, Finset.mem_insert]
                exact ⟨fun ⟨h1, h2⟩ => h1.elim Or.inl (fun hd => Or.inr ⟨hd, h2⟩),
                       fun h => h.elim (fun he => ⟨Or.inl he, he ▸ hvA⟩) (fun ⟨hd, ha⟩ => ⟨Or.inr hd, ha⟩)⟩
              rw [this, Finset.card_insert_of_notMem (fun h => hvnD (Finset.mem_inter.mp h).1)]
              have : (D ∩ A').card < cA := not_le.mp (fun h => hstop (Or.inl h))
              omega
            · have : insert v D ∩ A' = D ∩ A' := by
                ext x; simp only [Finset.mem_inter, Finset.mem_insert]
                exact ⟨fun ⟨h1, h2⟩ => ⟨h1.elim (fun he => (hvA (he ▸ h2)).elim) id, h2⟩,
                       fun ⟨hd, ha⟩ => ⟨Or.inr hd, ha⟩⟩
              rw [this]
              exact (not_le.mp (fun h => hstop (Or.inl h))).le
          have hDB' : ((insert v D) ∩ B').card ≤ cB := by
            by_cases hvB : v ∈ B'
            · have : insert v D ∩ B' = insert v (D ∩ B') := by
                ext x; simp only [Finset.mem_inter, Finset.mem_insert]
                exact ⟨fun ⟨h1, h2⟩ => h1.elim Or.inl (fun hd => Or.inr ⟨hd, h2⟩),
                       fun h => h.elim (fun he => ⟨Or.inl he, he ▸ hvB⟩) (fun ⟨hd, hb⟩ => ⟨Or.inr hd, hb⟩)⟩
              rw [this, Finset.card_insert_of_notMem (fun h => hvnD (Finset.mem_inter.mp h).1)]
              have : (D ∩ B').card < cB := not_le.mp (fun h => hstop (Or.inr h))
              omega
            · have : insert v D ∩ B' = D ∩ B' := by
                ext x; simp only [Finset.mem_inter, Finset.mem_insert]
                exact ⟨fun ⟨h1, h2⟩ => ⟨h1.elim (fun he => (hvB (he ▸ h2)).elim) id, h2⟩,
                       fun ⟨hd, hb⟩ => ⟨Or.inr hd, hb⟩⟩
              rw [this]
              exact (not_le.mp (fun h => hstop (Or.inr h))).le
          refine ih _ hlt rest (insert v D) W rfl hrest_ne ?_ (List.nodup_cons.mp hPnodup).2
            hPchain.tail ?_ ?_ hWsub ?_ ?_ ?_ ?_ ?_ hDA' hDB'
          · rcases rest with _ | ⟨r, rs⟩
            · exact (hrest_ne rfl).elim
            · simpa using hPlast
          · exact fun x hx => hPsub (by simp [List.mem_toFinset] at hx ⊢; right; exact hx)
          · rw [Finset.insert_subset_iff]
            exact ⟨hvsub, hDsub⟩
          · intro x hx
            rcases Finset.mem_union.mp (hcov hx) with hPD | hW
            · rcases Finset.mem_union.mp hPD with hP | hD
              · simp only [List.toFinset_cons, Finset.mem_insert] at hP
                rcases hP with rfl | hxR
                · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_insert_self _ _))
                · exact Finset.mem_union_left _ (Finset.mem_union_left _ hxR)
              · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_insert_of_mem hD))
            · exact Finset.mem_union_right _ hW
          · exact Finset.disjoint_insert_left.mpr ⟨hvnW, hDW⟩
          · rw [Finset.disjoint_insert_left]
            exact ⟨hvnR, Finset.disjoint_of_subset_right
              (by intro x hx; simp [List.mem_toFinset] at hx ⊢; right; exact hx) hDP⟩
          · exact Finset.disjoint_of_subset_right
              (by intro x hx; simp [List.mem_toFinset] at hx ⊢; right; exact hx) hWP
          · intro d hd w hw hadj
            rcases Finset.mem_insert.mp hd with rfl | hd
            · exact hex ⟨w, hw, hadj⟩
            · exact hnoEdge d hd w hw hadj

private lemma alternating_chain_props {N : ℕ} (G : SimpleGraph (Fin N)) :
    ∀ (Q : List (Fin N)) (A' B' : Finset (Fin N)),
      Disjoint A' B' → Q ≠ [] →
      (∀ h : Q ≠ [], Q.head h ∈ A') →
      Q.IsChain (bipartAdj G A' B') → Q.Nodup →
      (Q.toFinset ∩ A').card ≤ (Q.length + 1) / 2 ∧
      (Q.toFinset ∩ B').card ≤ Q.length / 2 ∧
      (∀ i (hi : i < Q.length), (Even i → Q[i] ∈ A') ∧ (Odd i → Q[i] ∈ B')) := by
  intro Q
  induction Q with
  | nil => intro _ _ _ hne; exact (hne rfl).elim
  | cons a t ih =>
    intro A' B' hdisj _ hhead hchain hnodup
    have haA : a ∈ A' := hhead (by simp)
    have haB : a ∉ B' := Finset.disjoint_left.mp hdisj haA
    rcases t with _ | ⟨b, ts⟩
    · refine ⟨?_, ?_, ?_⟩
      · simp [haA]
      · simp [haB]
      · intro i hi
        have hi0 : i = 0 := by simpa using hi
        subst hi0
        exact ⟨fun _ => haA, fun hodd => by simp at hodd⟩
    · have hab : bipartAdj G A' B' a b := List.IsChain.rel_head hchain
      have hbB : b ∈ B' := by
        rcases hab.1 with ⟨_, hb⟩ | ⟨ha, _⟩
        · exact hb
        · exact (haB ha).elim
      have hchain_t : (b :: ts).IsChain (bipartAdj G B' A') := by
        refine hchain.tail.imp fun {x y} hxy => ?_
        rcases hxy.1 with ⟨hx, hy⟩ | ⟨hx, hy⟩
        · exact ⟨Or.inr ⟨hx, hy⟩, hxy.2⟩
        · exact ⟨Or.inl ⟨hx, hy⟩, hxy.2⟩
      have hrec := ih B' A' hdisj.symm (by simp) (fun _ => hbB) hchain_t (List.nodup_cons.mp hnodup).2
      have hanT : a ∉ (b :: ts).toFinset := by
        simpa [List.mem_toFinset] using (List.nodup_cons.mp hnodup).1
      have hsubA : (a :: b :: ts).toFinset ∩ A' = insert a ((b :: ts).toFinset ∩ A') := by
        ext x; simp [haA]
      have hsubB : (a :: b :: ts).toFinset ∩ B' = (b :: ts).toFinset ∩ B' := by
        ext x; simp [haB]
      refine ⟨?_, ?_, ?_⟩
      · rw [hsubA, Finset.card_insert_of_notMem (fun h => hanT (Finset.mem_inter.mp h).1)]
        have := hrec.2.1
        simp only [List.length_cons] at this ⊢
        omega
      · rw [hsubB]
        have := hrec.1
        simp only [List.length_cons] at this ⊢
        omega
      · intro i hi
        rcases i with _ | i
        · exact ⟨fun _ => haA, fun hodd => by simp at hodd⟩
        · have hi' : i < (b :: ts).length := by simpa using hi
          have hstep := hrec.2.2 i hi'
          refine ⟨fun heven => ?_, fun hodd => ?_⟩
          · rcases Nat.even_or_odd i with h | h
            · exact absurd h (Nat.even_add_one.mp heven)
            · exact hstep.2 h
          · rcases Nat.even_or_odd i with h | h
            · exact hstep.1 h
            · exact absurd h (Nat.odd_add_one.mp hodd)

private lemma dfs_long_path {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A' B' : Finset (Fin N)) (hdisj : Disjoint A' B') {cA cB : ℕ}
    (hcA : 0 < cA) (hcB : 0 < cB)
    (hnoempty : ∀ X ⊆ A', ∀ Y ⊆ B', cA ≤ X.card → cB ≤ Y.card → ∃ x ∈ X, ∃ y ∈ Y, G.Adj x y)
    (a₀ : Fin N) (ha₀ : a₀ ∈ A') (hdeg₀ : cB ≤ (G.neighborFinset a₀ ∩ B').card) :
    ∃ Q : List (Fin N),
      Q ≠ [] ∧ Q.head? = some a₀ ∧ Q.Nodup ∧ Q.IsChain (bipartAdj G A' B') ∧
      Q.toFinset ⊆ A' ∪ B' ∧
      2 * (min A'.card B'.card - 2 * max cA cB) + 1 ≤ Q.length ∧
      (∀ i (hi : i < Q.length), (Even i → Q[i] ∈ A') ∧ (Odd i → Q[i] ∈ B')) := by
  have ha₀_sub : a₀ ∈ A' ∪ B' := Finset.mem_union_left _ ha₀
  set W₀ := (A' ∪ B').erase a₀
  have hspec := dfsStep_spec G A' B' hdisj cA cB a₀ ha₀ hdeg₀
    (2 * W₀.card + [a₀].length) [a₀] ∅ W₀ rfl (by simp) (by simp) (by simp) (by simp)
    (by simp [ha₀_sub]) (by simp) (Finset.erase_subset _ _)
    (fun x hx => by
      by_cases h : x = a₀
      · subst h; simp
      · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨h, hx⟩))
    (by simp) (by simp) (by simp [W₀]) (by simp) (by simp) (by simp)
  set res := dfsStep G A' B' cA cB [a₀] ∅ W₀
  set P := res.1
  set D := res.2.1
  set W := res.2.2
  obtain ⟨hPne, hPlast, hPnodup, hPchain, hPsub, hDsub, hWsub, hcov, hnoEdge, hDA, hDB, hstop⟩ := hspec
  set Q := P.reverse
  have hQne : Q ≠ [] := by simpa [Q] using hPne
  have hQhead : Q.head? = some a₀ := by
    rw [List.head?_reverse]
    exact hPlast
  have hQnodup : Q.Nodup := List.nodup_reverse.mpr hPnodup
  have hQchain : Q.IsChain (bipartAdj G A' B') := by
    rw [List.isChain_reverse]
    exact hPchain.imp (fun {_ _} h => bipartAdj_symm h)
  have hQsub : Q.toFinset ⊆ A' ∪ B' := by
    intro x hx
    exact hPsub (by simpa [Q] using hx)
  have hprops := alternating_chain_props G Q A' B' hdisj hQne (fun h => by
    have := List.head?_eq_some_head h
    rw [hQhead] at this
    exact (Option.some.inj this).symm ▸ ha₀) hQchain hQnodup
  have hQpos : 0 < Q.length := List.length_pos_of_ne_nil hQne
  have hlen : 2 * (min A'.card B'.card - 2 * max cA cB) + 1 ≤ Q.length := by
    rcases hstop with hDA_ge | hDB_ge
    · have hWB : (W ∩ B').card < cB := by
        by_contra! hWB_ge
        obtain ⟨x, hx, y, hy, hadj⟩ := hnoempty (D ∩ A') Finset.inter_subset_right
          (W ∩ B') Finset.inter_subset_right hDA_ge hWB_ge
        exact hnoEdge x (Finset.mem_inter.mp hx).1 y (Finset.mem_inter.mp hy).1
          ⟨Or.inl ⟨(Finset.mem_inter.mp hx).2, (Finset.mem_inter.mp hy).2⟩, hadj⟩
      have hB_cov : B' ⊆ (Q.toFinset ∩ B') ∪ (D ∩ B') ∪ (W ∩ B') := by
        intro b hb
        have hbAB : b ∈ A' ∪ B' := Finset.mem_union_right _ hb
        rcases Finset.mem_union.mp (hcov hbAB) with hPD | hW
        · rcases Finset.mem_union.mp hPD with hP | hD
          · exact Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_inter.mpr ⟨by simpa [Q] using hP, hb⟩))
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hD, hb⟩))
        · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hW, hb⟩)
      have hB_card : B'.card ≤ (Q.toFinset ∩ B').card + (D ∩ B').card + (W ∩ B').card :=
        (Finset.card_le_card hB_cov).trans
          ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
      have hQB := hprops.2.1
      have hDB' : (D ∩ B').card ≤ cB := hDB
      have hmin := min_le_right A'.card B'.card
      have hmax := le_max_right cA cB
      omega
    · have hWA : (W ∩ A').card < cA := by
        by_contra! hWA_ge
        obtain ⟨x, hx, y, hy, hadj⟩ := hnoempty (W ∩ A') Finset.inter_subset_right
          (D ∩ B') Finset.inter_subset_right hWA_ge hDB_ge
        exact hnoEdge y (Finset.mem_inter.mp hy).1 x (Finset.mem_inter.mp hx).1
          ⟨Or.inr ⟨(Finset.mem_inter.mp hy).2, (Finset.mem_inter.mp hx).2⟩, hadj.symm⟩
      have hA_cov : A' ⊆ (Q.toFinset ∩ A') ∪ (D ∩ A') ∪ (W ∩ A') := by
        intro a ha
        have haAB : a ∈ A' ∪ B' := Finset.mem_union_left _ ha
        rcases Finset.mem_union.mp (hcov haAB) with hPD | hW
        · rcases Finset.mem_union.mp hPD with hP | hD
          · exact Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_inter.mpr ⟨by simpa [Q] using hP, ha⟩))
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hD, ha⟩))
        · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hW, ha⟩)
      have hA_card : A'.card ≤ (Q.toFinset ∩ A').card + (D ∩ A').card + (W ∩ A').card :=
        (Finset.card_le_card hA_cov).trans
          ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
      have hQA := hprops.1
      have hDA' : (D ∩ A').card ≤ cA := hDA
      have hmin := min_le_left A'.card B'.card
      have hmax := le_max_left cA cB
      omega
  exact ⟨Q, hQne, hQhead, hQnodup, hQchain, hQsub, hlen, hprops.2.2⟩

/- ### Extracting disjoint matching edges and building closed walk in R -/

private lemma extract_matching_pairs {t : ℕ} {R : SimpleGraph (Fin t)} (M : R.Subgraph)
    (hM : M.IsMatching) :
    ∀ (k : ℕ) (S : Finset (Fin t)),
      (∀ x ∈ S, x ∈ M.verts) →
      (∀ x ∈ S, ∀ y, M.Adj x y → y ∈ S) →
      2 * k ≤ S.card →
      ∃ edges : List (Fin t × Fin t),
        edges.length = k ∧
        (∀ p ∈ edges, M.Adj p.1 p.2) ∧
        (∀ p ∈ edges, p.1 ∈ S ∧ p.2 ∈ S) ∧
        (edges.flatMap (fun p => [p.1, p.2])).Nodup := by
  intro k
  induction k with
  | zero =>
    intro S _ _ _
    exact ⟨[], rfl, by simp, by simp, by simp⟩
  | succ k ih =>
    intro S hSverts hSclosed hScard
    have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨u, huS⟩ := hSne
    obtain ⟨v, hvAdj, hvUniq⟩ := hM (hSverts u huS)
    have hvS : v ∈ S := hSclosed u huS v hvAdj
    have huv : u ≠ v := R.ne_of_adj (M.adj_sub hvAdj)
    set S' := (S.erase u).erase v
    have hS'verts : ∀ x ∈ S', x ∈ M.verts := fun x hx =>
      hSverts x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))
    have hS'closed : ∀ x ∈ S', ∀ y, M.Adj x y → y ∈ S' := by
      intro x hx y hxy
      have hxS := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)
      have hxv : x ≠ v := Finset.ne_of_mem_erase hx
      have hxu : x ≠ u := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hx)
      have hyS := hSclosed x hxS y hxy
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hyS⟩⟩
      · intro hyv; subst hyv
        exact hxu (hM.eq_of_adj_right hxy hvAdj)
      · intro hyu; subst hyu
        exact hxv (hvUniq x hxy.symm)
    have hS'card : 2 * k ≤ S'.card := by
      have h1 : (S.erase u).card = S.card - 1 := Finset.card_erase_of_mem huS
      have hv_er : v ∈ S.erase u := Finset.mem_erase.mpr ⟨huv.symm, hvS⟩
      have h2 : S'.card = (S.erase u).card - 1 := Finset.card_erase_of_mem hv_er
      omega
    obtain ⟨edges, hlen, hadj, hmemS', hnodup⟩ := ih S' hS'verts hS'closed hS'card
    have hnotU : u ∉ edges.flatMap (fun p => [p.1, p.2]) := by
      rw [List.mem_flatMap]
      rintro ⟨q, hq, hzq⟩
      have hqS' := hmemS' q hq
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hzq
      rcases hzq with rfl | rfl
      · exact Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hqS'.1) rfl
      · exact Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hqS'.2) rfl
    have hnotV : v ∉ edges.flatMap (fun p => [p.1, p.2]) := by
      rw [List.mem_flatMap]
      rintro ⟨q, hq, hzq⟩
      have hqS' := hmemS' q hq
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hzq
      rcases hzq with rfl | rfl
      · exact Finset.ne_of_mem_erase hqS'.1 rfl
      · exact Finset.ne_of_mem_erase hqS'.2 rfl
    refine ⟨(u, v) :: edges, by simp [hlen], ?_, ?_, ?_⟩
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hvAdj
      · exact hadj p hp
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨huS, hvS⟩
      · exact ⟨Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (hmemS' p hp).1),
               Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (hmemS' p hp).2)⟩
    · simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons]
      refine ⟨?_, hnotV, hnodup⟩
      simp only [List.mem_cons]
      rintro (rfl | h)
      · exact huv rfl
      · exact hnotU h

private lemma walk_boundary_edge {t : ℕ} {R : SimpleGraph (Fin t)}
    {V : Finset (Fin t)} {a b : Fin t} (ha : a ∈ V) (hb : b ∉ V)
    (hwalk : R.Reachable a b) :
    ∃ x y : Fin t, R.Adj x y ∧ x ∈ V ∧ y ∉ V := by
  obtain ⟨w⟩ := hwalk
  induction w with
  | nil => exact (hb ha).elim
  | @cons u v c huv _ ih =>
    by_cases hv : v ∈ V
    · exact ih hv hb
    · exact ⟨u, v, huv, ha, hv⟩

private def spliceAt {α : Type*} [DecidableEq α] (x : α)
    (ins W : List (α × α × Bool)) : List (α × α × Bool) :=
  match W with
  | [] => ins
  | e :: rest => if e.1 = x then ins ++ e :: rest else e :: spliceAt x ins rest

private lemma isChain_append {α : Type*} {r : α → α → Prop} {l₁ l₂ : List α}
    (h₁ : l₁.IsChain r) (h₂ : l₂.IsChain r)
    (hbd : ∀ a ∈ l₁.getLast?, ∀ b ∈ l₂.head?, r a b) :
    (l₁ ++ l₂).IsChain r := by
  induction l₁ with
  | nil => simpa using h₂
  | cons x xs ih =>
    rcases xs with _ | ⟨y, ys⟩
    · simp only [List.nil_append, List.singleton_append]
      rcases l₂ with _ | ⟨b, bs⟩
      · exact h₁
      · exact List.IsChain.cons_cons (hbd x (by simp) b (by simp)) h₂
    · simp only [List.cons_append]
      exact List.IsChain.cons_cons (List.IsChain.rel_head h₁)
        (ih h₁.tail (fun a ha b hb => hbd a (by simpa using ha) b hb))

private lemma spliceAt_props {α : Type*} [DecidableEq α] (x : α)
    (ins W : List (α × α × Bool))
    (hWne : W ≠ []) (hex : ∃ e ∈ W, e.1 = x)
    (hWchain : W.IsChain (fun a b => a.2.1 = b.1))
    (hins_ne : ins ≠ [])
    (hins_head : (ins.head hins_ne).1 = x)
    (hins_last : (ins.getLast hins_ne).2.1 = x)
    (hins_chain : ins.IsChain (fun a b => a.2.1 = b.1)) :
    let W' := spliceAt x ins W
    W' ≠ [] ∧
    (∀ h' : W' ≠ [], (W'.head h').1 = (W.head hWne).1) ∧
    (∀ h' : W' ≠ [], W'.getLast h' = W.getLast hWne) ∧
    W'.length = W.length + ins.length ∧
    W'.IsChain (fun a b => a.2.1 = b.1) ∧
    (∀ e, e ∈ W' ↔ e ∈ ins ∨ e ∈ W) ∧
    List.Perm (W'.filter (·.2.2)) (ins.filter (·.2.2) ++ W.filter (·.2.2)) := by
  induction W with
  | nil => exact (hWne rfl).elim
  | cons e rest ih =>
    unfold spliceAt
    by_cases he : e.1 = x
    · rw [if_pos he]
      have hne' : ins ++ e :: rest ≠ [] := List.append_ne_nil_of_right_ne_nil _ (by simp)
      refine ⟨hne', ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro h'
        rw [List.head_append_of_ne_nil hins_ne]
        simpa [he] using hins_head
      · intro h'
        exact List.getLast_append_of_ne_nil _ (by simp)
      · simp; omega
      · refine isChain_append hins_chain hWchain ?_
        intro a ha b hb
        have ha' : a = ins.getLast hins_ne := (by
          rw [List.getLast?_eq_some_getLast hins_ne] at ha
          simpa using ha : ins.getLast hins_ne = a).symm
        have hb' : b = e := (by simpa using hb : e = b).symm
        subst ha'; subst hb'
        simpa [he] using hins_last
      · intro z; simp
      · rw [List.filter_append]
    · rw [if_neg he]
      have hex_rest : ∃ e' ∈ rest, e'.1 = x := by
        rcases hex with ⟨e', he', hx'⟩
        rcases List.mem_cons.mp he' with rfl | he'
        · exact (he hx').elim
        · exact ⟨e', he', hx'⟩
      have hrest_ne : rest ≠ [] := by
        rintro rfl; obtain ⟨e', he', _⟩ := hex_rest; exact (List.not_mem_nil he').elim
      obtain ⟨hne_r, hhead_r, hlast_r, hlen_r, hchain_r, hmem_r, hperm_r⟩ :=
        ih hrest_ne hex_rest hWchain.tail
      refine ⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro _; simp
      · intro h'
        rw [List.getLast_cons hne_r, hlast_r hne_r, List.getLast_cons hrest_ne]
      · simp [hlen_r]; omega
      · refine List.IsChain.cons_of_ne_nil hne_r hchain_r ?_
        rw [hhead_r hne_r]
        rcases rest with _ | ⟨r, rs⟩
        · exact (hrest_ne rfl).elim
        · simp only [List.head_cons]
          exact List.isChain_iff_getElem.mp hWchain 0 (by simp)
      · intro z
        simp only [List.mem_cons, hmem_r]
        tauto
      · by_cases hp : e.2.2 = true
        · simp only [List.filter_cons, hp, ↓reduceIte]
          exact (hperm_r.cons e).trans (List.perm_middle.symm)
        · have hp' : e.2.2 = false := Bool.eq_false_iff.mpr hp
          simp only [List.filter_cons, hp', Bool.false_eq_true, ↓reduceIte]
          exact hperm_r

private lemma nodup_flatMap_pair_unique {α : Type*} :
    ∀ (L : List (α × α)) (p q : α × α),
      (L.flatMap (fun r => [r.1, r.2])).Nodup →
      p ∈ L → q ∈ L → (q.1 = p.1 ∨ q.1 = p.2 ∨ q.2 = p.1 ∨ q.2 = p.2) → q = p := by
  intro L
  induction L with
  | nil => intro p q _ hp; exact (List.not_mem_nil hp).elim
  | cons a t ih =>
    intro p q hnodup hp hq heq
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons] at hnodup
    rcases List.mem_cons.mp hp with hpa | hp'
    · rcases List.mem_cons.mp hq with hqa | hq'
      · exact hqa.trans hpa.symm
      · exfalso
        have h1 : q.1 ∈ t.flatMap (fun r => [r.1, r.2]) := List.mem_flatMap.mpr ⟨q, hq', by simp⟩
        have h2 : q.2 ∈ t.flatMap (fun r => [r.1, r.2]) := List.mem_flatMap.mpr ⟨q, hq', by simp⟩
        rw [hpa] at heq
        rcases heq with h | h | h | h
        · exact hnodup.1 (List.mem_cons.mpr (Or.inr (h ▸ h1)))
        · exact hnodup.2.1 (h ▸ h1)
        · exact hnodup.1 (List.mem_cons.mpr (Or.inr (h ▸ h2)))
        · exact hnodup.2.1 (h ▸ h2)
    · rcases List.mem_cons.mp hq with hqa | hq'
      · exfalso
        have h1 : p.1 ∈ t.flatMap (fun r => [r.1, r.2]) := List.mem_flatMap.mpr ⟨p, hp', by simp⟩
        have h2 : p.2 ∈ t.flatMap (fun r => [r.1, r.2]) := List.mem_flatMap.mpr ⟨p, hp', by simp⟩
        rw [hqa] at heq
        rcases heq with h | h | h | h
        · exact hnodup.1 (List.mem_cons.mpr (Or.inr (h.symm ▸ h1)))
        · exact hnodup.1 (List.mem_cons.mpr (Or.inr (h.symm ▸ h2)))
        · exact hnodup.2.1 (h.symm ▸ h1)
        · exact hnodup.2.1 (h.symm ▸ h2)
      · exact ih p q hnodup.2.2 hp' hq' heq

private lemma filter_length_insert_two {α : Type*} [DecidableEq α]
    (L : List (α × α)) (hL : L.Nodup) (V : Finset α) (y y' : α)
    (p : α × α) (hpL : p ∈ L) (hp_eq : (p.1 = y ∧ p.2 = y') ∨ (p.1 = y' ∧ p.2 = y))
    (huniq : ∀ q ∈ L, (q.1 = y ∨ q.1 = y') → q = p)
    (hyV : y ∉ V) (hy'V : y' ∉ V) :
    (L.filter (fun q => decide (q.1 ∈ insert y (insert y' V)))).length =
      (L.filter (fun q => decide (q.1 ∈ V))).length + 1 := by
  induction L with
  | nil => exact (List.not_mem_nil hpL).elim
  | cons a t ih =>
    have hat : a ∉ t := (List.nodup_cons.mp hL).1
    have ht : t.Nodup := (List.nodup_cons.mp hL).2
    rcases List.mem_cons.mp hpL with hpa | hp
    · have hp_old : decide (p.1 ∈ V) = false := by
        rw [decide_eq_false_iff_not]
        rcases hp_eq with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact h1 ▸ hyV
        · exact h1 ▸ hy'V
      have hp_new : decide (p.1 ∈ insert y (insert y' V)) = true := by
        rw [decide_eq_true_eq]
        rcases hp_eq with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact h1 ▸ Finset.mem_insert_self _ _
        · exact h1 ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      have hcongr : t.filter (fun q => decide (q.1 ∈ insert y (insert y' V))) =
          t.filter (fun q => decide (q.1 ∈ V)) := by
        refine List.filter_congr fun q hqt => ?_
        have hqn : q ≠ p := fun h => hat (hpa ▸ h ▸ hqt)
        have hqnot : ¬ (q.1 = y ∨ q.1 = y') := fun h => hqn (huniq q (List.mem_cons_of_mem _ hqt) h)
        have hiff : q.1 ∈ insert y (insert y' V) ↔ q.1 ∈ V := by simp only [Finset.mem_insert]; tauto
        simp only [hiff]
      rw [← hpa]
      simp only [List.filter_cons, hp_old, hp_new, Bool.false_eq_true, ↓reduceIte, hcongr, List.length_cons]
    · have ha_neq : a ≠ p := fun h => hat (h ▸ hp)
      have ha_not : ¬ (a.1 = y ∨ a.1 = y') := fun h => ha_neq (huniq a List.mem_cons_self h)
      have hiff : a.1 ∈ insert y (insert y' V) ↔ a.1 ∈ V := by simp only [Finset.mem_insert]; tauto
      have hsame : decide (a.1 ∈ insert y (insert y' V)) = decide (a.1 ∈ V) := by simp only [hiff]
      have ih' := ih ht hp (fun q hqt h => huniq q (List.mem_cons_of_mem _ hqt) h)
      simp only [List.filter_cons, hsame]
      cases h : decide (a.1 ∈ V)
      · simp only [Bool.false_eq_true, ↓reduceIte, ih']
      · simp only [↓reduceIte, List.length_cons, ih']

private lemma build_closed_walk {t : ℕ} {R : SimpleGraph (Fin t)}
    (chosen : List (Fin t × Fin t)) (hchosen_ne : chosen ≠ [])
    (hchosen_adj : ∀ p ∈ chosen, R.Adj p.1 p.2)
    (hchosen_nodup : (chosen.flatMap (fun p => [p.1, p.2])).Nodup)
    (hchosen_reach : ∀ p ∈ chosen, ∀ q ∈ chosen, R.Reachable p.1 q.1) :
    ∃ W : List (Fin t × Fin t × Bool),
      W ≠ [] ∧
      (∀ e ∈ W, R.Adj e.1 e.2.1) ∧
      W.IsChain (fun a b => a.2.1 = b.1) ∧
      (∀ h : W ≠ [], (W.getLast h).2.1 = (W.head h).1) ∧
      (∀ h : W ≠ [], (W.getLast h).2.2 = false) ∧
      Even W.length ∧ 2 ≤ W.length ∧ W.length ≤ 2 * t ∧
      chosen.length ≤ W.length / 2 ∧
      (chosen.length = 1 → W.length = 2) ∧
      W.countP (·.2.2) = chosen.length ∧
      ((W.filter (·.2.2)).flatMap (fun e => [e.1, e.2.1])).Nodup := by
  classical
  rcases chosen with _ | ⟨⟨u₁, v₁⟩, rest_ch⟩
  · exact (hchosen_ne rfl).elim
  have h1_mem : (u₁, v₁) ∈ (u₁, v₁) :: rest_ch := List.mem_cons_self
  have h1_adj : R.Adj u₁ v₁ := hchosen_adj _ h1_mem
  have huv1 : u₁ ≠ v₁ := R.ne_of_adj h1_adj
  set W₀ : List (Fin t × Fin t × Bool) := [(u₁, v₁, true), (v₁, u₁, false)]
  set V₀ : Finset (Fin t) := {u₁, v₁}
  have hV₀_card : V₀.card = 2 := Finset.card_pair huv1
  have ht2 : 2 ≤ t := by
    have h1 : V₀.card ≤ t := by simpa using Finset.card_le_univ V₀
    omega
  by_cases hrest : rest_ch = []
  · subst hrest
    refine ⟨W₀, by simp [W₀], ?_, List.IsChain.cons_cons rfl (List.IsChain.singleton _),
      by simp [W₀], by simp [W₀], ⟨1, rfl⟩, by simp [W₀], by simp [W₀]; omega,
      by simp [W₀], fun _ => by simp [W₀], by simp [W₀], by simp [W₀, huv1]⟩
    intro e he
    simp only [W₀, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact h1_adj
    · exact h1_adj.symm
  set ch := (u₁, v₁) :: rest_ch
  have hch_nodup : ch.Nodup := by
    have : ∀ (L : List (Fin t × Fin t)), (L.flatMap (fun p => [p.1, p.2])).Nodup → L.Nodup := by
      intro L h
      induction L with
      | nil => simp
      | cons a ts ih =>
        simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons] at h
        refine List.nodup_cons.mpr ⟨fun ha => ?_, ih h.2.2⟩
        exact h.1 (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_self⟩))
    exact this ch hchosen_nodup
  have hstep : ∀ n : ℕ, ∀ (W : List (Fin t × Fin t × Bool)) (V : Finset (Fin t)),
      t - V.card = n →
      W ≠ [] →
      (∀ e ∈ W, R.Adj e.1 e.2.1) →
      W.IsChain (fun a b => a.2.1 = b.1) →
      (∀ h : W ≠ [], (W.getLast h).2.1 = (W.head h).1) →
      (∀ h : W ≠ [], (W.getLast h).2.2 = false) →
      u₁ ∈ V →
      (∀ e ∈ W, e.1 ∈ V ∧ e.2.1 ∈ V) →
      (∀ v ∈ V, ∃ e ∈ W, e.1 = v) →
      W.length = 2 * (V.card - 1) → 2 ≤ V.card →
      (∀ p ∈ ch, (p.1 ∈ V ∧ p.2 ∈ V) ∨ (p.1 ∉ V ∧ p.2 ∉ V)) →
      W.countP (·.2.2) = (ch.filter (fun p => decide (p.1 ∈ V))).length →
      ((W.filter (·.2.2)).flatMap (fun e => [e.1, e.2.1])).Nodup →
      ∃ W' : List (Fin t × Fin t × Bool),
        W' ≠ [] ∧
        (∀ e ∈ W', R.Adj e.1 e.2.1) ∧
        W'.IsChain (fun a b => a.2.1 = b.1) ∧
        (∀ h : W' ≠ [], (W'.getLast h).2.1 = (W'.head h).1) ∧
        (∀ h : W' ≠ [], (W'.getLast h).2.2 = false) ∧
        Even W'.length ∧ 2 ≤ W'.length ∧ W'.length ≤ 2 * t ∧
        ch.length ≤ W'.length / 2 ∧
        (ch.length = 1 → W'.length = 2) ∧
        W'.countP (·.2.2) = ch.length ∧
        ((W'.filter (·.2.2)).flatMap (fun e => [e.1, e.2.1])).Nodup := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro W V hn hWne hWadj hWchain hWwrap hWlastf hu1V hWV hVW hWlen hV2 hchInv hWcnt hWnodup
      by_cases hall : ∀ p ∈ ch, p.1 ∈ V ∧ p.2 ∈ V
      · have hfilt : ch.filter (fun p => decide (p.1 ∈ V)) = ch :=
          List.filter_eq_self.mpr fun p hp => decide_eq_true (hall p hp).1
        have hch_sub : ∀ z ∈ ch.flatMap (fun p => [p.1, p.2]), z ∈ V := by
          intro z hz
          rw [List.mem_flatMap] at hz
          obtain ⟨p, hp, hzp⟩ := hz
          rcases List.mem_cons.mp hzp with rfl | hzp
          · exact (hall p hp).1
          · rw [List.mem_singleton] at hzp; subst hzp; exact (hall p hp).2
        have h2ch : 2 * ch.length ≤ V.card := by
          have h1 : (ch.flatMap (fun p => [p.1, p.2])).toFinset ⊆ V := fun z hz =>
            hch_sub z (List.mem_toFinset.mp hz)
          have h2 := Finset.card_le_card h1
          rw [List.toFinset_card_of_nodup hchosen_nodup] at h2
          have h3 : (ch.flatMap (fun p => [p.1, p.2])).length = 2 * ch.length := by
            clear h1 h2 hch_sub hfilt hall
            induction ch with
            | nil => simp
            | cons a ts ihc => simp [ihc]; omega
          omega
        have hVt : V.card ≤ t := by simpa using Finset.card_le_univ V
        refine ⟨W, hWne, hWadj, hWchain, hWwrap, hWlastf, ?_, by omega, by omega, by omega,
          fun hch1 => by exfalso; simp [ch] at hch1; exact hrest hch1, ?_, hWnodup⟩
        · exact ⟨V.card - 1, by omega⟩
        · rw [hWcnt, hfilt]
      · push_neg at hall
        obtain ⟨p, hp_ch, hp_not⟩ := hall
        have hp_out : p.1 ∉ V ∧ p.2 ∉ V := by
          rcases hchInv p hp_ch with h | h
          · exact (hp_not h.1 h.2).elim
          · exact h
        obtain ⟨x, y, hxyAdj, hxV, hyV⟩ :=
          walk_boundary_edge hu1V hp_out.1 (hchosen_reach (u₁, v₁) h1_mem p hp_ch)
        obtain ⟨ex, hexW, hex1⟩ := hVW x hxV
        by_cases hy_ch : ∃ q ∈ ch, q.1 = y ∨ q.2 = y
        · obtain ⟨q, hq_ch, hqy⟩ := hy_ch
          set y' := if q.1 = y then q.2 else q.1
          have hy'_eq : (q.1 = y ∧ q.2 = y') ∨ (q.1 = y' ∧ q.2 = y) := by
            by_cases h : q.1 = y
            · exact Or.inl ⟨h, by simp [y', h]⟩
            · exact Or.inr ⟨by simp [y', h], hqy.resolve_left h⟩
          have hq_adj : R.Adj y y' := by
            rcases hy'_eq with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rw [← h1, ← h2]; exact hchosen_adj q hq_ch
            · rw [← h1, ← h2]; exact (hchosen_adj q hq_ch).symm
          have hyy' : y ≠ y' := R.ne_of_adj hq_adj
          have hy'V : y' ∉ V := by
            rcases hchInv q hq_ch with h | h
            · exfalso
              rcases hqy with h1 | h1
              · exact hyV (h1 ▸ h.1)
              · exact hyV (h1 ▸ h.2)
            · rcases hy'_eq with ⟨_, h2⟩ | ⟨h1, _⟩
              · exact h2 ▸ h.2
              · exact h1 ▸ h.1
          set ins : List (Fin t × Fin t × Bool) :=
            [(x, y, false), (y, y', true), (y', y, false), (y, x, false)]
          have hins_ne : ins ≠ [] := by simp [ins]
          have hins_chain : ins.IsChain (fun a b => a.2.1 = b.1) := by
            simp only [ins]
            exact List.IsChain.cons_cons rfl (List.IsChain.cons_cons rfl
              (List.IsChain.cons_cons rfl (List.IsChain.singleton _)))
          obtain ⟨hne', hhead', hlast', hlen', hchain', hmem', hperm'⟩ :=
            spliceAt_props x ins W hWne ⟨ex, hexW, hex1⟩ hWchain hins_ne rfl rfl hins_chain
          set W' := spliceAt x ins W
          set V' := insert y (insert y' V)
          have hV'card : V'.card = V.card + 2 := by
            have hy_ins : y ∉ insert y' V := by
              simp [hyy', hyV]
            rw [Finset.card_insert_of_notMem hy_ins, Finset.card_insert_of_notMem hy'V]
          have hVt : V.card ≤ t := by simpa using Finset.card_le_univ V
          have hV't : V'.card ≤ t := by simpa using Finset.card_le_univ V'
          have hlt : t - V'.card < n := by omega
          refine ih _ hlt W' V' rfl hne' ?_ hchain' ?_ ?_ ?_ ?_ ?_ ?_ (by omega) ?_ ?_ ?_
          · intro e he
            rcases (hmem' e).mp he with he_ins | he_W
            · simp only [ins, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he_ins
              rcases he_ins with rfl | rfl | rfl | rfl
              · exact hxyAdj
              · exact hq_adj
              · exact hq_adj.symm
              · exact hxyAdj.symm
            · exact hWadj e he_W
          · intro h'
            rw [hlast' h', hhead' h', hWwrap hWne]
          · intro h'
            rw [hlast' h', hWlastf hWne]
          · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu1V)
          · intro e he
            rcases (hmem' e).mp he with he_ins | he_W
            · simp only [ins, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he_ins
              rcases he_ins with rfl | rfl | rfl | rfl
              · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxV),
                       Finset.mem_insert_self _ _⟩
              · exact ⟨Finset.mem_insert_self _ _,
                       Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩
              · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),
                       Finset.mem_insert_self _ _⟩
              · exact ⟨Finset.mem_insert_self _ _,
                       Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxV)⟩
            · have := hWV e he_W
              exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem this.1),
                     Finset.mem_insert_of_mem (Finset.mem_insert_of_mem this.2)⟩
          · intro v hv
            simp only [V', Finset.mem_insert] at hv
            rcases hv with hvy | hvy' | hv
            · exact ⟨(y, y', true), (hmem' _).mpr (Or.inl (by simp [ins])), hvy.symm⟩
            · exact ⟨(y', y, false), (hmem' _).mpr (Or.inl (by simp [ins])), hvy'.symm⟩
            · obtain ⟨e, heW, he1⟩ := hVW v hv
              exact ⟨e, (hmem' _).mpr (Or.inr heW), he1⟩
          · rw [hlen', hV'card, hWlen]; simp [ins]; omega
          · intro r hr
            rcases hchInv r hr with ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩
            · exact Or.inl ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hr1),
                            Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hr2)⟩
            · by_cases hr_eq : r = q
              · subst hr_eq
                rcases hy'_eq with ⟨h1, h2⟩ | ⟨h1, h2⟩
                · exact Or.inl ⟨h1 ▸ Finset.mem_insert_self _ _,
                                h2 ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩
                · exact Or.inl ⟨h1 ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),
                                h2 ▸ Finset.mem_insert_self _ _⟩
              · refine Or.inr ⟨?_, ?_⟩
                · simp only [V', Finset.mem_insert, not_or]
                  refine ⟨fun h => hr_eq (nodup_flatMap_pair_unique ch q r hchosen_nodup hq_ch hr ?_),
                          fun h => hr_eq (nodup_flatMap_pair_unique ch q r hchosen_nodup hq_ch hr ?_), hr1⟩
                  · rcases hy'_eq with ⟨h1, _⟩ | ⟨_, h2⟩ <;> [exact Or.inl (h.trans h1.symm); exact Or.inr (Or.inl (h.trans h2.symm))]
                  · rcases hy'_eq with ⟨_, h2⟩ | ⟨h1, _⟩ <;> [exact Or.inr (Or.inl (h.trans h2.symm)); exact Or.inl (h.trans h1.symm)]
                · simp only [V', Finset.mem_insert, not_or]
                  refine ⟨fun h => hr_eq (nodup_flatMap_pair_unique ch q r hchosen_nodup hq_ch hr ?_),
                          fun h => hr_eq (nodup_flatMap_pair_unique ch q r hchosen_nodup hq_ch hr ?_), hr2⟩
                  · rcases hy'_eq with ⟨h1, _⟩ | ⟨_, h2⟩ <;> [exact Or.inr (Or.inr (Or.inl (h.trans h1.symm))); exact Or.inr (Or.inr (Or.inr (h.trans h2.symm)))]
                  · rcases hy'_eq with ⟨_, h2⟩ | ⟨h1, _⟩ <;> [exact Or.inr (Or.inr (Or.inr (h.trans h2.symm))); exact Or.inr (Or.inr (Or.inl (h.trans h1.symm)))]
          · rw [List.countP_eq_length_filter] at hWcnt ⊢
            have hperm_len := hperm'.length_eq
            have hins_filt : ins.filter (·.2.2) = [(y, y', true)] := by simp [ins]
            rw [hins_filt, List.length_append] at hperm_len
            simp only [List.length_singleton] at hperm_len
            have huniq_q : ∀ r ∈ ch, (r.1 = y ∨ r.1 = y') → r = q := by
              intro r hr h
              refine nodup_flatMap_pair_unique ch q r hchosen_nodup hq_ch hr ?_
              rcases h with h | h
              · rcases hy'_eq with ⟨h1, _⟩ | ⟨_, h2⟩
                · exact Or.inl (h.trans h1.symm)
                · exact Or.inr (Or.inl (h.trans h2.symm))
              · rcases hy'_eq with ⟨_, h2⟩ | ⟨h1, _⟩
                · exact Or.inr (Or.inl (h.trans h2.symm))
                · exact Or.inl (h.trans h1.symm)
            rw [hperm_len, hWcnt, filter_length_insert_two ch hch_nodup V y y' q hq_ch hy'_eq huniq_q hyV hy'V]
            omega
          · have hperm_flat : List.Perm ((W'.filter (·.2.2)).flatMap (fun e => [e.1, e.2.1]))
                (y :: y' :: (W.filter (·.2.2)).flatMap (fun e => [e.1, e.2.1])) := by
              have h1 := hperm'.flatMap (fun e _ => List.Perm.refl [e.1, e.2.1])
              simpa [ins] using h1
            rw [hperm_flat.nodup_iff, List.nodup_cons, List.nodup_cons]
            refine ⟨?_, ?_, hWnodup⟩
            · intro h
              rcases List.mem_cons.mp h with hy0 | h
              · exact hyy' hy0
              · rw [List.mem_flatMap] at h
                rcases h with ⟨e, he, hye⟩
                have heW : e ∈ W := (List.mem_filter.mp he).1
                rcases List.mem_cons.mp hye with hye | hye
                · exact hyV (hye ▸ (hWV e heW).1)
                · rw [List.mem_singleton] at hye
                  exact hyV (hye ▸ (hWV e heW).2)
            · rw [List.mem_flatMap]
              rintro ⟨e, he, hy'e⟩
              have heW : e ∈ W := (List.mem_filter.mp he).1
              rcases List.mem_cons.mp hy'e with hy'e | hy'e
              · exact hy'V (hy'e ▸ (hWV e heW).1)
              · rw [List.mem_singleton] at hy'e
                exact hy'V (hy'e ▸ (hWV e heW).2)
        · push_neg at hy_ch
          set ins : List (Fin t × Fin t × Bool) := [(x, y, false), (y, x, false)]
          have hins_ne : ins ≠ [] := by simp [ins]
          have hins_chain : ins.IsChain (fun a b => a.2.1 = b.1) := by
            simp only [ins]
            exact List.IsChain.cons_cons rfl (List.IsChain.singleton _)
          obtain ⟨hne', hhead', hlast', hlen', hchain', hmem', hperm'⟩ :=
            spliceAt_props x ins W hWne ⟨ex, hexW, hex1⟩ hWchain hins_ne rfl rfl hins_chain
          set W' := spliceAt x ins W
          set V' := insert y V
          have hV'card : V'.card = V.card + 1 := Finset.card_insert_of_notMem hyV
          have hV't : V'.card ≤ t := by simpa using Finset.card_le_univ V'
          have hlt : t - V'.card < n := by omega
          refine ih _ hlt W' V' rfl hne' ?_ hchain' ?_ ?_ ?_ ?_ ?_ ?_ (by omega) ?_ ?_ ?_
          · intro e he
            rcases (hmem' e).mp he with he_ins | he_W
            · simp only [ins, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he_ins
              rcases he_ins with rfl | rfl
              · exact hxyAdj
              · exact hxyAdj.symm
            · exact hWadj e he_W
          · intro h'; rw [hlast' h', hhead' h', hWwrap hWne]
          · intro h'; rw [hlast' h', hWlastf hWne]
          · exact Finset.mem_insert_of_mem hu1V
          · intro e he
            rcases (hmem' e).mp he with he_ins | he_W
            · simp only [ins, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he_ins
              rcases he_ins with rfl | rfl
              · exact ⟨Finset.mem_insert_of_mem hxV, Finset.mem_insert_self _ _⟩
              · exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hxV⟩
            · have := hWV e he_W
              exact ⟨Finset.mem_insert_of_mem this.1, Finset.mem_insert_of_mem this.2⟩
          · intro v hv
            rcases Finset.mem_insert.mp hv with hvy | hv
            · exact ⟨(y, x, false), (hmem' _).mpr (Or.inl (by simp [ins])), hvy.symm⟩
            · obtain ⟨e, heW, he1⟩ := hVW v hv
              exact ⟨e, (hmem' _).mpr (Or.inr heW), he1⟩
          · rw [hlen', hV'card, hWlen]; simp [ins]; omega
          · intro r hr
            rcases hchInv r hr with ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩
            · exact Or.inl ⟨Finset.mem_insert_of_mem hr1, Finset.mem_insert_of_mem hr2⟩
            · exact Or.inr ⟨fun h => by
                  rcases Finset.mem_insert.mp h with h | h
                  · exact (hy_ch r hr).1 h
                  · exact hr1 h,
                fun h => by
                  rcases Finset.mem_insert.mp h with h | h
                  · exact (hy_ch r hr).2 h
                  · exact hr2 h⟩
          · rw [List.countP_eq_length_filter] at hWcnt ⊢
            have hperm_len := hperm'.length_eq
            have hins_filt : ins.filter (·.2.2) = [] := by simp [ins]
            rw [hins_filt, List.nil_append] at hperm_len
            have hcongr : ch.filter (fun r => decide (r.1 ∈ V')) = ch.filter (fun r => decide (r.1 ∈ V)) := by
              refine List.filter_congr fun r hr => ?_
              have hry : r.1 ≠ y := fun h => (hy_ch r hr).1 h
              simp [V', hry]
            rw [hperm_len, hWcnt, hcongr]
          · have hperm_flat : List.Perm ((W'.filter (·.2.2)).flatMap (fun e => [e.1, e.2.1]))
                ((W.filter (·.2.2)).flatMap (fun e => [e.1, e.2.1])) := by
              have h1 := hperm'.flatMap (fun e _ => List.Perm.refl [e.1, e.2.1])
              simpa [ins] using h1
            exact hperm_flat.nodup_iff.mpr hWnodup
  have hchInv₀ : ∀ p ∈ ch, (p.1 ∈ V₀ ∧ p.2 ∈ V₀) ∨ (p.1 ∉ V₀ ∧ p.2 ∉ V₀) := by
    intro p hp
    by_cases hp1 : p = (u₁, v₁)
    · subst hp1; exact Or.inl ⟨by simp [V₀], by simp [V₀]⟩
    · refine Or.inr ⟨?_, ?_⟩
      · simp only [V₀, Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => hp1 (nodup_flatMap_pair_unique ch (u₁, v₁) p hchosen_nodup h1_mem hp (Or.inl h)),
               fun h => hp1 (nodup_flatMap_pair_unique ch (u₁, v₁) p hchosen_nodup h1_mem hp (Or.inr (Or.inl h)))⟩
      · simp only [V₀, Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => hp1 (nodup_flatMap_pair_unique ch (u₁, v₁) p hchosen_nodup h1_mem hp (Or.inr (Or.inr (Or.inl h)))),
               fun h => hp1 (nodup_flatMap_pair_unique ch (u₁, v₁) p hchosen_nodup h1_mem hp (Or.inr (Or.inr (Or.inr h))))⟩
  have hWcnt₀ : W₀.countP (·.2.2) = (ch.filter (fun p => decide (p.1 ∈ V₀))).length := by
    have hfilt : ch.filter (fun p => decide (p.1 ∈ V₀)) = [(u₁, v₁)] := by
      simp only [ch, List.filter_cons, decide_eq_true (by simp [V₀] : u₁ ∈ V₀),
        ↓reduceIte, List.cons.injEq, true_and]
      rw [List.filter_eq_nil_iff]
      intro p hp
      have hne1 : p ≠ (u₁, v₁) := by
        intro h; subst h
        simp only [ch, List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons] at hchosen_nodup
        exact hchosen_nodup.1 (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨(u₁, v₁), hp, List.mem_cons_self⟩))
      have hp_out : p.1 ∉ V₀ := by
        rcases hchInv₀ p (List.mem_cons_of_mem _ hp) with h | h
        · exfalso
          exact hne1 (nodup_flatMap_pair_unique ch (u₁, v₁) p hchosen_nodup h1_mem (List.mem_cons_of_mem _ hp)
            (Or.inl (by
              rcases Finset.mem_insert.mp h.1 with h1 | h1
              · exact h1
              · rw [Finset.mem_singleton] at h1
                exfalso; exact hne1 (nodup_flatMap_pair_unique ch (u₁, v₁) p hchosen_nodup h1_mem
                  (List.mem_cons_of_mem _ hp) (Or.inr (Or.inl h1))))))
        · exact h.1
      simp [hp_out]
    simp [W₀, hfilt]
  refine hstep (t - V₀.card) W₀ V₀ rfl (by simp [W₀]) ?_ ?_ (by simp [W₀]) (by simp [W₀])
    (by simp [V₀]) ?_ ?_ (by simp [W₀, hV₀_card]) (by omega) hchInv₀ hWcnt₀ ?_
  · intro e he
    simp only [W₀, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact h1_adj
    · exact h1_adj.symm
  · exact List.IsChain.cons_cons rfl (List.IsChain.singleton _)
  · intro e he
    simp only [W₀, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> simp [V₀]
  · intro v hv
    simp only [V₀, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with hvu | hvv
    · rw [hvu]; exact ⟨(u₁, v₁, true), by simp [W₀], rfl⟩
    · rw [hvv]; exact ⟨(v₁, u₁, false), by simp [W₀], rfl⟩
  · simp [W₀, huv1]

/- ### Length assignment and cycle assembly -/

private def assignList {α : Type*} (B : ℕ) (W : List (α × α × Bool)) (D : ℕ) : List ℕ :=
  match W with
  | [] => []
  | e :: rest =>
    if e.2.2 then min B D :: assignList B rest (D - min B D)
    else 0 :: assignList B rest D

private lemma assignList_length {α : Type*} (B : ℕ) :
    ∀ (W : List (α × α × Bool)) (D : ℕ), (assignList B W D).length = W.length := by
  intro W
  induction W with
  | nil => intro D; simp [assignList]
  | cons e rest ih =>
    intro D
    unfold assignList
    by_cases hf : e.2.2 = true <;> simp [hf, ih]

private lemma assignList_props {α : Type*} (B : ℕ) :
    ∀ (W : List (α × α × Bool)) (D : ℕ),
      D ≤ W.countP (·.2.2) * B →
      (assignList B W D).length = W.length ∧
      (assignList B W D).sum = D ∧
      (∀ i (hi : i < W.length), (assignList B W D)[i]'(assignList_length B W D ▸ hi) ≤ B) ∧
      (∀ i (hi : i < W.length), W[i].2.2 = false →
        (assignList B W D)[i]'(assignList_length B W D ▸ hi) = 0) := by
  intro W
  induction W with
  | nil =>
    intro D hD
    simp [assignList] at hD ⊢
    omega
  | cons e rest ih =>
    intro D hD
    by_cases hf : e.2.2 = true
    · have hD' : D - min B D ≤ rest.countP (·.2.2) * B := by
        have hcnt : (e :: rest).countP (·.2.2) = rest.countP (·.2.2) + 1 := by
          simp [List.countP_cons, hf]
        rw [hcnt, Nat.add_one_mul] at hD
        by_cases hBD : B ≤ D
        · rw [min_eq_left hBD]; omega
        · rw [min_eq_right (Nat.le_of_not_le hBD)]; simp
      obtain ⟨hlen, hsum, hleB, hzero⟩ := ih (D - min B D) hD'
      refine ⟨assignList_length B (e :: rest) D, ?_, ?_, ?_⟩
      · simp only [assignList, if_pos hf, List.sum_cons, hsum]; omega
      · intro i hi
        rcases i with _ | i
        · simp only [assignList, if_pos hf, List.getElem_cons_zero]; exact min_le_left B D
        · simp only [assignList, if_pos hf, List.getElem_cons_succ]
          exact hleB i (by simpa using hi)
      · intro i hi hif
        rcases i with _ | i
        · simp [hf] at hif
        · simp only [assignList, if_pos hf, List.getElem_cons_succ]
          exact hzero i (by simpa using hi) (by simpa using hif)
    · have hf' : e.2.2 = false := Bool.eq_false_iff.mpr hf
      have hcnt : (e :: rest).countP (·.2.2) = rest.countP (·.2.2) := by
        simp [List.countP_cons, hf']
      rw [hcnt] at hD
      obtain ⟨hlen, hsum, hleB, hzero⟩ := ih D hD
      refine ⟨assignList_length B (e :: rest) D, ?_, ?_, ?_⟩
      · simp only [assignList, if_neg hf, List.sum_cons, zero_add, hsum]
      · intro i hi
        rcases i with _ | i
        · simp only [assignList, if_neg hf, List.getElem_cons_zero]; omega
        · simp only [assignList, if_neg hf, List.getElem_cons_succ]
          exact hleB i (by simpa using hi)
      · intro i hi hif
        rcases i with _ | i
        · simp only [assignList, if_neg hf, List.getElem_cons_zero]
        · simp only [assignList, if_neg hf, List.getElem_cons_succ]
          exact hzero i (by simpa using hi) (by simpa using hif)

private lemma sum_range_eq_list_sum : ∀ (l : List ℕ) (f : ℕ → ℕ),
    (∀ i (hi : i < l.length), f i = l[i]) →
    ∑ i ∈ Finset.range l.length, f i = l.sum := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
    intro f hf
    rw [List.length_cons, Finset.sum_range_succ', List.sum_cons, add_comm]
    congr 1
    · exact hf 0 (Nat.zero_lt_succ _)
    · exact ih (fun i => f (i + 1)) (fun i hi => by
        rw [hf (i + 1) (Nat.succ_lt_succ hi), List.getElem_cons_succ])

private lemma cycleGraph_of_cycleList {N n : ℕ} (G : SimpleGraph (Fin N)) (hn4 : 4 ≤ n)
    (cyc : List (Fin N)) (hlen : cyc.length = n) (hnodup : cyc.Nodup)
    (hstep : ∀ i (hi : i + 1 < cyc.length), G.Adj cyc[i] cyc[i + 1])
    (hwrap : ∀ h : 0 < cyc.length, G.Adj cyc[cyc.length - 1] cyc[0]) :
    (cycleGraph n).IsContained G := by
  have hn0 : 0 < n := by omega
  haveI : NeZero n := ⟨by omega⟩
  let f : Fin n → Fin N := fun i => cyc[i.val]'(hlen ▸ i.isLt)
  have hinj : Function.Injective f := by
    intro i j hij
    exact Fin.ext (congrArg (@Fin.val cyc.length)
      (List.nodup_iff_injective_getElem.mp hnodup (a₁ := ⟨i.val, hlen ▸ i.isLt⟩) (a₂ := ⟨j.val, hlen ▸ j.isLt⟩) hij))
  let hhom : (cycleGraph n) →g G := ⟨f, by
    intro a b hab
    have hcases : (a - b).val = 1 ∨ (b - a).val = 1 := SimpleGraph.cycleGraph_adj'.mp hab
    have step_adj : ∀ x y : Fin n, (y - x).val = 1 → G.Adj (f x) (f y) := by
      intro x y hxy
      have hy_val : y.val = (x.val + 1) % n := by
        rw [Fin.coe_sub] at hxy
        by_cases hle : x.val ≤ y.val
        · have h1 : y.val - x.val = 1 := by
            rw [show (n - x.val + y.val) % n = (n + (y.val - x.val)) % n by congr 1; omega,
              Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hxy
            exact hxy
          have : x.val + 1 < n := by omega
          rw [Nat.mod_eq_of_lt this]; omega
        · have h1 : n - x.val + y.val = 1 := by
            rw [Nat.mod_eq_of_lt (by omega)] at hxy; exact hxy
          have hx_last : x.val = n - 1 := by omega
          have hy0 : y.val = 0 := by omega
          rw [hx_last, show n - 1 + 1 = n by omega, Nat.mod_self, hy0]
      rcases eq_or_ne (x.val + 1) n with hlast | hlt
      · have hy0 : y.val = 0 := by rw [hy_val, hlast, Nat.mod_self]
        have hxlast : x.val = cyc.length - 1 := by omega
        simpa [f, hxlast, hy0] using hwrap (hlen ▸ hn0)
      · have hlt' : x.val + 1 < cyc.length := by omega
        have hy' : y.val = x.val + 1 := by rw [hy_val, Nat.mod_eq_of_lt (by omega)]
        simpa [f, hy'] using hstep x.val hlt'
    rcases hcases with h | h
    · exact (step_adj b a h).symm
    · exact step_adj a b h⟩
  exact ⟨⟨hhom, fun i j h => hinj h⟩⟩

private lemma assemble_cycle {N n L : ℕ} (G : SimpleGraph (Fin N)) (hn4 : 4 ≤ n) (hL : 0 < L)
    (z : ℕ → Fin N) (segs : ℕ → List (Fin N))
    (hne : ∀ i < L, segs i ≠ [])
    (hhead : ∀ i < L, ∀ h : segs i ≠ [], (segs i).head h = z i)
    (hnodup : ∀ i < L, (segs i).Nodup)
    (hchain : ∀ i < L, (segs i).IsChain G.Adj)
    (hnext : ∀ i < L, ∀ h : segs i ≠ [], G.Adj ((segs i).getLast h) (z ((i + 1) % L)))
    (hdisj : ∀ i₁ < L, ∀ i₂ < L, i₁ ≠ i₂ → Disjoint (segs i₁).toFinset (segs i₂).toFinset)
    (hsum : ∑ i ∈ Finset.range L, (segs i).length = n) :
    (cycleGraph n).IsContained G := by
  have hbuild : ∀ k : ℕ, 1 ≤ k → k ≤ L →
      let pref := (List.range k).flatMap segs
      pref ≠ [] ∧
      (∀ h : pref ≠ [], pref.head h = z 0) ∧
      (∀ h : pref ≠ [], ∀ hk : segs (k - 1) ≠ [], pref.getLast h = (segs (k - 1)).getLast hk) ∧
      pref.Nodup ∧
      pref.IsChain G.Adj ∧
      pref.toFinset = (Finset.range k).biUnion (fun i => (segs i).toFinset) ∧
      pref.length = ∑ i ∈ Finset.range k, (segs i).length := by
    intro k hk1 hkL
    induction k with
    | zero => omega
    | succ k ih =>
      rcases eq_or_lt_of_le hk1 with hkeq1 | hkgt1
      · have hk0 : k = 0 := by omega
        subst hk0
        have h0ne : segs 0 ≠ [] := hne 0 hL
        refine ⟨by simpa using h0ne, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro _; simpa using hhead 0 hL h0ne
        · intro _ _; simp
        · simpa using hnodup 0 hL
        · simpa using hchain 0 hL
        · simp
        · simp
      · have hk1' : 1 ≤ k := by omega
        obtain ⟨hpne, hphead, hplast, hpnodup, hpchain, hpfin, hplen⟩ := ih hk1' (by omega)
        have hkne : segs k ≠ [] := hne k hkL
        have hk1ne : segs (k - 1) ≠ [] := hne (k - 1) (by omega)
        have heq_cat : (List.range (k + 1)).flatMap segs = (List.range k).flatMap segs ++ segs k := by
          rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
        rw [heq_cat]
        set pref := (List.range k).flatMap segs
        have hne' : pref ++ segs k ≠ [] := List.append_ne_nil_of_right_ne_nil _ hkne
        have hdisj_k : Disjoint pref.toFinset (segs k).toFinset := by
          rw [hpfin, Finset.disjoint_biUnion_left]
          intro i hi
          exact hdisj i (by rw [Finset.mem_range] at hi; omega) k hkL (by rw [Finset.mem_range] at hi; omega)
        refine ⟨hne', ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro h'
          rw [List.head_append_of_ne_nil hpne, hphead hpne]
        · intro h' _
          simpa using List.getLast_append_of_ne_nil h' hkne
        · rw [List.nodup_append]
          refine ⟨hpnodup, hnodup k hkL, fun a ha b hb heq => ?_⟩
          subst heq
          exact Finset.disjoint_left.mp hdisj_k (List.mem_toFinset.mpr ha) (List.mem_toFinset.mpr hb)
        · refine isChain_append hpchain (hchain k hkL) ?_
          intro a ha b hb
          have ha' : a = pref.getLast hpne := (by
            rw [List.getLast?_eq_some_getLast hpne] at ha; simpa using ha : pref.getLast hpne = a).symm
          have hb' : b = (segs k).head hkne := (by
            rw [List.head?_eq_some_head hkne] at hb; simpa using hb : (segs k).head hkne = b).symm
          subst ha'; subst hb'
          rw [hplast hpne hk1ne, hhead k hkL hkne]
          have hmod : (k - 1 + 1) % L = k := by
            rw [show k - 1 + 1 = k by omega, Nat.mod_eq_of_lt hkL]
          simpa [hmod] using hnext (k - 1) (by omega) hk1ne
        · rw [List.toFinset_append, hpfin, Finset.range_add_one, Finset.biUnion_insert, Finset.union_comm]
        · rw [List.length_append, hplen, Finset.sum_range_succ]
  obtain ⟨hcyne, hcyhead, hcylast, hcynodup, hcychain, _, hcylen⟩ := hbuild L hL le_rfl
  set cyc := (List.range L).flatMap segs
  have hL1ne : segs (L - 1) ≠ [] := hne (L - 1) (by omega)
  refine cycleGraph_of_cycleList G hn4 cyc (hcylen.trans hsum) hcynodup ?_ ?_
  · intro i hi
    exact List.isChain_iff_getElem.mp hcychain i hi
  · intro h0
    have hne' : cyc ≠ [] := List.ne_nil_of_length_pos h0
    have hlast_eq : cyc[cyc.length - 1] = cyc.getLast hne' := (List.getLast_eq_getElem hne').symm
    have hhead_eq : cyc[0] = cyc.head hne' := (List.head_eq_getElem hne').symm
    rw [hlast_eq, hhead_eq, hcylast hne' hL1ne, hcyhead hne']
    have hmod : (L - 1 + 1) % L = 0 := by rw [show L - 1 + 1 = L by omega, Nat.mod_self]
    simpa [hmod] using hnext (L - 1) (by omega) hL1ne

/- ### Bridge segment for a blown-up matching step -/

private lemma true_indices_disjoint {α : Type*} [DecidableEq α] :
    ∀ (W : List (α × α × Bool)),
      ((W.filter (·.2.2)).flatMap (fun e => [e.1, e.2.1])).Nodup →
      ∀ (i₁ i₂ : ℕ) (hi₁ : i₁ < W.length) (hi₂ : i₂ < W.length),
        i₁ < i₂ → W[i₁].2.2 = true → W[i₂].2.2 = true →
        Disjoint ({W[i₁].1, W[i₁].2.1} : Finset α) ({W[i₂].1, W[i₂].2.1} : Finset α) := by
  intro W
  induction W with
  | nil => intro _ i₁ _ hi₁; simp at hi₁
  | cons e rest ih =>
    intro hnodup i₁ i₂ hi₁ hi₂ hlt h1 h2
    have hnodup_rest : ((rest.filter (·.2.2)).flatMap (fun x => [x.1, x.2.1])).Nodup := by
      by_cases he : e.2.2 = true
      · simp only [List.filter_cons, he, ↓reduceIte, List.flatMap_cons, List.cons_append,
          List.nil_append, List.nodup_cons] at hnodup
        exact hnodup.2.2
      · have he' : e.2.2 = false := Bool.eq_false_iff.mpr he
        simp only [List.filter_cons, he', Bool.false_eq_true, ↓reduceIte] at hnodup
        exact hnodup
    rcases i₁ with _ | j₁ <;> rcases i₂ with _ | j₂
    · omega
    · simp only [List.getElem_cons_zero] at h1
      simp only [List.filter_cons, h1, ↓reduceIte, List.flatMap_cons, List.cons_append,
        List.nil_append, List.nodup_cons] at hnodup
      have hj₂ : j₂ < rest.length := by simpa using hi₂
      have hmem : rest[j₂]'hj₂ ∈ rest.filter (·.2.2) :=
        List.mem_filter.mpr ⟨List.getElem_mem hj₂, by simpa using h2⟩
      have hm1 : (rest[j₂]'hj₂).1 ∈ (rest.filter (·.2.2)).flatMap (fun x => [x.1, x.2.1]) :=
        List.mem_flatMap.mpr ⟨rest[j₂]'hj₂, hmem, by simp⟩
      have hm2 : (rest[j₂]'hj₂).2.1 ∈ (rest.filter (·.2.2)).flatMap (fun x => [x.1, x.2.1]) :=
        List.mem_flatMap.mpr ⟨rest[j₂]'hj₂, hmem, by simp⟩
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      simp only [List.getElem_cons_zero, List.getElem_cons_succ, Finset.mem_insert,
        Finset.mem_singleton] at hz1 hz2
      rcases hz1 with rfl | rfl <;> rcases hz2 with heq | heq
      · exact hnodup.1 (List.mem_cons_of_mem _ (heq ▸ hm1))
      · exact hnodup.1 (List.mem_cons_of_mem _ (heq ▸ hm2))
      · exact hnodup.2.1 (heq ▸ hm1)
      · exact hnodup.2.1 (heq ▸ hm2)
    · omega
    · exact ih hnodup_rest j₁ j₂ (by simpa using hi₁) (by simpa using hi₂) (by omega)
        (by simpa using h1) (by simpa using h2)

private lemma bridge_segment {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    {d η : ℝ} (hη : 0 < η) (hd_gt : η < d)
    {U V ResU CapU BodyU BodyV : Finset (Fin N)}
    (hResU : ResU ⊆ U) (hCapU : CapU ⊆ U) (hBodyU : BodyU ⊆ U) (hBodyV : BodyV ⊆ V)
    (hdisjUV : Disjoint U V)
    (hRC : Disjoint ResU CapU) (hRB : Disjoint ResU BodyU) (hCB : Disjoint CapU BodyU)
    (huni : G.IsUniform η U V) (hd : d ≤ (G.edgeDensity U V : ℝ))
    (hUpos : 0 < U.card) (hVpos : 0 < V.card)
    (c : ℕ) (hcU : (U.card : ℝ) * η ≤ (c : ℝ)) (hcV : (V.card : ℝ) * η ≤ (c : ℝ))
    (hcBodyU : (c : ℝ) ≤ (d - η) * (BodyU.card : ℝ))
    (hCapCard : (U.card : ℝ) * η ≤ (CapU.card : ℝ))
    (hBodyUcard : (U.card : ℝ) * η ≤ (BodyU.card : ℝ))
    (hBodyVcard : (V.card : ℝ) * η ≤ (BodyV.card : ℝ))
    {zu zv : Fin N} (hzu : zu ∈ ResU)
    (hzu_deg : (d - η) * (BodyV.card : ℝ) < ((G.neighborFinset zu ∩ BodyV).card : ℝ))
    (hzv_deg : (d - η) * (CapU.card : ℝ) < ((G.neighborFinset zv ∩ CapU).card : ℝ))
    (hSend_big : (U.card : ℝ) * η ≤ (d - η) * (CapU.card : ℝ))
    (hPool_big : 3 * ((max U.card V.card : ℝ) * η + 1) ≤ (d - η) * (BodyV.card : ℝ))
    (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓ_len : ℓ ≤ min (BodyV.card - c) BodyU.card - 2 * c) :
    ∃ seg : List (Fin N),
      seg ≠ [] ∧
      seg.length = 2 * ℓ + 1 ∧
      (∀ h : seg ≠ [], seg.head h = zu) ∧
      (∀ h : seg ≠ [], G.Adj (seg.getLast h) zv) ∧
      seg.Nodup ∧
      seg.IsChain G.Adj ∧
      seg.toFinset ⊆ insert zu (BodyU ∪ BodyV ∪ CapU) := by
  set S_end := G.neighborFinset zv ∩ CapU
  have hSend_sub : S_end ⊆ U := Finset.inter_subset_right.trans hCapU
  have hSend_card : (U.card : ℝ) * η ≤ (S_end.card : ℝ) := hSend_big.trans hzv_deg.le
  have huniVU : G.IsUniform η V U := huni.symm
  have hdVU : d ≤ (G.edgeDensity V U : ℝ) := by rwa [SimpleGraph.edgeDensity_comm]
  set B_bad := V.filter (fun y => ((G.neighborFinset y ∩ S_end).card : ℝ) ≤ (d - η) * (S_end.card : ℝ))
  have hB_bad : (B_bad.card : ℝ) < (V.card : ℝ) * η :=
    card_bad_lt G hη huniVU hdVU hVpos hUpos hSend_sub hSend_card
  set Body'V := BodyV \ B_bad
  have hBody'V_sub : Body'V ⊆ V := Finset.sdiff_subset.trans hBodyV
  have hBody'V_card : BodyV.card - c ≤ Body'V.card := by
    have hB_le : B_bad.card ≤ c := by
      have h1 : (B_bad.card : ℝ) < (c : ℝ) := hB_bad.trans_le hcV
      exact_mod_cast h1.le
    have h2 : BodyV.card ≤ Body'V.card + B_bad.card := by
      calc BodyV.card ≤ (Body'V ∪ B_bad).card := Finset.card_le_card (fun x hx => by
            by_cases h : x ∈ B_bad
            · exact Finset.mem_union_right _ h
            · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, h⟩))
        _ ≤ Body'V.card + B_bad.card := Finset.card_union_le _ _
    omega
  set P := G.neighborFinset zu ∩ Body'V
  have hP_sub : P ⊆ V := Finset.inter_subset_right.trans hBody'V_sub
  have hP_card : ((∅ : Finset (Fin N)).card : ℝ) + 2 * (V.card : ℝ) * η ≤ (P.card : ℝ) := by
    have h1 : (G.neighborFinset zu ∩ BodyV).card ≤ P.card + B_bad.card := by
      calc (G.neighborFinset zu ∩ BodyV).card
          ≤ (P ∪ B_bad).card := Finset.card_le_card (fun x hx => by
              rw [Finset.mem_inter] at hx
              by_cases h : x ∈ B_bad
              · exact Finset.mem_union_right _ h
              · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx.1, Finset.mem_sdiff.mpr ⟨hx.2, h⟩⟩))
        _ ≤ P.card + B_bad.card := Finset.card_union_le _ _
    have h1r : ((G.neighborFinset zu ∩ BodyV).card : ℝ) ≤ (P.card : ℝ) + (B_bad.card : ℝ) := by
      exact_mod_cast h1
    have hmaxV : (V.card : ℝ) ≤ (max U.card V.card : ℝ) := by exact_mod_cast le_max_right U.card V.card
    simp only [Finset.card_empty, Nat.cast_zero, zero_add]
    nlinarith
  obtain ⟨y₁, hy₁P, _, hy₁_BodyU, _⟩ := exists_good_two G hη hP_sub hVpos huniVU hdVU
    hUpos hBodyU hBodyUcard huniVU hdVU hUpos hBodyU hBodyUcard hP_card
  have hy₁_Body'V : y₁ ∈ Body'V := (Finset.mem_inter.mp hy₁P).2
  have hzy₁ : G.Adj zu y₁ := (G.mem_neighborFinset zu y₁).mp (Finset.mem_inter.mp hy₁P).1
  have hy₁_deg : c ≤ (G.neighborFinset y₁ ∩ BodyU).card := by
    exact_mod_cast (hcBodyU.trans_lt hy₁_BodyU).le
  have hc_pos : 0 < c := by
    have h1 : (0 : ℝ) < (U.card : ℝ) * η := by positivity
    exact_mod_cast h1.trans_le hcU
  have hdisj_BU : Disjoint Body'V BodyU :=
    hdisjUV.symm.mono hBody'V_sub hBodyU
  have hnoempty : ∀ X ⊆ Body'V, ∀ Y ⊆ BodyU, c ≤ X.card → c ≤ Y.card →
      ∃ x ∈ X, ∃ y ∈ Y, G.Adj x y :=
    no_empty_pair_of_uniform G hd_gt huniVU hdVU hBody'V_sub hBodyU hcV hcU
  obtain ⟨Q, hQne, hQhead, hQnodup, hQchain, hQsub, hQlen, hQalt⟩ :=
    dfs_long_path G Body'V BodyU hdisj_BU hc_pos hc_pos hnoempty y₁ hy₁_Body'V hy₁_deg
  have htake_le : 2 * ℓ - 1 ≤ Q.length := by
    have h1 : min (BodyV.card - c) BodyU.card ≤ min Body'V.card BodyU.card := by omega
    omega
  set Q' := Q.take (2 * ℓ - 1)
  have hQ'len : Q'.length = 2 * ℓ - 1 := List.length_take_of_le htake_le
  have hQ'ne : Q' ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hQ'head : Q'.head hQ'ne = y₁ := by
    rw [List.head_eq_getElem hQ'ne]
    simp only [Q', List.getElem_take]
    rw [← List.head_eq_getElem hQne, ← Option.some.injEq]
    rw [List.head?_eq_some_head hQne] at hQhead
    exact hQhead
  have hQ'nodup : Q'.Nodup := hQnodup.take
  have hQ'chain : Q'.IsChain G.Adj := by
    have h1 : Q'.IsChain (bipartAdj G Body'V BodyU) := hQchain.take (2 * ℓ - 1)
    exact h1.imp (fun {_ _} h => h.2)
  have hQ'sub : Q'.toFinset ⊆ BodyU ∪ BodyV := by
    intro x hx
    have hxQ : x ∈ Q := List.mem_of_mem_take (List.mem_toFinset.mp hx)
    rcases Finset.mem_union.mp (hQsub (List.mem_toFinset.mpr hxQ)) with hV | hU
    · exact Finset.mem_union_right _ (Finset.sdiff_subset hV)
    · exact Finset.mem_union_left _ hU
  set y_last := Q'.getLast hQ'ne
  have hy_last_eq : y_last = Q[2 * ℓ - 2]'(by omega) := by
    change Q'.getLast hQ'ne = Q[2 * ℓ - 2]'(by omega)
    rw [List.getLast_eq_getElem hQ'ne]
    simp only [Q', hQ'len]
    exact List.getElem_take
  have hy_last_Body'V : y_last ∈ Body'V := by
    rw [hy_last_eq]
    exact (hQalt (2 * ℓ - 2) (by omega)).1 ⟨ℓ - 1, by omega⟩
  have hy_last_bad : y_last ∉ B_bad := (Finset.mem_sdiff.mp hy_last_Body'V).2
  have hy_last_V : y_last ∈ V := hBody'V_sub hy_last_Body'V
  have hy_last_deg : (d - η) * (S_end.card : ℝ) < ((G.neighborFinset y_last ∩ S_end).card : ℝ) := by
    by_contra! hle
    exact hy_last_bad (Finset.mem_filter.mpr ⟨hy_last_V, hle⟩)
  have hy_last_pos : 0 < (G.neighborFinset y_last ∩ S_end).card := by
    have hSpos : (0 : ℝ) < (S_end.card : ℝ) := by
      have : (0 : ℝ) < (U.card : ℝ) * η := by positivity
      exact this.trans_le hSend_card
    have h1 : (0 : ℝ) < (d - η) * (S_end.card : ℝ) := mul_pos (sub_pos.mpr hd_gt) hSpos
    exact_mod_cast h1.trans hy_last_deg
  obtain ⟨x_last, hx_last⟩ := Finset.card_pos.mp hy_last_pos
  rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hx_last
  have hx_last_CapU : x_last ∈ CapU := (Finset.mem_inter.mp hx_last.2).2
  have hx_last_zv : G.Adj x_last zv :=
    ((G.mem_neighborFinset zv x_last).mp (Finset.mem_inter.mp hx_last.2).1).symm
  set seg := zu :: (Q' ++ [x_last])
  have hseg_ne : seg ≠ [] := by simp [seg]
  have hzu_not_BUV : zu ∉ BodyU ∪ BodyV := by
    intro h
    rcases Finset.mem_union.mp h with hU | hV
    · exact Finset.disjoint_left.mp hRB hzu hU
    · exact Finset.disjoint_left.mp hdisjUV (hResU hzu) (hBodyV hV)
  have hx_not_BUV : x_last ∉ BodyU ∪ BodyV := by
    intro h
    rcases Finset.mem_union.mp h with hU | hV
    · exact Finset.disjoint_left.mp hCB hx_last_CapU hU
    · exact Finset.disjoint_left.mp hdisjUV (hCapU hx_last_CapU) (hBodyV hV)
  have hzu_ne_x : zu ≠ x_last := fun h =>
    Finset.disjoint_left.mp hRC hzu (h ▸ hx_last_CapU)
  refine ⟨seg, hseg_ne, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [seg, hQ'len]; omega
  · intro _; simp [seg]
  · intro _
    have h1 : seg.getLast hseg_ne = (Q' ++ [x_last]).getLast (by simp) :=
      List.getLast_cons (by simp)
    rw [h1, List.getLast_append_singleton]
    exact hx_last_zv
  · rw [show seg = zu :: (Q' ++ [x_last]) from rfl, List.nodup_cons]
    refine ⟨?_, ?_⟩
    · simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨fun h => hzu_not_BUV (hQ'sub (List.mem_toFinset.mpr h)), hzu_ne_x⟩
    · rw [List.nodup_append]
      refine ⟨hQ'nodup, List.nodup_singleton _, fun a ha b hb heq => ?_⟩
      rw [List.mem_singleton] at hb
      subst hb; subst heq
      exact hx_not_BUV (hQ'sub (List.mem_toFinset.mpr ha))
  · refine List.IsChain.cons_of_ne_nil (by simp) ?_ ?_
    · refine isChain_append hQ'chain (List.isChain_singleton _) ?_
      intro a ha b hb
      have ha' : a = y_last := (by
        rw [List.getLast?_eq_some_getLast hQ'ne] at ha; simpa using ha : y_last = a).symm
      have hb' : b = x_last := (by simpa using hb : x_last = b).symm
      subst ha'; subst hb'
      exact hx_last.1
    · rw [List.head_append_of_ne_nil hQ'ne, hQ'head]
      exact hzy₁
  · intro x hx
    simp only [seg, List.toFinset_cons, List.toFinset_append, List.toFinset_nil,
      Finset.mem_insert, Finset.mem_union, Finset.notMem_empty, or_false] at hx
    rcases hx with rfl | hxQ | rfl
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (by
        have := hQ'sub hxQ
        rcases Finset.mem_union.mp this with h | h
        · exact Finset.mem_union_left _ h
        · exact Finset.mem_union_right _ h))
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hx_last_CapU)

/- ### Selecting tour transition vertices along closed walk W -/

set_option maxHeartbeats 800000 in
private lemma embed_tour_vertices {N t : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    {d η : ℝ} (hη : 0 < η)
    (parts : Fin t → Finset (Fin N)) (R : SimpleGraph (Fin t))
    (hparts_pos : ∀ i : Fin t, 0 < (parts i).card)
    (hR : ∀ u v : Fin t, R.Adj u v → G.IsUniform η (parts u) (parts v) ∧ d ≤ (G.edgeDensity (parts u) (parts v) : ℝ))
    (Res Cap Body : Fin t → Finset (Fin N))
    (hRes_sub : ∀ i, Res i ⊆ parts i) (hCap_sub : ∀ i, Cap i ⊆ parts i) (hBody_sub : ∀ i, Body i ⊆ parts i)
    (hRes_sz : ∀ i j, (parts j).card * η ≤ (Res i).card)
    (hCap_sz : ∀ i j, (parts j).card * η ≤ (Cap i).card)
    (hBody_sz : ∀ i j, (parts j).card * η ≤ (Body i).card)
    (L : ℕ) (w w' : ℕ → Fin t)
    (hw_adj : ∀ i < L, R.Adj (w i) (w' i))
    (hw'_eq : ∀ i, i + 1 < L → w' i = w (i + 1))
    (hw_wrap : w' (L - 1) = w 0)
    (len : ℕ → ℕ)
    (hlen_L : len (L - 1) = 0)
    (hL_ge : 2 ≤ L)
    (hL2_len0 : L = 2 → 0 < len 0)
    (hPool_Res : ∀ i, (L : ℝ) + 2 * ((parts i).card : ℝ) * η ≤ (Res i).card)
    (hPool_Send : ∀ i j, (parts j).card * η ≤ (d - η) * (Res i).card ∧
      (L : ℝ) + 2 * ((parts j).card : ℝ) * η ≤ (d - η) * (Res i).card)
    (hPool_Send2 : ∀ i j, (L : ℝ) + 2 * ((parts j).card : ℝ) * η ≤ (d - η) * ((d - η) * (Res i).card)) :
    ∃ z : ℕ → Fin N,
      (∀ i < L, z i ∈ Res (w i)) ∧
      (∀ i₁ < L, ∀ i₂ < L, i₁ ≠ i₂ → z i₁ ≠ z i₂) ∧
      (∀ i (hi : i + 1 < L),
        if 0 < len i then (d - η) * ((Body (w' i)).card : ℝ) < ((G.neighborFinset (z i) ∩ Body (w' i)).card : ℝ)
        else if i + 1 < L - 1 then (d - η) * ((Res (w' i)).card : ℝ) < ((G.neighborFinset (z i) ∩ Res (w' i)).card : ℝ)
        else (d - η) * ((G.neighborFinset (z 0) ∩ Res (w (L - 1))).card : ℝ) <
          ((G.neighborFinset (z i) ∩ (G.neighborFinset (z 0) ∩ Res (w (L - 1)))).card : ℝ)) ∧
      (∀ i (hi : 0 < i) (hiL : i < L),
        if 0 < len (i - 1) then (d - η) * ((Cap (w (i - 1))).card : ℝ) < ((G.neighborFinset (z i) ∩ Cap (w (i - 1))).card : ℝ)
        else G.Adj (z (i - 1)) (z i)) ∧
      G.Adj (z (L - 1)) (z 0) := by
  classical
  let S_end : Fin N → Finset (Fin N) := fun z0 => G.neighborFinset z0 ∩ Res (w (L - 1))
  let TargetNext : Fin N → (i : ℕ) → i + 1 < L → Finset (Fin N) := fun z0 i _ =>
    if 0 < len i then Body (w' i)
    else if i + 1 < L - 1 then Res (w' i)
    else S_end z0
  have hT_sub : ∀ z0 i (hi : i + 1 < L), TargetNext z0 i hi ⊆ parts (w' i) := by
    intro z0 i hi
    simp only [TargetNext]
    split_ifs with h1 h2
    · exact hBody_sub _
    · exact hRes_sub _
    · have heq : w (L - 1) = w' i := by
        have hL1 : i + 1 = L - 1 := by omega
        rw [← hL1, ← hw'_eq i hi]
      rw [← heq]
      exact Finset.inter_subset_right.trans (hRes_sub _)
  have hbind : ∀ k : ℕ, 1 ≤ k → k ≤ L →
      ∃ z : ℕ → Fin N,
        (∀ i < k, z i ∈ Res (w i)) ∧
        (∀ i₁ < k, ∀ i₂ < k, i₁ ≠ i₂ → z i₁ ≠ z i₂) ∧
        (d - η) * ((Res (w (L - 1))).card : ℝ) < ((G.neighborFinset (z 0) ∩ Res (w (L - 1))).card : ℝ) ∧
        (∀ i (hi : i < k) (hi1 : i + 1 < L),
          (d - η) * ((TargetNext (z 0) i hi1).card : ℝ) <
            ((G.neighborFinset (z i) ∩ TargetNext (z 0) i hi1).card : ℝ)) ∧
        (∀ i (hi : 0 < i) (hik : i < k),
          if 0 < len (i - 1) then
            (d - η) * ((Cap (w (i - 1))).card : ℝ) < ((G.neighborFinset (z i) ∩ Cap (w (i - 1))).card : ℝ)
          else G.Adj (z (i - 1)) (z i)) ∧
        (k = L → G.Adj (z (L - 1)) (z 0)) := by
    intro k hk1 hkL
    induction k with
    | zero => omega
    | succ k ih =>
      rcases eq_or_lt_of_le hk1 with hkeq1 | hkgt1
      · have hk0 : k = 0 := by omega
        subst hk0
        have h0L : 0 + 1 < L := by omega
        let T1 := if 0 < len 0 then Body (w' 0) else Res (w' 0)
        have hT1_sub : T1 ⊆ parts (w' 0) := by
          dsimp [T1]; split_ifs <;> [exact hBody_sub _; exact hRes_sub _]
        have hT1_sz : (parts (w' 0)).card * η ≤ (T1.card : ℝ) := by
          dsimp [T1]; split_ifs <;> [exact hBody_sz _ _; exact hRes_sz _ _]
        have hR01 := hR (w 0) (w' 0) (hw_adj 0 (by omega))
        have hRL0 : R.Adj (w 0) (w (L - 1)) := by
          have := hw_adj (L - 1) (by omega)
          rw [hw_wrap] at this
          exact this.symm
        have hR0L := hR (w 0) (w (L - 1)) hRL0
        have hP0 : ((∅ : Finset (Fin N)).card : ℝ) + 2 * ((parts (w 0)).card : ℝ) * η ≤ (Res (w 0)).card := by
          simp only [Finset.card_empty, Nat.cast_zero, zero_add]
          exact le_trans (by linarith) (hPool_Res (w 0))
        obtain ⟨z0, hz0_Res, _, hz0_T1, hz0_SL⟩ := exists_good_two G hη (hRes_sub (w 0))
          (hparts_pos _) hR01.1 hR01.2 (hparts_pos _) hT1_sub hT1_sz
          hR0L.1 hR0L.2 (hparts_pos _) (hRes_sub _) (hRes_sz _ _) hP0
        refine ⟨fun _ => z0, ?_, ?_, hz0_SL, ?_, ?_, ?_⟩
        · intro i hi; rw [show i = 0 by omega]; exact hz0_Res
        · intro i₁ hi₁ i₂ hi₂ hne; omega
        · intro i hi hi1
          have hi0 : i = 0 := by omega
          subst hi0
          have hT_eq : TargetNext z0 0 hi1 = T1 := by
            dsimp [TargetNext, T1]
            by_cases h0 : 0 < len 0
            · simp [h0]
            · have hLne2 : L ≠ 2 := fun h2 => h0 (hL2_len0 h2)
              have h1L : 0 + 1 < L - 1 := by omega
              simp [h0, h1L]
          simpa [hT_eq] using hz0_T1
        · intro i hi hik; omega
        · intro hL1; omega
      · obtain ⟨z, hz_Res, hz_inj, hz0_SL, hz_next, hz_prev, _⟩ := ih (by omega) (by omega)
        set avoid := (Finset.range k).image z
        have havoid_card : avoid.card ≤ L :=
          (Finset.card_image_le.trans (Finset.card_range k).le).trans (by omega)
        have hSend_sz : (parts (w (L - 1))).card * η ≤ ((S_end (z 0)).card : ℝ) :=
          (hPool_Send (w (L - 1)) (w (L - 1))).1.trans hz0_SL.le
        have hT_sz : ∀ i (hi : i + 1 < L), (parts (w' i)).card * η ≤ ((TargetNext (z 0) i hi).card : ℝ) := by
          intro i hi
          dsimp [TargetNext]
          split_ifs with h1 h2
          · exact hBody_sz _ _
          · exact hRes_sz _ _
          · have heq : w (L - 1) = w' i := by
              have hL1 : i + 1 = L - 1 := by omega
              rw [← hL1, ← hw'_eq i hi]
            rw [← heq]
            exact hSend_sz
        have hk_w : w' (k - 1) = w k := by
          simpa [show k - 1 + 1 = k by omega] using hw'_eq (k - 1) (by omega)
        have hR_prev : R.Adj (w k) (w (k - 1)) := by
          have := hw_adj (k - 1) (by omega)
          rw [hk_w] at this
          exact this.symm
        have hR_prev_p := hR (w k) (w (k - 1)) hR_prev
        have hSend_sub_wk : S_end (z 0) ⊆ parts (w (L - 1)) := Finset.inter_subset_right.trans (hRes_sub _)
        have hpick : ∃ zk : Fin N,
            zk ∈ Res (w k) ∧ zk ∉ avoid ∧
            (if 0 < len (k - 1) then
              (d - η) * ((Cap (w (k - 1))).card : ℝ) < ((G.neighborFinset zk ∩ Cap (w (k - 1))).card : ℝ)
            else G.Adj (z (k - 1)) zk) ∧
            (∀ hk1L : k + 1 < L,
              (d - η) * ((TargetNext (z 0) k hk1L).card : ℝ) <
                ((G.neighborFinset zk ∩ TargetNext (z 0) k hk1L).card : ℝ)) ∧
            (k = L - 1 → G.Adj zk (z 0)) := by
          by_cases hlen_prev : 0 < len (k - 1)
          · by_cases hk1L : k + 1 < L
            · have hR_next := hR (w k) (w' k) (hw_adj k hkL)
              have hP : (avoid.card : ℝ) + 2 * ((parts (w k)).card : ℝ) * η ≤ (Res (w k)).card := by
                have hav : (avoid.card : ℝ) ≤ (L : ℝ) := Nat.cast_le.mpr havoid_card
                linarith only [hav, hPool_Res (w k)]
              obtain ⟨zk, hzkP, hzk_av, hzk_cap, hzk_next⟩ := exists_good_two G hη (hRes_sub (w k))
                (hparts_pos _) hR_prev_p.1 hR_prev_p.2 (hparts_pos _) (hCap_sub _) (hCap_sz _ _)
                hR_next.1 hR_next.2 (hparts_pos _) (hT_sub (z 0) k hk1L) (hT_sz k hk1L) hP
              refine ⟨zk, hzkP, hzk_av, by simp [hlen_prev, hzk_cap], fun _ => hzk_next, fun h => by omega⟩
            · have hk_eq : k = L - 1 := by omega
              have hP_sub : S_end (z 0) ⊆ parts (w k) := by rw [hk_eq]; exact hSend_sub_wk
              have hP : (avoid.card : ℝ) + 2 * ((parts (w k)).card : ℝ) * η ≤ ((S_end (z 0)).card : ℝ) := by
                have hav : (avoid.card : ℝ) ≤ (L : ℝ) := Nat.cast_le.mpr havoid_card
                have hps := (hPool_Send (w (L - 1)) (w k)).2
                rw [hk_eq] at hps ⊢
                linarith only [hav, hps, hz0_SL]
              obtain ⟨zk, hzkP, hzk_av, hzk_cap, _⟩ := exists_good_two G hη hP_sub
                (hparts_pos _) hR_prev_p.1 hR_prev_p.2 (hparts_pos _) (hCap_sub _) (hCap_sz _ _)
                hR_prev_p.1 hR_prev_p.2 (hparts_pos _) (hCap_sub _) (hCap_sz _ _) hP
              have hzk_Res : zk ∈ Res (w k) := by rw [hk_eq]; exact (Finset.mem_inter.mp hzkP).2
              have hzk_z0 : G.Adj zk (z 0) :=
                ((G.mem_neighborFinset (z 0) zk).mp (Finset.mem_inter.mp hzkP).1).symm
              exact ⟨zk, hzk_Res, hzk_av, by simp [hlen_prev, hzk_cap], fun h => (hk1L h).elim, fun _ => hzk_z0⟩
          · have hk_prev_lt : k - 1 + 1 < L := by omega
            have hz_prev_deg := hz_next (k - 1) (by omega) hk_prev_lt
            by_cases hk1L : k + 1 < L
            · have hk_lt_L1 : k - 1 + 1 < L - 1 := by omega
              have hT_eq : TargetNext (z 0) (k - 1) hk_prev_lt = Res (w k) := by
                simp only [TargetNext, hlen_prev, ↓reduceIte, hk_lt_L1, hk_w]
              rw [hT_eq] at hz_prev_deg
              set P := G.neighborFinset (z (k - 1)) ∩ Res (w k)
              have hP_sub : P ⊆ parts (w k) := Finset.inter_subset_right.trans (hRes_sub _)
              have hP : (avoid.card : ℝ) + 2 * ((parts (w k)).card : ℝ) * η ≤ (P.card : ℝ) := by
                have hav : (avoid.card : ℝ) ≤ (L : ℝ) := Nat.cast_le.mpr havoid_card
                have hps := (hPool_Send (w k) (w k)).2
                linarith only [hav, hps, hz_prev_deg]
              have hR_next := hR (w k) (w' k) (hw_adj k hkL)
              obtain ⟨zk, hzkP, hzk_av, hzk_next, _⟩ := exists_good_two G hη hP_sub
                (hparts_pos _) hR_next.1 hR_next.2 (hparts_pos _) (hT_sub (z 0) k hk1L) (hT_sz k hk1L)
                hR_next.1 hR_next.2 (hparts_pos _) (hT_sub (z 0) k hk1L) (hT_sz k hk1L) hP
              have hzk_Res : zk ∈ Res (w k) := (Finset.mem_inter.mp hzkP).2
              have hzk_adj : G.Adj (z (k - 1)) zk := (G.mem_neighborFinset (z (k - 1)) zk).mp (Finset.mem_inter.mp hzkP).1
              exact ⟨zk, hzk_Res, hzk_av, by simp [hlen_prev, hzk_adj], fun _ => hzk_next, fun h => by omega⟩
            · have hk_eq : k = L - 1 := by omega
              have hk_lt_L1 : ¬ (k - 1 + 1 < L - 1) := by omega
              have hT_eq : TargetNext (z 0) (k - 1) hk_prev_lt = S_end (z 0) := by
                simp only [TargetNext, hlen_prev, ↓reduceIte, hk_lt_L1]
              rw [hT_eq] at hz_prev_deg
              set P := G.neighborFinset (z (k - 1)) ∩ S_end (z 0)
              have hP_pos : avoid.card < P.card := by
                have h1 : (avoid.card : ℝ) ≤ (L : ℝ) := Nat.cast_le.mpr havoid_card
                have h2 : (L : ℝ) < (d - η) * ((d - η) * ((Res (w (L - 1))).card : ℝ)) := by
                  have hnn := hPool_Send2 (w (L - 1)) (w k)
                  have hp : (0 : ℝ) < 2 * ((parts (w k)).card : ℝ) * η := by
                    have := hparts_pos (w k)
                    positivity
                  linarith only [hnn, hp]
                have h3 : (d - η) * ((d - η) * ((Res (w (L - 1))).card : ℝ)) <
                    (d - η) * ((S_end (z 0)).card : ℝ) := by
                  have hdn : 0 < d - η := by
                    have hps1 := (hPool_Send (w (L - 1)) (w (L - 1))).1
                    have hpos1 : (0 : ℝ) < (parts (w (L - 1))).card * η := by
                      have := hparts_pos (w (L - 1)); positivity
                    have hpos2 : (0 : ℝ) ≤ (Res (w (L - 1))).card := Nat.cast_nonneg _
                    nlinarith only [hps1, hpos1, hpos2]
                  exact mul_lt_mul_of_pos_left hz0_SL hdn
                exact_mod_cast (h1.trans_lt (h2.trans h3)).trans hz_prev_deg
              have hrem : (P \ avoid).Nonempty := Finset.card_pos.mp (by
                have : P.card ≤ (P \ avoid).card + avoid.card := by
                  calc P.card ≤ ((P \ avoid) ∪ avoid).card := Finset.card_le_card (fun x hx => by
                        by_cases h : x ∈ avoid
                        · exact Finset.mem_union_right _ h
                        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, h⟩))
                    _ ≤ (P \ avoid).card + avoid.card := Finset.card_union_le _ _
                omega)
              obtain ⟨zk, hzk⟩ := hrem
              rw [Finset.mem_sdiff] at hzk
              have hzk_mem := Finset.mem_inter.mp hzk.1
              have hzk_Send := Finset.mem_inter.mp hzk_mem.2
              have hzk_Res : zk ∈ Res (w k) := by rw [hk_eq]; exact hzk_Send.2
              have hzk_adj : G.Adj (z (k - 1)) zk := (G.mem_neighborFinset (z (k - 1)) zk).mp hzk_mem.1
              have hzk_z0 : G.Adj zk (z 0) := ((G.mem_neighborFinset (z 0) zk).mp hzk_Send.1).symm
              exact ⟨zk, hzk_Res, hzk.2, by simp [hlen_prev, hzk_adj], fun h => (hk1L h).elim, fun _ => hzk_z0⟩
        obtain ⟨zk, hzk_Res, hzk_av, hzk_prev, hzk_next, hzk_wrap⟩ := hpick
        let z' : ℕ → Fin N := fun i => if i = k then zk else z i
        have hz'0 : z' 0 = z 0 := if_neg (by omega : (0 : ℕ) ≠ k)
        refine ⟨z', ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro i hi
          by_cases hik : i = k
          · subst hik; dsimp only [z']; rw [if_pos rfl]; exact hzk_Res
          · dsimp only [z']; rw [if_neg hik]; exact hz_Res i (by omega)
        · intro i₁ hi₁ i₂ hi₂ hne
          by_cases h1 : i₁ = k <;> by_cases h2 : i₂ = k
          · exact (hne (h1.trans h2.symm)).elim
          · subst h1; dsimp only [z']; rw [if_pos rfl, if_neg h2]
            intro heq
            exact hzk_av (Finset.mem_image.mpr ⟨i₂, Finset.mem_range.mpr (by omega), heq.symm⟩)
          · subst h2; dsimp only [z']; rw [if_neg h1, if_pos rfl]
            intro heq
            exact hzk_av (Finset.mem_image.mpr ⟨i₁, Finset.mem_range.mpr (by omega), heq⟩)
          · dsimp only [z']; rw [if_neg h1, if_neg h2]
            exact hz_inj i₁ (by omega) i₂ (by omega) hne
        · rw [hz'0]; exact hz0_SL
        · intro i hi hi1
          rw [hz'0]
          by_cases hik : i = k
          · subst hik
            have hzk1 : z' i = zk := by dsimp [z']; exact if_pos rfl
            rw [hzk1]; exact hzk_next hi1
          · have hzi : z' i = z i := by dsimp [z']; exact if_neg hik
            rw [hzi]; exact hz_next i (by omega) hi1
        · intro i hi hik
          by_cases hkeq : i = k
          · subst hkeq
            have hzk1 : z' i = zk := by dsimp [z']; exact if_pos rfl
            have hzm1 : z' (i - 1) = z (i - 1) := by dsimp [z']; exact if_neg (by omega : i - 1 ≠ i)
            rw [hzk1, hzm1]; exact hzk_prev
          · have him1 : i - 1 ≠ k := by omega
            have hzi : z' i = z i := by dsimp [z']; exact if_neg hkeq
            have hzm : z' (i - 1) = z (i - 1) := by dsimp [z']; exact if_neg him1
            rw [hzi, hzm]; exact hz_prev i hi (by omega)
        · intro hkL1
          have hk_eq : k = L - 1 := by omega
          subst hk_eq
          rw [hz'0]
          simp only [z', if_pos rfl]; exact hzk_wrap rfl
  obtain ⟨z, hz_Res, hz_inj, hz0_SL, hz_next, hz_prev, hz_wrap⟩ := hbind L (by omega) le_rfl
  refine ⟨z, hz_Res, hz_inj, ?_, hz_prev, hz_wrap rfl⟩
  intro i hi
  have h := hz_next i (by omega) hi
  dsimp [TargetNext, S_end] at h
  split_ifs at h ⊢ <;> exact h

end H2Proof

set_option maxHeartbeats 800000 in
theorem h2_proof : OMA.Erdos556R1.H2 := by
  intro d δ hd hδ0 hδ1
  let d' : ℝ := min d 1
  have hd' : 0 < d' := lt_min hd zero_lt_one
  have hd'1 : d' ≤ 1 := min_le_right d 1
  have hd'd : d' ≤ d := min_le_left d 1
  let η : ℝ := min (d' / 4) (min (δ / 16) (d' ^ 2 * δ / 256))
  have hη : 0 < η := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hη_d' : η ≤ d' / 4 := min_le_left _ _
  have hη_δ : η ≤ δ / 16 := (min_le_right _ _).trans (min_le_left _ _)
  have hη_sq : η ≤ d' ^ 2 * δ / 256 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨η, hη, fun t => ?_⟩
  let m₀ : ℕ := Nat.ceil (256 * (t : ℝ) / (d' ^ 2 * δ) + (t : ℝ) / (1 - δ) + 32 / δ + 32 / (d' * δ)) + 32
  refine ⟨m₀, fun N n m k G _ parts R M heven hn4 hk1 hm hm₀ hdisj hparts hR hM hMcard hMreach => ?_⟩
  classical
  have hm32 : 32 ≤ m := le_trans (by omega : 32 ≤ m₀) hm
  have hm_pos : 0 < m := by omega
  have hm_real_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
  have hparts_pos : ∀ i : Fin t, 0 < (parts i).card := fun i =>
    lt_of_lt_of_le hm_pos (hparts i).1
  have hS_card : 2 * k ≤ M.verts.toFinset.card := by
    rwa [← Set.ncard_eq_toFinset_card']
  obtain ⟨edges, hedges_len, hedges_adj, _, hedges_nodup⟩ :=
    H2Proof.extract_matching_pairs M hM k M.verts.toFinset
      (fun x hx => Set.mem_toFinset.mp hx)
      (fun x hx y hxy => Set.mem_toFinset.mpr (M.edge_vert hxy.symm))
      hS_card
  have hR_has_edge : ∃ u v : Fin t, R.Adj u v := by
    have hne : edges ≠ [] := by intro h; simp [h] at hedges_len; omega
    obtain ⟨⟨u, v⟩, rest, h⟩ := List.exists_cons_of_ne_nil hne
    exact ⟨u, v, M.adj_sub (hedges_adj (u, v) (by simp [h]))⟩
  have hd1 : d ≤ 1 := by
    obtain ⟨u, v, huv⟩ := hR_has_edge
    have h1 := (hR u v huv).2
    have h2 : (G.edgeDensity (parts u) (parts v) : ℝ) ≤ 1 := by
      exact_mod_cast SimpleGraph.edgeDensity_le_one G (parts u) (parts v)
    linarith
  have hd_gt : η < d := by linarith
  have hd_sub_ge : 3 / 4 * d' ≤ d - η := by linarith
  have hη_d1 : η ≤ d' / 256 := by
    have h1 : d' ^ 2 * δ / 256 ≤ d' * 1 / 256 := by nlinarith
    linarith
  have hη_δd : η ≤ d' * δ / 256 := by
    have h1 : d' ^ 2 * δ / 256 ≤ d' * δ / 256 := by nlinarith
    linarith
  have h1mδ : 0 < 1 - δ := sub_pos.mpr hδ1
  have hm_t_den : (t : ℝ) / (1 - δ) ≤ (m : ℝ) := by
    have h1 : (256 * (t : ℝ) / (d' ^ 2 * δ) + (t : ℝ) / (1 - δ) + 32 / δ + 32 / (d' * δ)) ≤ (m₀ : ℝ) := by
      calc _ ≤ (Nat.ceil (256 * (t : ℝ) / (d' ^ 2 * δ) + (t : ℝ) / (1 - δ) + 32 / δ + 32 / (d' * δ)) : ℝ) :=
            Nat.le_ceil _
        _ ≤ (m₀ : ℝ) := by simp only [m₀, Nat.cast_add, Nat.cast_ofNat]; linarith
    have h2 : (0 : ℝ) ≤ 256 * (t : ℝ) / (d' ^ 2 * δ) := by positivity
    have h3 : (0 : ℝ) ≤ 32 / δ := by positivity
    have h4 : (0 : ℝ) ≤ 32 / (d' * δ) := by positivity
    have h5 : (m₀ : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm
    linarith
  have hm_t_sq : 256 * (t : ℝ) / (d' ^ 2 * δ) ≤ (m : ℝ) := by
    have h1 : (256 * (t : ℝ) / (d' ^ 2 * δ) + (t : ℝ) / (1 - δ) + 32 / δ + 32 / (d' * δ)) ≤ (m₀ : ℝ) := by
      calc _ ≤ (Nat.ceil (256 * (t : ℝ) / (d' ^ 2 * δ) + (t : ℝ) / (1 - δ) + 32 / δ + 32 / (d' * δ)) : ℝ) :=
            Nat.le_ceil _
        _ ≤ (m₀ : ℝ) := by simp only [m₀, Nat.cast_add, Nat.cast_ofNat]; linarith
    have h2 : (0 : ℝ) ≤ (t : ℝ) / (1 - δ) := by positivity
    have h3 : (0 : ℝ) ≤ 32 / δ := by positivity
    have h4 : (0 : ℝ) ≤ 32 / (d' * δ) := by positivity
    have h5 : (m₀ : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm
    linarith
  have hm_δ : 32 / δ ≤ (m : ℝ) := by
    have h1 : (256 * (t : ℝ) / (d' ^ 2 * δ) + (t : ℝ) / (1 - δ) + 32 / δ + 32 / (d' * δ)) ≤ (m₀ : ℝ) := by
      calc _ ≤ (Nat.ceil (256 * (t : ℝ) / (d' ^ 2 * δ) + (t : ℝ) / (1 - δ) + 32 / δ + 32 / (d' * δ)) : ℝ) :=
            Nat.le_ceil _
        _ ≤ (m₀ : ℝ) := by simp only [m₀, Nat.cast_add, Nat.cast_ofNat]; linarith
    have h2 : (0 : ℝ) ≤ 256 * (t : ℝ) / (d' ^ 2 * δ) := by positivity
    have h3 : (0 : ℝ) ≤ (t : ℝ) / (1 - δ) := by positivity
    have h4 : (0 : ℝ) ≤ 32 / (d' * δ) := by positivity
    have h5 : (m₀ : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm
    linarith
  have hm_dδ : 32 / (d' * δ) ≤ (m : ℝ) := by
    have h1 : (256 * (t : ℝ) / (d' ^ 2 * δ) + (t : ℝ) / (1 - δ) + 32 / δ + 32 / (d' * δ)) ≤ (m₀ : ℝ) := by
      calc _ ≤ (Nat.ceil (256 * (t : ℝ) / (d' ^ 2 * δ) + (t : ℝ) / (1 - δ) + 32 / δ + 32 / (d' * δ)) : ℝ) :=
            Nat.le_ceil _
        _ ≤ (m₀ : ℝ) := by simp only [m₀, Nat.cast_add, Nat.cast_ofNat]; linarith
    have h2 : (0 : ℝ) ≤ 256 * (t : ℝ) / (d' ^ 2 * δ) := by positivity
    have h3 : (0 : ℝ) ≤ (t : ℝ) / (1 - δ) := by positivity
    have h4 : (0 : ℝ) ≤ 32 / δ := by positivity
    have h5 : (m₀ : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm
    linarith
  have hchoose_r : ∃ r : ℕ, 1 ≤ r ∧ r ≤ k ∧ (n : ℝ) ≤ (1 - δ) * (2 * (r : ℝ) * (m : ℝ)) ∧
      (2 ≤ r → (1 - δ) * (2 * ((r - 1 : ℕ) : ℝ) * (m : ℝ)) < (n : ℝ)) := by
    let S : Finset ℕ := (Finset.Icc (1 : ℕ) k).filter (fun j => (n : ℝ) ≤ (1 - δ) * (2 * (j : ℝ) * (m : ℝ)))
    have hkS : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk1, le_rfl⟩, hm₀⟩
    have hSne : S.Nonempty := ⟨k, hkS⟩
    let r := S.min' hSne
    have hrS : r ∈ S := Finset.min'_mem S hSne
    have hr_mem := Finset.mem_filter.mp hrS
    have hr_icc := Finset.mem_Icc.mp hr_mem.1
    refine ⟨r, hr_icc.1, hr_icc.2, hr_mem.2, fun hr2 => ?_⟩
    by_contra! hle
    have hr1_mem : r - 1 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hle⟩
    have := Finset.min'_le S (r - 1) hr1_mem
    omega
  obtain ⟨r, hr1, hrk, hnr, hnr_min⟩ := hchoose_r
  set chosen := edges.take r
  have hchosen_len : chosen.length = r := by rw [List.length_take, hedges_len]; exact min_eq_left hrk
  have hchosen_ne : chosen ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hchosen_adj : ∀ p ∈ chosen, R.Adj p.1 p.2 := fun p hp =>
    M.adj_sub (hedges_adj p (List.mem_of_mem_take hp))
  have hchosen_nodup : (chosen.flatMap (fun p => [p.1, p.2])).Nodup := by
    have h1 : chosen.flatMap (fun p => [p.1, p.2]) <+: edges.flatMap (fun p => [p.1, p.2]) :=
      (List.take_prefix r edges).flatMap (fun p => [p.1, p.2])
    exact hedges_nodup.sublist h1.sublist
  have hchosen_reach : ∀ p ∈ chosen, ∀ q ∈ chosen, R.Reachable p.1 q.1 := fun p hp q hq =>
    hMreach p.1 (M.edge_vert (hedges_adj p (List.mem_of_mem_take hp)))
      q.1 (M.edge_vert (hedges_adj q (List.mem_of_mem_take hq)))
  obtain ⟨W, hWne, hWadj, hWchain, hWwrap, hWlastf, hWeven, hW2, hW2t, hr_le_W2, hW1_eq, hWcnt, hWnodup⟩ :=
    H2Proof.build_closed_walk chosen hchosen_ne hchosen_adj hchosen_nodup hchosen_reach
  rw [hchosen_len] at hr_le_W2 hW1_eq hWcnt
  set L := W.length
  have hL_le_n : L ≤ n := by
    rcases eq_or_lt_of_le hr1 with rfl | hr2
    · have : L = 2 := hW1_eq rfl
      omega
    · have hgt := hnr_min hr2
      have h2m : 2 * (1 - δ) * (m : ℝ) < (n : ℝ) := by
        have h1 : (1 : ℝ) ≤ ((r - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ r - 1)
        nlinarith
      have ht_le : (t : ℝ) ≤ (1 - δ) * (m : ℝ) := by linarith [(div_le_iff₀ h1mδ).mp hm_t_den]
      have hLt : (L : ℝ) ≤ 2 * (t : ℝ) := by exact_mod_cast hW2t
      have hLn_real : (L : ℝ) < (n : ℝ) := by linarith
      exact_mod_cast hLn_real.le
  obtain ⟨n_half, hn_half⟩ := heven
  obtain ⟨L_half, hL_half⟩ := hWeven
  set D := n_half - L_half
  have hn_eq : n = L + 2 * D := by omega
  set B := Nat.floor ((1 - δ) * (m : ℝ))
  have hD_le : D ≤ r * B := by
    have hB_gt : (1 - δ) * (m : ℝ) < (B : ℝ) + 1 := Nat.lt_floor_add_one _
    have h1 : (D : ℝ) + (r : ℝ) ≤ (n_half : ℝ) := by
      have : L_half ≥ r := by omega
      exact_mod_cast (by omega : D + r ≤ n_half)
    have h2 : (n_half : ℝ) ≤ (1 - δ) * (r : ℝ) * (m : ℝ) := by
      have h2n : (n : ℝ) = 2 * (n_half : ℝ) := by exact_mod_cast (by omega : n = 2 * n_half)
      linarith
    have h3 : (1 - δ) * (r : ℝ) * (m : ℝ) < (r : ℝ) * ((B : ℝ) + 1) := by
      have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
      nlinarith
    have h4 : (D : ℝ) < (r : ℝ) * (B : ℝ) := by linarith
    have h4n : D < r * B := by exact_mod_cast h4
    exact h4n.le
  set lens := H2Proof.assignList B W D
  obtain ⟨hlens_len, hlens_sum, hlens_leB, hlens_zero⟩ := H2Proof.assignList_props B W D (hWcnt ▸ hD_le)
  have hlens_L : lens.length = L := hlens_len
  let len : ℕ → ℕ := fun i => if h : i < L then lens[i]'(hlens_len ▸ h) else 0
  have hlen_L : len (L - 1) = 0 := by
    simp only [len, dif_pos (by omega : L - 1 < L)]
    refine hlens_zero (L - 1) (by omega) ?_
    have h1 := hWlastf hWne
    rwa [List.getLast_eq_getElem hWne] at h1
  have hL2_len0 : L = 2 → 0 < len 0 := by
    intro hL2
    have hlen1_0 : len 1 = 0 := by simpa [hL2] using hlen_L
    have hL_half1 : L_half = 1 := by omega
    have hD_pos : 0 < D := by omega
    have hsum0 : len 0 + len 1 = D := by
      have hsum_rng := H2Proof.sum_range_eq_list_sum lens len (fun i hi => by
        have hiL : i < L := hlens_L ▸ hi
        simp [len, hiL])
      rw [hlens_L, hL2, hlens_sum] at hsum_rng
      simpa [Finset.sum_range_succ] using hsum_rng
    omega
  set q := Nat.ceil (δ / 8 * (m : ℝ))
  have hq_ge : δ / 8 * (m : ℝ) ≤ (q : ℝ) := Nat.le_ceil _
  have hq_lt : (q : ℝ) < δ / 8 * (m : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
  have h2q_le : 2 * q ≤ m := by
    have h1 : (2 * q : ℝ) < δ / 4 * (m : ℝ) + 2 := by linarith only [hq_lt]
    have h2 : δ / 4 * (m : ℝ) + 2 ≤ 1 / 4 * (m : ℝ) + 2 := by nlinarith only [hδ1, hm_real_pos]
    have h3 : (1 / 4 * (m : ℝ) + 2 : ℝ) ≤ (m : ℝ) := by
      have : (32 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm32
      linarith only [this]
    exact_mod_cast (h1.trans_le (h2.trans h3)).le
  have hsplit_all : ∀ i : Fin t, ∃ Res Cap Body : Finset (Fin N),
      Res ⊆ parts i ∧ Cap ⊆ parts i ∧ Body ⊆ parts i ∧
      Disjoint Res Cap ∧ Disjoint Res Body ∧ Disjoint Cap Body ∧
      Res.card = q ∧ Cap.card = q ∧ Body.card = (parts i).card - 2 * q :=
    fun i => H2Proof.split_cluster (parts i) q (h2q_le.trans (hparts i).1)
  choose Res Cap Body hRes_sub hCap_sub hBody_sub hRC hRB hCB hRes_card hCap_card hBody_card using hsplit_all
  set c := Nat.ceil ((m + 1 : ℝ) * η)
  have hc_ge : (m + 1 : ℝ) * η ≤ (c : ℝ) := Nat.le_ceil _
  have hc_lt : (c : ℝ) < (m + 1 : ℝ) * η + 1 := Nat.ceil_lt_add_one (by positivity)
  have hm1_2m : (m + 1 : ℝ) ≤ 2 * (m : ℝ) := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_pos
    linarith only [this]
  have hparts_le : ∀ i : Fin t, ((parts i).card : ℝ) ≤ (m : ℝ) + 1 := fun i => by
    exact_mod_cast (hparts i).2
  have hc_parts : ∀ i : Fin t, ((parts i).card : ℝ) * η ≤ (c : ℝ) := fun i =>
    (mul_le_mul_of_nonneg_right (hparts_le i) hη.le).trans hc_ge
  have h_m1η_q : (m + 1 : ℝ) * η ≤ (q : ℝ) := by
    have h1 : (m + 1 : ℝ) * η ≤ 2 * (m : ℝ) * (δ / 16) := mul_le_mul hm1_2m hη_δ hη.le (by positivity)
    linarith only [h1, hq_ge]
  have hRes_sz : ∀ i j : Fin t, ((parts j).card : ℝ) * η ≤ ((Res i).card : ℝ) := fun i j => by
    rw [hRes_card i]
    exact (mul_le_mul_of_nonneg_right (hparts_le j) hη.le).trans h_m1η_q
  have hCap_sz : ∀ i j : Fin t, ((parts j).card : ℝ) * η ≤ ((Cap i).card : ℝ) := fun i j => by
    rw [hCap_card i]
    exact (mul_le_mul_of_nonneg_right (hparts_le j) hη.le).trans h_m1η_q
  have hBody_ge : ∀ i : Fin t, (m : ℝ) / 2 ≤ ((Body i).card : ℝ) := fun i => by
    have hb1 : m - 2 * q ≤ (Body i).card := by rw [hBody_card i]; exact Nat.sub_le_sub_right (hparts i).1 _
    have hb2 : (m : ℝ) - 2 * (q : ℝ) ≤ ((Body i).card : ℝ) := by
      have : ((m - 2 * q : ℕ) : ℝ) = (m : ℝ) - 2 * (q : ℝ) := by
        rw [Nat.cast_sub h2q_le]; push_cast; rfl
      rw [← this]; exact_mod_cast hb1
    have h2q : 2 * (q : ℝ) ≤ δ / 4 * (m : ℝ) + 2 := by linarith only [hq_lt]
    have h32 : (32 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm32
    nlinarith only [hb2, h2q, h32, hδ1, hδ0]
  have hBody_sz : ∀ i j : Fin t, ((parts j).card : ℝ) * η ≤ ((Body i).card : ℝ) := fun i j => by
    have h1 : ((parts j).card : ℝ) * η ≤ 2 * (m : ℝ) * (δ / 16) :=
      mul_le_mul ((hparts_le j).trans hm1_2m) hη_δ hη.le (by positivity)
    have h2 : 2 * (m : ℝ) * (δ / 16) ≤ (m : ℝ) / 2 := by nlinarith only [hδ1, hm_real_pos]
    exact h1.trans (h2.trans (hBody_ge i))
  have hBody_pool : ∀ i j₁ j₂ : Fin t,
      3 * ((max (parts j₁).card (parts j₂).card : ℝ) * η + 1) ≤ (d - η) * ((Body i).card : ℝ) := by
    intro i j₁ j₂
    have hmax : (max (parts j₁).card (parts j₂).card : ℝ) ≤ (m : ℝ) + 1 := by
      exact_mod_cast max_le (hparts j₁).2 (hparts j₂).2
    have h1 : 3 * ((max (parts j₁).card (parts j₂).card : ℝ) * η + 1) ≤ 3 * (2 * (m : ℝ) * (d' / 256) + 1) := by
      have : (max (parts j₁).card (parts j₂).card : ℝ) * η ≤ 2 * (m : ℝ) * (d' / 256) :=
        mul_le_mul (hmax.trans hm1_2m) hη_d1 hη.le (by positivity)
      linarith only [this]
    have h2 : (32 : ℝ) ≤ d' * (m : ℝ) := by
      have hdm := (div_le_iff₀ (by positivity : 0 < d' * δ)).mp hm_dδ
      have hle : d' * δ * (m : ℝ) ≤ d' * (m : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hd'.le hδ1.le) hm_real_pos.le
      linarith only [hdm, hle, show (m : ℝ) * (d' * δ) = d' * δ * (m : ℝ) by ring]
    have h3 : 3 * (2 * (m : ℝ) * (d' / 256) + 1) ≤ 3 / 8 * (d' * (m : ℝ)) := by
      have heq : 3 * (2 * (m : ℝ) * (d' / 256) + 1) = 3 / 128 * (d' * (m : ℝ)) + 3 := by ring
      rw [heq]
      linarith only [h2]
    have h4 : 3 / 8 * (d' * (m : ℝ)) ≤ (d - η) * ((Body i).card : ℝ) := by
      have hb := hBody_ge i
      nlinarith only [hb, hd_sub_ge, hd', hm_real_pos]
    exact h1.trans (h3.trans h4)
  have hc_Body : ∀ i : Fin t, (c : ℝ) ≤ (d - η) * ((Body i).card : ℝ) := fun i => by
    have h1 : (c : ℝ) ≤ 3 * ((max (parts i).card (parts i).card : ℝ) * η + 1) := by
      have hm_le : (m : ℝ) ≤ (parts i).card := by exact_mod_cast (hparts i).1
      have h2m : (m + 1 : ℝ) * η ≤ 2 * ((parts i).card : ℝ) * η := by
        nlinarith only [hm1_2m, hm_le, hη]
      simp only [max_self]
      linarith only [hc_lt, h2m]
    exact h1.trans (hBody_pool i i i)
  have hd'2 : d' ^ 2 ≤ 1 := by rw [sq]; exact mul_le_one₀ hd'1 hd'.le hd'1
  have hSend_big : ∀ i j : Fin t, ((parts j).card : ℝ) * η ≤ (d - η) * ((Cap i).card : ℝ) := by
    intro i j
    rw [hCap_card i]
    have h1 : ((parts j).card : ℝ) * η ≤ 2 * (m : ℝ) * (d' * δ / 256) :=
      mul_le_mul ((hparts_le j).trans hm1_2m) hη_δd hη.le (by positivity)
    have h2 : 2 * (m : ℝ) * (d' * δ / 256) ≤ (3 / 4 * d') * (δ / 8 * (m : ℝ)) := by
      have hdm0 : 0 ≤ d' * δ * (m : ℝ) := by positivity
      linarith only [hdm0, show 2 * (m : ℝ) * (d' * δ / 256) = (1 / 128) * (d' * δ * (m : ℝ)) by ring,
        show (3 / 4 * d') * (δ / 8 * (m : ℝ)) = (3 / 32) * (d' * δ * (m : ℝ)) by ring]
    have h3 : (3 / 4 * d') * (δ / 8 * (m : ℝ)) ≤ (d - η) * (q : ℝ) :=
      mul_le_mul hd_sub_ge hq_ge (by positivity) (by linarith only [hd_sub_ge, hd'])
    exact h1.trans (h2.trans h3)
  have hPool_Res : ∀ i : Fin t, (L : ℝ) + 2 * ((parts i).card : ℝ) * η ≤ ((Res i).card : ℝ) := by
    intro i
    rw [hRes_card i]
    have hL2t : (L : ℝ) ≤ 2 * (t : ℝ) := by exact_mod_cast hW2t
    have ht_bnd : 2 * (t : ℝ) ≤ d' ^ 2 * δ * (m : ℝ) / 128 := by
      have h1 := (div_le_iff₀ (by positivity : 0 < d' ^ 2 * δ)).mp hm_t_sq
      linarith only [h1, show (m : ℝ) * (d' ^ 2 * δ) = d' ^ 2 * δ * (m : ℝ) by ring]
    have h2η' : 2 * ((parts i).card : ℝ) * η ≤ d' ^ 2 * δ * (m : ℝ) / 64 := by
      have hle := (hparts_le i).trans hm1_2m
      have h1 := mul_le_mul hle hη_sq hη.le (by positivity)
      linarith only [h1, show 2 * (m : ℝ) * (d' ^ 2 * δ / 256) = d' ^ 2 * δ * (m : ℝ) / 128 by ring]
    have h3' : d' ^ 2 * δ * (m : ℝ) / 128 + d' ^ 2 * δ * (m : ℝ) / 64 ≤ δ / 8 * (m : ℝ) := by
      have hδm0 : 0 ≤ δ * (m : ℝ) := by positivity
      have hsq : d' ^ 2 * (δ * (m : ℝ)) ≤ 1 * (δ * (m : ℝ)) := mul_le_mul_of_nonneg_right hd'2 hδm0
      linarith only [hsq, hδm0, show d' ^ 2 * δ * (m : ℝ) = d' ^ 2 * (δ * (m : ℝ)) by ring]
    linarith only [hL2t, ht_bnd, h2η', h3', hq_ge]
  have hPool_Send : ∀ i j : Fin t, ((parts j).card : ℝ) * η ≤ (d - η) * ((Res i).card : ℝ) ∧
      (L : ℝ) + 2 * ((parts j).card : ℝ) * η ≤ (d - η) * ((Res i).card : ℝ) := by
    intro i j
    rw [hRes_card i]
    have hL2t : (L : ℝ) ≤ 2 * (t : ℝ) := by exact_mod_cast hW2t
    have ht_bnd : 2 * (t : ℝ) ≤ d' ^ 2 * δ * (m : ℝ) / 128 := by
      have h1 := (div_le_iff₀ (by positivity : 0 < d' ^ 2 * δ)).mp hm_t_sq
      linarith only [h1, show (m : ℝ) * (d' ^ 2 * δ) = d' ^ 2 * δ * (m : ℝ) by ring]
    have h2η : 2 * ((parts j).card : ℝ) * η ≤ d' ^ 2 * δ * (m : ℝ) / 64 := by
      have hle := (hparts_le j).trans hm1_2m
      have h1 := mul_le_mul hle hη_sq hη.le (by positivity)
      linarith only [h1, show 2 * (m : ℝ) * (d' ^ 2 * δ / 256) = d' ^ 2 * δ * (m : ℝ) / 128 by ring]
    have h1η : ((parts j).card : ℝ) * η ≤ d' ^ 2 * δ * (m : ℝ) / 128 := by
      have hle := (hparts_le j).trans hm1_2m
      have h1 := mul_le_mul hle hη_sq hη.le (by positivity)
      linarith only [h1, show 2 * (m : ℝ) * (d' ^ 2 * δ / 256) = d' ^ 2 * δ * (m : ℝ) / 128 by ring]
    have hRHS : (3 / 4 * d') * (δ / 8 * (m : ℝ)) ≤ (d - η) * (q : ℝ) :=
      mul_le_mul hd_sub_ge hq_ge (by positivity) (by linarith only [hd_sub_ge, hd'])
    have hdm_bnd : d' ^ 2 * δ * (m : ℝ) ≤ d' * δ * (m : ℝ) := by
      have hδm0 : 0 ≤ δ * (m : ℝ) := by positivity
      have hsq : d' ^ 2 ≤ d' := by rw [sq]; exact mul_le_of_le_one_left hd'.le hd'1
      have h1 := mul_le_mul_of_nonneg_right hsq hδm0
      linarith only [h1, show d' ^ 2 * (δ * (m : ℝ)) = d' ^ 2 * δ * (m : ℝ) by ring,
        show d' * (δ * (m : ℝ)) = d' * δ * (m : ℝ) by ring]
    have hdm0 : 0 ≤ d' * δ * (m : ℝ) := by positivity
    have hA : d' ^ 2 * δ * (m : ℝ) / 128 + d' ^ 2 * δ * (m : ℝ) / 64 ≤
        (3 / 4 * d') * (δ / 8 * (m : ℝ)) := by
      linarith only [hdm_bnd, hdm0, show (3 / 4 * d') * (δ / 8 * (m : ℝ)) = 3 / 32 * (d' * δ * (m : ℝ)) by ring]
    have hB : d' ^ 2 * δ * (m : ℝ) / 128 ≤ (3 / 4 * d') * (δ / 8 * (m : ℝ)) := by
      linarith only [hdm_bnd, hdm0, show (3 / 4 * d') * (δ / 8 * (m : ℝ)) = 3 / 32 * (d' * δ * (m : ℝ)) by ring]
    exact ⟨h1η.trans (hB.trans hRHS), by linarith only [hL2t, ht_bnd, h2η, hA, hRHS]⟩
  have hPool_Send2 : ∀ i j : Fin t,
      (L : ℝ) + 2 * ((parts j).card : ℝ) * η ≤ (d - η) * ((d - η) * ((Res i).card : ℝ)) := by
    intro i j
    rw [hRes_card i]
    have hL2t : (L : ℝ) ≤ 2 * (t : ℝ) := by exact_mod_cast hW2t
    have ht_bnd : 2 * (t : ℝ) ≤ d' ^ 2 * δ * (m : ℝ) / 128 := by
      have h1 := (div_le_iff₀ (by positivity : 0 < d' ^ 2 * δ)).mp hm_t_sq
      linarith only [h1, show (m : ℝ) * (d' ^ 2 * δ) = d' ^ 2 * δ * (m : ℝ) by ring]
    have h2η : 2 * ((parts j).card : ℝ) * η ≤ d' ^ 2 * δ * (m : ℝ) / 64 := by
      have hle := (hparts_le j).trans hm1_2m
      have h1 := mul_le_mul hle hη_sq hη.le (by positivity)
      linarith only [h1, show 2 * (m : ℝ) * (d' ^ 2 * δ / 256) = d' ^ 2 * δ * (m : ℝ) / 128 by ring]
    have hRHS : (3 / 4 * d') * ((3 / 4 * d') * (δ / 8 * (m : ℝ))) ≤ (d - η) * ((d - η) * (q : ℝ)) := by
      have hq' : (3 / 4 * d') * (δ / 8 * (m : ℝ)) ≤ (d - η) * (q : ℝ) :=
        mul_le_mul hd_sub_ge hq_ge (by positivity) (by linarith only [hd_sub_ge, hd'])
      exact mul_le_mul hd_sub_ge hq' (by positivity) (by linarith only [hd_sub_ge, hd'])
    have hA : d' ^ 2 * δ * (m : ℝ) / 128 + d' ^ 2 * δ * (m : ℝ) / 64 ≤
        (3 / 4 * d') * ((3 / 4 * d') * (δ / 8 * (m : ℝ))) := by
      have hpos : 0 ≤ d' ^ 2 * δ * (m : ℝ) := by positivity
      linarith only [hpos, show (3 / 4 * d') * ((3 / 4 * d') * (δ / 8 * (m : ℝ))) = 9 / 128 * (d' ^ 2 * δ * (m : ℝ)) by ring]
    linarith only [hL2t, ht_bnd, h2η, hA, hRHS]
  let w : ℕ → Fin t := fun i => if h : i < L then W[i].1 else (W.head hWne).1
  let w' : ℕ → Fin t := fun i => if h : i < L then W[i].2.1 else (W.head hWne).1
  have hw_adj : ∀ i (hi : i < L), R.Adj (w i) (w' i) := fun i hi => by
    simp only [w, w', dif_pos hi]
    exact hWadj W[i] (List.getElem_mem hi)
  have hw'_eq : ∀ i (hi : i + 1 < L), w' i = w (i + 1) := fun i hi => by
    simp only [w', w, dif_pos (by omega : i < L), dif_pos hi]
    exact List.isChain_iff_getElem.mp hWchain i hi
  have hw_wrap : w' (L - 1) = w 0 := by
    simp only [w', w, dif_pos (by omega : L - 1 < L), dif_pos (by omega : 0 < L)]
    have h1 := hWwrap hWne
    rwa [List.getLast_eq_getElem hWne, List.head_eq_getElem hWne] at h1
  obtain ⟨z, hz_Res, hz_inj, hz_next, hz_prev, hz_wrap⟩ :=
    H2Proof.embed_tour_vertices G hη parts R hparts_pos hR Res Cap Body
      hRes_sub hCap_sub hBody_sub hRes_sz hCap_sz hBody_sz
      L w w' hw_adj hw'_eq hw_wrap len hlen_L hW2 hL2_len0 hPool_Res hPool_Send hPool_Send2
  have hℓ_bound : ∀ i (hi : i < L), len i ≤ min ((Body (w' i)).card - c) (Body (w i)).card - 2 * c := by
    intro i hi
    have hleB : len i ≤ B := by
      simp only [len, dif_pos hi]
      exact hlens_leB i hi
    have hB_real : (B : ℝ) ≤ (1 - δ) * (m : ℝ) := Nat.floor_le (by positivity)
    have hc_ub : (c : ℝ) < 2 * (m : ℝ) * (δ / 16) + 1 := by
      have : (m + 1 : ℝ) * η ≤ 2 * (m : ℝ) * (δ / 16) := mul_le_mul hm1_2m hη_δ hη.le (by positivity)
      linarith only [this, hc_lt]
    have hq_ub : (q : ℝ) < δ / 8 * (m : ℝ) + 1 := hq_lt
    have hBU : (m : ℝ) - 2 * (q : ℝ) ≤ ((Body (w i)).card : ℝ) := by
      have hb1 : m - 2 * q ≤ (Body (w i)).card := by
        rw [hBody_card (w i)]; exact Nat.sub_le_sub_right (hparts (w i)).1 _
      have hb2 : ((m - 2 * q : ℕ) : ℝ) = (m : ℝ) - 2 * (q : ℝ) := by
        rw [Nat.cast_sub h2q_le]; push_cast; rfl
      rw [← hb2]; exact_mod_cast hb1
    have hBV : (m : ℝ) - 2 * (q : ℝ) ≤ ((Body (w' i)).card : ℝ) := by
      have hb1 : m - 2 * q ≤ (Body (w' i)).card := by
        rw [hBody_card (w' i)]; exact Nat.sub_le_sub_right (hparts (w' i)).1 _
      have hb2 : ((m - 2 * q : ℕ) : ℝ) = (m : ℝ) - 2 * (q : ℝ) := by
        rw [Nat.cast_sub h2q_le]; push_cast; rfl
      rw [← hb2]; exact_mod_cast hb1
    have h32 : (32 : ℝ) ≤ δ * (m : ℝ) := by
      have := (div_le_iff₀ hδ0).mp hm_δ
      linarith only [this]
    have h1 : (len i : ℝ) ≤ (1 - δ) * (m : ℝ) := (Nat.cast_le.mpr hleB).trans hB_real
    have h2 : (1 - δ) * (m : ℝ) ≤ ((Body (w' i)).card : ℝ) - 3 * (c : ℝ) := by
      nlinarith only [hBV, hc_ub, hq_ub, h32, hδ0, hδ1, hm_real_pos]
    have h3 : (1 - δ) * (m : ℝ) ≤ ((Body (w i)).card : ℝ) - 3 * (c : ℝ) := by
      nlinarith only [hBU, hc_ub, hq_ub, h32, hδ0, hδ1, hm_real_pos]
    have hn1 : len i ≤ (Body (w' i)).card - 3 * c := by
      have : (len i : ℝ) + 3 * (c : ℝ) ≤ ((Body (w' i)).card : ℝ) := by linarith only [h1, h2]
      have : len i + 3 * c ≤ (Body (w' i)).card := by exact_mod_cast this
      omega
    have hn2 : len i ≤ (Body (w i)).card - 3 * c := by
      have : (len i : ℝ) + 3 * (c : ℝ) ≤ ((Body (w i)).card : ℝ) := by linarith only [h1, h3]
      have : len i + 3 * c ≤ (Body (w i)).card := by exact_mod_cast this
      omega
    omega
  have hseg_exists : ∀ i : ℕ, i < L →
      ∃ seg : List (Fin N),
        seg ≠ [] ∧
        seg.length = 2 * len i + 1 ∧
        (∀ h : seg ≠ [], seg.head h = z i) ∧
        (∀ h : seg ≠ [], G.Adj (seg.getLast h) (z ((i + 1) % L))) ∧
        seg.Nodup ∧
        seg.IsChain G.Adj ∧
        (0 < len i → seg.toFinset ⊆ insert (z i) (Body (w i) ∪ Body (w' i) ∪ Cap (w i))) ∧
        (len i = 0 → seg = [z i]) := by
    intro i hi
    by_cases hli : 0 < len i
    · have hi1 : i + 1 < L := by
        by_contra! hge
        have : i = L - 1 := by omega
        subst this
        omega
      have hmod : (i + 1) % L = i + 1 := Nat.mod_eq_of_lt hi1
      have hzu_deg := hz_next i hi1
      simp only [hli, ↓reduceIte] at hzu_deg
      have hzv_deg := hz_prev (i + 1) (by omega) hi1
      simp only [show i + 1 - 1 = i by omega, hli, ↓reduceIte] at hzv_deg
      have hR_uv := hR (w i) (w' i) (hw_adj i hi)
      obtain ⟨seg, hne, hlen_s, hhead_s, hlast_s, hnodup_s, hchain_s, hsub_s⟩ :=
        H2Proof.bridge_segment G hη hd_gt (hRes_sub (w i)) (hCap_sub (w i)) (hBody_sub (w i)) (hBody_sub (w' i))
          (hdisj (R.ne_of_adj (hw_adj i hi))) (hRC (w i)) (hRB (w i)) (hCB (w i))
          hR_uv.1 hR_uv.2 (hparts_pos (w i)) (hparts_pos (w' i)) c
          (hc_parts (w i)) (hc_parts (w' i))
          (hc_Body (w i)) (hCap_sz (w i) (w i)) (hBody_sz (w i) (w i)) (hBody_sz (w' i) (w' i))
          (hz_Res i hi) hzu_deg hzv_deg (hSend_big (w i) (w i)) (hBody_pool (w' i) (w i) (w' i))
          (len i) hli (hℓ_bound i hi)
      refine ⟨seg, hne, hlen_s, hhead_s, ?_, hnodup_s, hchain_s, fun _ => hsub_s, fun h => by omega⟩
      rw [hmod]
      exact hlast_s
    · have hli0 : len i = 0 := by omega
      refine ⟨[z i], by simp, by simp [hli0], fun _ => rfl, ?_, List.nodup_singleton _, List.isChain_singleton _, fun h => by omega, fun _ => rfl⟩
      intro _
      simp only [List.getLast_singleton]
      by_cases hi1 : i + 1 < L
      · have hmod : (i + 1) % L = i + 1 := Nat.mod_eq_of_lt hi1
        rw [hmod]
        have hp := hz_prev (i + 1) (by omega) hi1
        simpa [show i + 1 - 1 = i by omega, hli0] using hp
      · have hieq : i = L - 1 := by omega
        subst hieq
        have hmod : (L - 1 + 1) % L = 0 := by rw [show L - 1 + 1 = L by omega, Nat.mod_self]
        rw [hmod]
        exact hz_wrap
  let segs : ℕ → List (Fin N) := fun i =>
    if h : i < L then (hseg_exists i h).choose else []
  have hsegs_spec : ∀ i (hi : i < L),
      segs i ≠ [] ∧
      (segs i).length = 2 * len i + 1 ∧
      (∀ h : segs i ≠ [], (segs i).head h = z i) ∧
      (∀ h : segs i ≠ [], G.Adj ((segs i).getLast h) (z ((i + 1) % L))) ∧
      (segs i).Nodup ∧
      (segs i).IsChain G.Adj ∧
      (0 < len i → (segs i).toFinset ⊆ insert (z i) (Body (w i) ∪ Body (w' i) ∪ Cap (w i))) ∧
      (len i = 0 → segs i = [z i]) := by
    intro i hi
    simp only [segs, dif_pos hi]
    exact (hseg_exists i hi).choose_spec
  have hlen_true : ∀ i (hi : i < L), 0 < len i → W[i].2.2 = true := by
    intro i hi hpos
    by_contra hfalse
    have hf : W[i].2.2 = false := Bool.eq_false_iff.mpr hfalse
    have hz := hlens_zero i hi hf
    simp only [len, dif_pos hi] at hpos
    rw [hz] at hpos
    omega
  have hW_disj_true : ∀ i₁ < L, ∀ i₂ < L, i₁ ≠ i₂ → 0 < len i₁ → 0 < len i₂ →
      Disjoint ({w i₁, w' i₁} : Finset (Fin t)) ({w i₂, w' i₂} : Finset (Fin t)) := by
    intro i₁ hi₁ i₂ hi₂ hne hpos₁ hpos₂
    have ht1 := hlen_true i₁ hi₁ hpos₁
    have ht2 := hlen_true i₂ hi₂ hpos₂
    simp only [w, w', dif_pos hi₁, dif_pos hi₂]
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact H2Proof.true_indices_disjoint W hWnodup i₁ i₂ hi₁ hi₂ hlt ht1 ht2
    · exact (H2Proof.true_indices_disjoint W hWnodup i₂ i₁ hi₂ hi₁ hlt ht2 ht1).symm
  have hz_not_BBC : ∀ i₁ < L, ∀ i₂ < L,
      z i₁ ∉ Body (w i₂) ∪ Body (w' i₂) ∪ Cap (w i₂) := by
    intro i₁ hi₁ i₂ hi₂ hmem
    have hz1 : z i₁ ∈ Res (w i₁) := hz_Res i₁ hi₁
    have hzR := hRes_sub (w i₁) hz1
    simp only [Finset.mem_union] at hmem
    rcases hmem with (hB1 | hB2) | hC
    · by_cases heq : w i₁ = w i₂
      · rw [heq] at hz1
        exact Finset.disjoint_left.mp (hRB (w i₂)) hz1 hB1
      · exact Finset.disjoint_left.mp (hdisj heq) hzR (hBody_sub _ hB1)
    · by_cases heq : w i₁ = w' i₂
      · rw [heq] at hz1
        exact Finset.disjoint_left.mp (hRB (w' i₂)) hz1 hB2
      · exact Finset.disjoint_left.mp (hdisj heq) hzR (hBody_sub _ hB2)
    · by_cases heq : w i₁ = w i₂
      · rw [heq] at hz1
        exact Finset.disjoint_left.mp (hRC (w i₂)) hz1 hC
      · exact Finset.disjoint_left.mp (hdisj heq) hzR (hCap_sub _ hC)
  have hdisj_segs : ∀ i₁ < L, ∀ i₂ < L, i₁ ≠ i₂ →
      Disjoint (segs i₁).toFinset (segs i₂).toFinset := by
    intro i₁ hi₁ i₂ hi₂ hne
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    by_cases h1 : 0 < len i₁ <;> by_cases h2 : 0 < len i₂
    · have hs1 := (hsegs_spec i₁ hi₁).2.2.2.2.2.2.1 h1 hx₁
      have hs2 := (hsegs_spec i₂ hi₂).2.2.2.2.2.2.1 h2 hx₂
      rcases Finset.mem_insert.mp hs1 with rfl | hx1' <;>
        rcases Finset.mem_insert.mp hs2 with hzx | hx2'
      · exact hz_inj i₁ hi₁ i₂ hi₂ hne hzx
      · exact hz_not_BBC i₁ hi₁ i₂ hi₂ hx2'
      · exact hz_not_BBC i₂ hi₂ i₁ hi₁ (hzx ▸ hx1')
      · have hd := hW_disj_true i₁ hi₁ i₂ hi₂ hne h1 h2
        have hx_in₁ : ∃ u ∈ ({w i₁, w' i₁} : Finset (Fin t)), x ∈ parts u := by
          simp only [Finset.mem_union] at hx1'
          rcases hx1' with (h | h) | h
          · exact ⟨w i₁, by simp, hBody_sub _ h⟩
          · exact ⟨w' i₁, by simp, hBody_sub _ h⟩
          · exact ⟨w i₁, by simp, hCap_sub _ h⟩
        have hx_in₂ : ∃ v ∈ ({w i₂, w' i₂} : Finset (Fin t)), x ∈ parts v := by
          simp only [Finset.mem_union] at hx2'
          rcases hx2' with (h | h) | h
          · exact ⟨w i₂, by simp, hBody_sub _ h⟩
          · exact ⟨w' i₂, by simp, hBody_sub _ h⟩
          · exact ⟨w i₂, by simp, hCap_sub _ h⟩
        obtain ⟨u, hu, hxu⟩ := hx_in₁
        obtain ⟨v, hv, hxv⟩ := hx_in₂
        have huv : u ≠ v := fun h => Finset.disjoint_left.mp hd hu (h ▸ hv)
        exact Finset.disjoint_left.mp (hdisj huv) hxu hxv
    · have hl2 : len i₂ = 0 := by omega
      have hs1 := (hsegs_spec i₁ hi₁).2.2.2.2.2.2.1 h1 hx₁
      have hs2 := (hsegs_spec i₂ hi₂).2.2.2.2.2.2.2 hl2
      rw [hs2] at hx₂
      simp only [List.toFinset_cons, List.toFinset_nil, Finset.mem_insert,
        Finset.notMem_empty, or_false] at hx₂
      subst hx₂
      rcases Finset.mem_insert.mp hs1 with hzx | hx1'
      · exact hz_inj i₂ hi₂ i₁ hi₁ hne.symm hzx
      · exact hz_not_BBC i₂ hi₂ i₁ hi₁ hx1'
    · have hl1 : len i₁ = 0 := by omega
      have hs1 := (hsegs_spec i₁ hi₁).2.2.2.2.2.2.2 hl1
      have hs2 := (hsegs_spec i₂ hi₂).2.2.2.2.2.2.1 h2 hx₂
      rw [hs1] at hx₁
      simp only [List.toFinset_cons, List.toFinset_nil, Finset.mem_insert,
        Finset.notMem_empty, or_false] at hx₁
      subst hx₁
      rcases Finset.mem_insert.mp hs2 with hzx | hx2'
      · exact hz_inj i₁ hi₁ i₂ hi₂ hne hzx
      · exact hz_not_BBC i₁ hi₁ i₂ hi₂ hx2'
    · have hl1 : len i₁ = 0 := by omega
      have hl2 : len i₂ = 0 := by omega
      rw [List.mem_toFinset, (hsegs_spec i₁ hi₁).2.2.2.2.2.2.2 hl1, List.mem_singleton] at hx₁
      rw [List.mem_toFinset, (hsegs_spec i₂ hi₂).2.2.2.2.2.2.2 hl2, List.mem_singleton] at hx₂
      exact hz_inj i₁ hi₁ i₂ hi₂ hne (hx₁.symm.trans hx₂)
  have hsum_segs : ∑ i ∈ Finset.range L, (segs i).length = n := by
    have h1 : ∑ i ∈ Finset.range L, (segs i).length = ∑ i ∈ Finset.range L, (2 * len i + 1) :=
      Finset.sum_congr rfl fun i hi => (hsegs_spec i (Finset.mem_range.mp hi)).2.1
    rw [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one,
      ← Finset.mul_sum]
    have h2 : ∑ i ∈ Finset.range L, len i = D := by
      have h3 : ∑ i ∈ Finset.range L, len i = lens.sum := by
        rw [← hlens_L]
        exact H2Proof.sum_range_eq_list_sum lens len (fun i hi => by
          have hiL : i < L := hlens_L ▸ hi
          simp [len, hiL])
      exact h3.trans hlens_sum
    omega
  exact H2Proof.assemble_cycle G hn4 (by omega) z segs
    (fun i hi => (hsegs_spec i hi).1)
    (fun i hi => (hsegs_spec i hi).2.2.1)
    (fun i hi => (hsegs_spec i hi).2.2.2.2.1)
    (fun i hi => (hsegs_spec i hi).2.2.2.2.2.1)
    (fun i hi => (hsegs_spec i hi).2.2.2.1)
    hdisj_segs
    hsum_segs
end H2Section

theorem OMA.solution : type_of% @Erdos556.erdos_556.variants.luczak_asymptotic_even :=
  OMA.Erdos556R1.main h1_proof h2_proof
