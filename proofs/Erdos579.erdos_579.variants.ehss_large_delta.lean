import FormalConjectures.ErdosProblems.«579»

/-!
# Proof of Erdős Problem 579 (EHSS large delta variant)

Formal proof of `Erdos579.erdos_579.variants.ehss_large_delta`: for every `δ > 1 / 8` there is
`c > 0` such that for all sufficiently large `n`, every `K_{2,2,2}`-free graph on `n` vertices
with at least `δ * n^2` edges has independence number at least `c * n`.

The proof combines Mathlib's `szemeredi_regularity`, Mantel's theorem, and two elementary
`K_{2,2,2}` embedding lemmas via double counting.
-/

-- Problem: Erdős Problem 579 — ehss large delta
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/579.lean:71 (declaration Erdos579.erdos_579.variants.ehss_large_delta)
-- Credit: @mrmario2202

namespace Erdos579Proof

open Finset Filter SimpleGraph

/-- Six vertices forming the three parts of size 2 of `K_{2,2,2}` refute `octahedron.Free G`. -/
lemma not_octahedron_free_of_six {V : Type*} {G : SimpleGraph V}
    {a0 a1 b0 b1 c0 c1 : V}
    (ha : a0 ≠ a1) (hb : b0 ≠ b1) (hc : c0 ≠ c1)
    (hab00 : G.Adj a0 b0) (hab01 : G.Adj a0 b1) (hab10 : G.Adj a1 b0) (hab11 : G.Adj a1 b1)
    (hac00 : G.Adj a0 c0) (hac01 : G.Adj a0 c1) (hac10 : G.Adj a1 c0) (hac11 : G.Adj a1 c1)
    (hbc00 : G.Adj b0 c0) (hbc01 : G.Adj b0 c1) (hbc10 : G.Adj b1 c0) (hbc11 : G.Adj b1 c1) :
    ¬ Erdos579.octahedron.Free G := by
  let f : (Σ _ : Fin 3, Fin 2) → V
    | ⟨0, 0⟩ => a0
    | ⟨0, 1⟩ => a1
    | ⟨1, 0⟩ => b0
    | ⟨1, 1⟩ => b1
    | ⟨2, 0⟩ => c0
    | ⟨2, 1⟩ => c1
  have hf_adj : ∀ {x y : Σ _ : Fin 3, Fin 2}, Erdos579.octahedron.Adj x y → G.Adj (f x) (f y) := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have hne : i ≠ i' := h
    fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
      first
      | exact absurd rfl hne
      | exact hab00 | exact hab01 | exact hab10 | exact hab11
      | exact hab00.symm | exact hab01.symm | exact hab10.symm | exact hab11.symm
      | exact hac00 | exact hac01 | exact hac10 | exact hac11
      | exact hac00.symm | exact hac01.symm | exact hac10.symm | exact hac11.symm
      | exact hbc00 | exact hbc01 | exact hbc10 | exact hbc11
      | exact hbc00.symm | exact hbc01.symm | exact hbc10.symm | exact hbc11.symm
  have hf_inj : Function.Injective f := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
      first
      | rfl
      | exact absurd h ha | exact absurd h ha.symm
      | exact absurd h hb | exact absurd h hb.symm
      | exact absurd h hc | exact absurd h hc.symm
      | exact absurd h (G.ne_of_adj hab00) | exact absurd h (G.ne_of_adj hab00).symm
      | exact absurd h (G.ne_of_adj hab01) | exact absurd h (G.ne_of_adj hab01).symm
      | exact absurd h (G.ne_of_adj hab10) | exact absurd h (G.ne_of_adj hab10).symm
      | exact absurd h (G.ne_of_adj hab11) | exact absurd h (G.ne_of_adj hab11).symm
      | exact absurd h (G.ne_of_adj hac00) | exact absurd h (G.ne_of_adj hac00).symm
      | exact absurd h (G.ne_of_adj hac01) | exact absurd h (G.ne_of_adj hac01).symm
      | exact absurd h (G.ne_of_adj hac10) | exact absurd h (G.ne_of_adj hac10).symm
      | exact absurd h (G.ne_of_adj hac11) | exact absurd h (G.ne_of_adj hac11).symm
      | exact absurd h (G.ne_of_adj hbc00) | exact absurd h (G.ne_of_adj hbc00).symm
      | exact absurd h (G.ne_of_adj hbc01) | exact absurd h (G.ne_of_adj hbc01).symm
      | exact absurd h (G.ne_of_adj hbc10) | exact absurd h (G.ne_of_adj hbc10).symm
      | exact absurd h (G.ne_of_adj hbc11) | exact absurd h (G.ne_of_adj hbc11).symm
  intro hfree
  exact hfree ⟨⟨⟨f, hf_adj⟩, hf_inj⟩⟩

/-- Greedy independent set bound: if every vertex in `S` has at most `d` neighbors in `S`,
then `S` contains an independent set `I` with `#S ≤ (d + 1) * #I`. -/
lemma exists_indepSet_of_maxDeg_le {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) :
    ∀ S : Finset V, (∀ v ∈ S, #{w ∈ S | G.Adj v w} ≤ d) →
      ∃ I ⊆ S, G.IsIndepSet (I : Set V) ∧ #S ≤ (d + 1) * #I := by
  intro S
  induction hn : #S using Nat.strong_induction_on generalizing S with
  | h m ih =>
    intro hdeg
    rcases S.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
    · simp only [card_empty] at hn
      subst hn
      exact ⟨∅, Subset.rfl, by simp [SimpleGraph.IsIndepSet], by simp⟩
    · let N : Finset V := {w ∈ S | G.Adj v w}
      let S' : Finset V := {w ∈ S | w ≠ v ∧ ¬ G.Adj v w}
      have hS'_sub : S' ⊆ S := filter_subset _ S
      have hv_not : v ∉ S' := by simp [S']
      have hS'_lt : #S' < m := by
        rw [← hn]
        exact card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hS'_sub, fun heq => hv_not (heq ▸ hv)⟩)
      have hdeg' : ∀ u ∈ S', #{w ∈ S' | G.Adj u w} ≤ d := fun u hu =>
        (card_le_card (filter_subset_filter _ hS'_sub)).trans (hdeg u (hS'_sub hu))
      obtain ⟨I', hI'_sub, hI'_indep, hI'_card⟩ := ih #S' hS'_lt S' rfl hdeg'
      have hv_not_I' : v ∉ I' := fun h => hv_not (hI'_sub h)
      refine ⟨insert v I', insert_subset hv (hI'_sub.trans hS'_sub), ?_, ?_⟩
      · intro x hx y hy hxy
        simp only [coe_insert, Set.mem_insert_iff, mem_coe] at hx hy
        rcases hx with rfl | hx <;> rcases hy with rfl | hy
        · exact absurd rfl hxy
        · exact ((mem_filter.mp (hI'_sub hy)).2).2
        · exact fun hadj => ((mem_filter.mp (hI'_sub hx)).2).2 hadj.symm
        · exact hI'_indep hx hy hxy
      · have hcover : S ⊆ insert v (N ∪ S') := by
          intro w hw
          by_cases hwv : w = v
          · subst hwv
            exact mem_insert_self _ _
          · by_cases hadj : G.Adj v w
            · exact mem_insert_of_mem (mem_union_left _ (mem_filter.mpr ⟨hw, hadj⟩))
            · exact mem_insert_of_mem (mem_union_right _ (mem_filter.mpr ⟨hw, hwv, hadj⟩))
        have hS_le : #S ≤ 1 + #N + #S' := by
          calc #S ≤ #(insert v (N ∪ S')) := card_le_card hcover
            _ ≤ #(N ∪ S') + 1 := card_insert_le _ _
            _ ≤ #N + #S' + 1 := by grw [card_union_le]
            _ = 1 + #N + #S' := by omega
        have hN_le : #N ≤ d := hdeg v hv
        rw [card_insert_of_notMem hv_not_I']
        nlinarith

/-- Contrapositive of the greedy independent set bound: if `r * G.indepNum < #S`,
then some vertex in `S` has at least `r` neighbors in `S`. -/
lemma exists_vertex_deg_ge_of_indepNum_lt {V : Type*} [DecidableEq V] [Finite V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {S : Finset V} {r : ℕ} (hr : 1 ≤ r)
    (hcard : r * G.indepNum < #S) :
    ∃ v ∈ S, r ≤ #{w ∈ S | G.Adj v w} := by
  by_contra h
  push Not at h
  have hdeg : ∀ v ∈ S, #{w ∈ S | G.Adj v w} ≤ r - 1 := fun v hv => Nat.le_sub_one_of_lt (h v hv)
  obtain ⟨I, _, hI_indep, hI_card⟩ := exists_indepSet_of_maxDeg_le G (r - 1) S hdeg
  have hI_le : #I ≤ G.indepNum := hI_indep.card_le_indepNum
  have hr1 : r - 1 + 1 = r := Nat.sub_add_cancel hr
  rw [hr1] at hI_card
  have : #S ≤ r * G.indepNum := hI_card.trans (Nat.mul_le_mul_left r hI_le)
  omega

/-- Number of ordered interedges equals the sum of degrees from the left part to the right part. -/
lemma card_interedges_eq_sum {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s t : Finset V) :
    #(G.interedges s t) = ∑ x ∈ s, #{y ∈ t | G.Adj x y} := by
  rw [SimpleGraph.interedges, Rel.interedges_eq_biUnion, card_biUnion]
  · congr 1
    ext x
    exact card_map _
  · intro x _ y _ hxy
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hp1 hp2
    obtain ⟨a, _, rfl⟩ := hp1
    obtain ⟨b, _, h⟩ := hp2
    exact hxy (Prod.mk.inj h).1.symm

/-- Total number of ordered adjacent pairs equals `2 * #G.edgeFinset`. -/
lemma card_interedges_univ {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    #(G.interedges univ univ) = 2 * #G.edgeFinset := by
  rw [card_interedges_eq_sum, ← G.sum_degrees_eq_twice_card_edges]
  congr 1
  ext v
  rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter]

/-- Sum over a union of finsets is at most the sum of the two sums when `f ≥ 0`. -/
lemma sum_union_le_of_nonneg {α : Type*} [DecidableEq α] (s₁ s₂ : Finset α)
    (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s₁ ∪ s₂, f x ≤ ∑ x ∈ s₁, f x + ∑ x ∈ s₂, f x := by
  have h := Finset.sum_union_inter (s₁ := s₁) (s₂ := s₂) (f := f)
  have hnn : 0 ≤ ∑ x ∈ s₁ ∩ s₂, f x := Finset.sum_nonneg fun x _ => hf x
  linarith

/-- Double counting + Cauchy-Schwarz: among subsets `N(a) ⊆ B` indexed by `a ∈ A` with `#A ≥ 2`,
some pair of distinct `a₁, a₂ ∈ A` has large common intersection. -/
lemma exists_pair_common_neighbors_ge {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (hA : 2 ≤ #A) :
    ∃ a₁ ∈ A, ∃ a₂ ∈ A, a₁ ≠ a₂ ∧
      ((#(G.interedges A B) : ℝ) ^ 2 - (#B : ℝ) * (#(G.interedges A B) : ℝ)) ≤
        (#B : ℝ) * ((#A : ℝ) * ((#A : ℝ) - 1)) *
          (#{b ∈ B | G.Adj a₁ b ∧ G.Adj a₂ b} : ℝ) := by
  let degB : V → ℕ := fun b => #{a ∈ A | G.Adj a b}
  have hE_eq : #(G.interedges A B) = ∑ b ∈ B, degB b := by
    have : Std.Symm G.Adj := G.symm
    rw [SimpleGraph.interedges, Rel.card_interedges_comm, ← SimpleGraph.interedges,
      card_interedges_eq_sum]
    congr 1
    ext b
    congr 1
    ext a
    simp only [mem_filter, G.adj_comm]
  have hdouble :
      ∑ p ∈ A.offDiag, #{b ∈ B | G.Adj p.1 b ∧ G.Adj p.2 b} =
        ∑ b ∈ B, degB b * (degB b - 1) := by
    have h1 : ∀ p : V × V,
        #{b ∈ B | G.Adj p.1 b ∧ G.Adj p.2 b} =
          ∑ b ∈ B, if G.Adj p.1 b ∧ G.Adj p.2 b then 1 else 0 := fun p => by
      rw [card_filter]
    simp_rw [h1]
    rw [sum_comm]
    congr 1
    ext b
    have h2 :
        ∑ p ∈ A.offDiag, (if G.Adj p.1 b ∧ G.Adj p.2 b then 1 else 0) =
          #({a ∈ A | G.Adj a b}.offDiag) := by
      rw [← card_filter]
      congr 1
      ext ⟨a₁, a₂⟩
      simp only [mem_filter, mem_offDiag]
      tauto
    rw [h2, offDiag_card]
    simp [degB, Nat.mul_sub_left_distrib]
  have hreal_sum :
      ((∑ b ∈ B, degB b * (degB b - 1) : ℕ) : ℝ) =
        ∑ b ∈ B, ((degB b : ℝ) ^ 2 - (degB b : ℝ)) := by
    push_cast
    congr 1
    ext b
    rcases Nat.eq_zero_or_pos (degB b) with h0 | hpos
    · simp [h0]
    · rw [Nat.cast_sub hpos]
      ring
  have hCS : (#(G.interedges A B) : ℝ) ^ 2 ≤ (#B : ℝ) * ∑ b ∈ B, (degB b : ℝ) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := B) (f := fun b => (degB b : ℝ))
    rw [hE_eq]
    simpa [Nat.cast_sum] using h
  have hsum_lower :
      (#(G.interedges A B) : ℝ) ^ 2 - (#B : ℝ) * (#(G.interedges A B) : ℝ) ≤
        (#B : ℝ) * ∑ p ∈ A.offDiag, (#{b ∈ B | G.Adj p.1 b ∧ G.Adj p.2 b} : ℝ) := by
    have hcast :
        ∑ p ∈ A.offDiag, (#{b ∈ B | G.Adj p.1 b ∧ G.Adj p.2 b} : ℝ) =
          ∑ b ∈ B, ((degB b : ℝ) ^ 2 - (degB b : ℝ)) := by
      rw [← Nat.cast_sum, hdouble, hreal_sum]
    rw [hcast, sum_sub_distrib, mul_sub]
    have hE_cast : ∑ b ∈ B, (degB b : ℝ) = (#(G.interedges A B) : ℝ) := by
      rw [hE_eq, Nat.cast_sum]
    rw [hE_cast]
    linarith
  have hoff_pos : 0 < #A.offDiag := by
    rw [offDiag_card]
    have : #A < #A * #A := by nlinarith only [hA]
    omega
  have hoff_ne : A.offDiag.Nonempty := card_pos.mp hoff_pos
  obtain ⟨p, hp_mem, hp_max⟩ :=
    exists_max_image A.offDiag (fun p => (#{b ∈ B | G.Adj p.1 b ∧ G.Adj p.2 b} : ℝ)) hoff_ne
  have hsum_le_max :
      ∑ q ∈ A.offDiag, (#{b ∈ B | G.Adj q.1 b ∧ G.Adj q.2 b} : ℝ) ≤
        (#A.offDiag : ℝ) * (#{b ∈ B | G.Adj p.1 b ∧ G.Adj p.2 b} : ℝ) := by
    calc ∑ q ∈ A.offDiag, (#{b ∈ B | G.Adj q.1 b ∧ G.Adj q.2 b} : ℝ)
        ≤ ∑ _ ∈ A.offDiag, (#{b ∈ B | G.Adj p.1 b ∧ G.Adj p.2 b} : ℝ) := sum_le_sum hp_max
      _ = (#A.offDiag : ℝ) * (#{b ∈ B | G.Adj p.1 b ∧ G.Adj p.2 b} : ℝ) := by
          rw [sum_const, nsmul_eq_mul]
  have hoff_cast : (#A.offDiag : ℝ) = (#A : ℝ) * ((#A : ℝ) - 1) := by
    rw [offDiag_card]
    have h1 : #A ≤ #A * #A := Nat.le_mul_self #A
    rw [Nat.cast_sub h1, Nat.cast_mul]
    ring
  rw [mem_offDiag] at hp_mem
  refine ⟨p.1, hp_mem.1, p.2, hp_mem.2.1, hp_mem.2.2, ?_⟩
  have hB_nonneg : (0 : ℝ) ≤ #B := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hsum_le_max hB_nonneg
  rw [hoff_cast, ← mul_assoc] at hmul
  exact hsum_lower.trans hmul

/-- Lemma 1 (Dense Pair): If disjoint `A, B` have edge density at least `1/2 + 3 * η`
and `G.indepNum < (η^2 / 2) * min #A #B`, then `G` contains `K_{2,2,2}`. -/
lemma dense_pair_not_octahedron_free {V : Type*} [DecidableEq V] [Finite V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (hdisj : Disjoint A B)
    (hA_pos : 0 < #A) (hB_pos : 0 < #B)
    {η : ℝ} (hη_pos : 0 < η) (hη_le : η ≤ 1 / 4)
    (hdense : (1 / 2 + 3 * η) * (#A : ℝ) * (#B : ℝ) ≤ (#(G.interedges A B) : ℝ))
    (hindepA : (G.indepNum : ℝ) < (η ^ 2 / 2) * (#A : ℝ))
    (hindepB : (G.indepNum : ℝ) < (η ^ 2 / 2) * (#B : ℝ)) :
    ¬ Erdos579.octahedron.Free G := by
  let U : Finset V := {u ∈ A | (1 / 2 + η) * (#B : ℝ) ≤ (#{v ∈ B | G.Adj u v} : ℝ)}
  have hU_sub : U ⊆ A := filter_subset _ A
  -- Markov lower bound: 4 * η * #A ≤ #U
  have hU_card : 4 * η * (#A : ℝ) ≤ (#U : ℝ) := by
    have hsplit : (#(G.interedges A B) : ℝ) =
        ∑ u ∈ U, (#{v ∈ B | G.Adj u v} : ℝ) + ∑ u ∈ A \ U, (#{v ∈ B | G.Adj u v} : ℝ) := by
      rw [card_interedges_eq_sum, Nat.cast_sum, ← sum_sdiff hU_sub, add_comm]
    have h1 : ∑ u ∈ U, (#{v ∈ B | G.Adj u v} : ℝ) ≤ (#U : ℝ) * (#B : ℝ) := by
      calc ∑ u ∈ U, (#{v ∈ B | G.Adj u v} : ℝ)
          ≤ ∑ _ ∈ U, (#B : ℝ) := sum_le_sum fun u _ => by exact_mod_cast card_filter_le B _
        _ = (#U : ℝ) * (#B : ℝ) := by rw [sum_const, nsmul_eq_mul]
    have h2 : ∑ u ∈ A \ U, (#{v ∈ B | G.Adj u v} : ℝ) ≤
        (#(A \ U) : ℝ) * ((1 / 2 + η) * (#B : ℝ)) := by
      calc ∑ u ∈ A \ U, (#{v ∈ B | G.Adj u v} : ℝ)
          ≤ ∑ _ ∈ A \ U, ((1 / 2 + η) * (#B : ℝ)) := by
            refine sum_le_sum fun u hu => ?_
            rw [Finset.mem_sdiff] at hu
            have hnot : ¬ ((1 / 2 + η) * (#B : ℝ) ≤ (#{v ∈ B | G.Adj u v} : ℝ)) := fun h =>
              hu.2 (mem_filter.mpr ⟨hu.1, h⟩)
            linarith
        _ = (#(A \ U) : ℝ) * ((1 / 2 + η) * (#B : ℝ)) := by rw [sum_const, nsmul_eq_mul]
    have hsdiff_card : (#(A \ U) : ℝ) = (#A : ℝ) - (#U : ℝ) := by
      rw [card_sdiff_of_subset hU_sub, Nat.cast_sub (card_le_card hU_sub)]
    have hB_rpos : (0 : ℝ) < #B := Nat.cast_pos.mpr hB_pos
    have htot : (1 / 2 + 3 * η) * (#A : ℝ) * (#B : ℝ) ≤
        ((#U : ℝ) + ((#A : ℝ) - (#U : ℝ)) * (1 / 2 + η)) * (#B : ℝ) := by
      rw [hsdiff_card] at h2
      linarith
    have hcancel : (1 / 2 + 3 * η) * (#A : ℝ) ≤
        (#U : ℝ) + ((#A : ℝ) - (#U : ℝ)) * (1 / 2 + η) :=
      le_of_mul_le_mul_right htot hB_rpos
    have hU_nn : (0 : ℝ) ≤ #U := Nat.cast_nonneg _
    nlinarith only [hcancel, hη_pos, hU_nn]
  -- Choose r large enough so 2 * η * r ≥ 2
  let r : ℕ := Nat.ceil (1 / η) + 1
  have hr_ge_two : 2 ≤ r := by
    have h1 : 1 ≤ Nat.ceil (1 / η) := Nat.one_le_iff_ne_zero.mpr (by
      intro h0
      have : (1 / η : ℝ) ≤ (Nat.ceil (1 / η) : ℝ) := Nat.le_ceil _
      rw [h0, Nat.cast_zero] at this
      have : (0 : ℝ) < 1 / η := one_div_pos.mpr hη_pos
      linarith)
    omega
  have hr_ge_inv : 1 / η ≤ (r : ℝ) := by
    have h1 : (1 / η : ℝ) ≤ (Nat.ceil (1 / η) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (1 / η) : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.le_succ _
    linarith
  have hr_lt : (r : ℝ) < 1 / η + 2 := by
    have hlt : (Nat.ceil (1 / η) : ℝ) < 1 / η + 1 := Nat.ceil_lt_add_one (by positivity)
    have hrc : (r : ℝ) = (Nat.ceil (1 / η) : ℝ) + 1 := by exact_mod_cast rfl
    linarith
  have hηr_ge_one : 1 ≤ η * (r : ℝ) := by
    have := mul_le_mul_of_nonneg_left hr_ge_inv hη_pos.le
    rwa [mul_one_div_cancel hη_pos.ne'] at this
  -- Show r * G.indepNum < #U
  have hr_indep_lt : r * G.indepNum < #U := by
    suffices h : ((r : ℝ) * (G.indepNum : ℝ)) < (#U : ℝ) by exact_mod_cast h
    have hr_pos : (0 : ℝ) < r := by
      have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr_ge_two
      linarith
    have h1 : (r : ℝ) * (G.indepNum : ℝ) < (r : ℝ) * ((η ^ 2 / 2) * (#A : ℝ)) :=
      mul_lt_mul_of_pos_left hindepA hr_pos
    have h2 : (r : ℝ) * (η ^ 2 / 2) < 4 * η := by
      have hA1 : (r : ℝ) * (η ^ 2 / 2) < (1 / η + 2) * (η ^ 2 / 2) :=
        mul_lt_mul_of_pos_right hr_lt (by positivity)
      have hA2 : (1 / η + 2) * (η ^ 2 / 2) = η / 2 + η ^ 2 := by
        field_simp [hη_pos.ne']
      nlinarith only [hA1, hA2, hη_pos, hη_le]
    have hA_rpos : (0 : ℝ) < #A := Nat.cast_pos.mpr hA_pos
    have h3 : (r : ℝ) * ((η ^ 2 / 2) * (#A : ℝ)) < 4 * η * (#A : ℝ) := by
      rw [← mul_assoc]
      exact mul_lt_mul_of_pos_right h2 hA_rpos
    linarith
  -- Find c1 ∈ U with at least r neighbors in U
  obtain ⟨c1, hc1_U, hc1_deg⟩ :=
    exists_vertex_deg_ge_of_indepNum_lt G (by omega : 1 ≤ r) hr_indep_lt
  obtain ⟨R, hR_sub, hR_card⟩ := exists_subset_card_eq hc1_deg
  let W1 : Finset V := {v ∈ B | G.Adj c1 v}
  have hW1_sub : W1 ⊆ B := filter_subset _ B
  have hW1_card : (1 / 2 + η) * (#B : ℝ) ≤ (#W1 : ℝ) := (mem_filter.mp hc1_U).2
  have hW1_pos : (0 : ℝ) < #W1 := by
    have hBr : (0 : ℝ) < #B := Nat.cast_pos.mpr hB_pos
    nlinarith only [hW1_card, hη_pos, hBr]
  -- Every a ∈ R has at least 2 * η * #W1 neighbors in W1
  have hR_deg : ∀ a ∈ R, 2 * η * (#W1 : ℝ) ≤ (#{v ∈ W1 | G.Adj a v} : ℝ) := by
    intro a haR
    have haU : a ∈ U := (mem_filter.mp (hR_sub haR)).1
    let Na : Finset V := {v ∈ B | G.Adj a v}
    have hNa_card : (1 / 2 + η) * (#B : ℝ) ≤ (#Na : ℝ) := (mem_filter.mp haU).2
    have hinter_eq : {v ∈ W1 | G.Adj a v} = W1 ∩ Na := by
      ext v
      simp only [mem_filter, mem_inter, W1, Na]
      tauto
    have hunion_le : #(W1 ∪ Na) ≤ #B := card_le_card (union_subset hW1_sub (filter_subset _ B))
    have hinc : #W1 + #Na = #(W1 ∪ Na) + #(W1 ∩ Na) := (card_union_add_card_inter W1 Na).symm
    have hW1_le_B : (#W1 : ℝ) ≤ (#B : ℝ) := by exact_mod_cast card_le_card hW1_sub
    rw [hinter_eq]
    have hinc_r : (#W1 : ℝ) + (#Na : ℝ) ≤ (#B : ℝ) + (#(W1 ∩ Na) : ℝ) := by
      exact_mod_cast (show #W1 + #Na ≤ #B + #(W1 ∩ Na) by omega)
    nlinarith only [hW1_card, hNa_card, hinc_r, hW1_le_B, hη_pos]
  have hE_lower : 2 * η * (r : ℝ) * (#W1 : ℝ) ≤ (#(G.interedges R W1) : ℝ) := by
    rw [card_interedges_eq_sum, Nat.cast_sum]
    calc 2 * η * (r : ℝ) * (#W1 : ℝ)
        = ∑ _ ∈ R, (2 * η * (#W1 : ℝ)) := by
            rw [sum_const, hR_card, nsmul_eq_mul]; ring
      _ ≤ ∑ a ∈ R, (#{v ∈ W1 | G.Adj a v} : ℝ) := sum_le_sum hR_deg
  -- Double count on (R, W1)
  obtain ⟨a1, ha1_R, a2, ha2_R, ha_ne, hpair⟩ :=
    exists_pair_common_neighbors_ge G R W1 (by omega)
  let W2 : Finset V := {v ∈ W1 | G.Adj a1 v ∧ G.Adj a2 v}
  have hW2_card : η ^ 2 * (#B : ℝ) ≤ (#W2 : ℝ) := by
    set E : ℝ := (#(G.interedges R W1) : ℝ)
    set E0 : ℝ := 2 * η * (r : ℝ) * (#W1 : ℝ)
    have hE0_ge : 2 * (#W1 : ℝ) ≤ E0 := by
      have : 2 * (#W1 : ℝ) ≤ 2 * (η * (r : ℝ)) * (#W1 : ℝ) := by
        nlinarith only [hηr_ge_one, hW1_pos]
      simpa only [E0, mul_assoc] using this
    have hquad : E0 ^ 2 - (#W1 : ℝ) * E0 ≤ E ^ 2 - (#W1 : ℝ) * E := by
      have hdiff : E ^ 2 - (#W1 : ℝ) * E - (E0 ^ 2 - (#W1 : ℝ) * E0) =
          (E - E0) * (E + E0 - (#W1 : ℝ)) := by ring
      have h1 : 0 ≤ E - E0 := by linarith only [hE_lower]
      have h2 : 0 ≤ E + E0 - (#W1 : ℝ) := by linarith only [hE_lower, hE0_ge, hW1_pos]
      have h3 : 0 ≤ (E - E0) * (E + E0 - (#W1 : ℝ)) := mul_nonneg h1 h2
      linarith only [hdiff, h3]
    rw [hR_card] at hpair
    have h1 : E0 ^ 2 - (#W1 : ℝ) * E0 ≤
        (#W1 : ℝ) * ((r : ℝ) * ((r : ℝ) - 1)) * (#W2 : ℝ) := hquad.trans hpair
    have hr1_pos : (0 : ℝ) < (r : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr_ge_two
      linarith
    have hr_pos : (0 : ℝ) < (r : ℝ) := by linarith
    have hden_pos : (0 : ℝ) < (#W1 : ℝ) * ((r : ℝ) * ((r : ℝ) - 1)) := by positivity
    have hnum : (2 * η ^ 2 * (#W1 : ℝ)) * ((#W1 : ℝ) * ((r : ℝ) * ((r : ℝ) - 1))) ≤
        E0 ^ 2 - (#W1 : ℝ) * E0 := by
      have hstep : E0 ^ 2 - (#W1 : ℝ) * E0 =
          2 * η * (r : ℝ) * (#W1 : ℝ) ^ 2 * (2 * η * (r : ℝ) - 1) := by
        simp only [E0]; ring
      have hlhs : (2 * η ^ 2 * (#W1 : ℝ)) * ((#W1 : ℝ) * ((r : ℝ) * ((r : ℝ) - 1))) =
          2 * η * (r : ℝ) * (#W1 : ℝ) ^ 2 * (η * ((r : ℝ) - 1)) := by ring
      rw [hstep, hlhs]
      have hlin : η * ((r : ℝ) - 1) ≤ 2 * η * (r : ℝ) - 1 := by
        nlinarith only [hηr_ge_one, hη_pos]
      exact mul_le_mul_of_nonneg_left hlin (by positivity)
    have h2 : 2 * η ^ 2 * (#W1 : ℝ) ≤ (#W2 : ℝ) := by
      have hcomb : (2 * η ^ 2 * (#W1 : ℝ)) * ((#W1 : ℝ) * ((r : ℝ) * ((r : ℝ) - 1))) ≤
          (#W2 : ℝ) * ((#W1 : ℝ) * ((r : ℝ) * ((r : ℝ) - 1))) := by
        rw [mul_comm (#W2 : ℝ)]
        exact hnum.trans h1
      exact le_of_mul_le_mul_right hcomb hden_pos
    have h3 : η ^ 2 * (#B : ℝ) ≤ 2 * η ^ 2 * (#W1 : ℝ) := by
      have hBr : (0 : ℝ) < #B := Nat.cast_pos.mpr hB_pos
      have hhalf : (#B : ℝ) ≤ 2 * (#W1 : ℝ) := by nlinarith only [hW1_card, hη_pos, hBr]
      have hmul := mul_le_mul_of_nonneg_left hhalf (sq_nonneg η)
      linarith only [hmul]
    exact h3.trans h2
  -- Find a cherry in W2
  have hW2_indep_lt : 2 * G.indepNum < #W2 := by
    suffices h : (2 : ℝ) * (G.indepNum : ℝ) < (#W2 : ℝ) by exact_mod_cast h
    linarith only [hindepB, hW2_card]
  obtain ⟨c2, hc2_W2, hc2_deg⟩ :=
    exists_vertex_deg_ge_of_indepNum_lt G (by decide : 1 ≤ 2) hW2_indep_lt
  obtain ⟨b1, hb1, b2, hb2, hb_ne⟩ := one_lt_card.mp (by omega : 1 < #{w ∈ W2 | G.Adj c2 w})
  rw [mem_filter] at hb1 hb2
  -- Verify all 6 vertices form an octahedron
  have ha1_adj_c1 : G.Adj a1 c1 := (mem_filter.mp (hR_sub ha1_R)).2.symm
  have ha2_adj_c1 : G.Adj a2 c1 := (mem_filter.mp (hR_sub ha2_R)).2.symm
  have hc1_ne_c2 : c1 ≠ c2 := by
    have hc1A : c1 ∈ A := hU_sub hc1_U
    have hc2B : c2 ∈ B := hW1_sub (mem_filter.mp hc2_W2).1
    exact fun heq => Finset.disjoint_left.mp hdisj hc1A (heq ▸ hc2B)
  have hb1_W1 : b1 ∈ W1 := (mem_filter.mp hb1.1).1
  have hb2_W1 : b2 ∈ W1 := (mem_filter.mp hb2.1).1
  exact not_octahedron_free_of_six ha_ne hb_ne hc1_ne_c2
    (mem_filter.mp hb1.1).2.1 (mem_filter.mp hb2.1).2.1
    (mem_filter.mp hb1.1).2.2 (mem_filter.mp hb2.1).2.2
    ha1_adj_c1 (mem_filter.mp hc2_W2).2.1
    ha2_adj_c1 (mem_filter.mp hc2_W2).2.2
    (mem_filter.mp hb1_W1).2.symm hb1.2.symm
    (mem_filter.mp hb2_W1).2.symm hb2.2.symm

/-- Standard degree lemma for an `η`-uniform pair: fewer than `η * #S` vertices in `S` have
fewer than `(d - η) * #T'` neighbors in a large subset `T' ⊆ T`. -/
lemma card_low_degree_lt_of_isUniform {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {S T T' : Finset V} {η d : ℝ}
    (hunif : G.IsUniform η S T) (hT'_sub : T' ⊆ T)
    (hS_pos : 0 < #S) (hT_pos : 0 < #T) (hη_pos : 0 < η)
    (hT'_card : (#T : ℝ) * η ≤ (#T' : ℝ))
    (hd : d ≤ (G.edgeDensity S T : ℝ)) :
    (#{x ∈ S | (#{y ∈ T' | G.Adj x y} : ℝ) < (d - η) * (#T' : ℝ)} : ℝ) < (#S : ℝ) * η := by
  set Bad : Finset V := {x ∈ S | (#{y ∈ T' | G.Adj x y} : ℝ) < (d - η) * (#T' : ℝ)}
  by_contra hle
  push Not at hle
  have hBad_sub : Bad ⊆ S := filter_subset _ S
  have hBad_rpos : (0 : ℝ) < #Bad := lt_of_lt_of_le (mul_pos (Nat.cast_pos.mpr hS_pos) hη_pos) hle
  have hBad_ne : Bad.Nonempty := card_pos.mp (by exact_mod_cast hBad_rpos)
  have hT'_rpos : (0 : ℝ) < #T' := lt_of_lt_of_le (mul_pos (Nat.cast_pos.mpr hT_pos) hη_pos) hT'_card
  have hreg := hunif hBad_sub hT'_sub hle hT'_card
  have hdens_gt : d - η < (G.edgeDensity Bad T' : ℝ) := by
    have := (abs_lt.mp hreg).1
    linarith
  have hE_gt : (d - η) * ((#Bad : ℝ) * (#T' : ℝ)) < (#(G.interedges Bad T') : ℝ) := by
    rw [SimpleGraph.edgeDensity_def, Rat.cast_div, Rat.cast_natCast, Rat.cast_mul,
      Rat.cast_natCast, Rat.cast_natCast] at hdens_gt
    exact (lt_div_iff₀ (mul_pos hBad_rpos hT'_rpos)).mp hdens_gt
  have hE_lt : (#(G.interedges Bad T') : ℝ) < (#Bad : ℝ) * ((d - η) * (#T' : ℝ)) := by
    rw [card_interedges_eq_sum, Nat.cast_sum]
    calc ∑ x ∈ Bad, (#{y ∈ T' | G.Adj x y} : ℝ)
        < ∑ _ ∈ Bad, ((d - η) * (#T' : ℝ)) :=
          sum_lt_sum_of_nonempty hBad_ne fun x hx => (mem_filter.mp hx).2
      _ = (#Bad : ℝ) * ((d - η) * (#T' : ℝ)) := by rw [sum_const, nsmul_eq_mul]
  linarith

/-- Lemma 2 (Regular Dense Triangle): A pairwise `η`-uniform triple of parts
with edge densities at least `γ` and sufficient size contains `K_{2,2,2}`. -/
lemma regular_triangle_not_octahedron_free {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {V1 V2 V3 : Finset V} {η γ : ℝ}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1)
    (hη_pos : 0 < η) (hη_le : η ≤ γ ^ 2 / 4)
    (hm1 : (16 / γ ^ 2 + 2) / η ≤ (#V1 : ℝ))
    (hm2 : (16 / γ ^ 2 + 2) / η ≤ (#V2 : ℝ))
    (hm3 : (16 / γ ^ 2 + 2) / η ≤ (#V3 : ℝ))
    (hu12 : G.IsUniform η V1 V2) (hu13 : G.IsUniform η V1 V3) (hu23 : G.IsUniform η V2 V3)
    (hd12 : γ ≤ (G.edgeDensity V1 V2 : ℝ))
    (hd13 : γ ≤ (G.edgeDensity V1 V3 : ℝ))
    (hd23 : γ ≤ (G.edgeDensity V2 V3 : ℝ)) :
    ¬ Erdos579.octahedron.Free G := by
  have hη_le_γ4 : η ≤ γ / 4 := by nlinarith only [hγ_pos, hγ_le, hη_le]
  have hη_le_quarter : η ≤ 1 / 4 := by linarith only [hη_le_γ4, hγ_le]
  have hγ_sub_η_ge : 3 / 4 * γ ≤ γ - η := by linarith only [hη_le_γ4]
  have hsq_ge_η : η ≤ (γ - η) ^ 2 := by nlinarith only [hγ_sub_η_ge, hγ_pos, hη_le]
  have hη_le_γ_sub : η ≤ γ - η := by linarith only [hη_le_γ4, hγ_pos]
  have hmin_ge_two : (2 : ℝ) ≤ (16 / γ ^ 2 + 2) / η := by
    have h0 : (0 : ℝ) ≤ 16 / γ ^ 2 := by positivity
    have h1 : (2 : ℝ) ≤ 16 / γ ^ 2 + 2 := by linarith only [h0]
    have h2 : (1 : ℝ) ≤ 1 / η := (one_le_div hη_pos).mpr (by linarith only [hη_le_quarter])
    rw [div_eq_mul_one_div]
    nlinarith only [h1, h2]
  have hV1_pos : 0 < #V1 := by exact_mod_cast (show (0 : ℝ) < #V1 by linarith only [hm1, hmin_ge_two])
  have hV2_pos : 0 < #V2 := by exact_mod_cast (show (0 : ℝ) < #V2 by linarith only [hm2, hmin_ge_two])
  have hV3_pos : 0 < #V3 := by exact_mod_cast (show (0 : ℝ) < #V3 by linarith only [hm3, hmin_ge_two])
  -- Step 1: Pick a1 ∈ V1 with many neighbors in both V2 and V3
  have hBad12 := card_low_degree_lt_of_isUniform G hu12 Subset.rfl hV1_pos hV2_pos hη_pos
    (by nlinarith only [hη_le_quarter, Nat.cast_nonneg (α := ℝ) #V2] : (#V2 : ℝ) * η ≤ (#V2 : ℝ)) hd12
  have hBad13 := card_low_degree_lt_of_isUniform G hu13 Subset.rfl hV1_pos hV3_pos hη_pos
    (by nlinarith only [hη_le_quarter, Nat.cast_nonneg (α := ℝ) #V3] : (#V3 : ℝ) * η ≤ (#V3 : ℝ)) hd13
  set Bad12 := {x ∈ V1 | (#{y ∈ V2 | G.Adj x y} : ℝ) < (γ - η) * (#V2 : ℝ)}
  set Bad13 := {x ∈ V1 | (#{z ∈ V3 | G.Adj x z} : ℝ) < (γ - η) * (#V3 : ℝ)}
  have hGood1_ne : (V1 \ (Bad12 ∪ Bad13)).Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro hemp
    have hsub : V1 ⊆ Bad12 ∪ Bad13 := sdiff_eq_empty_iff_subset.mp hemp
    have hcard : (#V1 : ℝ) ≤ (#Bad12 : ℝ) + (#Bad13 : ℝ) := by
      exact_mod_cast (card_le_card hsub).trans (card_union_le Bad12 Bad13)
    have hV1_rpos : (0 : ℝ) < #V1 := Nat.cast_pos.mpr hV1_pos
    nlinarith only [hcard, hBad12, hBad13, hη_le_quarter, hV1_rpos]
  obtain ⟨a1, ha1_mem⟩ := hGood1_ne
  rw [Finset.mem_sdiff, mem_union] at ha1_mem
  have ha1_V1 : a1 ∈ V1 := ha1_mem.1
  let B1 : Finset V := {y ∈ V2 | G.Adj a1 y}
  let C1 : Finset V := {z ∈ V3 | G.Adj a1 z}
  have hB1_sub : B1 ⊆ V2 := filter_subset _ V2
  have hC1_sub : C1 ⊆ V3 := filter_subset _ V3
  have hB1_card : (γ - η) * (#V2 : ℝ) ≤ (#B1 : ℝ) := by
    by_contra hlt
    push Not at hlt
    exact ha1_mem.2 (Or.inl (mem_filter.mpr ⟨ha1_V1, hlt⟩))
  have hC1_card : (γ - η) * (#V3 : ℝ) ≤ (#C1 : ℝ) := by
    by_contra hlt
    push Not at hlt
    exact ha1_mem.2 (Or.inr (mem_filter.mpr ⟨ha1_V1, hlt⟩))
  -- Step 2: Pick a2 ∈ V1 \ {a1} with many neighbors in both B1 and C1
  have hB1_ge_η : (#V2 : ℝ) * η ≤ (#B1 : ℝ) := by
    nlinarith only [hB1_card, hη_le_γ_sub, Nat.cast_nonneg (α := ℝ) #V2]
  have hC1_ge_η : (#V3 : ℝ) * η ≤ (#C1 : ℝ) := by
    nlinarith only [hC1_card, hη_le_γ_sub, Nat.cast_nonneg (α := ℝ) #V3]
  have hBad2 := card_low_degree_lt_of_isUniform G hu12 hB1_sub hV1_pos hV2_pos hη_pos hB1_ge_η hd12
  have hBad3 := card_low_degree_lt_of_isUniform G hu13 hC1_sub hV1_pos hV3_pos hη_pos hC1_ge_η hd13
  set Bad2 := {x ∈ V1 | (#{y ∈ B1 | G.Adj x y} : ℝ) < (γ - η) * (#B1 : ℝ)}
  set Bad3 := {x ∈ V1 | (#{z ∈ C1 | G.Adj x z} : ℝ) < (γ - η) * (#C1 : ℝ)}
  have hGood2_ne : (V1 \ (Bad2 ∪ Bad3 ∪ {a1})).Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro hemp
    have hsub : V1 ⊆ Bad2 ∪ Bad3 ∪ {a1} := sdiff_eq_empty_iff_subset.mp hemp
    have hcard : (#V1 : ℝ) ≤ (#Bad2 : ℝ) + (#Bad3 : ℝ) + 1 := by
      have h1 : #V1 ≤ #(Bad2 ∪ Bad3 ∪ {a1}) := card_le_card hsub
      have h2 : #(Bad2 ∪ Bad3 ∪ {a1}) ≤ #(Bad2 ∪ Bad3) + #{a1} := card_union_le _ _
      have h3 : #(Bad2 ∪ Bad3) ≤ #Bad2 + #Bad3 := card_union_le _ _
      rw [card_singleton] at h2
      exact_mod_cast (h1.trans h2).trans (Nat.add_le_add_right h3 1)
    have hV1_ge2 : (2 : ℝ) ≤ (#V1 : ℝ) := hmin_ge_two.trans hm1
    nlinarith only [hcard, hBad2, hBad3, hη_le_quarter, hV1_ge2]
  obtain ⟨a2, ha2_mem⟩ := hGood2_ne
  rw [Finset.mem_sdiff, mem_union, mem_union, mem_singleton] at ha2_mem
  have ha2_V1 : a2 ∈ V1 := ha2_mem.1
  have ha_ne : a1 ≠ a2 := fun h => ha2_mem.2 (Or.inr h.symm)
  let B2 : Finset V := {y ∈ B1 | G.Adj a2 y}
  let C2 : Finset V := {z ∈ C1 | G.Adj a2 z}
  have hB2_sub : B2 ⊆ V2 := (filter_subset _ B1).trans hB1_sub
  have hC2_sub : C2 ⊆ V3 := (filter_subset _ C1).trans hC1_sub
  have hB2_card_B1 : (γ - η) * (#B1 : ℝ) ≤ (#B2 : ℝ) := by
    by_contra hlt
    push Not at hlt
    exact ha2_mem.2 (Or.inl (Or.inl (mem_filter.mpr ⟨ha2_V1, hlt⟩)))
  have hC2_card_C1 : (γ - η) * (#C1 : ℝ) ≤ (#C2 : ℝ) := by
    by_contra hlt
    push Not at hlt
    exact ha2_mem.2 (Or.inl (Or.inr (mem_filter.mpr ⟨ha2_V1, hlt⟩)))
  have hB2_card_η : (#V2 : ℝ) * η ≤ (#B2 : ℝ) := by
    have hγsub_nn : 0 ≤ γ - η := by linarith only [hη_le_γ_sub, hη_pos]
    have h1 : (γ - η) ^ 2 * (#V2 : ℝ) ≤ (#B2 : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hB1_card hγsub_nn
      linarith only [hB2_card_B1, hmul, (show (γ - η) * ((γ - η) * (#V2 : ℝ)) = (γ - η) ^ 2 * (#V2 : ℝ) by ring)]
    have h2 : (#V2 : ℝ) * η ≤ (γ - η) ^ 2 * (#V2 : ℝ) := by
      rw [mul_comm (#V2 : ℝ)]
      exact mul_le_mul_of_nonneg_right hsq_ge_η (Nat.cast_nonneg _)
    exact h2.trans h1
  have hC2_card_η : (#V3 : ℝ) * η ≤ (#C2 : ℝ) := by
    have hγsub_nn : 0 ≤ γ - η := by linarith only [hη_le_γ_sub, hη_pos]
    have h1 : (γ - η) ^ 2 * (#V3 : ℝ) ≤ (#C2 : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hC1_card hγsub_nn
      linarith only [hC2_card_C1, hmul, (show (γ - η) * ((γ - η) * (#V3 : ℝ)) = (γ - η) ^ 2 * (#V3 : ℝ) by ring)]
    have h2 : (#V3 : ℝ) * η ≤ (γ - η) ^ 2 * (#V3 : ℝ) := by
      rw [mul_comm (#V3 : ℝ)]
      exact mul_le_mul_of_nonneg_right hsq_ge_η (Nat.cast_nonneg _)
    exact h2.trans h1
  have hB2_large : 16 / γ ^ 2 + 2 ≤ (#B2 : ℝ) := by
    have := mul_le_mul_of_nonneg_right hm2 hη_pos.le
    rw [div_mul_cancel₀ _ hη_pos.ne'] at this
    linarith only [this, hB2_card_η]
  have hC2_large : 16 / γ ^ 2 + 2 ≤ (#C2 : ℝ) := by
    have := mul_le_mul_of_nonneg_right hm3 hη_pos.le
    rw [div_mul_cancel₀ _ hη_pos.ne'] at this
    linarith only [this, hC2_card_η]
  -- Step 3: Uniformity of (V2, V3) gives density ≥ γ / 2 between B2 and C2
  have hreg23 := hu23 hB2_sub hC2_sub hB2_card_η hC2_card_η
  have hdens23 : γ / 2 ≤ (G.edgeDensity B2 C2 : ℝ) := by
    have := (abs_lt.mp hreg23).1
    linarith only [this, hd23, hη_le_γ4, hγ_pos]
  have hB2_rpos : (0 : ℝ) < #B2 := by
    have : (0 : ℝ) ≤ 16 / γ ^ 2 := by positivity
    linarith only [hB2_large, this]
  have hC2_rpos : (0 : ℝ) < #C2 := by
    have : (0 : ℝ) ≤ 16 / γ ^ 2 := by positivity
    linarith only [hC2_large, this]
  have hE23 : (γ / 2) * (#B2 : ℝ) * (#C2 : ℝ) ≤ (#(G.interedges B2 C2) : ℝ) := by
    rw [SimpleGraph.edgeDensity_def, Rat.cast_div, Rat.cast_natCast, Rat.cast_mul,
      Rat.cast_natCast, Rat.cast_natCast] at hdens23
    have := (le_div_iff₀ (mul_pos hB2_rpos hC2_rpos)).mp hdens23
    linarith only [this]
  -- Step 4: Double counting finds a K_{2,2} between B2 and C2
  have hB2_ge_two : 2 ≤ #B2 := by
    suffices h : (2 : ℝ) ≤ (#B2 : ℝ) by exact_mod_cast h
    have : (0 : ℝ) ≤ 16 / γ ^ 2 := by positivity
    linarith only [hB2_large, this]
  obtain ⟨b1, hb1_B2, b2, hb2_B2, hb_ne, hpair⟩ :=
    exists_pair_common_neighbors_ge G B2 C2 hB2_ge_two
  have hcommon_ge_two : 2 ≤ #{c ∈ C2 | G.Adj b1 c ∧ G.Adj b2 c} := by
    suffices h : (1 : ℝ) < (#{c ∈ C2 | G.Adj b1 c ∧ G.Adj b2 c} : ℝ) by
      have : 1 < #{c ∈ C2 | G.Adj b1 c ∧ G.Adj b2 c} := by exact_mod_cast h
      omega
    set E : ℝ := (#(G.interedges B2 C2) : ℝ)
    set E0 : ℝ := (γ / 2) * (#B2 : ℝ) * (#C2 : ℝ)
    have hγB2 : 4 ≤ γ * (#B2 : ℝ) := by
      have h1 : 4 / γ ≤ 16 / γ ^ 2 + 2 := by
        have h3 : 4 / γ ≤ 16 / γ ^ 2 := by
          rw [div_le_div_iff₀ hγ_pos (sq_pos_of_pos hγ_pos)]
          nlinarith only [hγ_pos, hγ_le]
        linarith only [h3]
      have h2 : 4 / γ ≤ (#B2 : ℝ) := h1.trans hB2_large
      have := mul_le_mul_of_nonneg_left h2 hγ_pos.le
      rwa [mul_div_cancel₀ _ hγ_pos.ne'] at this
    have hE0_ge : 2 * (#C2 : ℝ) ≤ E0 := by
      have hmul := mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ (γ / 2) * (#B2 : ℝ) by linarith only [hγB2]) hC2_rpos.le
      simpa only [E0] using hmul
    have hquad : E0 ^ 2 - (#C2 : ℝ) * E0 ≤ E ^ 2 - (#C2 : ℝ) * E := by
      have hdiff : E ^ 2 - (#C2 : ℝ) * E - (E0 ^ 2 - (#C2 : ℝ) * E0) =
          (E - E0) * (E + E0 - (#C2 : ℝ)) := by ring
      have h1 : 0 ≤ E - E0 := by linarith only [hE23]
      have h2 : 0 ≤ E + E0 - (#C2 : ℝ) := by linarith only [hE23, hE0_ge, hC2_rpos]
      have h3 : 0 ≤ (E - E0) * (E + E0 - (#C2 : ℝ)) := mul_nonneg h1 h2
      linarith only [hdiff, h3]
    have h1 : E0 ^ 2 - (#C2 : ℝ) * E0 ≤
        (#C2 : ℝ) * ((#B2 : ℝ) * ((#B2 : ℝ) - 1)) *
          (#{c ∈ C2 | G.Adj b1 c ∧ G.Adj b2 c} : ℝ) := hquad.trans hpair
    have h2 : (#C2 : ℝ) * ((#B2 : ℝ) * ((#B2 : ℝ) - 1)) < E0 ^ 2 - (#C2 : ℝ) * E0 := by
      have hC2_ge : 16 / γ ^ 2 < (#C2 : ℝ) := by linarith only [hC2_large]
      have hγ2C2 : 16 < γ ^ 2 * (#C2 : ℝ) := by
        have := mul_lt_mul_of_pos_left hC2_ge (sq_pos_of_pos hγ_pos)
        rwa [mul_div_cancel₀ _ (sq_pos_of_pos hγ_pos).ne'] at this
      have hfactor : E0 ^ 2 - (#C2 : ℝ) * E0 =
          (#C2 : ℝ) * (#B2 : ℝ) * ((γ / 2) * (#C2 : ℝ) * ((γ / 2) * (#B2 : ℝ) - 1)) := by
        simp only [E0]; ring
      rw [hfactor]
      have hmid : (γ / 4) * (#B2 : ℝ) ≤ (γ / 2) * (#B2 : ℝ) - 1 := by linarith only [hγB2]
      have hstep1 : (γ / 2) * (#C2 : ℝ) * ((γ / 4) * (#B2 : ℝ)) ≤
          (γ / 2) * (#C2 : ℝ) * ((γ / 2) * (#B2 : ℝ) - 1) :=
        mul_le_mul_of_nonneg_left hmid (by positivity)
      have hstep2 : (γ / 2) * (#C2 : ℝ) * ((γ / 4) * (#B2 : ℝ)) =
          (γ ^ 2 * (#C2 : ℝ) / 8) * (#B2 : ℝ) := by ring
      have hprod : 2 * (#B2 : ℝ) < (γ / 2) * (#C2 : ℝ) * ((γ / 2) * (#B2 : ℝ) - 1) := by
        have hlt : 2 * (#B2 : ℝ) < (γ ^ 2 * (#C2 : ℝ) / 8) * (#B2 : ℝ) :=
          mul_lt_mul_of_pos_right (by linarith only [hγ2C2]) hB2_rpos
        linarith only [hlt, hstep1, hstep2]
      have hlt2 : (#B2 : ℝ) - 1 < (γ / 2) * (#C2 : ℝ) * ((γ / 2) * (#B2 : ℝ) - 1) := by
        linarith only [hprod, hB2_rpos]
      have hBC_pos : (0 : ℝ) < (#C2 : ℝ) * (#B2 : ℝ) := mul_pos hC2_rpos hB2_rpos
      rw [← mul_assoc]
      exact mul_lt_mul_of_pos_left hlt2 hBC_pos
    have hden_pos : (0 : ℝ) < (#C2 : ℝ) * ((#B2 : ℝ) * ((#B2 : ℝ) - 1)) := by
      have hB2_gt1 : (0 : ℝ) < (#B2 : ℝ) - 1 := by
        have : (2 : ℝ) ≤ (#B2 : ℝ) := by exact_mod_cast hB2_ge_two
        linarith only [this]
      exact mul_pos hC2_rpos (mul_pos hB2_rpos hB2_gt1)
    have hstrict : (#C2 : ℝ) * ((#B2 : ℝ) * ((#B2 : ℝ) - 1)) * 1 <
        (#C2 : ℝ) * ((#B2 : ℝ) * ((#B2 : ℝ) - 1)) *
          (#{c ∈ C2 | G.Adj b1 c ∧ G.Adj b2 c} : ℝ) := by
      rw [mul_one]
      exact lt_of_lt_of_le h2 h1
    exact lt_of_mul_lt_mul_left hstrict hden_pos.le
  obtain ⟨c1, hc1, c2, hc2, hc_ne⟩ := one_lt_card.mp (by omega : 1 < #{c ∈ C2 | G.Adj b1 c ∧ G.Adj b2 c})
  rw [mem_filter] at hc1 hc2
  -- Assemble the 6 vertices into an octahedron
  exact not_octahedron_free_of_six ha_ne hb_ne hc_ne
    (mem_filter.mp (mem_filter.mp hb1_B2).1).2
    (mem_filter.mp (mem_filter.mp hb2_B2).1).2
    (mem_filter.mp hb1_B2).2
    (mem_filter.mp hb2_B2).2
    (mem_filter.mp (mem_filter.mp hc1.1).1).2
    (mem_filter.mp (mem_filter.mp hc2.1).1).2
    (mem_filter.mp hc1.1).2
    (mem_filter.mp hc2.1).2
    hc1.2.1 hc2.2.1 hc1.2.2 hc2.2.2

/-- Mantel's theorem for a triangle-free graph on `V`: `4 * #R.edgeFinset ≤ (Fintype.card V)^2`. -/
lemma mantel_bound {V : Type*} [Fintype V] (R : SimpleGraph V) [DecidableRel R.Adj]
    (hcf : R.CliqueFree 3) :
    4 * #R.edgeFinset ≤ Fintype.card V ^ 2 := by
  have hle := SimpleGraph.CliqueFree.card_edgeFinset_le (r := 2) hcf
  dsimp only at hle
  set m := Fintype.card V
  have hmod : m % 2 = 0 ∨ m % 2 = 1 := Nat.mod_two_eq_zero_or_one m
  rcases hmod with h0 | h1
  · rw [h0] at hle
    norm_num at hle
    omega
  · rw [h1] at hle
    norm_num at hle
    omega

end Erdos579Proof

open Filter SimpleGraph Finset Erdos579Proof

theorem OMA.solution : type_of% @Erdos579.erdos_579.variants.ehss_large_delta := by
  classical
  intro δ hδ
  let ε : ℝ := min (δ - 1 / 8) (1 / 8)
  have hε_pos : 0 < ε := lt_min (by linarith) (by norm_num)
  have hε_le_eighth : ε ≤ 1 / 8 := min_le_right _ _
  have hε_le_δ : 1 / 8 + ε ≤ δ := by linarith [min_le_left (δ - 1 / 8) (1 / 8)]
  let γ : ℝ := ε / 2
  have hγ_pos : 0 < γ := by positivity
  have hγ_le_one : γ ≤ 1 := by simp only [γ]; linarith only [hε_le_eighth]
  let η : ℝ := γ ^ 2 / 4
  have hη_pos : 0 < η := by positivity
  have hη_le_γ2 : η ≤ γ ^ 2 / 4 := le_rfl
  have hη_le_quarter : η ≤ 1 / 4 := by simp only [η, γ]; nlinarith only [hε_pos, hε_le_eighth]
  have hη_le_ε : η ≤ ε / 32 := by simp only [η, γ]; nlinarith only [hε_pos, hε_le_eighth]
  let l : ℕ := Nat.ceil (4 / ε) + 1
  have hl_pos : 0 < l := Nat.succ_pos _
  have hl_inv : 1 / (l : ℝ) < ε / 4 := by
    have h1 : 4 / ε < (l : ℝ) := by
      have := Nat.le_ceil (4 / ε)
      have hlc : (l : ℝ) = (Nat.ceil (4 / ε) : ℝ) + 1 := by exact_mod_cast rfl
      linarith
    rw [div_lt_iff₀ (Nat.cast_pos.mpr hl_pos)]
    have := mul_lt_mul_of_pos_right h1 hε_pos
    rw [div_mul_cancel₀ _ hε_pos.ne'] at this
    linarith
  let M : ℕ := SzemerediRegularity.bound η l
  have hM_ge_l : l ≤ M := (SzemerediRegularity.le_initialBound η l).trans
    (SzemerediRegularity.initialBound_le_bound η l)
  have hM_pos : 0 < M := lt_of_lt_of_le hl_pos hM_ge_l
  have hM_rpos : (0 : ℝ) < M := Nat.cast_pos.mpr hM_pos
  let c : ℝ := η ^ 2 / (4 * (M : ℝ))
  have hc_pos : 0 < c := by positivity
  refine ⟨c, hc_pos, ?_⟩
  let m0 : ℕ := Nat.ceil ((16 / γ ^ 2 + 2) / η) + 2
  let N0 : ℕ := max (max l (2 * M)) (max (M * m0) (Nat.ceil (3 * (M : ℝ) / ε) + 1))
  rw [eventually_atTop]
  refine ⟨N0, fun n hn G hfree hedge => ?_⟩
  have hn_l : l ≤ n := (le_trans (le_max_left _ _) (le_max_left _ _)).trans hn
  have hn_2M : 2 * M ≤ n := (le_trans (le_max_right _ _) (le_max_left _ _)).trans hn
  have hn_Mm0 : M * m0 ≤ n := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hn
  have hn_eps : Nat.ceil (3 * (M : ℝ) / ε) + 1 ≤ n :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans hn
  by_contra hindep_lt
  push Not at hindep_lt
  -- Apply Szemerédi Regularity Lemma to G
  have hl_card : l ≤ Fintype.card (Fin n) := by simpa using hn_l
  obtain ⟨P, hP_eq, hP_ge, hP_le, hP_unif⟩ := szemeredi_regularity G hη_pos hl_card
  set k : ℕ := #P.parts
  have hk_ge_l : l ≤ k := hP_ge
  have hk_le_M : k ≤ M := hP_le
  have hk_pos : 0 < k := lt_of_lt_of_le hl_pos hk_ge_l
  have hk_rpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk_pos
  have hn_pos : 0 < n := lt_of_lt_of_le hl_pos hn_l
  have hn_rpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  -- Part size bounds
  have hpart_lower : ∀ u ∈ P.parts, m0 ≤ #u := fun u hu => by
    have h1 : n / k ≤ #u := by
      have := hP_eq.average_le_card_part hu
      simpa using this
    have h2 : m0 ≤ n / k := by
      rw [Nat.le_div_iff_mul_le hk_pos]
      exact (Nat.mul_le_mul_left m0 hk_le_M).trans (by rw [mul_comm]; exact hn_Mm0)
    exact h2.trans h1
  have hpart_lower_real : ∀ u ∈ P.parts, (n : ℝ) / (2 * (M : ℝ)) ≤ (#u : ℝ) := fun u hu => by
    have h1 : n / k ≤ #u := by
      have := hP_eq.average_le_card_part hu
      simpa using this
    have h2 : n / M ≤ n / k := Nat.div_le_div_left hk_le_M hk_pos
    have h3 : n / M ≤ #u := h2.trans h1
    have hdiv : (n : ℝ) / (M : ℝ) - 1 < (n / M : ℕ) := by
      have hmod : (n % M : ℕ) < M := Nat.mod_lt n hM_pos
      have hdm : M * (n / M) + n % M = n := Nat.div_add_mod n M
      have hdm_r : (M : ℝ) * (n / M : ℕ) + (n % M : ℕ) = (n : ℝ) := by exact_mod_cast hdm
      have hmod_r : ((n % M : ℕ) : ℝ) < (M : ℝ) := by exact_mod_cast hmod
      rw [sub_lt_iff_lt_add, div_lt_iff₀ hM_rpos]
      nlinarith only [hdm_r, hmod_r]
    have hn_ge_2M_r : 2 * (M : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_2M
    have h4 : (n : ℝ) / (2 * (M : ℝ)) ≤ (n : ℝ) / (M : ℝ) - 1 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (M : ℝ))]
      have hm : (n : ℝ) / (M : ℝ) * (M : ℝ) = (n : ℝ) := div_mul_cancel₀ _ hM_rpos.ne'
      have heq : ((n : ℝ) / (M : ℝ) - 1) * (2 * (M : ℝ)) =
          2 * ((n : ℝ) / (M : ℝ) * (M : ℝ)) - 2 * (M : ℝ) := by ring
      linarith only [hm, heq, hn_ge_2M_r]
    have h3_r : ((n / M : ℕ) : ℝ) ≤ (#u : ℝ) := by exact_mod_cast h3
    linarith only [hdiv, h4, h3_r]
  have hpart_upper : ∀ u ∈ P.parts, (#u : ℝ) ≤ (n : ℝ) / (k : ℝ) + 1 := fun u hu => by
    have h1 : #u ≤ n / k + 1 := by
      have := hP_eq.card_part_le_average_add_one hu
      simpa using this
    have h2 : ((n / k : ℕ) : ℝ) ≤ (n : ℝ) / (k : ℝ) := Nat.cast_div_le
    have h1_r : (#u : ℝ) ≤ ((n / k : ℕ) : ℝ) + 1 := by exact_mod_cast h1
    linarith only [h1_r, h2]
  have hm0_real : (16 / γ ^ 2 + 2) / η ≤ (m0 : ℝ) := by
    have h1 : (16 / γ ^ 2 + 2) / η ≤ (Nat.ceil ((16 / γ ^ 2 + 2) / η) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil ((16 / γ ^ 2 + 2) / η) : ℝ) ≤ (m0 : ℝ) := by
      exact_mod_cast Nat.le_add_right _ 2
    linarith only [h1, h2]
  -- Reduced graph R on P.parts
  let R : SimpleGraph P.parts :=
    { Adj := fun u v => u ≠ v ∧ G.IsUniform η u.1 v.1 ∧ γ ≤ (G.edgeDensity u.1 v.1 : ℝ)
      symm := ⟨fun _ _ ⟨hne, hun, hd⟩ =>
        ⟨hne.symm, hun.symm, by rwa [G.edgeDensity_comm]⟩⟩
      loopless := ⟨fun _ h => h.1 rfl⟩ }
  -- R is triangle-free by Lemma 2
  have hR_cf : R.CliqueFree 3 := by
    intro t ht
    obtain ⟨u, v, w, huv, huw, hvw, rfl⟩ := card_eq_three.mp ht.card_eq
    have huv_adj : R.Adj u v := ht.isClique (by simp) (by simp) huv
    have huw_adj : R.Adj u w := ht.isClique (by simp) (by simp) huw
    have hvw_adj : R.Adj v w := ht.isClique (by simp) (by simp) hvw
    have hm1 : (16 / γ ^ 2 + 2) / η ≤ (#u.1 : ℝ) :=
      hm0_real.trans (by exact_mod_cast hpart_lower u.1 u.2)
    have hm2 : (16 / γ ^ 2 + 2) / η ≤ (#v.1 : ℝ) :=
      hm0_real.trans (by exact_mod_cast hpart_lower v.1 v.2)
    have hm3 : (16 / γ ^ 2 + 2) / η ≤ (#w.1 : ℝ) :=
      hm0_real.trans (by exact_mod_cast hpart_lower w.1 w.2)
    exact regular_triangle_not_octahedron_free G hγ_pos hγ_le_one hη_pos hη_le_γ2
      hm1 hm2 hm3 huv_adj.2.1 huw_adj.2.1 hvw_adj.2.1
      huv_adj.2.2 huw_adj.2.2 hvw_adj.2.2 hfree
  -- Mantel bound on R
  have hR_mantel : 4 * #R.edgeFinset ≤ k ^ 2 := by
    have h := mantel_bound R hR_cf
    simpa [Fintype.card_coe, k] using h
  -- Define the dense uniform off-diagonal pairs
  let DenseUnif : Finset (Finset (Fin n) × Finset (Fin n)) :=
    P.parts.offDiag.filter fun p => G.IsUniform η p.1 p.2 ∧ γ ≤ (G.edgeDensity p.1 p.2 : ℝ)
  have hDU_card : 2 * #DenseUnif ≤ k ^ 2 := by
    have hPne : P.parts.Nonempty :=
      P.parts_nonempty (univ_nonempty_iff.mpr ⟨⟨0, hn_pos⟩⟩).ne_empty
    let dummy : P.parts := ⟨hPne.choose, hPne.choose_spec⟩
    have hinj : #DenseUnif ≤ #(R.interedges univ univ) := by
      refine card_le_card_of_injOn
        (fun p => if h : p.1 ∈ P.parts ∧ p.2 ∈ P.parts then
          ((⟨p.1, h.1⟩ : P.parts), (⟨p.2, h.2⟩ : P.parts)) else (dummy, dummy))
        ?_ ?_
      · intro p hp
        simp only [Finset.mem_coe, DenseUnif, mem_filter, mem_offDiag] at hp
        dsimp only
        rw [dif_pos ⟨hp.1.1, hp.1.2.1⟩, Finset.mem_coe, mem_interedges_iff]
        refine ⟨mem_univ _, mem_univ _, ?_, hp.2.1, hp.2.2⟩
        intro heq
        exact hp.1.2.2 (congrArg Subtype.val heq)
      · intro p hp q hq heq
        simp only [Finset.mem_coe, DenseUnif, mem_filter, mem_offDiag] at hp hq
        dsimp only at heq
        rw [dif_pos ⟨hp.1.1, hp.1.2.1⟩, dif_pos ⟨hq.1.1, hq.1.2.1⟩] at heq
        have h1 := congrArg (fun x : P.parts × P.parts => x.1.1) heq
        have h2 := congrArg (fun x : P.parts × P.parts => x.2.1) heq
        exact Prod.ext h1 h2
    rw [card_interedges_univ] at hinj
    omega
  -- Every dense uniform pair has density < 1/2 + 3 * η by Lemma 1
  have hDU_edge_bound : ∀ p ∈ DenseUnif,
      (#(G.interedges p.1 p.2) : ℝ) ≤ (1 / 2 + 3 * η) * ((n : ℝ) / (k : ℝ) + 1) ^ 2 := by
    intro p hp
    simp only [DenseUnif, mem_filter, mem_offDiag] at hp
    have hdisj : Disjoint p.1 p.2 := P.disjoint hp.1.1 hp.1.2.1 hp.1.2.2
    have hp1_pos : 0 < #p.1 := lt_of_lt_of_le (by omega : 0 < m0) (hpart_lower p.1 hp.1.1)
    have hp2_pos : 0 < #p.2 := lt_of_lt_of_le (by omega : 0 < m0) (hpart_lower p.2 hp.1.2.1)
    have hindep1 : (G.indepNum : ℝ) < (η ^ 2 / 2) * (#p.1 : ℝ) := by
      have h1 := hpart_lower_real p.1 hp.1.1
      have h2 : c * (n : ℝ) = (η ^ 2 / 2) * ((n : ℝ) / (2 * (M : ℝ))) := by
        simp only [c]; ring
      have h3 : (η ^ 2 / 2) * ((n : ℝ) / (2 * (M : ℝ))) ≤ (η ^ 2 / 2) * (#p.1 : ℝ) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      linarith only [hindep_lt, h2, h3]
    have hindep2 : (G.indepNum : ℝ) < (η ^ 2 / 2) * (#p.2 : ℝ) := by
      have h1 := hpart_lower_real p.2 hp.1.2.1
      have h2 : c * (n : ℝ) = (η ^ 2 / 2) * ((n : ℝ) / (2 * (M : ℝ))) := by
        simp only [c]; ring
      have h3 : (η ^ 2 / 2) * ((n : ℝ) / (2 * (M : ℝ))) ≤ (η ^ 2 / 2) * (#p.2 : ℝ) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      linarith only [hindep_lt, h2, h3]
    have hnot_dense : (#(G.interedges p.1 p.2) : ℝ) < (1 / 2 + 3 * η) * (#p.1 : ℝ) * (#p.2 : ℝ) := by
      by_contra hge
      push Not at hge
      exact dense_pair_not_octahedron_free G hdisj hp1_pos hp2_pos hη_pos hη_le_quarter
        hge hindep1 hindep2 hfree
    have hu1 := hpart_upper p.1 hp.1.1
    have hu2 := hpart_upper p.2 hp.1.2.1
    have hprod : (#p.1 : ℝ) * (#p.2 : ℝ) ≤ ((n : ℝ) / (k : ℝ) + 1) ^ 2 := by
      rw [sq]
      exact mul_le_mul hu1 hu2 (Nat.cast_nonneg _) (by positivity)
    have hmul := mul_le_mul_of_nonneg_left hprod (by positivity : (0 : ℝ) ≤ 1 / 2 + 3 * η)
    linarith only [hnot_dense, hmul]
  -- Partition total ordered edges into 4 pieces
  set B : ℝ := ((n : ℝ) / (k : ℝ) + 1) ^ 2
  have hB_nonneg : 0 ≤ B := sq_nonneg _
  have htotal_eq : (#(G.interedges univ univ) : ℝ) =
      ∑ p ∈ P.parts ×ˢ P.parts, (#(G.interedges p.1 p.2) : ℝ) := by
    have hnat : #(G.interedges univ univ) =
        ∑ u ∈ P.parts, ∑ v ∈ P.parts, #(G.interedges u v) := by
      change #(Rel.interedges G.Adj univ univ) = _
      rw [Rel.card_interedges_finpartition_left G.Adj P univ]
      congr 1
      ext u
      exact Rel.card_interedges_finpartition_right G.Adj u P
    rw [hnat, ← sum_product', Nat.cast_sum]
  have hcell_le_B : ∀ p ∈ P.parts ×ˢ P.parts, (#(G.interedges p.1 p.2) : ℝ) ≤ B := by
    intro p hp
    rw [mem_product] at hp
    have h1 : (#(G.interedges p.1 p.2) : ℝ) ≤ (#p.1 : ℝ) * (#p.2 : ℝ) := by
      exact_mod_cast G.card_interedges_le_mul p.1 p.2
    have h2 : (#p.1 : ℝ) * (#p.2 : ℝ) ≤ B := by
      simp only [B]
      rw [sq]
      exact mul_le_mul (hpart_upper p.1 hp.1) (hpart_upper p.2 hp.2) (Nat.cast_nonneg _) (by positivity)
    exact h1.trans h2
  -- Split P.parts ×ˢ P.parts = diag ∪ nonUniforms ∪ (uniform sparse) ∪ DenseUnif
  let Diag : Finset (Finset (Fin n) × Finset (Fin n)) := P.parts.diag
  let SparseUnif : Finset (Finset (Fin n) × Finset (Fin n)) :=
    P.parts.offDiag.filter fun p => G.IsUniform η p.1 p.2 ∧ (G.edgeDensity p.1 p.2 : ℝ) < γ
  have hcover : P.parts ×ˢ P.parts ⊆ Diag ∪ (P.nonUniforms G η ∪ (SparseUnif ∪ DenseUnif)) := by
    intro ⟨u, v⟩ hp
    rw [mem_product] at hp
    by_cases huv : u = v
    · exact mem_union_left _ (mem_diag.mpr ⟨hp.1, huv⟩)
    · apply mem_union_right
      by_cases hun : G.IsUniform η u v
      · apply mem_union_right
        by_cases hgd : γ ≤ (G.edgeDensity u v : ℝ)
        · exact mem_union_right _ (mem_filter.mpr ⟨mem_offDiag.mpr ⟨hp.1, hp.2, huv⟩, hun, hgd⟩)
        · push Not at hgd
          exact mem_union_left _ (mem_filter.mpr ⟨mem_offDiag.mpr ⟨hp.1, hp.2, huv⟩, hun, hgd⟩)
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_offDiag.mpr ⟨hp.1, hp.2, huv⟩, hun⟩)
  have hsum_le_four :
      ∑ p ∈ P.parts ×ˢ P.parts, (#(G.interedges p.1 p.2) : ℝ) ≤
        ∑ p ∈ Diag, (#(G.interedges p.1 p.2) : ℝ) +
        ∑ p ∈ P.nonUniforms G η, (#(G.interedges p.1 p.2) : ℝ) +
        ∑ p ∈ SparseUnif, (#(G.interedges p.1 p.2) : ℝ) +
        ∑ p ∈ DenseUnif, (#(G.interedges p.1 p.2) : ℝ) := by
    have hnn : ∀ p : Finset (Fin n) × Finset (Fin n), (0 : ℝ) ≤ (#(G.interedges p.1 p.2) : ℝ) :=
      fun _ => Nat.cast_nonneg _
    have h1 := sum_le_sum_of_subset_of_nonneg hcover (fun p _ _ => hnn p)
    have h2 := sum_union_le_of_nonneg Diag (P.nonUniforms G η ∪ (SparseUnif ∪ DenseUnif))
      (fun p => (#(G.interedges p.1 p.2) : ℝ)) hnn
    have h3 := sum_union_le_of_nonneg (P.nonUniforms G η) (SparseUnif ∪ DenseUnif)
      (fun p => (#(G.interedges p.1 p.2) : ℝ)) hnn
    have h4 := sum_union_le_of_nonneg SparseUnif DenseUnif
      (fun p => (#(G.interedges p.1 p.2) : ℝ)) hnn
    linarith only [h1, h2, h3, h4]
  -- Bound piece 1: Diag
  have hDiag_le : ∑ p ∈ Diag, (#(G.interedges p.1 p.2) : ℝ) ≤ (k : ℝ) * B := by
    have hsub : Diag ⊆ P.parts ×ˢ P.parts := fun p hp => by
      rw [mem_diag] at hp
      rw [mem_product]
      exact ⟨hp.1, hp.2 ▸ hp.1⟩
    calc ∑ p ∈ Diag, (#(G.interedges p.1 p.2) : ℝ)
        ≤ ∑ _ ∈ Diag, B := sum_le_sum fun p hp => hcell_le_B p (hsub hp)
      _ = (#Diag : ℝ) * B := by rw [sum_const, nsmul_eq_mul]
      _ = (k : ℝ) * B := by simp [Diag, k]
  -- Bound piece 2: nonUniforms
  have hNonUnif_le : ∑ p ∈ P.nonUniforms G η, (#(G.interedges p.1 p.2) : ℝ) ≤
      η * (k : ℝ) ^ 2 * B := by
    have hsub : P.nonUniforms G η ⊆ P.parts ×ˢ P.parts := fun p hp => by
      have hp' := (filter_subset _ _ hp)
      rw [mem_offDiag] at hp'
      rw [mem_product]
      exact ⟨hp'.1, hp'.2.1⟩
    have hcard_le : (#(P.nonUniforms G η) : ℝ) ≤ η * (k : ℝ) ^ 2 := by
      have h1 : (#(P.nonUniforms G η) : ℝ) ≤ ((k * (k - 1) : ℕ) : ℝ) * η := hP_unif
      have h2 : ((k * (k - 1) : ℕ) : ℝ) ≤ (k : ℝ) ^ 2 := by
        have : k * (k - 1) ≤ k * k := Nat.mul_le_mul_left k (Nat.sub_le k 1)
        exact_mod_cast (show k * (k - 1) ≤ k ^ 2 by rwa [sq])
      have h3 := mul_le_mul_of_nonneg_right h2 hη_pos.le
      linarith only [h1, h3]
    calc ∑ p ∈ P.nonUniforms G η, (#(G.interedges p.1 p.2) : ℝ)
        ≤ ∑ _ ∈ P.nonUniforms G η, B := sum_le_sum fun p hp => hcell_le_B p (hsub hp)
      _ = (#(P.nonUniforms G η) : ℝ) * B := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (η * (k : ℝ) ^ 2) * B := mul_le_mul_of_nonneg_right hcard_le hB_nonneg
  -- Bound piece 3: SparseUnif
  have hSparse_le : ∑ p ∈ SparseUnif, (#(G.interedges p.1 p.2) : ℝ) ≤
      γ * (k : ℝ) ^ 2 * B := by
    have hcard_le : (#SparseUnif : ℝ) ≤ (k : ℝ) ^ 2 := by
      have h1 : #SparseUnif ≤ #P.parts.offDiag := card_filter_le _ _
      have h2 : #P.parts.offDiag ≤ k ^ 2 := by
        rw [offDiag_card, sq]
        exact Nat.sub_le _ _
      exact_mod_cast h1.trans h2
    have hterm : ∀ p ∈ SparseUnif, (#(G.interedges p.1 p.2) : ℝ) ≤ γ * B := by
      intro p hp
      simp only [SparseUnif, mem_filter, mem_offDiag] at hp
      have hp1_pos : (0 : ℝ) < #p.1 :=
        Nat.cast_pos.mpr (lt_of_lt_of_le (by omega : 0 < m0) (hpart_lower p.1 hp.1.1))
      have hp2_pos : (0 : ℝ) < #p.2 :=
        Nat.cast_pos.mpr (lt_of_lt_of_le (by omega : 0 < m0) (hpart_lower p.2 hp.1.2.1))
      have hdens := hp.2.2
      rw [SimpleGraph.edgeDensity_def, Rat.cast_div, Rat.cast_natCast, Rat.cast_mul,
        Rat.cast_natCast, Rat.cast_natCast, div_lt_iff₀ (mul_pos hp1_pos hp2_pos)] at hdens
      have hprod : (#p.1 : ℝ) * (#p.2 : ℝ) ≤ B := by
        simp only [B]
        rw [sq]
        exact mul_le_mul (hpart_upper p.1 hp.1.1) (hpart_upper p.2 hp.1.2.1)
          (Nat.cast_nonneg _) (by positivity)
      have hmul := mul_le_mul_of_nonneg_left hprod hγ_pos.le
      linarith only [hdens, hmul]
    calc ∑ p ∈ SparseUnif, (#(G.interedges p.1 p.2) : ℝ)
        ≤ ∑ _ ∈ SparseUnif, (γ * B) := sum_le_sum hterm
      _ = (#SparseUnif : ℝ) * (γ * B) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (k : ℝ) ^ 2 * (γ * B) := mul_le_mul_of_nonneg_right hcard_le (by positivity)
      _ = γ * (k : ℝ) ^ 2 * B := by ring
  -- Bound piece 4: DenseUnif
  have hDense_le : ∑ p ∈ DenseUnif, (#(G.interedges p.1 p.2) : ℝ) ≤
      (1 / 4 + 3 / 2 * η) * (k : ℝ) ^ 2 * B := by
    have hDU_r : (#DenseUnif : ℝ) ≤ (k : ℝ) ^ 2 / 2 := by
      have : (2 : ℝ) * (#DenseUnif : ℝ) ≤ (k : ℝ) ^ 2 := by exact_mod_cast hDU_card
      linarith only [this]
    calc ∑ p ∈ DenseUnif, (#(G.interedges p.1 p.2) : ℝ)
        ≤ ∑ _ ∈ DenseUnif, ((1 / 2 + 3 * η) * B) := sum_le_sum hDU_edge_bound
      _ = (#DenseUnif : ℝ) * ((1 / 2 + 3 * η) * B) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ((k : ℝ) ^ 2 / 2) * ((1 / 2 + 3 * η) * B) :=
          mul_le_mul_of_nonneg_right hDU_r (by positivity)
      _ = (1 / 4 + 3 / 2 * η) * (k : ℝ) ^ 2 * B := by ring
  -- Combine all 4 pieces
  have hupper_total : (#(G.interedges univ univ) : ℝ) ≤
      (1 / 4 + 1 / (k : ℝ) + γ + 5 / 2 * η) * ((n : ℝ) + (k : ℝ)) ^ 2 := by
    have hkB : (k : ℝ) ^ 2 * B = ((n : ℝ) + (k : ℝ)) ^ 2 := by
      simp only [B]
      rw [← mul_pow, mul_add, mul_div_cancel₀ _ hk_rpos.ne', mul_one]
    have hdiag_rw : (k : ℝ) * B = (1 / (k : ℝ)) * ((k : ℝ) ^ 2 * B) := by
      rw [one_div, sq, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hk_rpos.ne', one_mul]
    rw [htotal_eq]
    calc ∑ p ∈ P.parts ×ˢ P.parts, (#(G.interedges p.1 p.2) : ℝ)
        ≤ (k : ℝ) * B + η * (k : ℝ) ^ 2 * B + γ * (k : ℝ) ^ 2 * B +
            (1 / 4 + 3 / 2 * η) * (k : ℝ) ^ 2 * B := by
              linarith only [hsum_le_four, hDiag_le, hNonUnif_le, hSparse_le, hDense_le]
      _ = (1 / 4 + 1 / (k : ℝ) + γ + 5 / 2 * η) * ((k : ℝ) ^ 2 * B) := by
            rw [hdiag_rw]; ring
      _ = (1 / 4 + 1 / (k : ℝ) + γ + 5 / 2 * η) * ((n : ℝ) + (k : ℝ)) ^ 2 := by rw [hkB]
  -- Final contradiction against 2 * δ * n^2 ≤ #(G.interedges univ univ)
  have hlower_total : (1 / 4 + 2 * ε) * (n : ℝ) ^ 2 ≤ (#(G.interedges univ univ) : ℝ) := by
    have h1 : (#(G.interedges univ univ) : ℝ) = 2 * (#G.edgeFinset : ℝ) := by
      exact_mod_cast card_interedges_univ G
    rw [h1]
    have h2 : (1 / 4 + 2 * ε) * (n : ℝ) ^ 2 ≤ 2 * (δ * (n : ℝ) ^ 2) := by
      nlinarith only [hε_le_δ, sq_nonneg (n : ℝ)]
    linarith only [h2, hedge]
  have hcoeff : 1 / 4 + 1 / (k : ℝ) + γ + 5 / 2 * η < 1 / 4 + ε := by
    have hkinv : 1 / (k : ℝ) ≤ 1 / (l : ℝ) :=
      one_div_le_one_div_of_le (Nat.cast_pos.mpr hl_pos) (by exact_mod_cast hk_ge_l)
    simp only [γ]
    linarith only [hkinv, hl_inv, hη_le_ε, hε_pos]
  have hnk_sq : ((n : ℝ) + (k : ℝ)) ^ 2 ≤ (1 + ε) * (n : ℝ) ^ 2 := by
    have h1 : 3 * (M : ℝ) / ε < (n : ℝ) := by
      have hceil : 3 * (M : ℝ) / ε ≤ (Nat.ceil (3 * (M : ℝ) / ε) : ℝ) := Nat.le_ceil _
      have hnc : (Nat.ceil (3 * (M : ℝ) / ε) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn_eps
      linarith only [hceil, hnc]
    have h2 : 3 * (M : ℝ) < ε * (n : ℝ) := by
      have := mul_lt_mul_of_pos_right h1 hε_pos
      rw [div_mul_cancel₀ _ hε_pos.ne'] at this
      linarith only [this]
    have hk_le_M_r : (k : ℝ) ≤ (M : ℝ) := by exact_mod_cast hk_le_M
    have h3 : 3 * (k : ℝ) < ε * (n : ℝ) := by linarith only [h2, hk_le_M_r]
    have hk_le_n : (k : ℝ) ≤ (n : ℝ) := by
      have : k ≤ n := hk_le_M.trans (by omega : M ≤ n)
      exact_mod_cast this
    have hsq : (k : ℝ) ^ 2 ≤ (k : ℝ) * (n : ℝ) := by nlinarith only [hk_le_n, hk_rpos]
    nlinarith only [h3, hsq, hn_rpos, hε_pos]
  have hfinal : (1 / 4 + 1 / (k : ℝ) + γ + 5 / 2 * η) * ((n : ℝ) + (k : ℝ)) ^ 2 <
      (1 / 4 + 2 * ε) * (n : ℝ) ^ 2 := by
    have hstep1 : (1 / 4 + 1 / (k : ℝ) + γ + 5 / 2 * η) * ((n : ℝ) + (k : ℝ)) ^ 2 <
        (1 / 4 + ε) * ((n : ℝ) + (k : ℝ)) ^ 2 :=
      mul_lt_mul_of_pos_right hcoeff (by positivity)
    have hstep2 : (1 / 4 + ε) * ((n : ℝ) + (k : ℝ)) ^ 2 ≤
        (1 / 4 + ε) * ((1 + ε) * (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hnk_sq (by positivity)
    have hstep3 : (1 / 4 + ε) * (1 + ε) ≤ 1 / 4 + 2 * ε := by
      nlinarith only [hε_pos, hε_le_eighth]
    have hstep4 : (1 / 4 + ε) * ((1 + ε) * (n : ℝ) ^ 2) ≤ (1 / 4 + 2 * ε) * (n : ℝ) ^ 2 := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hstep3 (sq_nonneg _)
    linarith only [hstep1, hstep2, hstep4]
  linarith only [hlower_total, hupper_total, hfinal]
